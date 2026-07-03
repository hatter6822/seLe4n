-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-SM SM6.C: PRODUCTION (LANDED).  Entered the production import closure with
-- `endpointReplyOnCore` when the live `.reply` / `.replyRecv` dispatch was wired
-- through the cross-core reply stack.  See docs/planning/SMP_CROSS_CORE_IPC_PLAN.md §5 (SM6.C).

import SeLe4n.Kernel.IPC.CrossCore.EndpointReply
import SeLe4n.Kernel.IPC.Invariant
import SeLe4n.Kernel.IPC.Invariant.LookupCongruence
import SeLe4n.Kernel.IPC.Invariant.PerCoreBundle
import SeLe4n.Kernel.IPC.Invariant.PerCoreBundlePreservation

/-!
# WS-SM SM6.C — Cross-core reply IPC-invariant preservation

`endpointReplyOnCore` preserves the kernel's object-store integrity
(`objects.invExt`) and the IPC `ipcInvariant` (notification well-formedness).  The
cross-core reply differs from its single-core form only in the *scheduler*
placement of the woken caller; `ipcInvariant` is **lookup-only** (it reads the
state solely through `objects[·]?`), so the cross-core caller wake (`wakeThread`,
object-invisible on the already-`.ready` caller — the SM6.A/SM6.B object-
invisibility keystone) cannot disturb it.  The reply store step reuses the
single-core per-step preservation lemmas verbatim.

**WS-SM SM6.D closure** (§4–§10): the three cross-core reply-path transitions
preserve the **whole twenty-conjunct bundle** and every core's per-core view of
it — `endpointReplyOnCore` / `endpointReceiveDualOnCore` via the off-scheduler
agreement dichotomy against their single-core counterparts (both spines run the
same object-store sequence and diverge only in scheduler placement;
`endpointReply`'s `replier == expected` gate is discharged by instantiating the
single-core replier at the recorded server, since a delegated reply cap carries
the same object-level effect), and the composed `endpointReplyRecvOnCore`
**compositionally** through its two legs — the receive leg's pre-state facts are
transported across the reply leg by the §9 effect characterisations (TCB
backward transport, endpoint-slot invisibility, reply-free/one-object-reuse
freshness).  The scheduler-reading `passiveServerIdle` rides the per-core
frames throughout.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  State characterisation: a reply either no-ops or stores-then-wakes
-- ============================================================================

/-- WS-SM SM6.C: the post-state of a cross-core reply is **either** the pre-state
(every error / non-`blockedOnReply` / wrong-replier path returns `st`) **or** the
cross-core wake of the reply-store result, followed — when the woken caller carried
a linked Reply — by the folded single-use consume (PR #827 review #3).  This is the
control-flow factoring the invariant proofs case on. -/
theorem endpointReplyOnCore_state_eq
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) :
    (endpointReplyOnCore replier target msg executingCore st).1 = st
    ∨ ∃ tcb st', lookupTcb st target = some tcb
        ∧ storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) = .ok st'
        ∧ ((tcb.replyObject = none ∧
              (endpointReplyOnCore replier target msg executingCore st).1
                = (wakeThread st' target executingCore).1)
           ∨ ∃ rid, tcb.replyObject = some rid ∧
              SystemState.consumeCallerReply target rid
                  (wakeThread st' target executingCore).1
                = .ok ((), (endpointReplyOnCore replier target msg executingCore st).1)) := by
  unfold endpointReplyOnCore
  split
  · exact Or.inl rfl
  split
  · exact Or.inl rfl
  split
  · exact Or.inl rfl
  · next tcb hLk =>
    split
    · next ep replyTarget =>
      split
      · exact Or.inl rfl
      · next expected =>
        -- PR #822 review 6J-lYm: the `replier == expected` gate was removed (authority
        -- is the reply cap), so the `some expected` arm is directly the store match.
        split
        · exact Or.inl rfl
        · next st' hStore =>
          -- PR #827 #3 fold: case on the woken caller's reply link.
          cases hRO : tcb.replyObject with
          | none =>
            exact Or.inr ⟨tcb, st', hLk, hStore, Or.inl ⟨hRO, rfl⟩⟩
          | some rid =>
            obtain ⟨stC, hCons⟩ := SystemState.consumeCallerReply_isOk
              (wakeThread st' target executingCore).1 target rid
            simp only [hCons]
            exact Or.inr ⟨tcb, st', hLk, hStore, Or.inr ⟨rid, hRO, hCons⟩⟩
    · exact Or.inl rfl

-- ============================================================================
-- §2  `objects.invExt` preservation
-- ============================================================================

/-- WS-SM SM6.C: the cross-core reply preserves object-store integrity (`invExt`)
on every control path. -/
theorem endpointReplyOnCore_preserves_objects_invExt
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    (endpointReplyOnCore replier target msg executingCore st).1.objects.invExt := by
  rcases endpointReplyOnCore_state_eq replier target msg executingCore st with
    hEq | ⟨tcb, st', hLk, hStore, hTail⟩
  · rw [hEq]; exact hObjInv
  · have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st' := by
      rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk]; exact hStore
    have hWake : (wakeThread st' target executingCore).1.objects.invExt :=
      wakeThread_preserves_objects_invExt st' target executingCore
        (storeTcbIpcStateAndMessage_preserves_objects_invExt st st' target .ready (some msg) hObjInv hStore')
    rcases hTail with ⟨_, hEq⟩ | ⟨rid, _, hCons⟩
    · rw [hEq]; exact hWake
    · -- PR #827 #3 fold: the consume is two object-store writes; invExt carries.
      exact SystemState.consumeCallerReply_preserves_objects_invExt _ _ target rid hWake hCons

-- ============================================================================
-- §3  `ipcInvariant` (notification well-formedness) preservation
-- ============================================================================

/-- WS-SM SM6.C: the cross-core reply preserves the IPC `ipcInvariant`.  Mirrors
`endpointReply_preserves_ipcInvariant`, with the cross-core caller wake discharged
through the object-invisibility keystone (the caller is already `.ready` after the
reply store, so `wakeThread` does not disturb any object lookup). -/
theorem endpointReplyOnCore_preserves_ipcInvariant
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (hInv : ipcInvariant st) (hObjInv : st.objects.invExt) :
    ipcInvariant (endpointReplyOnCore replier target msg executingCore st).1 := by
  rcases endpointReplyOnCore_state_eq replier target msg executingCore st with
    hEq | ⟨tcb, st', hLk, hStore, hTail⟩
  · rw [hEq]; exact hInv
  · have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st' := by
      rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk]; exact hStore
    have hInv1 := storeTcbIpcStateAndMessage_preserves_ipcInvariant st st' target .ready (some msg)
      hInv hObjInv hStore'
    have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st' target .ready (some msg)
      hObjInv hStore'
    obtain ⟨tr, hGet, hReady⟩ :=
      storeTcbIpcStateAndMessage_getTcb?_ipcState st st' target .ready (some msg) hObjInv hStore'
    have hWakeInv : ipcInvariant (wakeThread st' target executingCore).1 :=
      fun oid ntfn h => hInv1 oid ntfn
        (by rwa [wakeThread_objects_getElem_eq_of_ready st' target executingCore tr hGet hReady hObjInv1 oid] at h)
    rcases hTail with ⟨_, hEq⟩ | ⟨rid, _, hCons⟩
    · rw [hEq]; exact hWakeInv
    · -- PR #827 #3 fold: the consume touches only a `.reply` and a `.tcb` slot.
      have hWakeObjInv : (wakeThread st' target executingCore).1.objects.invExt :=
        wakeThread_preserves_objects_invExt st' target executingCore hObjInv1
      exact consumeCallerReply_preserves_ipcInvariant _ _ target rid hWakeObjInv hWakeInv hCons

-- ============================================================================
-- §4  SM6.D: per-core passive-server frame for the cross-core reply
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D: `endpointReplyOnCore` frames every core's `passiveServerIdle`
slice, unconditionally over success/failure.  The unblocked caller is woken
`.ready` (allowed); the folded consume rewrites only the caller's `replyObject`
and the reply's `caller` (binding/ipcState-invisible). -/
theorem endpointReplyOnCore_passiveServerIdleFrameOnCore
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (c : CoreId) (hObjInv : st.objects.invExt) :
    passiveServerIdleFrameOnCore st
      (endpointReplyOnCore replier target msg executingCore st).1 c := by
  rcases endpointReplyOnCore_state_eq replier target msg executingCore st with
    hEq | ⟨tcb, st', hLk, hStore, hTail⟩
  · rw [hEq]; exact passiveServerIdleFrameOnCore.refl st
  · have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st' := by
      rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk]; exact hStore
    have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st' target .ready
      (some msg) hObjInv hStore'
    obtain ⟨tr, hTrGet, hTrReady⟩ :=
      storeTcbIpcStateAndMessage_getTcb?_ipcState st st' target .ready (some msg) hObjInv hStore'
    have hFWake : passiveServerIdleFrameOnCore st (wakeThread st' target executingCore).1 c :=
      (storeTcbIpcStateAndMessage_passiveServerIdleFrameOnCore st st' target .ready (some msg)
        (Or.inl (Or.inl rfl)) hObjInv hStore').trans
        (wakeThread_passiveServerIdleFrameOnCore_of_ready st' target executingCore tr
          hTrGet hTrReady hObjInv1)
    rcases hTail with ⟨_, hEq⟩ | ⟨rid, _, hCons⟩
    · rw [hEq]; exact hFWake
    · have hWakeInv : (wakeThread st' target executingCore).1.objects.invExt :=
        wakeThread_preserves_objects_invExt st' target executingCore hObjInv1
      exact hFWake.trans
        (consumeCallerReply_passiveServerIdleFrameOnCore _ _ target rid hWakeInv hCons)

-- ============================================================================
-- §5  SM6.D: cross-core / single-core off-scheduler agreement dichotomy (reply)
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D: agreement dichotomy for the cross-core reply.  Either the
cross-core transition failed (post-state = pre-state), or the single-core
`endpointReply` — instantiated at the **recorded server** `expected` (PR #822
review 6J-lYm: the OnCore primitive accepts any reply-cap holder, but the
delegated reply's *object-level effect* is that of the recorded server's reply,
which is exactly what the single-core gate admits) — succeeds from the same
pre-state and the two post-states agree off-scheduler. -/
theorem endpointReplyOnCore_post_agrees
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    (endpointReplyOnCore replier target msg executingCore st).1 = st ∨
    ∃ expected r1, endpointReply expected target msg st = .ok ((), r1) ∧
      OffSchedulerAgrees r1 (endpointReplyOnCore replier target msg executingCore st).1 := by
  unfold endpointReplyOnCore
  split
  · exact Or.inl rfl
  next hSize =>
    split
    · exact Or.inl rfl
    next hCaps =>
      cases hLk : lookupTcb st target with
      | none => left; rfl
      | some tcb =>
        simp only
        cases hIpc : tcb.ipcState with
        | ready => left; rfl
        | blockedOnSend _ => left; rfl
        | blockedOnReceive _ => left; rfl
        | blockedOnCall _ => left; rfl
        | blockedOnNotification _ => left; rfl
        | blockedOnReply epId rt =>
          simp only
          cases rt with
          | none => left; rfl
          | some expected =>
            simp only
            cases hStore : storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) with
            | error e => left; rfl
            | ok st' =>
              simp only
              have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st' := by
                rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk]; exact hStore
              have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st' target
                .ready (some msg) hObjInv hStore'
              obtain ⟨tr, hTrGet, hTrReady⟩ :=
                storeTcbIpcStateAndMessage_getTcb?_ipcState st st' target .ready (some msg)
                  hObjInv hStore'
              have hRel0 : OffSchedulerAgrees (ensureRunnable st' target)
                  (wakeThread st' target executingCore).1 :=
                (ensureRunnable_offSchedulerAgrees st' target).symm.trans
                  (wakeThread_offSchedulerAgrees_of_ready st' target executingCore tr
                    hTrGet hTrReady hObjInv1)
              cases hRO : tcb.replyObject with
              | none =>
                right
                refine ⟨expected, ensureRunnable st' target, ?_, hRel0⟩
                unfold endpointReply
                simp only [if_neg hSize, if_neg hCaps, hLk, hIpc,
                  if_pos (beq_self_eq_true expected), hStore, hRO]
              | some rid =>
                simp only
                cases hConsOC : SystemState.consumeCallerReply target rid
                    (wakeThread st' target executingCore).1 with
                | error e => left; rfl
                | ok pr =>
                  obtain ⟨⟨⟩, stOC⟩ := pr
                  right
                  have hInvEns : (ensureRunnable st' target).objects.invExt := by
                    rw [ensureRunnable_preserves_objects]; exact hObjInv1
                  have hInvWake : (wakeThread st' target executingCore).1.objects.invExt :=
                    wakeThread_preserves_objects_invExt st' target executingCore hObjInv1
                  obtain ⟨r1, hCons1⟩ :=
                    SystemState.consumeCallerReply_isOk (ensureRunnable st' target) target rid
                  refine ⟨expected, r1, ?_, ?_⟩
                  · unfold endpointReply
                    simp only [if_neg hSize, if_neg hCaps, hLk, hIpc,
                      if_pos (beq_self_eq_true expected), hStore, hRO]
                    exact hCons1
                  · exact consumeCallerReply_offSchedulerAgrees target rid hRel0
                      hInvEns hInvWake hCons1 hConsOC

-- ============================================================================
-- §6  SM6.D: whole-bundle + per-core bundle preservation (cross-core reply)
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (SM6.C closure): the cross-core reply preserves the **whole
twenty-conjunct bundle**, unconditionally over success/failure.  Hypotheses
mirror `endpointReply_preserves_ipcInvariantFull` (the threaded post-state
facts `hWtpmn'`/`hDOV'` stated at the cross-core post-state). -/
theorem endpointReplyOnCore_preserves_ipcInvariantFull
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : waitingThreadsPendingMessageNone
      (endpointReplyOnCore replier target msg executingCore st).1)
    (hDOV' : donationOwnerValid
      (endpointReplyOnCore replier target msg executingCore st).1)
    (hAllBudgetsNone : allTimeoutBudgetsNone st) :
    ipcInvariantFull (endpointReplyOnCore replier target msg executingCore st).1 := by
  have hPsi' : passiveServerIdle (endpointReplyOnCore replier target msg executingCore st).1 :=
    (passiveServerIdle_perCore_bootCore_iff _).mp
      (passiveServerIdle_perCore_of_frameOnCore
        (endpointReplyOnCore_passiveServerIdleFrameOnCore replier target msg executingCore
          st bootCoreId hObjInv)
        ((passiveServerIdle_perCore_bootCore_iff st).mpr hInv.passiveServerIdle))
  rcases endpointReplyOnCore_post_agrees replier target msg executingCore st hObjInv with
    hPre | ⟨expected, r1, hStep1, hAgree⟩
  · rw [hPre]; exact hInv
  · exact ipcInvariantFull_of_getElem_eq hAgree.objects hPsi'
      (endpointReply_preserves_ipcInvariantFull st r1 expected target msg hInv hObjInv
        (waitingThreadsPendingMessageNone_of_getElem_eq
          (fun oid => (hAgree.objects oid).symm) hWtpmn')
        hAllBudgetsNone
        (donationOwnerValid_of_getElem_eq (fun oid => (hAgree.objects oid).symm) hDOV')
        hStep1)

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D flagship (cross-core reply): `endpointReplyOnCore` preserves
**every core's** view of the IPC invariant bundle.  No idle-core assumption. -/
theorem endpointReplyOnCore_preserves_ipcInvariantFull_perCore
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : waitingThreadsPendingMessageNone
      (endpointReplyOnCore replier target msg executingCore st).1)
    (hDOV' : donationOwnerValid
      (endpointReplyOnCore replier target msg executingCore st).1)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (c : CoreId) :
    ipcInvariantFull_perCore (endpointReplyOnCore replier target msg executingCore st).1 c :=
  ipcInvariantFull_perCore_of_full
    (endpointReplyOnCore_preserves_ipcInvariantFull replier target msg executingCore st
      (ipcInvariantFull_of_smp hInv) hObjInv hWtpmn' hDOV' hAllBudgetsNone)
    (passiveServerIdle_perCore_of_frameOnCore
      (endpointReplyOnCore_passiveServerIdleFrameOnCore replier target msg executingCore
        st c hObjInv)
      (hInv c).passiveServerIdle)

-- ============================================================================
-- §7  SM6.D: per-core passive-server frame for the cross-core receive leg
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D: `endpointReceiveDualOnCore` frames every core's
`passiveServerIdle` slice, unconditionally over success/failure.  Rendezvous:
pop the sender + set it `.blockedOnReply` (Call, allowed) or `.ready` (Send,
allowed, then cross-core wake) + complete the receiver `.ready`.  Blocking:
return the receiver's own donation (needs the running receiver `.ready`) +
enqueue + block `.blockedOnReceive` (allowed) + optional stash + per-core
deschedule. -/
theorem endpointReceiveDualOnCore_passiveServerIdleFrameOnCore
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (executingCore : CoreId)
    (st : SystemState) (c : CoreId)
    (hReceiverReady : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        tcb.ipcState = .ready)
    (hObjInv : st.objects.invExt) :
    passiveServerIdleFrameOnCore st
      (endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1 c := by
  unfold endpointReceiveDualOnCore
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact passiveServerIdleFrameOnCore.refl st
  | some ep =>
    simp only
    cases hHead : ep.sendQ.head with
    | some sHead =>
      simp only
      cases hPop : endpointQueuePopHead endpointId false st with
      | error e => simp only; exact passiveServerIdleFrameOnCore.refl st
      | ok popRes =>
        obtain ⟨sender, senderTcb, st1⟩ := popRes
        simp only
        have hObjInvPop : st1.objects.invExt :=
          endpointQueuePopHead_preserves_objects_invExt endpointId false st st1 sender senderTcb
            hObjInv hPop
        have hF1 := endpointQueuePopHead_passiveServerIdleFrameOnCore (c := c) endpointId false
          st st1 sender senderTcb hObjInv hPop
        cases hSIpc : senderTcb.ipcState with
        | blockedOnCall _ =>
          simp only
          cases hStore1 : storeTcbIpcStateAndMessage st1 sender
              (.blockedOnReply endpointId (some receiver)) none with
          | error e => simp only; exact passiveServerIdleFrameOnCore.refl st
          | ok st2 =>
            simp only
            have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt st1 st2 sender _
              none hObjInvPop hStore1
            have hF2 := hF1.trans (storeTcbIpcStateAndMessage_passiveServerIdleFrameOnCore
              (c := c) st1 st2 sender (.blockedOnReply endpointId (some receiver)) none
              (Or.inl (Or.inr (Or.inr ⟨endpointId, some receiver, rfl⟩))) hObjInvPop hStore1)
            cases hRid : replyId with
            | none => simp only; exact passiveServerIdleFrameOnCore.refl st
            | some rid =>
              simp only
              cases hLink : SystemState.linkCallerReply sender rid st2 with
              | error e => simp only; exact passiveServerIdleFrameOnCore.refl st
              | ok lp =>
                obtain ⟨⟨⟩, st3⟩ := lp
                simp only
                have hObjInv3 : st3.objects.invExt :=
                  linkCallerReply_preserves_objects_invExt st2 st3 sender rid hObjInv2 hLink
                have hF3 := hF2.trans
                  (linkCallerReply_passiveServerIdleFrameOnCore st2 st3 sender rid hObjInv2 hLink)
                cases hStore2 : storeTcbIpcStateAndMessage st3 receiver .ready
                    senderTcb.pendingMessage with
                | error e => simp only; exact passiveServerIdleFrameOnCore.refl st
                | ok st4 =>
                  simp only
                  exact hF3.trans (storeTcbIpcStateAndMessage_passiveServerIdleFrameOnCore
                    (c := c) st3 st4 receiver .ready senderTcb.pendingMessage
                    (Or.inl (Or.inl rfl)) hObjInv3 hStore2)
        | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _
        | blockedOnReply _ _ =>
          all_goals
            simp only
            cases hStore1 : storeTcbIpcStateAndMessage st1 sender .ready none with
            | error e => simp only; exact passiveServerIdleFrameOnCore.refl st
            | ok st2 =>
              simp only
              have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt st1 st2 sender
                .ready none hObjInvPop hStore1
              obtain ⟨tr, hTrGet, hTrReady⟩ :=
                storeTcbIpcStateAndMessage_getTcb?_ipcState st1 st2 sender .ready none
                  hObjInvPop hStore1
              have hF2 := hF1.trans (storeTcbIpcStateAndMessage_passiveServerIdleFrameOnCore
                (c := c) st1 st2 sender .ready none (Or.inl (Or.inl rfl)) hObjInvPop hStore1)
              have hF3 := hF2.trans (wakeThread_passiveServerIdleFrameOnCore_of_ready st2 sender
                executingCore tr hTrGet hTrReady hObjInv2)
              have hInvWake : (wakeThread st2 sender executingCore).1.objects.invExt :=
                wakeThread_preserves_objects_invExt st2 sender executingCore hObjInv2
              cases hStore2 : storeTcbIpcStateAndMessage (wakeThread st2 sender executingCore).1
                  receiver .ready senderTcb.pendingMessage with
              | error e => simp only; exact passiveServerIdleFrameOnCore.refl st
              | ok st4 =>
                simp only
                exact hF3.trans (storeTcbIpcStateAndMessage_passiveServerIdleFrameOnCore
                  (c := c) (wakeThread st2 sender executingCore).1 st4 receiver .ready
                  senderTcb.pendingMessage (Or.inl (Or.inl rfl)) hInvWake hStore2)
    | none =>
      simp only
      cases hClean : cleanupPreReceiveDonationChecked st receiver with
      | error e => simp only; exact passiveServerIdleFrameOnCore.refl st
      | ok stClean =>
        simp only
        have hBridge : stClean = cleanupPreReceiveDonation st receiver :=
          (cleanupPreReceiveDonationChecked_ok_eq_cleanup st stClean receiver hClean).symm
        subst hBridge
        have hObjInvClean := cleanupPreReceiveDonation_preserves_objects_invExt st receiver hObjInv
        have hFClean := cleanupPreReceiveDonation_passiveServerIdleFrameOnCore (c := c) st receiver
          hObjInv (fun tcb h => Or.inl (hReceiverReady tcb h))
        cases hEnq : endpointQueueEnqueue endpointId true receiver
            (cleanupPreReceiveDonation st receiver) with
        | error e => simp only; exact passiveServerIdleFrameOnCore.refl st
        | ok st1 =>
          simp only
          have hObjInvEnq : st1.objects.invExt :=
            endpointQueueEnqueue_preserves_objects_invExt endpointId true receiver
              (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hEnq
          have hF1 := hFClean.trans (endpointQueueEnqueue_passiveServerIdleFrameOnCore endpointId
            true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hEnq)
          cases hIpc : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
          | error e => simp only; exact passiveServerIdleFrameOnCore.refl st
          | ok st2 =>
            simp only
            have hObjInv2 : st2.objects.invExt :=
              storeTcbIpcState_preserves_objects_invExt st1 st2 receiver _ hObjInvEnq hIpc
            have hF2 := hF1.trans (storeTcbIpcState_passiveServerIdleFrameOnCore st1 st2 receiver
              (.blockedOnReceive endpointId) (Or.inl (Or.inr (Or.inl ⟨endpointId, Or.inl rfl⟩)))
              hObjInvEnq hIpc)
            cases hGetR : st2.getTcb? receiver with
            | none =>
              simp only
              exact hF2.trans (removeRunnableOnCore_passiveServerIdleFrameOnCore st2 receiver
                executingCore (fun tcb hTcb => by rw [hGetR] at hTcb; cases hTcb))
            | some rTcb =>
              simp only
              split
              · next hValid =>
                cases hStash : storeObject receiver.toObjId
                    (.tcb { rTcb with pendingReceiveReply := replyId }) st2 with
                | error e => simp only; exact passiveServerIdleFrameOnCore.refl st
                | ok pStash =>
                  obtain ⟨⟨⟩, stStashed⟩ := pStash
                  simp only
                  have hRecvObj := (getTcb?_eq_some_iff st2 receiver rTcb).mp hGetR
                  have hRTcbIpc : rTcb.ipcState = .blockedOnReceive endpointId :=
                    storeTcbIpcState_ipcState_eq st1 st2 receiver _ hObjInvEnq hIpc rTcb hRecvObj
                  have hF3 := hF2.trans (storeObject_modifiedTcb_passiveServerIdleFrameOnCore st2
                    stStashed receiver.toObjId rTcb { rTcb with pendingReceiveReply := replyId }
                    hRecvObj rfl
                    (Or.inl (by rw [show ({ rTcb with pendingReceiveReply := replyId } : TCB).ipcState
                      = .blockedOnReceive endpointId from hRTcbIpc]
                                exact Or.inr (Or.inl ⟨endpointId, Or.inl rfl⟩)))
                    hObjInv2 hStash)
                  have hStashObj := storeObject_objects_eq st2 stStashed receiver.toObjId
                    (.tcb { rTcb with pendingReceiveReply := replyId }) hObjInv2 hStash
                  exact hF3.trans (removeRunnableOnCore_passiveServerIdleFrameOnCore stStashed
                    receiver executingCore (fun tcb hTcb => Or.inr (by
                      have hTcbRaw := (getTcb?_eq_some_iff stStashed receiver tcb).mp hTcb
                      rw [hStashObj] at hTcbRaw
                      obtain rfl := KernelObject.tcb.inj (Option.some.inj hTcbRaw)
                      rw [show ({ rTcb with pendingReceiveReply := replyId } : TCB).ipcState
                        = .blockedOnReceive endpointId from hRTcbIpc]
                      exact Or.inr (Or.inl ⟨endpointId, Or.inl rfl⟩))))
              · exact passiveServerIdleFrameOnCore.refl st

-- ============================================================================
-- §8  SM6.D: cross-core / single-core agreement dichotomy (receive leg)
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D: agreement dichotomy for the cross-core receive leg.  Either
the cross-core transition failed (post-state = pre-state), or the single-core
`endpointReceiveDual` succeeds from the same pre-state with the same rendezvous
thread and the two post-states agree off-scheduler — the Call-rendezvous path
is *identical* (no scheduler step), the Send-rendezvous path diverges in the
sender wake (`wakeThread` vs `ensureRunnable`, lookup-invisible on the
just-stored `.ready` sender), and the block path diverges in the final
per-core deschedule.  Both spines read the stash guard `replyStashValid` at
the *same* input state, so the representation-dependent fold never needs
cross-state alignment. -/
theorem endpointReceiveDualOnCore_post_agrees
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    (endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1 = st ∨
    ∃ sender r1, endpointReceiveDual endpointId receiver replyId st = .ok (sender, r1) ∧
      OffSchedulerAgrees r1
        (endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1 := by
  unfold endpointReceiveDualOnCore
  cases hEp : st.getEndpoint? endpointId with
  | none => left; simp only; split <;> rfl
  | some ep =>
    have hEpRaw : st.objects[endpointId]? = some (.endpoint ep) :=
      (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mp hEp
    simp only
    cases hHead : ep.sendQ.head with
    | some sHead =>
      simp only
      cases hPop : endpointQueuePopHead endpointId false st with
      | error e => left; rfl
      | ok popRes =>
        obtain ⟨sender, senderTcb, st1⟩ := popRes
        simp only
        cases hSIpc : senderTcb.ipcState with
        | blockedOnCall _ =>
          simp only
          cases hStore1 : storeTcbIpcStateAndMessage st1 sender
              (.blockedOnReply endpointId (some receiver)) none with
          | error e => left; rfl
          | ok st2 =>
            simp only
            cases hRid : replyId with
            | none => left; rfl
            | some rid =>
              simp only
              cases hLink : SystemState.linkCallerReply sender rid st2 with
              | error e => left; rfl
              | ok lp =>
                obtain ⟨⟨⟩, st3⟩ := lp
                simp only
                cases hStore2 : storeTcbIpcStateAndMessage st3 receiver .ready
                    senderTcb.pendingMessage with
                | error e => left; rfl
                | ok st4 =>
                  right
                  refine ⟨sender, st4, ?_, OffSchedulerAgrees.refl st4⟩
                  unfold endpointReceiveDual
                  simp only [hEpRaw, hHead, hPop, hSIpc, hStore1, hLink, hStore2, ↓reduceIte]
        | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _
        | blockedOnReply _ _ =>
          all_goals
            simp only
            cases hStore1 : storeTcbIpcStateAndMessage st1 sender .ready none with
            | error e => left; rfl
            | ok st2 =>
              simp only
              cases hStore2 : storeTcbIpcStateAndMessage (wakeThread st2 sender executingCore).1
                  receiver .ready senderTcb.pendingMessage with
              | error e => left; rfl
              | ok st4OC =>
                right
                have hObjInvPop : st1.objects.invExt :=
                  endpointQueuePopHead_preserves_objects_invExt endpointId false st st1 sender
                    senderTcb hObjInv hPop
                have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt st1 st2
                  sender .ready none hObjInvPop hStore1
                obtain ⟨tr, hTrGet, hTrReady⟩ :=
                  storeTcbIpcStateAndMessage_getTcb?_ipcState st1 st2 sender .ready none
                    hObjInvPop hStore1
                have hRel0 : OffSchedulerAgrees (ensureRunnable st2 sender)
                    (wakeThread st2 sender executingCore).1 :=
                  (ensureRunnable_offSchedulerAgrees st2 sender).symm.trans
                    (wakeThread_offSchedulerAgrees_of_ready st2 sender executingCore tr
                      hTrGet hTrReady hObjInv2)
                have hInvEns : (ensureRunnable st2 sender).objects.invExt := by
                  rw [ensureRunnable_preserves_objects]; exact hObjInv2
                have hInvWake : (wakeThread st2 sender executingCore).1.objects.invExt :=
                  wakeThread_preserves_objects_invExt st2 sender executingCore hObjInv2
                obtain ⟨st4SC, hStore2SC, hAgree4⟩ :=
                  storeTcbIpcStateAndMessage_offSchedulerAgrees receiver .ready
                    senderTcb.pendingMessage hRel0 hInvEns hInvWake hStore2
                refine ⟨sender, st4SC, ?_, hAgree4⟩
                unfold endpointReceiveDual
                simp only [hEpRaw, hHead, hPop, hSIpc, if_neg Bool.false_ne_true,
                  hStore1, hStore2SC]
    | none =>
      simp only
      cases hClean : cleanupPreReceiveDonationChecked st receiver with
      | error e => left; rfl
      | ok stClean =>
        simp only
        cases hEnq : endpointQueueEnqueue endpointId true receiver stClean with
        | error e => left; rfl
        | ok st1 =>
          simp only
          cases hStore1 : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
          | error e => left; rfl
          | ok st2 =>
            simp only
            cases hGetR : st2.getTcb? receiver with
            | none =>
              right
              refine ⟨receiver, removeRunnable st2 receiver, ?_, ?_⟩
              · unfold endpointReceiveDual
                simp only [hEpRaw, hHead, hClean, hEnq, hStore1, hGetR]
              · exact (removeRunnable_offSchedulerAgrees st2 receiver).symm.trans
                  (removeRunnableOnCore_offSchedulerAgrees st2 receiver executingCore)
            | some rTcb =>
              simp only
              split
              · next hValid =>
                cases hStash : storeObject receiver.toObjId
                    (.tcb { rTcb with pendingReceiveReply := replyId }) st2 with
                | error e => left; rfl
                | ok pStash =>
                  obtain ⟨⟨⟩, stStashed⟩ := pStash
                  right
                  refine ⟨receiver, removeRunnable stStashed receiver, ?_, ?_⟩
                  · unfold endpointReceiveDual
                    simp only [hEpRaw, hHead, hClean, hEnq, hStore1, hGetR, if_pos hValid, hStash]
                  · exact (removeRunnable_offSchedulerAgrees stStashed receiver).symm.trans
                      (removeRunnableOnCore_offSchedulerAgrees stStashed receiver executingCore)
              · left; rfl

-- ============================================================================
-- §9  SM6.D: whole-bundle + per-core bundle preservation (cross-core receive)
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (SM6.C closure): the cross-core receive leg preserves the
**whole twenty-conjunct bundle**, unconditionally over success/failure.
Hypotheses mirror `endpointReceiveDual_preserves_ipcInvariantFull`, with TCB
lookups routed through the typed `getTcb?` and the threaded post-state facts
stated at the cross-core post-state. -/
theorem endpointReceiveDualOnCore_preserves_ipcInvariantFull
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (executingCore : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : waitingThreadsPendingMessageNone
      (endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1)
    (hRCLRecip' : replyCallerLinkageReciprocal
      (endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
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
          ep'.sendQ.tail ≠ some tailTid))
    (hReplyIdValid : ∀ rid, replyId = some rid → replyIdEstablishFresh st rid)
    (hReceiverNotRecv : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hReceiverReady : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        tcb.ipcState = .ready) :
    ipcInvariantFull
      (endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1 := by
  have hPsi' : passiveServerIdle
      (endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1 :=
    (passiveServerIdle_perCore_bootCore_iff _).mp
      (passiveServerIdle_perCore_of_frameOnCore
        (endpointReceiveDualOnCore_passiveServerIdleFrameOnCore endpointId receiver replyId
          executingCore st bootCoreId hReceiverReady hObjInv)
        ((passiveServerIdle_perCore_bootCore_iff st).mpr hInv.passiveServerIdle))
  rcases endpointReceiveDualOnCore_post_agrees endpointId receiver replyId executingCore st
    hObjInv with hPre | ⟨sender, r1, hStep1, hAgree⟩
  · rw [hPre]; exact hInv
  · exact ipcInvariantFull_of_getElem_eq hAgree.objects hPsi'
      (endpointReceiveDual_preserves_ipcInvariantFull endpointId receiver sender replyId st r1
        hInv hObjInv
        (waitingThreadsPendingMessageNone_of_getElem_eq
          (fun oid => (hAgree.objects oid).symm) hWtpmn')
        hAllBudgetsNone
        (replyCallerLinkageReciprocal_of_getElem_eq
          (fun oid => (hAgree.objects oid).symm) hRCLRecip')
        hFreshReceiver hRecvTailFresh hReplyIdValid hReceiverNotRecv
        (fun tcb hRaw => hReceiverReady tcb ((getTcb?_eq_some_iff st receiver tcb).mpr hRaw))
        hStep1)

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D flagship (cross-core receive): `endpointReceiveDualOnCore`
preserves **every core's** view of the IPC invariant bundle.  No idle-core
assumption. -/
theorem endpointReceiveDualOnCore_preserves_ipcInvariantFull_perCore
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (executingCore : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : waitingThreadsPendingMessageNone
      (endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1)
    (hRCLRecip' : replyCallerLinkageReciprocal
      (endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
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
          ep'.sendQ.tail ≠ some tailTid))
    (hReplyIdValid : ∀ rid, replyId = some rid → replyIdEstablishFresh st rid)
    (hReceiverNotRecv : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hReceiverReady : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        tcb.ipcState = .ready)
    (c : CoreId) :
    ipcInvariantFull_perCore
      (endpointReceiveDualOnCore endpointId receiver replyId executingCore st).1 c :=
  ipcInvariantFull_perCore_of_full
    (endpointReceiveDualOnCore_preserves_ipcInvariantFull endpointId receiver replyId
      executingCore st (ipcInvariantFull_of_smp hInv) hObjInv hWtpmn' hRCLRecip'
      hAllBudgetsNone hFreshReceiver hRecvTailFresh hReplyIdValid hReceiverNotRecv
      hReceiverReady)
    (passiveServerIdle_perCore_of_frameOnCore
      (endpointReceiveDualOnCore_passiveServerIdleFrameOnCore endpointId receiver replyId
        executingCore st c hReceiverReady hObjInv)
      (hInv c).passiveServerIdle)

-- ============================================================================
-- §10  SM6.D: reply-leg effect characterisations (composite transports)
-- ============================================================================
--
-- The composed `endpointReplyRecvOnCore` is closed *compositionally* through
-- its two legs (the stash guard `replyStashValid` reads a representation-
-- dependent `objects.fold`, so a monolithic dichotomy against the single-core
-- `endpointReplyRecv` would need cross-state fold alignment; the leg-wise
-- composition reads each fold at its own input state).  These lemmas
-- transport the receive leg's pre-state facts across the reply leg.

open SeLe4n.Model.SystemState in
/-- SM6.D transport helper: a post-`storeTcbIpcStateAndMessage` TCB lookup
pulls back to a pre-state TCB agreeing on `pendingReceiveReply` and
`timeoutBudget`, and either identical or rewritten to the stored `ipcState`. -/
theorem storeTcbIpcStateAndMessage_tcb_backward_fields
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    ∀ (s : SeLe4n.ObjId) (tx : TCB), st'.objects[s]? = some (.tcb tx) →
      ∃ ty, st.objects[s]? = some (.tcb ty) ∧
        tx.pendingReceiveReply = ty.pendingReceiveReply ∧
        tx.timeoutBudget = ty.timeoutBudget ∧
        (tx = ty ∨ tx.ipcState = ipc) := by
  intro s tx hObj
  unfold storeTcbIpcStateAndMessage at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId
        (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      obtain ⟨⟨⟩, st''⟩ := pair
      simp only [hStore, Except.ok.injEq] at hStep
      subst hStep
      by_cases hs : s = tid.toObjId
      · subst hs
        rw [storeObject_objects_eq st st'' tid.toObjId _ hObjInv hStore] at hObj
        obtain rfl := KernelObject.tcb.inj (Option.some.inj hObj)
        exact ⟨tcb, lookupTcb_some_objects st tid tcb hLookup, rfl, rfl, Or.inr rfl⟩
      · rw [storeObject_objects_ne st st'' tid.toObjId s _ hs hObjInv hStore] at hObj
        exact ⟨tx, hObj, rfl, rfl, Or.inl rfl⟩

open SeLe4n.Model.SystemState in
/-- SM6.D transport helper: a post-`consumeCallerReply` TCB lookup pulls back
to a pre-state TCB agreeing on `ipcState`, `pendingMessage`,
`pendingReceiveReply`, and `timeoutBudget` (the consume's only TCB write is
the caller's `replyObject := none`). -/
theorem consumeCallerReply_tcb_fields_backward
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hStep : SystemState.consumeCallerReply caller rid st = .ok ((), st')) :
    ∀ (s : SeLe4n.ObjId) (tx : TCB), st'.objects[s]? = some (.tcb tx) →
      ∃ ty, st.objects[s]? = some (.tcb ty) ∧
        tx.ipcState = ty.ipcState ∧ tx.pendingMessage = ty.pendingMessage ∧
        tx.pendingReceiveReply = ty.pendingReceiveReply ∧
        tx.timeoutBudget = ty.timeoutBudget := by
  intro s tx hObj
  unfold SystemState.consumeCallerReply at hStep
  cases hCons : consumeReply rid st with
  | error e => simp [hCons] at hStep
  | ok p1 =>
    obtain ⟨⟨⟩, st1⟩ := p1
    simp only [hCons] at hStep
    have hObjInv1 : st1.objects.invExt :=
      consumeReply_preserves_objects_invExt st st1 rid hObjInv hCons
    have hLeg2 : ∃ t1, st1.objects[s]? = some (.tcb t1) ∧
        tx.ipcState = t1.ipcState ∧ tx.pendingMessage = t1.pendingMessage ∧
        tx.pendingReceiveReply = t1.pendingReceiveReply ∧
        tx.timeoutBudget = t1.timeoutBudget := by
      cases hT : st1.getTcb? caller with
      | none =>
        simp only [hT, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
        rw [hStep]
        exact ⟨tx, hObj, rfl, rfl, rfl, rfl⟩
      | some tcb =>
        simp only [hT] at hStep
        by_cases hs : s = caller.toObjId
        · subst hs
          rw [storeObject_objects_eq st1 st' caller.toObjId _ hObjInv1 hStep] at hObj
          obtain rfl := KernelObject.tcb.inj (Option.some.inj hObj)
          exact ⟨tcb, (getTcb?_eq_some_iff st1 caller tcb).mp hT, rfl, rfl, rfl, rfl⟩
        · rw [storeObject_objects_ne st1 st' caller.toObjId s _ hs hObjInv1 hStep] at hObj
          exact ⟨tx, hObj, rfl, rfl, rfl, rfl⟩
    obtain ⟨t1, hT1, hEq1, hEq2, hEq3, hEq4⟩ := hLeg2
    unfold consumeReply at hCons
    cases hGet : st.getReply? rid with
    | none => rw [hGet] at hCons; cases hCons; exact ⟨t1, hT1, hEq1, hEq2, hEq3, hEq4⟩
    | some r =>
      rw [hGet] at hCons
      by_cases hs : s = rid.toObjId
      · subst hs
        rw [storeObject_objects_eq st st1 rid.toObjId _ hObjInv hCons] at hT1
        cases hT1
      · rw [storeObject_objects_ne st st1 rid.toObjId s _ hs hObjInv hCons] at hT1
        exact ⟨t1, hT1, hEq1, hEq2, hEq3, hEq4⟩

open SeLe4n.Model.SystemState in
/-- SM6.D transport (T1): every TCB observable after `endpointReplyOnCore`
pulls back to a pre-state TCB agreeing on `pendingReceiveReply` and
`timeoutBudget`, and is either woken `.ready` or agrees on
`ipcState`/`pendingMessage` too.  This is the lever that carries the receive
leg's thread-shaped pre-state facts (`hReceiverReady`, `hReceiverNotRecv`,
`allTimeoutBudgetsNone`, `waitingThreadsPendingMessageNone`, the stash
clause of `replyIdEstablishFresh`) across the reply leg. -/
theorem endpointReplyOnCore_tcb_backward
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB),
      (endpointReplyOnCore replier target msg executingCore st).1.getTcb? tid = some tcb' →
      ∃ tcb, st.getTcb? tid = some tcb ∧
        tcb'.pendingReceiveReply = tcb.pendingReceiveReply ∧
        tcb'.timeoutBudget = tcb.timeoutBudget ∧
        (tcb'.ipcState = .ready ∨
          (tcb'.ipcState = tcb.ipcState ∧ tcb'.pendingMessage = tcb.pendingMessage)) := by
  intro tid tcb' hTcb'
  rcases endpointReplyOnCore_state_eq replier target msg executingCore st with
    hEq | ⟨tcb, st', hLk, hStore, hTail⟩
  · rw [hEq] at hTcb'
    exact ⟨tcb', hTcb', rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩
  · have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st' := by
      rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk]; exact hStore
    have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st' target .ready
      (some msg) hObjInv hStore'
    obtain ⟨tr, hTrGet, hTrReady⟩ :=
      storeTcbIpcStateAndMessage_getTcb?_ipcState st st' target .ready (some msg) hObjInv hStore'
    have hWakeEq : ∀ oid : SeLe4n.ObjId,
        (wakeThread st' target executingCore).1.objects[oid]? = st'.objects[oid]? :=
      fun oid => wakeThread_objects_getElem_eq_of_ready st' target executingCore tr
        hTrGet hTrReady hObjInv1 oid
    rcases hTail with ⟨_, hPostEq⟩ | ⟨rid, _, hCons⟩
    · rw [hPostEq] at hTcb'
      have hRaw' := (getTcb?_eq_some_iff _ tid tcb').mp hTcb'
      rw [hWakeEq] at hRaw'
      obtain ⟨ty, hty, hStash, hBudget, hDisj⟩ :=
        storeTcbIpcStateAndMessage_tcb_backward_fields st st' target .ready (some msg)
          hObjInv hStore' tid.toObjId tcb' hRaw'
      refine ⟨ty, (getTcb?_eq_some_iff st tid ty).mpr hty, hStash, hBudget, ?_⟩
      rcases hDisj with rfl | hReady
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl hReady
    · have hInvWake : (wakeThread st' target executingCore).1.objects.invExt :=
        wakeThread_preserves_objects_invExt st' target executingCore hObjInv1
      have hRaw' := (getTcb?_eq_some_iff _ tid tcb').mp hTcb'
      obtain ⟨t1, hT1, hIpc1, hPend1, hStash1, hBudget1⟩ :=
        consumeCallerReply_tcb_fields_backward _ _ target rid hInvWake hCons tid.toObjId tcb' hRaw'
      rw [hWakeEq] at hT1
      obtain ⟨ty, hty, hStash, hBudget, hDisj⟩ :=
        storeTcbIpcStateAndMessage_tcb_backward_fields st st' target .ready (some msg)
          hObjInv hStore' tid.toObjId t1 hT1
      refine ⟨ty, (getTcb?_eq_some_iff st tid ty).mpr hty, hStash1.trans hStash,
        hBudget1.trans hBudget, ?_⟩
      rcases hDisj with rfl | hReady
      · exact Or.inr ⟨hIpc1, hPend1⟩
      · exact Or.inl (hIpc1.trans hReady)

open SeLe4n.Model.SystemState in
/-- SM6.D transport (T2): every endpoint observable after
`endpointReplyOnCore` was the *same* endpoint in the pre-state — the reply
leg's writes land only on TCB and Reply slots.  Carries the receive leg's
endpoint-shaped freshness facts (`hFreshReceiver`, `hRecvTailFresh`) across
the reply leg. -/
theorem endpointReplyOnCore_endpoint_backward
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    ∀ (oid : SeLe4n.ObjId) (ep : Endpoint),
      (endpointReplyOnCore replier target msg executingCore st).1.objects[oid]?
        = some (.endpoint ep) →
      st.objects[oid]? = some (.endpoint ep) := by
  intro oid ep hEp
  rcases endpointReplyOnCore_state_eq replier target msg executingCore st with
    hEq | ⟨tcb, st', hLk, hStore, hTail⟩
  · rw [hEq] at hEp; exact hEp
  · have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st' := by
      rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk]; exact hStore
    have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st' target .ready
      (some msg) hObjInv hStore'
    obtain ⟨tr, hTrGet, hTrReady⟩ :=
      storeTcbIpcStateAndMessage_getTcb?_ipcState st st' target .ready (some msg) hObjInv hStore'
    have hWakeEq : ∀ oid : SeLe4n.ObjId,
        (wakeThread st' target executingCore).1.objects[oid]? = st'.objects[oid]? :=
      fun oid => wakeThread_objects_getElem_eq_of_ready st' target executingCore tr
        hTrGet hTrReady hObjInv1 oid
    rcases hTail with ⟨_, hPostEq⟩ | ⟨rid, _, hCons⟩
    · rw [hPostEq, hWakeEq] at hEp
      exact storeTcbIpcStateAndMessage_endpoint_backward st st' target .ready (some msg)
        oid ep hObjInv hStore' hEp
    · have hInvWake : (wakeThread st' target executingCore).1.objects.invExt :=
        wakeThread_preserves_objects_invExt st' target executingCore hObjInv1
      have hEpWake := (SystemState.consumeCallerReply_nonTcbNonReply_agree _ _ target rid
        hInvWake hCons oid (.endpoint ep) (fun _ => by simp) (fun _ => by simp)).mp hEp
      rw [hWakeEq] at hEpWake
      exact storeTcbIpcStateAndMessage_endpoint_backward st st' target .ready (some msg)
        oid ep hObjInv hStore' hEpWake

open SeLe4n.Model.SystemState in
/-- SM6.D transport (T3): the reply leg preserves `replyIdEstablishFresh` —
the reply store rewrites only the woken caller (stash-invisible), the wake is
lookup-invisible, and the folded consume can only *free* a reply. -/
theorem endpointReplyOnCore_preserves_replyIdEstablishFresh
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hFresh : replyIdEstablishFresh st rid) :
    replyIdEstablishFresh (endpointReplyOnCore replier target msg executingCore st).1 rid := by
  rcases endpointReplyOnCore_state_eq replier target msg executingCore st with
    hEq | ⟨tcb, st', hLk, hStore, hTail⟩
  · rw [hEq]; exact hFresh
  · have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st' := by
      rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk]; exact hStore
    have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st' target .ready
      (some msg) hObjInv hStore'
    obtain ⟨tr, hTrGet, hTrReady⟩ :=
      storeTcbIpcStateAndMessage_getTcb?_ipcState st st' target .ready (some msg) hObjInv hStore'
    have hWakeEq : ∀ oid : SeLe4n.ObjId,
        (wakeThread st' target executingCore).1.objects[oid]? = st'.objects[oid]? :=
      fun oid => wakeThread_objects_getElem_eq_of_ready st' target executingCore tr
        hTrGet hTrReady hObjInv1 oid
    have hFresh' := storeTcbIpcStateAndMessage_preserves_replyIdEstablishFresh st st' target
      .ready (some msg) rid hObjInv hFresh hStore'
    have hFreshW : replyIdEstablishFresh (wakeThread st' target executingCore).1 rid := by
      obtain ⟨⟨r, hr, hrc⟩, hUn⟩ := hFresh'
      refine ⟨⟨r, ?_, hrc⟩, ?_⟩
      · rw [getReply?_eq_some_iff] at hr ⊢; rw [hWakeEq]; exact hr
      · intro t tcb0 hT hS
        rw [getTcb?_eq_some_iff, hWakeEq] at hT
        exact hUn t tcb0 ((getTcb?_eq_some_iff st' t tcb0).mpr hT) hS
    rcases hTail with ⟨_, hPostEq⟩ | ⟨rid', _, hCons⟩
    · rw [hPostEq]; exact hFreshW
    · have hInvWake : (wakeThread st' target executingCore).1.objects.invExt :=
        wakeThread_preserves_objects_invExt st' target executingCore hObjInv1
      exact consumeCallerReply_preserves_replyIdEstablishFresh _ _ target rid' rid
        hInvWake hFreshW hCons

open SeLe4n.Model.SystemState in
/-- SM6.D transport (T4, seL4-MCS one-object reuse): a *successful* reply that
consumed the answered caller's reply object `rid` leaves `rid`
establish-fresh in its post-state — the folded consume freed it
(`caller := none`), no thread stashed it before (and stashes are
reply-leg-invariant), so the server may immediately re-supply the same object
for its next caller on the receive leg. -/
theorem endpointReplyOnCore_reuse_freshens
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st st1 : SystemState) (rid : SeLe4n.ReplyId)
    (sgi? : Option (CoreId × SgiKind))
    (hObjInv : st.objects.invExt)
    (hUnstashed : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB), st.getTcb? tid = some tcb →
        tcb.pendingReceiveReply ≠ some rid)
    (r : SeLe4n.Kernel.Reply) (hGetR : st.getReply? rid = some r)
    (tcbT : TCB) (hTcbT : st.getTcb? target = some tcbT) (hRO : tcbT.replyObject = some rid)
    (hStep : endpointReplyOnCore replier target msg executingCore st = (st1, .ok sgi?)) :
    replyIdEstablishFresh st1 rid := by
  have hPost1 : (endpointReplyOnCore replier target msg executingCore st).1 = st1 := by
    rw [hStep]
  -- Stash clause via the T1 backward transport (spine-free).
  have hStashClause : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB), st1.getTcb? tid = some tcb →
      tcb.pendingReceiveReply ≠ some rid := by
    intro tid t hT hS
    obtain ⟨ty, hty, hStash, _, _⟩ := endpointReplyOnCore_tcb_backward replier target msg
      executingCore st hObjInv tid t (hPost1 ▸ hT)
    exact hUnstashed tid ty hty (hStash.symm.trans hS)
  refine ⟨?_, hStashClause⟩
  -- Present + free via the success spine: the consume ran on exactly `rid`.
  unfold endpointReplyOnCore at hStep
  split at hStep
  · simp at hStep
  split at hStep
  · simp at hStep
  cases hLk : lookupTcb st target with
  | none => simp only [hLk] at hStep; simp at hStep
  | some tcb =>
    simp only [hLk] at hStep
    have hRawT := lookupTcb_some_objects st target tcb hLk
    have hRawT2 := (getTcb?_eq_some_iff st target tcbT).mp hTcbT
    obtain rfl : tcb = tcbT := by
      rw [hRawT] at hRawT2
      exact KernelObject.tcb.inj (Option.some.inj hRawT2)
    cases hIpc : tcb.ipcState with
    | ready => simp only [hIpc] at hStep; simp at hStep
    | blockedOnSend _ => simp only [hIpc] at hStep; simp at hStep
    | blockedOnReceive _ => simp only [hIpc] at hStep; simp at hStep
    | blockedOnCall _ => simp only [hIpc] at hStep; simp at hStep
    | blockedOnNotification _ => simp only [hIpc] at hStep; simp at hStep
    | blockedOnReply epId rt =>
      simp only [hIpc] at hStep
      cases rt with
      | none => simp at hStep
      | some expected =>
        simp only at hStep
        cases hStore : storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) with
        | error e => simp only [hStore] at hStep; simp at hStep
        | ok st' =>
          simp only [hStore, hRO] at hStep
          cases hCons : SystemState.consumeCallerReply target rid
              (wakeThread st' target executingCore).1 with
          | error e => simp only [hCons] at hStep; simp at hStep
          | ok pr =>
            obtain ⟨⟨⟩, stC⟩ := pr
            simp only [hCons, Prod.mk.injEq] at hStep
            obtain ⟨rfl, _⟩ := hStep
            have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st' := by
              rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk]; exact hStore
            have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st' target
              .ready (some msg) hObjInv hStore'
            obtain ⟨tr, hTrGet, hTrReady⟩ :=
              storeTcbIpcStateAndMessage_getTcb?_ipcState st st' target .ready (some msg)
                hObjInv hStore'
            have hWakeEq : ∀ oid : SeLe4n.ObjId,
                (wakeThread st' target executingCore).1.objects[oid]? = st'.objects[oid]? :=
              fun oid => wakeThread_objects_getElem_eq_of_ready st' target executingCore tr
                hTrGet hTrReady hObjInv1 oid
            have hInvWake : (wakeThread st' target executingCore).1.objects.invExt :=
              wakeThread_preserves_objects_invExt st' target executingCore hObjInv1
            have hNeSlot : target.toObjId ≠ rid.toObjId :=
              getTcb?_getReply?_slot_ne st target rid tcb r hTcbT hGetR
            have hRWake : (wakeThread st' target executingCore).1.getReply? rid = some r := by
              rw [getReply?_eq_some_iff]
              rw [hWakeEq, storeTcbIpcStateAndMessage_preserves_objects_ne st st' target .ready
                (some msg) rid.toObjId (fun h => hNeSlot h.symm) hObjInv hStore']
              exact (getReply?_eq_some_iff st rid r).mp hGetR
            exact ⟨{ r with caller := none },
              SystemState.consumeCallerReply_getReply?_caller_none _ target rid r hInvWake
                hRWake stC hCons, rfl⟩

-- ============================================================================
-- §11  SM6.D: the composed cross-core reply-receive (compositional closure)
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D: `endpointReplyRecvOnCore` frames every core's
`passiveServerIdle` slice — the reply-leg frame composed with the receive-leg
frame at the intermediate state (the receiver stays `.ready` across the reply
leg by the T1 backward transport). -/
theorem endpointReplyRecvOnCore_passiveServerIdleFrameOnCore
    (endpointId : SeLe4n.ObjId) (receiver replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage) (replyId : Option SeLe4n.ReplyId) (executingCore : CoreId)
    (st : SystemState) (c : CoreId)
    (hReceiverReady : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        tcb.ipcState = .ready)
    (hObjInv : st.objects.invExt) :
    passiveServerIdleFrameOnCore st
      (endpointReplyRecvOnCore endpointId receiver replyTarget msg replyId
        executingCore st).1 c := by
  unfold endpointReplyRecvOnCore
  cases hR : endpointReplyOnCore receiver replyTarget msg executingCore st with
  | mk st1 res1 =>
    cases res1 with
    | error e => exact passiveServerIdleFrameOnCore.refl st
    | ok sgi1 =>
      simp only
      have hStEq : (endpointReplyOnCore receiver replyTarget msg executingCore st).1 = st1 := by
        rw [hR]
      have hF1 := endpointReplyOnCore_passiveServerIdleFrameOnCore receiver replyTarget msg
        executingCore st c hObjInv
      rw [hStEq] at hF1
      have hObjInv1 := endpointReplyOnCore_preserves_objects_invExt receiver replyTarget msg
        executingCore st hObjInv
      rw [hStEq] at hObjInv1
      have hTcbBwd := endpointReplyOnCore_tcb_backward receiver replyTarget msg
        executingCore st hObjInv
      rw [hStEq] at hTcbBwd
      have hReady1 : ∀ (tcb : TCB), st1.getTcb? receiver = some tcb →
          tcb.ipcState = .ready := by
        intro tcb hT
        obtain ⟨ty, hty, _, _, hDisj⟩ := hTcbBwd receiver tcb hT
        rcases hDisj with hReady | ⟨hIpcEq, _⟩
        · exact hReady
        · rw [hIpcEq]; exact hReceiverReady ty hty
      cases hR2 : endpointReceiveDualOnCore endpointId receiver replyId executingCore st1 with
      | mk st2 res2 =>
        cases res2 with
        | error e => exact passiveServerIdleFrameOnCore.refl st
        | ok pr =>
          simp only
          have hF2 := endpointReceiveDualOnCore_passiveServerIdleFrameOnCore endpointId receiver
            replyId executingCore st1 c hReady1 hObjInv1
          rw [hR2] at hF2
          exact hF1.trans hF2

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (SM6.C closure): the composed cross-core `replyRecv` preserves
the **whole twenty-conjunct bundle**, unconditionally over success/failure —
composed through its two legs, with every receive-leg pre-state fact
transported across the reply leg by the §10 characterisations.  The
`hReplyIdValid` premise is **disjunctive**: the supplied reply object is
either establish-fresh in the pre-state, or it is exactly the answered
caller's in-use reply object (present and nowhere stashed) — the faithful
seL4-MCS *one-object reuse* pattern, which the reply leg's folded consume
frees before the receive leg reads it. -/
theorem endpointReplyRecvOnCore_preserves_ipcInvariantFull
    (endpointId : SeLe4n.ObjId) (receiver replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage) (replyId : Option SeLe4n.ReplyId) (executingCore : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : waitingThreadsPendingMessageNone
      (endpointReplyRecvOnCore endpointId receiver replyTarget msg replyId executingCore st).1)
    (hRCLRecip' : replyCallerLinkageReciprocal
      (endpointReplyRecvOnCore endpointId receiver replyTarget msg replyId executingCore st).1)
    (hDOVMid : donationOwnerValid
      (endpointReplyOnCore receiver replyTarget msg executingCore st).1)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
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
          ep'.sendQ.tail ≠ some tailTid))
    (hReplyIdValid : ∀ rid, replyId = some rid →
        replyIdEstablishFresh st rid ∨
        ((∀ (tid : SeLe4n.ThreadId) (tcb : TCB), st.getTcb? tid = some tcb →
            tcb.pendingReceiveReply ≠ some rid) ∧
         (∃ r, st.getReply? rid = some r) ∧
         ∃ tcbT, st.getTcb? replyTarget = some tcbT ∧ tcbT.replyObject = some rid))
    (hReceiverNotRecv : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hReceiverReady : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        tcb.ipcState = .ready) :
    ipcInvariantFull
      (endpointReplyRecvOnCore endpointId receiver replyTarget msg replyId executingCore st).1 := by
  unfold endpointReplyRecvOnCore at hWtpmn' hRCLRecip' ⊢
  cases hR : endpointReplyOnCore receiver replyTarget msg executingCore st with
  | mk st1 res1 =>
    rw [hR] at hWtpmn' hRCLRecip'
    cases res1 with
    | error e => exact hInv
    | ok sgi1 =>
      simp only at hWtpmn' hRCLRecip' ⊢
      have hStEq : (endpointReplyOnCore receiver replyTarget msg executingCore st).1 = st1 := by
        rw [hR]
      have hObjInv1 := endpointReplyOnCore_preserves_objects_invExt receiver replyTarget msg
        executingCore st hObjInv
      rw [hStEq] at hObjInv1
      have hTcbBwd := endpointReplyOnCore_tcb_backward receiver replyTarget msg
        executingCore st hObjInv
      rw [hStEq] at hTcbBwd
      have hEpBwd := endpointReplyOnCore_endpoint_backward receiver replyTarget msg
        executingCore st hObjInv
      rw [hStEq] at hEpBwd
      have hDOVMid1 : donationOwnerValid st1 := by rw [← hStEq]; exact hDOVMid
      have hWtpmnMid : waitingThreadsPendingMessageNone st1 := by
        intro tid tcb hRaw
        obtain ⟨ty, hty, _, _, hDisj⟩ :=
          hTcbBwd tid tcb ((getTcb?_eq_some_iff st1 tid tcb).mpr hRaw)
        rcases hDisj with hReady | ⟨hIpcEq, hPendEq⟩
        · simp only [hReady]
        · have hPre := hInv.waitingThreadsPendingMessageNone tid ty
            ((getTcb?_eq_some_iff st tid ty).mp hty)
          rw [hIpcEq, hPendEq]
          exact hPre
      have hInv1 : ipcInvariantFull st1 := by
        rw [← hStEq]
        exact endpointReplyOnCore_preserves_ipcInvariantFull receiver replyTarget msg
          executingCore st hInv hObjInv (by rw [hStEq]; exact hWtpmnMid)
          (by rw [hStEq]; exact hDOVMid1) hAllBudgetsNone
      have hBudgets1 : allTimeoutBudgetsNone st1 := by
        intro tid tcb hRaw
        obtain ⟨ty, hty, _, hBudget, _⟩ :=
          hTcbBwd tid tcb ((getTcb?_eq_some_iff st1 tid tcb).mpr hRaw)
        rw [hBudget]
        exact hAllBudgetsNone tid ty ((getTcb?_eq_some_iff st tid ty).mp hty)
      have hReady1 : ∀ (tcb : TCB), st1.getTcb? receiver = some tcb →
          tcb.ipcState = .ready := by
        intro tcb hT
        obtain ⟨ty, hty, _, _, hDisj⟩ := hTcbBwd receiver tcb hT
        rcases hDisj with hReady | ⟨hIpcEq, _⟩
        · exact hReady
        · rw [hIpcEq]; exact hReceiverReady ty hty
      have hNotRecv1 : ∀ (tcb : TCB), st1.getTcb? receiver = some tcb →
          ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep := by
        intro tcb hT ep hBlk
        obtain ⟨ty, hty, _, _, hDisj⟩ := hTcbBwd receiver tcb hT
        rcases hDisj with hReady | ⟨hIpcEq, _⟩
        · rw [hReady] at hBlk; cases hBlk
        · exact hReceiverNotRecv ty hty ep (hIpcEq ▸ hBlk)
      have hFresh1 : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
          st1.objects[epId]? = some (.endpoint ep) →
          ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
          ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver :=
        fun epId ep hEp => hFreshReceiver epId ep (hEpBwd epId ep hEp)
      have hTailFresh1 : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
          st1.objects[endpointId]? = some (.endpoint ep) →
          ep.receiveQ.tail = some tailTid →
          ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
            st1.objects[epId']? = some (.endpoint ep') →
            (epId' ≠ endpointId →
              ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
            (epId' = endpointId →
              ep'.sendQ.tail ≠ some tailTid) :=
        fun ep tailTid hEp hTail epId' ep' hEp' =>
          hRecvTailFresh ep tailTid (hEpBwd endpointId ep hEp) hTail epId' ep'
            (hEpBwd epId' ep' hEp')
      have hReplyIdValid1 : ∀ rid, replyId = some rid → replyIdEstablishFresh st1 rid := by
        intro rid hRid
        rcases hReplyIdValid rid hRid with hFresh | ⟨hUnstashed, ⟨r, hGetR⟩, tcbT, hTcbT, hRO⟩
        · have hT3 := endpointReplyOnCore_preserves_replyIdEstablishFresh receiver replyTarget
            msg executingCore st rid hObjInv hFresh
          rwa [hStEq] at hT3
        · exact endpointReplyOnCore_reuse_freshens receiver replyTarget msg executingCore
            st st1 rid sgi1 hObjInv hUnstashed r hGetR tcbT hTcbT hRO hR
      cases hR2 : endpointReceiveDualOnCore endpointId receiver replyId executingCore st1 with
      | mk st2 res2 =>
        rw [hR2] at hWtpmn' hRCLRecip'
        cases res2 with
        | error e => exact hInv
        | ok pr =>
          simp only at hWtpmn' hRCLRecip' ⊢
          have hStEq2 :
              (endpointReceiveDualOnCore endpointId receiver replyId executingCore st1).1
                = st2 := by
            rw [hR2]
          have hFull2 := endpointReceiveDualOnCore_preserves_ipcInvariantFull endpointId
            receiver replyId executingCore st1 hInv1 hObjInv1
            (by rw [hStEq2]; exact hWtpmn') (by rw [hStEq2]; exact hRCLRecip')
            hBudgets1 hFresh1 hTailFresh1 hReplyIdValid1 hNotRecv1 hReady1
          rwa [hStEq2] at hFull2

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D flagship (cross-core replyRecv): the composed
`endpointReplyRecvOnCore` preserves **every core's** view of the IPC
invariant bundle.  No idle-core assumption. -/
theorem endpointReplyRecvOnCore_preserves_ipcInvariantFull_perCore
    (endpointId : SeLe4n.ObjId) (receiver replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage) (replyId : Option SeLe4n.ReplyId) (executingCore : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : waitingThreadsPendingMessageNone
      (endpointReplyRecvOnCore endpointId receiver replyTarget msg replyId executingCore st).1)
    (hRCLRecip' : replyCallerLinkageReciprocal
      (endpointReplyRecvOnCore endpointId receiver replyTarget msg replyId executingCore st).1)
    (hDOVMid : donationOwnerValid
      (endpointReplyOnCore receiver replyTarget msg executingCore st).1)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
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
          ep'.sendQ.tail ≠ some tailTid))
    (hReplyIdValid : ∀ rid, replyId = some rid →
        replyIdEstablishFresh st rid ∨
        ((∀ (tid : SeLe4n.ThreadId) (tcb : TCB), st.getTcb? tid = some tcb →
            tcb.pendingReceiveReply ≠ some rid) ∧
         (∃ r, st.getReply? rid = some r) ∧
         ∃ tcbT, st.getTcb? replyTarget = some tcbT ∧ tcbT.replyObject = some rid))
    (hReceiverNotRecv : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hReceiverReady : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        tcb.ipcState = .ready)
    (c : CoreId) :
    ipcInvariantFull_perCore
      (endpointReplyRecvOnCore endpointId receiver replyTarget msg replyId executingCore st).1
      c :=
  ipcInvariantFull_perCore_of_full
    (endpointReplyRecvOnCore_preserves_ipcInvariantFull endpointId receiver replyTarget msg
      replyId executingCore st (ipcInvariantFull_of_smp hInv) hObjInv hWtpmn' hRCLRecip'
      hDOVMid hAllBudgetsNone hFreshReceiver hRecvTailFresh hReplyIdValid hReceiverNotRecv
      hReceiverReady)
    (passiveServerIdle_perCore_of_frameOnCore
      (endpointReplyRecvOnCore_passiveServerIdleFrameOnCore endpointId receiver replyTarget
        msg replyId executingCore st c hReceiverReady hObjInv)
      (hInv c).passiveServerIdle)

end SeLe4n.Kernel
