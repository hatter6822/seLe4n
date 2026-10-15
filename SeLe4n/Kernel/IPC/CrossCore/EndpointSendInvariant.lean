-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-RR RR2.14 / RR2.15: PRODUCTION. The invariant surface of the cross-core
-- `Send` — the transition the live `.send` dispatch arm routes through.

import SeLe4n.Kernel.IPC.CrossCore.EndpointSend
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyInvariant
import SeLe4n.Kernel.IPC.Invariant.CapTransferBundle

/-!
# WS-RR RR2.14 / RR2.15 — the live `.send` arm carries an `ipcInvariantFull` bundle

Audit blocker 3: `SeLe4n/Kernel/IPC/CrossCore/EndpointSend.lean` contained **zero**
occurrences of `preserves_ipcInvariantFull`, while its call-side sibling carried
seven — and `endpointSendDualWithCapsOnCore` is what `API.dispatchWithCap`'s
`.send` arm actually calls, since PR #861 round 12 re-routed `.send` at
`v0.33.5`. SM8's registered debt (b) named the gap correctly; SM6.D's scope note
did not, citing `endpointSendDualWithCaps_preserves_ipcInvariantFull_perCore` —
a theorem about the *single-core, boot-pinned* function that stopped being the
live arm at that re-route.

This module closes it, along the shortest sound route rather than by
transcribing the 2805-line call-side invariant module:

* §1 — the **agreement dichotomy** `endpointSendDualOnCore_post_agrees`: either
  the cross-core send failed (post-state = pre-state), or the single-core
  `endpointSendDual` succeeds from the same pre-state and the two post-states
  agree **off-scheduler**. The two transitions run the same pop / store or the
  same enqueue / store and differ only in the final scheduling step —
  `wakeThread` vs `ensureRunnable` (lookup-invisible on the just-stored `.ready`
  receiver) and `removeRunnableOnCore` vs `removeRunnable` (scheduler-only).
  This is the `endpointReceiveDualOnCore_post_agrees` pattern the register's
  remediation note pointed at.
* §2 — the per-core `passiveServerIdle` frame, the one conjunct that reads the
  scheduler and so does *not* transport across an off-scheduler agreement.
* §3 — the bundle itself, and §4 its per-core form, both composed from the
  single-core `endpointSendDual_preserves_ipcInvariantFull` through
  `ipcInvariantFull_of_getElem_eq`.
* §5 — the capability-carrying forms, composing §3/§4 with
  `ipcUnwrapCaps_preserves_ipcInvariantFull` (RR2.14's shared assembly).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1 RR2.14 — cross-core / single-core agreement dichotomy (send leg)
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- WS-RR RR2.14: agreement dichotomy for the cross-core send. Either the
transition failed (the per-core form is fail-closed, so the post-state is the
pre-state), or the single-core `endpointSendDual` succeeds from the same
pre-state and the two post-states agree off-scheduler.

The rendezvous leg diverges only in the receiver wake (`wakeThread` vs
`ensureRunnable`), which is lookup-invisible because `storeTcbReceiveComplete`
has just written the receiver `.ready` and the wake's object write re-inserts
that same value; the block leg diverges only in the final deschedule, which is
a scheduler-only record update. -/
theorem endpointSendDualOnCore_post_agrees
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (payload : SendPayload)
    (executingCore : CoreId) (st : SystemState) (hObjInv : st.objects.invExt) :
    (endpointSendDualOnCore endpointId sender payload executingCore st).1 = st ∨
    ∃ r1, endpointSendDual endpointId sender payload st = .ok ((), r1) ∧
      OffSchedulerAgrees r1 (endpointSendDualOnCore endpointId sender payload executingCore st).1 := by
  unfold endpointSendDualOnCore endpointSendDual SystemState.getObject?
  cases hEp : st.getEndpoint? endpointId with
  | none => left; simp only; split <;> rfl
  | some ep =>
    have hEpRaw : st.objects[endpointId]? = some (.endpoint ep) :=
      (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mp hEp
    simp only [hEpRaw]
    cases hHead : ep.receiveQ.head with
    | some receiver =>
      simp only
      cases hSnd : st.getTcb? sender with
      | none => left; simp only
      | some senderTcb =>
        simp only
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => left; rfl
        | ok popRes =>
          obtain ⟨popped, poppedTcb, st1⟩ := popRes
          simp only
          cases hStore : storeTcbReceiveComplete st1 popped (some (sendPayloadMessage st sender payload)) with
          | error e => left; rfl
          | ok st2 =>
            simp only
            right
            refine ⟨ensureRunnable st2 popped, rfl, ?_⟩
            have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true
              st st1 popped poppedTcb hObjInv hPop
            have hObjInv2 := storeTcbReceiveComplete_preserves_objects_invExt st1 st2 popped
              (some (sendPayloadMessage st sender payload)) hObjInv1 hStore
            obtain ⟨rt, hRtGet, hRtReady⟩ :=
              storeTcbReceiveComplete_getTcb?_ipcState st1 st2 popped (some (sendPayloadMessage st sender payload)) hObjInv1 hStore
            exact (ensureRunnable_offSchedulerAgrees st2 popped).symm.trans
              (wakeThread_offSchedulerAgrees_of_ready st2 popped executingCore rt hRtGet
                hRtReady hObjInv2)
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false sender st with
      | error e => left; rfl
      | ok st1 =>
        simp only
        cases hStore : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId)
            none with
        | error e => left; rfl
        | ok st2 =>
          simp only
          right
          refine ⟨recordSendCap (removeRunnable st2 sender) sender payload.badge payload.grant,
            rfl, ?_⟩
          exact (recordSendCap_offSchedulerAgrees _ _ _ _).symm.trans
            ((removeRunnable_offSchedulerAgrees st2 sender).symm.trans
              ((removeRunnableOnCore_offSchedulerAgrees st2 sender executingCore).trans
                (recordSendCap_offSchedulerAgrees _ _ _ _)))

-- ============================================================================
-- §2 RR2.15 — the per-core `passiveServerIdle` frame
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- WS-RR RR2.15: the cross-core send frames every core's `passiveServerIdle`
reading. Mirrors `endpointSendDual_passiveServerIdleFrameOnCore` step for step,
with the two per-core scheduling steps substituted: the rendezvous wake is
lookup-invisible on the just-stored `.ready` receiver, and the block-path
deschedule only removes the sender from its own core's queue.

The one substantive obligation is the same as the single-core proof's: the
thread the send drives into `.blockedOnSend` — a state `passiveServerIdle`
forbids for an unbound descheduled thread — is the running sender, which holds a
SchedContext (`hSenderNotUnbound`) and is therefore not unbound. -/
theorem endpointSendDualOnCore_passiveServerIdleFrameOnCore
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (payload : SendPayload)
    (executingCore : CoreId) (st : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hSenderNotUnbound : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        tcb.schedContextBinding ≠ .unbound) :
    passiveServerIdleFrameOnCore st
      (endpointSendDualOnCore endpointId sender payload executingCore st).1 c := by
  unfold endpointSendDualOnCore
  cases hEp : st.getEndpoint? endpointId with
  | none =>
    simp only
    split <;> exact passiveServerIdleFrameOnCore.refl st
  | some ep =>
    simp only
    cases hHead : ep.receiveQ.head with
    | some receiver =>
      simp only
      cases hSnd : st.getTcb? sender with
      | none => simp only; exact passiveServerIdleFrameOnCore.refl st
      | some senderTcb =>
        simp only
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp only; exact passiveServerIdleFrameOnCore.refl st
        | ok popRes =>
          obtain ⟨popped, poppedTcb, st1⟩ := popRes
          simp only
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true
            st st1 popped poppedTcb hObjInv hPop
          have hF1 := endpointQueuePopHead_passiveServerIdleFrameOnCore (c := c) endpointId
            true st st1 popped poppedTcb hObjInv hPop
          cases hStore : storeTcbReceiveComplete st1 popped (some (sendPayloadMessage st sender payload)) with
          | error e => simp only; exact passiveServerIdleFrameOnCore.refl st
          | ok st2 =>
            simp only
            have hObjInv2 := storeTcbReceiveComplete_preserves_objects_invExt st1 st2 popped
              (some (sendPayloadMessage st sender payload)) hObjInv1 hStore
            obtain ⟨rt, hRtGet, hRtReady⟩ :=
              storeTcbReceiveComplete_getTcb?_ipcState st1 st2 popped (some (sendPayloadMessage st sender payload)) hObjInv1 hStore
            exact (hF1.trans (storeTcbReceiveComplete_passiveServerIdleFrameOnCore st1 st2
              popped (some (sendPayloadMessage st sender payload)) hObjInv1 hStore)).trans
              (wakeThread_passiveServerIdleFrameOnCore_of_ready st2 popped executingCore rt
                hRtGet hRtReady hObjInv2)
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false sender st with
      | error e => simp only; exact passiveServerIdleFrameOnCore.refl st
      | ok st1 =>
        simp only
        have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false sender
          st st1 hObjInv hEnq
        have hF1 := endpointQueueEnqueue_passiveServerIdleFrameOnCore (c := c) endpointId
          false sender st st1 hObjInv hEnq
        cases hStore : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId)
            none with
        | error e => simp only; exact passiveServerIdleFrameOnCore.refl st
        | ok st2 =>
          simp only
          refine (hF1.trans (storeTcbIpcStateAndMessage_passiveServerIdleFrameOnCore st1 st2
            sender (.blockedOnSend endpointId) none
            (Or.inr (fun tcb hTcb => ?_)) hObjInv1 hStore)).trans
            (removeRunnableOnCore_passiveServerIdleFrameOnCore st2 sender executingCore
              (fun tcb hTcb => Or.inl ?_))
            |>.trans (passiveServerIdleFrameOnCore.of_objectsAgreeOffRunLinks
              (recordSendCap_objectsAgreeOffRunLinks _ _ _ _) (recordSendCap_scheduler _ _ _ _))
          · obtain ⟨tcb0, hTcb0, hBindEq⟩ := endpointQueueEnqueue_sameSchedContextBindings
              endpointId false sender st st1 hObjInv hEnq sender tcb
              ((getTcb?_eq_some_iff st1 sender tcb).mp hTcb)
            exact hBindEq ▸ hSenderNotUnbound tcb0
              ((getTcb?_eq_some_iff st sender tcb0).mpr hTcb0)
          · obtain ⟨tcb1, hTcb1, hBindEq1⟩ := storeTcbIpcStateAndMessage_sameSchedContextBindings
              st1 st2 sender (.blockedOnSend endpointId) none hObjInv1 hStore sender tcb
              ((getTcb?_eq_some_iff st2 sender tcb).mp hTcb)
            obtain ⟨tcb0, hTcb0, hBindEq0⟩ := endpointQueueEnqueue_sameSchedContextBindings
              endpointId false sender st st1 hObjInv hEnq sender tcb1 hTcb1
            exact hBindEq1 ▸ hBindEq0 ▸ hSenderNotUnbound tcb0
              ((getTcb?_eq_some_iff st sender tcb0).mpr hTcb0)

-- ============================================================================
-- §3 RR2.14 — object-store invariant preservation
-- ============================================================================

/-- WS-RR RR2.14: the cross-core send preserves the Robin Hood object-store
invariant. Needed by the capability-carrying form, whose `ipcUnwrapCaps` leg
runs on the send's post-state. -/
theorem endpointSendDualOnCore_preserves_objects_invExt
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (payload : SendPayload)
    (executingCore : CoreId) (st : SystemState) (hObjInv : st.objects.invExt) :
    (endpointSendDualOnCore endpointId sender payload executingCore st).1.objects.invExt := by
  unfold endpointSendDualOnCore
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact hObjInv
  | some ep =>
    simp only
    cases hHead : ep.receiveQ.head with
    | some receiver =>
      simp only
      cases hSnd : st.getTcb? sender with
      | none => simp only; exact hObjInv
      | some senderTcb =>
        simp only
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp only; exact hObjInv
        | ok popRes =>
          obtain ⟨popped, poppedTcb, st1⟩ := popRes
          simp only
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true
            st st1 popped poppedTcb hObjInv hPop
          cases hStore : storeTcbReceiveComplete st1 popped (some (sendPayloadMessage st sender payload)) with
          | error e => simp only; exact hObjInv
          | ok st2 =>
            simp only
            exact wakeThread_preserves_objects_invExt st2 popped executingCore
              (storeTcbReceiveComplete_preserves_objects_invExt st1 st2 popped (some (sendPayloadMessage st sender payload))
                hObjInv1 hStore)
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false sender st with
      | error e => simp only; exact hObjInv
      | ok st1 =>
        simp only
        have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false sender
          st st1 hObjInv hEnq
        cases hStore : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId)
            none with
        | error e => simp only; exact hObjInv
        | ok st2 =>
          simp only
          exact recordSendCap_objects_invExt _ _ _ _ <| removeRunnableOnCore_objects_invExt _ _ _
            (storeTcbIpcStateAndMessage_preserves_objects_invExt st1 st2 sender _ _
              hObjInv1 hStore)

-- ============================================================================
-- §4 RR2.14 — the whole-bundle theorem the live `.send` arm was missing
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- **WS-RR RR2.14 (audit blocker 3)**: the cross-core send preserves the
**whole twenty-conjunct** IPC invariant bundle, unconditionally over
success/failure.

Hypotheses mirror `endpointSendDual_preserves_ipcInvariantFull` exactly, with
the two threaded post-state conjuncts (`blockedThreadsPendingMessageConsistent`,
`replyCallerLinkageReciprocal`) stated at the cross-core post-state — the same
two the single-core theorem threads, and the two WS-RR RR3 is chartered to
de-thread across the whole surface. Nothing new is threaded here.

The proof is the agreement dichotomy plus one scheduler-sensitive conjunct: the
nineteen object-reading conjuncts transport across the off-scheduler agreement
(`ipcInvariantFull_of_getElem_eq`), and `passiveServerIdle` is supplied at the
per-core post-state from §2's frame. -/
theorem endpointSendDualOnCore_preserves_ipcInvariantFull
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (payload : SendPayload)
    (executingCore : CoreId) (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hFreshSender : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some sender ∧ ep.sendQ.tail ≠ some sender ∧
      ep.receiveQ.head ≠ some sender ∧ ep.receiveQ.tail ≠ some sender)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid))
    (hSenderNotRecv : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hSenderNotReply : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt)
    (hSenderNotUnbound : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        tcb.schedContextBinding ≠ .unbound) :
    ipcInvariantFull (endpointSendDualOnCore endpointId sender payload executingCore st).1 := by
  have hSenderNotUnboundT : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
      tcb.schedContextBinding ≠ .unbound := hSenderNotUnbound
  have hPsi' : passiveServerIdle
      (endpointSendDualOnCore endpointId sender payload executingCore st).1 :=
    (passiveServerIdle_perCore_bootCore_iff _).mp
      (passiveServerIdle_perCore_of_frameOnCore
        (endpointSendDualOnCore_passiveServerIdleFrameOnCore endpointId sender payload executingCore
          st bootCoreId hObjInv hSenderNotUnboundT)
        ((passiveServerIdle_perCore_bootCore_iff st).mpr hInv.passiveServerIdle))
  rcases endpointSendDualOnCore_post_agrees endpointId sender payload executingCore st hObjInv with
    hPre | ⟨r1, hStep1, hAgree⟩
  · rw [hPre]; exact hInv
  · exact ipcInvariantFull_of_objectsAgreeOffRunLinks hAgree.objects hPsi'
      (endpointSendDual_preserves_ipcInvariantFull st r1 endpointId sender payload hInv hObjInv
        hAllBudgetsNone
        hFreshSender hSendTailFresh hSenderNotRecv
        (fun tcb hRaw => hSenderNotReply tcb ((getTcb?_eq_some_iff st sender tcb).mpr hRaw))
        (fun tcb hRaw => hSenderNotUnbound tcb ((getTcb?_eq_some_iff st sender tcb).mpr hRaw))
        hStep1)

open SeLe4n.Model.SystemState in
/-- **WS-RR RR2.15**: the per-core form — the cross-core send preserves **every
core's** view of the IPC invariant bundle, with no idle-core assumption. -/
theorem endpointSendDualOnCore_preserves_ipcInvariantFull_perCore
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (payload : SendPayload)
    (executingCore : CoreId) (st : SystemState)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hFreshSender : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some sender ∧ ep.sendQ.tail ≠ some sender ∧
      ep.receiveQ.head ≠ some sender ∧ ep.receiveQ.tail ≠ some sender)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid))
    (hSenderNotRecv : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hSenderNotReply : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt)
    (hSenderNotUnbound : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        tcb.schedContextBinding ≠ .unbound)
    (c : CoreId) :
    ipcInvariantFull_perCore
      (endpointSendDualOnCore endpointId sender payload executingCore st).1 c :=
  ipcInvariantFull_perCore_of_full
    (endpointSendDualOnCore_preserves_ipcInvariantFull endpointId sender payload executingCore st
      (ipcInvariantFull_of_smp hInv) hObjInv hAllBudgetsNone hFreshSender
      hSendTailFresh hSenderNotRecv hSenderNotReply hSenderNotUnbound)
    (passiveServerIdle_perCore_of_frameOnCore
      (endpointSendDualOnCore_passiveServerIdleFrameOnCore endpointId sender payload executingCore
        st c hObjInv
        hSenderNotUnbound)
      (hInv c).passiveServerIdle)

-- ============================================================================
-- §5 RR2.14 / RR2.15 — the capability-carrying live `.send` arm
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- **WS-RR RR2.14 (the live arm)**: `endpointSendDualWithCapsOnCore` — the
transition `API.dispatchWithCap{,Checked}`'s `.send` arm really calls — preserves
the whole IPC invariant bundle.

The composition is the point: §4's bare cross-core bundle, then
`ipcUnwrapCaps_preserves_ipcInvariantFull` on the arm that transfers
capabilities.  WS-ZA ZA4.7: the send carries its capability's badge and grant
right (`SendPayload`); the capabilities it transfers are resolved from the
sender's own CSpace at the rendezvous (`receiveTransferCaps_frame`), so their
badges are valid because the badges at rest there are -- a conjunct of the
bundle itself, not a hypothesis about the syscall's argument. -/
theorem endpointSendDualWithCapsOnCore_preserves_ipcInvariantFull
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (payload : SendPayload)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hFreshSender : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some sender ∧ ep.sendQ.tail ≠ some sender ∧
      ep.receiveQ.head ≠ some sender ∧ ep.receiveQ.tail ≠ some sender)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid))
    (hSenderNotRecv : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hSenderNotReply : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt)
    (hSenderNotUnbound : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        tcb.schedContextBinding ≠ .unbound) :
    ipcInvariantFull
      (endpointSendDualWithCapsOnCore endpointId sender payload
        receiverSlotBase executingCore st).1 := by
  have hBare := endpointSendDualOnCore_preserves_ipcInvariantFull endpointId sender
    payload executingCore st hInv
    hObjInv hAllBudgetsNone hFreshSender hSendTailFresh hSenderNotRecv
    hSenderNotReply hSenderNotUnbound
  have hBareInv := endpointSendDualOnCore_preserves_objects_invExt endpointId sender
    payload executingCore st hObjInv
  unfold endpointSendDualWithCapsOnCore
  cases hSend : endpointSendDualOnCore endpointId sender
      payload executingCore st with
  | mk stSend res =>
    rw [hSend] at hBare hBareInv
    cases res with
    | error e => exact hBare
    | ok sgi =>
      -- WS-ZA ZA4.7: the sender's capabilities are resolved from its own CSpace
      -- at the rendezvous (`receiveTransferCaps_frame`), so their badges are
      -- valid because the badges at rest there are.
      simp only
      repeat' split
      all_goals first
        | exact hBare
        | (rename_i hT
           obtain ⟨stR, caps, hO, hS, hCaps, hOr⟩ := receiveTransferCaps_frame hT
           have hR : ipcInvariantFull stR := ipcInvariantFull_of_objects_scheduler_eq hO hS hBare
           rcases hOr with rfl | hU
           · exact hR
           · exact ipcUnwrapCaps_preserves_ipcInvariantFull _ _ receiverSlotBase _ stR _ _ hR
               (hO ▸ hBareInv) (fun i c hc b hb => hCaps hBare.badgeWellFormed.2 i c hc b hb) hU)

open SeLe4n.Model.SystemState in
/-- WS-RR RR2.14: the capability-carrying cross-core send frames every core's
`passiveServerIdle` reading — §2's frame for the bare send, then the
capability transfer's own (`receiveTransferCaps_frame`, then
`ipcUnwrapCaps_passiveServerIdleFrameOnCore`; the transfer writes no TCB at all). -/
theorem endpointSendDualWithCapsOnCore_passiveServerIdleFrameOnCore
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (payload : SendPayload)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt)
    (hSenderNotUnbound : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        tcb.schedContextBinding ≠ .unbound) :
    passiveServerIdleFrameOnCore st
      (endpointSendDualWithCapsOnCore endpointId sender payload
        receiverSlotBase executingCore st).1 c := by
  have hBare := endpointSendDualOnCore_passiveServerIdleFrameOnCore endpointId sender
    payload executingCore st c hObjInv
    hSenderNotUnbound
  have hBareInv := endpointSendDualOnCore_preserves_objects_invExt endpointId sender
    payload executingCore st hObjInv
  unfold endpointSendDualWithCapsOnCore
  cases hSend : endpointSendDualOnCore endpointId sender
      payload executingCore st with
  | mk stSend res =>
    rw [hSend] at hBare hBareInv
    cases res with
    | error e => exact hBare
    | ok sgi =>
      simp only
      repeat' split
      all_goals first
        | exact hBare
        | (rename_i hT
           obtain ⟨stR, caps, hO, hS, _, hOr⟩ := receiveTransferCaps_frame hT
           have hR : passiveServerIdleFrameOnCore st stR c :=
             hBare.trans (passiveServerIdleFrameOnCore.of_objectsAgreeOffRunLinks
               (fun _ => by rw [hO]) hS)
           rcases hOr with rfl | hU
           · exact hR
           · exact hR.trans (ipcUnwrapCaps_passiveServerIdleFrameOnCore _
               _ receiverSlotBase _ stR _ _ (hO ▸ hBareInv) hU))

open SeLe4n.Model.SystemState in
/-- **WS-RR RR2.15 (the live arm, per core)**: `endpointSendDualWithCapsOnCore`
preserves **every core's** view of the IPC invariant bundle. This is the
theorem SM6.D's scope note claimed and cited the retired single-core function
for; it is now about the function the live `.send` dispatch actually runs. -/
theorem endpointSendDualWithCapsOnCore_preserves_ipcInvariantFull_perCore
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (payload : SendPayload)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hFreshSender : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some sender ∧ ep.sendQ.tail ≠ some sender ∧
      ep.receiveQ.head ≠ some sender ∧ ep.receiveQ.tail ≠ some sender)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid))
    (hSenderNotRecv : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hSenderNotReply : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt)
    (hSenderNotUnbound : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        tcb.schedContextBinding ≠ .unbound)
    (c : CoreId) :
    ipcInvariantFull_perCore
      (endpointSendDualWithCapsOnCore endpointId sender payload
        receiverSlotBase executingCore st).1 c :=
  ipcInvariantFull_perCore_of_full
    (endpointSendDualWithCapsOnCore_preserves_ipcInvariantFull endpointId sender payload
      receiverSlotBase executingCore st
      (ipcInvariantFull_of_smp hInv) hObjInv hAllBudgetsNone
      hFreshSender hSendTailFresh hSenderNotRecv hSenderNotReply hSenderNotUnbound)
    (passiveServerIdle_perCore_of_frameOnCore
      (endpointSendDualWithCapsOnCore_passiveServerIdleFrameOnCore endpointId sender payload
        receiverSlotBase executingCore st c hObjInv
        hSenderNotUnbound)
      (hInv c).passiveServerIdle)

end SeLe4n.Kernel
