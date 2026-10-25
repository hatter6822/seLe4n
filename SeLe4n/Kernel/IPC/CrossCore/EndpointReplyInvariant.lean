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
-- through the cross-core reply stack.  See WS-SM SM6.C.

import SeLe4n.Kernel.IPC.CrossCore.EndpointReply
import SeLe4n.Kernel.IPC.Invariant
import SeLe4n.Kernel.IPC.Invariant.LookupCongruence
import SeLe4n.Kernel.IPC.Invariant.PerCoreBundle
import SeLe4n.Kernel.IPC.Invariant.PerCoreBundlePreservation
import SeLe4n.Kernel.IPC.Invariant.CapTransferBundle

/-!
# WS-SM SM6.C — Cross-core reply IPC-invariant preservation

`endpointReplyOnCore` preserves the kernel's object-store integrity
(`objects.invExt`) and the IPC `ipcInvariant` (notification well-formedness).  The
cross-core reply differs from its single-core form only in the *scheduler*
placement of the woken caller; `ipcInvariant` is **lookup-only** (it reads the
state solely through `objects[·]?`), so the cross-core caller wake (`wakeThread`,
invisible off run-queue links on the already-`.ready` caller — the SM6.A/SM6.B object-
invisibility keystone) cannot disturb it.  The reply store step reuses the
single-core per-step preservation lemmas verbatim.

**WS-SM SM6.D closure** (§4–§10): the two cross-core reply-path legs,
`endpointReplyOnCore` and `endpointReceiveDualOnCore`, preserve the **whole
nineteen-conjunct bundle** and every core's per-core view of it, via the
off-scheduler agreement dichotomy against their single-core counterparts (both
spines run the same object-store sequence and diverge only in scheduler
placement; `endpointReply`'s `replier == expected` gate is discharged by
instantiating the single-core replier at the recorded server, since a delegated
reply cap carries the same object-level effect).  The receive leg's pre-state
facts are transported across the reply leg by the §9 effect characterisations
(TCB backward transport, endpoint-slot invisibility, reply-free/one-object-reuse
freshness), which the live ReplyRecv's preservation theorem
(`endpointReplyRecvOnCore_preserves_ipcInvariantFull`,
`IPC/Invariant/DispatchPayoff.lean`) consumes — for the **global** bundle only:
the live transition has no `ipcInvariantFull_perCore` statement yet (the one
deleted at `v0.36.49` covered a composite no arm ran; `docs/REGISTERED_DEBT.md`
carries the row).  No conjunct reads the scheduler, so nothing rides a
per-core frame through the two legs.
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
    ∨ ∃ tcb st' server pre, lookupTcb st target = some tcb
        ∧ storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) = .ok st'
        ∧ (endpointReplyOnCore replier target msg executingCore st).1
            = pre.unlinkReplyWaiter target server
        ∧ ((tcb.replyObject = none ∧ pre = (wakeThread st' target executingCore).1)
           ∨ ∃ rid, tcb.replyObject = some rid ∧
              removeCallerReplyFrame target rid
                  (wakeThread st' target executingCore).1 = .ok ((), pre)) := by
  unfold endpointReplyOnCore
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
            exact Or.inr ⟨tcb, st', expected, _, hLk, hStore, rfl, Or.inl ⟨hRO, rfl⟩⟩
          | some rid =>
            obtain ⟨stC, hCons⟩ := removeCallerReplyFrame_isOk
              (wakeThread st' target executingCore).1 target rid
            simp only [hCons]
            exact Or.inr ⟨tcb, st', expected, stC, hLk, hStore, rfl, Or.inr ⟨rid, hRO, hCons⟩⟩
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
    hEq | ⟨tcb, st', server, pre, hLk, hStore, hPost, hTail⟩
  · rw [hEq]; exact hObjInv
  · rw [hPost]; refine SystemState.unlinkReplyWaiter_objects_invExt _ _ _ ?_
    have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st' := by
      rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk]; exact hStore
    have hWake : (wakeThread st' target executingCore).1.objects.invExt :=
      wakeThread_preserves_objects_invExt st' target executingCore
        (storeTcbIpcStateAndMessage_preserves_objects_invExt st st' target .ready (some msg) hObjInv hStore')
    rcases hTail with ⟨_, hEq⟩ | ⟨rid, _, hCons⟩
    · rw [hEq]; exact hWake
    · -- PR #827 #3 fold: the consume is two object-store writes; invExt carries.
      exact removeCallerReplyFrame_preserves_objects_invExt _ _ target rid hWake hCons

/-- **WS-RR RR8.12 Cut C2 (`v0.35.162`, frame)**: the reply leg writes **no replenish
queue** on any path.  Its one scheduler write is the woken caller's run-queue insert
(`wakeThread`), and the two object stores around it — the delivery and the reply
frame's removal — leave the scheduler untouched.  The `.replyRecv` footprint's
replenish segment starts after this leg, and this is the frame that licenses it: a
footprint that declared nothing for a leg that migrated would be false. -/
theorem endpointReplyOnCore_replenishQueueOnCore
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (c : CoreId) :
    (endpointReplyOnCore replier target msg executingCore st).1.scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  rcases endpointReplyOnCore_state_eq replier target msg executingCore st with
    hEq | ⟨tcb, st', server, pre, hLk, hStore, hPost, hTail⟩
  · rw [hEq]
  · rw [hPost, SystemState.unlinkReplyWaiter_scheduler]
    have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st' := by
      rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk]; exact hStore
    have hSched : st'.scheduler = st.scheduler :=
      storeTcbIpcStateAndMessage_scheduler_eq st st' target .ready (some msg) hStore'
    have hWake : (wakeThread st' target executingCore).1.scheduler.replenishQueueOnCore c
        = st.scheduler.replenishQueueOnCore c := by
      rw [wakeThread_replenishQueueOnCore, hSched]
    rcases hTail with ⟨_, hEq⟩ | ⟨rid, _, hRem⟩
    · rw [hEq]; exact hWake
    · rw [removeCallerReplyFrame_scheduler_eq _ _ target rid hRem]
      exact hWake

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
    hEq | ⟨tcb, st', server, pre, hLk, hStore, hPost, hTail⟩
  · rw [hEq]; exact hInv
  · rw [hPost]; refine ipcInvariant_of_objectsAgreeOffRunLinks (SystemState.unlinkReplyWaiter_objectsAgreeOffRunLinks pre target server) ?_
    have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st' := by
      rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk]; exact hStore
    have hInv1 := storeTcbIpcStateAndMessage_preserves_ipcInvariant st st' target .ready (some msg)
      hInv hObjInv hStore'
    have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st' target .ready (some msg)
      hObjInv hStore'
    obtain ⟨tr, hGet, hReady⟩ :=
      storeTcbIpcStateAndMessage_getTcb?_ipcState st st' target .ready (some msg) hObjInv hStore'
    have hWakeInv : ipcInvariant (wakeThread st' target executingCore).1 :=
      fun oid ntfn h => hInv1 oid ntfn
        ((wakeThread_objectsAgreeOffRunLinks_of_ready st' target executingCore tr hGet hReady
          hObjInv1).get_notification_iff.mp h)
    rcases hTail with ⟨_, hEq⟩ | ⟨rid, _, hCons⟩
    · rw [hEq]; exact hWakeInv
    · -- PR #827 #3 fold: the consume touches only a `.reply` and a `.tcb` slot.
      have hWakeObjInv : (wakeThread st' target executingCore).1.objects.invExt :=
        wakeThread_preserves_objects_invExt st' target executingCore hObjInv1
      exact removeCallerReplyFrame_preserves_ipcInvariant _ _ target rid hWakeObjInv hWakeInv hCons

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
              refine ⟨expected, ensureRunnable st' target, ?_,
                hRel0.trans (unlinkReplyWaiter_offSchedulerAgrees _ target expected)⟩
              unfold endpointReply
              simp only [if_neg hSize, hLk, hIpc,
                if_pos (beq_self_eq_true expected), hStore, hRO]
            | some rid =>
              simp only
              cases hConsOC : removeCallerReplyFrame target rid
                  (wakeThread st' target executingCore).1 with
              | error e => left; rfl
              | ok pr =>
                obtain ⟨⟨⟩, stOC⟩ := pr
                right
                have hInvEns : (ensureRunnable st' target).objects.invExt := by
                  exact ensureRunnable_objects_invExt _ _ hObjInv1
                have hInvWake : (wakeThread st' target executingCore).1.objects.invExt :=
                  wakeThread_preserves_objects_invExt st' target executingCore hObjInv1
                obtain ⟨r1, hCons1⟩ :=
                  removeCallerReplyFrame_isOk (ensureRunnable st' target) target rid
                refine ⟨expected, r1, ?_, ?_⟩
                · unfold endpointReply
                  simp only [if_neg hSize, hLk, hIpc,
                    if_pos (beq_self_eq_true expected), hStore, hRO]
                  exact hCons1
                · exact (removeCallerReplyFrame_offSchedulerAgrees target rid hRel0
                    hInvEns hInvWake hCons1 hConsOC).trans
                    (unlinkReplyWaiter_offSchedulerAgrees _ target expected)

-- ============================================================================
-- §6  SM6.D: whole-bundle + per-core bundle preservation (cross-core reply)
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- WS-RR RR3.12: the cross-core reply frames the donation-owner side relaxed at the
answered caller — the `post_agrees` lift of `endpointReply_donationOwnerFrameExcept`.
The cross-core substitutions differ from the single-core spine only in scheduler
placement, which this frame does not read. -/
theorem endpointReplyOnCore_donationOwnerFrameExcept
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    donationOwnerFrameExcept st
      (endpointReplyOnCore replier target msg executingCore st).1 target := by
  rcases endpointReplyOnCore_post_agrees replier target msg executingCore st hObjInv with
    hPre | ⟨expected, r1, hStep1, hAgree⟩
  · rw [hPre]; exact donationOwnerFrameExcept.refl st target
  · exact (endpointReply_donationOwnerFrameExcept st r1 expected target msg hObjInv
      hStep1).trans (donationOwnerFrameExcept.of_objectsAgreeOffRunLinks hAgree.objects)

open SeLe4n.Model.SystemState in
/-- WS-RR RR3.12: the cross-core reply writes no `schedContextBinding` — the
`post_agrees` lift of `endpointReply_sameSchedContextBindings`. -/
theorem endpointReplyOnCore_sameSchedContextBindings
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) :
    sameSchedContextBindings st
      (endpointReplyOnCore replier target msg executingCore st).1 := by
  rcases endpointReplyOnCore_post_agrees replier target msg executingCore st hObjInv with
    hPre | ⟨expected, r1, hStep1, hAgree⟩
  · rw [hPre]; exact sameSchedContextBindings.refl st
  · refine (endpointReply_sameSchedContextBindings st r1 expected target msg hObjInv
      hStep1).trans ?_
    exact sameSchedContextBindings.of_objectsAgreeOffRunLinks hAgree.objects

open SeLe4n.Model.SystemState in
/-- WS-RR RR3.12: the cross-core reply establishes the bundle **relaxed at the
answered caller** — the honest unconditional statement about a bare reply, and the
one the composite cross-core dispatch consumes before the donation return upgrades
it.  Reduces to the single-core establisher through the `post_agrees` lever, exactly
as the full-bundle theorem below does. -/
theorem endpointReplyOnCore_preserves_ipcInvariantFullExceptDonationOwner
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hAllBudgetsNone : allTimeoutBudgetsNone st) :
    ipcInvariantFullExceptDonationOwner
      (endpointReplyOnCore replier target msg executingCore st).1 target := by
  rcases endpointReplyOnCore_post_agrees replier target msg executingCore st hObjInv with
    hPre | ⟨expected, r1, hStep1, hAgree⟩
  · rw [hPre]; exact ipcInvariantFullExceptDonationOwner_of_full target hInv
  · exact ipcInvariantFullExceptDonationOwner_of_objectsAgreeOffRunLinks hAgree.objects
      (endpointReply_preserves_ipcInvariantFullExceptDonationOwner st r1 expected target msg
        hInv hObjInv hAllBudgetsNone hStep1)

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (SM6.C closure) / WS-RR RR3.12: the cross-core reply preserves the
**whole nineteen-conjunct bundle**, unconditionally over success/failure, on a reply
whose answered caller donated nothing.  Hypotheses mirror
`endpointReply_preserves_ipcInvariantFull`, `hNoDonationOwnedBy` included: the
threaded post-state `hDOV'` it replaces is false of this transition's own result
whenever the answered call donated, so the theorem asserted nothing there.  The
donating path goes through the relaxed statement above plus the donation return. -/
theorem endpointReplyOnCore_preserves_ipcInvariantFull
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hNoDonationOwnedBy : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB)
      (scId : SeLe4n.SchedContextId),
      st.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.schedContextBinding ≠ .donated scId target)
    (hAllBudgetsNone : allTimeoutBudgetsNone st) :
    ipcInvariantFull (endpointReplyOnCore replier target msg executingCore st).1 := by
  rcases endpointReplyOnCore_post_agrees replier target msg executingCore st hObjInv with
    hPre | ⟨expected, r1, hStep1, hAgree⟩
  · rw [hPre]; exact hInv
  · exact ipcInvariantFull_of_objectsAgreeOffRunLinks hAgree.objects
      (endpointReply_preserves_ipcInvariantFull st r1 expected target msg hInv hObjInv
        hAllBudgetsNone hNoDonationOwnedBy hStep1)

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D flagship (cross-core reply): `endpointReplyOnCore` preserves
**every core's** view of the IPC invariant bundle.  No idle-core assumption. -/
theorem endpointReplyOnCore_preserves_ipcInvariantFull_perCore
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    -- WS-RR RR3.12: replaces the threaded post-state `hDOV'` with the pre-state
    -- condition that makes it derivable.
    (hNoDonationOwnedBy : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB)
      (scId : SeLe4n.SchedContextId),
      st.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.schedContextBinding ≠ .donated scId target)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (c : CoreId) :
    ipcInvariantFull_perCore (endpointReplyOnCore replier target msg executingCore st).1 c :=
  ipcInvariantFull_perCore_of_full
    (endpointReplyOnCore_preserves_ipcInvariantFull replier target msg executingCore st
      (ipcInvariantFull_of_smp hInv) hObjInv hNoDonationOwnedBy hAllBudgetsNone)

-- ============================================================================
-- §7  SM6.D: the receive leg's pre-return migration frame
-- ============================================================================

/-- **`v0.35.161`**: and it agrees with its input off the scheduler — the migration
is a scheduler-only update (`migrateSchedContextReplenishment` rewrites two
replenish queues and nothing else), or the identity.  This is what lets the
single-core/cross-core agreement dichotomy carry the block path across the point
where the two spines part. -/
theorem preReceiveReturnMigration_offSchedulerAgrees (st stClean : SystemState)
    (receiver : SeLe4n.ThreadId) :
    OffSchedulerAgrees stClean (preReceiveReturnMigration st stClean receiver) := by
  unfold preReceiveReturnMigration
  split
  · exact migrateSchedContextReplenishment_offSchedulerAgrees _ _ _ _
  · exact OffSchedulerAgrees.refl _

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
                    (some (blockedSenderMessage st1 sender senderTcb)) with
                | error e => left; rfl
                | ok st4 =>
                  right
                  refine ⟨sender, st4, ?_, linkReplyWaiter_offSchedulerAgrees st4 _ _⟩
                  unfold endpointReceiveDual SystemState.getObject?
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
                  receiver .ready (some (blockedSenderMessage st1 sender senderTcb)) with
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
                  exact ensureRunnable_objects_invExt _ _ hObjInv2
                have hInvWake : (wakeThread st2 sender executingCore).1.objects.invExt :=
                  wakeThread_preserves_objects_invExt st2 sender executingCore hObjInv2
                obtain ⟨st4SC, hStore2SC, hAgree4⟩ :=
                  storeTcbIpcStateAndMessage_offSchedulerAgrees receiver .ready
                    (some (blockedSenderMessage st1 sender senderTcb)) hRel0 hInvEns hInvWake hStore2
                refine ⟨sender, st4SC, ?_, hAgree4⟩
                unfold endpointReceiveDual SystemState.getObject?
                simp only [hEpRaw, hHead, hPop, hSIpc, if_neg Bool.false_ne_true,
                  hStore1, hStore2SC]
    | none =>
      simp only
      cases hClean : cleanupPreReceiveDonationMigrated st receiver with
      | error e => left; rfl
      | ok stClean' =>
        simp only
        -- **`v0.35.161`**: the two spines part here.  The single-core spine runs
        -- the bare checked cleanup and lands on `stClean`; the cross-core spine
        -- runs the migrated one and lands on `stClean'`, which agrees with it off
        -- the scheduler.  From here on both run the same object-level steps on
        -- two states rather than one, and each step's congruence carries the
        -- relation (`endpointQueueEnqueue_offSchedulerAgrees`,
        -- `storeTcbIpcStateAndMessage_offSchedulerAgrees`,
        -- `storeObject_offSchedulerAgrees`); the stash guard reads the *input*
        -- state `st`, so it needs no congruence at all.
        obtain ⟨stClean, hChecked, hMig⟩ := cleanupPreReceiveDonationMigrated_ok_decompose hClean
        have hRelC : OffSchedulerAgrees stClean stClean' := by
          rw [hMig]; exact preReceiveReturnMigration_offSchedulerAgrees st stClean receiver
        have hInvC : stClean.objects.invExt := by
          rw [← cleanupPreReceiveDonationChecked_ok_eq_cleanup st stClean receiver hChecked]
          exact cleanupPreReceiveDonation_preserves_objects_invExt st receiver hObjInv
        have hInvC' : stClean'.objects.invExt :=
          cleanupPreReceiveDonationMigrated_preserves_objects_invExt st stClean' receiver
            hObjInv hClean
        cases hEnq' : endpointQueueEnqueue endpointId true receiver stClean' with
        | error e => left; rfl
        | ok st1' =>
          simp only
          obtain ⟨st1, hEnq, hRel1⟩ := endpointQueueEnqueue_offSchedulerAgrees endpointId true
            receiver hRelC hInvC hInvC' hEnq'
          have hInv1 : st1.objects.invExt :=
            endpointQueueEnqueue_preserves_objects_invExt endpointId true receiver stClean st1
              hInvC hEnq
          have hInv1' : st1'.objects.invExt :=
            endpointQueueEnqueue_preserves_objects_invExt endpointId true receiver stClean' st1'
              hInvC' hEnq'
          cases hStore1' : storeTcbIpcStateAndMessage st1' receiver (.blockedOnReceive endpointId)
              none with
          | error e => left; rfl
          | ok st2' =>
            simp only
            obtain ⟨st2, hStore1, hRel2⟩ := storeTcbIpcStateAndMessage_offSchedulerAgrees receiver
              (.blockedOnReceive endpointId) none hRel1 hInv1 hInv1' hStore1'
            have hInv2 : st2.objects.invExt :=
              storeTcbIpcStateAndMessage_preserves_objects_invExt st1 st2 receiver _ _ hInv1 hStore1
            have hInv2' : st2'.objects.invExt :=
              storeTcbIpcStateAndMessage_preserves_objects_invExt st1' st2' receiver _ _ hInv1'
                hStore1'
            cases hGetR' : st2'.getTcb? receiver with
            | none =>
              have hGetR : st2.getTcb? receiver = none := by
                have hSome := hRel2.objects.getTcb?_isSome receiver
                rw [hGetR'] at hSome
                cases e : st2.getTcb? receiver with
                | none => rfl
                | some _ => rw [e] at hSome; cases hSome
              right
              refine ⟨receiver, removeRunnable st2 receiver, ?_, ?_⟩
              · unfold endpointReceiveDual SystemState.getObject?
                simp only [hEpRaw, hHead, hChecked, hEnq, hStore1, hGetR]
              · exact (removeRunnable_offSchedulerAgrees st2 receiver).symm.trans
                  (hRel2.trans (removeRunnableOnCore_offSchedulerAgrees st2' receiver executingCore))
            | some rTcb' =>
              obtain ⟨rTcb, hObjR, hEqR⟩ :=
                hRel2.objects.get_tcb' ((SystemState.getTcb?_eq_some_iff _ _ _).mp hGetR')
              have hGetR : st2.getTcb? receiver = some rTcb :=
                (SystemState.getTcb?_eq_some_iff _ _ _).mpr hObjR
              simp only
              split
              · next hValid =>
                cases hStash' : storeObject receiver.toObjId
                    (.tcb { rTcb' with pendingReceiveReplyCode := SeLe4n.ReplyId.optCode replyId })
                    (st2'.recordReplyStasher (SeLe4n.ReplyId.optCode replyId) receiver) with
                | error e => left; rfl
                | ok pStash' =>
                  obtain ⟨⟨⟩, stStashed'⟩ := pStash'
                  right
                  obtain ⟨stStashed, hStash⟩ := storeObject_isOk
                    (st2.recordReplyStasher (SeLe4n.ReplyId.optCode replyId) receiver) receiver.toObjId
                    (.tcb { rTcb with pendingReceiveReplyCode := SeLe4n.ReplyId.optCode replyId })
                  refine ⟨receiver, removeRunnable stStashed receiver, ?_, ?_⟩
                  · unfold endpointReceiveDual SystemState.getObject?
                    simp only [hEpRaw, hHead, hChecked, hEnq, hStore1, hGetR,
                      if_pos hValid, hStash]
                  · refine (removeRunnable_offSchedulerAgrees stStashed receiver).symm.trans
                      ((storeObject_offSchedulerAgrees_of_agree _ ?_
                        (recordReplyStasher_offSchedulerAgrees _ _ hRel2 hInv2 hInv2')
                        (SystemState.recordReplyStasher_objects_invExt _ _ _ hInv2)
                        (SystemState.recordReplyStasher_objects_invExt _ _ _ hInv2') hStash
                        hStash').trans
                        (removeRunnableOnCore_offSchedulerAgrees stStashed' receiver
                          executingCore))
                    rw [TCB.eq_withRunLinks_of_withoutRunLinks_eq hEqR]
                    rfl
              · left; rfl

-- ============================================================================
-- §9  SM6.D: whole-bundle + per-core bundle preservation (cross-core receive)
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (SM6.C closure): the cross-core receive leg preserves the
**whole nineteen-conjunct bundle**, unconditionally over success/failure.
Hypotheses mirror `endpointReceiveDual_preserves_ipcInvariantFull`, with TCB
lookups routed through the typed `getTcb?` and the threaded post-state facts
stated at the cross-core post-state. -/
theorem endpointReceiveDualOnCore_preserves_ipcInvariantFull
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (executingCore : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    -- **WS-OD OD4.4**: the pre-receive cleanup's pop resolves its new owner from
    -- the reply stack; this is the obligation that resolution carries.
    (hStackValid : cleanupDonationStackValid st receiver)
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
  rcases endpointReceiveDualOnCore_post_agrees endpointId receiver replyId executingCore st
    hObjInv with hPre | ⟨sender, r1, hStep1, hAgree⟩
  · rw [hPre]; exact hInv
  · exact ipcInvariantFull_of_objectsAgreeOffRunLinks hAgree.objects
      (endpointReceiveDual_preserves_ipcInvariantFull endpointId receiver sender replyId st r1
        hInv hObjInv hStackValid
        hAllBudgetsNone
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
    -- **WS-OD OD4.4**: the pre-receive cleanup's pop resolves its new owner from
    -- the reply stack; this is the obligation that resolution carries.
    (hStackValid : cleanupDonationStackValid st receiver)
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
      executingCore st (ipcInvariantFull_of_smp hInv) hObjInv hStackValid
      hAllBudgetsNone hFreshReceiver hRecvTailFresh hReplyIdValid hReceiverNotRecv
      hReceiverReady)

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

-- **WS-RR RR8.16**: `storeTcbIpcStateAndMessage_tcb_backward_fields` used to be
-- declared here.  It is a **frame over a primitive**, and it sat in a cross-core
-- *arm* module that the information-flow layer cannot reach -- so the establishment
-- of `blockedSenderFlowsToEndpoint` at the one write that creates a blocked sender
-- was unstateable beside the predicate.  It now lives beside
-- `storeTcbIpcStateAndMessage` in `IPC/Operations/Endpoint.lean`, next to its two
-- existing siblings (`_preserves_objects_ne` and `storeTcbIpcState`'s own frames,
-- themselves moved there for the same reason at WS-RR RR3.5), keeping its name and
-- statement -- the `v0.35.59` rule: *when a question has one owner and an asker that
-- cannot see it, the owner is in the wrong layer.*

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
/-- **WS-RM (`v0.35.6`)**: the removal's pullback — the splice writes no TCB at
all, so the four fields agree for the same reason they do across the consume. -/
theorem removeCallerReplyFrame_tcb_fields_backward
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    ∀ (s : SeLe4n.ObjId) (tx : TCB), st'.objects[s]? = some (.tcb tx) →
      ∃ ty, st.objects[s]? = some (.tcb ty) ∧
        tx.ipcState = ty.ipcState ∧ tx.pendingMessage = ty.pendingMessage ∧
        tx.pendingReceiveReply = ty.pendingReceiveReply ∧
        tx.timeoutBudget = ty.timeoutBudget := by
  intro s tx hObj
  rw [removeCallerReplyFrame_eq] at hStep
  obtain ⟨ty, hTy, h1, h2, h3, h4⟩ := consumeCallerReply_tcb_fields_backward _ st' caller rid
    (spliceReplyFrameOutOrSelf_preserves_objects_invExt st rid hObjInv) hStep s tx hObj
  exact ⟨ty, spliceReplyFrameOutOrSelf_tcb_backward st rid hObjInv s ty hTy, h1, h2, h3, h4⟩

open SeLe4n.Model.SystemState in
/-- SM6.D transport (T1): every TCB observable after `endpointReplyOnCore`
pulls back to a pre-state TCB agreeing on `pendingReceiveReply` and
`timeoutBudget`, and is either woken `.ready` or agrees on
`ipcState`/`pendingMessage` too.  This is the lever that carries the receive
leg's thread-shaped pre-state facts (`hReceiverReady`, `hReceiverNotRecv`,
`allTimeoutBudgetsNone`, `blockedThreadsPendingMessageConsistent`, the stash
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
    hEq | ⟨tcb, st', server, pre, hLk, hStore, hPost, hTail⟩
  · rw [hEq] at hTcb'
    exact ⟨tcb', hTcb', rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩
  · rw [hPost] at hTcb'
    obtain ⟨tcb', hTcb', hEp⟩ := SystemState.getTcb?_of_objectsAgreeOffRunLinks (SystemState.unlinkReplyWaiter_objectsAgreeOffRunLinks pre target server).symm hTcb'
    rw [← TCB.proj_eq_of_withoutRunLinks_eq TCB.pendingReceiveReply hEp,
      ← TCB.proj_eq_of_withoutRunLinks_eq TCB.timeoutBudget hEp,
      ← TCB.proj_eq_of_withoutRunLinks_eq TCB.ipcState hEp,
      ← TCB.proj_eq_of_withoutRunLinks_eq TCB.pendingMessage hEp]
    have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st' := by
      rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk]; exact hStore
    have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st' target .ready
      (some msg) hObjInv hStore'
    obtain ⟨tr, hTrGet, hTrReady⟩ :=
      storeTcbIpcStateAndMessage_getTcb?_ipcState st st' target .ready (some msg) hObjInv hStore'
    have hWA := wakeThread_objectsAgreeOffRunLinks_of_ready st' target executingCore tr
      hTrGet hTrReady hObjInv1
    rcases hTail with ⟨_, hPostEq⟩ | ⟨rid, _, hCons⟩
    · rw [hPostEq] at hTcb'
      have hRaw' := (getTcb?_eq_some_iff _ tid tcb').mp hTcb'
      obtain ⟨tw, hRaw, hE⟩ := hWA.get_tcb' hRaw'
      obtain ⟨ty, hty, hStash, hBudget, hDisj⟩ :=
        storeTcbIpcStateAndMessage_tcb_backward_fields st st' target .ready (some msg)
          hObjInv hStore' tid.toObjId tw hRaw
      refine ⟨ty, (getTcb?_eq_some_iff st tid ty).mpr hty,
        (TCB.proj_eq_of_withoutRunLinks_eq TCB.pendingReceiveReply hE).trans hStash,
        (TCB.proj_eq_of_withoutRunLinks_eq TCB.timeoutBudget hE).trans hBudget, ?_⟩
      rcases hDisj with rfl | hReady
      · exact Or.inr ⟨TCB.proj_eq_of_withoutRunLinks_eq TCB.ipcState hE, TCB.proj_eq_of_withoutRunLinks_eq TCB.pendingMessage hE⟩
      · exact Or.inl ((TCB.proj_eq_of_withoutRunLinks_eq TCB.ipcState hE).trans hReady)
    · have hInvWake : (wakeThread st' target executingCore).1.objects.invExt :=
        wakeThread_preserves_objects_invExt st' target executingCore hObjInv1
      have hRaw' := (getTcb?_eq_some_iff _ tid tcb').mp hTcb'
      obtain ⟨t1, hT1, hIpc1, hPend1, hStash1, hBudget1⟩ :=
        removeCallerReplyFrame_tcb_fields_backward _ _ target rid hInvWake hCons tid.toObjId tcb' hRaw'
      obtain ⟨tw, hTw, hE⟩ := hWA.get_tcb' hT1
      obtain ⟨ty, hty, hStash, hBudget, hDisj⟩ :=
        storeTcbIpcStateAndMessage_tcb_backward_fields st st' target .ready (some msg)
          hObjInv hStore' tid.toObjId tw hTw
      refine ⟨ty, (getTcb?_eq_some_iff st tid ty).mpr hty,
        hStash1.trans ((TCB.proj_eq_of_withoutRunLinks_eq TCB.pendingReceiveReply hE).trans hStash),
        hBudget1.trans ((TCB.proj_eq_of_withoutRunLinks_eq TCB.timeoutBudget hE).trans hBudget), ?_⟩
      rcases hDisj with rfl | hReady
      · exact Or.inr ⟨hIpc1.trans (TCB.proj_eq_of_withoutRunLinks_eq TCB.ipcState hE), hPend1.trans (TCB.proj_eq_of_withoutRunLinks_eq TCB.pendingMessage hE)⟩
      · exact Or.inl (hIpc1.trans ((TCB.proj_eq_of_withoutRunLinks_eq TCB.ipcState hE).trans hReady))

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
    hEq | ⟨tcb, st', server, pre, hLk, hStore, hPost, hTail⟩
  · rw [hEq] at hEp; exact hEp
  · rw [hPost] at hEp
    replace hEp := (SystemState.unlinkReplyWaiter_objectsAgreeOffRunLinks pre target server).get_of_not_tcb' (fun _ h => by cases h) hEp
    have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st' := by
      rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk]; exact hStore
    have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st' target .ready
      (some msg) hObjInv hStore'
    obtain ⟨tr, hTrGet, hTrReady⟩ :=
      storeTcbIpcStateAndMessage_getTcb?_ipcState st st' target .ready (some msg) hObjInv hStore'
    have hWA := wakeThread_objectsAgreeOffRunLinks_of_ready st' target executingCore tr
      hTrGet hTrReady hObjInv1
    rcases hTail with ⟨_, hPostEq⟩ | ⟨rid, _, hCons⟩
    · rw [hPostEq] at hEp
      exact storeTcbIpcStateAndMessage_endpoint_backward st st' target .ready (some msg)
        oid ep hObjInv hStore' (hWA.get_endpoint_iff.mp hEp)
    · have hInvWake : (wakeThread st' target executingCore).1.objects.invExt :=
        wakeThread_preserves_objects_invExt st' target executingCore hObjInv1
      have hEpWake := (removeCallerReplyFrame_nonTcbNonReply_agree _ _ target rid
        hInvWake hCons oid (.endpoint ep) (fun _ => by simp) (fun _ => by simp)).mp hEp
      exact storeTcbIpcStateAndMessage_endpoint_backward st st' target .ready (some msg)
        oid ep hObjInv hStore' (hWA.get_endpoint_iff.mp hEpWake)

open SeLe4n.Model.SystemState in
/-- SM6.D transport (T3): the reply leg preserves `replyIdEstablishFresh` —
the reply store rewrites only the woken caller (stash-invisible), the wake
writes only run-queue links, and the folded consume can only *free* a reply. -/
theorem endpointReplyOnCore_preserves_replyIdEstablishFresh
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hFresh : replyIdEstablishFresh st rid) :
    replyIdEstablishFresh (endpointReplyOnCore replier target msg executingCore st).1 rid := by
  rcases endpointReplyOnCore_state_eq replier target msg executingCore st with
    hEq | ⟨tcb, st', server, pre, hLk, hStore, hPost, hTail⟩
  · rw [hEq]; exact hFresh
  · rw [hPost]
    refine (fun hF => ?_) (?_ : replyIdEstablishFresh pre rid)
    · obtain ⟨⟨r, hr, hrc⟩, hUn⟩ := hF
      refine ⟨⟨r, ?_, hrc⟩, ?_⟩
      · rw [getReply?_eq_some_iff] at hr ⊢; exact (SystemState.unlinkReplyWaiter_objectsAgreeOffRunLinks pre target server).get_reply_iff.mpr hr
      · intro t tcb0 hT hS
        rw [getTcb?_eq_some_iff] at hT
        obtain ⟨t0, h0, hE⟩ := (SystemState.unlinkReplyWaiter_objectsAgreeOffRunLinks pre target server).get_tcb' hT
        exact hUn t t0 ((getTcb?_eq_some_iff pre t t0).mpr h0)
          (by rw [← TCB.proj_eq_of_withoutRunLinks_eq TCB.pendingReceiveReply hE]; exact hS)
    have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st' := by
      rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk]; exact hStore
    have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st' target .ready
      (some msg) hObjInv hStore'
    obtain ⟨tr, hTrGet, hTrReady⟩ :=
      storeTcbIpcStateAndMessage_getTcb?_ipcState st st' target .ready (some msg) hObjInv hStore'
    have hWA := wakeThread_objectsAgreeOffRunLinks_of_ready st' target executingCore tr
      hTrGet hTrReady hObjInv1
    have hFresh' := storeTcbIpcStateAndMessage_preserves_replyIdEstablishFresh st st' target
      .ready (some msg) rid hObjInv hFresh hStore'
    have hFreshW : replyIdEstablishFresh (wakeThread st' target executingCore).1 rid := by
      obtain ⟨⟨r, hr, hrc⟩, hUn⟩ := hFresh'
      refine ⟨⟨r, ?_, hrc⟩, ?_⟩
      · rw [getReply?_eq_some_iff] at hr ⊢; exact hWA.get_reply_iff.mpr hr
      · intro t tcb0 hT hS
        rw [getTcb?_eq_some_iff] at hT
        obtain ⟨t0, h0, hE⟩ := hWA.get_tcb' hT
        exact hUn t t0 ((getTcb?_eq_some_iff st' t t0).mpr h0)
          (by rw [← TCB.proj_eq_of_withoutRunLinks_eq TCB.pendingReceiveReply hE]; exact hS)
    rcases hTail with ⟨_, hPostEq⟩ | ⟨rid', _, hCons⟩
    · rw [hPostEq]; exact hFreshW
    · have hInvWake : (wakeThread st' target executingCore).1.objects.invExt :=
        wakeThread_preserves_objects_invExt st' target executingCore hObjInv1
      exact removeCallerReplyFrame_preserves_replyIdEstablishFresh _ _ target rid' rid
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
          cases hCons : removeCallerReplyFrame target rid
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
            have hWA := wakeThread_objectsAgreeOffRunLinks_of_ready st' target executingCore tr
              hTrGet hTrReady hObjInv1
            have hInvWake : (wakeThread st' target executingCore).1.objects.invExt :=
              wakeThread_preserves_objects_invExt st' target executingCore hObjInv1
            have hNeSlot : target.toObjId ≠ rid.toObjId :=
              getTcb?_getReply?_slot_ne st target rid tcb r hTcbT hGetR
            have hRWake : (wakeThread st' target executingCore).1.getReply? rid = some r := by
              rw [getReply?_eq_some_iff]
              refine hWA.get_reply_iff.mpr ?_
              rw [storeTcbIpcStateAndMessage_preserves_objects_ne st st' target .ready
                (some msg) rid.toObjId (fun h => hNeSlot h.symm) hObjInv hStore']
              exact (getReply?_eq_some_iff st rid r).mp hGetR
            obtain ⟨r', h1, h2⟩ :=
              removeCallerReplyFrame_getReply?_free _ target rid r hInvWake hRWake stC hCons
            refine ⟨r', ?_, h2⟩
            rw [getReply?_eq_some_iff] at h1 ⊢
            exact (SystemState.unlinkReplyWaiter_objectsAgreeOffRunLinks _ _ _).get_reply_iff.mpr h1

-- ============================================================================
-- §10  WS-RR RR2 closure audit — the capability-carrying live `.receive` arm
-- ============================================================================
--
-- `endpointReceiveDualWithCapsOnCore` is the transition the live `.receive` arm
-- (and `endpointReplyRecvOnCore`'s receive leg) actually runs; §9's bundle covers only the
-- bare per-core receive inside it.  The pre-SM10 audit counted the receive arm
-- as covered on the strength of the bare form — measuring the wrong function,
-- the same shape as blocker 3's retired-single-core citation — so the closure
-- audit builds the WithCaps composition here, mirroring the `.send` side's
-- RR2.14 exactly: the bare bundle, then `ipcUnwrapCaps`' on the installing arm,
-- with the transfer's two *input* conditions (a CNode at the destination root,
-- valid badges on the capabilities resolved from the sender's CSpace) rather than
-- any post-state conjunct.

open SeLe4n.Model.SystemState in
-- WS-SM SM6.C, relocated at **WS-RR RR8.12**:
-- `endpointReceiveDualOnCore_preserves_objects_invExt` moved to
-- `IPC/CrossCore/EndpointReply.lean`, beside the transition it frames.  An
-- `objects.invExt` preservation is a frame, and this project homes a frame with the
-- write it is about; sitting here it was *downstream* of the module that declares
-- the transition, so the receive leg's own home-core frame -- which needs invExt at
-- the post-leg state to reach the capability installation -- could not consult it.
-- Third instance of that layering in this cut, after `endpointReceiveDualWriteSet`
-- and `endpointReceiveDualWithCapsOnCore_scheduler_eq`.

/-- **WS-RR RR2 (closure audit): the transition the live `.receive` arm really
calls preserves the whole IPC invariant bundle.**

The composition is §9's bare cross-core bundle, then
`ipcUnwrapCaps_preserves_ipcInvariantFull` on the arm that installs the dequeued
sender's capabilities.  WS-ZA ZA4.7: those capabilities are resolved from the
sender's own CSpace at the rendezvous (`receiveTransferCaps_frame`), so their
badges are valid because the badges at rest there are -- a conjunct of the
bundle itself, not a hypothesis about the delivered message. -/
theorem endpointReceiveDualWithCapsOnCore_preserves_ipcInvariantFull
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId)
    (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    -- **WS-OD OD4.4**: the pre-receive cleanup's pop resolves its new owner from
    -- the reply stack; this is the obligation that resolution carries.
    (hStackValid : cleanupDonationStackValid st receiver)
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
:
    ipcInvariantFull
      (endpointReceiveDualWithCapsOnCore endpointId receiver replyId receiverCspaceRoot
        receiverSlotBase executingCore st).1 := by
  have hBare := endpointReceiveDualOnCore_preserves_ipcInvariantFull endpointId receiver replyId
    executingCore st hInv hObjInv hStackValid hAllBudgetsNone hFreshReceiver
    hRecvTailFresh hReplyIdValid hReceiverNotRecv hReceiverReady
  have hBareInv := endpointReceiveDualOnCore_preserves_objects_invExt endpointId receiver replyId
    executingCore st hObjInv
  unfold endpointReceiveDualWithCapsOnCore
  cases hRecv : endpointReceiveDualOnCore endpointId receiver replyId executingCore st with
  | mk stRecv res =>
    rw [hRecv] at hBare hBareInv
    cases res with
    | error e => exact hBare
    | ok pr =>
      obtain ⟨senderId, sgi⟩ := pr
      simp only
      split
      · exact hBare
      · -- WS-ZA ZA4.7: the sender's capabilities are resolved (CDT nodes only)
        -- and installed (`receiveTransferCaps_frame`); their badges are valid
        -- because the badges at rest in the sender's CSpace are.
        split
        · exact hBare
        · rename_i summary stFinal hT
          obtain ⟨stR, caps, hO, hS, hCaps, hOr⟩ := receiveTransferCaps_frame hT
          have hR : ipcInvariantFull stR := ipcInvariantFull_of_objects_eq hO hBare
          rcases hOr with rfl | hU
          · exact hR
          · exact ipcUnwrapCaps_preserves_ipcInvariantFull _ receiverCspaceRoot
              receiverSlotBase _ stR _ _ hR (hO ▸ hBareInv)
              (fun i c hc b hb => hCaps hBare.badgeWellFormed.2 i c hc b hb) hU

open SeLe4n.Model.SystemState in
/-- WS-RR RR2 (closure audit): the per-core bundle form for the live `.receive`
arm, mirroring `endpointSendDualWithCapsOnCore_preserves_ipcInvariantFull_perCore`. -/
theorem endpointReceiveDualWithCapsOnCore_preserves_ipcInvariantFull_perCore
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId)
    (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState)
    (hInv : ipcInvariantFull_smp st)
    (hObjInv : st.objects.invExt)
    -- **WS-OD OD4.4**: the pre-receive cleanup's pop resolves its new owner from
    -- the reply stack; this is the obligation that resolution carries.
    (hStackValid : cleanupDonationStackValid st receiver)
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
      (endpointReceiveDualWithCapsOnCore endpointId receiver replyId receiverCspaceRoot
        receiverSlotBase executingCore st).1 c :=
  ipcInvariantFull_perCore_of_full
    (endpointReceiveDualWithCapsOnCore_preserves_ipcInvariantFull endpointId receiver replyId
      receiverCspaceRoot receiverSlotBase executingCore st (ipcInvariantFull_of_smp hInv)
      hObjInv hStackValid hAllBudgetsNone hFreshReceiver hRecvTailFresh hReplyIdValid
      hReceiverNotRecv hReceiverReady)

-- ============================================================================
-- WS-RR RR7.4: observer atomicity for the reply pair
--
-- The reply half of the five instantiations register §4 finding 7 names as
-- missing.  `endpointReplyOnCore_atomic_under_lockSet` is an `rfl` instance of
-- the body-agnostic `lockSet_atomic_under_2pl`; this carries the substantive
-- form.  (Audit IPC-2, `v0.36.49`: the `replyRecv` companion was stated about a
-- two-leg composite the live arm never ran and is deleted with it; the live
-- `.replyRecv` runs under the syscall-wide bracket, `syscallDispatchBracket`.)
-- ============================================================================

/-- **WS-RR RR7.4** (**WS-LS LS2.1**: over the pair, hypothesis-free): under its
declared footprint the cross-core reply is observationally atomic — the whole
2PL bracket is invisible to any thread's IPC state, the field the reply writes
on the answered caller.  The `invExt` hypothesis and the acquire-fold conjunct
are dropped because the growing phase no longer touches the kernel state — a
strengthening (plan O6). -/
theorem endpointReplyOnCore_observer_atomic
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (cnRoot : SeLe4n.ObjId) (donatedSc? : Option SeLe4n.SchedContextId)
    (donatedOwner? : Option SeLe4n.ThreadId) (observed : SeLe4n.ThreadId)
    -- WS-OD OD3.5: over **every** argument of the footprint this theorem names,
    -- the resolved reply object included.  The three `.replyRecv`-only members
    -- (`installsCaps`, the recorded server, the re-donated context) were
    -- mistakenly declared here rather than on the companion below: they do not
    -- occur in `lockSet_endpointReply` at all, so the statement read as covering
    -- shapes it says nothing about while the compiler reported them unused.
    (replyId : Option SeLe4n.ReplyId)
    -- WS-OD OD3.7: and the two objects the donation return reads below the
    -- reply-stack head, for the same reason the reply object is here.
    (belowHeadReply? : Option SeLe4n.ReplyId) (outerCaller? : Option SeLe4n.ThreadId)
    -- WS-OD (`v0.35.4`) / WS-RM (`v0.35.6`): and the head the pop clears and the
    -- frame above the answered reply, which the removal's splice writes -- every
    -- argument of the footprint this theorem names, for the reason above.
    (donatedHead? answeredFrameAbove? : Option SeLe4n.ReplyId)
    -- **WS-HP HP3.1**: and at the frame-below arity.
    (answeredFrameBelow? : Option SeLe4n.ReplyId)
    -- **WS-HP HP10.6**: and at the origin-recipient arity.
    (originRecipient? : Option SeLe4n.ThreadId)
    (s : LockedSystemState) :
    threadIpcStateObserver observed
        (withLockSet
          (lockSet_endpointReply replier cnRoot target donatedSc? donatedOwner? replyId
            belowHeadReply? outerCaller? donatedHead? answeredFrameAbove? answeredFrameBelow? originRecipient?)
          executingCore (endpointReplyOnCore replier target msg executingCore) s).1.kernel
      = threadIpcStateObserver observed
          (endpointReplyOnCore replier target msg executingCore s.kernel).1 :=
  lockSet_observer_atomic _ executingCore _ s _

-- ============================================================================
-- §11  WS-RR RR8.16 (`v0.35.199`) — the reply leg's two cross-subsystem bundles
-- ============================================================================
--
-- Register row 85.  `v0.35.197` gave `schedulerInvariantBase_smp` and
-- `capabilityInvariantBundle` their frames; here the reply leg's own store chain
-- -- the delivery, the wake and seL4's `reply_remove` -- is carried across both,
-- each step by a citation rather than by an argument.
--
-- The two lifts take different preconditions, and the asymmetry is the content:
-- the capability bundle reads only the object store and the two CDT tables, all
-- three of which the leg frames or writes kind-preservingly, so it is
-- **unconditional**; the scheduler bundle reads `currentOnCore`, and the wake's
-- `queueCurrentConsistentOnCore` preservation needs the thread it enqueues not
-- to be that core's current thread.

/-- **WS-RR RR8.16** (`v0.35.199`): the cross-core reply leg preserves the **base
SMP scheduler invariant**.

Three steps, one citation each: the delivery store is a `kindPreservingWrite` on
a state whose scheduler it does not touch, the wake is `wakeThread`'s own lift,
and seL4's `reply_remove` is another kind-preserving object write.

`hNotCur` is stated on the **pre**-state, which is where a caller can discharge
it: the delivery frames the scheduler and every thread's `cpuAffinity`, so the
core the wake enqueues on and the slot it reads are the pre-state's.

It is **stated rather than derived**, and the reason is a gap this cut does not
close: the answered caller is `.blockedOnReply` in the pre-state, and what turns
that into "not current" is a *per-core* current-thread-IPC-readiness discipline,
which this tree states at the boot core only (`currentThreadIpcReady`).
`blockedOnReplyNotRunnable` is not it — it says a reply-blocked thread is not in
a run **queue**, which `queueCurrentConsistentOnCore` makes compatible with being
current rather than incompatible.  A per-core `currentThreadIpcReady` retires the
hypothesis; until there is one, a caller supplies it (the single-core
`endpointReply_preserves_schedulerInvariantBundle` has taken the boot-core form
since WS-H1 for the same reason). -/
theorem endpointReplyOnCore_preserves_schedulerInvariantBase_smp
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt)
    (hNotCur : st.scheduler.currentOnCore (determineTargetCore st target) ≠ some target)
    (h : schedulerInvariantBase_smp st) :
    schedulerInvariantBase_smp
      (endpointReplyOnCore replier target msg executingCore st).1 := by
  rcases endpointReplyOnCore_state_eq replier target msg executingCore st with
    hEq | ⟨tcb, st', server, pre, hLk, hStore, hPost, hTail⟩
  · rw [hEq]; exact h
  · rw [hPost]
    refine schedulerInvariantBase_smp_of_kindPreserving ?_
      (SystemState.unlinkReplyWaiter_scheduler _ _ _)
      (SystemState.unlinkReplyWaiter_kindPreservingWrite _ _ _)
    have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st' := by
      rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk]; exact hStore
    have hSched : st'.scheduler = st.scheduler :=
      storeTcbIpcStateAndMessage_scheduler_eq st st' target .ready (some msg) hStore'
    have hObj' : st'.objects.invExt :=
      storeTcbIpcStateAndMessage_preserves_objects_invExt st st' target .ready (some msg)
        hObjInv hStore'
    have h1 : schedulerInvariantBase_smp st' :=
      schedulerInvariantBase_smp_of_kindPreserving h hSched
        (storeTcbIpcStateAndMessage_fromTcb_kindPreservingWrite hObjInv
          (lookupTcb_some_objects st target tcb hLk) hStore)
    have hNotCur' :
        st'.scheduler.currentOnCore (determineTargetCore st' target) ≠ some target := by
      rw [storeTcbIpcStateAndMessage_determineTargetCore_eq st st' target .ready (some msg)
        target hObjInv hStore', hSched]
      exact hNotCur
    have h2 : schedulerInvariantBase_smp (wakeThread st' target executingCore).1 :=
      wakeThread_preserves_schedulerInvariantBase_smp st' target executingCore hObj'
        hNotCur' h1
    rcases hTail with ⟨_, hEq⟩ | ⟨rid, _, hCons⟩
    · rw [hEq]; exact h2
    · exact schedulerInvariantBase_smp_of_kindPreserving h2
        (removeCallerReplyFrame_scheduler_eq _ _ target rid hCons)
        (removeCallerReplyFrame_kindPreservingWrite _ _ target rid
          (wakeThread_preserves_objects_invExt st' target executingCore hObj') hCons)

/-- **WS-RR RR8.16** (`v0.35.199`): ...and the **capability invariant bundle**,
with no precondition beyond object-store integrity.

Every write the leg performs replaces an object with one of the same non-`cnode`
kind -- a TCB for a TCB at the answered caller, the woken thread's own `.ready`
rewrite, and a Reply for a Reply at each frame `reply_remove` repairs -- and no
step writes either CDT table.  That is exactly what
`capabilityInvariantBundle_of_kindPreserving` asks. -/
theorem endpointReplyOnCore_preserves_capabilityInvariantBundle
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt)
    (h : capabilityInvariantBundle st) :
    capabilityInvariantBundle
      (endpointReplyOnCore replier target msg executingCore st).1 := by
  rcases endpointReplyOnCore_state_eq replier target msg executingCore st with
    hEq | ⟨tcb, st', server, pre, hLk, hStore, hPost, hTail⟩
  · rw [hEq]; exact h
  · have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st' := by
      rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk]; exact hStore
    have hObj' : st'.objects.invExt :=
      storeTcbIpcStateAndMessage_preserves_objects_invExt st st' target .ready (some msg)
        hObjInv hStore'
    have hCdt := storeTcbIpcStateAndMessage_fromTcb_cdt_eq hStore
    have h1 : capabilityInvariantBundle st' :=
      capabilityInvariantBundle_of_kindPreserving h hCdt hObj'
        (storeTcbIpcStateAndMessage_fromTcb_kindPreservingWrite hObjInv
          (lookupTcb_some_objects st target tcb hLk) hStore)
    have hObjW : (wakeThread st' target executingCore).1.objects.invExt :=
      wakeThread_preserves_objects_invExt st' target executingCore hObj'
    have h2 : capabilityInvariantBundle (wakeThread st' target executingCore).1 :=
      wakeThread_preserves_capabilityInvariantBundle st' target executingCore hObj' h1
    rw [hPost]
    have hU : ∀ s, s.objects.invExt → capabilityInvariantBundle s →
        capabilityInvariantBundle (s.unlinkReplyWaiter target server) := fun s hI hB =>
      capabilityInvariantBundle_of_kindPreserving hB
        (SystemState.unlinkReplyWaiter_cdt _ _ _)
        (SystemState.unlinkReplyWaiter_objects_invExt _ _ _ hI)
        (SystemState.unlinkReplyWaiter_kindPreservingWrite _ _ _)
    rcases hTail with ⟨_, hEq⟩ | ⟨rid, _, hCons⟩
    · rw [hEq]; exact hU _ hObjW h2
    · exact hU _ (removeCallerReplyFrame_preserves_objects_invExt _ _ target rid hObjW hCons)
        (capabilityInvariantBundle_of_kindPreserving h2
        (removeCallerReplyFrame_cdt_eq _ _ target rid hCons)
        (removeCallerReplyFrame_preserves_objects_invExt _ _ target rid hObjW hCons)
        (removeCallerReplyFrame_kindPreservingWrite _ _ target rid hObjW hCons))


end SeLe4n.Kernel
