-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-RR RR2.11: PRODUCTION.  The IPC-bundle preservation surface of the live
-- cross-core `.reply` dispatch chain.  Split out of the staged
-- `DispatchInvariant.lean` during the RR2 closure audit: every surface this
-- module composes — `EndpointReplyInvariant`'s reply/receive bundles, the
-- donation primitives' (`IPC/Invariant/DonationPreservation.lean`), and the
-- priority-inheritance walk's (same file, §8) — is production, so the reply
-- chain's bundle was staged only by cohabiting with the `.call` chain, whose
-- `EndpointCallInvariant` dependency is genuinely staged.

import SeLe4n.Kernel.IPC.Invariant.DonationPreservation
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDispatch
-- WS-RM (`v0.35.6`): the reply path's removal and its chain lemmas.  Not a
-- staged dependency: `CancellationReplyShape` is production, and the cancellation
-- and reply paths share one removal step by design.
import SeLe4n.Kernel.Lifecycle.Invariant.CancellationReplyShape

/-!
# WS-RR RR2.11 — the live `.reply` dispatch chain preserves `ipcInvariantFull`

`endpointReplyCrossCoreDispatch` is the operation the live SMP `.reply` arm
routes through: reply delivery → SchedContext donation return (with the RR2.8
replenishment migration) → priority-inheritance reversion.  Until RR2 only the
first stage carried a bundle theorem; this module supplies the donation return's
and the whole chain's.  The chain's third stage, the PIP walk, has its bundle
beside the driver it uses (`DonationPreservation.lean` §8).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId SgiKind)
open SeLe4n.Kernel.PriorityInheritance

-- ============================================================================
-- §1  WS-RM (`v0.35.6`) — the donation chain across the reply dispatch
-- ============================================================================

/-- **WS-RM (`v0.35.6`)**: the per-core donation return preserves the chain, from
a pre-state relaxed at the head it pops.

The two stages after the pop -- the replenishment migration and the replier's
deschedule -- write no object at all, so the whole operation's chain effect is
the pop's (`returnDonatedSchedContext_preserves_donationChainWellFormed_of_except`),
and the relaxation is carried through unchanged. -/
theorem applyReplyDonationOnCore_preserves_donationChainWellFormed_of_except
    (st st'' : SystemState) (replierVtid : SeLe4n.ValidThreadId)
    (replierHome ownerHome : CoreId)
    (hObjInv : st.objects.invExt)
    (hChainNone : ∀ scId owner sc, replyDonationReturn? st replierVtid.val = some (scId, owner) →
      st.getSchedContext? scId = some sc →
      donationHeadOf? st scId sc = .ok none → donationChainWellFormed st)
    (hChainHead : ∀ scId owner sc rid r,
      replyDonationReturn? st replierVtid.val = some (scId, owner) →
      st.getSchedContext? scId = some sc →
      donationHeadOf? st scId sc = .ok (some (rid, r)) → donationChainWellFormedExcept st rid)
    (hChainNoReturn : replyDonationReturn? st replierVtid.val = none → donationChainWellFormed st)
    (h : applyReplyDonationOnCore st replierVtid replierHome ownerHome = .ok st'') :
    donationChainWellFormed st'' := by
  rcases applyReplyDonationOnCore_ok_decompose st st'' replierVtid replierHome ownerHome h with ⟨hNone, hEq⟩ | ⟨scId, owner, n, st', hRetRes, _, hRet, hEq⟩
  · rw [hEq]; exact hChainNoReturn hNone
  · have hChain' : donationChainWellFormed st' :=
      returnDonatedSchedContext_preserves_donationChainWellFormed_of_except st st'
        replierVtid.val scId owner n hObjInv (hChainNone scId owner · hRetRes)
        (hChainHead scId owner · · · hRetRes) hRet
    rw [hEq]
    refine donationChainWellFormed_of_frame ?_ hChain'
    exact donationChainFrame.of_objects_eq
      (by rw [descheduleAtPlacement_preserves_objects, migrateSchedContextReplenishment_objects])

/-- **WS-RM (`v0.35.6`)**: what the cross-core reply leg leaves of the donation
chain.

Two outcomes, and the second is the whole point of the workstream.  The reply
leg's last step is `removeCallerReplyFrame`, which detaches the answered frame
from the one above it and then consumes the caller link.  On a frame that heads
no scheduling context that restores `Reply.wellFormed` outright (RM2's
`removeCallerReplyFrame_preserves_donationChainWellFormed`).  On a frame that
*is* a stack head, `Reply.consumed` keeps the links deliberately — the donation
pop that follows in the same transition validates the head by that very link —
so the chain is relaxed at exactly that frame, and the composite below is where
the pop discharges it.

The second disjunct carries what the composite needs to connect the two halves:
which frame is relaxed, which context it heads *in the pre-state* (so the reply
server's donation can be identified) and *in the post-state* (so the pop's head
validation can be located at it), and that the answered caller names it. -/
theorem endpointReplyOnCore_donationChain_cases
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt) (hChain : donationChainWellFormed st) :
    donationChainWellFormed (endpointReplyOnCore replier target msg executingCore st).1 ∨
      ∃ (tcb : TCB) (rid : SeLe4n.ReplyId) (r : Reply) (scId : SeLe4n.SchedContextId),
        lookupTcb st target = some tcb ∧ tcb.replyObject = some rid ∧
        st.getReply? rid = some r ∧ r.next = some (.head scId) ∧
        (∃ r1, (endpointReplyOnCore replier target msg executingCore st).1.getReply? rid = some r1 ∧
          r1.next = some (.head scId)) ∧
        donationChainWellFormedExcept
          (endpointReplyOnCore replier target msg executingCore st).1 rid := by
  rcases endpointReplyOnCore_state_eq replier target msg executingCore st with
    hEq | ⟨tcb, st', hLk, hStore, hTail⟩
  · exact Or.inl (by rw [hEq]; exact hChain)
  · have hStore' : storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st' := by
      rw [← storeTcbIpcStateAndMessage_fromTcb_eq hLk]; exact hStore
    have hTargetObj : st.objects[target.toObjId]? = some (.tcb tcb) :=
      lookupTcb_some_objects st target tcb hLk
    have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st' target .ready
      (some msg) hObjInv hStore'
    obtain ⟨tr, hTrGet, hTrReady⟩ :=
      storeTcbIpcStateAndMessage_getTcb?_ipcState st st' target .ready (some msg) hObjInv hStore'
    obtain ⟨t1, hT1⟩ := storeTcbIpcStateAndMessage_tcb_exists_at_target st st' target .ready
      (some msg) hObjInv hStore' ⟨tcb, hTargetObj⟩
    -- The store writes one TCB and the wake writes no object at all (its target
    -- is `.ready`), so the chain reaches the removal's input framed.
    have hStNe : ∀ oid : SeLe4n.ObjId, oid ≠ target.toObjId →
        st'.objects[oid]? = st.objects[oid]? :=
      fun oid h => storeTcbIpcStateAndMessage_preserves_objects_ne st st' target .ready (some msg)
        oid h hObjInv hStore'
    have hFrameStore : donationChainFrame st st' := by
      refine donationChainFrame.of_no_chain_object_write (fun oid r => ?_) (fun oid sc => ?_)
      · by_cases hk : oid = target.toObjId
        · subst hk
          refine ⟨fun h => ?_, fun h => ?_⟩
          · rw [hT1] at h; cases h
          · rw [hTargetObj] at h; cases h
        · rw [hStNe oid hk]
      · by_cases hk : oid = target.toObjId
        · subst hk
          refine ⟨fun h => ?_, fun h => ?_⟩
          · rw [hT1] at h; cases h
          · rw [hTargetObj] at h; cases h
        · rw [hStNe oid hk]
    have hWakeObjs : ∀ oid : SeLe4n.ObjId,
        (wakeThread st' target executingCore).1.objects[oid]? = st'.objects[oid]? :=
      wakeThread_objects_getElem_eq_of_ready st' target executingCore tr hTrGet hTrReady hObjInv1
    have hFrameWake : donationChainFrame st' (wakeThread st' target executingCore).1 :=
      donationChainFrame.of_no_chain_object_write
        (fun oid _ => by rw [hWakeObjs oid]) (fun oid _ => by rw [hWakeObjs oid])
    have hChainWake : donationChainWellFormed (wakeThread st' target executingCore).1 :=
      donationChainWellFormed_of_frame (hFrameStore.trans hFrameWake) hChain
    have hInvWake : (wakeThread st' target executingCore).1.objects.invExt :=
      wakeThread_preserves_objects_invExt st' target executingCore hObjInv1
    rcases hTail with ⟨_, hEq⟩ | ⟨rid, hRO, hRun⟩
    · exact Or.inl (by rw [hEq]; exact hChainWake)
    · by_cases hHead : ∃ (r : Reply) (scId : SeLe4n.SchedContextId),
          (wakeThread st' target executingCore).1.getReply? rid = some r ∧
            r.next = some (.head scId)
      · obtain ⟨r, scId, hR, hNext⟩ := hHead
        -- Read the frame back to the pre-state: it holds a Reply, so its key is
        -- not the answered caller's, which the store rewrote.
        have hRObj : (wakeThread st' target executingCore).1.objects[rid.toObjId]?
            = some (.reply r) := (SystemState.getReply?_eq_some_iff _ rid r).mp hR
        have hRidNe : rid.toObjId ≠ target.toObjId := by
          intro hx; rw [hx, hWakeObjs, hT1] at hRObj; cases hRObj
        have hRPre : st.getReply? rid = some r := by
          rw [SystemState.getReply?_eq_some_iff, ← hStNe rid.toObjId hRidNe, ← hWakeObjs]
          exact hRObj
        exact Or.inr ⟨tcb, rid, r, scId, hLk, hRO, hRPre, hNext,
          removeCallerReplyFrame_head_getReply?_next _ target rid r scId hInvWake hR hNext _ hRun,
          removeCallerReplyFrame_head_preserves_donationChainWellFormedExcept _ _ target rid r scId
            hInvWake hChainWake hR hNext hRun⟩
      · exact Or.inl (removeCallerReplyFrame_preserves_donationChainWellFormed _ _ target rid
          hInvWake hChainWake (fun r sc hR hN => hHead ⟨r, sc, hR, hN⟩) hRun)

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
    (replierHome ownerHome : CoreId)
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st)
    (hReplierIdleAllowed : ∀ tcb, st.getTcb? replierVtid.val = some tcb →
        passiveServerIdleAllowed tcb.ipcState)
    -- **WS-OD OD4.4**: the pop resolves its new owner from the context's reply
    -- stack, so at depth ≥ 2 it mints a `.donated` binding at the outer caller.
    (hStackValid : ∀ scId serverTid originalOwner,
        replyStackOuterCallerValid st scId serverTid originalOwner)
    (h : applyReplyDonationOnCore st replierVtid replierHome ownerHome = .ok st'') :
    ipcInvariantFull st'' := by
  rcases applyReplyDonationOnCore_ok_decompose st st'' replierVtid replierHome ownerHome h with ⟨_, hEq⟩ | ⟨scId, owner, n, st', hRet, hRes, hR, hEq⟩
  · rw [hEq]; exact hInv
  · have hFull' : ipcInvariantFull st' :=
      returnDonatedSchedContext_preserves_ipcInvariantFull st st' replierVtid scId owner
        hObjInv hInv hRet hReplierIdleAllowed n
        (donationReturnOuterValid_of_stackValid
          (hStackValid scId replierVtid.val owner) hRes) hR
    obtain ⟨pTcb, hPPre, _, _, _, hNe⟩ :=
      replyDonationReturn?_some_char st replierVtid.val scId owner
        (donationOwnerValidExcept_of_donationOwnerValid owner hInv.donationOwnerValid) hRet
    obtain ⟨_, ⟨pTcb0, hPPre0, hPPost⟩, _⟩ :=
      returnDonatedSchedContext_getTcb?_char st st' replierVtid.val scId owner hObjInv hNe n hR
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
    -- The deschedule writes only the placed core's queue and `current` slot --
    -- and nothing at all when the state places the replier on no core.
    rw [hEq]
    refine ipcInvariantFull_of_descheduleFrame stM _ hFullM
      (descheduleAtPlacement_preserves_objects stM replierVtid.val)
      (descheduleAtPlacement_passiveServerIdleFrame stM replierVtid.val
        (fun tcb hTcb => ?_))
    rw [hMObjs] at hTcb
    have hEqT : { pTcb with schedContextBinding := .unbound } = tcb :=
      Option.some.inj (hPPost.symm.trans ((getTcb?_eq_some_iff st' _ tcb).mpr hTcb))
    exact Or.inr (by rw [← hEqT]; exact hReplierIdleAllowed pTcb hPPre)



/-- WS-RR RR3.12: `applyReplyDonationOnCore` **establishes** the full bundle from the
form relaxed at the thread the reply woke — the cross-core counterpart of
`applyReplyDonation_establishes_ipcInvariantFull_of_except`, and the second half of
the live `.reply` chain's honest statement.

Same three stages, and the same single pre-state condition tying the halves together:
if anything is donated by the woken thread, this replier's donation return is exactly
it.  Only the return touches an object, so the migration and the deschedule carry the
full bundle across their frames unchanged. -/
theorem applyReplyDonationOnCore_establishes_ipcInvariantFull_of_except
    (st st'' : SystemState) (replierVtid : SeLe4n.ValidThreadId)
    (woken : SeLe4n.ThreadId)
    (replierHome ownerHome : CoreId)
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFullExceptDonationOwner st woken)
    (hDonationReturned : ∀ (s : SeLe4n.ThreadId) (sTcb : TCB) (sc : SeLe4n.SchedContextId),
      st.objects[s.toObjId]? = some (.tcb sTcb) →
      sTcb.schedContextBinding = .donated sc woken →
      replyDonationReturn? st replierVtid.val = some (sc, woken))
    (hReplierIdleAllowed : ∀ tcb, st.getTcb? replierVtid.val = some tcb →
        passiveServerIdleAllowed tcb.ipcState)
    -- **WS-OD OD4.4**: the pop resolves its new owner from the context's reply
    -- stack, so at depth ≥ 2 it mints a `.donated` binding at the outer caller.
    (hStackValid : ∀ scId serverTid originalOwner,
        replyStackOuterCallerValid st scId serverTid originalOwner)
    (h : applyReplyDonationOnCore st replierVtid replierHome ownerHome = .ok st'') :
    ipcInvariantFull st'' := by
  by_cases hAny : ∃ (s : SeLe4n.ThreadId) (sTcb : TCB) (sc : SeLe4n.SchedContextId),
      st.objects[s.toObjId]? = some (.tcb sTcb) ∧ sTcb.schedContextBinding = .donated sc woken
  · obtain ⟨s0, sTcb0, sc0, hS0, hB0⟩ := hAny
    have hRetEq := hDonationReturned s0 sTcb0 sc0 hS0 hB0
    rcases applyReplyDonationOnCore_ok_decompose st st'' replierVtid replierHome ownerHome h with ⟨hNone, _⟩ | ⟨scId, owner, n, st', hRet, hRes, hR, hEq⟩
    · rw [hRetEq] at hNone; cases hNone
    · obtain ⟨rfl, rfl⟩ : sc0 = scId ∧ woken = owner := by
        have := hRetEq.symm.trans hRet
        simpa using this
      have hFull' : ipcInvariantFull st' :=
        returnDonatedSchedContext_establishes_ipcInvariantFull_of_except st st' replierVtid sc0
          woken hObjInv hInv hRet hReplierIdleAllowed n
          (donationReturnOuterValid_of_stackValid
            (hStackValid sc0 replierVtid.val woken) hRes) hR
      obtain ⟨pTcb, hPPre, _, _, _, hNe⟩ :=
        replyDonationReturn?_some_char st replierVtid.val sc0 woken
          hInv.donationOwnerValidExcept hRet
      obtain ⟨_, ⟨pTcb0, hPPre0, hPPost⟩, _⟩ :=
        returnDonatedSchedContext_getTcb?_char st st' replierVtid.val sc0 woken hObjInv hNe n hR
      have hPEq : pTcb0 = pTcb := Option.some.inj (hPPre0.symm.trans hPPre)
      rw [hPEq] at hPPost
      let stM : SystemState := migrateSchedContextReplenishment st' sc0 replierHome ownerHome
      have hMObjs : stM.objects = st'.objects := migrateSchedContextReplenishment_objects _ _ _ _
      have hMRq := migrateSchedContextReplenishment_runQueue_current_eq st' sc0 replierHome
        ownerHome bootCoreId
      have hFullM : ipcInvariantFull stM :=
        ipcInvariantFull_of_descheduleFrame st' stM hFull' hMObjs
          (passiveServerIdleFrame.of_objects_scheduler_eq hMObjs hMRq.1 hMRq.2)
      rw [hEq]
      refine ipcInvariantFull_of_descheduleFrame stM _ hFullM
        (descheduleAtPlacement_preserves_objects stM replierVtid.val)
        (descheduleAtPlacement_passiveServerIdleFrame stM replierVtid.val
          (fun tcb hTcb => ?_))
      rw [hMObjs] at hTcb
      have hEqT : { pTcb with schedContextBinding := .unbound } = tcb :=
        Option.some.inj (hPPost.symm.trans ((getTcb?_eq_some_iff st' _ tcb).mpr hTcb))
      exact Or.inr (by rw [← hEqT]; exact hReplierIdleAllowed pTcb hPPre)
  · exact applyReplyDonationOnCore_preserves_ipcInvariantFull st st'' replierVtid
      replierHome ownerHome hObjInv
      (ipcInvariantFull_of_exceptDonationOwner hInv
        (donationOwnerValid_of_except_of_no_donation_owned_by hInv.donationOwnerValidExcept
          (fun tid tcb sc hTcb hBind => hAny ⟨tid, tcb, sc, hTcb, hBind⟩)))
      hReplierIdleAllowed hStackValid h

-- ============================================================================
-- §5  RR2.11 — the cross-core `.reply` chain
-- ============================================================================

/-- WS-RR RR2.11: `applyReplyDonationOnCore` preserves the object store's
extended invariant — the return through `returnDonatedSchedContext`, the
migration and the deschedule through their object frames. -/
theorem applyReplyDonationOnCore_preserves_objects_invExt
    (st st'' : SystemState) (replierVtid : SeLe4n.ValidThreadId)
    (replierHome ownerHome : CoreId)
    (hObjInv : st.objects.invExt)
    (h : applyReplyDonationOnCore st replierVtid replierHome ownerHome = .ok st'') :
    st''.objects.invExt := by
  rcases applyReplyDonationOnCore_ok_decompose st st'' replierVtid replierHome ownerHome h with ⟨_, hEq⟩ | ⟨scId, owner, n, st', _, _, hR, hEq⟩
  · rw [hEq]; exact hObjInv
  · have hInv' := returnDonatedSchedContext_preserves_objects_invExt st st' replierVtid.val scId
      owner hObjInv n hR
    rw [hEq, descheduleAtPlacement_preserves_objects, migrateSchedContextReplenishment_objects]
    exact hInv'

/-- **WS-RR RR3.12: the live cross-core `.reply` dispatch preserves
`ipcInvariantFull` on every path — the donating one included.**

The reply chain is *not* invariant-preserving stage by stage, and this is the
theorem that says what it is instead.  `endpointReplyOnCore` wakes the answered
caller `.ready` while the recorded server still holds `.donated _ caller`; the
donated SchedContext comes back only at the next stage, because the server needs
that budget *while* it replies (the AUD-3 ordering).  So the intermediate state
satisfies `ipcInvariantFullExceptDonationOwner … target` and nothing stronger, and
`applyReplyDonationOnCore` is what closes the relaxation.

`hDonationReturned` is the one condition that ties the two halves together, and it
is about the **pre**-state: *if* anything is donated by the answered caller, the
recorded reply server's donation return is exactly that donation.  True on the
seL4-MCS path, because a caller donates to the very server that later answers it.
When nothing is donated it is vacuous and the chain runs on the unrelaxed route.

This supersedes the `hNoDonationOwnedBy` form below, which is the same statement
restricted to non-donating replies; that one is kept because it is what the bare
`endpointReplyOnCore` bundle can offer on its own. -/
theorem endpointReplyCrossCoreDispatch_establishes_ipcInvariantFull
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hDonationReturned : ∀ (expected : SeLe4n.ThreadId),
      recordedReplyServer? st target = some expected →
      ∀ (s : SeLe4n.ThreadId) (sTcb : TCB) (sc : SeLe4n.SchedContextId),
        st.objects[s.toObjId]? = some (.tcb sTcb) →
        sTcb.schedContextBinding = .donated sc target →
        replyDonationReturn? st expected = some (sc, target))
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hServerIdleAllowed : ∀ (expected : SeLe4n.ThreadId), recordedReplyServer? st target
        = some expected →
      ∀ tcb, st.getTcb? expected = some tcb → passiveServerIdleAllowed tcb.ipcState)
    -- **WS-OD OD4.4**: the donation return resolves its new owner from the
    -- context's reply stack, so at depth ≥ 2 it mints a `.donated` binding at the
    -- outer caller.  Stated at the state the pop actually runs at -- the reply leg
    -- commits first -- which is a pre-state-computable expression, so the
    -- de-threading discipline is respected.
    (hStackValid : ∀ scId serverTid originalOwner,
        replyStackOuterCallerValid (endpointReplyOnCore replier target msg executingCore st).1
          scId serverTid originalOwner) :
    ipcInvariantFull (endpointReplyCrossCoreDispatch replier target msg executingCore st).1 := by
  have hReplyExc : ipcInvariantFullExceptDonationOwner
      (endpointReplyOnCore replier target msg executingCore st).1 target :=
    endpointReplyOnCore_preserves_ipcInvariantFullExceptDonationOwner replier target msg
      executingCore st hInv hObjInv hAllBudgetsNone
  have hReplyInv : (endpointReplyOnCore replier target msg executingCore st).1.objects.invExt :=
    endpointReplyOnCore_preserves_objects_invExt replier target msg executingCore st hObjInv
  have hBack := endpointReplyOnCore_tcb_backward replier target msg executingCore st hObjInv
  have hBindBack := endpointReplyOnCore_sameSchedContextBindings replier target msg executingCore
    st hObjInv
  have hFrame := endpointReplyOnCore_donationOwnerFrameExcept replier target msg executingCore
    st hObjInv
  unfold endpointReplyCrossCoreDispatch
  cases hRep : endpointReplyOnCore replier target msg executingCore st with
  | mk st1 res =>
    rw [hRep] at hReplyExc hReplyInv hBack hBindBack hFrame hStackValid
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
          -- Transport the donation-return condition across the reply.  The reply
          -- writes no `schedContextBinding`, so a donation present after it was
          -- present before it, and the recorded server's return reads the same
          -- binding on both sides.
          have hDonMid : ∀ (s : SeLe4n.ThreadId) (sTcb : TCB) (sc : SeLe4n.SchedContextId),
              st1.objects[s.toObjId]? = some (.tcb sTcb) →
              sTcb.schedContextBinding = .donated sc target →
              replyDonationReturn? st1 expectedV.val = some (sc, target) := by
            intro s sTcb sc hS hB
            obtain ⟨sTcb0, hS0, hB0⟩ := hBindBack s sTcb hS
            have hPre := hDonationReturned expected hRec s sTcb0 sc hS0 (hB0.trans hB)
            obtain ⟨eTcb, hELk, hEB⟩ :=
              replyDonationReturn?_some_lookup st expected sc target hPre
            obtain ⟨eTcb', hE', hEB', _⟩ :=
              hFrame.tcbForward expected eTcb (lookupTcb_some_objects st expected eTcb hELk)
            rw [hExpV]
            rw [replyDonationReturn?_eq_of_binding_agree hELk hE' hEB']
            exact hPre
          cases hDon : applyReplyDonationOnCore st1 expectedV
              (determineTargetCore st expected) (replyDonationOwnerHome st expected) with
          | error e => simp only; exact hInv
          | ok st2 =>
            simp only
            have hDonFull : ipcInvariantFull st2 :=
              applyReplyDonationOnCore_establishes_ipcInvariantFull_of_except st1 st2 expectedV
                target _ _ hReplyInv hReplyExc hDonMid hAllowed hStackValid hDon
            have hDonInv : st2.objects.invExt :=
              applyReplyDonationOnCore_preserves_objects_invExt st1 st2 expectedV _ _
                hReplyInv hDon
            exact propagatePipChainCrossCore_preserves_ipcInvariantFull st2 expected executingCore
              _ hDonInv hDonFull

/-- WS-RR RR2.11 / WS-RR RR3.12: the live cross-core `.reply` dispatch preserves
`ipcInvariantFull` on a reply whose answered caller donated nothing — the
non-donating instance of `endpointReplyCrossCoreDispatch_establishes_ipcInvariantFull`
above, where `hDonationReturned` is vacuous because its premise cannot be met.

Kept as its own statement because `hNoDonationOwnedBy` is what the *bare*
`endpointReplyOnCore` bundle can be stated against; the composite above is what the
donating path needs. -/
theorem endpointReplyCrossCoreDispatch_preserves_ipcInvariantFull
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hNoDonationOwnedBy : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB)
      (scId : SeLe4n.SchedContextId),
      st.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.schedContextBinding ≠ .donated scId target)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hServerIdleAllowed : ∀ (expected : SeLe4n.ThreadId), recordedReplyServer? st target
        = some expected →
      ∀ tcb, st.getTcb? expected = some tcb → passiveServerIdleAllowed tcb.ipcState)
    -- **WS-OD OD4.4**: see `endpointReplyCrossCoreDispatch_establishes_ipcInvariantFull`.
    (hStackValid : ∀ scId serverTid originalOwner,
        replyStackOuterCallerValid (endpointReplyOnCore replier target msg executingCore st).1
          scId serverTid originalOwner) :
    ipcInvariantFull (endpointReplyCrossCoreDispatch replier target msg executingCore st).1 :=
  endpointReplyCrossCoreDispatch_establishes_ipcInvariantFull replier target msg executingCore
    st hInv hObjInv
    (fun _ _ s sTcb sc hS hB => absurd hB (hNoDonationOwnedBy s sTcb sc hS))
    hAllBudgetsNone hServerIdleAllowed hStackValid

-- ============================================================================
-- §6  WS-RM (`v0.35.6`) — the composite payoff: the chain across the dispatch
-- ============================================================================

/-- **WS-RM (`v0.35.6`): the context the answered caller's reply frame heads is
the one the recorded reply server holds.**

The third of this tree's *local coherence facts* about one reply, beside
`replyDonationOwnerIsAnsweredCaller` (the returned donation is owned by the thread
the reply answers) and `replyStackHeadIsAnsweredReply` (the returned context's
stack head is that thread's own reply object).  It is this one's converse: the
other two start from a server that holds a donation, this one starts from a frame
that heads a context and names its holder.

True on the seL4-MCS path, because `applyCallDonation` mints the `.donated`
binding at the very server the caller later replies through and pushes the
caller's own `replyObject` as that context's stack head — the two writes of one
step.  **Not entailed by `ipcInvariantFull`**: `donationOwnerValid` relates a
caller's recorded reply target to no donation, and `donationChainWellFormed`
carries no binding clause at all (see its docstring's *what is deliberately
absent*).  So it is stated, for exactly the reason WS-RR RR7.22 stated
`donationHolderIsReplyTarget` from the cancellation end.

Stated on the **pre-state**, like `hDonationReturned` on the bundle composite
beside it and unlike `hStackValid`: `replyStackOuterCallerValid`'s subject is a
state the pop runs on, whereas a `schedContextBinding` is something the reply leg
provably does not write (`endpointReplyOnCore_donationOwnerFrameExcept`), so the
transport belongs inside the proof rather than on every caller.  That also makes
the fault reply's two occurrences one fact rather than two spellings differing
only in a message the question never reads. -/
def answeredHeadContextIsServerDonation (st : SystemState) (target : SeLe4n.ThreadId) : Prop :=
  ∀ (tcb : TCB) (rid : SeLe4n.ReplyId) (r : Reply) (scId : SeLe4n.SchedContextId),
    lookupTcb st target = some tcb → tcb.replyObject = some rid →
    st.getReply? rid = some r → r.next = some (.head scId) →
    ∀ expected, recordedReplyServer? st target = some expected →
      ∃ owner, replyDonationReturn? st expected = some (scId, owner)

/-- A reply that answers no resolvable caller heads nothing, so the fact is
vacuous — the discharge every reply outside the donating path takes. -/
theorem answeredHeadContextIsServerDonation_of_no_caller (st : SystemState)
    (target : SeLe4n.ThreadId) (h : lookupTcb st target = none) :
    answeredHeadContextIsServerDonation st target := by
  intro _ _ _ _ hLk
  rw [h] at hLk
  cases hLk

/-- And so is a reply by a caller holding no reply object. -/
theorem answeredHeadContextIsServerDonation_of_no_reply (st : SystemState)
    (target : SeLe4n.ThreadId) (tcb : TCB)
    (hLk : lookupTcb st target = some tcb) (hRO : tcb.replyObject = none) :
    answeredHeadContextIsServerDonation st target := by
  intro tcb' _ _ _ hLk' hRO'
  rw [hLk] at hLk'
  obtain rfl : tcb' = tcb := Option.some.inj hLk'.symm
  rw [hRO] at hRO'
  cases hRO'

-- ============================================================================
-- WS-HP HP2: the two donation-pop triggers agree on every coherent state
-- ============================================================================

/-- **WS-HP HP2.1: the head-driven trigger implies the binding-driven one.**

The safety net that makes HP4 a *refactor* rather than a semantic change: on every
state satisfying `donationOwnerValid` and the coherence fact
`answeredHeadContextIsServerDonation`, a reply whose answered frame heads a
context is exactly a reply whose recorded server holds that context's donation --
and the holder the head-driven resolver reports **is** that recorded server.

The second conjunct is the load-bearing half and it is not cosmetic: the
binding-driven trigger takes its `serverTid` from `recordedReplyServer?` while the
head-driven one takes it from `SchedContext.boundThread`, and
`donationOwnerValid`'s first clause -- a `.donated scId _` holder is what `scId`
is bound to -- is what identifies them.  Without it the flip could point
`returnDonatedSchedContext` at a different thread, which is precisely what its own
`boundThread` guard exists to refuse.

Stated with `lookupTcb` rather than `getTcb?` at the answered caller because
`answeredHeadContextIsServerDonation` is: the two differ on a reserved id, and a
reserved thread is not a caller this path can reach. -/
theorem answeredFrameHeadContext?_implies_serverDonation (st : SystemState)
    (target : SeLe4n.ThreadId) (tcb : TCB)
    (scId : SeLe4n.SchedContextId) (holder expected : SeLe4n.ThreadId)
    (hOwnerValid : donationOwnerValid st)
    (hHeadReturned : answeredHeadContextIsServerDonation st target)
    (hLk : lookupTcb st target = some tcb)
    (hExp : recordedReplyServer? st target = some expected)
    (h : answeredFrameHeadContext? st target = some (scId, holder)) :
    holder = expected ∧
      ∃ owner, endpointReplyServerDonation? st target = some (scId, owner) := by
  obtain ⟨rid, hRid, hHead, hBt⟩ := answeredFrameHeadContext?_eq_some h
  obtain ⟨r, sc, hR, hN, hSc, _⟩ := replyFrameHeadContext?_eq_some hHead
  have hGet : st.getTcb? target = some tcb := getTcb?_of_lookupTcb st target tcb hLk
  have hRO : tcb.replyObject = some rid := by
    unfold answeredReplyObject? at hRid; rw [hGet] at hRid; exact hRid
  have hBound : sc.boundThread = some holder := by rw [hSc] at hBt; exact hBt
  obtain ⟨owner, hRet⟩ := hHeadReturned tcb rid r scId hLk hRO hR hN expected hExp
  obtain ⟨eTcb, hLkE, hB⟩ := replyDonationReturn?_some_lookup st expected scId owner hRet
  have hGetE : st.getTcb? expected = some eTcb := getTcb?_of_lookupTcb st expected eTcb hLkE
  obtain ⟨⟨sc', hSc'Obj, hSc'Bound⟩, _⟩ :=
    hOwnerValid expected eTcb scId owner ((getTcb?_eq_some_iff st expected eTcb).mp hGetE) hB
  have hSame : sc' = sc :=
    KernelObject.schedContext.inj (Option.some.inj
      (hSc'Obj.symm.trans ((getSchedContext?_eq_some_iff st scId sc).mp hSc)))
  refine ⟨?_, owner, ?_⟩
  · rw [hSame] at hSc'Bound
    exact Option.some.inj (hBound.symm.trans hSc'Bound)
  · unfold endpointReplyServerDonation? endpointReplyDonation?
    simp only [hExp, hGetE, hB]

/-- **WS-HP HP2.4: the head of the popped context IS the answered caller's reply
object** -- `replyStackHeadIsAnsweredReply`'s content, as a theorem of the
head-driven resolver rather than a hypothesis a caller supplies.

Under this trigger it is immediate: the resolver reads the context off the frame's
own `.head` link and validates the context's `scReply` against that same frame, so
the head and the answered reply object are the one `rid` the resolver matched.
HP7 is what retires the stated predicate; this is the theorem that lets it. -/
theorem answeredFrameHeadContext?_head_is_answered_reply (st : SystemState)
    (target : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (h : answeredFrameHeadContext? st target = some (scId, holder)) :
    ∃ rid : SeLe4n.ReplyId, answeredReplyObject? st target = some rid ∧
      replyStackHead? st scId = some rid := by
  obtain ⟨rid, hRid, hHead, _⟩ := answeredFrameHeadContext?_eq_some h
  obtain ⟨_, sc, _, _, hSc, hScReply⟩ := replyFrameHeadContext?_eq_some hHead
  exact ⟨rid, hRid, by unfold replyStackHead?; rw [hSc]; exact hScReply⟩

/-- **WS-HP HP2.4: the popped context's head validates** -- `donationHeadOf?`
succeeds with the answered frame, so the pop's own head validation is a
consequence of the trigger firing rather than a step that can refuse.

This is what makes the head-driven pop provably reach its stores: under the
binding-driven trigger `donationHeadOf?` could refuse (the context's head need not
be the answered frame), and `donationHeadResolves` had to be carried as a
hypothesis. -/
theorem answeredFrameHeadContext?_donationHeadOf (st : SystemState)
    (target : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (h : answeredFrameHeadContext? st target = some (scId, holder)) :
    ∃ (rid : SeLe4n.ReplyId) (r : Reply) (sc : SchedContext),
      answeredReplyObject? st target = some rid ∧
      st.getSchedContext? scId = some sc ∧
      donationHeadOf? st scId sc = .ok (some (rid, r)) := by
  obtain ⟨rid, hRid, hHead, _⟩ := answeredFrameHeadContext?_eq_some h
  obtain ⟨r, sc, hR, hN, hSc, hScReply⟩ := replyFrameHeadContext?_eq_some hHead
  refine ⟨rid, r, sc, hRid, hSc, ?_⟩
  unfold donationHeadOf?
  rw [hScReply]
  simp only [hR, hN, bne_self_eq_false, Bool.false_eq_true, if_false]

/-- **WS-HP HP2.4: the pop's `boundThread` guard is satisfied by construction.**

`returnDonatedSchedContext` refuses when the context is not bound to the
`serverTid` it was handed.  Under the binding-driven trigger that was defence in
depth against a drift `donationOwnerValid` rules out; under the head-driven one
the holder *is* read from `SchedContext.boundThread`, so the guard cannot fire --
the operation reads the fact it used to check, which is the honest direction. -/
theorem answeredFrameHeadContext?_boundThread (st : SystemState)
    (target : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (h : answeredFrameHeadContext? st target = some (scId, holder)) :
    ∃ sc : SchedContext, st.getSchedContext? scId = some sc ∧
      sc.boundThread = some holder := by
  obtain ⟨_, _, hHead, hBt⟩ := answeredFrameHeadContext?_eq_some h
  obtain ⟨_, sc, _, _, hSc, _⟩ := replyFrameHeadContext?_eq_some hHead
  exact ⟨sc, hSc, by rw [hSc] at hBt; exact hBt⟩

/-- **WS-HP HP2.3's negative twin: the state `spliceOutTheCut` creates under a
binding-driven trigger, named exactly.**

A frame that *heads* a context while the thread its caller recorded as its reply
server holds no donation of that context falsifies
`answeredHeadContextIsServerDonation` outright.  That is the orphan head the
splice produces and the sever does not
(`severAtCut_pop_leaves_no_head`, `IPC/Invariant/Defs.lean`): the splice's pop
re-heads the frame below a cut, whose caller recorded a server that the
cancellation removed.

So this is the checkable form of "the splice breaks the equivalence HP4 stands
on", and it is why HP6 may not precede HP4. -/
theorem answeredHeadContextIsServerDonation_false_of_orphan_head (st : SystemState)
    (target : SeLe4n.ThreadId) (tcb : TCB) (rid : SeLe4n.ReplyId) (r : Reply)
    (scId : SeLe4n.SchedContextId) (expected : SeLe4n.ThreadId)
    (hLk : lookupTcb st target = some tcb) (hRO : tcb.replyObject = some rid)
    (hR : st.getReply? rid = some r) (hN : r.next = some (.head scId))
    (hExp : recordedReplyServer? st target = some expected)
    (hNoDon : ∀ owner, replyDonationReturn? st expected ≠ some (scId, owner)) :
    ¬ answeredHeadContextIsServerDonation st target := by
  intro hFact
  obtain ⟨owner, hRet⟩ := hFact tcb rid r scId hLk hRO hR hN expected hExp
  exact hNoDon owner hRet

/-- **WS-HP HP2.3: and at such a state the two triggers demonstrably disagree.**

The head-driven resolver fires -- the frame heads the context, the context names
it back, and it is bound to a holder -- while the binding-driven one answers
`none`, because the recorded server holds nothing.  So a `spliceOutTheCut` cut
landing before HP4 would leave the live reply path popping on a fact that is
false of exactly the states the splice makes reachable; and one landing *after*
HP4 is the intended behaviour, since the head-driven pop returns the context to
the caller the surviving stack names.

This is the sharp statement of plan §4's second forced ordering, and the reason
it is a theorem rather than a note. -/
theorem donationPopTriggers_disagree_at_orphan_head (st : SystemState)
    (target : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (r : Reply)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (holder expected : SeLe4n.ThreadId)
    (hRid : answeredReplyObject? st target = some rid)
    (hR : st.getReply? rid = some r) (hN : r.next = some (.head scId))
    (hSc : st.getSchedContext? scId = some sc) (hScReply : sc.scReply = some rid)
    (hBound : sc.boundThread = some holder)
    (hExp : recordedReplyServer? st target = some expected)
    (hNoDon : endpointReplyDonation? st expected = none) :
    answeredFrameHeadContext? st target = some (scId, holder) ∧
      endpointReplyServerDonation? st target = none := by
  refine ⟨answeredFrameHeadContext?_of_head st target rid scId holder hRid
    (replyFrameHeadContext?_of_head st rid r scId sc hR hN hSc hScReply) ?_, ?_⟩
  · rw [hSc]; exact hBound
  · unfold endpointReplyServerDonation?
    rw [hExp]; exact hNoDon

/-- **WS-RM (`v0.35.6`): the live cross-core `.reply` dispatch preserves the
donation chain — the theorem the workstream exists for.**

Neither half preserves it on its own, and this says what they do instead.  The
reply leg answers a caller and takes its frame off the reply stack; when that
frame *heads* a scheduling context `Reply.consumed` keeps its links, deliberately,
because the donation pop that follows in the same transition validates the head by
that very link (WS-OD plan §3.3).  So the intermediate state satisfies
`donationChainWellFormedExcept … rid` and nothing stronger, and
`applyReplyDonationOnCore` is what closes the relaxation — exactly as it closes
`ipcInvariantFullExceptDonationOwner` on the bundle side.

`answeredHeadContextIsServerDonation` is the one condition that ties the two
halves together, and it is the chain analogue of `hDonationReturned` in every
respect, its **pre**-state statement included: *if* the answered frame heads a
context, the recorded reply server's donation return is that context's.  When the
answered frame heads nothing it is vacuous, and the chain runs on the unrelaxed
route — which is every reply in a tree with no donation. -/
theorem endpointReplyCrossCoreDispatch_preserves_donationChainWellFormed
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState)
    (hObjInv : st.objects.invExt)
    (hChain : donationChainWellFormed st)
    (hHeadReturned : answeredHeadContextIsServerDonation st target) :
    donationChainWellFormed
      (endpointReplyCrossCoreDispatch replier target msg executingCore st).1 := by
  have hReplyInv : (endpointReplyOnCore replier target msg executingCore st).1.objects.invExt :=
    endpointReplyOnCore_preserves_objects_invExt replier target msg executingCore st hObjInv
  have hCases := endpointReplyOnCore_donationChain_cases replier target msg executingCore st
    hObjInv hChain
  -- The reply leg writes no `schedContextBinding`, which is what lets the
  -- pre-state fact be read at the state the pop runs on.
  have hFrame := endpointReplyOnCore_donationOwnerFrameExcept replier target msg executingCore
    st hObjInv
  unfold endpointReplyCrossCoreDispatch
  cases hRep : endpointReplyOnCore replier target msg executingCore st with
  | mk st1 res =>
    rw [hRep] at hReplyInv hCases hFrame
    cases res with
    | error e => exact hChain
    | ok replySgi =>
      simp only
      cases hRec : recordedReplyServer? st target with
      | none => simp only; exact hChain
      | some expected =>
        simp only
        cases hEV : SeLe4n.ThreadId.toValid? expected with
        | none => simp only; exact hChain
        | some expectedV =>
          simp only
          have hExpV : expectedV.val = expected :=
            SeLe4n.ThreadId.toValid?_some_val_eq expected expectedV hEV
          -- The relaxation, if any, is at the frame the pop is about to clear,
          -- and the reply server's donation return is that frame's context.
          have hDon : donationChainWellFormed st1 ∨
              ∃ (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId)
                (r1 : Reply),
                donationChainWellFormedExcept st1 rid ∧
                replyDonationReturn? st1 expectedV.val = some (scId, owner) ∧
                st1.getReply? rid = some r1 ∧ r1.next = some (.head scId) := by
            rcases hCases with hFull | ⟨tcb, rid, r, scId, hLk, hRO, hRPre, hNext,
              ⟨r1, hR1, hN1⟩, hExc⟩
            · exact Or.inl hFull
            · obtain ⟨owner, hRetPre⟩ :=
                hHeadReturned tcb rid r scId hLk hRO hRPre hNext expected hRec
              have hRet : replyDonationReturn? st1 expected = some (scId, owner) := by
                obtain ⟨eTcb, hELk, _⟩ :=
                  replyDonationReturn?_some_lookup st expected scId owner hRetPre
                obtain ⟨_, hE', hEB', _⟩ :=
                  hFrame.tcbForward expected eTcb (lookupTcb_some_objects st expected eTcb hELk)
                rw [replyDonationReturn?_eq_of_binding_agree hELk hE' hEB']
                exact hRetPre
              exact Or.inr ⟨rid, scId, owner, r1, hExc, by rw [hExpV]; exact hRet, hR1, hN1⟩
          cases hApply : applyReplyDonationOnCore st1 expectedV
              (determineTargetCore st expected)
              (replyDonationOwnerHome st expected) with
          | error e => simp only; exact hChain
          | ok st2 =>
            simp only
            have hInv2 : st2.objects.invExt :=
              applyReplyDonationOnCore_preserves_objects_invExt st1 st2 expectedV _ _
                hReplyInv hApply
            have hChain2 : donationChainWellFormed st2 := by
              rcases hDon with hFull | ⟨rid, scId, owner, r1, hExc, hRet, hR1, hN1⟩
              · exact applyReplyDonationOnCore_preserves_donationChainWellFormed_of_except
                  st1 st2 expectedV _ _ hReplyInv (fun _ _ _ _ _ _ => hFull)
                  (fun _ _ _ ridX _ _ _ _ => donationChainWellFormedExcept_of_wellFormed hFull ridX)
                  (fun _ => hFull) hApply
              -- The popped context is the one the relaxed frame heads, so the head
              -- the pop validates *is* that frame and the relaxation is discharged.
              · have hSc : ∃ sc, st1.getSchedContext? scId = some sc ∧ sc.scReply = some rid := by
                  obtain ⟨sc, hScObj, hScReply⟩ := hExc.headLinkResolves rid r1 scId
                    ((SystemState.getReply?_eq_some_iff st1 rid r1).mp hR1) hN1
                  exact ⟨sc, (SystemState.getSchedContext?_eq_some_iff st1 scId sc).mpr hScObj,
                    hScReply⟩
                obtain ⟨sc, hScGet, hScReply⟩ := hSc
                refine applyReplyDonationOnCore_preserves_donationChainWellFormed_of_except
                  st1 st2 expectedV _ _ hReplyInv ?_ ?_ ?_ hApply
                · -- A context whose stack head is `rid` has a head: this arm is vacuous.
                  intro scId' owner' sc' hRet' hSc' hHead'
                  obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj (hRet'.symm.trans hRet))
                  rw [hScGet] at hSc'
                  obtain rfl : sc' = sc := Option.some.inj hSc'.symm
                  have hKey := donationHeadOf?_ok_key st1 scId' sc' none hHead'
                  rw [hScReply] at hKey
                  cases hKey
                · -- And the head it validates is exactly the relaxed frame.
                  intro scId' owner' sc' ridX rX hRet' hSc' hHead'
                  obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj (hRet'.symm.trans hRet))
                  rw [hScGet] at hSc'
                  obtain rfl : sc' = sc := Option.some.inj hSc'.symm
                  have hKey := donationHeadOf?_ok_key st1 scId' sc' (some (ridX, rX)) hHead'
                  rw [hScReply] at hKey
                  obtain rfl : ridX = rid := Option.some.inj (by simpa using hKey)
                  exact hExc
                · intro hNone; rw [hNone] at hRet; cases hRet
            exact propagatePipChainCrossCore_preserves_donationChainWellFormed st2 expected
              executingCore _ hInv2 hChain2


end SeLe4n.Kernel
