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
    (st st'' : SystemState) (rid : SeLe4n.ReplyId) (targetVtid : SeLe4n.ValidThreadId)
    (holderHome ownerHome : CoreId)
    (hObjInv : st.objects.invExt)
    -- **WS-HP HP4.3**: the three chain conditions are quantified over the
    -- head-driven trigger, which is the pop's own case split after the flip.
    (hChainNone : ∀ scId holder sc,
      replyFrameHeadHolder? st rid = some (scId, holder) →
      st.getSchedContext? scId = some sc →
      donationHeadOf? st scId sc = .ok none → donationChainWellFormed st)
    (hChainHead : ∀ scId holder sc hid r,
      replyFrameHeadHolder? st rid = some (scId, holder) →
      st.getSchedContext? scId = some sc →
      donationHeadOf? st scId sc = .ok (some (hid, r)) → donationChainWellFormedExcept st hid)
    (hChainNoReturn : replyFrameHeadHolder? st rid = none →
      donationChainWellFormed st)
    (h : applyReplyDonationOnCore st rid targetVtid holderHome ownerHome = .ok st'') :
    donationChainWellFormed st'' := by
  rcases applyReplyDonationOnCore_ok_decompose st st'' rid targetVtid holderHome ownerHome h with ⟨hNone, hEq⟩ | ⟨scId, holderVtid, n, st', hHead, _, hRet, hEq⟩
  · rw [hEq]; exact hChainNoReturn hNone
  · have hChain' : donationChainWellFormed st' :=
      returnDonatedSchedContext_preserves_donationChainWellFormed_of_except st st'
        holderVtid.val scId (replyDonationRecipient st scId targetVtid.val) n hObjInv
        (hChainNone scId holderVtid.val · hHead)
        (hChainHead scId holderVtid.val · · · hHead) hRet
    rw [hEq]
    refine donationChainWellFormed_of_frame ?_ hChain'
    exact donationChainFrame.of_objects_eq
      (by rw [descheduleAtPlacement_preserves_objects, migrateSchedContextReplenishment_objects])

/-- **WS-RM (`v0.35.6`)**: what the cross-core reply leg leaves of the donation
chain.

Two outcomes, and the second is the whole point of the workstream.  The reply
leg's last step is `removeCallerReplyFrame`, which splices the answered frame
out from between its neighbours and then consumes the caller link.  On a frame that heads
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

`hHolderIdleAllowed` is the same precondition the single-core form carries, and
for the same reason: the deschedule hands `passiveServerIdle` an obligation for a
thread it previously had none for.  **WS-HP HP4.3**: both it and `hHolderDonation`
are quantified over the trigger, because the thread the step deschedules is now
read off `SchedContext.boundThread` rather than supplied by the caller. -/
theorem applyReplyDonationOnCore_preserves_ipcInvariantFull
    (st st'' : SystemState) (rid : SeLe4n.ReplyId) (targetVtid : SeLe4n.ValidThreadId)
    (holderHome ownerHome : CoreId)
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st)
    (hHolderDonation : replyFrameHeadHolderDonation st rid targetVtid.val)
    (hHolderIdleAllowed : ∀ scId holder,
        replyFrameHeadHolder? st rid = some (scId, holder) →
        ∀ tcb, st.getTcb? holder = some tcb → passiveServerIdleAllowed tcb.ipcState)
    -- **WS-OD OD4.4**: the pop resolves its new owner from the context's reply
    -- stack, so at depth ≥ 2 it mints a `.donated` binding at the outer caller.
    (hStackValid : ∀ scId serverTid originalOwner,
        replyStackOuterCallerValid st scId serverTid originalOwner)
    -- **`v0.35.157`**: the origin redirect's coherence obligation -- see the
    -- single-core `applyReplyDonation_preserves_ipcInvariantFull`.
    (hOriginCoherent : redirectedOriginFrameCoherent st rid targetVtid.val)
    (h : applyReplyDonationOnCore st rid targetVtid holderHome ownerHome = .ok st'') :
    ipcInvariantFull st'' := by
  rcases applyReplyDonationOnCore_ok_decompose st st'' rid targetVtid holderHome ownerHome h with ⟨_, hEq⟩ | ⟨scId, holderVtid, n, st', hHead, hRes, hR, hEq⟩
  · rw [hEq]; exact hInv
  · have hRet : replyDonationReturn? st holderVtid.val = some (scId, targetVtid.val) :=
      hHolderDonation scId holderVtid.val hHead
    have hIdle : ∀ tcb, st.getTcb? holderVtid.val = some tcb →
        passiveServerIdleAllowed tcb.ipcState := hHolderIdleAllowed scId holderVtid.val hHead
    obtain ⟨pTcb, hLk, hPB⟩ :=
      replyDonationReturn?_some_lookup st holderVtid.val scId targetVtid.val hRet
    have hPPre : st.getTcb? holderVtid.val = some pTcb :=
      getTcb?_of_lookupTcb st holderVtid.val pTcb hLk
    have hNe : replyDonationRecipient st scId targetVtid.val ≠ holderVtid.val := by
      intro hEqq
      have hUnb := returnDonatedSchedContext_ok_recipient_unbound st st' holderVtid.val scId
        (replyDonationRecipient st scId targetVtid.val) n hR pTcb (hEqq ▸ hLk)
      rw [hPB] at hUnb; cases hUnb
    -- **WS-HP HP10.7**: three cases, as in the single-core spine.
    have hFull' : ipcInvariantFull st' := by
      by_cases hNoOrigin : donationOriginRecipient? st scId = none
      · rw [replyDonationRecipient_eq_of_no_origin st scId targetVtid.val hNoOrigin] at hR
        exact returnDonatedSchedContext_preserves_ipcInvariantFull st st' holderVtid scId
          targetVtid.val hObjInv hInv hRet hIdle n
          (donationReturnOuterValid_of_stackValid
            (hStackValid scId holderVtid.val targetVtid.val) hRes) hR
      · obtain ⟨o, hOrigin⟩ : ∃ o, donationOriginRecipient? st scId = some o := by
          cases hc : donationOriginRecipient? st scId with
          | none => exact absurd hc hNoOrigin
          | some o => exact ⟨o, rfl⟩
        have hRecipEq : replyDonationRecipient st scId targetVtid.val = o :=
          replyDonationRecipient_eq_origin st hOrigin
        by_cases hSame : o = targetVtid.val
        · rw [hRecipEq, hSame] at hR
          exact returnDonatedSchedContext_preserves_ipcInvariantFull st st' holderVtid scId
            targetVtid.val hObjInv hInv hRet hIdle n
            (donationReturnOuterValid_of_stackValid
              (hStackValid scId holderVtid.val targetVtid.val) hRes) hR
        · rw [hRecipEq] at hR
          exact returnDonatedSchedContext_establishes_ipcInvariantFull_of_except_redirected
            st st' holderVtid scId targetVtid.val o hObjInv
            (ipcInvariantFullExceptDonationOwner_of_full targetVtid.val hInv) hRet
            (donationOriginRebindable_no_owner
              (hOriginCoherent scId holderVtid.val o hHead hOrigin hSame)
              (donationOriginRecipient?_resolves st hOrigin)
              (donationOriginRecipient?_rebindable st hOrigin))
            hIdle n
            (donationReturnOuterValid_of_stackValid (hStackValid scId holderVtid.val o) hRes) hR
    obtain ⟨_, ⟨pTcb0, hPPre0, hPPost⟩, _⟩ :=
      returnDonatedSchedContext_getTcb?_char st st' holderVtid.val scId
        (replyDonationRecipient st scId targetVtid.val) hObjInv hNe n hR
    have hPEq : pTcb0 = pTcb := Option.some.inj (hPPre0.symm.trans hPPre)
    rw [hPEq] at hPPost
    -- The migration writes only per-core replenish queues.
    let stM : SystemState := migrateSchedContextReplenishment st' scId holderHome ownerHome
    have hMObjs : stM.objects = st'.objects := migrateSchedContextReplenishment_objects _ _ _ _
    have hMRq := migrateSchedContextReplenishment_runQueue_current_eq st' scId holderHome
      ownerHome bootCoreId
    have hFullM : ipcInvariantFull stM :=
      ipcInvariantFull_of_descheduleFrame st' stM hFull' hMObjs
        (passiveServerIdleFrame.of_objects_scheduler_eq hMObjs hMRq.1 hMRq.2)
    -- The deschedule writes only the placed core's queue and `current` slot --
    -- and nothing at all when the state places the holder on no core.
    rw [hEq]
    refine ipcInvariantFull_of_descheduleFrame stM _ hFullM
      (descheduleAtPlacement_preserves_objects stM holderVtid.val)
      (descheduleAtPlacement_passiveServerIdleFrame stM holderVtid.val
        (fun tcb hTcb => ?_))
    rw [hMObjs] at hTcb
    have hEqT : { pTcb with schedContextBinding := .unbound } = tcb :=
      Option.some.inj (hPPost.symm.trans ((getTcb?_eq_some_iff st' _ tcb).mpr hTcb))
    exact Or.inr (by rw [← hEqT]; exact hIdle pTcb hPPre)



/-- WS-RR RR3.12: `applyReplyDonationOnCore` **establishes** the full bundle from the
form relaxed at the thread the reply woke — the cross-core counterpart of
`applyReplyDonation_establishes_ipcInvariantFull_of_except`, and the second half of
the live `.reply` chain's honest statement.

Same three stages, and the same single pre-state condition tying the halves together:
if anything is donated by the woken thread, this replier's donation return is exactly
it.  Only the return touches an object, so the migration and the deschedule carry the
full bundle across their frames unchanged. -/
theorem applyReplyDonationOnCore_establishes_ipcInvariantFull_of_except
    (st st'' : SystemState) (rid : SeLe4n.ReplyId) (targetVtid : SeLe4n.ValidThreadId)
    (woken : SeLe4n.ThreadId)
    (holderHome ownerHome : CoreId)
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFullExceptDonationOwner st woken)
    -- **WS-HP HP4.3**: re-keyed on the head-driven trigger, which names both the
    -- context and its holder -- see the single-core
    -- `applyReplyDonation_establishes_ipcInvariantFull_of_except`.
    (hDonationReturned : ∀ (s : SeLe4n.ThreadId) (sTcb : TCB) (sc : SeLe4n.SchedContextId),
      st.objects[s.toObjId]? = some (.tcb sTcb) →
      sTcb.schedContextBinding = .donated sc woken →
      replyFrameHeadHolder? st rid = some (sc, s))
    (hHolderDonation : replyFrameHeadHolderDonation st rid targetVtid.val)
    (hHolderIdleAllowed : ∀ scId holder,
        replyFrameHeadHolder? st rid = some (scId, holder) →
        ∀ tcb, st.getTcb? holder = some tcb → passiveServerIdleAllowed tcb.ipcState)
    -- **WS-OD OD4.4**: the pop resolves its new owner from the context's reply
    -- stack, so at depth ≥ 2 it mints a `.donated` binding at the outer caller.
    (hStackValid : ∀ scId serverTid originalOwner,
        replyStackOuterCallerValid st scId serverTid originalOwner)
    -- **`v0.35.157`**: see `applyReplyDonationOnCore_preserves_ipcInvariantFull`.
    (hOriginCoherent : redirectedOriginFrameCoherent st rid targetVtid.val)
    (h : applyReplyDonationOnCore st rid targetVtid holderHome ownerHome = .ok st'') :
    ipcInvariantFull st'' := by
  by_cases hAny : ∃ (s : SeLe4n.ThreadId) (sTcb : TCB) (sc : SeLe4n.SchedContextId),
      st.objects[s.toObjId]? = some (.tcb sTcb) ∧ sTcb.schedContextBinding = .donated sc woken
  · obtain ⟨s0, sTcb0, sc0, hS0, hB0⟩ := hAny
    have hHeadEq := hDonationReturned s0 sTcb0 sc0 hS0 hB0
    rcases applyReplyDonationOnCore_ok_decompose st st'' rid targetVtid holderHome ownerHome h with ⟨hNone, _⟩ | ⟨scId, holderVtid, n, st', hHead, hRes, hR, hEq⟩
    · rw [hHeadEq] at hNone; cases hNone
    · obtain ⟨hScEq, hS0Eq⟩ : sc0 = scId ∧ s0 = holderVtid.val := by
        have := hHeadEq.symm.trans hHead
        simpa using this
      rw [hScEq] at hB0
      rw [hS0Eq] at hS0
      have hRet : replyDonationReturn? st holderVtid.val = some (scId, targetVtid.val) :=
        hHolderDonation scId holderVtid.val hHead
      -- The woken thread IS the answered caller: two readings of one binding.
      have hWoken : woken = targetVtid.val :=
        (answeredHeadHolder_donation_owner_eq st targetVtid.val holderVtid.val woken sTcb0
          scId scId hRet hS0 hB0).2
      subst hWoken
      have hIdle : ∀ tcb, st.getTcb? holderVtid.val = some tcb →
          passiveServerIdleAllowed tcb.ipcState := hHolderIdleAllowed scId holderVtid.val hHead
      obtain ⟨pTcb, hLk, hPB⟩ :=
        replyDonationReturn?_some_lookup st holderVtid.val scId targetVtid.val hRet
      have hPPre : st.getTcb? holderVtid.val = some pTcb :=
        getTcb?_of_lookupTcb st holderVtid.val pTcb hLk
      have hNe : replyDonationRecipient st scId targetVtid.val ≠ holderVtid.val := by
        intro hEqq
        have hUnb := returnDonatedSchedContext_ok_recipient_unbound st st' holderVtid.val scId
          (replyDonationRecipient st scId targetVtid.val) n hR pTcb (hEqq ▸ hLk)
        rw [hPB] at hUnb; cases hUnb
      have hFull' : ipcInvariantFull st' := by
        by_cases hNoOrigin : donationOriginRecipient? st scId = none
        · rw [replyDonationRecipient_eq_of_no_origin st scId targetVtid.val hNoOrigin] at hR
          exact returnDonatedSchedContext_establishes_ipcInvariantFull_of_except st st' holderVtid
            scId targetVtid.val hObjInv hInv hRet hIdle n
            (donationReturnOuterValid_of_stackValid
              (hStackValid scId holderVtid.val targetVtid.val) hRes) hR
        · obtain ⟨o, hOrigin⟩ : ∃ o, donationOriginRecipient? st scId = some o := by
            cases hc : donationOriginRecipient? st scId with
            | none => exact absurd hc hNoOrigin
            | some o => exact ⟨o, rfl⟩
          have hRecipEq : replyDonationRecipient st scId targetVtid.val = o :=
            replyDonationRecipient_eq_origin st hOrigin
          by_cases hSame : o = targetVtid.val
          · rw [hRecipEq, hSame] at hR
            exact returnDonatedSchedContext_establishes_ipcInvariantFull_of_except st st'
              holderVtid scId targetVtid.val hObjInv hInv hRet hIdle n
              (donationReturnOuterValid_of_stackValid
                (hStackValid scId holderVtid.val targetVtid.val) hRes) hR
          · rw [hRecipEq] at hR
            exact returnDonatedSchedContext_establishes_ipcInvariantFull_of_except_redirected
              st st' holderVtid scId targetVtid.val o hObjInv hInv hRet
              (donationOriginRebindable_no_owner
                (hOriginCoherent scId holderVtid.val o hHead hOrigin hSame)
                (donationOriginRecipient?_resolves st hOrigin)
                (donationOriginRecipient?_rebindable st hOrigin))
              hIdle n
              (donationReturnOuterValid_of_stackValid (hStackValid scId holderVtid.val o) hRes) hR
      obtain ⟨_, ⟨pTcb0, hPPre0, hPPost⟩, _⟩ :=
        returnDonatedSchedContext_getTcb?_char st st' holderVtid.val scId
          (replyDonationRecipient st scId targetVtid.val) hObjInv hNe n hR
      have hPEq : pTcb0 = pTcb := Option.some.inj (hPPre0.symm.trans hPPre)
      rw [hPEq] at hPPost
      let stM : SystemState := migrateSchedContextReplenishment st' scId holderHome ownerHome
      have hMObjs : stM.objects = st'.objects := migrateSchedContextReplenishment_objects _ _ _ _
      have hMRq := migrateSchedContextReplenishment_runQueue_current_eq st' scId holderHome
        ownerHome bootCoreId
      have hFullM : ipcInvariantFull stM :=
        ipcInvariantFull_of_descheduleFrame st' stM hFull' hMObjs
          (passiveServerIdleFrame.of_objects_scheduler_eq hMObjs hMRq.1 hMRq.2)
      rw [hEq]
      refine ipcInvariantFull_of_descheduleFrame stM _ hFullM
        (descheduleAtPlacement_preserves_objects stM holderVtid.val)
        (descheduleAtPlacement_passiveServerIdleFrame stM holderVtid.val
          (fun tcb hTcb => ?_))
      rw [hMObjs] at hTcb
      have hEqT : { pTcb with schedContextBinding := .unbound } = tcb :=
        Option.some.inj (hPPost.symm.trans ((getTcb?_eq_some_iff st' _ tcb).mpr hTcb))
      exact Or.inr (by rw [← hEqT]; exact hIdle pTcb hPPre)
  · exact applyReplyDonationOnCore_preserves_ipcInvariantFull st st'' rid targetVtid
      holderHome ownerHome hObjInv
      (ipcInvariantFull_of_exceptDonationOwner hInv
        (donationOwnerValid_of_except_of_no_donation_owned_by hInv.donationOwnerValidExcept
          (fun tid tcb sc hTcb hBind => hAny ⟨tid, tcb, sc, hTcb, hBind⟩)))
      hHolderDonation hHolderIdleAllowed hStackValid hOriginCoherent h

-- ============================================================================
-- §5  RR2.11 — the cross-core `.reply` chain
-- ============================================================================

/-- WS-RR RR2.11: `applyReplyDonationOnCore` preserves the object store's
extended invariant — the return through `returnDonatedSchedContext`, the
migration and the deschedule through their object frames. -/
theorem applyReplyDonationOnCore_preserves_objects_invExt
    (st st'' : SystemState) (rid : SeLe4n.ReplyId) (targetVtid : SeLe4n.ValidThreadId)
    (holderHome ownerHome : CoreId)
    (hObjInv : st.objects.invExt)
    (h : applyReplyDonationOnCore st rid targetVtid holderHome ownerHome = .ok st'') :
    st''.objects.invExt := by
  rcases applyReplyDonationOnCore_ok_decompose st st'' rid targetVtid holderHome ownerHome h with ⟨_, hEq⟩ | ⟨scId, holderVtid, n, st', _, _, hR, hEq⟩
  · rw [hEq]; exact hObjInv
  · have hInv' := returnDonatedSchedContext_preserves_objects_invExt st st' holderVtid.val scId
      (replyDonationRecipient st scId targetVtid.val) hObjInv n hR
    rw [hEq, descheduleAtPlacement_preserves_objects, migrateSchedContextReplenishment_objects]
    exact hInv'

/-- **WS-RR RR8.16 (`v0.35.195`)**: the cross-core donation return preserves every
thread's `ipcState` backward.

Its three object writes rewrite a `SchedContext`'s `boundThread` and two TCBs'
`schedContextBinding` (`returnDonatedSchedContext_tcb_ipcState_replyObject_backward`),
and the migration and the deschedule write no object at all — which is what
`applyReplyDonationOnCore_objects_eq` already says, so this costs no second case
analysis over the return's arms. -/
theorem applyReplyDonationOnCore_tcb_ipcState_backward
    (st st'' : SystemState) (rid : SeLe4n.ReplyId) (targetVtid : SeLe4n.ValidThreadId)
    (holderHome ownerHome : CoreId)
    (hObjInv : st.objects.invExt)
    (h : applyReplyDonationOnCore st rid targetVtid holderHome ownerHome = .ok st'')
    (t : SeLe4n.ObjId) (tcb' : TCB)
    (hTcb' : st''.objects[t]? = some (.tcb tcb')) :
    ∃ tcb, st.objects[t]? = some (.tcb tcb) ∧ tcb.ipcState = tcb'.ipcState := by
  rcases applyReplyDonationOnCore_objects_eq st st'' rid targetVtid holderHome ownerHome h with
    ⟨_, hObj⟩ | ⟨scId, holder, newOwner?, st', hRet, hObj⟩
  · exact ⟨tcb', by rw [← hObj]; exact hTcb', rfl⟩
  · rw [hObj] at hTcb'
    obtain ⟨tcb, hPre, hIpc, _⟩ :=
      returnDonatedSchedContext_tcb_ipcState_replyObject_backward st st' holder scId
        (replyDonationRecipient st scId targetVtid.val) hObjInv newOwner? hRet t tcb' hTcb'
    exact ⟨tcb, hPre, hIpc⟩

/-- **WS-RR RR8.16 (`v0.35.195`)**: a successful cross-core reply leaves the thread
it answers `.ready`.

The fault reply's abandon arm needs exactly this, and carried it as a caller
hypothesis (`hTargetIdleAllowed`) from WS-RR RR4.18 until this cut: the abandon
deschedules the faulted thread, so `passiveServerIdle` has to be re-established at
it, and `.ready` is a `passiveServerIdleAllowed` state.  Reading it off the
**outcome** instead is what retires that hypothesis — and the hypothesis was
consumed on the `.ok` branch alone, so nothing weaker was ever being asked for.

Every step after the reply leg frames the answered thread's `ipcState`: the
donation return through `applyReplyDonationOnCore_tcb_ipcState_backward`, the
priority-inheritance reversion through
`PriorityInheritance.propagatePipChainCrossCore_tcb_ipcState_backward`.  So the
`.ready` the leg writes (`endpointReplyOnCore_ok_target_ready`) is what a consumer
of the whole dispatch reads back. -/
theorem endpointReplyCrossCoreDispatch_ok_target_ready
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt)
    {sgi? : Option (CoreId × SgiKind)}
    (hOk : (endpointReplyCrossCoreDispatch replier target msg executingCore st).2 = .ok sgi?)
    {t : TCB}
    (hTcb : (endpointReplyCrossCoreDispatch replier target msg executingCore st).1.getTcb? target
        = some t) :
    t.ipcState = .ready := by
  have hReplyInv : (endpointReplyOnCore replier target msg executingCore st).1.objects.invExt :=
    endpointReplyOnCore_preserves_objects_invExt replier target msg executingCore st hObjInv
  unfold endpointReplyCrossCoreDispatch at hOk hTcb
  cases hRep : endpointReplyOnCore replier target msg executingCore st with
  | mk st1 res =>
    rw [hRep] at hOk hTcb hReplyInv
    cases res with
    | error e => exact absurd hOk (by simp)
    | ok replySgi =>
      simp only at hOk hTcb
      have hLeg' : ∀ u : TCB, st1.getTcb? target = some u → u.ipcState = .ready := fun u hU =>
        endpointReplyOnCore_ok_target_ready replier target msg executingCore st hObjInv
          (by rw [hRep]) (by rw [hRep]; exact hU)
      cases hRec : recordedReplyServer? st target with
      | none => rw [hRec] at hOk; exact absurd hOk (by simp)
      | some expected =>
        rw [hRec] at hOk hTcb
        simp only at hOk hTcb
        cases hEV : SeLe4n.ThreadId.toValid? expected with
        | none => rw [hEV] at hOk; exact absurd hOk (by simp)
        | some _expectedV =>
          rw [hEV] at hOk hTcb
          simp only at hOk hTcb
          cases hRid : answeredReplyObject? st target with
          | none =>
              rw [hRid] at hTcb
              simp only at hTcb
              rw [SystemState.getTcb?_eq_some_iff] at hTcb
              obtain ⟨u, hU, hIpc⟩ :=
                PriorityInheritance.propagatePipChainCrossCore_tcb_ipcState_backward st1
                  expected executingCore _ hReplyInv target t hTcb
              rw [← hIpc]
              exact hLeg' u ((SystemState.getTcb?_eq_some_iff st1 target u).mpr hU)
          | some rid =>
            rw [hRid] at hOk hTcb
            simp only at hOk hTcb
            cases hTV : SeLe4n.ThreadId.toValid? target with
            | none => rw [hTV] at hOk; exact absurd hOk (by simp)
            | some targetV =>
              rw [hTV] at hOk hTcb
              simp only at hOk hTcb
              cases hDon : applyReplyDonationOnCore st1 rid targetV
                  (replyDonationHolderHome st1 rid target)
                  (replyDonationRecipientHome st1 rid target) with
              | error e => rw [hDon] at hOk; exact absurd hOk (by simp)
              | ok st2 =>
                rw [hDon] at hTcb
                simp only at hTcb
                have hDonInv : st2.objects.invExt :=
                  applyReplyDonationOnCore_preserves_objects_invExt st1 st2 rid targetV _ _
                    hReplyInv hDon
                rw [SystemState.getTcb?_eq_some_iff] at hTcb
                obtain ⟨u, hU, hIpcU⟩ :=
                  PriorityInheritance.propagatePipChainCrossCore_tcb_ipcState_backward st2
                    expected executingCore _ hDonInv target t hTcb
                obtain ⟨v, hV, hIpcV⟩ :=
                  applyReplyDonationOnCore_tcb_ipcState_backward st1 st2 rid targetV _ _
                    hReplyInv hDon target.toObjId u hU
                rw [← hIpcU, ← hIpcV]
                exact hLeg' v ((SystemState.getTcb?_eq_some_iff st1 target v).mpr hV)

/-- **WS-RR RR3.12: the live cross-core `.reply` dispatch preserves
`ipcInvariantFull` on every path — the donating one included.**

The reply chain is *not* invariant-preserving stage by stage, and this is the
theorem that says what it is instead.  `endpointReplyOnCore` wakes the answered
caller `.ready` while the recorded server still holds `.donated _ caller`; the
donated SchedContext comes back only at the next stage, because the server needs
that budget *while* it replies (the AUD-3 ordering).  So the intermediate state
satisfies `ipcInvariantFullExceptDonationOwner … target` and nothing stronger, and
`applyReplyDonationOnCore` is what closes the relaxation.

`hDonationReturned` is the one condition that ties the two halves together: *if*
anything is donated by the answered caller, this reply's answered frame heads
exactly that context and `s` is exactly the thread holding it.  True on the
seL4-MCS path, because a caller donates to the very server that later answers it.
When nothing is donated it is vacuous and the chain runs on the unrelaxed route.

**WS-HP HP4.4 -- the pop's three conditions are stated at the state the pop runs
on**, which is `hStackValid`'s convention in this same signature and for the same
reason: it is a pre-state-computable expression, so the de-threading discipline
is respected, and no transport lemma stands between what a caller discharges and
what the pop consumes.  The one exception is the *frame*, which is read from the
genuine pre-state `st`: `endpointReplyOnCore`'s `consumeCallerReply` clears
`target.replyObject`, so `answeredReplyObject?` answers `none` at `st1` and the
link from the answered caller to its frame exists only before the leg.

This supersedes the `hNoDonationOwnedBy` form below, which is the same statement
restricted to non-donating replies; that one is kept because it is what the bare
`endpointReplyOnCore` bundle can offer on its own.

**WS-RR RR8.16 (`v0.35.195`)**: that form's last in-tree consumer was the fault
reply's bundle, and it moved here — `faultDeliverOnCore` composes the live `.call`
chain, so a faulted thread that holds a reservation donates it to its handler and
`hNoDonationOwnedBy` is **false** in exactly the state the handler replies from.
The corollary is kept (it cannot diverge: its proof is one application of this
theorem) and anchored in Tier 3, since a derivation nothing consults reads exactly
like one nobody checked. -/
theorem endpointReplyCrossCoreDispatch_establishes_ipcInvariantFull
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hDonationReturned : ∀ (s : SeLe4n.ThreadId) (sTcb : TCB) (sc : SeLe4n.SchedContextId),
        (endpointReplyOnCore replier target msg executingCore st).1.objects[s.toObjId]?
            = some (.tcb sTcb) →
        sTcb.schedContextBinding = .donated sc target →
        ∃ rid : SeLe4n.ReplyId, answeredReplyObject? st target = some rid ∧
          replyFrameHeadHolder?
            (endpointReplyOnCore replier target msg executingCore st).1 rid = some (sc, s))
    (hHolderDonation : ∀ rid : SeLe4n.ReplyId, answeredReplyObject? st target = some rid →
      replyFrameHeadHolderDonation
        (endpointReplyOnCore replier target msg executingCore st).1 rid target)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hHolderIdleAllowed : ∀ (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId)
        (holder : SeLe4n.ThreadId),
      answeredReplyObject? st target = some rid →
      replyFrameHeadHolder?
          (endpointReplyOnCore replier target msg executingCore st).1 rid = some (scId, holder) →
      ∀ tcb, (endpointReplyOnCore replier target msg executingCore st).1.getTcb? holder = some tcb →
        passiveServerIdleAllowed tcb.ipcState)
    -- **WS-OD OD4.4**: the donation return resolves its new owner from the
    -- context's reply stack, so at depth ≥ 2 it mints a `.donated` binding at the
    -- outer caller.  Stated at the state the pop actually runs at -- the reply leg
    -- commits first -- which is a pre-state-computable expression, so the
    -- de-threading discipline is respected.
    (hStackValid : ∀ scId serverTid originalOwner,
        replyStackOuterCallerValid (endpointReplyOnCore replier target msg executingCore st).1
          scId serverTid originalOwner)
    -- **`v0.35.157`**: the origin redirect's coherence obligation, at the same
    -- state and quantified over the answered frame like the trigger's own fields.
    (hOriginCoherent : ∀ rid : SeLe4n.ReplyId, answeredReplyObject? st target = some rid →
      redirectedOriginFrameCoherent (endpointReplyOnCore replier target msg executingCore st).1
        rid target) :
    ipcInvariantFull (endpointReplyCrossCoreDispatch replier target msg executingCore st).1 := by
  have hReplyExc : ipcInvariantFullExceptDonationOwner
      (endpointReplyOnCore replier target msg executingCore st).1 target :=
    endpointReplyOnCore_preserves_ipcInvariantFullExceptDonationOwner replier target msg
      executingCore st hInv hObjInv hAllBudgetsNone
  have hReplyInv : (endpointReplyOnCore replier target msg executingCore st).1.objects.invExt :=
    endpointReplyOnCore_preserves_objects_invExt replier target msg executingCore st hObjInv
  unfold endpointReplyCrossCoreDispatch
  cases hRep : endpointReplyOnCore replier target msg executingCore st with
  | mk st1 res =>
    rw [hRep] at hReplyExc hReplyInv hStackValid hDonationReturned hHolderDonation hHolderIdleAllowed hOriginCoherent
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
        | some _expectedV =>
          simp only
          cases hRid : answeredReplyObject? st target with
          | none =>
              -- No answered frame, so `hDonationReturned` rules out any donation
              -- owned by the woken caller and the relaxation is already empty.
              simp only
              refine propagatePipChainCrossCore_preserves_ipcInvariantFull st1 expected
                executingCore _ hReplyInv
                (ipcInvariantFull_of_exceptDonationOwner hReplyExc
                  (donationOwnerValid_of_except_of_no_donation_owned_by
                    hReplyExc.donationOwnerValidExcept (fun tid tcb sc hTcb hBind => ?_)))
              obtain ⟨rid0, hRid0, _⟩ := hDonationReturned tid tcb sc hTcb hBind
              rw [hRid] at hRid0; cases hRid0
          | some rid =>
            simp only
            cases hTV : SeLe4n.ThreadId.toValid? target with
            | none => simp only; exact hInv
            | some targetV =>
              simp only
              have hTEq : targetV.val = target :=
                SeLe4n.ThreadId.toValid?_some_val_eq target targetV hTV
              cases hDon : applyReplyDonationOnCore st1 rid targetV
                  (replyDonationHolderHome st1 rid target) (replyDonationRecipientHome st1 rid target) with
              | error e => simp only; exact hInv
              | ok st2 =>
                simp only
                have hDonFull : ipcInvariantFull st2 :=
                  applyReplyDonationOnCore_establishes_ipcInvariantFull_of_except st1 st2 rid
                    targetV target _ _ hReplyInv hReplyExc
                    (fun s sTcb sc hS hB => by
                      obtain ⟨rid0, hRid0, hHead0⟩ := hDonationReturned s sTcb sc hS hB
                      rw [hRid] at hRid0
                      exact (Option.some.inj hRid0) ▸ hHead0)
                    (by rw [hTEq]; exact hHolderDonation rid hRid)
                    (fun scId holder hHead => hHolderIdleAllowed rid scId holder hRid hHead)
                    hStackValid (by rw [hTEq]; exact hOriginCoherent rid hRid) hDon
                have hDonInv : st2.objects.invExt :=
                  applyReplyDonationOnCore_preserves_objects_invExt st1 st2 rid targetV _ _
                    hReplyInv hDon
                exact propagatePipChainCrossCore_preserves_ipcInvariantFull st2 expected
                  executingCore _ hDonInv hDonFull

/-- WS-RR RR2.11 / WS-RR RR3.12: the live cross-core `.reply` dispatch preserves
`ipcInvariantFull` on a reply whose answered caller donated nothing — the
non-donating instance of `endpointReplyCrossCoreDispatch_establishes_ipcInvariantFull`
above, where `hDonationReturned` is vacuous because its premise cannot be met.

Kept as its own statement because `hNoDonationOwnedBy` is what the *bare*
`endpointReplyOnCore` bundle can be stated against; the composite above is what the
donating path needs.

**WS-HP HP4.4 — "this reply returns no donation" is two facts after the trigger
flip, and stating only the first would be a claim about the wrong thing.**
`hNoDonationOwnedBy` says nothing is donated *by the answered caller*, which is
what makes the relaxation empty; `hNoHead` says the answered *frame* heads no
scheduling context, which is what makes the pop the identity.  Under the
binding-driven trigger the first implied the second, because the pop read the
recorded server's binding.  It no longer does: a frame heading a context held by
a thread whose binding names some *other* owner satisfies the first and not the
second, so the two are separate conditions and both are stated.  On a reachable
state they coincide -- a frame heads a context exactly when the caller whose
frame it is pushed the donation -- and the pair is exactly what a non-donating
reply discharges.

`hNoDonationOwnedBy` stays on the genuine pre-state: the reply leg writes no
`schedContextBinding` (`endpointReplyOnCore_sameSchedContextBindings`), so the
transport is done here once rather than at every caller. -/
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
    (hNoHead : ∀ rid : SeLe4n.ReplyId, answeredReplyObject? st target = some rid →
      replyFrameHeadHolder?
        (endpointReplyOnCore replier target msg executingCore st).1 rid = none)
    -- **WS-OD OD4.4**: see `endpointReplyCrossCoreDispatch_establishes_ipcInvariantFull`.
    (hStackValid : ∀ scId serverTid originalOwner,
        replyStackOuterCallerValid (endpointReplyOnCore replier target msg executingCore st).1
          scId serverTid originalOwner) :
    ipcInvariantFull (endpointReplyCrossCoreDispatch replier target msg executingCore st).1 :=
  endpointReplyCrossCoreDispatch_establishes_ipcInvariantFull replier target msg executingCore
    st hInv hObjInv
    (fun s sTcb sc hS hB => by
      obtain ⟨sTcb0, hS0, hB0⟩ :=
        endpointReplyOnCore_sameSchedContextBindings replier target msg executingCore st hObjInv
          s sTcb hS
      exact absurd (hB0.trans hB) (hNoDonationOwnedBy s sTcb0 sc hS0))
    (fun rid hRid => replyFrameHeadHolderDonation_of_no_head _ rid target (hNoHead rid hRid))
    hAllBudgetsNone
    (fun rid scId holder hRid hHead _ _ => by rw [hNoHead rid hRid] at hHead; cases hHead)
    hStackValid
    (fun rid hRid scId holder origin hHead _ _ => by rw [hNoHead rid hRid] at hHead; cases hHead)

-- ============================================================================
-- §6  WS-RM (`v0.35.6`) — the composite payoff: the chain across the dispatch
-- ============================================================================

-- ----------------------------------------------------------------------------
-- WS-HP HP7 (`v0.35.46`): the retired coherence fact and HP2.1's equivalence
-- ----------------------------------------------------------------------------
--
-- `answeredHeadContextIsServerDonation` lived here from WS-RM (`v0.35.6`) with
-- its two vacuity discharges, and HP2.1's `answeredFrameHeadContext?_implies_serverDonation`
-- beside them.  All four are **deleted**.
--
-- The predicate was a *stated* pre-state fact -- the context the answered
-- caller's reply frame heads is the one the recorded reply server holds -- which
-- no invariant in this tree entails: `donationOwnerValid` relates a caller's
-- recorded reply target to no donation, and `donationChainWellFormed` carries no
-- binding clause at all.  HP4.4 (`v0.35.38`) took it out of the chain composite
-- for the strictly weaker `replyFrameHeadIsBound`, HP6.2 (`v0.35.44`) deleted the
-- footprint stand-in that was its last consumer, and HP6.8 (`v0.35.45`)
-- **falsified it on reachable states**: a spliced cut re-heads a frame whose
-- recorded reply server is gone and `.unbound`.  A stated fact that nothing
-- consumes and that the live kernel refutes is not a weaker obligation, it is a
-- false one.
--
-- HP2.1's equivalence went with it because its subject did: it related the live
-- head-driven trigger to `endpointReplyServerDonation?`, the binding-driven
-- resolver HP6.2 repointed the last footprint off, and it took the predicate as
-- a hypothesis.
--
-- **What replaced it is the HP2.4 family below** -- `answeredFrameHeadContext?_head_is_answered_reply`,
-- `_donationHeadOf` and `_boundThread`.  Those are the *derivations*: under the
-- head-driven trigger the resolver reads the context off the frame's own `.head`
-- link and validates the context's `scReply` against that same frame, so what the
-- retired predicates asked a caller to supply is now a consequence of the trigger
-- firing.  They are anchored in Tier 3 rather than left unread, because a
-- derivation nothing consults reads exactly like one nobody checked.
--
-- **And the equivalence's evidence is an executed witness.**
-- `tests/SmpCrossCoreReplySuite.lean` computes the retired binding-driven reading
-- beside the live one on the agreeing shape and on the orphan head, with the
-- retired spelling private to that suite -- the pattern
-- `tests/SmpCancellationSuite.lean` §3.20 set at HP5.5 and `FrozenOpsSuite`'s
-- `FO-042` set for the frozen surface.

/-! **WS-HP HP6.2 (`v0.35.44`): the coverage stand-in is gone.**

`lockSet_endpointReplyOnCore_covers_headDrivenPop` stood here from HP4.4: the
footprint resolved its donation members through `endpointReplyServerDonation?`
while the pop read `replyFrameHeadHolder?`, so something had to say that the
SchedContext the pop writes and the TCB it unbinds carry declared write locks,
and it said so under HP2.1's two coherence facts.  HP6.2 repointed the
footprints onto the pop's own trigger, which makes that coverage **definitional**
— `lockSet_endpointReplyOnCore_covers_donationPop` and its `.replyRecv` twin
take no hypothesis at all — so keeping a conditional restatement beside them
would be a theorem whose content its own subject already supplies.

`answeredFrameHeadContext?_implies_serverDonation` — HP2.1's equivalence, stated
over the binding-driven resolver — did not survive HP6.2 for long either: HP7
(`v0.35.46`) deleted it with the predicate it took as a hypothesis, as the section
above records.  What stands in its place is the HP2.4 family below, together with
the executed orphan-head witness in `tests/SmpCrossCoreReplySuite.lean`. -/

/-- **WS-HP HP2.4: the head of the popped context IS the answered caller's reply
object** -- `replyStackHeadIsAnsweredReply`'s content, as a theorem of the
head-driven resolver rather than a hypothesis a caller supplies.

Under this trigger it is immediate: the resolver reads the context off the frame's
own `.head` link and validates the context's `scReply` against that same frame, so
the head and the answered reply object are the one `rid` the resolver matched.
HP7 (`v0.35.46`) **deleted** the stated predicate; this is the theorem that let it,
and it is anchored in Tier 3 for that reason -- a derivation nothing consults reads
exactly like one nobody checked. -/
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

-- ----------------------------------------------------------------------------
-- WS-HP HP7 (`v0.35.46`): HP2.3's orphan-head pair
-- ----------------------------------------------------------------------------
--
-- `answeredHeadContextIsServerDonation_false_of_orphan_head` and
-- `donationPopTriggers_disagree_at_orphan_head` stood here from HP2.3 as the
-- checkable form of "the splice breaks the equivalence a binding-driven pop
-- stands on", which is why HP6 could not precede HP4.  The ordering was
-- respected -- HP4 (`v0.35.38`) and HP5 (`v0.35.39`) moved both triggers onto the
-- answered frame's own `.head` link, and HP6.8 (`v0.35.45`) then made the splice
-- live -- and with that the pair's job was done: the first was HP7's warrant for
-- deleting `answeredHeadContextIsServerDonation`, so it cannot outlive the
-- predicate it negates, and the second named `endpointReplyServerDonation?`,
-- which no footprint or transition reads any more.
--
-- The orphan head itself is not gone, it is **reachable**, and the evidence moved
-- from a theorem to an executed run: `tests/SmpCrossCoreReplySuite.lean` builds
-- that state and computes both readings on it, so what these two asserted is now
-- measured rather than stated.

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

**WS-HP HP4.4 — `answeredHeadContextIsServerDonation` is GONE from this
statement, and that is the workstream's payoff arriving early.**  Under the
binding-driven trigger the relaxation sat at the answered *frame* while the pop
was keyed on the recorded *server's binding*, so a hypothesis was needed to say
the two named one context.  The head-driven pop is keyed on that same frame, so
they name one context by construction: the relaxed `rid` **is** the `rid` the pop
resolves its head from, and `replyFrameHeadHolder?`'s own answer supplies the
`sc.scReply = some rid` that `donationHeadOf?` validates.

What survives is strictly weaker and is the one arm that construction does not
close: `replyFrameHeadIsBound` rules out a frame that heads a context bound to
**nobody**, where the pop would be the identity while the leg has already relaxed
the chain at that frame.  It is vacuous on every reply whose frame heads nothing,
which is every reply in a tree with no donation.  It is a **stated** hypothesis:
HP7 (`v0.35.46`) deleted the three binding-driven coherence facts and left this
one standing -- no chain clause entails it, and making it one is registered
(`docs/REGISTERED_DEBT.md`, WS-HP) rather than predicted here a second time. -/
theorem endpointReplyCrossCoreDispatch_preserves_donationChainWellFormed
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState)
    (hObjInv : st.objects.invExt)
    (hChain : donationChainWellFormed st)
    (hHeadBound : ∀ rid : SeLe4n.ReplyId, answeredReplyObject? st target = some rid →
      replyFrameHeadIsBound (endpointReplyOnCore replier target msg executingCore st).1 rid) :
    donationChainWellFormed
      (endpointReplyCrossCoreDispatch replier target msg executingCore st).1 := by
  have hReplyInv : (endpointReplyOnCore replier target msg executingCore st).1.objects.invExt :=
    endpointReplyOnCore_preserves_objects_invExt replier target msg executingCore st hObjInv
  have hCases := endpointReplyOnCore_donationChain_cases replier target msg executingCore st
    hObjInv hChain
  unfold endpointReplyCrossCoreDispatch
  cases hRep : endpointReplyOnCore replier target msg executingCore st with
  | mk st1 res =>
    rw [hRep] at hReplyInv hCases hHeadBound
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
        | some _expectedV =>
          simp only
          -- `hCases`' relaxed disjunct names the answered caller's own frame, so
          -- it *is* the frame the pop will be handed.
          have hRidOf : ∀ (tcb : TCB) (rid0 : SeLe4n.ReplyId),
              lookupTcb st target = some tcb → tcb.replyObject = some rid0 →
              answeredReplyObject? st target = some rid0 := by
            intro tcb rid0 hLk hRO
            unfold answeredReplyObject?
            rw [getTcb?_of_lookupTcb st target tcb hLk]; exact hRO
          cases hRid : answeredReplyObject? st target with
          | none =>
              simp only
              have hFull : donationChainWellFormed st1 := by
                rcases hCases with hFull | ⟨tcb, rid0, _, _, hLk, hRO, _, _, _, _⟩
                · exact hFull
                · exact absurd (hRidOf tcb rid0 hLk hRO) (by rw [hRid]; exact fun hx => by cases hx)
              exact propagatePipChainCrossCore_preserves_donationChainWellFormed st1 expected
                executingCore _ hReplyInv hFull
          | some rid =>
            simp only
            cases hTV : SeLe4n.ThreadId.toValid? target with
            | none => simp only; exact hChain
            | some targetV =>
              simp only
              -- The relaxation, if any, is at exactly the frame the pop resolves.
              have hDon : donationChainWellFormed st1 ∨
                  ∃ (scId : SeLe4n.SchedContextId) (sc : SchedContext),
                    donationChainWellFormedExcept st1 rid ∧
                    st1.getSchedContext? scId = some sc ∧ sc.scReply = some rid ∧
                    replyFrameHeadContext? st1 rid = some scId := by
                rcases hCases with hFull | ⟨tcb, rid0, _, scId, hLk, hRO, _, _,
                  ⟨r1, hR1, hN1⟩, hExc⟩
                · exact Or.inl hFull
                · have hRidEq : rid0 = rid :=
                    Option.some.inj ((hRidOf tcb rid0 hLk hRO).symm.trans hRid)
                  rw [hRidEq] at hR1 hExc
                  obtain ⟨sc, hScObj, hScReply⟩ := hExc.headLinkResolves rid r1 scId
                    ((SystemState.getReply?_eq_some_iff st1 rid r1).mp hR1) hN1
                  have hScGet : st1.getSchedContext? scId = some sc :=
                    (SystemState.getSchedContext?_eq_some_iff st1 scId sc).mpr hScObj
                  exact Or.inr ⟨scId, sc, hExc, hScGet, hScReply,
                    replyFrameHeadContext?_of_head st1 rid r1 scId sc hR1 hN1 hScGet hScReply⟩
              cases hApply : applyReplyDonationOnCore st1 rid targetV
                  (replyDonationHolderHome st1 rid target) (replyDonationRecipientHome st1 rid target) with
              | error e => simp only; exact hChain
              | ok st2 =>
                simp only
                have hInv2 : st2.objects.invExt :=
                  applyReplyDonationOnCore_preserves_objects_invExt st1 st2 rid targetV _ _
                    hReplyInv hApply
                have hChain2 : donationChainWellFormed st2 := by
                  rcases hDon with hFull | ⟨scId, sc, hExc, hScGet, hScReply, hHeadCtx⟩
                  · exact applyReplyDonationOnCore_preserves_donationChainWellFormed_of_except
                      st1 st2 rid targetV _ _ hReplyInv (fun _ _ _ _ _ _ => hFull)
                      (fun _ _ _ hidX _ _ _ _ =>
                        donationChainWellFormedExcept_of_wellFormed hFull hidX)
                      (fun _ => hFull) hApply
                  -- The popped context is the one the relaxed frame heads, so the
                  -- head the pop validates *is* that frame and the relaxation is
                  -- discharged.
                  · refine applyReplyDonationOnCore_preserves_donationChainWellFormed_of_except
                      st1 st2 rid targetV _ _ hReplyInv ?_ ?_ ?_ hApply
                    · -- A context whose stack head is `rid` has a head: vacuous.
                      intro scId' holder' sc' hHead' hSc' hHeadOf
                      obtain rfl : scId' = scId :=
                        Option.some.inj ((replyFrameHeadHolder?_eq_some hHead').1.symm.trans
                          hHeadCtx)
                      rw [hScGet] at hSc'
                      obtain rfl : sc' = sc := Option.some.inj hSc'.symm
                      have hKey := donationHeadOf?_ok_key st1 scId' sc' none hHeadOf
                      rw [hScReply] at hKey
                      cases hKey
                    · -- And the head it validates is exactly the relaxed frame.
                      intro scId' holder' sc' hidX rX hHead' hSc' hHeadOf
                      obtain rfl : scId' = scId :=
                        Option.some.inj ((replyFrameHeadHolder?_eq_some hHead').1.symm.trans
                          hHeadCtx)
                      rw [hScGet] at hSc'
                      obtain rfl : sc' = sc := Option.some.inj hSc'.symm
                      have hKey := donationHeadOf?_ok_key st1 scId' sc' (some (hidX, rX)) hHeadOf
                      rw [hScReply] at hKey
                      obtain rfl : hidX = rid := Option.some.inj (by simpa using hKey)
                      exact hExc
                    · -- The frame heads `scId`, so `replyFrameHeadIsBound` gives it a
                      -- holder and this arm cannot fire.
                      intro hNone
                      exact absurd hNone (replyFrameHeadHolder?_ne_none_of_bound
                        (hHeadBound rid hRid) hHeadCtx)
                exact propagatePipChainCrossCore_preserves_donationChainWellFormed st2 expected
                  executingCore _ hInv2 hChain2


-- ============================================================================
-- WS-RR RR8.16 (`v0.35.199`) — the reply path's two cross-subsystem bundles
-- ============================================================================
--
-- Register row 85's substance.  `v0.35.197` gave `schedulerInvariantBase_smp`
-- and `capabilityInvariantBundle` their frames and lifted the three steps both
-- IPC chains share; `v0.35.199` adds the reply path's own, and each is the
-- composition of citations rather than an argument -- which is the change the
-- frames made.
--
-- This module is where they live because it is the first that sees the reply
-- dispatch, the two invariants and the frames at once.

/-- WS-RR RR8.16 (`v0.35.199`): **the reply path's donation pop preserves the base
SMP scheduler invariant.**

Three steps, one citation each: the return writes no scheduler state, the SM5.H
migration writes `replenishQueue` alone (which the invariant does not read), and
the deschedule is a placement removal. -/
theorem applyReplyDonationOnCore_preserves_schedulerInvariantBase_smp
    {st st'' : SystemState} {rid : SeLe4n.ReplyId} {targetVtid : SeLe4n.ValidThreadId}
    {holderHome ownerHome : CoreId}
    (hObjInv : st.objects.invExt)
    (h : schedulerInvariantBase_smp st)
    (hStep : applyReplyDonationOnCore st rid targetVtid holderHome ownerHome = .ok st'') :
    schedulerInvariantBase_smp st'' := by
  rcases applyReplyDonationOnCore_ok_decompose st st'' rid targetVtid holderHome ownerHome hStep
    with ⟨_, rfl⟩ | ⟨scId, holderVtid, newOwner?, st', _, _, hRet, hEq⟩
  · exact h
  · subst hEq
    exact descheduleAtPlacement_preserves_schedulerInvariantBase_smp _
      (migrateSchedContextReplenishment_preserves_schedulerInvariantBase_smp _ _ _
        (returnDonatedSchedContext_preserves_schedulerInvariantBase_smp hObjInv h hRet))

/-- WS-RR RR8.16 (`v0.35.199`): **and the capability bundle.**

The migration and the deschedule write no object at all
(`applyReplyDonationOnCore_objects_eq` reads the pop down to the return's own
store), so this is the return's lift plus a `_of_objects_and_cdt_eq`. -/
theorem applyReplyDonationOnCore_preserves_capabilityInvariantBundle
    {st st'' : SystemState} {rid : SeLe4n.ReplyId} {targetVtid : SeLe4n.ValidThreadId}
    {holderHome ownerHome : CoreId}
    (h : capabilityInvariantBundle st)
    (hStep : applyReplyDonationOnCore st rid targetVtid holderHome ownerHome = .ok st'') :
    capabilityInvariantBundle st'' := by
  rcases applyReplyDonationOnCore_ok_decompose st st'' rid targetVtid holderHome ownerHome hStep
    with ⟨_, rfl⟩ | ⟨scId, holderVtid, newOwner?, st', _, _, hRet, hEq⟩
  · exact h
  · subst hEq
    refine capabilityInvariantBundle_of_objects_and_cdt_eq
      (returnDonatedSchedContext_preserves_capabilityInvariantBundle h hRet) ?_ ?_ ?_
    · rw [descheduleAtPlacement_preserves_objects,
        migrateSchedContextReplenishment_objects]
    · rw [descheduleAtPlacement_cdtNodeSlot, migrateSchedContextReplenishment_cdtNodeSlot]
    · rw [descheduleAtPlacement_cdt, migrateSchedContextReplenishment_cdt]

/-- **WS-RR RR8.16** (`v0.35.199`): **the live `.reply` chain preserves the base
SMP scheduler invariant.**

The composition, step for step: the reply leg (which writes the answered caller's
TCB, wakes it and runs seL4's `reply_remove`), the donation pop when the answered
frame heads a context, and the priority-inheritance reversion.  Each is a
citation; nothing here is a fresh argument, which is what `v0.35.197`'s two
frames bought.

`hNotCur` is the reply leg's own precondition, unchanged, and stated rather than
derived for the reason that leg records: what turns the answered caller's
`.blockedOnReply` into "not current" is a per-core current-thread-IPC-readiness
discipline this tree states at the boot core only. -/
theorem endpointReplyCrossCoreDispatch_preserves_schedulerInvariantBase_smp
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt)
    (hNotCur : st.scheduler.currentOnCore (determineTargetCore st target) ≠ some target)
    (h : schedulerInvariantBase_smp st) :
    schedulerInvariantBase_smp
      (endpointReplyCrossCoreDispatch replier target msg executingCore st).1 := by
  have hRep := endpointReplyOnCore_preserves_schedulerInvariantBase_smp replier target msg
    executingCore st hObjInv hNotCur h
  have hRepObj := endpointReplyOnCore_preserves_objects_invExt replier target msg
    executingCore st hObjInv
  unfold endpointReplyCrossCoreDispatch
  cases hRepEq : endpointReplyOnCore replier target msg executingCore st with
  | mk st1 res1 =>
      rw [hRepEq] at hRep hRepObj
      simp only at hRep hRepObj ⊢
      cases res1 with
      | error e => exact h
      | ok replySgi? =>
          simp only
          split
          · split
            · split
              · exact propagatePipChainCrossCore_preserves_schedulerInvariantBase_smp
                  _ _ _ _ hRepObj hRep
              · split
                · exact h
                · split
                  · exact h
                  · rename_i st2 hRet
                    exact propagatePipChainCrossCore_preserves_schedulerInvariantBase_smp
                      _ _ _ _
                      (applyReplyDonationOnCore_preserves_objects_invExt _ _ _ _ _ _ hRepObj hRet)
                      (applyReplyDonationOnCore_preserves_schedulerInvariantBase_smp hRepObj hRep hRet)
            · exact h
          · exact h

/-- **WS-RR RR8.16** (`v0.35.199`): ...and the **capability invariant bundle**,
unconditionally.

None of the chain's three steps writes a CNode or either CDT table: the reply
leg's writes are TCBs and Reply objects, the pop's are a SchedContext, two TCBs
and the two stack frames, and the reversion's are TCBs and run queues. -/
theorem endpointReplyCrossCoreDispatch_preserves_capabilityInvariantBundle
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) (hObjInv : st.objects.invExt)
    (h : capabilityInvariantBundle st) :
    capabilityInvariantBundle
      (endpointReplyCrossCoreDispatch replier target msg executingCore st).1 := by
  have hRep := endpointReplyOnCore_preserves_capabilityInvariantBundle replier target msg
    executingCore st hObjInv h
  have hRepObj := endpointReplyOnCore_preserves_objects_invExt replier target msg
    executingCore st hObjInv
  unfold endpointReplyCrossCoreDispatch
  cases hRepEq : endpointReplyOnCore replier target msg executingCore st with
  | mk st1 res1 =>
      rw [hRepEq] at hRep hRepObj
      simp only at hRep hRepObj ⊢
      cases res1 with
      | error e => exact h
      | ok replySgi? =>
          simp only
          split
          · split
            · split
              · exact propagatePipChainCrossCore_preserves_capabilityInvariantBundle
                  _ _ _ _ hRep
              · split
                · exact h
                · split
                  · exact h
                  · rename_i st2 hRet
                    exact propagatePipChainCrossCore_preserves_capabilityInvariantBundle
                      _ _ _ _
                      (applyReplyDonationOnCore_preserves_capabilityInvariantBundle hRep hRet)
            · exact h
          · exact h


end SeLe4n.Kernel
