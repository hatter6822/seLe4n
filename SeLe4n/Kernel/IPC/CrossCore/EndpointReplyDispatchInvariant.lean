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
        holderVtid.val scId targetVtid.val n hObjInv (hChainNone scId holderVtid.val · hHead)
        (hChainHead scId holderVtid.val · · · hHead) hRet
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
    (h : applyReplyDonationOnCore st rid targetVtid holderHome ownerHome = .ok st'') :
    ipcInvariantFull st'' := by
  rcases applyReplyDonationOnCore_ok_decompose st st'' rid targetVtid holderHome ownerHome h with ⟨_, hEq⟩ | ⟨scId, holderVtid, n, st', hHead, hRes, hR, hEq⟩
  · rw [hEq]; exact hInv
  · have hRet : replyDonationReturn? st holderVtid.val = some (scId, targetVtid.val) :=
      hHolderDonation scId holderVtid.val hHead
    have hIdle : ∀ tcb, st.getTcb? holderVtid.val = some tcb →
        passiveServerIdleAllowed tcb.ipcState := hHolderIdleAllowed scId holderVtid.val hHead
    have hFull' : ipcInvariantFull st' :=
      returnDonatedSchedContext_preserves_ipcInvariantFull st st' holderVtid scId targetVtid.val
        hObjInv hInv hRet hIdle n
        (donationReturnOuterValid_of_stackValid
          (hStackValid scId holderVtid.val targetVtid.val) hRes) hR
    obtain ⟨pTcb, hPPre, _, _, _, hNe⟩ :=
      replyDonationReturn?_some_char st holderVtid.val scId targetVtid.val
        (donationOwnerValidExcept_of_donationOwnerValid targetVtid.val hInv.donationOwnerValid)
        hRet
    obtain ⟨_, ⟨pTcb0, hPPre0, hPPost⟩, _⟩ :=
      returnDonatedSchedContext_getTcb?_char st st' holderVtid.val scId targetVtid.val hObjInv
        hNe n hR
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
      have hFull' : ipcInvariantFull st' :=
        returnDonatedSchedContext_establishes_ipcInvariantFull_of_except st st' holderVtid scId
          targetVtid.val hObjInv hInv hRet hIdle n
          (donationReturnOuterValid_of_stackValid
            (hStackValid scId holderVtid.val targetVtid.val) hRes) hR
      obtain ⟨pTcb, hPPre, _, _, _, hNe⟩ :=
        replyDonationReturn?_some_char st holderVtid.val scId targetVtid.val
          hInv.donationOwnerValidExcept hRet
      obtain ⟨_, ⟨pTcb0, hPPre0, hPPost⟩, _⟩ :=
        returnDonatedSchedContext_getTcb?_char st st' holderVtid.val scId targetVtid.val hObjInv
          hNe n hR
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
      hHolderDonation hHolderIdleAllowed hStackValid h

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
      targetVtid.val hObjInv n hR
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
`endpointReplyOnCore` bundle can offer on its own. -/
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
          scId serverTid originalOwner) :
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
    rw [hRep] at hReplyExc hReplyInv hStackValid hDonationReturned hHolderDonation hHolderIdleAllowed
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
                  (replyDonationHolderHome st1 rid target) (determineTargetCore st1 target) with
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
                    hStackValid hDon
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
`donationHolderIsReplyTarget` from the cancellation end — a fact WS-HP HP5.3
re-keyed onto the frame as `donatedContextIsOwnerFrameHead`, since the reclaim now
reads the stack too.

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

`answeredFrameHeadContext?_implies_serverDonation` above is **not** retired with
it: that is HP2.1's equivalence, cited where this tree explains why the two
readings agree on every state `severAtCut` can produce, and HP2.3 is what makes
the splice falsify its hypotheses. -/

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
which is every reply in a tree with no donation, and HP7 is where it becomes a
clause of the chain invariant. -/
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
                  (replyDonationHolderHome st1 rid target) (determineTargetCore st1 target) with
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


end SeLe4n.Kernel
