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
    (executingCore replierHome ownerHome : CoreId)
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st)
    (hReplierIdleAllowed : ∀ tcb, st.getTcb? replierVtid.val = some tcb →
        passiveServerIdleAllowed tcb.ipcState)
    (h : applyReplyDonationOnCore st replierVtid executingCore replierHome ownerHome = .ok st'') :
    ipcInvariantFull st'' := by
  rcases applyReplyDonationOnCore_ok_decompose st st'' replierVtid executingCore replierHome
    ownerHome h with ⟨_, hEq⟩ | ⟨scId, owner, st', hRet, hR, hEq⟩
  · rw [hEq]; exact hInv
  · have hFull' : ipcInvariantFull st' :=
      returnDonatedSchedContext_preserves_ipcInvariantFull st st' replierVtid scId owner
        hObjInv hInv hRet hReplierIdleAllowed hR
    obtain ⟨pTcb, hPPre, _, _, _, hNe⟩ :=
      replyDonationReturn?_some_char st replierVtid.val scId owner
        (donationOwnerValidExcept_of_donationOwnerValid owner hInv.donationOwnerValid) hRet
    obtain ⟨_, ⟨pTcb0, hPPre0, hPPost⟩, _⟩ :=
      returnDonatedSchedContext_getTcb?_char st st' replierVtid.val scId owner hObjInv hNe hR
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
    -- The deschedule writes only the executing core's queue and `current` slot.
    rw [hEq]
    refine ipcInvariantFull_of_descheduleFrame stM _ hFullM
      (removeRunnableOnCore_preserves_objects stM replierVtid.val executingCore)
      (removeRunnableOnCore_passiveServerIdleFrame stM replierVtid.val executingCore
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
    (executingCore replierHome ownerHome : CoreId)
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFullExceptDonationOwner st woken)
    (hDonationReturned : ∀ (s : SeLe4n.ThreadId) (sTcb : TCB) (sc : SeLe4n.SchedContextId),
      st.objects[s.toObjId]? = some (.tcb sTcb) →
      sTcb.schedContextBinding = .donated sc woken →
      replyDonationReturn? st replierVtid.val = some (sc, woken))
    (hReplierIdleAllowed : ∀ tcb, st.getTcb? replierVtid.val = some tcb →
        passiveServerIdleAllowed tcb.ipcState)
    (h : applyReplyDonationOnCore st replierVtid executingCore replierHome ownerHome = .ok st'') :
    ipcInvariantFull st'' := by
  by_cases hAny : ∃ (s : SeLe4n.ThreadId) (sTcb : TCB) (sc : SeLe4n.SchedContextId),
      st.objects[s.toObjId]? = some (.tcb sTcb) ∧ sTcb.schedContextBinding = .donated sc woken
  · obtain ⟨s0, sTcb0, sc0, hS0, hB0⟩ := hAny
    have hRetEq := hDonationReturned s0 sTcb0 sc0 hS0 hB0
    rcases applyReplyDonationOnCore_ok_decompose st st'' replierVtid executingCore replierHome
      ownerHome h with ⟨hNone, _⟩ | ⟨scId, owner, st', hRet, hR, hEq⟩
    · rw [hRetEq] at hNone; cases hNone
    · obtain ⟨rfl, rfl⟩ : sc0 = scId ∧ woken = owner := by
        have := hRetEq.symm.trans hRet
        simpa using this
      have hFull' : ipcInvariantFull st' :=
        returnDonatedSchedContext_establishes_ipcInvariantFull_of_except st st' replierVtid sc0
          woken hObjInv hInv hRet hReplierIdleAllowed hR
      obtain ⟨pTcb, hPPre, _, _, _, hNe⟩ :=
        replyDonationReturn?_some_char st replierVtid.val sc0 woken
          hInv.donationOwnerValidExcept hRet
      obtain ⟨_, ⟨pTcb0, hPPre0, hPPost⟩, _⟩ :=
        returnDonatedSchedContext_getTcb?_char st st' replierVtid.val sc0 woken hObjInv hNe hR
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
        (removeRunnableOnCore_preserves_objects stM replierVtid.val executingCore)
        (removeRunnableOnCore_passiveServerIdleFrame stM replierVtid.val executingCore
          (fun tcb hTcb => ?_))
      rw [hMObjs] at hTcb
      have hEqT : { pTcb with schedContextBinding := .unbound } = tcb :=
        Option.some.inj (hPPost.symm.trans ((getTcb?_eq_some_iff st' _ tcb).mpr hTcb))
      exact Or.inr (by rw [← hEqT]; exact hReplierIdleAllowed pTcb hPPre)
  · exact applyReplyDonationOnCore_preserves_ipcInvariantFull st st'' replierVtid executingCore
      replierHome ownerHome hObjInv
      (ipcInvariantFull_of_exceptDonationOwner hInv
        (donationOwnerValid_of_except_of_no_donation_owned_by hInv.donationOwnerValidExcept
          (fun tid tcb sc hTcb hBind => hAny ⟨tid, tcb, sc, hTcb, hBind⟩)))
      hReplierIdleAllowed h

-- ============================================================================
-- §5  RR2.11 — the cross-core `.reply` chain
-- ============================================================================

/-- WS-RR RR2.11: `applyReplyDonationOnCore` preserves the object store's
extended invariant — the return through `returnDonatedSchedContext`, the
migration and the deschedule through their object frames. -/
theorem applyReplyDonationOnCore_preserves_objects_invExt
    (st st'' : SystemState) (replierVtid : SeLe4n.ValidThreadId)
    (executingCore replierHome ownerHome : CoreId)
    (hObjInv : st.objects.invExt)
    (h : applyReplyDonationOnCore st replierVtid executingCore replierHome ownerHome = .ok st'') :
    st''.objects.invExt := by
  rcases applyReplyDonationOnCore_ok_decompose st st'' replierVtid executingCore replierHome
    ownerHome h with ⟨_, hEq⟩ | ⟨scId, owner, st', _, hR, hEq⟩
  · rw [hEq]; exact hObjInv
  · have hInv' := returnDonatedSchedContext_preserves_objects_invExt st st' replierVtid.val scId
      owner hObjInv hR
    rw [hEq, removeRunnableOnCore_preserves_objects, migrateSchedContextReplenishment_objects]
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
      ∀ tcb, st.getTcb? expected = some tcb → passiveServerIdleAllowed tcb.ipcState) :
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
    rw [hRep] at hReplyExc hReplyInv hBack hBindBack hFrame
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
          cases hDon : applyReplyDonationOnCore st1 expectedV (determineExecutingCore st expected)
              (determineTargetCore st expected) (replyDonationOwnerHome st expected) with
          | error e => simp only; exact hInv
          | ok st2 =>
            simp only
            have hDonFull : ipcInvariantFull st2 :=
              applyReplyDonationOnCore_establishes_ipcInvariantFull_of_except st1 st2 expectedV
                target _ _ _ hReplyInv hReplyExc hDonMid hAllowed hDon
            have hDonInv : st2.objects.invExt :=
              applyReplyDonationOnCore_preserves_objects_invExt st1 st2 expectedV _ _ _
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
      ∀ tcb, st.getTcb? expected = some tcb → passiveServerIdleAllowed tcb.ipcState) :
    ipcInvariantFull (endpointReplyCrossCoreDispatch replier target msg executingCore st).1 :=
  endpointReplyCrossCoreDispatch_establishes_ipcInvariantFull replier target msg executingCore
    st hInv hObjInv
    (fun _ _ s sTcb sc hS hB => absurd hB (hNoDonationOwnedBy s sTcb sc hS))
    hAllBudgetsNone hServerIdleAllowed
