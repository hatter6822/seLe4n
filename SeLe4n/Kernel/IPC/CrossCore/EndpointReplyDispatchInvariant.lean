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
      replyDonationReturn?_some_char st replierVtid.val scId owner hInv.donationOwnerValid hRet
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

/-- **WS-RR RR2.11: the live cross-core `.reply` dispatch preserves
`ipcInvariantFull`.**

The chain is reply delivery → SchedContext donation return → priority-inheritance
reversion, and as on the `.call` side only the first stage carried a bundle
theorem before RR2.

`hServerIdleAllowed` is stated on the **pre**-state and transported through the
reply by `endpointReplyOnCore_tcb_backward`, whose dichotomy is exactly what
makes that sound: the reply either leaves a thread's `ipcState` alone or sets it
`.ready`, and `.ready` is itself a `passiveServerIdleAllowed` state.  What it
rules out is a recorded server parked in `.blockedOnSend` / `.blockedOnCall`,
which the donation return would strand `.unbound` off the run queue in a state
`passiveServerIdle` forbids. -/
theorem endpointReplyCrossCoreDispatch_preserves_ipcInvariantFull
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : blockedThreadsPendingMessageConsistent
      (endpointReplyOnCore replier target msg executingCore st).1)
    (hDOV' : donationOwnerValid
      (endpointReplyOnCore replier target msg executingCore st).1)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hServerIdleAllowed : ∀ (expected : SeLe4n.ThreadId), recordedReplyServer? st target
        = some expected →
      ∀ tcb, st.getTcb? expected = some tcb → passiveServerIdleAllowed tcb.ipcState) :
    ipcInvariantFull (endpointReplyCrossCoreDispatch replier target msg executingCore st).1 := by
  have hReply : ipcInvariantFull (endpointReplyOnCore replier target msg executingCore st).1 :=
    endpointReplyOnCore_preserves_ipcInvariantFull replier target msg executingCore st hInv
      hObjInv hWtpmn' hDOV' hAllBudgetsNone
  have hReplyInv : (endpointReplyOnCore replier target msg executingCore st).1.objects.invExt :=
    endpointReplyOnCore_preserves_objects_invExt replier target msg executingCore st hObjInv
  have hBack := endpointReplyOnCore_tcb_backward replier target msg executingCore st hObjInv
  unfold endpointReplyCrossCoreDispatch
  cases hRep : endpointReplyOnCore replier target msg executingCore st with
  | mk st1 res =>
    rw [hRep] at hReply hReplyInv hBack
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
          cases hDon : applyReplyDonationOnCore st1 expectedV (determineExecutingCore st expected)
              (determineTargetCore st expected) (replyDonationOwnerHome st expected) with
          | error e => simp only; exact hInv
          | ok st2 =>
            simp only
            have hDonFull : ipcInvariantFull st2 :=
              applyReplyDonationOnCore_preserves_ipcInvariantFull st1 st2 expectedV _ _ _
                hReplyInv hReply hAllowed hDon
            have hDonInv : st2.objects.invExt :=
              applyReplyDonationOnCore_preserves_objects_invExt st1 st2 expectedV _ _ _
                hReplyInv hDon
            exact propagatePipChainCrossCore_preserves_ipcInvariantFull st2 expected executingCore
              _ hDonInv hDonFull

