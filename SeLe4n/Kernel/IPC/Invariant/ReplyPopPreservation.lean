/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Invariant.UnheldContextPop

/-!
# The IPC bundle across the single-core reply pop

`applyReplyDonation` is seL4-MCS's `reply_pop` at the answered frame: the
donated context returned from the thread holding it, or -- where the frame heads
a context its finalised server returned to no one -- that context donated to the
answered caller (`popUnheldReplyHead`, WS-ZA ZA6.34).  These are the two bundle
statements over it; they sit above the unheld pop's own
(`popUnheldReplyHead_preserves_ipcInvariantFull`), which reads the donation
read-agreement layer `DonationPreservation` provides.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)
open SeLe4n.Kernel.PriorityInheritance

/-- **WS-RR RR2.5**: `applyReplyDonation` preserves the whole nineteen-conjunct IPC
bundle — the return (`returnDonatedSchedContext_preserves_ipcInvariantFull`)
followed by the **holder's** deschedule, which writes only run-queue links.

**WS-HP HP4.2 — the precondition is quantified over the trigger.**  The
head-driven trigger reads the holder off `SchedContext.boundThread`, so the
obligation attaches to whichever thread the trigger names — and is discharged
vacuously on every reply that pops nothing.  `hHolderDonation` is that
precondition, and **HP7
(`v0.35.46`) did not retire it**: see `replyFrameHeadHolderDonation` for why the
trigger fixes the two threads without fixing the binding between them, which is
exactly what keeps this hypothesis load-bearing.  HP7 retired the *binding-driven*
readings, whose content the trigger does witness; this one it does not, so it stays
stated.  (The docstring here named `answeredHeadHolderDonation`, the name HP4.2
renamed away.) -/
theorem applyReplyDonation_preserves_ipcInvariantFull
    (st st'' : SystemState) (rid : SeLe4n.ReplyId) (targetVtid : SeLe4n.ValidThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st)
    (hHolderDonation : replyFrameHeadHolderDonation st rid targetVtid.val)
    -- **WS-OD OD4.4**: the pop resolves its new owner from the context's reply
    -- stack, so at depth ≥ 2 it mints a `.donated` binding at the outer caller.
    -- This is the half of that obligation no O(1) guard can decide.
    (hStackValid : ∀ scId serverTid originalOwner,
        replyStackOuterCallerValid st scId serverTid originalOwner)
    -- **`v0.35.157`**: the origin redirect's guard is the bind's own admissibility,
    -- and what makes it sound is the binding → head coherence fact at the resolved
    -- origin -- gated on the trigger, the resolver and the distinctness, so it
    -- costs every reply that redirects nothing exactly nothing.
    (hOriginCoherent : redirectedOriginFrameCoherent st rid targetVtid.val)
    -- **WS-ZA ZA6.34**: the unheld pop's obligation, vacuous where the frame
    -- heads nothing or a held context.
    (hUnheld : unheldReplyPopCoherent st rid targetVtid.val)
    (h : applyReplyDonation st rid targetVtid = .ok st'') :
    ipcInvariantFull st'' := by
  rcases applyReplyDonation_ok_decompose st st'' rid targetVtid h with
    ⟨hNoH, hEq⟩ | ⟨scId, holderVtid, newOwner?, st', hHead, hRes, hR, hEq⟩
  · exact popUnheldReplyHead_preserves_ipcInvariantFull hObjInv hInv hStackValid hUnheld hNoH hEq
  · have hRet : replyDonationReturn? st holderVtid.val = some (scId, targetVtid.val) :=
      hHolderDonation scId holderVtid.val hHead
    -- **WS-HP HP10.7: three cases, and only the third is new.**  No origin
    -- recorded, or one that *is* the answered caller, both reduce the redirect to
    -- the identity and run the pre-HP10.7 argument verbatim; a distinct origin
    -- takes the generalised bundle, whose extra hypothesis is exactly what the
    -- redirect's own `donationOriginRebindable` guard supplies.
    have hFull' : ipcInvariantFull st' := by
      by_cases hNoOrigin : donationOriginRecipient? st scId = none
      · rw [replyDonationRecipient_eq_of_no_origin st scId targetVtid.val hNoOrigin] at hR
        exact returnDonatedSchedContext_preserves_ipcInvariantFull st st' holderVtid scId
          targetVtid.val hObjInv hInv hRet newOwner?
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
            targetVtid.val hObjInv hInv hRet newOwner?
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
            newOwner?
            (donationReturnOuterValid_of_stackValid (hStackValid scId holderVtid.val o) hRes) hR
    rw [hEq]
    exact ipcInvariantFull_of_objectsAgreeOffRunLinks
      (removeRunnable_objectsAgreeOffRunLinks _ holderVtid.val)
      (ipcInvariantFull_of_objectsAgreeOffSchedulerLinks
        (.of_releaseLinks (SchedContextOps.settleReturnedContext_agree st'
          Concurrency.bootCoreId scId)) hFull')


/-- WS-RR RR3.12: `applyReplyDonation` **establishes** the full bundle from the form
relaxed at the thread the reply woke.

This is the composite half of the reply chain's honest statement.  The bare reply
leaves `donationOwnerValid` false whenever the answered call donated
(`endpointReply_preserves_ipcInvariantFullExceptDonationOwner`); this step is the one
that puts it back, and `hDonationReturned` is what ties the two together: *if* anything
is donated by the woken thread, this replier's donation return is exactly it.  That is
a condition on the **pre**-state and the operation's argument, true on the seL4-MCS
path because a caller donates to the very server that later answers it — categorically
unlike the post-state conjunct the reply bundles used to thread.

When nothing is donated by the woken thread the condition is vacuous, the relaxed
bundle is already the full one, and the unrelaxed theorem below applies unchanged. -/
theorem applyReplyDonation_establishes_ipcInvariantFull_of_except
    (st st'' : SystemState) (rid : SeLe4n.ReplyId) (targetVtid : SeLe4n.ValidThreadId)
    (woken : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFullExceptDonationOwner st woken)
    -- **WS-HP HP4.2**: the condition is re-keyed on the head-driven trigger, and
    -- it now names *both* threads: if anything is donated by the woken thread,
    -- this reply's answered frame heads exactly that context and `s` is exactly
    -- the thread holding it.  Under the binding-driven trigger the holder was the
    -- operation's own argument so only the context had to be named.
    (hDonationReturned : ∀ (s : SeLe4n.ThreadId) (sTcb : TCB) (sc : SeLe4n.SchedContextId),
      st.objects[s.toObjId]? = some (.tcb sTcb) →
      sTcb.schedContextBinding = .donated sc woken →
      replyFrameHeadHolder? st rid = some (sc, s))
    (hHolderDonation : replyFrameHeadHolderDonation st rid targetVtid.val)
    -- **WS-OD OD4.4**: see `applyReplyDonation_preserves_ipcInvariantFull`.
    (hStackValid : ∀ scId serverTid originalOwner,
        replyStackOuterCallerValid st scId serverTid originalOwner)
    -- **`v0.35.157`**: see `applyReplyDonation_preserves_ipcInvariantFull`.
    (hOriginCoherent : redirectedOriginFrameCoherent st rid targetVtid.val)
    -- **WS-ZA ZA6.34**: see `applyReplyDonation_preserves_ipcInvariantFull`.
    (hUnheld : unheldReplyPopCoherent st rid targetVtid.val)
    (h : applyReplyDonation st rid targetVtid = .ok st'') :
    ipcInvariantFull st'' := by
  by_cases hAny : ∃ (s : SeLe4n.ThreadId) (sTcb : TCB) (sc : SeLe4n.SchedContextId),
      st.objects[s.toObjId]? = some (.tcb sTcb) ∧ sTcb.schedContextBinding = .donated sc woken
  · -- The woken thread did donate; `hDonationReturned` pins this return to it.
    obtain ⟨s0, sTcb0, sc0, hS0, hB0⟩ := hAny
    have hHeadEq := hDonationReturned s0 sTcb0 sc0 hS0 hB0
    rcases applyReplyDonation_ok_decompose st st'' rid targetVtid h with
      ⟨hNone, _⟩ | ⟨scId, holderVtid, newOwner?, st', hHead, hRes, hR, hEq⟩
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
      have hFull' : ipcInvariantFull st' := by
        by_cases hNoOrigin : donationOriginRecipient? st scId = none
        · rw [replyDonationRecipient_eq_of_no_origin st scId targetVtid.val hNoOrigin] at hR
          exact returnDonatedSchedContext_establishes_ipcInvariantFull_of_except st st' holderVtid
            scId targetVtid.val hObjInv hInv hRet newOwner?
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
              holderVtid scId targetVtid.val hObjInv hInv hRet newOwner?
              (donationReturnOuterValid_of_stackValid
                (hStackValid scId holderVtid.val targetVtid.val) hRes) hR
          · rw [hRecipEq] at hR
            exact returnDonatedSchedContext_establishes_ipcInvariantFull_of_except_redirected
              st st' holderVtid scId targetVtid.val o hObjInv hInv hRet
              (donationOriginRebindable_no_owner
                (hOriginCoherent scId holderVtid.val o hHead hOrigin hSame)
                (donationOriginRecipient?_resolves st hOrigin)
                (donationOriginRecipient?_rebindable st hOrigin))
              newOwner?
              (donationReturnOuterValid_of_stackValid (hStackValid scId holderVtid.val o) hRes) hR
      rw [hEq]
      exact ipcInvariantFull_of_objectsAgreeOffRunLinks
        (removeRunnable_objectsAgreeOffRunLinks _ holderVtid.val)
        (ipcInvariantFull_of_objectsAgreeOffSchedulerLinks
          (.of_releaseLinks (SchedContextOps.settleReturnedContext_agree st'
            Concurrency.bootCoreId scId)) hFull')
  · -- Nothing is donated by the woken thread, so the relaxation is empty.
    exact applyReplyDonation_preserves_ipcInvariantFull st st'' rid targetVtid hObjInv
      (ipcInvariantFull_of_exceptDonationOwner hInv
        (donationOwnerValid_of_except_of_no_donation_owned_by hInv.donationOwnerValidExcept
          (fun tid tcb sc hTcb hBind => hAny ⟨tid, tcb, sc, hTcb, hBind⟩)))
      hHolderDonation hStackValid hOriginCoherent hUnheld h

end SeLe4n.Kernel
