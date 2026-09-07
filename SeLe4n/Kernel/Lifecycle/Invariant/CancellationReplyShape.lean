-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Invariant.CancellationNotificationShape

/-!
# WS-RR RR7.22 (residual, remediation) — the cancelled caller's donation

seL4-MCS's `cancelIPC` on a reply-blocked thread runs `reply_remove`, which hands
back the scheduling context the caller donated on its `Call`.  Until v0.34.97
this model's `.blockedOnReply` arm cleared the reply *link* only, so the server
kept `schedContextBinding = .donated scId caller` while the caller was moved to
`.ready` and then `.Inactive` — a state `donationOwnerValid` forbids, and
operationally a permanent transfer of the caller's CBS reservation to the server,
after which the caller could never be scheduled again.

No existing theorem was unsound: nothing claimed `donationOwnerValid` across
suspend.  That is what made it a false-assurance gap rather than a broken proof,
and why the reply arm could not state the bundle.

## What this module holds

`donationHolderIsReplyTarget` — the fact the return needs and the bundle does not
entail: the thread holding a caller's donation is the caller's own recorded reply
target, and is a real (non-reserved) thread.  Operationally maintained — every
`.blockedOnReply` write in this tree names the receiver, and the `Call` donates to
that same receiver — but `ipcInvariantFull` admits `.blockedOnReply epId rt` for
any `rt` and relates `rt` to no donation.  Stated, in the same style as this
workstream's other four queue-coherence facts.

The *behaviour* needs no hypothesis: a donation found at the reply target is
always returned, which improves every state and regresses none.  The hypothesis
scopes the **proof** that the arm leaves no donation naming the caller
(`cancelIpcBlocking_reply_no_donation_to_victim`) — the theorem that says the
defect is fixed.

## What it does not hold yet

The whole `ipcInvariantFull` for the reply arm.  That needs the other nineteen
conjuncts carried through three writes, and is the reply arm's bundle cut; the
conjunct this remediation is *about* is proved here in the form that matters —
the premise of `donationOwnerValid`'s second clause has no witness naming the
cancelled caller after the arm runs.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.RobinHood

-- ============================================================================
-- §1  The resolver, characterised
-- ============================================================================

theorem cancelledCallerDonation?_some (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (h : Lifecycle.Suspend.cancelledCallerDonation? st tid tcb = some (scId, holder)) :
    (∃ ep, tcb.ipcState = .blockedOnReply ep (some holder)) ∧
    ∃ holderTcb, lookupTcb st holder = some holderTcb ∧
      holderTcb.schedContextBinding = .donated scId tid := by
  unfold Lifecycle.Suspend.cancelledCallerDonation? at h
  repeat' split at h
  all_goals simp_all

def donationHolderIsReplyTarget (st : SystemState) (owner : SeLe4n.ThreadId) : Prop :=
  ∀ ownerTcb, lookupTcb st owner = some ownerTcb →
    ∀ (holder : SeLe4n.ThreadId) (holderTcb : TCB) (scId : SeLe4n.SchedContextId),
      st.objects[holder.toObjId]? = some (.tcb holderTcb) →
      holderTcb.schedContextBinding = .donated scId owner →
        (∃ epId, ownerTcb.ipcState = .blockedOnReply epId (some holder)) ∧
        lookupTcb st holder = some holderTcb

theorem returnDonationToCancelledCaller_no_donation_to_victim
    (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hOwner : donationOwnerValid st)
    (hHolder : donationHolderIsReplyTarget st v)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (hTcb : (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV).objects[tid.toObjId]?
      = some (.tcb tcb)) :
    tcb.schedContextBinding ≠ .donated scId v := by
  intro hBind
  have hGetV : st.getTcb? v = some tcbV := by
    rw [SystemState.getTcb?_eq_some_iff]; exact lookupTcb_some_objects st v tcbV hLookup
  unfold Lifecycle.Suspend.returnDonationToCancelledCaller at hTcb
  rw [hGetV] at hTcb
  cases hRes : Lifecycle.Suspend.cancelledCallerDonation? st v tcbV with
  | none =>
    rw [hRes] at hTcb
    simp only at hTcb
    obtain ⟨⟨epId, hIp⟩, hLkH⟩ := hHolder tcbV hLookup tid tcb scId hTcb hBind
    exact absurd hRes (by
      unfold Lifecycle.Suspend.cancelledCallerDonation?
      simp [hIp, hLkH, hBind])
  | some p =>
    obtain ⟨scId0, holder⟩ := p
    rw [hRes] at hTcb
    simp only at hTcb
    obtain ⟨⟨ep, hIpV⟩, holderTcb, hLkH, hBindH⟩ := cancelledCallerDonation?_some st v tcbV
      scId0 holder hRes
    -- The reclaim aborts the holder's outstanding IPC first; every fact the
    -- hand-back reads survives that step, and the holder's own `.donated`
    -- binding is what keeps `donationOwnerValid` true across it.
    have hHolderAt := lookupTcb_some_objects st holder holderTcb hLkH
    have hGetH : st.getTcb? holder = some holderTcb :=
      (SystemState.getTcb?_eq_some_iff st holder holderTcb).mpr hHolderAt
    have hBoundH : ∀ t, st.getTcb? holder = some t →
        t.schedContextBinding ≠ .unbound := by
      intro t hAt
      have hEqT : t = holderTcb := Option.some.inj (hAt.symm.trans hGetH)
      rw [hEqT, hBindH]
      intro hc; cases hc
    have hInvA : (Lifecycle.Suspend.abortHolderPendingIpc st holder).objects.invExt :=
      Lifecycle.Suspend.abortHolderPendingIpc_preserves_objects_invExt st holder hInv
    have hOwnerA : donationOwnerValid (Lifecycle.Suspend.abortHolderPendingIpc st holder) :=
      Lifecycle.Suspend.abortHolderPendingIpc_preserves_donationOwnerValid st holder hInv
        hBoundH hOwner
    obtain ⟨holderTcbA, hHolderAtA, hBindEqA⟩ :=
      Lifecycle.Suspend.abortHolderPendingIpc_binding_forward st holder hInv holder.toObjId
        holderTcb hHolderAt
    have hLkHA : lookupTcb (Lifecycle.Suspend.abortHolderPendingIpc st holder) holder
        = some holderTcbA :=
      lookupTcb_of_objects_of_not_reserved _ holder holderTcbA hHolderAtA
        (lookupTcb_some_not_reserved st holder holderTcb hLkH)
    obtain ⟨st', hOk⟩ := returnDonatedSchedContext_ok_under_invariants
      (Lifecycle.Suspend.abortHolderPendingIpc st holder) holder holderTcbA
      scId0 v hInvA hOwnerA hLkHA (hBindEqA.trans hBindH)
      (lookupTcb_some_not_reserved st holder holderTcb hLkH)
      (lookupTcb_some_not_reserved st v tcbV hLookup)
    rw [hOk] at hTcb
    simp only at hTcb
    obtain ⟨hSrv, hOwn, hOther⟩ := returnDonatedSchedContext_tcb_schedContextBinding_backward
      (Lifecycle.Suspend.abortHolderPendingIpc st holder) st' holder scId0 v hInvA hOk
      tid.toObjId tcb hTcb
    by_cases hH : tid.toObjId = holder.toObjId
    · rw [hSrv hH] at hBind; cases hBind
    · by_cases hV : tid.toObjId = v.toObjId
      · rw [hOwn hH hV] at hBind; cases hBind
      · obtain ⟨tA, hAtA, hEqA⟩ := hOther hH hV
        obtain ⟨t0, h0, hEqB⟩ :=
          Lifecycle.Suspend.abortHolderPendingIpc_binding_backward st holder hInv tid.toObjId
            tA hAtA
        obtain ⟨⟨epId, hIp⟩, _⟩ := hHolder tcbV hLookup tid t0 scId h0
          (by rw [hEqB, hEqA]; exact hBind)
        rw [hIpV] at hIp
        exact hH (by rw [(Option.some.inj (ThreadIpcState.blockedOnReply.inj hIp).2)])

theorem clearTcbReplyObject_sameSchedContextBindings (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    sameSchedContextBindings st (Lifecycle.Suspend.clearTcbReplyObject st tid) := by
  intro k tcb' hTcb'
  unfold Lifecycle.Suspend.clearTcbReplyObject at hTcb'
  split at hTcb'
  · rename_i t hT
    by_cases hk : k = tid
    · subst hk
      have hx : (st.objects.insert k.toObjId (.tcb { t with replyObject := none })).get?
          k.toObjId = some (.tcb tcb') := hTcb'
      rw [RHTable.getElem?_insert_self st.objects k.toObjId _ hInv] at hx
      have hEqT : { t with replyObject := (none : Option SeLe4n.ReplyId) } = tcb' :=
        KernelObject.tcb.inj (Option.some.inj hx)
      exact ⟨t, (SystemState.getTcb?_eq_some_iff st k t).mp hT, by rw [← hEqT]⟩
    · have hx : (st.objects.insert tid.toObjId _).get? k.toObjId = some (.tcb tcb') := hTcb'
      rw [RHTable.getElem?_insert_ne st.objects tid.toObjId k.toObjId _
        (by simpa using fun h => hk (SeLe4n.ThreadId.toObjId_injective _ _ h).symm) hInv] at hx
      exact ⟨tcb', hx, rfl⟩
  · exact ⟨tcb', hTcb', rfl⟩

theorem clearReplyObjectCaller_sameSchedContextBindings (st : SystemState)
    (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt) :
    sameSchedContextBindings st (Lifecycle.Suspend.clearReplyObjectCaller st rid) := by
  intro k tcb' hTcb'
  unfold Lifecycle.Suspend.clearReplyObjectCaller at hTcb'
  split at hTcb'
  · rename_i r hR
    by_cases hk : k.toObjId = rid.toObjId
    · exfalso
      have hx : (st.objects.insert rid.toObjId (.reply { r with caller := none })).get?
          k.toObjId = some (.tcb tcb') := hTcb'
      rw [hk, RHTable.getElem?_insert_self st.objects rid.toObjId _ hInv] at hx
      cases hx
    · have hx : (st.objects.insert rid.toObjId _).get? k.toObjId = some (.tcb tcb') := hTcb'
      rw [RHTable.getElem?_insert_ne st.objects rid.toObjId k.toObjId _
        (by simpa using fun h => hk h.symm) hInv] at hx
      exact ⟨tcb', hx, rfl⟩
  · exact ⟨tcb', hTcb', rfl⟩

theorem consumeReplyLink_sameSchedContextBindings (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hInv : st.objects.invExt) :
    sameSchedContextBindings st (Lifecycle.Suspend.consumeReplyLink st tid tcb) := by
  unfold Lifecycle.Suspend.consumeReplyLink
  split
  · exact sameSchedContextBindings.refl st
  · rename_i rid _
    exact (clearTcbReplyObject_sameSchedContextBindings st tid hInv).trans
      (clearReplyObjectCaller_sameSchedContextBindings _ rid
        (Lifecycle.Suspend.clearTcbReplyObject_preserves_objects_invExt st tid hInv))

theorem restoreToReadyStaging_sameSchedContextBindings (st : SystemState)
    (tid : SeLe4n.ThreadId) (frame : Option Architecture.SyscallReturnFrame)
    (hInv : st.objects.invExt) :
    sameSchedContextBindings st (Lifecycle.Suspend.restoreToReadyStaging st tid frame) := by
  intro k tcb' hTcb'
  by_cases hk : k.toObjId = tid.toObjId
  · rw [hk] at hTcb'
    cases hT : st.getTcb? tid with
    | none =>
      rw [restoreToReadyStaging_eq, hT] at hTcb'
      simp only at hTcb'
      exact ⟨tcb', by rw [hk]; exact hTcb', rfl⟩
    | some t =>
      rw [restoreToReadyStaging_objects_self st tid frame t hInv hT] at hTcb'
      have hEqT : restoredTcb t frame = tcb' := KernelObject.tcb.inj (Option.some.inj hTcb')
      refine ⟨t, ?_, ?_⟩
      · rw [hk]; exact (SystemState.getTcb?_eq_some_iff st tid t).mp hT
      · rw [← hEqT, restoredTcb_eq]
  · rw [restoreToReadyStaging_objects_ne st tid frame k.toObjId hInv hk] at hTcb'
    exact ⟨tcb', hTcb', rfl⟩

/-- **WS-RR RR7.22 (residual, remediation) — the payoff**: after the corrected
reply arm, **no** thread holds a SchedContext donated by the cancelled caller.

That is the invariant the arm used to break: `donationOwnerValid` requires a
donation's owner to be `.unbound` and `.blockedOnReply`, and the cancellation
makes the caller `.ready`.  Returning the donation removes the edge rather than
leaving it dangling, so the conjunct's premise no longer has a witness at all —
which is why the fix is a *return* and not a weakening of the invariant. -/
theorem cancelIpcBlocking_reply_no_donation_to_victim
    (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB) (ep : SeLe4n.ObjId)
    (rt : Option SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hBlocked : tcbV.ipcState = .blockedOnReply ep rt)
    (hOwner : donationOwnerValid st)
    (hHolder : donationHolderIsReplyTarget st v)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (hTcb : (Lifecycle.Suspend.cancelIpcBlocking st v tcbV).objects[tid.toObjId]?
      = some (.tcb tcb)) :
    tcb.schedContextBinding ≠ .donated scId v := by
  have hArm : Lifecycle.Suspend.cancelIpcBlocking st v tcbV =
      Lifecycle.Suspend.consumeReplyLink
        (Lifecycle.Suspend.restoreToReadyCancelled
          (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) v) v tcbV := by
    unfold Lifecycle.Suspend.cancelIpcBlocking
    rw [hBlocked]
  rw [hArm] at hTcb
  have hInvR := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt st v tcbV hInv
  have hInvS := Lifecycle.Suspend.restoreToReadyCancelled_invExt _ v hInvR
  have hSame :
      sameSchedContextBindings (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV)
        (Lifecycle.Suspend.consumeReplyLink
          (Lifecycle.Suspend.restoreToReadyCancelled
            (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) v) v tcbV) :=
    (restoreToReadyStaging_sameSchedContextBindings _ v _ hInvR).trans
      (consumeReplyLink_sameSchedContextBindings _ v tcbV hInvS)
  obtain ⟨t0, h0, hEqB⟩ := hSame tid tcb hTcb
  intro hBind
  exact returnDonationToCancelledCaller_no_donation_to_victim st v tcbV hInv hLookup hOwner
    hHolder tid t0 scId h0 (by rw [hEqB]; exact hBind)

end SeLe4n.Kernel
