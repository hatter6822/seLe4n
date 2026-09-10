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
    -- WS-OD OD3.2: the reclaim's hand-back runs `returnDonatedSchedContext`, whose
    -- reply-stack head validation is ruled out by the chain invariant.  It is a
    -- conjunct of `ipcReachable` rather than of `ipcInvariantFull`, so it is
    -- stated rather than projected, and it carries across the holder abort by
    -- `abortHolderPendingIpc_donationChainFrame`.
    (hChain : donationChainWellFormed st)
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
    have hHeadResA : donationHeadResolves (Lifecycle.Suspend.abortHolderPendingIpc st holder)
        scId0 :=
      donationHeadResolves_of_frame
        (Lifecycle.Suspend.abortHolderPendingIpc_donationChainFrame st holder hInv) scId0
        (donationHeadResolves_of_chainWellFormed st scId0 hChain)
    obtain ⟨st', hOk⟩ := returnDonatedSchedContext_ok_under_invariants
      (Lifecycle.Suspend.abortHolderPendingIpc st holder) holder holderTcbA
      scId0 v hInvA hOwnerA hHeadResA hLkHA (hBindEqA.trans hBindH)
      (lookupTcb_some_not_reserved st holder holderTcb hLkH)
      (lookupTcb_some_not_reserved st v tcbV hLookup) none
      -- WS-OD OD4.4: the pop's outer-caller guard is free at the bottom of the
      -- reply stack, which is what this site passes.
      (outerCallerAcceptable_none _ holder v)
    rw [hOk] at hTcb
    simp only at hTcb
    obtain ⟨hSrv, hOwn, hOther⟩ := returnDonatedSchedContext_tcb_schedContextBinding_backward
      (Lifecycle.Suspend.abortHolderPendingIpc st holder) st' holder scId0 v hInvA none hOk
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


-- ============================================================================
-- §4  WS-OD OD1.5 — the reply arm frames `passiveServerIdle`
-- ============================================================================

/-- WS-OD OD1.5: clearing the caller's forward reply link frames
`passiveServerIdle` — its one write rewrites `replyObject`, which is neither
field the conjunct reads. -/
theorem clearTcbReplyObject_passiveServerIdleFrame (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    passiveServerIdleFrame st (Lifecycle.Suspend.clearTcbReplyObject st tid) := by
  refine passiveServerIdleFrame_of_backward ?_
    (Lifecycle.Suspend.clearTcbReplyObject_scheduler_eq st tid)
  intro a tcb' hPost
  unfold Lifecycle.Suspend.clearTcbReplyObject at hPost
  split at hPost
  · rename_i t hT
    by_cases hk : a = tid
    · subst hk
      have hx : (st.objects.insert a.toObjId (.tcb { t with replyObject := none })).get?
          a.toObjId = some (.tcb tcb') := hPost
      rw [RHTable.getElem?_insert_self st.objects a.toObjId _ hInv] at hx
      have hEqT : { t with replyObject := (none : Option SeLe4n.ReplyId) } = tcb' :=
        KernelObject.tcb.inj (Option.some.inj hx)
      exact ⟨t, (SystemState.getTcb?_eq_some_iff st a t).mp hT, by rw [← hEqT], by rw [← hEqT]⟩
    · have hx : (st.objects.insert tid.toObjId _).get? a.toObjId = some (.tcb tcb') := hPost
      rw [RHTable.getElem?_insert_ne st.objects tid.toObjId a.toObjId _
        (by simpa using fun h => hk (SeLe4n.ThreadId.toObjId_injective _ _ h).symm) hInv] at hx
      exact ⟨tcb', hx, rfl, rfl⟩
  · exact ⟨tcb', hPost, rfl, rfl⟩

/-- WS-OD OD1.5: clearing the Reply's back-link frames `passiveServerIdle` — its
one write lands on a `.reply` value, whose key can never hold a TCB. -/
theorem clearReplyObjectCaller_passiveServerIdleFrame (st : SystemState)
    (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt) :
    passiveServerIdleFrame st (Lifecycle.Suspend.clearReplyObjectCaller st rid) := by
  refine passiveServerIdleFrame_of_backward ?_
    (Lifecycle.Suspend.clearReplyObjectCaller_scheduler_eq st rid)
  intro a tcb' hPost
  refine ⟨tcb', ?_, rfl, rfl⟩
  unfold Lifecycle.Suspend.clearReplyObjectCaller at hPost
  split at hPost
  · rename_i r hR
    by_cases hk : a.toObjId = rid.toObjId
    · exfalso
      have hx : (st.objects.insert rid.toObjId (.reply { r with caller := none })).get?
          a.toObjId = some (.tcb tcb') := hPost
      rw [hk, RHTable.getElem?_insert_self st.objects rid.toObjId _ hInv] at hx
      cases hx
    · have hx : (st.objects.insert rid.toObjId _).get? a.toObjId = some (.tcb tcb') := hPost
      rw [RHTable.getElem?_insert_ne st.objects rid.toObjId a.toObjId _
        (by simpa using fun h => hk h.symm) hInv] at hx
      exact hx
  · exact hPost

/-- WS-OD OD1.5: the reply-link consume frames `passiveServerIdle`. -/
theorem consumeReplyLink_passiveServerIdleFrame (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hInv : st.objects.invExt) :
    passiveServerIdleFrame st (Lifecycle.Suspend.consumeReplyLink st tid tcb) := by
  unfold Lifecycle.Suspend.consumeReplyLink
  cases tcb.replyObject with
  | none => exact passiveServerIdleFrame.refl st
  | some rid =>
    exact (clearTcbReplyObject_passiveServerIdleFrame st tid hInv).trans
      (clearReplyObjectCaller_passiveServerIdleFrame _ rid
        (Lifecycle.Suspend.clearTcbReplyObject_preserves_objects_invExt st tid hInv))

/-- WS-OD OD1.5: the unblock-and-stage rewrite frames `passiveServerIdle`.

The restored thread is the only one it writes, and it writes `.ready` there —
which the frame's own filter admits, so the pullback never reaches it.  This is
the same argument `sweptAndRestored_passiveServerIdleFrame` makes for the queue
arms, at the bare rewrite rather than at the composite. -/
theorem restoreToReadyStaging_passiveServerIdleFrame (st : SystemState)
    (tid : SeLe4n.ThreadId) (frame : Option Architecture.SyscallReturnFrame)
    (hInv : st.objects.invExt) :
    passiveServerIdleFrame st (Lifecycle.Suspend.restoreToReadyStaging st tid frame) := by
  refine passiveServerIdleFrame_of_backward_of_not_allowed ?_
    (Lifecycle.Suspend.restoreToReadyStaging_scheduler_eq st tid frame)
  intro a tcb' hPostT _ hNA
  have hPost := (SystemState.getTcb?_eq_some_iff _ a tcb').mp hPostT
  by_cases hk : a.toObjId = tid.toObjId
  · rw [hk] at hPost
    cases hT : st.getTcb? tid with
    | none =>
      rw [restoreToReadyStaging_eq, hT] at hPost
      simp only at hPost
      exact ⟨tcb', (SystemState.getTcb?_eq_some_iff st a tcb').mpr (by rw [hk]; exact hPost),
        rfl, rfl⟩
    | some t =>
      exfalso
      rw [restoreToReadyStaging_objects_self st tid frame t hInv hT] at hPost
      have hEqT : restoredTcb t frame = tcb' := KernelObject.tcb.inj (Option.some.inj hPost)
      exact hNA (Or.inl (by rw [← hEqT, restoredTcb_ipcState]))
  · rw [restoreToReadyStaging_objects_ne st tid frame a.toObjId hInv hk] at hPost
    exact ⟨tcb', (SystemState.getTcb?_eq_some_iff st a tcb').mpr hPost, rfl, rfl⟩


/-- WS-OD OD1.5: the hand-back frames `passiveServerIdle`, given that the holder
it unbinds is already in a state the conjunct permits.

Three classes of thread, and each is discharged by a *different* one of the two
hypotheses the frame makes available — which is why both are handed to the
backward obligation:

* the **holder** keeps its `ipcState` (the return writes bindings and one
  SchedContext, never a blocking state) and becomes `.unbound`, so only the
  `¬ passiveServerIdleAllowed` filter can exclude it — hence `hHolderAllowed`,
  which OD1.4's abort prefix is what makes true;
* the **caller** becomes `.bound scId`, so the pullback's own `.unbound`
  hypothesis excludes it outright;
* **everyone else** keeps both fields.

`hHolderAllowed` is stated on the state the return is applied to, not on the
reclaim's pre-state, because the abort runs in between and is exactly what moves
the holder into the permitted half. -/
theorem returnDonatedSchedContext_passiveServerIdleFrame
    {sA st' : SystemState} {holder : SeLe4n.ThreadId} {scId : SeLe4n.SchedContextId}
    {owner : SeLe4n.ThreadId}
    (hInv : sA.objects.invExt)
    (newOwner? : Option SeLe4n.ThreadId)
    (hOk : returnDonatedSchedContext sA holder scId owner newOwner? = .ok st')
    (hHolderAllowed : ∀ t, sA.getTcb? holder = some t →
      passiveServerIdleAllowed t.ipcState) :
    passiveServerIdleFrame sA st' := by
  refine passiveServerIdleFrame_of_backward_of_not_allowed ?_
    (returnDonatedSchedContext_scheduler_eq sA st' holder scId owner newOwner? hOk)
  intro a tcb' hPostT hUnbound hNA
  have hPost := (SystemState.getTcb?_eq_some_iff st' a tcb').mp hPostT
  obtain ⟨t0, h0, hIpc, _⟩ :=
    returnDonatedSchedContext_tcb_ipcState_replyObject_backward sA st' holder scId owner hInv
      newOwner? hOk a.toObjId tcb' hPost
  obtain ⟨hSrv, hOwn, hOther⟩ :=
    returnDonatedSchedContext_tcb_schedContextBinding_backward sA st' holder scId owner hInv
      newOwner? hOk a.toObjId tcb' hPost
  by_cases hH : a.toObjId = holder.toObjId
  · exact absurd (hIpc ▸ hHolderAllowed t0
      ((SystemState.getTcb?_eq_some_iff sA holder t0).mpr (hH ▸ h0))) hNA
  · by_cases hV : a.toObjId = owner.toObjId
    · -- WS-OD OD3.2: the target's post-binding names `scId` on both arms of
      -- `donationReturnBinding`, so it is never `.unbound`.
      refine absurd (hOwn hH hV) ?_
      rw [hUnbound]
      cases newOwner? <;> intro hc <;> cases hc
    · obtain ⟨t1, h1, hB1⟩ := hOther hH hV
      rw [h0] at h1
      have hEqT : t0 = t1 := KernelObject.tcb.inj (Option.some.inj h1)
      exact ⟨t0, (SystemState.getTcb?_eq_some_iff sA a t0).mpr h0, hIpc,
        by rw [hEqT]; exact hB1⟩

/-- **WS-OD OD1.5**: the cancellation reclaim frames `passiveServerIdle`.

The abort prefix and the hand-back compose: the prefix moves a holder blocked
sending or calling into `.ready` (`abortHolderPendingIpc_passiveServerIdleFrame`),
and the hand-back then unbinds a holder that is *already* in the permitted half
(`abortHolderPendingIpc_holder_ipcState_allowed`).  Reversing them would leave an
intermediate state with an `.unbound` holder still blocked on a call — which is
the whole reason OD1.4 put the abort first, restated here as the frame that would
otherwise not exist. -/
theorem returnDonationToCancelledCaller_passiveServerIdleFrame
    (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB)
    (hInv : st.objects.invExt)
    (hMem : ipcStateQueueMembershipConsistent st) :
    passiveServerIdleFrame st (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) := by
  unfold Lifecycle.Suspend.returnDonationToCancelledCaller
  split
  · rename_i scId holder _ hRes _
    obtain ⟨_, holderTcb, hLkH, _⟩ := cancelledCallerDonation?_some st v tcbV scId holder hRes
    split
    · rename_i st' hOk
      refine (Lifecycle.Suspend.abortHolderPendingIpc_passiveServerIdleFrame st holder hInv).trans
        (returnDonatedSchedContext_passiveServerIdleFrame
          (Lifecycle.Suspend.abortHolderPendingIpc_preserves_objects_invExt st holder hInv)
          none hOk ?_)
      intro t hAt
      exact Lifecycle.Suspend.abortHolderPendingIpc_holder_ipcState_allowed st holder holderTcb
        hInv hMem hLkH t hAt
    · exact passiveServerIdleFrame.refl st
  · exact passiveServerIdleFrame.refl st


/-- **WS-OD OD1.5 — the payoff frame.**  `cancelIpcBlocking` frames
`passiveServerIdle` on **every** arm.

One statement per arm, and each is already carried by the shape module that owns
it: the two queue arms by `sweptAndRestored` / `purgedAndRestored`, the `.ready`
arm by reflexivity, and the reply arm by the three-step composition this cut
builds.  The reply arm is the one that did not hold before OD1.4: without the
abort prefix its holder ends `.unbound` and still `.blockedOnCall`, in the half
`passiveServerIdle` forbids, and no pullback can produce an `.unbound` pre-state
holder because there is none — the holder was `.donated`. -/
theorem cancelIpcBlocking_passiveServerIdleFrame
    (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB)
    (hInv : st.objects.invExt)
    (hLink : tcbQueueLinkIntegrity st) (hAcyc : tcbQueueChainAcyclic st)
    (hLookup : lookupTcb st v = some tcbV)
    (hMem : ipcStateQueueMembershipConsistent st) :
    passiveServerIdleFrame st (Lifecycle.Suspend.cancelIpcBlocking st v tcbV) := by
  cases hIp : tcbV.ipcState with
  | ready =>
    rw [show Lifecycle.Suspend.cancelIpcBlocking st v tcbV = st by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hIp]]
    exact passiveServerIdleFrame.refl st
  | blockedOnSend ep =>
    rw [cancelIpcBlocking_endpoint_arm_eq st v tcbV ep (Or.inl hIp)]
    exact sweptAndRestored_passiveServerIdleFrame st v _ tcbV hInv hLink hAcyc hLookup
  | blockedOnReceive ep =>
    rw [cancelIpcBlocking_endpoint_arm_eq st v tcbV ep (Or.inr (Or.inl hIp))]
    exact sweptAndRestored_passiveServerIdleFrame st v _ tcbV hInv hLink hAcyc hLookup
  | blockedOnCall ep =>
    rw [cancelIpcBlocking_endpoint_arm_eq st v tcbV ep (Or.inr (Or.inr hIp))]
    exact sweptAndRestored_passiveServerIdleFrame st v _ tcbV hInv hLink hAcyc hLookup
  | blockedOnNotification n =>
    rw [cancelIpcBlocking_notification_arm_eq st v tcbV n hIp]
    exact purgedAndRestored_passiveServerIdleFrame st v _ tcbV hInv hLookup
  | blockedOnReply ep rt =>
    rw [show Lifecycle.Suspend.cancelIpcBlocking st v tcbV =
        Lifecycle.Suspend.consumeReplyLink
          (Lifecycle.Suspend.restoreToReadyCancelled
            (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) v) v tcbV by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hIp]]
    have hF1 := returnDonationToCancelledCaller_passiveServerIdleFrame st v tcbV hInv hMem
    have hI1 := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt
      st v tcbV hInv
    have hF2 := restoreToReadyStaging_passiveServerIdleFrame
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) v
      (some Architecture.cancelledIpcFrame) hI1
    have hI2 := Lifecycle.Suspend.restoreToReadyCancelled_invExt
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) v hI1
    have hF3 := consumeReplyLink_passiveServerIdleFrame
      (Lifecycle.Suspend.restoreToReadyCancelled
        (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) v) v tcbV hI2
    exact (hF1.trans hF2).trans hF3

/-- **WS-OD OD1.5 — the theorem OD1 exists to prove.**

`cancelIpcBlocking` preserves `passiveServerIdle`.  Before OD1.4 this was
*false*: the reply arm's reclaim unbound a holder that could still be
`.blockedOnCall`, reachable at depth 1 with no donation chain — a server that
Calls an endpoint with no receiver waiting keeps the donation, and the reclaim
then unbinds it in place.  Nothing was unsound, because nothing claimed the
conjunct across the cancellation; that is what made it a false-assurance gap, and
it is why this theorem's *existence* is the payoff rather than its statement.

Four hypotheses, and each is a fact about the pre-state rather than a proof
convenience.  `tcbQueueLinkIntegrity` and `tcbQueueChainAcyclic` are what make
the endpoint arm's splice a well-defined relink; `ipcStateQueueMembershipConsistent`
is what makes the reply arm's abort *succeed* — a thread blocked sending or
calling names an endpoint that exists — and without it a refused abort would
leave the holder exactly where the defect left it. -/
theorem cancelIpcBlocking_preserves_passiveServerIdle
    (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB)
    (hInv : st.objects.invExt)
    (hLink : tcbQueueLinkIntegrity st) (hAcyc : tcbQueueChainAcyclic st)
    (hLookup : lookupTcb st v = some tcbV)
    (hMem : ipcStateQueueMembershipConsistent st)
    (hPassive : passiveServerIdle st) :
    passiveServerIdle (Lifecycle.Suspend.cancelIpcBlocking st v tcbV) :=
  passiveServerIdle_of_frame
    (cancelIpcBlocking_passiveServerIdleFrame st v tcbV hInv hLink hAcyc hLookup hMem) hPassive

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
    (hChain : donationChainWellFormed st)
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
    hChain hHolder tid t0 scId h0 (by rw [hEqB]; exact hBind)

-- ============================================================================
-- WS-OD OD3.5 — the reply arm relinks no queue neighbour
-- ============================================================================

/-- **WS-OD OD3.5**: `consumeReplyLink` leaves every TCB but the swept thread's
verbatim.

Its TCB leg (`clearTcbReplyObject`) rewrites `tid` alone, and its Reply leg
(`clearReplyObjectCaller`) writes a key that holds a `.reply`, which can never
alias a TCB-holding key.  The existing `consumeReplyLink_tcb_lookup` says only
that the *kind* and `cpuAffinity` survive; a footprint argument needs the
stronger reading, because "some TCB is still there" does not rule out its links
having changed. -/
theorem consumeReplyLink_other_tcb_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (hInv : st.objects.invExt) (k : SeLe4n.ObjId) (t0 : TCB)
    (hNe : k ≠ tid.toObjId) (hPre : st.objects[k]? = some (.tcb t0)) :
    (Lifecycle.Suspend.consumeReplyLink st tid tcb).objects[k]? = some (.tcb t0) := by
  unfold Lifecycle.Suspend.consumeReplyLink
  cases hR : tcb.replyObject with
  | none => exact hPre
  | some rid =>
    have hClear : (Lifecycle.Suspend.clearTcbReplyObject st tid).objects[k]? = some (.tcb t0) := by
      unfold Lifecycle.Suspend.clearTcbReplyObject
      cases hT : st.getTcb? tid with
      | none => exact hPre
      | some t =>
        show (st.objects.insert tid.toObjId _).get? k = some (.tcb t0)
        rw [RHTable.getElem?_insert_ne st.objects tid.toObjId k _
          (by simpa using fun h => hNe h.symm) hInv]
        exact hPre
    exact (Lifecycle.Suspend.clearReplyObjectCaller_tcb_lookup_eq
      (Lifecycle.Suspend.clearTcbReplyObject st tid) rid k t0
      (Lifecycle.Suspend.clearTcbReplyObject_preserves_objects_invExt st tid hInv)
      hClear).trans hClear

/-- **WS-OD OD3.5: the reply arm writes no queue neighbour** — on the shape where
the reclaim is inert.

This is what licenses the arm-selected cancellation footprint
(`cancelArmSpliceNeighbors?`) to stop declaring the victim's `queuePrev` /
`queueNext` TCB write locks on the reply arm.  A `.blockedOnReply` victim is on
no endpoint queue, so the arm runs no `spliceOutMidQueueNode` and relinks
nothing; here that is *checked* rather than read off the definition, by showing
every TCB but the victim's survives verbatim.

Confined to `cancelledCallerDonation? = none`, and the general form is
`cancelIpcBlocking_replyArm_tcb_frame` below: with a donation the arm
additionally runs `returnDonationToCancelledCaller`, whose writes land on the
holder, its two queue neighbours and the cancelled caller — every one a declared
member of its own.  The two are kept apart because the inert shape needs no
holder hypotheses at all, and a caller that has established
`cancelledCallerDonation? = none` should not have to supply them. -/
theorem cancelIpcBlocking_replyArm_noDonation_tcb_frame (st : SystemState)
    (v : SeLe4n.ThreadId) (tcbV : TCB) (ep : SeLe4n.ObjId)
    (rt : Option SeLe4n.ThreadId)
    (hInv : st.objects.invExt)
    (hBlocked : tcbV.ipcState = .blockedOnReply ep rt)
    (hNoDonation : Lifecycle.Suspend.cancelledCallerDonation? st v tcbV = none)
    (k : SeLe4n.ObjId) (t0 : TCB) (hNe : k ≠ v.toObjId)
    (hPre : st.objects[k]? = some (.tcb t0)) :
    (Lifecycle.Suspend.cancelIpcBlocking st v tcbV).objects[k]? = some (.tcb t0) := by
  have hArm : Lifecycle.Suspend.cancelIpcBlocking st v tcbV =
      Lifecycle.Suspend.consumeReplyLink
        (Lifecycle.Suspend.restoreToReadyCancelled st v) v tcbV := by
    unfold Lifecycle.Suspend.cancelIpcBlocking
    rw [hBlocked, Lifecycle.Suspend.returnDonationToCancelledCaller_none st v tcbV hNoDonation]
  rw [hArm]
  refine consumeReplyLink_other_tcb_eq _ v tcbV
    (Lifecycle.Suspend.restoreToReadyCancelled_invExt st v hInv) k t0 hNe ?_
  show (Lifecycle.Suspend.restoreToReadyStaging st v _).objects[k]? = some (.tcb t0)
  rw [restoreToReadyStaging_objects_ne st v _ k hInv hNe]
  exact hPre

/-- **WS-OD OD3.5**: a successful `endpointQueueRemove` resolved its endpoint.

The removal's two error arms are the unresolvable object and the wrong-kind
object, and `getEndpoint?` collapses exactly those two; so `.ok` entails the
typed read succeeded, which is what lets `endpointQueueRemove_eq_patches` be
stated on the splicing arm without its callers having to carry the endpoint. -/
theorem endpointQueueRemove_ok_getEndpoint?
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hStep : endpointQueueRemove endpointId isReceiveQ tid st = .ok st') :
    ∃ ep, st.getEndpoint? endpointId = some ep := by
  cases hObj : st.objects[endpointId]? with
  | none =>
    simp only [endpointQueueRemove, hObj] at hStep
    exact absurd hStep (by simp)
  | some obj =>
    cases obj with
    | endpoint ep =>
      exact ⟨ep, (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mpr hObj⟩
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
      simp only [endpointQueueRemove, hObj] at hStep
      exact absurd hStep (by simp)

/-- **WS-OD OD3.5**: `endpointQueueRemove`'s two link patches **are**
`queueNeighbourPatch`, the same step `spliceOutMidQueueNode` performs twice.

Stated on the arm that splices — the endpoint resolves, the thread resolves —
rather than as a second copy of the whole body: the equation is then about the
program the removal *runs*, its two error arms are `endpointQueueRemove_ok_getEndpoint?`'s
subject rather than this one's, and the store is read through `getEndpoint?`
rather than by re-opening the discriminator the operation has already opened
(AK7 reader hygiene — a `rfl` restatement of a raw match is still a raw match
site as far as every reader, human or scanner, is concerned).

The tree had two inlined copies of this shape and one named abstraction over it;
naming the third is what makes the removal's write set one lemma rather than a
four-deep nested match.  The two `upd` functions are the shared
`queueUnlinkPredecessor` / `queueUnlinkSuccessor` (WS-OD OD3.9) — the definitions
`endpointQueueRemove` itself applies and `spliceOutMidQueueNode_eq_patches` names
— so the two removals' write sets are stated over one spelling rather than over a
lambda each that could drift apart.  The successor's carries `queuePPrev`
(WS-OD OD1.1), which is why the two patches take different updates and not
one. -/
theorem endpointQueueRemove_eq_patches (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st : SystemState) (ep : Endpoint) (tcb : TCB)
    (hEp : st.getEndpoint? endpointId = some ep)
    (hTcb : lookupTcb st tid = some tcb) :
    endpointQueueRemove endpointId isReceiveQ tid st =
      (let q := if isReceiveQ then ep.receiveQ else ep.sendQ
       let objs := queueNeighbourPatch
         (queueNeighbourPatch st.objects tcb.queuePrev (queueUnlinkPredecessor tcb))
         tcb.queueNext (queueUnlinkSuccessor tcb)
       let q' : IntrusiveQueue :=
         { head := if q.head = some tid then tcb.queueNext else q.head,
           tail := if q.tail = some tid then tcb.queuePrev else q.tail }
       let ep' := if isReceiveQ then { ep with receiveQ := q' } else { ep with sendQ := q' }
       .ok { st with objects :=
         ((objs.insert endpointId (.endpoint ep')).insert tid.toObjId
           (.tcb { tcb with queuePrev := none, queuePPrev := none, queueNext := none })) }) := by
  unfold endpointQueueRemove
  rw [(SystemState.getEndpoint?_eq_some_iff st endpointId ep).mp hEp, hTcb]
  rfl

/-- **WS-OD OD3.5: the removal writes four keys and no others** — the endpoint it
splices, the removed thread, and the two queue neighbours whose links it patches.

The tree had only `endpointQueueRemove_objects_present_backward` (the removal
occupies no key the pre-state did not), and "some object is still there" is not
"the object is unchanged", which is what a declared-write-set argument needs.
The neighbour hypotheses are quantified over the resolution rather than taking
two threads, so a caller that knows the victim has no successor discharges the
second by `simp`. -/
theorem endpointQueueRemove_objects_ne
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState) (tcb : TCB)
    (hInv : st.objects.invExt)
    (hTcb : lookupTcb st tid = some tcb)
    (hStep : endpointQueueRemove endpointId isReceiveQ tid st = .ok st')
    (k : SeLe4n.ObjId)
    (hkEp : k ≠ endpointId) (hkTid : k ≠ tid.toObjId)
    (hkPrev : ∀ p, tcb.queuePrev = some p → k ≠ p.toObjId)
    (hkNext : ∀ n, tcb.queueNext = some n → k ≠ n.toObjId) :
    st'.objects[k]? = st.objects[k]? := by
  obtain ⟨ep, hEp⟩ :=
    endpointQueueRemove_ok_getEndpoint? endpointId isReceiveQ tid st st' hStep
  rw [endpointQueueRemove_eq_patches endpointId isReceiveQ tid st ep tcb hEp hTcb] at hStep
  simp only [Except.ok.injEq] at hStep
  subst hStep
  have hI1 : (queueNeighbourPatch st.objects tcb.queuePrev
      (queueUnlinkPredecessor tcb)).invExt :=
    queueNeighbourPatch_invExt _ _ _ hInv
  have hI2 : (queueNeighbourPatch
      (queueNeighbourPatch st.objects tcb.queuePrev (queueUnlinkPredecessor tcb))
      tcb.queueNext (queueUnlinkSuccessor tcb)).invExt :=
    queueNeighbourPatch_invExt _ _ _ hI1
  simp only [RHTable_getElem?_eq_get?]
  rw [RHTable.getElem?_insert_ne _ tid.toObjId k _
    (by simpa using fun h => hkTid h.symm)
    (RHTable.insert_preserves_invExt _ _ _ hI2)]
  rw [RHTable.getElem?_insert_ne _ endpointId k _
    (by simpa using fun h => hkEp h.symm) hI2]
  rw [← RHTable_getElem?_eq_get?, ← RHTable_getElem?_eq_get?]
  rw [queueNeighbourPatch_at_other _ tcb.queueNext _ hI1 k
    (fun n hn h => hkNext n hn h.symm)]
  exact queueNeighbourPatch_at_other _ tcb.queuePrev _ hInv k
    (fun p hp h => hkPrev p hp h.symm)

/-- **WS-OD OD3.5**: the abort writes the endpoint it splices, the thread it
unblocks, and that thread's two queue neighbours — and nothing else.

`k ≠ epId` is *derived* rather than assumed: a successful removal reads an
`.endpoint` at that key, and the hypothesis says `k` holds a `.tcb`. -/
theorem abortPendingIpcOnEndpoint_other_tcb_eq
    (epId : SeLe4n.ObjId) (isRecvQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState) (tcb : TCB)
    (hInv : st.objects.invExt)
    (hTcb : lookupTcb st tid = some tcb)
    (hStep : abortPendingIpcOnEndpoint epId isRecvQ tid st = .ok st')
    (k : SeLe4n.ObjId) (t0 : TCB)
    (hkTid : k ≠ tid.toObjId)
    (hkPrev : ∀ p, tcb.queuePrev = some p → k ≠ p.toObjId)
    (hkNext : ∀ n, tcb.queueNext = some n → k ≠ n.toObjId)
    (hPre : st.objects[k]? = some (.tcb t0)) :
    st'.objects[k]? = some (.tcb t0) := by
  unfold abortPendingIpcOnEndpoint at hStep
  cases hRem : endpointQueueRemove epId isRecvQ tid st with
  | error e => rw [hRem] at hStep; exact absurd hStep (by simp)
  | ok st1 =>
    rw [hRem] at hStep
    simp only [] at hStep
    -- The removal succeeded, so the endpoint key holds an `.endpoint`; `k` holds
    -- a `.tcb`, so the two are different keys.
    have hkEp : k ≠ epId := by
      intro hEqK
      have hEp : ∃ ep, st.objects[epId]? = some (.endpoint ep) := by
        unfold endpointQueueRemove at hRem
        cases hObj : st.objects[epId]? with
        | none => rw [hObj] at hRem; exact absurd hRem (by simp)
        | some obj =>
          cases obj with
          | endpoint ep => exact ⟨ep, rfl⟩
          | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _
          | reply _ => rw [hObj] at hRem; exact absurd hRem (by simp)
      obtain ⟨ep, hEp⟩ := hEp
      rw [hEqK, hEp] at hPre
      exact absurd hPre (by simp)
    have h1 : st1.objects[k]? = st.objects[k]? :=
      endpointQueueRemove_objects_ne epId isRecvQ tid st st1 tcb hInv hTcb hRem k
        hkEp hkTid hkPrev hkNext
    have hInv1 : st1.objects.invExt :=
      endpointQueueRemove_preserves_objects_invExt _ _ _ _ _ hInv hRem
    cases hLook : lookupTcb st1 tid with
    | none => rw [hLook] at hStep; exact absurd hStep (by simp)
    | some tcb1 =>
      rw [hLook] at hStep
      simp only [] at hStep
      cases hStore : storeObject tid.toObjId (.tcb _) st1 with
      | error e => rw [hStore] at hStep; exact absurd hStep (by simp)
      | ok pr =>
        rw [hStore] at hStep
        simp only [Except.ok.injEq] at hStep
        subst hStep
        rw [storeObject_objects_ne st1 pr.2 _ k _ hkTid hInv1 (by rw [← hStore]),
          h1, hPre]

/-- **WS-OD OD3.5**: and so the reclaim's abort prefix leaves every TCB but the
holder and its two queue neighbours verbatim. -/
theorem abortHolderPendingIpc_other_tcb_eq (st : SystemState)
    (holder : SeLe4n.ThreadId) (holderTcb : TCB)
    (hInv : st.objects.invExt)
    (hLook : lookupTcb st holder = some holderTcb)
    (k : SeLe4n.ObjId) (t0 : TCB)
    (hkHolder : k ≠ holder.toObjId)
    (hkPrev : ∀ p, holderTcb.queuePrev = some p → k ≠ p.toObjId)
    (hkNext : ∀ n, holderTcb.queueNext = some n → k ≠ n.toObjId)
    (hPre : st.objects[k]? = some (.tcb t0)) :
    (Lifecycle.Suspend.abortHolderPendingIpc st holder).objects[k]? = some (.tcb t0) := by
  unfold Lifecycle.Suspend.abortHolderPendingIpc
  rw [hLook]
  simp only []
  cases hIp : holderTcb.ipcState with
  | ready | blockedOnReceive _ | blockedOnReply _ _ | blockedOnNotification _ =>
    exact hPre
  | blockedOnSend epId | blockedOnCall epId =>
    simp only []
    cases hAb : abortPendingIpcOnEndpoint epId false holder st with
    | error e => exact hPre
    | ok st' =>
      exact abortPendingIpcOnEndpoint_other_tcb_eq epId false holder st st' holderTcb
        hInv hLook hAb k t0 hkHolder hkPrev hkNext hPre

/-- **WS-OD OD3.5: the reply arm writes no TCB the footprint does not name** —
the general form, with the reclaim live.

`cancelIpcBlocking_replyArm_noDonation_tcb_frame` above covers the shape where
the reclaim is inert.  With a donation resolved the arm additionally runs
`returnDonationToCancelledCaller`, which is the OD1.4 abort prefix followed by
the OD3 pop, and between them they rewrite exactly four TCBs: the holder and its
two queue neighbours (the abort's splice), and the two threads the pop rebinds —
the holder again, and the cancelled caller.  Every one of those four is a
declared member of `lockSet_cancelIpcBlockingOnCore`
(`cancelHolderSpliceNeighbors?`, the donation holder, the victim), which is what
licenses the arm-selected footprint to declare no *victim* splice neighbour on
this arm: the victim's own `queuePrev` / `queueNext` are stale links to threads
this arm never touches.

Stated with the holder's neighbours quantified over the holder's TCB fields
rather than over two supplied threads, so the hypotheses are discharged from the
same resolution the footprint reads. -/
theorem cancelIpcBlocking_replyArm_tcb_frame (st : SystemState)
    (v : SeLe4n.ThreadId) (tcbV : TCB) (ep : SeLe4n.ObjId)
    (rt : Option SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (holder : SeLe4n.ThreadId) (holderTcb : TCB)
    (hInv : st.objects.invExt)
    (hBlocked : tcbV.ipcState = .blockedOnReply ep rt)
    (hDon : Lifecycle.Suspend.cancelledCallerDonation? st v tcbV = some (scId, holder))
    (hHolder : lookupTcb st holder = some holderTcb)
    (k : SeLe4n.ObjId) (t0 : TCB)
    (hkV : k ≠ v.toObjId) (hkHolder : k ≠ holder.toObjId)
    (hkPrev : ∀ p, holderTcb.queuePrev = some p → k ≠ p.toObjId)
    (hkNext : ∀ n, holderTcb.queueNext = some n → k ≠ n.toObjId)
    (hPre : st.objects[k]? = some (.tcb t0)) :
    (Lifecycle.Suspend.cancelIpcBlocking st v tcbV).objects[k]? = some (.tcb t0) := by
  have hArm : Lifecycle.Suspend.cancelIpcBlocking st v tcbV =
      Lifecycle.Suspend.consumeReplyLink
        (Lifecycle.Suspend.restoreToReadyCancelled
          (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) v) v tcbV := by
    unfold Lifecycle.Suspend.cancelIpcBlocking
    rw [hBlocked]
  rw [hArm]
  -- Stage 1: the reclaim — the abort's splice, then the pop's two rebinds.
  have hReclaim :
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV).objects[k]?
        = some (.tcb t0) := by
    unfold Lifecycle.Suspend.returnDonationToCancelledCaller
    rw [hDon]
    cases hVGet : st.getTcb? v with
    | none => simp only []; exact hPre
    | some _ =>
      simp only []
      have hAbort : (Lifecycle.Suspend.abortHolderPendingIpc st holder).objects[k]?
          = some (.tcb t0) :=
        abortHolderPendingIpc_other_tcb_eq st holder holderTcb hInv hHolder k t0
          hkHolder hkPrev hkNext hPre
      have hInvA : (Lifecycle.Suspend.abortHolderPendingIpc st holder).objects.invExt :=
        Lifecycle.Suspend.abortHolderPendingIpc_preserves_objects_invExt st holder hInv
      cases hRet : returnDonatedSchedContext
          (Lifecycle.Suspend.abortHolderPendingIpc st holder) holder scId v none with
      | error e => exact hPre
      | ok stRet =>
        exact returnDonatedSchedContext_other_tcb_eq _ stRet holder scId v none hInvA hRet
          k t0 hkV hkHolder hAbort
  -- Stage 2: the restore writes the victim alone; stage 3: the reply consume
  -- writes the victim's TCB and a Reply object.
  have hInvR : (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV).objects.invExt :=
    Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt st v tcbV hInv
  refine consumeReplyLink_other_tcb_eq _ v tcbV
    (Lifecycle.Suspend.restoreToReadyCancelled_invExt _ v hInvR) k t0 hkV ?_
  show (Lifecycle.Suspend.restoreToReadyStaging
    (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) v _).objects[k]?
      = some (.tcb t0)
  rw [restoreToReadyStaging_objects_ne _ v _ k hInvR hkV]
  exact hReclaim

end SeLe4n.Kernel
