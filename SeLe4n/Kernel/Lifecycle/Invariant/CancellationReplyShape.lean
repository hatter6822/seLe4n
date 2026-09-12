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

/-- **WS-OD OD4.4: the outer-caller obligation for the cancellation reclaim.**

The reclaim resolves its scheduling context from the *holder's* binding rather
than taking it as an argument, and it pops at the **post-abort** state -- so the
obligation is stated over the victim: whatever donation the cancellation is
reclaiming, the outer caller its reply stack names is a proper waiting donor and
is owned by nobody.  Vacuous on every state where that context heads no reply
stack (`cancelDonationStackValid_of_no_stacks`) — which was every state this tree
reached until OD4.1 (`v0.35.2`), and is now every state below the first donating
`Call`.

Stated in the cancellation's own shape rather than at a resolved `(scId, holder)`
pair, for the reason `cleanupDonationStackValid` is: a consumer holds the victim
and its TCB, never the donation the arm is about to discover. -/
def cancelDonationStackValid (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB) : Prop :=
  ∀ (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId),
    Lifecycle.Suspend.cancelledCallerDonation? st v tcbV = some (scId, holder) →
    replyStackOuterCallerValid (Lifecycle.Suspend.abortHolderPendingIpc st holder) scId holder v

/-- `v0.35.4`: the cancelled caller's frame detach writes at most one Reply, so
every binding reads through unchanged. -/
theorem detachFrameAboveThreadReply_sameSchedContextBindings (st : SystemState) (tcb : TCB)
    (hInv : st.objects.invExt) :
    sameSchedContextBindings st (detachFrameAboveThreadReply st tcb) :=
  fun t tcb' hPost =>
    ⟨tcb', detachFrameAboveThreadReply_tcb_backward st tcb hInv t.toObjId tcb'
      hPost, rfl⟩

/-- WS-OD OD4.4: the reclaim's outer-caller obligation is discharged outright on
a store where no scheduling context heads a reply stack -- the shape of every
state the tree reached before OD4.1 (`v0.35.2`), which is why threading the
resolver was a refactor rather than a behaviour change. -/
theorem cancelDonationStackValid_of_no_stacks (st : SystemState)
    (v : SeLe4n.ThreadId) (tcbV : TCB)
    (hNoHeads : ∀ (holder : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
      (sc : SeLe4n.Kernel.SchedContext),
      (Lifecycle.Suspend.abortHolderPendingIpc st holder).getSchedContext? scId = some sc →
      sc.scReply = none) :
    cancelDonationStackValid st v tcbV :=
  fun scId holder _ =>
    replyStackOuterCallerValid_of_no_stacks _ (hNoHeads holder) scId holder v

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
    -- **WS-OD OD4.4**: the reclaim's pop resolves its new owner from the context's
    -- own reply stack; this is the obligation that resolution carries, and it is
    -- what keeps the pop from *refusing* -- a refused reclaim leaves exactly the
    -- donation this result denies.
    (hStack : cancelDonationStackValid st v tcbV)
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
    -- **WS-OD OD4.4**: the pop resolves its new owner off the context's own reply
    -- stack, at the post-abort state.  The chain invariant carries across the
    -- abort (`abortHolderPendingIpc_donationChainFrame`), so the resolver
    -- *answers*; what it answers is the caller's obligation.
    have hChainA : donationChainWellFormed (Lifecycle.Suspend.abortHolderPendingIpc st holder) :=
      donationChainWellFormed_of_frame
        (Lifecycle.Suspend.abortHolderPendingIpc_donationChainFrame st holder hInv) hChain
    obtain ⟨scA, hScA, _⟩ :=
      (hOwnerA holder holderTcbA scId0 v hHolderAtA (hBindEqA.trans hBindH)).1
    obtain ⟨n, hResN⟩ :=
      replyStackOuterCallerResolves_of_chainWellFormed _ scId0 hChainA scA hScA
    obtain ⟨st', hOk⟩ := returnDonatedSchedContext_ok_under_invariants
      (Lifecycle.Suspend.abortHolderPendingIpc st holder) holder holderTcbA
      scId0 v hInvA hOwnerA hHeadResA hLkHA (hBindEqA.trans hBindH)
      (lookupTcb_some_not_reserved st holder holderTcb hLkH)
      (lookupTcb_some_not_reserved st v tcbV hLookup) n
      ((hStack scId0 holder hRes) n hResN).1
    rw [returnDonatedSchedContextResolved_of_resolved hResN, hOk] at hTcb
    simp only at hTcb
    obtain ⟨hSrv, hOwn, hOther⟩ := returnDonatedSchedContext_tcb_schedContextBinding_backward
      (Lifecycle.Suspend.abortHolderPendingIpc st holder) st' holder scId0 v hInvA n hOk
      tid.toObjId tcb hTcb
    by_cases hH : tid.toObjId = holder.toObjId
    · rw [hSrv hH] at hBind; cases hBind
    · by_cases hV : tid.toObjId = v.toObjId
      · -- At the bottom of the stack the target is rebound `.bound`, and one level
        -- up `.donated scId0 outer` -- where `outerCallerAcceptable` has already
        -- decided `outer ≠ v` (`outerNeTarget`), so neither arm is a donation
        -- naming the cancelled caller.
        rw [hOwn hH hV] at hBind
        cases hN : n with
        | none => rw [hN] at hBind; cases hBind
        | some outer =>
            rw [hN] at hBind
            simp only [donationReturnBinding, SchedContextBinding.donated.injEq] at hBind
            exact absurd hBind.2
              (((hStack scId0 holder hRes) n hResN).1
                |> fun hAcc => by
                    rw [hN] at hAcc
                    exact (outerCallerAcceptable_some_char _ holder v outer hAcc).1)
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
      have hx : (st.objects.insert rid.toObjId (.reply r.consumed)).get?
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
      have hx : (st.objects.insert rid.toObjId (.reply r.consumed)).get?
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

/-- `v0.35.4`: the cancelled caller's frame detach frames `passiveServerIdle` —
its one write lands on a `.reply` value, whose key can never hold a TCB, and it
touches no scheduler slot. -/
theorem detachFrameAboveThreadReply_passiveServerIdleFrame (st : SystemState) (tcb : TCB)
    (hInv : st.objects.invExt) :
    passiveServerIdleFrame st (detachFrameAboveThreadReply st tcb) :=
  passiveServerIdleFrame_of_backward
    (fun t tcb' hPost =>
      ⟨tcb', detachFrameAboveThreadReply_tcb_backward st tcb hInv t.toObjId tcb'
        hPost, rfl, rfl⟩)
    (detachFrameAboveThreadReply_scheduler_eq st tcb)

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
      obtain ⟨n, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hOk
      refine (Lifecycle.Suspend.abortHolderPendingIpc_passiveServerIdleFrame st holder hInv).trans
        (returnDonatedSchedContext_passiveServerIdleFrame
          (Lifecycle.Suspend.abortHolderPendingIpc_preserves_objects_invExt st holder hInv)
          n hPop ?_)
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
            (detachFrameAboveThreadReply
              (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV) v) v tcbV by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hIp]]
    have hF1 := returnDonationToCancelledCaller_passiveServerIdleFrame st v tcbV hInv hMem
    have hI1 := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt
      st v tcbV hInv
    -- `v0.35.4`: the frame detach writes at most a Reply, which frames the conjunct.
    have hFD := detachFrameAboveThreadReply_passiveServerIdleFrame
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV hI1
    have hID := detachFrameAboveThreadReply_preserves_objects_invExt
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV hI1
    have hF2 := restoreToReadyStaging_passiveServerIdleFrame
      (detachFrameAboveThreadReply
        (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV) v
      (some Architecture.cancelledIpcFrame) hID
    have hI2 := Lifecycle.Suspend.restoreToReadyCancelled_invExt
      (detachFrameAboveThreadReply
        (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV) v hID
    have hF3 := consumeReplyLink_passiveServerIdleFrame
      (Lifecycle.Suspend.restoreToReadyCancelled
        (detachFrameAboveThreadReply
          (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV) v) v tcbV hI2
    exact ((hF1.trans hFD).trans hF2).trans hF3

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
    -- **WS-OD OD4.4**: see `returnDonationToCancelledCaller_no_donation_to_victim`.
    (hStack : cancelDonationStackValid st v tcbV)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (hTcb : (Lifecycle.Suspend.cancelIpcBlocking st v tcbV).objects[tid.toObjId]?
      = some (.tcb tcb)) :
    tcb.schedContextBinding ≠ .donated scId v := by
  have hArm : Lifecycle.Suspend.cancelIpcBlocking st v tcbV =
      Lifecycle.Suspend.consumeReplyLink
        (Lifecycle.Suspend.restoreToReadyCancelled
          (detachFrameAboveThreadReply
            (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV) v) v tcbV := by
    unfold Lifecycle.Suspend.cancelIpcBlocking
    rw [hBlocked]
  rw [hArm] at hTcb
  have hInvR := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt st v tcbV hInv
  have hInvD := detachFrameAboveThreadReply_preserves_objects_invExt _ tcbV hInvR
  have hInvS := Lifecycle.Suspend.restoreToReadyCancelled_invExt _ v hInvD
  have hSame :
      sameSchedContextBindings (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV)
        (Lifecycle.Suspend.consumeReplyLink
          (Lifecycle.Suspend.restoreToReadyCancelled
            (detachFrameAboveThreadReply
              (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV) v) v tcbV) :=
    ((detachFrameAboveThreadReply_sameSchedContextBindings _ tcbV hInvR).trans
      (restoreToReadyStaging_sameSchedContextBindings _ v _ hInvD)).trans
      (consumeReplyLink_sameSchedContextBindings _ v tcbV hInvS)
  obtain ⟨t0, h0, hEqB⟩ := hSame tid tcb hTcb
  intro hBind
  exact returnDonationToCancelledCaller_no_donation_to_victim st v tcbV hInv hLookup hOwner
    hChain hHolder hStack tid t0 scId h0 (by rw [hEqB]; exact hBind)

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
        (Lifecycle.Suspend.restoreToReadyCancelled
          (detachFrameAboveThreadReply st tcbV) v) v tcbV := by
    unfold Lifecycle.Suspend.cancelIpcBlocking
    rw [hBlocked, Lifecycle.Suspend.returnDonationToCancelledCaller_none st v tcbV hNoDonation]
  rw [hArm]
  -- `v0.35.4`: the frame detach writes at most a Reply, so every TCB is untouched.
  have hInvD := detachFrameAboveThreadReply_preserves_objects_invExt st tcbV hInv
  refine consumeReplyLink_other_tcb_eq _ v tcbV
    (Lifecycle.Suspend.restoreToReadyCancelled_invExt _ v hInvD) k t0 hNe ?_
  show (Lifecycle.Suspend.restoreToReadyStaging
    (detachFrameAboveThreadReply st tcbV) v _).objects[k]? = some (.tcb t0)
  rw [restoreToReadyStaging_objects_ne _ v _ k hInvD hNe]
  exact detachFrameAboveThreadReply_tcb_eq st tcbV hInv k t0 hPre

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
    simp only [endpointQueueRemove, hObj, SystemState.getObject?] at hStep
    exact absurd hStep (by simp)
  | some obj =>
    cases obj with
    | endpoint ep =>
      exact ⟨ep, (SystemState.getEndpoint?_eq_some_iff st endpointId ep).mpr hObj⟩
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
      simp only [endpointQueueRemove, hObj, SystemState.getObject?] at hStep
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
  unfold endpointQueueRemove SystemState.getObject?
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
        unfold endpointQueueRemove SystemState.getObject? at hRem
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
          (detachFrameAboveThreadReply
            (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV) v) v tcbV := by
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
      cases hRet : returnDonatedSchedContextResolved
          (Lifecycle.Suspend.abortHolderPendingIpc st holder) holder scId v with
      | error e => exact hPre
      | ok stRet =>
        obtain ⟨n, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
        exact returnDonatedSchedContext_other_tcb_eq _ stRet holder scId v n hInvA hPop
          k t0 hkV hkHolder hAbort
  -- Stage 2: the restore writes the victim alone; stage 3: the reply consume
  -- writes the victim's TCB and a Reply object.
  have hInvR : (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV).objects.invExt :=
    Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt st v tcbV hInv
  -- `v0.35.4`: the frame detach between the reclaim and the restore writes at
  -- most a Reply, so the TCB reads through it.
  have hDetach : (detachFrameAboveThreadReply
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV).objects[k]?
        = some (.tcb t0) :=
    detachFrameAboveThreadReply_tcb_eq _ tcbV hInvR k t0 hReclaim
  have hInvD := detachFrameAboveThreadReply_preserves_objects_invExt _ tcbV hInvR
  refine consumeReplyLink_other_tcb_eq _ v tcbV
    (Lifecycle.Suspend.restoreToReadyCancelled_invExt _ v hInvD) k t0 hkV ?_
  show (Lifecycle.Suspend.restoreToReadyStaging
    (detachFrameAboveThreadReply
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV) v _).objects[k]?
      = some (.tcb t0)
  rw [restoreToReadyStaging_objects_ne _ v _ k hInvD hkV]
  exact hDetach

-- ============================================================================
-- WS-OD OD5.2 — `.tcbSuspend` of a caller, at every chain depth
-- ============================================================================

/-- **WS-OD OD5.2: the cancelled caller gets its scheduling context back exactly
when it is the immediate donor to the thread holding it.**

The reclaim resolves through the victim's own recorded reply target and accepts
the donation only when that thread's binding names the victim as its `owner` --
which, because a push always records the *immediate* donor, is precisely the
depth-1-below-the-victim case.  So on a chain `D → C → S`, cancelling `C`
returns the context to `C` (and OD4.4's resolver then rebinds it
`.donated sc D`, since the stack still names `D` below `C`'s frame).

Stated so the *positive* half of the policy is visible beside the negative one
below: `severAtCut` is not "a cancelled caller never gets its context back", it
is "a cancelled caller gets back exactly the donation it made". -/
theorem cancelledCallerDonation?_some_of_immediate_donee
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (ep : SeLe4n.ObjId) (holder : SeLe4n.ThreadId) (holderTcb : TCB)
    (scId : SeLe4n.SchedContextId)
    (hIpc : tcb.ipcState = .blockedOnReply ep (some holder))
    (hLk : lookupTcb st holder = some holderTcb)
    (hBind : holderTcb.schedContextBinding = .donated scId tid) :
    Lifecycle.Suspend.cancelledCallerDonation? st tid tcb = some (scId, holder) := by
  unfold Lifecycle.Suspend.cancelledCallerDonation?
  rw [hIpc]
  simp only []
  rw [hLk]
  simp only []
  rw [hBind]
  simp only [beq_self_eq_true, if_true]

/-- **WS-OD OD5.2: below the cut the reclaim declines, and that is the policy.**

At call depth ≥ 3 the victim's recorded reply target has already donated the
context onward, so its own binding is `.unbound` and names nobody: the reclaim
answers `none` and `returnDonationToCancelledCaller` is the identity.  The
context stays where it is, and the pop that later reaches the victim's now
caller-less frame binds the innermost live caller `.bound scId`
(`cancelledMiddleCaller_severs_at_cut`).

This is `severAtCut` seen from the cancellation end, and it is a decision rather
than an omission: `reclaimToCancelledThread` would reach the real holder through
`SchedContext.boundThread` and rewrite a binding this theorem says is untouched.
Its cost is stated at `cancelledMiddleCallerPolicy` -- the original owner's
reservation ends up with the innermost live caller. -/
theorem cancelledCallerDonation?_none_below_the_cut
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (ep : SeLe4n.ObjId) (holder : SeLe4n.ThreadId) (holderTcb : TCB)
    (hIpc : tcb.ipcState = .blockedOnReply ep (some holder))
    (hLk : lookupTcb st holder = some holderTcb)
    (hDonatedOnward : holderTcb.schedContextBinding = .unbound) :
    cancelledMiddleCallerPolicy = CancelledMiddleCallerPolicy.severAtCut ∧
    Lifecycle.Suspend.cancelledCallerDonation? st tid tcb = none ∧
    Lifecycle.Suspend.returnDonationToCancelledCaller st tid tcb = st := by
  have hNone : Lifecycle.Suspend.cancelledCallerDonation? st tid tcb = none := by
    unfold Lifecycle.Suspend.cancelledCallerDonation?
    rw [hIpc]
    simp only []
    rw [hLk]
    simp only []
    rw [hDonatedOnward]
  exact ⟨rfl, hNone, Lifecycle.Suspend.returnDonationToCancelledCaller_none st tid tcb hNone⟩

/-- **WS-OD OD5.2 / `v0.35.4`: and the whole cancellation arm reclaims nothing
there.**

The payoff for `.tcbSuspend`: below the cut the reply arm is the teardown -- the
`O(1)` detach of the victim's frame from its stack, the `.ipcCancelled` restore
and the reply-link consume -- with no donation write at all.  So the depth-≥ 3
case needs no binding argument beyond the one the no-donation arm already has,
which is what makes `severAtCut` cheap as well as seL4-shaped; what it does need
is the chain argument, since the detach and the consume both write stack links
(`consumeReplyLink_preserves_donationChainWellFormed`). -/
theorem cancelIpcBlocking_reply_arm_below_the_cut
    (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB)
    (ep : SeLe4n.ObjId) (holder : SeLe4n.ThreadId) (holderTcb : TCB)
    (hIpc : tcbV.ipcState = .blockedOnReply ep (some holder))
    (hLk : lookupTcb st holder = some holderTcb)
    (hDonatedOnward : holderTcb.schedContextBinding = .unbound) :
    Lifecycle.Suspend.cancelIpcBlocking st v tcbV =
      Lifecycle.Suspend.consumeReplyLink
        (Lifecycle.Suspend.restoreToReadyCancelled
          (detachFrameAboveThreadReply st tcbV) v) v tcbV := by
  obtain ⟨_, _, hIdent⟩ :=
    cancelledCallerDonation?_none_below_the_cut st v tcbV ep holder holderTcb hIpc hLk
      hDonatedOnward
  unfold Lifecycle.Suspend.cancelIpcBlocking
  rw [hIpc, hIdent]

-- ============================================================================
-- WS-OD OD5.3 — the reclaim can leave the victim `.donated`
-- ============================================================================

/-- **WS-OD OD5.3: at call depth ≥ 2 the reclaim leaves the victim holding a
donation, which is what makes the suspend pipeline pop a second time.**

`donationReturnBinding scId (some outer)` is `.donated scId outer`, so a victim
that entered `.tcbSuspend` `.unbound` -- a caller whose own context had been
donated onward and reclaimed -- comes out of the G2 teardown `.donated`.  The
pipeline's arm selector re-reads the binding from the **post-teardown** TCB, so
the `.donated` arm then fires and runs a *second* SchedContext teardown with a
*second* replenishment migration, whose destination is `outer`'s home core.

That is the whole reason `suspendThreadOnCoreSchedLockSet`'s replenish segment is
a triple rather than a pair: the third core is not resolvable from the victim's
pre-state binding, because at the pre-state the victim has none. -/
theorem returnDonationToCancelledCaller_leaves_donated_at_depth_two
    (st st' : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB)
    (scId : SeLe4n.SchedContextId) (holder outer : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hNe : v ≠ holder)
    (hDon : Lifecycle.Suspend.cancelledCallerDonation? st v tcbV = some (scId, holder))
    (hGetV : st.getTcb? v = some tcbV)
    (hRes : replyStackOuterCaller? (Lifecycle.Suspend.abortHolderPendingIpc st holder) scId
      = .ok (some outer))
    (hPop : returnDonatedSchedContext (Lifecycle.Suspend.abortHolderPendingIpc st holder)
      holder scId v (some outer) = .ok st') :
    Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV = st' ∧
    ∃ vTcb, st'.getTcb? v = some vTcb ∧
      vTcb.schedContextBinding = .donated scId outer := by
  have hResolved :
      returnDonatedSchedContextResolved (Lifecycle.Suspend.abortHolderPendingIpc st holder)
        holder scId v = .ok st' := by
    rw [returnDonatedSchedContextResolved_of_resolved hRes]; exact hPop
  have hEq : Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV = st' := by
    unfold Lifecycle.Suspend.returnDonationToCancelledCaller
    rw [hDon, hGetV]
    simp only []
    rw [hResolved]
  refine ⟨hEq, ?_⟩
  have hInvA := Lifecycle.Suspend.abortHolderPendingIpc_preserves_objects_invExt st holder hObjInv
  obtain ⟨tA, hkA, _⟩ := Lifecycle.Suspend.abortHolderPendingIpc_tcb_lookup st holder hObjInv
    v.toObjId tcbV ((SystemState.getTcb?_eq_some_iff st v tcbV).mp hGetV)
  obtain ⟨t', hk', _⟩ := returnDonatedSchedContext_tcb_rewrite _ st' holder scId v hInvA
    (some outer) hPop v.toObjId tA hkA
  obtain ⟨_, hOwn, _⟩ := returnDonatedSchedContext_tcb_binding_cases _ st' holder scId v
    (some outer) hInvA hPop v.toObjId t' hk'
  refine ⟨t', (SystemState.getTcb?_eq_some_iff st' v t').mpr hk', ?_⟩
  simpa [donationReturnBinding] using
    hOwn (fun hx => hNe (SeLe4n.ThreadId.toObjId_injective v holder hx)) rfl

-- ============================================================================
-- WS-OD OD5.6 — the teardown paths frame the donation chain
-- ============================================================================

/-- **WS-OD OD5.6**: the TCB half of the sever carries no chain data at all. -/
theorem clearTcbReplyObject_donationChainFrame (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    donationChainFrame st (Lifecycle.Suspend.clearTcbReplyObject st tid) := by
  unfold Lifecycle.Suspend.clearTcbReplyObject
  cases hT : st.getTcb? tid with
  | none => simp only []; exact donationChainFrame.refl st
  | some t =>
    simp only []
    exact donationChainFrame_of_objects_insert hInv
      (by rw [(SystemState.getTcb?_eq_some_iff st tid t).mp hT]; rfl)
      (by rw [(SystemState.getTcb?_eq_some_iff st tid t).mp hT]; rfl)
      (fun _ h => by cases h)

/-- `v0.35.4`: the TCB half of the sever leaves every Reply where it was. -/
theorem clearTcbReplyObject_reply_backward (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (k : SeLe4n.ObjId) (r : Reply)
    (h : (Lifecycle.Suspend.clearTcbReplyObject st tid).objects[k]? = some (.reply r)) :
    st.objects[k]? = some (.reply r) := by
  unfold Lifecycle.Suspend.clearTcbReplyObject at h
  cases hT : st.getTcb? tid with
  | none => rw [hT] at h; exact h
  | some t =>
    rw [hT] at h
    by_cases hk : k = tid.toObjId
    · rw [hk] at h
      have hx : (st.objects.insert tid.toObjId (.tcb { t with replyObject := none })).get?
          tid.toObjId = some (.reply r) := h
      rw [RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hInv] at hx
      cases hx
    · have hx : (st.objects.insert tid.toObjId _).get? k = some (.reply r) := h
      rw [RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId k _
        (by simpa using fun h => hk h.symm) hInv] at hx
      exact hx

theorem clearTcbReplyObject_getReply?_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (rid : SeLe4n.ReplyId) :
    (Lifecycle.Suspend.clearTcbReplyObject st tid).getReply? rid = st.getReply? rid := by
  cases hPost : (Lifecycle.Suspend.clearTcbReplyObject st tid).getReply? rid with
  | some r =>
    exact ((SystemState.getReply?_eq_some_iff st rid r).mpr
      (clearTcbReplyObject_reply_backward st tid hInv rid.toObjId r
        ((SystemState.getReply?_eq_some_iff _ rid r).mp hPost))).symm
  | none =>
    cases hPre : st.getReply? rid with
    | none => rfl
    | some r =>
      exfalso
      have hObj := (SystemState.getReply?_eq_some_iff st rid r).mp hPre
      have hPostObj : (Lifecycle.Suspend.clearTcbReplyObject st tid).objects[rid.toObjId]?
          = some (.reply r) := by
        unfold Lifecycle.Suspend.clearTcbReplyObject
        cases hT : st.getTcb? tid with
        | none => exact hObj
        | some t =>
          have hNe : rid.toObjId ≠ tid.toObjId := by
            intro hx; rw [hx, (SystemState.getTcb?_eq_some_iff st tid t).mp hT] at hObj
            cases hObj
          show (st.objects.insert tid.toObjId _).get? rid.toObjId = some (.reply r)
          rw [RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId rid.toObjId _
            (by simpa using fun h => hNe h.symm) hInv]
          exact hObj
      have hSome := (SystemState.getReply?_eq_some_iff _ rid r).mpr hPostObj
      rw [hPost] at hSome
      cases hSome

-- ============================================================================
-- `v0.35.4` — the cancellation's chain writes preserve the chain
-- ============================================================================

/-! With the doubly-linked stack the cancellation's reply arm is a chain
**writer** on two counts, and neither reaches `donationChainWellFormed_of_frame`:

* the `O(1)` detach (`detachReplyFrameAbove`, seL4's `reply_remove_tcb` on a
  non-head frame) clears the `prev` of the frame above the cancelled caller's;
* the reply-link consume (`clearReplyObjectCaller`, storing `Reply.consumed`)
  clears the cancelled caller's own two links unless the frame heads a context.

So each carries a preservation theorem.  The detach needs no hypothesis: it
shortens one stack and repairs the only link that named the frame it cut
(`donationChainWalk_exists_of_agree_or_cut`).  The consume needs two facts about
the frame it clears, both established by the detach that runs first: the frame
heads no context (a head is popped by the reclaim, never consumed in place), and
no frame's `prev` still names it — which is exactly what the detach guarantees
(`detachFrameAboveThreadReply_unreferenced`).  The stale *upward* link the frame
below the cut keeps (`next = .frame victim`) is one the invariant deliberately
does not constrain: nothing trusts an upward link that is not answered from
above, which is what lets the cut be `O(1)`. -/

/-- `v0.35.4`: **the detach preserves the chain invariant** — one Reply store that
clears the `prev` of a frame whose `next` is unchanged, so every reciprocity
clause is either untouched or made vacuous, and the walk from the frame's head
stops at it. -/
theorem detachReplyFrameAbove_preserves_donationChainWellFormed {st st' : SystemState}
    {rid : SeLe4n.ReplyId} (hInv : st.objects.invExt) (hChain : donationChainWellFormed st)
    (h : detachReplyFrameAbove st rid = .ok st') : donationChainWellFormed st' := by
  rcases detachReplyFrameAbove_cases h with rfl | ⟨_, above, a, _, _, hA, _, hS⟩
  · exact hChain
  · have hAObj := (SystemState.getReply?_eq_some_iff _ _ _).mp hA
    have hAbove : st'.objects[above.toObjId]? = some (.reply { a with prev := none }) :=
      storeObject_objects_eq' st _ _ _ hInv hS
    have hOther : ∀ k : SeLe4n.ObjId, k ≠ above.toObjId → st'.objects[k]? = st.objects[k]? :=
      fun k hk => storeObject_objects_ne st st' above.toObjId k _ hk hInv hS
    have hReplyCases : ∀ (q : SeLe4n.ReplyId) (rq : Reply),
        st'.objects[q.toObjId]? = some (.reply rq) →
        (q.toObjId = above.toObjId ∧ rq = { a with prev := none }) ∨
        (q.toObjId ≠ above.toObjId ∧ st.objects[q.toObjId]? = some (.reply rq)) := by
      intro q rq hq
      by_cases hk : q.toObjId = above.toObjId
      · left
        rw [hk, hAbove] at hq
        exact ⟨hk, (KernelObject.reply.inj (Option.some.inj hq)).symm⟩
      · right
        exact ⟨hk, by rw [← hOther q.toObjId hk]; exact hq⟩
    have hScBack : ∀ (c : SeLe4n.SchedContextId) (sc : SchedContext),
        st'.objects[c.toObjId]? = some (.schedContext sc) →
        st.objects[c.toObjId]? = some (.schedContext sc) := by
      intro c sc hc
      have hk : c.toObjId ≠ above.toObjId := by intro hx; rw [hx, hAbove] at hc; cases hc
      rw [← hOther c.toObjId hk]; exact hc
    have hScFwd : ∀ (c : SeLe4n.SchedContextId) (sc : SchedContext),
        st.objects[c.toObjId]? = some (.schedContext sc) →
        st'.objects[c.toObjId]? = some (.schedContext sc) := by
      intro c sc hc
      have hk : c.toObjId ≠ above.toObjId := by intro hx; rw [hx, hAObj] at hc; cases hc
      rw [hOther c.toObjId hk]; exact hc
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro q rq hq
      rcases hReplyCases q rq hq with ⟨_, rfl⟩ | ⟨_, hqPre⟩
      · intro hC
        exact ⟨rfl, (hChain.replyWellFormed above a hAObj hC).2⟩
      · exact hChain.replyWellFormed q rq hqPre
    · intro c sc hc rid' hRid'
      obtain ⟨r', hR', hNext'⟩ := hChain.headLinkReciprocal c sc (hScBack c sc hc) rid' hRid'
      by_cases hk : rid'.toObjId = above.toObjId
      · have hra : r' = a := by
          rw [hk, hAObj] at hR'
          exact (KernelObject.reply.inj (Option.some.inj hR')).symm
        refine ⟨{ a with prev := none }, by rw [hk]; exact hAbove, ?_⟩
        show a.next = some (.head c)
        rw [← hra]; exact hNext'
      · exact ⟨r', by rw [hOther rid'.toObjId hk]; exact hR', hNext'⟩
    · intro rid' r' c hR' hNext'
      rcases hReplyCases rid' r' hR' with ⟨hk, rfl⟩ | ⟨_, hPre⟩
      · obtain ⟨sc, hSc, hHead⟩ := hChain.headLinkResolves above a c hAObj hNext'
        refine ⟨sc, hScFwd c sc hSc, ?_⟩
        rw [SeLe4n.ReplyId.toObjId_injective _ _ hk]
        exact hHead
      · obtain ⟨sc, hSc, hHead⟩ := hChain.headLinkResolves rid' r' c hPre hNext'
        exact ⟨sc, hScFwd c sc hSc, hHead⟩
    · intro rid' r' below hR' hPrev'
      rcases hReplyCases rid' r' hR' with ⟨_, rfl⟩ | ⟨_, hPre⟩
      · simp at hPrev'
      · obtain ⟨b, hB, hBnext⟩ := hChain.prevLinkReciprocal rid' r' below hPre hPrev'
        by_cases hk : below.toObjId = above.toObjId
        · have hba : b = a := by
            rw [hk, hAObj] at hB
            exact (KernelObject.reply.inj (Option.some.inj hB)).symm
          refine ⟨{ a with prev := none }, by rw [hk]; exact hAbove, ?_⟩
          show a.next = some (.frame rid')
          rw [← hba]; exact hBnext
        · exact ⟨b, by rw [hOther below.toObjId hk]; exact hB, hBnext⟩
    · intro c sc hc
      obtain ⟨fuel, chain, hWalk⟩ := hChain.headTerminates c sc (hScBack c sc hc)
      obtain ⟨chain', hWalk'⟩ :=
        donationChainWalk_exists_of_agree_or_cut (st := st) (st' := st') fuel (.head c)
          sc.scReply chain hWalk (by
            intro q hq
            by_cases hk : q.toObjId = above.toObjId
            · right
              exact ⟨a, { a with prev := none }, by rw [hk]; exact hAObj,
                by rw [hk]; exact hAbove, rfl, rfl⟩
            · left
              unfold replyStackLinksAt? SystemState.getObject?
              rw [hOther q.toObjId hk])
      exact ⟨fuel, chain', hWalk'⟩

/-- `v0.35.4`: the cancelled caller's frame detach preserves the chain — the
identity where there is nothing to detach, one `detachReplyFrameAbove` otherwise. -/
theorem detachFrameAboveThreadReply_preserves_donationChainWellFormed (st : SystemState)
    (tcb : TCB) (hInv : st.objects.invExt) (hChain : donationChainWellFormed st) :
    donationChainWellFormed (detachFrameAboveThreadReply st tcb) := by
  rcases detachFrameAboveThreadReply_cases st tcb with h | ⟨_, _, h⟩
  · rw [h]; exact hChain
  · exact detachReplyFrameAbove_preserves_donationChainWellFormed hInv hChain h

/-- `v0.35.6` (WS-RM): **the fold preserves the chain invariant** — the identity
on a refusal, `detachReplyFrameAbove_preserves_donationChainWellFormed` otherwise. -/
theorem detachReplyFrameAboveOrSelf_preserves_donationChainWellFormed (st : SystemState)
    (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt) (hChain : donationChainWellFormed st) :
    donationChainWellFormed (detachReplyFrameAboveOrSelf st rid) := by
  rcases detachReplyFrameAboveOrSelf_cases st rid with h | h
  · rw [h]; exact hChain
  · exact detachReplyFrameAbove_preserves_donationChainWellFormed hInv hChain h

/-- **WS-RM (`v0.35.6`): after the fold, no stored Reply's `prev` names `rid`.**

This is the producer for the consume's `hUnreferenced` obligation, and it is why
the detach must run **before** the consume rather than beside it: `Reply.consumed`
clears a non-head frame's `next`, so a frame still linking down to `rid` would
lose its reciprocity and every later walk would refuse it.

It holds on **all three** arms, which is what licenses folding the refusal to the
identity.  Under `prevLinkReciprocal` the only frame whose `prev` can name `rid`
is the one `rid`'s own `next` names, so: on the writing arm that frame is the one
the store repaired; on the identity arm `rid`'s `next` names no frame at all; and
on a *refusal* — the frame above does not resolve, or does not point back — no
stored Reply satisfies the reciprocity clause for `rid` in the first place, so
there is nothing to repair.  The refusal is therefore not a case the fold papers
over: it is the case in which the repair was already unnecessary. -/
theorem detachReplyFrameAboveOrSelf_unreferenced (st : SystemState)
    (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt) (hChain : donationChainWellFormed st)
    (a : SeLe4n.ReplyId) (ra : Reply)
    (hA : (detachReplyFrameAboveOrSelf st rid).objects[a.toObjId]? = some (.reply ra)) :
    ra.prev ≠ some rid := by
  intro hPrevA
  -- The post-state frame at `a` is a pre-state frame with the same `prev`: the
  -- fold's one write sets a `prev` to `none`, which `hPrevA` is not.
  have hA0 : st.objects[a.toObjId]? = some (.reply ra) := by
    rcases detachReplyFrameAboveOrSelf_cases st rid with h | h
    · rw [h] at hA; exact hA
    · rcases detachReplyFrameAbove_cases h with h' | ⟨_, above, a', _, _, _, _, hS⟩
      · rw [h'] at hA; exact hA
      · by_cases hk : a.toObjId = above.toObjId
        · rw [hk, storeObject_objects_eq' st _ _ _ hInv hS] at hA
          have hEq := KernelObject.reply.inj (Option.some.inj hA)
          rw [← hEq] at hPrevA
          cases hPrevA
        · rw [storeObject_objects_ne st _ above.toObjId a.toObjId _ hk hInv hS] at hA
          exact hA
  -- So in the pre-state `a` names `rid` below it, and `rid` answers with `.frame a`.
  obtain ⟨r, hRObj, hRnext⟩ := hChain.prevLinkReciprocal a ra rid hA0 hPrevA
  -- The detach therefore ran to completion at `a` and cleared its `prev`, so the
  -- fold is that store and not the identity.
  have hGetR : st.getReply? rid = some r := (SystemState.getReply?_eq_some_iff _ _ _).mpr hRObj
  have hGetA : st.getReply? a = some ra := (SystemState.getReply?_eq_some_iff _ _ _).mpr hA0
  obtain ⟨p, hP⟩ : ∃ p, storeObject a.toObjId (.reply { ra with prev := none }) st = .ok p :=
    ⟨_, rfl⟩
  obtain ⟨u, s'⟩ := p
  cases u
  have hDet : detachReplyFrameAbove st rid = .ok s' := by
    unfold detachReplyFrameAbove
    rw [hGetR]
    simp only [hRnext]
    rw [hGetA]
    simp only [hPrevA, bne_self_eq_false, Bool.false_eq_true, if_false]
    rw [hP]
  have hPost : detachReplyFrameAboveOrSelf st rid = s' := by
    unfold detachReplyFrameAboveOrSelf; rw [hDet]
  rw [hPost, storeObject_objects_eq' st _ _ _ hInv hP] at hA
  have hEq := KernelObject.reply.inj (Option.some.inj hA)
  have hPrevEq : ({ ra with prev := none } : Reply).prev = ra.prev := by rw [hEq]
  rw [hPrevA] at hPrevEq
  cases hPrevEq

/-- `v0.35.4`: **after the detach, no frame's `prev` names the cancelled caller's
frame** — the TCB-keyed instance of `detachReplyFrameAboveOrSelf_unreferenced`,
which answers the same question for whichever `ReplyId` the thread holds. -/
theorem detachFrameAboveThreadReply_unreferenced (st : SystemState) (tcb : TCB)
    (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt) (hChain : donationChainWellFormed st)
    (hRid : tcb.replyObject = some rid) (a : SeLe4n.ReplyId) (ra : Reply)
    (hA : (detachFrameAboveThreadReply st tcb).objects[a.toObjId]?
      = some (.reply ra)) :
    ra.prev ≠ some rid := by
  refine detachReplyFrameAboveOrSelf_unreferenced st rid hInv hChain a ra ?_
  rw [show detachReplyFrameAboveOrSelf st rid = detachFrameAboveThreadReply st tcb by
    unfold detachFrameAboveThreadReply; rw [hRid]]
  exact hA

/-- **WS-RM (`v0.35.6`): the object-store effect of consuming a reply link
preserves the chain**, when the frame heads no context and no frame's `prev`
names it — the two facts a detach run beforehand establishes.

Stated over the *store effect* (`hAt` / `hOther`) rather than over an operation,
because the tree spells that effect twice — `consumeReply` on the reply path and
`clearReplyObjectCaller` on the cancellation path — and a chain argument written
against one of them would have to be written again for the other.  Both cite this.

The consumed frame leaves the structure with both links clear, every other object
is untouched, and the frame was on no walk to begin with
(`donationChainWalk_mem_prev`). -/
theorem consumedReplyStore_preserves_donationChainWellFormed (st s' : SystemState)
    (rid : SeLe4n.ReplyId) (r : Reply)
    (hChain : donationChainWellFormed st)
    (hR : st.getReply? rid = some r)
    (hNotHead : ∀ sc : SeLe4n.SchedContextId, r.next ≠ some (.head sc))
    (hUnreferenced : ∀ (a : SeLe4n.ReplyId) (ra : Reply),
      st.objects[a.toObjId]? = some (.reply ra) → ra.prev ≠ some rid)
    (hAt : s'.objects[rid.toObjId]? = some (.reply r.consumed))
    (hOther : ∀ k : SeLe4n.ObjId, k ≠ rid.toObjId → s'.objects[k]? = st.objects[k]?) :
    donationChainWellFormed s' := by
  have hRObj := (SystemState.getReply?_eq_some_iff _ _ _).mp hR
  have hCons := Reply.consumed_of_not_head r hNotHead
  have hConsPrev : r.consumed.prev = none := by rw [hCons]
  have hConsNext : r.consumed.next = none := by rw [hCons]
  have hReplyCases : ∀ (q : SeLe4n.ReplyId) (rq : Reply),
      s'.objects[q.toObjId]? = some (.reply rq) →
      (q = rid ∧ rq = r.consumed) ∨ (q ≠ rid ∧ st.objects[q.toObjId]? = some (.reply rq)) := by
    intro q rq hq
    by_cases hk : q.toObjId = rid.toObjId
    · left
      refine ⟨SeLe4n.ReplyId.toObjId_injective q rid hk, ?_⟩
      rw [hk, hAt] at hq
      exact (KernelObject.reply.inj (Option.some.inj hq)).symm
    · right
      exact ⟨fun hx => hk (by rw [hx]), by rw [← hOther q.toObjId hk]; exact hq⟩
  have hScBack : ∀ (c : SeLe4n.SchedContextId) (sc : SchedContext),
      s'.objects[c.toObjId]? = some (.schedContext sc) →
      st.objects[c.toObjId]? = some (.schedContext sc) := by
    intro c sc hc
    have hk : c.toObjId ≠ rid.toObjId := by intro hx; rw [hx, hAt] at hc; cases hc
    rw [← hOther c.toObjId hk]; exact hc
  have hScFwd : ∀ (c : SeLe4n.SchedContextId) (sc : SchedContext),
      st.objects[c.toObjId]? = some (.schedContext sc) →
      s'.objects[c.toObjId]? = some (.schedContext sc) := by
    intro c sc hc
    have hk : c.toObjId ≠ rid.toObjId := by intro hx; rw [hx, hRObj] at hc; cases hc
    rw [hOther c.toObjId hk]; exact hc
  have hReplyFwd : ∀ (q : SeLe4n.ReplyId) (rq : Reply), q ≠ rid →
      st.objects[q.toObjId]? = some (.reply rq) → s'.objects[q.toObjId]? = some (.reply rq) := by
    intro q rq h1 hq
    rw [hOther q.toObjId (fun hx => h1 (SeLe4n.ReplyId.toObjId_injective q rid hx))]
    exact hq
  -- The frame at `rid` heads no context: a context whose head it was would make
  -- its `next` a `.head`, which `hNotHead` refuses.
  have hRidNotHeadOf : ∀ (c : SeLe4n.SchedContextId) (sc : SchedContext),
      st.objects[c.toObjId]? = some (.schedContext sc) → sc.scReply ≠ some rid := by
    intro c sc hc hEq
    obtain ⟨r', hR', hNext'⟩ := hChain.headLinkReciprocal c sc hc rid hEq
    have hr' : r' = r := KernelObject.reply.inj (Option.some.inj (hR'.symm.trans hRObj))
    rw [hr'] at hNext'
    exact hNotHead c hNext'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q rq hq
    rcases hReplyCases q rq hq with ⟨_, rfl⟩ | ⟨_, hqPre⟩
    · intro _; exact ⟨hConsPrev, hConsNext⟩
    · exact hChain.replyWellFormed q rq hqPre
  · intro c sc hc rid' hRid'
    have hcPre := hScBack c sc hc
    obtain ⟨r', hR', hNext'⟩ := hChain.headLinkReciprocal c sc hcPre rid' hRid'
    have hNe : rid' ≠ rid := by
      intro hx; rw [hx] at hRid'; exact hRidNotHeadOf c sc hcPre hRid'
    exact ⟨r', hReplyFwd rid' r' hNe hR', hNext'⟩
  · intro rid' r' c hR' hNext'
    rcases hReplyCases rid' r' hR' with ⟨_, rfl⟩ | ⟨_, hPre⟩
    · rw [hConsNext] at hNext'; cases hNext'
    · obtain ⟨sc, hSc, hHead⟩ := hChain.headLinkResolves rid' r' c hPre hNext'
      exact ⟨sc, hScFwd c sc hSc, hHead⟩
  · intro rid' r' below hR' hPrev'
    rcases hReplyCases rid' r' hR' with ⟨_, rfl⟩ | ⟨_, hPre⟩
    · rw [hConsPrev] at hPrev'; cases hPrev'
    · obtain ⟨b, hB, hBnext⟩ := hChain.prevLinkReciprocal rid' r' below hPre hPrev'
      have hNeB : below ≠ rid := fun hx => hUnreferenced rid' r' hPre (hx ▸ hPrev')
      exact ⟨b, hReplyFwd below b hNeB hB, hBnext⟩
  · intro c sc hc
    have hcPre := hScBack c sc hc
    obtain ⟨fuel, chain, hWalk⟩ := hChain.headTerminates c sc hcPre
    refine ⟨fuel, chain, ?_⟩
    have hRidNotIn : rid ∉ chain := by
      intro hMem
      rcases donationChainWalk_mem_prev st fuel (.head c) sc.scReply chain hWalk rid hMem with
        hEq | ⟨p, rp, _, hRp, hPrevP⟩
      · exact hRidNotHeadOf c sc hcPre hEq
      · exact hUnreferenced p rp hRp hPrevP
    exact donationChainFrom_congr_on_chain c fuel sc.scReply chain hWalk (by
      intro q hq
      have hqNe : q ≠ rid := fun hx => hRidNotIn (hx ▸ hq)
      obtain ⟨rq, hrq, _⟩ := donationChainFrom_mem st c fuel sc.scReply chain hWalk q hq
      unfold replyStackLinksAt? SystemState.getObject?
      rw [hReplyFwd q rq hqNe hrq, hrq])

/-- `v0.35.4`: **consuming a reply link preserves the chain** when the frame heads
no context and no frame's `prev` names it — the cancellation spelling's instance
of `consumedReplyStore_preserves_donationChainWellFormed`. -/
theorem clearReplyObjectCaller_preserves_donationChainWellFormed (st : SystemState)
    (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt) (hChain : donationChainWellFormed st)
    (hNotHead : ∀ (r : Reply) (sc : SeLe4n.SchedContextId),
      st.getReply? rid = some r → r.next ≠ some (.head sc))
    (hUnreferenced : ∀ (a : SeLe4n.ReplyId) (ra : Reply),
      st.objects[a.toObjId]? = some (.reply ra) → ra.prev ≠ some rid) :
    donationChainWellFormed (Lifecycle.Suspend.clearReplyObjectCaller st rid) := by
  unfold Lifecycle.Suspend.clearReplyObjectCaller
  cases hR : st.getReply? rid with
  | none => simp only []; exact hChain
  | some r =>
    simp only []
    refine consumedReplyStore_preserves_donationChainWellFormed st _ rid r hChain hR
      (fun sc => hNotHead r sc hR) hUnreferenced
      (RobinHood.RHTable.getElem?_insert_self st.objects rid.toObjId _ hInv)
      (fun k hk => RobinHood.RHTable.getElem?_insert_ne st.objects rid.toObjId k _
        (by simpa using fun h => hk h.symm) hInv)

/-- **WS-RM (`v0.35.6`): the reply path's spelling preserves the chain** — the
same instance, for the store `consumeReply` performs.  `consumeCallerReply`'s
other write is the answered caller's TCB, which moves no chain data at all. -/
theorem consumeCallerReply_preserves_donationChainWellFormed (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt)
    (hChain : donationChainWellFormed st)
    (hNotHead : ∀ (r : Reply) (sc : SeLe4n.SchedContextId),
      st.getReply? rid = some r → r.next ≠ some (.head sc))
    (hUnreferenced : ∀ (a : SeLe4n.ReplyId) (ra : Reply),
      st.objects[a.toObjId]? = some (.reply ra) → ra.prev ≠ some rid)
    (hStep : SystemState.consumeCallerReply caller rid st = .ok ((), st')) :
    donationChainWellFormed st' := by
  unfold SystemState.consumeCallerReply at hStep
  cases hCons : SystemState.consumeReply rid st with
  | error e => simp [hCons] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hCons] at hStep
    have hInv1 : st1.objects.invExt :=
      SystemState.consumeReply_preserves_objects_invExt st st1 rid hInv hCons
    -- The Reply leg: the store the chain argument above is stated over.
    have hChain1 : donationChainWellFormed st1 := by
      unfold SystemState.consumeReply at hCons
      cases hR : st.getReply? rid with
      | none =>
        simp only [hR, Except.ok.injEq, Prod.mk.injEq, true_and] at hCons
        rw [← hCons]; exact hChain
      | some r =>
        simp only [hR] at hCons
        exact consumedReplyStore_preserves_donationChainWellFormed st st1 rid r hChain hR
          (fun sc => hNotHead r sc hR) hUnreferenced
          (storeObject_objects_eq' st _ _ _ hInv hCons)
          (fun k hk => storeObject_objects_ne st st1 rid.toObjId k _ hk hInv hCons)
    -- The TCB leg: a `replyObject := none` store, which writes no chain data.
    cases hT : st1.getTcb? caller with
    | none =>
      simp only [hT, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      rw [← hStep]; exact hChain1
    | some tcb =>
      simp only [hT] at hStep
      exact donationChainWellFormed_of_frame
        (donationChainFrame_of_tcb_rewrite hInv1
          ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hStep) hChain1

/-- `v0.35.4`: **the cancellation's reply-link sever preserves the donation
chain**, under the two facts the detach that precedes it establishes about the
victim's frame.  The TCB half frames the chain outright; the Reply half is
`clearReplyObjectCaller_preserves_donationChainWellFormed`, with both facts
carried across the TCB write (which moves no Reply). -/
theorem consumeReplyLink_preserves_donationChainWellFormed (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hInv : st.objects.invExt)
    (hChain : donationChainWellFormed st)
    (hNotHead : ∀ (rid : SeLe4n.ReplyId) (r : Reply) (sc : SeLe4n.SchedContextId),
      tcb.replyObject = some rid → st.getReply? rid = some r → r.next ≠ some (.head sc))
    (hUnreferenced : ∀ (rid a : SeLe4n.ReplyId) (ra : Reply), tcb.replyObject = some rid →
      st.objects[a.toObjId]? = some (.reply ra) → ra.prev ≠ some rid) :
    donationChainWellFormed (Lifecycle.Suspend.consumeReplyLink st tid tcb) := by
  unfold Lifecycle.Suspend.consumeReplyLink
  cases hR : tcb.replyObject with
  | none => simp only []; exact hChain
  | some rid =>
    simp only []
    have hInv1 := Lifecycle.Suspend.clearTcbReplyObject_preserves_objects_invExt st tid hInv
    have hChain1 : donationChainWellFormed (Lifecycle.Suspend.clearTcbReplyObject st tid) :=
      donationChainWellFormed_of_frame (clearTcbReplyObject_donationChainFrame st tid hInv) hChain
    refine clearReplyObjectCaller_preserves_donationChainWellFormed _ rid hInv1 hChain1 ?_ ?_
    · intro r sc hR1
      rw [clearTcbReplyObject_getReply?_eq st tid hInv rid] at hR1
      exact hNotHead rid r sc hR hR1
    · intro a ra hA
      exact hUnreferenced rid a ra hR (clearTcbReplyObject_reply_backward st tid hInv _ ra hA)

/-- **WS-RM (`v0.35.6`): consuming a *head* frame's caller link leaves the chain
relaxed at exactly that key.**

`Reply.consumed` keeps a head's links (`Reply.consumed_of_head`), so the stored
record differs from the pre-state one in `caller` alone.  Every clause that reads
a link therefore holds verbatim; `replyWellFormed` is the one that reads `caller`,
and it is relaxed at `rid` and nowhere else.

Stated over the *store effect*, for the same reason its non-head sibling is. -/
theorem consumedHeadReplyStore_preserves_donationChainWellFormedExcept
    (st s' : SystemState) (rid : SeLe4n.ReplyId) (r : Reply) (scId : SeLe4n.SchedContextId)
    (hChain : donationChainWellFormed st)
    (hR : st.getReply? rid = some r)
    (hHead : r.next = some (.head scId))
    (hAt : s'.objects[rid.toObjId]? = some (.reply r.consumed))
    (hOther : ∀ k : SeLe4n.ObjId, k ≠ rid.toObjId → s'.objects[k]? = st.objects[k]?) :
    donationChainWellFormedExcept s' rid := by
  have hRObj := (SystemState.getReply?_eq_some_iff _ _ _).mp hR
  have hCons := Reply.consumed_of_head r scId hHead
  have hConsPrev : r.consumed.prev = r.prev := by rw [hCons]
  have hConsNext : r.consumed.next = r.next := by rw [hCons]
  -- Object readings, in both directions, at the exempt key and elsewhere.
  have hReplyCases : ∀ (q : SeLe4n.ReplyId) (rq : Reply),
      s'.objects[q.toObjId]? = some (.reply rq) →
      (q = rid ∧ rq = r.consumed) ∨ (q ≠ rid ∧ st.objects[q.toObjId]? = some (.reply rq)) := by
    intro q rq hq
    by_cases hk : q.toObjId = rid.toObjId
    · left
      refine ⟨SeLe4n.ReplyId.toObjId_injective q rid hk, ?_⟩
      rw [hk, hAt] at hq
      exact (KernelObject.reply.inj (Option.some.inj hq)).symm
    · right
      exact ⟨fun hx => hk (by rw [hx]), by rw [← hOther q.toObjId hk]; exact hq⟩
  have hReplyFwd : ∀ (q : SeLe4n.ReplyId) (rq : Reply), q ≠ rid →
      st.objects[q.toObjId]? = some (.reply rq) → s'.objects[q.toObjId]? = some (.reply rq) := by
    intro q rq h1 hq
    rw [hOther q.toObjId (fun hx => h1 (SeLe4n.ReplyId.toObjId_injective q rid hx))]
    exact hq
  have hScBack : ∀ (c : SeLe4n.SchedContextId) (sc : SchedContext),
      s'.objects[c.toObjId]? = some (.schedContext sc) →
      st.objects[c.toObjId]? = some (.schedContext sc) := by
    intro c sc hc
    have hk : c.toObjId ≠ rid.toObjId := by intro hx; rw [hx, hAt] at hc; cases hc
    rw [← hOther c.toObjId hk]; exact hc
  have hScFwd : ∀ (c : SeLe4n.SchedContextId) (sc : SchedContext),
      st.objects[c.toObjId]? = some (.schedContext sc) →
      s'.objects[c.toObjId]? = some (.schedContext sc) := by
    intro c sc hc
    have hk : c.toObjId ≠ rid.toObjId := by intro hx; rw [hx, hRObj] at hc; cases hc
    rw [hOther c.toObjId hk]; exact hc
  -- The store is a `caller`-only rewrite at `rid`, so both links agree everywhere.
  have hLinks : ∀ oid : SeLe4n.ObjId,
      replyStackLinks? s'.objects[oid]? = replyStackLinks? st.objects[oid]? := by
    intro oid
    by_cases hk : oid = rid.toObjId
    · rw [hk, hAt, hRObj]
      simp [replyStackLinks?, hConsPrev, hConsNext]
    · rw [hOther oid hk]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q rq hNe hq
    rcases hReplyCases q rq hq with ⟨hEq, _⟩ | ⟨_, hqPre⟩
    · exact absurd hEq hNe
    · exact hChain.replyWellFormed q rq hqPre
  · intro c sc hc q hRid
    obtain ⟨r', hR', hNext'⟩ := hChain.headLinkReciprocal c sc (hScBack c sc hc) q hRid
    by_cases hEq : q = rid
    · subst hEq
      refine ⟨r.consumed, hAt, ?_⟩
      rw [hConsNext]
      have hr' : r' = r := KernelObject.reply.inj (Option.some.inj (hR'.symm.trans hRObj))
      rw [← hr']; exact hNext'
    · exact ⟨r', hReplyFwd q r' hEq hR', hNext'⟩
  · intro q r' c hR' hNext'
    rcases hReplyCases q r' hR' with ⟨hEq, hrq⟩ | ⟨_, hPre⟩
    · subst hEq
      refine hChain.headLinkResolves q r c hRObj ?_ |>.imp fun sc hsc => ⟨hScFwd c sc hsc.1, hsc.2⟩
      rw [← hConsNext, ← hrq]; exact hNext'
    · obtain ⟨sc, hSc, hHeadEq⟩ := hChain.headLinkResolves q r' c hPre hNext'
      exact ⟨sc, hScFwd c sc hSc, hHeadEq⟩
  · intro q r' below hR' hPrev'
    have hPre : ∃ rp, st.objects[q.toObjId]? = some (.reply rp) ∧ rp.prev = r'.prev := by
      rcases hReplyCases q r' hR' with ⟨hEq, hrq⟩ | ⟨_, hPre⟩
      · exact ⟨r, by rw [hEq]; exact hRObj, by rw [hrq, hConsPrev]⟩
      · exact ⟨r', hPre, rfl⟩
    obtain ⟨rp, hrp, hpEq⟩ := hPre
    obtain ⟨b, hB, hBnext⟩ := hChain.prevLinkReciprocal q rp below hrp (by rw [hpEq]; exact hPrev')
    by_cases hEq : below = rid
    · subst hEq
      refine ⟨r.consumed, hAt, ?_⟩
      rw [hConsNext]
      have hb : b = r := KernelObject.reply.inj (Option.some.inj (hB.symm.trans hRObj))
      rw [← hb]; exact hBnext
    · exact ⟨b, hReplyFwd below b hEq hB, hBnext⟩
  · intro c sc hc
    obtain ⟨fuel, chain, hWalk⟩ := hChain.headTerminates c sc (hScBack c sc hc)
    refine ⟨fuel, chain, ?_⟩
    unfold donationChainFrom at hWalk ⊢
    rw [donationChainWalk_congr hLinks]
    exact hWalk

/-- **WS-RM (`v0.35.6`): the reply path's spelling, on a head frame.**  The Reply
leg is the store lemma above; the TCB leg moves no chain data at all, so the
relaxed form is transported by the frame (`donationChainWellFormedExcept_of_frame`)
at the same key. -/
theorem consumeCallerReply_head_preserves_donationChainWellFormedExcept
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (r : Reply) (scId : SeLe4n.SchedContextId) (hInv : st.objects.invExt)
    (hChain : donationChainWellFormed st)
    (hR : st.getReply? rid = some r) (hHead : r.next = some (.head scId))
    (hStep : SystemState.consumeCallerReply caller rid st = .ok ((), st')) :
    donationChainWellFormedExcept st' rid := by
  unfold SystemState.consumeCallerReply at hStep
  cases hCons : SystemState.consumeReply rid st with
  | error e => simp [hCons] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hCons] at hStep
    have hInv1 : st1.objects.invExt :=
      SystemState.consumeReply_preserves_objects_invExt st st1 rid hInv hCons
    have hChain1 : donationChainWellFormedExcept st1 rid := by
      unfold SystemState.consumeReply at hCons
      rw [hR] at hCons
      exact consumedHeadReplyStore_preserves_donationChainWellFormedExcept st st1 rid r scId
        hChain hR hHead (storeObject_objects_eq' st _ _ _ hInv hCons)
        (fun k hk => storeObject_objects_ne st st1 rid.toObjId k _ hk hInv hCons)
    cases hT : st1.getTcb? caller with
    | none =>
      simp only [hT, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      rw [← hStep]; exact hChain1
    | some tcb =>
      simp only [hT] at hStep
      exact donationChainWellFormedExcept_of_frame
        (donationChainFrame_of_tcb_rewrite hInv1
          ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hStep) hChain1

-- ============================================================================
-- WS-RM (`v0.35.6`) — the reply path's removal preserves the chain
-- ============================================================================

/-- **WS-RM (`v0.35.6`): `removeCallerReplyFrame` preserves the chain invariant**
for a frame that heads no context, with **no** side condition beyond `invExt` and
the chain itself.

`hUnreferenced` — the fact the consume needs and cannot establish — is discharged
by the detach that runs first (`detachReplyFrameAboveOrSelf_unreferenced`), on all
three of its arms.  That is the whole reason the removal is a *sequence* rather
than a fold: run the other way round, the consume would clear a non-head frame's
`next` while the frame above still linked down to it, and every later walk to that
frame would refuse (fail-closed) rather than return the context.

`hNotHead` is read on the **pre**-state, which is sound because the detach writes
a `prev` and never a `next`
(`detachReplyFrameAboveOrSelf_reply_next`). -/
theorem removeCallerReplyFrame_preserves_donationChainWellFormed (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt)
    (hChain : donationChainWellFormed st)
    (hNotHead : ∀ (r : Reply) (sc : SeLe4n.SchedContextId),
      st.getReply? rid = some r → r.next ≠ some (.head sc))
    (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    donationChainWellFormed st' := by
  rw [removeCallerReplyFrame_eq] at hStep
  refine consumeCallerReply_preserves_donationChainWellFormed _ st' caller rid
    (detachReplyFrameAboveOrSelf_preserves_objects_invExt st rid hInv)
    (detachReplyFrameAboveOrSelf_preserves_donationChainWellFormed st rid hInv hChain)
    ?_ (detachReplyFrameAboveOrSelf_unreferenced st rid hInv hChain) hStep
  intro r sc hR
  obtain ⟨rp, hrp, hNext, _⟩ := detachReplyFrameAboveOrSelf_reply_next st rid hInv rid r hR
  rw [hNext]
  exact hNotHead rp sc hrp

/-- **WS-RM (`v0.35.6`): on a stack *head* the removal leaves the chain relaxed at
exactly one key** — the frame it answered.

A head keeps its links when its caller is consumed (`Reply.consumed_of_head`), so
between the reply leg and the donation pop that follows it in the same transition
the frame at `rid` has `caller = none` and a live `.head` link:
`Reply.wellFormed` is false there and **nowhere else**.  The context still names
the frame and the frame still names the context; no frame's `prev` names it,
because its `next` is a `.head` and the pre-state reciprocity admits none; and
every walk runs over links nothing moved.

The transient is discharged where the pop runs, which is why this is stated rather
than hidden. -/
theorem removeCallerReplyFrame_head_preserves_donationChainWellFormedExcept
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (r : Reply) (scId : SeLe4n.SchedContextId) (hInv : st.objects.invExt)
    (hChain : donationChainWellFormed st)
    (hR : st.getReply? rid = some r) (hHead : r.next = some (.head scId))
    (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    donationChainWellFormedExcept st' rid := by
  -- On a head the detach is the identity: a `.head` link names no frame above.
  have hFold : detachReplyFrameAboveOrSelf st rid = st :=
    detachReplyFrameAboveOrSelf_eq_self_of_no_frame_above st rid
      (replyFrameAbove?_of_head st rid r scId hR hHead)
  rw [removeCallerReplyFrame_eq, hFold] at hStep
  exact consumeCallerReply_head_preserves_donationChainWellFormedExcept st st' caller rid r scId
    hInv hChain hR hHead hStep

end SeLe4n.Kernel
