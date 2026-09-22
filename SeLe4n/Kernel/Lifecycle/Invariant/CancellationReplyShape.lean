-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Invariant.CancellationNotificationShape
-- WS-RR RR8.7: the reclaim ends in `returnDonatedSchedContext`, whose bundle
-- carriage lives here.  The dependency runs cancellation -> donation and never
-- the reverse, so no cycle closes.
import SeLe4n.Kernel.IPC.Invariant.DonationPreservation

/-!
# WS-RR RR7.22 (residual, remediation) — the cancelled caller's donation

A cancelled caller gets back the scheduling context it donated on its `Call` —
seL4-MCS's `reply_remove` semantics applied at the *cancellation* point, where
upstream defers them to Reply-object finalisation (`v0.35.40`; `cancelIPC` itself
runs `reply_remove_tcb` and donates nothing, and this kernel's binding typing
forces the earlier point — see `Lifecycle/Suspend.lean`'s
`returnDonationToCancelledCaller` for the four upstream paths).  Until v0.34.97
this model's `.blockedOnReply` arm cleared the reply *link* only, so the server
kept `schedContextBinding = .donated scId caller` while the caller was moved to
`.ready` and then `.Inactive` — a state `donationOwnerValid` forbids, and
operationally a permanent transfer of the caller's CBS reservation to the server,
after which the caller could never be scheduled again.

No existing theorem was unsound: nothing claimed `donationOwnerValid` across
suspend.  That is what made it a false-assurance gap rather than a broken proof,
and why the reply arm could not state the bundle.

## What this module holds

`donatedContextIsOwnerFrameHead` — the fact the return needs and the bundle does
not entail: the donation a cancelled caller owns is the one that caller's own reply
**frame heads**, and its holder is a real (non-reserved) thread.  Operationally
maintained — `donateSchedContext` mints the `.donated` binding and pushes the
donor's own `replyObject` as the context's stack head in one step — but
`donationOwnerValid` relates a donation to no reply object and
`donationChainWellFormed` carries no binding clause at all.  Stated, in the same
style as this workstream's other four queue-coherence facts.

**WS-HP HP5.3** re-keyed it with the resolver: until then it was
`donationHolderIsReplyTarget`, about the caller's *recorded reply target*, which is
what the reclaim used to read.  The old fact is deleted rather than kept beside the
new one — a stated hypothesis with no consumer is the shape this project retires.

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

/-- **WS-HP HP5.1: what a resolved reclaim asserts, under the head-driven trigger.**

The binding reading made this say two things: the victim is `.blockedOnReply`
naming `holder`, and `holder`'s binding is `.donated scId` *this victim*.  The head
reading says something different and, for the pop, more useful: the victim's own
reply **frame heads** `scId`, and that context is bound to `holder`.

`sc.boundThread = some holder` is exactly the pop's own guard, so what used to be
recovered from `donationOwnerValid` is now a consequence of the trigger firing —
which is what lets the reclaim reach
`returnDonatedSchedContext_ok_of_boundAndRecipient` with no coherence hypothesis
about a binding this resolver never reads.

The **recorded** reply target is no longer part of the claim, because the resolver
no longer reads it; `cancelledCallerDonation?_some_blockedOnReply` still gives the
arm shape, which is all the exclusivity arguments need. -/
theorem cancelledCallerDonation?_some (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (h : Lifecycle.Suspend.cancelledCallerDonation? st tid tcb = some (scId, holder)) :
    (∃ ep rt, tcb.ipcState = .blockedOnReply ep rt) ∧
    ∃ (rid : SeLe4n.ReplyId) (r : Reply) (sc : SeLe4n.Kernel.SchedContext),
      tcb.replyObject = some rid ∧ st.getReply? rid = some r ∧
      r.next = some (.head scId) ∧ st.getSchedContext? scId = some sc ∧
      sc.scReply = some rid ∧ sc.boundThread = some holder := by
  unfold Lifecycle.Suspend.cancelledCallerDonation? at h
  cases hIp : tcb.ipcState with
  | blockedOnReply ep rt =>
    rw [hIp] at h
    cases hRO : tcb.replyObject with
    | none => rw [hRO] at h; cases h
    | some rid =>
      rw [hRO] at h
      obtain ⟨hHead, hBt⟩ := replyFrameHeadHolder?_eq_some h
      obtain ⟨r, sc, hR, hN, hSc, hRec⟩ := replyFrameHeadContext?_eq_some hHead
      refine ⟨⟨ep, rt, rfl⟩, rid, r, sc, rfl, hR, hN, hSc, hRec, ?_⟩
      rw [hSc] at hBt
      simpa using hBt
  | _ => rw [hIp] at h; cases h

/-- **WS-HP HP5.2 / `v0.35.157`: the donation a cancelled caller owns is the one its
own reply frame heads** — the cancellation reading of `donatedContextIsOwnerFrameHead`.

The fact itself lives upstream in `IPC/Invariant/Defs.lean` since `v0.35.157`, stated
over the reply path's resolver (`answeredFrameHeadContext?`), because the reply pop's
origin redirect became its second asker and could not see a definition here.  This
is the corollary the reclaim consumes: on an owner `donationOwnerValid` puts
`.blockedOnReply`, HP5.1's bridge
(`cancelledCallerDonation?_eq_answeredFrameHeadContext?`) makes the reclaim's
trigger answer exactly the pair the reply path's resolver answers, so whatever
donation the victim owns, `cancelledCallerDonation?` finds it, and finds it at the
same `(context, holder)`.

**Why the reclaim consumes this direction.**  The reply path's sibling ran head ->
binding, because there the *consumers* were binding-keyed and the trigger became
head-keyed; that sibling was `answeredHeadContextIsServerDonation`, **deleted** at
WS-HP HP7 (`v0.35.46`).  Here it is the other way round:
`returnDonationToCancelledCaller_no_donation_to_victim` quantifies over bindings
while the trigger is head-keyed, so what it needs is binding -> head. -/
theorem donatedContextIsOwnerFrameHead_cancelledCallerDonation? (st : SystemState)
    (owner : SeLe4n.ThreadId) (ownerTcb : TCB)
    (hHolder : donatedContextIsOwnerFrameHead st owner)
    (hLk : lookupTcb st owner = some ownerTcb)
    (hOwnerValid : donationOwnerValid st)
    (holder : SeLe4n.ThreadId) (holderTcb : TCB) (scId : SeLe4n.SchedContextId)
    (hAt : st.objects[holder.toObjId]? = some (.tcb holderTcb))
    (hBind : holderTcb.schedContextBinding = .donated scId owner) :
    Lifecycle.Suspend.cancelledCallerDonation? st owner ownerTcb = some (scId, holder) ∧
      lookupTcb st holder = some holderTcb := by
  obtain ⟨hHead, hLkHolder⟩ := hHolder ownerTcb hLk holder holderTcb scId hAt hBind
  obtain ⟨_, ownerTcb0, hOwnerObj, _, ep, rt, hIp0⟩ :=
    hOwnerValid holder holderTcb scId owner hAt hBind
  have hOwnerSame : ownerTcb0 = ownerTcb :=
    KernelObject.tcb.inj (Option.some.inj
      (hOwnerObj.symm.trans (lookupTcb_some_objects st owner ownerTcb hLk)))
  rw [hOwnerSame] at hIp0
  refine ⟨?_, hLkHolder⟩
  rw [Lifecycle.Suspend.cancelledCallerDonation?_eq_answeredFrameHeadContext? st owner ownerTcb
    hLk ep rt hIp0]
  exact hHead

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

/-- `v0.35.4`: the cancelled caller's frame splice writes only Reply objects, so
every binding reads through unchanged. -/
theorem spliceThreadReplyFrameOut_sameSchedContextBindings (st : SystemState) (tcb : TCB)
    (hInv : st.objects.invExt) :
    sameSchedContextBindings st (spliceThreadReplyFrameOut st tcb) :=
  fun t tcb' hPost =>
    ⟨tcb', spliceThreadReplyFrameOut_tcb_backward st tcb hInv t.toObjId tcb'
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

/-- **WS-RR RR7.22 (residual, remediation) / WS-HP HP5.2**: after the reclaim no
thread holds a SchedContext donated by the cancelled caller.

**What changed at HP5.2**, and it is the whole of the difference: the reclaim's
trigger is head-driven, so the `(context, holder)` pair it acts on comes from the
victim's own reply frame rather than from a stored `.donated` binding.  The
statement is unchanged and so is every hypothesis but one --
`donatedContextIsOwnerFrameHead` replaces `donationHolderIsReplyTarget`, which is
the same local coherence fact re-keyed onto the thing the resolver now reads.

**How the two directions are covered.**  The conclusion quantifies over bindings
and the trigger reads frames, so a binding naming `v` has to be shown to be *the*
donation the trigger resolves; that is the coherence fact's content, consumed at
each of the three places a residual binding could survive: the reclaim declining
outright, the pop refusing, and the pop leaving a third thread untouched.  Nothing
is needed in the other direction, because everything the pop must know about the
context it pops -- that it exists, and that it is bound to the holder the trigger
names -- falls out of `cancelledCallerDonation?_some`.

**Why the case split is on the pop's own result.**  Under the binding reading the
proof established that the pop *succeeds* up front, from the holder's `.donated`
binding.  The head reading does not supply that binding, and the fact it would be
needed for -- that the victim is `.unbound`, which HP4.6's recipient guard asks --
is available only where a residual binding naming `v` actually exists.  So the
refused branch is where the success argument belongs: there `hTcb` *is* a pre-state
binding, `donationOwnerValid` reads the victim's `.unbound` off it, and the pop
therefore cannot have refused.  The committed branch needs no such argument. -/
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
    (hHolder : donatedContextIsOwnerFrameHead st v)
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
    -- The reclaim is the identity, so `hTcb` is a pre-state binding naming `v` --
    -- and the coherence fact says the trigger resolves exactly that donation.
    rw [hRes] at hTcb
    simp only at hTcb
    exact absurd ((donatedContextIsOwnerFrameHead_cancelledCallerDonation? st v tcbV hHolder
      hLookup hOwner tid tcb scId hTcb hBind).1.symm.trans hRes)
      (by intro hc; cases hc)
  | some p =>
    obtain ⟨scId0, holder⟩ := p
    rw [hRes] at hTcb
    simp only at hTcb
    -- **WS-HP HP5.1**: everything the pop needs about the context it is popping is
    -- a consequence of the trigger firing: the frame heads `scId0`, and `scId0` is
    -- bound to `holder`.  No binding is read here, and none is available.
    -- Only the context and its bound thread are consumed here; the frame's own
    -- identity and reciprocity are the trigger's business, and naming them would
    -- shadow the `cases hN : n` below.
    obtain ⟨_, _, _, sc, _, _, _, hSc, _, hBt⟩ := cancelledCallerDonation?_some st v tcbV
      scId0 holder hRes
    have hInvA : (Lifecycle.Suspend.abortHolderPendingIpc st holder).objects.invExt :=
      Lifecycle.Suspend.abortHolderPendingIpc_preserves_objects_invExt st holder hInv
    have hHeadResA : donationHeadResolves (Lifecycle.Suspend.abortHolderPendingIpc st holder)
        scId0 :=
      donationHeadResolves_of_frame
        (Lifecycle.Suspend.abortHolderPendingIpc_donationChainFrame st holder hInv) scId0
        (donationHeadResolves_of_chainWellFormed st scId0 hChain)
    -- **WS-OD OD4.4**: the pop resolves its new owner off the context's own reply
    -- stack, at the post-abort state.  The chain invariant carries across the
    -- abort (`abortHolderPendingIpc_donationChainFrame`), so the resolver
    -- *answers*; what it answers is the caller's obligation.  The SchedContext
    -- witness the resolution needs comes from the trigger rather than from a
    -- binding, and it crosses the abort because the abort writes no SchedContext.
    have hChainA : donationChainWellFormed (Lifecycle.Suspend.abortHolderPendingIpc st holder) :=
      donationChainWellFormed_of_frame
        (Lifecycle.Suspend.abortHolderPendingIpc_donationChainFrame st holder hInv) hChain
    have hScObj : st.objects[scId0.toObjId]? = some (.schedContext sc) :=
      (SystemState.getSchedContext?_eq_some_iff st scId0 sc).mp hSc
    have hScA : (Lifecycle.Suspend.abortHolderPendingIpc st holder).objects[scId0.toObjId]?
        = some (.schedContext sc) :=
      Lifecycle.Suspend.abortHolderPendingIpc_unwritten_kind_forward st holder hInv
        (fun o => ∃ sc0 : SeLe4n.Kernel.SchedContext, o = .schedContext sc0)
        (fun _ hc => nomatch hc.choose_spec) (fun _ hc => nomatch hc.choose_spec)
        scId0.toObjId _ ⟨sc, rfl⟩ hScObj
    obtain ⟨n, hResN⟩ :=
      replyStackOuterCallerResolves_of_chainWellFormed _ scId0 hChainA sc hScA
    rw [returnDonatedSchedContextResolved_of_resolved hResN] at hTcb
    cases hRet : returnDonatedSchedContext (Lifecycle.Suspend.abortHolderPendingIpc st holder)
        holder scId0 v n with
    | error e =>
      -- A refused reclaim is the identity, so `hTcb` is again a pre-state binding
      -- naming `v` -- and *that* is what licenses the success argument: the
      -- coherence fact identifies the residual donation with the one the trigger
      -- resolved, and `donationOwnerValid` then reads off the two facts the pop
      -- asks of its recipient.
      rw [hRet] at hTcb
      simp only at hTcb
      obtain ⟨hResEq, hLkTid⟩ := donatedContextIsOwnerFrameHead_cancelledCallerDonation? st v tcbV
        hHolder hLookup hOwner tid tcb scId hTcb hBind
      have hPair : (scId, tid) = (scId0, holder) :=
        Option.some.inj (hResEq.symm.trans hRes)
      have hScIdEq : scId = scId0 := congrArg Prod.fst hPair
      have hTidEq : tid = holder := congrArg Prod.snd hPair
      have hHolderAt : st.objects[holder.toObjId]? = some (.tcb tcb) := by
        rw [← hTidEq]; exact hTcb
      have hLkHolder : lookupTcb st holder = some tcb := by rw [← hTidEq]; exact hLkTid
      have hBind0 : tcb.schedContextBinding = .donated scId0 v := by
        rw [← hScIdEq]; exact hBind
      obtain ⟨_, vTcb0, hVObj, hVUnbound, _⟩ := hOwner holder tcb scId0 v hHolderAt hBind0
      have hVSame : vTcb0 = tcbV :=
        KernelObject.tcb.inj (Option.some.inj
          (hVObj.symm.trans (lookupTcb_some_objects st v tcbV hLookup)))
      have hVUnboundV : tcbV.schedContextBinding = .unbound := by
        rw [← hVSame]; exact hVUnbound
      -- `v` gave its binding up and the residual holder holds one, so they differ.
      have hNeVHolder : v ≠ holder := by
        intro hEq
        rw [hEq] at hVObj
        rw [KernelObject.tcb.inj (Option.some.inj (hVObj.symm.trans hHolderAt))] at hVUnbound
        rw [hBind0] at hVUnbound
        cases hVUnbound
      obtain ⟨holderTcbA, hHolderAtA, _⟩ :=
        Lifecycle.Suspend.abortHolderPendingIpc_binding_forward st holder hInv holder.toObjId
          tcb hHolderAt
      obtain ⟨vTcbA, hVObjA, hVBindA⟩ :=
        Lifecycle.Suspend.abortHolderPendingIpc_binding_forward st holder hInv v.toObjId
          tcbV (by rw [← hVSame]; exact hVObj)
      obtain ⟨st', hOk⟩ := returnDonatedSchedContext_ok_of_boundAndRecipient
        (Lifecycle.Suspend.abortHolderPendingIpc st holder) holder holderTcbA scId0 v sc vTcbA
        hInvA hHeadResA
        (lookupTcb_of_objects_of_not_reserved _ holder holderTcbA hHolderAtA
          (lookupTcb_some_not_reserved st holder tcb hLkHolder))
        hScA (by simpa using hBt) hVObjA (hVBindA.trans hVUnboundV)
        hNeVHolder (lookupTcb_some_not_reserved st holder tcb hLkHolder)
        (lookupTcb_some_not_reserved st v tcbV hLookup) n
        ((hStack scId0 holder hRes) n hResN).1
      rw [hOk] at hRet
      cases hRet
    | ok st' =>
      rw [hRet] at hTcb
      simp only at hTcb
      obtain ⟨hSrv, hOwn, hOther⟩ := returnDonatedSchedContext_tcb_schedContextBinding_backward
        (Lifecycle.Suspend.abortHolderPendingIpc st holder) st' holder scId0 v hInvA n hRet
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
        · -- A third thread the pop left alone: its binding is the pre-state's, and
          -- the coherence fact says the only pre-state donation naming `v` is the
          -- one the trigger resolved -- whose holder is `holder`, which this thread
          -- is not.
          obtain ⟨tA, hAtA, hEqA⟩ := hOther hH hV
          obtain ⟨t0, h0, hEqB⟩ :=
            Lifecycle.Suspend.abortHolderPendingIpc_binding_backward st holder hInv tid.toObjId
              tA hAtA
          obtain ⟨hResEq, _⟩ := donatedContextIsOwnerFrameHead_cancelledCallerDonation? st v tcbV
            hHolder hLookup hOwner tid t0 scId h0 (by rw [hEqB, hEqA]; exact hBind)
          have hPair : (scId, tid) = (scId0, holder) :=
            Option.some.inj (hResEq.symm.trans hRes)
          have hTidEq : tid = holder := congrArg Prod.snd hPair
          exact hH (by rw [hTidEq])

theorem consumeReplyLink_sameSchedContextBindings (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hInv : st.objects.invExt) :
    sameSchedContextBindings st (Lifecycle.Suspend.consumeReplyLink st tid tcb) := by
  unfold Lifecycle.Suspend.consumeReplyLink
  split
  · exact sameSchedContextBindings.refl st
  · rename_i rid _
    exact consumeCallerReply_sameSchedContextBindings st _ tid rid hInv
      (SystemState.consumeCallerReply_eq_link st tid rid)

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

/-- WS-OD OD1.5: the reply-link consume frames `passiveServerIdle` — the reply
path's own frame, through the RR8.5 bridge. -/
theorem consumeReplyLink_passiveServerIdleFrame (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hInv : st.objects.invExt) :
    passiveServerIdleFrame st (Lifecycle.Suspend.consumeReplyLink st tid tcb) := by
  unfold Lifecycle.Suspend.consumeReplyLink
  cases tcb.replyObject with
  | none => exact passiveServerIdleFrame.refl st
  | some rid =>
    exact consumeCallerReply_passiveServerIdleFrame st _ tid rid hInv
      (SystemState.consumeCallerReply_eq_link st tid rid)

/-- `v0.35.4`: the cancelled caller's frame splice frames `passiveServerIdle` —
its writes all land on `.reply` values, whose keys can never hold a TCB, and it
touches no scheduler slot. -/
theorem spliceThreadReplyFrameOut_passiveServerIdleFrame (st : SystemState) (tcb : TCB)
    (hInv : st.objects.invExt) :
    passiveServerIdleFrame st (spliceThreadReplyFrameOut st tcb) :=
  passiveServerIdleFrame_of_backward
    (fun t tcb' hPost =>
      ⟨tcb', spliceThreadReplyFrameOut_tcb_backward st tcb hInv t.toObjId tcb'
        hPost, rfl, rfl⟩)
    (spliceThreadReplyFrameOut_scheduler_eq st tcb)

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
  · rename_i scId holder _ _ _
    split
    · rename_i st' hOk
      obtain ⟨n, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hOk
      refine (Lifecycle.Suspend.abortHolderPendingIpc_passiveServerIdleFrame st holder hInv).trans
        (returnDonatedSchedContext_passiveServerIdleFrame
          (Lifecycle.Suspend.abortHolderPendingIpc_preserves_objects_invExt st holder hInv)
          n hPop ?_)
      intro t hAt
      -- **WS-HP HP5.2**: the head-driven trigger names a scheduling context's
      -- `boundThread`, which no invariant in this tree ties to a stored TCB -- so
      -- the holder's TCB comes from the pop *having succeeded* rather than from the
      -- resolver, which is the only place it is now available.
      cases hLkH : lookupTcb st holder with
      | none =>
        exfalso
        rw [Lifecycle.Suspend.abortHolderPendingIpc_eq_self_of_lookup_none st holder hLkH] at hAt
        rw [lookupTcb_of_objects_of_not_reserved st holder t
          ((SystemState.getTcb?_eq_some_iff st holder t).mp hAt)
          (returnDonatedSchedContext_ok_server_not_reserved _ _ _ _ _ n hPop)] at hLkH
        cases hLkH
      | some holderTcb =>
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
            (spliceThreadReplyFrameOut
              (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV) v) v tcbV by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hIp]]
    have hF1 := returnDonationToCancelledCaller_passiveServerIdleFrame st v tcbV hInv hMem
    have hI1 := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt
      st v tcbV hInv
    -- `v0.35.4`: the frame splice writes only Reply objects, which frames the conjunct.
    have hFD := spliceThreadReplyFrameOut_passiveServerIdleFrame
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV hI1
    have hID := spliceThreadReplyFrameOut_preserves_objects_invExt
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV hI1
    have hF2 := restoreToReadyStaging_passiveServerIdleFrame
      (spliceThreadReplyFrameOut
        (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV) v
      (some Architecture.cancelledIpcFrame) hID
    have hI2 := Lifecycle.Suspend.restoreToReadyCancelled_invExt
      (spliceThreadReplyFrameOut
        (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV) v hID
    have hF3 := consumeReplyLink_passiveServerIdleFrame
      (Lifecycle.Suspend.restoreToReadyCancelled
        (spliceThreadReplyFrameOut
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
    (hHolder : donatedContextIsOwnerFrameHead st v)
    -- **WS-OD OD4.4**: see `returnDonationToCancelledCaller_no_donation_to_victim`.
    (hStack : cancelDonationStackValid st v tcbV)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (hTcb : (Lifecycle.Suspend.cancelIpcBlocking st v tcbV).objects[tid.toObjId]?
      = some (.tcb tcb)) :
    tcb.schedContextBinding ≠ .donated scId v := by
  have hArm : Lifecycle.Suspend.cancelIpcBlocking st v tcbV =
      Lifecycle.Suspend.consumeReplyLink
        (Lifecycle.Suspend.restoreToReadyCancelled
          (spliceThreadReplyFrameOut
            (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV) v) v tcbV := by
    unfold Lifecycle.Suspend.cancelIpcBlocking
    rw [hBlocked]
  rw [hArm] at hTcb
  have hInvR := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt st v tcbV hInv
  have hInvD := spliceThreadReplyFrameOut_preserves_objects_invExt _ tcbV hInvR
  have hInvS := Lifecycle.Suspend.restoreToReadyCancelled_invExt _ v hInvD
  have hSame :
      sameSchedContextBindings (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV)
        (Lifecycle.Suspend.consumeReplyLink
          (Lifecycle.Suspend.restoreToReadyCancelled
            (spliceThreadReplyFrameOut
              (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV) v) v tcbV) :=
    ((spliceThreadReplyFrameOut_sameSchedContextBindings _ tcbV hInvR).trans
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

Its TCB leg rewrites `tid` alone, and its Reply leg writes a key that holds a
`.reply`, which can never alias a TCB-holding key — since WS-RR RR8.5 both are
the reply path's own `consumeCallerReply`, so this is
`consumeCallerReply_tcb_other` through the bridge.  The existing `consumeReplyLink_tcb_lookup` says only
that the *kind* and `cpuAffinity` survive; a footprint argument needs the
stronger reading, because "some TCB is still there" does not rule out its links
having changed. -/
theorem consumeReplyLink_other_tcb_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (hInv : st.objects.invExt) (k : SeLe4n.ObjId) (t0 : TCB)
    (hNe : k ≠ tid.toObjId) (hPre : st.objects[k]? = some (.tcb t0)) :
    (Lifecycle.Suspend.consumeReplyLink st tid tcb).objects[k]? = some (.tcb t0) := by
  unfold Lifecycle.Suspend.consumeReplyLink
  cases tcb.replyObject with
  | none => exact hPre
  | some rid =>
    exact SystemState.consumeCallerReply_tcb_other st _ tid rid hInv
      (SystemState.consumeCallerReply_eq_link st tid rid) k t0 hNe hPre

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
          (spliceThreadReplyFrameOut st tcbV) v) v tcbV := by
    unfold Lifecycle.Suspend.cancelIpcBlocking
    rw [hBlocked, Lifecycle.Suspend.returnDonationToCancelledCaller_none st v tcbV hNoDonation]
  rw [hArm]
  -- `v0.35.4`: the frame splice writes only Reply objects, so every TCB is untouched.
  have hInvD := spliceThreadReplyFrameOut_preserves_objects_invExt st tcbV hInv
  refine consumeReplyLink_other_tcb_eq _ v tcbV
    (Lifecycle.Suspend.restoreToReadyCancelled_invExt _ v hInvD) k t0 hNe ?_
  show (Lifecycle.Suspend.restoreToReadyStaging
    (spliceThreadReplyFrameOut st tcbV) v _).objects[k]? = some (.tcb t0)
  rw [restoreToReadyStaging_objects_ne _ v _ k hInvD hNe]
  exact spliceThreadReplyFrameOut_tcb_eq st tcbV hInv k t0 hPre

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
          (spliceThreadReplyFrameOut
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
  -- `v0.35.4`: the frame splice between the reclaim and the restore writes only
  -- Reply objects, so the TCB reads through it.
  have hSplice : (spliceThreadReplyFrameOut
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV).objects[k]?
        = some (.tcb t0) :=
    spliceThreadReplyFrameOut_tcb_eq _ tcbV hInvR k t0 hReclaim
  have hInvD := spliceThreadReplyFrameOut_preserves_objects_invExt _ tcbV hInvR
  refine consumeReplyLink_other_tcb_eq _ v tcbV
    (Lifecycle.Suspend.restoreToReadyCancelled_invExt _ v hInvD) k t0 hkV ?_
  show (Lifecycle.Suspend.restoreToReadyStaging
    (spliceThreadReplyFrameOut
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV) v _).objects[k]?
      = some (.tcb t0)
  rw [restoreToReadyStaging_objects_ne _ v _ k hInvD hkV]
  exact hSplice

-- ============================================================================
-- WS-OD OD5.2 — `.tcbSuspend` of a caller, at every chain depth
-- ============================================================================

/-- **WS-OD OD5.2 / WS-HP HP5.3: the cancelled caller gets its scheduling context
back exactly when its own reply frame heads that context.**

The binding reading of this said "exactly when it is the immediate donor to the
thread holding it", and reached the holder through the victim's recorded reply
target.  The head reading says the same thing about the *stack*, and says it about
the object the reclaim now reads: `donateSchedContext` pushes the donor's own
`replyObject` as the context's stack head, so "the victim's frame heads `scId`" and
"the victim is the immediate donor of `scId`" are two spellings of one fact -- and
this is the spelling that is a theorem rather than a hypothesis, because the
trigger reads the frame directly.

So on a chain `D → C → S`, cancelling `C` returns the context to `C` (and OD4.4's
resolver then rebinds it `.donated sc D`, since the stack still names `D` below
`C`'s frame).

Stated so the *positive* half of the policy is visible beside the negative one
below: `severAtCut` is not "a cancelled caller never gets its context back", it
is "a cancelled caller gets back exactly the donation it made". -/
theorem cancelledCallerDonation?_some_of_frame_head
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (holder : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (sc : SeLe4n.Kernel.SchedContext)
    (hIpc : tcb.ipcState = .blockedOnReply ep rt)
    (hRO : tcb.replyObject = some rid)
    (hHead : replyFrameHeadContext? st rid = some scId)
    (hSc : st.getSchedContext? scId = some sc)
    (hBound : sc.boundThread = some holder) :
    Lifecycle.Suspend.cancelledCallerDonation? st tid tcb = some (scId, holder) := by
  unfold Lifecycle.Suspend.cancelledCallerDonation?
  rw [hIpc, hRO]
  exact replyFrameHeadHolder?_of_head st rid scId holder hHead (by rw [hSc]; simpa using hBound)

/-- **WS-OD OD5.2 / WS-HP HP5.3: below the cut the reclaim declines, and that is
the policy.**

At call depth ≥ 3 the victim has donated the context onward, so a *further* frame
sits above its own on that context's reply stack and the context's head names that
frame instead -- `replyFrameHeadContext?_of_frameAbove` is the structural fact, and
it is the cut's other side: the pop's trigger and the removal's are mutually
exclusive by construction.  The reclaim therefore answers `none` and
`returnDonationToCancelledCaller` is the identity.  The context stays where it is,
and the pop that later reaches the victim's now caller-less frame carries it on
outward to the caller the surviving stack names, `.donated scId outer`
(`cancelledMiddleCaller_splices_at_cut`).

**What HP5.1 changed is the reason, not the outcome.**  Under the binding reading
the reclaim declined because the victim's recorded reply target had given its own
binding up; under the head reading it declines because the victim's frame is not a
head.  The second is a fact about the reply stack alone, so it needs no binding
hypothesis at all -- which is why this restatement is strictly cheaper than the one
it replaces.

This is `spliceOutTheCut` seen from the cancellation end, and it is a decision
rather than an omission: `reclaimToCancelledThread` would reach the real holder
through `SchedContext.boundThread` and rewrite a binding this theorem says is
untouched.  What the splice costs, and does not, is stated at
`cancelledMiddleCallerPolicy`: since HP6.8 the reservation travels outward past the
cut rather than settling on the innermost live caller, and the depth-2 residue the
splice provably cannot reach is closed instead by the reservation's recorded origin
(`donationAccountingPreserved_atCallDepthTwo`, WS-HP HP10.9). -/
theorem cancelledCallerDonation?_none_below_the_cut
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId) (rid above : SeLe4n.ReplyId)
    (hIpc : tcb.ipcState = .blockedOnReply ep rt)
    (hRO : tcb.replyObject = some rid)
    (hDonatedOnward : replyFrameAbove? st rid = some above) :
    cancelledMiddleCallerPolicy = CancelledMiddleCallerPolicy.spliceOutTheCut ∧
    Lifecycle.Suspend.cancelledCallerDonation? st tid tcb = none ∧
    Lifecycle.Suspend.returnDonationToCancelledCaller st tid tcb = st := by
  have hNone : Lifecycle.Suspend.cancelledCallerDonation? st tid tcb = none := by
    unfold Lifecycle.Suspend.cancelledCallerDonation?
    rw [hIpc, hRO]
    exact replyFrameHeadHolder?_of_no_head st rid
      (replyFrameHeadContext?_of_frameAbove st rid above hDonatedOnward)
  exact ⟨rfl, hNone, Lifecycle.Suspend.returnDonationToCancelledCaller_none st tid tcb hNone⟩

/-- **WS-OD OD5.2 / `v0.35.4`: and the whole cancellation arm reclaims nothing
there.**

The payoff for `.tcbSuspend`: below the cut the reply arm is the teardown -- the
`O(1)` splice of the victim's frame out of its stack, the `.ipcCancelled` restore
and the reply-link consume -- with no donation write at all.  So the depth-≥ 3
case needs no binding argument at all since HP5.3 (the reclaim declines on the
*stack*, which the removal is about anyway), which is what makes the removal cheap
as well as `O(1)`; what it does need is the chain argument, since the removal and
the consume both write stack links
(`consumeReplyLink_preserves_donationChainWellFormed`). -/
theorem cancelIpcBlocking_reply_arm_below_the_cut
    (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB)
    (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId) (rid above : SeLe4n.ReplyId)
    (hIpc : tcbV.ipcState = .blockedOnReply ep rt)
    (hRO : tcbV.replyObject = some rid)
    (hDonatedOnward : replyFrameAbove? st rid = some above) :
    Lifecycle.Suspend.cancelIpcBlocking st v tcbV =
      Lifecycle.Suspend.consumeReplyLink
        (Lifecycle.Suspend.restoreToReadyCancelled
          (spliceThreadReplyFrameOut st tcbV) v) v tcbV := by
  obtain ⟨_, _, hIdent⟩ :=
    cancelledCallerDonation?_none_below_the_cut st v tcbV ep rt rid above hIpc hRO
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

-- ============================================================================
-- `v0.35.4` — the cancellation's chain writes preserve the chain
-- ============================================================================

/-! With the doubly-linked stack the cancellation's reply arm is a chain
**writer** on two counts, and neither reaches `donationChainWellFormed_of_frame`:

* the `O(1)` splice (`spliceReplyFrameOut`, seL4's `reply_remove_tcb` on a
  non-head frame, with the middle case spliced rather than severed since WS-HP
  HP6.3) re-points the `prev` of the frame above the cancelled caller's at the
  frame below it, links that frame back up, and clears the cut frame's own `prev`
  — or, at a bottom frame, clears the frame above's `prev` alone;
* the reply-link consume (`consumeReplyLink` — the reply path's own
  `consumeCallerReply` since WS-RR RR8.5, storing `Reply.consumed`) clears the
  cancelled caller's own two links unless the frame heads a context.

So each carries a preservation theorem.  The splice needs no hypothesis: it
reconnects the two frames either side of the cut
(`spliceReplyFrameOut_preserves_donationChainWellFormed`), or — at a bottom frame,
the degenerate sever — shortens the stack by one and repairs the only link that
named the frame it cut (`donationChainWalk_exists_of_agree_or_cut`).  The consume
needs two facts about the frame it clears, both established by the splice that
runs first: the frame heads no context (a head is popped by the reclaim, never
consumed in place), and no frame's `prev` still names it — which is exactly what
the splice guarantees (`spliceThreadReplyFrameOut_unreferenced`).  A stale
*upward* link (`next = .frame victim` on a frame below whose own link did not
reciprocate) survives only the degenerate arm, and is one the invariant
deliberately does not constrain: nothing trusts an upward link that is not
answered from above, which is what keeps the cut `O(1)`. -/

/-- `v0.35.4`: **the splice preserves the chain invariant** — since WS-HP HP6.3
three Reply stores that reconnect the frames either side of the cut and clear the
cut frame's own `prev` (one store, clearing the frame above's `prev`, at a bottom
frame), so every reciprocity clause is either untouched or re-established, and
the walk from the frame's head continues past the cut — or, at the bottom, stops
at it. -/
theorem spliceReplyFrameOut_preserves_donationChainWellFormed {st st' : SystemState}
    {rid : SeLe4n.ReplyId} (hInv : st.objects.invExt) (hChain : donationChainWellFormed st)
    (h : spliceReplyFrameOut st rid = .ok st') : donationChainWellFormed st' := by
  rcases spliceReplyFrameOut_cases h with rfl | ⟨r, above, a, hR, hN, hA, hP, hS⟩
  · exact hChain
  · rcases spliceReplyFrameStores_cases hS with
      ⟨_, hS1⟩ | ⟨below, b, s1, s2, hBelow, hS1, hS2, hS3⟩
    · -- **The degenerate branch**: nothing below the cut to splice to, so this is
      -- the pre-WS-HP sever and the proof below is that cut's verbatim.
      have hAObj := (SystemState.getReply?_eq_some_iff _ _ _).mp hA
      have hAbove : st'.objects[above.toObjId]? = some (.reply { a with prev := none }) :=
        storeObject_objects_eq' st _ _ _ hInv hS1
      have hOther : ∀ k : SeLe4n.ObjId, k ≠ above.toObjId → st'.objects[k]? = st.objects[k]? :=
        fun k hk => storeObject_objects_ne st st' above.toObjId k _ hk hInv hS1
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
    · -- **The splice branch**: three stores at pairwise-distinct keys.  Every
      -- clause is decided by which of the three the key is.
      obtain ⟨hAboveVal, hBelowVal, hCutVal, hFrame⟩ :=
        spliceReplyFrameStores_splice_values hInv hR hN hA hP hBelow hS
      obtain ⟨hPrevR, hNeBA, hB, hBN⟩ := spliceFrameBelow?_eq_some hBelow
      have hNeBR : below ≠ rid := spliceFrameBelow?_ne_cut hR hN hBelow
      have hAObj : st.objects[above.toObjId]? = some (.reply a) :=
        (SystemState.getReply?_eq_some_iff _ _ _).mp hA
      have hBObj : st.objects[below.toObjId]? = some (.reply b) :=
        (SystemState.getReply?_eq_some_iff _ _ _).mp hB
      have hRObj : st.objects[rid.toObjId]? = some (.reply r) :=
        (SystemState.getReply?_eq_some_iff _ _ _).mp hR
      have hAPost : st'.objects[above.toObjId]? = some (.reply { a with prev := some below }) :=
        (SystemState.getReply?_eq_some_iff _ _ _).mp hAboveVal
      have hBPost :
          st'.objects[below.toObjId]? = some (.reply { b with next := some (.frame above) }) :=
        (SystemState.getReply?_eq_some_iff _ _ _).mp hBelowVal
      have hRPost : st'.objects[rid.toObjId]? = some (.reply { r with prev := none }) :=
        (SystemState.getReply?_eq_some_iff _ _ _).mp hCutVal
      have hFrame' : ∀ q : SeLe4n.ReplyId, q ≠ above → q ≠ below → q ≠ rid →
          st'.objects[q.toObjId]? = st.objects[q.toObjId]? := by
        intro q h1 h2 h3
        exact hFrame q.toObjId (fun hx => h1 (SeLe4n.ReplyId.toObjId_injective _ _ hx))
          (fun hx => h2 (SeLe4n.ReplyId.toObjId_injective _ _ hx))
          (fun hx => h3 (SeLe4n.ReplyId.toObjId_injective _ _ hx))
      have hReplyCases : ∀ (q : SeLe4n.ReplyId) (rq : Reply),
          st'.objects[q.toObjId]? = some (.reply rq) →
          (q = above ∧ rq = { a with prev := some below }) ∨
          (q = below ∧ rq = { b with next := some (.frame above) }) ∨
          (q = rid ∧ rq = { r with prev := none }) ∨
          (q ≠ above ∧ q ≠ below ∧ q ≠ rid ∧ st.objects[q.toObjId]? = some (.reply rq)) := by
        intro q rq hq
        by_cases h1 : q = above
        · rw [h1, hAPost] at hq
          exact Or.inl ⟨h1, (KernelObject.reply.inj (Option.some.inj hq)).symm⟩
        · by_cases h2 : q = below
          · rw [h2, hBPost] at hq
            exact Or.inr (Or.inl ⟨h2, (KernelObject.reply.inj (Option.some.inj hq)).symm⟩)
          · by_cases h3 : q = rid
            · rw [h3, hRPost] at hq
              exact Or.inr (Or.inr (Or.inl
                ⟨h3, (KernelObject.reply.inj (Option.some.inj hq)).symm⟩))
            · exact Or.inr (Or.inr (Or.inr
                ⟨h1, h2, h3, by rw [← hFrame' q h1 h2 h3]; exact hq⟩))
      have hScBack : ∀ (c : SeLe4n.SchedContextId) (sc : SchedContext),
          st'.objects[c.toObjId]? = some (.schedContext sc) →
          st.objects[c.toObjId]? = some (.schedContext sc) := by
        intro c sc hc
        have h1 : c.toObjId ≠ above.toObjId := by intro hx; rw [hx, hAPost] at hc; cases hc
        have h2 : c.toObjId ≠ below.toObjId := by intro hx; rw [hx, hBPost] at hc; cases hc
        have h3 : c.toObjId ≠ rid.toObjId := by intro hx; rw [hx, hRPost] at hc; cases hc
        rw [← hFrame c.toObjId h1 h2 h3]; exact hc
      have hScFwd : ∀ (c : SeLe4n.SchedContextId) (sc : SchedContext),
          st.objects[c.toObjId]? = some (.schedContext sc) →
          st'.objects[c.toObjId]? = some (.schedContext sc) := by
        intro c sc hc
        have h1 : c.toObjId ≠ above.toObjId := by intro hx; rw [hx, hAObj] at hc; cases hc
        have h2 : c.toObjId ≠ below.toObjId := by intro hx; rw [hx, hBObj] at hc; cases hc
        have h3 : c.toObjId ≠ rid.toObjId := by intro hx; rw [hx, hRObj] at hc; cases hc
        rw [hFrame c.toObjId h1 h2 h3]; exact hc
      -- Every frame the walk and the reciprocity clause can reach from a rewritten
      -- `prev`: the frame above keeps its `next`, and the other two are ruled out by
      -- the very links the splice validated.
      have hPrevPost : ∀ (q x : SeLe4n.ReplyId) (bx : Reply),
          st.objects[x.toObjId]? = some (.reply bx) → bx.next = some (.frame q) →
          q ≠ rid → q ≠ above →
          ∃ bx', st'.objects[x.toObjId]? = some (.reply bx') ∧ bx'.next = some (.frame q) := by
        intro q x bx hBx hBxNext hqR hqA
        by_cases hxA : x = above
        · refine ⟨{ a with prev := some below }, by rw [hxA]; exact hAPost, ?_⟩
          have hba : bx = a := by
            rw [hxA, hAObj] at hBx; exact (KernelObject.reply.inj (Option.some.inj hBx)).symm
          show a.next = some (.frame q)
          rw [← hba]; exact hBxNext
        · by_cases hxB : x = below
          · exfalso
            have hbb : bx = b := by
              rw [hxB, hBObj] at hBx; exact (KernelObject.reply.inj (Option.some.inj hBx)).symm
            rw [hbb, hBN] at hBxNext
            exact hqR (ReplyStackLink.frame.inj (Option.some.inj hBxNext)).symm
          · by_cases hxR : x = rid
            · exfalso
              have hbr : bx = r := by
                rw [hxR, hRObj] at hBx; exact (KernelObject.reply.inj (Option.some.inj hBx)).symm
              rw [hbr, hN] at hBxNext
              exact hqA (ReplyStackLink.frame.inj (Option.some.inj hBxNext)).symm
            · exact ⟨bx, by rw [hFrame' x hxA hxB hxR]; exact hBx, hBxNext⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- `replyWellFormed`: each of the three written frames still has a caller,
        -- because each carries a link the pre-state invariant would have forbidden.
        intro q rq hq
        rcases hReplyCases q rq hq with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, _, hPre⟩
        · intro hC
          exact absurd (hChain.replyWellFormed above a hAObj hC).1 (by rw [hP]; simp)
        · intro hC
          exact absurd (hChain.replyWellFormed below b hBObj hC).2 (by rw [hBN]; simp)
        · intro hC
          exact absurd (hChain.replyWellFormed rid r hRObj hC).2 (by rw [hN]; simp)
        · exact hChain.replyWellFormed q rq hPre
      · -- `headLinkReciprocal`: a context's head keeps its `.head` link, and neither
        -- the frame below the cut nor the cut frame can be one.
        intro c sc hc q hQ
        obtain ⟨rq, hRq, hNextQ⟩ := hChain.headLinkReciprocal c sc (hScBack c sc hc) q hQ
        by_cases hqA : q = above
        · refine ⟨{ a with prev := some below }, by rw [hqA]; exact hAPost, ?_⟩
          have hra : rq = a := by
            rw [hqA, hAObj] at hRq; exact (KernelObject.reply.inj (Option.some.inj hRq)).symm
          show a.next = some (.head c)
          rw [← hra]; exact hNextQ
        · by_cases hqB : q = below
          · exfalso
            have hrb : rq = b := by
              rw [hqB, hBObj] at hRq; exact (KernelObject.reply.inj (Option.some.inj hRq)).symm
            rw [hrb, hBN] at hNextQ; cases hNextQ
          · by_cases hqR : q = rid
            · exfalso
              have hrr : rq = r := by
                rw [hqR, hRObj] at hRq; exact (KernelObject.reply.inj (Option.some.inj hRq)).symm
              rw [hrr, hN] at hNextQ; cases hNextQ
            · exact ⟨rq, by rw [hFrame' q hqA hqB hqR]; exact hRq, hNextQ⟩
      · -- `headLinkResolves`: only the frame above the cut can still claim a head,
        -- and its `next` is untouched.
        intro q rq c hRq hNextQ
        rcases hReplyCases q rq hRq with ⟨hqA, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, _, hPre⟩
        · obtain ⟨sc, hSc, hHead⟩ := hChain.headLinkResolves above a c hAObj hNextQ
          exact ⟨sc, hScFwd c sc hSc, by rw [hqA]; exact hHead⟩
        · exact absurd hNextQ (by simp)
        · exact absurd hNextQ (by rw [hN]; simp)
        · obtain ⟨sc, hSc, hHead⟩ := hChain.headLinkResolves q rq c hPre hNextQ
          exact ⟨sc, hScFwd c sc hSc, hHead⟩
      · -- `prevLinkReciprocal`: **the reciprocal pair is written together**, so the
        -- frame above is answered by the frame below; the cut frame's own `prev` is
        -- gone, which is the third store and the whole reason it exists.
        intro q rq x hRq hPrevQ
        rcases hReplyCases q rq hRq with ⟨hqA, rfl⟩ | ⟨hqB, rfl⟩ | ⟨_, rfl⟩ | ⟨hqA', hqB', hqR', hPre⟩
        · have hx : x = below := (Option.some.inj hPrevQ).symm
          subst hx
          refine ⟨{ b with next := some (.frame above) }, hBPost, ?_⟩
          show some (ReplyStackLink.frame above) = some (.frame q)
          rw [hqA]
        · obtain ⟨bx, hBx, hBxNext⟩ := hChain.prevLinkReciprocal below b x hBObj hPrevQ
          rcases hPrevPost below x bx hBx hBxNext hNeBR hNeBA with ⟨bx', hBx', hBxNext'⟩
          exact ⟨bx', hBx', by rw [hqB]; exact hBxNext'⟩
        · exact absurd hPrevQ (by simp)
        · obtain ⟨bx, hBx, hBxNext⟩ := hChain.prevLinkReciprocal q rq x hPre hPrevQ
          exact hPrevPost q x bx hBx hBxNext hqR' hqA'
      · -- `headTerminates`: the post-state walk follows the same frames with the cut
        -- one skipped, so it terminates on the same fuel.
        intro c sc hc
        obtain ⟨fuel, chain, hWalk⟩ := hChain.headTerminates c sc (hScBack c sc hc)
        have hLA : replyStackLinksAt? st above = some (some rid, a.next) := by
          unfold replyStackLinksAt? SystemState.getObject?; rw [hAObj]; simp [hP]
        have hLAPost : replyStackLinksAt? st' above = some (some below, a.next) := by
          unfold replyStackLinksAt? SystemState.getObject?; rw [hAPost]; rfl
        have hLR : replyStackLinksAt? st rid = some (some below, some (.frame above)) := by
          unfold replyStackLinksAt? SystemState.getObject?; rw [hRObj]; simp [hPrevR, hN]
        have hLRPost : replyStackLinksAt? st' rid = some (none, some (.frame above)) := by
          unfold replyStackLinksAt? SystemState.getObject?; rw [hRPost]; simp [hN]
        have hLB : replyStackLinksAt? st below = some (b.prev, some (.frame rid)) := by
          unfold replyStackLinksAt? SystemState.getObject?; rw [hBObj]; simp [hBN]
        have hLBPost : replyStackLinksAt? st' below = some (b.prev, some (.frame above)) := by
          unfold replyStackLinksAt? SystemState.getObject?; rw [hBPost]; rfl
        have hAgreeL : ∀ q : SeLe4n.ReplyId, q ≠ above → q ≠ below → q ≠ rid →
            replyStackLinksAt? st' q = replyStackLinksAt? st q := by
          intro q h1 h2 h3
          unfold replyStackLinksAt? SystemState.getObject?
          rw [hFrame' q h1 h2 h3]
        obtain ⟨chain', hWalk'⟩ :=
          (donationChainWalk_exists_of_splice hNeBR hAgreeL hLA hLAPost hLR hLRPost hLB hLBPost
            fuel).1 (.head c) sc.scReply chain hWalk (by rintro ⟨hx, -⟩; cases hx)
        exact ⟨fuel, chain', hWalk'⟩

/-- `v0.35.4`: the cancelled caller's frame splice preserves the chain — the
identity where there is nothing to splice out, one `spliceReplyFrameOut` otherwise. -/
theorem spliceThreadReplyFrameOut_preserves_donationChainWellFormed (st : SystemState)
    (tcb : TCB) (hInv : st.objects.invExt) (hChain : donationChainWellFormed st) :
    donationChainWellFormed (spliceThreadReplyFrameOut st tcb) := by
  rcases spliceThreadReplyFrameOut_cases st tcb with h | ⟨_, _, h⟩
  · rw [h]; exact hChain
  · exact spliceReplyFrameOut_preserves_donationChainWellFormed hInv hChain h

/-- `v0.35.6` (WS-RM): **the fold preserves the chain invariant** — the identity
on a refusal, `spliceReplyFrameOut_preserves_donationChainWellFormed` otherwise. -/
theorem spliceReplyFrameOutOrSelf_preserves_donationChainWellFormed (st : SystemState)
    (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt) (hChain : donationChainWellFormed st) :
    donationChainWellFormed (spliceReplyFrameOutOrSelf st rid) := by
  rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
  · rw [h]; exact hChain
  · exact spliceReplyFrameOut_preserves_donationChainWellFormed hInv hChain h

/-- **WS-RM (`v0.35.6`): after the fold, no stored Reply's `prev` names `rid`.**

This is the producer for the consume's `hUnreferenced` obligation, and it is why
the splice must run **before** the consume rather than beside it: `Reply.consumed`
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
theorem spliceReplyFrameOutOrSelf_unreferenced (st : SystemState)
    (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt) (hChain : donationChainWellFormed st)
    (q : SeLe4n.ReplyId) (rq : Reply)
    (hQ : (spliceReplyFrameOutOrSelf st rid).objects[q.toObjId]? = some (.reply rq)) :
    rq.prev ≠ some rid := by
  intro hPrevQ
  rcases spliceReplyFrameOutOrSelf_decision st rid with
    ⟨r, above, a, hR, hN, hA, hP, hS⟩ | ⟨hId, hNo⟩
  · -- The removal ran.  Under `prevLinkReciprocal` the only frame whose `prev` can
    -- name `rid` is the one `rid`'s own `next` names — the frame above the cut — and
    -- the removal rewrote exactly that `prev`, to `none` on the degenerate branch and
    -- to the frame *below* the cut on the splice.  Neither value is `some rid`,
    -- because the frame below is provably not the cut frame.
    have hAObj : st.objects[above.toObjId]? = some (.reply a) :=
      (SystemState.getReply?_eq_some_iff _ _ _).mp hA
    have hRObj : st.objects[rid.toObjId]? = some (.reply r) :=
      (SystemState.getReply?_eq_some_iff _ _ _).mp hR
    -- Away from the frame above, a frame naming `rid` contradicts `rid`'s own `next`.
    have hAwayFromAbove : ∀ (x : SeLe4n.ReplyId) (rx : Reply), x ≠ above →
        st.objects[x.toObjId]? = some (.reply rx) → rx.prev ≠ some rid := by
      intro x rx hxA hPre hPrevX
      obtain ⟨r0, hR0, hR0next⟩ := hChain.prevLinkReciprocal x rx rid hPre hPrevX
      have hr0 : r0 = r := by
        rw [hRObj] at hR0; exact (KernelObject.reply.inj (Option.some.inj hR0)).symm
      rw [hr0, hN] at hR0next
      exact hxA (ReplyStackLink.frame.inj (Option.some.inj hR0next)).symm
    rcases spliceReplyFrameStores_cases hS with
      ⟨_, hS1⟩ | ⟨below, b, s1, s2, hBelow, hS1, hS2, hS3⟩
    · -- The degenerate branch: one store, clearing the frame above's `prev`.
      by_cases hqA : q = above
      · rw [hqA, storeObject_objects_eq' st _ _ _ hInv hS1] at hQ
        rw [← KernelObject.reply.inj (Option.some.inj hQ)] at hPrevQ
        exact absurd hPrevQ (by simp)
      · refine hAwayFromAbove q rq hqA ?_ hPrevQ
        rw [← storeObject_objects_ne st _ above.toObjId q.toObjId _
          (fun hx => hqA (SeLe4n.ReplyId.toObjId_injective _ _ hx)) hInv hS1]
        exact hQ
    · -- The splice branch: three stores, and none of them writes `some rid`.
      obtain ⟨hAboveVal, hBelowVal, hCutVal, hFrame⟩ :=
        spliceReplyFrameStores_splice_values hInv hR hN hA hP hBelow hS
      obtain ⟨hPrevR, hNeBA, hB, hBN⟩ := spliceFrameBelow?_eq_some hBelow
      have hNeBR : below ≠ rid := spliceFrameBelow?_ne_cut hR hN hBelow
      have hBObj : st.objects[below.toObjId]? = some (.reply b) :=
        (SystemState.getReply?_eq_some_iff _ _ _).mp hB
      by_cases hqA : q = above
      · rw [hqA, (SystemState.getReply?_eq_some_iff _ _ _).mp hAboveVal] at hQ
        rw [← KernelObject.reply.inj (Option.some.inj hQ)] at hPrevQ
        exact hNeBR (Option.some.inj hPrevQ)
      · by_cases hqB : q = below
        · -- The frame below the cut keeps its `prev`, and reciprocity for it would
          -- make `rid`'s `next` name the frame below rather than the frame above.
          rw [hqB, (SystemState.getReply?_eq_some_iff _ _ _).mp hBelowVal] at hQ
          rw [← KernelObject.reply.inj (Option.some.inj hQ)] at hPrevQ
          obtain ⟨r0, hR0, hR0next⟩ := hChain.prevLinkReciprocal below b rid hBObj hPrevQ
          have hr0 : r0 = r := by
            rw [hRObj] at hR0; exact (KernelObject.reply.inj (Option.some.inj hR0)).symm
          rw [hr0, hN] at hR0next
          exact hNeBA (ReplyStackLink.frame.inj (Option.some.inj hR0next)).symm
        · by_cases hqR : q = rid
          · -- The cut frame's own `prev` is what the third store clears.
            rw [hqR, (SystemState.getReply?_eq_some_iff _ _ _).mp hCutVal] at hQ
            rw [← KernelObject.reply.inj (Option.some.inj hQ)] at hPrevQ
            exact absurd hPrevQ (by simp)
          · refine hAwayFromAbove q rq hqA ?_ hPrevQ
            rw [← hFrame q.toObjId (fun hx => hqA (SeLe4n.ReplyId.toObjId_injective _ _ hx))
              (fun hx => hqB (SeLe4n.ReplyId.toObjId_injective _ _ hx))
              (fun hx => hqR (SeLe4n.ReplyId.toObjId_injective _ _ hx))]
            exact hQ
  · -- The fold is the identity, so `q` names `rid` in the pre-state too — and then
    -- reciprocity supplies exactly the shape the removal's validation accepts, which
    -- is what the identity arm says did not hold.
    rw [hId] at hQ
    obtain ⟨r0, hR0, hR0next⟩ := hChain.prevLinkReciprocal q rq rid hQ hPrevQ
    exact hNo r0 q rq ((SystemState.getReply?_eq_some_iff _ _ _).mpr hR0) hR0next
      ((SystemState.getReply?_eq_some_iff _ _ _).mpr hQ) hPrevQ

/-- `v0.35.4`: **after the splice, no frame's `prev` names the cancelled caller's
frame** — the TCB-keyed instance of `spliceReplyFrameOutOrSelf_unreferenced`,
which answers the same question for whichever `ReplyId` the thread holds. -/
theorem spliceThreadReplyFrameOut_unreferenced (st : SystemState) (tcb : TCB)
    (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt) (hChain : donationChainWellFormed st)
    (hRid : tcb.replyObject = some rid) (a : SeLe4n.ReplyId) (ra : Reply)
    (hA : (spliceThreadReplyFrameOut st tcb).objects[a.toObjId]?
      = some (.reply ra)) :
    ra.prev ≠ some rid := by
  refine spliceReplyFrameOutOrSelf_unreferenced st rid hInv hChain a ra ?_
  rw [show spliceReplyFrameOutOrSelf st rid = spliceThreadReplyFrameOut st tcb by
    unfold spliceThreadReplyFrameOut; rw [hRid]]
  exact hA

/-- **WS-RM (`v0.35.6`): the object-store effect of consuming a reply link
preserves the chain**, when the frame heads no context and no frame's `prev`
names it — the two facts a splice run beforehand establishes.

Stated over the *store effect* (`hAt` / `hOther`) rather than over an operation.
When it was written the tree spelled that effect twice — `consumeReply` on the
reply path and a raw-insert twin on the cancellation path — and a chain argument
written against one of them would have had to be written again for the other.
WS-RR RR8.5 deleted the twin (the cancellation path reads `consumeReply` through
`consumeCallerReplyLink` now), and stating the argument over the effect is what
made that deletion a pure removal rather than a re-proof; `consumeReply`'s chain
results cite this.

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

/-- **WS-RR RR8.5**: the same fact stated over the pure projection
`SystemState.consumeCallerReplyLink` — the spelling the cancellation path reads —
so the reply-stack write census holds that site to a chain result of its own
rather than to its monadic twin's. -/
theorem consumeCallerReplyLink_preserves_donationChainWellFormed (st : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt)
    (hChain : donationChainWellFormed st)
    (hNotHead : ∀ (r : Reply) (sc : SeLe4n.SchedContextId),
      st.getReply? rid = some r → r.next ≠ some (.head sc))
    (hUnreferenced : ∀ (a : SeLe4n.ReplyId) (ra : Reply),
      st.objects[a.toObjId]? = some (.reply ra) → ra.prev ≠ some rid) :
    donationChainWellFormed (st.consumeCallerReplyLink caller rid) :=
  consumeCallerReply_preserves_donationChainWellFormed st _ caller rid hInv hChain hNotHead
    hUnreferenced (SystemState.consumeCallerReply_eq_link st caller rid)

/-- `v0.35.4`: **the cancellation's reply-link consume preserves the donation
chain**, under the two facts the splice that precedes it establishes about the
victim's frame.  Since WS-RR RR8.5 the consume *is* the reply path's, so this is
`consumeCallerReplyLink_preserves_donationChainWellFormed` at the victim's own
reply object and nothing more. -/
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
    exact consumeCallerReplyLink_preserves_donationChainWellFormed st tid rid hInv hChain
      (fun r sc hR1 => hNotHead rid r sc hR hR1)
      (fun a ra hA => hUnreferenced rid a ra hR hA)

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

/-- **WS-RR RR8.5**: the head case over the pure projection, for the same reason. -/
theorem consumeCallerReplyLink_head_preserves_donationChainWellFormedExcept
    (st : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (r : Reply) (scId : SeLe4n.SchedContextId) (hInv : st.objects.invExt)
    (hChain : donationChainWellFormed st)
    (hR : st.getReply? rid = some r) (hHead : r.next = some (.head scId)) :
    donationChainWellFormedExcept (st.consumeCallerReplyLink caller rid) rid :=
  consumeCallerReply_head_preserves_donationChainWellFormedExcept st _ caller rid r scId hInv
    hChain hR hHead (SystemState.consumeCallerReply_eq_link st caller rid)

-- ============================================================================
-- WS-RM (`v0.35.6`) — the reply path's removal preserves the chain
-- ============================================================================

/-- **WS-RM (`v0.35.6`): `removeCallerReplyFrame` preserves the chain invariant**
for a frame that heads no context, with **no** side condition beyond `invExt` and
the chain itself.

`hUnreferenced` — the fact the consume needs and cannot establish — is discharged
by the splice that runs first (`spliceReplyFrameOutOrSelf_unreferenced`), on all
three of its arms.  That is the whole reason the removal is a *sequence* rather
than a fold: run the other way round, the consume would clear a non-head frame's
`next` while the frame above still linked down to it, and every later walk to that
frame would refuse (fail-closed) rather than return the context.

`hNotHead` is read on the **pre**-state, which is sound because the splice never
turns a `.frame` link into a `.head` one: it writes the frame above's `prev`, the
frame below's `next` — from one `.frame` to another — and the cut frame's own
`prev`, so no reply's `next` acquires a `.head` link
(`spliceReplyFrameOutOrSelf_preserves_reply_caller_and_headLink`). -/
theorem removeCallerReplyFrame_preserves_donationChainWellFormed (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hInv : st.objects.invExt)
    (hChain : donationChainWellFormed st)
    (hNotHead : ∀ (r : Reply) (sc : SeLe4n.SchedContextId),
      st.getReply? rid = some r → r.next ≠ some (.head sc))
    (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    donationChainWellFormed st' := by
  rw [removeCallerReplyFrame_eq] at hStep
  refine consumeCallerReply_preserves_donationChainWellFormed _ st' caller rid
    (spliceReplyFrameOutOrSelf_preserves_objects_invExt st rid hInv)
    (spliceReplyFrameOutOrSelf_preserves_donationChainWellFormed st rid hInv hChain)
    ?_ (spliceReplyFrameOutOrSelf_unreferenced st rid hInv hChain) hStep
  intro r sc hR
  obtain ⟨rp, hrp, _, hNext⟩ :=
    spliceReplyFrameOutOrSelf_preserves_reply_caller_and_headLink st rid hInv rid r hR
  rcases hNext with hEq | ⟨_, y, _, hqy⟩
  · rw [hEq]; exact hNotHead rp sc hrp
  · rw [hqy]; simp


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
  -- On a head the splice is the identity: a `.head` link names no frame above.
  have hFold : spliceReplyFrameOutOrSelf st rid = st :=
    spliceReplyFrameOutOrSelf_eq_self_of_no_frame_above st rid
      (replyFrameAbove?_of_head st rid r scId hR hHead)
  rw [removeCallerReplyFrame_eq, hFold] at hStep
  exact consumeCallerReply_head_preserves_donationChainWellFormedExcept st st' caller rid r scId
    hInv hChain hR hHead hStep

-- ============================================================================
-- WS-RR RR8.7 — §11  The restore's own bundle preservation
-- ============================================================================

/-! ### Why this step gets its own bundle theorem

The reply arm is four steps, and three of them already carry `ipcInvariantFull`:
the reclaim's abort (`abortPendingIpcOnEndpoint_preserves_ipcInvariantFull`), its
pop (`returnDonatedSchedContext_establishes_ipcInvariantFull_of_except`), the
frame splice (`spliceReplyFrameOut_preserves_ipcInvariantFull`) and the reply-link
teardown (`consumeCallerReply_preserves_ipcInvariantFull`, which WS-RR RR8.5 gave
it when it collapsed the two spellings).  The unblock-and-stage rewrite was the
one link with no bundle result at all, so the arm could not be composed.

It is **not** a third answer to a question the other two cancellation arms
already answer.  Those prove their *composites* — `sweptAndRestored`,
`purgedAndRestored` — and neither composite is separable: on the endpoint arm the
field clear is what repairs the swept thread's own dangling links
(`sweptAndRestored_tcbQueueLinkIntegrity` holds over the composite and not over
the sweep), and on the notification arm the purge leaves the victim
`.blockedOnNotification` with its waiter entry gone until the restore makes it
`.ready`.  The reply arm's four steps *are* separable, because nothing before the
restore needs the restore to repair it, so the restore's own contribution is
statable here and was not there.

Two of the tree's reusable frames are **false** of this step and the conjuncts
they serve are proved directly instead.  `donationOwnerFrame.ownerForward` asks
that an `.unbound` reply-blocked owner still be one afterwards, and
`replyLinkageFrame.pushLinked` asks that a linked `.blockedOnReply` TCB stay
`.blockedOnReply`; this step makes exactly such a thread `.ready`.  What rescues
`donationOwnerValid` is `hNotOwner` — no donation names the restored thread as
its owner — which is the fact the reclaim establishes
(`returnDonationToCancelledCaller_no_donation_to_victim`) and the reason the
reclaim runs first.  What rescues `replyCallerLinkage` is that the step writes
neither `TCB.replyObject` nor `Reply.caller`, so both of its clauses survive: the
reciprocal one reads only untouched fields, and the `.blockedOnReply ⇒
replyObject` one loses its antecedent at the restored thread.
-/

/-- The restore's TCB pullback: away from the restored thread the pre-state's
record **verbatim**, at the restored thread `restoredTcb`.

The counterpart of `purgedAndRestored_tcb_pullback` at the bare rewrite. -/
theorem restoreToReadyStaging_tcb_pullback (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (k : SeLe4n.ObjId) (tA : TCB)
    (h : (Lifecycle.Suspend.restoreToReadyStaging st v frame).objects[k]? = some (.tcb tA)) :
    (k ≠ v.toObjId ∧ st.objects[k]? = some (.tcb tA)) ∨
      (k = v.toObjId ∧ tA = restoredTcb tcbV frame) := by
  have hGet : st.getTcb? v = some tcbV := by
    rw [SystemState.getTcb?_eq_some_iff]; exact lookupTcb_some_objects st v tcbV hLookup
  by_cases hk : k = v.toObjId
  · subst hk
    rw [restoreToReadyStaging_objects_self st v frame tcbV hInv hGet] at h
    exact Or.inr ⟨rfl, (KernelObject.tcb.inj (Option.some.inj h)).symm⟩
  · rw [restoreToReadyStaging_objects_ne st v frame k hInv hk] at h
    exact Or.inl ⟨hk, h⟩

/-- ...and forwards, away from the restored thread. -/
theorem restoreToReadyStaging_tcb_forward (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame)
    (hInv : st.objects.invExt) (k : SeLe4n.ObjId) (t0 : TCB) (hk : k ≠ v.toObjId)
    (h : st.objects[k]? = some (.tcb t0)) :
    (Lifecycle.Suspend.restoreToReadyStaging st v frame).objects[k]? = some (.tcb t0) := by
  rw [restoreToReadyStaging_objects_ne st v frame k hInv hk]; exact h

/-- **The restore writes a TCB and nothing else**, so every reading of an object
of another kind agrees in both directions.

At the restored thread's own key the post-state holds a `.tcb`, and the pre-state
did too (the rewrite is the identity where the lookup fails), so a non-TCB
reading is never at that key. -/
theorem restoreToReadyStaging_nonTcb (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (k : SeLe4n.ObjId) (o : KernelObject) (hNotTcb : ∀ t : TCB, o ≠ .tcb t) :
    ((Lifecycle.Suspend.restoreToReadyStaging st v frame).objects[k]? = some o) ↔
      (st.objects[k]? = some o) := by
  have hGet : st.getTcb? v = some tcbV := by
    rw [SystemState.getTcb?_eq_some_iff]; exact lookupTcb_some_objects st v tcbV hLookup
  by_cases hk : k = v.toObjId
  · subst hk
    constructor
    · intro h
      rw [restoreToReadyStaging_objects_self st v frame tcbV hInv hGet] at h
      exact absurd (Option.some.inj h).symm (hNotTcb _)
    · intro h
      rw [lookupTcb_some_objects st v tcbV hLookup] at h
      exact absurd (Option.some.inj h).symm (hNotTcb _)
  · rw [restoreToReadyStaging_objects_ne st v frame k hInv hk]

/-- **The restore writes no queue link.**  Away from the restored thread the TCB
is the pre-state's; at the restored thread it writes `none` over fields
`sweptThreadOffQueueChains` already says are `none`. -/
theorem restoreToReadyStaging_tcb_links (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hOff : sweptThreadOffQueueChains st v)
    (k : SeLe4n.ObjId) (tA : TCB)
    (h : (Lifecycle.Suspend.restoreToReadyStaging st v frame).objects[k]? = some (.tcb tA)) :
    ∃ t0, st.objects[k]? = some (.tcb t0) ∧
      tA.queuePrev = t0.queuePrev ∧ tA.queueNext = t0.queueNext := by
  rcases restoreToReadyStaging_tcb_pullback st v frame tcbV hInv hLookup k tA h with
    ⟨_, h0⟩ | ⟨hk, rfl⟩
  · exact ⟨tA, h0, rfl, rfl⟩
  · obtain ⟨hp, hn⟩ := hOff tcbV hLookup
    exact ⟨tcbV, by rw [hk]; exact lookupTcb_some_objects st v tcbV hLookup,
      by rw [restoredTcb_queuePrev, hp], by rw [restoredTcb_queueNext, hn]⟩

/-- ...and the reading is an equivalence, so a pre-state link reappears
unchanged. -/
theorem restoreToReadyStaging_tcb_links_forward (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hOff : sweptThreadOffQueueChains st v)
    (k : SeLe4n.ObjId) (t0 : TCB)
    (h : st.objects[k]? = some (.tcb t0)) :
    ∃ tA, (Lifecycle.Suspend.restoreToReadyStaging st v frame).objects[k]? = some (.tcb tA) ∧
      tA.queuePrev = t0.queuePrev ∧ tA.queueNext = t0.queueNext := by
  have hGet : st.getTcb? v = some tcbV := by
    rw [SystemState.getTcb?_eq_some_iff]; exact lookupTcb_some_objects st v tcbV hLookup
  by_cases hk : k = v.toObjId
  · subst hk
    have hx : t0 = tcbV := by
      rw [lookupTcb_some_objects st v tcbV hLookup] at h
      exact (KernelObject.tcb.inj (Option.some.inj h)).symm
    obtain ⟨hp, hn⟩ := hOff tcbV hLookup
    exact ⟨restoredTcb tcbV frame,
      restoreToReadyStaging_objects_self st v frame tcbV hInv hGet,
      by rw [restoredTcb_queuePrev, hx, hp], by rw [restoredTcb_queueNext, hx, hn]⟩
  · exact ⟨t0, restoreToReadyStaging_tcb_forward st v frame hInv k t0 hk h, rfl, rfl⟩

/-- Reachability through the restore is reachability in the pre-state — indeed the
**same** path, no `queueNext` field having moved. -/
theorem restoreToReadyStaging_path_transport (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hOff : sweptThreadOffQueueChains st v)
    {x y : SeLe4n.ThreadId}
    (h : QueueNextPath (Lifecycle.Suspend.restoreToReadyStaging st v frame) x y) :
    QueueNextPath st x y := by
  induction h with
  | single a b tcb hA hN =>
    obtain ⟨t0, h0, _, hn⟩ :=
      restoreToReadyStaging_tcb_links st v frame tcbV hInv hLookup hOff a.toObjId tcb hA
    exact .single a b t0 h0 (by rw [← hn]; exact hN)
  | cons a b c tcb hA hN _ ih =>
    obtain ⟨t0, h0, _, hn⟩ :=
      restoreToReadyStaging_tcb_links st v frame tcbV hInv hLookup hOff a.toObjId tcb hA
    exact .cons a b c t0 h0 (by rw [← hn]; exact hN) ih

/-- The restore preserves the dual-queue system invariant.

Endpoints are untouched (it writes one TCB), no `queueNext` / `queuePrev` field
moves anywhere, so acyclicity transports path for path; and the restored thread's
own `queuePPrev` is cleared, which satisfies the RR8.3 pairing outright. -/
theorem restoreToReadyStaging_dualQueueSystemInvariant (st : SystemState)
    (v : SeLe4n.ThreadId) (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hOff : sweptThreadOffQueueChains st v)
    -- **PR #897 review (`v0.35.106`)**: the strengthened head boundary carries the
    -- head's back-pointer, and the restore clears the restored thread's — so a queue
    -- still naming it as head would be left with a head that has none.  A
    -- `.blockedOnReply` thread bounds no endpoint queue
    -- (`notQueueBlocked_bounds_no_endpoint_queue`), but that is
    -- `queueHeadBlockedConsistent`'s fact rather than this bundle's, so it is stated
    -- here and supplied by the composite.
    (hOffEp : ∀ (k : SeLe4n.ObjId) (e : Endpoint), st.objects[k]? = some (.endpoint e) →
      e.sendQ.head ≠ some v ∧ e.receiveQ.head ≠ some v)
    (hDual : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant (Lifecycle.Suspend.restoreToReadyStaging st v frame) := by
  obtain ⟨hEps, hLink, hAcyc, hPPair, hHD⟩ := hDual
  have hEpIff : ∀ (k : SeLe4n.ObjId) (ep : Endpoint),
      ((Lifecycle.Suspend.restoreToReadyStaging st v frame).objects[k]?
          = some (.endpoint ep)) ↔ (st.objects[k]? = some (.endpoint ep)) :=
    fun k ep => restoreToReadyStaging_nonTcb st v frame tcbV hInv hLookup k (.endpoint ep)
      (by simp)
  have hWF : ∀ (q : IntrusiveQueue), intrusiveQueueWellFormed q st → q.head ≠ some v →
      intrusiveQueueWellFormed q (Lifecycle.Suspend.restoreToReadyStaging st v frame) := by
    intro q hq hqHead
    refine ⟨hq.1, ?_, ?_⟩
    · intro hd hHd
      obtain ⟨t0, h0, hp, hpp⟩ := hq.2.1 hd hHd
      have hNeV : hd.toObjId ≠ v.toObjId := by
        intro hEq
        rw [threadId_toObjId_injective hEq] at hHd
        exact absurd hHd hqHead
      obtain ⟨tA, hA, hpA, _⟩ :=
        restoreToReadyStaging_tcb_links_forward st v frame tcbV hInv hLookup hOff
          hd.toObjId t0 h0
      -- Away from the restored thread the record is the pre-state's verbatim, so
      -- the head's back-pointer carries with the rest of it.
      rcases restoreToReadyStaging_tcb_pullback st v frame tcbV hInv hLookup
          hd.toObjId tA hA with ⟨-, h0'⟩ | ⟨hv, -⟩
      · rw [h0] at h0'
        obtain rfl : tA = t0 := (KernelObject.tcb.inj (Option.some.inj h0')).symm
        exact ⟨tA, hA, hp, hpp⟩
      · exact absurd hv hNeV
    · intro tl hTl
      obtain ⟨t0, h0, hn⟩ := hq.2.2 tl hTl
      obtain ⟨tA, hA, _, hnA⟩ :=
        restoreToReadyStaging_tcb_links_forward st v frame tcbV hInv hLookup hOff
          tl.toObjId t0 h0
      exact ⟨tA, hA, by rw [hnA]; exact hn⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro epId ep hEp
    have hEp0 : st.objects[epId]? = some (.endpoint ep) := (hEpIff epId ep).mp hEp
    have h0 := hEps epId ep hEp0
    unfold dualQueueEndpointWellFormed at h0 ⊢
    rw [hEp0] at h0
    rw [hEp]
    obtain ⟨hNeS, hNeR⟩ := hOffEp epId ep hEp0
    exact ⟨hWF ep.sendQ h0.1 hNeS, hWF ep.receiveQ h0.2 hNeR⟩
  · refine ⟨?_, ?_⟩
    · intro a tcbA hA b hNext
      obtain ⟨t0a, h0a, _, hnA⟩ :=
        restoreToReadyStaging_tcb_links st v frame tcbV hInv hLookup hOff a.toObjId tcbA hA
      obtain ⟨t0b, h0b, hpB⟩ := hLink.1 a t0a h0a b (by rw [← hnA]; exact hNext)
      obtain ⟨tB, hB, hpBA, _⟩ :=
        restoreToReadyStaging_tcb_links_forward st v frame tcbV hInv hLookup hOff
          b.toObjId t0b h0b
      exact ⟨tB, hB, by rw [hpBA]; exact hpB⟩
    · intro b tcbB hB a hPrev
      obtain ⟨t0b, h0b, hpB, _⟩ :=
        restoreToReadyStaging_tcb_links st v frame tcbV hInv hLookup hOff b.toObjId tcbB hB
      obtain ⟨t0a, h0a, hnA⟩ := hLink.2 b t0b h0b a (by rw [← hpB]; exact hPrev)
      obtain ⟨tA, hA, _, hnAA⟩ :=
        restoreToReadyStaging_tcb_links_forward st v frame tcbV hInv hLookup hOff
          a.toObjId t0a h0a
      exact ⟨tA, hA, by rw [hnAA]; exact hnA⟩
  · exact fun x hPath => hAcyc x
      (restoreToReadyStaging_path_transport st v frame tcbV hInv hLookup hOff hPath)
  · intro tid tcb hTcb
    rcases restoreToReadyStaging_tcb_pullback st v frame tcbV hInv hLookup
      tid.toObjId tcb hTcb with ⟨_, h0⟩ | ⟨_, rfl⟩
    · exact hPPair tid tcb h0
    · -- `v0.35.99`: both back-pointers, the restore clearing each.
      exact TCB.queuePPrevAgreesWithPrev_of_pprev_none (restoredTcb_queuePPrev tcbV frame)
        (restoredTcb_queuePrev tcbV frame)
  · -- **PR #897 review**: the restore writes one TCB, so no endpoint moves and the
    -- fifth conjunct transports.
    exact endpointQueueHeadDisjoint_of_endpointBackward
      (fun epId ep hEp => (hEpIff epId ep).mp hEp) hHD

/-- The restore frames the timeout budget: it writes no `timeoutBudget`. -/
theorem restoreToReadyStaging_timeoutBudgetFrame (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV) :
    timeoutBudgetFrame st (Lifecycle.Suspend.restoreToReadyStaging st v frame) := by
  intro tid tcb' hTcb'
  rcases restoreToReadyStaging_tcb_pullback st v frame tcbV hInv hLookup
    tid.toObjId tcb' hTcb' with ⟨_, h0⟩ | ⟨hk, rfl⟩
  · exact ⟨tcb', h0, rfl⟩
  · exact ⟨tcbV, by rw [hk]; exact lookupTcb_some_objects st v tcbV hLookup,
      by rw [restoredTcb_eq]⟩

theorem restoreToReadyStaging_allPendingMessagesBounded (st : SystemState)
    (v : SeLe4n.ThreadId) (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (h : allPendingMessagesBounded st) :
    allPendingMessagesBounded (Lifecycle.Suspend.restoreToReadyStaging st v frame) := by
  intro tid tcb' msg hTcb' hMsg
  rcases restoreToReadyStaging_tcb_pullback st v frame tcbV hInv hLookup
    tid.toObjId tcb' hTcb' with ⟨_, h0⟩ | ⟨hk, rfl⟩
  · exact h tid tcb' msg h0 hMsg
  · exact h tid tcbV msg (by rw [hk]; exact lookupTcb_some_objects st v tcbV hLookup)
      (by rw [restoredTcb_eq] at hMsg; exact hMsg)

theorem restoreToReadyStaging_badgeWellFormed (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (h : badgeWellFormed st) :
    badgeWellFormed (Lifecycle.Suspend.restoreToReadyStaging st v frame) := by
  refine ⟨?_, ?_⟩
  · intro oid ntfn badge hN hB
    exact h.1 oid ntfn badge
      ((restoreToReadyStaging_nonTcb st v frame tcbV hInv hLookup oid (.notification ntfn)
        (by simp)).mp hN) hB
  · intro oid cn slot cap badge hC hL hB
    exact h.2 oid cn slot cap badge
      ((restoreToReadyStaging_nonTcb st v frame tcbV hInv hLookup oid (.cnode cn)
        (by simp)).mp hC) hL hB

theorem restoreToReadyStaging_blockedThreadsPendingMessageConsistent (st : SystemState)
    (v : SeLe4n.ThreadId) (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (h : blockedThreadsPendingMessageConsistent st) :
    blockedThreadsPendingMessageConsistent
      (Lifecycle.Suspend.restoreToReadyStaging st v frame) := by
  intro tid tcb' hTcb'
  rcases restoreToReadyStaging_tcb_pullback st v frame tcbV hInv hLookup
    tid.toObjId tcb' hTcb' with ⟨_, h0⟩ | ⟨_, rfl⟩
  · exact h tid tcb' h0
  · rw [restoredTcb_eq]
    simp only

theorem restoreToReadyStaging_blockedOnReplyHasTarget (st : SystemState)
    (v : SeLe4n.ThreadId) (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (h : blockedOnReplyHasTarget st) :
    blockedOnReplyHasTarget (Lifecycle.Suspend.restoreToReadyStaging st v frame) := by
  intro tid tcb' epId rt hTcb' hBlocked
  rcases restoreToReadyStaging_tcb_pullback st v frame tcbV hInv hLookup
    tid.toObjId tcb' hTcb' with ⟨_, h0⟩ | ⟨_, rfl⟩
  · exact h tid tcb' epId rt h0 hBlocked
  · rw [restoredTcb_ipcState] at hBlocked
    cases hBlocked

theorem restoreToReadyStaging_donationChainAcyclic (st : SystemState)
    (v : SeLe4n.ThreadId) (frame : Option Architecture.SyscallReturnFrame)
    (hInv : st.objects.invExt) (h : donationChainAcyclic st) :
    donationChainAcyclic (Lifecycle.Suspend.restoreToReadyStaging st v frame) := by
  have hBind := restoreToReadyStaging_sameSchedContextBindings st v frame hInv
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 h1 h2 hB1 hB2
  obtain ⟨tc1, hP1, hEq1⟩ := hBind tid1 tcb1 h1
  obtain ⟨tc2, hP2, hEq2⟩ := hBind tid2 tcb2 h2
  exact h tid1 tid2 tc1 tc2 scId1 scId2 hP1 hP2
    (by rw [hEq1]; exact hB1) (by rw [hEq2]; exact hB2)

theorem restoreToReadyStaging_pendingReceiveReplyWellFormed (st : SystemState)
    (v : SeLe4n.ThreadId) (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (h : pendingReceiveReplyWellFormed st) :
    pendingReceiveReplyWellFormed (Lifecycle.Suspend.restoreToReadyStaging st v frame) := by
  have hPull : ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB) (rid : SeLe4n.ReplyId),
      (Lifecycle.Suspend.restoreToReadyStaging st v frame).getTcb? tid = some tcb' →
      tcb'.pendingReceiveReply = some rid → st.getTcb? tid = some tcb' := by
    intro tid tcb' rid hTcb' hStash
    have hObj : (Lifecycle.Suspend.restoreToReadyStaging st v frame).objects[tid.toObjId]?
        = some (.tcb tcb') := (SystemState.getTcb?_eq_some_iff _ tid tcb').mp hTcb'
    rcases restoreToReadyStaging_tcb_pullback st v frame tcbV hInv hLookup
      tid.toObjId tcb' hObj with ⟨_, h0⟩ | ⟨_, rfl⟩
    · exact (SystemState.getTcb?_eq_some_iff _ tid tcb').mpr h0
    · rw [restoredTcb_pendingReceiveReply] at hStash
      cases hStash
  refine ⟨?_, ?_⟩
  · intro tid tcb' rid hTcb' hStash
    obtain ⟨hEp, r, hr, hrc⟩ := h.1 tid tcb' rid (hPull tid tcb' rid hTcb' hStash) hStash
    refine ⟨hEp, r, ?_, hrc⟩
    exact (SystemState.getReply?_eq_some_iff _ rid r).mpr
      ((restoreToReadyStaging_nonTcb st v frame tcbV hInv hLookup rid.toObjId (.reply r)
        (by simp)).mpr ((SystemState.getReply?_eq_some_iff st rid r).mp hr))
  · intro tid₁ tid₂ tcb₁ tcb₂ rid h1 h2 hs1 hs2
    exact h.2 tid₁ tid₂ tcb₁ tcb₂ rid (hPull tid₁ tcb₁ rid h1 hs1)
      (hPull tid₂ tcb₂ rid h2 hs2) hs1 hs2

/-- No `queueNext` edge in the restored state touches the restored thread: it
points at nothing (the restore cleared its link) and nothing points at it (link
integrity would give it a `queuePrev`, which `sweptThreadOffQueueChains`
denies). -/
theorem restoreToReadyStaging_edge_avoids_victim (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hLink : tcbQueueLinkIntegrity st) (hOff : sweptThreadOffQueueChains st v)
    (a b : SeLe4n.ThreadId) (tcbA : TCB)
    (hA : (Lifecycle.Suspend.restoreToReadyStaging st v frame).objects[a.toObjId]?
      = some (.tcb tcbA))
    (hNext : tcbA.queueNext = some b) :
    a.toObjId ≠ v.toObjId ∧ b.toObjId ≠ v.toObjId := by
  obtain ⟨hp, hn⟩ := hOff tcbV hLookup
  have hGet : st.getTcb? v = some tcbV := by
    rw [SystemState.getTcb?_eq_some_iff]; exact lookupTcb_some_objects st v tcbV hLookup
  have hav : a.toObjId ≠ v.toObjId := by
    intro hEq
    rw [hEq, restoreToReadyStaging_objects_self st v frame tcbV hInv hGet] at hA
    have hx : tcbA = restoredTcb tcbV frame := (KernelObject.tcb.inj (Option.some.inj hA)).symm
    rw [hx, restoredTcb_queueNext] at hNext
    cases hNext
  refine ⟨hav, ?_⟩
  intro hEq
  obtain ⟨t0, h0, _, hnA⟩ :=
    restoreToReadyStaging_tcb_links st v frame tcbV hInv hLookup hOff a.toObjId tcbA hA
  obtain ⟨tB, hB, hpB⟩ := hLink.1 a t0 h0 b (by rw [← hnA]; exact hNext)
  rw [hEq, lookupTcb_some_objects st v tcbV hLookup] at hB
  have hy : tB = tcbV := (KernelObject.tcb.inj (Option.some.inj hB)).symm
  rw [hy, hp] at hpB
  cases hpB

theorem restoreToReadyStaging_queueNextTargetBlocked (st : SystemState)
    (v : SeLe4n.ThreadId) (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hLink : tcbQueueLinkIntegrity st) (hOff : sweptThreadOffQueueChains st v)
    (hTgt : queueNextTargetBlocked st) :
    queueNextTargetBlocked (Lifecycle.Suspend.restoreToReadyStaging st v frame) := by
  intro a b tcbA tcbB hA hB hNext
  obtain ⟨hav, hbv⟩ := restoreToReadyStaging_edge_avoids_victim st v frame tcbV hInv hLookup
    hLink hOff a b tcbA hA hNext
  rcases restoreToReadyStaging_tcb_pullback st v frame tcbV hInv hLookup
    a.toObjId tcbA hA with ⟨_, h0a⟩ | ⟨hk, _⟩
  · rcases restoreToReadyStaging_tcb_pullback st v frame tcbV hInv hLookup
      b.toObjId tcbB hB with ⟨_, h0b⟩ | ⟨hk, _⟩
    · exact hTgt a b tcbA tcbB h0a h0b hNext
    · exact absurd hk hbv
  · exact absurd hk hav

theorem restoreToReadyStaging_queueNextBlockingConsistent (st : SystemState)
    (v : SeLe4n.ThreadId) (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hLink : tcbQueueLinkIntegrity st) (hOff : sweptThreadOffQueueChains st v)
    (hQNB : queueNextBlockingConsistent st) :
    queueNextBlockingConsistent (Lifecycle.Suspend.restoreToReadyStaging st v frame) := by
  intro a b tcbA tcbB hA hB hNext
  obtain ⟨hav, hbv⟩ := restoreToReadyStaging_edge_avoids_victim st v frame tcbV hInv hLookup
    hLink hOff a b tcbA hA hNext
  rcases restoreToReadyStaging_tcb_pullback st v frame tcbV hInv hLookup
    a.toObjId tcbA hA with ⟨_, h0a⟩ | ⟨hk, _⟩
  · rcases restoreToReadyStaging_tcb_pullback st v frame tcbV hInv hLookup
      b.toObjId tcbB hB with ⟨_, h0b⟩ | ⟨hk, _⟩
    · exact hQNB a b tcbA tcbB h0a h0b hNext
    · exact absurd hk hbv
  · exact absurd hk hav

theorem restoreToReadyStaging_endpointQueueNoDup (st : SystemState)
    (v : SeLe4n.ThreadId) (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hLink : tcbQueueLinkIntegrity st) (hOff : sweptThreadOffQueueChains st v)
    (hNoDup : endpointQueueNoDup st) :
    endpointQueueNoDup (Lifecycle.Suspend.restoreToReadyStaging st v frame) := by
  intro oid ep hEp
  have hEp0 : st.objects[oid]? = some (.endpoint ep) :=
    (restoreToReadyStaging_nonTcb st v frame tcbV hInv hLookup oid (.endpoint ep)
      (by simp)).mp hEp
  refine ⟨?_, (hNoDup oid ep hEp0).2⟩
  intro tid tcb hTcb hSelf
  obtain ⟨hav, _⟩ := restoreToReadyStaging_edge_avoids_victim st v frame tcbV hInv hLookup
    hLink hOff tid tid tcb hTcb hSelf
  rcases restoreToReadyStaging_tcb_pullback st v frame tcbV hInv hLookup
    tid.toObjId tcb hTcb with ⟨_, h0⟩ | ⟨hk, _⟩
  · exact (hNoDup oid ep hEp0).1 tid tcb h0 hSelf
  · exact absurd hk hav

theorem restoreToReadyStaging_ipcStateQueueMembershipConsistent (st : SystemState)
    (v : SeLe4n.ThreadId) (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hOff : sweptThreadOffQueueChains st v)
    (hMem : ipcStateQueueMembershipConsistent st) :
    ipcStateQueueMembershipConsistent
      (Lifecycle.Suspend.restoreToReadyStaging st v frame) := by
  obtain ⟨_, hvn⟩ := hOff tcbV hLookup
  intro tid tcb' hTcb'
  rcases restoreToReadyStaging_tcb_pullback st v frame tcbV hInv hLookup
    tid.toObjId tcb' hTcb' with ⟨_, h0⟩ | ⟨_, rfl⟩
  · have hPre := hMem tid tcb' h0
    have hFwd : ∀ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
        st.objects[prev.toObjId]? = some (.tcb prevTcb) → TCB.queueNext prevTcb = some tid →
        ∃ (p : SeLe4n.ThreadId) (pTcb : TCB),
          (Lifecycle.Suspend.restoreToReadyStaging st v frame).objects[p.toObjId]?
            = some (.tcb pTcb) ∧ TCB.queueNext pTcb = some tid := by
      intro prev prevTcb hPrev hPN
      have hpv : prev.toObjId ≠ v.toObjId := by
        intro hEq
        rw [hEq, lookupTcb_some_objects st v tcbV hLookup] at hPrev
        have hx : prevTcb = tcbV := (KernelObject.tcb.inj (Option.some.inj hPrev)).symm
        rw [hx, hvn] at hPN
        cases hPN
      exact ⟨prev, prevTcb,
        restoreToReadyStaging_tcb_forward st v frame hInv prev.toObjId prevTcb hpv hPrev, hPN⟩
    cases hI : tcb'.ipcState with
    | blockedOnSend epId =>
      rw [hI] at hPre
      obtain ⟨ep, hEp, hW⟩ := hPre
      refine ⟨ep, (restoreToReadyStaging_nonTcb st v frame tcbV hInv hLookup epId
        (.endpoint ep) (by simp)).mpr hEp, ?_⟩
      rcases hW with hHd | ⟨prev, prevTcb, hPrev, hPN⟩
      · exact Or.inl hHd
      · exact Or.inr (hFwd prev prevTcb hPrev hPN)
    | blockedOnCall epId =>
      rw [hI] at hPre
      obtain ⟨ep, hEp, hW⟩ := hPre
      refine ⟨ep, (restoreToReadyStaging_nonTcb st v frame tcbV hInv hLookup epId
        (.endpoint ep) (by simp)).mpr hEp, ?_⟩
      rcases hW with hHd | ⟨prev, prevTcb, hPrev, hPN⟩
      · exact Or.inl hHd
      · exact Or.inr (hFwd prev prevTcb hPrev hPN)
    | blockedOnReceive epId =>
      rw [hI] at hPre
      obtain ⟨ep, hEp, hW⟩ := hPre
      refine ⟨ep, (restoreToReadyStaging_nonTcb st v frame tcbV hInv hLookup epId
        (.endpoint ep) (by simp)).mpr hEp, ?_⟩
      rcases hW with hHd | ⟨prev, prevTcb, hPrev, hPN⟩
      · exact Or.inl hHd
      · exact Or.inr (hFwd prev prevTcb hPrev hPN)
    | _ => trivial
  · rw [restoredTcb_ipcState]
    trivial

theorem restoreToReadyStaging_queueHeadBlockedConsistent (st : SystemState)
    (v : SeLe4n.ThreadId) (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (epV : SeLe4n.ObjId) (rtV : Option SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hBlocked : tcbV.ipcState = .blockedOnReply epV rtV)
    (hHead : queueHeadBlockedConsistent st)
    (hTail : endpointQueueTailBlockedConsistent st) :
    queueHeadBlockedConsistent (Lifecycle.Suspend.restoreToReadyStaging st v frame) := by
  intro epId ep hd tcbHd hEp hHd
  have hEp0 : st.objects[epId]? = some (.endpoint ep) :=
    (restoreToReadyStaging_nonTcb st v frame tcbV hInv hLookup epId (.endpoint ep)
      (by simp)).mp hEp
  obtain ⟨hSH, hRH, _, _⟩ := notQueueBlocked_bounds_no_endpoint_queue st v tcbV hLookup
    (fun _ h => by rw [hBlocked] at h; cases h)
    (fun _ h => by rw [hBlocked] at h; cases h)
    (fun _ h => by rw [hBlocked] at h; cases h) hHead hTail epId ep hEp0
  constructor
  · intro hx
    have hdv : hd.toObjId ≠ v.toObjId := fun hEq =>
      hRH (hx.trans (congrArg some (SeLe4n.ThreadId.toObjId_injective _ _ hEq)))
    rcases restoreToReadyStaging_tcb_pullback st v frame tcbV hInv hLookup
      hd.toObjId tcbHd hHd with ⟨_, h0⟩ | ⟨hk, _⟩
    · exact (hHead epId ep hd tcbHd hEp0 h0).1 hx
    · exact absurd hk hdv
  · intro hx
    have hdv : hd.toObjId ≠ v.toObjId := fun hEq =>
      hSH (hx.trans (congrArg some (SeLe4n.ThreadId.toObjId_injective _ _ hEq)))
    rcases restoreToReadyStaging_tcb_pullback st v frame tcbV hInv hLookup
      hd.toObjId tcbHd hHd with ⟨_, h0⟩ | ⟨hk, _⟩
    · exact (hHead epId ep hd tcbHd hEp0 h0).2 hx
    · exact absurd hk hdv

theorem restoreToReadyStaging_endpointQueueTailBlockedConsistent (st : SystemState)
    (v : SeLe4n.ThreadId) (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (epV : SeLe4n.ObjId) (rtV : Option SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hBlocked : tcbV.ipcState = .blockedOnReply epV rtV)
    (hHead : queueHeadBlockedConsistent st)
    (hTail : endpointQueueTailBlockedConsistent st) :
    endpointQueueTailBlockedConsistent
      (Lifecycle.Suspend.restoreToReadyStaging st v frame) := by
  intro epId ep tl tcbTl hEp hTl
  have hEp0 : st.objects[epId]? = some (.endpoint ep) :=
    (restoreToReadyStaging_nonTcb st v frame tcbV hInv hLookup epId (.endpoint ep)
      (by simp)).mp hEp
  obtain ⟨_, _, hST, hRT⟩ := notQueueBlocked_bounds_no_endpoint_queue st v tcbV hLookup
    (fun _ h => by rw [hBlocked] at h; cases h)
    (fun _ h => by rw [hBlocked] at h; cases h)
    (fun _ h => by rw [hBlocked] at h; cases h) hHead hTail epId ep hEp0
  constructor
  · intro hx
    have htv : tl.toObjId ≠ v.toObjId := fun hEq =>
      hRT (hx.trans (congrArg some (SeLe4n.ThreadId.toObjId_injective _ _ hEq)))
    rcases restoreToReadyStaging_tcb_pullback st v frame tcbV hInv hLookup
      tl.toObjId tcbTl hTl with ⟨_, h0⟩ | ⟨hk, _⟩
    · exact (hTail epId ep tl tcbTl hEp0 h0).1 hx
    · exact absurd hk htv
  · intro hx
    have htv : tl.toObjId ≠ v.toObjId := fun hEq =>
      hST (hx.trans (congrArg some (SeLe4n.ThreadId.toObjId_injective _ _ hEq)))
    rcases restoreToReadyStaging_tcb_pullback st v frame tcbV hInv hLookup
      tl.toObjId tcbTl hTl with ⟨_, h0⟩ | ⟨hk, _⟩
    · exact (hTail epId ep tl tcbTl hEp0 h0).2 hx
    · exact absurd hk htv

/-- **The restore's donation-owner conjunct, and the one hypothesis it needs.**

Making a thread `.ready` breaks `donationOwnerValid` at any donation that names it
as owner, because the conjunct requires an owner to be reply-blocked.  What rules
that out is `hNotOwner`, which is exactly what the reclaim establishes
(`returnDonationToCancelledCaller_no_donation_to_victim`) and the reason the
reclaim runs before the restore. -/
theorem restoreToReadyStaging_donationOwnerValid (st : SystemState)
    (v : SeLe4n.ThreadId) (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hNotOwner : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId),
      st.objects[tid.toObjId]? = some (.tcb tcb) → tcb.schedContextBinding ≠ .donated scId v)
    (h : donationOwnerValid st) :
    donationOwnerValid (Lifecycle.Suspend.restoreToReadyStaging st v frame) := by
  intro tid tcb scId owner hTcb hBind
  obtain ⟨t0, h0, hEq⟩ :=
    restoreToReadyStaging_sameSchedContextBindings st v frame hInv tid tcb hTcb
  obtain ⟨⟨sc, hSc, hBound⟩, oTcb, hO, hUnb, hBlk⟩ :=
    h tid t0 scId owner h0 (hEq.trans hBind)
  have hOv : owner.toObjId ≠ v.toObjId := by
    intro hEqO
    exact hNotOwner tid t0 scId h0
      (by rw [hEq.trans hBind, SeLe4n.ThreadId.toObjId_injective _ _ hEqO])
  refine ⟨⟨sc, (restoreToReadyStaging_nonTcb st v frame tcbV hInv hLookup
    scId.toObjId (.schedContext sc) (by simp)).mpr hSc, hBound⟩, oTcb,
    restoreToReadyStaging_tcb_forward st v frame hInv owner.toObjId oTcb hOv hO,
    hUnb, hBlk⟩

/-- **The restore's reply linkage, relaxed at the thread it wakes.**

Clause 1 and the third clause survive outright: the step writes neither
`TCB.replyObject` nor any `Reply`, and the woken thread's `.blockedOnReply`
antecedent is gone.  Clause 2 is where the relaxation is spent — the woken
thread's Reply still names it — and the pair is still required to exist. -/
theorem restoreToReadyStaging_replyCallerLinkageExcept (st : SystemState)
    (v : SeLe4n.ThreadId) (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (h : replyCallerLinkage st) :
    replyCallerLinkageExcept (Lifecycle.Suspend.restoreToReadyStaging st v frame) v := by
  have hVObj : st.objects[v.toObjId]? = some (.tcb tcbV) :=
    lookupTcb_some_objects st v tcbV hLookup
  have hRep : ∀ (rid : SeLe4n.ReplyId) (r : Reply),
      ((Lifecycle.Suspend.restoreToReadyStaging st v frame).objects[rid.toObjId]?
          = some (.reply r)) ↔ (st.objects[rid.toObjId]? = some (.reply r)) :=
    fun rid r => restoreToReadyStaging_nonTcb st v frame tcbV hInv hLookup
      rid.toObjId (.reply r) (by simp)
  refine ⟨?_, ?_, ?_⟩
  · intro tid tcb' rid hTcb' hRO
    rcases restoreToReadyStaging_tcb_pullback st v frame tcbV hInv hLookup
      tid.toObjId tcb' hTcb' with ⟨_, h0⟩ | ⟨hk, rfl⟩
    · obtain ⟨r, hr, hrc⟩ := h.1.1 tid tcb' rid h0 hRO
      exact ⟨r, (hRep rid r).mpr hr, hrc⟩
    · have hidv : tid = v := SeLe4n.ThreadId.toObjId_injective _ _ hk
      subst hidv
      rw [restoredTcb_replyObject] at hRO
      obtain ⟨r, hr, hrc⟩ := h.1.1 tid tcbV rid hVObj hRO
      exact ⟨r, (hRep rid r).mpr hr, hrc⟩
  · intro rid r tid hr hrc
    obtain ⟨t0, h0, hRO, ep, rt, hBlk⟩ := h.1.2 rid r tid ((hRep rid r).mp hr) hrc
    by_cases hidv : tid = v
    · subst hidv
      refine ⟨restoredTcb tcbV frame, ?_, ?_, Or.inl rfl⟩
      · exact restoreToReadyStaging_objects_self st tid frame tcbV hInv
          (by rw [SystemState.getTcb?_eq_some_iff]; exact hVObj)
      · have hx : t0 = tcbV := by
          rw [hVObj] at h0; exact (KernelObject.tcb.inj (Option.some.inj h0)).symm
        rw [hx] at hRO
        rw [restoredTcb_replyObject]; exact hRO
    · have hne : tid.toObjId ≠ v.toObjId := fun hEq =>
        hidv (SeLe4n.ThreadId.toObjId_injective _ _ hEq)
      exact ⟨t0, restoreToReadyStaging_tcb_forward st v frame hInv tid.toObjId t0 hne h0,
        hRO, Or.inr ⟨ep, rt, hBlk⟩⟩
  · intro tid tcb' ep rt hTcb' hBlk
    rcases restoreToReadyStaging_tcb_pullback st v frame tcbV hInv hLookup
      tid.toObjId tcb' hTcb' with ⟨_, h0⟩ | ⟨_, rfl⟩
    · exact h.2 tid tcb' ep rt h0 hBlk
    · rw [restoredTcb_ipcState] at hBlk
      cases hBlk

/-- **WS-RR RR8.7 — the restore's keystone**: the unblock-and-stage rewrite
establishes `ipcInvariantFull` with the reply linkage relaxed at the thread it
wakes.

Four hypotheses beyond the bundle, and each is a fact about a different way the
step could break a conjunct.  `hAllBudgetsNone` is the one both other cancellation
arms take, for the same reason: the timeout conjunct says a budget-carrying thread
is blocked and this step makes one `.ready`.  `hOff` is the queue-coherence fact —
the step clears the woken thread's links with nothing to repair a neighbour, and
`ipcInvariantFull` carries no connectivity.  `hNotOwner` is what the reclaim
establishes.  And the blocking state is what puts the thread off every endpoint
queue boundary.

The one conjunct it cannot carry is the sixteenth, which is why the conclusion is
the relaxed bundle: see `ipcInvariantFullExceptReplyLinkage`. -/
theorem restoreToReadyStaging_establishes_ipcInvariantFullExceptReplyLinkage
    (st : SystemState) (v : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (tcbV : TCB)
    (epV : SeLe4n.ObjId) (rtV : Option SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hBlocked : tcbV.ipcState = .blockedOnReply epV rtV)
    (hBundle : ipcInvariantFull st)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hOff : sweptThreadOffQueueChains st v)
    (hNotOwner : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId),
      st.objects[tid.toObjId]? = some (.tcb tcb) → tcb.schedContextBinding ≠ .donated scId v) :
    ipcInvariantFullExceptReplyLinkage
      (Lifecycle.Suspend.restoreToReadyStaging st v frame) v := by
  obtain ⟨hIpc, hDual, hBnd, hBadge, hBlkMsg, hNoDup, hMem, hQNB, hQHB, _hTimeout,
    hDonAcyc, hDonOwner, hPassive, hDonBudget, hBlkReply, hReplyLink, hStash,
    hDonUnique, hTailBlk, hTgt⟩ := hBundle
  have hLink : tcbQueueLinkIntegrity st := hDual.2.1
  have hBind := restoreToReadyStaging_sameSchedContextBindings st v frame hInv
  exact ⟨Lifecycle.Suspend.restoreToReadyStaging_preserves_ipcInvariant st v frame hInv hIpc,
    restoreToReadyStaging_dualQueueSystemInvariant st v frame tcbV hInv hLookup hOff
      (fun k e hE =>
        let o := notQueueBlocked_bounds_no_endpoint_queue st v tcbV hLookup
          (fun _ h => by rw [hBlocked] at h; cases h)
          (fun _ h => by rw [hBlocked] at h; cases h)
          (fun _ h => by rw [hBlocked] at h; cases h)
          hQHB hTailBlk k e hE
        ⟨o.1, o.2.1⟩) hDual,
    restoreToReadyStaging_allPendingMessagesBounded st v frame tcbV hInv hLookup hBnd,
    restoreToReadyStaging_badgeWellFormed st v frame tcbV hInv hLookup hBadge,
    restoreToReadyStaging_blockedThreadsPendingMessageConsistent st v frame tcbV hInv
      hLookup hBlkMsg,
    restoreToReadyStaging_endpointQueueNoDup st v frame tcbV hInv hLookup hLink hOff hNoDup,
    restoreToReadyStaging_ipcStateQueueMembershipConsistent st v frame tcbV hInv hLookup
      hOff hMem,
    restoreToReadyStaging_queueNextBlockingConsistent st v frame tcbV hInv hLookup hLink
      hOff hQNB,
    restoreToReadyStaging_queueHeadBlockedConsistent st v frame tcbV epV rtV hInv hLookup
      hBlocked hQHB hTailBlk,
    blockedThreadTimeoutConsistent_of_frame
      (restoreToReadyStaging_timeoutBudgetFrame st v frame tcbV hInv hLookup) hAllBudgetsNone,
    restoreToReadyStaging_donationChainAcyclic st v frame hInv hDonAcyc,
    restoreToReadyStaging_donationOwnerValid st v frame tcbV hInv hLookup hNotOwner hDonOwner,
    passiveServerIdle_of_frame
      (restoreToReadyStaging_passiveServerIdleFrame st v frame hInv) hPassive,
    donationBudgetTransfer_of_sameSchedContextBindings hBind hDonBudget,
    restoreToReadyStaging_blockedOnReplyHasTarget st v frame tcbV hInv hLookup hBlkReply,
    restoreToReadyStaging_replyCallerLinkageExcept st v frame tcbV hInv hLookup hReplyLink,
    restoreToReadyStaging_pendingReceiveReplyWellFormed st v frame tcbV hInv hLookup hStash,
    donationOwnerUnique_of_sameSchedContextBindings hBind hDonUnique,
    restoreToReadyStaging_endpointQueueTailBlockedConsistent st v frame tcbV epV rtV hInv
      hLookup hBlocked hQHB hTailBlk,
    restoreToReadyStaging_queueNextTargetBlocked st v frame tcbV hInv hLookup hLink hOff hTgt⟩

/-- **WS-RR RR8.7 — the teardown closes the relaxation it was opened for.**

`consumeReplyLink` is the other half of the pair: the restore opens the relaxation
by waking the caller, and this step closes it by clearing both sides of that
caller's reply link.  Stated over the *relaxed* bundle, which is what the restore
leaves and what the full bundle provably is not.

The two arms close it differently.  With a reply object the step is the reply
path's own consume, and the relaxed clause 1 at the woken thread supplies the
`caller` link that theorem needs.  With none the step is the identity, and the
relaxed clause 2 is what says no Reply names the thread at all — a Reply that did
would force the thread's single `replyObject` to name it. -/
theorem consumeReplyLink_closes_exceptReplyLinkage (st : SystemState)
    (v : SeLe4n.ThreadId) (tcb tcbSt : TCB)
    (hInv : st.objects.invExt)
    (hStore : st.objects[v.toObjId]? = some (.tcb tcbSt))
    (hAgree : tcbSt.replyObject = tcb.replyObject)
    (hWoken : ∀ (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId),
      tcbSt.ipcState ≠ .blockedOnReply ep rt)
    (hExcept : ipcInvariantFullExceptReplyLinkage st v) :
    ipcInvariantFull (Lifecycle.Suspend.consumeReplyLink st v tcb) := by
  have hRecip := hExcept.replyCallerLinkageExcept
  -- A Reply naming `v` forces `v`'s stored `replyObject` to name it back.
  have hNames : ∀ (rid : SeLe4n.ReplyId) (r : Reply),
      st.objects[rid.toObjId]? = some (.reply r) → r.caller = some v →
      tcbSt.replyObject = some rid := by
    intro rid r hr hc
    obtain ⟨t, ht, htr, _⟩ := hRecip.2.1 rid r v hr hc
    rw [hStore] at ht
    rw [(KernelObject.tcb.inj (Option.some.inj ht)).symm] at htr
    exact htr
  cases hR : tcb.replyObject with
  | none =>
    rw [Lifecycle.Suspend.consumeReplyLink_none st v tcb hR]
    refine ipcInvariantFull_of_exceptReplyLinkage hExcept
      (replyCallerLinkage_of_except_of_unreferenced hRecip ?_)
    intro rid r hr hc
    have hStRid : tcbSt.replyObject = some rid := hNames rid r hr hc
    rw [hAgree, hR] at hStRid
    cases hStRid
  | some rid =>
    rw [Lifecycle.Suspend.consumeReplyLink_some st v tcb rid hR]
    have hStRid : tcbSt.replyObject = some rid := by rw [hAgree, hR]
    obtain ⟨r0, hr0, hc0⟩ := hRecip.1 v tcbSt rid hStore hStRid
    exact consumeCallerReply_establishes_ipcInvariantFull_of_exceptReplyLinkage st _ v rid r0
      hExcept hInv ((SystemState.getReply?_eq_some_iff st rid r0).mpr hr0) hc0
      (fun t ht ep rt => by
        rw [hStore] at ht
        rw [(KernelObject.tcb.inj (Option.some.inj ht)).symm]
        exact hWoken ep rt)
      (SystemState.consumeCallerReply_eq_link st v rid)

/-- **WS-RR RR8.7 — the reply arm's teardown pair.**

The cancellation's reply arm ends in the unblock-and-stage rewrite followed by the
reply-link teardown, and this is that pair: `restoreToReadyCancelled` then
`consumeReplyLink`, at the victim's own reply object.

**The pair is the unit the bundle is about, and neither step is.**  The restore
alone leaves a woken caller whose Reply still names it, which
`replyCallerLinkageReciprocal` forbids, and the teardown alone would clear a
still-blocked caller's reply object, which the third clause forbids.  Run in this
order they are each other's repair, so the pair carries all twenty conjuncts while
the two halves carry nineteen and a relaxation between them. -/
def restoredAndConsumed (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB)
    (frame : Option Architecture.SyscallReturnFrame) : SystemState :=
  Lifecycle.Suspend.consumeReplyLink
    (Lifecycle.Suspend.restoreToReadyStaging st v frame) v tcbV

/-- **WS-RR RR8.7 — the teardown pair's keystone**: it preserves `ipcInvariantFull`.

The hypotheses are the restore's: the victim resolves and is reply-blocked, the
timeout-budget discipline, this arm's queue-coherence fact, and the no-donation
fact the reclaim establishes.  The teardown needs nothing further — everything it
asks of its own pre-state is read off `restoredTcb`. -/
theorem restoredAndConsumed_preserves_ipcInvariantFull (st : SystemState)
    (v : SeLe4n.ThreadId) (tcbV : TCB) (frame : Option Architecture.SyscallReturnFrame)
    (epV : SeLe4n.ObjId) (rtV : Option SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hBlocked : tcbV.ipcState = .blockedOnReply epV rtV)
    (hBundle : ipcInvariantFull st)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hOff : sweptThreadOffQueueChains st v)
    (hNotOwner : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId),
      st.objects[tid.toObjId]? = some (.tcb tcb) → tcb.schedContextBinding ≠ .donated scId v) :
    ipcInvariantFull (restoredAndConsumed st v tcbV frame) := by
  have hGet : st.getTcb? v = some tcbV := by
    rw [SystemState.getTcb?_eq_some_iff]; exact lookupTcb_some_objects st v tcbV hLookup
  unfold restoredAndConsumed
  exact consumeReplyLink_closes_exceptReplyLinkage _ v tcbV (restoredTcb tcbV frame)
    (Lifecycle.Suspend.restoreToReadyStaging_invExt st v frame hInv)
    (restoreToReadyStaging_objects_self st v frame tcbV hInv hGet)
    (restoredTcb_replyObject tcbV frame)
    (fun ep rt => by rw [restoredTcb_ipcState]; intro hc; cases hc)
    (restoreToReadyStaging_establishes_ipcInvariantFullExceptReplyLinkage st v frame tcbV
      epV rtV hInv hLookup hBlocked hBundle hAllBudgetsNone hOff hNotOwner)


-- ============================================================================
-- WS-RR RR8.7 — §12  The holder abort's obligation, and its bundle carriage
-- ============================================================================

/-- **WS-RR RR8.7: the three queue-coherence facts the holder abort needs.**

`abortPendingIpcOnEndpoint_preserves_ipcInvariantFull` asks for three things
`ipcInvariantFull` does not entail — the dual removal is enabled at the aborted
thread's endpoint, the predecessor promoted to tail is blocked on it, and the
splice leaves the thread out of every endpoint queue.  The reply arm's reclaim
resolves its holder from the victim's own reply frame, so the arm's callers cannot
name that thread to state those facts *of* it; this packages them under the arm
gate the abort itself branches on.

**Why the gate is `lookupTcb` and an `ipcState` disjunction rather than a resolved
holder.**  The abort is the identity on every arm but `.blockedOnSend` /
`.blockedOnCall` (`abortHolderPendingIpc_eq_self_of_allowed`), so on the other
arms there is nothing to be coherent about and a fact stated unconditionally would
be an obligation a caller could not discharge and the abort would not use.  The
shape mirrors `sweptThreadQueueCoherent`, which states the same class of fact for
the endpoint arm's whole-store sweep, and for the same stated reason: the bundle
constrains a queue only at its boundaries and carries no connectivity. -/
structure abortHolderQueueCoherent (st : SystemState) (holder : SeLe4n.ThreadId) : Prop where
  /-- The dual removal is enabled at the endpoint the holder is blocked on. -/
  removalEnabled : ∀ (holderTcb : TCB) (epId : SeLe4n.ObjId),
    lookupTcb st holder = some holderTcb →
    (holderTcb.ipcState = .blockedOnSend epId ∨ holderTcb.ipcState = .blockedOnCall epId) →
    dualRemovalEnabled epId false holder st
  /-- A predecessor the splice promotes to tail is blocked on that endpoint. -/
  predecessorBlocked : ∀ (holderTcb : TCB) (epId : SeLe4n.ObjId),
    lookupTcb st holder = some holderTcb →
    (holderTcb.ipcState = .blockedOnSend epId ∨ holderTcb.ipcState = .blockedOnCall epId) →
    splicePredecessorBlocked false epId st holder
  /-- After the splice the holder bounds no endpoint queue and nothing points at it. -/
  leavesDetached : ∀ (holderTcb : TCB) (epId : SeLe4n.ObjId),
    lookupTcb st holder = some holderTcb →
    (holderTcb.ipcState = .blockedOnSend epId ∨ holderTcb.ipcState = .blockedOnCall epId) →
    ∀ st1, endpointQueueRemove epId false holder st = .ok st1 →
      spliceLeavesThreadDetached st1 holder

open SeLe4n.Model.SystemState in
/-- **WS-RR RR8.7: the holder abort carries the whole IPC bundle.**

Four of its five arms are the identity and the fifth is one successful
`abortPendingIpcOnEndpoint`, so this is that operation's carriage under the arm
gate — with the refusal arm the identity too, since the abort declines rather than
diverging.

**`hNotReply` is discharged here, not assumed, and it is FALSE of a general
holder.**  The engine asks that the aborted thread is not `.blockedOnReply`; a
holder in general may be (a passive server that called onward and is waiting on
its own reply), so hoisting the fact above the case split is unprovable.  Under the
two arms that abort it is immediate from the branch condition, which is why it is
derived inside each one. -/
theorem abortHolderPendingIpc_preserves_ipcInvariantFull
    (st : SystemState) (holder : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hBudgets : allTimeoutBudgetsNone st)
    (hCoh : abortHolderQueueCoherent st holder) :
    ipcInvariantFull (Lifecycle.Suspend.abortHolderPendingIpc st holder) := by
  unfold Lifecycle.Suspend.abortHolderPendingIpc
  cases hLk : lookupTcb st holder with
  | none => exact hInv
  | some holderTcb =>
    have hObj : st.objects[holder.toObjId]? = some (.tcb holderTcb) :=
      lookupTcb_some_objects st holder holderTcb hLk
    have hG' : st.getTcb? holder = some holderTcb :=
      (SystemState.getTcb?_eq_some_iff st holder holderTcb).mpr hObj
    have hNotReplyOf : ∀ (epId : SeLe4n.ObjId),
        (holderTcb.ipcState = ThreadIpcState.blockedOnSend epId ∨
          holderTcb.ipcState = ThreadIpcState.blockedOnCall epId) →
        ∀ (tcb : TCB), st.getTcb? holder = some tcb →
          ∀ (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId),
            tcb.ipcState ≠ ThreadIpcState.blockedOnReply ep rt := by
      intro epId hOr tcb hG ep rt hEq
      rw [hG'] at hG
      cases hG
      rcases hOr with hS | hC
      · rw [hS] at hEq; cases hEq
      · rw [hC] at hEq; cases hEq
    simp only []
    cases hIp : holderTcb.ipcState with
    | ready => exact hInv
    | blockedOnReceive _ => exact hInv
    | blockedOnNotification _ => exact hInv
    | blockedOnReply _ _ => exact hInv
    | blockedOnSend epId =>
      simp only []
      cases hAb : abortPendingIpcOnEndpoint epId false holder st with
      | error _ => exact hInv
      | ok st' =>
        exact abortPendingIpcOnEndpoint_preserves_ipcInvariantFull hObjInv hInv hBudgets
          (hNotReplyOf epId (Or.inl hIp)) (hCoh.removalEnabled holderTcb epId hLk (Or.inl hIp))
          (hCoh.predecessorBlocked holderTcb epId hLk (Or.inl hIp))
          (hCoh.leavesDetached holderTcb epId hLk (Or.inl hIp)) hAb
    | blockedOnCall epId =>
      simp only []
      cases hAb : abortPendingIpcOnEndpoint epId false holder st with
      | error _ => exact hInv
      | ok st' =>
        exact abortPendingIpcOnEndpoint_preserves_ipcInvariantFull hObjInv hInv hBudgets
          (hNotReplyOf epId (Or.inr hIp)) (hCoh.removalEnabled holderTcb epId hLk (Or.inr hIp))
          (hCoh.predecessorBlocked holderTcb epId hLk (Or.inr hIp))
          (hCoh.leavesDetached holderTcb epId hLk (Or.inr hIp)) hAb

open SeLe4n.Model.SystemState in
/-- **WS-RR RR8.7**: and it keeps every timeout budget `none` — the same arm split
over `abortPendingIpcOnEndpoint_preserves_allTimeoutBudgetsNone`, which is what the
restore's keystone reads at the end of the arm. -/
theorem abortHolderPendingIpc_preserves_allTimeoutBudgetsNone (st : SystemState)
    (holder : SeLe4n.ThreadId) (hObjInv : st.objects.invExt)
    (hAll : allTimeoutBudgetsNone st) :
    allTimeoutBudgetsNone (Lifecycle.Suspend.abortHolderPendingIpc st holder) := by
  unfold Lifecycle.Suspend.abortHolderPendingIpc
  cases hLk : lookupTcb st holder with
  | none => exact hAll
  | some holderTcb =>
    simp only []
    cases hIp : holderTcb.ipcState with
    | ready => exact hAll
    | blockedOnReceive _ => exact hAll
    | blockedOnNotification _ => exact hAll
    | blockedOnReply _ _ => exact hAll
    | blockedOnSend epId =>
      simp only []
      cases hAb : abortPendingIpcOnEndpoint epId false holder st with
      | error _ => exact hAll
      | ok st' => exact abortPendingIpcOnEndpoint_preserves_allTimeoutBudgetsNone hObjInv hAll hAb
    | blockedOnCall epId =>
      simp only []
      cases hAb : abortPendingIpcOnEndpoint epId false holder st with
      | error _ => exact hAll
      | ok st' => exact abortPendingIpcOnEndpoint_preserves_allTimeoutBudgetsNone hObjInv hAll hAb

-- ============================================================================
-- WS-RR RR8.7 — §13  The reclaim's bundle carriage
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- **WS-RR RR8.7: the holder the reclaim resolves holds the victim's donation.**

`cancelledCallerDonation?` reads the victim's own reply *frame* and answers
`(context, holder)` off a `.head` link and that context's `boundThread`; it says
nothing about `holder`'s **binding**, and the pop's bundle carriage is stated over
exactly that binding (`replyDonationReturn?`).  So the missing half is supplied by
the reply path's own stated fact `replyFrameHeadHolderDonation`, applied at the
victim's reply object — head -> binding, the direction WS-HP HP7 kept live because
the trigger does not witness it.

**Reusing that predicate rather than spelling a cancellation-side twin is the
point**: the two paths' triggers agree on this question
(`cancelledCallerDonation?_eq_answeredFrameHeadContext?`), so a second predicate
would be one question with two answers, free to drift.  Note this is *not*
`donatedContextIsOwnerFrameHead`, which runs binding -> head and is what the
no-donation payoff consumes; the reply arm needs both directions, and neither is
derivable from the other or from `ipcInvariantFull` — the chain invariant carries
no binding clause at all. -/
theorem cancelledCallerDonation?_holder_holds_victim_donation (st : SystemState)
    (v : SeLe4n.ThreadId) (tcbV : TCB) (scId : SeLe4n.SchedContextId)
    (holder : SeLe4n.ThreadId)
    (hOwed : ∀ rid, tcbV.replyObject = some rid → replyFrameHeadHolderDonation st rid v)
    (hRes : Lifecycle.Suspend.cancelledCallerDonation? st v tcbV = some (scId, holder)) :
    replyDonationReturn? st holder = some (scId, v) := by
  obtain ⟨⟨ep0, rt0, hIp⟩, rid, _, _, hRO, _, _, _, _, _⟩ :=
    cancelledCallerDonation?_some st v tcbV scId holder hRes
  have hHead : replyFrameHeadHolder? st rid = some (scId, holder) := by
    unfold Lifecycle.Suspend.cancelledCallerDonation? at hRes
    rw [hIp, hRO] at hRes
    exact hRes
  exact hOwed rid hRO scId holder hHead

open SeLe4n.Model.SystemState in
/-- **WS-RR RR8.7: the resolved holder is not the victim.**

Read off `donationOwnerValid`: the holder's binding is a donation owed to `v`, and
that conjunct makes an owner `.unbound` — so were the two the same thread its
binding would have to be both.  Consumed twice, by the abort's off-queue frame and
by the victim's TCB rewrite, which is why it is named rather than inlined. -/
theorem cancelledCallerDonation?_holder_ne_victim (st : SystemState)
    (v : SeLe4n.ThreadId) (tcbV : TCB) (scId : SeLe4n.SchedContextId)
    (holder : SeLe4n.ThreadId)
    (hOwner : donationOwnerValid st)
    (hOwed : ∀ rid, tcbV.replyObject = some rid → replyFrameHeadHolderDonation st rid v)
    (hRes : Lifecycle.Suspend.cancelledCallerDonation? st v tcbV = some (scId, holder)) :
    v ≠ holder := by
  obtain ⟨pTcb, hLkP, hBindP⟩ := replyDonationReturn?_some_lookup st holder scId v
    (cancelledCallerDonation?_holder_holds_victim_donation st v tcbV scId holder hOwed hRes)
  obtain ⟨_, vTcb, hVObj, hVUnbound, _⟩ :=
    hOwner holder pTcb scId v (lookupTcb_some_objects st holder pTcb hLkP) hBindP
  intro hEq
  rw [hEq] at hVObj
  rw [KernelObject.tcb.inj (Option.some.inj
    (hVObj.symm.trans (lookupTcb_some_objects st holder pTcb hLkP)))] at hVUnbound
  rw [hBindP] at hVUnbound
  cases hVUnbound

open SeLe4n.Model.SystemState in
/-- **WS-RR RR8.7: the holder abort leaves a thread off every queue chain
verbatim.**

`abortHolderPendingIpc_other_tcb_eq` needs the key to be neither the holder nor
either of its queue neighbours.  For a thread the state puts on no chain the last
two are *derived* rather than assumed: link integrity turns "the holder's
`queuePrev` names `v`" into "`v`'s `queueNext` names the holder", which
`sweptThreadOffQueueChains` refutes, and symmetrically for `queueNext`.  That is
what lets the reply arm carry the victim's `ipcState`, `replyObject` **and** queue
links across the abort with one lemma rather than a field-by-field frame. -/
theorem abortHolderPendingIpc_offQueue_tcb_eq (st : SystemState)
    (holder v : SeLe4n.ThreadId) (tcbV : TCB)
    (hObjInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hOff : sweptThreadOffQueueChains st v) (hNe : v ≠ holder)
    (hLookup : lookupTcb st v = some tcbV) :
    (Lifecycle.Suspend.abortHolderPendingIpc st holder).objects[v.toObjId]?
      = some (.tcb tcbV) := by
  have hAtV : st.objects[v.toObjId]? = some (.tcb tcbV) := lookupTcb_some_objects st v tcbV hLookup
  obtain ⟨hPrevNone, hNextNone⟩ := hOff tcbV hLookup
  cases hLk : lookupTcb st holder with
  | none =>
    rw [Lifecycle.Suspend.abortHolderPendingIpc_eq_self_of_lookup_none st holder hLk]
    exact hAtV
  | some holderTcb =>
    have hAtH : st.objects[holder.toObjId]? = some (.tcb holderTcb) :=
      lookupTcb_some_objects st holder holderTcb hLk
    refine abortHolderPendingIpc_other_tcb_eq st holder holderTcb hObjInv hLk
      v.toObjId tcbV (fun hEq => hNe (SeLe4n.ThreadId.toObjId_injective v holder hEq)) ?_ ?_ hAtV
    · intro p hp hEq
      obtain rfl := SeLe4n.ThreadId.toObjId_injective v p hEq
      obtain ⟨tcbA, hA, hNext⟩ := hLink.2 holder holderTcb hAtH v hp
      rw [hAtV] at hA
      obtain rfl := KernelObject.tcb.inj (Option.some.inj hA)
      rw [hNextNone] at hNext
      cases hNext
    · intro n hn hEq
      obtain rfl := SeLe4n.ThreadId.toObjId_injective v n hEq
      obtain ⟨tcbB, hB, hPrev⟩ := hLink.1 holder holderTcb hAtH v hn
      rw [hAtV] at hB
      obtain rfl := KernelObject.tcb.inj (Option.some.inj hB)
      rw [hPrevNone] at hPrev
      cases hPrev

open SeLe4n.Model.SystemState in
/-- **WS-RR RR8.7: the reclaim carries the whole IPC bundle.**

`returnDonationToCancelledCaller` is the holder abort followed by
`returnDonatedSchedContextResolved`, and this composes the two rather than
re-proving twenty conjuncts: the abort's carriage is §12, and the pop's is
`returnDonatedSchedContext_establishes_ipcInvariantFull_of_except`.

Five things the composition needs, and where each comes from.  `hOwed` supplies the
binding the pop's carriage is stated over, transported across the abort because the
abort writes no `schedContextBinding`
(`abortHolderPendingIpc_binding_forward`).  `hReplierIdleAllowed` is
`abortHolderPendingIpc_holder_ipcState_allowed` — the abort is precisely what makes
a blocked holder's state one `passiveServerIdle` admits, which is why the abort runs
**first**.  The relaxation point is the victim: the pop rebinds `v`, so the pre-state
the engine reads is `ipcInvariantFullExceptDonationOwner … v`, obtained from the
full bundle at the post-abort state.  `hStack` is WS-OD OD4.4's outer-caller
obligation, threaded through `donationReturnOuterValid_of_stackValid` at whatever the
resolver answers.  And the resolver *answers* because the chain invariant crosses the
abort (`abortHolderPendingIpc_donationChainFrame`), the SchedContext the trigger named
surviving it because the abort writes no SchedContext at all.

**Both refusal arms are the identity**, so the conclusion needs no success argument:
a pop that declines returns the pre-state, abort and all (WS-OD OD1.4's
all-or-nothing), and the pre-state carries the bundle by hypothesis. -/
theorem returnDonationToCancelledCaller_preserves_ipcInvariantFull
    (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB)
    (hObjInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hBundle : ipcInvariantFull st)
    (hChain : donationChainWellFormed st)
    (hBudgets : allTimeoutBudgetsNone st)
    (hOwed : ∀ rid, tcbV.replyObject = some rid → replyFrameHeadHolderDonation st rid v)
    (hStack : cancelDonationStackValid st v tcbV)
    (hCoh : ∀ (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId),
      Lifecycle.Suspend.cancelledCallerDonation? st v tcbV = some (scId, holder) →
      abortHolderQueueCoherent st holder) :
    ipcInvariantFull (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) := by
  have hGetV : st.getTcb? v = some tcbV := by
    rw [SystemState.getTcb?_eq_some_iff]; exact lookupTcb_some_objects st v tcbV hLookup
  unfold Lifecycle.Suspend.returnDonationToCancelledCaller
  rw [hGetV]
  cases hRes : Lifecycle.Suspend.cancelledCallerDonation? st v tcbV with
  | none => exact hBundle
  | some p =>
    obtain ⟨scId, holder⟩ := p
    simp only []
    obtain ⟨⟨ep0, rt0, hIp⟩, rid, r, sc, hRO, hR, hN, hSc, hRec, hBt⟩ :=
      cancelledCallerDonation?_some st v tcbV scId holder hRes
    have hRet : replyDonationReturn? st holder = some (scId, v) :=
      cancelledCallerDonation?_holder_holds_victim_donation st v tcbV scId holder hOwed hRes
    obtain ⟨pTcb, hLkP, hBindP⟩ := replyDonationReturn?_some_lookup st holder scId v hRet
    -- The post-abort state: the pop's own pre-state.
    have hInvA : (Lifecycle.Suspend.abortHolderPendingIpc st holder).objects.invExt :=
      Lifecycle.Suspend.abortHolderPendingIpc_preserves_objects_invExt st holder hObjInv
    have hBundleA : ipcInvariantFull (Lifecycle.Suspend.abortHolderPendingIpc st holder) :=
      abortHolderPendingIpc_preserves_ipcInvariantFull st holder hObjInv hBundle hBudgets
        (hCoh scId holder hRes)
    have hChainA : donationChainWellFormed (Lifecycle.Suspend.abortHolderPendingIpc st holder) :=
      donationChainWellFormed_of_frame
        (Lifecycle.Suspend.abortHolderPendingIpc_donationChainFrame st holder hObjInv) hChain
    -- The binding the pop reads survives the abort, which writes none.
    obtain ⟨pTcbA, hAtA, hBindA⟩ :=
      Lifecycle.Suspend.abortHolderPendingIpc_binding_forward st holder hObjInv holder.toObjId
        pTcb (lookupTcb_some_objects st holder pTcb hLkP)
    have hNotRes : ¬ holder.isReserved := lookupTcb_some_not_reserved st holder pTcb hLkP
    have hLkA : lookupTcb (Lifecycle.Suspend.abortHolderPendingIpc st holder) holder
        = some pTcbA :=
      lookupTcb_of_objects_of_not_reserved _ holder pTcbA hAtA hNotRes
    have hRetA : replyDonationReturn? (Lifecycle.Suspend.abortHolderPendingIpc st holder) holder
        = some (scId, v) := by
      unfold replyDonationReturn?
      rw [hLkA]
      simp only []
      rw [hBindA, hBindP]
    -- The abort is what makes the holder's state one `passiveServerIdle` admits.
    have hAllowed : ∀ tcb, (Lifecycle.Suspend.abortHolderPendingIpc st holder).getTcb? holder
        = some tcb → passiveServerIdleAllowed tcb.ipcState :=
      fun tcb h => Lifecycle.Suspend.abortHolderPendingIpc_holder_ipcState_allowed st holder
        pTcb hObjInv hBundle.ipcStateQueueMembershipConsistent hLkP tcb h
    have hNeSent : holder ≠ SeLe4n.ThreadId.sentinel := by
      intro hc
      rw [hc] at hNotRes
      exact hNotRes SeLe4n.ThreadId.sentinel_isReserved
    -- The context the trigger named survives the abort, so the outer caller resolves.
    have hScA : (Lifecycle.Suspend.abortHolderPendingIpc st holder).objects[scId.toObjId]?
        = some (.schedContext sc) :=
      Lifecycle.Suspend.abortHolderPendingIpc_unwritten_kind_forward st holder hObjInv
        (fun o => ∃ sc0 : SeLe4n.Kernel.SchedContext, o = .schedContext sc0)
        (fun _ hc => nomatch hc.choose_spec) (fun _ hc => nomatch hc.choose_spec)
        scId.toObjId _ ⟨sc, rfl⟩ ((SystemState.getSchedContext?_eq_some_iff st scId sc).mp hSc)
    obtain ⟨n, hResN⟩ :=
      replyStackOuterCallerResolves_of_chainWellFormed _ scId hChainA sc hScA
    rw [returnDonatedSchedContextResolved_of_resolved hResN]
    cases hPop : returnDonatedSchedContext (Lifecycle.Suspend.abortHolderPendingIpc st holder)
        holder scId v n with
    | error _ => exact hBundle
    | ok st' =>
      exact returnDonatedSchedContext_establishes_ipcInvariantFull_of_except _ st'
        ⟨holder, hNeSent⟩ scId v hInvA
        (ipcInvariantFullExceptDonationOwner_of_full v hBundleA) hRetA hAllowed n
        (donationReturnOuterValid_of_stackValid (hStack scId holder hRes) hResN) hPop

open SeLe4n.Model.SystemState in
/-- **WS-RR RR8.7**: and the reclaim keeps every timeout budget `none` — the abort's
half from §12, the pop's from `returnDonatedSchedContext_tcb_timeoutBudget_backward`,
which is that operation's `tcbBindingRewrite` reading at one field. -/
theorem returnDonationToCancelledCaller_preserves_allTimeoutBudgetsNone (st : SystemState)
    (v : SeLe4n.ThreadId) (tcbV : TCB) (hObjInv : st.objects.invExt)
    (hAll : allTimeoutBudgetsNone st) :
    allTimeoutBudgetsNone (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) := by
  unfold Lifecycle.Suspend.returnDonationToCancelledCaller
  split
  · rename_i scId holder _ _ _
    have hAllA : allTimeoutBudgetsNone (Lifecycle.Suspend.abortHolderPendingIpc st holder) :=
      abortHolderPendingIpc_preserves_allTimeoutBudgetsNone st holder hObjInv hAll
    have hInvA :=
      Lifecycle.Suspend.abortHolderPendingIpc_preserves_objects_invExt st holder hObjInv
    split
    · rename_i st' h
      obtain ⟨n, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose h
      exact allTimeoutBudgetsNone_of_frame
        (fun t tcb' hT => returnDonatedSchedContext_tcb_timeoutBudget_backward _ st' holder scId v
          hInvA n hPop t.toObjId tcb' hT) hAllA
    · exact hAll
  · exact hAll

open SeLe4n.Model.SystemState in
/-- **WS-RR RR8.7: the reclaim rewrites the victim's binding and nothing else of it.**

The abort leaves a thread off every queue chain verbatim (§13 above) and the pop
rewrites exactly one field of every TCB it touches
(`returnDonatedSchedContext_tcb_rewrite`), so the victim's `ipcState`,
`replyObject` **and** queue links all cross the reclaim unchanged.  That is what
the arm keystone needs at three separate places — the restore's blocking-state
hypothesis, the teardown's reply-object agreement, and the queue-coherence fact —
and stating it once as a `tcbBindingRewrite` gives all three rather than a frame
per field. -/
theorem returnDonationToCancelledCaller_victim_tcb_rewrite (st : SystemState)
    (v : SeLe4n.ThreadId) (tcbV : TCB)
    (hObjInv : st.objects.invExt) (hLink : tcbQueueLinkIntegrity st)
    (hOwner : donationOwnerValid st)
    (hOff : sweptThreadOffQueueChains st v) (hLookup : lookupTcb st v = some tcbV)
    (hOwed : ∀ rid, tcbV.replyObject = some rid → replyFrameHeadHolderDonation st rid v) :
    ∃ tcbV', (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV).objects[v.toObjId]?
        = some (.tcb tcbV') ∧ tcbBindingRewrite tcbV' tcbV := by
  have hAtV : st.objects[v.toObjId]? = some (.tcb tcbV) := lookupTcb_some_objects st v tcbV hLookup
  have hGetV : st.getTcb? v = some tcbV := (SystemState.getTcb?_eq_some_iff st v tcbV).mpr hAtV
  unfold Lifecycle.Suspend.returnDonationToCancelledCaller
  rw [hGetV]
  cases hRes : Lifecycle.Suspend.cancelledCallerDonation? st v tcbV with
  | none => exact ⟨tcbV, hAtV, tcbBindingRewrite.refl tcbV⟩
  | some p =>
    obtain ⟨scId, holder⟩ := p
    simp only []
    have hNe : v ≠ holder :=
      cancelledCallerDonation?_holder_ne_victim st v tcbV scId holder hOwner hOwed hRes
    have hAtVA : (Lifecycle.Suspend.abortHolderPendingIpc st holder).objects[v.toObjId]?
        = some (.tcb tcbV) :=
      abortHolderPendingIpc_offQueue_tcb_eq st holder v tcbV hObjInv hLink hOff hNe hLookup
    have hInvA :=
      Lifecycle.Suspend.abortHolderPendingIpc_preserves_objects_invExt st holder hObjInv
    cases hR : returnDonatedSchedContextResolved
        (Lifecycle.Suspend.abortHolderPendingIpc st holder) holder scId v with
    | error _ => exact ⟨tcbV, hAtV, tcbBindingRewrite.refl tcbV⟩
    | ok st' =>
      obtain ⟨n, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hR
      exact returnDonatedSchedContext_tcb_rewrite _ st' holder scId v hInvA n hPop v.toObjId
        tcbV hAtVA

-- ============================================================================
-- WS-RR RR8.7 — §14  The arm keystone
-- ============================================================================

/-- **WS-RR RR8.7: the teardown pair is a function of the TCB's reply object.**

`consumeReplyLink` reads `tcb.replyObject` and nothing else of the record it is
handed, so two TCBs agreeing there drive the pair to the same state.  The reply
arm needs exactly this: it passes the **pre-cancellation** TCB to the teardown
while the state the teardown runs on holds that TCB with its `schedContextBinding`
rewritten by the reclaim, and those differ. -/
theorem restoredAndConsumed_congr (st : SystemState) (v : SeLe4n.ThreadId) (t1 t2 : TCB)
    (frame : Option Architecture.SyscallReturnFrame) (h : t1.replyObject = t2.replyObject) :
    restoredAndConsumed st v t1 frame = restoredAndConsumed st v t2 frame := by
  unfold restoredAndConsumed
  cases hR : t1.replyObject with
  | none =>
    rw [Lifecycle.Suspend.consumeReplyLink_none _ v t1 hR,
      Lifecycle.Suspend.consumeReplyLink_none _ v t2 (h.symm.trans hR)]
  | some rid =>
    rw [Lifecycle.Suspend.consumeReplyLink_some _ v t1 rid hR,
      Lifecycle.Suspend.consumeReplyLink_some _ v t2 rid (h.symm.trans hR)]

/-- **WS-RR RR8.7: the cancellation's reply arm IS reclaim, splice, then the
teardown pair** — `rfl`, so the two cannot drift, exactly as
`cancelIpcBlocking_endpoint_arm_eq` pins the endpoint arm to its sweep.

`restoredAndConsumed`'s `frame` argument is the `.ipcCancelled` frame WS-RR RR7.14
stages here, `restoreToReadyCancelled` being that instance of the staging restore
by definition. -/
theorem cancelIpcBlocking_reply_arm_eq (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB)
    (epV : SeLe4n.ObjId) (rtV : Option SeLe4n.ThreadId)
    (hBlocked : tcbV.ipcState = .blockedOnReply epV rtV) :
    Lifecycle.Suspend.cancelIpcBlocking st v tcbV =
      restoredAndConsumed
        (spliceThreadReplyFrameOut
          (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV)
        v tcbV (some Architecture.cancelledIpcFrame) := by
  unfold Lifecycle.Suspend.cancelIpcBlocking restoredAndConsumed
  rw [hBlocked]
  rfl

open SeLe4n.Model.SystemState in
/-- **WS-RR RR8.7 — the keystone: the cancellation's reply arm preserves
`ipcInvariantFull`.**

The last of the three arms.  The endpoint arm's is
`cancelIpcBlocking_endpointArm_preserves_ipcInvariantFull` and the notification
arm's `cancelIpcBlocking_notificationArm_preserves_ipcInvariantFull`; this one took
longer because its arm is a *four-step composition* rather than one sweep — reclaim,
splice, restore, teardown — and no two of those steps carry the bundle for the same
reason.  The reclaim's is §13, the splice's is
`spliceThreadReplyFrameOut_preserves_ipcInvariantFull`, and the restore and teardown
are `restoredAndConsumed_preserves_ipcInvariantFull`, which is the **pair**: the
restore alone leaves `ipcInvariantFullExceptReplyLinkage` and the teardown alone
would clear a still-blocked caller's reply object, so neither half is the unit the
bundle is about.

**Two stated coherence facts, and both are needed.**  `hOwed` is head -> binding
(`replyFrameHeadHolderDonation` at the victim's reply object), which the *pop's*
bundle carriage is stated over; `hHolder` is binding -> head
(`donatedContextIsOwnerFrameHead`), which the no-donation payoff
`returnDonationToCancelledCaller_no_donation_to_victim` consumes and which is what
discharges the restore's `hNotOwner`.  Neither follows from the other: a frame head
whose context is `.bound` to its holder satisfies the second direction and refutes
the first, and a binding with no frame satisfies the first vacuously.  Neither
follows from `ipcInvariantFull` either — `donationOwnerValid` relates a donation to
no reply object and `donationChainWellFormed` carries no binding clause at all,
which is WS-HP HP7's own reason for keeping `replyFrameHeadHolderDonation` stated.

`hOff` is the arm's queue-coherence fact, exactly as the notification arm takes it:
the restore clears the victim's links with nothing to repair a neighbour, and the
bundle carries no connectivity.  It does double duty here — it is also what rules
the victim out as a queue neighbour of the abort's holder, so the victim's own TCB
crosses the reclaim with only its binding rewritten. -/
theorem cancelIpcBlocking_replyArm_preserves_ipcInvariantFull
    (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB)
    (epV : SeLe4n.ObjId) (rtV : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hBlocked : tcbV.ipcState = .blockedOnReply epV rtV)
    (hBundle : ipcInvariantFull st)
    (hChain : donationChainWellFormed st)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hOff : sweptThreadOffQueueChains st v)
    (hOwed : ∀ rid, tcbV.replyObject = some rid → replyFrameHeadHolderDonation st rid v)
    (hHolder : donatedContextIsOwnerFrameHead st v)
    (hStack : cancelDonationStackValid st v tcbV)
    (hCoh : ∀ (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId),
      Lifecycle.Suspend.cancelledCallerDonation? st v tcbV = some (scId, holder) →
      abortHolderQueueCoherent st holder) :
    ipcInvariantFull (Lifecycle.Suspend.cancelIpcBlocking st v tcbV) := by
  have hLink : tcbQueueLinkIntegrity st := hBundle.dualQueueSystemInvariant.linkIntegrity
  -- Step 1: the reclaim.
  have hInvR :=
    Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt st v tcbV hObjInv
  have hBundleR := returnDonationToCancelledCaller_preserves_ipcInvariantFull st v tcbV
    hObjInv hLookup hBundle hChain hAllBudgetsNone hOwed hStack hCoh
  have hBudgetsR := returnDonationToCancelledCaller_preserves_allTimeoutBudgetsNone st v tcbV
    hObjInv hAllBudgetsNone
  obtain ⟨tcbR, hAtR, sb, hEqR⟩ := returnDonationToCancelledCaller_victim_tcb_rewrite st v tcbV
    hObjInv hLink hBundle.donationOwnerValid hOff hLookup hOwed
  -- Step 2: the splice, which writes no TCB at all.
  have hInvS := spliceThreadReplyFrameOut_preserves_objects_invExt
    (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV hInvR
  have hBundleS := spliceThreadReplyFrameOut_preserves_ipcInvariantFull
    (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV hInvR hBundleR
  have hBudgetsS := allTimeoutBudgetsNone_of_frame
    (spliceThreadReplyFrameOut_timeoutBudgetFrame
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV hInvR) hBudgetsR
  have hAtS := spliceThreadReplyFrameOut_tcb_eq
    (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV hInvR v.toObjId tcbR hAtR
  have hLkS : lookupTcb (spliceThreadReplyFrameOut
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV) v = some tcbR :=
    lookupTcb_of_objects_of_not_reserved _ v tcbR hAtS
      (lookupTcb_some_not_reserved st v tcbV hLookup)
  -- The restore's no-donation hypothesis, pulled back through the splice.
  have hNotOwnerS : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId),
      (spliceThreadReplyFrameOut
        (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV).objects[tid.toObjId]?
          = some (.tcb tcb) → tcb.schedContextBinding ≠ .donated scId v := by
    intro tid tcb scId hAt
    exact returnDonationToCancelledCaller_no_donation_to_victim st v tcbV hObjInv hLookup
      hBundle.donationOwnerValid hChain hHolder hStack tid tcb scId
      (spliceThreadReplyFrameOut_tcb_backward _ tcbV hInvR tid.toObjId tcb hAt)
  -- And the queue-coherence fact, which survives because only the binding moved.
  have hOffS : sweptThreadOffQueueChains (spliceThreadReplyFrameOut
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV) v := by
    intro t hLk
    obtain rfl : t = tcbR := Option.some.inj (hLk.symm.trans hLkS)
    rw [hEqR]
    exact hOff tcbV hLookup
  -- Steps 3 and 4: the teardown pair, at the TCB the state actually holds.
  rw [cancelIpcBlocking_reply_arm_eq st v tcbV epV rtV hBlocked,
    restoredAndConsumed_congr _ v tcbV tcbR _ (by rw [hEqR])]
  exact restoredAndConsumed_preserves_ipcInvariantFull _ v tcbR _ epV rtV hInvS hLkS
    (by rw [hEqR]; exact hBlocked) hBundleS hBudgetsS hOffS hNotOwnerS

end SeLe4n.Kernel
