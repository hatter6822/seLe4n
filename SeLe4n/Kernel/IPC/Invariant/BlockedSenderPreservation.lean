/-
  SeLe4n — a verified microkernel in Lean 4
  Copyright (C) 2025 seLe4n contributors

  This program is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.
-/
import SeLe4n.Kernel.IPC.CrossCore.EndpointSend
import SeLe4n.Kernel.IPC.CrossCore.EndpointSendInvariant
import SeLe4n.Kernel.IPC.Invariant.DonationPreservation
import SeLe4n.Kernel.InformationFlow.Invariant.Composition

/-!
# WS-RR RR8.16 — the donation flow fact across the two blocking dispatches

`donationOwnerFlowsToHolder` — every lent SchedContext's owner has a label its
holder's dominates — across the checked send and the checked call.  The send
binds no SchedContext, so it transports the fact by the binding frame
(`endpointSendDualOnCore_sameSchedContextBindings`); the call's donation is the
one write that lends, and the fact there is a consequence of the caller's gate
and the receiver's (`rendezvousReceiverFlow`).

The blocked-sender label fact these dispatches also carry is no longer lifted
here: WS-SX SX11.2 carries the pair `endpointWaitersLabelsEqual` across every
kernel entry (`EndpointWaitersStage`), each new waiter admitted by the gate its
entry checks, and that stage superseded the per-dispatch sender lifts this
module held.  What remains of them is the walk's `ipcState` frame, which the
reply-holder cancel reads.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  The priority-inheritance walk frames every `ipcState`
-- ============================================================================

/-- WS-RR RR8.16: the cross-core chain walk frames every `ipcState`, by induction on
the fuel — the shape `propagatePipChainCrossCore_notification_backward` already has
for the notification half of the same question. -/
theorem propagatePipChainCrossCore_ipcStateFrame (st : SystemState)
    (tid : SeLe4n.ThreadId) (ec : CoreId) (fuel : Nat) (hInv : st.objects.invExt) :
    ipcStateFrame st (PriorityInheritance.propagatePipChainCrossCore st tid ec fuel).1 :=
  fun t tcb' hTcb' =>
    PriorityInheritance.propagatePipChainCrossCore_tcb_ipcState_backward st tid ec fuel
      hInv t tcb' hTcb'

-- ============================================================================
-- §2  The donation flow fact across the `.send` arm
-- ============================================================================

/-- WS-RR RR8.16: the cross-core send binds no SchedContext.

`donationOwnerFlowsToHolder` — the flow fact's sibling — transports across any
step that leaves every thread's `schedContextBinding` alone, and the send is such
a step on both paths: it writes `ipcState`s, queue links and the endpoint, and
only `.call` donates.  The `.call` chain has had this frame since RR2
(`endpointCallOnCore_sameSchedContextBindings`); its send counterpart did not
exist, so a consumer still had to carry the donation fact by hand across a send. -/
theorem endpointSendDualOnCore_sameSchedContextBindings
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (payload : SendPayload)
    (executingCore : CoreId) (st : SystemState) (hObjInv : st.objects.invExt) :
    sameSchedContextBindings st
      (endpointSendDualOnCore endpointId sender payload executingCore st).1 := by
  unfold endpointSendDualOnCore
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only []; split <;> exact sameSchedContextBindings.refl st
  | some ep =>
    simp only []
    cases hHead : ep.receiveQ.head with
    | none =>
      simp only []
      cases hEnq : endpointQueueEnqueue endpointId false sender st with
      | error e => exact sameSchedContextBindings.refl st
      | ok st1 =>
        simp only []
        have hS1 := endpointQueueEnqueue_sameSchedContextBindings endpointId false
          sender st st1 hObjInv hEnq
        have hInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false
          sender st st1 hObjInv hEnq
        cases hIpc : storeTcbIpcStateAndMessage st1 sender
            (.blockedOnSend endpointId) none with
        | error e => exact sameSchedContextBindings.refl st
        | ok st2 =>
          simp only []
          exact (hS1.trans (storeTcbIpcStateAndMessage_sameSchedContextBindings st1 st2
            sender _ none hInv1 hIpc)).trans
            (sameSchedContextBindings.of_objectsAgreeOffRunLinks
              (SystemState.objectsAgreeOffRunLinks.trans
                (recordSendCap_objectsAgreeOffRunLinks _ _ _ _ _)
                (removeRunnableOnCore_objectsAgreeOffRunLinks st2 sender executingCore)))
    | some _ =>
      simp only []
      cases hSnd : st.getTcb? sender with
      | none => exact sameSchedContextBindings.refl st
      | some _ =>
        simp only []
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => exact sameSchedContextBindings.refl st
        | ok triple =>
          obtain ⟨receiver, headTcb, st1⟩ := triple
          simp only []
          have hS1 := endpointQueuePopHead_sameSchedContextBindings endpointId true
            st st1 receiver headTcb hObjInv hPop
          have hInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true
            st st1 receiver headTcb hObjInv hPop
          cases hRecv : storeTcbReceiveComplete st1 receiver (some (sendPayloadMessage st sender payload)) with
          | error e => exact sameSchedContextBindings.refl st
          | ok st2 =>
            simp only []
            have hS2 := hS1.trans (storeTcbReceiveComplete_sameSchedContextBindings st1
              st2 receiver (some (sendPayloadMessage st sender payload)) hInv1 hRecv)
            have hInv2 := storeTcbReceiveComplete_preserves_objects_invExt st1 st2
              receiver (some (sendPayloadMessage st sender payload)) hInv1 hRecv
            obtain ⟨tr, hTrGet, hTrReady⟩ :=
              storeTcbReceiveComplete_getTcb?_ipcState st1 st2 receiver (some (sendPayloadMessage st sender payload))
                hInv1 hRecv
            exact hS2.trans (wakeThread_sameSchedContextBindings_of_ready st2 receiver
              executingCore tr hTrGet hTrReady hInv2)

/-- WS-RR RR8.16: and neither does the caps-carrying form — the transfer writes
CNodes and the derivation tree. -/
theorem endpointSendDualWithCapsOnCore_sameSchedContextBindings
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (payload : SendPayload)
    (executingCore : CoreId) (st : SystemState) (hObjInv : st.objects.invExt) :
    sameSchedContextBindings st
      (endpointSendDualWithCapsOnCore endpointId sender payload
        executingCore st).1 := by
  have hSend := endpointSendDualOnCore_sameSchedContextBindings endpointId sender
    payload executingCore st hObjInv
  have hSendInv := endpointSendDualOnCore_preserves_objects_invExt endpointId sender
    payload executingCore st hObjInv
  unfold endpointSendDualWithCapsOnCore
  cases hStep : endpointSendDualOnCore endpointId sender
      payload executingCore st with
  | mk st' res =>
    rw [hStep] at hSend hSendInv
    simp only at hSend hSendInv
    cases res with
    | error e => exact hSend
    | ok sgi =>
      simp only []
      repeat' split
      all_goals first
        | exact hSend
        | (rename_i hT; exact hSend.trans (receiveTransferCaps_sameSchedContextBindings hSendInv hT))

/-- WS-RR RR8.16: **the live `.send` arm carries the donation flow fact too.**

The sibling half of the lift, and free once the send is known to bind no
SchedContext: `donationOwnerFlowsToHolder_of_sameSchedContextBindings` is what
transports it.

The `.call` arm's counterpart could not be stated **from this direction**: its
dispatch **mints** a donation, so the fact at the post-state is about a binding
the pre-state does not have, and what makes the two ends comparable is the
*receiving* gate the server passed when it blocked on its own `Recv` —
`donationFlowFromBlockedDonor`'s `hReceiveGate` argument, which no state recorded.
`v0.35.196` recorded it (`blockedReceiverLabelsEqual`, established at the
same store from the receive arm's own gate), so the `.call` lift exists too and
is §6 below; the two differ in the direction their derivation reads, not in
strength. -/
theorem endpointSendCrossCoreDispatchChecked_preserves_donationOwnerFlowsToHolder
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (payload : SendPayload)
    (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt)
    (hPre : donationOwnerFlowsToHolder ctx st) :
    donationOwnerFlowsToHolder ctx
      (endpointSendCrossCoreDispatchChecked ctx endpointId sender payload
        executingCore st).1 := by
  unfold endpointSendCrossCoreDispatchChecked
  split
  · exact donationOwnerFlowsToHolder_of_sameSchedContextBindings hPre
      (endpointSendDualWithCapsOnCore_sameSchedContextBindings endpointId sender payload
        executingCore st hObjInv)
  · exact hPre

-- ============================================================================
-- §3  `v0.35.196` (register row 183) — the donation flow fact across `.call`
-- ============================================================================

/-- WS-RR RR8.16 (`v0.35.196`): the priority-inheritance walk binds no
SchedContext.

One application of `PriorityInheritance.propagatePipChainCrossCore_tcb_backward`,
whose record-level statement is what makes this and the `ipcState` restatement
above two instances of one proof rather than two copies of it. -/
theorem propagatePipChainCrossCore_sameSchedContextBindings (st : SystemState)
    (tid : SeLe4n.ThreadId) (ec : CoreId) (fuel : Nat) (hInv : st.objects.invExt) :
    sameSchedContextBindings st
      (PriorityInheritance.propagatePipChainCrossCore st tid ec fuel).1 := by
  intro t tcb' hTcb'
  obtain ⟨tcb, p, hPre, hEq⟩ :=
    PriorityInheritance.propagatePipChainCrossCore_tcb_backward st tid ec fuel hInv t tcb'
      hTcb'
  exact ⟨tcb, hPre, (TCB.proj_eq_of_withoutRunLinks_eq TCB.schedContextBinding hEq).symm⟩

/-- **WS-RR RR8.16 (`v0.35.196`)**: the cross-core call donation carries the
donation flow fact, given the flow the rendezvous established between its two
principals.

This is the one step in the tree that **mints** a `.donated` binding, so it is the
one that cannot inherit the fact through a `sameSchedContextBindings` frame.  What
it does instead is the three-way case split
`applyCallDonation_donating_binding` already states: the donor's binding becomes
`.unbound` (so it holds no donation at all), the donee's becomes
`.donated scId donor` (where the conclusion is `hFlow`), and every other thread
reads through (where the pre-state fact applies).

`hFlow` is an argument rather than a hypothesis on the state because it is the
composition of two **transition-time** gates, and the caller that can discharge it
is the checked dispatch — through `donationFlowToBlockedReceiver`, which reads the
receiving half off `blockedReceiverLabelsEqual`.  It is demanded only under
the donation's own guard, which is what lets a caller discharge it from the
receiver's TCB: a `some` there **is** `lookupTcb`-resolution of both principals
(`callDonationSchedContext?_some_char`), and where the guard declines the step is
the identity and owes nothing. -/
theorem applyCallDonationOnCore_preserves_donationOwnerFlowsToHolder
    (ctx : LabelingContext) (st st'' : SystemState)
    (callerVtid receiverVtid : SeLe4n.ValidThreadId) (donorHome doneeHome : CoreId)
    (hObjInv : st.objects.invExt)
    (hPre : donationOwnerFlowsToHolder ctx st)
    (hFlow : ∀ scId : SeLe4n.SchedContextId,
      callDonationSchedContext? st callerVtid.val receiverVtid.val = some scId →
      securityFlowsTo (ctx.threadLabelOf callerVtid.val)
        (ctx.threadLabelOf receiverVtid.val) = true)
    (h : applyCallDonationOnCore st callerVtid receiverVtid donorHome doneeHome = .ok st'') :
    donationOwnerFlowsToHolder ctx st'' := by
  obtain ⟨st', hDon, harm⟩ := applyCallDonationOnCore_ok_decompose st st'' callerVtid
    receiverVtid donorHome doneeHome h
  -- The migration writes release-queue links alone, so every thread reads as
  -- in `applyCallDonation`'s own store and the whole question is about it.
  have hTcbs : ∀ t, st''.getTcb? t = st'.getTcb? t := by
    rcases harm with ⟨_, hEq⟩ | ⟨scId, _, hEq⟩ <;> rw [hEq] <;> intro t
    · rfl
    · exact (migrateSchedContextReplenishment_agree _ _ _ _).getTcb? t
  have hMid : donationOwnerFlowsToHolder ctx st' := by
    cases hSc : callDonationSchedContext? st callerVtid.val receiverVtid.val with
    | none =>
        rw [applyCallDonation_characterisation, hSc] at hDon
        cases hDon
        exact hPre
    | some scId =>
      intro holder owner scId' hRet
      -- Unfold the resolver: a `.donated` binding at `holder` in the post-state.
      unfold replyDonationReturn? at hRet
      cases hLook : lookupTcb st' holder with
      | none => rw [hLook] at hRet; exact absurd hRet (by simp)
      | some tcb' =>
        rw [hLook] at hRet
        simp only at hRet
        cases hBind : tcb'.schedContextBinding with
        | unbound => rw [hBind] at hRet; exact absurd hRet (by simp)
        | bound s => rw [hBind] at hRet; exact absurd hRet (by simp)
        | donated s o =>
          rw [hBind] at hRet
          simp only [Option.some.injEq, Prod.mk.injEq] at hRet
          obtain ⟨hS, hO⟩ := hRet
          rcases applyCallDonation_donating_binding st st' callerVtid receiverVtid scId
              hObjInv hSc hDon holder tcb'
              (getTcb?_of_lookupTcb st' holder tcb' hLook) with
            ⟨_, hUnbound⟩ | ⟨hRid, hDonated⟩ | ⟨_, _, hRead⟩
          · rw [hBind] at hUnbound; exact absurd hUnbound (by simp)
          · -- the donee: the conclusion IS the composed gate
            rw [hBind] at hDonated
            simp only [SchedContextBinding.donated.injEq] at hDonated
            rw [← hO, hDonated.2, hRid]
            exact hFlow scId hSc
          · -- every other thread reads through
            refine hPre holder owner scId' ?_
            unfold replyDonationReturn?
            rw [show lookupTcb st holder = some tcb' from by
                  unfold lookupTcb
                  rw [if_neg (lookupTcb_some_not_reserved st' holder tcb' hLook)]
                  exact hRead]
            simp only [hBind, Option.some.injEq, Prod.mk.injEq]
            exact ⟨hS, hO⟩
  intro holder owner scId' hRet
  refine hMid holder owner scId' ?_
  unfold replyDonationReturn? at hRet ⊢
  rw [show lookupTcb st'' holder = lookupTcb st' holder by unfold lookupTcb; rw [hTcbs]] at hRet
  exact hRet

/-- **WS-RR RR8.16 (`v0.35.196`)**: the rendezvous's two principals are comparable,
read off the pre-state.

The `.call` rendezvous donates the invoking thread's reservation to the endpoint's
**receive-queue head**, so the flow the donation needs is the composition of two
gates that ran at two different times: the caller's, which the dispatch is
evaluating now, and the receiver's, which ran when *it* blocked and which only
`blockedReceiverLabelsEqual` records.

`queueHeadBlockedConsistent` is what joins them — it says a receive queue's head is
`.blockedOnReceive` on **that** endpoint, which is the premise the receiver-side
fact is quantified over.  That is the structural asymmetry register row 183 named:
the sending gate is evaluated on the thread the transition was invoked by, whose
identity the transition holds directly, while the receiving gate was evaluated on a
thread the rendezvous *finds on a queue*, and relating that thread to the endpoint
is a queue fact rather than a gate fact. -/
theorem rendezvousReceiverFlow {ctx : LabelingContext} {st : SystemState}
    {endpointId : SeLe4n.ObjId} {caller receiverTid : SeLe4n.ThreadId}
    {ep : Endpoint} {rTcb : TCB}
    (hBlockedReceivers : blockedReceiverLabelsEqual ctx st)
    (hQueueHeads : queueHeadBlockedConsistent st)
    (hGate : securityFlowsTo (ctx.threadLabelOf caller)
      (ctx.endpointLabelOf endpointId) = true)
    (hEp : st.objects[endpointId]? = some (.endpoint ep))
    (hHead : ep.receiveQ.head = some receiverTid)
    (hTcb : lookupTcb st receiverTid = some rTcb) :
    securityFlowsTo (ctx.threadLabelOf caller) (ctx.threadLabelOf receiverTid) = true :=
  donationFlowToBlockedReceiver hBlockedReceivers hGate hTcb
    ((hQueueHeads endpointId ep receiverTid rTcb hEp
      (lookupTcb_some_objects st receiverTid rTcb hTcb)).1 hHead)

/-- **WS-RR RR8.16 (`v0.35.196`)**: **the live `.call` arm carries the donation flow
fact.**

Register row 183's part (1), and the half `v0.35.191` registered rather than
approximated: `endpointSendCrossCoreDispatchChecked` has carried
`donationOwnerFlowsToHolder` since that cut because a send mints no donation and
the fact rides its binding frame, while the `.call` arm — the one transition that
**does** mint one — could carry nothing, the receiving gate being recorded in no
state.

What closes it is the receiver-side predicate, and what it costs is one
`ipcInvariantFull` conjunct where the send's lift takes none.  The asymmetry is
structural rather than incidental, and `rendezvousReceiverFlow`'s docstring says
which side of the difference it comes from: the caller's gate is the dispatch's
own branch condition, and the receiver's is a fact about a thread the rendezvous
found on a queue.

The receiver is resolved on the **pre**-state — it is the `maybeReceiver` the
dispatch itself reads — while the donation's guard is evaluated after the call
leg, so the two are joined by that leg's own binding frame: a guard that fires at
the post-state resolves a receiver the pre-state also holds. -/
theorem endpointCallCrossCoreDispatch_preserves_donationOwnerFlowsToHolder
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (payload : SendPayload)
    (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt)
    (hPre : donationOwnerFlowsToHolder ctx st)
    (hBlockedReceivers : blockedReceiverLabelsEqual ctx st)
    (hQueueHeads : queueHeadBlockedConsistent st)
    (hGate : securityFlowsTo (ctx.threadLabelOf caller)
      (ctx.endpointLabelOf endpointId) = true) :
    donationOwnerFlowsToHolder ctx
      (endpointCallCrossCoreDispatch endpointId caller payload
        executingCore st).1 := by
  have hWcFrame := endpointCallWithCapsOnCore_sameSchedContextBindings endpointId caller payload
    executingCore st hObjInv
  have hWcInv := endpointCallWithCapsOnCore_preserves_objects_invExt endpointId caller payload
    executingCore st hObjInv
  unfold endpointCallCrossCoreDispatch
  cases hWc : endpointCallWithCapsOnCore endpointId caller payload
      executingCore st with
  | mk st' res =>
    rw [hWc] at hWcFrame hWcInv
    simp only at hWcFrame hWcInv
    have hMid : donationOwnerFlowsToHolder ctx st' :=
      donationOwnerFlowsToHolder_of_sameSchedContextBindings hPre hWcFrame
    cases res with
    | error e => exact hMid
    | ok pair =>
      obtain ⟨summary, sgi⟩ := pair
      simp only []
      split
      · rename_i receiverTid hRecv
        split
        · split
          · rename_i callerV receiverV hCV hRV
            split
            · exact hMid
            · rename_i st'' hDon
              have hDonInv := applyCallDonationOnCore_preserves_objects_invExt _ _ _ _ _ _
                hWcInv hDon
              refine donationOwnerFlowsToHolder_of_sameSchedContextBindings ?_
                (propagatePipChainCrossCore_sameSchedContextBindings _ _ executingCore _ hDonInv)
              refine applyCallDonationOnCore_preserves_donationOwnerFlowsToHolder ctx st' st''
                callerV receiverV _ _ hWcInv hMid (fun scId hSc => ?_) hDon
              -- The donation fired: both principals resolve at `st'`, so the
              -- receiver resolves at `st` too and the queue fact applies there.
              obtain ⟨⟨rTcb', hRLook', _⟩, _⟩ :=
                callDonationSchedContext?_some_char st' callerV.val receiverV.val scId hSc
              obtain ⟨rTcb, hRObj, _⟩ :=
                hWcFrame receiverV.val rTcb' (lookupTcb_some_objects st' receiverV.val rTcb' hRLook')
              have hRLook : lookupTcb st receiverV.val = some rTcb :=
                lookupTcb_of_objects_of_not_reserved st receiverV.val rTcb hRObj
                  (lookupTcb_some_not_reserved st' receiverV.val rTcb' hRLook')
              -- `maybeReceiver` is the pre-state receive-queue head, and the two
              -- `ThreadId.toValid?` shims name the same two threads the dispatch does.
              have hCallerEq : callerV.val = caller :=
                SeLe4n.ThreadId.toValid?_some_val_eq caller callerV hCV
              have hRecvEq : receiverV.val = receiverTid :=
                SeLe4n.ThreadId.toValid?_some_val_eq receiverTid receiverV hRV
              cases hEp : st.getEndpoint? endpointId with
              | none => rw [hEp] at hRecv; exact absurd hRecv (by simp)
              | some ep =>
                rw [hEp] at hRecv
                simp only at hRecv
                rw [hCallerEq, hRecvEq]
                exact rendezvousReceiverFlow hBlockedReceivers hQueueHeads hGate
                  ((SystemState.getEndpoint?_eq_some_iff st endpointId ep).mp hEp) hRecv
                  (by rw [← hRecvEq]; exact hRLook)
          all_goals exact hMid
        · exact hMid
      · exact hMid

/-- **WS-RR RR8.16 (`v0.35.196`)**: and the flow-checked arm, where the gate the
composition needs is the branch condition itself. -/
theorem endpointCallCrossCoreDispatchChecked_preserves_donationOwnerFlowsToHolder
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (payload : SendPayload)
    (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt)
    (hPre : donationOwnerFlowsToHolder ctx st)
    (hBlockedReceivers : blockedReceiverLabelsEqual ctx st)
    (hQueueHeads : queueHeadBlockedConsistent st) :
    donationOwnerFlowsToHolder ctx
      (endpointCallCrossCoreDispatchChecked ctx endpointId caller payload
        executingCore st).1 := by
  unfold endpointCallCrossCoreDispatchChecked
  split
  · rename_i hGate
    exact endpointCallCrossCoreDispatch_preserves_donationOwnerFlowsToHolder ctx endpointId
      caller payload executingCore st hObjInv hPre
      hBlockedReceivers hQueueHeads
      (endpointFlowGate_implies_securityFlowsTo ctx endpointId _ _ hGate)
  · exact hPre

end SeLe4n.Kernel
