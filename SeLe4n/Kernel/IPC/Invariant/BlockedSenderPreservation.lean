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
# WS-RR RR8.16 — the blocked-sender flow fact across the two blocking dispatches

`blockedSenderFlowsToEndpoint` says that every thread blocked *sending* or
*calling* on an endpoint has a label the endpoint's dominates — the fact the live
`endpointFlowGate` checked at the transition and the state records no trace of.
`v0.35.126` gave it a transport relation, an establishment at the one write that
creates a blocked sender, and an inhabitant at the boot state, and left the
**per-transition lift** owed: the two checked dispatches that perform that write
carried the fact through nothing, so a consumer of the cancellation-NI reductions
had to re-establish it by hand across a send or a call.

This module is that lift, for `endpointSendCrossCoreDispatchChecked` and
`endpointCallCrossCoreDispatchChecked`.

## Why the lift lives here rather than beside either transition

`EndpointSend.lean` and `EndpointCallDispatch.lean` are **operations** modules,
and this project keeps the Operations/Invariant split: a preservation result about
a transition is invariant work, so it may not sit in the module that defines the
transition.  `EndpointSendInvariant.lean` is the only production invariant module
that sees both dispatches, and its subject is the send chain alone — a `.call`
result there would be a claim filed under the wrong name.  So the two lifts share
a module of their own, which is the shape `SyscallSchedContainment.lean` and
`IPC/Invariant/CancellationBundle.lean` already have: **a claim about several arms
that no single arm's module can host.**

Nothing is relocated to make that work.  `blockedSenderFlowsToEndpoint`,
`blockedSenderShrinks` and the store establishment stay in
`InformationFlow/Invariant/Composition.lean`, because this module *can see them* —
the layering rule is that an owner whose asker cannot reach it is in the wrong
layer, and here the asker reaches it.

## The shape of the proofs

Every step of both composites falls into exactly one of three classes, and the
classification is the content:

1. **It preserves every thread's `ipcState`** — the queue splice, the capability
   transfer, the reply link, the SchedContext donation, the priority-inheritance
   walk, the run-queue removal.  These get `ipcStateFrame`, the relation
   `QueueSplicePreservation.lean` already owns for exactly this question, and
   `blockedSenderShrinks_of_ipcStateFrame` turns each into the transport.
2. **It writes `.ready`** — `storeTcbReceiveComplete` and the wake's
   `enqueueRunnableOnCore`.  `.ready` is neither `.blockedOnSend` nor
   `.blockedOnCall`, so these *shrink* the blocked-sender set rather than framing
   it, and they get `blockedSenderShrinks` directly.
3. **It writes the blocking state** — `storeTcbIpcStateAndMessage`, the one
   production write that creates a blocked sender.  It carries the fact through
   `storeTcbIpcStateAndMessage_preserves_blockedSenderFlowsToEndpoint`, whose
   `hGate` argument is discharged from the checked dispatch's own
   `endpointFlowGate` — which is why the lift is stated of the **checked** arm
   and is false of the unchecked one.

The refusal branches of both checked dispatches return the pre-state, so they are
`blockedSenderShrinks.refl`.  A `.call` rendezvous writes the *caller*
`.blockedOnReply`, which is class 2's reason rather than class 3's: no gate is
needed there, and the `hGate` argument is vacuous.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  The `ipcState`-preserving steps
-- ============================================================================

/-- WS-RR RR8.16: a step that writes no object at all frames every `ipcState`. -/
theorem ipcStateFrame_of_objects_eq {st st' : SystemState}
    (h : st'.objects = st.objects) : ipcStateFrame st st' := by
  intro t tcb' hTcb
  exact ⟨tcb', by rw [← h]; exact hTcb, rfl⟩

/-- WS-RR RR8.16: the donation read agreement frames every `ipcState`.

Its `tcbBwd` clause already states exactly this conjunct, so every transition with
a `donationReadAgreement` — the donation itself among them — transports the
blocked-sender fact with no new argument. -/
theorem ipcStateFrame_of_donationReadAgreement {st st' : SystemState}
    (h : donationReadAgreement st st') : ipcStateFrame st st' := by
  intro t tcb' hTcb
  obtain ⟨ty, hPre, hIpc, _⟩ := h.tcbBwd t.toObjId tcb' hTcb
  exact ⟨ty, hPre, hIpc.symm⟩

/-- WS-RR RR8.16: the endpoint-queue pop frames every `ipcState` — it rewrites
the popped thread's links and the endpoint, and no thread's blocking state. -/
theorem endpointQueuePopHead_ipcStateFrame
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (headTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st')) :
    ipcStateFrame st st' :=
  fun anyTid tcb' hTcb' =>
    endpointQueuePopHead_tcb_ipcState_backward endpointId isReceiveQ st st' tid anyTid
      tcb' hObjInv hStep hTcb'

/-- WS-RR RR8.16: and so does the enqueue. -/
theorem endpointQueueEnqueue_ipcStateFrame
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (enqueueTid : SeLe4n.ThreadId) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ enqueueTid st = .ok st') :
    ipcStateFrame st st' :=
  fun anyTid tcb' hTcb' =>
    endpointQueueEnqueue_tcb_ipcState_backward endpointId isReceiveQ enqueueTid st st'
      anyTid tcb' hObjInv hStep hTcb'

/-- WS-RR RR8.16: the capability transfer writes only the receiver's CSpace, and a
post-state TCB is its pre-state self. -/
theorem ipcUnwrapCaps_ipcStateFrame
    (msg : IpcMessage) (receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hObjInv : st.objects.invExt)
    (hStep : ipcUnwrapCaps msg receiverRoot slotBase grantRight st = .ok (summary, st')) :
    ipcStateFrame st st' :=
  fun t tcb' hTcb' =>
    ⟨tcb', ipcUnwrapCaps_tcb_backward msg receiverRoot slotBase grantRight st st' summary
      t.toObjId tcb' hObjInv hStep hTcb', rfl⟩

/-- WS-RR RR8.16: the server-first reply link writes a Reply and two TCBs' reply
fields, never an `ipcState`. -/
theorem linkServerStashedReply_ipcStateFrame
    (st st' : SystemState) (caller server : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : SystemState.linkServerStashedReply caller server st = .ok ((), st')) :
    ipcStateFrame st st' :=
  fun y tcbY' hTcb =>
    linkServerStashedReply_tcb_ipcState_backward st st' caller server y tcbY' hObjInv
      hStep hTcb

/-- WS-RR RR8.16: a run-queue removal writes no object. -/
theorem removeRunnableOnCore_ipcStateFrame (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    ipcStateFrame st (removeRunnableOnCore st tid c) :=
  ipcStateFrame_of_objects_eq (removeRunnableOnCore_preserves_objects st tid c)

/-- WS-RR RR8.16: a priority-inheritance boost frames every `ipcState`.

**`v0.35.195`**: the *fact* is
`PriorityInheritance.updatePipBoostOnCore_tcb_ipcState_backward`, which lives
beside the transition and beside its notification sibling
(`Scheduler/PriorityInheritance/Propagate.lean`) — a frame over a production
transition belongs there rather than in whichever module first needed it, and the
reply path's own askers cannot see this module.  What stays here is the
restatement in the relation's vocabulary, because `ipcStateFrame` is declared in
`QueueSplicePreservation.lean` and the scheduler layer is upstream of it. -/
theorem updatePipBoostOnCore_ipcStateFrame (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    ipcStateFrame st (PriorityInheritance.updatePipBoostOnCore st c tid) :=
  fun t tcb' hTcb' =>
    PriorityInheritance.updatePipBoostOnCore_tcb_ipcState_backward st c tid hInv t tcb'
      hTcb'

/-- WS-RR RR8.16: the wake-surfacing form is the boost with an SGI computation
beside it, so it frames the same thing. -/
theorem pipBoostWithWake_ipcStateFrame (st : SystemState) (tid : SeLe4n.ThreadId)
    (ec : CoreId) (hInv : st.objects.invExt) :
    ipcStateFrame st (PriorityInheritance.pipBoostWithWake st tid ec).1 :=
  fun t tcb' hTcb' =>
    PriorityInheritance.pipBoostWithWake_tcb_ipcState_backward st tid ec hInv t tcb' hTcb'

/-- WS-RR RR8.16: and the whole chain walk inherits it by induction on the fuel —
the shape `propagatePipChainCrossCore_notification_backward` already has for the
notification half of the same question. -/
theorem propagatePipChainCrossCore_ipcStateFrame (st : SystemState)
    (tid : SeLe4n.ThreadId) (ec : CoreId) (fuel : Nat) (hInv : st.objects.invExt) :
    ipcStateFrame st (PriorityInheritance.propagatePipChainCrossCore st tid ec fuel).1 :=
  fun t tcb' hTcb' =>
    PriorityInheritance.propagatePipChainCrossCore_tcb_ipcState_backward st tid ec fuel
      hInv t tcb' hTcb'

/-- WS-RR RR8.16: the SchedContext donation frames every `ipcState`.

Read off `donationReadAgreement`, whose `tcbBwd` clause states this conjunct
outright — so the fact costs no new case analysis over the donation's arms, and a
later widening of the donation reaches this theorem through the agreement it
already has to maintain. -/
theorem applyCallDonation_ipcStateFrame
    (st st' : SystemState) (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (hObjInv : st.objects.invExt)
    (h : applyCallDonation st callerVtid receiverVtid = .ok st') :
    ipcStateFrame st st' :=
  ipcStateFrame_of_donationReadAgreement
    (applyCallDonation_donationReadAgreement st st' callerVtid receiverVtid hObjInv h)

/-- WS-RR RR8.16: and the per-core form adds only the replenishment migration,
which writes no object. -/
theorem applyCallDonationOnCore_ipcStateFrame
    (st st'' : SystemState) (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (donorHome doneeHome : CoreId)
    (hObjInv : st.objects.invExt)
    (h : applyCallDonationOnCore st callerVtid receiverVtid donorHome doneeHome = .ok st'') :
    ipcStateFrame st st'' := by
  obtain ⟨st', hDon, harm⟩ := applyCallDonationOnCore_ok_decompose st st'' callerVtid
    receiverVtid donorHome doneeHome h
  have hFrame : ipcStateFrame st st' :=
    applyCallDonation_ipcStateFrame st st' callerVtid receiverVtid hObjInv hDon
  rcases harm with ⟨_, hEq⟩ | ⟨scId, _, hEq⟩ <;> subst hEq
  · exact hFrame
  · exact hFrame.trans
      (ipcStateFrame_of_objects_eq (migrateSchedContextReplenishment_objects _ _ _ _))

-- ============================================================================
-- §2  The `.ready` writers
-- ============================================================================

/-- WS-RR RR8.16: a wake introduces no blocked sender.

It is not an `ipcStateFrame`: the woken thread's `ipcState` becomes `.ready`.  But
`.ready` is neither `.blockedOnSend` nor `.blockedOnCall`, so the blocked-sender
set can only **shrink** — which is exactly the weakening `blockedSenderShrinks`
exists for, and why the flow fact rides a wake with no gate. -/
theorem enqueueRunnableOnCore_blockedSenderShrinks (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    blockedSenderShrinks st (enqueueRunnableOnCore st c tid) := by
  cases hFresh : runnableOnSomeCore st tid with
  | true =>
      rw [enqueueRunnableOnCore_eq_self_of_runnable st c tid hFresh]
      exact blockedSenderShrinks.refl st
  | false =>
      intro other t' epId hLook hB
      have hNotRes : ¬ other.isReserved :=
        lookupTcb_some_not_reserved _ other t' hLook
      have hGet : (enqueueRunnableOnCore st c tid).getTcb? other = some t' := by
        unfold lookupTcb at hLook; rw [if_neg hNotRes] at hLook; exact hLook
      by_cases hEq : other = tid
      · subst hEq
        cases hPre : st.getTcb? other with
        | none =>
            rw [enqueueRunnableOnCore_no_tcb_noop st c other hPre] at hGet
            exact absurd (hPre.symm.trans hGet) (by simp)
        | some tcb =>
            rw [enqueueRunnableOnCore_makes_ready st c other tcb hPre hInv hFresh] at hGet
            have : t'.ipcState = ThreadIpcState.ready := by
              simp only [Option.some.injEq] at hGet; rw [← hGet]
            rcases hB with h | h <;> rw [this] at h <;> exact absurd h (by simp)
      · rw [enqueueRunnableOnCore_getTcb?_ne st c tid other hInv hEq] at hGet
        exact ⟨t', by unfold lookupTcb; rw [if_neg hNotRes]; exact hGet, hB⟩

/-- WS-RR RR8.16: and so does the cross-core wake, which is that enqueue on the
woken thread's home core. -/
theorem wakeThread_blockedSenderShrinks (st : SystemState) (tid : SeLe4n.ThreadId)
    (ec : CoreId) (hInv : st.objects.invExt) :
    blockedSenderShrinks st (wakeThread st tid ec).1 := by
  rw [wakeThread_state_eq_enqueue]
  exact enqueueRunnableOnCore_blockedSenderShrinks st (determineTargetCore st tid) tid hInv

/-- WS-RR RR8.16: the receive completion writes the receiver `.ready`, so it
shrinks the blocked-sender set for the same reason. -/
theorem storeTcbReceiveComplete_blockedSenderShrinks
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbReceiveComplete st tid msg = .ok st') :
    blockedSenderShrinks st st' := by
  intro other t' epId hLook hB
  have hNotRes : ¬ other.isReserved := lookupTcb_some_not_reserved st' other t' hLook
  have hObj : st'.objects[other.toObjId]? = some (.tcb t') :=
    lookupTcb_some_objects st' other t' hLook
  by_cases hEq : other.toObjId = tid.toObjId
  · rw [hEq] at hObj
    have hReady := storeTcbReceiveComplete_ipcState_eq st st' tid msg hObjInv hStep t' hObj
    rcases hB with h | h <;> rw [hReady] at h <;> exact absurd h (by simp)
  · refine ⟨t', ?_, hB⟩
    refine lookupTcb_of_objects_of_not_reserved st other t' ?_ hNotRes
    rw [← storeTcbReceiveComplete_preserves_objects_ne st st' tid msg other.toObjId hEq
      hObjInv hStep]
    exact hObj

-- ============================================================================
-- §3  The `.send` chain
-- ============================================================================

/-- WS-RR RR8.16: the cross-core send carries the blocked-sender flow fact,
**given the gate that admitted it**.

The two paths are the two classes.  A rendezvous pops, completes the receive and
wakes: a splice, a `.ready` write and a `.ready` write, none of which can add a
blocked sender.  A block enqueues, writes the sender `.blockedOnSend endpointId`
and removes it from its core: the middle step is the one that creates a blocked
sender, and `hGate` is exactly what the checked dispatch above checked before
reaching here.  Both bounds rejections and every error arm return the pre-state.

Stated of the **unchecked** operation with the gate as an argument rather than of
the checked one alone, because the caps-carrying wrapper composes this one and the
gate is the same value at both levels. -/
theorem endpointSendDualOnCore_preserves_blockedSenderFlowsToEndpoint
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt)
    (hPre : blockedSenderFlowsToEndpoint ctx st)
    (hGate : securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf endpointId) = true) :
    blockedSenderFlowsToEndpoint ctx
      (endpointSendDualOnCore endpointId sender msg executingCore st).1 := by
  unfold endpointSendDualOnCore
  split
  · exact hPre
  · split
    · exact hPre
    · cases hEp : st.getEndpoint? endpointId with
      | none => simp only []; split <;> exact hPre
      | some ep =>
        simp only []
        cases hHead : ep.receiveQ.head with
        | none =>
          simp only []
          cases hEnq : endpointQueueEnqueue endpointId false sender st with
          | error e => exact hPre
          | ok st1 =>
            simp only []
            have hInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false
              sender st st1 hObjInv hEnq
            have hPre1 : blockedSenderFlowsToEndpoint ctx st1 :=
              blockedSenderFlowsToEndpoint_of_shrinks hPre
                (blockedSenderShrinks_of_ipcStateFrame
                  (endpointQueueEnqueue_ipcStateFrame endpointId false sender st st1
                    hObjInv hEnq))
            cases hIpc : storeTcbIpcStateAndMessage st1 sender
                (.blockedOnSend endpointId) (some msg) with
            | error e => exact hPre
            | ok st2 =>
              simp only []
              have hPre2 : blockedSenderFlowsToEndpoint ctx st2 :=
                storeTcbIpcStateAndMessage_preserves_blockedSenderFlowsToEndpoint ctx st1 st2
                  sender _ (some msg) hInv1 hIpc hPre1
                  (by
                    rintro ep' (h | h)
                    · injection h with h'; subst h'; exact hGate
                    · exact absurd h (by simp))
              exact blockedSenderFlowsToEndpoint_of_shrinks hPre2
                (blockedSenderShrinks_of_ipcStateFrame
                  (removeRunnableOnCore_ipcStateFrame st2 sender executingCore))
        | some _ =>
          simp only []
          cases hSnd : st.getTcb? sender with
          | none => exact hPre
          | some _ =>
            simp only []
            cases hPop : endpointQueuePopHead endpointId true st with
            | error e => exact hPre
            | ok triple =>
              obtain ⟨receiver, headTcb, st1⟩ := triple
              simp only []
              have hInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true
                st st1 receiver headTcb hObjInv hPop
              have hPre1 : blockedSenderFlowsToEndpoint ctx st1 :=
                blockedSenderFlowsToEndpoint_of_shrinks hPre
                  (blockedSenderShrinks_of_ipcStateFrame
                    (endpointQueuePopHead_ipcStateFrame endpointId true st st1 receiver
                      headTcb hObjInv hPop))
              cases hRecv : storeTcbReceiveComplete st1 receiver (some msg) with
              | error e => exact hPre
              | ok st2 =>
                simp only []
                have hInv2 := storeTcbReceiveComplete_preserves_objects_invExt st1 st2
                  receiver (some msg) hInv1 hRecv
                have hPre2 : blockedSenderFlowsToEndpoint ctx st2 :=
                  blockedSenderFlowsToEndpoint_of_shrinks hPre1
                    (storeTcbReceiveComplete_blockedSenderShrinks st1 st2 receiver
                      (some msg) hInv1 hRecv)
                exact blockedSenderFlowsToEndpoint_of_shrinks hPre2
                  (wakeThread_blockedSenderShrinks st2 receiver executingCore hInv2)

/-- WS-RR RR8.16: and so does the caps-carrying form — the capability transfer
writes the receiver's CSpace and the derivation tree, never an `ipcState`.

Its error arm returns the *post-send* state rather than the pre-state, which is
why the fact is established at that state first and the transfer extends it. -/
theorem endpointSendDualWithCapsOnCore_preserves_blockedSenderFlowsToEndpoint
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt)
    (hPre : blockedSenderFlowsToEndpoint ctx st)
    (hGate : securityFlowsTo (ctx.threadLabelOf sender) (ctx.endpointLabelOf endpointId) = true) :
    blockedSenderFlowsToEndpoint ctx
      (endpointSendDualWithCapsOnCore endpointId sender msg endpointRights
        receiverSlotBase executingCore st).1 := by
  have hSendPre := endpointSendDualOnCore_preserves_blockedSenderFlowsToEndpoint ctx
    endpointId sender { msg with capsGranted := endpointRights.mem .grant } executingCore st
    hObjInv hPre hGate
  have hSendInv := endpointSendDualOnCore_preserves_objects_invExt endpointId sender
    { msg with capsGranted := endpointRights.mem .grant } executingCore st hObjInv
  unfold endpointSendDualWithCapsOnCore
  cases hSend : endpointSendDualOnCore endpointId sender
      { msg with capsGranted := endpointRights.mem .grant } executingCore st with
  | mk st' res =>
    rw [hSend] at hSendPre hSendInv
    simp only at hSendPre hSendInv
    cases res with
    | error e => exact hSendPre
    | ok sgi =>
      simp only []
      -- `hasReceiver` is a `let` over the pre-state endpoint lookup, so the
      -- lookup has to be resolved before the `if` it guards can be split.
      cases hEp : st.getEndpoint? endpointId with
      | none => simp only []; split <;> exact hSendPre
      | some ep =>
        simp only []
        cases hHead : ep.receiveQ.head with
        | none => simp only []; split <;> exact hSendPre
        | some receiverId =>
          simp only []
          split
          · exact hSendPre
          · cases hRoot : lookupCspaceRoot st' receiverId with
            | none => simp only []; exact hSendPre
            | some recvRoot =>
              simp only []
              cases hUnwrap : ipcUnwrapCaps
                  { msg with capsGranted := endpointRights.mem .grant } recvRoot
                  receiverSlotBase (endpointRights.mem .grant) st' with
              | error e => simp only []; exact hSendPre
              | ok pair =>
                obtain ⟨summary, st''⟩ := pair
                simp only []
                exact blockedSenderFlowsToEndpoint_of_shrinks hSendPre
                  (blockedSenderShrinks_of_ipcStateFrame
                    (ipcUnwrapCaps_ipcStateFrame _ recvRoot receiverSlotBase _ st' st''
                      summary hSendInv hUnwrap))

/-- WS-RR RR8.16: **the live `.send` arm carries the blocked-sender flow fact.**

The lift the `v0.35.126` register row named as owed.  Both bounds rejections and
the flow denial return the pre-state, so they are `blockedSenderShrinks.refl`; the
admitted branch is the caps-carrying send under exactly the gate the branch
condition supplies, through `endpointFlowGate_implies_securityFlowsTo`.

It is a theorem about the **checked** arm and is false of the unchecked one: what
discharges the blocking store's obligation is the gate this dispatch evaluates. -/
theorem endpointSendCrossCoreDispatchChecked_preserves_blockedSenderFlowsToEndpoint
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt)
    (hPre : blockedSenderFlowsToEndpoint ctx st) :
    blockedSenderFlowsToEndpoint ctx
      (endpointSendCrossCoreDispatchChecked ctx endpointId sender msg endpointRights
        receiverSlotBase executingCore st).1 := by
  unfold endpointSendCrossCoreDispatchChecked
  split
  · exact hPre
  · split
    · exact hPre
    · split
      · rename_i hGate
        exact endpointSendDualWithCapsOnCore_preserves_blockedSenderFlowsToEndpoint ctx
          endpointId sender msg endpointRights receiverSlotBase executingCore st hObjInv hPre
          (endpointFlowGate_implies_securityFlowsTo ctx endpointId _ _ hGate)
      · exact hPre

-- ============================================================================
-- §4  The `.call` chain
-- ============================================================================

/-- WS-RR RR8.16: the cross-core call carries the blocked-sender flow fact, given
the gate that admitted it.

The **block** path is the send's, with `.blockedOnCall endpointId` in place of
`.blockedOnSend endpointId` — the two states the fact ranges over, which is why
one gate discharges either.

The **rendezvous** path writes three `ipcState`s and needs the gate for none of
them: the receiver becomes `.ready`, and the caller becomes `.blockedOnReply`,
which is not a blocked *sender* — a caller waiting on a reply is queued on no
endpoint's send queue and reaches no endpoint object.  Both of those stores go
through the same establishment lemma with a **vacuous** `hGate` argument, which is
exactly what that lemma's "stated for an arbitrary `ipc`" clause is for. -/
theorem endpointCallOnCore_preserves_blockedSenderFlowsToEndpoint
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt)
    (hPre : blockedSenderFlowsToEndpoint ctx st)
    (hGate : securityFlowsTo (ctx.threadLabelOf caller) (ctx.endpointLabelOf endpointId) = true) :
    blockedSenderFlowsToEndpoint ctx
      (endpointCallOnCore endpointId caller msg executingCore st).1 := by
  unfold endpointCallOnCore
  split
  · exact hPre
  · split
    · exact hPre
    · cases hEp : st.getEndpoint? endpointId with
      | none => simp only []; split <;> exact hPre
      | some ep =>
        simp only []
        cases hHead : ep.receiveQ.head with
        | none =>
          simp only []
          cases hEnq : endpointQueueEnqueue endpointId false caller st with
          | error e => exact hPre
          | ok st1 =>
            simp only []
            have hInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false
              caller st st1 hObjInv hEnq
            have hPre1 : blockedSenderFlowsToEndpoint ctx st1 :=
              blockedSenderFlowsToEndpoint_of_shrinks hPre
                (blockedSenderShrinks_of_ipcStateFrame
                  (endpointQueueEnqueue_ipcStateFrame endpointId false caller st st1
                    hObjInv hEnq))
            cases hIpc : storeTcbIpcStateAndMessage st1 caller
                (.blockedOnCall endpointId) (some msg) with
            | error e => exact hPre
            | ok st2 =>
              simp only []
              have hPre2 : blockedSenderFlowsToEndpoint ctx st2 :=
                storeTcbIpcStateAndMessage_preserves_blockedSenderFlowsToEndpoint ctx st1 st2
                  caller _ (some msg) hInv1 hIpc hPre1
                  (by
                    rintro ep' (h | h)
                    · exact absurd h (by simp)
                    · injection h with h'; subst h'; exact hGate)
              exact blockedSenderFlowsToEndpoint_of_shrinks hPre2
                (blockedSenderShrinks_of_ipcStateFrame
                  (removeRunnableOnCore_ipcStateFrame st2 caller executingCore))
        | some _ =>
          simp only []
          cases hPop : endpointQueuePopHead endpointId true st with
          | error e => exact hPre
          | ok triple =>
            obtain ⟨receiver, headTcb, st1⟩ := triple
            simp only []
            have hInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true
              st st1 receiver headTcb hObjInv hPop
            have hPre1 : blockedSenderFlowsToEndpoint ctx st1 :=
              blockedSenderFlowsToEndpoint_of_shrinks hPre
                (blockedSenderShrinks_of_ipcStateFrame
                  (endpointQueuePopHead_ipcStateFrame endpointId true st st1 receiver
                    headTcb hObjInv hPop))
            cases hReady : storeTcbIpcStateAndMessage st1 receiver .ready (some msg) with
            | error e => exact hPre
            | ok st2 =>
              simp only []
              have hInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt st1 st2
                receiver _ (some msg) hInv1 hReady
              have hPre2 : blockedSenderFlowsToEndpoint ctx st2 :=
                storeTcbIpcStateAndMessage_preserves_blockedSenderFlowsToEndpoint ctx st1 st2
                  receiver _ (some msg) hInv1 hReady hPre1
                  (by rintro ep' (h | h) <;> exact absurd h (by simp))
              have hInv3 : (wakeThread st2 receiver executingCore).1.objects.invExt := by
                rw [wakeThread_state_eq_enqueue]
                exact enqueueRunnableOnCore_preserves_objects_invExt st2
                  (determineTargetCore st2 receiver) receiver hInv2
              have hPre3 : blockedSenderFlowsToEndpoint ctx
                  (wakeThread st2 receiver executingCore).1 :=
                blockedSenderFlowsToEndpoint_of_shrinks hPre2
                  (wakeThread_blockedSenderShrinks st2 receiver executingCore hInv2)
              cases hReply : storeTcbIpcStateAndMessage (wakeThread st2 receiver executingCore).1
                  caller (.blockedOnReply endpointId (some receiver)) none with
              | error e => exact hPre
              | ok st4 =>
                simp only []
                have hInv4 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ st4
                  caller _ none hInv3 hReply
                have hPre4 : blockedSenderFlowsToEndpoint ctx st4 :=
                  storeTcbIpcStateAndMessage_preserves_blockedSenderFlowsToEndpoint ctx _ st4
                    caller _ none hInv3 hReply hPre3
                    (by rintro ep' (h | h) <;> exact absurd h (by simp))
                cases hLink : SystemState.linkServerStashedReply caller receiver st4 with
                | error e => exact hPre
                | ok pair =>
                  obtain ⟨u, st5⟩ := pair
                  simp only []
                  have hPre5 : blockedSenderFlowsToEndpoint ctx st5 :=
                    blockedSenderFlowsToEndpoint_of_shrinks hPre4
                      (blockedSenderShrinks_of_ipcStateFrame
                        (linkServerStashedReply_ipcStateFrame st4 st5 caller receiver
                          hInv4 hLink))
                  exact blockedSenderFlowsToEndpoint_of_shrinks hPre5
                    (blockedSenderShrinks_of_ipcStateFrame
                      (removeRunnableOnCore_ipcStateFrame st5 caller executingCore))

/-- WS-RR RR8.16: and the caps-carrying call form, for the send's reason. -/
theorem endpointCallWithCapsOnCore_preserves_blockedSenderFlowsToEndpoint
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt)
    (hPre : blockedSenderFlowsToEndpoint ctx st)
    (hGate : securityFlowsTo (ctx.threadLabelOf caller) (ctx.endpointLabelOf endpointId) = true) :
    blockedSenderFlowsToEndpoint ctx
      (endpointCallWithCapsOnCore endpointId caller msg endpointRights
        receiverSlotBase executingCore st).1 := by
  have hCallPre := endpointCallOnCore_preserves_blockedSenderFlowsToEndpoint ctx endpointId
    caller { msg with capsGranted := endpointRights.mem .grant } executingCore st hObjInv
    hPre hGate
  have hCallInv := endpointCallOnCore_preserves_objects_invExt endpointId caller
    { msg with capsGranted := endpointRights.mem .grant } executingCore st hObjInv
  unfold endpointCallWithCapsOnCore
  cases hCall : endpointCallOnCore endpointId caller
      { msg with capsGranted := endpointRights.mem .grant } executingCore st with
  | mk stCall res =>
    rw [hCall] at hCallPre hCallInv
    simp only at hCallPre hCallInv
    cases res with
    | error e => exact hCallPre
    | ok sgi =>
      simp only []
      cases hEp : st.getEndpoint? endpointId with
      | none => simp only []; split <;> exact hCallPre
      | some ep =>
        simp only []
        cases hHead : ep.receiveQ.head with
        | none => simp only []; split <;> exact hCallPre
        | some receiverId =>
          simp only []
          split
          · exact hCallPre
          · cases hRoot : lookupCspaceRoot stCall receiverId with
            | none => simp only []; exact hCallPre
            | some recvRoot =>
              simp only []
              cases hUnwrap : ipcUnwrapCaps
                  { msg with capsGranted := endpointRights.mem .grant } recvRoot
                  receiverSlotBase (endpointRights.mem .grant) stCall with
              | error e => simp only []; exact hCallPre
              | ok pair =>
                obtain ⟨summary, stFinal⟩ := pair
                simp only []
                exact blockedSenderFlowsToEndpoint_of_shrinks hCallPre
                  (blockedSenderShrinks_of_ipcStateFrame
                    (ipcUnwrapCaps_ipcStateFrame _ recvRoot receiverSlotBase _ stCall stFinal
                      summary hCallInv hUnwrap))

/-- WS-RR RR8.16: the full cross-core `.call` dispatch carries it too.

Past the caps-carrying call it composes the SchedContext donation and the
priority-inheritance chain walk, and neither writes an `ipcState`: the donation's
own `donationReadAgreement` states that conjunct outright, and the walk writes
`pipBoost` and run-queue buckets — the fact its own definition already relies on
when it reads `blockingServer` from the pre-mutation state. -/
theorem endpointCallCrossCoreDispatch_preserves_blockedSenderFlowsToEndpoint
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt)
    (hPre : blockedSenderFlowsToEndpoint ctx st)
    (hGate : securityFlowsTo (ctx.threadLabelOf caller) (ctx.endpointLabelOf endpointId) = true) :
    blockedSenderFlowsToEndpoint ctx
      (endpointCallCrossCoreDispatch endpointId caller msg endpointRights
        receiverSlotBase executingCore st).1 := by
  have hWcPre := endpointCallWithCapsOnCore_preserves_blockedSenderFlowsToEndpoint ctx
    endpointId caller msg endpointRights receiverSlotBase executingCore st hObjInv hPre hGate
  have hWcInv := endpointCallWithCapsOnCore_preserves_objects_invExt endpointId caller msg
    endpointRights receiverSlotBase executingCore st hObjInv
  unfold endpointCallCrossCoreDispatch
  cases hWc : endpointCallWithCapsOnCore endpointId caller msg endpointRights
      receiverSlotBase executingCore st with
  | mk st' res =>
    rw [hWc] at hWcPre hWcInv
    simp only at hWcPre hWcInv
    cases res with
    | error e => exact hWcPre
    | ok pair =>
      obtain ⟨summary, sgi⟩ := pair
      simp only []
      -- `split` rather than `cases` on each scrutinee: `maybeReceiver` is a `let`
      -- over the pre-state endpoint lookup, so the stuck scrutinee at each level is
      -- whatever the reduction left, not the expression the source names.
      split
      · split
        · split
          · exact hWcPre
          · rename_i hDon
            have hDonInv := applyCallDonationOnCore_preserves_objects_invExt _ _ _ _ _ _
              hWcInv hDon
            refine blockedSenderFlowsToEndpoint_of_shrinks ?_
              (blockedSenderShrinks_of_ipcStateFrame
                (propagatePipChainCrossCore_ipcStateFrame _ _ executingCore _ hDonInv))
            exact blockedSenderFlowsToEndpoint_of_shrinks hWcPre
              (blockedSenderShrinks_of_ipcStateFrame
                (applyCallDonationOnCore_ipcStateFrame _ _ _ _ _ _ hWcInv hDon))
        all_goals exact hWcPre
      · exact hWcPre

/-- WS-RR RR8.16: **the live `.call` arm carries the blocked-sender flow fact.**

The second half of the lift the `v0.35.126` register row named as owed.  The
denial returns the pre-state; the admitted branch is the full cross-core dispatch
under the gate the branch condition supplies. -/
theorem endpointCallCrossCoreDispatchChecked_preserves_blockedSenderFlowsToEndpoint
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt)
    (hPre : blockedSenderFlowsToEndpoint ctx st) :
    blockedSenderFlowsToEndpoint ctx
      (endpointCallCrossCoreDispatchChecked ctx endpointId caller msg endpointRights
        receiverSlotBase executingCore st).1 := by
  unfold endpointCallCrossCoreDispatchChecked
  split
  · rename_i hGate
    exact endpointCallCrossCoreDispatch_preserves_blockedSenderFlowsToEndpoint ctx endpointId
      caller msg endpointRights receiverSlotBase executingCore st hObjInv hPre
      (endpointFlowGate_implies_securityFlowsTo ctx endpointId _ _ hGate)
  · exact hPre

-- ============================================================================
-- §5  The donation flow fact across the `.send` arm
-- ============================================================================

/-- WS-RR RR8.16: the cross-core send binds no SchedContext.

`donationOwnerFlowsToHolder` — the flow fact's sibling — transports across any
step that leaves every thread's `schedContextBinding` alone, and the send is such
a step on both paths: it writes `ipcState`s, queue links and the endpoint, and
only `.call` donates.  The `.call` chain has had this frame since RR2
(`endpointCallOnCore_sameSchedContextBindings`); its send counterpart did not
exist, so a consumer still had to carry the donation fact by hand across a send. -/
theorem endpointSendDualOnCore_sameSchedContextBindings
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) (hObjInv : st.objects.invExt) :
    sameSchedContextBindings st
      (endpointSendDualOnCore endpointId sender msg executingCore st).1 := by
  unfold endpointSendDualOnCore
  split
  · exact sameSchedContextBindings.refl st
  · split
    · exact sameSchedContextBindings.refl st
    · cases hEp : st.getEndpoint? endpointId with
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
                (.blockedOnSend endpointId) (some msg) with
            | error e => exact sameSchedContextBindings.refl st
            | ok st2 =>
              simp only []
              exact (hS1.trans (storeTcbIpcStateAndMessage_sameSchedContextBindings st1 st2
                sender _ (some msg) hInv1 hIpc)).trans
                (sameSchedContextBindings.of_objects_eq
                  (removeRunnableOnCore_preserves_objects st2 sender executingCore))
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
              cases hRecv : storeTcbReceiveComplete st1 receiver (some msg) with
              | error e => exact sameSchedContextBindings.refl st
              | ok st2 =>
                simp only []
                have hS2 := hS1.trans (storeTcbReceiveComplete_sameSchedContextBindings st1
                  st2 receiver (some msg) hInv1 hRecv)
                have hInv2 := storeTcbReceiveComplete_preserves_objects_invExt st1 st2
                  receiver (some msg) hInv1 hRecv
                obtain ⟨tr, hTrGet, hTrReady⟩ :=
                  storeTcbReceiveComplete_getTcb?_ipcState st1 st2 receiver (some msg)
                    hInv1 hRecv
                exact hS2.trans (wakeThread_sameSchedContextBindings_of_ready st2 receiver
                  executingCore tr hTrGet hTrReady hInv2)

/-- WS-RR RR8.16: and neither does the caps-carrying form — the transfer writes
CNodes and the derivation tree. -/
theorem endpointSendDualWithCapsOnCore_sameSchedContextBindings
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) (hObjInv : st.objects.invExt) :
    sameSchedContextBindings st
      (endpointSendDualWithCapsOnCore endpointId sender msg endpointRights
        receiverSlotBase executingCore st).1 := by
  have hSend := endpointSendDualOnCore_sameSchedContextBindings endpointId sender
    { msg with capsGranted := endpointRights.mem .grant } executingCore st hObjInv
  have hSendInv := endpointSendDualOnCore_preserves_objects_invExt endpointId sender
    { msg with capsGranted := endpointRights.mem .grant } executingCore st hObjInv
  unfold endpointSendDualWithCapsOnCore
  cases hStep : endpointSendDualOnCore endpointId sender
      { msg with capsGranted := endpointRights.mem .grant } executingCore st with
  | mk st' res =>
    rw [hStep] at hSend hSendInv
    simp only at hSend hSendInv
    cases res with
    | error e => exact hSend
    | ok sgi =>
      simp only []
      cases hEp : st.getEndpoint? endpointId with
      | none => simp only []; split <;> exact hSend
      | some ep =>
        simp only []
        cases hHead : ep.receiveQ.head with
        | none => simp only []; split <;> exact hSend
        | some receiverId =>
          simp only []
          split
          · exact hSend
          · cases hRoot : lookupCspaceRoot st' receiverId with
            | none => simp only []; exact hSend
            | some recvRoot =>
              simp only []
              cases hUnwrap : ipcUnwrapCaps
                  { msg with capsGranted := endpointRights.mem .grant } recvRoot
                  receiverSlotBase (endpointRights.mem .grant) st' with
              | error e => simp only []; exact hSend
              | ok pair =>
                obtain ⟨summary, st''⟩ := pair
                simp only []
                exact hSend.trans (ipcUnwrapCaps_sameSchedContextBindings _ recvRoot
                  receiverSlotBase _ st' st'' summary hSendInv hUnwrap)

/-- WS-RR RR8.16: **the live `.send` arm carries the donation flow fact too.**

The sibling half of the lift, and free once the send is known to bind no
SchedContext: `donationOwnerFlowsToHolder_of_sameSchedContextBindings` is what
transports it.

The `.call` arm's counterpart could not be stated **from this direction**: its
dispatch **mints** a donation, so the fact at the post-state is about a binding
the pre-state does not have, and what makes the two ends comparable is the
*receiving* gate the server passed when it blocked on its own `Recv` —
`donationFlowFromBlockedDonor`'s `hReceiveGate` argument, which no state recorded.
`v0.35.196` recorded it (`blockedReceiverFlowsFromEndpoint`, established at the
same store from the receive arm's own gate), so the `.call` lift exists too and
is §6 below; the two differ in the direction their derivation reads, not in
strength. -/
theorem endpointSendCrossCoreDispatchChecked_preserves_donationOwnerFlowsToHolder
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt)
    (hPre : donationOwnerFlowsToHolder ctx st) :
    donationOwnerFlowsToHolder ctx
      (endpointSendCrossCoreDispatchChecked ctx endpointId sender msg endpointRights
        receiverSlotBase executingCore st).1 := by
  unfold endpointSendCrossCoreDispatchChecked
  split
  · exact hPre
  · split
    · exact hPre
    · split
      · exact donationOwnerFlowsToHolder_of_sameSchedContextBindings hPre
          (endpointSendDualWithCapsOnCore_sameSchedContextBindings endpointId sender msg
            endpointRights receiverSlotBase executingCore st hObjInv)
      · exact hPre

-- ============================================================================
-- §6  `v0.35.196` (register row 183) — the donation flow fact across `.call`
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
  exact ⟨tcb, hPre, by rw [hEq]⟩

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
receiving half off `blockedReceiverFlowsFromEndpoint`.  It is demanded only under
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
  -- The migration and the deschedule write no object, so the whole question is
  -- about `applyCallDonation`'s own two stores.
  have hObjs : ∀ oid : SeLe4n.ObjId, st''.objects[oid]? = st'.objects[oid]? := by
    rcases harm with ⟨_, hEq⟩ | ⟨scId, _, hEq⟩ <;> rw [hEq] <;> intro oid
    · rfl
    · rw [migrateSchedContextReplenishment_objects]
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
  rw [lookupTcb_congr_getElem hObjs holder] at hRet
  exact hRet

/-- **WS-RR RR8.16 (`v0.35.196`)**: the rendezvous's two principals are comparable,
read off the pre-state.

The `.call` rendezvous donates the invoking thread's reservation to the endpoint's
**receive-queue head**, so the flow the donation needs is the composition of two
gates that ran at two different times: the caller's, which the dispatch is
evaluating now, and the receiver's, which ran when *it* blocked and which only
`blockedReceiverFlowsFromEndpoint` records.

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
    (hBlockedReceivers : blockedReceiverFlowsFromEndpoint ctx st)
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
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt)
    (hPre : donationOwnerFlowsToHolder ctx st)
    (hBlockedReceivers : blockedReceiverFlowsFromEndpoint ctx st)
    (hQueueHeads : queueHeadBlockedConsistent st)
    (hGate : securityFlowsTo (ctx.threadLabelOf caller)
      (ctx.endpointLabelOf endpointId) = true) :
    donationOwnerFlowsToHolder ctx
      (endpointCallCrossCoreDispatch endpointId caller msg endpointRights
        receiverSlotBase executingCore st).1 := by
  have hWcFrame := endpointCallWithCapsOnCore_sameSchedContextBindings endpointId caller msg
    endpointRights receiverSlotBase executingCore st hObjInv
  have hWcInv := endpointCallWithCapsOnCore_preserves_objects_invExt endpointId caller msg
    endpointRights receiverSlotBase executingCore st hObjInv
  unfold endpointCallCrossCoreDispatch
  cases hWc : endpointCallWithCapsOnCore endpointId caller msg endpointRights
      receiverSlotBase executingCore st with
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

/-- **WS-RR RR8.16 (`v0.35.196`)**: and the flow-checked arm, where the gate the
composition needs is the branch condition itself. -/
theorem endpointCallCrossCoreDispatchChecked_preserves_donationOwnerFlowsToHolder
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt)
    (hPre : donationOwnerFlowsToHolder ctx st)
    (hBlockedReceivers : blockedReceiverFlowsFromEndpoint ctx st)
    (hQueueHeads : queueHeadBlockedConsistent st) :
    donationOwnerFlowsToHolder ctx
      (endpointCallCrossCoreDispatchChecked ctx endpointId caller msg endpointRights
        receiverSlotBase executingCore st).1 := by
  unfold endpointCallCrossCoreDispatchChecked
  split
  · rename_i hGate
    exact endpointCallCrossCoreDispatch_preserves_donationOwnerFlowsToHolder ctx endpointId
      caller msg endpointRights receiverSlotBase executingCore st hObjInv hPre
      hBlockedReceivers hQueueHeads
      (endpointFlowGate_implies_securityFlowsTo ctx endpointId _ _ hGate)
  · exact hPre

end SeLe4n.Kernel
