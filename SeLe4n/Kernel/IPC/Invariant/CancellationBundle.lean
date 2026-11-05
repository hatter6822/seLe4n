-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Invariant.CancellationReplyShape
import SeLe4n.Kernel.IPC.CrossCore.Cancellation
import SeLe4n.Kernel.IPC.Invariant.PerCoreBundlePreservation

/-!
# WS-RR RR8.10 — the cancellation's IPC bundle, over every arm and across cores

`cancelIpcBlocking` matches on the victim's `ipcState`, whose **six**
constructors it services with **four** bodies: the `.ready` identity, one body
shared by `.blockedOnSend` / `.blockedOnReceive` / `.blockedOnCall`, the
`.blockedOnReply` four-step composition, and the `.blockedOnNotification` purge.
Each of the three non-identity bodies has carried an `ipcInvariantFull` result
since `v0.34.95`, `v0.34.96` and `v0.35.82` respectively — each in its own module
and each needing a different engine, because two of them run a whole-store fold
and the third is a composition in which no two steps carry the bundle for the
same reason.  What no theorem stated was the **arm-complete** composite, nor its
lift to the cross-core `cancelIpcBlockingOnCore`.  This module is both, and
nothing else.

**A correction, `v0.35.90`.**  That sentence read "…that the live `.tcbSuspend`
dispatch actually runs", and `cancelIpcBlockingOnCore` is not what it runs:
`Lifecycle.Suspend.suspendThreadOnCore` is, and this module's own host file has
said so since v0.32.61.  The claim was wrong when written (WS-RR RR8.10) and is
struck rather than quietly reworded, because it is the reading that let WS-RR
RR8.12 find two fixes sitting in a transition nothing calls.  The lift is still
worth having — the composite is the prefix the pipeline's G2 reads plus the
victim's deschedule (`cancelIpcBlockingOnCore_eq_reclaimed_deschedule`) — and the
honest statement of its reach is that, not a claim about the dispatch.

Two things decide its shape.

**The premises are per-arm, because the facts are.**  `ipcInvariantFull` entails
none of the queue-coherence facts the three bodies need (that is stated at each
of them and is why they take hypotheses at all), so demanding every fact
unconditionally would make a `.ready` cancellation — which commits no write at
all — carry the reply arm's five-fact pack.  `cancelIpcBlockingArmPremises` gates
each group on the arm's own `ipcState` equation, so a caller discharges exactly
what its arm reaches, and the `.ready` arm discharges nothing.

**No conjunct reads the scheduler**, which is what makes the cross-core lift
short rather than a second nineteen-conjunct argument.  Every conjunct is a
property of the object store alone (`v0.36.136` retired `passiveServerIdle`, the
one that read the boot core's run queue and `current` slot), so the three
scheduler steps the composite adds over the teardown — the replenishment
migration, the reclaim's holder deschedule and the victim's placement removal —
write only run-queue links in TCBs and scheduler state, and
`ipcInvariantFull_of_objectsAgreeOffRunLinks` transports the whole bundle across
them.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)


/-- The restore's own half of `cancelIpcBlocking_victim_ready`: the thread the
staging restore writes ends `.ready`.

Factored out because three of the four arms end in a restore and the fourth is
the identity, so this is the only place the field is actually established. -/
private theorem restoreVictimReady (v : SeLe4n.ThreadId)
    (s : SystemState) (tV : TCB) (f : Option Architecture.SyscallReturnFrame)
    (hI : s.objects.invExt) (hL : lookupTcb s v = some tV) :
    ∀ t', (Lifecycle.Suspend.restoreToReadyStaging s v f).objects[v.toObjId]? = some (.tcb t') →
      t'.ipcState = ThreadIpcState.ready := by
  intro t' h
  rcases restoreToReadyStaging_tcb_pullback s v f tV hI hL v.toObjId t' h with ⟨hne, _⟩ | ⟨_, rfl⟩
  · exact absurd rfl hne
  · unfold restoredTcb
    cases f <;> rfl

/-- **WS-RR RR8.10**: a cancelled victim ends `.ready`, on every arm.

What the suspend's runnability argument and the cancel-all sweep read off the
teardown: the victim leaves the cancellation able to run, and that is
*established* here rather than assumed at each call site.

Each arm for its own reason.  `.ready` commits no write at all, so the victim's
stored TCB carries the IPC state the caller read (WS-ZA ZA6.33: read off any
TCB with that state, so a step before the teardown may rewrite other fields).  The three endpoint states and the
notification state end in `restoreToReadyCancelled` over a queue removal, whose
write at the victim's key is `restoredTcb` (`ipcState := .ready` by
construction).  The reply arm's restore sits over the reclaim and the splice —
neither of which moves a TCB's `ipcState`, and the splice moves no TCB at all —
and its trailing `consumeReplyLink` clears `replyObject` and copies every other
field, which is what `SystemState.consumeCallerReply_tcb_caller` states field by
field. -/
theorem cancelIpcBlocking_victim_ready_of_ipcState
    (st : SystemState) (v : SeLe4n.ThreadId) (tcbV x : TCB)
    (hObjInv : st.objects.invExt) (hAt : st.objects[v.toObjId]? = some (.tcb x))
    (hNR : ¬ v.isReserved) (hX : x.ipcState = tcbV.ipcState) :
    ∀ t', (Lifecycle.Suspend.cancelIpcBlocking st v tcbV).objects[v.toObjId]? = some (.tcb t') →
      t'.ipcState = ThreadIpcState.ready := by
  cases hIp : tcbV.ipcState with
  | ready =>
    rw [show Lifecycle.Suspend.cancelIpcBlocking st v tcbV = st by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hIp]]
    intro t' h
    rw [hAt] at h
    cases h
    rw [hX]; exact hIp
  | blockedOnSend ep =>
    rw [show Lifecycle.Suspend.cancelIpcBlocking st v tcbV =
        Lifecycle.Suspend.restoreToReadyCancelled (removeFromBlockingEndpoint st v ep) v by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hIp]]
    unfold Lifecycle.Suspend.restoreToReadyCancelled
    obtain ⟨hI1, t1, hL1, _⟩ := removeFromBlockingEndpoint_tcb_lookup st v ep v.toObjId x hObjInv hAt
    exact restoreVictimReady v _ t1 _ hI1 (lookupTcb_of_objects_of_not_reserved _ v t1 hL1 hNR)
  | blockedOnReceive ep =>
    rw [show Lifecycle.Suspend.cancelIpcBlocking st v tcbV =
        Lifecycle.Suspend.restoreToReadyCancelled (removeFromBlockingEndpoint st v ep) v by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hIp]]
    unfold Lifecycle.Suspend.restoreToReadyCancelled
    obtain ⟨hI1, t1, hL1, _⟩ := removeFromBlockingEndpoint_tcb_lookup st v ep v.toObjId x hObjInv hAt
    exact restoreVictimReady v _ t1 _ hI1 (lookupTcb_of_objects_of_not_reserved _ v t1 hL1 hNR)
  | blockedOnCall ep =>
    rw [show Lifecycle.Suspend.cancelIpcBlocking st v tcbV =
        Lifecycle.Suspend.restoreToReadyCancelled (removeFromBlockingEndpoint st v ep) v by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hIp]]
    unfold Lifecycle.Suspend.restoreToReadyCancelled
    obtain ⟨hI1, t1, hL1, _⟩ := removeFromBlockingEndpoint_tcb_lookup st v ep v.toObjId x hObjInv hAt
    exact restoreVictimReady v _ t1 _ hI1 (lookupTcb_of_objects_of_not_reserved _ v t1 hL1 hNR)
  | blockedOnNotification nId =>
    rw [cancelIpcBlocking_notification_arm_eq st v tcbV nId hIp]
    unfold purgedAndRestored
    obtain ⟨hI1, t1, hL1, _⟩ :=
      removeFromNotificationWaitQueue_tcb_lookup st v v.toObjId x hObjInv hAt
    exact restoreVictimReady v _ t1 _ hI1 (lookupTcb_of_objects_of_not_reserved _ v t1 hL1 hNR)
  | blockedOnReply ep rt =>
    rw [cancelIpcBlocking_reply_arm_eq st v tcbV ep rt hIp]
    -- the reclaim, then the splice: both keep a TCB at the victim's key
    have hIR : (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV).objects.invExt :=
      Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt st v tcbV hObjInv
    obtain ⟨tR, hAtR, _⟩ :=
      Lifecycle.Suspend.returnDonationToCancelledCaller_tcb_lookup st v tcbV hObjInv
        v.toObjId x hAt
    have hIX : (cutThreadReplyFrameOut
        (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV).objects.invExt :=
      cutThreadReplyFrameOut_preserves_objects_invExt _ tcbV hIR
    have hAtX := cutThreadReplyFrameOut_tcb_eq _ tcbV hIR v.toObjId tR hAtR
    unfold restoredAndConsumed
    have hGetX : (cutThreadReplyFrameOut
        (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV).getTcb? v = some tR :=
      (SystemState.getTcb?_eq_some_iff _ v tR).mpr hAtX
    have hAtY := restoreToReadyStaging_objects_self _ v (some Architecture.cancelledIpcFrame) tR
      hIX hGetX
    have hReadyY : (restoredTcb tR (some Architecture.cancelledIpcFrame)).ipcState
        = ThreadIpcState.ready := by
      unfold restoredTcb; rfl
    -- the teardown then clears the reply link, which moves no other field
    cases hRO : tcbV.replyObject with
    | none =>
      rw [Lifecycle.Suspend.consumeReplyLink_none _ v tcbV hRO]
      intro t' h
      obtain ⟨t0, h, e⟩ :=
        (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffRunLinks _ v _).get_tcb' h
      rw [TCB.proj_eq_of_withoutRunLinks_eq TCB.ipcState e]
      rw [hAtY] at h
      cases h
      exact hReadyY
    | some rid =>
      intro t' h
      obtain ⟨t0, h, e⟩ :=
        (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffRunLinks _ v _).get_tcb' h
      rw [TCB.proj_eq_of_withoutRunLinks_eq TCB.ipcState e]
      rw [Lifecycle.Suspend.consumeReplyLink_some _ v tcbV rid hRO] at h
      have hIY : (Lifecycle.Suspend.restoreToReadyStaging
          (cutThreadReplyFrameOut
            (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV) v
          (some Architecture.cancelledIpcFrame)).objects.invExt :=
        Lifecycle.Suspend.restoreToReadyStaging_invExt _ v _ hIX
      have hPost := SystemState.consumeCallerReply_tcb_caller _ _ v rid hIY
        (SystemState.consumeCallerReply_eq_link _ v rid) _ hAtY
      rw [hPost] at h
      cases h
      exact hReadyY

/-- ...read off the victim's own TCB. -/
theorem cancelIpcBlocking_victim_ready
    (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB)
    (hObjInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV) :
    ∀ t', (Lifecycle.Suspend.cancelIpcBlocking st v tcbV).objects[v.toObjId]? = some (.tcb t') →
      t'.ipcState = ThreadIpcState.ready :=
  cancelIpcBlocking_victim_ready_of_ipcState st v tcbV tcbV hObjInv
    (lookupTcb_some_objects st v tcbV hLookup) (lookupTcb_some_not_reserved st v tcbV hLookup) rfl

-- ============================================================================
-- §2  The four-arm composite over the pure teardown
-- ============================================================================

/-- **WS-RR RR8.10**: the reply arm's five premises, named.

They are cited together everywhere — the arm keystone takes all five — so they
get one name rather than five positional hypotheses threaded through the
composite.  None is entailed by `ipcInvariantFull`: the reply-stack resolution
(`cancelDonationResolves`) follows from `donationChainWellFormed`, a separate
predicate, or from a pre-state commit check, `sweptThreadOffQueueChains` is the queue-connectivity fact
the bundle carries nowhere, and the last three are the local coherence facts
WS-HP HP7 measured as stated rather than derived.  (`v0.36.136` retired a sixth,
the queue coherence of a holder the reclaim used to pull off its endpoint: the
reclaim no longer touches the holder's queue.) -/
structure cancelReplyArmPremises (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB) : Prop where
  resolves : cancelDonationResolves st v tcbV
  offQueue : sweptThreadOffQueueChains st v
  owed : ∀ rid, tcbV.replyObject = some rid → replyFrameHeadHolderDonation st rid v
  holder : donatedContextIsOwnerFrameHead st v
  stack : cancelDonationStackValid st v tcbV

/-- **WS-RR RR8.10**: the teardown's premises, **gated on the arm that needs
them**.

Three fields, one per non-identity arm, each an implication from that arm's own
`ipcState` equation.  The `.ready` arm appears nowhere, which is the point: it
commits no write, so it owes nothing, and an unconditional pack would have made
it carry the reply arm's five facts to prove that the identity preserves the
bundle.

The gate is the `ipcState` equation rather than a re-spelled arm classifier,
because that equation is exactly what each arm theorem already takes — so a
caller that has the equation has the gate, and no second reading of "which arm is
this" enters the tree. -/
structure cancelIpcBlockingArmPremises (st : SystemState) (v : SeLe4n.ThreadId)
    (tcbV : TCB) : Prop where
  endpointArm : ∀ epId, (tcbV.ipcState = ThreadIpcState.blockedOnSend epId ∨
      tcbV.ipcState = ThreadIpcState.blockedOnReceive epId ∨
      tcbV.ipcState = ThreadIpcState.blockedOnCall epId) → sweptThreadQueueCoherent st v
  notificationArm : ∀ nId, tcbV.ipcState = ThreadIpcState.blockedOnNotification nId →
    sweptThreadOffQueueChains st v
  replyArm : ∀ epV rtV, tcbV.ipcState = ThreadIpcState.blockedOnReply epV rtV →
    cancelReplyArmPremises st v tcbV

/-- **WS-RR RR8.10 — the arm-complete composite**: `cancelIpcBlocking` preserves
`ipcInvariantFull` on every one of its four bodies.

The first half of the RR7.22 residual's second half: the three arm theorems
landed one per cut in three modules, and nothing put them together, so no caller
could cite "the cancellation preserves the bundle" without case-splitting on
`ipcState` itself and re-deriving which arm needs what.

A case analysis and nothing more — every arm's content is at its own theorem,
which is where it belongs.  The `.ready` arm is the identity
(`cancelIpcBlocking`'s own `.ready` branch returns `st`), so it is the hypothesis
returned unchanged. -/
theorem cancelIpcBlocking_preserves_ipcInvariantFull
    (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB)
    (hObjInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV)
    (hBundle : ipcInvariantFull st) (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hArms : cancelIpcBlockingArmPremises st v tcbV) :
    ipcInvariantFull (Lifecycle.Suspend.cancelIpcBlocking st v tcbV) := by
  cases hIp : tcbV.ipcState with
  | ready =>
    rw [show Lifecycle.Suspend.cancelIpcBlocking st v tcbV = st by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hIp]]
    exact hBundle
  | blockedOnSend ep =>
    exact cancelIpcBlocking_endpointArm_preserves_ipcInvariantFull st v tcbV ep hObjInv hLookup
      (Or.inl hIp) hBundle hAllBudgetsNone (hArms.endpointArm ep (Or.inl hIp))
  | blockedOnReceive ep =>
    exact cancelIpcBlocking_endpointArm_preserves_ipcInvariantFull st v tcbV ep hObjInv hLookup
      (Or.inr (Or.inl hIp)) hBundle hAllBudgetsNone (hArms.endpointArm ep (Or.inr (Or.inl hIp)))
  | blockedOnCall ep =>
    exact cancelIpcBlocking_endpointArm_preserves_ipcInvariantFull st v tcbV ep hObjInv hLookup
      (Or.inr (Or.inr hIp)) hBundle hAllBudgetsNone (hArms.endpointArm ep (Or.inr (Or.inr hIp)))
  | blockedOnNotification nId =>
    exact cancelIpcBlocking_notificationArm_preserves_ipcInvariantFull st v tcbV nId hObjInv
      hLookup hIp hBundle (hArms.notificationArm nId hIp)
  | blockedOnReply ep rt =>
    have hR := hArms.replyArm ep rt hIp
    exact cancelIpcBlocking_replyArm_preserves_ipcInvariantFull st v tcbV ep rt hObjInv hLookup
      hIp hBundle hR.resolves (hAllBudgetsNone v tcbV (lookupTcb_some_objects st v tcbV hLookup))
      hR.offQueue hR.owed hR.holder hR.stack

-- ============================================================================
-- §4  The lift to the cross-core composite
-- ============================================================================

/-- **WS-RR RR8.10 — the payoff**: the **cross-core** cancellation preserves
`ipcInvariantFull`, on every arm.

The transition the live `.tcbSuspend` dispatch runs, and the second half of the
RR7.22 residual.  Its premises are the teardown's and nothing more: the three
scheduler steps the composite adds over `cancelIpcBlocking` write only run-queue
links in TCBs and scheduler state, and no conjunct of the bundle reads either
(`v0.36.136` retired the one that read the boot core's run queue), so objects
unchanged off the scheduler links (`cancelIpcBlockingOnCore_objectsAgreeOffSchedulerLinks`,
which is where the three steps' object frames already compose) is the whole
argument. -/
theorem cancelIpcBlockingOnCore_preserves_ipcInvariantFull
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) (hLookup : lookupTcb st victim = some tcb)
    (hBundle : ipcInvariantFull st) (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hArms : cancelIpcBlockingArmPremises st victim tcb) :
    ipcInvariantFull (cancelIpcBlockingOnCore victim tcb executingCore st).1 :=
  ipcInvariantFull_of_objectsAgreeOffSchedulerLinks
    (cancelIpcBlockingOnCore_objectsAgreeOffSchedulerLinks victim tcb executingCore st)
    (cancelIpcBlocking_preserves_ipcInvariantFull st victim tcb hObjInv hLookup
      hBundle hAllBudgetsNone hArms)

-- ============================================================================
-- §4  WS-RR RR8.11 — the composite establishes the SM5.H replenish-affinity
--     invariant
-- ============================================================================
--
-- **`v0.35.166`: seven of this section's frames moved out, and the reason is a
-- layering fact rather than tidiness.**  This module is downstream of the
-- destroy path (`Lifecycle/Operations/CleanupPreservation.lean`) *and* of the
-- retype wrapper, so a frame written `private` here is invisible to the retype's
-- own reservation theorems — which is precisely why register row 63 could not be
-- stated until now.  Each one is public and beside the fact its proof rests on:
--
--   * `SystemState.getSchedContext?_eq_of_kind_iff` and
--     `SystemState.map_tcbField_eq_of_refines` → `Model/State.lean`, beside
--     `getSchedContext?_eq_some_iff` / `getTcb?_eq_some_iff`, whose unfolding is
--     the whole of each proof.  Both are generic bridges between the kind
--     biconditionals the store's frames produce and the typed readings the
--     invariants read, so their owner is the accessor, not this bundle.
--   * `spliceOutMidQueueNode_placement_frame` → `CleanupPreservation.lean`,
--     beside `spliceOutMidQueueNode_tcb_lookup` / `_tcb_backward`.
--   * `removeFromAllEndpointQueues_getSchedContext?_eq` / `_placement_frame` →
--     `Lifecycle/Invariant/CancellationQueueShape.lean`, beside
--     `removeFromAllEndpointQueues_nonEndpoint`.
--   * `removeFromNotificationWaitQueue_getSchedContext?_eq` /
--     `_placement_frame` (and the `Option`-level `_getTcb?_eq` the second is one
--     consequence of) → `Lifecycle/Invariant/CancellationNotificationShape.lean`,
--     beside `removeFromNotificationWaitQueue_nonNotification`.
--
-- Nothing below changed but the names; the frames this section keeps are the
-- ones whose subjects are cancellation-path steps and have no second asker.

/-- WS-RR RR8.11: the restore writes one TCB, so it writes no scheduling
context. -/
theorem restoreToReadyStaging_getSchedContext?_eq (st : SystemState)
    (tid : SeLe4n.ThreadId) (frame : Option Architecture.SyscallReturnFrame)
    (hInv : st.objects.invExt) (scId : SeLe4n.SchedContextId) :
    (Lifecycle.Suspend.restoreToReadyStaging st tid frame).getSchedContext? scId
      = st.getSchedContext? scId := by
  refine SystemState.getSchedContext?_eq_of_kind_iff (fun sc => ?_)
  rw [restoreToReadyStaging_eq]
  cases hT : st.getTcb? tid with
  | none => exact Iff.rfl
  | some tcb =>
    by_cases hk : scId.toObjId = tid.toObjId
    · -- the one key the restore writes holds a TCB before and after, so neither
      -- side of the reading is a scheduling context
      rw [hk, (SystemState.getTcb?_eq_some_iff st tid tcb).mp hT,
        show (({ st with objects :=
              st.objects.insert tid.toObjId (.tcb (restoredTcb tcb frame)) } :
              SystemState).objects[tid.toObjId]?)
            = some (.tcb (restoredTcb tcb frame)) from
          SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _
            hInv]
      simp
    · rw [show (({ st with objects :=
              st.objects.insert tid.toObjId (.tcb (restoredTcb tcb frame)) } :
              SystemState).objects[scId.toObjId]?) = st.objects[scId.toObjId]? from
        SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId
          scId.toObjId _ (by simpa using Ne.symm hk) hInv]

/-- WS-RR RR8.11: the frame cut writes Reply objects only. -/
theorem cutThreadReplyFrameOut_getSchedContext?_eq (st : SystemState)
    (tcb : TCB) (hInv : st.objects.invExt) (scId : SeLe4n.SchedContextId) :
    (cutThreadReplyFrameOut st tcb).getSchedContext? scId = st.getSchedContext? scId := by
  unfold cutThreadReplyFrameOut
  cases tcb.replyObject with
  | none => rfl
  | some rid => exact cutReplyFrameOutOrSelf_getSchedContext?_eq st rid hInv scId

/-- WS-RR RR8.11: the reply-link teardown writes a TCB and a Reply, so it writes
no scheduling context — RR8.5's projection of the reply path's own consume, whose
frame `consumeCallerReply_getSchedContext?_eq` states. -/
theorem consumeReplyLink_getSchedContext?_eq (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hInv : st.objects.invExt)
    (scId : SeLe4n.SchedContextId) :
    (Lifecycle.Suspend.consumeReplyLink st tid tcb).getSchedContext? scId
      = st.getSchedContext? scId := by
  unfold Lifecycle.Suspend.consumeReplyLink
  cases hR : tcb.replyObject with
  | none => rfl
  | some rid =>
    exact consumeCallerReply_getSchedContext?_eq st _ tid rid hInv
      (SystemState.consumeCallerReply_eq_link st tid rid) scId

/-- WS-RR RR8.11: **the reclaim writes exactly the scheduling context it hands
back.**  Its three refusing shapes — no donation resolved, a caller with no TCB,
and a refused return — commit nothing at all, and on the committing shape the only
SchedContext store is `returnDonatedSchedContext`'s at `scId`. -/
private theorem returnDonationToCancelledCaller_getSchedContext?_ne (st : SystemState)
    (v : SeLe4n.ThreadId) (tcbV : TCB) (hInv : st.objects.invExt)
    (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (scId₀ : SeLe4n.SchedContextId)
    (hD : Lifecycle.Suspend.cancelledCallerDonation? st v tcbV = some (scId, holder))
    (hne : scId₀ ≠ scId) :
    (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV).getSchedContext? scId₀
      = st.getSchedContext? scId₀ := by
  unfold Lifecycle.Suspend.returnDonationToCancelledCaller
  rw [hD]
  cases hT : st.getTcb? v with
  | none => rfl
  | some _ =>
    dsimp only
    cases hRet : returnDonatedSchedContextResolved st holder scId v with
    | error _ => rfl
    | ok st' =>
      obtain ⟨newOwner?, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
      exact returnDonatedSchedContext_getSchedContext?_ne _ st' holder scId scId₀ v hne hInv
        newOwner? hPop

/-- **WS-RR RR8.11: the teardown writes a scheduling context only through the
reclaim.**

Five of the six `ipcState` constructors write none at all: the `.ready` identity
commits nothing, the three endpoint states run a splice and a whole-store endpoint
sweep followed by the restore, and `.blockedOnNotification` runs a notification
purge followed by the restore.  Only `.blockedOnReply` can write one, and only
through the reclaim — so the reclaim's own frame at a key is the teardown's frame
at that key, which is what this takes as its hypothesis.

Stated this way rather than with the exclusion built in because the two callers
ask different questions of it: one excludes the context the resolver names (the
committing case), the other has the whole reclaim inert (the refused case).  One
six-arm analysis, two corollaries. -/
theorem cancelIpcBlocking_getSchedContext?_eq_of_reclaim_frame (st : SystemState)
    (v : SeLe4n.ThreadId) (tcbV : TCB) (hInv : st.objects.invExt)
    (scId₀ : SeLe4n.SchedContextId)
    (hReclaim : (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV).getSchedContext? scId₀
      = st.getSchedContext? scId₀) :
    (Lifecycle.Suspend.cancelIpcBlocking st v tcbV).getSchedContext? scId₀
      = st.getSchedContext? scId₀ := by
  unfold Lifecycle.Suspend.cancelIpcBlocking Lifecycle.Suspend.restoreToReadyCancelled
  cases hIp : tcbV.ipcState with
  | ready => rfl
  | blockedOnSend e =>
    rw [restoreToReadyStaging_getSchedContext?_eq _ v _
        (removeFromBlockingEndpoint_preserves_objects_invExt st v e hInv),
      removeFromBlockingEndpoint_getSchedContext?_eq st v e hInv]
  | blockedOnReceive e =>
    rw [restoreToReadyStaging_getSchedContext?_eq _ v _
        (removeFromBlockingEndpoint_preserves_objects_invExt st v e hInv),
      removeFromBlockingEndpoint_getSchedContext?_eq st v e hInv]
  | blockedOnCall e =>
    rw [restoreToReadyStaging_getSchedContext?_eq _ v _
        (removeFromBlockingEndpoint_preserves_objects_invExt st v e hInv),
      removeFromBlockingEndpoint_getSchedContext?_eq st v e hInv]
  | blockedOnNotification _ =>
    rw [restoreToReadyStaging_getSchedContext?_eq _ v _
        (removeFromNotificationWaitQueue_preserves_objects_invExt st v hInv),
      removeFromNotificationWaitQueue_getSchedContext?_eq st v hInv]
  | blockedOnReply ep rt =>
    have hR := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt
      st v tcbV hInv
    have hS := cutThreadReplyFrameOut_preserves_objects_invExt
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV hR
    dsimp only
    rw [(SystemState.unlinkReplyWaiterOpt_objectsAgreeOffRunLinks _ v _).getSchedContext?,
      consumeReplyLink_getSchedContext?_eq _ v tcbV
        (Lifecycle.Suspend.restoreToReadyStaging_invExt _ v _ hS),
      restoreToReadyStaging_getSchedContext?_eq _ v _ hS,
      cutThreadReplyFrameOut_getSchedContext?_eq _ tcbV hR, hReclaim]

/-- **WS-RR RR8.11: the teardown writes at most ONE scheduling context** — the one
the reclaim hands back to the cancelled caller — so every other context reads
through it unchanged.

Stated with the exclusion as a hypothesis **over the resolver** rather than over a
supplied id, because the context is *resolved* rather than passed: a caller that
has not resolved it discharges the hypothesis vacuously, and one that has
discharges it from its own distinctness. -/
theorem cancelIpcBlocking_getSchedContext?_ne (st : SystemState) (v : SeLe4n.ThreadId)
    (tcbV : TCB) (hInv : st.objects.invExt) (scId₀ : SeLe4n.SchedContextId)
    (hne : ∀ scId holder, Lifecycle.Suspend.cancelledCallerDonation? st v tcbV
      = some (scId, holder) → scId₀ ≠ scId) :
    (Lifecycle.Suspend.cancelIpcBlocking st v tcbV).getSchedContext? scId₀
      = st.getSchedContext? scId₀ := by
  refine cancelIpcBlocking_getSchedContext?_eq_of_reclaim_frame st v tcbV hInv scId₀ ?_
  cases hD : Lifecycle.Suspend.cancelledCallerDonation? st v tcbV with
  | none => rw [Lifecycle.Suspend.returnDonationToCancelledCaller_none st v tcbV hD]
  | some p =>
    obtain ⟨scId, holder⟩ := p
    exact returnDonationToCancelledCaller_getSchedContext?_ne st v tcbV hInv scId holder
      scId₀ hD (hne scId holder hD)

/-- **WS-RR RR8.11: a teardown whose reclaim committed nothing writes no scheduling
context at all** — including the one the resolver names, which is the key the
`_ne` form above deliberately excludes.  This is the reading the refused-reclaim
case needs, and it is what makes the migration's destination degenerate to its own
source there. -/
theorem cancelIpcBlocking_getSchedContext?_eq_of_reclaim_inert (st : SystemState)
    (v : SeLe4n.ThreadId) (tcbV : TCB) (hInv : st.objects.invExt)
    (hInert : Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV = st)
    (scId₀ : SeLe4n.SchedContextId) :
    (Lifecycle.Suspend.cancelIpcBlocking st v tcbV).getSchedContext? scId₀
      = st.getSchedContext? scId₀ :=
  cancelIpcBlocking_getSchedContext?_eq_of_reclaim_frame st v tcbV hInv scId₀ (by rw [hInert])

/-- WS-ZA ZA6.3: **the reclaim holds the release queues** — its one context
store, the hand-back's, keeps the context's release fields. -/
theorem returnDonationToCancelledCaller_releaseStateAgree (st : SystemState)
    (v : SeLe4n.ThreadId) (tcbV : TCB) (hInv : st.objects.invExt) :
    SystemState.releaseStateAgree (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) st := by
  cases hD : Lifecycle.Suspend.cancelledCallerDonation? st v tcbV with
  | none =>
    rw [Lifecycle.Suspend.returnDonationToCancelledCaller_none st v tcbV hD]; exact .refl st
  | some p =>
    obtain ⟨scId, holder⟩ := p
    unfold Lifecycle.Suspend.returnDonationToCancelledCaller
    rw [hD]
    cases hT : st.getTcb? v with
    | none => exact .refl st
    | some _ =>
      dsimp only
      cases hRet : returnDonatedSchedContextResolved st holder scId v with
      | error _ => exact .refl st
      | ok st' =>
        obtain ⟨_, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
        exact returnDonatedSchedContext_releaseStateAgree hInv hPop

/-- WS-ZA ZA6.3: **the teardown holds the release queues** — it writes a
context only through the reclaim, which keeps its release fields, and no
release-queue slot. -/
theorem cancelIpcBlocking_releaseStateAgree (st : SystemState) (v : SeLe4n.ThreadId)
    (tcbV : TCB) (hInv : st.objects.invExt) :
    SystemState.releaseStateAgree (Lifecycle.Suspend.cancelIpcBlocking st v tcbV) st := by
  refine ⟨?_, by rw [Lifecycle.Suspend.cancelIpcBlocking_scheduler_eq st v tcbV]; rfl⟩
  have hEp : ∀ e s, (Lifecycle.Suspend.restoreToReadyStaging
      (removeFromBlockingEndpoint st v e) v
      (some Architecture.cancelledIpcFrame)).getSchedContext? s = st.getSchedContext? s :=
    fun e s => by
      rw [restoreToReadyStaging_getSchedContext?_eq _ v _
          (removeFromBlockingEndpoint_preserves_objects_invExt st v e hInv),
        removeFromBlockingEndpoint_getSchedContext?_eq st v e hInv]
  unfold Lifecycle.Suspend.cancelIpcBlocking Lifecycle.Suspend.restoreToReadyCancelled
  cases hIp : tcbV.ipcState with
  | ready => exact .refl _
  | blockedOnSend e => exact .of_getSchedContext? (hEp e)
  | blockedOnReceive e => exact .of_getSchedContext? (hEp e)
  | blockedOnCall e => exact .of_getSchedContext? (hEp e)
  | blockedOnNotification _ =>
    exact .of_getSchedContext? fun s => by
      rw [restoreToReadyStaging_getSchedContext?_eq _ v _
          (removeFromNotificationWaitQueue_preserves_objects_invExt st v hInv),
        removeFromNotificationWaitQueue_getSchedContext?_eq st v hInv]
  | blockedOnReply ep rt =>
    have hR := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt
      st v tcbV hInv
    have hS := cutThreadReplyFrameOut_preserves_objects_invExt
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV hR
    dsimp only
    refine SystemState.ReleaseLinksAgree.trans (.of_getSchedContext? fun s => ?_)
      (returnDonationToCancelledCaller_releaseStateAgree st v tcbV hInv).1
    rw [(SystemState.unlinkReplyWaiterOpt_objectsAgreeOffRunLinks _ v _).getSchedContext?,
      consumeReplyLink_getSchedContext?_eq _ v tcbV
        (Lifecycle.Suspend.restoreToReadyStaging_invExt _ v _ hS),
      restoreToReadyStaging_getSchedContext?_eq _ v _ hS,
      cutThreadReplyFrameOut_getSchedContext?_eq _ tcbV hR]

/-- WS-ZA ZA6.33: a thread's refill view reads its suspension alone. -/
theorem tcbRefillView_bind_of_threadState {a b : SystemState} {t : SeLe4n.ThreadId}
    (h : (a.getTcb? t).map TCB.threadState = (b.getTcb? t).map TCB.threadState) :
    (a.getTcb? t).bind tcbRefillView = (b.getTcb? t).bind tcbRefillView := by
  revert h
  cases a.getTcb? t <;> cases b.getTcb? t <;> intro h
  · rfl
  · cases h
  · cases h
  · simp only [Option.map_some, Option.some.injEq] at h
    simp only [Option.bind_some, tcbRefillView, h]

/-- WS-ZA ZA6.33: the restore keeps every refill view: it writes one thread and
leaves its suspension alone. -/
theorem restoreToReadyStaging_refillViewsKept (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (hInv : st.objects.invExt) :
    RefillViewsKept (Lifecycle.Suspend.restoreToReadyStaging st tid frame) st := by
  unfold Lifecycle.Suspend.restoreToReadyStaging
  exact .updateTcb _ _ _ hInv (fun x h => by cases frame <;> exact h)

/-- WS-ZA ZA6.33: the cancelled caller's donation return keeps every context's
refills off the returned one (`returnDonatedSchedContext_refillsKeptOff`). -/
theorem returnDonationToCancelledCaller_refillsKeptOff (st : SystemState)
    (v : SeLe4n.ThreadId) (tcbV : TCB) (hInv : st.objects.invExt)
    (P : SeLe4n.SchedContextId → Prop)
    (hP : ∀ p, Lifecycle.Suspend.cancelledCallerDonation? st v tcbV = some p → P p.1) :
    SystemState.RefillsKeptOff P (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) st := by
  cases hD : Lifecycle.Suspend.cancelledCallerDonation? st v tcbV with
  | none =>
    rw [Lifecycle.Suspend.returnDonationToCancelledCaller_none st v tcbV hD]
    exact .refl P st
  | some p =>
    obtain ⟨scId, holder⟩ := p
    have hS : P scId := hP _ hD
    unfold Lifecycle.Suspend.returnDonationToCancelledCaller
    rw [hD]
    cases hT : st.getTcb? v with
    | none => exact .refl P st
    | some _ =>
      dsimp only
      cases hRet : returnDonatedSchedContextResolved st holder scId v with
      | error _ => exact .refl P st
      | ok st' =>
        obtain ⟨_, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
        exact (returnDonatedSchedContext_refillsKeptOff hInv hPop).mono fun x hx => by subst hx; exact hS

/-- WS-ZA ZA6.33: **everything the teardown does but the return keeps every
refill view** — the queue removals and the frame cut write no context and no
suspension, the restore and the reply-link consume rewrite no suspension. -/
theorem cancelIpcBlocking_refillViewsKept_of_return (st : SystemState) (v : SeLe4n.ThreadId)
    (tcbV : TCB) (hInv : st.objects.invExt) :
    RefillViewsKept (Lifecycle.Suspend.cancelIpcBlocking st v tcbV)
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) := by
  have hNone : ∀ (h : Lifecycle.Suspend.cancelledCallerDonation? st v tcbV = none),
      Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV = st :=
    Lifecycle.Suspend.returnDonationToCancelledCaller_none st v tcbV
  have hEp : ∀ e, RefillViewsKept (Lifecycle.Suspend.restoreToReadyStaging
      (removeFromBlockingEndpoint st v e) v (some Architecture.cancelledIpcFrame)) st :=
    fun e => (restoreToReadyStaging_refillViewsKept _ v _
      (removeFromBlockingEndpoint_preserves_objects_invExt st v e hInv)).trans
      (.of_getSchedContext?_eq (removeFromBlockingEndpoint_getSchedContext?_eq st v e hInv)
        fun t => tcbRefillView_bind_of_threadState (by
          rw [removeFromBlockingEndpoint_getTcb?_eq_splice st v e hInv t]
          exact spliceOutMidQueueNode_tcbField_frame TCB.threadState
            (fun _ _ _ _ _ _ => rfl) st v hInv t))
  unfold Lifecycle.Suspend.cancelIpcBlocking Lifecycle.Suspend.restoreToReadyCancelled
  cases hIp : tcbV.ipcState with
  | ready =>
    rw [hNone (Lifecycle.Suspend.cancelledCallerDonation?_of_ready st v tcbV hIp)]; exact .refl _
  | blockedOnSend e | blockedOnReceive e | blockedOnCall e =>
    rw [hNone (by unfold Lifecycle.Suspend.cancelledCallerDonation?; rw [hIp])]; exact hEp e
  | blockedOnNotification _ =>
    rw [hNone (by unfold Lifecycle.Suspend.cancelledCallerDonation?; rw [hIp])]
    exact (restoreToReadyStaging_refillViewsKept _ v _
      (removeFromNotificationWaitQueue_preserves_objects_invExt st v hInv)).trans
      (.of_getSchedContext?_eq (removeFromNotificationWaitQueue_getSchedContext?_eq st v hInv)
        fun t => tcbRefillView_bind_of_threadState
          (removeFromNotificationWaitQueue_tcbField_frame TCB.threadState
            (fun _ _ _ _ _ _ => rfl) st v hInv t))
  | blockedOnReply ep rt =>
    have hR := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt
      st v tcbV hInv
    have hS := cutThreadReplyFrameOut_preserves_objects_invExt
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV hR
    have hU := Lifecycle.Suspend.restoreToReadyStaging_invExt _ v
      (some Architecture.cancelledIpcFrame) hS
    dsimp only
    refine (RefillViewsKept.of_agreeOffRunLinks
      (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffRunLinks _ v _)).trans ?_
    refine (RefillViewsKept.of_getSchedContext?_eq
      (consumeReplyLink_getSchedContext?_eq _ v tcbV hU)
      fun t => tcbRefillView_bind_of_threadState
        (consumeReplyLink_map_frame TCB.threadState (fun _ => rfl) _ v tcbV hU t)).trans ?_
    refine (restoreToReadyStaging_refillViewsKept _ v _ hS).trans ?_
    exact .of_getSchedContext?_eq (cutThreadReplyFrameOut_getSchedContext?_eq _ tcbV hR)
      fun t => by rw [cutThreadReplyFrameOut_getTcb?_eq _ tcbV hR]

/-- WS-ZA ZA6.4: **the teardown with nothing to return keeps every context's
refill view**. -/
theorem cancelIpcBlocking_refillViewsKept (st : SystemState) (v : SeLe4n.ThreadId)
    (tcbV : TCB) (hInv : st.objects.invExt)
    (hD : Lifecycle.Suspend.cancelledCallerDonation? st v tcbV = none) :
    RefillViewsKept (Lifecycle.Suspend.cancelIpcBlocking st v tcbV) st := by
  have h := cancelIpcBlocking_refillViewsKept_of_return st v tcbV hInv
  rwa [Lifecycle.Suspend.returnDonationToCancelledCaller_none st v tcbV hD] at h

/-- WS-ZA ZA6.33: **the teardown keeps every context's refills off the one it
returns**. -/
theorem cancelIpcBlocking_refillsKeptOff (st : SystemState) (v : SeLe4n.ThreadId)
    (tcbV : TCB) (hInv : st.objects.invExt) (P : SeLe4n.SchedContextId → Prop)
    (hP : ∀ p, Lifecycle.Suspend.cancelledCallerDonation? st v tcbV = some p → P p.1) :
    SystemState.RefillsKeptOff P (Lifecycle.Suspend.cancelIpcBlocking st v tcbV) st :=
  (SystemState.RefillsKeptOff.of_kept (cancelIpcBlocking_refillViewsKept_of_return st v tcbV hInv)
    fun c => by
      unfold SchedulerState.replenishQueueOnCore
      rw [Lifecycle.Suspend.cancelIpcBlocking_scheduler_eq,
        Lifecycle.Suspend.returnDonationToCancelledCaller_scheduler_eq]).trans
    (returnDonationToCancelledCaller_refillsKeptOff st v tcbV hInv P hP)

/-- WS-ZA ZA6.6: the restore writes one thread's IPC fields and frame, not its
yield code. -/
theorem restoreToReadyStaging_yieldLinksKept (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (hInv : st.objects.invExt) :
    YieldLinksKept (Lifecycle.Suspend.restoreToReadyStaging st tid frame) st := by
  unfold Lifecycle.Suspend.restoreToReadyStaging
  exact .updateTcb st tid _ hInv fun _ => by cases frame <;> rfl

/-- WS-ZA ZA6.6: the cancelled caller's donation return keeps every yield code
(`returnDonatedSchedContext_yieldLinksKept`). -/
theorem returnDonationToCancelledCaller_yieldLinksKept (st : SystemState)
    (v : SeLe4n.ThreadId) (tcbV : TCB) (hInv : st.objects.invExt) :
    YieldLinksKept (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) st := by
  cases hD : Lifecycle.Suspend.cancelledCallerDonation? st v tcbV with
  | none =>
    rw [Lifecycle.Suspend.returnDonationToCancelledCaller_none st v tcbV hD]; exact .refl st
  | some p =>
    obtain ⟨scId, holder⟩ := p
    unfold Lifecycle.Suspend.returnDonationToCancelledCaller
    rw [hD]
    cases hT : st.getTcb? v with
    | none => exact .refl st
    | some _ =>
      dsimp only
      cases hRet : returnDonatedSchedContextResolved st holder scId v with
      | error _ => exact .refl st
      | ok st' =>
        obtain ⟨_, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
        exact returnDonatedSchedContext_yieldLinksKept hInv hPop

/-- WS-ZA ZA6.6: **the teardown keeps every yield code** — it patches queue
links, IPC fields, bindings and the reply link, never a yield end. -/
theorem cancelIpcBlocking_yieldLinksKept (st : SystemState) (v : SeLe4n.ThreadId)
    (tcbV : TCB) (hInv : st.objects.invExt) :
    YieldLinksKept (Lifecycle.Suspend.cancelIpcBlocking st v tcbV) st := by
  have hEp : ∀ e, YieldLinksKept (removeFromBlockingEndpoint st v e) st := fun e =>
    .of_tcbMap (fun t => by
        rw [removeFromBlockingEndpoint_getTcb?_eq_splice st v e hInv t]
        exact spliceOutMidQueueNode_tcbField_frame TCB.yieldToCode
          (fun _ _ _ _ _ _ => rfl) st v hInv t)
      (removeFromBlockingEndpoint_getSchedContext?_eq st v e hInv)
  have hEpR := fun e => (restoreToReadyStaging_yieldLinksKept _ v (some Architecture.cancelledIpcFrame)
    (removeFromBlockingEndpoint_preserves_objects_invExt st v e hInv)).trans (hEp e)
  unfold Lifecycle.Suspend.cancelIpcBlocking Lifecycle.Suspend.restoreToReadyCancelled
  cases hIp : tcbV.ipcState with
  | ready => exact .refl _
  | blockedOnSend e => exact hEpR e
  | blockedOnReceive e => exact hEpR e
  | blockedOnCall e => exact hEpR e
  | blockedOnNotification _ =>
    exact (restoreToReadyStaging_yieldLinksKept _ v _
      (removeFromNotificationWaitQueue_preserves_objects_invExt st v hInv)).trans
      (.of_tcbMap (fun t => removeFromNotificationWaitQueue_tcbField_frame TCB.yieldToCode
          (fun _ _ _ _ _ _ => rfl) st v hInv t)
        (removeFromNotificationWaitQueue_getSchedContext?_eq st v hInv))
  | blockedOnReply ep rt =>
    have hR := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt
      st v tcbV hInv
    have hS := cutThreadReplyFrameOut_preserves_objects_invExt
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV hR
    have hU := Lifecycle.Suspend.restoreToReadyStaging_invExt _ v
      (some Architecture.cancelledIpcFrame) hS
    dsimp only
    refine YieldLinksKept.trans (.of_map KernelObject.withoutReplyLinks
      (fun o => by cases o <;> rfl)
      (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffReplyLinks _ v _)) ?_
    refine YieldLinksKept.trans (.of_tcbMap
      (consumeReplyLink_map_frame TCB.yieldToCode (fun _ => rfl) _ v tcbV hU)
      (consumeReplyLink_getSchedContext?_eq _ v tcbV hU)) ?_
    refine YieldLinksKept.trans (restoreToReadyStaging_yieldLinksKept _ v _ hS) ?_
    exact (YieldLinksKept.of_getTcb?_eq (cutThreadReplyFrameOut_getTcb?_eq _ tcbV hR)
      (cutThreadReplyFrameOut_getSchedContext?_eq _ tcbV hR)).trans
      (returnDonationToCancelledCaller_yieldLinksKept st v tcbV hInv)

/-- WS-SM SM6.E (resolution frame) / **WS-RR RR8.11**: the teardown never moves
**any** thread's home core.

Moved here from `IPC/CrossCore/Cancellation.lean` and generalised from the victim
to an arbitrary thread.  The proof it had there could only be stated at the victim,
because `cancelIpcBlocking_getTcb?_none` is; the general form reads the teardown's
whole affinity frame, whose per-step pieces this module has the imports for.  Since
WS-RR RR8.6 the deschedule no longer reads it; what still does is the `.bound`
arm's replenish purge core in `suspendThreadOnCore`, resolved on the pre-state, and
the SM5.H affinity invariant, which reads the home of whichever thread a scheduling
context is bound to — not the victim. -/
theorem cancelIpcBlocking_determineTargetCore_eq (st : SystemState)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (hInv : st.objects.invExt)
    (x : SeLe4n.ThreadId) :
    determineTargetCore (Lifecycle.Suspend.cancelIpcBlocking st victim tcb) x
      = determineTargetCore st x :=
  determineTargetCore_congr st _ x
    (TCB.map_cpuAffinity_of_placement (cancelIpcBlocking_placement_frame st victim tcb hInv x))

/-- The mid-queue splice rewrites threads only. -/
theorem spliceOutMidQueueNode_tableReferenceFrame (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    SystemState.TableReferenceFrame st (spliceOutMidQueueNode st tid) :=
  SystemState.TableReferenceFrame.of_offTcb
    (fun k o hNot => spliceOutMidQueueNode_nonTcb st tid hInv k o hNot)
    (spliceOutMidQueueNode_sameTaintWords st tid hInv)

/-- WS-ZA ZA6.33: the targeted dequeue rewrites one endpoint's queue ends only,
so it keeps every endpoint's registration flag. -/
theorem removeFromBlockingEndpoint_tableReferenceFrame (st : SystemState)
    (tid : SeLe4n.ThreadId) (e : SeLe4n.ObjId) (hInv : st.objects.invExt) :
    SystemState.TableReferenceFrame st (removeFromBlockingEndpoint st tid e) := by
  have hS := spliceOutMidQueueNode_preserves_objects_invExt st tid hInv
  refine (spliceOutMidQueueNode_tableReferenceFrame st tid hInv).trans ?_
  rcases removeFromBlockingEndpoint_cases st tid e with h | ⟨ep, hA, hE, h⟩ <;> rw [h]
  · exact .refl _
  · exact SystemState.TableReferenceFrame.rewriteObject _ hS (by rw [hE]; rfl)

/-- The endpoint sweep rewrites queue ends only, so it keeps every endpoint's
registration flag. -/
theorem removeFromAllEndpointQueues_tableReferenceFrame (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    SystemState.TableReferenceFrame st (removeFromAllEndpointQueues st tid) := by
  have hS := spliceOutMidQueueNode_preserves_objects_invExt st tid hInv
  rw [removeFromAllEndpointQueues_eq_fold]
  refine (spliceOutMidQueueNode_tableReferenceFrame st tid hInv).trans
    (RobinHood.RHTable.fold_preserves_of_lookup (spliceOutMidQueueNode st tid).objects
      (spliceOutMidQueueNode st tid) (endpointSweepBody (spliceOutMidQueueNode st tid) tid)
      (fun acc => acc.objects.invExt ∧
        SystemState.TableReferenceFrame (spliceOutMidQueueNode st tid) acc)
      hS ⟨hS, .refl _⟩ ?_).2
  rintro acc k' v' _ ⟨hE, hA⟩
  unfold endpointSweepBody
  cases v' with
  | endpoint _ =>
    simp only
    split
    · next ep hEp _ =>
      split
      · exact ⟨SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hE,
          hA.trans (.rewriteObject _ hE (by
            rw [(SystemState.getEndpoint?_eq_some_iff acc k' ep).mp hEp]; rfl))⟩
      · exact ⟨hE, hA⟩
    · exact ⟨hE, hA⟩
  | _ => exact ⟨hE, hA⟩

/-- A thread write chained onto a frame. -/
private theorem tableReferenceFrame_updateTcb_step {st s : SystemState}
    (h : s.objects.invExt ∧ SystemState.TableReferenceFrame st s)
    (p : SeLe4n.ThreadId) (f : TCB → TCB)
    (hW : ∀ t, (f t).taintWords = t.taintWords := by taint_words_kept) :
    (s.updateTcb p f).objects.invExt ∧ SystemState.TableReferenceFrame st (s.updateTcb p f) :=
  ⟨SystemState.updateTcb_preserves_objects_invExt s p f h.1,
    h.2.trans (.updateTcb s p f h.1)⟩

/-- The neighbour relink after a frame. -/
private theorem unlinkNtfnNeighbours_tableReferenceFrame_step {st s : SystemState}
    (h : s.objects.invExt ∧ SystemState.TableReferenceFrame st s)
    (prev next : Option SeLe4n.ThreadId) :
    SystemState.TableReferenceFrame st (unlinkNtfnNeighbours s prev next) := by
  unfold unlinkNtfnNeighbours
  cases prev <;> cases next <;> dsimp only
  · exact h.2
  · exact (tableReferenceFrame_updateTcb_step h _ _).2
  · exact (tableReferenceFrame_updateTcb_step h _ _).2
  · exact (tableReferenceFrame_updateTcb_step (tableReferenceFrame_updateTcb_step h _ _) _ _).2

/-- The notification unlink keeps the notification's interrupt flag and
rewrites threads' links. -/
theorem removeFromNotificationWaitQueue_tableReferenceFrame (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    SystemState.TableReferenceFrame st (removeFromNotificationWaitQueue st tid) := by
  unfold removeFromNotificationWaitQueue
  split
  · split
    · split
      · next notif hN _ =>
        have hN' := (SystemState.getNotification?_eq_some_iff st _ notif).mp hN
        dsimp only
        unfold unlinkNtfnNeighbours clearNtfnLinks
        refine unlinkNtfnNeighbours_tableReferenceFrame_step
          (tableReferenceFrame_updateTcb_step
            ⟨SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hInv,
              SystemState.TableReferenceFrame.rewriteObject _ hInv ?_⟩ _ _) _ _
        rw [hN']; rfl
      · exact .refl _
    · exact .refl _
  · exact .refl _

/-- The reply consume rewrites a reply and a thread. -/
theorem consumeCallerReply_tableReferenceFrame {st st' : SystemState}
    {caller : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} (hInv : st.objects.invExt)
    (h : SystemState.consumeCallerReply caller rid st = .ok ((), st')) :
    SystemState.TableReferenceFrame st st' := by
  unfold SystemState.consumeCallerReply at h
  cases hC : SystemState.consumeReply rid st with
  | error e => simp [hC] at h
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hC] at h
    have hF1 : SystemState.TableReferenceFrame st st1 := by
      unfold SystemState.consumeReply at hC
      cases hG : st.getReply? rid with
      | none => rw [hG] at hC; cases hC; exact .refl _
      | some r =>
        rw [hG] at hC
        exact .storeObject hInv hC (by
          rw [(SystemState.getReply?_eq_some_iff st rid r).mp hG]; rfl)
    have hInv1 := SystemState.consumeReply_preserves_objects_invExt st st1 rid hInv hC
    cases hT : st1.getTcb? caller with
    | none =>
      simp only [hT, Except.ok.injEq, Prod.mk.injEq, true_and] at h
      rw [← h]; exact hF1
    | some tcb =>
      simp only [hT] at h
      exact hF1.trans (.storeObject hInv1 h
        (SystemState.TableReferenceFrame.tcb_over
          ((SystemState.getTcb?_eq_some_iff st1 caller tcb).mp hT)))

/-- The reply-link teardown rewrites a reply and a thread. -/
theorem consumeReplyLink_tableReferenceFrame (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (hInv : st.objects.invExt) :
    SystemState.TableReferenceFrame st (Lifecycle.Suspend.consumeReplyLink st tid tcb) := by
  unfold Lifecycle.Suspend.consumeReplyLink
  split
  · exact .refl _
  · next rid _ =>
    exact consumeCallerReply_tableReferenceFrame hInv (SystemState.consumeCallerReply_eq_link _ tid rid)

/-- The cancelled caller's reply-frame cut rewrites replies only. -/
theorem cutThreadReplyFrameOut_tableReferenceFrame (st : SystemState) (tcb : TCB)
    (hInv : st.objects.invExt) :
    SystemState.TableReferenceFrame st (cutThreadReplyFrameOut st tcb) := by
  unfold cutThreadReplyFrameOut
  split
  · exact .refl _
  · next rid _ =>
    rcases cutReplyFrameOutOrSelf_cases st rid with h | h
    · rw [h]; exact .refl _
    · exact fun oid => by
        rcases cutReplyFrameOut_objects_rewrite hInv h oid with e | ⟨_, _, h1, h2, _⟩
        · rw [e]
        · rw [h1, h2]; rfl

/-- The restore rewrites its thread. -/
theorem restoreToReadyStaging_tableReferenceFrame (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (hInv : st.objects.invExt) :
    SystemState.TableReferenceFrame st (Lifecycle.Suspend.restoreToReadyStaging st tid frame) := by
  unfold Lifecycle.Suspend.restoreToReadyStaging
  exact .updateTcb _ _ _ hInv

/-- The cancelled caller's donation return. -/
theorem returnDonationToCancelledCaller_tableReferenceFrame (st : SystemState)
    (v : SeLe4n.ThreadId) (tcbV : TCB) (hInv : st.objects.invExt) :
    SystemState.TableReferenceFrame st
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) := by
  unfold Lifecycle.Suspend.returnDonationToCancelledCaller
  cases hD : Lifecycle.Suspend.cancelledCallerDonation? st v tcbV with
  | none => exact .refl _
  | some p =>
    obtain ⟨scId, holder⟩ := p
    cases hT : st.getTcb? v with
    | none => exact .refl _
    | some _ =>
      dsimp only
      cases hRet : returnDonatedSchedContextResolved st holder scId v with
      | error _ => exact .refl _
      | ok st' =>
        obtain ⟨_, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
        exact returnDonatedSchedContext_tableReferenceFrame hInv hPop

/-- **The IPC teardown keeps the reference tables and every object's
back-links**: each of its writes rewrites a thread, a reply, a scheduling
context, an endpoint's queue ends or a notification's queue ends. -/
theorem cancelIpcBlocking_tableReferenceFrame (st : SystemState) (victim : SeLe4n.ThreadId)
    (tcb : TCB) (hInv : st.objects.invExt) :
    SystemState.TableReferenceFrame st (Lifecycle.Suspend.cancelIpcBlocking st victim tcb) := by
  unfold Lifecycle.Suspend.cancelIpcBlocking Lifecycle.Suspend.restoreToReadyCancelled
  cases tcb.ipcState with
  | ready => exact .refl _
  | blockedOnSend e | blockedOnReceive e | blockedOnCall e =>
    exact (removeFromBlockingEndpoint_tableReferenceFrame st victim e hInv).trans
      (restoreToReadyStaging_tableReferenceFrame _ victim _
        (removeFromBlockingEndpoint_preserves_objects_invExt st victim e hInv))
  | blockedOnNotification _ =>
    exact (removeFromNotificationWaitQueue_tableReferenceFrame st victim hInv).trans
      (restoreToReadyStaging_tableReferenceFrame _ victim _
        (removeFromNotificationWaitQueue_preserves_objects_invExt st victim hInv))
  | blockedOnReply _ _ =>
    have hR := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt
      st victim tcb hInv
    have hS := cutThreadReplyFrameOut_preserves_objects_invExt
      (Lifecycle.Suspend.returnDonationToCancelledCaller st victim tcb) tcb hR
    have hU := Lifecycle.Suspend.restoreToReadyStaging_invExt _ victim
      (some Architecture.cancelledIpcFrame) hS
    dsimp only
    have f3 := ((returnDonationToCancelledCaller_tableReferenceFrame st victim tcb hInv).trans
      (cutThreadReplyFrameOut_tableReferenceFrame _ tcb hR)).trans
      (restoreToReadyStaging_tableReferenceFrame _ victim (some Architecture.cancelledIpcFrame) hS)
    have f4 := f3.trans (consumeReplyLink_tableReferenceFrame _ victim tcb hU)
    exact f4.trans (.of_agreeOffRunLinks
      (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffRunLinks _ _ _))

/-- **WS-ZA ZA4.5: the teardown keeps the run queues in agreement with the
links** — it writes no scheduler slot (`cancelIpcBlocking_scheduler_eq`) and moves
no thread (`cancelIpcBlocking_placement_frame`).  WS-ZA ZA6.33: a frame stage off
the context it returns, whose holder changes. -/
theorem cancelIpcBlocking_runQueueFrameStage (st : SystemState) (victim : SeLe4n.ThreadId)
    (tcb : TCB) (P : SeLe4n.SchedContextId → Prop)
    (hP : ∀ p, Lifecycle.Suspend.cancelledCallerDonation? st victim tcb = some p → P p.1) :
    SystemState.RunQueueFrameStage P st (Lifecycle.Suspend.cancelIpcBlocking st victim tcb) :=
  have hS := Lifecycle.Suspend.cancelIpcBlocking_scheduler_eq st victim tcb
  SystemState.RunQueueFrameStage.of_placement
    (fun hInv => Lifecycle.Suspend.cancelIpcBlocking_preserves_objects_invExt st victim tcb hInv)
    (by rw [hS]) (by rw [hS])
    (fun hInv x => cancelIpcBlocking_placement_frame st victim tcb hInv x)
    (fun hInv => cancelIpcBlocking_stateMono st victim tcb hInv)
    (fun hInv => cancelIpcBlocking_releaseStateAgree st victim tcb hInv)
    (fun hInv => cancelIpcBlocking_refillsKeptOff st victim tcb hInv P hP)
    (fun hInv => cancelIpcBlocking_yieldLinksKept st victim tcb hInv)
    (hRes := by rw [Lifecycle.Suspend.cancelIpcBlocking_machine_eq st victim tcb])

/-- ...and a stage when it returns nothing: every arm but a reply arm whose
caller had donated. -/
theorem cancelIpcBlocking_runQueueStage (st : SystemState) (victim : SeLe4n.ThreadId)
    (tcb : TCB) (hD : Lifecycle.Suspend.cancelledCallerDonation? st victim tcb = none) :
    SystemState.RunQueueStage st (Lifecycle.Suspend.cancelIpcBlocking st victim tcb) :=
  have hS := Lifecycle.Suspend.cancelIpcBlocking_scheduler_eq st victim tcb
  SystemState.RunQueueStage.of_placement
    (fun hInv => Lifecycle.Suspend.cancelIpcBlocking_preserves_objects_invExt st victim tcb hInv)
    (by rw [hS]) (by rw [hS])
    (fun hInv x => cancelIpcBlocking_placement_frame st victim tcb hInv x)
    (fun hInv => cancelIpcBlocking_stateMono st victim tcb hInv)
    (fun hInv => cancelIpcBlocking_releaseStateAgree st victim tcb hInv)
    (fun hInv => cancelIpcBlocking_refillViewsKept st victim tcb hInv hD)
    (fun hInv => cancelIpcBlocking_yieldLinksKept st victim tcb hInv)
    (hRes := by rw [Lifecycle.Suspend.cancelIpcBlocking_machine_eq st victim tcb])

/-- WS-ZA ZA6.33: the context the teardown returns is well formed after it
wherever it was before: the return rebinds it and keeps its refills. -/
theorem cancelIpcBlocking_returned_refillsView (st : SystemState) (victim : SeLe4n.ThreadId)
    (tcb : TCB) (hInv : st.objects.invExt) (scId : SeLe4n.SchedContextId) (a : SchedContext)
    (ha : (Lifecycle.Suspend.cancelIpcBlocking st victim tcb).getSchedContext? scId = some a) :
    ∃ b, st.getSchedContext? scId = some b ∧ a.refillsView = b.refillsView := by
  obtain ⟨b1, hb1, hv1⟩ :=
    (cancelIpcBlocking_refillViewsKept_of_return st victim tcb hInv).getSchedContext? ha
  have hR : ∀ c, (Lifecycle.Suspend.returnDonationToCancelledCaller st victim tcb).getSchedContext?
      scId = some c → ∃ b, st.getSchedContext? scId = some b ∧ c.refillsView = b.refillsView := by
    intro c hc
    unfold Lifecycle.Suspend.returnDonationToCancelledCaller at hc
    split at hc
    · rename_i s0 holder _ _ _
      split at hc
      · rename_i st' hRet
        obtain ⟨_, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
        by_cases hs : scId = s0
        · subst hs
          obtain ⟨b, a', hb, -, ha', -, hv⟩ := returnDonatedSchedContext_rebinds hInv hPop
          rw [ha'] at hc; cases hc; exact ⟨b, hb, hv⟩
        · obtain ⟨b, hb, hv⟩ := (returnDonatedSchedContext_refillsKeptOff hInv hPop).1 scId c hs hc
          exact ⟨b, hb, by
            show ({ c.refillView with boundThreadCode := 0 } : SchedContext) =
              { b.refillView with boundThreadCode := 0 }
            rw [hv]⟩
      · exact ⟨c, hc, rfl⟩
    · exact ⟨c, hc, rfl⟩
  obtain ⟨b, hb, hv⟩ := hR b1 hb1
  refine ⟨b, hb, ?_⟩
  rw [← hv]
  show ({ a.refillView with boundThreadCode := 0 } : SchedContext) =
    { b1.refillView with boundThreadCode := 0 }
  rw [hv1]

/-- ...and so does the teardown with its returned context settled
(`settleReturnedContext_runQueueStage`, WS-ZA ZA6.33). -/
theorem cancelIpcBlockingMigrated_runQueueStage (st : SystemState) (victim : SeLe4n.ThreadId)
    (tcb : TCB) : SystemState.RunQueueStage st (cancelIpcBlockingMigrated victim tcb st) := by
  unfold cancelIpcBlockingMigrated
  cases hD : Lifecycle.Suspend.cancelledCallerDonation? st victim tcb with
  | none => exact cancelIpcBlocking_runQueueStage st victim tcb hD
  | some p =>
    obtain ⟨scId, holder⟩ := p
    dsimp only
    refine SchedContextOps.settleReturnedContext_runQueueStage
      (cancelIpcBlocking_runQueueFrameStage st victim tcb (· = scId)
        (fun p h => by rw [hD] at h; cases h; rfl)) ?_
    intro S hs hI hSnd _ a ha
    obtain ⟨b, hb, hv⟩ := cancelIpcBlocking_returned_refillsView st victim tcb hI scId a ha
    exact schedContextWellFormed_of_refillsView hv (hSnd.1 scId b hs hb)

/-- ...and so does the reclaim-complete teardown: its last step is a dequeue. -/
theorem cancelIpcBlockingReclaimed_runQueueStage (st : SystemState) (victim : SeLe4n.ThreadId)
    (tcb : TCB) : SystemState.RunQueueStage st (cancelIpcBlockingReclaimed victim tcb st) := by
  refine (cancelIpcBlockingMigrated_runQueueStage st victim tcb).trans ?_
  unfold cancelIpcBlockingReclaimed descheduleUnboundHolder descheduleAtPlacement
  split
  · exact .refl _
  · exact descheduleAt_runQueueStage _ _ _

/-- **WS-RR RR8.11: the settled teardown establishes the SM5.H replenish-affinity
invariant** (WS-ZA ZA6.33: the settle, `settleReturnedContext_preserves_affinityConsistent_smp`).

The destination is read off the post-teardown binding
(`replenishHomeOfSchedContext`), so "the destination is right" is
`replenishHomeOfSchedContext_spec`, free on a refused reclaim and a committed
one alike.  The rest are the teardown's own frames: it writes no scheduler slot
(`cancelIpcBlocking_scheduler_eq`), no scheduling context but the one the reclaim
hands back (`cancelIpcBlocking_getSchedContext?_ne`), and no thread's
`cpuAffinity` (`cancelIpcBlocking_determineTargetCore_eq`); and it keeps the
release queues refined (`cancelIpcBlocking_releaseStateAgree`), which is what
lets the settle's purge take every entry of the returned context. -/
theorem cancelIpcBlockingMigrated_establishes_replenishQueueAffinityConsistent_smp
    (victim : SeLe4n.ThreadId) (tcb : TCB) (st : SystemState)
    (hInv : st.objects.invExt) (hRef : st.releaseQueueRefined)
    (hCons : replenishQueueAffinityConsistent_smp st) :
    replenishQueueAffinityConsistent_smp (cancelIpcBlockingMigrated victim tcb st) := by
  unfold cancelIpcBlockingMigrated
  cases hD : Lifecycle.Suspend.cancelledCallerDonation? st victim tcb with
  | none =>
    refine (replenishQueueAffinityConsistent_smp_congr
      (fun c => by rw [Lifecycle.Suspend.cancelIpcBlocking_scheduler_eq]; rfl)
      (fun scId₀ => cancelIpcBlocking_getSchedContext?_ne st victim tcb hInv scId₀
        (fun s h hD' => by rw [hD] at hD'; exact absurd hD' (by simp)))
      (fun tid => cancelIpcBlocking_determineTargetCore_eq st victim tcb hInv tid)).mpr hCons
  | some p =>
    obtain ⟨scId, holder⟩ := p
    dsimp only
    refine settleReturnedContext_preserves_affinityConsistent_smp _ _ scId
      ((cancelIpcBlocking_releaseStateAgree st victim tcb hInv).refined hRef)
      (replenishHomeOfSchedContext_spec _ scId _) ?_
    intro c' s0 t0 hs hMem sc hSc tid hB
    have hQ : (Lifecycle.Suspend.cancelIpcBlocking st victim tcb).scheduler.replenishQueueOnCore c'
        = st.scheduler.replenishQueueOnCore c' := by
      rw [Lifecycle.Suspend.cancelIpcBlocking_scheduler_eq]; rfl
    rw [hQ] at hMem
    rw [cancelIpcBlocking_getSchedContext?_ne st victim tcb hInv s0
      (fun s h hD' => by rw [hD] at hD'; cases hD'; exact hs)] at hSc
    rw [cancelIpcBlocking_determineTargetCore_eq st victim tcb hInv tid]
    exact hCons c' s0 t0 hMem sc hSc tid hB

-- `v0.35.158`: `enqueueAbortedHolderOnCore_replenishQueueOnCore` and
-- `wakeAbortedDonationHolder_replenishQueueOnCore` are retired with the wake;
-- the reclaim's deschedule step has the same frame beside its definition
-- (`descheduleUnboundHolder_replenishQueueOnCore`, `Lifecycle/Suspend.lean`).

/-- **WS-RR RR8.11: the cross-core cancellation composite establishes the SM5.H
replenish-affinity invariant.**

The lift adds nothing, for the same reason RR8.10's bundle lift adds no premise:
the two scheduler steps the composite performs over the settled teardown — the
reclaim's holder deschedule and the victim's placement removal — write run queues
and current slots, which the invariant does not read, and no object at all, so
all three of its readings are the settled teardown's. -/
theorem cancelIpcBlockingOnCore_establishes_replenishQueueAffinityConsistent_smp
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) (hRef : st.releaseQueueRefined)
    (hCons : replenishQueueAffinityConsistent_smp st) :
    replenishQueueAffinityConsistent_smp
      (cancelIpcBlockingOnCore victim tcb executingCore st).1 := by
  have hBase := cancelIpcBlockingMigrated_establishes_replenishQueueAffinityConsistent_smp
    victim tcb st hInv hRef hCons
  rw [cancelIpcBlockingOnCore_state_eq]
  unfold cancelIpcBlockingReclaimed
  refine (replenishQueueAffinityConsistent_smp_congr (fun c => ?_) (fun scId₀ => ?_)
    (fun tid => ?_)).mpr hBase
  · rw [descheduleAtPlacement_replenishQueueOnCore,
      descheduleUnboundHolder_replenishQueueOnCore]
  · rw [(descheduleAtPlacement_objectsAgreeOffRunLinks _ _).getSchedContext?,
      (descheduleUnboundHolder_objectsAgreeOffRunLinks _ _ _ _).getSchedContext?]
  · rw [descheduleAtPlacement_determineTargetCore,
      descheduleUnboundHolder_determineTargetCore]

/-- WS-ZA ZA6.6: the yield-link cancel places and unplaces no thread. -/
theorem cancelYieldTo_threadPlacedOnSomeCore (st : SystemState) (tid u : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    threadPlacedOnSomeCore (cancelYieldTo st tid) u = threadPlacedOnSomeCore st u :=
  threadPlacedOnSomeCore_of_scheduler_eq st _ u (SystemState.cancelYieldTo_scheduler st tid)
    (SystemState.cancelYieldTo_objectsAgreeOffYield st tid hInv).runCoresAgree

section SuspendPayoff
open SeLe4n.Kernel.Concurrency
open SeLe4n.Kernel.Lifecycle.Suspend

/-- The suspend's teardown leaves an active victim runnable: the cancellation
makes it `.ready` (`cancelIpcBlocking_victim_ready`) and blocks or suspends no
thread, and the reclaim moves only run-queue links. -/
theorem cancelIpcBlockingReclaimed_victim_runnable (st : SystemState) (v : SeLe4n.ThreadId)
    (tcbV : TCB) (hInv : st.objects.invExt) (hNR : v.isReserved = false)
    (hT : st.getTcb? v = some tcbV) (hA : tcbV.threadState ≠ .Inactive) :
    (cancelIpcBlockingReclaimed v tcbV st).runnable v := by
  have hLookup : lookupTcb st v = some tcbV := by simp [lookupTcb, hNR, hT]
  obtain ⟨z, hz, hzA⟩ := (cancelIpcBlocking_stateMono st v tcbV hInv).activeAt ⟨tcbV, hT, hA⟩
  have hzR := cancelIpcBlocking_victim_ready st v tcbV hInv hLookup z
    ((SystemState.getTcb?_eq_some_iff _ _ _).mp hz)
  exact (SystemState.StateMono.of_agreeOffRunLinks
    (cancelIpcBlockingReclaimed_objectsAgreeOffRunLinks v tcbV st)).runnable
    ⟨z, by rw [cancelIpcBlockingMigrated_getTcb?]; exact hz, hzR, hzA⟩

end SuspendPayoff

end SeLe4n.Kernel
