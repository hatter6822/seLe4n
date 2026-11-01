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
stored TCB is the one the caller looked up.  The three endpoint states and the
notification state end in `restoreToReadyCancelled` over a queue removal, whose
write at the victim's key is `restoredTcb` (`ipcState := .ready` by
construction).  The reply arm's restore sits over the reclaim and the splice —
neither of which moves a TCB's `ipcState`, and the splice moves no TCB at all —
and its trailing `consumeReplyLink` clears `replyObject` and copies every other
field, which is what `SystemState.consumeCallerReply_tcb_caller` states field by
field. -/
theorem cancelIpcBlocking_victim_ready
    (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB)
    (hObjInv : st.objects.invExt) (hLookup : lookupTcb st v = some tcbV) :
    ∀ t', (Lifecycle.Suspend.cancelIpcBlocking st v tcbV).objects[v.toObjId]? = some (.tcb t') →
      t'.ipcState = ThreadIpcState.ready := by
  have hAt : st.objects[v.toObjId]? = some (.tcb tcbV) := lookupTcb_some_objects st v tcbV hLookup
  have hNR : ¬ v.isReserved := lookupTcb_some_not_reserved st v tcbV hLookup
  cases hIp : tcbV.ipcState with
  | ready =>
    rw [show Lifecycle.Suspend.cancelIpcBlocking st v tcbV = st by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hIp]]
    intro t' h
    rw [hAt] at h
    cases h
    exact hIp
  | blockedOnSend ep =>
    rw [cancelIpcBlocking_endpoint_arm_eq st v tcbV ep (Or.inl hIp)]
    unfold sweptAndRestored
    obtain ⟨hI1, t1, hL1, _⟩ := removeFromAllEndpointQueues_tcb_lookup st v v.toObjId tcbV hObjInv hAt
    exact restoreVictimReady v _ t1 _ hI1 (lookupTcb_of_objects_of_not_reserved _ v t1 hL1 hNR)
  | blockedOnReceive ep =>
    rw [cancelIpcBlocking_endpoint_arm_eq st v tcbV ep (Or.inr (Or.inl hIp))]
    unfold sweptAndRestored
    obtain ⟨hI1, t1, hL1, _⟩ := removeFromAllEndpointQueues_tcb_lookup st v v.toObjId tcbV hObjInv hAt
    exact restoreVictimReady v _ t1 _ hI1 (lookupTcb_of_objects_of_not_reserved _ v t1 hL1 hNR)
  | blockedOnCall ep =>
    rw [cancelIpcBlocking_endpoint_arm_eq st v tcbV ep (Or.inr (Or.inr hIp))]
    unfold sweptAndRestored
    obtain ⟨hI1, t1, hL1, _⟩ := removeFromAllEndpointQueues_tcb_lookup st v v.toObjId tcbV hObjInv hAt
    exact restoreVictimReady v _ t1 _ hI1 (lookupTcb_of_objects_of_not_reserved _ v t1 hL1 hNR)
  | blockedOnNotification nId =>
    rw [cancelIpcBlocking_notification_arm_eq st v tcbV nId hIp]
    unfold purgedAndRestored
    obtain ⟨hI1, t1, hL1, _⟩ :=
      removeFromNotificationWaitQueue_tcb_lookup st v v.toObjId tcbV hObjInv hAt
    exact restoreVictimReady v _ t1 _ hI1 (lookupTcb_of_objects_of_not_reserved _ v t1 hL1 hNR)
  | blockedOnReply ep rt =>
    rw [cancelIpcBlocking_reply_arm_eq st v tcbV ep rt hIp]
    -- the reclaim, then the splice: both keep a TCB at the victim's key
    have hIR : (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV).objects.invExt :=
      Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt st v tcbV hObjInv
    obtain ⟨tR, hAtR, _⟩ :=
      Lifecycle.Suspend.returnDonationToCancelledCaller_tcb_lookup st v tcbV hObjInv
        v.toObjId tcbV hAt
    have hIX : (spliceThreadReplyFrameOut
        (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV).objects.invExt :=
      spliceThreadReplyFrameOut_preserves_objects_invExt _ tcbV hIR
    have hAtX := spliceThreadReplyFrameOut_tcb_eq _ tcbV hIR v.toObjId tR hAtR
    unfold restoredAndConsumed
    have hGetX : (spliceThreadReplyFrameOut
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
          (spliceThreadReplyFrameOut
            (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV) v
          (some Architecture.cancelledIpcFrame)).objects.invExt :=
        Lifecycle.Suspend.restoreToReadyStaging_invExt _ v _ hIX
      have hPost := SystemState.consumeCallerReply_tcb_caller _ _ v rid hIY
        (SystemState.consumeCallerReply_eq_link _ v rid) _ hAtY
      rw [hPost] at h
      cases h
      exact hReadyY

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

/-- WS-RR RR8.11: the frame splice writes Reply objects only. -/
theorem spliceThreadReplyFrameOut_getSchedContext?_eq (st : SystemState)
    (tcb : TCB) (hInv : st.objects.invExt) (scId : SeLe4n.SchedContextId) :
    (spliceThreadReplyFrameOut st tcb).getSchedContext? scId = st.getSchedContext? scId := by
  unfold spliceThreadReplyFrameOut
  cases tcb.replyObject with
  | none => rfl
  | some rid => exact spliceReplyFrameOutOrSelf_getSchedContext?_eq st rid hInv scId

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
  | blockedOnSend _ =>
    rw [restoreToReadyStaging_getSchedContext?_eq _ v _
        (removeFromAllEndpointQueues_preserves_objects_invExt st v hInv),
      removeFromAllEndpointQueues_getSchedContext?_eq st v hInv]
  | blockedOnReceive _ =>
    rw [restoreToReadyStaging_getSchedContext?_eq _ v _
        (removeFromAllEndpointQueues_preserves_objects_invExt st v hInv),
      removeFromAllEndpointQueues_getSchedContext?_eq st v hInv]
  | blockedOnCall _ =>
    rw [restoreToReadyStaging_getSchedContext?_eq _ v _
        (removeFromAllEndpointQueues_preserves_objects_invExt st v hInv),
      removeFromAllEndpointQueues_getSchedContext?_eq st v hInv]
  | blockedOnNotification _ =>
    rw [restoreToReadyStaging_getSchedContext?_eq _ v _
        (removeFromNotificationWaitQueue_preserves_objects_invExt st v hInv),
      removeFromNotificationWaitQueue_getSchedContext?_eq st v hInv]
  | blockedOnReply ep rt =>
    have hR := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt
      st v tcbV hInv
    have hS := spliceThreadReplyFrameOut_preserves_objects_invExt
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV hR
    dsimp only
    rw [(SystemState.unlinkReplyWaiterOpt_objectsAgreeOffRunLinks _ v _).getSchedContext?,
      consumeReplyLink_getSchedContext?_eq _ v tcbV
        (Lifecycle.Suspend.restoreToReadyStaging_invExt _ v _ hS),
      restoreToReadyStaging_getSchedContext?_eq _ v _ hS,
      spliceThreadReplyFrameOut_getSchedContext?_eq _ tcbV hR, hReclaim]

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
  have hEp : ∀ s, (Lifecycle.Suspend.restoreToReadyStaging
      (removeFromAllEndpointQueues st v) v
      (some Architecture.cancelledIpcFrame)).getSchedContext? s = st.getSchedContext? s :=
    fun s => by
      rw [restoreToReadyStaging_getSchedContext?_eq _ v _
          (removeFromAllEndpointQueues_preserves_objects_invExt st v hInv),
        removeFromAllEndpointQueues_getSchedContext?_eq st v hInv]
  unfold Lifecycle.Suspend.cancelIpcBlocking Lifecycle.Suspend.restoreToReadyCancelled
  cases hIp : tcbV.ipcState with
  | ready => exact .refl _
  | blockedOnSend _ => exact .of_getSchedContext? hEp
  | blockedOnReceive _ => exact .of_getSchedContext? hEp
  | blockedOnCall _ => exact .of_getSchedContext? hEp
  | blockedOnNotification _ =>
    exact .of_getSchedContext? fun s => by
      rw [restoreToReadyStaging_getSchedContext?_eq _ v _
          (removeFromNotificationWaitQueue_preserves_objects_invExt st v hInv),
        removeFromNotificationWaitQueue_getSchedContext?_eq st v hInv]
  | blockedOnReply ep rt =>
    have hR := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt
      st v tcbV hInv
    have hS := spliceThreadReplyFrameOut_preserves_objects_invExt
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV hR
    dsimp only
    refine SystemState.ReleaseLinksAgree.trans (.of_getSchedContext? fun s => ?_)
      (returnDonationToCancelledCaller_releaseStateAgree st v tcbV hInv).1
    rw [(SystemState.unlinkReplyWaiterOpt_objectsAgreeOffRunLinks _ v _).getSchedContext?,
      consumeReplyLink_getSchedContext?_eq _ v tcbV
        (Lifecycle.Suspend.restoreToReadyStaging_invExt _ v _ hS),
      restoreToReadyStaging_getSchedContext?_eq _ v _ hS,
      spliceThreadReplyFrameOut_getSchedContext?_eq _ tcbV hR]

/-- WS-ZA ZA6.4: the cancelled caller's donation return keeps every context's
refill view (`returnDonatedSchedContext_refillViewsKept`). -/
theorem returnDonationToCancelledCaller_refillViewsKept (st : SystemState)
    (v : SeLe4n.ThreadId) (tcbV : TCB) (hInv : st.objects.invExt) :
    RefillViewsKept (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) st := by
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
        exact returnDonatedSchedContext_refillViewsKept hInv hPop

/-- WS-ZA ZA6.4: **the teardown keeps every context's refill view** — it writes
a context only through the donation return, which keeps it. -/
theorem cancelIpcBlocking_refillViewsKept (st : SystemState) (v : SeLe4n.ThreadId)
    (tcbV : TCB) (hInv : st.objects.invExt) :
    RefillViewsKept (Lifecycle.Suspend.cancelIpcBlocking st v tcbV) st := by
  have hEp : ∀ s, (Lifecycle.Suspend.restoreToReadyStaging
      (removeFromAllEndpointQueues st v) v
      (some Architecture.cancelledIpcFrame)).getSchedContext? s = st.getSchedContext? s :=
    fun s => by
      rw [restoreToReadyStaging_getSchedContext?_eq _ v _
          (removeFromAllEndpointQueues_preserves_objects_invExt st v hInv),
        removeFromAllEndpointQueues_getSchedContext?_eq st v hInv]
  unfold Lifecycle.Suspend.cancelIpcBlocking Lifecycle.Suspend.restoreToReadyCancelled
  cases hIp : tcbV.ipcState with
  | ready => exact .refl _
  | blockedOnSend _ => exact .of_getSchedContext?_eq hEp
  | blockedOnReceive _ => exact .of_getSchedContext?_eq hEp
  | blockedOnCall _ => exact .of_getSchedContext?_eq hEp
  | blockedOnNotification _ =>
    exact .of_getSchedContext?_eq fun s => by
      rw [restoreToReadyStaging_getSchedContext?_eq _ v _
          (removeFromNotificationWaitQueue_preserves_objects_invExt st v hInv),
        removeFromNotificationWaitQueue_getSchedContext?_eq st v hInv]
  | blockedOnReply ep rt =>
    have hR := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt
      st v tcbV hInv
    have hS := spliceThreadReplyFrameOut_preserves_objects_invExt
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV hR
    dsimp only
    refine RefillViewsKept.trans (.of_getSchedContext?_eq fun s => ?_)
      (returnDonationToCancelledCaller_refillViewsKept st v tcbV hInv)
    rw [(SystemState.unlinkReplyWaiterOpt_objectsAgreeOffRunLinks _ v _).getSchedContext?,
      consumeReplyLink_getSchedContext?_eq _ v tcbV
        (Lifecycle.Suspend.restoreToReadyStaging_invExt _ v _ hS),
      restoreToReadyStaging_getSchedContext?_eq _ v _ hS,
      spliceThreadReplyFrameOut_getSchedContext?_eq _ tcbV hR]

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
  have hEp : YieldLinksKept (removeFromAllEndpointQueues st v) st :=
    .of_tcbMap (fun t => by
        rw [removeFromAllEndpointQueues_getTcb?_eq_splice st v hInv t]
        exact spliceOutMidQueueNode_tcbField_frame TCB.yieldToCode
          (fun _ _ _ _ _ _ => rfl) st v hInv t)
      (removeFromAllEndpointQueues_getSchedContext?_eq st v hInv)
  have hEpR := (restoreToReadyStaging_yieldLinksKept _ v (some Architecture.cancelledIpcFrame)
    (removeFromAllEndpointQueues_preserves_objects_invExt st v hInv)).trans hEp
  unfold Lifecycle.Suspend.cancelIpcBlocking Lifecycle.Suspend.restoreToReadyCancelled
  cases hIp : tcbV.ipcState with
  | ready => exact .refl _
  | blockedOnSend _ => exact hEpR
  | blockedOnReceive _ => exact hEpR
  | blockedOnCall _ => exact hEpR
  | blockedOnNotification _ =>
    exact (restoreToReadyStaging_yieldLinksKept _ v _
      (removeFromNotificationWaitQueue_preserves_objects_invExt st v hInv)).trans
      (.of_tcbMap (fun t => removeFromNotificationWaitQueue_tcbField_frame TCB.yieldToCode
          (fun _ _ _ _ _ _ => rfl) st v hInv t)
        (removeFromNotificationWaitQueue_getSchedContext?_eq st v hInv))
  | blockedOnReply ep rt =>
    have hR := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt
      st v tcbV hInv
    have hS := spliceThreadReplyFrameOut_preserves_objects_invExt
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
    exact (YieldLinksKept.of_getTcb?_eq (spliceThreadReplyFrameOut_getTcb?_eq _ tcbV hR)
      (spliceThreadReplyFrameOut_getSchedContext?_eq _ tcbV hR)).trans
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
    (by rw [spliceOutMidQueueNode_eq_patches]; split <;> rfl)
    (fun k o hNot => spliceOutMidQueueNode_nonTcb st tid hInv k o hNot)
    (spliceOutMidQueueNode_sameTaintWords st tid hInv)

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

/-- The reply-waiter unlink writes no reference table. -/
theorem unlinkReplyWaiterOpt_referenceTables (st : SystemState) (w : SeLe4n.ThreadId)
    (s? : Option SeLe4n.ThreadId) :
    (st.unlinkReplyWaiterOpt w s?).referenceTables = st.referenceTables := by
  have h := congrArg SystemState.referenceTables (SystemState.unlinkReplyWaiterOpt_eq_objects st w s?)
  exact h.trans rfl

/-- The reply-link teardown rewrites a reply and a thread. -/
theorem consumeReplyLink_tableReferenceFrame (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (hInv : st.objects.invExt) :
    SystemState.TableReferenceFrame st (Lifecycle.Suspend.consumeReplyLink st tid tcb) := by
  unfold Lifecycle.Suspend.consumeReplyLink
  split
  · exact .refl _
  · next rid _ =>
    exact consumeCallerReply_tableReferenceFrame hInv (SystemState.consumeCallerReply_eq_link _ tid rid)

/-- The cancelled caller's reply-frame splice rewrites replies only. -/
theorem spliceThreadReplyFrameOut_tableReferenceFrame (st : SystemState) (tcb : TCB)
    (hInv : st.objects.invExt) :
    SystemState.TableReferenceFrame st (spliceThreadReplyFrameOut st tcb) := by
  unfold spliceThreadReplyFrameOut
  split
  · exact .refl _
  · next rid _ =>
    rcases spliceReplyFrameOutOrSelf_cases st rid with h | h
    · rw [h]; exact .refl _
    · exact ⟨spliceReplyFrameOut_referenceTables h, fun oid => by
        rcases spliceReplyFrameOut_objects_rewrite hInv h oid with e | ⟨_, _, h1, h2, _⟩
        · rw [e]
        · rw [h1, h2]; rfl⟩

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
  | blockedOnSend _ | blockedOnReceive _ | blockedOnCall _ =>
    exact (removeFromAllEndpointQueues_tableReferenceFrame st victim hInv).trans
      (restoreToReadyStaging_tableReferenceFrame _ victim _
        (removeFromAllEndpointQueues_preserves_objects_invExt st victim hInv))
  | blockedOnNotification _ =>
    exact (removeFromNotificationWaitQueue_tableReferenceFrame st victim hInv).trans
      (restoreToReadyStaging_tableReferenceFrame _ victim _
        (removeFromNotificationWaitQueue_preserves_objects_invExt st victim hInv))
  | blockedOnReply _ _ =>
    have hR := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt
      st victim tcb hInv
    have hS := spliceThreadReplyFrameOut_preserves_objects_invExt
      (Lifecycle.Suspend.returnDonationToCancelledCaller st victim tcb) tcb hR
    have hU := Lifecycle.Suspend.restoreToReadyStaging_invExt _ victim
      (some Architecture.cancelledIpcFrame) hS
    dsimp only
    have f3 := ((returnDonationToCancelledCaller_tableReferenceFrame st victim tcb hInv).trans
      (spliceThreadReplyFrameOut_tableReferenceFrame _ tcb hR)).trans
      (restoreToReadyStaging_tableReferenceFrame _ victim (some Architecture.cancelledIpcFrame) hS)
    have f4 := f3.trans (consumeReplyLink_tableReferenceFrame _ victim tcb hU)
    exact f4.trans (.of_agreeOffRunLinks
      (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffRunLinks _ _ _)
      (unlinkReplyWaiterOpt_referenceTables _ _ _))

/-- **WS-ZA ZA4.5: the teardown keeps the run queues in agreement with the
links** — it writes no scheduler slot (`cancelIpcBlocking_scheduler_eq`) and moves
no thread (`cancelIpcBlocking_placement_frame`). -/
theorem cancelIpcBlocking_runQueueStage (st : SystemState) (victim : SeLe4n.ThreadId)
    (tcb : TCB) : SystemState.RunQueueStage st (Lifecycle.Suspend.cancelIpcBlocking st victim tcb) :=
  have hS := Lifecycle.Suspend.cancelIpcBlocking_scheduler_eq st victim tcb
  SystemState.RunQueueStage.of_placement
    (fun hInv => Lifecycle.Suspend.cancelIpcBlocking_preserves_objects_invExt st victim tcb hInv)
    (by rw [hS]) (by rw [hS])
    (fun hInv x => cancelIpcBlocking_placement_frame st victim tcb hInv x)
    (fun hInv => cancelIpcBlocking_stateMono st victim tcb hInv)
    (fun hInv => cancelIpcBlocking_tableReferenceFrame st victim tcb hInv)
    (fun hInv => cancelIpcBlocking_releaseStateAgree st victim tcb hInv)
    (fun hInv => cancelIpcBlocking_refillViewsKept st victim tcb hInv)
    (fun hInv => cancelIpcBlocking_yieldLinksKept st victim tcb hInv)
    (hRes := by rw [Lifecycle.Suspend.cancelIpcBlocking_machine_eq st victim tcb])

/-- ...and so does the teardown with its replenishment migration. -/
theorem cancelIpcBlockingMigrated_runQueueStage (st : SystemState) (victim : SeLe4n.ThreadId)
    (tcb : TCB) : SystemState.RunQueueStage st (cancelIpcBlockingMigrated victim tcb st) := by
  unfold cancelIpcBlockingMigrated
  split
  · exact (cancelIpcBlocking_runQueueStage st victim tcb).trans
      (migrateSchedContextReplenishment_runQueueStage _ _ _ _)
  · exact cancelIpcBlocking_runQueueStage st victim tcb

/-- ...and so does the reclaim-complete teardown: its last step is a dequeue. -/
theorem cancelIpcBlockingReclaimed_runQueueStage (st : SystemState) (victim : SeLe4n.ThreadId)
    (tcb : TCB) : SystemState.RunQueueStage st (cancelIpcBlockingReclaimed victim tcb st) := by
  refine (cancelIpcBlockingMigrated_runQueueStage st victim tcb).trans ?_
  unfold cancelIpcBlockingReclaimed descheduleUnboundHolder descheduleAtPlacement
  split
  · exact .refl _
  · exact descheduleAt_runQueueStage _ _ _

/-- **WS-RR RR8.11: the migrated teardown establishes the SM5.H replenish-affinity
invariant** — the second half of the obligation `cancelIpcBlockingMigrated`'s
docstring registered, and it takes **no** hypothesis beyond the object-store
invariant and the pre-state invariant itself.

That is what the destination fix buys.  With the destination read off the
post-teardown binding (`replenishHomeOfSchedContext`) the "the destination is
right" obligation is `replenishHomeOfSchedContext_spec`, which is free; with the
victim's pre-state home in that position it was **false** on a refused reclaim, and
no hypothesis short of "the reclaim committed" could have rescued it.

The three remaining obligations are the teardown's own frames: it writes no
scheduler slot (`cancelIpcBlocking_scheduler_eq`), no scheduling context but the
one the reclaim hands back (`cancelIpcBlocking_getSchedContext?_ne`), and no
thread's `cpuAffinity` (`cancelIpcBlocking_determineTargetCore_eq`).  The
migration's *source* is the pre-state bound thread's home, which
`cancelledCallerDonation?_some` supplies: the resolver reads the context off the
victim's own reply frame head, and that context's `boundThread` **is** the holder
the resolver names. -/
theorem cancelIpcBlockingMigrated_establishes_replenishQueueAffinityConsistent_smp
    (victim : SeLe4n.ThreadId) (tcb : TCB) (st : SystemState)
    (hInv : st.objects.invExt)
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
    obtain ⟨-, rid, r, sc, -, -, -, hSc, -, hBound⟩ :=
      cancelledCallerDonation?_some st victim tcb scId holder hD
    exact migrateSchedContextReplenishment_to_home_preserves_affinityConsistent_smp
      st (Lifecycle.Suspend.cancelIpcBlocking st victim tcb) scId
      (determineTargetCore st holder) sc holder
      (fun c => by rw [Lifecycle.Suspend.cancelIpcBlocking_scheduler_eq]; rfl)
      (fun scId₀ hne => cancelIpcBlocking_getSchedContext?_ne st victim tcb hInv scId₀
        (fun s h hD' => by rw [hD] at hD'; cases hD'; exact hne))
      (fun tid => cancelIpcBlocking_determineTargetCore_eq st victim tcb hInv tid)
      hSc hBound rfl hCons

-- `v0.35.158`: `enqueueAbortedHolderOnCore_replenishQueueOnCore` and
-- `wakeAbortedDonationHolder_replenishQueueOnCore` are retired with the wake;
-- the reclaim's deschedule step has the same frame beside its definition
-- (`descheduleUnboundHolder_replenishQueueOnCore`, `Lifecycle/Suspend.lean`).

/-- **WS-RR RR8.11: the cross-core cancellation composite establishes the SM5.H
replenish-affinity invariant.**

The lift adds nothing, for the same reason RR8.10's bundle lift adds no premise:
the two scheduler steps the composite performs over the migrated teardown — the
reclaim's holder deschedule and the victim's placement removal — write run queues
and current slots, which the invariant does not read, and no object at all, so
all three of its readings are the migrated teardown's. -/
theorem cancelIpcBlockingOnCore_establishes_replenishQueueAffinityConsistent_smp
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId) (st : SystemState)
    (hInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st) :
    replenishQueueAffinityConsistent_smp
      (cancelIpcBlockingOnCore victim tcb executingCore st).1 := by
  have hBase := cancelIpcBlockingMigrated_establishes_replenishQueueAffinityConsistent_smp
    victim tcb st hInv hCons
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

/-- **WS-RR RR8.11: a refused reclaim migrates nothing.**

This is the defect the destination fix closed, stated.  The reclaim's guards are
fail-closed — the outer-caller check, HP4.6's recipient guard and the head
validation all refuse — and on a refusal `returnDonationToCancelledCaller` returns
its own input with `scId` still bound to the holder.  With the destination read
off the post-teardown binding the migration's source and destination then coincide,
so `migrateSchedContextReplenishment_noop` collapses it to the identity; with the
victim's pre-state home in that position it moved `scId`'s replenishments to a core
no thread bound to `scId` is homed on, which is
`replenishQueueAffinityConsistentOnCore`'s own negation. -/
theorem cancelIpcBlockingMigrated_eq_teardown_of_reclaim_inert
    (victim : SeLe4n.ThreadId) (tcb : TCB) (st : SystemState) (hInv : st.objects.invExt)
    (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (hD : Lifecycle.Suspend.cancelledCallerDonation? st victim tcb = some (scId, holder))
    (hInert : Lifecycle.Suspend.returnDonationToCancelledCaller st victim tcb = st) :
    cancelIpcBlockingMigrated victim tcb st
      = Lifecycle.Suspend.cancelIpcBlocking st victim tcb := by
  obtain ⟨-, rid, r, sc, -, -, -, hSc, -, hBound⟩ :=
    cancelledCallerDonation?_some st victim tcb scId holder hD
  have hPost : (Lifecycle.Suspend.cancelIpcBlocking st victim tcb).getSchedContext? scId
      = some sc := by
    rw [cancelIpcBlocking_getSchedContext?_eq_of_reclaim_inert st victim tcb hInv hInert scId,
      hSc]
  have hDest : replenishHomeOfSchedContext (Lifecycle.Suspend.cancelIpcBlocking st victim tcb)
      scId (determineTargetCore st holder) = determineTargetCore st holder := by
    rw [replenishHomeOfSchedContext_eq_of_bound _ scId _ sc holder hPost hBound,
      cancelIpcBlocking_determineTargetCore_eq st victim tcb hInv holder]
  unfold cancelIpcBlockingMigrated
  rw [hD]
  dsimp only
  rw [hDest, migrateSchedContextReplenishment_noop]

/-- **WS-RR RR8.11: a committed reclaim migrates exactly where it did before the
fix.**

The other half of the measurement: where the reclaim commits, the post-teardown
binding names the cancelled caller, so the destination the resolver reads *is* the
victim's home — the pre-fix expression, since the teardown writes no `cpuAffinity`.
So the fix is a no-op on every state the tree's stated coherence facts admit, which
is why the golden trace is byte-identical. -/
theorem cancelIpcBlockingMigrated_eq_victim_home_of_committed
    (victim : SeLe4n.ThreadId) (tcb : TCB) (st : SystemState) (hInv : st.objects.invExt)
    (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId)
    (hD : Lifecycle.Suspend.cancelledCallerDonation? st victim tcb = some (scId, holder))
    (scPost : SeLe4n.Kernel.SchedContext)
    (hPost : (Lifecycle.Suspend.cancelIpcBlocking st victim tcb).getSchedContext? scId
      = some scPost)
    (hBoundPost : scPost.boundThread = some victim) :
    cancelIpcBlockingMigrated victim tcb st
      = migrateSchedContextReplenishment (Lifecycle.Suspend.cancelIpcBlocking st victim tcb)
          scId (determineTargetCore st holder) (determineTargetCore st victim) := by
  unfold cancelIpcBlockingMigrated
  rw [hD]
  dsimp only
  rw [replenishHomeOfSchedContext_eq_of_bound _ scId _ scPost victim hPost hBoundPost,
    cancelIpcBlocking_determineTargetCore_eq st victim tcb hInv victim]

/-- WS-ZA ZA6.6: the yield-link cancel places and unplaces no thread. -/
theorem cancelYieldTo_threadPlacedOnSomeCore (st : SystemState) (tid u : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    threadPlacedOnSomeCore (cancelYieldTo st tid) u = threadPlacedOnSomeCore st u :=
  threadPlacedOnSomeCore_of_scheduler_eq st _ u (SystemState.cancelYieldTo_scheduler st tid)
    (SystemState.cancelYieldTo_objectsAgreeOffYield st tid hInv).runCoresAgree

section SuspendPayoff
open SeLe4n.Kernel.Concurrency
open SeLe4n.Kernel.Lifecycle.Suspend

/-- WS-ZA ZA4.5: the suspend's donation-cancellation dispatcher keeps the run
queues in agreement with the links, on the arm that succeeds. -/
theorem cancelSuspendDonation_runQueueStage (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hStep : (match tcb.schedContextBinding with
              | .unbound => (Except.ok st : Except KernelError SystemState)
              | .bound _ => cancelBoundDonationOnCore st tid tcb
              | .donated _ _ => cancelDonatedDonationOnCore st tid tcb) = .ok st') :
    SystemState.RunQueueStage st st' := by
  revert hStep
  cases tcb.schedContextBinding with
  | unbound => intro hStep; cases hStep; exact .refl st
  | bound _ => exact cancelBoundDonationOnCore_runQueueStage
  | donated _ _ => exact cancelDonatedDonationOnCore_runQueueStage

/-- The suspend's donation-cancellation dispatcher moves no thread between
scheduler slots: both arms write no current slot and keep every thread's run
core, so every thread's placement is the pre-state's. -/
theorem cancelSuspendDonation_placedCoreOf? (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (u : SeLe4n.ThreadId)
    (hInv : st.objects.invExt)
    (hStep : (match tcb.schedContextBinding with
              | .unbound => (Except.ok st : Except KernelError SystemState)
              | .bound _ => cancelBoundDonationOnCore st tid tcb
              | .donated _ _ => cancelDonatedDonationOnCore st tid tcb) = .ok st') :
    placedCoreOf? st' u = placedCoreOf? st u := by
  revert hStep
  cases tcb.schedContextBinding with
  | unbound => intro hStep; cases hStep; rfl
  | bound _ =>
    intro hStep
    exact placedCoreOf?_congr_of_runCores_current_eq u
      (cancelBoundDonationOnCore_runCoresAgree hInv hStep)
      (fun c => (cancelBoundDonationOnCore_runQueue_current_eq st st' tid tcb c hStep).2)
  | donated _ _ =>
    intro hStep
    exact placedCoreOf?_congr_of_runCores_current_eq u
      (cancelDonatedDonationOnCore_runCoresAgree hInv hStep)
      (fun c => (cancelDonatedDonationOnCore_runQueue_current_eq st st' tid tcb c hStep).2)

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

/-- **`v0.35.158` — the payoff: a `.tcbSuspend` of a client does not hand the
server it called the CPU on nobody's budget.**

`descheduleUnboundHolder_holder_unplaced` says the reclaim leaves the holder it
unbound on no scheduler slot.  That is a statement about the state **G2**
leaves, and the live `.tcbSuspend` runs six more stages after it — so until this
theorem the user-visible guarantee would rest on
`tests/SmpCancellationSuite.lean` §3.26 *measuring* the whole transition rather
than on a proof of it.  This is that lift, and it is a composition of frames
rather than a new argument: the chain revert re-buckets inside the queue a
thread already sits in, both donation arms wake and deschedule nothing, the
placement removal is about the **victim**, the pending-state clear and the
`.Inactive` write touch objects alone, and the scheduling point dispatches only
a thread the executing core's run queue holds.

**Three hypotheses are load-bearing rather than bookkeeping.**  `holder ≠ victim`
is not assumed — it is `cancelUnboundHolder?_ne_victim`, structural in the
trigger, which is what licenses G4 to leave the holder alone.  Single placement
of the holder (`hUnique`) is what makes one removal a removal from *every* core;
the scheduler maintains it by construction (`enqueueRunnableOnCore`'s global
guard, dequeue-on-dispatch, `currentThreadUniqueAcrossCores`), and the statement
takes the fact rather than a bundle that entails it, so a caller holding only the
scheduler invariant can discharge it.  And the run queues agree with the
threads' links (`hR`, WS-ZA ZA4.5), carried through every stage
(`SystemState.RunQueueStage`), because the chooser walks the links and its
membership fact — the dispatched thread is *in* the queue, hence not the holder —
is stated under the agreement; the object-store invariant rides beside it because
each stage needs its predecessor's to state its own.  A scheduling point places a
thread only by dispatching it, so the holder's TCB is never consulted. -/
theorem suspendThreadOnCore_holder_unplaced
    (st st' : SystemState) (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId)
    (sgi? : Option (CoreId × SgiKind)) (tcb : TCB) (holder : SeLe4n.ThreadId)
    (hTcb : st.getTcb? vtid.val = some tcb)
    (hW : cancelUnboundHolder? st (cancelIpcBlockingMigrated vtid.val tcb st)
            vtid.val tcb = some holder)
    (hUnique : ∀ c c' : CoreId,
        (holder ∈ st.scheduler.runQueueOnCore c
          ∨ st.scheduler.currentOnCore c = some holder) →
        (holder ∈ st.scheduler.runQueueOnCore c'
          ∨ st.scheduler.currentOnCore c' = some holder) →
        c = c')
    (hInv : st.objects.invExt) (hR : st.runQueueRefined)
    (hStep : suspendThreadOnCore st vtid executingCore = .ok (st', sgi?)) :
    threadPlacedOnSomeCore st' holder = false := by
  have hNe : holder ≠ vtid.val :=
    cancelUnboundHolder?_ne_victim st _ vtid.val tcb holder hW
  -- Single placement transports across the migrated teardown, which writes no
  -- run queue and no current slot.
  have hUniqueM : ∀ c c' : CoreId,
      ((cancelIpcBlockingMigrated vtid.val tcb st).queuedOn c holder = true
        ∨ (cancelIpcBlockingMigrated vtid.val tcb st).scheduler.currentOnCore c
            = some holder) →
      ((cancelIpcBlockingMigrated vtid.val tcb st).queuedOn c' holder = true
        ∨ (cancelIpcBlockingMigrated vtid.val tcb st).scheduler.currentOnCore c'
            = some holder) →
      c = c' := by
    have hRM := ((cancelIpcBlockingMigrated_runQueueStage st vtid.val tcb).1 hInv hR).2
    intro c c' hc hc'
    replace hc := hc.imp_left (SystemState.mem_runQueueOnCore_of_queuedOn hRM)
    replace hc' := hc'.imp_left (SystemState.mem_runQueueOnCore_of_queuedOn hRM)
    rw [cancelIpcBlockingMigrated_runQueueOnCore, cancelIpcBlockingMigrated_currentOnCore,
      cancelIpcBlocking_scheduler_eq] at hc hc'
    exact hUnique c c' hc hc'
  -- G2 — the reclaim, where the deschedule's payoff lands.
  have hP1 : threadPlacedOnSomeCore (cancelIpcBlockingReclaimed vtid.val tcb st) holder
      = false := by
    rw [threadPlacedOnSomeCore_eq_isSome_placedCoreOf?]
    unfold cancelIpcBlockingReclaimed
    rw [descheduleUnboundHolder_holder_unplaced st _ vtid.val tcb holder hW hUniqueM]
    rfl
  -- The agreement, carried stage by stage to the scheduling point.
  have hS1 := cancelIpcBlockingReclaimed_runQueueStage st vtid.val tcb
  simp only [suspendThreadOnCore] at hStep
  split at hStep
  case h_2 => exact absurd hStep (by simp)
  case h_1 tcb0 hTcb0 =>
    obtain rfl : tcb = tcb0 := by rw [hTcb] at hTcb0; exact Option.some.inj hTcb0
    split at hStep
    case isTrue => exact absurd hStep (by simp)
    case isFalse =>
      -- G2b — the cross-core priority-inheritance revert.
      have hP2 : threadPlacedOnSomeCore
          (match PriorityInheritance.blockingServer st vtid.val with
           | some serverId => (PriorityInheritance.propagatePipChainCrossCore
               (cancelIpcBlockingReclaimed vtid.val tcb st) serverId executingCore).1
           | none => cancelIpcBlockingReclaimed vtid.val tcb st) holder = false := by
        cases PriorityInheritance.blockingServer st vtid.val with
        | none => exact hP1
        | some serverId =>
            rw [propagatePipChainCrossCore_threadPlacedOnSomeCore _ _ _ _ _ (hS1.1 hInv hR).1]
            exact hP1
      have hS2 : SystemState.RunQueueStage st
          (match PriorityInheritance.blockingServer st vtid.val with
           | some serverId => (PriorityInheritance.propagatePipChainCrossCore
               (cancelIpcBlockingReclaimed vtid.val tcb st) serverId executingCore).1
           | none => cancelIpcBlockingReclaimed vtid.val tcb st) := by
        cases PriorityInheritance.blockingServer st vtid.val with
        | none => exact hS1
        | some serverId =>
            exact hS1.trans (PriorityInheritance.propagatePipChainCrossCore_runQueueStage _ _ _ _)
      -- G3 onwards, on the post-revert state.
      revert hStep
      split
      · intro hStep; exact absurd hStep (by simp)
      · next s3 hDon =>
        intro hStep
        -- G3 — the donation arm.
        have hP3 : threadPlacedOnSomeCore s3 holder = false := by
          rw [cancelSuspendDonation_threadPlacedOnSomeCore _ s3 vtid.val _ holder (hS2.1 hInv hR).1 hDon]
          exact hP2
        have hS3 := hS2.trans (cancelSuspendDonation_runQueueStage _ s3 vtid.val _ hDon)
        -- G4 — the placement removal, which is about the VICTIM.
        have hP4 : threadPlacedOnSomeCore
            (descheduleAt s3 vtid.val (placedCoreOf? st vtid.val)) holder = false := by
          rw [descheduleAt_threadPlacedOnSomeCore_ne s3 vtid.val holder _ hNe]; exact hP3
        have hS4 := hS3.trans (descheduleAt_runQueueStage s3 vtid.val (placedCoreOf? st vtid.val))
        -- G5 / G6 — two object writes, both scheduler-free.
        have hP6 : threadPlacedOnSomeCore
            ((Lifecycle.Suspend.clearPendingState
              (descheduleAt s3 vtid.val (placedCoreOf? st vtid.val)) vtid.val).updateTcb
                vtid.val (fun t => { t with threadState := .Inactive })) holder = false := by
          have hInv4 := (hS4.1 hInv hR).1
          rw [threadPlacedOnSomeCore_updateTcb _ _ _ (fun t => { t with threadState := .Inactive })
              (fun _ => rfl)
              (by unfold Lifecycle.Suspend.clearPendingState
                  exact SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv4),
            Lifecycle.Suspend.clearPendingState,
            threadPlacedOnSomeCore_updateTcb _ _ _ (fun tcb => { tcb with
              pendingMessage := none, timeoutBudget := none, queuePrevCode := 0,
              queueNextCode := 0, queuePPrevCode := 0 }) (fun _ => rfl) hInv4]
          exact hP4
        have hS6 : SystemState.RunQueueLinkStage st
            ((clearPendingStateValid (descheduleAt s3 vtid.val (placedCoreOf? st vtid.val))
              vtid).updateTcb vtid.val (fun t => { t with threadState := .Inactive })) :=
          (hS4.1.trans (by
            unfold clearPendingStateValid clearPendingState
            exact SystemState.RunQueueLinkStage.updateTcb _ vtid.val (fun _ _ => rfl))).trans
          (SystemState.RunQueueLinkStage.updateTcb _ vtid.val (fun _ _ => rfl))
        -- G6b — the yield-link cancel, which writes no placement.
        have hInv6 := (hS6 hInv hR).1
        have hP6b : threadPlacedOnSomeCore (cancelYieldTo
            ((clearPendingStateValid (descheduleAt s3 vtid.val (placedCoreOf? st vtid.val))
              vtid).updateTcb vtid.val (fun t => { t with threadState := .Inactive })) vtid.val)
            holder = false := by
          rw [cancelYieldTo_threadPlacedOnSomeCore _ _ _ hInv6]; exact hP6
        have hS6b := hS6.trans (SystemState.cancelYieldTo_runQueueStage _ vtid.val).1
        -- G7 — the local scheduling point.
        exact suspendRescheduleOnCore_preserves_unplaced _ st' _ executingCore
          _ _ sgi? holder (hS6b hInv hR).1 ((hS6b hInv hR).2 executingCore) hStep hP6b

end SuspendPayoff

end SeLe4n.Kernel
