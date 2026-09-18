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
lift to the cross-core `cancelIpcBlockingOnCore` that the live `.tcbSuspend`
dispatch actually runs.  This module is both, and nothing else.

Three things decide its shape.

**The premises are per-arm, because the facts are.**  `ipcInvariantFull` entails
none of the queue-coherence facts the three bodies need (that is stated at each
of them and is why they take hypotheses at all), so demanding every fact
unconditionally would make a `.ready` cancellation — which commits no write at
all — carry the reply arm's six-fact pack.  `cancelIpcBlockingArmPremises` gates
each group on the arm's own `ipcState` equation, so a caller discharges exactly
what its arm reaches, and the `.ready` arm discharges nothing.

**Only one of the twenty conjuncts reads the scheduler**, which is what makes the
cross-core lift short rather than a second twenty-conjunct argument.
`passiveServerIdle` is that conjunct — every other one is a property of the
object store alone — and `ipcInvariantFull_of_descheduleFrame` (WS-RR RR2.5) is
the tool it was factored for: objects unchanged plus a `passiveServerIdleFrame`
transports the whole bundle.

**The composite adds three scheduler steps, and each frames for its own
reason.**  The replenishment migration writes neither a run queue nor a current
slot, so it frames by `of_objects_scheduler_eq`.  The holder wake only
*inserts*, so a thread absent from the post-state queue was absent from the
pre-state one — the pullback direction `passiveServerIdleFrame` asks for, which
is why an enqueue can never break a conjunct whose antecedent is
*not queued*.  And the victim's placement removal is
`descheduleAtPlacement_passiveServerIdleFrame`, whose obligation is discharged
rather than assumed: `cancelIpcBlocking_victim_ready` establishes that a
cancelled victim ends `.ready` on every arm, and `.ready` is a state
`passiveServerIdleAllowed` admits.
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

The fact the cross-core composite's deschedule needs, and the reason it needs it:
taking a thread off its run queue hands `passiveServerIdle` an obligation it did
not have, dischargeable only if that thread's `ipcState` is one the predicate
admits.  `.ready` is — so the obligation is free, but only because it is
*established* here rather than assumed at the call site.

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
      removeFromAllNotificationWaitLists_tcb_lookup st v v.toObjId tcbV hObjInv hAt
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
      rw [hAtY] at h
      cases h
      exact hReadyY
    | some rid =>
      intro t' h
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

/-- **WS-RR RR8.10**: the reply arm's six premises, named.

They are cited together everywhere — the arm keystone takes all six and
`CLAUDE.md`'s RR8.7 note lists them as a group — so they get one name rather than
six positional hypotheses threaded through the composite.  None is entailed by
`ipcInvariantFull`: `donationChainWellFormed` is a separate predicate,
`sweptThreadOffQueueChains` is the queue-connectivity fact the bundle carries
nowhere, and the last four are the local coherence facts WS-HP HP7 measured as
stated rather than derived. -/
structure cancelReplyArmPremises (st : SystemState) (v : SeLe4n.ThreadId) (tcbV : TCB) : Prop where
  chain : donationChainWellFormed st
  offQueue : sweptThreadOffQueueChains st v
  owed : ∀ rid, tcbV.replyObject = some rid → replyFrameHeadHolderDonation st rid v
  holder : donatedContextIsOwnerFrameHead st v
  stack : cancelDonationStackValid st v tcbV
  abortCoherent : ∀ (scId : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId),
    Lifecycle.Suspend.cancelledCallerDonation? st v tcbV = some (scId, holder) →
    abortHolderQueueCoherent st holder

/-- **WS-RR RR8.10**: the teardown's premises, **gated on the arm that needs
them**.

Three fields, one per non-identity arm, each an implication from that arm's own
`ipcState` equation.  The `.ready` arm appears nowhere, which is the point: it
commits no write, so it owes nothing, and an unconditional pack would have made
it carry the reply arm's six facts to prove that the identity preserves the
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
      hLookup hIp hBundle hAllBudgetsNone (hArms.notificationArm nId hIp)
  | blockedOnReply ep rt =>
    have hR := hArms.replyArm ep rt hIp
    exact cancelIpcBlocking_replyArm_preserves_ipcInvariantFull st v tcbV ep rt hObjInv hLookup
      hIp hBundle hR.chain hAllBudgetsNone hR.offQueue hR.owed hR.holder hR.stack hR.abortCoherent

-- ============================================================================
-- §3  The two scheduler frames the cross-core composite adds
-- ============================================================================

/-- **WS-RR RR8.10**: the replenishment migration frames `passiveServerIdle`.

It moves a scheduling context's pending replenishments between cores' replenish
queues, which is neither a run queue nor a current slot — so all three of
`of_objects_scheduler_eq`'s inputs are existing `@[simp]` frames and the proof is
their composition.  Stated at `bootCoreId` because that is the only core
`passiveServerIdle` reads. -/
theorem cancelIpcBlockingMigrated_passiveServerIdleFrame
    (victim : SeLe4n.ThreadId) (tcb : TCB) (st : SystemState) :
    passiveServerIdleFrame (Lifecycle.Suspend.cancelIpcBlocking st victim tcb)
      (cancelIpcBlockingMigrated victim tcb st) :=
  passiveServerIdleFrame.of_objects_scheduler_eq
    (cancelIpcBlockingMigrated_objects victim tcb st)
    (cancelIpcBlockingMigrated_runQueueOnCore victim tcb st bootCoreId)
    (cancelIpcBlockingMigrated_currentOnCore victim tcb st bootCoreId)

/-- **WS-RR RR8.10**: the aborted holder's enqueue keeps every thread already on
a run queue.

The monotonicity the wake's frame is built from, and the sibling of
`enqueueRunnableOnCore_mem_old` for the guarded enqueue this path uses.  Both of
the guard's refusal arms are the identity, and the admitting arm inserts into one
core's queue and leaves the others alone, so membership can only grow. -/
theorem enqueueAbortedHolderOnCore_mem_old (st : SystemState) (c c' : CoreId)
    (tid x : SeLe4n.ThreadId) (hMem : x ∈ st.scheduler.runQueueOnCore c') :
    x ∈ (enqueueAbortedHolderOnCore st c tid).scheduler.runQueueOnCore c' := by
  unfold enqueueAbortedHolderOnCore
  cases hT : st.getTcb? tid with
  | none => simp only []; exact hMem
  | some t =>
    simp only []
    by_cases hG : (runnableOnSomeCore st tid || runningOnSomeCore st tid) = true
    · rw [if_pos hG]; exact hMem
    · rw [if_neg hG]
      by_cases hcc : c' = c
      · subst hcc
        show x ∈ (st.scheduler.setRunQueueOnCore c'
          ((st.scheduler.runQueueOnCore c').insert tid (t.boostedPriority))).runQueueOnCore c'
        rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
        exact (RunQueue.mem_insert _ tid _ x).mpr (Or.inl hMem)
      · show x ∈ (st.scheduler.setRunQueueOnCore c
          ((st.scheduler.runQueueOnCore c).insert tid (t.boostedPriority))).runQueueOnCore c'
        rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ c c' _ (Ne.symm hcc)]
        exact hMem

/-- **WS-RR RR8.10**: the holder wake frames `passiveServerIdle`.

An *insert* can never break a conjunct whose antecedent is "not queued": the
frame's pullback asks a thread absent from the **post**-state queue to be absent
from the pre-state one, and that is monotonicity read backwards.  So the wake
frames with no hypothesis at all — no fact about the holder, and none about the
victim — which is worth stating because the wake is the step OD1.7 added and the
one a reader might expect to owe something here. -/
theorem wakeAbortedDonationHolder_passiveServerIdleFrame
    (stPre stPost : SystemState) (victim : SeLe4n.ThreadId) (tcb : TCB) :
    passiveServerIdleFrame stPost (wakeAbortedDonationHolder stPre stPost victim tcb) := by
  refine ⟨fun tid tcb' hAt hUnbound hNotQ hNotCur _ => ?_⟩
  refine ⟨tcb', ?_, hUnbound, ?_, ?_, rfl⟩
  · rw [wakeAbortedDonationHolder_objects stPre stPost victim tcb] at hAt; exact hAt
  · intro hMemPre
    apply hNotQ
    unfold wakeAbortedDonationHolder
    split
    · exact hMemPre
    · exact enqueueAbortedHolderOnCore_mem_old stPost _ _ _ tid hMemPre
  · rw [wakeAbortedDonationHolder_currentOnCore stPre stPost victim tcb bootCoreId] at hNotCur
    exact hNotCur

-- ============================================================================
-- §4  The lift to the cross-core composite
-- ============================================================================

/-- **WS-RR RR8.10 — the payoff**: the **cross-core** cancellation preserves
`ipcInvariantFull`, on every arm.

The transition the live `.tcbSuspend` dispatch runs, and the second half of the
RR7.22 residual.  Its premises are the teardown's and nothing more: the three
scheduler steps the composite adds over `cancelIpcBlocking` contribute no
hypothesis, because each frames for a reason that is a property of the step
rather than of the state (see the three frames above), and the one obligation
that *is* about the state — the victim's `ipcState` at the deschedule — is
discharged from `cancelIpcBlocking_victim_ready`.

`ipcInvariantFull_of_descheduleFrame` is the whole argument: objects unchanged
(`cancelIpcBlockingOnCore_objects_eq`, which is where the three steps' object
frames already compose) plus a `passiveServerIdleFrame` chained from the three.
Nineteen of the twenty conjuncts never see the scheduler, so there is nothing
else to transport. -/
theorem cancelIpcBlockingOnCore_preserves_ipcInvariantFull
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt) (hLookup : lookupTcb st victim = some tcb)
    (hBundle : ipcInvariantFull st) (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hArms : cancelIpcBlockingArmPremises st victim tcb) :
    ipcInvariantFull (cancelIpcBlockingOnCore victim tcb executingCore st).1 := by
  have hTeardown := cancelIpcBlocking_preserves_ipcInvariantFull st victim tcb hObjInv hLookup
    hBundle hAllBudgetsNone hArms
  have hReady := cancelIpcBlocking_victim_ready st victim tcb hObjInv hLookup
  -- the objects the three scheduler steps do not touch
  have hObjsWake : (wakeAbortedDonationHolder st (cancelIpcBlockingMigrated victim tcb st)
      victim tcb).objects = (Lifecycle.Suspend.cancelIpcBlocking st victim tcb).objects := by
    rw [wakeAbortedDonationHolder_objects, cancelIpcBlockingMigrated_objects]
  -- the deschedule's own obligation, discharged from the victim's post-teardown state
  have hRemoved : ∀ t, (wakeAbortedDonationHolder st (cancelIpcBlockingMigrated victim tcb st)
      victim tcb).objects[victim.toObjId]? = some (.tcb t) →
      t.schedContextBinding ≠ SchedContextBinding.unbound ∨ passiveServerIdleAllowed t.ipcState := by
    intro t hAt
    rw [hObjsWake] at hAt
    exact Or.inr (Or.inl (hReady t hAt))
  refine ipcInvariantFull_of_descheduleFrame _ _ hTeardown
    (cancelIpcBlockingOnCore_objects_eq victim tcb executingCore st) ?_
  rw [cancelIpcBlockingOnCore_state_eq]
  exact ((cancelIpcBlockingMigrated_passiveServerIdleFrame victim tcb st).trans
    (wakeAbortedDonationHolder_passiveServerIdleFrame st _ victim tcb)).trans
    (descheduleAtPlacement_passiveServerIdleFrame _ victim hRemoved)

end SeLe4n.Kernel
