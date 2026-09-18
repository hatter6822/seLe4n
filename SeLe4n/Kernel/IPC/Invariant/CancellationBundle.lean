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

-- ============================================================================
-- §4  WS-RR RR8.11 — the composite establishes the SM5.H replenish-affinity
--     invariant
-- ============================================================================

/-- WS-RR RR8.11: `getSchedContext?` is determined by which `.schedContext` the
store holds at the context's key, so two states agreeing on that at one key agree
on the reading there.  The bridge every step frame below crosses: the pieces the
tree already has are *kind* biconditionals over `objects[·]?`, and this turns one
into the typed reading. -/
private theorem getSchedContext?_of_kind_iff {sa sb : SystemState}
    {scId : SeLe4n.SchedContextId}
    (h : ∀ sc : SeLe4n.Kernel.SchedContext,
      sb.objects[scId.toObjId]? = some (.schedContext sc) ↔
      sa.objects[scId.toObjId]? = some (.schedContext sc)) :
    sb.getSchedContext? scId = sa.getSchedContext? scId := by
  cases hA : sa.getSchedContext? scId with
  | none =>
    cases hB : sb.getSchedContext? scId with
    | none => rfl
    | some sc =>
      exact absurd
        ((SystemState.getSchedContext?_eq_some_iff sa scId sc).mpr
          ((h sc).mp ((SystemState.getSchedContext?_eq_some_iff sb scId sc).mp hB)))
        (by rw [hA]; simp)
  | some sc =>
    rw [(SystemState.getSchedContext?_eq_some_iff sb scId sc).mpr
      ((h sc).mpr ((SystemState.getSchedContext?_eq_some_iff sa scId sc).mp hA))]

/-- WS-RR RR8.11: the restore writes one TCB, so it writes no scheduling
context. -/
private theorem restoreToReadyStaging_getSchedContext?_eq (st : SystemState)
    (tid : SeLe4n.ThreadId) (frame : Option Architecture.SyscallReturnFrame)
    (hInv : st.objects.invExt) (scId : SeLe4n.SchedContextId) :
    (Lifecycle.Suspend.restoreToReadyStaging st tid frame).getSchedContext? scId
      = st.getSchedContext? scId := by
  refine getSchedContext?_of_kind_iff (fun sc => ?_)
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
private theorem spliceThreadReplyFrameOut_getSchedContext?_eq (st : SystemState)
    (tcb : TCB) (hInv : st.objects.invExt) (scId : SeLe4n.SchedContextId) :
    (spliceThreadReplyFrameOut st tcb).getSchedContext? scId = st.getSchedContext? scId := by
  unfold spliceThreadReplyFrameOut
  cases tcb.replyObject with
  | none => rfl
  | some rid => exact spliceReplyFrameOutOrSelf_getSchedContext?_eq st rid hInv scId

/-- WS-RR RR8.11: the reply-link teardown writes a TCB and a Reply, so it writes
no scheduling context — RR8.5's projection of the reply path's own consume, whose
frame `consumeCallerReply_getSchedContext?_eq` states. -/
private theorem consumeReplyLink_getSchedContext?_eq (st : SystemState)
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

/-- WS-RR RR8.11: the endpoint sweep and the splice it composes write endpoints
and TCBs only. -/
private theorem removeFromAllEndpointQueues_getSchedContext?_eq (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (scId : SeLe4n.SchedContextId) :
    (removeFromAllEndpointQueues st tid).getSchedContext? scId
      = st.getSchedContext? scId := by
  refine getSchedContext?_of_kind_iff (fun sc => ?_)
  refine Iff.trans (removeFromAllEndpointQueues_nonEndpoint st tid
      (spliceOutMidQueueNode_preserves_objects_invExt st tid hInv)
      scId.toObjId (.schedContext sc) (fun e => fun hc => KernelObject.noConfusion hc)) ?_
  exact spliceOutMidQueueNode_nonTcb st tid hInv scId.toObjId (.schedContext sc)
    (fun t => fun hc => KernelObject.noConfusion hc)

/-- WS-RR RR8.11: the notification purge writes notifications only. -/
private theorem removeFromAllNotificationWaitLists_getSchedContext?_eq (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (scId : SeLe4n.SchedContextId) :
    (removeFromAllNotificationWaitLists st tid).getSchedContext? scId
      = st.getSchedContext? scId := by
  refine getSchedContext?_of_kind_iff (fun sc => ?_)
  exact removeFromAllNotificationWaitLists_nonNotification st tid hInv
    scId.toObjId (.schedContext sc) (fun n => fun hc => KernelObject.noConfusion hc)

/-- WS-RR RR8.11: the holder abort writes endpoints and TCBs, so it writes no
scheduling context — the `unwritten_kind` pair WS-OD OD3.2 built for the chain
frame, read at the SchedContext kind. -/
private theorem abortHolderPendingIpc_getSchedContext?_eq (st : SystemState)
    (holder : SeLe4n.ThreadId) (hInv : st.objects.invExt) (scId : SeLe4n.SchedContextId) :
    (Lifecycle.Suspend.abortHolderPendingIpc st holder).getSchedContext? scId
      = st.getSchedContext? scId := by
  refine getSchedContext?_of_kind_iff (fun sc => ?_)
  exact ⟨fun h => Lifecycle.Suspend.abortHolderPendingIpc_unwritten_kind_backward st holder hInv
      (fun o => ∃ sc0 : SeLe4n.Kernel.SchedContext, o = .schedContext sc0)
      (fun _ hc => nomatch hc.choose_spec) (fun _ hc => nomatch hc.choose_spec)
      scId.toObjId _ ⟨sc, rfl⟩ h,
    fun h => Lifecycle.Suspend.abortHolderPendingIpc_unwritten_kind_forward st holder hInv
      (fun o => ∃ sc0 : SeLe4n.Kernel.SchedContext, o = .schedContext sc0)
      (fun _ hc => nomatch hc.choose_spec) (fun _ hc => nomatch hc.choose_spec)
      scId.toObjId _ ⟨sc, rfl⟩ h⟩

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
    cases hRet : returnDonatedSchedContextResolved
        (Lifecycle.Suspend.abortHolderPendingIpc st holder) holder scId v with
    | error _ => rfl
    | ok st' =>
      obtain ⟨newOwner?, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
      rw [returnDonatedSchedContext_getSchedContext?_ne _ st' holder scId scId₀ v hne
          (Lifecycle.Suspend.abortHolderPendingIpc_preserves_objects_invExt st holder hInv)
          newOwner? hPop,
        abortHolderPendingIpc_getSchedContext?_eq st holder hInv scId₀]

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
        (removeFromAllNotificationWaitLists_preserves_objects_invExt st v hInv),
      removeFromAllNotificationWaitLists_getSchedContext?_eq st v hInv]
  | blockedOnReply ep rt =>
    have hR := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt
      st v tcbV hInv
    have hS := spliceThreadReplyFrameOut_preserves_objects_invExt
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV hR
    rw [consumeReplyLink_getSchedContext?_eq _ v tcbV
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

/-- WS-RR RR8.11: the shape every affinity frame below is proved in.  A step whose
TCB readings refine forward with the affinity preserved and whose post-state TCBs
all have pre-state TCBs at the same key frames `determineTargetCore` at that key —
the `Option.map` form, whose `none` case is the statement that the step
materialises no thread. -/
private theorem map_affinity_of_refines {sa sb : SystemState} {x : SeLe4n.ThreadId}
    (hFwd : ∀ t0, sa.getTcb? x = some t0 →
      ∃ t', sb.getTcb? x = some t' ∧ t'.cpuAffinity = t0.cpuAffinity)
    (hBwd : ∀ t', sb.getTcb? x = some t' → ∃ t0, sa.getTcb? x = some t0) :
    (sb.getTcb? x).map (·.cpuAffinity) = (sa.getTcb? x).map (·.cpuAffinity) := by
  cases hA : sa.getTcb? x with
  | none =>
    cases hB : sb.getTcb? x with
    | none => rfl
    | some t' =>
      obtain ⟨t0, h0⟩ := hBwd t' hB
      rw [hA] at h0
      exact absurd h0 (by simp)
  | some t0 =>
    obtain ⟨t', hB, hAff⟩ := hFwd t0 hA
    rw [hB]
    simp [hAff]

/-- WS-RR RR8.11: the mid-queue splice patches queue links only. -/
private theorem spliceOutMidQueueNode_affinity_frame (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    ((spliceOutMidQueueNode st tid).getTcb? x).map (·.cpuAffinity)
      = (st.getTcb? x).map (·.cpuAffinity) := by
  refine map_affinity_of_refines (fun t0 hT0 => ?_) (fun t' hT' => ?_)
  · obtain ⟨t', hL', hAff'⟩ := spliceOutMidQueueNode_tcb_lookup st tid x.toObjId t0 hInv
      ((SystemState.getTcb?_eq_some_iff st x t0).mp hT0)
    exact ⟨t', (SystemState.getTcb?_eq_some_iff _ x t').mpr hL', hAff'⟩
  · obtain ⟨t0, hL0, _⟩ := spliceOutMidQueueNode_tcb_backward st tid x.toObjId t' hInv
      ((SystemState.getTcb?_eq_some_iff _ x t').mp hT')
    exact ⟨t0, (SystemState.getTcb?_eq_some_iff st x t0).mpr hL0⟩

/-- WS-RR RR8.11: the endpoint sweep's fold writes endpoints only, so every TCB
reading is the splice's; the splice is the affinity frame above. -/
private theorem removeFromAllEndpointQueues_affinity_frame (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    ((removeFromAllEndpointQueues st tid).getTcb? x).map (·.cpuAffinity)
      = (st.getTcb? x).map (·.cpuAffinity) := by
  have hFold : ∀ t : TCB,
      (removeFromAllEndpointQueues st tid).getTcb? x = some t
        ↔ (spliceOutMidQueueNode st tid).getTcb? x = some t := fun t =>
    Iff.trans (SystemState.getTcb?_eq_some_iff _ x t)
      (Iff.trans (removeFromAllEndpointQueues_nonEndpoint st tid
          (spliceOutMidQueueNode_preserves_objects_invExt st tid hInv)
          x.toObjId (.tcb t) (fun e => fun hc => KernelObject.noConfusion hc))
        (SystemState.getTcb?_eq_some_iff _ x t).symm)
  have hEq : (removeFromAllEndpointQueues st tid).getTcb? x
      = (spliceOutMidQueueNode st tid).getTcb? x := by
    cases hA : (spliceOutMidQueueNode st tid).getTcb? x with
    | none =>
      cases hB : (removeFromAllEndpointQueues st tid).getTcb? x with
      | none => rfl
      | some t => exact absurd ((hFold t).mp hB) (by rw [hA]; simp)
    | some t => exact (hFold t).mpr hA
  rw [hEq]
  exact spliceOutMidQueueNode_affinity_frame st tid hInv x

/-- WS-RR RR8.11: the notification purge writes notifications only. -/
private theorem removeFromAllNotificationWaitLists_affinity_frame (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    ((removeFromAllNotificationWaitLists st tid).getTcb? x).map (·.cpuAffinity)
      = (st.getTcb? x).map (·.cpuAffinity) := by
  have hIff : ∀ t : TCB,
      (removeFromAllNotificationWaitLists st tid).getTcb? x = some t ↔ st.getTcb? x = some t :=
    fun t => Iff.trans (SystemState.getTcb?_eq_some_iff _ x t)
      (Iff.trans (removeFromAllNotificationWaitLists_nonNotification st tid hInv
          x.toObjId (.tcb t) (fun n => fun hc => KernelObject.noConfusion hc))
        (SystemState.getTcb?_eq_some_iff st x t).symm)
  have hEq : (removeFromAllNotificationWaitLists st tid).getTcb? x = st.getTcb? x := by
    cases hA : st.getTcb? x with
    | none =>
      cases hB : (removeFromAllNotificationWaitLists st tid).getTcb? x with
      | none => rfl
      | some t => exact absurd ((hIff t).mp hB) (by rw [hA]; simp)
    | some t => exact (hIff t).mpr hA
  rw [hEq]

/-- WS-RR RR8.11: the restore rewrites the victim's own TCB and writes nothing
where no TCB was. -/
private theorem restoreToReadyStaging_affinity_frame (st : SystemState)
    (tid : SeLe4n.ThreadId) (frame : Option Architecture.SyscallReturnFrame)
    (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    ((Lifecycle.Suspend.restoreToReadyStaging st tid frame).getTcb? x).map (·.cpuAffinity)
      = (st.getTcb? x).map (·.cpuAffinity) := by
  cases hT : st.getTcb? tid with
  | none =>
    rw [Lifecycle.Suspend.restoreToReadyStaging_eq_self_of_getTcb?_none st tid frame hT]
  | some tcb =>
    by_cases hk : x = tid
    · subst hk
      have hPost : (Lifecycle.Suspend.restoreToReadyStaging st x frame).getTcb? x
          = some (restoredTcb tcb frame) := by
        rw [restoreToReadyStaging_eq]
        simp only [hT]
        exact (SystemState.getTcb?_eq_some_iff _ x _).mpr
          (SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self st.objects x.toObjId _ hInv)
      rw [hPost, hT]
      cases frame with
      | none => simp [restoredTcb]
      | some f => simp [restoredTcb, TCB.withReturnFrame]
    · have hPost : (Lifecycle.Suspend.restoreToReadyStaging st tid frame).getTcb? x
          = st.getTcb? x := by
        unfold SystemState.getTcb?
        rw [restoreToReadyStaging_objects_ne st tid frame x.toObjId hInv
          (fun hc => hk (SeLe4n.ThreadId.toObjId_injective x tid hc))]
      rw [hPost]

/-- WS-RR RR8.11: a store of one TCB at a key that already held a TCB with the same
`cpuAffinity` frames every thread's home core. -/
private theorem storeObject_tcb_affinity_frame {st st' : SystemState} {k : SeLe4n.ObjId}
    {t t' : TCB}
    (hInv : st.objects.invExt) (hPre : st.objects[k]? = some (.tcb t))
    (hAff : t'.cpuAffinity = t.cpuAffinity)
    (hStore : storeObject k (.tcb t') st = .ok ((), st')) (x : SeLe4n.ThreadId) :
    (st'.getTcb? x).map (·.cpuAffinity) = (st.getTcb? x).map (·.cpuAffinity) := by
  by_cases hk : x.toObjId = k
  · subst hk
    rw [show st'.getTcb? x = some t' from
        (SystemState.getTcb?_eq_some_iff _ x t').mpr
          (storeObject_objects_eq' st x.toObjId (.tcb t') ((), st') hInv hStore),
      show st.getTcb? x = some t from (SystemState.getTcb?_eq_some_iff st x t).mpr hPre]
    simp [hAff]
  · unfold SystemState.getTcb?
    rw [storeObject_objects_ne st st' k x.toObjId (.tcb t') hk hInv hStore]

/-- WS-RR RR8.11: the guarded endpoint-queue removal patches queue links only, in
**both** directions — the `FieldRefines` pair WS-OD OD1.4 built, whose backward half
is what says the removal materialises no thread. -/
private theorem endpointQueueRemove_affinity_frame {endpointId : SeLe4n.ObjId}
    {isReceiveQ : Bool} {tid : SeLe4n.ThreadId} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : endpointQueueRemove endpointId isReceiveQ tid st = .ok st') (x : SeLe4n.ThreadId) :
    (st'.getTcb? x).map (·.cpuAffinity) = (st.getTcb? x).map (·.cpuAffinity) := by
  refine map_affinity_of_refines (fun t0 hT0 => ?_) (fun t' hT' => ?_)
  · obtain ⟨ot', hL', hAff'⟩ := endpointQueueRemove_getTcb_upToAffinity endpointId isReceiveQ
      tid st st' hInv h x.toObjId t0
      (by rw [← RHTable_getElem?_eq_get?]; exact (SystemState.getTcb?_eq_some_iff st x t0).mp hT0)
    exact ⟨ot', (SystemState.getTcb?_eq_some_iff _ x ot').mpr
      (by rw [RHTable_getElem?_eq_get?]; exact hL'), hAff'.symm⟩
  · obtain ⟨ot, hL, _⟩ := endpointQueueRemove_getTcb_backward_upToField
      (fun t : TCB => t.cpuAffinity)
      (fun _ _ _ _ => rfl) endpointId isReceiveQ tid st st' hInv h x.toObjId t'
      ((SystemState.getTcb?_eq_some_iff _ x t').mp hT')
    exact ⟨ot, (SystemState.getTcb?_eq_some_iff st x ot).mpr hL⟩

/-- WS-RR RR8.11: the holder abort ends an outstanding send or call and moves no
thread's home core. -/
private theorem abortHolderPendingIpc_affinity_frame (st : SystemState)
    (holder : SeLe4n.ThreadId) (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    ((Lifecycle.Suspend.abortHolderPendingIpc st holder).getTcb? x).map (·.cpuAffinity)
      = (st.getTcb? x).map (·.cpuAffinity) := by
  have hArm : ∀ (epId : SeLe4n.ObjId),
      (((match abortPendingIpcOnEndpoint epId false holder st with
        | .ok s => s
        | .error _ => st : SystemState)).getTcb? x).map (fun t : TCB => t.cpuAffinity)
        = (st.getTcb? x).map (fun t : TCB => t.cpuAffinity) := by
    intro epId
    cases hA : abortPendingIpcOnEndpoint epId false holder st with
    | error _ => rfl
    | ok stA =>
      obtain ⟨st1, tcb1, hRem, hLook, hStore⟩ := abortPendingIpcOnEndpoint_shape hA
      have hInv1 := endpointQueueRemove_preserves_objects_invExt _ _ _ _ _ hInv hRem
      rw [storeObject_tcb_affinity_frame (hInv := hInv1)
            (hPre := lookupTcb_some_objects _ _ _ hLook) (hStore := hStore)
            (hAff := by simp [TCB.withReturnFrame]) (x := x),
        endpointQueueRemove_affinity_frame hInv hRem x]
  unfold Lifecycle.Suspend.abortHolderPendingIpc
  split
  · rfl
  · rename_i holderTcb _
    split
    · rename_i epId _; exact hArm epId
    · rename_i epId _; exact hArm epId
    · rfl

/-- WS-RR RR8.11: the reclaim moves no thread's home core — its abort prefix
patches queue links and blocking state, and the pop rebinds scheduling contexts
(`returnDonatedSchedContext_getTcb?_cpuAffinity_eq`). -/
private theorem returnDonationToCancelledCaller_affinity_frame (st : SystemState)
    (v : SeLe4n.ThreadId) (tcbV : TCB) (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    ((Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV).getTcb? x).map (·.cpuAffinity)
      = (st.getTcb? x).map (·.cpuAffinity) := by
  unfold Lifecycle.Suspend.returnDonationToCancelledCaller
  cases hD : Lifecycle.Suspend.cancelledCallerDonation? st v tcbV with
  | none => rfl
  | some p =>
    obtain ⟨scId, holder⟩ := p
    cases hT : st.getTcb? v with
    | none => rfl
    | some _ =>
      dsimp only
      cases hRet : returnDonatedSchedContextResolved
          (Lifecycle.Suspend.abortHolderPendingIpc st holder) holder scId v with
      | error _ => rfl
      | ok st' =>
        obtain ⟨newOwner?, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hRet
        rw [returnDonatedSchedContext_getTcb?_cpuAffinity_eq _ st' holder scId v
            (Lifecycle.Suspend.abortHolderPendingIpc_preserves_objects_invExt st holder hInv)
            newOwner? hPop x,
          abortHolderPendingIpc_affinity_frame st holder hInv x]

/-- WS-RR RR8.11: **the consume materialises no thread.**  The backward half the
tree lacked: its two stores are at keys their own lookups found occupied, so a TCB
the post-state holds had a TCB at the same key before. -/
private theorem consumeCallerReply_getTcb?_backward {st st' : SystemState}
    {caller : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} (hInv : st.objects.invExt)
    (hStep : SystemState.consumeCallerReply caller rid st = .ok ((), st'))
    (x : SeLe4n.ThreadId) (t' : TCB) (hT' : st'.getTcb? x = some t') :
    ∃ t0, st.getTcb? x = some t0 := by
  unfold SystemState.consumeCallerReply at hStep
  cases hCons : SystemState.consumeReply rid st with
  | error e => simp [hCons] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hCons] at hStep
    have hInv1 := SystemState.consumeReply_preserves_objects_invExt st st1 rid hInv hCons
    have hMid : ∀ (y : SeLe4n.ThreadId) (t : TCB), st1.getTcb? y = some t → st.getTcb? y = some t := by
      intro y t hy
      unfold SystemState.consumeReply at hCons
      cases hG : st.getReply? rid with
      | none => rw [hG] at hCons; cases hCons; exact hy
      | some r0 =>
        rw [hG] at hCons
        by_cases hk : y.toObjId = rid.toObjId
        · exfalso
          have hPost : st1.objects[y.toObjId]? = some (.reply r0.consumed) := by
            rw [hk]; exact storeObject_objects_eq' st _ _ _ hInv hCons
          rw [(SystemState.getTcb?_eq_some_iff st1 y t).mp hy] at hPost
          exact absurd hPost (by simp)
        · refine (SystemState.getTcb?_eq_some_iff st y t).mpr ?_
          rw [← storeObject_objects_ne st st1 rid.toObjId y.toObjId _ hk hInv hCons]
          exact (SystemState.getTcb?_eq_some_iff st1 y t).mp hy
    cases hT : st1.getTcb? caller with
    | none =>
      simp only [hT, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      rw [← hStep] at hT'
      exact ⟨t', hMid x t' hT'⟩
    | some tcb =>
      simp only [hT] at hStep
      by_cases hk : x.toObjId = caller.toObjId
      · refine ⟨tcb, hMid x tcb ?_⟩
        rw [show x = caller from SeLe4n.ThreadId.toObjId_injective x caller hk]
        exact hT
      · refine ⟨t', hMid x t' ?_⟩
        refine (SystemState.getTcb?_eq_some_iff st1 x t').mpr ?_
        rw [← storeObject_objects_ne st1 st' caller.toObjId x.toObjId _ hk hInv1 hStep]
        exact (SystemState.getTcb?_eq_some_iff st' x t').mp hT'

/-- WS-RR RR8.11: the reply-link teardown clears one TCB field and consumes one
Reply, so it moves no thread's home core. -/
private theorem consumeReplyLink_affinity_frame (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    ((Lifecycle.Suspend.consumeReplyLink st tid tcb).getTcb? x).map (·.cpuAffinity)
      = (st.getTcb? x).map (·.cpuAffinity) := by
  unfold Lifecycle.Suspend.consumeReplyLink
  cases hR : tcb.replyObject with
  | none => rfl
  | some rid =>
    have hStep := SystemState.consumeCallerReply_eq_link st tid rid
    refine map_affinity_of_refines (fun t0 hT0 => ?_)
      (fun t' hT' => consumeCallerReply_getTcb?_backward hInv hStep x t' hT')
    by_cases hk : x.toObjId = tid.toObjId
    · refine ⟨{ t0 with replyObject := none }, ?_, rfl⟩
      refine (SystemState.getTcb?_eq_some_iff _ x _).mpr ?_
      rw [hk]
      exact SystemState.consumeCallerReply_tcb_caller st _ tid rid hInv hStep t0
        (by rw [← hk]; exact (SystemState.getTcb?_eq_some_iff st x t0).mp hT0)
    · exact ⟨t0, (SystemState.getTcb?_eq_some_iff _ x t0).mpr
        (SystemState.consumeCallerReply_tcb_other st _ tid rid hInv hStep x.toObjId t0 hk
          ((SystemState.getTcb?_eq_some_iff st x t0).mp hT0)), rfl⟩

/-- **WS-RR RR8.11: the teardown moves no thread's home core.**  The composite of
the per-step frames above, stated in the `Option.map` form so its `none` case is
the statement that the teardown materialises no thread — which is what a reader of
`replenishQueueAffinityConsistentOnCore` needs, since a scheduling context's
`boundThread` is tied to no stored TCB by any invariant. -/
theorem cancelIpcBlocking_affinity_frame (st : SystemState) (v : SeLe4n.ThreadId)
    (tcbV : TCB) (hInv : st.objects.invExt) (x : SeLe4n.ThreadId) :
    ((Lifecycle.Suspend.cancelIpcBlocking st v tcbV).getTcb? x).map (·.cpuAffinity)
      = (st.getTcb? x).map (·.cpuAffinity) := by
  unfold Lifecycle.Suspend.cancelIpcBlocking Lifecycle.Suspend.restoreToReadyCancelled
  cases hIp : tcbV.ipcState with
  | ready => rfl
  | blockedOnSend _ =>
    rw [restoreToReadyStaging_affinity_frame _ v _
        (removeFromAllEndpointQueues_preserves_objects_invExt st v hInv) x,
      removeFromAllEndpointQueues_affinity_frame st v hInv x]
  | blockedOnReceive _ =>
    rw [restoreToReadyStaging_affinity_frame _ v _
        (removeFromAllEndpointQueues_preserves_objects_invExt st v hInv) x,
      removeFromAllEndpointQueues_affinity_frame st v hInv x]
  | blockedOnCall _ =>
    rw [restoreToReadyStaging_affinity_frame _ v _
        (removeFromAllEndpointQueues_preserves_objects_invExt st v hInv) x,
      removeFromAllEndpointQueues_affinity_frame st v hInv x]
  | blockedOnNotification _ =>
    rw [restoreToReadyStaging_affinity_frame _ v _
        (removeFromAllNotificationWaitLists_preserves_objects_invExt st v hInv) x,
      removeFromAllNotificationWaitLists_affinity_frame st v hInv x]
  | blockedOnReply ep rt =>
    have hR := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt
      st v tcbV hInv
    have hS := spliceThreadReplyFrameOut_preserves_objects_invExt
      (Lifecycle.Suspend.returnDonationToCancelledCaller st v tcbV) tcbV hR
    rw [consumeReplyLink_affinity_frame _ v tcbV
        (Lifecycle.Suspend.restoreToReadyStaging_invExt _ v _ hS) x,
      restoreToReadyStaging_affinity_frame _ v _ hS x,
      spliceThreadReplyFrameOut_getTcb?_eq _ tcbV hR x,
      returnDonationToCancelledCaller_affinity_frame st v tcbV hInv x]

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
  determineTargetCore_congr st _ x (cancelIpcBlocking_affinity_frame st victim tcb hInv x)

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
      (fun c => by rw [Lifecycle.Suspend.cancelIpcBlocking_scheduler_eq])
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
      (fun c => by rw [Lifecycle.Suspend.cancelIpcBlocking_scheduler_eq])
      (fun scId₀ hne => cancelIpcBlocking_getSchedContext?_ne st victim tcb hInv scId₀
        (fun s h hD' => by rw [hD] at hD'; cases hD'; exact hne))
      (fun tid => cancelIpcBlocking_determineTargetCore_eq st victim tcb hInv tid)
      hSc hBound rfl hCons

/-- WS-RR RR8.11: the holder wake is a run-queue insert, so it moves no
replenishment. -/
@[simp] theorem enqueueAbortedHolderOnCore_replenishQueueOnCore (st : SystemState)
    (c : CoreId) (tid : SeLe4n.ThreadId) (c' : CoreId) :
    (enqueueAbortedHolderOnCore st c tid).scheduler.replenishQueueOnCore c'
      = st.scheduler.replenishQueueOnCore c' := by
  unfold enqueueAbortedHolderOnCore
  split
  · rfl
  · split
    · rfl
    · rfl

/-- WS-RR RR8.11: ...and so does the wake that resolves it. -/
@[simp] theorem wakeAbortedDonationHolder_replenishQueueOnCore (stPre stPost : SystemState)
    (victim : SeLe4n.ThreadId) (tcb : TCB) (c : CoreId) :
    (wakeAbortedDonationHolder stPre stPost victim tcb).scheduler.replenishQueueOnCore c
      = stPost.scheduler.replenishQueueOnCore c := by
  unfold wakeAbortedDonationHolder
  split
  · rfl
  · exact enqueueAbortedHolderOnCore_replenishQueueOnCore _ _ _ c

/-- **WS-RR RR8.11: the cross-core cancellation composite establishes the SM5.H
replenish-affinity invariant.**

The lift adds nothing, for the same reason RR8.10's bundle lift adds no premise:
the two scheduler steps the composite performs over the migrated teardown — the
holder wake and the victim's placement removal — write run queues and current
slots, which the invariant does not read, and no object at all, so all three of its
readings are the migrated teardown's. -/
theorem cancelIpcBlockingOnCore_establishes_replenishQueueAffinityConsistent_smp
    (victim : SeLe4n.ThreadId) (tcb : TCB) (executingCore : CoreId) (st : SystemState)
    (hInv : st.objects.invExt)
    (hCons : replenishQueueAffinityConsistent_smp st) :
    replenishQueueAffinityConsistent_smp
      (cancelIpcBlockingOnCore victim tcb executingCore st).1 := by
  have hBase := cancelIpcBlockingMigrated_establishes_replenishQueueAffinityConsistent_smp
    victim tcb st hInv hCons
  rw [cancelIpcBlockingOnCore_state_eq]
  refine (replenishQueueAffinityConsistent_smp_congr (fun c => ?_) (fun scId₀ => ?_)
    (fun tid => ?_)).mpr hBase
  · rw [descheduleAtPlacement_replenishQueueOnCore,
      wakeAbortedDonationHolder_replenishQueueOnCore]
  · unfold SystemState.getSchedContext?
    rw [descheduleAtPlacement_preserves_objects, wakeAbortedDonationHolder_objects]
  · rw [descheduleAtPlacement_determineTargetCore,
      wakeAbortedDonationHolder_determineTargetCore]

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

end SeLe4n.Kernel
