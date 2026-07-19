-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.Defs
import SeLe4n.Kernel.IPC.Operations.Endpoint
import SeLe4n.Kernel.Scheduler.Operations.Selection
import SeLe4n.Kernel.Scheduler.Operations.PerCoreWake
import SeLe4n.Kernel.IPC.CrossCore.EndpointCall

/-!
# WS-SM SM6.D — Pointwise-lookup congruence for the IPC invariant surface

Every conjunct of `ipcInvariantFull` except the scheduler-reading
`passiveServerIdle` reads the system state **only** through `objects[·]?`
lookups.  This module makes that observation a reusable theorem family:

* **§1** — per-conjunct transports `X_of_getElem_eq`: two states whose
  object lookups agree pointwise satisfy each conjunct interchangeably,
  assembled into `ipcInvariantFull_of_getElem_eq` (all twenty conjuncts,
  the passive slice supplied for the target state).  Pointwise (rather
  than structural `objects`-equality) matters because the cross-core wake
  (`enqueueRunnableOnCore`) re-inserts the woken TCB with an identical
  value: every lookup is unchanged while the Robin-Hood array
  representation may differ.  (The first eight members were landed with
  SM6.A inside the staged `CrossCore/EndpointCallInvariant.lean`; they
  live here — production — so the SM6.D whole-bundle closures for every
  cross-core transition share one family.)

* **§2** — `OffSchedulerAgrees`: the state relation the cross-core
  transitions actually induce against their single-core counterparts —
  object lookups agree pointwise and **every** non-`scheduler` field is
  equal (the wake's re-insert is the only object write that differs, and
  it is lookup-invisible; the scheduler substitution `wakeThread` /
  `removeRunnableOnCore` vs `ensureRunnable` / `removeRunnable` is
  unconstrained by the relation).

* **§3** — the scheduler-substitution agreements: `ensureRunnable`,
  `removeRunnable`, `removeRunnableOnCore`, and the already-`.ready`
  `wakeThread` each relate a state to its scheduler-substituted image.

* **§4** — step congruences: the store-level transition steps
  (`storeObject`, `storeTcbIpcStateAndMessage`, `consumeReply`,
  `consumeCallerReply`) map `OffSchedulerAgrees`-related inputs to
  `OffSchedulerAgrees`-related outputs with aligned control flow — the
  lever that lets a cross-core transition's post-state ride the
  single-core whole-bundle theorem even when stores execute *after* the
  object-visible wake.

Axiom-clean: every theorem depends only on the standard foundational
axioms (`propext` / `Quot.sound` / `Classical.choice`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §0  Typed-getter congruences
-- ============================================================================

/-- Pointwise object-lookup agreement lifts to `getTcb?` agreement. -/
theorem getTcb?_congr_getElem {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (tid : SeLe4n.ThreadId) : s2.getTcb? tid = s1.getTcb? tid := by
  unfold SystemState.getTcb?; rw [hEq]

/-- Pointwise object-lookup agreement lifts to `getReply?` agreement. -/
theorem getReply?_congr_getElem {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (rid : SeLe4n.ReplyId) : s2.getReply? rid = s1.getReply? rid := by
  unfold SystemState.getReply?; rw [hEq]

/-- Pointwise object-lookup agreement lifts to `getSchedContext?` agreement. -/
theorem getSchedContext?_congr_getElem {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (scId : SeLe4n.SchedContextId) : s2.getSchedContext? scId = s1.getSchedContext? scId := by
  unfold SystemState.getSchedContext?; rw [hEq]

/-- Pointwise object-lookup agreement lifts to `getNotification?` agreement. -/
theorem getNotification?_congr_getElem {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (oid : SeLe4n.ObjId) : s2.getNotification? oid = s1.getNotification? oid := by
  unfold SystemState.getNotification?; rw [hEq]

/-- Pointwise object-lookup agreement lifts to `getEndpoint?` agreement. -/
theorem getEndpoint?_congr_getElem {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (oid : SeLe4n.ObjId) : s2.getEndpoint? oid = s1.getEndpoint? oid := by
  unfold SystemState.getEndpoint?; rw [hEq]

/-- Pointwise object-lookup agreement lifts to `lookupTcb` agreement. -/
theorem lookupTcb_congr_getElem {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (tid : SeLe4n.ThreadId) : lookupTcb s2 tid = lookupTcb s1 tid := by
  unfold lookupTcb; rw [hEq]

-- ============================================================================
-- §1  Per-conjunct pointwise-lookup transports
-- ============================================================================

/-- Pointwise-lookup transport of a `queueNext` reachability path. -/
theorem QueueNextPath_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?) {a b : SeLe4n.ThreadId}
    (hp : QueueNextPath s2 a b) : QueueNextPath s1 a b := by
  induction hp with
  | single x y tcbA hObj hNext => exact .single x y tcbA (by rw [← hEq]; exact hObj) hNext
  | cons x y z tcbA hObj hNext _ ih => exact .cons x y z tcbA (by rw [← hEq]; exact hObj) hNext ih

/-- Pointwise-lookup transport of TCB-queue chain acyclicity. -/
theorem tcbQueueChainAcyclic_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : tcbQueueChainAcyclic s1) : tcbQueueChainAcyclic s2 :=
  fun tid hp => h tid (QueueNextPath_of_getElem_eq hEq hp)

/-- Pointwise-lookup transport of doubly-linked TCB-queue link integrity. -/
theorem tcbQueueLinkIntegrity_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : tcbQueueLinkIntegrity s1) : tcbQueueLinkIntegrity s2 := by
  obtain ⟨hFwd, hRev⟩ := h
  refine ⟨fun a tcbA hA b hNext => ?_, fun b tcbB hB a hPrev => ?_⟩
  · rw [hEq] at hA
    obtain ⟨tcbB, hB, hPrev⟩ := hFwd a tcbA hA b hNext
    exact ⟨tcbB, by rw [hEq]; exact hB, hPrev⟩
  · rw [hEq] at hB
    obtain ⟨tcbA, hA, hNext⟩ := hRev b tcbB hB a hPrev
    exact ⟨tcbA, by rw [hEq]; exact hA, hNext⟩

/-- Pointwise-lookup transport of single-queue well-formedness. -/
theorem intrusiveQueueWellFormed_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?) {q : IntrusiveQueue}
    (h : intrusiveQueueWellFormed q s1) : intrusiveQueueWellFormed q s2 := by
  obtain ⟨hP1, hP2, hP3⟩ := h
  refine ⟨hP1, fun hd hHead => ?_, fun tl hTail => ?_⟩
  · obtain ⟨tcb, hObj, hPrev⟩ := hP2 hd hHead
    exact ⟨tcb, by rw [hEq]; exact hObj, hPrev⟩
  · obtain ⟨tcb, hObj, hNext⟩ := hP3 tl hTail
    exact ⟨tcb, by rw [hEq]; exact hObj, hNext⟩

/-- Pointwise-lookup transport of an endpoint's dual-queue well-formedness. -/
theorem dualQueueEndpointWellFormed_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?) {epId : SeLe4n.ObjId}
    (h : dualQueueEndpointWellFormed epId s1) : dualQueueEndpointWellFormed epId s2 := by
  unfold dualQueueEndpointWellFormed at h ⊢
  rw [hEq]
  revert h
  cases s1.objects[epId]? with
  | none => exact fun _ => trivial
  | some obj =>
    cases obj with
    | endpoint ep =>
      exact fun h => ⟨intrusiveQueueWellFormed_of_getElem_eq hEq h.1,
                      intrusiveQueueWellFormed_of_getElem_eq hEq h.2⟩
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ | schedContext _ | reply _ =>
      exact fun _ => trivial

/-- WS-SM SM6.A.1: the dual-queue system invariant is preserved by any state
change that leaves every object lookup intact.  Assembles the four sub-predicate
congruences above. -/
theorem dualQueueSystemInvariant_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : dualQueueSystemInvariant s1) : dualQueueSystemInvariant s2 := by
  obtain ⟨hEp, hLink, hAcyc⟩ := h
  refine ⟨fun epId ep hObj => ?_,
          tcbQueueLinkIntegrity_of_getElem_eq hEq hLink,
          tcbQueueChainAcyclic_of_getElem_eq hEq hAcyc⟩
  rw [hEq] at hObj
  exact dualQueueEndpointWellFormed_of_getElem_eq hEq (hEp epId ep hObj)

/-- Pointwise-lookup transport of pending-message boundedness. -/
theorem allPendingMessagesBounded_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : allPendingMessagesBounded s1) : allPendingMessagesBounded s2 := by
  intro tid tcb msg hObj hPend
  rw [hEq] at hObj
  exact h tid tcb msg hObj hPend

/-- Pointwise-lookup transport of badge well-formedness (notification + cap). -/
theorem badgeWellFormed_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : badgeWellFormed s1) : badgeWellFormed s2 := by
  obtain ⟨hNtfn, hCap⟩ := h
  refine ⟨fun oid ntfn badge hObj hBadge => ?_, fun oid cn slot cap badge hObj hLk hBadge => ?_⟩
  · rw [hEq] at hObj; exact hNtfn oid ntfn badge hObj hBadge
  · rw [hEq] at hObj; exact hCap oid cn slot cap badge hObj hLk hBadge

/-- SM6.D: pointwise-lookup transport of notification well-formedness. -/
theorem ipcInvariant_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : ipcInvariant s1) : ipcInvariant s2 := by
  intro oid ntfn hObj
  rw [hEq] at hObj
  exact h oid ntfn hObj

/-- SM6.D: pointwise-lookup transport of `waitingThreadsPendingMessageNone`. -/
theorem waitingThreadsPendingMessageNone_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : waitingThreadsPendingMessageNone s1) : waitingThreadsPendingMessageNone s2 := by
  intro tid tcb hObj
  rw [hEq] at hObj
  exact h tid tcb hObj

/-- SM6.D: pointwise-lookup transport of `endpointQueueNoDup`. -/
theorem endpointQueueNoDup_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : endpointQueueNoDup s1) : endpointQueueNoDup s2 := by
  intro oid ep hEp
  rw [hEq] at hEp
  obtain ⟨hSelf, hDisj⟩ := h oid ep hEp
  refine ⟨fun tid tcb hTcb => ?_, hDisj⟩
  rw [hEq] at hTcb
  exact hSelf tid tcb hTcb

/-- SM6.D: pointwise-lookup transport of `ipcStateQueueMembershipConsistent`. -/
theorem ipcStateQueueMembershipConsistent_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : ipcStateQueueMembershipConsistent s1) : ipcStateQueueMembershipConsistent s2 := by
  intro tid tcb hTcb
  rw [hEq] at hTcb
  have hG := h tid tcb hTcb
  cases hIpc : tcb.ipcState with
  | blockedOnSend epId =>
      simp only [hIpc] at hG
      obtain ⟨ep, hEp, hReach⟩ := hG
      refine ⟨ep, by rw [hEq]; exact hEp, ?_⟩
      rcases hReach with hHead | ⟨prev, prevTcb, hPrev, hNext⟩
      · exact Or.inl hHead
      · exact Or.inr ⟨prev, prevTcb, by rw [hEq]; exact hPrev, hNext⟩
  | blockedOnReceive epId =>
      simp only [hIpc] at hG
      obtain ⟨ep, hEp, hReach⟩ := hG
      refine ⟨ep, by rw [hEq]; exact hEp, ?_⟩
      rcases hReach with hHead | ⟨prev, prevTcb, hPrev, hNext⟩
      · exact Or.inl hHead
      · exact Or.inr ⟨prev, prevTcb, by rw [hEq]; exact hPrev, hNext⟩
  | blockedOnCall epId =>
      simp only [hIpc] at hG
      obtain ⟨ep, hEp, hReach⟩ := hG
      refine ⟨ep, by rw [hEq]; exact hEp, ?_⟩
      rcases hReach with hHead | ⟨prev, prevTcb, hPrev, hNext⟩
      · exact Or.inl hHead
      · exact Or.inr ⟨prev, prevTcb, by rw [hEq]; exact hPrev, hNext⟩
  | ready => trivial
  | blockedOnNotification nid => trivial
  | blockedOnReply ep rt => trivial

/-- SM6.D: pointwise-lookup transport of `queueNextBlockingConsistent`. -/
theorem queueNextBlockingConsistent_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : queueNextBlockingConsistent s1) : queueNextBlockingConsistent s2 := by
  intro a b tcbA tcbB hA hB hNext
  rw [hEq] at hA hB
  exact h a b tcbA tcbB hA hB hNext

/-- SM6.D: pointwise-lookup transport of `queueHeadBlockedConsistent`. -/
theorem queueHeadBlockedConsistent_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : queueHeadBlockedConsistent s1) : queueHeadBlockedConsistent s2 := by
  intro epId ep hd tcb hEp hTcb
  rw [hEq] at hEp hTcb
  exact h epId ep hd tcb hEp hTcb

/-- SM6.D: pointwise-lookup transport of `blockedThreadTimeoutConsistent`. -/
theorem blockedThreadTimeoutConsistent_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : blockedThreadTimeoutConsistent s1) : blockedThreadTimeoutConsistent s2 := by
  intro tid tcb scId hTcb hBudget
  rw [hEq] at hTcb
  obtain ⟨⟨sc, hSc⟩, hBlk⟩ := h tid tcb scId hTcb hBudget
  exact ⟨⟨sc, by rw [hEq]; exact hSc⟩, hBlk⟩

/-- SM6.D: pointwise-lookup transport of `allTimeoutBudgetsNone`. -/
theorem allTimeoutBudgetsNone_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : allTimeoutBudgetsNone s1) : allTimeoutBudgetsNone s2 := by
  intro tid tcb hTcb
  rw [hEq] at hTcb
  exact h tid tcb hTcb

/-- SM6.D: pointwise-lookup transport of `donationChainAcyclic`. -/
theorem donationChainAcyclic_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : donationChainAcyclic s1) : donationChainAcyclic s2 := by
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 h1 h2 hB1 hB2
  rw [hEq] at h1 h2
  exact h tid1 tid2 tcb1 tcb2 scId1 scId2 h1 h2 hB1 hB2

/-- SM6.D: pointwise-lookup transport of `donationOwnerValid`. -/
theorem donationOwnerValid_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : donationOwnerValid s1) : donationOwnerValid s2 := by
  intro tid tcb scId owner hTcb hBind
  rw [hEq] at hTcb
  obtain ⟨⟨sc, hSc, hBound⟩, ⟨ownerTcb, hOwner, hUnbound, hReply⟩⟩ := h tid tcb scId owner hTcb hBind
  exact ⟨⟨sc, by rw [hEq]; exact hSc, hBound⟩,
    ⟨ownerTcb, by rw [hEq]; exact hOwner, hUnbound, hReply⟩⟩

/-- SM6.D: pointwise-lookup transport of `donationBudgetTransfer`. -/
theorem donationBudgetTransfer_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : donationBudgetTransfer s1) : donationBudgetTransfer s2 := by
  intro tid1 tid2 tcb1 tcb2 scId h1 h2 hNe hS1 hS2
  rw [hEq] at h1 h2
  exact h tid1 tid2 tcb1 tcb2 scId h1 h2 hNe hS1 hS2

/-- SM6.D: pointwise-lookup transport of `blockedOnReplyHasTarget`. -/
theorem blockedOnReplyHasTarget_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : blockedOnReplyHasTarget s1) : blockedOnReplyHasTarget s2 := by
  intro tid tcb endpointId replyTarget hTcb hIpc
  rw [hEq] at hTcb
  exact h tid tcb endpointId replyTarget hTcb hIpc

/-- SM6.D: pointwise-lookup transport of `replyCallerLinkageReciprocal`. -/
theorem replyCallerLinkageReciprocal_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : replyCallerLinkageReciprocal s1) : replyCallerLinkageReciprocal s2 := by
  refine ⟨fun tid tcb rid hTcb hRep => ?_, fun rid r tid hRep hCaller => ?_⟩
  · rw [hEq] at hTcb
    obtain ⟨r, hR, hBack⟩ := h.1 tid tcb rid hTcb hRep
    exact ⟨r, by rw [hEq]; exact hR, hBack⟩
  · rw [hEq] at hRep
    obtain ⟨tcb, hTcb, hFwd, hBlk⟩ := h.2 rid r tid hRep hCaller
    exact ⟨tcb, by rw [hEq]; exact hTcb, hFwd, hBlk⟩

/-- SM6.D: pointwise-lookup transport of `blockedOnReplyHasReplyObject`. -/
theorem blockedOnReplyHasReplyObject_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : blockedOnReplyHasReplyObject s1) : blockedOnReplyHasReplyObject s2 := by
  intro tid tcb ep rt hTcb hIpc
  rw [hEq] at hTcb
  exact h tid tcb ep rt hTcb hIpc

/-- SM6.D: pointwise-lookup transport of `replyCallerLinkage`. -/
theorem replyCallerLinkage_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : replyCallerLinkage s1) : replyCallerLinkage s2 :=
  ⟨replyCallerLinkageReciprocal_of_getElem_eq hEq h.1,
   blockedOnReplyHasReplyObject_of_getElem_eq hEq h.2⟩

/-- SM6.D: pointwise-lookup transport of `pendingReceiveReplyWellFormed`. -/
theorem pendingReceiveReplyWellFormed_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : pendingReceiveReplyWellFormed s1) : pendingReceiveReplyWellFormed s2 := by
  refine ⟨fun tid tcb rid hTcb hStash => ?_,
          fun tid₁ tid₂ tcb₁ tcb₂ rid h1 h2 hS1 hS2 => ?_⟩
  · rw [getTcb?_congr_getElem hEq] at hTcb
    obtain ⟨hRecv, ⟨r, hR, hFree⟩⟩ := h.1 tid tcb rid hTcb hStash
    exact ⟨hRecv, ⟨r, by rw [getReply?_congr_getElem hEq]; exact hR, hFree⟩⟩
  · rw [getTcb?_congr_getElem hEq] at h1 h2
    exact h.2 tid₁ tid₂ tcb₁ tcb₂ rid h1 h2 hS1 hS2

/-- SM6.D: pointwise-lookup transport of `donationOwnerUnique`. -/
theorem donationOwnerUnique_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : donationOwnerUnique s1) : donationOwnerUnique s2 := by
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 h2 hB1 hB2
  rw [hEq] at h1 h2
  exact h tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 h2 hB1 hB2

/-- SM6.D: pointwise-lookup transport of `endpointQueueTailBlockedConsistent`. -/
theorem endpointQueueTailBlockedConsistent_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : endpointQueueTailBlockedConsistent s1) : endpointQueueTailBlockedConsistent s2 := by
  intro epId ep tl tcb hEp hTcb
  rw [hEq] at hEp hTcb
  exact h epId ep tl tcb hEp hTcb

/-- SM6.D: pointwise-lookup transport of `queueNextTargetBlocked`. -/
theorem queueNextTargetBlocked_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : queueNextTargetBlocked s1) : queueNextTargetBlocked s2 := by
  intro a b tcbA tcbB hA hB hNext
  rw [hEq] at hA hB
  exact h a b tcbA tcbB hA hB hNext

/-- SM6.D: pointwise-lookup transport of `notificationWaiterConsistent`. -/
theorem notificationWaiterConsistent_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : notificationWaiterConsistent s1) : notificationWaiterConsistent s2 := by
  intro oid ntfn tid hNtfn hMem
  rw [hEq] at hNtfn
  obtain ⟨tcb, hTcb, hIpc⟩ := h oid ntfn tid hNtfn hMem
  exact ⟨tcb, by rw [hEq]; exact hTcb, hIpc⟩

/-- WS-SM SM6.D: **the whole-bundle pointwise transport** — two states whose
object lookups agree pointwise satisfy the nineteen object-reading conjuncts
of `ipcInvariantFull` interchangeably; the one scheduler-reading conjunct
(`passiveServerIdle`) is supplied for the target state.  This is the lever
that carries the single-core whole-bundle theorems across the cross-core
wake's lookup-invisible re-insert. -/
theorem ipcInvariantFull_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (hPsi2 : passiveServerIdle s2)
    (h : ipcInvariantFull s1) : ipcInvariantFull s2 :=
  ⟨ipcInvariant_of_getElem_eq hEq h.ipcInvariant,
   dualQueueSystemInvariant_of_getElem_eq hEq h.dualQueueSystemInvariant,
   allPendingMessagesBounded_of_getElem_eq hEq h.allPendingMessagesBounded,
   badgeWellFormed_of_getElem_eq hEq h.badgeWellFormed,
   waitingThreadsPendingMessageNone_of_getElem_eq hEq h.waitingThreadsPendingMessageNone,
   endpointQueueNoDup_of_getElem_eq hEq h.endpointQueueNoDup,
   ipcStateQueueMembershipConsistent_of_getElem_eq hEq h.ipcStateQueueMembershipConsistent,
   queueNextBlockingConsistent_of_getElem_eq hEq h.queueNextBlockingConsistent,
   queueHeadBlockedConsistent_of_getElem_eq hEq h.queueHeadBlockedConsistent,
   blockedThreadTimeoutConsistent_of_getElem_eq hEq h.blockedThreadTimeoutConsistent,
   donationChainAcyclic_of_getElem_eq hEq h.donationChainAcyclic,
   donationOwnerValid_of_getElem_eq hEq h.donationOwnerValid,
   hPsi2,
   donationBudgetTransfer_of_getElem_eq hEq h.donationBudgetTransfer,
   blockedOnReplyHasTarget_of_getElem_eq hEq h.blockedOnReplyHasTarget,
   replyCallerLinkage_of_getElem_eq hEq h.replyCallerLinkage,
   pendingReceiveReplyWellFormed_of_getElem_eq hEq h.pendingReceiveReplyWellFormed,
   donationOwnerUnique_of_getElem_eq hEq h.donationOwnerUnique,
   endpointQueueTailBlockedConsistent_of_getElem_eq hEq h.endpointQueueTailBlockedConsistent,
   queueNextTargetBlocked_of_getElem_eq hEq h.queueNextTargetBlocked⟩

-- ============================================================================
-- §2  The off-scheduler agreement relation
-- ============================================================================

/-- WS-SM SM6.D: the state relation a cross-core transition induces against
its single-core counterpart — object lookups agree **pointwise** and every
non-`scheduler` field is **equal**; the `scheduler` field is unconstrained.
The cross-core substitutions (`wakeThread` / `removeRunnableOnCore` for
`ensureRunnable` / `removeRunnable`) differ from their single-core
counterparts only in scheduler placement plus the wake's lookup-invisible
identical-value TCB re-insert, so the two spines stay in this relation at
every step.

Field-wise (rather than a record-update encoding) so each step-congruence
proof discharges per field; if `SystemState` gains a field, this structure
must gain the matching clause — the §4 step congruences will fail to
elaborate otherwise, which is the intended tripwire. -/
structure OffSchedulerAgrees (s1 s2 : SystemState) : Prop where
  objects : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?
  machine : s2.machine = s1.machine
  objectIndex : s2.objectIndex = s1.objectIndex
  objectIndexSet : s2.objectIndexSet = s1.objectIndexSet
  services : s2.services = s1.services
  irqHandlers : s2.irqHandlers = s1.irqHandlers
  lifecycle : s2.lifecycle = s1.lifecycle
  asidTable : s2.asidTable = s1.asidTable
  interfaceRegistry : s2.interfaceRegistry = s1.interfaceRegistry
  serviceRegistry : s2.serviceRegistry = s1.serviceRegistry
  cdt : s2.cdt = s1.cdt
  cdtSlotNode : s2.cdtSlotNode = s1.cdtSlotNode
  cdtNodeSlot : s2.cdtNodeSlot = s1.cdtNodeSlot
  cdtNextNode : s2.cdtNextNode = s1.cdtNextNode
  scThreadIndex : s2.scThreadIndex = s1.scThreadIndex
  tlb : s2.tlb = s1.tlb
  objStoreLock : s2.objStoreLock = s1.objStoreLock
  perCoreTlb : s2.perCoreTlb = s1.perCoreTlb

namespace OffSchedulerAgrees

/-- Reflexivity. -/
theorem refl (st : SystemState) : OffSchedulerAgrees st st :=
  ⟨fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Symmetry. -/
theorem symm {s1 s2 : SystemState} (h : OffSchedulerAgrees s1 s2) :
    OffSchedulerAgrees s2 s1 :=
  ⟨fun oid => (h.objects oid).symm, h.machine.symm, h.objectIndex.symm,
   h.objectIndexSet.symm, h.services.symm, h.irqHandlers.symm, h.lifecycle.symm,
   h.asidTable.symm, h.interfaceRegistry.symm, h.serviceRegistry.symm, h.cdt.symm,
   h.cdtSlotNode.symm, h.cdtNodeSlot.symm, h.cdtNextNode.symm, h.scThreadIndex.symm,
   h.tlb.symm, h.objStoreLock.symm, h.perCoreTlb.symm⟩

/-- Transitivity. -/
theorem trans {s1 s2 s3 : SystemState}
    (h12 : OffSchedulerAgrees s1 s2) (h23 : OffSchedulerAgrees s2 s3) :
    OffSchedulerAgrees s1 s3 :=
  ⟨fun oid => (h23.objects oid).trans (h12.objects oid), h23.machine.trans h12.machine,
   h23.objectIndex.trans h12.objectIndex, h23.objectIndexSet.trans h12.objectIndexSet,
   h23.services.trans h12.services, h23.irqHandlers.trans h12.irqHandlers,
   h23.lifecycle.trans h12.lifecycle, h23.asidTable.trans h12.asidTable,
   h23.interfaceRegistry.trans h12.interfaceRegistry,
   h23.serviceRegistry.trans h12.serviceRegistry, h23.cdt.trans h12.cdt,
   h23.cdtSlotNode.trans h12.cdtSlotNode, h23.cdtNodeSlot.trans h12.cdtNodeSlot,
   h23.cdtNextNode.trans h12.cdtNextNode, h23.scThreadIndex.trans h12.scThreadIndex,
   h23.tlb.trans h12.tlb, h23.objStoreLock.trans h12.objStoreLock,
   h23.perCoreTlb.trans h12.perCoreTlb⟩

end OffSchedulerAgrees

-- ============================================================================
-- §3  Scheduler-substitution agreements
-- ============================================================================

/-- SM6.D: a scheduler-only record update agrees with its base state
off-scheduler. -/
theorem offSchedulerAgrees_scheduler_update (st : SystemState) (σ : SchedulerState) :
    OffSchedulerAgrees st { st with scheduler := σ } :=
  ⟨fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- SM6.D: `ensureRunnable` (the single-core boot enqueue) agrees with its
input off-scheduler. -/
theorem ensureRunnable_offSchedulerAgrees (st : SystemState) (tid : SeLe4n.ThreadId) :
    OffSchedulerAgrees st (ensureRunnable st tid) := by
  unfold ensureRunnable
  split
  · exact OffSchedulerAgrees.refl st
  · split
    · exact offSchedulerAgrees_scheduler_update st _
    · exact OffSchedulerAgrees.refl st

/-- SM6.D: `removeRunnable` (the single-core boot dequeue) agrees with its
input off-scheduler. -/
theorem removeRunnable_offSchedulerAgrees (st : SystemState) (tid : SeLe4n.ThreadId) :
    OffSchedulerAgrees st (removeRunnable st tid) :=
  offSchedulerAgrees_scheduler_update st _

/-- SM6.D: `removeRunnableOnCore` (the per-core dequeue) agrees with its
input off-scheduler. -/
theorem removeRunnableOnCore_offSchedulerAgrees (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    OffSchedulerAgrees st (removeRunnableOnCore st tid c) :=
  offSchedulerAgrees_scheduler_update st _

/-- SM6.D: `enqueueRunnableOnCore` of an already-`.ready` thread agrees with
its input off-scheduler — the only object it writes is the woken TCB with
`ipcState := .ready`, an identical-value (lookup-invisible) re-insert; every
other field is untouched. -/
theorem enqueueRunnableOnCore_offSchedulerAgrees_of_ready
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hReady : tcb.ipcState = .ready)
    (hInv : st.objects.invExt) :
    OffSchedulerAgrees st (enqueueRunnableOnCore st c tid) := by
  refine ⟨fun oid => enqueueRunnableOnCore_objects_getElem_eq_of_ready st c tid tcb hTcb hReady hInv oid,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [enqueueRunnableOnCore, hTcb]
  all_goals split <;> rfl

/-- SM6.D: the cross-core `wakeThread` of an already-`.ready` thread agrees
with its input off-scheduler. -/
theorem wakeThread_offSchedulerAgrees_of_ready
    (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hReady : tcb.ipcState = .ready)
    (hInv : st.objects.invExt) :
    OffSchedulerAgrees st (wakeThread st tid ec).1 := by
  rw [wakeThread_state_eq_enqueue]
  exact enqueueRunnableOnCore_offSchedulerAgrees_of_ready st _ tid tcb hTcb hReady hInv

-- ============================================================================
-- §4  Step congruences
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- SM6.D step congruence: `storeObject` maps off-scheduler-agreeing inputs to
off-scheduler-agreeing outputs (it is total; control-free). -/
theorem storeObject_offSchedulerAgrees {s1 s2 r1 r2 : SystemState}
    (id : SeLe4n.ObjId) (obj : KernelObject)
    (hRel : OffSchedulerAgrees s1 s2)
    (hInv1 : s1.objects.invExt) (hInv2 : s2.objects.invExt)
    (h1 : storeObject id obj s1 = .ok ((), r1))
    (h2 : storeObject id obj s2 = .ok ((), r2)) :
    OffSchedulerAgrees r1 r2 := by
  have hObjEq : ∀ oid : SeLe4n.ObjId, r2.objects[oid]? = r1.objects[oid]? := by
    intro oid
    by_cases hEq : oid = id
    · rw [hEq, storeObject_objects_eq s2 r2 id obj hInv2 h2,
          storeObject_objects_eq s1 r1 id obj hInv1 h1]
    · rw [storeObject_objects_ne s2 r2 id oid obj hEq hInv2 h2,
          storeObject_objects_ne s1 r1 id oid obj hEq hInv1 h1]
      exact hRel.objects oid
  unfold storeObject at h1 h2
  cases h1
  cases h2
  refine ⟨hObjEq, hRel.machine, ?_, ?_, hRel.services, hRel.irqHandlers, ?_, ?_,
    hRel.interfaceRegistry, hRel.serviceRegistry, hRel.cdt, hRel.cdtSlotNode,
    hRel.cdtNodeSlot, hRel.cdtNextNode, hRel.scThreadIndex, hRel.tlb, hRel.objStoreLock,
    hRel.perCoreTlb⟩
  · simp only [hRel.objectIndexSet, hRel.objectIndex]
  · simp only [hRel.objectIndexSet]
  · simp only [hRel.lifecycle]
  · simp only [hRel.objects id, hRel.asidTable]

open SeLe4n.Model.SystemState in
/-- SM6.D step congruence: `storeTcbIpcStateAndMessage` succeeds on the
single-core-side state whenever it succeeds on the cross-core-side state,
with off-scheduler-agreeing outputs. -/
theorem storeTcbIpcStateAndMessage_offSchedulerAgrees {s1 s2 r2 : SystemState}
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hRel : OffSchedulerAgrees s1 s2)
    (hInv1 : s1.objects.invExt) (hInv2 : s2.objects.invExt)
    (h2 : storeTcbIpcStateAndMessage s2 tid ipc msg = .ok r2) :
    ∃ r1, storeTcbIpcStateAndMessage s1 tid ipc msg = .ok r1 ∧ OffSchedulerAgrees r1 r2 := by
  unfold storeTcbIpcStateAndMessage at h2 ⊢
  rw [lookupTcb_congr_getElem hRel.objects tid] at h2
  cases hL : lookupTcb s1 tid with
  | none => simp only [hL] at h2; cases h2
  | some tcb =>
    simp only [hL] at h2 ⊢
    cases hSO2 : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) s2 with
    | error e => simp only [hSO2] at h2; cases h2
    | ok p2 =>
      obtain ⟨⟨⟩, r2'⟩ := p2
      simp only [hSO2, Except.ok.injEq] at h2
      subst h2
      cases hSO1 : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) s1 with
      | error e => exact absurd hSO1 (by unfold storeObject; simp)
      | ok p1 =>
        obtain ⟨⟨⟩, r1'⟩ := p1
        exact ⟨r1', rfl, storeObject_offSchedulerAgrees _ _ hRel hInv1 hInv2 hSO1 hSO2⟩

open SeLe4n.Model.SystemState in
/-- SM6.D step congruence: `consumeReply` (total) maps off-scheduler-agreeing
inputs to off-scheduler-agreeing outputs. -/
theorem consumeReply_offSchedulerAgrees {s1 s2 r1 r2 : SystemState}
    (rid : SeLe4n.ReplyId)
    (hRel : OffSchedulerAgrees s1 s2)
    (hInv1 : s1.objects.invExt) (hInv2 : s2.objects.invExt)
    (h1 : consumeReply rid s1 = .ok ((), r1))
    (h2 : consumeReply rid s2 = .ok ((), r2)) :
    OffSchedulerAgrees r1 r2 := by
  unfold consumeReply at h1 h2
  rw [getReply?_congr_getElem hRel.objects rid] at h2
  cases hG : s1.getReply? rid with
  | none =>
      simp only [hG, Except.ok.injEq, Prod.mk.injEq, true_and] at h1 h2
      rw [← h1, ← h2]
      exact hRel
  | some r =>
      simp only [hG] at h1 h2
      exact storeObject_offSchedulerAgrees _ _ hRel hInv1 hInv2 h1 h2

open SeLe4n.Model.SystemState in
/-- SM6.D step congruence: `consumeCallerReply` (total) maps
off-scheduler-agreeing inputs to off-scheduler-agreeing outputs — the
reply-side `consumeReply` then the caller-side `replyObject` clear, both
lookup-determined. -/
theorem consumeCallerReply_offSchedulerAgrees {s1 s2 r1 r2 : SystemState}
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hRel : OffSchedulerAgrees s1 s2)
    (hInv1 : s1.objects.invExt) (hInv2 : s2.objects.invExt)
    (h1 : consumeCallerReply caller rid s1 = .ok ((), r1))
    (h2 : consumeCallerReply caller rid s2 = .ok ((), r2)) :
    OffSchedulerAgrees r1 r2 := by
  unfold SystemState.consumeCallerReply at h1 h2
  cases hC1 : consumeReply rid s1 with
  | error e => simp only [hC1] at h1; cases h1
  | ok p1 =>
    obtain ⟨⟨⟩, m1⟩ := p1
    cases hC2 : consumeReply rid s2 with
    | error e => simp only [hC2] at h2; cases h2
    | ok p2 =>
      obtain ⟨⟨⟩, m2⟩ := p2
      simp only [hC1] at h1
      simp only [hC2] at h2
      have hInvM1 : m1.objects.invExt := by
        unfold consumeReply at hC1
        cases hG : s1.getReply? rid with
        | none => rw [hG] at hC1; cases hC1; exact hInv1
        | some r =>
            rw [hG] at hC1
            exact storeObject_preserves_objects_invExt s1 m1 _ _ hInv1 hC1
      have hInvM2 : m2.objects.invExt := by
        unfold consumeReply at hC2
        cases hG : s2.getReply? rid with
        | none => rw [hG] at hC2; cases hC2; exact hInv2
        | some r =>
            rw [hG] at hC2
            exact storeObject_preserves_objects_invExt s2 m2 _ _ hInv2 hC2
      have hRelM : OffSchedulerAgrees m1 m2 := consumeReply_offSchedulerAgrees rid hRel hInv1 hInv2 hC1 hC2
      rw [getTcb?_congr_getElem hRelM.objects caller] at h2
      cases hG : m1.getTcb? caller with
      | none =>
          simp only [hG, Except.ok.injEq, Prod.mk.injEq, true_and] at h1 h2
          rw [← h1, ← h2]
          exact hRelM
      | some tcb =>
          simp only [hG] at h1 h2
          exact storeObject_offSchedulerAgrees _ _ hRelM hInvM1 hInvM2 h1 h2

end SeLe4n.Kernel
