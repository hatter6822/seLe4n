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

/-- SM6.D: pointwise-lookup transport of `blockedThreadsPendingMessageConsistent`. -/
theorem blockedThreadsPendingMessageConsistent_of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : blockedThreadsPendingMessageConsistent s1) : blockedThreadsPendingMessageConsistent s2 := by
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
   blockedThreadsPendingMessageConsistent_of_getElem_eq hEq h.blockedThreadsPendingMessageConsistent,
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

/-- WS-RR RR3.12: the relaxed donation-owner invariant is a pure object-store
property, so it transports across pointwise lookup agreement. -/
theorem donationOwnerValidExcept_of_getElem_eq {s1 s2 : SystemState}
    {woken : SeLe4n.ThreadId}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (h : donationOwnerValidExcept s1 woken) : donationOwnerValidExcept s2 woken := by
  intro tid tcb scId owner hTcb hBind
  rw [hEq] at hTcb
  obtain ⟨⟨sc, hSc, hBound⟩, ⟨ownerTcb, hOwner, hUnbound, hCase⟩⟩ :=
    h tid tcb scId owner hTcb hBind
  exact ⟨⟨sc, by rw [hEq]; exact hSc, hBound⟩,
    ⟨ownerTcb, by rw [hEq]; exact hOwner, hUnbound, hCase⟩⟩

/-- WS-RR RR3.12: the relaxed bundle transports across pointwise lookup agreement,
exactly as `ipcInvariantFull_of_getElem_eq` does for the full one — `passiveServerIdle`
is the single scheduler-reading conjunct and is supplied for the target state. -/
theorem ipcInvariantFullExceptDonationOwner_of_getElem_eq {s1 s2 : SystemState}
    {woken : SeLe4n.ThreadId}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?)
    (hPsi2 : passiveServerIdle s2)
    (h : ipcInvariantFullExceptDonationOwner s1 woken) :
    ipcInvariantFullExceptDonationOwner s2 woken :=
  ⟨ipcInvariant_of_getElem_eq hEq h.1,
   dualQueueSystemInvariant_of_getElem_eq hEq h.2.1,
   allPendingMessagesBounded_of_getElem_eq hEq h.2.2.1,
   badgeWellFormed_of_getElem_eq hEq h.2.2.2.1,
   blockedThreadsPendingMessageConsistent_of_getElem_eq hEq h.2.2.2.2.1,
   endpointQueueNoDup_of_getElem_eq hEq h.2.2.2.2.2.1,
   ipcStateQueueMembershipConsistent_of_getElem_eq hEq h.2.2.2.2.2.2.1,
   queueNextBlockingConsistent_of_getElem_eq hEq h.2.2.2.2.2.2.2.1,
   queueHeadBlockedConsistent_of_getElem_eq hEq h.2.2.2.2.2.2.2.2.1,
   blockedThreadTimeoutConsistent_of_getElem_eq hEq h.2.2.2.2.2.2.2.2.2.1,
   donationChainAcyclic_of_getElem_eq hEq h.2.2.2.2.2.2.2.2.2.2.1,
   donationOwnerValidExcept_of_getElem_eq hEq h.donationOwnerValidExcept,
   hPsi2,
   donationBudgetTransfer_of_getElem_eq hEq h.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   blockedOnReplyHasTarget_of_getElem_eq hEq h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   replyCallerLinkage_of_getElem_eq hEq h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   pendingReceiveReplyWellFormed_of_getElem_eq hEq h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   donationOwnerUnique_of_getElem_eq hEq h.donationOwnerUnique,
   endpointQueueTailBlockedConsistent_of_getElem_eq hEq
     h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   queueNextTargetBlocked_of_getElem_eq hEq h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

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
  perCoreICache : s2.perCoreICache = s1.perCoreICache
  pendingIcacheMaintenance :
    s2.pendingIcacheMaintenance = s1.pendingIcacheMaintenance
  /-- WS-SM SM8.C.8: the declassification audit trail agrees.  A scheduler-only
      substitution must not silently forge or drop a recorded downgrade. -/
  declassificationAuditLog :
    s2.declassificationAuditLog = s1.declassificationAuditLog
  /-- WS-SM SM9.A.1a: the declassification audit epoch agrees.  The trail's own
      clause says a scheduler-only substitution forges no downgrade; this one
      says it does not silently *renumber* the downgrades that are there —
      which, once drain exists, is a distinct way to falsify
      `declassificationAuditLog_timestamp_identifies_event`. -/
  declassificationAuditEpoch :
    s2.declassificationAuditEpoch = s1.declassificationAuditEpoch
  /-- WS-SM SM9.B.6: the declassification **refusal** ledger agrees.  The
      trail's clauses say a scheduler-only substitution neither forges nor
      renumbers an authorized downgrade; this one says it cannot forge, drop or
      re-order a recorded *attempt* — which, since the ledger's `version` is
      the token a monitor brackets its reads with, would also let a
      substitution hide an overwrite. -/
  declassificationRefusals :
    s2.declassificationRefusals = s1.declassificationRefusals
  /-- WS-SM SM9.D.5: the declassification **taint side table** agrees.

      The provenance analogue of the two clauses above, and load-bearing for the
      same reason: a scheduler substitution that silently re-keyed an object's
      taint would move a recorded downgrade's causal ancestry, so a chain the
      detector reports would name a different subject's history. -/
  declassificationTaint :
    s2.declassificationTaint = s1.declassificationTaint

namespace OffSchedulerAgrees

/-- Reflexivity. -/
theorem refl (st : SystemState) : OffSchedulerAgrees st st :=
  ⟨fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Symmetry. -/
theorem symm {s1 s2 : SystemState} (h : OffSchedulerAgrees s1 s2) :
    OffSchedulerAgrees s2 s1 :=
  ⟨fun oid => (h.objects oid).symm, h.machine.symm, h.objectIndex.symm,
   h.objectIndexSet.symm, h.services.symm, h.irqHandlers.symm, h.lifecycle.symm,
   h.asidTable.symm, h.interfaceRegistry.symm, h.serviceRegistry.symm, h.cdt.symm,
   h.cdtSlotNode.symm, h.cdtNodeSlot.symm, h.cdtNextNode.symm, h.scThreadIndex.symm,
   h.tlb.symm, h.objStoreLock.symm, h.perCoreTlb.symm, h.perCoreICache.symm,
   h.pendingIcacheMaintenance.symm, h.declassificationAuditLog.symm,
   h.declassificationAuditEpoch.symm, h.declassificationRefusals.symm,
   h.declassificationTaint.symm⟩

/-- Transitivity. -/
theorem trans {s1 s2 s3 : SystemState}
    (hFirst : OffSchedulerAgrees s1 s2) (hSecond : OffSchedulerAgrees s2 s3) :
    OffSchedulerAgrees s1 s3 :=
  ⟨fun oid => (hSecond.objects oid).trans (hFirst.objects oid), hSecond.machine.trans hFirst.machine,
   hSecond.objectIndex.trans hFirst.objectIndex, hSecond.objectIndexSet.trans hFirst.objectIndexSet,
   hSecond.services.trans hFirst.services, hSecond.irqHandlers.trans hFirst.irqHandlers,
   hSecond.lifecycle.trans hFirst.lifecycle, hSecond.asidTable.trans hFirst.asidTable,
   hSecond.interfaceRegistry.trans hFirst.interfaceRegistry,
   hSecond.serviceRegistry.trans hFirst.serviceRegistry, hSecond.cdt.trans hFirst.cdt,
   hSecond.cdtSlotNode.trans hFirst.cdtSlotNode, hSecond.cdtNodeSlot.trans hFirst.cdtNodeSlot,
   hSecond.cdtNextNode.trans hFirst.cdtNextNode, hSecond.scThreadIndex.trans hFirst.scThreadIndex,
   hSecond.tlb.trans hFirst.tlb, hSecond.objStoreLock.trans hFirst.objStoreLock,
   hSecond.perCoreTlb.trans hFirst.perCoreTlb, hSecond.perCoreICache.trans hFirst.perCoreICache,
   hSecond.pendingIcacheMaintenance.trans hFirst.pendingIcacheMaintenance,
   hSecond.declassificationAuditLog.trans hFirst.declassificationAuditLog,
   hSecond.declassificationAuditEpoch.trans hFirst.declassificationAuditEpoch,
   hSecond.declassificationRefusals.trans hFirst.declassificationRefusals,
   hSecond.declassificationTaint.trans hFirst.declassificationTaint⟩

end OffSchedulerAgrees

-- ============================================================================
-- §3  Scheduler-substitution agreements
-- ============================================================================

/-- SM6.D: a scheduler-only record update agrees with its base state
off-scheduler. -/
theorem offSchedulerAgrees_scheduler_update (st : SystemState) (σ : SchedulerState) :
    OffSchedulerAgrees st { st with scheduler := σ } :=
  ⟨fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    hRel.perCoreTlb, hRel.perCoreICache, hRel.pendingIcacheMaintenance,
    hRel.declassificationAuditLog, hRel.declassificationAuditEpoch,
    hRel.declassificationRefusals, hRel.declassificationTaint⟩
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

-- ============================================================================
-- §5  Read-view agreement: transports for transitions that rewrite only
--     objects the bundle never reads
-- ============================================================================

/-- Object kinds none of `ipcInvariantFull`'s queue, message, donation or reply
conjuncts read.  CNode *content* is read by exactly one clause —
`capabilityBadgesWellFormed` — which the master transport below therefore takes
as an explicit obligation for the target state; no conjunct reads a VSpaceRoot
or a piece of untyped memory at all.  `none` is deliberately **not** inert: a
transition that deletes or creates an object of a read kind must not slip
through this frame, so only a rewrite that keeps the oid on a non-read kind on
*both* sides qualifies. -/
def ipcReadInert : Option KernelObject → Prop
  | some (.cnode _) => True
  | some (.vspaceRoot _) => True
  | some (.untyped _) => True
  | _ => False

/-- Pointwise agreement on every object kind the IPC bundle's conjuncts read
through the store: TCBs, endpoints, notifications, replies and SchedContexts.
CNodes are deliberately absent — `capabilityBadgesWellFormed` is the one clause
that reads them, and the transitions this frame serves (capability writes,
page-table writes, untyped scrubs) exist precisely to rewrite them. -/
structure ipcReadViewAgreement (s1 s2 : SystemState) : Prop where
  tcb : ∀ (oid : SeLe4n.ObjId) (t : TCB),
    s2.objects[oid]? = some (.tcb t) ↔ s1.objects[oid]? = some (.tcb t)
  endpoint : ∀ (oid : SeLe4n.ObjId) (ep : Endpoint),
    s2.objects[oid]? = some (.endpoint ep) ↔ s1.objects[oid]? = some (.endpoint ep)
  /-- The notification clause is *content* agreement, not value agreement:
  every notification-reading conjunct reads `state`, `waitingThreads` and
  `pendingBadge` only, so a rewrite that moves `boundTCB` or the lock word —
  the `.tcbBindNotification` arms — stays inside the frame. -/
  notification : ∀ (oid : SeLe4n.ObjId) (ntfn : Notification),
    s2.objects[oid]? = some (.notification ntfn) →
    ∃ ntfn₀ : Notification, s1.objects[oid]? = some (.notification ntfn₀) ∧
      ntfn₀.state = ntfn.state ∧ ntfn₀.waitingThreads = ntfn.waitingThreads ∧
      ntfn₀.pendingBadge = ntfn.pendingBadge
  reply : ∀ (oid : SeLe4n.ObjId) (r : SeLe4n.Kernel.Reply),
    s2.objects[oid]? = some (.reply r) ↔ s1.objects[oid]? = some (.reply r)
  /-- The SchedContext clause is likewise *content* agreement, stated in the
  `s1 → s2` direction the transports consume: the bundle reads only an SC's
  existence and its `boundThread`, so budget, period, priority, deadline and
  domain rewrites — the `.schedContextConfigure` and priority arms — stay
  inside the frame. -/
  schedContext : ∀ (oid : SeLe4n.ObjId) (sc : SeLe4n.Kernel.SchedContext),
    s1.objects[oid]? = some (.schedContext sc) →
    ∃ sc' : SeLe4n.Kernel.SchedContext, s2.objects[oid]? = some (.schedContext sc') ∧
      sc'.boundThread = sc.boundThread

namespace ipcReadViewAgreement

/-- Full pointwise lookup agreement is read-view agreement. -/
theorem of_getElem_eq {s1 s2 : SystemState}
    (hEq : ∀ oid : SeLe4n.ObjId, s2.objects[oid]? = s1.objects[oid]?) :
    ipcReadViewAgreement s1 s2 :=
  ⟨fun oid _ => by rw [hEq oid], fun oid _ => by rw [hEq oid],
   fun oid ntfn hObj => ⟨ntfn, (hEq oid) ▸ hObj, rfl, rfl, rfl⟩,
   fun oid _ => by rw [hEq oid],
   fun oid sc hSc => ⟨sc, by rw [hEq oid]; exact hSc, rfl⟩⟩

/-- The frame the capability, VSpace and untyped-scrub transitions induce:
lookups agree except at rewritten oids, and every rewritten oid holds a kind
outside the read view in **both** states. -/
theorem of_inertWrites {s1 s2 : SystemState}
    (h : ∀ oid : SeLe4n.ObjId,
      s2.objects[oid]? = s1.objects[oid]? ∨
      (ipcReadInert s1.objects[oid]? ∧ ipcReadInert s2.objects[oid]?)) :
    ipcReadViewAgreement s1 s2 := by
  have step : ∀ (oid : SeLe4n.ObjId) (o : KernelObject), ¬ ipcReadInert (some o) →
      (s2.objects[oid]? = some o ↔ s1.objects[oid]? = some o) := by
    intro oid o hNotInert
    rcases h oid with hEq | ⟨h1, h2⟩
    · rw [hEq]
    · constructor
      · intro hx; rw [hx] at h2; exact absurd h2 hNotInert
      · intro hx; rw [hx] at h1; exact absurd h1 hNotInert
  exact ⟨fun oid t => step oid (.tcb t) (by simp [ipcReadInert]),
         fun oid ep => step oid (.endpoint ep) (by simp [ipcReadInert]),
         fun oid ntfn hObj =>
           ⟨ntfn, (step oid (.notification ntfn) (by simp [ipcReadInert])).mp hObj,
             rfl, rfl, rfl⟩,
         fun oid r => step oid (.reply r) (by simp [ipcReadInert]),
         fun oid sc hSc =>
           ⟨sc, (step oid (.schedContext sc) (by simp [ipcReadInert])).mpr hSc, rfl⟩⟩

/-- The single-oid instance: one rewritten slot, inert on both sides — the
shape of every CNode-slot write and every page-table update. -/
theorem of_single_inert_write {s1 s2 : SystemState} {key : SeLe4n.ObjId}
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ key → s2.objects[oid]? = s1.objects[oid]?)
    (h1 : ipcReadInert s1.objects[key]?) (h2 : ipcReadInert s2.objects[key]?) :
    ipcReadViewAgreement s1 s2 :=
  of_inertWrites fun oid => by
    by_cases hEq : oid = key
    · subst hEq; exact Or.inr ⟨h1, h2⟩
    · exact Or.inl (hNe oid hEq)

/-- A single notification rewrite preserving queue content — `state`,
`waitingThreads`, `pendingBadge`; `boundTCB` and the lock word are free —
is read-view agreement.  The `.tcbBindNotification` /
`.tcbUnbindNotification` arms' notification store is exactly this shape. -/
theorem of_notification_content_write {s1 s2 : SystemState} {key : SeLe4n.ObjId}
    {ntfn ntfn' : Notification}
    (hPre : s1.objects[key]? = some (.notification ntfn))
    (hAt : s2.objects[key]? = some (.notification ntfn'))
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ key → s2.objects[oid]? = s1.objects[oid]?)
    (hState : ntfn'.state = ntfn.state)
    (hWaiters : ntfn'.waitingThreads = ntfn.waitingThreads)
    (hBadge : ntfn'.pendingBadge = ntfn.pendingBadge) :
    ipcReadViewAgreement s1 s2 := by
  have step : ∀ (oid : SeLe4n.ObjId) (o : KernelObject),
      (∀ n : Notification, o ≠ .notification n) →
      (s2.objects[oid]? = some o ↔ s1.objects[oid]? = some o) := by
    intro oid o hNo
    by_cases hK : oid = key
    · subst hK
      rw [hPre, hAt]
      constructor
      · intro hx
        exact absurd (Option.some.inj hx).symm (hNo ntfn')
      · intro hx
        exact absurd (Option.some.inj hx).symm (hNo ntfn)
    · rw [hNe oid hK]
  refine ⟨fun oid t => step oid (.tcb t) (fun n h => KernelObject.noConfusion h),
          fun oid ep => step oid (.endpoint ep) (fun n h => KernelObject.noConfusion h),
          fun oid n hObj => ?_,
          fun oid r => step oid (.reply r) (fun n h => KernelObject.noConfusion h),
          fun oid sc hSc =>
            ⟨sc, (step oid (.schedContext sc)
              (fun n h => KernelObject.noConfusion h)).mpr hSc, rfl⟩⟩
  by_cases hK : oid = key
  · subst hK
    rw [hAt] at hObj
    obtain rfl : ntfn' = n := by
      simpa only [Option.some.injEq, KernelObject.notification.injEq] using hObj
    exact ⟨ntfn, hPre, hState.symm, hWaiters.symm, hBadge.symm⟩
  · rw [hNe oid hK] at hObj
    exact ⟨n, hObj, rfl, rfl, rfl⟩

/-- A single SchedContext rewrite preserving `boundThread` — budget, period,
priority, deadline, domain and the lock word are free — is read-view
agreement.  The `.schedContextConfigure` arm's store and the priority arms'
SC-priority update are exactly this shape. -/
theorem of_schedContext_content_write {s1 s2 : SystemState} {key : SeLe4n.ObjId}
    {sc sc' : SeLe4n.Kernel.SchedContext}
    (hPre : s1.objects[key]? = some (.schedContext sc))
    (hAt : s2.objects[key]? = some (.schedContext sc'))
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ key → s2.objects[oid]? = s1.objects[oid]?)
    (hBound : sc'.boundThread = sc.boundThread) :
    ipcReadViewAgreement s1 s2 := by
  have step : ∀ (oid : SeLe4n.ObjId) (o : KernelObject),
      (∀ x : SeLe4n.Kernel.SchedContext, o ≠ .schedContext x) →
      (s2.objects[oid]? = some o ↔ s1.objects[oid]? = some o) := by
    intro oid o hNo
    by_cases hK : oid = key
    · subst hK
      rw [hPre, hAt]
      constructor
      · intro hx
        exact absurd (Option.some.inj hx).symm (hNo sc')
      · intro hx
        exact absurd (Option.some.inj hx).symm (hNo sc)
    · rw [hNe oid hK]
  refine ⟨fun oid t => step oid (.tcb t) (fun x h => KernelObject.noConfusion h),
          fun oid ep => step oid (.endpoint ep) (fun x h => KernelObject.noConfusion h),
          fun oid n hObj =>
            ⟨n, (step oid (.notification n)
              (fun x h => KernelObject.noConfusion h)).mp hObj, rfl, rfl, rfl⟩,
          fun oid r => step oid (.reply r) (fun x h => KernelObject.noConfusion h),
          fun oid x hSc => ?_⟩
  by_cases hK : oid = key
  · subst hK
    rw [hPre] at hSc
    obtain rfl : sc = x := by
      simpa only [Option.some.injEq, KernelObject.schedContext.injEq] using hSc
    exact ⟨sc', hAt, hBound⟩
  · rw [← hNe oid hK] at hSc
    exact ⟨x, hSc, rfl⟩

/-- Read-view agreement composes. -/
theorem trans {s1 s2 s3 : SystemState}
    (hFore : ipcReadViewAgreement s1 s2) (hAft : ipcReadViewAgreement s2 s3) :
    ipcReadViewAgreement s1 s3 :=
  ⟨fun oid t => (hAft.tcb oid t).trans (hFore.tcb oid t),
   fun oid ep => (hAft.endpoint oid ep).trans (hFore.endpoint oid ep),
   fun oid n h3 => by
     obtain ⟨n2, h2, hS2, hW2, hB2⟩ := hAft.notification oid n h3
     obtain ⟨n1, h1, hS1, hW1, hB1⟩ := hFore.notification oid n2 h2
     exact ⟨n1, h1, hS1.trans hS2, hW1.trans hW2, hB1.trans hB2⟩,
   fun oid r => (hAft.reply oid r).trans (hFore.reply oid r),
   fun oid sc h1 => by
     obtain ⟨sc2, h2, hB2⟩ := hFore.schedContext oid sc h1
     obtain ⟨sc3, h3, hB3⟩ := hAft.schedContext oid sc2 h2
     exact ⟨sc3, h3, hB3.trans hB2⟩⟩

/-- The typed-getter form of the TCB clause. -/
theorem getTcb?_iff {s1 s2 : SystemState} (hView : ipcReadViewAgreement s1 s2)
    (tid : SeLe4n.ThreadId) (t : TCB) :
    s2.getTcb? tid = some t ↔ s1.getTcb? tid = some t :=
  (SystemState.getTcb?_eq_some_iff s2 tid t).trans
    ((hView.tcb tid.toObjId t).trans (SystemState.getTcb?_eq_some_iff s1 tid t).symm)

/-- The typed-getter form of the reply clause. -/
theorem getReply?_iff {s1 s2 : SystemState} (hView : ipcReadViewAgreement s1 s2)
    (rid : SeLe4n.ReplyId) (r : SeLe4n.Kernel.Reply) :
    s2.getReply? rid = some r ↔ s1.getReply? rid = some r :=
  (SystemState.getReply?_eq_some_iff s2 rid r).trans
    ((hView.reply rid.toObjId r).trans (SystemState.getReply?_eq_some_iff s1 rid r).symm)

end ipcReadViewAgreement

/-- Read-view transport of a `queueNext` reachability path. -/
theorem QueueNextPath_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2) {a b : SeLe4n.ThreadId}
    (hp : QueueNextPath s2 a b) : QueueNextPath s1 a b := by
  induction hp with
  | single x y tcbA hObj hNext => exact .single x y tcbA ((hView.tcb _ _).mp hObj) hNext
  | cons x y z tcbA hObj hNext _ ih => exact .cons x y z tcbA ((hView.tcb _ _).mp hObj) hNext ih

/-- Read-view transport of TCB-queue chain acyclicity. -/
theorem tcbQueueChainAcyclic_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : tcbQueueChainAcyclic s1) : tcbQueueChainAcyclic s2 :=
  fun tid hp => h tid (QueueNextPath_of_readViewAgreement hView hp)

/-- Read-view transport of doubly-linked TCB-queue link integrity. -/
theorem tcbQueueLinkIntegrity_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : tcbQueueLinkIntegrity s1) : tcbQueueLinkIntegrity s2 := by
  obtain ⟨hFwd, hRev⟩ := h
  refine ⟨fun a tcbA hA b hNext => ?_, fun b tcbB hB a hPrev => ?_⟩
  · rw [hView.tcb] at hA
    obtain ⟨tcbB, hB, hPrev⟩ := hFwd a tcbA hA b hNext
    exact ⟨tcbB, (hView.tcb _ _).mpr hB, hPrev⟩
  · rw [hView.tcb] at hB
    obtain ⟨tcbA, hA, hNext⟩ := hRev b tcbB hB a hPrev
    exact ⟨tcbA, (hView.tcb _ _).mpr hA, hNext⟩

/-- Read-view transport of single-queue well-formedness. -/
theorem intrusiveQueueWellFormed_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2) {q : IntrusiveQueue}
    (h : intrusiveQueueWellFormed q s1) : intrusiveQueueWellFormed q s2 := by
  obtain ⟨hP1, hP2, hP3⟩ := h
  refine ⟨hP1, fun hd hHead => ?_, fun tl hTail => ?_⟩
  · obtain ⟨tcb, hObj, hPrev⟩ := hP2 hd hHead
    exact ⟨tcb, (hView.tcb _ _).mpr hObj, hPrev⟩
  · obtain ⟨tcb, hObj, hNext⟩ := hP3 tl hTail
    exact ⟨tcb, (hView.tcb _ _).mpr hObj, hNext⟩

/-- Read-view transport of an endpoint's dual-queue well-formedness. -/
theorem dualQueueEndpointWellFormed_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2) {epId : SeLe4n.ObjId}
    (h : dualQueueEndpointWellFormed epId s1) : dualQueueEndpointWellFormed epId s2 := by
  unfold dualQueueEndpointWellFormed at h ⊢
  cases hObj : s2.objects[epId]? with
  | none => trivial
  | some obj =>
    cases obj with
    | endpoint ep =>
      rw [(hView.endpoint _ _).mp hObj] at h
      exact ⟨intrusiveQueueWellFormed_of_readViewAgreement hView h.1,
             intrusiveQueueWellFormed_of_readViewAgreement hView h.2⟩
    | tcb _ | cnode _ | vspaceRoot _ | notification _ | untyped _ | schedContext _ | reply _ =>
      trivial

/-- Read-view transport of the dual-queue system invariant. -/
theorem dualQueueSystemInvariant_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : dualQueueSystemInvariant s1) : dualQueueSystemInvariant s2 := by
  obtain ⟨hEp, hLink, hAcyc⟩ := h
  refine ⟨fun epId ep hObj => ?_,
          tcbQueueLinkIntegrity_of_readViewAgreement hView hLink,
          tcbQueueChainAcyclic_of_readViewAgreement hView hAcyc⟩
  rw [hView.endpoint] at hObj
  exact dualQueueEndpointWellFormed_of_readViewAgreement hView (hEp epId ep hObj)

/-- Read-view transport of pending-message boundedness. -/
theorem allPendingMessagesBounded_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : allPendingMessagesBounded s1) : allPendingMessagesBounded s2 := by
  intro tid tcb msg hObj hPend
  rw [hView.tcb] at hObj
  exact h tid tcb msg hObj hPend

/-- Read-view transport of the generic in-flight-message family. -/
theorem pendingMessagesSatisfy_of_readViewAgreement {P : IpcMessage → Prop} {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : pendingMessagesSatisfy P s1) : pendingMessagesSatisfy P s2 := by
  intro tid tcb msg hObj hPend
  rw [hView.tcb] at hObj
  exact h tid tcb msg hObj hPend

/-- Read-view transport of the notification half of `badgeWellFormed`. -/
theorem notificationBadgesWellFormed_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : notificationBadgesWellFormed s1) : notificationBadgesWellFormed s2 := by
  intro oid ntfn badge hObj hBadge
  obtain ⟨ntfn₀, hL, _, _, hB⟩ := hView.notification oid ntfn hObj
  exact h oid ntfn₀ badge hL (hB.trans hBadge)

/-- Read-view transport of notification well-formedness. -/
theorem ipcInvariant_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : ipcInvariant s1) : ipcInvariant s2 := by
  intro oid ntfn hObj
  obtain ⟨ntfn₀, hL, hS, hW, hB⟩ := hView.notification oid ntfn hObj
  have h₀ := h oid ntfn₀ hL
  unfold notificationInvariant notificationQueueWellFormed at h₀ ⊢
  rw [← hS, ← hW, ← hB]
  exact h₀

/-- Read-view transport of `blockedThreadsPendingMessageConsistent`. -/
theorem blockedThreadsPendingMessageConsistent_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : blockedThreadsPendingMessageConsistent s1) :
    blockedThreadsPendingMessageConsistent s2 := by
  intro tid tcb hObj
  rw [hView.tcb] at hObj
  exact h tid tcb hObj

/-- Read-view transport of `endpointQueueNoDup`. -/
theorem endpointQueueNoDup_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : endpointQueueNoDup s1) : endpointQueueNoDup s2 := by
  intro oid ep hEp
  rw [hView.endpoint] at hEp
  obtain ⟨hSelf, hDisj⟩ := h oid ep hEp
  refine ⟨fun tid tcb hTcb => ?_, hDisj⟩
  rw [hView.tcb] at hTcb
  exact hSelf tid tcb hTcb

/-- Read-view transport of `ipcStateQueueMembershipConsistent`. -/
theorem ipcStateQueueMembershipConsistent_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : ipcStateQueueMembershipConsistent s1) : ipcStateQueueMembershipConsistent s2 := by
  intro tid tcb hTcb
  rw [hView.tcb] at hTcb
  have hG := h tid tcb hTcb
  cases hIpc : tcb.ipcState with
  | blockedOnSend epId =>
      simp only [hIpc] at hG
      obtain ⟨ep, hEp, hReach⟩ := hG
      refine ⟨ep, (hView.endpoint _ _).mpr hEp, ?_⟩
      rcases hReach with hHead | ⟨prev, prevTcb, hPrev, hNext⟩
      · exact Or.inl hHead
      · exact Or.inr ⟨prev, prevTcb, (hView.tcb _ _).mpr hPrev, hNext⟩
  | blockedOnReceive epId =>
      simp only [hIpc] at hG
      obtain ⟨ep, hEp, hReach⟩ := hG
      refine ⟨ep, (hView.endpoint _ _).mpr hEp, ?_⟩
      rcases hReach with hHead | ⟨prev, prevTcb, hPrev, hNext⟩
      · exact Or.inl hHead
      · exact Or.inr ⟨prev, prevTcb, (hView.tcb _ _).mpr hPrev, hNext⟩
  | blockedOnCall epId =>
      simp only [hIpc] at hG
      obtain ⟨ep, hEp, hReach⟩ := hG
      refine ⟨ep, (hView.endpoint _ _).mpr hEp, ?_⟩
      rcases hReach with hHead | ⟨prev, prevTcb, hPrev, hNext⟩
      · exact Or.inl hHead
      · exact Or.inr ⟨prev, prevTcb, (hView.tcb _ _).mpr hPrev, hNext⟩
  | ready => trivial
  | blockedOnNotification nid => trivial
  | blockedOnReply ep rt => trivial

/-- Read-view transport of `queueNextBlockingConsistent`. -/
theorem queueNextBlockingConsistent_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : queueNextBlockingConsistent s1) : queueNextBlockingConsistent s2 := by
  intro a b tcbA tcbB hA hB hNext
  rw [hView.tcb] at hA hB
  exact h a b tcbA tcbB hA hB hNext

/-- Read-view transport of `queueHeadBlockedConsistent`. -/
theorem queueHeadBlockedConsistent_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : queueHeadBlockedConsistent s1) : queueHeadBlockedConsistent s2 := by
  intro epId ep hd tcb hEp hTcb
  rw [hView.endpoint] at hEp
  rw [hView.tcb] at hTcb
  exact h epId ep hd tcb hEp hTcb

/-- Read-view transport of `blockedThreadTimeoutConsistent`. -/
theorem blockedThreadTimeoutConsistent_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : blockedThreadTimeoutConsistent s1) : blockedThreadTimeoutConsistent s2 := by
  intro tid tcb scId hTcb hBudget
  rw [hView.tcb] at hTcb
  obtain ⟨⟨sc, hSc⟩, hBlk⟩ := h tid tcb scId hTcb hBudget
  obtain ⟨sc', hSc', _⟩ := hView.schedContext _ sc hSc
  exact ⟨⟨sc', hSc'⟩, hBlk⟩

/-- Read-view transport of `allTimeoutBudgetsNone`. -/
theorem allTimeoutBudgetsNone_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : allTimeoutBudgetsNone s1) : allTimeoutBudgetsNone s2 := by
  intro tid tcb hTcb
  rw [hView.tcb] at hTcb
  exact h tid tcb hTcb

/-- Read-view transport of `donationChainAcyclic`. -/
theorem donationChainAcyclic_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : donationChainAcyclic s1) : donationChainAcyclic s2 := by
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 h1 h2 hB1 hB2
  rw [hView.tcb] at h1 h2
  exact h tid1 tid2 tcb1 tcb2 scId1 scId2 h1 h2 hB1 hB2

/-- Read-view transport of `donationOwnerValid`. -/
theorem donationOwnerValid_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : donationOwnerValid s1) : donationOwnerValid s2 := by
  intro tid tcb scId owner hTcb hBind
  rw [hView.tcb] at hTcb
  obtain ⟨⟨sc, hSc, hBound⟩, ⟨ownerTcb, hOwner, hUnbound, hReply⟩⟩ :=
    h tid tcb scId owner hTcb hBind
  obtain ⟨sc', hSc', hBT⟩ := hView.schedContext _ sc hSc
  exact ⟨⟨sc', hSc', hBT.trans hBound⟩,
    ⟨ownerTcb, (hView.tcb _ _).mpr hOwner, hUnbound, hReply⟩⟩

/-- Read-view transport of `donationBudgetTransfer`. -/
theorem donationBudgetTransfer_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : donationBudgetTransfer s1) : donationBudgetTransfer s2 := by
  intro tid1 tid2 tcb1 tcb2 scId h1 h2 hNe hS1 hS2
  rw [hView.tcb] at h1 h2
  exact h tid1 tid2 tcb1 tcb2 scId h1 h2 hNe hS1 hS2

/-- Read-view transport of `blockedOnReplyHasTarget`. -/
theorem blockedOnReplyHasTarget_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : blockedOnReplyHasTarget s1) : blockedOnReplyHasTarget s2 := by
  intro tid tcb endpointId replyTarget hTcb hIpc
  rw [hView.tcb] at hTcb
  exact h tid tcb endpointId replyTarget hTcb hIpc

/-- Read-view transport of `replyCallerLinkageReciprocal`. -/
theorem replyCallerLinkageReciprocal_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : replyCallerLinkageReciprocal s1) : replyCallerLinkageReciprocal s2 := by
  refine ⟨fun tid tcb rid hTcb hRep => ?_, fun rid r tid hRep hCaller => ?_⟩
  · rw [hView.tcb] at hTcb
    obtain ⟨r, hR, hBack⟩ := h.1 tid tcb rid hTcb hRep
    exact ⟨r, (hView.reply _ _).mpr hR, hBack⟩
  · rw [hView.reply] at hRep
    obtain ⟨tcb, hTcb, hFwd, hBlk⟩ := h.2 rid r tid hRep hCaller
    exact ⟨tcb, (hView.tcb _ _).mpr hTcb, hFwd, hBlk⟩

/-- Read-view transport of `blockedOnReplyHasReplyObject`. -/
theorem blockedOnReplyHasReplyObject_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : blockedOnReplyHasReplyObject s1) : blockedOnReplyHasReplyObject s2 := by
  intro tid tcb ep rt hTcb hIpc
  rw [hView.tcb] at hTcb
  exact h tid tcb ep rt hTcb hIpc

/-- Read-view transport of `replyCallerLinkage`. -/
theorem replyCallerLinkage_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : replyCallerLinkage s1) : replyCallerLinkage s2 :=
  ⟨replyCallerLinkageReciprocal_of_readViewAgreement hView h.1,
   blockedOnReplyHasReplyObject_of_readViewAgreement hView h.2⟩

/-- Read-view transport of `pendingReceiveReplyWellFormed`. -/
theorem pendingReceiveReplyWellFormed_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : pendingReceiveReplyWellFormed s1) : pendingReceiveReplyWellFormed s2 := by
  refine ⟨fun tid tcb rid hTcb hStash => ?_,
          fun tid₁ tid₂ tcb₁ tcb₂ rid h1 h2 hS1 hS2 => ?_⟩
  · rw [hView.getTcb?_iff] at hTcb
    obtain ⟨hRecv, ⟨r, hR, hFree⟩⟩ := h.1 tid tcb rid hTcb hStash
    exact ⟨hRecv, ⟨r, (hView.getReply?_iff _ _).mpr hR, hFree⟩⟩
  · rw [hView.getTcb?_iff] at h1 h2
    exact h.2 tid₁ tid₂ tcb₁ tcb₂ rid h1 h2 hS1 hS2

/-- Read-view transport of `donationOwnerUnique`. -/
theorem donationOwnerUnique_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : donationOwnerUnique s1) : donationOwnerUnique s2 := by
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 h2 hB1 hB2
  rw [hView.tcb] at h1 h2
  exact h tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 h2 hB1 hB2

/-- Read-view transport of `endpointQueueTailBlockedConsistent`. -/
theorem endpointQueueTailBlockedConsistent_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : endpointQueueTailBlockedConsistent s1) : endpointQueueTailBlockedConsistent s2 := by
  intro epId ep tl tcb hEp hTcb
  rw [hView.endpoint] at hEp
  rw [hView.tcb] at hTcb
  exact h epId ep tl tcb hEp hTcb

/-- Read-view transport of `queueNextTargetBlocked`. -/
theorem queueNextTargetBlocked_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : queueNextTargetBlocked s1) : queueNextTargetBlocked s2 := by
  intro a b tcbA tcbB hA hB hNext
  rw [hView.tcb] at hA hB
  exact h a b tcbA tcbB hA hB hNext

/-- Read-view transport of `notificationWaiterConsistent`. -/
theorem notificationWaiterConsistent_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (h : notificationWaiterConsistent s1) : notificationWaiterConsistent s2 := by
  intro oid ntfn tid hNtfn hMem
  obtain ⟨ntfn₀, hL, _, hW, _⟩ := hView.notification oid ntfn hNtfn
  have hMem₀ : tid ∈ ntfn₀.waitingThreads := by rw [hW]; exact hMem
  obtain ⟨tcb, hTcb, hIpc⟩ := h oid ntfn₀ tid hL hMem₀
  exact ⟨tcb, (hView.tcb _ _).mpr hTcb, hIpc⟩

/-- **The read-view master transport**: two states agreeing on every object
kind the bundle reads satisfy the eighteen CNode-free object conjuncts
interchangeably; the one scheduler-reading conjunct (`passiveServerIdle`) and
the one CNode-reading clause (`capabilityBadgesWellFormed`) are supplied for
the target state.  This is the lever that carries the whole bundle across the
capability, VSpace and untyped-scrub dispatch arms, whose writes the bundle
never reads. -/
theorem ipcInvariantFull_of_readViewAgreement {s1 s2 : SystemState}
    (hView : ipcReadViewAgreement s1 s2)
    (hPsi2 : passiveServerIdle s2)
    (hCapBadges : capabilityBadgesWellFormed s2)
    (h : ipcInvariantFull s1) : ipcInvariantFull s2 :=
  ⟨ipcInvariant_of_readViewAgreement hView h.ipcInvariant,
   dualQueueSystemInvariant_of_readViewAgreement hView h.dualQueueSystemInvariant,
   allPendingMessagesBounded_of_readViewAgreement hView h.allPendingMessagesBounded,
   ⟨notificationBadgesWellFormed_of_readViewAgreement hView h.badgeWellFormed.1, hCapBadges⟩,
   blockedThreadsPendingMessageConsistent_of_readViewAgreement hView
     h.blockedThreadsPendingMessageConsistent,
   endpointQueueNoDup_of_readViewAgreement hView h.endpointQueueNoDup,
   ipcStateQueueMembershipConsistent_of_readViewAgreement hView
     h.ipcStateQueueMembershipConsistent,
   queueNextBlockingConsistent_of_readViewAgreement hView h.queueNextBlockingConsistent,
   queueHeadBlockedConsistent_of_readViewAgreement hView h.queueHeadBlockedConsistent,
   blockedThreadTimeoutConsistent_of_readViewAgreement hView h.blockedThreadTimeoutConsistent,
   donationChainAcyclic_of_readViewAgreement hView h.donationChainAcyclic,
   donationOwnerValid_of_readViewAgreement hView h.donationOwnerValid,
   hPsi2,
   donationBudgetTransfer_of_readViewAgreement hView h.donationBudgetTransfer,
   blockedOnReplyHasTarget_of_readViewAgreement hView h.blockedOnReplyHasTarget,
   replyCallerLinkage_of_readViewAgreement hView h.replyCallerLinkage,
   pendingReceiveReplyWellFormed_of_readViewAgreement hView h.pendingReceiveReplyWellFormed,
   donationOwnerUnique_of_readViewAgreement hView h.donationOwnerUnique,
   endpointQueueTailBlockedConsistent_of_readViewAgreement hView
     h.endpointQueueTailBlockedConsistent,
   queueNextTargetBlocked_of_readViewAgreement hView h.queueNextTargetBlocked⟩

/-- The transition frame nearly every capability-only dispatch arm induces:
objects and scheduler both untouched.  `ipcInvariantFull` transports whole. -/
theorem ipcInvariantFull_of_objects_scheduler_eq {st st' : SystemState}
    (hObjs : st'.objects = st.objects)
    (hSched : st'.scheduler = st.scheduler)
    (h : ipcInvariantFull st) : ipcInvariantFull st' :=
  ipcInvariantFull_of_getElem_eq (fun _ => by rw [hObjs])
    (passiveServerIdle_of_frame
      (passiveServerIdleFrame.of_objects_scheduler_eq hObjs
        (by rw [hSched]) (by rw [hSched]))
      h.passiveServerIdle)
    h

end SeLe4n.Kernel
