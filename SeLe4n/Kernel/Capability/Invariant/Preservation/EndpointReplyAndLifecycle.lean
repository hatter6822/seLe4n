-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Invariant.Preservation.CopyMoveMutate

/-!
AN4-F.3 (CAP-M03) child module extracted from
`SeLe4n.Kernel.Capability.Invariant.Preservation`. Contains the IPC/lifecycle
composition stratum: `endpointReply` capability preservation, the
`coreIpcInvariantBundle` definition + its projection theorems (now 15
after WS-RC R4.C.7 `uniqueWaiters` retirement), the M3.5
IPC-scheduler coherence components, the `lifecycleCompositionInvariantBundle`
definition.  The in-place retype's preservation family
(`lifecycleRetypeObject_preserves_*`) left with the in-place retype itself:
every object is now carved from an untyped.  The historical
`cspaceSlotUnique` transfer-theorem cluster that previously closed the
file was deleted in the WS-RC R4.A close-out.
All remaining declarations retain their original names, order, and proofs.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- WS-E4: Preservation theorems for endpointReply
-- ============================================================================

/-- WS-SM SM6.D / PR #822 Phase H (#1.a): a TCB-payload store preserves
`replyCapPointsToValidReply`.  `storeTcbIpcStateAndMessage` only rewrites the `.tcb` object at
`target` (no `.cnode` is created or altered, so every CNode in the post-state was a CNode in the
pre-state with the same caps) and leaves every `.reply` object untouched (`getReply?` frames
through), so the backing of every reply cap carries over.  Shared by every TCB-store reply path
(`endpointReply`, the lifecycle cleanup paths, IPC capability transfer). -/
theorem storeTcbIpcStateAndMessage_preserves_replyCapPointsToValidReply
    (st st1 : SystemState) (target : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage) (tcb : TCB)
    (hRCPV : replyCapPointsToValidReply st)
    (hObjInv : st.objects.invExt)
    (hTcb : storeTcbIpcStateAndMessage st target ipc msg = .ok st1)
    (hLookup : lookupTcb st target = some tcb) :
    replyCapPointsToValidReply st1 := by
  -- `lookupTcb_some_objects` is the typed bridge from the resolved TCB to its object-store slot,
  -- avoiding a raw thread-id object-store projection.
  have hStTcb := lookupTcb_some_objects st target tcb hLookup
  obtain ⟨t1, hTcb1⟩ :=
    storeTcbIpcStateAndMessage_tcb_exists_at_target st st1 target ipc msg hObjInv hTcb ⟨tcb, hStTcb⟩
  have hGR : ∀ rid : SeLe4n.ReplyId, st1.getReply? rid = st.getReply? rid := by
    intro rid
    by_cases hEq : rid.toObjId = target.toObjId
    · simp only [SystemState.getReply?, hEq, hTcb1, hStTcb]
    · simp only [SystemState.getReply?,
        storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target ipc msg rid.toObjId hEq hObjInv hTcb]
  intro oid cn slot cap rid hObj1 hLook hTgt
  rw [hGR]
  by_cases hEq : oid = target.toObjId
  · subst hEq
    obtain ⟨o, ho, hS⟩ := (storeTcbIpcStateAndMessage_kindPreservingWrite hObjInv hTcb).slotCap_back hObj1
    exact hRCPV _ o slot cap rid ho (hS ▸ hLook) hTgt
  · rw [storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target ipc msg oid hEq hObjInv hTcb] at hObj1
    exact hRCPV oid cn slot cap rid hObj1 hLook hTgt

/-- M-P05: Shared reply-path infrastructure — if `storeTcbIpcStateAndMessage`
succeeds and the target was a TCB (evidenced by `lookupTcb`), then
`ensureRunnable` on the result preserves the capability invariant bundle.

Extracted from `endpointReply_preserves_capabilityInvariantBundle` to eliminate
duplicated proof across the authorized/unrestricted reply branches. Also
provides reusable infrastructure for M3 (IPC capability transfer). -/
theorem capabilityInvariantBundle_of_storeTcbAndEnsureRunnable
    (st st1 : SystemState) (target : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (tcb : TCB)
    (hComp : cdtCompleteness st) (hAcyclic : cdtAcyclicity st)
    (hDepthPre : cspaceDepthConsistent st)
    (hObjInv : st.objects.invExt)
    (hRCPV : replyCapPointsToValidReply st)
    (hLinks : cdtLinksAgree st) (hShape : SystemState.CapTreeShape st)
    (hTcb : storeTcbIpcStateAndMessage st target ipc msg = .ok st1)
    (hLookup : lookupTcb st target = some tcb) :
    capabilityInvariantBundle (ensureRunnable st1 target) := by
  have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st1 target ipc msg hObjInv hTcb
  have hEns := ensureRunnable_onlyObjectsSchedulerDiffer st1 target
  unfold SystemState.onlyObjectsSchedulerDiffer at hEns
  have hEnsCdt : (ensureRunnable st1 target).cdt = st.cdt :=
    (show (ensureRunnable st1 target).cdt = st1.cdt by rw [hEns]).trans
      (storeTcbIpcStateAndMessage_cdt_eq hTcb)
  -- The store rewrites the target's TCB off its slots and the wake rewrites run
  -- links: both are kind- and slot-preserving writes.
  exact capabilityInvariantBundle_of_kindPreserving
    ⟨cspaceLookupSound_holds _, hComp, hAcyclic, hDepthPre, hObjInv, hRCPV, hLinks, hShape⟩ hEnsCdt
    ((ensureRunnable_objects_invExt st1 target) hObjInv1)
    ((storeTcbIpcStateAndMessage_kindPreservingWrite hObjInv hTcb).trans
      (ensureRunnable_objectsAgreeOffRunLinks st1 target).kindPreserving)

/-- PR #827 #3 fold: `consumeCallerReply` preserves `capabilityInvariantBundle` —
neither leg touches a CNode, the CDT, or the CDT node→slot mapping;
`objects.invExt` is preserved; no object is removed (both legs overwrite
existing slots); and the consumed Reply object *remains present* (only its
`caller` is cleared), so every reply cap stays backed. -/
theorem consumeCallerReply_preserves_capabilityInvariantBundle
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hInv : capabilityInvariantBundle st)
    (hStep : SystemState.consumeCallerReply caller rid st = .ok ((), st')) :
    capabilityInvariantBundle st' :=
  capabilityInvariantBundle_of_kindPreserving hInv
    (SystemState.consumeCallerReply_cdt_eq st st' caller rid hStep)
    (SystemState.consumeCallerReply_preserves_objects_invExt st st' caller rid hInv.2.2.2.2.1 hStep)
    (SystemState.consumeCallerReply_kindPreservingWrite st st' caller rid hInv.2.2.2.2.1 hStep)

/-- **WS-RM (`v0.35.6`)**: the *removal* preserves the bundle.  It is
`consumeCallerReply` run at the state the splice left, and the splice writes only
`.reply` slots that already held Replies — so no CNode moves, the CDT and its slot
map are untouched, and every key that resolved still resolves.  Proved directly
rather than by composing a splice-level bundle lemma: the bundle's CDT clauses
read fields the splice frames by `rfl`, so a second bundle statement about the
fold would be a copy of this reasoning at a state no transition visits. -/
theorem removeCallerReplyFrame_preserves_capabilityInvariantBundle
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hInv : capabilityInvariantBundle st)
    (hStep : removeCallerReplyFrame caller rid st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  have hObjInv : st.objects.invExt := hInv.2.2.2.2.1
  refine consumeCallerReply_preserves_capabilityInvariantBundle
    (spliceReplyFrameOutOrSelf st rid) st' caller rid ?_ hStep
  exact capabilityInvariantBundle_of_kindPreserving hInv (spliceReplyFrameOutOrSelf_cdt_eq st rid)
    (spliceReplyFrameOutOrSelf_preserves_objects_invExt st rid hObjInv)
    (spliceReplyFrameOutOrSelf_kindPreservingWrite st rid hObjInv)

/-- WS-F1/WS-E4/M-12/WS-H1: endpointReply preserves capabilityInvariantBundle.
Reply stores a TCB with message (not a CNode), so CSpace invariants are preserved.
Updated for WS-H1 reply-target scoping (replier parameter + replyTarget validation).
M-P05: Proof body delegated to `capabilityInvariantBundle_of_storeTcbAndEnsureRunnable`. -/
theorem endpointReply_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (hInv : capabilityInvariantBundle st)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨_hSound, hComp, hAcyclic, hDepthPre, hObjInv, hRCPV, hLinks, hShape⟩
  unfold endpointReply at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp only [hLookup] at hStep
      rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
      cases hIpc : tcb.ipcState with
      | ready => simp [hIpc] at hStep
      | blockedOnSend _ => simp [hIpc] at hStep
      | blockedOnReceive _ => simp [hIpc] at hStep
      | blockedOnNotification _ => simp [hIpc] at hStep
      | blockedOnCall _ => simp [hIpc] at hStep
      | blockedOnReply epId replyTarget =>
          simp only [hIpc] at hStep
          -- AK1-B (I-H02): Fail-closed on replyTarget = none
          suffices ∀ st1, storeTcbIpcStateAndMessage st target .ready (some msg) = .ok st1 →
              capabilityInvariantBundle (ensureRunnable st1 target) by
            cases replyTarget with
            | none => simp at hStep
            | some expected =>
              simp only at hStep
              split at hStep
              · -- authorized = true
                cases hTcb : storeTcbIpcStateAndMessage st target .ready (some msg) with
                | error e => simp [hTcb] at hStep
                | ok st1 =>
                    simp only [hTcb] at hStep
                    have hMid := this st1 hTcb
                    -- PR #827 #3 fold: peel the atomic caller↔Reply consume.
                    cases hRO : tcb.replyObject with
                    | none =>
                      simp only [hRO, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
                      rw [← hStep]; exact hMid
                    | some rid =>
                      simp only [hRO] at hStep
                      exact removeCallerReplyFrame_preserves_capabilityInvariantBundle
                        _ _ target rid hMid hStep
              · -- authorized = false
                simp_all
          -- Dispatch to extracted lemma
          intro st1 hTcb
          exact capabilityInvariantBundle_of_storeTcbAndEnsureRunnable
            st st1 target .ready (some msg) tcb
            hComp hAcyclic hDepthPre hObjInv hRCPV hLinks hShape hTcb hLookup

/-- M3 composed bundle entrypoint: M1 scheduler + M2 capability + M3 IPC.

WS-H12e: Updated to use `ipcInvariantFull` (which composes `ipcInvariant`,
`dualQueueSystemInvariant`, and `allPendingMessagesBounded`) instead of
the bare `ipcInvariant`. This closes the gap where dual-queue structural
well-formedness and message payload bounds were defined but not composed
into the cross-subsystem proof surface. -/
def coreIpcInvariantBundle (st : SystemState) : Prop :=
  schedulerInvariantBundle st ∧ capabilityInvariantBundle st ∧ ipcInvariantFull st

/-- WS-H12e: Extract the bare `ipcInvariant` from the core bundle for
backward-compatible proof composition. -/
theorem coreIpcInvariantBundle_to_ipcInvariant {st : SystemState}
    (h : coreIpcInvariantBundle st) : ipcInvariant st :=
  h.2.2.1

/-- WS-H12e: Extract `dualQueueSystemInvariant` from the core bundle. -/
theorem coreIpcInvariantBundle_to_dualQueueSystemInvariant {st : SystemState}
    (h : coreIpcInvariantBundle st) : dualQueueSystemInvariant st :=
  h.2.2.2.1

/-- WS-H12e: Extract `allPendingMessagesBounded` from the core bundle. -/
theorem coreIpcInvariantBundle_to_allPendingMessagesBounded {st : SystemState}
    (h : coreIpcInvariantBundle st) : allPendingMessagesBounded st :=
  h.2.2.2.2.1

/-- WS-F5/D1d: Extract `badgeWellFormed` from the core bundle. -/
theorem coreIpcInvariantBundle_to_badgeWellFormed {st : SystemState}
    (h : coreIpcInvariantBundle st) : badgeWellFormed st :=
  h.2.2.2.2.2.1

/-- V3-G6: Extract `blockedThreadsPendingMessageConsistent` from the core bundle. -/
theorem coreIpcInvariantBundle_to_blockedThreadsPendingMessageConsistent {st : SystemState}
    (h : coreIpcInvariantBundle st) : blockedThreadsPendingMessageConsistent st :=
  h.2.2.2.2.2.2.1

/-- V3-K: Extract `endpointQueueNoDup` from the core bundle. -/
theorem coreIpcInvariantBundle_to_endpointQueueNoDup {st : SystemState}
    (h : coreIpcInvariantBundle st) : endpointQueueNoDup st :=
  h.2.2.2.2.2.2.2.1

/-- V3-J: Extract `ipcStateQueueMembershipConsistent` from the core bundle. -/
theorem coreIpcInvariantBundle_to_ipcStateQueueMembershipConsistent {st : SystemState}
    (h : coreIpcInvariantBundle st) : ipcStateQueueMembershipConsistent st :=
  h.2.2.2.2.2.2.2.2.1

/-- V3-J-cross: Extract `queueNextBlockingConsistent` from the core bundle. -/
theorem coreIpcInvariantBundle_to_queueNextBlockingConsistent {st : SystemState}
    (h : coreIpcInvariantBundle st) : queueNextBlockingConsistent st :=
  h.2.2.2.2.2.2.2.2.2.1

/-- V3-J-cross: Extract `queueHeadBlockedConsistent` from the core bundle. -/
theorem coreIpcInvariantBundle_to_queueHeadBlockedConsistent {st : SystemState}
    (h : coreIpcInvariantBundle st) : queueHeadBlockedConsistent st :=
  h.2.2.2.2.2.2.2.2.2.2.1

/-- Z6-J: Extract `blockedThreadTimeoutConsistent` from the core bundle. -/
theorem coreIpcInvariantBundle_to_blockedThreadTimeoutConsistent {st : SystemState}
    (h : coreIpcInvariantBundle st) : blockedThreadTimeoutConsistent st :=
  h.2.2.2.2.2.2.2.2.2.2.2.1

/-- Z7-F: Extract `donationChainAcyclic` from the core bundle. -/
theorem coreIpcInvariantBundle_to_donationChainAcyclic {st : SystemState}
    (h : coreIpcInvariantBundle st) : donationChainAcyclic st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Z7-G: Extract `donationOwnerValid` from the core bundle. -/
theorem coreIpcInvariantBundle_to_donationOwnerValid {st : SystemState}
    (h : coreIpcInvariantBundle st) : donationOwnerValid st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Z7-I: Extract `donationBudgetTransfer` from the core bundle. -/
theorem coreIpcInvariantBundle_to_donationBudgetTransfer {st : SystemState}
    (h : coreIpcInvariantBundle st) : donationBudgetTransfer st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

-- WS-RC R4.C close-out: `coreIpcInvariantBundle_to_uniqueWaiters` was
-- deleted along with the `uniqueWaiters` predicate it extracted.

/-- AJ1-B: Extract `blockedOnReplyHasTarget` from the core bundle.
WS-RC R4.C.7: index shifted after `uniqueWaiters` conjunct removal.
WS-SM SM6.D (PR #822): `+.1` after `replyCallerLinkage` became the 16th
`ipcInvariantFull` conjunct (the slot now holds the `blockedOnReplyHasTarget ∧
replyCallerLinkage` pair). -/
theorem coreIpcInvariantBundle_to_blockedOnReplyHasTarget {st : SystemState}
    (h : coreIpcInvariantBundle st) : blockedOnReplyHasTarget st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- WS-SM SM6.D (PR #822 review): extract the bidirectional `replyCallerLinkage`
(15th `ipcInvariantFull` conjunct) from the core bundle. -/
theorem coreIpcInvariantBundle_to_replyCallerLinkage {st : SystemState}
    (h : coreIpcInvariantBundle st) : replyCallerLinkage st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- WS-SM SM6.D (PR #822 review): extract the server-first stash well-formedness
(16th `ipcInvariantFull` conjunct) from the core bundle. -/
theorem coreIpcInvariantBundle_to_pendingReceiveReplyWellFormed {st : SystemState}
    (h : coreIpcInvariantBundle st) : pendingReceiveReplyWellFormed st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- IPC de-threading D6: extract donation-owner uniqueness (17th `ipcInvariantFull` conjunct). -/
theorem coreIpcInvariantBundle_to_donationOwnerUnique {st : SystemState}
    (h : coreIpcInvariantBundle st) : donationOwnerUnique st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- IPC de-threading D4 (Finding F-2): extract endpoint-queue tail-blocked consistency
(18th `ipcInvariantFull` conjunct). -/
theorem coreIpcInvariantBundle_to_endpointQueueTailBlockedConsistent {st : SystemState}
    (h : coreIpcInvariantBundle st) : endpointQueueTailBlockedConsistent st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- IPC de-threading D4 Slice 2c: extract queue-next target-blocked consistency
(19th `ipcInvariantFull` conjunct). -/
theorem coreIpcInvariantBundle_to_queueNextTargetBlocked {st : SystemState}
    (h : coreIpcInvariantBundle st) : queueNextTargetBlocked st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Extract notification binding reciprocity (20th `ipcInvariantFull` conjunct). -/
theorem coreIpcInvariantBundle_to_notificationBindingReciprocal {st : SystemState}
    (h : coreIpcInvariantBundle st) : notificationBindingReciprocal st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Extract the endpoint-queue link discipline (21st `ipcInvariantFull` conjunct):
a thread with a queue successor is blocked on an endpoint. -/
theorem coreIpcInvariantBundle_to_endpointQueueLinksOnlyBlocked {st : SystemState}
    (h : coreIpcInvariantBundle st) : endpointQueueLinksOnlyBlocked st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- Named M3.5 coherence component: runnable threads stay IPC-ready. -/
def ipcSchedulerRunnableReadyComponent (st : SystemState) : Prop :=
  runnableThreadIpcReady st

/-- Named M3.5 coherence component: send-blocked threads are not runnable. -/
def ipcSchedulerBlockedSendComponent (st : SystemState) : Prop :=
  blockedOnSendNotRunnable st

/-- Named M3.5 coherence component: receive-blocked threads are not runnable. -/
def ipcSchedulerBlockedReceiveComponent (st : SystemState) : Prop :=
  blockedOnReceiveNotRunnable st

/-- WS-H1: Named coherence component: call-blocked threads are not runnable. -/
def ipcSchedulerBlockedCallComponent (st : SystemState) : Prop :=
  blockedOnCallNotRunnable st

/-- WS-H1: Named coherence component: reply-blocked threads are not runnable. -/
def ipcSchedulerBlockedReplyComponent (st : SystemState) : Prop :=
  blockedOnReplyNotRunnable st

/-- WS-F6/D2: Named coherence component: notification-blocked threads are not runnable. -/
def ipcSchedulerBlockedNotificationComponent (st : SystemState) : Prop :=
  blockedOnNotificationNotRunnable st

/-- Named M3.5 aggregate coherence component for IPC+scheduler interaction. -/
def ipcSchedulerCoherenceComponent (st : SystemState) : Prop :=
  ipcSchedulerRunnableReadyComponent st ∧
  ipcSchedulerBlockedSendComponent st ∧
  ipcSchedulerBlockedReceiveComponent st ∧
  ipcSchedulerBlockedCallComponent st ∧
  ipcSchedulerBlockedReplyComponent st ∧
  ipcSchedulerBlockedNotificationComponent st

theorem ipcSchedulerCoherenceComponent_iff_contractPredicates (st : SystemState) :
    ipcSchedulerCoherenceComponent st ↔ ipcSchedulerContractPredicates st := by
  rfl

/-- M3.5 composed bundle entrypoint layered over the M3 IPC seed bundle.

This is the step-4 composition target for active-slice endpoint/scheduler coupling.
WS-H12e: Adds `contextMatchesCurrent` and `currentThreadDequeueCoherent` to the
coupling bundle, ensuring register-context coherence and dequeue-on-dispatch
coherence predicates are part of the cross-subsystem proof surface. -/
def ipcSchedulerCouplingInvariantBundle (st : SystemState) : Prop :=
  coreIpcInvariantBundle st ∧ ipcSchedulerCoherenceComponent st ∧
  contextMatchesCurrent st ∧ currentThreadDequeueCoherent st

/-- M4-A composed bundle entrypoint:
M3.5 IPC+scheduler composition plus lifecycle metadata/invariant obligations. -/
def lifecycleCompositionInvariantBundle (st : SystemState) : Prop :=
  ipcSchedulerCouplingInvariantBundle st ∧ lifecycleInvariantBundle st


-- WS-RC R4 close-out: the historical transfer theorems
-- `cspaceSlotUnique_of_storeTcbIpcState`,
-- `cspaceSlotUnique_through_blocking_path`, and
-- `cspaceSlotUnique_through_handshake_path` were deleted along with the
-- `cspaceSlotUnique` predicate they discharged.  Per the CLAUDE.md
-- structural-promotion convention, every `CNode.slots : UniqueSlotMap`
-- value satisfies the slot-uniqueness invariant by construction; no
-- transfer theorems are needed.

end SeLe4n.Kernel
