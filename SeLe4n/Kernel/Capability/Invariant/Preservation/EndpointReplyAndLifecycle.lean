-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Invariant.Preservation.Revoke

/-!
AN4-F.3 (CAP-M03) child module extracted from
`SeLe4n.Kernel.Capability.Invariant.Preservation`. Contains the IPC/lifecycle
composition stratum: `endpointReply` capability preservation, the
`coreIpcInvariantBundle` definition + its projection theorems (now 15
after WS-RC R4.C.7 `uniqueWaiters` retirement), the M3.5
IPC-scheduler coherence components, the `lifecycleCompositionInvariantBundle`
definition, and the full family of `lifecycleRetypeObject` and
`lifecycleRevokeDeleteRetype` preservation theorems.  The historical
`cspaceSlotUnique` transfer-theorem cluster that previously closed the
file was deleted in the WS-RC R4.A close-out.
All remaining declarations retain their original names, order, and proofs.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Internal

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
    rw [hTcb1] at hObj1; exact absurd hObj1 (by simp)
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
    (hBounded : cspaceSlotCountBounded st)
    (hComp : cdtCompleteness st) (hAcyclic : cdtAcyclicity st)
    (hDepthPre : cspaceDepthConsistent st)
    (hObjInv : st.objects.invExt)
    (hRCPV : replyCapPointsToValidReply st)
    (hTcb : storeTcbIpcStateAndMessage st target ipc msg = .ok st1)
    (hLookup : lookupTcb st target = some tcb) :
    capabilityInvariantBundle (ensureRunnable st1 target) := by
  have hCnodeBackward : ∀ (cnodeId : SeLe4n.ObjId) (cn : CNode),
      st1.objects[cnodeId]? = some (.cnode cn) → st.objects[cnodeId]? = some (.cnode cn) := by
    intro cnodeId cn hCn1
    by_cases hEq : cnodeId = target.toObjId
    · subst hEq
      have hTargetTcb : ∃ tcb', st.objects[target.toObjId]? = some (.tcb tcb') := by
        unfold lookupTcb at hLookup; cases hObj : st.objects[target.toObjId]? with
        | none => simp [hObj] at hLookup
        | some obj => cases obj with
          | tcb t => exact ⟨t, rfl⟩
          | _ => simp [hObj] at hLookup
      have hTcbPost := storeTcbIpcStateAndMessage_tcb_exists_at_target st st1 target ipc msg hObjInv hTcb hTargetTcb
      rcases hTcbPost with ⟨tcb', hTcb'⟩
      rw [hTcb'] at hCn1; cases hCn1
    · rw [storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target ipc msg cnodeId hEq hObjInv hTcb] at hCn1; exact hCn1
  have ⟨hBndE, hCompE, hAcyclicE⟩ :=
    cdtPredicates_through_reply_path st st1 target ipc msg hBounded hComp hAcyclic hObjInv hTcb
  have hDepth1 : cspaceDepthConsistent st1 := by
    intro cnodeId cn hCn1; exact hDepthPre cnodeId cn (hCnodeBackward cnodeId cn hCn1)
  have hDepthE := cspaceDepthConsistent_of_objects_eq st1 _ hDepth1
    (ensureRunnable_preserves_objects st1 target)
  have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st1 target ipc msg hObjInv hTcb
  have hObjInvE : (ensureRunnable st1 target).objects.invExt :=
    (ensureRunnable_preserves_objects st1 target) ▸ hObjInv1
  -- WS-RC R4.A.6: cspaceSlotUnique conjunct removed from bundle; the
  -- predicate is structurally trivial.
  exact ⟨cspaceLookupSound_holds _,
    hBndE, hCompE, hAcyclicE, hDepthE, hObjInvE,
    replyCapPointsToValidReply_of_objects_eq (ensureRunnable_preserves_objects st1 target)
      (storeTcbIpcStateAndMessage_preserves_replyCapPointsToValidReply
        st st1 target ipc msg tcb hRCPV hObjInv hTcb hLookup)⟩

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
  rcases hInv with ⟨_hSound, hBounded, hComp, hAcyclic, hDepthPre, hObjInv, hRCPV⟩
  unfold endpointReply at hStep
  -- WS-H12d: Eliminate bounds-check if-branches (error cases contradict hStep : ... = .ok ...)
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
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
                revert hStep
                cases hTcb : storeTcbIpcStateAndMessage st target .ready (some msg) with
                | error e => simp
                | ok st1 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hStEq⟩; subst hStEq
                    exact this st1 hTcb
              · -- authorized = false
                simp_all
          -- Dispatch to extracted lemma
          intro st1 hTcb
          exact capabilityInvariantBundle_of_storeTcbAndEnsureRunnable
            st st1 target .ready (some msg) tcb
            hBounded hComp hAcyclic hDepthPre hObjInv hRCPV hTcb hLookup

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

/-- V3-G6: Extract `waitingThreadsPendingMessageNone` from the core bundle. -/
theorem coreIpcInvariantBundle_to_waitingThreadsPendingMessageNone {st : SystemState}
    (h : coreIpcInvariantBundle st) : waitingThreadsPendingMessageNone st :=
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

/-- Z7-H: Extract `passiveServerIdle` from the core bundle. -/
theorem coreIpcInvariantBundle_to_passiveServerIdle {st : SystemState}
    (h : coreIpcInvariantBundle st) : passiveServerIdle st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Z7-I: Extract `donationBudgetTransfer` from the core bundle. -/
theorem coreIpcInvariantBundle_to_donationBudgetTransfer {st : SystemState}
    (h : coreIpcInvariantBundle st) : donationBudgetTransfer st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

-- WS-RC R4.C close-out: `coreIpcInvariantBundle_to_uniqueWaiters` was
-- deleted along with the `uniqueWaiters` predicate it extracted.

/-- AJ1-B: Extract `blockedOnReplyHasTarget` from the core bundle.
WS-RC R4.C.7: index shifted after `uniqueWaiters` conjunct removal.
WS-SM SM6.D (PR #822): `+.1` after `replyCallerLinkage` became the 16th
`ipcInvariantFull` conjunct (the slot now holds the `blockedOnReplyHasTarget ∧
replyCallerLinkage` pair). -/
theorem coreIpcInvariantBundle_to_blockedOnReplyHasTarget {st : SystemState}
    (h : coreIpcInvariantBundle st) : blockedOnReplyHasTarget st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- WS-SM SM6.D (PR #822 review): extract the bidirectional `replyCallerLinkage`
(16th `ipcInvariantFull` conjunct) from the core bundle. -/
theorem coreIpcInvariantBundle_to_replyCallerLinkage {st : SystemState}
    (h : coreIpcInvariantBundle st) : replyCallerLinkage st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- WS-SM SM6.D (PR #822 review): extract the server-first stash well-formedness
(17th `ipcInvariantFull` conjunct) from the core bundle. -/
theorem coreIpcInvariantBundle_to_pendingReceiveReplyWellFormed {st : SystemState}
    (h : coreIpcInvariantBundle st) : pendingReceiveReplyWellFormed st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

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

theorem lifecycleRetypeObject_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : schedulerInvariantBundle st)
    (hCurrentValid : currentThreadValid st')
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
    ⟨_, _, _, _, _, _, hStore⟩
  have hSchedEq : st'.scheduler = st.scheduler :=
    lifecycle_storeObject_scheduler_eq st st' target newObj hStore
  rcases hInv with ⟨hQueue, hRunUnique, _hCurrent⟩
  exact ⟨by simpa [hSchedEq] using hQueue, by simpa [hSchedEq] using hRunUnique, hCurrentValid⟩

/-- WS-E2 / H-01: Compositional preservation of `lifecycleRetypeObject`.
Requires new CNode objects to have unique slots (analogous to existing
`hNewObjEndpointInv` / `hNewObjNotificationInv` side conditions on IPC proofs).

WS-SM SM6.D / PR #822 Phase H (#1.a): `replyCapPointsToValidReply st'` is taken as an
**externalized post-state hypothesis** (`hReplyBacked'`), exactly like the `hCdtPost`
discharge for CDT-modifying ops and the `hRCL'`/`hPRR'`/`hDOV'` externalizations at this
layer.  Retype overwrites the object at `target`: it can *orphan* a reply cap (if a cap
references a reply that is retyped away) or introduce a reply cap (in a fresh CNode), so —
unlike `cspaceCopy`/`Move`/`Mutate`, which preserve the property from the pre-state — the
property is not derivable from the pre-state alone and is discharged by the caller that knows
the retype target is unreferenced and the new object is fresh. -/
theorem lifecycleRetypeObject_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : capabilityInvariantBundle st)
    (hNewObjCNodeUniq : ∀ cn, newObj = .cnode cn → cn.slotsUnique)
    (hNewObjCNodeBounded : ∀ cn, newObj = .cnode cn → cn.slotCountBounded)
    (hNewObjCNodeDepth : ∀ cn, newObj = .cnode cn →
      cn.depth ≤ maxCSpaceDepth ∧ (cn.bitsConsumed > 0 → cn.wellFormed))
    (hReplyBacked' : replyCapPointsToValidReply st')
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨_hSound, hBounded, hComp, hAcyclic, hDepthPre, hObjInv, _hRCPV⟩
  -- WS-H4: lifecycleRetypeObject delegates to storeObject, which preserves CDT fields
  have ⟨hBounded', hComp', hAcyclic', hDepth', hObjInv'⟩ :
      cspaceSlotCountBounded st' ∧ cdtCompleteness st' ∧ cdtAcyclicity st' ∧ cspaceDepthConsistent st' ∧ st'.objects.invExt := by
    rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
      ⟨_, _, _, _, _, _, hStore⟩
    have hNS := (storeObject_cdtNodeSlot_eq st st' target newObj hStore).1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro cnodeId cn hObj
      by_cases hEq : cnodeId = target
      · rw [hEq] at hObj; rw [lifecycle_storeObject_objects_eq st st' target newObj hObjInv hStore] at hObj
        cases newObj with
        | cnode _ => cases hObj; exact hNewObjCNodeBounded cn rfl
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ => cases hObj
      · rw [lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target cnodeId newObj hEq hObjInv hStep] at hObj
        exact hBounded cnodeId cn hObj
    · exact cdtCompleteness_of_storeObject st st' target newObj hComp hObjInv hStore hNS
    · exact cdtAcyclicity_of_cdt_eq st st' hAcyclic (storeObject_cdt_eq st st' target newObj hStore)
    · intro cnodeId cn hObj
      by_cases hEq : cnodeId = target
      · rw [hEq] at hObj; rw [lifecycle_storeObject_objects_eq st st' target newObj hObjInv hStore] at hObj
        cases newObj with
        | cnode _ => cases hObj; exact hNewObjCNodeDepth cn rfl
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ => cases hObj
      · rw [lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target cnodeId newObj hEq hObjInv hStep] at hObj
        exact hDepthPre cnodeId cn hObj
    · exact storeObject_preserves_objects_invExt st st' target newObj hObjInv hStore
  -- WS-RC R4.A.6: cspaceSlotUnique conjunct removed from bundle.
  exact ⟨cspaceLookupSound_holds st',
    hBounded', hComp', hAcyclic', hDepth', hObjInv', hReplyBacked'⟩

theorem lifecycleRetypeObject_preserves_ipcInvariant
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : ipcInvariant st)
    (hNewObjNotificationInv : ∀ ntfn, newObj = .notification ntfn → notificationInvariant ntfn)
    (hObjInv : st.objects.invExt)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    ipcInvariant st' := by
  intro oid ntfn hNtfn
  by_cases hEq : oid = target
  · subst hEq
    have hObjAtTarget : st'.objects[oid]? = some newObj := by
      rcases lifecycleRetypeObject_ok_as_storeObject st st' authority oid newObj hStep with
        ⟨_, _, _, _, _, _, hStore⟩
      exact lifecycle_storeObject_objects_eq st st' oid newObj hObjInv hStore
    have hSomeEq : some newObj = some (.notification ntfn) := by
      simpa [hObjAtTarget] using hNtfn
    have hNewObjEq : newObj = .notification ntfn := by
      injection hSomeEq
    exact hNewObjNotificationInv ntfn hNewObjEq
  · have hPreserved : st'.objects[oid]? = st.objects[oid]? :=
      lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target oid newObj hEq hObjInv hStep
    have hNtfnSt : st.objects[oid]? = some (.notification ntfn) := by simpa [hPreserved] using hNtfn
    exact hInv oid ntfn hNtfnSt

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2: `lifecycleRetypeObject` **establishes** the third clause from a
`newObj` well-formedness side-condition `hNewObjThird` (a `.blockedOnReply` retyped TCB must
carry a reply — the natural constraint, analogous to the CNode/notification ones the
bundle already takes).  Retype writes only `target`: every other slot is framed
(`lifecycleRetypeObject_ok_lookup_preserved_ne`), and the `target` slot's obligation is
exactly `hNewObjThird`. -/
theorem lifecycleRetypeObject_preserves_blockedOnReplyHasReplyObject
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : blockedOnReplyHasReplyObject st)
    (hObjInv : st.objects.invExt)
    (hNewObjThird : ∀ (t : TCB) (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId),
        newObj = .tcb t → t.ipcState = .blockedOnReply ep rt → ∃ rid, t.replyObject = some rid)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    blockedOnReplyHasReplyObject st' := by
  intro tid tcb ep rt hTcb hBlk
  by_cases hEq : tid.toObjId = target
  · have hObjAtTarget : st'.objects[tid.toObjId]? = some newObj := by
      rw [hEq]
      rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
        ⟨_, _, _, _, _, _, hStore⟩
      exact lifecycle_storeObject_objects_eq st st' target newObj hObjInv hStore
    have hNewEq : newObj = .tcb tcb := by simpa using (hObjAtTarget.symm.trans hTcb)
    exact hNewObjThird tcb ep rt hNewEq hBlk
  · have hPreserved := lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target
      tid.toObjId newObj hEq hObjInv hStep
    rw [hPreserved] at hTcb
    exact hInv tid tcb ep rt hTcb hBlk

open SeLe4n.Model.SystemState in
/-- D3: `lifecycleRetypeObject` **establishes** `blockedOnReplyHasTarget` from a `newObj`
side-condition (`hNewObjTarget`: a `.blockedOnReply` retyped TCB has a `some` target). -/
theorem lifecycleRetypeObject_preserves_blockedOnReplyHasTarget
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : blockedOnReplyHasTarget st)
    (hObjInv : st.objects.invExt)
    (hNewObjTarget : ∀ (t : TCB) (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId),
        newObj = .tcb t → t.ipcState = .blockedOnReply ep rt → rt.isSome)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    blockedOnReplyHasTarget st' := by
  intro tid tcb ep rt hTcb hBlk
  by_cases hEq : tid.toObjId = target
  · have hObjAtTarget : st'.objects[tid.toObjId]? = some newObj := by
      rw [hEq]
      rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
        ⟨_, _, _, _, _, _, hStore⟩
      exact lifecycle_storeObject_objects_eq st st' target newObj hObjInv hStore
    have hNewEq : newObj = .tcb tcb := by simpa using (hObjAtTarget.symm.trans hTcb)
    exact hNewObjTarget tcb ep rt hNewEq hBlk
  · have hPreserved := lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target
      tid.toObjId newObj hEq hObjInv hStep
    rw [hPreserved] at hTcb
    exact hInv tid tcb ep rt hTcb hBlk

open SeLe4n.Model.SystemState in
/-- IPC de-threading D6: `lifecycleRetypeObject` preserves `donationBudgetTransfer` from a
`newObj` side-condition (`hNewObjUnbound`: a retyped TCB is `.unbound`).  A fresh retyped TCB
holds no SchedContext, so it cannot be one of two threads sharing an scId; every other slot
frames from the pre-state, where `donationBudgetTransfer st` rules out the share. -/
theorem lifecycleRetypeObject_preserves_donationBudgetTransfer
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : donationBudgetTransfer st)
    (hObjInv : st.objects.invExt)
    (hNewObjUnbound : ∀ (t : TCB), newObj = .tcb t → t.schedContextBinding = .unbound)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    donationBudgetTransfer st' := by
  intro tid1 tid2 tcb1 tcb2 scId h1 h2 hNe hB1 hB2
  have hTargetUnbound : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
      st'.objects[tid.toObjId]? = some (.tcb tcb) → tid.toObjId = target →
      tcb.schedContextBinding.scId? = some scId → False := by
    intro tid tcb hObjT hEq hBT
    have hObjAtTarget : st'.objects[tid.toObjId]? = some newObj := by
      rw [hEq]
      rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
        ⟨_, _, _, _, _, _, hStore⟩
      exact lifecycle_storeObject_objects_eq st st' target newObj hObjInv hStore
    have hNewEq : newObj = .tcb tcb := by simpa using (hObjAtTarget.symm.trans hObjT)
    rw [hNewObjUnbound tcb hNewEq] at hBT
    simp [SchedContextBinding.scId?] at hBT
  have hT1 : tid1.toObjId ≠ target := fun hEq => hTargetUnbound tid1 tcb1 h1 hEq hB1
  have hT2 : tid2.toObjId ≠ target := fun hEq => hTargetUnbound tid2 tcb2 h2 hEq hB2
  rw [lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target tid1.toObjId newObj hT1 hObjInv hStep] at h1
  rw [lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target tid2.toObjId newObj hT2 hObjInv hStep] at h2
  exact hInv tid1 tid2 tcb1 tcb2 scId h1 h2 hNe hB1 hB2

open SeLe4n.Model.SystemState in
/-- IPC de-threading D3: `lifecycleRetypeObject` preserves `pendingReceiveReplyWellFormed`
from the pre-state, given two `newObj`/`target`-keyed side-conditions of the same flavour as
`hNewObjTarget`/`hNewObjThird`.  The retype reduces to a single `storeObject target newObj`
(`lifecycleRetypeObject_ok_as_storeObject`), but unlike the per-kind keystones it must cope
with an *arbitrary* pre-state object at `target` (untyped→tcb etc.), so it discharges PRR's
two clauses directly off the post-state:

* `hNewObjNoStash` — a retyped TCB stashes nothing (`pendingReceiveReply = none`).  This makes
  C1/C2 *vacuous* at `tid.toObjId = target`: the post-state object there is `newObj = .tcb t`,
  whose stash is `none`, so no `some rid` constraint arises at the retype slot.
* `hTargetNotStashedReply` — no blocked receiver stashes a reply whose object slot is `target`.
  This protects C1's "free Reply" half at the framed slots: if a stashed `rid` survived the
  retype it cannot be the `target` slot, so `getReply? rid` frames from the pre-state and stays
  present-and-free.

The two bundles below discharge both conditions as caller obligations (retyping a fresh TCB
clears its stash; the retype target slot is unreferenced by any blocked receiver's stash). -/
theorem lifecycleRetypeObject_preserves_pendingReceiveReplyWellFormed
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : pendingReceiveReplyWellFormed st)
    (hObjInv : st.objects.invExt)
    (hNewObjNoStash : ∀ (t : TCB), newObj = .tcb t → t.pendingReceiveReply = none)
    (hTargetNotStashedReply : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (rid : SeLe4n.ReplyId),
        st.getTcb? tid = some tcb → tcb.pendingReceiveReply = some rid → rid.toObjId ≠ target)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    pendingReceiveReplyWellFormed st' := by
  -- The store wrote `newObj` at `target`; every other slot frames from the pre-state.
  have hStoreAtTarget : st'.objects[target]? = some newObj := by
    rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
      ⟨_, _, _, _, _, _, hStore⟩
    exact lifecycle_storeObject_objects_eq st st' target newObj hObjInv hStore
  -- A surviving TCB (`st'.getTcb? tid = some tcb`) was a TCB in the pre-state, *unless* it sits
  -- at `target` — in which case `newObj = .tcb tcb` and its stash is `none` (`hNewObjNoStash`).
  refine ⟨?_, ?_⟩
  · intro tid tcb rid hTcb hStash
    by_cases hEq : tid.toObjId = target
    · -- retype slot: `newObj = .tcb tcb`, but a retyped TCB stashes nothing — vacuous.
      have hObjEq : st'.objects[tid.toObjId]? = some newObj := by rw [hEq]; exact hStoreAtTarget
      have hNewEq : newObj = .tcb tcb := by
        have := hObjEq.symm.trans ((getTcb?_eq_some_iff st' tid tcb).mp hTcb)
        simpa using this
      exact absurd hStash (by rw [hNewObjNoStash tcb hNewEq]; exact (by simp))
    · -- framed slot: the TCB and its stashed reply both carry from the pre-state.
      have hFrameTcb : st.getTcb? tid = some tcb := by
        rw [getTcb?_eq_some_iff] at hTcb ⊢
        rwa [lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target tid.toObjId
          newObj hEq hObjInv hStep] at hTcb
      obtain ⟨hBlk, r, hr, hrcaller⟩ := hInv.1 tid tcb rid hFrameTcb hStash
      refine ⟨hBlk, r, ?_, hrcaller⟩
      have hRidNe : rid.toObjId ≠ target := hTargetNotStashedReply tid tcb rid hFrameTcb hStash
      rw [getReply?_eq_some_iff] at hr ⊢
      rwa [lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target rid.toObjId
        newObj hRidNe hObjInv hStep]
  · intro tid₁ tid₂ tcb₁ tcb₂ rid hTcb₁ hTcb₂ hStash₁ hStash₂
    -- Either thread sitting at `target` would carry a fresh (`none`) stash — vacuous.
    have noTarget : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB), st'.getTcb? tid = some tcb →
        tcb.pendingReceiveReply = some rid → tid.toObjId ≠ target := by
      intro tid tcb hTcb hStash hEq
      have hObjEq : st'.objects[tid.toObjId]? = some newObj := by rw [hEq]; exact hStoreAtTarget
      have hNewEq : newObj = .tcb tcb := by
        have := hObjEq.symm.trans ((getTcb?_eq_some_iff st' tid tcb).mp hTcb)
        simpa using this
      exact absurd hStash (by rw [hNewObjNoStash tcb hNewEq]; exact (by simp))
    have hNe₁ : tid₁.toObjId ≠ target := noTarget tid₁ tcb₁ hTcb₁ hStash₁
    have hNe₂ : tid₂.toObjId ≠ target := noTarget tid₂ tcb₂ hTcb₂ hStash₂
    have hFrame₁ : st.getTcb? tid₁ = some tcb₁ := by
      rw [getTcb?_eq_some_iff] at hTcb₁ ⊢
      rwa [lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target tid₁.toObjId
        newObj hNe₁ hObjInv hStep] at hTcb₁
    have hFrame₂ : st.getTcb? tid₂ = some tcb₂ := by
      rw [getTcb?_eq_some_iff] at hTcb₂ ⊢
      rwa [lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target tid₂.toObjId
        newObj hNe₂ hObjInv hStep] at hTcb₂
    exact hInv.2 tid₁ tid₂ tcb₁ tcb₂ rid hFrame₁ hFrame₂ hStash₁ hStash₂

/-- IPC de-threading D4: `lifecycleRetypeObject` frames `queueNextBlockingConsistent`.
The retype writes `newObj` at `target`; every other slot frames from the pre-state.
A retyped TCB carries no queue links (`hNewObjNoNext`), and nothing in the pre-state
links to `target` (`hTargetNotQueueLinked`) — so neither the forward nor backward
queueNext obligation at `target` can fire. -/
theorem lifecycleRetypeObject_preserves_queueNextBlockingConsistent
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : queueNextBlockingConsistent st)
    (hObjInv : st.objects.invExt)
    (hNewObjNoNext : ∀ (t : TCB), newObj = .tcb t → t.queueNext = none)
    (hTargetNotQueueLinked : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB) (b : SeLe4n.ThreadId),
        st.objects[a.toObjId]? = some (.tcb tcbA) → tcbA.queueNext = some b → b.toObjId ≠ target)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    queueNextBlockingConsistent st' := by
  have hStoreAtTarget : st'.objects[target]? = some newObj := by
    rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
      ⟨_, _, _, _, _, _, hStore⟩
    exact lifecycle_storeObject_objects_eq st st' target newObj hObjInv hStore
  intro a b tcbA tcbB hA hB hN
  by_cases hEqA : a.toObjId = target
  · -- a is the retyped object: `newObj = .tcb tcbA`, whose queueNext is none — vacuous.
    have hObjEq : st'.objects[a.toObjId]? = some newObj := by rw [hEqA]; exact hStoreAtTarget
    have hNewEq : newObj = .tcb tcbA := by rw [hObjEq] at hA; exact Option.some.inj hA
    rw [hNewObjNoNext tcbA hNewEq] at hN; cases hN
  · -- a is framed; recover its pre-state TCB.
    have hAPre : st.objects[a.toObjId]? = some (.tcb tcbA) := by
      rwa [lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target a.toObjId newObj hEqA hObjInv hStep] at hA
    -- b ≠ target (nobody links to target in the pre-state, and `a.queueNext = some b`).
    have hEqB : b.toObjId ≠ target := hTargetNotQueueLinked a tcbA b hAPre hN
    have hBPre : st.objects[b.toObjId]? = some (.tcb tcbB) := by
      rwa [lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target b.toObjId newObj hEqB hObjInv hStep] at hB
    exact hInv a b tcbA tcbB hAPre hBPre hN

/-- IPC de-threading D4: `lifecycleRetypeObject` frames `queueHeadBlockedConsistent`.
The retype writes `newObj` at `target`; endpoints and TCBs elsewhere frame from the
pre-state.  If a *new* endpoint is created at `target`, its queue heads must be
correctly blocked (`hNewObjHeadsBlocked`); a retyped TCB keeps the head-block
discipline since heads point at framed threads. -/
theorem lifecycleRetypeObject_preserves_queueHeadBlockedConsistent
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : queueHeadBlockedConsistent st)
    (hObjInv : st.objects.invExt)
    (hNewObjNotEndpoint : ∀ ep, newObj ≠ .endpoint ep)
    (hTargetNotHead : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint) (hd : SeLe4n.ThreadId),
        st.objects[epId]? = some (.endpoint ep) →
        (ep.receiveQ.head = some hd ∨ ep.sendQ.head = some hd) → hd.toObjId ≠ target)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    queueHeadBlockedConsistent st' := by
  have hStoreAtTarget : st'.objects[target]? = some newObj := by
    rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
      ⟨_, _, _, _, _, _, hStore⟩
    exact lifecycle_storeObject_objects_eq st st' target newObj hObjInv hStore
  intro epId ep hd tcbHd hEp hTcb
  -- The endpoint must be a framed (pre-state) endpoint: `newObj` is not an endpoint.
  have hEpNe : epId ≠ target := by
    intro hEq; rw [hEq, hStoreAtTarget] at hEp; exact (hNewObjNotEndpoint ep (Option.some.inj hEp))
  have hEpPre : st.objects[epId]? = some (.endpoint ep) := by
    rwa [lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target epId newObj hEpNe hObjInv hStep] at hEp
  refine ⟨fun hHd => ?_, fun hHd => ?_⟩
  · -- receiveQ.head = some hd.  The head is not at `target`, so it frames.
    have hHdNe : hd.toObjId ≠ target := hTargetNotHead epId ep hd hEpPre (Or.inl hHd)
    have hHdPre : st.objects[hd.toObjId]? = some (.tcb tcbHd) := by
      rwa [lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target hd.toObjId newObj hHdNe hObjInv hStep] at hTcb
    exact (hInv epId ep hd tcbHd hEpPre hHdPre).1 hHd
  · have hHdNe : hd.toObjId ≠ target := hTargetNotHead epId ep hd hEpPre (Or.inr hHd)
    have hHdPre : st.objects[hd.toObjId]? = some (.tcb tcbHd) := by
      rwa [lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target hd.toObjId newObj hHdNe hObjInv hStep] at hTcb
    exact (hInv epId ep hd tcbHd hEpPre hHdPre).2 hHd

theorem lifecycleRetypeObject_preserves_coreIpcInvariantBundle
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : coreIpcInvariantBundle st)
    (hNewObjNotificationInv : ∀ ntfn, newObj = .notification ntfn → notificationInvariant ntfn)
    (hNewObjCNodeUniq : ∀ cn, newObj = .cnode cn → cn.slotsUnique)
    (hNewObjCNodeBounded : ∀ cn, newObj = .cnode cn → cn.slotCountBounded)
    (hNewObjCNodeDepth : ∀ cn, newObj = .cnode cn →
      cn.depth ≤ maxCSpaceDepth ∧ (cn.bitsConsumed > 0 → cn.wellFormed))
    (hCurrentValid : currentThreadValid st')
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBounded' : allPendingMessagesBounded st')
    (hBadge' : badgeWellFormed st')
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hNoDup' : endpointQueueNoDup st')
    (hQMC' : ipcStateQueueMembershipConsistent st')
    -- IPC de-threading D4: queueNext/headBlocked established from the pre-state via
    -- retype-link preconditions (a retyped TCB carries no `queueNext`; `target` is
    -- neither a queue link target nor a queue head; a retype never creates an endpoint).
    (hNewObjNoNext : ∀ (t : TCB), newObj = .tcb t → t.queueNext = none)
    (hTargetNotQueueLinked : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB) (b : SeLe4n.ThreadId),
        st.objects[a.toObjId]? = some (.tcb tcbA) → tcbA.queueNext = some b → b.toObjId ≠ target)
    (hNewObjNotEndpoint : ∀ ep, newObj ≠ .endpoint ep)
    (hTargetNotHead : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint) (hd : SeLe4n.ThreadId),
        st.objects[epId]? = some (.endpoint ep) →
        (ep.receiveQ.head = some hd ∨ ep.sendQ.head = some hd) → hd.toObjId ≠ target)
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hNewObjUnbound : ∀ (t : TCB), newObj = .tcb t → t.schedContextBinding = .unbound)
    (hNewObjTarget : ∀ (t : TCB) (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId),
        newObj = .tcb t → t.ipcState = .blockedOnReply ep rt → rt.isSome)
    (hRCLRecip' : replyCallerLinkageReciprocal st')
    (hNewObjThird : ∀ (t : TCB) (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId),
        newObj = .tcb t → t.ipcState = .blockedOnReply ep rt → ∃ rid, t.replyObject = some rid)
    (hNewObjNoStash : ∀ (t : TCB), newObj = .tcb t → t.pendingReceiveReply = none)
    (hTargetNotStashedReply : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (rid : SeLe4n.ReplyId),
        st.getTcb? tid = some tcb → tcb.pendingReceiveReply = some rid → rid.toObjId ≠ target)
    (hReplyBacked' : replyCapPointsToValidReply st')
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    coreIpcInvariantBundle st' := by
  rcases hInv with ⟨hSched, hCap, hIpcFull⟩
  have hObjInvSt : st.objects.invExt := objects_invExt_of_capabilityInvariantBundle st hCap
  refine ⟨?_, ?_, ?_⟩
  · exact lifecycleRetypeObject_preserves_schedulerInvariantBundle st st' authority target newObj hSched
      hCurrentValid hStep
  · exact lifecycleRetypeObject_preserves_capabilityInvariantBundle st st' authority target newObj hCap
      hNewObjCNodeUniq hNewObjCNodeBounded hNewObjCNodeDepth hReplyBacked' hStep
  · exact ⟨lifecycleRetypeObject_preserves_ipcInvariant st st' authority target newObj hIpcFull.1 hNewObjNotificationInv (objects_invExt_of_capabilityInvariantBundle st hCap) hStep,
           hDualQueue', hBounded', hBadge', hWtpmn', hNoDup', hQMC',
           lifecycleRetypeObject_preserves_queueNextBlockingConsistent st st' authority target newObj
             hIpcFull.queueNextBlockingConsistent hObjInvSt hNewObjNoNext hTargetNotQueueLinked hStep,
           lifecycleRetypeObject_preserves_queueHeadBlockedConsistent st st' authority target newObj
             hIpcFull.queueHeadBlockedConsistent hObjInvSt hNewObjNotEndpoint hTargetNotHead hStep,
           hBlockedTimeout',
           -- IPC de-threading D7: derive `donationChainAcyclic` from the threaded
           -- post-state `donationOwnerValid` via the subsumption lemma.
           donationOwnerValid_implies_donationChainAcyclic st' hDOV', hDOV', hPSI',
           lifecycleRetypeObject_preserves_donationBudgetTransfer st st' authority target newObj hIpcFull.donationBudgetTransfer hObjInvSt hNewObjUnbound hStep,
           lifecycleRetypeObject_preserves_blockedOnReplyHasTarget st st' authority target newObj hIpcFull.blockedOnReplyHasTarget (objects_invExt_of_capabilityInvariantBundle st hCap) hNewObjTarget hStep,
           ⟨hRCLRecip', lifecycleRetypeObject_preserves_blockedOnReplyHasReplyObject st st' authority
             target newObj hIpcFull.replyCallerLinkage.2 (objects_invExt_of_capabilityInvariantBundle st hCap)
             hNewObjThird hStep⟩,
           lifecycleRetypeObject_preserves_pendingReceiveReplyWellFormed st st' authority target newObj
             hIpcFull.pendingReceiveReplyWellFormed (objects_invExt_of_capabilityInvariantBundle st hCap)
             hNewObjNoStash hTargetNotStashedReply hStep⟩

theorem lifecycleRetypeObject_preserves_lifecycleCompositionInvariantBundle
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : lifecycleCompositionInvariantBundle st)
    (hNewObjNotificationInv : ∀ ntfn, newObj = .notification ntfn → notificationInvariant ntfn)
    (hNewObjCNodeUniq : ∀ cn, newObj = .cnode cn → cn.slotsUnique)
    (hNewObjCNodeBounded : ∀ cn, newObj = .cnode cn → cn.slotCountBounded)
    (hNewObjCNodeDepth : ∀ cn, newObj = .cnode cn →
      cn.depth ≤ maxCSpaceDepth ∧ (cn.bitsConsumed > 0 → cn.wellFormed))
    (hCurrentValid : currentThreadValid st')
    (hCoherence' : ipcSchedulerCoherenceComponent st')
    (hCtxMatch' : contextMatchesCurrent st')
    (hDeqCoherent' : currentThreadDequeueCoherent st')
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBounded' : allPendingMessagesBounded st')
    (hBadge' : badgeWellFormed st')
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hNoDup' : endpointQueueNoDup st')
    (hQMC' : ipcStateQueueMembershipConsistent st')
    -- IPC de-threading D4: retype-link preconditions replace the threaded
    -- `queueNextBlockingConsistent` / `queueHeadBlockedConsistent` post-states.
    (hNewObjNoNext : ∀ (t : TCB), newObj = .tcb t → t.queueNext = none)
    (hTargetNotQueueLinked : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB) (b : SeLe4n.ThreadId),
        st.objects[a.toObjId]? = some (.tcb tcbA) → tcbA.queueNext = some b → b.toObjId ≠ target)
    (hNewObjNotEndpoint : ∀ ep, newObj ≠ .endpoint ep)
    (hTargetNotHead : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint) (hd : SeLe4n.ThreadId),
        st.objects[epId]? = some (.endpoint ep) →
        (ep.receiveQ.head = some hd ∨ ep.sendQ.head = some hd) → hd.toObjId ≠ target)
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hNewObjUnbound : ∀ (t : TCB), newObj = .tcb t → t.schedContextBinding = .unbound)
    (hNewObjTarget : ∀ (t : TCB) (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId),
        newObj = .tcb t → t.ipcState = .blockedOnReply ep rt → rt.isSome)
    (hRCLRecip' : replyCallerLinkageReciprocal st')
    (hNewObjThird : ∀ (t : TCB) (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId),
        newObj = .tcb t → t.ipcState = .blockedOnReply ep rt → ∃ rid, t.replyObject = some rid)
    (hNewObjNoStash : ∀ (t : TCB), newObj = .tcb t → t.pendingReceiveReply = none)
    (hTargetNotStashedReply : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (rid : SeLe4n.ReplyId),
        st.getTcb? tid = some tcb → tcb.pendingReceiveReply = some rid → rid.toObjId ≠ target)
    (hReplyBacked' : replyCapPointsToValidReply st')
    (hObjTypesInv : st.lifecycle.objectTypes.invExt)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    lifecycleCompositionInvariantBundle st' := by
  rcases hInv with ⟨hM35, hLifecycle⟩
  rcases hM35 with ⟨hM3, _hCoherence, _hCtx, _hDeq⟩
  have hM3' : coreIpcInvariantBundle st' :=
    lifecycleRetypeObject_preserves_coreIpcInvariantBundle st st' authority target newObj hM3
      hNewObjNotificationInv hNewObjCNodeUniq hNewObjCNodeBounded hNewObjCNodeDepth hCurrentValid hDualQueue' hBounded' hBadge' hWtpmn' hNoDup' hQMC' hNewObjNoNext hTargetNotQueueLinked hNewObjNotEndpoint hTargetNotHead hBlockedTimeout' hDOV' hPSI' hNewObjUnbound hNewObjTarget hRCLRecip' hNewObjThird hNewObjNoStash hTargetNotStashedReply hReplyBacked' hStep
  have hLifecycle' : lifecycleInvariantBundle st' :=
    SeLe4n.Kernel.lifecycleRetypeObject_preserves_lifecycleInvariantBundle st st' authority target
      newObj hLifecycle (objects_invExt_of_capabilityInvariantBundle st hM3.2.1) hObjTypesInv hStep
  exact ⟨⟨hM3', hCoherence', hCtxMatch', hDeqCoherent'⟩, hLifecycle'⟩


theorem lifecycleRevokeDeleteRetype_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (authority cleanup : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : capabilityInvariantBundle st)
    (hNewObjCNodeUniq : ∀ cn, newObj = .cnode cn → cn.slotsUnique)
    (hNewObjCNodeBounded : ∀ cn, newObj = .cnode cn → cn.slotCountBounded)
    (hNewObjCNodeDepth : ∀ cn, newObj = .cnode cn →
      cn.depth ≤ maxCSpaceDepth ∧ (cn.bitsConsumed > 0 → cn.wellFormed))
    (hReplyBacked' : replyCapPointsToValidReply st')
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
    (hStep : lifecycleRevokeDeleteRetype authority cleanup target newObj st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases lifecycleRevokeDeleteRetype_ok_implies_staged_steps st st' authority cleanup target newObj hStep with
    ⟨stRevoked, stDeleted, _hNe, hRevoke, hDelete, _hLookupDeleted, hRetype⟩
  have hRevoked : capabilityInvariantBundle stRevoked :=
    cspaceRevoke_preserves_capabilityInvariantBundle st stRevoked cleanup hInv hRevoke
  -- cspaceRevoke preserves cdtNodeSlot
  have hRevokedNS : stRevoked.cdtNodeSlot = st.cdtNodeSlot := by
    unfold cspaceRevoke at hRevoke
    cases hLookup : cspaceLookupSlot cleanup st with
    | error e => simp [hLookup] at hRevoke
    | ok pair =>
      rcases pair with ⟨parent, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 cleanup parent hLookup
      subst st1; simp [hLookup] at hRevoke
      cases hObj : st.objects[cleanup.cnode]? with
      | none => simp [hObj] at hRevoke
      | some obj =>
        cases obj with
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ => simp [hObj] at hRevoke
        | cnode preCn =>
          simp [hObj] at hRevoke
          cases hStore : storeObject cleanup.cnode
              (.cnode (preCn.revokeTargetLocal cleanup.slot parent.target)) st with
          | error e => simp [hStore] at hRevoke
          | ok pair =>
            obtain ⟨_, stMid⟩ := pair; simp [hStore] at hRevoke; rw [← hRevoke]
            have hNSMid := (storeObject_cdtNodeSlot_eq st stMid cleanup.cnode _ hStore).1
            have ⟨_, hNSClear, _, _⟩ := revokeAndClearRefsState_cdt_eq preCn cleanup.slot parent.target cleanup.cnode stMid
            rw [hNSClear, hNSMid]
  have hDeleted : capabilityInvariantBundle stDeleted :=
    cspaceDeleteSlot_preserves_capabilityInvariantBundle stRevoked stDeleted cleanup hRevoked
      (hRevokedNS ▸ hNodeSlotK) hDelete
  exact lifecycleRetypeObject_preserves_capabilityInvariantBundle stDeleted st' authority target newObj
    hDeleted hNewObjCNodeUniq hNewObjCNodeBounded hNewObjCNodeDepth hReplyBacked' hRetype

theorem lifecycleRevokeDeleteRetype_preserves_lifecycleCapabilityStaleAuthorityInvariant
    (st st' : SystemState)
    (authority cleanup : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hCap : capabilityInvariantBundle st)
    (hNewObjCNodeUniq : ∀ cn, newObj = .cnode cn → cn.slotsUnique)
    (hNewObjCNodeBounded : ∀ cn, newObj = .cnode cn → cn.slotCountBounded)
    (hNewObjCNodeDepth : ∀ cn, newObj = .cnode cn →
      cn.depth ≤ maxCSpaceDepth ∧ (cn.bitsConsumed > 0 → cn.wellFormed))
    (hLifecycleAfterCleanup :
      ∀ stRevoked stDeleted,
        cspaceRevoke cleanup st = .ok ((), stRevoked) →
        cspaceDeleteSlot cleanup stRevoked = .ok ((), stDeleted) →
        cspaceLookupSlot cleanup stDeleted = .error .invalidCapability →
        lifecycleInvariantBundle stDeleted)
    (hObjInvAfterCleanup :
      ∀ stRevoked stDeleted,
        cspaceRevoke cleanup st = .ok ((), stRevoked) →
        cspaceDeleteSlot cleanup stRevoked = .ok ((), stDeleted) →
        stDeleted.objects.invExt)
    (hObjTypesInvAfterCleanup :
      ∀ stRevoked stDeleted,
        cspaceRevoke cleanup st = .ok ((), stRevoked) →
        cspaceDeleteSlot cleanup stRevoked = .ok ((), stDeleted) →
        stDeleted.lifecycle.objectTypes.invExt)
    (hReplyBacked' : replyCapPointsToValidReply st')
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
    (hObjInvFinal : st'.objects.invExt)
    (hStep : lifecycleRevokeDeleteRetype authority cleanup target newObj st = .ok ((), st')) :
    lifecycleCapabilityStaleAuthorityInvariant st' := by
  rcases lifecycleRevokeDeleteRetype_ok_implies_staged_steps st st' authority cleanup target newObj hStep with
    ⟨stRevoked, stDeleted, _hNe, hRevoke, hDelete, hLookupDeleted, hRetype⟩
  have hCap' : capabilityInvariantBundle st' :=
    lifecycleRevokeDeleteRetype_preserves_capabilityInvariantBundle st st' authority cleanup target
      newObj hCap hNewObjCNodeUniq hNewObjCNodeBounded hNewObjCNodeDepth hReplyBacked' hNodeSlotK hStep
  have hLifecycleDeleted : lifecycleInvariantBundle stDeleted :=
    hLifecycleAfterCleanup stRevoked stDeleted hRevoke hDelete hLookupDeleted
  have hLifecycle' : lifecycleInvariantBundle st' :=
    SeLe4n.Kernel.lifecycleRetypeObject_preserves_lifecycleInvariantBundle stDeleted st' authority target
      newObj hLifecycleDeleted
      (hObjInvAfterCleanup stRevoked stDeleted hRevoke hDelete)
      (hObjTypesInvAfterCleanup stRevoked stDeleted hRevoke hDelete)
      hRetype
  exact lifecycleCapabilityStaleAuthorityInvariant_of_bundles st' hLifecycle' hCap'
    (lifecycleAuthorityMonotonicity_holds st' hObjInvFinal)

theorem lifecycleRevokeDeleteRetype_error_preserves_lifecycleCompositionInvariantBundle
    (st : SystemState)
    (authority cleanup : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hAlias : authority = cleanup)
    (hInv : lifecycleCompositionInvariantBundle st) :
    lifecycleCompositionInvariantBundle st := by
  have _hExpected : lifecycleRevokeDeleteRetype authority cleanup target newObj st = .error .illegalState :=
    lifecycleRevokeDeleteRetype_error_authority_cleanup_alias st authority cleanup target newObj hAlias
  exact hInv

-- WS-RC R4 close-out: the historical transfer theorems
-- `cspaceSlotUnique_of_storeTcbIpcState`,
-- `cspaceSlotUnique_through_blocking_path`, and
-- `cspaceSlotUnique_through_handshake_path` were deleted along with the
-- `cspaceSlotUnique` predicate they discharged.  Per the CLAUDE.md
-- structural-promotion convention, every `CNode.slots : UniqueSlotMap`
-- value satisfies the slot-uniqueness invariant by construction; no
-- transfer theorems are needed.

end SeLe4n.Kernel
