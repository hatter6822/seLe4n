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
`coreIpcInvariantBundle` definition + its 16 projection theorems, the M3.5
IPC-scheduler coherence components, the `lifecycleCompositionInvariantBundle`
definition, and the full family of `lifecycleRetypeObject` and
`lifecycleRevokeDeleteRetype` preservation theorems. The file closes with
the private `cspaceSlotUnique` helpers shared by IPC proof callers.
All declarations retain their original names, order, and proofs.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Internal

-- ============================================================================
-- WS-E4: Preservation theorems for endpointReply
-- ============================================================================

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
    (hUnique : cspaceSlotUnique st)
    (hBounded : cspaceSlotCountBounded st)
    (hComp : cdtCompleteness st) (hAcyclic : cdtAcyclicity st)
    (hDepthPre : cspaceDepthConsistent st)
    (hObjInv : st.objects.invExt)
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
  have hU1 : cspaceSlotUnique st1 := by
    intro cnodeId cn hCn1; exact hUnique cnodeId cn (hCnodeBackward cnodeId cn hCn1)
  have hU := cspaceSlotUnique_of_objects_eq st1 (ensureRunnable st1 target)
    hU1 (ensureRunnable_preserves_objects st1 target)
  have ⟨hBndE, hCompE, hAcyclicE⟩ :=
    cdtPredicates_through_reply_path st st1 target ipc msg hBounded hComp hAcyclic hObjInv hTcb
  have hDepth1 : cspaceDepthConsistent st1 := by
    intro cnodeId cn hCn1; exact hDepthPre cnodeId cn (hCnodeBackward cnodeId cn hCn1)
  have hDepthE := cspaceDepthConsistent_of_objects_eq st1 _ hDepth1
    (ensureRunnable_preserves_objects st1 target)
  have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st1 target ipc msg hObjInv hTcb
  have hObjInvE : (ensureRunnable st1 target).objects.invExt :=
    (ensureRunnable_preserves_objects st1 target) ▸ hObjInv1
  exact ⟨hU, cspaceLookupSound_of_cspaceSlotUnique _ hU,
    hBndE, hCompE, hAcyclicE, hDepthE, hObjInvE⟩

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
  rcases hInv with ⟨hUnique, _hSound, hBounded, hComp, hAcyclic, hDepthPre, hObjInv⟩
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
            hUnique hBounded hComp hAcyclic hDepthPre hObjInv hTcb hLookup

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

/-- AG1-C: Extract `uniqueWaiters` from the core bundle. -/
theorem coreIpcInvariantBundle_to_uniqueWaiters {st : SystemState}
    (h : coreIpcInvariantBundle st) : uniqueWaiters st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- AJ1-B: Extract `blockedOnReplyHasTarget` from the core bundle. -/
theorem coreIpcInvariantBundle_to_blockedOnReplyHasTarget {st : SystemState}
    (h : coreIpcInvariantBundle st) : blockedOnReplyHasTarget st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

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
`hNewObjEndpointInv` / `hNewObjNotificationInv` side conditions on IPC proofs). -/
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
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hBounded, hComp, hAcyclic, hDepthPre, hObjInv⟩
  have hUnique' : cspaceSlotUnique st' := by
    rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
      ⟨_, _, _, _, _, _, hStore⟩
    intro cnodeId cn hObj
    by_cases hEq : cnodeId = target
    · rw [hEq] at hObj
      have hObjAtTarget := lifecycle_storeObject_objects_eq st st' target newObj hObjInv hStore
      rw [hObjAtTarget] at hObj
      cases newObj with
      | cnode _ => cases hObj; exact hNewObjCNodeUniq cn rfl
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => cases hObj
    · have hPreserved := lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target
        cnodeId newObj hEq hObjInv hStep
      rw [hPreserved] at hObj
      exact hUnique cnodeId cn hObj
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
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => cases hObj
      · rw [lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target cnodeId newObj hEq hObjInv hStep] at hObj
        exact hBounded cnodeId cn hObj
    · exact cdtCompleteness_of_storeObject st st' target newObj hComp hObjInv hStore hNS
    · exact cdtAcyclicity_of_cdt_eq st st' hAcyclic (storeObject_cdt_eq st st' target newObj hStore)
    · intro cnodeId cn hObj
      by_cases hEq : cnodeId = target
      · rw [hEq] at hObj; rw [lifecycle_storeObject_objects_eq st st' target newObj hObjInv hStore] at hObj
        cases newObj with
        | cnode _ => cases hObj; exact hNewObjCNodeDepth cn rfl
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => cases hObj
      · rw [lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target cnodeId newObj hEq hObjInv hStep] at hObj
        exact hDepthPre cnodeId cn hObj
    · exact storeObject_preserves_objects_invExt st st' target newObj hObjInv hStore
  exact ⟨hUnique', cspaceLookupSound_of_cspaceSlotUnique st' hUnique',
    hBounded', hComp', hAcyclic', hDepth', hObjInv'⟩

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
    (hQNBC' : queueNextBlockingConsistent st')
    (hQHBC' : queueHeadBlockedConsistent st')
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDCA' : donationChainAcyclic st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hDBT' : donationBudgetTransfer st')
    (hUW' : uniqueWaiters st')
    (hBRT' : blockedOnReplyHasTarget st')
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    coreIpcInvariantBundle st' := by
  rcases hInv with ⟨hSched, hCap, hIpcFull⟩
  refine ⟨?_, ?_, ?_⟩
  · exact lifecycleRetypeObject_preserves_schedulerInvariantBundle st st' authority target newObj hSched
      hCurrentValid hStep
  · exact lifecycleRetypeObject_preserves_capabilityInvariantBundle st st' authority target newObj hCap
      hNewObjCNodeUniq hNewObjCNodeBounded hNewObjCNodeDepth hStep
  · exact ⟨lifecycleRetypeObject_preserves_ipcInvariant st st' authority target newObj hIpcFull.1 hNewObjNotificationInv (objects_invExt_of_capabilityInvariantBundle st hCap) hStep,
           hDualQueue', hBounded', hBadge', hWtpmn', hNoDup', hQMC', hQNBC', hQHBC', hBlockedTimeout',
           hDCA', hDOV', hPSI', hDBT', hUW', hBRT'⟩

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
    (hQNBC' : queueNextBlockingConsistent st')
    (hQHBC' : queueHeadBlockedConsistent st')
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDCA' : donationChainAcyclic st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hDBT' : donationBudgetTransfer st')
    (hUW' : uniqueWaiters st')
    (hBRT' : blockedOnReplyHasTarget st')
    (hObjTypesInv : st.lifecycle.objectTypes.invExt)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    lifecycleCompositionInvariantBundle st' := by
  rcases hInv with ⟨hM35, hLifecycle⟩
  rcases hM35 with ⟨hM3, _hCoherence, _hCtx, _hDeq⟩
  have hM3' : coreIpcInvariantBundle st' :=
    lifecycleRetypeObject_preserves_coreIpcInvariantBundle st st' authority target newObj hM3
      hNewObjNotificationInv hNewObjCNodeUniq hNewObjCNodeBounded hNewObjCNodeDepth hCurrentValid hDualQueue' hBounded' hBadge' hWtpmn' hNoDup' hQMC' hQNBC' hQHBC' hBlockedTimeout' hDCA' hDOV' hPSI' hDBT' hUW' hBRT' hStep
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
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hRevoke
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
    hDeleted hNewObjCNodeUniq hNewObjCNodeBounded hNewObjCNodeDepth hRetype

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
    (hNodeSlotK : st.cdtNodeSlot.invExtK)
    (hObjInvFinal : st'.objects.invExt)
    (hStep : lifecycleRevokeDeleteRetype authority cleanup target newObj st = .ok ((), st')) :
    lifecycleCapabilityStaleAuthorityInvariant st' := by
  rcases lifecycleRevokeDeleteRetype_ok_implies_staged_steps st st' authority cleanup target newObj hStep with
    ⟨stRevoked, stDeleted, _hNe, hRevoke, hDelete, hLookupDeleted, hRetype⟩
  have hCap' : capabilityInvariantBundle st' :=
    lifecycleRevokeDeleteRetype_preserves_capabilityInvariantBundle st st' authority cleanup target
      newObj hCap hNewObjCNodeUniq hNewObjCNodeBounded hNewObjCNodeDepth hNodeSlotK hStep
  have hLifecycleDeleted : lifecycleInvariantBundle stDeleted :=
    hLifecycleAfterCleanup stRevoked stDeleted hRevoke hDelete hLookupDeleted
  have hLifecycle' : lifecycleInvariantBundle st' :=
    SeLe4n.Kernel.lifecycleRetypeObject_preserves_lifecycleInvariantBundle stDeleted st' authority target
      newObj hLifecycleDeleted
      (hObjInvAfterCleanup stRevoked stDeleted hRevoke hDelete)
      (hObjTypesInvAfterCleanup stRevoked stDeleted hRevoke hDelete)
      hRetype
  exact lifecycleCapabilityStaleAuthorityInvariant_of_bundles st' hLifecycle' hCap'
    (lifecycleAuthorityMonotonicity_holds st' hCap'.1 hObjInvFinal)

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

/-- WS-E3/H-09: storeTcbIpcState stores a TCB (not a CNode), so cspaceSlotUnique is preserved. -/
theorem cspaceSlotUnique_of_storeTcbIpcState
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hUniq : cspaceSlotUnique st)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    cspaceSlotUnique st' := by
  unfold storeTcbIpcState at hStep
  cases hLookup : lookupTcb st tid with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have := Except.ok.inj hStep; subst this
      exact cspaceSlotUnique_of_storeObject_nonCNode st pair.2 tid.toObjId _ hUniq hObjInv hStore
        (fun cn h => by cases h)

/-- WS-E3/H-09: cspaceSlotUnique through storeObject + storeTcbIpcState + removeRunnable chain. -/
theorem cspaceSlotUnique_through_blocking_path
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (ep : Endpoint)
    (hUniq : cspaceSlotUnique st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject endpointId (.endpoint ep) st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 target ipc = .ok st2) :
    cspaceSlotUnique (removeRunnable st2 target) :=
  cspaceSlotUnique_of_objects_eq st2 (removeRunnable st2 target)
    (cspaceSlotUnique_of_storeTcbIpcState st1 st2 target ipc
      (cspaceSlotUnique_of_endpoint_store st st1 endpointId ep hUniq hObjInv hStore)
      (storeObject_preserves_objects_invExt st st1 endpointId _ hObjInv hStore)
      hTcb) rfl

/-- WS-E3/H-09: cspaceSlotUnique through storeObject + storeTcbIpcState + ensureRunnable chain. -/
theorem cspaceSlotUnique_through_handshake_path
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (ep : Endpoint)
    (hUniq : cspaceSlotUnique st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject endpointId (.endpoint ep) st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 target .ready = .ok st2) :
    cspaceSlotUnique (ensureRunnable st2 target) :=
  cspaceSlotUnique_of_objects_eq st2 (ensureRunnable st2 target)
    (cspaceSlotUnique_of_storeTcbIpcState st1 st2 target .ready
      (cspaceSlotUnique_of_endpoint_store st st1 endpointId ep hUniq hObjInv hStore)
      (storeObject_preserves_objects_invExt st st1 endpointId _ hObjInv hStore)
      hTcb) (ensureRunnable_preserves_objects st2 target)


end SeLe4n.Kernel
