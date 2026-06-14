-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM SM6.A cross-core IPC (runtime dispatch wiring
-- gated on the SM5.I FFI seam; see docs/planning/SMP_CROSS_CORE_IPC_PLAN.md).

import SeLe4n.Kernel.IPC.CrossCore.EndpointCall
import SeLe4n.Kernel.InformationFlow.Invariant.Operations

/-!
# WS-SM SM6.A.7 — Cross-core endpoint-call non-interference

The information-flow slice of SM6.A: the cross-core `endpointCallOnCore`
rendezvous is invisible to a low observer when the endpoint, caller, and
receiver are all high (non-observable) — `projectState` is preserved across the
whole call, exactly as the single-core `endpointCall_preserves_projection`
(plan §3, the `endpointCall_call_path_NI` cross-core variant).

The new content over the single-core proof is the projection preservation of
the two cross-core scheduler steps — `enqueueRunnableOnCore` (the receiver wake
routed to its home core, via `wakeThread`) and `removeRunnableOnCore` (the
caller block on its own core) — for a high thread, on an *arbitrary* core.
These compose with the existing `endpointQueuePopHead_preserves_projection` /
`storeTcbIpcStateAndMessage_preserves_projection` lemmas.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §1  `projectObjects` is preserved by a high-object insert
-- ============================================================================

/-- A kernel state whose object store is `st`'s with one extra insert at a
**non-observable** id has the same observable object projection as `st`. -/
theorem projectObjects_insert_high (ctx : LabelingContext) (observer : IfObserver)
    (st s' : SystemState) (tid : SeLe4n.ThreadId) (v : KernelObject)
    (hObjEq : s'.objects = st.objects.insert tid.toObjId v)
    (hHighObj : objectObservable ctx observer tid.toObjId = false)
    (hObjInv : st.objects.invExt) :
    projectObjects ctx observer s' = projectObjects ctx observer st := by
  funext oid
  by_cases hObs : objectObservable ctx observer oid
  · by_cases hEq : oid = tid.toObjId
    · subst hEq; rw [hHighObj] at hObs; exact absurd hObs (by simp)
    · simp only [projectObjects, hObs, if_true, hObjEq]
      congr 1
      exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId oid v
        (by simp only [beq_iff_eq]; exact fun h => hEq h.symm) hObjInv
  · simp [projectObjects, hObs]

-- ============================================================================
-- §2  Cross-core scheduler steps preserve `projectState` for a high thread
-- ============================================================================

/-- WS-SM SM6.A.7: removing a **non-observable** thread from *any* core's run
queue preserves the low-observer projection.  Boot core: the single-core
`removeRunnable_preserves_projection`; other cores: the boot-core scheduler
slots `projectState` reads are framed out. -/
theorem removeRunnableOnCore_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (hHigh : threadObservable ctx observer tid = false) :
    projectState ctx observer (removeRunnableOnCore st tid c)
      = projectState ctx observer st := by
  by_cases hc : c = bootCoreId
  · subst hc
    rw [removeRunnableOnCore_bootCoreId]
    exact removeRunnable_preserves_projection ctx observer st tid hHigh
  · have hRQ := removeRunnableOnCore_runQueueOnCore_ne st tid c bootCoreId hc
    have hCur := removeRunnableOnCore_currentOnCore_ne st tid c bootCoreId hc
    -- The boot core's domain slots and the machine register file are
    -- definitionally unchanged by a deschedule on another core, so those
    -- `congr` subgoals close by `rfl`; only the run-queue and current-thread
    -- slots need their explicit frame lemmas.
    have hMach : (removeRunnableOnCore st tid c).machine = st.machine := rfl
    simp only [projectState]
    congr 1 <;>
      first
        | rfl
        | simp only [projectRunnable, projectCurrent, projectMachineRegs,
            SchedulerState.runnable, hRQ, hCur, hMach]

/-- WS-SM SM6.A.7: enqueuing a **non-observable** thread onto *any* core's run
queue (the receiver wake) preserves the low-observer projection.  The
`ipcState := .ready` write lands on the high receiver TCB (invisible to
`projectObjects`); the run-queue insert lands on a high thread (invisible to
`projectRunnable`, whether the target is the boot core or a remote core). -/
theorem enqueueRunnableOnCore_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hHighThread : threadObservable ctx observer tid = false)
    (hHighObj : objectObservable ctx observer tid.toObjId = false)
    (hObjInv : st.objects.invExt) :
    projectState ctx observer (enqueueRunnableOnCore st c tid)
      = projectState ctx observer st := by
  obtain hTcb | ⟨tcb, hTcb⟩ : st.getTcb? tid = none ∨ ∃ tcb, st.getTcb? tid = some tcb := by
    cases st.getTcb? tid with
    | none => exact Or.inl rfl
    | some t => exact Or.inr ⟨t, rfl⟩
  · simp only [enqueueRunnableOnCore, hTcb]
  · simp only [enqueueRunnableOnCore, hTcb]
    split
    · rfl
    · simp only [projectState]
      congr 1
      · exact projectObjects_insert_high ctx observer st _ tid
          (.tcb { tcb with ipcState := .ready }) rfl hHighObj hObjInv
      case _ =>
        simp only [projectRunnable, SchedulerState.runnable]
        by_cases hc : c = bootCoreId
        · subst hc; rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
          exact RunQueue.toList_filter_insert_neg' _ _ _ _ hHighThread
        · rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hc]
      all_goals
        first
          | rfl
          | simp only [projectCurrent, projectMachineRegs, projectActiveDomain,
              projectDomainTimeRemaining, projectDomainSchedule, projectDomainScheduleIndex,
              SchedulerState.setRunQueueOnCore_currentOnCore,
              SchedulerState.setRunQueueOnCore_activeDomainOnCore,
              SchedulerState.setRunQueueOnCore_domainTimeRemainingOnCore,
              SchedulerState.setRunQueueOnCore_domainScheduleIndexOnCore,
              SchedulerState.setRunQueueOnCore_domainSchedule]

/-- WS-SM SM6.A.7: the cross-core receiver wake (`wakeThread`) preserves the
low-observer projection for a high receiver. -/
theorem wakeThread_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (tid : SeLe4n.ThreadId) (executingCore : CoreId)
    (hHighThread : threadObservable ctx observer tid = false)
    (hHighObj : objectObservable ctx observer tid.toObjId = false)
    (hObjInv : st.objects.invExt) :
    projectState ctx observer (wakeThread st tid executingCore).1
      = projectState ctx observer st := by
  rw [wakeThread_state_eq_enqueue]
  exact enqueueRunnableOnCore_preserves_projection ctx observer st
    (determineTargetCore st tid) tid hHighThread hHighObj hObjInv

-- ============================================================================
-- §3  SM6.A.7 — `endpointCall_call_path_NI` (cross-core variant)
-- ============================================================================

/-- WS-SM SM6.A.7 (`endpointCall_call_path_NI`, cross-core variant): a
cross-core endpoint call at a **non-observable** endpoint, between a
non-observable caller and a non-observable receiver, is invisible to a low
observer — `projectState` of the post-state equals that of the pre-state.  No
covert channel is opened across cores by the rendezvous: the message transfer,
the receiver wake (routed to a remote core), and the caller block all touch
only high state. -/
theorem endpointCallOnCore_call_path_NI
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) (ep : Endpoint)
    (receiver : SeLe4n.ThreadId) (recvTcb0 : TCB) (st' st'' st4 : SystemState)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hHead : ep.receiveQ.head = some receiver)
    (hPop : endpointQueuePopHead endpointId true st = .ok (receiver, recvTcb0, st'))
    (hStore : storeTcbIpcStateAndMessage st' receiver .ready (some msg) = .ok st'')
    (hCallerStore : storeTcbIpcStateAndMessage (wakeThread st'' receiver executingCore).1
        caller (.blockedOnReply endpointId (some receiver)) none = .ok st4)
    (hObjInv : st.objects.invExt)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hReceiverHigh : threadObservable ctx observer receiver = false)
    (hReceiverObjHigh : objectObservable ctx observer receiver.toObjId = false)
    (hCallerHigh : threadObservable ctx observer caller = false)
    (hCallerObjHigh : objectObservable ctx observer caller.toObjId = false)
    (hNextHigh : ∀ nextTid, recvTcb0.queueNext = some nextTid →
        objectObservable ctx observer nextTid.toObjId = false) :
    projectState ctx observer (endpointCallOnCore endpointId caller msg executingCore st).1
      = projectState ctx observer st := by
  have hInv' : st'.objects.invExt :=
    endpointQueuePopHead_preserves_objects_invExt endpointId true st st' receiver recvTcb0 hObjInv hPop
  have hInv'' : st''.objects.invExt :=
    storeTcbIpcStateAndMessage_preserves_objects_invExt st' st'' receiver .ready (some msg) hInv' hStore
  rw [endpointCallOnCore_rendezvous_eq endpointId caller msg executingCore st ep receiver
        recvTcb0 st' st'' st4 hSz1 hSz2 hObj hHead hPop hStore hCallerStore]
  show projectState ctx observer (removeRunnableOnCore st4 caller executingCore)
    = projectState ctx observer st
  rw [removeRunnableOnCore_preserves_projection ctx observer st4 caller executingCore hCallerHigh,
      storeTcbIpcStateAndMessage_preserves_projection ctx observer
        (wakeThread st'' receiver executingCore).1 st4 caller
        (.blockedOnReply endpointId (some receiver)) none hCallerObjHigh
        (wakeThread_preserves_objects_invExt st'' receiver executingCore hInv'') hCallerStore,
      wakeThread_preserves_projection ctx observer st'' receiver executingCore
        hReceiverHigh hReceiverObjHigh hInv'',
      storeTcbIpcStateAndMessage_preserves_projection ctx observer st' st'' receiver .ready
        (some msg) hReceiverObjHigh hInv' hStore]
  exact endpointQueuePopHead_preserves_projection ctx observer endpointId true st st' receiver
    recvTcb0 hEndpointHigh hReceiverObjHigh hNextHigh hObjInv hPop

end SeLe4n.Kernel
