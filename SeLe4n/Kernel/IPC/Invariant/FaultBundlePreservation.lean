-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.Fault
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDispatchInvariant
import SeLe4n.Kernel.IPC.Invariant.DispatchArmPreservation

/-!
# WS-RR RR8.16 (`v0.35.200`) — the fault path carries the scheduler and capability bundles

The composition register row 85 is named for.  `faultDeliverOnCore` composes the
live cross-core `.call` chain and `faultReplyOnCore` the live `.reply` chain, so
until both chains carried the two *cross-subsystem* bundles themselves the fault
path could not compose what its substrate lacked.  `v0.35.197` built the frames,
`v0.35.199` the reply chain, `v0.35.200` the call chain — and this module is the
join.

## Why this is not `IPC/Invariant/FaultPreservation.lean`

That module holds the fault path's `ipcInvariantFull` surface and is **staged**,
because the delivery's `ipcInvariantFull` composes the staged
`EndpointCallInvariant` / `DispatchInvariant` call-chain bundle.  Every theorem
here composes *production* facts only — the call chain's two bundle lifts landed
in the production `IPC/CrossCore/EndpointCallDispatch.lean`, the reply chain's in
the production `IPC/CrossCore/EndpointReplyDispatchInvariant.lean` — so putting
them there would make them uncitable from production code, which is the very
shape row 85 records: *a lift that exists and cannot be reached is a lift the
consumer does not have.*  The four fault-path `_preserves_objects_invExt` frames
moved out of that module in the same cut, for the same reason.

## The two lifts take different preconditions, and the asymmetry is the claim

The **capability** bundle reads the object store and the two derivation tables.
Every fault-path write is a TCB rewrite (`updateTcb`) or a deschedule, and the
chains are kind-preserving outside `ipcUnwrapCaps` — which **neither** fault
transition reaches, the delivery because `faultMessage` carries no capabilities
and the reply because its payload is registers.  So both capability lifts are
unconditional, where the *general* caps-carrying `.call` chain reduces its bundle
to that one step (`ipcUnwrapCapsPreservesCapabilityBundle`).

The **scheduler** bundle reads `currentOnCore`, so it inherits each chain's
`hNotCur`: the delivery takes `endpointReceiveHeadsNotCurrent` (the state-level
form, since the handler endpoint comes from `resolveFaultHandler` and no caller
can name it), and the reply takes the answered thread's own.  Both are *stated
rather than derived*, for the reason `v0.35.199` recorded: what would turn
"blocked" into "not current" is a per-core current-thread-IPC-readiness
discipline this tree states at the boot core alone.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind)

-- ============================================================================
-- §1 The fail-closed dispositions
-- ============================================================================

/-- **WS-RR RR8.16** (`v0.35.200`): the fail-closed suspend preserves the base SMP
scheduler invariant — the deschedule is a placement removal and the `.Inactive`
store writes no scheduler state. -/
theorem faultSuspendOnCore_preserves_schedulerInvariantBase_smp (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) (hObjInv : st.objects.invExt)
    (h : schedulerInvariantBase_smp st) :
    schedulerInvariantBase_smp (faultSuspendOnCore st tid c) :=
  schedulerInvariantBase_smp_of_kindPreserving
    (removeRunnableOnCore_preserves_schedulerInvariantBase_smp tid c h)
    (faultSuspendOnCore_scheduler_eq st tid c)
    (by
      unfold faultSuspendOnCore
      exact SystemState.updateTcb_kindPreservingWrite _ tid _
        hObjInv)

/-- **WS-RR RR8.16** (`v0.35.200`): ...and the capability bundle. -/
theorem faultSuspendOnCore_preserves_capabilityInvariantBundle (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) (h : capabilityInvariantBundle st) :
    capabilityInvariantBundle (faultSuspendOnCore st tid c) := by
  have hObjInv : st.objects.invExt := h.2.2.2.2.2.1
  have hCdt := faultSuspendOnCore_cdt_eq st tid c
  exact capabilityInvariantBundle_of_kindPreserving h hCdt.2 hCdt.1
    (faultSuspendOnCore_preserves_objects_invExt st tid c hObjInv)
    (faultSuspendOnCore_kindPreservingWrite st tid c hObjInv)

/-- **WS-RR RR8.16** (`v0.35.200`): the reply-declined disposition, same shape —
it adds only the `pendingFault` clear to the suspend's writes. -/
theorem faultAbandonOnCore_preserves_schedulerInvariantBase_smp (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) (hObjInv : st.objects.invExt)
    (h : schedulerInvariantBase_smp st) :
    schedulerInvariantBase_smp (faultAbandonOnCore st tid c) :=
  schedulerInvariantBase_smp_of_kindPreserving
    (removeRunnableOnCore_preserves_schedulerInvariantBase_smp tid c h)
    (faultAbandonOnCore_scheduler_eq st tid c)
    (by
      unfold faultAbandonOnCore
      exact SystemState.updateTcb_kindPreservingWrite _ tid _
        hObjInv)

/-- **WS-RR RR8.16** (`v0.35.200`): ...and the capability bundle. -/
theorem faultAbandonOnCore_preserves_capabilityInvariantBundle (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) (h : capabilityInvariantBundle st) :
    capabilityInvariantBundle (faultAbandonOnCore st tid c) := by
  have hObjInv : st.objects.invExt := h.2.2.2.2.2.1
  have hCdt := faultAbandonOnCore_cdt_eq st tid c
  exact capabilityInvariantBundle_of_kindPreserving h hCdt.2 hCdt.1
    (faultAbandonOnCore_preserves_objects_invExt st tid c hObjInv)
    (faultAbandonOnCore_kindPreservingWrite st tid c hObjInv)

/-- **WS-RR RR8.16** (`v0.35.200`): and the decoded outcome, whichever arm it
takes — the restart is a TCB rewrite, the abandon the disposition above. -/
theorem faultReplyApplyOnCore_preserves_schedulerInvariantBase_smp (st : SystemState)
    (faulted : SeLe4n.ThreadId) (outcome : Architecture.FaultReplyOutcome)
    (hObjInv : st.objects.invExt) (h : schedulerInvariantBase_smp st) :
    schedulerInvariantBase_smp (faultReplyApplyOnCore st faulted outcome) := by
  unfold faultReplyApplyOnCore
  cases outcome with
  | restart frame =>
      exact schedulerInvariantBase_smp_of_kindPreserving h
        (applyFaultRestart_scheduler_eq st faulted frame)
        (applyFaultRestart_kindPreservingWrite st faulted frame hObjInv)
  | abandon =>
      exact faultAbandonOnCore_preserves_schedulerInvariantBase_smp st faulted _ hObjInv h

/-- **WS-RR RR8.16** (`v0.35.200`): ...and the capability bundle. -/
theorem faultReplyApplyOnCore_preserves_capabilityInvariantBundle (st : SystemState)
    (faulted : SeLe4n.ThreadId) (outcome : Architecture.FaultReplyOutcome)
    (h : capabilityInvariantBundle st) :
    capabilityInvariantBundle (faultReplyApplyOnCore st faulted outcome) := by
  have hObjInv : st.objects.invExt := h.2.2.2.2.2.1
  unfold faultReplyApplyOnCore
  cases outcome with
  | restart frame =>
      have hCdt := applyFaultRestart_cdt_eq st faulted frame
      exact capabilityInvariantBundle_of_kindPreserving h hCdt.2 hCdt.1
        (applyFaultRestart_preserves_objects_invExt st faulted frame hObjInv)
        (applyFaultRestart_kindPreservingWrite st faulted frame hObjInv)
  | abandon => exact faultAbandonOnCore_preserves_capabilityInvariantBundle st faulted _ h

-- ============================================================================
-- §2 The fault delivery
-- ============================================================================

/-- **WS-RR RR8.16** (`v0.35.200`): **the fault delivery preserves the base SMP
scheduler invariant**, on both dispositions.

Three shapes, and each is a citation: the fail-closed arm is the deschedule plus
the fault record, the delivered arm is the live `.call` chain plus the woken
handler's return-frame staging plus the record, and the record itself writes one
TCB field.  `endpointReceiveHeadsNotCurrent` is the call chain's own `hNotCur` in
the one form a caller can supply here — the handler endpoint is resolved
*inside* the transition. -/
theorem faultDeliverOnCore_preserves_schedulerInvariantBase_smp (st : SystemState)
    (tid : SeLe4n.ThreadId) (f : Fault) (ctx : FaultContext) (executingCore : CoreId)
    (hObjInv : st.objects.invExt)
    (hHeads : endpointReceiveHeadsNotCurrent st)
    (h : schedulerInvariantBase_smp st) :
    schedulerInvariantBase_smp (faultDeliverOnCore st tid f ctx executingCore).1 := by
  have hSusp := faultSuspendOnCore_preserves_schedulerInvariantBase_smp st tid executingCore
    hObjInv h
  have hSuspObj := faultSuspendOnCore_preserves_objects_invExt st tid executingCore hObjInv
  have hFail : ∀ tf : ThreadFault,
      schedulerInvariantBase_smp
        (recordPendingFault (faultSuspendOnCore st tid executingCore) tid tf) := fun tf =>
    schedulerInvariantBase_smp_of_kindPreserving hSusp
      (recordPendingFault_scheduler_eq _ tid tf)
      (recordPendingFault_kindPreservingWrite _ tid tf hSuspObj)
  unfold faultDeliverOnCore
  cases hRes : resolveFaultHandler st tid with
  | error e => exact hFail _
  | ok tgt =>
      simp only
      cases hCall : endpointCallCrossCoreDispatch tgt.endpoint tid
          (faultMessage f ctx tgt.cap.badge) tgt.cap.rights
          (SeLe4n.Slot.ofNat 0) executingCore st with
      | mk stC resC =>
          have hC := endpointCallCrossCoreDispatch_preserves_schedulerInvariantBase_smp
            tgt.endpoint tid (faultMessage f ctx tgt.cap.badge) tgt.cap.rights
            (SeLe4n.Slot.ofNat 0) executingCore st hObjInv
            (endpointReceiveHeadsNotCurrent_at hHeads tgt.endpoint) h
          have hCObj := endpointCallCrossCoreDispatch_preserves_objects_invExt
            tgt.endpoint tid (faultMessage f ctx tgt.cap.badge) tgt.cap.rights
            (SeLe4n.Slot.ofNat 0) executingCore st hObjInv
          rw [hCall] at hC hCObj
          simp only at hC hCObj
          cases resC with
          | error e => exact hFail _
          | ok r =>
              obtain ⟨summary, sgi?⟩ := r
              simp only
              have hStage : schedulerInvariantBase_smp
                  (Architecture.stageWokenDelivery stC
                    ((st.getEndpoint? tgt.endpoint).bind (·.receiveQ.head))
                    summary.installedCount) :=
                schedulerInvariantBase_smp_of_kindPreserving hC
                  (Architecture.stageWokenDelivery_scheduler_eq stC _ _)
                  (Architecture.stageWokenDelivery_kindPreservingWrite stC _ _ hCObj)
              exact schedulerInvariantBase_smp_of_kindPreserving hStage
                (recordPendingFault_scheduler_eq _ tid _)
                (recordPendingFault_kindPreservingWrite _ tid _
                  (stageWokenDelivery_preserves_objects_invExt stC _ _ hCObj))

/-- **WS-RR RR8.16** (`v0.35.200`): ...and the **capability invariant bundle**,
with **no** hypothesis at all.

The `.call` chain's capability lift reduces to `ipcUnwrapCaps`'s, and a fault
delivery never reaches that step: `faultMessage` carries `caps := #[]`
(`faultMessage_caps_empty`) and `endpointCallWithCapsOnCore` short-circuits on
`msg.caps.isEmpty` *before* it resolves the receiver's CSpace root.  So the
delivery composes the **no-caps** form and owes nothing — which is the honest
reading of "a fault's payload is registers", one step further than the reply
side needed it. -/
theorem faultDeliverOnCore_preserves_capabilityInvariantBundle (st : SystemState)
    (tid : SeLe4n.ThreadId) (f : Fault) (ctx : FaultContext) (executingCore : CoreId)
    (h : capabilityInvariantBundle st) :
    capabilityInvariantBundle (faultDeliverOnCore st tid f ctx executingCore).1 := by
  have hObjInv : st.objects.invExt := h.2.2.2.2.2.1
  have hSusp := faultSuspendOnCore_preserves_capabilityInvariantBundle st tid executingCore h
  have hSuspObj := faultSuspendOnCore_preserves_objects_invExt st tid executingCore hObjInv
  have hFail : ∀ tf : ThreadFault,
      capabilityInvariantBundle
        (recordPendingFault (faultSuspendOnCore st tid executingCore) tid tf) := fun tf =>
    capabilityInvariantBundle_of_kindPreserving hSusp
      (recordPendingFault_cdt_eq _ tid tf).2 (recordPendingFault_cdt_eq _ tid tf).1
      (recordPendingFault_preserves_objects_invExt _ tid tf hSuspObj)
      (recordPendingFault_kindPreservingWrite _ tid tf hSuspObj)
  unfold faultDeliverOnCore
  cases hRes : resolveFaultHandler st tid with
  | error e => exact hFail _
  | ok tgt =>
      simp only
      cases hCall : endpointCallCrossCoreDispatch tgt.endpoint tid
          (faultMessage f ctx tgt.cap.badge) tgt.cap.rights
          (SeLe4n.Slot.ofNat 0) executingCore st with
      | mk stC resC =>
          have hC := endpointCallCrossCoreDispatch_preserves_capabilityInvariantBundle_of_no_caps
            tgt.endpoint tid (faultMessage f ctx tgt.cap.badge) tgt.cap.rights
            (SeLe4n.Slot.ofNat 0) executingCore st (faultMessage_caps_empty f ctx tgt.cap.badge) h
          have hCObj := endpointCallCrossCoreDispatch_preserves_objects_invExt
            tgt.endpoint tid (faultMessage f ctx tgt.cap.badge) tgt.cap.rights
            (SeLe4n.Slot.ofNat 0) executingCore st hObjInv
          rw [hCall] at hC hCObj
          simp only at hC hCObj
          cases resC with
          | error e => exact hFail _
          | ok r =>
              obtain ⟨summary, sgi?⟩ := r
              simp only
              have hStageObj := stageWokenDelivery_preserves_objects_invExt stC
                ((st.getEndpoint? tgt.endpoint).bind (·.receiveQ.head))
                summary.installedCount hCObj
              have hStage : capabilityInvariantBundle
                  (Architecture.stageWokenDelivery stC
                    ((st.getEndpoint? tgt.endpoint).bind (·.receiveQ.head))
                    summary.installedCount) :=
                capabilityInvariantBundle_of_kindPreserving hC
                  (Architecture.stageWokenDelivery_cdt_eq stC _ _).2
                  (Architecture.stageWokenDelivery_cdt_eq stC _ _).1
                  hStageObj
                  (Architecture.stageWokenDelivery_kindPreservingWrite stC _ _ hCObj)
              exact capabilityInvariantBundle_of_kindPreserving hStage
                (recordPendingFault_cdt_eq _ tid _).2 (recordPendingFault_cdt_eq _ tid _).1
                (recordPendingFault_preserves_objects_invExt _ tid _ hStageObj)
                (recordPendingFault_kindPreservingWrite _ tid _ hStageObj)

-- ============================================================================
-- §3 The fault reply
-- ============================================================================

/-- **WS-RR RR8.16** (`v0.35.200`): **the fault reply preserves the base SMP
scheduler invariant** — the live `.reply` chain, then the decoded outcome.

`hNotCur` is the reply chain's own, at the answered thread: a fault reply unblocks
the faulted thread exactly as an ordinary reply unblocks its caller. -/
theorem faultReplyOnCore_preserves_schedulerInvariantBase_smp
    (replier faulted : SeLe4n.ThreadId) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) (executingCore : CoreId) (st : SystemState)
    (hObjInv : st.objects.invExt)
    (hNotCur : st.scheduler.currentOnCore (determineTargetCore st faulted) ≠ some faulted)
    (h : schedulerInvariantBase_smp st) :
    schedulerInvariantBase_smp (faultReplyOnCore replier faulted mi regs executingCore st).1 := by
  unfold faultReplyOnCore
  cases hT : st.getTcb? faulted with
  | none => exact h
  | some tcb =>
      simp only
      cases hF : tcb.pendingFault with
      | none => exact h
      | some tf =>
          simp only
          have hRep := endpointReplyCrossCoreDispatch_preserves_schedulerInvariantBase_smp
            replier faulted IpcMessage.empty executingCore st hObjInv hNotCur h
          have hRepObj := endpointReplyCrossCoreDispatch_preserves_objects_invExt
            replier faulted IpcMessage.empty executingCore st hObjInv
          cases hRepEq : endpointReplyCrossCoreDispatch replier faulted IpcMessage.empty
              executingCore st with
          | mk stR resR =>
              rw [hRepEq] at hRep hRepObj
              simp only at hRep hRepObj
              cases resR with
              | error e => exact h
              | ok sgi? =>
                  simp only
                  exact faultReplyApplyOnCore_preserves_schedulerInvariantBase_smp stR faulted
                    _ hRepObj hRep

/-- **WS-RR RR8.16** (`v0.35.200`): ...and the **capability invariant bundle**,
with **no** premises at all.

That is the difference between a chain that installs capabilities and one that
does not: the reply carries `IpcMessage.empty` and its payload is *registers*, so
no step of the fault reply reaches `ipcUnwrapCaps` and the whole composition is a
kind-preserving write of TCBs. -/
theorem faultReplyOnCore_preserves_capabilityInvariantBundle
    (replier faulted : SeLe4n.ThreadId) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) (executingCore : CoreId) (st : SystemState)
    (h : capabilityInvariantBundle st) :
    capabilityInvariantBundle (faultReplyOnCore replier faulted mi regs executingCore st).1 := by
  have hObjInv : st.objects.invExt := h.2.2.2.2.2.1
  unfold faultReplyOnCore
  cases hT : st.getTcb? faulted with
  | none => exact h
  | some tcb =>
      simp only
      cases hF : tcb.pendingFault with
      | none => exact h
      | some tf =>
          simp only
          have hRep := endpointReplyCrossCoreDispatch_preserves_capabilityInvariantBundle
            replier faulted IpcMessage.empty executingCore st hObjInv h
          cases hRepEq : endpointReplyCrossCoreDispatch replier faulted IpcMessage.empty
              executingCore st with
          | mk stR resR =>
              rw [hRepEq] at hRep
              simp only at hRep
              cases resR with
              | error e => exact h
              | ok sgi? =>
                  simp only
                  exact faultReplyApplyOnCore_preserves_capabilityInvariantBundle stR faulted _
                    hRep

end SeLe4n.Kernel
