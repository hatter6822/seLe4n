-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.EndpointWaiters.Ipc
import SeLe4n.Kernel.KernelRecords.Fault

/-! # The fault delivery: a creator

WS-SX SX11.2.  A fault is delivered as a call to the thread's handler, so it
blocks at most the faulting thread, on the handler's endpoint; the suspend a
missing handler or a denied flow takes, and the record of the fault, write no
IPC state.  The checked delivery checks `endpointFlowGate` on the thread and
the handler's endpoint, two-way, before the call, so the new waiter has the
endpoint's label.  The proofs follow the records' own
(`KernelRecords/Fault.lean`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)
-- ============================================================================
-- The fault delivery
-- ============================================================================

namespace EndpointWaitersFrame

/-- **The fail-closed suspend and the record** move no thread onto an
endpoint: the suspend writes the thread's scheduling state, the record its
fault, and neither its IPC state. -/
theorem faultSuspendRecord (st : SystemState) (t : SeLe4n.ThreadId) (c : CoreId)
    (tf : ThreadFault) (hInv : st.objects.invExt) :
    EndpointWaitersFrame st (_root_.SeLe4n.Kernel.recordPendingFault
      (_root_.SeLe4n.Kernel.faultSuspendOnCore st t c) t tf) := by
  unfold _root_.SeLe4n.Kernel.recordPendingFault _root_.SeLe4n.Kernel.faultSuspendOnCore
  exact ((of_frame (RecordsFrame.removeRunnableOnCore st t c hInv)).andThen fun h =>
    updateTcb _ t (f := fun tcb => { tcb with threadState := .Inactive }) h
      fun _ => TcbWaitsKept.of_ipc rfl).andThen fun h =>
    updateTcb _ t (f := fun tcb => { tcb.setPendingFault (some tf) with ipcFaultSend := true }) h
      fun _ => TcbWaitsKept.of_ipc rfl

end EndpointWaitersFrame

namespace EndpointWaitersGrowFrame

/-- **The fault delivery to a resolved handler blocks at most the faulting
thread, on the handler's endpoint**: it is the handler call, or the suspend. -/
theorem faultDeliverOnCore {lend : Bool} {st : SystemState} {t : SeLe4n.ThreadId} {f : Fault}
    {fctx : FaultContext} {c : CoreId} {tgt : FaultHandlerTarget} (hInv : st.objects.invExt)
    (hR : resolveFaultHandler st t = .ok tgt) :
    EndpointWaitersGrowFrame t tgt.endpoint st
      (_root_.SeLe4n.Kernel.faultDeliverOnCore st t f fctx c lend).1 := by
  have sus := (EndpointWaitersFrame.faultSuspendRecord st t c { fault := f, context := fctx } hInv).growAt
    t tgt.endpoint
  unfold _root_.SeLe4n.Kernel.faultDeliverOnCore
  rw [hR]
  dsimp only
  have S := endpointCallCrossCoreDispatch (endpointId := tgt.endpoint) (caller := t)
    (payload := .fault f fctx tgt.cap.badge tgt.cap.canLinkReply) (c := c) (lend := lend) hInv
  generalize _root_.SeLe4n.Kernel.endpointCallCrossCoreDispatch tgt.endpoint t
    (.fault f fctx tgt.cap.badge tgt.cap.canLinkReply) c st lend = r at S ⊢
  obtain ⟨st1, res⟩ := r
  dsimp only at S ⊢
  cases res with
  | error _ => exact sus
  | ok v =>
    dsimp only
    exact (S.thenFrame (.of_frame (RecordsFrame.stageWokenDelivery st1 _ _ S.invExt))).andThen
      fun h => .updateTcb _ t (f := fun tcb =>
        { tcb.setPendingFault (some { fault := f, context := fctx }) with ipcFaultSend := true }) h
        fun _ => TcbWaitsKept.of_ipc rfl

end EndpointWaitersGrowFrame

namespace EndpointWaitersStage

variable {ctx : LabelingContext}

/-- **The checked fault delivery carries the waiters' labels**: its gate, two
way between the faulting thread and the handler's endpoint, gives the thread
the endpoint's label before the handler call can block it; a denied flow
suspends. -/
theorem faultDeliverOnCoreChecked {st : SystemState} {t : SeLe4n.ThreadId} {f : Fault}
    {fctx : FaultContext} {c : CoreId} (hInv : st.objects.invExt) :
    EndpointWaitersStage ctx st (_root_.SeLe4n.Kernel.faultDeliverOnCoreChecked ctx st t f fctx c).1 := by
  have sus := (EndpointWaitersFrame.faultSuspendRecord st t c { fault := f, context := fctx } hInv).stage
    (ctx := ctx)
  unfold _root_.SeLe4n.Kernel.faultDeliverOnCoreChecked
  split
  · exact sus
  · rename_i tgt hR
    split
    · rename_i hGate
      exact (EndpointWaitersGrowFrame.faultDeliverOnCore hInv hR).stage
        (endpointFlowGate_implies_eq ctx tgt.endpoint _ _ hGate)
    · exact sus

end EndpointWaitersStage

end SeLe4n.Kernel
