-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.MappingRecordStage.SchedulingPoint

/-! # The fault delivery keeps the mappings recorded

A fault is delivered as a call to the thread's fault handler, or the thread is
suspended fail-closed; then the woken handler's frame is staged and the fault
recorded.  Each step is a call, a run-queue removal or a thread rewrite that
keeps the thread's space slots, so each is a `MappingStage`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState (MappingStage)
open SeLe4n.Kernel.Concurrency (CoreId)

theorem faultSuspendOnCore_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) :
    MappingStage st (faultSuspendOnCore st tid c) :=
  (removeRunnableOnCore_mappingStage st tid c).trans (updateTcb_mappingStage _ _ _)

theorem recordPendingFault_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (tf : ThreadFault) : MappingStage st (recordPendingFault st tid tf) :=
  updateTcb_mappingStage _ _ _

theorem writeFaultRegistersToTcb_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (w : FaultRegisterWindow) : MappingStage st (writeFaultRegistersToTcb st tid w) :=
  updateTcb_mappingStage _ _ _

/-- **The fault delivery keeps the mappings recorded**: the handler call, or
the fail-closed suspend; then the woken handler's frame and the fault record. -/
theorem faultDeliverOnCore_mappingStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (f : Fault) (fctx : FaultContext) (c : CoreId) :
    MappingStage st (faultDeliverOnCore st tid f fctx c).1 := by
  have sus := (faultSuspendOnCore_mappingStage st tid c).trans
    (recordPendingFault_mappingStage _ tid { fault := f, context := fctx })
  unfold faultDeliverOnCore
  split
  · exact sus
  · rename_i tgt _
    have s0 : MappingStage st (endpointCallCrossCoreDispatch tgt.endpoint tid
        (SendPayload.fault f fctx tgt.cap.badge) (SeLe4n.Slot.ofNat 0) c st).1 :=
      endpointCallCrossCoreDispatch_mappingStage
    generalize endpointCallCrossCoreDispatch tgt.endpoint tid
      (SendPayload.fault f fctx tgt.cap.badge) (SeLe4n.Slot.ofNat 0) c st = r at s0 ⊢
    obtain ⟨st1, r⟩ := r
    cases r with
    | error e => exact sus
    | ok res =>
      exact s0.trans ((stageWokenDelivery_mappingStage _ _ _).trans
        (recordPendingFault_mappingStage _ _ _))

/-- The flow-checked fault delivery: the delivery, or the suspend a denied flow
takes. -/
theorem faultDeliverOnCoreChecked_mappingStage (ctx : LabelingContext) (st : SystemState)
    (tid : SeLe4n.ThreadId) (f : Fault) (fctx : FaultContext) (c : CoreId) :
    MappingStage st (faultDeliverOnCoreChecked ctx st tid f fctx c).1 := by
  have sus := (faultSuspendOnCore_mappingStage st tid c).trans
    (recordPendingFault_mappingStage _ tid { fault := f, context := fctx })
  unfold faultDeliverOnCoreChecked
  split
  · exact sus
  · split
    · exact faultDeliverOnCore_mappingStage st tid f fctx c
    · exact sus

end SeLe4n.Kernel
