-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.ReschedulePendingArms.Dispatch
import SeLe4n.Kernel.Scheduler.Invariant.ReschedulePendingSchedulingPoints
import SeLe4n.Kernel.FaultEntry
import SeLe4n.Kernel.SyscallDispatchEntry

/-!
# The committing entries cover

The KSC-1 / HAL-3 row of `docs/REGISTERED_DEBT.md`, PR B2.  The two entries
that commit through the `(pre, post)` reschedule diff — the syscall step and
the fault delivery — are a covered transition followed by the executing core's
own scheduling point, so each covers end to end on the executing core.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind)

/-! ### Fault delivery -/

/-- The fail-closed suspend covers: the faulting thread leaves one core's run
queue, and its thread state is no key. -/
theorem faultSuspendOnCore_stepCovers (e : CoreId) (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) (hInv : st.objects.invExt) :
    stepCovers e st (faultSuspendOnCore st tid c) ∧ (faultSuspendOnCore st tid c).objects.invExt := by
  have hF := updateTcb_keyFrame (removeRunnableOnCore st tid c) tid
    (f := fun tcb => { tcb with threadState := .Inactive }) (fun _ => rfl) (removeRunnableOnCore_objects_invExt st tid c hInv)
  exact ⟨stepCovers_trans (removeRunnableOnCore_stepCovers e st tid c) hF.stepCovers, hF.2.2⟩

theorem recordPendingFault_keyFrame (st : SystemState) (tid : SeLe4n.ThreadId) (tf : ThreadFault)
    (hInv : st.objects.invExt) : capabilityKeyFrame st (recordPendingFault st tid tf) :=
  updateTcb_keyFrame st tid (f := fun tcb => { tcb with pendingFault := some tf, ipcFaultSend := true }) (fun _ => rfl)
    hInv

theorem writeFaultRegistersToTcb_keyFrame (st : SystemState) (tid : SeLe4n.ThreadId)
    (w : FaultRegisterWindow) (hInv : st.objects.invExt) :
    capabilityKeyFrame st (writeFaultRegistersToTcb st tid w) :=
  updateTcb_keyFrame st tid (f := fun tcb => { tcb with registerContext := w.spill tcb.registerContext })
    (fun _ => rfl) hInv

/-- The suspend-and-record disposition covers. -/
theorem faultSuspendRecord_stepCovers (e : CoreId) (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) (tf : ThreadFault) (hInv : st.objects.invExt) :
    stepCovers e st (recordPendingFault (faultSuspendOnCore st tid c) tid tf) ∧
    (recordPendingFault (faultSuspendOnCore st tid c) tid tf).objects.invExt := by
  obtain ⟨hS, hSInv⟩ := faultSuspendOnCore_stepCovers e st tid c hInv
  have hR := recordPendingFault_keyFrame _ tid tf hSInv
  exact ⟨stepCovers_trans hS hR.stepCovers, hR.2.2⟩

/-- **The fault delivery covers**: the Call it composes covers, and the
suspend, record and staging steps around it move no key. -/
theorem faultDeliverOnCore_stepCovers (e : CoreId) {st : SystemState} {tid : SeLe4n.ThreadId}
    {f : Fault} {ctx : FaultContext} {c : CoreId} (hInv : st.objects.invExt) :
    stepCovers e st (faultDeliverOnCore st tid f ctx c).1 ∧
    (faultDeliverOnCore st tid f ctx c).1.objects.invExt := by
  unfold faultDeliverOnCore
  split
  · exact faultSuspendRecord_stepCovers e st tid c _ hInv
  · rename_i tgt _
    dsimp only
    have hC := endpointCallCrossCoreDispatch_stepCovers e (endpointId := tgt.endpoint) (caller := tid)
      (payload := SendPayload.fault f ctx tgt.cap.badge)
      (receiverSlotBase := SeLe4n.Slot.ofNat 0) (executingCore := c) hInv
    generalize endpointCallCrossCoreDispatch tgt.endpoint tid (SendPayload.fault f ctx tgt.cap.badge)
      (SeLe4n.Slot.ofNat 0) c st = r at hC ⊢
    obtain ⟨st1, res⟩ := r
    obtain ⟨hC, hCInv⟩ := hC
    cases res with
    | error _ => exact faultSuspendRecord_stepCovers e st tid c _ hInv
    | ok p =>
      obtain ⟨summary, sgi?⟩ := p
      dsimp only
      have hS := stageWokenDelivery_keyFrame st1 ((st.getEndpoint? tgt.endpoint).bind (·.receiveQ.head))
        summary.installedCount hCInv
      have hR := recordPendingFault_keyFrame _ tid { fault := f, context := ctx } hS.2.2
      exact ⟨stepCovers_trans (stepCovers_trans hC hS.stepCovers) hR.stepCovers, hR.2.2⟩

/-- The flow-checked delivery covers: a denied flow takes the suspend. -/
theorem faultDeliverOnCoreChecked_stepCovers (e : CoreId) {lctx : LabelingContext}
    {st : SystemState} {tid : SeLe4n.ThreadId} {f : Fault} {ctx : FaultContext} {c : CoreId}
    (hInv : st.objects.invExt) :
    stepCovers e st (faultDeliverOnCoreChecked lctx st tid f ctx c).1 ∧
    (faultDeliverOnCoreChecked lctx st tid f ctx c).1.objects.invExt := by
  unfold faultDeliverOnCoreChecked
  split
  · exact faultSuspendRecord_stepCovers e st tid c _ hInv
  · split
    · exact faultDeliverOnCore_stepCovers e hInv
    · exact faultSuspendRecord_stepCovers e st tid c _ hInv

/-- The register spill, then the checked delivery. -/
theorem faultDeliveredState_stepCovers (e : CoreId) {lctx : LabelingContext} {st : SystemState}
    {f : Fault} {ectx : Architecture.ExceptionContext} {w : FaultRegisterWindow} {c : CoreId}
    {tid : SeLe4n.ThreadId} (hInv : st.objects.invExt) :
    stepCovers e st (faultDeliveredState lctx st f ectx w c tid) ∧
    (faultDeliveredState lctx st f ectx w c tid).objects.invExt := by
  unfold faultDeliveredState
  have hW := writeFaultRegistersToTcb_keyFrame st tid w hInv
  obtain ⟨hD, hDInv⟩ := faultDeliverOnCoreChecked_stepCovers e (lctx := lctx) (f := f)
    (ctx := Architecture.faultContextOfThread (writeFaultRegistersToTcb st tid w) tid ectx.elr
      ectx.spsr) (c := c) hW.2.2
  exact ⟨stepCovers_trans hW.stepCovers hD, hDInv⟩

/-! ### Transport across a register write -/

/-- **The register spill keeps the bundle the delete carries**: it rewrites one
thread's register file, which none of the bundle's conjuncts reads. -/
theorem finalisingDeleteBundle_writeFfiRegistersToTcb {st : SystemState} (tid : SeLe4n.ThreadId)
    (syscallId : UInt32) (x0 x1 x2 x3 x4 x5 : UInt64) (hB : finalisingDeleteBundle st) :
    finalisingDeleteBundle
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) := by
  have hInv := hB.1.2.1
  unfold Platform.FFI.writeFfiRegistersToTcb
  refine ⟨⟨?_, SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv,
    hB.1.2.2.of_loanWrite (FinaliseFrame.updateTcb st tid _ hInv).loan⟩,
    (SchedLinkFrame.updateTcb st tid _ hInv).preserves hB.2⟩
  cases hG : st.getTcb? tid with
  | none => rw [SystemState.updateTcb_eq_self_of_none hG]; exact hB.1.1
  | some x =>
    rw [SystemState.updateTcb_eq_of_some hG]
    exact insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull st tid x _ hInv hB.1.1
      ((SystemState.getTcb?_eq_some_iff st tid x).mp hG) rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- A TCB update keeps every placed thread's TCB. -/
theorem placedThreadsHaveTcbs_updateTcb {st : SystemState} {tid : SeLe4n.ThreadId}
    {f : TCB → TCB} (hInv : st.objects.invExt) (hP : placedThreadsHaveTcbs st) :
    placedThreadsHaveTcbs (st.updateTcb tid f) := by
  intro c t ht
  rw [SystemState.updateTcb_scheduler] at ht
  by_cases hEq : tid.toObjId = t.toObjId
  · have hId : tid = t := SeLe4n.ThreadId.toObjId_injective _ _ hEq
    subst hId
    rw [SystemState.updateTcb_getTcb?_self _ _ _ hInv]
    have := hP c tid ht
    cases h : st.getTcb? tid <;> simp_all
  · rw [SystemState.updateTcb_getTcb?_ne _ _ _ hInv _ hEq]; exact hP c t ht

/-! ### The ABI dispatch -/

/-- The argument spill writes registers only. -/
theorem writeFfiRegistersToTcb_keyFrame (st : SystemState) (tid : SeLe4n.ThreadId)
    (syscallId : UInt32) (x0 x1 x2 x3 x4 x5 : UInt64) (hInv : st.objects.invExt) :
    capabilityKeyFrame st
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) := by
  unfold Platform.FFI.writeFfiRegistersToTcb
  exact updateTcb_keyFrame st tid (fun _ => rfl) hInv

/-- **The ABI dispatch covers** on the executing core: the argument spill moves
no key, the checked entry covers, a capability fault is a covered delivery, and
a refusal record touches the refusal ledger alone. -/
theorem syscallDispatchFromAbi_stepCovers {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64}
    {st st' : SystemState} {outcome : Architecture.SyscallOutcome}
    (hInv : st.objects.invExt) (hB : finalisingDeleteBundle st)
    (hPlaced : placedThreadsHaveTcbs st)
    (hAwayCur : ∀ t, st.scheduler.currentOnCore e = some t → ∀ c, st.queuedOn c t = false)
    (h : Platform.FFI.syscallDispatchFromAbi ctx e syscallId x0 x1 x2 x3 x4 x5
      ipcBufferAddr elr spsr spEl0 x30 st = .ok (outcome, st')) :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold Platform.FFI.syscallDispatchFromAbi at h
  split at h
  · cases h; exact ⟨stepCovers_refl e st, hInv⟩
  rename_i tid hCur
  split at h
  · cases h; exact ⟨stepCovers_refl e st, hInv⟩
  have hW := writeFfiRegistersToTcb_keyFrame st tid syscallId x0 x1 x2 x3 x4 x5 hInv
  dsimp only at h
  split at h
  · split at h
    · cases h
      unfold Platform.FFI.deliverSyscallCapFault
      have hF := writeFaultRegistersToTcb_keyFrame _ tid
        (Platform.FFI.syscallWindow syscallId x0 x1 x2 x3 x4 x5 ipcBufferAddr spEl0 x30) hW.2.2
      exact stepCoversInv_trans (stepCovers_trans hW.stepCovers hF.stepCovers)
        (faultDeliverOnCoreChecked_stepCovers e hF.2.2)
    · cases h
      refine stepCoversInv_trans hW.stepCovers (capabilityKeyFrame.stepCoversInv ?_)
      exact capabilityKeyFrame_of_objects_scheduler_eq hW.2.2
        (Platform.FFI.recordSyscallRefusal_objects_eq _ _ _ _ _ _ _)
        (Platform.FFI.recordSyscallRefusal_scheduler_eq _ _ _ _ _ _ _)
  · rename_i hE
    cases h
    have hB' := finalisingDeleteBundle_writeFfiRegistersToTcb tid syscallId x0 x1 x2 x3 x4 x5 hB
    have hPl : placedThreadsHaveTcbs
        (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) := by
      unfold Platform.FFI.writeFfiRegistersToTcb
      exact placedThreadsHaveTcbs_updateTcb hInv hPlaced
    -- The argument spill writes registers alone: no current slot, no queue.
    have hAwayW : ∀ t, (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5
        ).scheduler.currentOnCore e = some t → ∀ c,
        (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5).queuedOn c t =
          false := by
      intro t ht c
      rw [Platform.FFI.writeFfiRegistersToTcb_scheduler] at ht
      rw [Platform.FFI.writeFfiRegistersToTcb_eq_updateTcb,
        (SystemState.RunCoresAgree.updateTcb (f := Platform.FFI.ffiRegisterSpill syscallId x0 x1 x2 x3 x4 x5)
          hInv fun _ => rfl).queuedOn c t]
      exact hAwayCur t ht c
    exact stepCoversInv_trans hW.stepCovers
      (syscallEntryChecked_stepCovers hW.2.2 hB' hPl hAwayW hE)

/-! ### The committing seams

Each seam diffs its pre-state against the state below, so coverage of that pair
is what `computeCrossCoreSgis_mem_flags_of_covers` needs at the seam. -/

/-- **The fault entry covers** on the faulting core: a vacated core's dispatch,
or the delivery followed by the core's own scheduling point. -/
theorem faultEntryDeliver_stepCovers (lctx : LabelingContext) (st : SystemState) (f : Fault)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (c : CoreId)
    (hInv : st.objects.invExt) :
    stepCovers c st (faultEntryDeliver lctx st f ectx w c).2 := by
  unfold faultEntryDeliver
  split
  · exact dispatchVacatedCore_stepCovers c st hInv
  · rename_i tid _
    split
    · exact stepCovers_refl c st
    obtain ⟨hD, hDInv⟩ := faultDeliveredState_stepCovers c (lctx := lctx) (st := st) (f := f)
      (ectx := ectx) (w := w) (c := c) (tid := tid) hInv
    exact stepCovers_trans hD (scheduleLocalSuccessorFrom_stepCovers c (some tid) _ hDInv)

/-- WS-ZA ZA6.7: **the activation covers**: what it writes — the current
thread's yield-to code and two return registers, the context's yield-from code
and consumed count (`KernelObject.withoutYield`), and the core's bank — is no
key input, and it writes no scheduler state. -/
theorem activateThreadOnCore_stepCovers (e c : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) : stepCovers e st (activateThreadOnCore st c) :=
  stepCovers_of_keys_sched
    (keyInputsEq_of_objectsAgreeOffYield (activateThreadOnCore_objectsAgreeOffYield st c hInv))
    (activateThreadOnCore_scheduler st c)

theorem activateThreadAt_stepCovers (e : CoreId) (st : SystemState) (coreId : UInt64)
    (hInv : st.objects.invExt) : stepCovers e st (activateThreadAt st coreId) := by
  unfold activateThreadAt
  split
  · exact activateThreadOnCore_stepCovers e _ st hInv
  · exact stepCovers_refl e st

/-- **The syscall seam covers** on the executing core: the ABI dispatch, the
caller's return staging, the local scheduling point, the residency settlement
and the activation.  (A refused dispatch fires no SGI, so it owes nothing.) -/
theorem syscallDispatchCrossCoreStep_stepCovers {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64}
    {st st' : SystemState} {outcome : Architecture.SyscallOutcome}
    (hInv : st.objects.invExt) (hB : finalisingDeleteBundle st)
    (hPlaced : placedThreadsHaveTcbs st)
    (hAwayCur : ∀ t, st.scheduler.currentOnCore e = some t → ∀ c, st.queuedOn c t = false)
    (h : Platform.FFI.syscallDispatchFromAbi ctx e syscallId x0 x1 x2 x3 x4 x5
      ipcBufferAddr elr spsr spEl0 x30 st = .ok (outcome, st')) :
    stepCovers e st (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore
      (PriorityInheritance.scheduleLocalSuccessor st
        (Architecture.stageCallerReturn st st' e outcome) e) e) e) := by
  obtain ⟨hD, hDInv⟩ := syscallDispatchFromAbi_stepCovers hInv hB hPlaced hAwayCur h
  have hSInv := settleResidencyOnCore_preserves_objects_invExt e _
    (scheduleLocalSuccessorFrom_preserves_objects_invExt e (st.scheduler.currentOnCore e) _
      (stageCallerReturnFor_stepCovers e (st.scheduler.currentOnCore e) st' outcome hDInv).2)
  exact stepCovers_trans (stepCovers_trans hD
    (syscallCommitTail_stepCovers e (st.scheduler.currentOnCore e) st' outcome hDInv))
    (activateThreadOnCore_stepCovers e e _ hSInv)

/-! ### The seams fire from the flags, and the flags cover the diff

Each seam now emits `rescheduleSgisFromFlags` over the flags it captured before
the step.  The diff `computeCrossCoreSgis` stays as the specification: every
core it names is poked by the seam, or its reschedule SGI was already
outstanding when the step began.  (The converse — the flags name only cores the
diff names — is not claimed: the flags deliberately over-approximate.) -/

/-- The fault entry's SGIs are the flags it raised. -/
theorem faultEntryDeliver_sgis_eq_flags (lctx : LabelingContext) (st : SystemState) (f : Fault)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (c : CoreId) :
    (faultEntryDeliver lctx st f ectx w c).1 =
      rescheduleSgisFromFlags st.scheduler.reschedulePending
        (faultEntryDeliver lctx st f ectx w c).2.scheduler.reschedulePending := by
  unfold faultEntryDeliver
  split
  · rfl
  · split
    · exact (rescheduleSgisFromFlags_nil_of_eq _).symm
    · rfl

/-- **The fault entry fires every SGI the diff names**, unless it was already
outstanding. -/
theorem faultEntryDeliver_sgis_cover_diff (lctx : LabelingContext) (st : SystemState) (f : Fault)
    (ectx : Architecture.ExceptionContext) (w : FaultRegisterWindow) (c : CoreId)
    (hInv : st.objects.invExt)
    (hId : ∀ oid (tcb : TCB), (faultEntryDeliver lctx st f ectx w c).2.getObject? oid =
      some (.tcb tcb) → tcb.tid.toObjId = oid)
    {c' : CoreId} {k : SgiKind}
    (hMem : (c', k) ∈ PriorityInheritance.computeCrossCoreSgis st (faultEntryDeliver lctx st f ectx w c).2 c) :
    (c', SgiKind.reschedule) ∈ (faultEntryDeliver lctx st f ectx w c).1 ∨
      st.scheduler.reschedulePendingOnCore c' = true := by
  rw [faultEntryDeliver_sgis_eq_flags]
  exact computeCrossCoreSgis_mem_flags_of_covers hId
    (faultEntryDeliver_stepCovers lctx st f ectx w c hInv).1 hMem

/-- **The syscall step fires every SGI the diff names**, unless it was already
outstanding: the diff is taken between the pre-state and the state the commit
settles to. -/
theorem syscallDispatchCrossCoreStep_sgis_cover_diff {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64}
    {st st' : SystemState} {outcome : Architecture.SyscallOutcome}
    (hInv : st.objects.invExt) (hB : finalisingDeleteBundle st)
    (hPlaced : placedThreadsHaveTcbs st)
    (hAwayCur : ∀ t, st.scheduler.currentOnCore e = some t → ∀ c, st.queuedOn c t = false)
    (h : Platform.FFI.syscallDispatchFromAbi ctx e syscallId x0 x1 x2 x3 x4 x5
      ipcBufferAddr elr spsr spEl0 x30 st = .ok (outcome, st'))
    (hId : ∀ oid (tcb : TCB), (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore
      (PriorityInheritance.scheduleLocalSuccessor st
        (Architecture.stageCallerReturn st st' e outcome) e) e) e).getObject? oid =
      some (.tcb tcb) → tcb.tid.toObjId = oid)
    {c : CoreId} {k : SgiKind}
    (hMem : (c, k) ∈ PriorityInheritance.computeCrossCoreSgis st
      (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore
        (PriorityInheritance.scheduleLocalSuccessor st
          (Architecture.stageCallerReturn st st' e outcome) e) e) e) e) :
    (c, SgiKind.reschedule) ∈ sgisOfRaised (syscallDispatchCrossCoreStep ctx e syscallId x0 x1 x2
        x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 st).1.2.1 ∨
      st.scheduler.reschedulePendingOnCore c = true := by
  rw [syscallDispatchCrossCoreStep_of_ok h]
  dsimp only
  rw [← rescheduleSgisFromFlags_eq_sgisOfRaised]
  exact computeCrossCoreSgis_mem_flags_of_covers hId
    (syscallDispatchCrossCoreStep_stepCovers hInv hB hPlaced hAwayCur h).1 hMem

end SeLe4n.Kernel
