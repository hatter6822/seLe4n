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
import SeLe4n.Kernel.IPC.CrossCore.InterruptDelivery

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
  updateTcb_keyFrame st tid (f := fun tcb => { tcb.setPendingFault (some tf) with ipcFaultSend := true }) (fun _ => rfl)
    hInv

theorem writeFaultRegistersToTcb_keyFrame (st : SystemState) (tid : SeLe4n.ThreadId)
    (w : FaultRegisterWindow) (hInv : st.objects.invExt) :
    capabilityKeyFrame st (writeFaultRegistersToTcb st tid w) :=
  updateTcb_keyFrame st tid (f := fun tcb => { tcb with registerContext := w.spill tcb.registerContext })
    (fun _ => rfl) hInv

/-! ### The entry's writes keep the residency record

What `resident_frame` reads through the fault and ABI entries' writes
(`machine_chain`): each rewrites a TCB, the refusal ledger or the physical-write
ledger (an error's fifth payload word), never a core's
residency record. -/

theorem recordPendingFault_machine (st : SystemState) (tid : SeLe4n.ThreadId) (tf : ThreadFault) :
    (recordPendingFault st tid tf).machine = st.machine :=
  SystemState.updateTcb_machine _ _ _

theorem writeFaultRegistersToTcb_machine (st : SystemState) (tid : SeLe4n.ThreadId)
    (w : FaultRegisterWindow) : (writeFaultRegistersToTcb st tid w).machine = st.machine :=
  SystemState.updateTcb_machine _ _ _

theorem writeFfiRegistersToTcb_machine (st : SystemState) (tid : SeLe4n.ThreadId)
    (syscallId : UInt32) (x0 x1 x2 x3 x4 x5 x6 : UInt64) :
    (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6).machine =
      st.machine := by
  rw [Platform.FFI.writeFfiRegistersToTcb_eq_updateTcb, SystemState.updateTcb_machine]

/-- The activation writes core `c`'s bank at most: no residency record moves. -/
theorem activateThreadOnCore_residentCode (st : SystemState) (c : CoreId) :
    (activateThreadOnCore st c).machine.residentCode = st.machine.residentCode := by
  rcases activateThreadOnCore_machine st c with h | ⟨w, h⟩ <;> rw [h]
  exact MachineState.modifyRegsOnCore_residentCode _ _ _

macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (recordPendingFault_machine _ _ _).trans ?_; machine_chain))
macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (writeFaultRegistersToTcb_machine _ _ _).trans ?_; machine_chain))
macro_rules | `(tactic| machine_chain) => `(tactic|
  (with_reducible refine (writeFfiRegistersToTcb_machine _ _ _ _ _ _ _ _ _ _).trans ?_;
   machine_chain))
macro_rules | `(tactic| machine_chain) => `(tactic|
  ((first
     | with_reducible refine (Platform.FFI.recordSyscallRefusal_machine_eq _ _ _ _ _ _ _).trans ?_
     | with_reducible refine (Architecture.recordErrorOverflow_machine _ _ _).trans ?_);
   machine_chain))
macro_rules | `(tactic| resident_frame) => `(tactic|
  (rw [activateThreadOnCore_residentCode]))

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
      (payload := SendPayload.fault f ctx tgt.cap.badge tgt.cap.canLinkReply)
      (executingCore := c) hInv
    generalize endpointCallCrossCoreDispatch tgt.endpoint tid (SendPayload.fault f ctx tgt.cap.badge tgt.cap.canLinkReply)
      c st = r at hC ⊢
    obtain ⟨st1, res⟩ := r
    obtain ⟨hC, hCInv⟩ := hC
    cases res with
    | error _ => exact faultSuspendRecord_stepCovers e st tid c _ hInv
    | ok p =>
      obtain ⟨summary, sgi?⟩ := p
      dsimp only
      have hS := stageWokenDelivery_keyFrame st1 ((st.getEndpoint? tgt.endpoint).bind (·.receiveQ.head))
        summary.capInfo hCInv
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
    (syscallId : UInt32) (x0 x1 x2 x3 x4 x5 x6 : UInt64) (hB : finalisingDeleteBundle st) :
    finalisingDeleteBundle
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6) := by
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
    (syscallId : UInt32) (x0 x1 x2 x3 x4 x5 x6 : UInt64) (hInv : st.objects.invExt) :
    capabilityKeyFrame st
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6) := by
  unfold Platform.FFI.writeFfiRegistersToTcb
  exact updateTcb_keyFrame st tid (fun _ => rfl) hInv

/-- **A refused reply-receive covers** (WS-SX SX34): every leg it ran before it
stopped covers and keeps the object table well formed. -/
theorem replyRecvTransferStoppedState_stepCovers (e : CoreId) {epId : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId} {label : Nat}
    {msg : IpcMessage} {grant : Bool} {core : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) :
    stepCovers e st (replyRecvTransferStoppedState epId tid rid prevCaller label msg grant core st) ∧
      (replyRecvTransferStoppedState epId tid rid prevCaller label msg grant core st).objects.invExt :=
  replyRecvTransferStoppedState_induct (fun a b => stepCovers e a b ∧ b.objects.invExt)
    (fun s h => ⟨stepCovers_refl e s, h⟩)
    (fun _ _ _ _ h1 h2 => ⟨stepCovers_trans h1.1 h2.1, h2.2⟩)
    (fun _ _ _ _ _ h => endpointReplyOnCore_stepCovers e h)
    (fun _ _ _ _ _ h hP => replyRecvPopDonation_stepCovers e h hP)
    (fun _ _ _ _ _ h hX =>
      have hK := receiveTransferCaps_keyFrame h hX
      ⟨hK.stepCovers (congrArg MachineState.residentCode (receiveTransferCaps_preserves_machine hX))
        (banksKeptOffCore_of_eq
          (congrArg MachineState.coreRegs (receiveTransferCaps_preserves_machine hX))), hK.2.2⟩)
    (fun a s t n h => by
      cases a with
      | none =>
        have hK := stageDeliveredMessage_keyFrame s t n h
        exact ⟨hK.stepCovers, hK.2.2⟩
      | some o => exact faultReplyApplyOnCore_stepCovers e s t o h)
    (fun s t h => receiveReturnSchedContext_stepCovers e true s t h)
    (fun _ h => endpointReceiveDualWithCapsOnCore_stepCovers e h)
    (fun s t h => descheduleAtPlacement_stepCovers e s t h)
    (fun s t c h => propagatePipChainCrossCore_stepCovers e c _ s t h) hInv


/-- The state a refusal of the checked entry reports (`cancelReceiveBusyReply`)
covers: the state itself, its busy reply's holder cancelled, or a
reply-receive's stopped state. -/
theorem cancelReceiveBusyReply_stepCovers (e : CoreId) (ctx : LabelingContext)
    (ec : CoreId) (st : SystemState) (hInv : st.objects.invExt) :
    stepCovers e st (cancelReceiveBusyReply ctx ec st) ∧
      (cancelReceiveBusyReply ctx ec st).objects.invExt := by
  rcases cancelReceiveBusyReply_cases_holder ctx ec st with h | ⟨_, _, -, -, h⟩ | hA | hB
  · rw [h]; exact ⟨stepCovers_refl e st, hInv⟩
  · rw [h]; exact cancelReplyHolder_stepCovers e st _ ec hInv
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, -, -, -, h⟩ := hA.stopped
    rw [h]
    exact replyRecvEntryRefusalTaint_induct (fun x => stepCovers e st x ∧ x.objects.invExt)
      (fun _ _ _ h => ⟨stepCovers_trans h.1 (stepCovers_of_scheduler_eq
          (keyInputsEq_of_objectsAgreeOffTaint (applySyscallTaint_objectsAgreeOffTaint _ _ _))
          (applySyscallTaint_scheduler _ _ _)), applySyscallTaint_invExt h.2⟩)
      (replyRecvTransferStoppedState_stepCovers e hInv)
  · -- WS-SX SX36.1: a reply-receive whose receive was refused after its reply
    exact hB.induct (fun a b => stepCovers e a b ∧ b.objects.invExt)
      (fun s h => ⟨stepCovers_refl e s, h⟩)
      (fun _ _ _ _ h1 h2 => ⟨stepCovers_trans h1.1 h2.1, h2.2⟩)
      (fun _ _ _ _ _ h => endpointReplyOnCore_stepCovers e h)
      (fun _ _ _ _ _ h hP => replyRecvPopDonation_stepCovers e h hP)
      (fun _ _ _ _ _ h hX =>
        have hK := receiveTransferCaps_keyFrame h hX
        ⟨hK.stepCovers (congrArg MachineState.residentCode (receiveTransferCaps_preserves_machine hX))
          (banksKeptOffCore_of_eq
            (congrArg MachineState.coreRegs (receiveTransferCaps_preserves_machine hX))), hK.2.2⟩)
      (fun a s t n h => by
        cases a with
        | none =>
          have hK := stageDeliveredMessage_keyFrame s t n h
          exact ⟨hK.stepCovers, hK.2.2⟩
        | some o => exact faultReplyApplyOnCore_stepCovers e s t o h)
      (fun s t h => receiveReturnSchedContext_stepCovers e true s t h)
      (fun _ _ _ _ _ h => endpointReceiveDualWithCapsOnCore_stepCovers e h)
      (fun s t h => descheduleAtPlacement_stepCovers e s t h)
      (fun s t c h => propagatePipChainCrossCore_stepCovers e c _ s t h)
      (fun _ _ _ _ _ _ _ _ _ hs hT => replyTransferOnCoreChecked_stepCovers e hs hT)
      (fun _ _ _ _ h => ⟨stepCovers_trans h.1 (stepCovers_of_scheduler_eq
          (keyInputsEq_of_objectsAgreeOffTaint (applySyscallTaint_objectsAgreeOffTaint _ _ _))
          (applySyscallTaint_scheduler _ _ _)), applySyscallTaint_invExt h.2⟩) hInv

/-- **The ABI dispatch covers** on the executing core: the argument spill moves
no key, the checked entry covers, a capability fault is a covered delivery, and
a refusal record touches the refusal ledger alone. -/
theorem syscallDispatchFromAbi_stepCovers {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 : UInt64}
    {st st' : SystemState} {outcome : Architecture.SyscallOutcome}
    (hInv : st.objects.invExt) (hB : finalisingDeleteBundle st)
    (hPlaced : placedThreadsHaveTcbs st)
    (hAwayCur : ∀ t, st.scheduler.currentOnCore e = some t → ∀ c, st.queuedOn c t = false)
    (h : Platform.FFI.syscallDispatchFromAbi ctx e syscallId x0 x1 x2 x3 x4 x5
      x6 elr spsr spEl0 x30 st = .ok (outcome, st')) :
    stepCovers e st st' ∧ st'.objects.invExt := by
  unfold Platform.FFI.syscallDispatchFromAbi at h
  split at h
  · cases h; exact ⟨stepCovers_refl e st, hInv⟩
  rename_i tid hCur
  split at h
  · cases h; exact ⟨stepCovers_refl e st, hInv⟩
  have hW := writeFfiRegistersToTcb_keyFrame st tid syscallId x0 x1 x2 x3 x4 x5 x6 hInv
  dsimp only at h
  split at h
  · -- the refusal's reported state: the spill, or its busy reply's holder
    -- cancelled on it
    obtain ⟨hC, hCInv⟩ := cancelReceiveBusyReply_stepCovers e ctx e
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6) hW.2.2
    split at h
    · split at h
      · -- an NBSend lookup fault is dropped: the refusal's state and its
        -- ledger record, nothing more
        cases h
        obtain ⟨L, hL⟩ := Platform.FFI.recordDroppedFault_frame ctx e
          (Platform.FFI.seamOperationCode
            (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6) tid)
          tid x0 _ (cancelReceiveBusyReply ctx e
            (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6))
        rw [hL]
        refine stepCoversInv_trans (stepCovers_trans hW.stepCovers hC)
          (capabilityKeyFrame.stepCoversInv ?_)
        exact capabilityKeyFrame_of_objects_scheduler_eq hCInv rfl rfl
      · cases h
        unfold Platform.FFI.deliverSyscallCapFault
        have hF := writeFaultRegistersToTcb_keyFrame _ tid
          (Platform.FFI.syscallWindow syscallId x0 x1 x2 x3 x4 x5 x6 spEl0 x30) hCInv
        exact stepCoversInv_trans
          (stepCovers_trans (stepCovers_trans hW.stepCovers hC) hF.stepCovers)
          (faultDeliverOnCoreChecked_stepCovers e hF.2.2)
    · split at h
      · cases h
        refine stepCoversInv_trans (stepCovers_trans hW.stepCovers hC)
          (capabilityKeyFrame.stepCoversInv ?_)
        exact capabilityKeyFrame_of_objects_scheduler_eq hCInv
          ((Platform.FFI.recordSyscallRefusal_objects_eq _ _ _ _ _ _ _).trans
            (Architecture.recordErrorOverflow_objects _ _ _))
          ((Platform.FFI.recordSyscallRefusal_scheduler_eq _ _ _ _ _ _ _).trans
            (Architecture.recordErrorOverflow_scheduler _ _ _))
      · cases h
        refine stepCoversInv_trans (stepCovers_trans hW.stepCovers hC)
          (capabilityKeyFrame.stepCoversInv ?_)
        exact capabilityKeyFrame_of_objects_scheduler_eq hCInv
          (Platform.FFI.recordSyscallRefusal_objects_eq _ _ _ _ _ _ _)
          (Platform.FFI.recordSyscallRefusal_scheduler_eq _ _ _ _ _ _ _)
  · rename_i hE
    cases h
    have hB' := finalisingDeleteBundle_writeFfiRegistersToTcb tid syscallId x0 x1 x2 x3 x4 x5 x6 hB
    have hPl : placedThreadsHaveTcbs
        (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6) := by
      unfold Platform.FFI.writeFfiRegistersToTcb
      exact placedThreadsHaveTcbs_updateTcb hInv hPlaced
    -- The argument spill writes registers alone: no current slot, no queue.
    have hAwayW : ∀ t, (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6
        ).scheduler.currentOnCore e = some t → ∀ c,
        (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5 x6).queuedOn c t =
          false := by
      intro t ht c
      rw [Platform.FFI.writeFfiRegistersToTcb_scheduler] at ht
      rw [Platform.FFI.writeFfiRegistersToTcb_eq_updateTcb,
        (SystemState.RunCoresAgree.updateTcb (f := Platform.FFI.ffiRegisterSpill syscallId x0 x1 x2 x3 x4 x5 x6)
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
and consumed count (`KernelObject.withoutYield`), and the core's own bank — is no
key input, and it writes no scheduler state. -/
theorem activateThreadOnCore_stepCovers (c : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) : stepCovers c st (activateThreadOnCore st c) :=
  stepCovers_of_keys_sched
    (keyInputsEq_of_objectsAgreeOffYield (activateThreadOnCore_objectsAgreeOffYield st c hInv))
    (activateThreadOnCore_scheduler st c)
    (hBank := fun d hd => activateThreadOnCore_regsOnCore_ne st c d hd)

/-- **The syscall seam covers** on the executing core: the ABI dispatch, the
caller's return staging, the drop of a caller whose lent context went back, the
local scheduling point, the residency settlement
and the activation.  (A refused dispatch fires no SGI, so it owes nothing.) -/
theorem syscallDispatchCrossCoreStep_stepCovers {ctx : LabelingContext} {e : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 : UInt64}
    {st st' : SystemState} {outcome : Architecture.SyscallOutcome}
    (hInv : st.objects.invExt) (hB : finalisingDeleteBundle st)
    (hPlaced : placedThreadsHaveTcbs st)
    (hAwayCur : ∀ t, st.scheduler.currentOnCore e = some t → ∀ c, st.queuedOn c t = false)
    (h : Platform.FFI.syscallDispatchFromAbi ctx e syscallId x0 x1 x2 x3 x4 x5
      x6 elr spsr spEl0 x30 st = .ok (outcome, st')) :
    stepCovers e st (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore
      (PriorityInheritance.scheduleLocalSuccessorFrom (st.scheduler.currentOnCore e)
        (dropReturnedContextCaller
          (contextReturnableAtEntry (syscallNumberIsReplyRecv syscallId) st
            (st.scheduler.currentOnCore e)) (st.scheduler.currentOnCore e)
          (Architecture.stageCallerReturnFor (st.scheduler.currentOnCore e) st' e outcome) e)
        e) e) e) := by
  obtain ⟨hD, hDInv⟩ := syscallDispatchFromAbi_stepCovers hInv hB hPlaced hAwayCur h
  have hSInv := settleResidencyOnCore_preserves_objects_invExt e _
    (scheduleLocalSuccessorFrom_preserves_objects_invExt e (st.scheduler.currentOnCore e) _
      (dropReturnedContextCaller_stepCovers e
        (contextReturnableAtEntry (syscallNumberIsReplyRecv syscallId) st
          (st.scheduler.currentOnCore e)) (st.scheduler.currentOnCore e) _
        (stageCallerReturnFor_stepCovers e (st.scheduler.currentOnCore e) st' outcome hDInv).2).2)
  exact stepCovers_trans (stepCovers_trans hD
    (syscallCommitTail_stepCovers e
      (contextReturnableAtEntry (syscallNumberIsReplyRecv syscallId) st
        (st.scheduler.currentOnCore e)) (st.scheduler.currentOnCore e) st' outcome hDInv))
    (activateThreadOnCore_stepCovers e _ hSInv)

/-- WS-ZA ZA6.32: **the mask covers**: it writes the machine's mask and the
physical-write ledger, no object, no scheduler field and no register bank. -/
theorem setInterruptLineMask_stepCovers (e : CoreId) (st : SystemState) (line : Nat)
    (masked : Bool) (hInv : st.objects.invExt) :
    stepCovers e st (Architecture.setInterruptLineMask st line masked) ∧
      (Architecture.setInterruptLineMask st line masked).objects.invExt :=
  (capabilityKeyFrame_of_objects_scheduler_eq
    (st' := Architecture.setInterruptLineMask st line masked) hInv rfl rfl).stepCoversInv
    (hRes := rfl) (hBank := banksKeptOffCore_of_eq rfl)

/-- WS-ZA ZA6.32: **the interrupt step covers** on any core, on a state where
the binding pair holds: the `sendSignal` coverage (`sendSignalOnCore_stepCovers`,
the bound-aware signal and the donation to the thread it woke), then the
mask. -/
theorem handleInterruptOnCore_stepCovers (e : CoreId) (st : SystemState)
    (c : CoreId) (line : Nat) (hInv : st.objects.invExt)
    (hBi : schedContextBindingBidirectional st) :
    stepCovers e st (handleInterruptOnCore st c line) ∧
      (handleInterruptOnCore st c line).objects.invExt := by
  unfold handleInterruptOnCore
  split
  · rename_i ntfn badge _
    obtain ⟨h1, hI⟩ := sendSignalOnCore_stepCovers e (n := ntfn) (badge := badge)
      (c := c) hInv hBi
    have hSig : stepCovers e st (interruptSignal ntfn badge c st) ∧
        (interruptSignal ntfn badge c st).objects.invExt := ⟨h1, hI⟩
    exact stepCoversInv_trans hSig.1 (setInterruptLineMask_stepCovers e _ line true hSig.2)
  · exact setInterruptLineMask_stepCovers e st line true hInv

/-- …and the raw step's. -/
theorem interruptEntryStep_stepCovers (e : CoreId) (st : SystemState) (coreId intId : UInt64)
    (hInv : st.objects.invExt) (hBi : schedContextBindingBidirectional st) :
    stepCovers e st (interruptEntryStep st coreId intId) :=
  interruptEntryStep_of (P := stepCovers e st) st coreId intId (stepCovers_refl e st)
    (fun c _ _ => (handleInterruptOnCore_stepCovers e st c _ hInv hBi).1)

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
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 x6 elr spsr spEl0 x30 : UInt64}
    {st st' : SystemState} {outcome : Architecture.SyscallOutcome}
    (hInv : st.objects.invExt) (hB : finalisingDeleteBundle st)
    (hPlaced : placedThreadsHaveTcbs st)
    (hAwayCur : ∀ t, st.scheduler.currentOnCore e = some t → ∀ c, st.queuedOn c t = false)
    (h : Platform.FFI.syscallDispatchFromAbi ctx e syscallId x0 x1 x2 x3 x4 x5
      x6 elr spsr spEl0 x30 st = .ok (outcome, st'))
    (hId : ∀ oid (tcb : TCB), (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore
      (PriorityInheritance.scheduleLocalSuccessorFrom (st.scheduler.currentOnCore e)
        (dropReturnedContextCaller
          (contextReturnableAtEntry (syscallNumberIsReplyRecv syscallId) st
            (st.scheduler.currentOnCore e)) (st.scheduler.currentOnCore e)
          (Architecture.stageCallerReturnFor (st.scheduler.currentOnCore e) st' e outcome) e)
        e) e) e).getObject? oid =
      some (.tcb tcb) → tcb.tid.toObjId = oid)
    {c : CoreId} {k : SgiKind}
    (hMem : (c, k) ∈ PriorityInheritance.computeCrossCoreSgis st
      (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore
        (PriorityInheritance.scheduleLocalSuccessorFrom (st.scheduler.currentOnCore e)
          (dropReturnedContextCaller
            (contextReturnableAtEntry (syscallNumberIsReplyRecv syscallId) st
              (st.scheduler.currentOnCore e)) (st.scheduler.currentOnCore e)
            (Architecture.stageCallerReturnFor (st.scheduler.currentOnCore e) st' e outcome) e)
          e) e) e) e) :
    (c, SgiKind.reschedule) ∈ sgisOfRaised (syscallDispatchCrossCoreStep ctx e syscallId x0 x1 x2
        x3 x4 x5 x6 elr spsr spEl0 x30 st).1.2.1 ∨
      st.scheduler.reschedulePendingOnCore c = true := by
  rw [syscallDispatchCrossCoreStep_of_ok h]
  dsimp only
  rw [← rescheduleSgisFromFlags_eq_sgisOfRaised]
  exact computeCrossCoreSgis_mem_flags_of_covers hId
    (syscallDispatchCrossCoreStep_stepCovers hInv hB hPlaced hAwayCur h).1 hMem

end SeLe4n.Kernel
