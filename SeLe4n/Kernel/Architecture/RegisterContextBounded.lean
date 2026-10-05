-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.ContextRestore
import SeLe4n.Kernel.Architecture.Adapter
import SeLe4n.Kernel.IPC.Operations.Fault
import SeLe4n.Kernel.Scheduler.Operations.Core
import SeLe4n.Kernel.Concurrency.Runtime

/-!
# Every saved context fits in machine words

`RegisterFile` is `Nat`-backed, and the boundary narrows each register with
`Nat.toUInt64`, which wraps a value at or above `2^64`
(`trapContextOfRegisterFile`).  `RegisterFile.wordBounded` names the property
under which that narrowing is lossless; this file carries it as a state
predicate — **every TCB's saved context and every core's register bank** —
and proves that every writer of a `TCB.registerContext` or of a bank preserves
it: the trap-frame saves, the syscall-return and fault-restart stagers, the
fault-reply spill, the SVC seam's argument spill, the scheduler's bank ↔ TCB
copies and the runtime adapter's register write.  Each writes either a
`UInt64` read as a `Nat`, a value copied from another bounded context, or a
`pc` rewound below the one it had.

The payoff is at the live restore path: `restoreTargetOnCore_user_roundTrip`
discharges `registerFileOfTrapContext_trapContextOfRegisterFile`'s hypothesis
from the carried predicate, so the context a core resumes is the thirty-five
words the model held, with no caller-supplied bound.

Invariant side of the Operations/Invariant split for `TrapFrameSave`,
`ContextRestore`, `SyscallReturn` and the writers above; the predicate is not
yet a conjunct of the IPC or scheduler bundles (registered debt,
`docs/REGISTERED_DEBT.md`, the `Nat`-backed register file row).
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

/-- **Every saved context and every core's bank is word-bounded**: each TCB's
`registerContext` and each `regsOnCore c` satisfy `RegisterFile.wordBounded`
(the bank half is `machineWordBounded`). -/
def registerContextsWordBounded (st : SystemState) : Prop :=
  (∀ tid tcb, st.getTcb? tid = some tcb → tcb.registerContext.wordBounded) ∧
    SeLe4n.machineWordBounded st.machine

/-- A TCB the state holds has a word-bounded context. -/
theorem registerContextsWordBounded.tcb {st : SystemState} (h : registerContextsWordBounded st)
    {tid : SeLe4n.ThreadId} {tcb : TCB} (hTcb : st.getTcb? tid = some tcb) :
    tcb.registerContext.wordBounded := h.1 tid tcb hTcb

/-- Every core's bank is word-bounded. -/
theorem registerContextsWordBounded.bank {st : SystemState} (h : registerContextsWordBounded st)
    (c : CoreId) : (st.machine.regsOnCore c).wordBounded := h.2 c

/-- `getTcb?` reads the object table and nothing else. -/
theorem getTcb?_of_objects_eq {st st' : SystemState} (hObj : st'.objects = st.objects)
    (tid : SeLe4n.ThreadId) : st'.getTcb? tid = st.getTcb? tid := by
  unfold SystemState.getTcb?; rw [hObj]

/-- **Frame**: a transition that leaves the object table and the machine alone
preserves the predicate, whatever else it writes. -/
theorem registerContextsWordBounded_of_eq {st st' : SystemState}
    (h : registerContextsWordBounded st) (hObj : st'.objects = st.objects)
    (hM : st'.machine = st.machine) : registerContextsWordBounded st' :=
  ⟨fun tid tcb hTcb => h.1 tid tcb (by rwa [getTcb?_of_objects_eq hObj] at hTcb),
   by rw [hM]; exact h.2⟩

/-- **A TCB rewrite preserves the predicate when the context it writes is
bounded** — for any `f`, given that `f` keeps the one TCB it rewrites bounded.
Every other TCB is framed (`updateTcb_objects_ne`), and the machine is untouched. -/
theorem registerContextsWordBounded_updateTcb {st : SystemState}
    (h : registerContextsWordBounded st) (hObjInv : st.objects.invExt)
    (tid : SeLe4n.ThreadId) (f : TCB → TCB)
    (hf : ∀ t, st.getTcb? tid = some t → (f t).registerContext.wordBounded) :
    registerContextsWordBounded (st.updateTcb tid f) := by
  refine ⟨fun tid' tcb' hTcb' => ?_, ?_⟩
  · by_cases hEq : tid.toObjId = tid'.toObjId
    · have hSame : (st.updateTcb tid f).getTcb? tid' = (st.updateTcb tid f).getTcb? tid := by
        unfold SystemState.getTcb?; rw [hEq]
      rw [hSame, SystemState.updateTcb_getTcb?_self st tid f hObjInv] at hTcb'
      cases hT : st.getTcb? tid with
      | none => rw [hT] at hTcb'; change none = some tcb' at hTcb'; cases hTcb'
      | some t =>
        rw [hT] at hTcb'; change some (f t) = some tcb' at hTcb'; cases hTcb'
        exact hf t hT
    · have hFrame := SystemState.updateTcb_objects_ne st tid f tid'.toObjId hEq hObjInv
      have hSame : (st.updateTcb tid f).getTcb? tid' = st.getTcb? tid' := by
        unfold SystemState.getTcb?; rw [hFrame]
      rw [hSame] at hTcb'
      exact h.1 tid' tcb' hTcb'
  · rw [SystemState.updateTcb_machine]; exact h.2

/-- The common shape: one TCB's context replaced by a bounded file. -/
theorem registerContextsWordBounded_updateTcb_registerContext {st : SystemState}
    (h : registerContextsWordBounded st) (hObjInv : st.objects.invExt)
    (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile) (hB : rf.wordBounded) :
    registerContextsWordBounded (st.updateTcb tid fun t => { t with registerContext := rf }) :=
  registerContextsWordBounded_updateTcb h hObjInv tid _ (fun _ _ => hB)

/-- **A bank write preserves the predicate when the file written is bounded**;
every other bank is framed (`regsOnCore_setRegsOnCore_ne`). -/
theorem registerContextsWordBounded_setRegsOnCore {st : SystemState}
    (h : registerContextsWordBounded st) (c : CoreId) (rf : SeLe4n.RegisterFile)
    (hB : rf.wordBounded) :
    registerContextsWordBounded { st with machine := st.machine.setRegsOnCore c rf } := by
  refine ⟨fun tid tcb hTcb => h.1 tid tcb hTcb, fun c' => ?_⟩
  show ((st.machine.setRegsOnCore c rf).regsOnCore c').wordBounded
  by_cases hc : c = c'
  · subst hc; rw [MachineState.regsOnCore_setRegsOnCore_self]; exact hB
  · rw [MachineState.regsOnCore_setRegsOnCore_ne _ _ _ _ hc]; exact h.2 c'

-- ============================================================================
-- §1  The trap-frame saves (WS-BP BP7.3, PR #904)
-- ============================================================================

/-- `saveTrapFrameOnCore` writes the frame into the current thread and the
core's bank: bounded in, bounded out. -/
theorem saveTrapFrameOnCore_preserves_registerContextsWordBounded (st : SystemState)
    (c : CoreId) (rf : SeLe4n.RegisterFile) (h : registerContextsWordBounded st)
    (hObjInv : st.objects.invExt) (hB : rf.wordBounded) :
    registerContextsWordBounded (saveTrapFrameOnCore st c rf) := by
  rcases saveTrapFrameOnCore_frame st c rf with hEq | ⟨tid, tcb, _, _, _, hEq⟩
  · rw [hEq]; exact h
  · rw [hEq]
    have h1 := registerContextsWordBounded_updateTcb_registerContext h hObjInv tid rf hB
    have h2 := registerContextsWordBounded_setRegsOnCore h1 c rf hB
    rwa [SystemState.updateTcb_machine] at h2

/-- `saveVacatedFrameOnCore` writes `saved` into the resident thread, or nothing. -/
theorem saveVacatedFrameOnCore_preserves_registerContextsWordBounded (st : SystemState)
    (c : CoreId) (rf saved : SeLe4n.RegisterFile) (h : registerContextsWordBounded st)
    (hObjInv : st.objects.invExt) (hB : saved.wordBounded) :
    registerContextsWordBounded (saveVacatedFrameOnCore st c rf saved) := by
  unfold saveVacatedFrameOnCore
  split
  · split
    · split
      · exact registerContextsWordBounded_updateTcb_registerContext h hObjInv _ saved hB
      · exact h
    all_goals exact h
  · exact h

/-- The entry's save, for any captured frame whose file is bounded. -/
theorem saveCapturedTrapFrame_preserves_registerContextsWordBounded (st : SystemState)
    (c : CoreId) (frame : Option SeLe4n.RegisterFile) (h : registerContextsWordBounded st)
    (hObjInv : st.objects.invExt) (hB : ∀ rf, frame = some rf → rf.wordBounded) :
    registerContextsWordBounded (saveCapturedTrapFrame st c frame) := by
  cases frame with
  | none => exact h
  | some rf =>
    have hrf := hB rf rfl
    exact saveVacatedFrameOnCore_preserves_registerContextsWordBounded _ _ _ _
      (saveTrapFrameOnCore_preserves_registerContextsWordBounded st c rf h hObjInv hrf)
      (saveTrapFrameOnCore_preserves_objects_invExt st c rf hObjInv) hrf

/-- The syscall entry's save: the vacated core's frame is rewound to the `SVC`,
which keeps it bounded (`restartAtSvc_wordBounded`). -/
theorem saveCapturedSyscallFrame_preserves_registerContextsWordBounded (st : SystemState)
    (c : CoreId) (frame : Option SeLe4n.RegisterFile) (h : registerContextsWordBounded st)
    (hObjInv : st.objects.invExt) (hB : ∀ rf, frame = some rf → rf.wordBounded) :
    registerContextsWordBounded (saveCapturedSyscallFrame st c frame) := by
  cases frame with
  | none => exact h
  | some rf =>
    have hrf := hB rf rfl
    exact saveVacatedFrameOnCore_preserves_registerContextsWordBounded _ _ _ _
      (saveTrapFrameOnCore_preserves_registerContextsWordBounded st c rf h hObjInv hrf)
      (saveTrapFrameOnCore_preserves_objects_invExt st c rf hObjInv)
      (restartAtSvc_wordBounded rf hrf)

/-- **The frame every live entry saves is bounded**: it is a `TrapContext` the HAL
handed over, read as a register file (`registerFileOfTrapContext_wordBounded`). -/
theorem ofTrapContext_frame_wordBounded (trapped : TrapContext) :
    ∀ rf, some (registerFileOfTrapContext trapped) = some rf → rf.wordBounded := by
  intro rf hrf; cases hrf; exact registerFileOfTrapContext_wordBounded trapped

/-- The fault and unknown-syscall entries' save (`Kernel.faultEntry`), by core id. -/
theorem saveCapturedTrapFrameAt_preserves_registerContextsWordBounded (st : SystemState)
    (coreId : UInt64) (frame : Option SeLe4n.RegisterFile) (h : registerContextsWordBounded st)
    (hObjInv : st.objects.invExt) (hB : ∀ rf, frame = some rf → rf.wordBounded) :
    registerContextsWordBounded (Concurrency.saveCapturedTrapFrameAt st coreId frame) := by
  unfold Concurrency.saveCapturedTrapFrameAt
  split
  · exact saveCapturedTrapFrame_preserves_registerContextsWordBounded _ _ _ h hObjInv hB
  · exact h

/-- The unknown-syscall entry's save (`Kernel.unknownSyscallEntry`), by core id. -/
theorem saveCapturedSyscallFrameAt_preserves_registerContextsWordBounded (st : SystemState)
    (coreId : UInt64) (frame : Option SeLe4n.RegisterFile) (h : registerContextsWordBounded st)
    (hObjInv : st.objects.invExt) (hB : ∀ rf, frame = some rf → rf.wordBounded) :
    registerContextsWordBounded (Concurrency.saveCapturedSyscallFrameAt st coreId frame) := by
  unfold Concurrency.saveCapturedSyscallFrameAt
  split
  · exact saveCapturedSyscallFrame_preserves_registerContextsWordBounded _ _ _ h hObjInv hB
  · exact h

-- ============================================================================
-- §2  The frame stagers and the spills
-- ============================================================================

/-- Staging a syscall return frame (`TCB.withReturnFrame`). -/
theorem writeReturnFrameToTcb_preserves_registerContextsWordBounded (st : SystemState)
    (tid : SeLe4n.ThreadId) (frame : SyscallReturnFrame) (h : registerContextsWordBounded st)
    (hObjInv : st.objects.invExt) :
    registerContextsWordBounded (writeReturnFrameToTcb st tid frame) :=
  registerContextsWordBounded_updateTcb h hObjInv tid _
    (fun t hT => t.registerContext.stageReturnFrame_wordBounded frame (h.1 tid t hT))

/-- Staging a fault restart frame (`TCB.withRestartFrame`). -/
theorem writeRestartFrameToTcb_preserves_registerContextsWordBounded (st : SystemState)
    (tid : SeLe4n.ThreadId) (frame : FaultRestartFrame) (h : registerContextsWordBounded st)
    (hObjInv : st.objects.invExt) :
    registerContextsWordBounded (writeRestartFrameToTcb st tid frame) :=
  registerContextsWordBounded_updateTcb h hObjInv tid _
    (fun t hT => t.registerContext.stageRestartFrame_wordBounded frame (h.1 tid t hT))

/-- The fault reply's spill of the register window (`FaultRegisterWindow.spill`). -/
theorem writeFaultRegistersToTcb_preserves_registerContextsWordBounded (st : SystemState)
    (tid : SeLe4n.ThreadId) (w : FaultRegisterWindow) (h : registerContextsWordBounded st)
    (hObjInv : st.objects.invExt) :
    registerContextsWordBounded (writeFaultRegistersToTcb st tid w) :=
  registerContextsWordBounded_updateTcb h hObjInv tid _
    (fun t hT => w.spill_wordBounded _ (h.1 tid t hT))

/-- The SVC seam's argument spill (`Platform.FFI.writeFfiRegistersToTcb`): six
64-bit words and the 32-bit syscall id, each read as a `Nat`. -/
theorem writeFfiRegistersToTcb_preserves_registerContextsWordBounded (st : SystemState)
    (tid : SeLe4n.ThreadId) (syscallId : UInt32) (x0 x1 x2 x3 x4 x5 : UInt64)
    (h : registerContextsWordBounded st) (hObjInv : st.objects.invExt) :
    registerContextsWordBounded
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) := by
  refine registerContextsWordBounded_updateTcb h hObjInv tid _ (fun t hT => ?_)
  have w := SeLe4n.writeReg_uint64_wordBounded
  exact SeLe4n.writeReg_wordBounded _ _ _
    (w _ _ _ (w _ _ _ (w _ _ _ (w _ _ _ (w _ _ _ (w _ _ _ (h.1 tid t hT)))))))
    (SeLe4n.RegValue.valid_of_uint32 syscallId)

-- ============================================================================
-- §3  The scheduler's bank ↔ TCB copies and the runtime adapter
-- ============================================================================

/-- Saving the outgoing thread's bank into its TCB (per core). -/
theorem saveOutgoingContextOnCore_preserves_registerContextsWordBounded (st : SystemState)
    (c : CoreId) (h : registerContextsWordBounded st) (hObjInv : st.objects.invExt) :
    registerContextsWordBounded (saveOutgoingContextOnCore st c) := by
  unfold saveOutgoingContextOnCore
  split
  · exact h
  · exact registerContextsWordBounded_updateTcb_registerContext h hObjInv _ _ (h.2 c)

/-- Saving the outgoing thread's bank into its TCB (the boot core). -/
theorem saveOutgoingContext_preserves_registerContextsWordBounded (st : SystemState)
    (h : registerContextsWordBounded st) (hObjInv : st.objects.invExt) :
    registerContextsWordBounded (saveOutgoingContext st) := by
  unfold saveOutgoingContext
  split
  · exact h
  · exact registerContextsWordBounded_updateTcb_registerContext h hObjInv _ _ (h.2 bootCoreId)

/-- Restoring a thread's saved context into a core's bank. -/
theorem restoreIncomingContextOnCore_preserves_registerContextsWordBounded (st : SystemState)
    (c : CoreId) (tid : SeLe4n.ThreadId) (h : registerContextsWordBounded st) :
    registerContextsWordBounded (restoreIncomingContextOnCore st c tid) := by
  unfold restoreIncomingContextOnCore
  split
  · rename_i inTcb hTcb
    exact registerContextsWordBounded_setRegsOnCore h c _ (h.1 tid inTcb hTcb)
  · exact h

/-- Restoring a thread's saved context into the boot core's bank. -/
theorem restoreIncomingContext_preserves_registerContextsWordBounded (st : SystemState)
    (tid : SeLe4n.ThreadId) (h : registerContextsWordBounded st) :
    registerContextsWordBounded (restoreIncomingContext st tid) := by
  unfold restoreIncomingContext
  split
  · rename_i inTcb hTcb
    exact registerContextsWordBounded_setRegsOnCore h bootCoreId _ (h.1 tid inTcb hTcb)
  · exact h

/-- The self-switch-guarded restore. -/
theorem restoreIncomingContextOnCoreUnlessCurrent_preserves_registerContextsWordBounded
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (h : registerContextsWordBounded st) :
    registerContextsWordBounded (restoreIncomingContextOnCoreUnlessCurrent st c tid) := by
  unfold restoreIncomingContextOnCoreUnlessCurrent
  split
  · exact h
  · exact restoreIncomingContextOnCore_preserves_registerContextsWordBounded st c tid h

/-- Dispatching a core's idle thread: a run-queue write, the idle context's
restore and a current-slot write. -/
theorem dispatchIdleOnCore_preserves_registerContextsWordBounded (st : SystemState)
    (c : CoreId) (h : registerContextsWordBounded st) :
    registerContextsWordBounded (dispatchIdleOnCore st c) := by
  unfold dispatchIdleOnCore
  have h1 : registerContextsWordBounded
      { st with
        scheduler :=
          st.scheduler.setRunQueueOnCore c ((st.scheduler.runQueueOnCore c).remove (idleThreadId c)) } :=
    registerContextsWordBounded_of_eq h rfl rfl
  have h2 := restoreIncomingContextOnCore_preserves_registerContextsWordBounded _ c (idleThreadId c) h1
  exact registerContextsWordBounded_of_eq h2 rfl rfl

/-- Preempting a core's current thread saves its bank into its TCB. -/
theorem preemptCurrentOnCore_preserves_registerContextsWordBounded (st : SystemState)
    (c : CoreId) (incoming : SeLe4n.ThreadId) (h : registerContextsWordBounded st)
    (hObjInv : st.objects.invExt) :
    registerContextsWordBounded (preemptCurrentOnCore st c incoming) := by
  unfold preemptCurrentOnCore
  split
  · exact h
  · split
    · exact h
    · split
      · rename_i outTid _ _ _ prevTcb hPrev _
        have hUpd := registerContextsWordBounded_updateTcb_registerContext h hObjInv outTid
          (st.machine.regsOnCore c) (h.2 c)
        rw [SystemState.updateTcb_eq_of_some hPrev] at hUpd
        exact registerContextsWordBounded_of_eq hUpd rfl rfl
      · exact h

/-- A successful `switchToThreadOnCore`: the preempt's save, the run-queue
dequeue, the incoming context's restore and the current-slot write. -/
theorem switchToThreadOnCore_preserves_registerContextsWordBounded (st st' : SystemState)
    (c : CoreId) (tid : SeLe4n.ThreadId) (h : registerContextsWordBounded st)
    (hObjInv : st.objects.invExt) (hStep : switchToThreadOnCore st c tid = .ok st') :
    registerContextsWordBounded st' := by
  unfold switchToThreadOnCore at hStep
  split at hStep
  · split at hStep
    · cases hStep
      have h1 := preemptCurrentOnCore_preserves_registerContextsWordBounded st c tid h hObjInv
      have h2 : registerContextsWordBounded
          { preemptCurrentOnCore st c tid with
            scheduler :=
              (preemptCurrentOnCore st c tid).scheduler.setRunQueueOnCore c
                (((preemptCurrentOnCore st c tid).scheduler.runQueueOnCore c).remove tid) } :=
        registerContextsWordBounded_of_eq h1 rfl rfl
      have h3 := restoreIncomingContextOnCoreUnlessCurrent_preserves_registerContextsWordBounded
        _ c tid h2
      exact registerContextsWordBounded_of_eq h3 rfl rfl
    · cases hStep
  · cases hStep

/-- The runtime adapter's register write: bounded when the value written is a
machine word — the adapter takes a `RegValue`, so the bound is its caller's. -/
theorem writeRegisterState_preserves_registerContextsWordBounded (reg : SeLe4n.RegName)
    (value : SeLe4n.RegValue) (st : SystemState) (h : registerContextsWordBounded st)
    (hv : value.valid) : registerContextsWordBounded (writeRegisterState reg value st) :=
  registerContextsWordBounded_setRegsOnCore h bootCoreId _
    (SeLe4n.writeReg_wordBounded _ _ _ (h.2 bootCoreId) hv)

-- ============================================================================
-- §4  The live restore path, and the state the kernel starts from
-- ============================================================================

/-- **The context a core resumes is word-bounded**: `restoreTargetOnCore` names
the current thread's saved context, which the predicate bounds. -/
theorem restoreTargetOnCore_user_wordBounded {st : SystemState} {c : CoreId}
    {ctx : SeLe4n.RegisterFile} {tableBase asid : UInt64} {fpLive : Bool}
    (h : registerContextsWordBounded st)
    (hT : restoreTargetOnCore st c = .user ctx tableBase asid fpLive) : ctx.wordBounded := by
  unfold restoreTargetOnCore at hT
  split at hT
  · split at hT
    · cases hT
    · split at hT
      · rename_i tcb hTcb
        cases hT
        exact h.1 _ _ hTcb
      · cases hT
  · cases hT

/-- **Restore then save is the identity on the live path, with no caller-supplied
bound**: the context `Platform.FFI.restoreTrapFrame` stages for a core
(`trapContextOfRegisterFile ctx`), read back as the model's register file, is
`ctx` on `pc`, `sp`, `pstate`, `tpidr` and `x0`–`x30` — the hypothesis
`registerFileOfTrapContext_trapContextOfRegisterFile` takes is discharged from
the carried predicate. -/
theorem restoreTargetOnCore_user_roundTrip {st : SystemState} {c : CoreId}
    {ctx : SeLe4n.RegisterFile} {tableBase asid : UInt64} {fpLive : Bool}
    (h : registerContextsWordBounded st)
    (hT : restoreTargetOnCore st c = .user ctx tableBase asid fpLive) :
    (registerFileOfTrapContext (trapContextOfRegisterFile ctx)).pc = ctx.pc ∧
    (registerFileOfTrapContext (trapContextOfRegisterFile ctx)).sp = ctx.sp ∧
    (registerFileOfTrapContext (trapContextOfRegisterFile ctx)).pstate = ctx.pstate ∧
    (registerFileOfTrapContext (trapContextOfRegisterFile ctx)).tpidr = ctx.tpidr ∧
    (∀ r : SeLe4n.RegName, r.val < 31 →
      (registerFileOfTrapContext (trapContextOfRegisterFile ctx)).gpr r = ctx.gpr r) :=
  registerFileOfTrapContext_trapContextOfRegisterFile ctx
    (restoreTargetOnCore_user_wordBounded h hT)

/-- The default state holds no TCB and all-zero banks, so it is bounded. -/
theorem registerContextsWordBounded_default : registerContextsWordBounded (default : SystemState) := by
  refine ⟨fun tid tcb hTcb => ?_, SeLe4n.machineWordBounded_default⟩
  exfalso
  have hNone : (default : SystemState).getTcb? tid = none := by
    have hEmpty : (default : SystemState).objects.get? tid.toObjId = none :=
      RobinHood.RHTable.getElem?_empty _ _ _
    unfold SystemState.getTcb?
    simp only [RHTable_getElem?_eq_get?]
    rw [hEmpty]
  rw [hNone] at hTcb
  cases hTcb

end SeLe4n.Kernel.Architecture
