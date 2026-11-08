-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RoutedArms.Report

/-!
# The overflowed route's arm, out of line

The routed entry's `.overflowed` arm (`syscallEntryCheckedK`): a call whose
message runs past the inline words and whose dispatch reads no word past
overflow slot 0 (a signal, a wait, a receive, an invocation, an audited call, a
configure or a service register), every overflow word of which sits on the page
of the caller's IPC buffer that holds slot 0, as its own function.  Slot 0 read, the call is dispatched as its short route is, on the
state with this core's TLB holding the buffer's translation, a refusal handing
back the TLB the entry held; one whose overflow words cross a page takes the
specification's decode and dispatch.  The syscall, the operand's address and
the message length cross as words, the state owned, and the result is the state
with its report pushed (`RoutedArms.Report`).

The `.shortArgs` arm, a configure or a service register of the inline words
alone, is here too: its operand found and checked, it is refused as missing its
fifth argument (`shortArgsRoutedArm`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- The overflowed dispatch as the arms run it, each kind of call its own arm
(`overflowedRoutedArm_eq`): the short route's operand dispatch, the five-word
invocations' fifth word `w` (`overflowedOperandR_eq`).  No code is generated for
it. -/
noncomputable def overflowedOperandR (ctx : LabelingContext) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (rf : SeLe4n.RegisterFile) (len : Nat) (w : UInt64)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  if Architecture.RegisterDecode.routedInvocation sid then
    dispatchOperandCheckedR capAddr tid executingCore
      (invocationOperandArmR ctx sid capAddr rf tid executingCore)
  else if Architecture.RegisterDecode.routedAudited sid then
    dispatchOperandCheckedR capAddr tid executingCore
      (auditedOperandArmR ctx sid rf capAddr tid executingCore)
  else
  match sid with
  | .notificationSignal =>
    dispatchOperandCheckedR capAddr tid executingCore
      (signalOperandArmThenTaintR ctx (.ok { badge := Badge.ofWord (readRegWord rf ⟨2⟩) }) tid
        executingCore (syscallRequiredRight .notificationSignal))
  | .notificationWait =>
    dispatchOperandCheckedR capAddr tid executingCore
      (waitOperandArmThenTaintR ctx tid executingCore (syscallRequiredRight .notificationWait))
  | .receive =>
    dispatchOperandCheckedR capAddr tid executingCore
      (receiveOperandArmThenTaintR ctx tid len (SeLe4n.CPtr.ofWord (readRegWord rf ⟨2⟩))
        executingCore (syscallRequiredRight .receive))
  | .schedContextConfigure => dispatchConfigureCheckedR capAddr rf w tid executingCore
  | .serviceRegister => dispatchServiceRegisterCheckedR ctx capAddr rf w tid executingCore
  | .yield => fun st =>
    if st.scheduler.currentOnCore executingCore ≠ some tid then .error (.illegalState, st)
    else
    match yieldOnCoreR st executingCore with
    | .error r => .error r
    | .ok st' => .ok ((), st')
  | _ => fun st => .error (.illegalState, st)

theorem overflowedOperandR_eq (ctx : LabelingContext) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (rf : SeLe4n.RegisterFile) (len : Nat) (w : UInt64)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) :
    overflowedOperandR ctx sid capAddr rf len w tid executingCore =
      dispatchOverflowedCheckedR ctx sid capAddr rf len w tid executingCore := by
  unfold overflowedOperandR dispatchOverflowedCheckedR
  split
  · rfl
  split
  · rfl
  cases sid <;> rfl

/-- The overflowed arm's body as the specification states it
(`syscallEntryCheckedK`), over the operand dispatch `op` (handed the overflow
word and the caller's registers): slot 0 read, then `op` on the entry's state
when this core's TLB already holds the buffer's translation, and otherwise on
the state with it filled, a refusal handing back the TLB the entry held; a call
whose overflow words cross a page takes the checked entry.  Its result reported
under the entry's first continuation. -/
def overflowedArmSpec (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (length : Nat)
    (op : UInt64 → SeLe4n.RegisterFile → RefusalCarrying Unit) (st : SystemState) :
    SystemState :=
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
    if SeLe4n.Kernel.Architecture.overflowSlotsOnFirstPage tcb.ipcBuffer 0 (length - 4) then
      SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
        (fun _ => entryReportGeneral (.error (.invalidMessageInfo, st)))
        (fun w => entryReportGeneral (
          if SeLe4n.Kernel.Architecture.ipcBufferFillHeldOne st executingCore tid then
            op w tcb.registerContext st
          else
            let n0 := (SeLe4n.Kernel.Architecture.tlbOnCore st executingCore).entries.length
            match op w tcb.registerContext
                (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid 1) with
            | .error (e, stF) =>
              .error (e, SeLe4n.Kernel.Architecture.tlbUndoFillOnCore stF executingCore n0)
            | .ok r => .ok r))
    else
      entryReportGeneral (RefusalCarrying.ofKernel
        (syscallEntryChecked ctx SeLe4n.arm64DefaultLayout executingCore 32) st)
  | _ => entryReportGeneral (.error (.illegalState, st))

/-- **The overflowed arm's body** as it runs: `overflowedArmSpec` with the
dispatch written once, on the state the TLB fill leaves (the entry's own when
the core already holds the translation), so each kind's arm inlines its
dispatch once (`overflowedArmWith_eq_spec`). -/
@[inline] def overflowedArmWith (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (length : Nat)
    (op : UInt64 → SeLe4n.RegisterFile → RefusalCarrying Unit) (st : SystemState) :
    SystemState :=
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
    if SeLe4n.Kernel.Architecture.overflowSlotsOnFirstPage tcb.ipcBuffer 0 (length - 4) then
      SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
        (fun _ => entryReportGeneral (.error (.invalidMessageInfo, st)))
        (fun w =>
          let held := SeLe4n.Kernel.Architecture.ipcBufferFillHeldOne st executingCore tid
          let n0 := (SeLe4n.Kernel.Architecture.tlbOnCore st executingCore).entries.length
          let st1 := if held then st
            else SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid 1
          entryReportGeneral (
            match op w tcb.registerContext st1 with
            | .error (e, stF) =>
              .error (e, if held then stF
                else SeLe4n.Kernel.Architecture.tlbUndoFillOnCore stF executingCore n0)
            | .ok r => .ok r))
    else
      entryReportGeneral (RefusalCarrying.ofKernel
        (syscallEntryChecked ctx SeLe4n.arm64DefaultLayout executingCore 32) st)
  | _ => entryReportGeneral (.error (.illegalState, st))

theorem overflowedArmWith_eq_spec (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (length : Nat)
    (op : UInt64 → SeLe4n.RegisterFile → RefusalCarrying Unit) (st : SystemState) :
    overflowedArmWith ctx executingCore tid length op st =
      overflowedArmSpec ctx executingCore tid length op st := by
  unfold overflowedArmWith overflowedArmSpec
  split
  · split
    · congr 1
      funext w
      cases hH : SeLe4n.Kernel.Architecture.ipcBufferFillHeldOne st executingCore tid
      · simp only [Bool.false_eq_true, ↓reduceIte]
      · simp only [↓reduceIte]
        rcases op w _ st with ⟨e, stF⟩ | r <;> rfl
    · rfl
  · rfl

/-- The overflowed arm of an invocation. -/
@[noinline] def overflowedInvocationRoutedArm (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (sid : SyscallId)
    (capWord : UInt64) (length : Nat) (st : SystemState) : SystemState :=
  overflowedArmWith ctx executingCore tid length (fun _ rf =>
    dispatchOperandCheckedR (SeLe4n.CPtr.ofWord capWord) tid executingCore
      (invocationOperandArmR ctx sid (SeLe4n.CPtr.ofWord capWord) rf tid executingCore)) st

/-- The overflowed arm of a declassification or an audit call. -/
@[noinline] def overflowedAuditedRoutedArm (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (sid : SyscallId)
    (capWord : UInt64) (length : Nat) (st : SystemState) : SystemState :=
  overflowedArmWith ctx executingCore tid length (fun _ rf =>
    dispatchOperandCheckedR (SeLe4n.CPtr.ofWord capWord) tid executingCore
      (auditedOperandArmR ctx sid rf (SeLe4n.CPtr.ofWord capWord) tid executingCore)) st

/-- The overflowed arm of a five-word invocation, its fifth word slot 0's. -/
@[noinline] def overflowedFiveWordRoutedArm (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (sid : SyscallId)
    (capWord : UInt64) (length : Nat) (st : SystemState) : SystemState :=
  overflowedArmWith ctx executingCore tid length (fun w rf =>
    match sid with
    | .schedContextConfigure =>
      dispatchConfigureCheckedR (SeLe4n.CPtr.ofWord capWord) rf w tid executingCore
    | _ => dispatchServiceRegisterCheckedR ctx (SeLe4n.CPtr.ofWord capWord) rf w tid
      executingCore) st

/-- The overflowed arm of a signal, a wait, a receive or a yield. -/
@[noinline] def overflowedNotificationRoutedArm (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (sid : SyscallId)
    (capWord : UInt64) (length : Nat) (st : SystemState) : SystemState :=
  overflowedArmWith ctx executingCore tid length (fun _ rf =>
    match sid with
    | .notificationSignal =>
      dispatchOperandCheckedR (SeLe4n.CPtr.ofWord capWord) tid executingCore
        (signalOperandArmThenTaintR ctx (.ok { badge := Badge.ofWord (readRegWord rf ⟨2⟩) }) tid
          executingCore (syscallRequiredRight .notificationSignal))
    | .notificationWait =>
      dispatchOperandCheckedR (SeLe4n.CPtr.ofWord capWord) tid executingCore
        (waitOperandArmThenTaintR ctx tid executingCore (syscallRequiredRight .notificationWait))
    | .receive =>
      dispatchOperandCheckedR (SeLe4n.CPtr.ofWord capWord) tid executingCore
        (receiveOperandArmThenTaintR ctx tid length (SeLe4n.CPtr.ofWord (readRegWord rf ⟨2⟩))
          executingCore (syscallRequiredRight .receive))
    | .yield => fun st =>
      if st.scheduler.currentOnCore executingCore ≠ some tid then .error (.illegalState, st)
      else
      match yieldOnCoreR st executingCore with
      | .error r => .error r
      | .ok st' => .ok ((), st')
    | _ => fun st => .error (.illegalState, st)) st

/-- **The overflowed arm**: the arm of the call's kind. -/
@[inline] def overflowedRoutedArm (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (sid : SyscallId) (capWord : UInt64) (length : Nat)
    (st : SystemState) : SystemState :=
  if Architecture.RegisterDecode.routedInvocation sid then
    overflowedInvocationRoutedArm ctx executingCore tid sid capWord length st
  else if Architecture.RegisterDecode.routedAudited sid then
    overflowedAuditedRoutedArm ctx executingCore tid sid capWord length st
  else if Architecture.RegisterDecode.routedOverflowOne sid then
    overflowedFiveWordRoutedArm ctx executingCore tid sid capWord length st
  else overflowedNotificationRoutedArm ctx executingCore tid sid capWord length st

/-- The overflowed arm is its body over the overflowed dispatch. -/
theorem overflowedRoutedArm_eq (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (sid : SyscallId) (capWord : UInt64) (length : Nat)
    (st : SystemState) :
    overflowedRoutedArm ctx executingCore tid sid capWord length st =
      overflowedArmWith ctx executingCore tid length (fun w rf =>
        overflowedOperandR ctx sid (SeLe4n.CPtr.ofWord capWord) rf length w tid executingCore)
        st := by
  unfold overflowedRoutedArm
  by_cases hI : Architecture.RegisterDecode.routedInvocation sid = true
  · rw [if_pos hI]
    unfold overflowedInvocationRoutedArm
    congr 1
    funext w rf
    simp only [overflowedOperandR, hI, ↓reduceIte]
  rw [if_neg hI]
  by_cases hA : Architecture.RegisterDecode.routedAudited sid = true
  · rw [if_pos hA]
    unfold overflowedAuditedRoutedArm
    congr 1
    funext w rf
    simp only [overflowedOperandR, hI, hA, ↓reduceIte, Bool.false_eq_true]
  rw [if_neg hA]
  by_cases hO : Architecture.RegisterDecode.routedOverflowOne sid = true
  · rw [if_pos hO]
    unfold overflowedFiveWordRoutedArm
    congr 1
    funext w rf
    simp only [overflowedOperandR, hI, hA, ↓reduceIte, Bool.false_eq_true]
    cases sid <;> first | rfl | (exfalso; revert hO; decide)
  rw [if_neg hO]
  unfold overflowedNotificationRoutedArm
  congr 1
  funext w rf
  simp only [overflowedOperandR, hI, hA, ↓reduceIte, Bool.false_eq_true]
  cases sid <;> first | rfl | (exfalso; revert hO; decide)

/-- **The short-arguments arm**: `dispatchOperandCheckedK` on the operand and the
refusal of a five-word invocation short of its fifth word
(`shortArgsOperandArmR`), its results reported. -/
@[noinline] def shortArgsRoutedArm (executingCore : Concurrency.CoreId) (tid : SeLe4n.ThreadId)
    (sid : SyscallId) (capWord : UInt64) (st : SystemState) : SystemState :=
  dispatchOperandCheckedK (SeLe4n.CPtr.ofWord capWord) tid executingCore
    (shortArgsOperandArmR sid) st entryReportGeneral entryReportResolved entryReportLookup

end SeLe4n.Kernel
