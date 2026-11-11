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
configure, a service register or a yield), as its own function.  Its overflow
words read as the long send's are (slot 0 and the next page's first slot), the
call is dispatched as its short route is, on the state with this core's TLB
holding the buffer's translations, a refusal handing back the TLB the entry
held.  Every kind but the yield runs the long route's operand dispatch
(`longOperandK`), so a refusal reaches the entry's resolved or lookup
continuation as the dispatch told them apart and the operand is never resolved
a second time.  The syscall, the operand's address and
the message length cross as words, the state owned, and the result is the state
with its report pushed (`RoutedArms.Report`).

The `.shortArgs` arm, a configure or a service register of the inline words
alone, is here too: its operand found and checked, it is refused as missing its
fifth argument (`shortArgsRoutedArm`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- The overflowed arm's body as the specification states it
(`syscallEntryCheckedK`), over the operand dispatch `op` (handed the overflow
word and the caller's registers): slot 0 and the next page's first slot read,
then `op` on the entry's state when this core's TLB already holds the buffer's
translations, and otherwise on the state with them filled, a refusal handing
back the TLB the entry held.  Its result reported
under the entry's first continuation. -/
def overflowedArmSpec (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (length : Nat)
    (op : UInt64 → SeLe4n.RegisterFile → RefusalCarrying Unit) (st : SystemState) :
    SystemState :=
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
      SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
        (fun _ => entryReportGeneral (.error (.invalidMessageInfo, st)))
        (fun w =>
          SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid
            (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (length - 4))
            (fun _ => entryReportGeneral (.error (.invalidMessageInfo, st)))
            (fun _ => entryReportGeneral (
              if SeLe4n.Kernel.Architecture.ipcBufferFillHeldIn st executingCore tid (length - 4) then
                op w tcb.registerContext st
              else
                let n0 := (SeLe4n.Kernel.Architecture.tlbOnCore st executingCore).entries.length
                match op w tcb.registerContext
                    (SeLe4n.Kernel.Architecture.tlbFillIpcBufferInOnCore st executingCore tid
                        (length - 4)) with
                | .error (e, stF) =>
                  .error (e, SeLe4n.Kernel.Architecture.tlbUndoFillOnCore stF executingCore n0)
                | .ok r => .ok r)))
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
      SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
        (fun _ => entryReportGeneral (.error (.invalidMessageInfo, st)))
        (fun w =>
          SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid
            (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (length - 4))
            (fun _ => entryReportGeneral (.error (.invalidMessageInfo, st)))
            (fun _ =>
              let held := SeLe4n.Kernel.Architecture.ipcBufferFillHeldIn st executingCore tid (length - 4)
              let n0 := (SeLe4n.Kernel.Architecture.tlbOnCore st executingCore).entries.length
              let st1 := if held then st
                else SeLe4n.Kernel.Architecture.tlbFillIpcBufferInOnCore st executingCore tid
                        (length - 4)
              entryReportGeneral (
                match op w tcb.registerContext st1 with
                | .error (e, stF) =>
                  .error (e, if held then stF
                    else SeLe4n.Kernel.Architecture.tlbUndoFillOnCore stF executingCore n0)
                | .ok r => .ok r)))
  | _ => entryReportGeneral (.error (.illegalState, st))

theorem overflowedArmWith_eq_spec (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (length : Nat)
    (op : UInt64 → SeLe4n.RegisterFile → RefusalCarrying Unit) (st : SystemState) :
    overflowedArmWith ctx executingCore tid length op st =
      overflowedArmSpec ctx executingCore tid length op st := by
  unfold overflowedArmWith overflowedArmSpec
  split
  · congr 1
    funext w
    congr 1
    funext _
    cases hH : SeLe4n.Kernel.Architecture.ipcBufferFillHeldIn st executingCore tid (length - 4)
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [↓reduceIte]
      rcases op w _ st with ⟨e, stF⟩ | r <;> rfl
  · rfl

/-- **The overflowed arm's body for a call with an operand**: slot 0 and the
next page's first slot read, then the long route's operand dispatch of `arm`
(handed the overflow word and the caller's registers) on the state whose TLB
holds the buffer's translations, a refusal handing back the TLB the entry held;
a refusal reported under the entry's resolved or lookup continuation as the
dispatch told them apart, so the entry never resolves the operand again
(`overflowedRoutedArm_eq`). -/
@[inline] def overflowedLongArmWith (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (sid : SyscallId) (length : Nat) (capAddr : SeLe4n.CPtr)
    (arm : UInt64 → SeLe4n.RegisterFile → Option Capability → RefusalCarrying Unit)
    (st : SystemState) : SystemState :=
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
      SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
        (fun _ => entryReportGeneral (.error (.invalidMessageInfo, st)))
        (fun w =>
          SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid
            (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (length - 4))
            (fun _ => entryReportGeneral (.error (.invalidMessageInfo, st)))
            (fun _ => longOperandK sid capAddr tid executingCore (arm w tcb.registerContext)
              (length - 4) st entryReportGeneral entryReportResolved entryReportLookup))
  | _ => entryReportGeneral (.error (.illegalState, st))

/-- The overflowed arm of an invocation. -/
@[noinline] def overflowedInvocationRoutedArm (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (sid : SyscallId)
    (capWord : UInt64) (length : Nat) (st : SystemState) : SystemState :=
  overflowedLongArmWith executingCore tid sid length (SeLe4n.CPtr.ofWord capWord) (fun _ rf =>
    invocationOperandArmR ctx sid (SeLe4n.CPtr.ofWord capWord) rf tid executingCore) st

/-- The overflowed arm of a declassification or an audit call. -/
@[noinline] def overflowedAuditedRoutedArm (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (sid : SyscallId)
    (capWord : UInt64) (length : Nat) (st : SystemState) : SystemState :=
  overflowedLongArmWith executingCore tid sid length (SeLe4n.CPtr.ofWord capWord) (fun _ rf =>
    auditedOperandArmR ctx sid rf (SeLe4n.CPtr.ofWord capWord) tid executingCore) st

/-- The overflowed arm of a five-word invocation, its fifth word slot 0's. -/
@[noinline] def overflowedFiveWordRoutedArm (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (sid : SyscallId)
    (capWord : UInt64) (length : Nat) (st : SystemState) : SystemState :=
  match sid with
  | .schedContextConfigure =>
    overflowedLongArmWith executingCore tid sid length (SeLe4n.CPtr.ofWord capWord) (fun w rf =>
      configureOperandArmR rf w tid) st
  | _ =>
    overflowedLongArmWith executingCore tid sid length (SeLe4n.CPtr.ofWord capWord) (fun w rf =>
      serviceRegisterOperandArmR ctx tid rf w) st

/-- The overflowed arm of a wait, a receive or a yield.  A long signal is a
signal (`routedNoOverflowOf`): it reads no overflow word. -/
@[noinline] def overflowedNotificationRoutedArm (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (sid : SyscallId)
    (capWord : UInt64) (length : Nat) (st : SystemState) : SystemState :=
  match sid with
  | .notificationWait =>
    overflowedLongArmWith executingCore tid sid length (SeLe4n.CPtr.ofWord capWord) (fun _ _ =>
      waitOperandArmThenTaintR ctx tid executingCore (syscallRequiredRight .notificationWait)) st
  | .receive =>
    overflowedLongArmWith executingCore tid sid length (SeLe4n.CPtr.ofWord capWord) (fun _ rf =>
      receiveOperandArmThenTaintR ctx tid length (SeLe4n.CPtr.ofWord (readRegWord rf ⟨2⟩))
        executingCore (syscallRequiredRight .receive)) st
  | _ =>
    overflowedArmWith ctx executingCore tid length (fun _ _ st =>
      match yieldOnCoreR st executingCore with
      | .error r => .error r
      | .ok st' => .ok ((), st')) st

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

/-- The overflowed arm is, for every call the route admits but the yield, the
long operand dispatch of its arm (`overflowedArmOf`), and for the yield the
specification's body over the overflowed dispatch. -/
theorem overflowedRoutedArm_eq (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (sid : SyscallId) (capWord : UInt64) (length : Nat)
    (st : SystemState) (hOv : Architecture.RegisterDecode.routedOverflowed sid = true) :
    overflowedRoutedArm ctx executingCore tid sid capWord length st =
      if sid ≠ .yield then
        overflowedLongArmWith executingCore tid sid length (SeLe4n.CPtr.ofWord capWord) (fun w rf =>
          overflowedArmOf ctx sid (SeLe4n.CPtr.ofWord capWord) rf length w tid executingCore) st
      else
        overflowedArmSpec ctx executingCore tid length (fun w rf =>
          dispatchOverflowedCheckedR ctx sid (SeLe4n.CPtr.ofWord capWord) rf length w tid
            executingCore) st := by
  unfold overflowedRoutedArm
  by_cases hI : Architecture.RegisterDecode.routedInvocation sid = true
  · have hY : sid ≠ .yield := by rintro rfl; exact absurd hI (by decide)
    simp only [hI, hY, ↓reduceIte, ne_eq, not_false_eq_true, overflowedInvocationRoutedArm,
      overflowedArmOf]
  by_cases hA : Architecture.RegisterDecode.routedAudited sid = true
  · have hY : sid ≠ .yield := by rintro rfl; exact absurd hA (by decide)
    simp only [hI, hA, hY, ↓reduceIte, ne_eq, not_false_eq_true, Bool.false_eq_true,
      overflowedAuditedRoutedArm, overflowedArmOf]
  by_cases hO : Architecture.RegisterDecode.routedOverflowOne sid = true
  · have hY : sid ≠ .yield := by rintro rfl; exact absurd hO (by decide)
    simp only [hI, hA, hO, hY, ↓reduceIte, ne_eq, not_false_eq_true, Bool.false_eq_true,
      overflowedFiveWordRoutedArm, overflowedArmOf]
    have hC : sid = .schedContextConfigure ∨ sid = .serviceRegister := by
      revert hO; cases sid <;> decide
    rcases hC with rfl | rfl <;> rfl
  simp only [hI, hA, hO, ↓reduceIte, Bool.false_eq_true, overflowedNotificationRoutedArm,
    overflowedArmOf]
  rcases routedOverflowed_cases hOv (by simpa using hI) (by simpa using hA) with
    rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rfl
    | (exfalso; revert hO; decide)
    | (simp only [ne_eq, not_true_eq_false, ↓reduceIte, overflowedArmWith_eq_spec]; rfl)

/-- **The short-arguments arm**: `dispatchOperandCheckedK` on the operand and the
refusal of a five-word invocation short of its fifth word
(`shortArgsOperandArmR`), its results reported. -/
@[noinline] def shortArgsRoutedArm (executingCore : Concurrency.CoreId) (tid : SeLe4n.ThreadId)
    (sid : SyscallId) (capWord : UInt64) (st : SystemState) : SystemState :=
  dispatchOperandCheckedK sid (SeLe4n.CPtr.ofWord capWord) tid executingCore
    (shortArgsOperandArmR sid) st entryReportGeneral entryReportResolved entryReportLookup

end SeLe4n.Kernel
