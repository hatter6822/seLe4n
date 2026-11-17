-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RoutedArms.Report
import SeLe4n.Kernel.RoutedArms.OverflowOne

/-!
# The overflowed route's arm, out of line

The routed entry's `.overflowed` arm (`syscallEntryCheckedK`): an invocation
past the inline words (a scheduling-context configure, a service register, a
CNode copy, a CNode mint, whose sixth word is slot 1's, or an untyped retype,
whose sixth and seventh are slots 1 and 2's, each read off the state the arm is
handed) whose message runs past them, as its own function.  Only a syscall that
reads its overflow words is routed past the inline registers
(`syscallReadsOverflow`), so no other kind reaches this arm.  Its overflow
words read as the long send's are (slot 0, the buffer in one frame), the
call runs the operand dispatch (`dispatchOperandCheckedK`) on the state it is
handed, so a refusal reaches the entry's resolved or lookup
continuation as the dispatch told them apart and the operand is never resolved
a second time.  An overflow slot that does not read clamps the message to its
inline words, as seL4's `handleInvocation` clamps a message with no IPC
buffer, and the invocation is refused short of its fifth argument once its
operand is found and checked (`shortArgsRoutedArm`).  The syscall, the
operand's address and the message length cross as words, the state owned, and
the result is the state with its report pushed (`RoutedArms.Report`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The overflowed arm's body**: slot 0 read,
then the long route's operand dispatch of `arm` (handed the overflow word and
the caller's registers) on the state it is handed; a slot that does
not read runs the short-arguments arm (`overflowedRoutedArm_eq`). -/
@[inline] def overflowedLongArmWith (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (sid : SyscallId) (length : Nat) (capWord : UInt64) (xc : Nat)
    (arm : UInt64 → SeLe4n.RegisterFile → Option Capability → RefusalCarrying Unit)
    (st : SystemState) : SystemState :=
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
      SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
        (fun _ => shortArgsRoutedArm executingCore tid sid capWord xc st)
        (fun w => dispatchOperandCheckedKW sid (SeLe4n.CPtr.ofWord capWord) tid executingCore xc
              (arm w tcb.registerContext) st entryReportGeneral
              (entryReportPushOk 1) (entryReportPushErrorW 1) entryReportLookup
              entryReportLookupAtW)
  | _ => entryReportGeneral (.error (.illegalState, st))

/-- **The overflowed arm**: the configure's, the service register's, the CNode
copy's, the CNode mint's or the untyped retype's, its fifth word slot 0's, a
mint's sixth slot 1's and a retype's sixth and seventh slots 1 and 2's; a retype
of six words is refused short of its seventh. -/
@[noinline] def overflowedRoutedArm (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (sid : SyscallId)
    (capWord : UInt64) (xc : Nat) (length : Nat) (st : SystemState) : SystemState :=
  match sid with
  | .schedContextConfigure =>
    overflowedLongArmWith executingCore tid sid length capWord xc (fun w rf =>
      configureOperandArmR rf w tid xc) st
  | .cspaceCopy =>
    overflowedLongArmWith executingCore tid sid length capWord xc (fun w rf =>
      copyOperandArmR ctx tid xc rf w) st
  | .cspaceMint =>
    overflowedLongArmWith executingCore tid sid length capWord xc (fun w rf =>
      mintOperandArmR ctx tid xc rf w (overflowWordAt st tid 1)) st
  | .untypedRetype =>
    overflowedLongArmWith executingCore tid sid length capWord xc (fun w rf =>
      if length < SeLe4n.Kernel.Architecture.SyscallArgDecode.truncationMinimum .untypedRetype then
        shortArgsOperandArmR .untypedRetype
      else
        retypeOperandArmR tid executingCore (SeLe4n.CPtr.ofWord capWord) xc rf w
          (overflowWordAt st tid 1) (overflowWordAt st tid 2)) st
  | _ =>
    overflowedLongArmWith executingCore tid sid length capWord xc (fun w rf =>
      serviceRegisterOperandArmR ctx tid xc rf w) st

/-- The overflowed arm is the long operand dispatch of the route's arm
(`overflowedArmOf`). -/
theorem overflowedRoutedArm_eq (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (sid : SyscallId) (capWord : UInt64) (xc : Nat) (length : Nat)
    (st : SystemState) (hOv : Architecture.RegisterDecode.routedOverflowOne sid = true) :
    overflowedRoutedArm ctx executingCore tid sid capWord xc length st =
      overflowedLongArmWith executingCore tid sid length capWord xc (fun w rf =>
        overflowedArmOf ctx sid rf w (overflowWordAt st tid 1) (overflowWordAt st tid 2) length
          tid executingCore (SeLe4n.CPtr.ofWord capWord) xc) st := by
  rcases routedOverflowOne_cases hOv with rfl | rfl | rfl | rfl | rfl <;> rfl

end SeLe4n.Kernel
