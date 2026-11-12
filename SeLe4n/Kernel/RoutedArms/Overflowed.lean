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

The routed entry's `.overflowed` arm (`syscallEntryCheckedK`): a five-word
invocation (a scheduling-context configure, a service register or a CNode
mint) whose
message runs past the inline words, as its own function.  Only a syscall that
reads its overflow words is routed past the inline registers
(`syscallReadsOverflow`), so no other kind reaches this arm.  Its overflow
words read as the long send's are (slot 0 and the next page's first slot), the
call runs the long route's operand dispatch (`longOperandK`) on the state with
this core's TLB holding the buffer's translations, a refusal handing back the
TLB the entry held, so a refusal reaches the entry's resolved or lookup
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

/-- **The overflowed arm's body**: slot 0 and the next page's first slot read,
then the long route's operand dispatch of `arm` (handed the overflow word and
the caller's registers) on the state whose TLB holds the buffer's
translations, a refusal handing back the TLB the entry held; a slot that does
not read runs the short-arguments arm (`overflowedRoutedArm_eq`). -/
@[inline] def overflowedLongArmWith (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (sid : SyscallId) (length : Nat) (capWord : UInt64)
    (arm : UInt64 → SeLe4n.RegisterFile → Option Capability → RefusalCarrying Unit)
    (st : SystemState) : SystemState :=
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
      SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid 0
        (fun _ => shortArgsRoutedArm executingCore tid sid capWord st)
        (fun w =>
          SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReadMrK st tid
            (SeLe4n.Kernel.Architecture.IpcBufferRead.overflowSecondRead tcb.ipcBuffer (length - 4))
            (fun _ => shortArgsRoutedArm executingCore tid sid capWord st)
            (fun _ => longOperandK sid (SeLe4n.CPtr.ofWord capWord) tid executingCore
              (arm w tcb.registerContext) (length - 4) st entryReportGeneral
              entryReportResolved entryReportLookup))
  | _ => entryReportGeneral (.error (.illegalState, st))

/-- **The overflowed arm**: the configure's, the service register's or the CNode
mint's, its fifth word slot 0's. -/
@[noinline] def overflowedRoutedArm (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (sid : SyscallId)
    (capWord : UInt64) (length : Nat) (st : SystemState) : SystemState :=
  match sid with
  | .schedContextConfigure =>
    overflowedLongArmWith executingCore tid sid length capWord (fun w rf =>
      configureOperandArmR rf w tid) st
  | .cspaceMint =>
    overflowedLongArmWith executingCore tid sid length capWord (fun w rf =>
      mintOperandArmR ctx tid rf w) st
  | _ =>
    overflowedLongArmWith executingCore tid sid length capWord (fun w rf =>
      serviceRegisterOperandArmR ctx tid rf w) st

/-- The overflowed arm is the long operand dispatch of the route's arm
(`overflowedArmOf`). -/
theorem overflowedRoutedArm_eq (ctx : LabelingContext) (executingCore : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (sid : SyscallId) (capWord : UInt64) (length : Nat)
    (st : SystemState) (hOv : Architecture.RegisterDecode.routedOverflowOne sid = true) :
    overflowedRoutedArm ctx executingCore tid sid capWord length st =
      overflowedLongArmWith executingCore tid sid length capWord (fun w rf =>
        overflowedArmOf ctx sid rf w tid) st := by
  rcases routedOverflowOne_cases hOv with rfl | rfl | rfl <;> rfl

end SeLe4n.Kernel
