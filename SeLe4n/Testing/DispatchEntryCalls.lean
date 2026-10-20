-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.FFI
import SeLe4n.Kernel.SyscallDispatchEntry

/-!
# Out-of-line syscall entries for the test suites

The kernel's syscall entries are `@[inline]` so the exported entry reads each
component of its result where it is computed and builds no result record
(`syscallDispatchFromAbiImpl`, `syscallDispatchCrossCoreStep`,
`syscallDispatchCrossCoreBracketedStep`, and the bracket record
`syscallDispatchBracket` whose step is the cross-core step).  A suite that calls one of them
therefore receives the whole kernel inlined into each calling helper: a single
C function of 70k–190k lines, which clang compiles in tens of minutes.

The suites call these copies instead.  The ABI entry and the cross-core step
are compiled once, here; the bracketed step and the bracket record call that
one step.  Each is the entry it names by `rfl` (the `_eq` theorems below), so a
suite's checks and proofs read the same function the kernel exports.
-/

namespace SeLe4n.Testing

open SeLe4n.Model
open SeLe4n.Kernel

/-- `Platform.FFI.syscallDispatchFromAbi`, compiled once. -/
@[noinline] def dispatchFromAbi (ctx : LabelingContext)
    (executingCore : SeLe4n.Kernel.Concurrency.CoreId) (syscallId : UInt32)
    (x0 x1 x2 x3 x4 x5 : UInt64) (ipcBufferAddr : UInt64)
    (elr spsr spEl0 x30 : UInt64) (st : SystemState) :
    Except KernelError (Architecture.SyscallOutcome × SystemState) :=
  Platform.FFI.syscallDispatchFromAbi ctx executingCore syscallId x0 x1 x2 x3 x4 x5
    ipcBufferAddr elr spsr spEl0 x30 st

/-- `syscallDispatchCrossCoreStep`, compiled once. -/
@[noinline] def dispatchCrossCoreStep (ctx : LabelingContext)
    (execCore : SeLe4n.Kernel.Concurrency.CoreId) (syscallId : UInt32)
    (x0 x1 x2 x3 x4 x5 : UInt64) (ipcBufferAddr elr spsr spEl0 x30 : UInt64)
    (st : SystemState) :
    (Architecture.SyscallOutcome × PerCoreFlags × List SeLe4n.Kernel.Concurrency.CoreId ×
      List Architecture.TlbInvalidation × (Nat × Nat) ×
      List Architecture.ICacheInvalidation × Architecture.PhysicalWriteLedger ×
      Architecture.RestoreTarget × Option SeLe4n.ThreadId) × SystemState :=
  syscallDispatchCrossCoreStep ctx execCore syscallId x0 x1 x2 x3 x4 x5
    ipcBufferAddr elr spsr spEl0 x30 st

/-- `syscallDispatchCrossCoreBracketedStep`: the bracket runs its step, so this
is the cross-core step at the trapped context's words. -/
def dispatchCrossCoreBracketedStep (ctx : LabelingContext)
    (execCore : SeLe4n.Kernel.Concurrency.CoreId) (syscallId : UInt32)
    (trapped : Architecture.InFlightContext) (st : SystemState) :
    (Architecture.SyscallOutcome × PerCoreFlags × List SeLe4n.Kernel.Concurrency.CoreId ×
      List Architecture.TlbInvalidation × (Nat × Nat) ×
      List Architecture.ICacheInvalidation × Architecture.PhysicalWriteLedger ×
      Architecture.RestoreTarget × Option SeLe4n.ThreadId) × SystemState :=
  dispatchCrossCoreStep ctx execCore syscallId
    trapped.x0 trapped.x1 trapped.x2 trapped.x3 trapped.x4 trapped.x5
    trapped.x6 trapped.pc trapped.pstate trapped.sp trapped.x30 st

/-- `syscallDispatchBracket`, with its step the out-of-line cross-core step. -/
@[noinline] def dispatchBracket (ctx : LabelingContext)
    (execCore : SeLe4n.Kernel.Concurrency.CoreId) (syscallId : UInt32)
    (trapped : Architecture.InFlightContext) :
    SeLe4n.Kernel.Concurrency.BracketSpec
      (Architecture.SyscallOutcome × PerCoreFlags × List SeLe4n.Kernel.Concurrency.CoreId ×
        List Architecture.TlbInvalidation × (Nat × Nat) ×
        List Architecture.ICacheInvalidation × Architecture.PhysicalWriteLedger ×
        Architecture.RestoreTarget × Option SeLe4n.ThreadId) :=
  { syscallDispatchBracket ctx execCore syscallId trapped with
    step := dispatchCrossCoreBracketedStep ctx execCore syscallId trapped }

theorem dispatchFromAbi_eq ctx c id x0 x1 x2 x3 x4 x5 ipc elr spsr sp x30 st :
    dispatchFromAbi ctx c id x0 x1 x2 x3 x4 x5 ipc elr spsr sp x30 st =
      Platform.FFI.syscallDispatchFromAbi ctx c id x0 x1 x2 x3 x4 x5 ipc elr spsr sp x30 st :=
  rfl

theorem dispatchCrossCoreStep_eq ctx c id x0 x1 x2 x3 x4 x5 ipc elr spsr sp x30 st :
    dispatchCrossCoreStep ctx c id x0 x1 x2 x3 x4 x5 ipc elr spsr sp x30 st =
      syscallDispatchCrossCoreStep ctx c id x0 x1 x2 x3 x4 x5 ipc elr spsr sp x30 st :=
  rfl

theorem dispatchCrossCoreBracketedStep_eq ctx c id trapped st :
    dispatchCrossCoreBracketedStep ctx c id trapped st =
      syscallDispatchCrossCoreBracketedStep ctx c id trapped st :=
  rfl

theorem dispatchBracket_eq ctx c id trapped :
    dispatchBracket ctx c id trapped = syscallDispatchBracket ctx c id trapped :=
  rfl

end SeLe4n.Testing
