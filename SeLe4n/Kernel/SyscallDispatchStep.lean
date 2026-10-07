-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-LS LS2.4: the atomic step the live syscall seam commits, as its own
-- module.  It was a section of `SyscallDispatchEntry.lean` (WS-RR RR7.12); it
-- moves out so that the seam's coverage theorem (`SyscallSeamCoverage.lean`)
-- can be stated over the step and the seam's `BracketSpec` can carry that
-- theorem as its `covers` field without the two modules importing each other.
-- Nothing about the step changed in the move.

import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore
import SeLe4n.Kernel.Scheduler.Operations.ReschedulePending
import SeLe4n.Kernel.Architecture.TlbShootdownProtocol
import SeLe4n.Kernel.Architecture.PerCoreCacheModel
import SeLe4n.Platform.FFI

/-!
# WS-LS LS2.4 — The cross-core syscall step

`syscallDispatchCrossCoreStep` is the pure function the live syscall seam
(`syscallDispatchCrossCoreEntry`, `SyscallDispatchEntry.lean`) hands
`Platform.FFI.modifyGetKernelState`: the verified ABI dispatch, the executing
core's local reschedule and residency settling, and the diffs the runtime half
consumes, in one atomic step.  Its two equations — the step on the dispatch's
result and the drained physical-write ledger — are stated here beside it.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind)

/-- **WS-RR RR7.12**: the atomic step the live syscall seam commits, as a named
function.

Extracted from `syscallDispatchCrossCoreEntry`'s `modifyGetKernelState` closure
verbatim — the dispatch, the inline local reschedule, and the five diffs the
runtime half consumes — so that the declared-footprint bracket has something to
wrap.  Nothing about it changed in the extraction; every property the entry's
docstring records about placement (the reschedule *inside* the atomic step, the
diffs against the **final** state `st''` rather than the pre-reschedule `st'`)
is a property of this function now.

The diffs are taken against **this function's own input**, which under the
bracket is the state the growing phase ended in.  That is what keeps the runtime
half honest: the growing phase's writes are lock words, and pokes derived
against a base that already carries them describe the state the action saw.

Inlined into the entry (WS-ZA ZA3.2), so the entry reads each component of the
result where it is computed and the nested tuple is never built. -/
@[inline] def syscallDispatchCrossCoreStep (ctx : LabelingContext) (execCore : CoreId)
    (syscallId : UInt32) (x0 x1 x2 x3 x4 x5 : UInt64)
    (ipcBufferAddr elr spsr spEl0 x30 : UInt64) (st : SystemState) :
    (Architecture.SyscallOutcome × List (CoreId × SgiKind) × List CoreId ×
      List Architecture.TlbInvalidation × (Nat × Nat) ×
      List Architecture.ICacheInvalidation × List Architecture.PhysicalWrite ×
      Architecture.RestoreTarget × Option SeLe4n.ThreadId) × SystemState :=
  -- KSC-1: everything the commit reads of the pre-state is captured here, before
  -- the dispatch consumes `st` — the caller, the reschedule flags (`numCores`
  -- bits) and the shootdown record — so `st` is dead once the dispatch starts.
  let caller? := st.scheduler.currentOnCore execCore
  let pending0 := reschedulePendingSnapshot st
  let tlb0 := st.tlbShootdown
  match hD : Platform.FFI.syscallDispatchFromAbi ctx execCore syscallId x0 x1 x2 x3 x4 x5
      ipcBufferAddr elr spsr spEl0 x30 st with
  | Except.ok (outcome, st') =>
      -- WS-BP BP7.4: the returning caller's result is in its saved context and
      -- the core's bank before any local reschedule, so a switch saves it.
      let stR := Architecture.stageCallerReturnFor caller? st' execCore outcome
      -- PR #904 review (`v0.36.41`): settle what this core resumes — a thread
      -- still resident on another core is deferred, and the one resumed here
      -- becomes this core's resident thread (`settleResidencyOnCore`).
      let st'' := PriorityInheritance.settleResidencyOnCore
        (PriorityInheritance.scheduleLocalSuccessorFrom caller? stR execCore) execCore
      -- KSC-1: a remote core is poked when the step raised its reschedule flag
      -- (`syscallDispatchCrossCoreStep_sgis_cover_diff`: the flags cover the old
      -- whole-index diff, which stays as the specification).
      ((outcome, rescheduleSgisFromFlags pending0 st''.scheduler.reschedulePending,
        Architecture.shootdownChangedTargetsFrom tlb0 st'',
        Architecture.shootdownPostedOpsFrom tlb0 st'',
        Architecture.shootdownRoundWindowFrom tlb0 st'',
        st''.pendingIcacheMaintenance,
        st''.pendingPhysicalWrites,
        Architecture.restoreTargetOnCore st'' execCore,
        st''.scheduler.currentOnCore execCore),
       Architecture.clearPhysicalWrites (Architecture.clearIcacheMaintenance st''))
  | Except.error e =>
      -- Unreachable (`syscallDispatchFromAbi_ne_error`); discharged rather than
      -- answered from `st`, which would keep the pre-state alive.
      absurd hD (Platform.FFI.syscallDispatchFromAbi_ne_error ctx execCore syscallId
        x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 st e)

/-- **The step, on the dispatch's result**: the committed state and the result
tuple, every pre-state read being one of the three captures. -/
theorem syscallDispatchCrossCoreStep_of_ok {ctx : LabelingContext} {execCore : CoreId}
    {syscallId : UInt32} {x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64}
    {st st' : SystemState} {outcome : Architecture.SyscallOutcome}
    (h : Platform.FFI.syscallDispatchFromAbi ctx execCore syscallId x0 x1 x2 x3 x4 x5
      ipcBufferAddr elr spsr spEl0 x30 st = Except.ok (outcome, st')) :
    syscallDispatchCrossCoreStep ctx execCore syscallId x0 x1 x2 x3 x4 x5
        ipcBufferAddr elr spsr spEl0 x30 st =
      let st'' := PriorityInheritance.settleResidencyOnCore
        (PriorityInheritance.scheduleLocalSuccessorFrom (st.scheduler.currentOnCore execCore)
          (Architecture.stageCallerReturnFor (st.scheduler.currentOnCore execCore) st' execCore
            outcome) execCore) execCore
      ((outcome,
        rescheduleSgisFromFlags st.scheduler.reschedulePending st''.scheduler.reschedulePending,
        Architecture.shootdownChangedTargetsFrom st.tlbShootdown st'',
        Architecture.shootdownPostedOpsFrom st.tlbShootdown st'',
        Architecture.shootdownRoundWindowFrom st.tlbShootdown st'',
        st''.pendingIcacheMaintenance,
        st''.pendingPhysicalWrites,
        Architecture.restoreTargetOnCore st'' execCore,
        st''.scheduler.currentOnCore execCore),
       Architecture.clearPhysicalWrites (Architecture.clearIcacheMaintenance st'')) := by
  unfold syscallDispatchCrossCoreStep
  split
  · rename_i o s hD
    rw [h] at hD; cases hD; rfl
  · rename_i e hD
    rw [h] at hD; cases hD

/-- **WS-BP BP7.2 (the ledger is drained exactly once)**: the state the step
commits owes no physical write, and the writes it hands the runtime are the ones
the committed transition recorded.  So a write is performed once — by the seam
this commit returns to — and none is stranded into the next syscall. -/
theorem syscallDispatchCrossCoreStep_drains_physicalWrites (ctx : LabelingContext)
    (execCore : CoreId) (syscallId : UInt32)
    (x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64) (st : SystemState) :
    ∃ outcome st',
      Platform.FFI.syscallDispatchFromAbi ctx execCore syscallId x0 x1 x2 x3 x4 x5
          ipcBufferAddr elr spsr spEl0 x30 st = Except.ok (outcome, st') ∧
      (syscallDispatchCrossCoreStep ctx execCore syscallId x0 x1 x2 x3 x4 x5
          ipcBufferAddr elr spsr spEl0 x30 st).2.pendingPhysicalWrites = [] ∧
      (syscallDispatchCrossCoreStep ctx execCore syscallId x0 x1 x2 x3 x4 x5
          ipcBufferAddr elr spsr spEl0 x30 st).1.2.2.2.2.2.2.1 =
        (PriorityInheritance.settleResidencyOnCore
          (PriorityInheritance.scheduleLocalSuccessor st
            (Architecture.stageCallerReturn st st' execCore outcome) execCore)
          execCore).pendingPhysicalWrites := by
  obtain ⟨outcome, st', h⟩ := Platform.FFI.syscallDispatchFromAbi_total ctx execCore syscallId
    x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 st
  refine ⟨outcome, st', h, ?_, ?_⟩ <;> rw [syscallDispatchCrossCoreStep_of_ok h]
  · simp
  · rfl

end SeLe4n.Kernel
