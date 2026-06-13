-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM SM6.A cross-core IPC (the live BaseIO seam +
-- @[export]; the pure dispatch ops live in EndpointCallDispatch, below the API
-- layer; see docs/planning/SMP_CROSS_CORE_IPC_PLAN.md).

import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDispatch
import SeLe4n.Kernel.Concurrency.Runtime
import SeLe4n.Platform.FFI

/-!
# WS-SM SM6.A — Cross-core endpoint call: the live FFI seam

The BaseIO live driver and the `@[export]` C symbol for the cross-core `Call`,
layered over the pure `endpointCallCrossCoreDispatch` (in `EndpointCallDispatch`,
below the API layer).  Reads the executing core (`currentCoreId`), commits the
dispatch atomically against the kernel state ref (`modifyGetKernelState`), then
fires the surfaced SGI (`emitWakeSgi`).  Mirrors the SM5.I `perCoreTimerTickEntry`
pattern.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind)

-- ============================================================================
-- §1  Live FFI seam (the SM5.I `perCoreTimerTickEntry` pattern)
-- ============================================================================

/-- WS-SM SM6.A.10 (reference BaseIO driver): run a cross-core `Call` against the
live kernel state.  Reads the executing core from the hardware (`currentCoreId`,
`TPIDR_EL1`), commits `endpointCallCrossCoreDispatch` **atomically** against the
kernel state ref (`modifyGetKernelState`), then — *after* the state commit is
globally visible — fires the recovered cross-core `.reschedule` SGI
(`emitWakeSgi`; the BKL release→acquire ordering, SM5.C.4) directly from the
operation's *surfaced* SGI.

NOTE: this direct endpoint-call driver is **not** the live `.call` entry — the
production cross-core `.call` routes through the *syscall* dispatch
(`SyscallDispatchEntry.syscallDispatchCrossCoreEntry`, the
`@[export lean_syscall_dispatch_cross_core]` symbol the Rust SVC handler resolves
against), which decodes the full trap-frame context and recovers the SGIs from the
`(pre, post)` state *diff* (`computeCrossCoreSgis`).  This driver is retained as a
reference for the surfaced-SGI firing pattern; it takes the full message /
capability context (unlike a syscall entry, it is not fed a decoded trap frame),
so it is not given a C `@[export]` (a 2-arg empty-context export would bypass the
syscall-ABI decode and capability/flow validation — PR #820 review #4). -/
def endpointCallCrossCoreEntry
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot) :
    BaseIO (Except KernelError CapTransferSummary) := do
  let executingCore ← Concurrency.currentCoreId
  let result ← Platform.FFI.modifyGetKernelState (fun st =>
    let (st', res) := endpointCallCrossCoreDispatch endpointId caller msg endpointRights
      callerCspaceRoot receiverSlotBase executingCore st
    match res with
    -- Fail-closed atomicity: on any dispatch error commit the *original* `st`,
    -- discarding the partial post-state `st'` (a mid-rendezvous failure — e.g. a
    -- missing receiver CSpace root or a donation failure — would otherwise leave
    -- the receiver woken / caller blocked on a syscall that returns an error).
    -- Mirrors the Kernel-monad dispatch arm, which drops post-state on `.error`.
    | .error e => ((Except.error e, (none : Option (CoreId × SgiKind))), st)
    | .ok (summary, sgi) => ((Except.ok summary, sgi), st'))
  Concurrency.emitWakeSgi result.2
  pure result.1

-- WS-SM SM6.A.10 / PR #820 review #4: the former 2-arg
-- `@[export lean_endpoint_call_cross_core]` C seam (`endpointCallCrossCoreExport`)
-- was removed.  It fed `endpointCallCrossCoreEntry` an *empty* message / cap set
-- / root-slot 0, so wiring it would have delivered payload-less, Grant-less calls
-- with the raw endpoint/caller ids bypassing the `syscallInvoke` / checked-dispatch
-- capability and flow validation.  The live cross-core `.call` is the full-context
-- `syscallDispatchCrossCoreEntry` (`@[export lean_syscall_dispatch_cross_core]`),
-- which the Rust SVC handler resolves against; this module keeps only the
-- reference BaseIO driver above.

/-- WS-SM SM6.A.10: the reference driver's three-phase shape — read the executing
core, atomically commit the dispatch, then fire the surfaced SGI. -/
theorem endpointCallCrossCoreEntry_def
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet) (callerCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) :
    endpointCallCrossCoreEntry endpointId caller msg endpointRights callerCspaceRoot
        receiverSlotBase
      = (do
          let executingCore ← Concurrency.currentCoreId
          let result ← Platform.FFI.modifyGetKernelState (fun st =>
            let (st', res) := endpointCallCrossCoreDispatch endpointId caller msg endpointRights
              callerCspaceRoot receiverSlotBase executingCore st
            match res with
            | .error e => ((Except.error e, (none : Option (CoreId × SgiKind))), st)
            | .ok (summary, sgi) => ((Except.ok summary, sgi), st'))
          Concurrency.emitWakeSgi result.2
          pure result.1) := rfl

end SeLe4n.Kernel
