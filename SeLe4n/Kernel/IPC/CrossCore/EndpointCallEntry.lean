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

/-- WS-SM SM6.A.10 (live driver): run a cross-core `Call` against the live
kernel state.  Reads the executing core from the hardware (`currentCoreId`,
`TPIDR_EL1`), commits `endpointCallCrossCoreDispatch` **atomically** against the
kernel state ref (`modifyGetKernelState`), then — *after* the state commit is
globally visible — fires the recovered cross-core `.reschedule` SGI
(`emitWakeSgi`; the BKL release→acquire ordering, SM5.C.4).  This is the live
analogue of the SM5.I `perCoreTimerTickEntry` seam, for the IPC `Call` path. -/
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
    | .error e => ((Except.error e, (none : Option (CoreId × SgiKind))), st')
    | .ok (summary, sgi) => ((Except.ok summary, sgi), st'))
  Concurrency.emitWakeSgi result.2
  pure result.1

/-- WS-SM SM6.A.10 (C entry): the `@[export]` cross-core `Call` symbol the Rust
syscall handler resolves against.  Takes the resolved endpoint object id and
caller thread id; the full message + capability decode from the trap frame is
the syscall-ABI layer above (identical to the single-core entry, which decodes
via the `SyscallDecodeResult` pipeline before invoking the operation).  Returns
the `KernelError`-encoded status word. -/
@[export lean_endpoint_call_cross_core]
def endpointCallCrossCoreExport (endpointIdRaw callerRaw : UInt64) :
    BaseIO UInt32 := do
  let res ← endpointCallCrossCoreEntry (SeLe4n.ObjId.ofNat endpointIdRaw.toNat)
    (SeLe4n.ThreadId.ofNat callerRaw.toNat) IpcMessage.empty AccessRightSet.empty
    (SeLe4n.ObjId.ofNat 0) (SeLe4n.Slot.ofNat 0)
  match res with
  | .ok _ => pure 0
  | .error e => pure (Platform.FFI.KernelError.toUInt32 e)

/-- WS-SM SM6.A.10: the live driver's three-phase shape — read the executing
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
            | .error e => ((Except.error e, (none : Option (CoreId × SgiKind))), st')
            | .ok (summary, sgi) => ((Except.ok summary, sgi), st'))
          Concurrency.emitWakeSgi result.2
          pure result.1) := rfl

end SeLe4n.Kernel
