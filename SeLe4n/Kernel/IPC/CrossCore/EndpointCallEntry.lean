-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM SM6.A cross-core IPC live dispatch (the SM5.I FFI
-- seam; see docs/planning/SMP_CROSS_CORE_IPC_PLAN.md).

import SeLe4n.Kernel.IPC.CrossCore.EndpointCall
import SeLe4n.Kernel.IPC.DualQueue.WithCaps
import SeLe4n.Kernel.IPC.Operations.Donation.Primitives
import SeLe4n.Kernel.Scheduler.PriorityInheritance.Propagate
import SeLe4n.Kernel.Concurrency.Runtime
import SeLe4n.Platform.FFI

/-!
# WS-SM SM6.A — Cross-core endpoint call: WithCaps + live FFI seam

The live cross-core `Call` path.  Composes:

* **`endpointCallWithCapsOnCore`** — the cross-core `endpointCallWithCaps`: the
  cross-core `endpointCallOnCore` rendezvous (SGI surfaced) followed by
  `ipcUnwrapCaps` capability transfer to the receiver's CSpace, mirroring the
  single-core `endpointCallWithCaps`.
* **`endpointCallCrossCoreDispatch`** — the full `.call` syscall semantics
  across cores: the WithCaps call, then the SchedContext **donation** to a
  passive server (`applyCallDonation`), then priority-inheritance propagation
  (`propagatePriorityInheritance`), surfacing the cross-core `.reschedule` SGI.
* **`endpointCallCrossCoreEntry`** — the live `BaseIO` FFI seam: read the
  executing core (`currentCoreId`), commit the dispatch atomically against the
  kernel state ref (`modifyGetKernelState`), then fire the surfaced SGI
  (`emitWakeSgi`).  Mirrors the SM5.I `perCoreTimerTickEntry` pattern.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind)

-- ============================================================================
-- §1  Cross-core `endpointCallWithCaps`
-- ============================================================================

/-- WS-SM SM6.A.8 (operation): endpoint call with capability transfer, across
cores.  The cross-core `endpointCallOnCore` rendezvous (which surfaces the
receiver-wake SGI), then — on an immediate rendezvous carrying caps —
`ipcUnwrapCaps` installs the transferred capabilities into the receiver's
CSpace (gated on the endpoint's `grant` right).  Returns the post-state, the
capability-transfer summary, and the optional cross-core SGI. -/
def endpointCallWithCapsOnCore
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (CapTransferSummary × Option (CoreId × SgiKind)) :=
  let hasReceiver := match st.getEndpoint? endpointId with
    | some ep => ep.receiveQ.head.isSome
    | none    => false
  match endpointCallOnCore endpointId caller msg executingCore st with
  | (st', .error e) => (st', .error e)
  | (st', .ok sgi) =>
      if !hasReceiver || msg.caps.isEmpty then (st', .ok ({ results := #[] }, sgi))
      else
        match st.getEndpoint? endpointId with
        | some ep =>
          match ep.receiveQ.head with
          | some receiverId =>
            match lookupCspaceRoot st' receiverId with
            | some recvRoot =>
              match ipcUnwrapCaps msg callerCspaceRoot recvRoot receiverSlotBase
                  (endpointRights.mem .grant) st' with
              | .error e => (st', .error e)
              | .ok (summary, st'') => (st'', .ok (summary, sgi))
            | none => (st', .error .invalidCapability)
          | none => (st', .ok ({ results := #[] }, sgi))
        | none => (st', .ok ({ results := #[] }, sgi))

-- ============================================================================
-- §2  Full cross-core `.call` dispatch (WithCaps + donation + PIP)
-- ============================================================================

/-- WS-SM SM6.A.5 (operation): the full cross-core `Call` syscall semantics.
The cross-core WithCaps call, then — if a receiver rendezvoused — the
SchedContext **donation** to a passive server (`applyCallDonation` rebinds the
caller's bound SchedContext to the receiver, an object-store-only update that is
cross-core-safe) and priority-inheritance propagation.  The cross-core
`.reschedule` SGI is surfaced for the runtime to fire after the commit.
Mirrors the live single-core `.call` dispatch arm (`API.dispatchWithCap`). -/
def endpointCallCrossCoreDispatch
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (CapTransferSummary × Option (CoreId × SgiKind)) :=
  let maybeReceiver := match st.getEndpoint? endpointId with
    | some ep => ep.receiveQ.head
    | none    => none
  match endpointCallWithCapsOnCore endpointId caller msg endpointRights callerCspaceRoot
      receiverSlotBase executingCore st with
  | (st', .error e) => (st', .error e)
  | (st', .ok (summary, sgi)) =>
      match maybeReceiver with
      | some receiverTid =>
        match SeLe4n.ThreadId.toValid? caller, SeLe4n.ThreadId.toValid? receiverTid with
        | some callerV, some receiverV =>
          match applyCallDonation st' callerV receiverV with
          | .error e => (st', .error e)
          | .ok st'' =>
              (PriorityInheritance.propagatePriorityInheritance st'' receiverTid, .ok (summary, sgi))
        | _, _ => (st', .error .invalidArgument)
      | none => (st', .ok (summary, sgi))

-- ============================================================================
-- §3  Live FFI seam (the SM5.I `perCoreTimerTickEntry` pattern)
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

-- ============================================================================
-- §4  Characterisation theorems
-- ============================================================================

/-- WS-SM SM6.A.8: with no capabilities to transfer, the WithCaps cross-core
call is exactly the bare cross-core call (empty transfer summary), so its
surfaced SGI is the bare call's — the SM6.A.3 SGI characterisation carries to
the WithCaps path. -/
theorem endpointCallWithCapsOnCore_no_caps
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet) (callerCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hCaps : msg.caps.isEmpty = true) :
    endpointCallWithCapsOnCore endpointId caller msg endpointRights callerCspaceRoot
        receiverSlotBase executingCore st
      = ((endpointCallOnCore endpointId caller msg executingCore st).1,
         (endpointCallOnCore endpointId caller msg executingCore st).2.map
           (fun sgi => ({ results := #[] }, sgi))) := by
  unfold endpointCallWithCapsOnCore
  cases h : endpointCallOnCore endpointId caller msg executingCore st with
  | mk st' res => cases res with
    | error e => simp [Except.map]
    | ok sgi => simp [hCaps, Except.map]

/-- WS-SM SM6.A.5: on the no-receiver path (the caller blocks as `blockedOnCall`)
the cross-core dispatch performs no donation — it is exactly the WithCaps call.
Donation only fires on an immediate rendezvous with a passive server. -/
theorem endpointCallCrossCoreDispatch_no_receiver
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet) (callerCspaceRoot : SeLe4n.ObjId)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hNoRecv : (match st.getEndpoint? endpointId with
      | some ep => ep.receiveQ.head | none => none) = none) :
    endpointCallCrossCoreDispatch endpointId caller msg endpointRights callerCspaceRoot
        receiverSlotBase executingCore st
      = endpointCallWithCapsOnCore endpointId caller msg endpointRights callerCspaceRoot
          receiverSlotBase executingCore st := by
  unfold endpointCallCrossCoreDispatch
  rw [hNoRecv]
  cases h : endpointCallWithCapsOnCore endpointId caller msg endpointRights callerCspaceRoot
      receiverSlotBase executingCore st with
  | mk st' res => cases res with
    | error e => rfl
    | ok pair => rfl

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
