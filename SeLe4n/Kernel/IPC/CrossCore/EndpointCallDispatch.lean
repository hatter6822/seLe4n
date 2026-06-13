-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-SM SM6.A: PRODUCTION (LANDED).  The pure `.call` dispatch ops below the API
-- layer; the live `API.dispatchWithCap{,Checked}` `.call` arm routes through
-- `endpointCallCrossCoreDispatch{,Checked}` here, deriving the executing core
-- from the live state (`determineExecutingCore`).  (Former "STATUS: staged"
-- marker replaced with this landing note per the implement-the-improvement rule;
-- see docs/planning/SMP_CROSS_CORE_IPC_PLAN.md.)

import SeLe4n.Kernel.IPC.CrossCore.EndpointCall
import SeLe4n.Kernel.IPC.DualQueue.WithCaps
import SeLe4n.Kernel.IPC.Operations.Donation.Primitives
import SeLe4n.Kernel.Scheduler.PriorityInheritance.Propagate
import SeLe4n.Kernel.InformationFlow.Enforcement.Wrappers

/-!
# WS-SM SM6.A — Cross-core `.call` dispatch (pure; below the API layer)

The pure cross-core `.call` dispatch operations — `endpointCallWithCapsOnCore`,
`endpointCallCrossCoreDispatch`, and the information-flow-checked
`endpointCallCrossCoreDispatchChecked`.  These live *below* `SeLe4n.Kernel.API`
(no `Platform.FFI` dependency) so the live `.call` dispatch arm can route through
them.  The BaseIO live driver (`endpointCallCrossCoreEntry`, which reads the
hardware core and fires the SGI) layers on top of these in
`EndpointCallEntry.lean`, which imports `Platform.FFI`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind)

-- ============================================================================
-- §0  Executing-core derivation (per-core dispatch without a parameter)
-- ============================================================================

/-- WS-SM SM6.A: the core a syscall is executing on, derived from the live state.
A thread issuing a syscall is the *current* thread on its core, so the executing
core is the unique `c` with `currentOnCore c = some tid` — found by scanning
`Concurrency.allCores`, defaulting to `bootCoreId` (the boot-pinned fallback, and
the single-core answer).  This lets the live `.call` dispatch identify and
deschedule the caller on its *own* core without threading a hardware-core
parameter through the `Kernel`-monad dispatch chain (which returns `Kernel Unit`,
applying its state positionally). -/
def determineExecutingCore (st : SystemState) (tid : SeLe4n.ThreadId) : CoreId :=
  (Concurrency.allCores.find? (fun c => st.scheduler.currentOnCore c == some tid)).getD
    Concurrency.bootCoreId

/-- `determineExecutingCore` always returns a core on which the caller is the
current thread, *or* the `bootCoreId` fallback — it never invents a core that
isn't running the caller.  (Either `find?` succeeds, witnessing `currentOnCore c
= some tid`, or it falls back to the boot core.) -/
theorem determineExecutingCore_sound (st : SystemState) (tid : SeLe4n.ThreadId) :
    determineExecutingCore st tid = Concurrency.bootCoreId
      ∨ st.scheduler.currentOnCore (determineExecutingCore st tid) = some tid := by
  unfold determineExecutingCore
  cases hf : Concurrency.allCores.find? (fun c => st.scheduler.currentOnCore c == some tid) with
  | none => exact Or.inl (by simp)
  | some c =>
    have hc := List.find?_some hf
    exact Or.inr (by simpa using hc)

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
              -- WS-SM SM6.A: propagate the donated-priority boost with the
              -- *cross-core* chain walk (`propagatePipChainCrossCore`, SM5.F.4 — in
              -- the FFI-free `Propagate`, so no import cycle below the API layer);
              -- its `.1` is the post-walk state.  Each boosted server's run-queue
              -- bucket migrates on its *home* core (via `pipBoostWithWake`'s
              -- `updatePipBoostOnCore`), so a passive server pinned to a remote core
              -- becomes schedulable at the donated priority there — and the run-queue
              -- change surfaces in the `(pre, post)` diff the syscall seam fires the
              -- cross-core SGI from.  On the boot core with an unbound receiver this
              -- is state-identical to the single-core `propagatePriorityInheritance`
              -- (`pipBoostWithWake … bootCoreId` of an unbound thread = `updatePipBoost`).
              ((PriorityInheritance.propagatePipChainCrossCore st'' receiverTid executingCore).1,
               .ok (summary, sgi))
        | _, _ => (st', .error .invalidArgument)
      | none => (st', .ok (summary, sgi))

/-- WS-SM SM6.A (live `.call` enforcement): the **information-flow-checked**
cross-core call dispatch — the cross-core analogue of `endpointCallChecked`
composed with `endpointCallCrossCoreDispatch`.  Mirrors the single-core checked
`.call` arm exactly: it first applies the SM-IF security guard
(`securityFlowsTo callerLabel endpointLabel`, rejecting with `.flowDenied` on a
disallowed flow), then runs the full cross-core dispatch (WithCaps +
`applyCallDonation` + PIP propagation), surfacing the cross-core `.reschedule`
SGI.  This is the operation the live `dispatchWithCapChecked` `.call` arm routes
through, replacing the boot-pinned `endpointCallChecked` so the receiver is woken
on its *home* core. -/
def endpointCallCrossCoreDispatchChecked
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (CapTransferSummary × Option (CoreId × SgiKind)) :=
  if securityFlowsTo (ctx.threadLabelOf caller) (ctx.endpointLabelOf endpointId) then
    endpointCallCrossCoreDispatch endpointId caller msg endpointRights callerCspaceRoot
      receiverSlotBase executingCore st
  else
    (st, .error .flowDenied)

/-- WS-SM SM6.A: a disallowed flow is rejected before any state change — the
checked cross-core dispatch is fail-closed (state unchanged, `.flowDenied`). -/
theorem endpointCallCrossCoreDispatchChecked_flow_denied
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState)
    (hDeny : securityFlowsTo (ctx.threadLabelOf caller) (ctx.endpointLabelOf endpointId) = false) :
    endpointCallCrossCoreDispatchChecked ctx endpointId caller msg endpointRights
        callerCspaceRoot receiverSlotBase executingCore st = (st, .error .flowDenied) := by
  simp [endpointCallCrossCoreDispatchChecked, hDeny]

/-- WS-SM SM6.A: when the flow is permitted, the checked dispatch is exactly the
unchecked cross-core dispatch — the guard is a pure precondition. -/
theorem endpointCallCrossCoreDispatchChecked_flow_allowed
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState)
    (hAllow : securityFlowsTo (ctx.threadLabelOf caller) (ctx.endpointLabelOf endpointId) = true) :
    endpointCallCrossCoreDispatchChecked ctx endpointId caller msg endpointRights
        callerCspaceRoot receiverSlotBase executingCore st
      = endpointCallCrossCoreDispatch endpointId caller msg endpointRights
          callerCspaceRoot receiverSlotBase executingCore st := by
  simp [endpointCallCrossCoreDispatchChecked, hAllow]

-- ============================================================================
-- §3  Characterisation theorems
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

end SeLe4n.Kernel
