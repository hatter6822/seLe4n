-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Invariant
import SeLe4n.Kernel.Architecture.SyscallReturn
import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Kernel.Capability.FrameFinalise
import SeLe4n.Kernel.Capability.IrqControl
import SeLe4n.Kernel.IPC.DualQueue
import SeLe4n.Kernel.IPC.Invariant
import SeLe4n.Kernel.IPC.Invariant.DonationPreservation
import SeLe4n.Kernel.IPC.Invariant.CancelAllPreservation
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDispatch
import SeLe4n.Kernel.IPC.CrossCore.EndpointSend
import SeLe4n.Kernel.IPC.CrossCore.EndpointSendInvariant
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDispatch
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecv
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyRecvInvariant
import SeLe4n.Kernel.IPC.CrossCore.Fault
import SeLe4n.Kernel.IPC.CrossCore.NotificationBindDispatch
-- WS-SM SM6.E: the live per-core suspend (`suspendThreadOnCore`) behind the
-- `.tcbSuspend` arm — the victim is descheduled on its *home* core.
import SeLe4n.Kernel.IPC.CrossCore.Cancellation
import SeLe4n.Kernel.IPC.CrossCore.ReplyHolderCancel
import SeLe4n.Kernel.IPC.CrossCore.Restart
import SeLe4n.Kernel.Capability.Invariant
import SeLe4n.Kernel.Scheduler.Operations

import SeLe4n.Kernel.Lifecycle.Operations
import SeLe4n.Kernel.Lifecycle.Invariant
import SeLe4n.Kernel.Service.Operations
import SeLe4n.Kernel.Service.Invariant
import SeLe4n.Kernel.Service.Registry
import SeLe4n.Kernel.InformationFlow.Policy
import SeLe4n.Kernel.InformationFlow.Projection
import SeLe4n.Kernel.InformationFlow.Invariant
import SeLe4n.Kernel.InformationFlow.Enforcement.Wrappers
-- WS-SM SM8.C.9: the live `.declassify` transition.  Deliberately the small
-- production module, not the staged `DeclassificationPerCore` that carries the
-- per-core audit theory on top of the SM8.A/SM8.B non-interference layer.
import SeLe4n.Kernel.InformationFlow.Declassification
-- WS-SM SM9.A: the audit trail's reader and drain.  Production, like the
-- transition it reads: the live `.auditRead` / `.auditDrain` arms import it, so
-- staging it would break the production/staged partition gate.
import SeLe4n.Kernel.InformationFlow.AuditRead
-- WS-SM SM9.C: the data-carrying declassification.  Production for the same
-- reason: the live `.declassifySignal` arm calls it, and it is deliberately the
-- transition module rather than the staged `NonInterferenceCrossCore` that
-- carries its declassification-relative non-interference on top.
import SeLe4n.Kernel.InformationFlow.DeclassifiedSignal
import SeLe4n.Kernel.InformationFlow.TaintPropagation
import SeLe4n.Kernel.InformationFlow.DeclassificationTaintStep

import SeLe4n.Kernel.Architecture.Assumptions
import SeLe4n.Kernel.Architecture.RegisterDecode
import SeLe4n.Kernel.Architecture.SyscallSelect
import SeLe4n.Kernel.Architecture.SyscallArgDecode

import SeLe4n.Kernel.SchedContext.Operations
import SeLe4n.Kernel.SchedContext.SchedControl
import SeLe4n.Kernel.Lifecycle.Suspend
import SeLe4n.Kernel.SchedContext.PriorityManagement
import SeLe4n.Kernel.SchedContext.PriorityManagementPerCore
import SeLe4n.Kernel.SchedContext.OperationsPerCore
import SeLe4n.Kernel.SchedContext.NotificationLink
import SeLe4n.Kernel.SchedContext.NotificationDonation
import SeLe4n.Kernel.IPC.Operations.Donation
import SeLe4n.Kernel.IPC.Invariant.DispatchArmPreservation
import SeLe4n.Kernel.IPC.Invariant.YieldPreservation
import SeLe4n.Kernel.SchedContext.BindingAffinity

import SeLe4n.Kernel.Architecture.Adapter
import SeLe4n.Kernel.Architecture.InterruptMask
import SeLe4n.Kernel.Architecture.Invariant
import SeLe4n.Kernel.Architecture.VSpace
import SeLe4n.Kernel.Architecture.VSpaceInvariant
import SeLe4n.Kernel.Architecture.IpcBufferValidation
-- WS-SM SM7.F.4: the per-core-TLB-aware VSpace shootdown wrappers the live
-- `.vspaceMap` / `.vspaceUnmap` arms dispatch through (initiator-atomic
-- `perCoreTlb` retirement + translation-walk fill; projection-invisible).
import SeLe4n.Kernel.Architecture.PerCoreTlbModel
import SeLe4n.Kernel.SchedContext.Invariant.NotificationLinkIpc

/-!
# L-01/WS-E6: Unified Public Kernel API

This module provides the public entry-point surface for the seLe4n kernel model.
Previously it was just an import barrel (finding L-01); it now defines:

1. **`apiInvariantBundle`** — a top-level alias for the composed proof-layer
   invariant bundle, giving API consumers a single entry point.
2. **Entry-point stability table** — documents which subsystem operations
   are considered part of the stable public API.

## Entry-point stability classification

| Entry point | Subsystem | Stability |
|---|---|---|
| `schedule`, `handleYield` | Scheduler | Single-core reference, proof-only (WS-ZA ZA4.5: writes the run queue through its ghost; the live forms are `scheduleEffectiveOnCore`, `yieldOnCore`) |
| `withOutgoingContextChecked` | Scheduler (X2-I) | Guard that refuses before any scheduler write when the outgoing context cannot be saved (tests wrap the boot core's live ops in it) |
| `timerTick` | Scheduler (M-04) | Single-core reference, proof-only (live form `timerTickOnCore`) |
| `scheduleDomain`, `switchDomain` | Scheduler (M-05) | Single-core reference, proof-only (live forms `scheduleDomainOnCore`, `switchDomainOnCore`) |
| `chooseThread`, `chooseThreadInDomain` | Scheduler | Single-core reference, proof-only (live form `chooseThreadEffectiveOnCore`) |
| `cspaceLookupSlot`, `cspaceLookupPath` | Capability | Stable |
| `cspaceMint`, `cspaceCopy`, `cspaceMove` | Capability | Stable (C-01: dispatch path now uses `cspaceMintWithCdt` for CDT-tracked derivation; `cspaceMint` is the untracked base used only for internal composition and proofs) |
| `cspaceMutate`, `cspaceInsertSlot`, `cspaceDeleteSlot` | Capability | Stable |
| `endpointSendDual`, `endpointReceiveDual` | IPC (dual-queue) | Stable |
| `endpointReply`, `endpointCall`, `endpointReplyRecv` | IPC | Stable |
| `retypeFromUntyped` | Lifecycle (WS-F2) | Stable |
| `registerService`, `revokeService`, `lookupServiceByRecordedRegistration` | Service (WS-Q1) | Stable |
| `adapterAdvanceTimer`, `adapterWriteRegister`, `adapterReadMemory` | Architecture | Stable |
| `vspaceMapPageCheckedWithFlushFromState`, `vspaceUnmapPageWithFlush`, `vspaceLookup` | VSpace | Stable (S6-A/X2-E: production uses state-aware WithFlush variant) |
| `endpointSendDualChecked` | Info-flow (dual-queue) | Stable |
| `cspaceMintChecked` | Info-flow | Stable |
| ~~`apiEndpointSend`, `apiEndpointReceive`~~ | Syscall IPC (WS-H15c) | **Removed** (S5-A v0.19.4) — replaced by `syscallEntryChecked` |
| ~~`apiEndpointCall`, `apiEndpointReply`~~ | Syscall IPC (WS-H15c) | **Removed** (S5-A v0.19.4) — replaced by `syscallEntryChecked` |
| ~~`apiCspaceMint`, `apiCspaceCopy`, `apiCspaceMove`~~ | Syscall Capability (WS-H15c) | **Removed** (S5-A v0.19.4) — replaced by `syscallEntryChecked` |
| ~~`apiCspaceDelete`~~ | Syscall Capability (WS-H15c) | **Removed** (S5-A v0.19.4) — replaced by `syscallEntryChecked` |
| ~~`apiLifecycleRetype`~~ | Syscall Lifecycle (WS-H15c) | **Removed** (S5-A v0.19.4) — replaced by `syscallEntryChecked` |
| ~~`apiVspaceMap`, `apiVspaceUnmap`~~ | Syscall VSpace (WS-H15c) | **Removed** (S5-A v0.19.4) — replaced by `syscallEntryChecked` |
| ~~`apiServiceRegister`, `apiServiceRevoke`, `apiServiceQuery`~~ | Syscall Service (WS-Q1-D) | **Removed** (S5-A v0.19.4) — replaced by `syscallEntryChecked` |
| `syscallEntryChecked` | Syscall dispatch (T6-I) | Stable (**production entry point** — information-flow-checked) |
| `lookupThreadRegisterContext` | Syscall dispatch (WS-J1-C) | Stable |
| `dispatchSyscallChecked` | Syscall dispatch (T6-I) | Stable (checked internal) |

## Deferred operations (WS-F5/D3)

The following seL4 operations are intentionally **deferred** from the current
model. Each is documented with rationale and the prerequisite that must be
completed before implementation.

| Operation | seL4 Reference | Rationale | Prerequisite |
|-----------|---------------|-----------|--------------|
| `setPriority` | `seL4_TCB_SetPriority` | **IMPLEMENTED** (D2, v0.24.1; per-core reroute WS-SM SM8.B). Wired as `SyscallId.tcbSetPriority` to `setPriorityOnCore` in `SchedContext/PriorityManagementPerCore.lean` (`setPriorityOp` remains its boot-core instance). | Complete |
| `setMCPriority` | `seL4_TCB_SetMCPriority` | **IMPLEMENTED** (D2, v0.24.1; per-core reroute WS-SM SM8.B). Wired as `SyscallId.tcbSetMCPriority` to `setMCPriorityOnCore` in `SchedContext/PriorityManagementPerCore.lean`. | Complete |
| `suspend` | `seL4_TCB_Suspend` | **IMPLEMENTED** (D1, v0.24.0; per-core reroute WS-SM SM6.E). Wired as `SyscallId.tcbSuspend` to `suspendThreadOnCore` in `Lifecycle/Suspend.lean` (`suspendThread` remains its boot-core form). | Complete |
| `resume` | `seL4_TCB_Resume` | **IMPLEMENTED** (D1, v0.24.0; per-core reroute WS-SM SM8.B, PR #861 round 10). Wired as `SyscallId.tcbResume` to `restartThreadOnCore` in `IPC/CrossCore/Restart.lean`, seL4's `restart`: a thread that is not stopped is left as it is, one blocked in an IPC has the IPC cancelled through the suspend, and an `Inactive` one is resumed by `resumeThreadOnCore` (`resumeThread` remains its boot-core form). | Complete |
| `setIPCBuffer` | `seL4_TCB_SetIPCBuffer` | **IMPLEMENTED** (D3, v0.24.2). `setIPCBufferOp` in `Architecture/IpcBufferValidation.lean`, wired as `SyscallId.tcbSetIPCBuffer`. | Complete |
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId)

/-- L-01/WS-E6: Unified public API invariant bundle.
Alias for `Architecture.proofLayerInvariantBundle` — the composed bundle of all
active subsystem invariants. API consumers should use this name to avoid coupling
to the internal architecture module. -/
abbrev apiInvariantBundle := Architecture.proofLayerInvariantBundle

-- ============================================================================
-- X2-I: Checked scheduler API wrappers (defense-in-depth)
-- ============================================================================

/-! ## X2-I: Scheduler operations with `saveOutgoingContextChecked`

The core scheduler operations (`schedule`, `handleYield`, `timerTick`,
`switchDomain`) in `Scheduler/Operations/Core.lean` use `saveOutgoingContext`
(unchecked) internally. Under `currentThreadValid` (part of
`schedulerInvariantBundle`), the unchecked variant's failure branch — where
the current thread's TCB lookup fails — is unreachable: the invariant
guarantees the current thread resolves to a valid TCB.

The checked wrappers below provide defense-in-depth at the API boundary:
they call `saveOutgoingContextChecked` before delegating to the underlying
scheduler operation. On failure (`false` return), they propagate
`schedulerInvariantViolation` rather than silently continuing with stale
register context. Under correct invariant maintenance the failure branch
is never taken; the guard exists to surface invariant violations early. -/

/-- X2-I: the checked guard the four wrappers below share: save the outgoing
context through `saveOutgoingContextChecked`, then run `op`; a failed save
surfaces `schedulerInvariantViolation` before any scheduler write.  WS-ZA ZA4.5:
taking the operation as a parameter lets the suites run the guard in front of the
live per-core operations, since the single-core ones it guards here write the run
queue only through its proof-only ghost. -/
def withOutgoingContextChecked (op : Kernel Unit) : Kernel Unit :=
  fun st =>
    let (stSaved, ok) := saveOutgoingContextChecked st
    if ok then
      op stSaved
    else
      .error .schedulerInvariantViolation

-- ============================================================================
-- WS-H15c/A-42: Syscall Capability-Checking Wrappers
-- ============================================================================

/-! ## WS-H15c/A-42: Capability-gated syscall entry points

In real seL4, every user-space syscall follows: (1) extract capability pointer
from message registers, (2) resolve the capability through the caller's CSpace
root using multi-level CNode walk, (3) check that the resolved capability grants
sufficient rights for the requested operation, (4) invoke the kernel operation.

The raw kernel operations above (e.g., `endpointSendDual`, `cspaceMint`) are
**internal kernel operations** — invoked by trusted kernel paths (scheduler,
IPC subsystem, lifecycle engine). They do not perform capability checks because
the kernel itself is the trusted computing base.

The production syscall path is `syscallEntryChecked → dispatchSyscallChecked →
syscallInvokeTyped → dispatchWithCapChecked`, which reads the caller's register
file, decodes typed arguments, resolves capabilities, gates each cross-domain
flow, and dispatches to the appropriate internal operation. The legacy `api*`
wrappers were removed in S5-A (v0.19.4); the unchecked, boot-pinned entry and
its dispatcher were retired by owner decision (2026-11-13).

### Internal vs syscall operations

| Category | Capability check? | Invoked by |
|---|---|---|
| **Internal** (`schedule`, `endpointSendDual`, etc.) | No | Kernel paths |
| **Syscall** (`syscallEntryChecked` → `dispatchSyscallChecked`) | Yes | User-space |
| **Scheduler** (`schedule`, `handleYield`, `timerTick`) | No | Timer IRQ, kernel |
-/

/-- WS-H15c/A-42: Syscall gate descriptor. Encodes the caller's identity,
the caller's CSpace root capability, the capability address, and the required
access right for the requested operation.  The address resolves at the word's
64 bits from the root capability (seL4's `lookupSlot` from `tcbCTable`), so the
gate carries no depth: the root capability's guard and the CNodes' radixes
decide how the bits divide. -/
structure SyscallGate where
  /-- Thread ID of the invoking user-space thread. -/
  callerId     : SeLe4n.ThreadId
  /-- The caller's CSpace root capability (`TCB.spaceCells` slot 0), `none`
  for a thread with no root. -/
  cspaceRootCap : Option Capability
  /-- Capability address to resolve within the CSpace. -/
  capAddr      : SeLe4n.CPtr
  /-- The access right required for this syscall. -/
  requiredRight : AccessRight
  deriving Repr, DecidableEq

/-- The object the gate's root capability names (`TCB.spaceCellObject`): the
caller's CSpace root CNode, read by the lock footprints. -/
@[reducible, inline] def SyscallGate.cspaceRoot (gate : SyscallGate) : SeLe4n.ObjId :=
  TCB.spaceCellObject gate.cspaceRootCap

/-- The slot the gate's address names, resolved at 64 bits from its root
capability (`lookupSlotFrom`); a gate with no root capability is
`invalidRoot`.  For the gate a thread's syscall builds this is `lookupSlot`
of that thread (`SyscallGate.lookupSlot_eq`). -/
def SyscallGate.lookupSlot (gate : SyscallGate) (st : SystemState) :
    Except LookupFault SlotRef :=
  match gate.cspaceRootCap with
  | some root => lookupSlotFrom root gate.capAddr st
  | none => .error .invalidRoot

theorem SyscallGate.lookupSlot_eq (gate : SyscallGate) (tcb : TCB) (st : SystemState)
    (h : gate.cspaceRootCap = tcb.spaceCells[0]) :
    gate.lookupSlot st = SeLe4n.Kernel.lookupSlot tcb gate.capAddr st := by
  unfold SyscallGate.lookupSlot SeLe4n.Kernel.lookupSlot; rw [h]
  cases tcb.spaceCells[0] <;> rfl

/-- `SyscallGate.lookupSlot` reads only CNodes. -/
theorem SyscallGate.lookupSlot_congr_getCNode? (gate : SyscallGate)
    (st₁ st₂ : SystemState) (hCNode : ∀ id, st₁.getCNode? id = st₂.getCNode? id) :
    gate.lookupSlot st₁ = gate.lookupSlot st₂ := by
  unfold SyscallGate.lookupSlot
  cases gate.cspaceRootCap with
  | none => rfl
  | some root => exact lookupSlotFrom_congr_getCNode? st₁ st₂ hCNode root gate.capAddr

/-- `SyscallGate.lookupSlot` in continuation form (`lookupSlotFromK`). -/
@[inline] def SyscallGate.lookupSlotK {α : Type} (gate : SyscallGate) (st : SystemState)
    (onErr : UInt64 → UInt64 → UInt64 → UInt64 → α)
    (onOk : SeLe4n.ObjId → SeLe4n.Slot → α) : α :=
  match gate.cspaceRootCap with
  | some root => lookupSlotFromK root gate.capAddr st onErr onOk
  | none => onErr 1 0 0 0

theorem SyscallGate.lookupSlotK_eq {α : Type} (gate : SyscallGate) (st : SystemState)
    (onErr : UInt64 → UInt64 → UInt64 → UInt64 → α)
    (onOk : SeLe4n.ObjId → SeLe4n.Slot → α) :
    gate.lookupSlotK st onErr onOk =
      match gate.lookupSlot st with
      | .error f => onErr (f.word 0) (f.word 1) (f.word 2) (f.word 3)
      | .ok ref => onOk ref.cnode ref.slot := by
  unfold SyscallGate.lookupSlotK SyscallGate.lookupSlot
  cases gate.cspaceRootCap with
  | none => rfl
  | some root => exact lookupSlotFromK_eq root gate.capAddr st onErr onOk

/-- The gate a thread's syscall builds resolves as `lookupSlot` of that
thread. -/
@[simp] theorem SyscallGate.lookupSlot_mk (c : SeLe4n.ThreadId) (tcb : TCB)
    (a : SeLe4n.CPtr) (r : AccessRight) (st : SystemState) :
    SyscallGate.lookupSlot (SyscallGate.mk c tcb.spaceCells[0] a r) st =
      SeLe4n.Kernel.lookupSlot tcb a st := rfl

/-- `SyscallGate.lookupSlot` reads only the object store. -/
theorem SyscallGate.lookupSlot_congr_objects (gate : SyscallGate)
    (st₁ st₂ : SystemState) (hObjects : st₁.objects = st₂.objects) :
    gate.lookupSlot st₁ = gate.lookupSlot st₂ :=
  gate.lookupSlot_congr_getCNode? st₁ st₂
    (fun id => by simp only [SystemState.getCNode?, hObjects])

/-- WS-SM SM9.A.9 (PR #870 round 5): **capability resolution without the
rights gate** — steps 1–2 of the syscall capability-checking sequence.

Extracted from `syscallLookupCap` so an arm can validate the capability's
*target* before its rights.  The full lookup answers a missing right with
`.illegalAuthority` before any arm runs, which made the audit syscalls'
documented contract — target first, right second — false for a capability
wrong on both axes: the caller learned `.illegalAuthority` where the contract
promises `.invalidCapability` for every non-audit target.  `syscallLookupCap`
is now *defined as* this resolution followed by the rights gate, so the two
share one resolution and cannot drift.  Read-only, like the full lookup. -/
def syscallResolveCap (gate : SyscallGate) : Kernel Capability :=
  fun st =>
    match gate.lookupSlot st with
    | .error f => .error (.failedLookup false f)
    | .ok ref =>
      match SystemState.lookupSlotCap st ref with
      | none => .error (.invalidCapability 0)
      | some cap =>
        -- PR #889 review round 2: a capability naming a kernel-reserved idle
        -- object is not a capability user space may hold — seL4 has none to
        -- its idle thread — so it resolves like an empty slot.  This is the
        -- one resolution every invoked capability passes through
        -- (`syscallLookupCap` is defined as it plus the rights gate), which
        -- is what makes `syscallResolveCap_ok_not_reserved` a statement about
        -- every syscall rather than about the arms that happen to check.
        if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability 0)
        else .ok (cap, st)

/-- WS-H15c/A-42: Resolve and validate a capability from a syscall gate.

Performs the full seL4 syscall capability-checking sequence:
1. Resolves the capability address from the CSpace root capability (`SyscallGate.lookupSlot`).
2. Looks up the capability at the resolved slot.
3. Verifies the capability grants the required access right.

Returns the resolved capability if all checks pass; an error otherwise.
The state is unchanged (capability lookup is read-only).  The resolution half
is the shared `syscallResolveCap`; the dispatchers' gate, `syscallInvokeTyped`,
checks the capability's type between the resolution and the right. -/
def syscallLookupCap (gate : SyscallGate) : Kernel Capability :=
  fun st =>
    match syscallResolveCap gate st with
    | .error e => .error e
    | .ok (cap, st') =>
      if cap.hasRight gate.requiredRight
      then .ok (cap, st')
      else .error .illegalAuthority

/-- **The one resolution of an argument capability**: `syscallLookupCap` on the
argument's gate, its refusals renumbered for argument capability `capNumber`
(`KernelError.forArgumentCap`; `i + 1` for argument capability `i`, seL4's
`invalidCapNumber`).  The invoked capability is resolved by `syscallLookupCap`
itself and answers `invalidCapability 0`; every capability an argument word or
an extra capability names is resolved here, so no arm can resolve one and
answer the invoked capability's number.  A compiled resolver of the same
argument hands its refusals to `KernelError.argumentCapRefusal` with the same
number constant.  A wrong-kind argument capability is refused by the arm with
`.invalidCapability capNumber` (or, through an extractor shared with the
invoked capability, the extractor's refusal renumbered by `forArgumentCap`). -/
@[inline] def syscallLookupArgumentCap (capNumber : UInt64) (gate : SyscallGate) :
    Kernel Capability :=
  fun st =>
    match syscallLookupCap gate st with
    | .error e => .error (e.forArgumentCap capNumber)
    | .ok p => .ok p

/-- An argument capability resolves exactly when `syscallLookupCap` resolves it,
to the same capability and state: the boundary renumbers refusals only. -/
theorem syscallLookupArgumentCap_ok_iff (capNumber : UInt64) (gate : SyscallGate)
    (st : SystemState) (p : Capability × SystemState) :
    syscallLookupArgumentCap capNumber gate st = .ok p ↔ syscallLookupCap gate st = .ok p := by
  unfold syscallLookupArgumentCap
  cases syscallLookupCap gate st <;> simp

/-- A refused argument capability is refused with `syscallLookupCap`'s refusal,
renumbered. -/
theorem syscallLookupArgumentCap_error (capNumber : UInt64) (gate : SyscallGate)
    (st : SystemState) (e : KernelError) (h : syscallLookupCap gate st = .error e) :
    syscallLookupArgumentCap capNumber gate st = .error (e.forArgumentCap capNumber) := by
  unfold syscallLookupArgumentCap; rw [h]

/-- **seL4-MCS's `lookupReply`** (`syscall.c`): the reply capability a receive
names, looked up through `gate` (its `capAddr` the reply capability's address).
A lookup that fails answers its own lookup fault; a slot that holds no reply
capability this receiver may use (empty, a reserved object's, without the
reply authority `.write`, or of another kind) answers `missingCapability 0`,
the fault `lookupReply` raises for a capability that is not a reply capability.
The receive raises `CapFault(replyCPtr, inRecvPhase)` with it, so the failure
is never an error frame. -/
def lookupReplyCap (gate : SyscallGate) (st : SystemState) :
    Except LookupFault (Capability × SeLe4n.ReplyId) :=
  match syscallLookupCap { gate with requiredRight := .write } st with
  | .error e => .error e.capFaultLookup
  | .ok (rcap, _) =>
      match rcap.target with
      | .replyCap rid => .ok (rcap, rid)
      | _ => .error (.missingCapability 0)

/-- `lookupReplyCap` reads the gate's caller, root and address alone: the
right it asks is the reply authority whatever the gate carries. -/
theorem lookupReplyCap_congr (g g' : SyscallGate) {st : SystemState}
    (h1 : g.callerId = g'.callerId) (h2 : g.cspaceRootCap = g'.cspaceRootCap)
    (h3 : g.capAddr = g'.capAddr) :
    lookupReplyCap g st = lookupReplyCap g' st := by
  rcases g with ⟨c, r, a, q⟩
  rcases g' with ⟨c', r', a', q'⟩
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

/-- Whether the slot `cnode`/`slot` holds a reply capability a receiver may
use: present, not a reserved object's, carrying `.write`, and a reply
capability (`lookupReplyCap`'s checks after the slot lookup), as one
answer, so the continuation form applies its failure continuation once. -/
def replySlotUsable (st : @& SystemState) (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot) : Bool :=
  match SystemState.lookupSlotCap st { cnode := cnode, slot := slot } with
  | none => false
  | some cap =>
      !SeLe4n.Kernel.capTargetsReservedKernelObject cap && cap.hasRight .write &&
        match cap.target with
        | .replyCap _ => true
        | _ => false

/-- `lookupReplyCap` in continuation form (`lookupReplyCapK_eq`): its lookup
fault handed on as its four words, so the entry re-checks a receive's reply
capability without building a result. -/
@[inline] def lookupReplyCapK {α : Type} (gate : SyscallGate) (st : SystemState)
    (onFail : UInt64 → UInt64 → UInt64 → UInt64 → α) (onOk : α) : α :=
  gate.lookupSlotK st onFail (fun cnode slot =>
    if replySlotUsable st cnode slot then onOk
    else
      onFail ((LookupFault.missingCapability 0).word 0)
        ((LookupFault.missingCapability 0).word 1) ((LookupFault.missingCapability 0).word 2)
        ((LookupFault.missingCapability 0).word 3))

theorem lookupReplyCapK_eq {α : Type} (gate : SyscallGate) (st : SystemState)
    (onFail : UInt64 → UInt64 → UInt64 → UInt64 → α) (onOk : α) :
    lookupReplyCapK gate st onFail onOk =
      match lookupReplyCap gate st with
      | .error lf => onFail (lf.word 0) (lf.word 1) (lf.word 2) (lf.word 3)
      | .ok _ => onOk := by
  unfold lookupReplyCapK lookupReplyCap
  rw [SyscallGate.lookupSlotK_eq]
  simp only [syscallLookupCap, syscallResolveCap]
  have hG : ({ gate with requiredRight := .write } : SyscallGate).lookupSlot st =
      gate.lookupSlot st := rfl
  rw [hG]
  cases gate.lookupSlot st with
  | error f => rfl
  | ok ref =>
    dsimp only
    unfold replySlotUsable
    cases SystemState.lookupSlotCap st ref with
    | none => rfl
    | some cap =>
      dsimp only
      by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
      · simp only [hIdle, ↓reduceIte, Bool.not_true, Bool.false_and, Bool.false_eq_true]; rfl
      · by_cases hRight : cap.hasRight .write = true
        · simp only [hIdle, hRight, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
            Bool.true_and]
          cases cap.target <;> rfl
        · simp only [hIdle, hRight, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
            Bool.true_and, Bool.false_and]; rfl

/-- WS-SM SM9.A.9: **bind the audit syscalls to an audit capability.**

`syscallLookupCap` verifies that the caller holds a capability carrying the
required right and **nothing about that capability's target**.  So a reader
gated only on `.read` would be available to any thread holding any readable
capability — which in practice is every thread, since its own TCB suffices.
That is precisely the confused deputy the project closed at **v0.32.97**, where
a thread holding only a writable capability to its own TCB unmapped an
executable page in a different address space; the fix there was
`vspaceCapAuthorizesAsid`, and the fix here is the same shape and cheaper,
because the trail is a singleton with no operand to bind against.

Written in the shape `lookupReplyCap` checks a reply capability with.  On the composed path the
gate checks the same type first (`syscallTargetAccepted`), so the target is
checked before the right for the audit pair as for every syscall, with
`dispatchSyscallChecked_type_before_rights` the composed witness. -/
def extractAuditAuthority (cap : Capability) : Except KernelError Unit :=
  match cap.target with
  | .auditTrail _ => .ok ()
  | _ => .error (.invalidCapability 0)

/-- WS-SM SM9.A.9: the authority check succeeds exactly on an audit
capability. -/
theorem extractAuditAuthority_eq_ok_iff (cap : Capability) :
    extractAuditAuthority cap = .ok () ↔ ∃ code, cap.target = .auditTrail code := by
  unfold extractAuditAuthority
  cases cap.target <;> simp

/-- WS-SM SM9.A.9 (**the load-bearing negative**): a capability that carries the
required right but does **not** target the audit trail is **rejected**.

The v0.32.97 class, stated as a theorem so a later cut cannot quietly drop back
to a rights-only gate.  The witness is the case that makes the class real: a
fully-rights-bearing capability to an ordinary object — the shape every thread
holds to its own TCB — fails the check. -/
theorem extractAuditAuthority_rejects_non_audit_capability (oid : SeLe4n.ObjId) :
    extractAuditAuthority
        { target := .object oid, rights := AccessRightSet.ofList AccessRight.all, } = .error (.invalidCapability 0) := rfl

/-- **The reply capability's address a receive names**, when it names one
(WS-SX SX7.3: seL4-MCS's `replyRegister`, x6): a `.receive` with `canReply`
and every `.replyRecv`, read as each arm reads it (`resolveRecvReplyId`,
`resolveReplyRecvReply`): seL4-MCS's `handleRecv` with `canReply`, which
`SysReplyRecv` passes as true.  `none` on every other syscall. -/
def receiveReplyAddr? (decoded : SyscallDecodeResult) : Option SeLe4n.CPtr :=
  match decoded.syscallId with
  | .receive => if decoded.canReply then some decoded.replyCPtr else none
  | .replyRecv => some decoded.replyCPtr
  | _ => none

theorem receiveReplyAddr?_of_receive' {decoded : SyscallDecodeResult}
    (hSid : decoded.syscallId = .receive) :
    receiveReplyAddr? decoded = if decoded.canReply then some decoded.replyCPtr else none := by
  unfold receiveReplyAddr?; rw [hSid]

theorem receiveReplyAddr?_of_replyRecv' {decoded : SyscallDecodeResult}
    (hSid : decoded.syscallId = .replyRecv) : receiveReplyAddr? decoded = some decoded.replyCPtr := by
  unfold receiveReplyAddr?; rw [hSid]

/-- WS-SM SM6.D (faithful seL4-MCS receive linkage): resolve the *server-supplied*
reply capability a receive passes to its `ReplyId`.  WS-SX SX7.3: the reply
capability is the one at `replyRegister` (x6), looked up exactly when the
syscall receives with `canReply` (`receiveReplyAddr?`: `Recv`, `NBRecv`,
`ReplyRecv`, `NBSendRecv`), as seL4-MCS's `handleRecv` calls `lookupReply`;
`Wait`, `NBWait` and `NBSendWait` pass none (`.ok none`).  No
message length decides it.  The reply cap lives at a **different** CSpace slot
than the endpoint receive cap, so it is resolved through a gate whose `capAddr`
is the reply register's address.  Read-only.  A reply register that names no
reply capability (`lookupReplyCap`, seL4-MCS's `lookupReply`: a failed lookup,
or a slot holding anything but a reply capability) is refused `failedLookup`
with its lookup fault, which the entry raises as the receive's capability fault
at the reply capability's address (`receiveReplyFault?`). -/
def resolveRecvReplyId (gate : SyscallGate) (decoded : SyscallDecodeResult)
    (st : SystemState) : Except KernelError (Option SeLe4n.ReplyId) :=
  match receiveReplyAddr? decoded with
  | none => .ok none
  | some replyAddr =>
  -- seL4-MCS `lookupReply`: a reply capability that does not look up is
  -- the receive's capability fault, its error the lookup fault itself.
  match lookupReplyCap { gate with capAddr := replyAddr } st with
  | .error lf => .error (.failedLookup false lf)
  | .ok (_, rid) =>
          -- PR #822 review: validate the reply object exists AND is FREE before
          -- treating the cap as usable.  "Free" means BOTH `caller = none` (no
          -- caller-first link) AND not already stashed in some server's
          -- `pendingReceiveReply` (`replyIsStashed` — a server-first link in
          -- progress); else a second receive via a copied cap could block another
          -- server on the same `rid` and later roll back `.replyCapInvalid` on a
          -- stale stash.
          match st.getReply? rid with
          | some r =>
              if r.caller.isNone && !st.replyStashedAt rid r then .ok (some rid)
              else .error .replyCapInvalid
          | none => .error .replyCapInvalid

/-- **WS-SX SX4: the thread a receive's busy reply cancels, as its code** (`0`
for none, `t + 1` for thread `t`): the reply capability the receive names,
resolved as `resolveRecvReplyId` resolves it, is busy with another thread
(`busyReplyHolderCode`), and the receiver may flow to that thread, whose IPC it
is about to cancel (the reply capability it presents is its authority over the
reply's holder).  Every answer is read from the state the receive is handed. -/
def recvBusyReplyHolderCode (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (decoded : SyscallDecodeResult) (st : SystemState) : Nat :=
  match receiveReplyAddr? decoded with
  | none => 0
  | some replyAddr =>
  match lookupReplyCap { gate with capAddr := replyAddr } st with
  | .error _ => 0
  | .ok (_, rid) =>
      let h := busyReplyHolderCode st tid rid
      if h = 0 then 0
      else if securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf ⟨h - 1⟩) then h
      else 0

/-- **WS-SX SX4: a receive's busy-reply cancel** (seL4-MCS `receiveIPC`'s
`cancelIPC(replyTCB)`): the holder `recvBusyReplyHolderCode` names cancelled in
place (`cancelReplyHolder`), committed as seL4's `cancelIPC` is; the state as it
was when there is none. -/
def cancelRecvBusyReply (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (decoded : SyscallDecodeResult) (executingCore : Concurrency.CoreId)
    (st : SystemState) : SystemState :=
  match recvBusyReplyHolderCode ctx tid gate decoded st with
  | 0 => st
  | k + 1 => cancelReplyHolder st ⟨k⟩ executingCore

/-- **The reply object a receive's reply capability names** — the lookup
`resolveRecvReplyId` and `recvBusyReplyHolderCode` both make, without the
freeness check: what the receive's lock operands name when its reply is busy, so
its footprints can name the holder the receive cancels. -/
def recvReplyLookup? (gate : SyscallGate) (decoded : SyscallDecodeResult)
    (st : SystemState) : Option SeLe4n.ReplyId :=
  match receiveReplyAddr? decoded with
  | none => none
  | some replyAddr =>
  match lookupReplyCap { gate with capAddr := replyAddr } st with
  | .error _ => none
  | .ok (_, rid) => some rid

/-- The holder a receive cancels is the one its named reply is busy with. -/
theorem recvBusyReplyHolderCode_succ {ctx : LabelingContext} {tid : SeLe4n.ThreadId}
    {gate : SyscallGate} {decoded : SyscallDecodeResult} {st : SystemState} {k : Nat}
    (h : recvBusyReplyHolderCode ctx tid gate decoded st = k + 1) :
    busyReplyHolder? st tid (recvReplyLookup? gate decoded st) = some ⟨k⟩ := by
  unfold recvBusyReplyHolderCode at h
  unfold recvReplyLookup?
  cases hA : receiveReplyAddr? decoded with
  | none => simp [hA] at h
  | some replyAddr =>
  simp only [hA] at h ⊢
  cases hL : lookupReplyCap { gate with capAddr := replyAddr } st with
  | error e => rw [hL] at h; simp at h
  | ok p =>
    obtain ⟨_, rid⟩ := p
    rw [hL] at h
    simp only at h ⊢
    split at h
    · simp at h
    · split at h
      · simp only [busyReplyHolder?, h]
      · simp at h

/-- A receive whose named reply is busy with no other thread cancels nothing. -/
theorem cancelRecvBusyReply_eq_self_of_busyReplyHolder?_none {ctx : LabelingContext}
    {tid : SeLe4n.ThreadId} {gate : SyscallGate} {decoded : SyscallDecodeResult}
    {executingCore : Concurrency.CoreId} {st : SystemState}
    (h : busyReplyHolder? st tid (recvReplyLookup? gate decoded st) = none) :
    cancelRecvBusyReply ctx tid gate decoded executingCore st = st := by
  unfold cancelRecvBusyReply
  cases hC : recvBusyReplyHolderCode ctx tid gate decoded st with
  | zero => rfl
  | succ k =>
    have hB := recvBusyReplyHolderCode_succ hC
    rw [h] at hB
    cases hB

/-- **A receive's busy-reply cancel is the identity, or a holder's cancel** —
of a holder that is never the receiver itself. -/
theorem cancelRecvBusyReply_cases (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (decoded : SyscallDecodeResult) (executingCore : Concurrency.CoreId)
    (st : SystemState) :
    cancelRecvBusyReply ctx tid gate decoded executingCore st = st ∨
      ∃ holder, holder ≠ tid ∧
        cancelRecvBusyReply ctx tid gate decoded executingCore st =
          cancelReplyHolder st holder executingCore := by
  unfold cancelRecvBusyReply
  cases hC : recvBusyReplyHolderCode ctx tid gate decoded st with
  | zero => exact Or.inl rfl
  | succ k => exact Or.inr ⟨⟨k⟩, busyReplyHolder?_ne (recvBusyReplyHolderCode_succ hC), rfl⟩

/-- A receive whose reply resolved free names no busy holder... -/
theorem busyReplyHolder?_of_resolveRecvReplyId_ok {gate : SyscallGate}
    {decoded : SyscallDecodeResult} {st : SystemState} {r : Option SeLe4n.ReplyId}
    (tid : SeLe4n.ThreadId) (h : resolveRecvReplyId gate decoded st = .ok r) :
    busyReplyHolder? st tid r = none := by
  unfold resolveRecvReplyId at h
  cases hA : receiveReplyAddr? decoded with
  | none => simp only [hA, Except.ok.injEq] at h; subst h; rfl
  | some replyAddr =>
  simp only [hA] at h
  cases hL : lookupReplyCap { gate with capAddr := replyAddr } st with
  | error e => rw [hL] at h; cases h
  | ok p =>
    obtain ⟨_, rid⟩ := p
    rw [hL] at h
    simp only at h
    cases hR : st.getReply? rid with
    | none => rw [hR] at h; cases h
    | some rr =>
      rw [hR] at h
      simp only at h
      split at h
      · rename_i hFree
        simp only [Except.ok.injEq] at h
        subst h
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true'] at hFree
        simp only [busyReplyHolder?, busyReplyHolderCode, hR, hFree.1, hFree.2,
          Bool.false_eq_true, ↓reduceIte]
      · cases h

/-- ...and so cancels none. -/
theorem busyReplyHolder?_recvReplyLookup?_of_resolveRecvReplyId_ok
    {gate : SyscallGate} {decoded : SyscallDecodeResult} {st : SystemState}
    {r : Option SeLe4n.ReplyId} (tid : SeLe4n.ThreadId)
    (h : resolveRecvReplyId gate decoded st = .ok r) :
    busyReplyHolder? st tid (recvReplyLookup? gate decoded st) = none := by
  have hN := busyReplyHolder?_of_resolveRecvReplyId_ok tid h
  -- the named reply is the resolved one
  unfold resolveRecvReplyId at h
  unfold recvReplyLookup?
  cases hA : receiveReplyAddr? decoded with
  | none => simp [hA, busyReplyHolder?]
  | some replyAddr =>
  simp only [hA] at h ⊢
  cases hL : lookupReplyCap { gate with capAddr := replyAddr } st with
  | error e => rw [hL] at h; cases h
  | ok p =>
    obtain ⟨_, rid⟩ := p
    rw [hL] at h
    simp only at h ⊢
    cases hR : st.getReply? rid with
    | none => rw [hR] at h; cases h
    | some rr =>
      rw [hR] at h
      simp only at h
      split at h
      · simp only [Except.ok.injEq] at h
        subst h
        exact hN
      · cases h

theorem recvBusyReplyHolderCode_eq_zero_of_resolveRecvReplyId_ok {ctx : LabelingContext}
    {tid : SeLe4n.ThreadId} {gate : SyscallGate} {decoded : SyscallDecodeResult}
    {st : SystemState} {r : Option SeLe4n.ReplyId}
    (h : resolveRecvReplyId gate decoded st = .ok r) :
    recvBusyReplyHolderCode ctx tid gate decoded st = 0 := by
  cases hC : recvBusyReplyHolderCode ctx tid gate decoded st with
  | zero => rfl
  | succ k =>
    have hB := recvBusyReplyHolderCode_succ hC
    rw [busyReplyHolder?_recvReplyLookup?_of_resolveRecvReplyId_ok tid h] at hB
    cases hB

/-- `lookupReplyCap` reads only CNodes. -/
theorem lookupReplyCap_congr_getCNode? (gate : SyscallGate) (st₁ st₂ : SystemState)
    (hC : ∀ id, st₁.getCNode? id = st₂.getCNode? id) :
    lookupReplyCap gate st₁ = lookupReplyCap gate st₂ := by
  have hL : ∀ ref, SystemState.lookupSlotCap st₁ ref = SystemState.lookupSlotCap st₂ ref := by
    intro ref
    have e := hC ref.cnode
    simp only [SystemState.getCNode?] at e
    simp only [SystemState.lookupSlotCap, SystemState.lookupCNode, e]
  unfold lookupReplyCap syscallLookupCap syscallResolveCap
  rw [SyscallGate.lookupSlot_congr_getCNode? _ st₁ st₂ hC]
  generalize SyscallGate.lookupSlot _ st₂ = res
  cases res with
  | error f => rfl
  | ok ref =>
    simp only [hL ref]
    generalize SystemState.lookupSlotCap st₂ ref = oc
    cases oc with
    | none => rfl
    | some cap =>
      by_cases hR : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
      · simp [hR]
      · by_cases hW : cap.hasRight AccessRight.write = true <;> simp [hR, hW]

/-- The busy-reply holder a receive names reads only the object store. -/
theorem recvBusyReplyHolderCode_congr_objects (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (decoded : SyscallDecodeResult) {st₁ st₂ : SystemState}
    (h : st₁.objects = st₂.objects) :
    recvBusyReplyHolderCode ctx tid gate decoded st₁ =
      recvBusyReplyHolderCode ctx tid gate decoded st₂ := by
  have hC : ∀ id, st₁.getCNode? id = st₂.getCNode? id := fun id => by
    simp only [SystemState.getCNode?, h]
  have hB : ∀ rid, busyReplyHolderCode st₁ tid rid = busyReplyHolderCode st₂ tid rid := by
    intro rid
    simp only [busyReplyHolderCode, SystemState.getReply?, SystemState.replyStashedAt,
      SystemState.getTcb?, h]
  unfold recvBusyReplyHolderCode
  simp only [lookupReplyCap_congr_getCNode? _ st₁ st₂ hC, hB]

/-- A receive whose CNodes a step left alone names the same reply after it: a
resolution on the later state, when it succeeds, is the reply the earlier
state's lookup named. -/
theorem resolveRecvReplyId_eq_of_getCNode? {gate : SyscallGate}
    {decoded : SyscallDecodeResult} {st st' : SystemState} {rid : SeLe4n.ReplyId}
    {r : Option SeLe4n.ReplyId}
    (hC : ∀ id, st'.getCNode? id = st.getCNode? id)
    (hLk : recvReplyLookup? gate decoded st = some rid)
    (h : resolveRecvReplyId gate decoded st' = .ok r) : r = some rid := by
  unfold recvReplyLookup? at hLk
  unfold resolveRecvReplyId at h
  cases hA : receiveReplyAddr? decoded with
  | none => simp [hA] at hLk
  | some replyAddr =>
  simp only [hA] at h hLk
  rw [lookupReplyCap_congr_getCNode? _ st' st hC] at h
  cases hL : lookupReplyCap { gate with capAddr := replyAddr } st with
  | error e => rw [hL] at h; cases h
  | ok p =>
    obtain ⟨_, rid'⟩ := p
    rw [hL] at h hLk
    simp only [Option.some.injEq] at hLk
    subst hLk
    simp only at h
    split at h
    · split at h
      · simp only [Except.ok.injEq] at h; exact h.symm
      · cases h
    · cases h

/-- WS-SM SM6.D (PR #822 review): clear a server-first reply **stash**
(`TCB.pendingReceiveReply`) on a receiver woken by a plain `Send`.  A server that
blocked on `Recv` having supplied a reply object carries the stash so a later `Call`
can be linked to it (folded into the Call rendezvous via `linkServerStashedReply`);
but if a *one-way* `Send` rendezvouses
first, the server leaves `.blockedOnReceive` for `.ready` while the stash survives —
violating `pendingReceiveReplyWellFormed` (a stash lives only on a `.blockedOnReceive`
TCB) and leaving a stale `rid` a *future* `Call` rendezvous could mis-link.  The
reply object itself is untouched (it stays free, `caller = none`; the server still
holds its cap and may re-supply it on the next `Recv`); only the stash pointer is
cleared.  `receiver?` is the pre-send receive-queue head — the thread the send wakes
— captured before the rendezvous dequeues it.  A no-op (returns the state unchanged,
no store) when there is no woken receiver or it carries no stash, so the trace is
byte-identical on every stash-free send.  Symmetric to the no-reply stash-clear
folded into `endpointReceiveDual`'s no-sender path (#7.2). -/
def clearWokenReceiverStash (receiver? : Option SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    match receiver? with
    | none => .ok ((), st)
    | some receiver =>
        match st.getTcb? receiver with
        | some rTcb =>
            match rTcb.pendingReceiveReply with
            | some _ =>
                storeObject receiver.toObjId
                  (.tcb { rTcb with pendingReceiveReplyCode := 0 }) st
            | none => .ok ((), st)
        | none => .ok ((), st)

/-- WS-SM SM9.C.8 frame lemma: clearing a woken receiver's stash never touches
the declassification audit trail.

Every arm is either the identity or a single `storeObject`, whose own trail
frame this lifts.  Needed at the dispatch level rather than the transition
level: the `.declassifySignal` arm runs this *after* the declassifying
transition, and an arm-level statement about the trail has to cover the whole
arm — a post-processing step that appended would falsify the arm property while
leaving the transition's own theorem true. -/
theorem clearWokenReceiverStash_declassificationAuditLog_eq
    (receiver? : Option SeLe4n.ThreadId) (st : SystemState) (pair : Unit × SystemState)
    (hStep : clearWokenReceiverStash receiver? st = .ok pair) :
    pair.2.declassificationAuditLog = st.declassificationAuditLog := by
  unfold clearWokenReceiverStash at hStep
  cases receiver? with
  | none => cases hStep; rfl
  | some receiver =>
    simp only at hStep
    cases hTcb : st.getTcb? receiver with
    | none => rw [hTcb] at hStep; cases hStep; rfl
    | some rTcb =>
      rw [hTcb] at hStep
      simp only at hStep
      cases hStash : rTcb.pendingReceiveReply with
      | none => rw [hStash] at hStep; cases hStep; rfl
      | some rid =>
        rw [hStash] at hStep
        exact storeObject_declassificationAuditLog_eq st _ _ pair hStep

/-- WS-SM SM9.C.6 frame lemma: clearing a woken receiver's stash never touches
the scheduler.  Every arm is the identity or one `storeObject`. -/
theorem clearWokenReceiverStash_scheduler_eq
    (receiver? : Option SeLe4n.ThreadId) (st : SystemState) (pair : Unit × SystemState)
    (hStep : clearWokenReceiverStash receiver? st = .ok pair) :
    pair.2.scheduler = st.scheduler := by
  unfold clearWokenReceiverStash at hStep
  cases receiver? with
  | none => cases hStep; rfl
  | some receiver =>
    simp only at hStep
    cases hTcb : st.getTcb? receiver with
    | none => rw [hTcb] at hStep; cases hStep; rfl
    | some rTcb =>
      rw [hTcb] at hStep
      simp only at hStep
      cases hStash : rTcb.pendingReceiveReply with
      | none => rw [hStash] at hStep; cases hStep; rfl
      | some rid =>
        rw [hStash] at hStep
        exact storeObject_scheduler_eq st pair.2 _ _ (by
          obtain ⟨u, st2⟩ := pair; cases u; exact hStep)

/-- WS-SM SM9.C.6 frame lemma: clearing a woken receiver's stash never touches
the machine. -/
theorem clearWokenReceiverStash_machine_eq
    (receiver? : Option SeLe4n.ThreadId) (st : SystemState) (pair : Unit × SystemState)
    (hStep : clearWokenReceiverStash receiver? st = .ok pair) :
    pair.2.machine = st.machine := by
  unfold clearWokenReceiverStash at hStep
  cases receiver? with
  | none => cases hStep; rfl
  | some receiver =>
    simp only at hStep
    cases hTcb : st.getTcb? receiver with
    | none => rw [hTcb] at hStep; cases hStep; rfl
    | some rTcb =>
      rw [hTcb] at hStep
      simp only at hStep
      cases hStash : rTcb.pendingReceiveReply with
      | none => rw [hStash] at hStep; cases hStep; rfl
      | some rid =>
        rw [hStash] at hStep
        exact storeObject_machine_eq st pair.2 _ _ (by
          obtain ⟨u, st2⟩ := pair; cases u; exact hStep)

-- ============================================================================
-- WS-RR RR2.16 — `clearWokenReceiverStash` preserves the IPC invariant bundle
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- **WS-RR RR2.16**: `clearWokenReceiverStash` — the dispatch-level
post-processing step the live `.send`, `.signal` and `.declassifySignal` arms run
after their transition — preserves the whole IPC invariant bundle.

Every arm but one returns the state untouched.  The one that stores writes a
single TCB differing only in `pendingReceiveReply := none`, and:

* the fourteen structural conjuncts read no `pendingReceiveReply`
  (`storeObject_tcb_pendingReceiveReply_preserves_ipcInvariantCore`);
* the reply linkage reads `replyObject` and `ipcState`, both unchanged;
* `pendingReceiveReplyWellFormed` — the one conjunct that *does* read the field —
  is preserved because the write **clears** it: both of its obligations on the
  stored thread are about a `some rid` stash, and the new stash is `none`, so
  they are vacuous.  Clearing a stash can only discharge obligations, never
  create one, which is precisely why the clear was introduced (a woken server
  leaving `.blockedOnReceive` with a live stash violates the conjunct);
* the donation trio's binding half is framed, and the tail/queue-target
  conjuncts are framed by the unchanged `ipcState` / `queueNext`.

Unconditional in the post-state: nothing here is threaded. -/
theorem clearWokenReceiverStash_preserves_ipcInvariantFull
    (receiver? : Option SeLe4n.ThreadId) (st : SystemState) (pair : Unit × SystemState)
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st)
    (hStep : clearWokenReceiverStash receiver? st = .ok pair) :
    ipcInvariantFull pair.2 := by
  unfold clearWokenReceiverStash at hStep
  cases receiver? with
  | none => cases hStep; exact hInv
  | some receiver =>
    simp only at hStep
    cases hTcb : st.getTcb? receiver with
    | none => rw [hTcb] at hStep; cases hStep; exact hInv
    | some rTcb =>
      rw [hTcb] at hStep
      simp only at hStep
      cases hStash : rTcb.pendingReceiveReply with
      | none => rw [hStash] at hStep; cases hStep; exact hInv
      | some rid =>
        rw [hStash] at hStep
        obtain ⟨u, st'⟩ := pair
        cases u
        exact storeObject_stashCleared_preserves_ipcInvariantFull st st' receiver rTcb hObjInv
          hInv hTcb hStep

/-- WS-RR RR2.16: `clearWokenReceiverStash` preserves the Robin Hood object-store
invariant — every arm is the identity or a single `storeObject`. -/
theorem clearWokenReceiverStash_preserves_objects_invExt
    (receiver? : Option SeLe4n.ThreadId) (st : SystemState) (pair : Unit × SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : clearWokenReceiverStash receiver? st = .ok pair) :
    pair.2.objects.invExt := by
  unfold clearWokenReceiverStash at hStep
  cases receiver? with
  | none => cases hStep; exact hObjInv
  | some receiver =>
    simp only at hStep
    cases hTcb : st.getTcb? receiver with
    | none => rw [hTcb] at hStep; cases hStep; exact hObjInv
    | some rTcb =>
      rw [hTcb] at hStep
      simp only at hStep
      cases hStash : rTcb.pendingReceiveReply with
      | none => rw [hStash] at hStep; cases hStep; exact hObjInv
      | some rid =>
        rw [hStash] at hStep
        exact storeObject_preserves_objects_invExt' st _ _ pair hObjInv hStep

/-- WS-SM SM6.D (faithful seL4-MCS `ReplyRecv`): resolve the server-supplied reply
capability a reply-receive replies through to the `(ReplyId, prevCaller)` pair
it authorizes — `prevCaller` is the reply object's `caller`, the previous caller
the reply leg answers.  WS-SX SX7.3: the reply capability is the one at
`replyRegister` (`decoded.replyCPtr`, x6), seL4-MCS's `SysReplyRecv`, whatever
the message length.  Resolves the reply cap from the caller's CSpace at that
address (a gate whose `capAddr` is that slot), then `getReply?` + reads
`reply.caller`.  Read-only.  A reply capability that does not look up
(`lookupReplyCap`, seL4-MCS `lookupReply`) answers `.failedLookup false lf`,
the receive's capability fault carrying the lookup fault `lf`, mirroring
`resolveRecvReplyId`.  WS-SX SX7.2: a reply object with **no outstanding
caller** answers `.ok none`: seL4-MCS's `doReplyTransfer` returns with nothing
to do when the reply's `replyTCB` is `NULL` or not blocked on reply, and the
receive half still runs (authority flows from *holding* the reply cap, exactly
like the `.reply` arm — no raw-thread bypass). -/
def resolveReplyRecvReply (gate : SyscallGate) (decoded : SyscallDecodeResult)
    (st : SystemState) :
    Except KernelError (Option (SeLe4n.ReplyId × SeLe4n.ThreadId × Option SeLe4n.Badge × Bool)) :=
  -- seL4-MCS `lookupReply`: a reply capability that does not look up is
  -- the receive's capability fault, its error the lookup fault itself.
  match lookupReplyCap { gate with capAddr := decoded.replyCPtr } st with
  | .error lf => .error (.failedLookup false lf)
  | .ok (rcap, rid) =>
          -- WS-RR RR7.11: one resolution of "which thread does this reply
          -- capability answer", shared with the `.reply` arm and with the
          -- declared-footprint resolver.
          match replyAnsweredCaller? st rid with
          -- PR #822 review: carry the *reply cap's* badge (the reply
          -- authority), not the endpoint receive cap's, so the previous
          -- caller receives the badge associated with the reply cap (as in
          -- the `.reply` arm) when the two differ.
          | some prevCaller => .ok (some (rid, prevCaller, rcap.badge, rcap.rights.mem .grant))
          | none => .ok none

/-- The CSpace root capability of the calling thread, as the syscall gate
reads it: its TCB's first space cell. -/
@[inline] def callerCspaceRoot (st : SystemState) (tid : SeLe4n.ThreadId) : Option Capability :=
  match st.getObject? tid.toObjId with
  | some (.tcb t) => t.spaceCells[0]
  | _ => none

/-- The gate a thread's own syscall reads its reply capability through: its
CSpace root, the reply authority (`lookupReplyCap` reads nothing else of a
gate but its caller and root, `lookupReplyCap_congr`). -/
@[inline] def callerReplyGate (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) : SyscallGate :=
  { callerId := tid, cspaceRootCap := callerCspaceRoot st tid, capAddr := decoded.replyCPtr,
    requiredRight := .write }

/-- **Whether a reply-receive skips its reply half**: its message names an
extra capability that does not look up, or its reply capability answers no
caller (`receivesWithoutReply`). -/
def replyRecvSkipsReply (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (st : SystemState) : Bool :=
  (callerExtraCapsFault? st tid decoded.msgInfo.extraCaps).isSome ||
    match resolveReplyRecvReply (callerReplyGate st tid decoded) decoded st with
    | .ok none => true
    | _ => false

/-- **The dispatch runs the receive arm with no reply leg**: a `.receive`, or
a `.replyRecv` whose reply half is skipped — its message names an extra
capability that does not look up (seL4-MCS `SysReplyRecv`: `handleInvocation`
with `isBlocking = false` skips the reply with no fault), or its reply
capability answers no caller (`doReplyTransfer` returns when the reply holds no
caller) — after which `handleRecv` still runs. -/
def receivesWithoutReply (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (st : SystemState) : Prop :=
  decoded.syscallId = .receive ∨
    (decoded.syscallId = .replyRecv ∧ replyRecvSkipsReply decoded tid st = true)

/-- `resolveReplyRecvReply` reads only the gate's caller and root. -/
theorem resolveReplyRecvReply_congr (g g' : SyscallGate) (decoded : SyscallDecodeResult)
    {st : SystemState} (h1 : g.callerId = g'.callerId) (h2 : g.cspaceRootCap = g'.cspaceRootCap) :
    resolveReplyRecvReply g decoded st = resolveReplyRecvReply g' decoded st := by
  unfold resolveReplyRecvReply
  rw [lookupReplyCap_congr { g with capAddr := decoded.replyCPtr }
    { g' with capAddr := decoded.replyCPtr } h1 h2 rfl]

/-- `resolveReplyRecvReply` reads only the objects. -/
theorem resolveReplyRecvReply_congr_objects (gate : SyscallGate) (decoded : SyscallDecodeResult)
    {st₁ st₂ : SystemState} (h : st₁.objects = st₂.objects) :
    resolveReplyRecvReply gate decoded st₁ = resolveReplyRecvReply gate decoded st₂ := by
  have hC : ∀ id, st₁.getCNode? id = st₂.getCNode? id := fun id => by
    simp only [SystemState.getCNode?, h]
  unfold resolveReplyRecvReply
  rw [lookupReplyCap_congr_getCNode? _ st₁ st₂ hC]
  simp only [replyAnsweredCaller?, SystemState.getReply?, h]

/-- A thread's CSpace root reads only the objects. -/
theorem callerCspaceRoot_congr_objects (tid : SeLe4n.ThreadId) {st₁ st₂ : SystemState}
    (h : st₁.objects = st₂.objects) : callerCspaceRoot st₁ tid = callerCspaceRoot st₂ tid := by
  simp only [callerCspaceRoot, SystemState.getObject?_eq_getElem, h]

-- ============================================================================
-- Syscall soundness theorems
-- ============================================================================

/-- **WS-LS LS2.3**: the reply a `.replyRecv` resolves is one the state records
an answered caller for — the resolver's own last check, read back out so the
scheduler footprint's `replyAnsweredCaller?` read is the arm's. -/
theorem resolveReplyRecvReply_answered (gate : SyscallGate) (decoded : SyscallDecodeResult)
    (st : SystemState) (rid : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId)
    (badge : Option SeLe4n.Badge) (grant : Bool)
    (h : resolveReplyRecvReply gate decoded st = .ok (some (rid, prevCaller, badge, grant))) :
    replyAnsweredCaller? st rid = some prevCaller := by
  unfold resolveReplyRecvReply at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · rename_i hAns
      simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hR, hP, _⟩ := h
      subst hR; subst hP
      exact hAns
    · exact absurd h (by simp)

/-- **WS-LS LS2.3**: the rights-gated lookup succeeds only through a successful
resolution of the same gate at the same state. -/
theorem syscallLookupCap_resolve (gate : SyscallGate) (st : SystemState) (cap : Capability)
    (h : syscallLookupCap gate st = .ok (cap, st)) :
    syscallResolveCap gate st = .ok (cap, st) := by
  unfold syscallLookupCap at h
  split at h
  · exact absurd h (by simp)
  · rename_i cap' st' hRes
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hC, hS⟩ := h
      subst hC; subst hS
      exact hRes
    · exact absurd h (by simp)

/-- **WS-LS LS2.3**: resolution reads the object store alone, so it answers the
same at two states with the same store — the shape of the register spill and
the IPC-buffer TLB fill between the seam's plan and its dispatch. -/
theorem syscallResolveCap_congr_objects (gate : SyscallGate) (st₁ st₂ : SystemState)
    (cap : Capability) (hObj : st₁.objects = st₂.objects)
    (h : syscallResolveCap gate st₁ = .ok (cap, st₁)) :
    syscallResolveCap gate st₂ = .ok (cap, st₂) := by
  unfold syscallResolveCap at h ⊢
  rw [gate.lookupSlot_congr_objects st₁ st₂ hObj] at h
  cases hRef : gate.lookupSlot st₂ with
  | error e => rw [hRef] at h; exact absurd h (by simp)
  | ok ref =>
    rw [hRef] at h
    simp only at h ⊢
    rw [lookupSlotCap_congr_objects st₁ st₂ ref hObj] at h
    cases hLk : SystemState.lookupSlotCap st₂ ref with
    | none => rw [hLk] at h; exact absurd h (by simp)
    | some cap' =>
      rw [hLk] at h
      simp only at h ⊢
      by_cases hRes : capTargetsReservedKernelObject cap' = true
      · rw [if_pos hRes] at h; exact absurd h (by simp)
      · rw [if_neg hRes] at h ⊢
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [h.1]

/-- WS-H15c/A-42: If `syscallLookupCap` succeeds, the caller's CSpace root
contains a valid capability at the specified address with the required right,
and the state is unchanged (lookup is read-only). -/
theorem syscallResolveCap_implies_capability_at_slot
    (gate : SyscallGate) (st : SystemState) (cap : Capability) (st' : SystemState)
    (hOk : syscallResolveCap gate st = .ok (cap, st')) :
    ∃ ref, gate.lookupSlot st = .ok ref ∧
           SystemState.lookupSlotCap st ref = some cap ∧
           st' = st := by
  unfold syscallResolveCap at hOk
  split at hOk
  · simp at hOk
  next ref hResolve =>
    split at hOk
    · simp at hOk
    next cap' hLookup =>
      split at hOk
      · simp at hOk
      · simp at hOk
        obtain ⟨hCap, hSt⟩ := hOk
        exact ⟨ref, hResolve, by rw [hCap.symm]; exact hLookup, hSt.symm⟩

/-- PR #889 review round 2: **no resolved capability names a reserved idle
object.**  Every invoked capability resolves through `syscallResolveCap`, so
this is the chokepoint form of "no syscall can act on a per-core idle TCB": a
boot CNode that carried a writable capability to `(idleThreadId c).toObjId`, or
a transfer that delivered one, yields a slot that resolves `.invalidCapability`
— exactly as an empty slot does, so the refusal discloses nothing about the
reservation. -/
theorem syscallResolveCap_ok_not_reserved
    (gate : SyscallGate) (st : SystemState) (cap : Capability) (st' : SystemState)
    (hOk : syscallResolveCap gate st = .ok (cap, st')) :
    SeLe4n.Kernel.capTargetsReservedKernelObject cap = false := by
  unfold syscallResolveCap at hOk
  split at hOk
  · simp at hOk
  next ref hResolve =>
    split at hOk
    · simp at hOk
    next cap' hLookup =>
      split at hOk
      · simp at hOk
      next hNot =>
        simp at hOk
        obtain ⟨hCap, _⟩ := hOk
        rw [← hCap]
        simpa using hNot

/-- WS-ZA ZA6.32: **no resolved capability reaches an interrupt node.**  A
line's node is kernel-reserved as the idle threads are
(`capTargetsReservedKernelObject_irqNode`), so a capability naming the node, or
a slot of it, resolves `.invalidCapability` at the one resolution every invoked
capability passes through: the node's slot is written only by
`seL4_IRQHandler_SetNotification` and `seL4_IRQHandler_Clear`, through the
handler capability, as seL4's `irq_node` slots are. -/
theorem syscallResolveCap_ok_not_irqNode
    (gate : SyscallGate) (st : SystemState) (cap : Capability) (st' : SystemState)
    (hOk : syscallResolveCap gate st = .ok (cap, st')) {line : Nat}
    (hLine : line < SeLe4n.InterruptLineSet.capacity) :
    cap.target ≠ .object (irqNodeId line) ∧
      ∀ s, cap.target ≠ .cnodeSlot (irqNodeId line) s := by
  have hR := syscallResolveCap_ok_not_reserved gate st cap st' hOk
  refine ⟨fun h => ?_, fun s h => ?_⟩
  · rw [capTargetsReservedKernelObject_irqNode cap hLine (.inl h)] at hR; cases hR
  · rw [capTargetsReservedKernelObject_irqNode cap hLine (.inr ⟨s, h⟩)] at hR; cases hR

/-- PR #870 round 5: a full-lookup success is a resolve success — the rights
gate only filters, never resolves.  What lets `syscallResolveCap`-based
hypotheses cover the classic lookup branch too. -/
theorem syscallResolveCap_of_lookup
    (gate : SyscallGate) (st : SystemState) (cap : Capability) (st' : SystemState)
    (hOk : syscallLookupCap gate st = .ok (cap, st')) :
    syscallResolveCap gate st = .ok (cap, st') := by
  unfold syscallLookupCap at hOk
  split at hOk
  · simp at hOk
  next cap' st'' hRes =>
    split at hOk
    · simp at hOk
      obtain ⟨hCap, hSt⟩ := hOk
      rw [← hCap, ← hSt]
      exact hRes
    · simp at hOk

theorem syscallLookupCap_implies_capability_held
    (gate : SyscallGate) (st : SystemState) (cap : Capability) (st' : SystemState)
    (hOk : syscallLookupCap gate st = .ok (cap, st')) :
    ∃ ref, gate.lookupSlot st = .ok ref ∧
           SystemState.lookupSlotCap st ref = some cap ∧
           cap.hasRight gate.requiredRight = true ∧
           st' = st := by
  have hRes := syscallResolveCap_of_lookup gate st cap st' hOk
  obtain ⟨ref, hResolve, hLookup, hSt⟩ :=
    syscallResolveCap_implies_capability_at_slot gate st cap st' hRes
  refine ⟨ref, hResolve, hLookup, ?_, hSt⟩
  by_cases hR : cap.hasRight gate.requiredRight
  · exact hR
  · exfalso
    unfold syscallLookupCap at hOk
    rw [hRes] at hOk
    simp [hR] at hOk

-- ============================================================================
-- S5-A: Deprecated api* wrappers removed (v0.19.4)
--
-- All 14 deprecated wrappers (apiEndpointSend, apiEndpointReceive,
-- apiEndpointCall, apiEndpointReply, apiCspaceMint, apiCspaceCopy,
-- apiCspaceMove, apiCspaceDelete, apiLifecycleRetype, apiVspaceMap,
-- apiVspaceUnmap, apiServiceRegister, apiServiceRevoke, apiServiceQuery)
-- were removed in S5-A. The production syscall path is:
--   syscallEntryChecked → dispatchSyscallChecked → syscallInvokeTyped →
--   dispatchWithCapChecked
-- Test migration was completed in S2-J (v0.19.1).
-- ============================================================================

-- ============================================================================
-- WS-J1-C: Syscall entry point and dispatch
-- ============================================================================

/-! ## WS-J1-C: Register-sourced syscall entry point

Wires the register decode layer (WS-J1-B) into a top-level user-space entry
point that:
1. Reads the current thread's register file from its TCB.
2. Decodes raw register values into typed kernel references via
   `decodeSyscallArgs`.
3. Dispatches to the appropriate kernel operation through capability-gated
   `syscallInvokeTyped`.

This closes the gap where the prior model accepted pre-typed arguments directly,
bypassing the register file entirely. -/

open Architecture.RegisterDecode
open Architecture.SyscallArgDecode

/-- WS-J1-C: Extract the current thread's saved register context from its TCB.
Returns `objectNotFound` if the thread ID does not correspond to any object,
or `illegalState` if the object is not a TCB. -/
def lookupThreadRegisterContext (tid : SeLe4n.ThreadId) : Kernel SeLe4n.RegisterFile :=
  fun st =>
    match st.getObject? tid.toObjId with
    | some (.tcb tcb) => .ok (tcb.registerContext, st)
    | some _          => .error .illegalState
    | none            => .error .objectNotFound

/-- WS-J1-C: Map each syscall identifier to its required access right.
Matches the authority requirements of the corresponding `api*` wrappers. -/
def syscallRequiredRight : SyscallId → AccessRight
  | .send            => .write
  | .receive         => .read
  | .call            => .write
  | .reply           => .write
  | .cspaceMint      => .grant
  | .cspaceCopy      => .grant
  | .cspaceMove      => .grant
  | .cspaceDelete    => .write
  -- **WS-RR RR8.16 (`v0.35.190`)**: revocation is `.write`, the delete's right,
  -- and that is seL4's authority model rather than a convenience.  The right to
  -- destroy a capability's *derivations* comes from holding the **parent**, not
  -- from holding the CNodes the descendants live in — which is exactly what a
  -- capability derivation tree is for — so a revocation that reaches into other
  -- CSpaces is authorised by write on the slot it starts from.  `.grant` would
  -- be wrong in the other direction: granting is the right to *hand out*
  -- authority, and revocation hands out none.
  | .cspaceRevoke    => .write
  -- **WS-BP BP7.1 (`v0.36.5`)**: a carve is a retype of the untyped's memory,
  -- so it takes the retype right — the one `lifecycleRetypeAuthority` checks
  -- inside `retypeFromUntyped` too, so the gate and the primitive agree.
  | .untypedRetype   => .retype
  -- **WS-SX SX6.3 (D6)**: `seL4_ARM_Page_Map` is invoked on the frame
  -- capability, and every mapping grants at least read access to the page, so
  -- the frame capability is held with `.read` (`resolveVSpaceMapFrame` asks the
  -- same right of it); a writable mapping needs `.write` on it as well
  -- (`frameMappingAdmissible`).
  | .vspaceMap       => .read
  -- `seL4_ARM_Page_Unmap` is invoked on the same frame capability and asks of
  -- it no more than the map does.
  | .vspaceUnmap     => .read
  -- WS-SM SM7.D: publishing freshly-written code requires the **write** right
  -- on the page's capability.  seL4's `Page_Unify_Instruction` needs only the
  -- frame cap; requiring write is the least-privilege reading of the same
  -- authority — the operation exists to push *the caller's own stores* to the
  -- Point of Unification, so the subject that needs it is by construction one
  -- that could write the page.  A read-only holder gains nothing by unifying.
  | .vspaceUnifyInstruction => .write
  -- WS-SX SX6.7: the declassifications are invocations of the audit-trail
  -- capability, and recording a downgrade appends to the trail, so each takes
  -- the trail's **write** right, the drain's.  The object released into is
  -- extra capability 0 and needs its own write right as well
  -- (`declassifyTargetRight`): the flow runs from the caller into the object,
  -- and the data-carrying one signals the notification, which the ordinary
  -- `.notificationSignal` also asks write for — the declassification is an
  -- *additional* gate on top of that authority, never a substitute for it.
  | .declassify         => .write
  | .declassifySignal   => .write
  -- WS-SM SM9.A.10: the audit reader needs the **read** right and the drain the
  -- **write** right, on an audit capability (`extractAuditAuthority` is the
  -- first gate; this is the second).  Two rights on one target rather than one
  -- syscall with a mode operand, so a monitoring deployment can mint a
  -- read-only audit capability that provably cannot drain.
  | .auditRead          => .read
  | .auditDrain         => .write
  | .serviceRegister    => .write
  | .serviceRevoke      => .write
  | .serviceQuery       => .read
  | .notificationSignal => .write
  | .notificationWait   => .read
  | .replyRecv          => .read
  | .schedContextConfigure => .write
  | .schedContextBind      => .write
  | .schedContextUnbind    => .write
  | .schedContextUnbindObject => .write
  | .tcbSuspend            => .write
  | .tcbResume             => .write
  | .tcbSetPriority        => .write
  | .tcbSetMCPriority      => .write
  | .tcbSetIPCBuffer       => .write
  | .tcbSetAffinity        => .write
  -- **WS-BP BP7.1 (`v0.36.11`)**: setting a thread's roots is configuring the
  -- thread — the write right on its TCB, like every thread-configuration arm.
  | .tcbSetSpace           => .write
  -- **WS-BP BP7.1 (`v0.36.12`)**: installing or removing a page table changes
  -- the table object — the write right on the table capability.
  | .pageTableMap          => .write
  | .pageTableUnmap        => .write
  | .tcbBindNotification   => .write
  | .tcbUnbindNotification => .write
  -- PR #822 Phase H: deriving a reply cap from the object cap to a Reply requires
  -- grant authority on that object cap (consistent with the cspaceMint/Copy/Move family).
  | .mintReplyCap          => .grant
  -- WS-ZA ZA4.3: a yield invokes no capability — `dispatchSyscallChecked`
  -- runs it before any gate is built — so no right is
  -- ever checked for it.  `.read`, the weakest, is the value a gate would carry.
  | .yield                 => .read
  -- WS-ZA ZA6.9: the Consumed invocation writes the context (its consumed time
  -- is reset), so it carries the write right Bind and Unbind carry; seL4's
  -- scheduling-context capability has no rights of its own to check.
  | .schedContextConsumed  => .write
  | .schedContextYieldTo   => .write
  -- WS-ZA ZA6.32: the acknowledge writes the interrupt controller's mask for
  -- the line; seL4's interrupt-handler capability has no rights of its own to
  -- check, so it carries the write right the other writing invocations carry.
  | .irqHandlerAck         => .write
  -- WS-ZA ZA6.32: seL4's interrupt-control and interrupt-handler capabilities
  -- carry no rights of their own; the issue, bind and unbind write kernel
  -- state, so each carries the write right the other writing invocations do.
  | .irqControlGet         => .write
  | .irqHandlerSetNotification => .write
  | .irqHandlerClear       => .write

/-- Whether the object `id` names is of kind `kind`, read in place.

An absent object answers `true`: the arm the capability reaches answers it as it
always has.  Under `capabilityInvariantBundle` the case is unreachable:
`capabilityInvariantBundle_objectCapsBacked` backs every `.object` capability a
slot holds with a present object. -/
@[inline] def objectKindIs (st : SystemState) (id : SeLe4n.ObjId)
    (kind : KernelObjectType) : Bool :=
  match st.getObject? id with
  | some o => o.objectType == kind
  | none => true

/-- **The kind of object each syscall invokes through an `.object`
capability**, or `none` where it invokes none: the `none` syscalls invoke a
capability of another target (WS-SX SX6.7: the declassifications invoke the
audit-trail capability, their object an extra capability; the service calls
invoke the service-registry capability, their endpoint an extra capability).  No wildcard: a new syscall states its kind. -/
def syscallObjectKind? : SyscallId → Option KernelObjectType
  | .send | .receive | .call | .replyRecv => some .endpoint
  | .notificationSignal | .notificationWait => some .notification
  | .cspaceMint | .cspaceCopy | .cspaceMove | .cspaceDelete | .cspaceRevoke
  | .mintReplyCap => some .cnode
  | .untypedRetype => some .untyped
  | .vspaceMap | .vspaceUnmap => some .frame
  | .vspaceUnifyInstruction => some .vspaceRoot
  | .schedContextBind | .schedContextUnbind | .schedContextUnbindObject | .schedContextConsumed
  | .schedContextYieldTo => some .schedContext
  | .tcbSuspend | .tcbResume | .tcbSetPriority | .tcbSetMCPriority | .tcbSetIPCBuffer
  | .tcbSetAffinity | .tcbSetSpace | .tcbBindNotification
  | .tcbUnbindNotification => some .tcb
  | .pageTableMap | .pageTableUnmap => some .pageTable
  | .declassify | .declassifySignal | .reply | .auditRead | .auditDrain | .schedContextConfigure
  | .serviceRegister | .serviceRevoke | .serviceQuery | .irqControlGet | .irqHandlerAck | .irqHandlerSetNotification | .irqHandlerClear
  | .yield => none

/-- **The target type each syscall invokes**, seL4's `decodeInvocation`
dispatch on the capability's type.  The type is the capability's `CapTarget`
constructor and, for an `.object` capability, the kind of the object it names,
read in place (`objectKindIs`).  The gate checks it after the lookup and before
any right (`syscallInvokeTyped`), so a capability of the wrong type answers
`.invalidCapability` whatever rights it carries.  The declassifications are
invocations of the audit-trail capability (WS-SX SX6.7), and the service calls
of the service-registry capability, so no `.object` capability selects them; the yield invokes no capability and accepts none.  Out of line, with the state and the capability
borrowed: every arm calls the one copy, and the arm keeps its state unshared. -/
@[noinline] def syscallTargetAccepted (sid : SyscallId) (st : @& SystemState)
    (cap : @& Capability) : Bool :=
  match cap.target with
  | .object id =>
      match syscallObjectKind? sid with
      | some kind => objectKindIs st id kind
      | none => false
  | .replyCap _ => sid == .reply
  | .auditTrail _ =>
      sid == .auditRead || sid == .auditDrain || sid == .declassify || sid == .declassifySignal
  | .schedControl _ => sid == .schedContextConfigure
  | .irqControl _ => sid == .irqControlGet
  | .serviceRegistry _ =>
      sid == .serviceRegister || sid == .serviceRevoke || sid == .serviceQuery
  | .irqHandler _ =>
      sid == .irqHandlerAck || sid == .irqHandlerSetNotification || sid == .irqHandlerClear
  | .cnodeSlotWord word => false

/-- **The answer to a capability of the right type without the syscall's
right.**  seL4's `decodeInvocation` refuses an endpoint or notification
capability without `CanSend` as `InvalidCapability` (invalid capability number
0), so `.send`, `.call` and `.notificationSignal` answer `.invalidCapability`.
seL4's
`handleRecv` raises a capability fault for an endpoint or notification without
`CanReceive`; the receive-phase syscalls answer `.invalidCapability`, which the
entry delivers as that fault (`syscallCapFaultOf`).  Every other right is an
seLe4n extension, checked after the type and before the length, and answers
`.illegalAuthority`.  No wildcard: a new syscall states its answer. -/
def syscallMissingRightError : SyscallId → KernelError
  | .send | .call | .notificationSignal => (.invalidCapability 0)
  | .receive | .notificationWait | .replyRecv => (.invalidCapability 0)
  | .reply | .cspaceMint | .cspaceCopy | .cspaceMove | .cspaceDelete | .cspaceRevoke
  | .untypedRetype | .vspaceMap | .vspaceUnmap | .vspaceUnifyInstruction
  | .declassify | .declassifySignal | .auditRead | .auditDrain | .serviceRegister | .serviceRevoke
  | .serviceQuery | .schedContextConfigure | .schedContextBind | .schedContextUnbind | .schedContextUnbindObject
  | .tcbSuspend | .tcbResume | .tcbSetPriority | .tcbSetMCPriority | .tcbSetIPCBuffer
  | .tcbSetAffinity | .tcbSetSpace | .pageTableMap
  | .pageTableUnmap | .yield | .schedContextConsumed | .schedContextYieldTo
  | .irqHandlerAck | .irqControlGet | .irqHandlerSetNotification | .irqHandlerClear
  | .tcbBindNotification | .tcbUnbindNotification | .mintReplyCap => .illegalAuthority

/-- **The refusal of a resolution that found no capability to invoke, when an
extra capability's lookup fails with `f`**, in seL4's order: an address that
does not resolve is `lookupCapAndSlot`'s failure, refused as the resolution
refused it; a slot that resolves but holds no capability user space may hold is
no failure of `lookupCapAndSlot`, which hands the null capability on, so the
extra capabilities' lookup runs (`lookupExtraCaps`) and its failure is the
refusal, before `decodeInvocation` would refuse the null capability. -/
@[inline] def syscallResolveRefusal (e : KernelError) (f : LookupFault) : KernelError :=
  match e with
  | .failedLookup w f' => .failedLookup w f'
  | _ => .failedLookup false f

/-- **The syscall gate, in seL4's order** (`handleInvocation`): resolve the
capability (`lookupCapAndSlot`), then the extra capabilities' lookup
(`lookupExtraCaps`), whose first failure `xf` — its address and lookup fault —
is refused as `.failedLookup false`, the send-phase capability fault the entry
raises at that address; then the capability's type (`syscallTargetAccepted`,
`.invalidCapability`), then the syscall's right (`syscallMissingRightError`),
then the arm, which checks the message length and the arguments.  A slot that
holds no capability is no failure of the resolution in seL4, so the extra
capabilities are looked up before it is refused (`syscallResolveRefusal`).
Every check precedes every write.  The dispatchers hand `xf` in already read on
the state the gate runs on (`callerExtraCapsFault?`), `none` for a syscall that
receives on its capability, which looks no extra capability up (seL4's
`handleRecv`). -/
def syscallInvokeTyped (sid : SyscallId) (gate : SyscallGate)
    (xf : Option (SeLe4n.CPtr × LookupFault))
    (op : Capability → Kernel α) : Kernel α :=
  fun st =>
    match syscallResolveCap gate st with
    | .error e =>
      match xf with
      | none => .error e
      | some (_, f) => .error (syscallResolveRefusal e f)
    | .ok (cap, st') =>
      match xf with
      | some (_, f) => .error (.failedLookup false f)
      | none =>
        if !syscallTargetAccepted sid st' cap then .error (.invalidCapability 0)
        else if cap.hasRight gate.requiredRight then op cap st'
        else .error (syscallMissingRightError sid)

/-- **The syscalls that receive on the invoked capability**, seL4's
`handleRecv`: the receive, the notification wait, and the receive half of the
reply-receive.  No wildcard: a new syscall states its answer.  Pinned against
`Platform.FFI.capFaultReceivePhase?` (`syscallReceivesOnCap_iff_receivePhase`). -/
@[inline] def syscallReceivesOnCap : SyscallId → Bool
  | .receive | .notificationWait | .replyRecv => true
  | .send | .call | .reply | .cspaceMint | .cspaceCopy | .cspaceMove | .cspaceDelete
  | .cspaceRevoke | .untypedRetype | .vspaceMap | .vspaceUnmap
  | .vspaceUnifyInstruction | .declassify | .auditRead | .auditDrain | .declassifySignal
  | .serviceRegister | .serviceRevoke | .serviceQuery | .notificationSignal
  | .schedContextConfigure | .schedContextBind | .schedContextUnbind | .schedContextUnbindObject | .tcbSuspend
  | .tcbResume | .tcbSetPriority | .tcbSetMCPriority | .tcbSetIPCBuffer | .tcbSetAffinity
  | .tcbSetSpace | .pageTableMap | .pageTableUnmap | .yield
  | .schedContextConsumed | .schedContextYieldTo | .irqHandlerAck | .irqControlGet
  | .irqHandlerSetNotification | .irqHandlerClear | .tcbBindNotification
  | .tcbUnbindNotification | .mintReplyCap => false

/-- **How many extra capabilities a syscall looks up before its arm** (seL4's
`handleInvocation` runs `lookupExtraCaps` on the message info's count): the
count `n` its message info names, or none for a syscall that receives on its
capability, which seL4's `handleRecv` serves with no lookup of its own. -/
@[inline] def syscallExtraCapCount (sid : SyscallId) (n : Nat) : Nat :=
  if syscallReceivesOnCap sid then 0 else n

theorem callerExtraCapsFault?_zero (st : SystemState) (tid : SeLe4n.ThreadId) :
    callerExtraCapsFault? st tid 0 = none := by
  unfold callerExtraCapsFault?
  split
  · exact extraCapsLookupFault?_zero st _
  · rfl

/-- A receive-phase syscall looks no extra capability up. -/
theorem callerExtraCapsFault?_receive (st : SystemState) (tid : SeLe4n.ThreadId)
    (sid : SyscallId) (n : Nat) (h : syscallReceivesOnCap sid = true) :
    callerExtraCapsFault? st tid (syscallExtraCapCount sid n) = none := by
  simp only [syscallExtraCapCount, h, ↓reduceIte, callerExtraCapsFault?_zero]

theorem callerExtraCapsFault?_of_tcb {st : SystemState} {tid : SeLe4n.ThreadId} {tcb : TCB}
    (h : st.getObject? tid.toObjId = some (.tcb tcb)) (n : Nat) :
    callerExtraCapsFault? st tid n = extraCapsLookupFault? st tcb n := by
  simp only [callerExtraCapsFault?, h]

theorem callerExtraCapsFault?_perCoreTlb (st : SystemState) (tid : SeLe4n.ThreadId) (n : Nat)
    (t : Vector TlbState Concurrency.numCores) :
    callerExtraCapsFault? { st with perCoreTlb := t } tid n = callerExtraCapsFault? st tid n := by
  have hObj : ({ st with perCoreTlb := t } : SystemState).getObject? tid.toObjId =
      st.getObject? tid.toObjId := rfl
  unfold callerExtraCapsFault?
  rw [hObj]
  split <;> simp only [extraCapsLookupFault?_perCoreTlb]

/-- **The extra-capability failure a decoded syscall's gate refuses**: the
caller's lookup of the extra capabilities the message info names, none on a
receive-phase syscall (`syscallExtraCapCount`). -/
@[inline] def decodedExtraCapsFault? (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) : Option (SeLe4n.CPtr × LookupFault) :=
  callerExtraCapsFault? st tid (syscallExtraCapCount decoded.syscallId decoded.msgInfo.extraCaps)

/-- **A notification bound to another thread** (seL4's `handleRecv`): a wait on
a notification capability whose notification is bound to a thread other than
the waiter.  `false` on every other syscall and capability. -/
def receiveBoundRefuses (sid : SyscallId) (tid : SeLe4n.ThreadId) (st : SystemState)
    (cap : Capability) : Bool :=
  match sid, cap.target with
  | .notificationWait, .object id => notificationBoundElsewhere st id tid
  | _, _ => false

/-- Whether a receive refuses the capability it resolved as seL4's `handleRecv`
does: a receive-phase syscall whose capability is not of its type or lacks its
right, or names a notification bound to another thread.  seL4 raises a capability fault there, with the lookup failure
`missing_capability`, exactly as for a failed lookup. -/
def receiveGateRefuses (sid : SyscallId) (tid : SeLe4n.ThreadId) (st : SystemState)
    (cap : Capability) : Bool :=
  syscallReceivesOnCap sid &&
    (!syscallTargetAccepted sid st cap || !cap.hasRight (syscallRequiredRight sid) ||
      receiveBoundRefuses sid tid st cap)

/-- **The capability fault a receive's reply capability raises**
(seL4-MCS's `lookupReply`): the reply capability's address and the lookup
fault, when the receive names a reply capability (`receiveReplyAddr?`) that
does not look up (`lookupReplyCap`) through the caller's gate.  The arms refuse
that receive `failedLookup` with the same fault (`resolveRecvReplyId`,
`resolveReplyRecvReply`), and the entry raises the fault rather than return the
error. -/
def receiveReplyFault? (gate : SyscallGate) (decoded : SyscallDecodeResult)
    (st : SystemState) : Option (SeLe4n.CPtr × LookupFault) :=
  match receiveReplyAddr? decoded with
  | none => none
  | some replyAddr =>
      match lookupReplyCap { gate with capAddr := replyAddr } st with
      | .error lf => some (replyAddr, lf)
      | .ok _ => none

/-- **The reply capability's fault a receive's refusal raises**: a refusal
that is the reply capability's own failed lookup, as `receiveReplyFault?` finds
it on the state the refusal hands back, is raised as the capability fault at
the reply capability's address with that lookup fault (seL4-MCS
`lookupReply`).  Decided on the lookup, not on the refusal's form: a
`failedLookup` refusal the reply capability's lookup did not raise is an
error. -/
def receiveReplyFaults (gate : SyscallGate) (decoded : SyscallDecodeResult)
    (st : SystemState) (ke : KernelError) : Option (SeLe4n.CPtr × LookupFault) :=
  match receiveReplyFault? gate decoded st with
  | some (replyAddr, lf) => if ke = .failedLookup false lf then some (replyAddr, lf) else none
  | none => none

/-- `receiveReplyFaults` for a refusal handed on as its discriminant and
payload words: only a refusal whose words are a `failedLookup` with the
receive phase's `false` word re-runs the reply lookup, and its fault is
compared on the words (`KernelError.matchesWords`), so no error is rebuilt. -/
@[inline] def receiveReplyFaultsW (gate : SyscallGate) (decoded : SyscallDecodeResult)
    (st : SystemState) (d : Nat) (w0 w1 w2 w3 w4 : UInt64) :
    Option (SeLe4n.CPtr × LookupFault) :=
  if d == (KernelError.failedLookup false .invalidRoot).toDiscriminant && w0 == 0 then
    match receiveReplyFault? gate decoded st with
    | some (replyAddr, lf) =>
        if (KernelError.failedLookup false lf).matchesWords d w0 w1 w2 w3 w4 then
          some (replyAddr, lf)
        else none
    | none => none
  else none

theorem receiveReplyFaultsW_eq (gate : SyscallGate) (decoded : SyscallDecodeResult)
    (st : SystemState) (ke : KernelError) :
    receiveReplyFaultsW gate decoded st ke.toDiscriminant (ke.payloadWord 0) (ke.payloadWord 1)
        (ke.payloadWord 2) (ke.payloadWord 3) (ke.payloadWord 4) =
      receiveReplyFaults gate decoded st ke := by
  unfold receiveReplyFaultsW receiveReplyFaults
  cases h : receiveReplyFault? gate decoded st with
  | none => split <;> rfl
  | some p =>
    obtain ⟨replyAddr, lf⟩ := p
    simp only [KernelError.matchesWords_iff]
    by_cases hk : ke = KernelError.failedLookup false lf
    · subst hk
      simp [KernelError.toDiscriminant, KernelError.payloadWord]
    · have hk' : ¬KernelError.failedLookup false lf = ke := fun e => hk e.symm
      simp only [hk, hk', ↓reduceIte]
      split <;> rfl

/-- A receive refused by its reply capability's resolution raises the
capability fault: the refusal is `lookupReplyCap`'s failure at the address
`receiveReplyAddr?` reads (seL4-MCS's `lookupReply`). -/
theorem resolveRecvReplyId_failedLookup (gate : SyscallGate) (decoded : SyscallDecodeResult)
    (st : SystemState) (w : Bool) (lf : LookupFault) (hSid : decoded.syscallId = .receive)
    (h : resolveRecvReplyId gate decoded st = .error (.failedLookup w lf)) :
    ∃ replyAddr, receiveReplyFaults gate decoded st (.failedLookup w lf) = some (replyAddr, lf) := by
  unfold resolveRecvReplyId at h
  unfold receiveReplyFaults receiveReplyFault?
  cases hA : receiveReplyAddr? decoded with
  | none => simp [hA] at h
  | some replyAddr =>
  simp only [hA] at h ⊢
  cases hL : lookupReplyCap { gate with capAddr := replyAddr } st with
  | error lf' =>
    rw [hL] at h
    simp only [Except.error.injEq, KernelError.failedLookup.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨replyAddr, by simp⟩
  | ok p =>
    rw [hL] at h
    simp only at h
    split at h <;> (try split at h) <;> cases h

/-- A reply-receive refused by its reply capability's resolution likewise
raises the capability fault. -/
theorem resolveReplyRecvReply_failedLookup (gate : SyscallGate) (decoded : SyscallDecodeResult)
    (st : SystemState) (w : Bool) (lf : LookupFault) (hSid : decoded.syscallId = .replyRecv)
    (h : resolveReplyRecvReply gate decoded st = .error (.failedLookup w lf)) :
    ∃ replyAddr, receiveReplyFaults gate decoded st (.failedLookup w lf) = some (replyAddr, lf) := by
  unfold resolveReplyRecvReply at h
  unfold receiveReplyFaults receiveReplyFault? receiveReplyAddr?
  rw [hSid]
  simp only
  cases hL : lookupReplyCap { gate with capAddr := decoded.replyCPtr } st with
  | error lf' =>
    rw [hL] at h
    simp only [Except.error.injEq, KernelError.failedLookup.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨decoded.replyCPtr, by simp⟩
  | ok p =>
    rw [hL] at h
    simp only at h
    split at h <;> cases h

/-- A receive whose reply capability resolved raises no reply fault. -/
theorem receiveReplyFault?_of_resolveRecvReplyId_ok (gate : SyscallGate)
    (decoded : SyscallDecodeResult) (st : SystemState) (r : Option SeLe4n.ReplyId)
    (hSid : decoded.syscallId = .receive) (h : resolveRecvReplyId gate decoded st = .ok r) :
    receiveReplyFault? gate decoded st = none := by
  unfold receiveReplyFault?
  unfold resolveRecvReplyId at h
  cases hA : receiveReplyAddr? decoded with
  | none => rfl
  | some replyAddr =>
  simp only [hA] at h ⊢
  cases hL : lookupReplyCap { gate with capAddr := replyAddr } st with
  | error lf => rw [hL] at h; cases h
  | ok q => rfl

/-- A receive whose reply capability looked up raises no reply fault, whether
or not the reply it names is free. -/
theorem receiveReplyFault?_of_recvReplyLookup?_some (gate : SyscallGate)
    (decoded : SyscallDecodeResult) (st : SystemState) (rid : SeLe4n.ReplyId)
    (hSid : decoded.syscallId = .receive) (h : recvReplyLookup? gate decoded st = some rid) :
    receiveReplyFault? gate decoded st = none := by
  unfold recvReplyLookup? at h
  unfold receiveReplyFault?
  cases hA : receiveReplyAddr? decoded with
  | none => rfl
  | some replyAddr =>
  simp only [hA] at h ⊢
  cases hL : lookupReplyCap { gate with capAddr := replyAddr } st with
  | error e => simp [hL] at h
  | ok q => rfl

/-- A reply-receive whose reply capability resolved raises no reply fault. -/
theorem receiveReplyFault?_of_resolveReplyRecvReply_ok (gate : SyscallGate)
    (decoded : SyscallDecodeResult) (st : SystemState)
    (r : Option (SeLe4n.ReplyId × SeLe4n.ThreadId × Option SeLe4n.Badge × Bool))
    (hSid : decoded.syscallId = .replyRecv) (h : resolveReplyRecvReply gate decoded st = .ok r) :
    receiveReplyFault? gate decoded st = none := by
  unfold receiveReplyFault? receiveReplyAddr?
  unfold resolveReplyRecvReply at h
  rw [hSid]
  simp only
  cases hL : lookupReplyCap { gate with capAddr := decoded.replyCPtr } st with
  | error lf => rw [hL] at h; cases h
  | ok q => rfl

/-- **The syscalls that name a reply capability to receive with**: the
receive and the reply-receive.  No wildcard: a new syscall states its answer. -/
def syscallNamesReply : SyscallId → Bool
  | .receive | .replyRecv => true
  | .send | .call | .reply | .cspaceMint | .cspaceCopy | .cspaceMove | .cspaceDelete
  | .cspaceRevoke | .untypedRetype | .vspaceMap | .vspaceUnmap
  | .vspaceUnifyInstruction | .declassify | .auditRead | .auditDrain | .declassifySignal
  | .serviceRegister | .serviceRevoke | .serviceQuery | .notificationSignal
  | .notificationWait | .schedContextConfigure | .schedContextBind | .schedContextUnbind | .schedContextUnbindObject
  | .tcbSuspend | .tcbResume | .tcbSetPriority | .tcbSetMCPriority | .tcbSetIPCBuffer
  | .tcbSetAffinity | .tcbSetSpace | .pageTableMap | .pageTableUnmap
  | .yield | .schedContextConsumed | .schedContextYieldTo | .irqHandlerAck | .irqControlGet
  | .irqHandlerSetNotification | .irqHandlerClear | .tcbBindNotification
  | .tcbUnbindNotification | .mintReplyCap => false

/-- A syscall that names no reply capability raises no reply capability's
fault. -/
theorem receiveReplyAddr?_none_of_namesReply (decoded : SyscallDecodeResult)
    (h : syscallNamesReply decoded.syscallId = false) :
    receiveReplyAddr? decoded = none := by
  unfold receiveReplyAddr?
  split
  · next hS => rw [hS] at h; cases h
  · next hS => rw [hS] at h; cases h
  · rfl

/-- A receive's reply fault reads the object store alone. -/
theorem receiveReplyFault?_congr_objects (gate : SyscallGate) (decoded : SyscallDecodeResult)
    (st₁ st₂ : SystemState) (hObj : st₁.objects = st₂.objects) :
    receiveReplyFault? gate decoded st₁ = receiveReplyFault? gate decoded st₂ := by
  unfold receiveReplyFault?
  cases receiveReplyAddr? decoded with
  | none => rfl
  | some r =>
    dsimp only
    have hL : lookupReplyCap { gate with capAddr := r } st₁ =
        lookupReplyCap { gate with capAddr := r } st₂ := by
      unfold lookupReplyCap syscallLookupCap syscallResolveCap
      rw [SyscallGate.lookupSlot_congr_objects _ st₁ st₂ hObj]
      cases SyscallGate.lookupSlot _ st₂ with
      | error e => rfl
      | ok ref =>
        dsimp only
        rw [lookupSlotCap_congr_objects st₁ st₂ ref hObj]
        cases SystemState.lookupSlotCap st₂ ref with
        | none => rfl
        | some c =>
          dsimp only
          by_cases h1 : capTargetsReservedKernelObject c = true
          · simp [h1]
          · by_cases h2 : c.hasRight .write = true <;> simp [h1, h2]
    rw [hL]

/-- The reply capability's fault reads only CNodes. -/
theorem receiveReplyFault?_congr_getCNode? (gate : SyscallGate) (decoded : SyscallDecodeResult)
    (st₁ st₂ : SystemState) (hC : ∀ id, st₁.getCNode? id = st₂.getCNode? id) :
    receiveReplyFault? gate decoded st₁ = receiveReplyFault? gate decoded st₂ := by
  unfold receiveReplyFault?
  simp only [lookupReplyCap_congr_getCNode? _ st₁ st₂ hC]

theorem receiveReplyFaults_none_of_namesReply (gate : SyscallGate)
    (decoded : SyscallDecodeResult) (st : SystemState) (ke : KernelError)
    (h : syscallNamesReply decoded.syscallId = false) :
    receiveReplyFaults gate decoded st ke = none := by
  simp only [receiveReplyFaults, receiveReplyFault?, receiveReplyAddr?_none_of_namesReply decoded h]

/-- No one-overflow-word invocation names a reply capability. -/
theorem syscallNamesReply_of_routedOverflowOne {sid : SyscallId}
    (h : Architecture.RegisterDecode.routedOverflowOne sid = true) :
    syscallNamesReply sid = false := by
  revert h; cases sid <;> decide

/-- No register-routed invocation names a reply capability. -/
theorem syscallNamesReply_of_routedInvocation {sid : SyscallId}
    (h : Architecture.RegisterDecode.routedInvocation sid = true) :
    syscallNamesReply sid = false := by
  revert h; cases sid <;> decide

/-- No audited syscall names a reply capability. -/
theorem syscallNamesReply_of_routedAudited {sid : SyscallId}
    (h : Architecture.RegisterDecode.routedAudited sid = true) :
    syscallNamesReply sid = false := by
  revert h; cases sid <;> decide

/-- **The lookup a capability fault reads**, with the address that failed, in
the gate's order (`syscallInvokeTyped`): the resolution at the gate's address;
then the caller's `xc` extra capabilities (seL4's `lookupExtraCaps`,
`callerExtraCapsFault?`), the first that fails answered at its own address
with `.failedLookup false`, the error the gate refuses it with; then, for a
receive-phase syscall, the type and the right (`receiveGateRefuses`), whose
failure is the lookup failure `.invalidCapability`, seL4's
`missing_capability`.  The dispatchers look up `syscallExtraCapCount` of the
extra capabilities, none on a receive-phase syscall.

A slot that resolves but holds no capability user space may hold is not
`lookupCapAndSlot`'s failure in seL4: the extra capabilities are looked up
after it as after any other slot (`syscallResolveRefusal`), and the null
capability is then `decodeInvocation`'s `InvalidCapability` error, which raises
no fault — except on a receive-phase syscall, where `handleRecv` raises the
capability fault (`missing_capability`) for it. -/
def syscallOperandLookup (sid : SyscallId) (gate : SyscallGate) (xc : Nat)
    (st : SystemState) : Except (SeLe4n.CPtr × KernelError) Unit :=
  match syscallResolveCap gate st with
  | .error e =>
      match e with
      | .failedLookup w f => .error (gate.capAddr, .failedLookup w f)
      | e =>
        match callerExtraCapsFault? st gate.callerId xc with
        | some (a, f) => .error (a, .failedLookup false f)
        | none => if syscallReceivesOnCap sid then .error (gate.capAddr, e) else .ok ()
  | .ok (cap, _) =>
      match callerExtraCapsFault? st gate.callerId xc with
      | some (a, f) => .error (a, .failedLookup false f)
      | none =>
        if receiveGateRefuses sid gate.callerId st cap then .error (gate.capAddr, .invalidCapability 0)
        else .ok ()

/-- Every failure the lookup answers is either the resolution's or the
receive gate's, at the gate's address, or an extra capability's failed lookup
at that capability's address. -/
theorem syscallOperandLookup_error_cases (sid : SyscallId) (gate : SyscallGate) (xc : Nat)
    (st : SystemState) (a : SeLe4n.CPtr) (e : KernelError)
    (h : syscallOperandLookup sid gate xc st = .error (a, e)) :
    (a = gate.capAddr ∧ (syscallResolveCap gate st = .error e ∨ e = .invalidCapability 0)) ∨
    ∃ f, e = .failedLookup false f ∧ callerExtraCapsFault? st gate.callerId xc = some (a, f) := by
  unfold syscallOperandLookup at h
  rcases hR : syscallResolveCap gate st with e' | ⟨cap, _⟩
  · rw [hR] at h
    simp only at h
    split at h
    · cases h; exact .inl ⟨rfl, .inl rfl⟩
    · split at h
      · next a' f hX => cases h; exact .inr ⟨f, rfl, hX⟩
      · split at h
        · cases h; exact .inl ⟨rfl, .inl rfl⟩
        · cases h
  · rw [hR] at h
    simp only at h
    split at h
    · next a' f hX => cases h; exact .inr ⟨f, rfl, hX⟩
    · split at h
      · cases h; exact .inl ⟨rfl, .inr rfl⟩
      · cases h

/-- A successful typed gate resolved a capability of the syscall's type that
carries the required right, at the state it was handed, and ran the arm on it. -/
theorem syscallInvokeTyped_ok (sid : SyscallId) (gate : SyscallGate)
    {xf : Option (SeLe4n.CPtr × LookupFault)}
    (op : Capability → Kernel α) (st : SystemState) (a : α) (st' : SystemState)
    (hOk : syscallInvokeTyped sid gate xf op st = .ok (a, st')) :
    ∃ cap, syscallLookupCap gate st = .ok (cap, st) ∧
      syscallTargetAccepted sid st cap = true ∧ op cap st = .ok (a, st') := by
  unfold syscallInvokeTyped at hOk
  cases hR : syscallResolveCap gate st with
  | error e => rw [hR] at hOk; cases xf <;> exact absurd hOk (by simp)
  | ok p =>
    obtain ⟨cap, stR⟩ := p
    obtain ⟨_, _, _, hSt⟩ := syscallResolveCap_implies_capability_at_slot gate st cap stR hR
    subst hSt
    rw [hR] at hOk
    simp only at hOk
    cases xf with
    | some e => exact absurd hOk (by simp)
    | none =>
    simp only at hOk
    by_cases hT : syscallTargetAccepted sid stR cap = true
    · by_cases hRt : cap.hasRight gate.requiredRight = true
      · simp only [hT, hRt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
        exact ⟨cap, by simp only [syscallLookupCap, hR, hRt, ↓reduceIte], hT, hOk⟩
      · simp only [hT, hRt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
        exact absurd hOk (by simp)
    · simp only [hT, Bool.not_false, ↓reduceIte] at hOk
      exact absurd hOk (by simp)

/-- A successful typed gate met no extra-capability lookup failure. -/
theorem syscallInvokeTyped_ok_extraCaps (sid : SyscallId) (gate : SyscallGate)
    {xf : Option (SeLe4n.CPtr × LookupFault)}
    (op : Capability → Kernel α) (st : SystemState) (a : α) (st' : SystemState)
    (hOk : syscallInvokeTyped sid gate xf op st = .ok (a, st')) : xf = none := by
  unfold syscallInvokeTyped at hOk
  cases hR : syscallResolveCap gate st with
  | error e => rw [hR] at hOk; cases xf <;> exact absurd hOk (by simp)
  | ok p =>
    rw [hR] at hOk
    cases xf with
    | some e => exact absurd hOk (by simp)
    | none => rfl

/-- The typed gate's success implies a resolved capability with the required
right. -/
theorem syscallInvokeTyped_requires_right (sid : SyscallId)
    (gate : SyscallGate) {xf : Option (SeLe4n.CPtr × LookupFault)}
    (op : Capability → Kernel α) (st : SystemState)
    (a : α) (st' : SystemState)
    (hOk : syscallInvokeTyped sid gate xf op st = .ok (a, st')) :
    ∃ cap ref, gate.lookupSlot st = .ok ref ∧
               SystemState.lookupSlotCap st ref = some cap ∧
               cap.hasRight gate.requiredRight = true := by
  obtain ⟨cap, hL, _, _⟩ := syscallInvokeTyped_ok sid gate op st a st' hOk
  obtain ⟨ref, hRes, hSlot, hRight, _⟩ :=
    syscallLookupCap_implies_capability_held gate st cap st hL
  exact ⟨cap, ref, hRes, hSlot, hRight⟩

/-- V3-F (M-PRF-3): All callers of `resolveAddressBits` perform post-resolution
    rights checks. Any successful `syscallInvokeTyped` — the sole gateway used
    by `dispatchSyscallChecked` — implies the
    resolved capability holds the required access right. The gate composes
    `lookupSlot` (`resolveAddressBits` at 64 bits) → `lookupSlotCap` → the
    type → `hasRight` before any operation is executed. -/
theorem resolveAddressBits_callers_check_rights (sid : SyscallId)
    (gate : SyscallGate) {xf : Option (SeLe4n.CPtr × LookupFault)}
    (op : Capability → Kernel α)
    (st : SystemState) (a : α) (st' : SystemState)
    (hOk : syscallInvokeTyped sid gate xf op st = .ok (a, st')) :
    ∃ cap ref,
      gate.lookupSlot st = .ok ref ∧
      SystemState.lookupSlotCap st ref = some cap ∧
      cap.hasRight gate.requiredRight = true :=
  syscallInvokeTyped_requires_right sid gate op st a st' hOk

/-- AN7-E (API-M01): the resolver on an empty address array resolves
    nothing, granted or not. -/
theorem resolveExtraCaps_empty
    (root : Capability) (granted : Bool) (st : SystemState) :
    resolveExtraCaps root #[] granted st = #[] := by
  cases granted <;> rfl

/-- **PR #873 round 14: a sender without Grant resolves nothing, whatever it
asked for.**  The statement the gate is for: its addresses are not even looked
up.  Stated over an arbitrary address array, so it is the resolver's contract
rather than a fact about one input. -/
theorem resolveExtraCaps_ungranted
    (root : Capability) (capAddrs : Array SeLe4n.CPtr) (st : SystemState) :
    resolveExtraCaps root capAddrs false st = #[] := rfl

/-- WS-AL AL7-A (cascades AK7-E): lift a raw `ThreadId` to `ValidThreadId`
at the dispatch boundary. Returns `.error .invalidArgument` if the id
is the reserved sentinel, otherwise `.ok` with the validated subtype.

Usage pattern in `dispatchCapabilityOnly` arms:
```
match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
| .error e => .error e
| .ok vtid => handler st vtid.val
```
The guard fires BEFORE any handler entry so sentinel IDs never reach
downstream object-store lookups. Defense-in-depth (graceful
`.objectNotFound` at lookup time) remains intact.

**PR #889 review round 11 (P1): a reserved idle thread id is refused here.**
`syscallResolveCap` refuses a *capability* naming a reserved idle object, and
that covers every arm whose operand is the resolved capability's own target.
It does not cover an arm whose operand is a **raw id from a message
register**: `.schedContextBind` resolves its capability to the *SchedContext*
and takes the thread from `args.threadId`, so a caller holding an ordinary
writable SchedContext capability could name `idleThreadId c` — and
`schedContextBind` would bind the boot-installed idle TCB, overwrite its
priority with the SchedContext's and re-bucket it, letting a high-priority
SchedContext make idle outrank ordinary runnable threads and starve them.
No idle capability is needed for that; the name alone sufficed.

This validator is the one lift point every raw thread-id operand passes
through, so the refusal is placed here rather than in the arm — the arm-level
fix would be an enumeration, and the next raw operand would miss it.  The
capability-derived call sites (`.tcbSuspend`, `.tcbResume`, the priority
arms, which pass `cap.target`'s object id) can never see an idle id anyway,
since the chokepoint refused their capability first; refusing again costs
them nothing and holds if that order ever changes.  The idle threads are the
kernel's own scheduling reserve — no user operand may name one
(`validateThreadIdArg_ok_not_reserved`).

**`v0.35.204`: the bind takes no raw thread operand any more.**  The round-11
narrative above describes `.schedContextBind` as it was.  Its operand is a TCB
capability address now (`SchedContextBindArgs.tcbCPtr`, extra capability 0 since
WS-SX SX6.4), resolved through the
caller's own CSpace by `resolveSchedContextBindThread`, so the idle TCB is
unreachable through the bind because the chokepoint refuses the *capability*
(`resolveSchedContextBindThread_refuses_idle_capability`); the resolver runs
the thread that capability names through this validator for the promotion to
`ValidThreadId`, with the idle refusal kept as the same defence in depth the
capability-derived arms get.  This is still the one lift point for every bare
thread id — the caller's own, which the priority arms pass through it, and any
operand a future arm reads out of a message register. -/
@[inline] def validateThreadIdArg (tid : SeLe4n.ThreadId) :
    Except KernelError SeLe4n.ValidThreadId :=
  if SeLe4n.Kernel.isIdleThreadId tid then .error (.invalidArgument 0)
  else
    match tid.toValid? with
    | none => .error (.invalidArgument 0)
    | some v => .ok v

/-- **PR #889 review round 11**: a validated raw thread operand is never a
reserved idle thread — the guarantee `syscallResolveCap_ok_not_reserved` gives
for capability targets, for the operands that arrive as bare numbers. -/
theorem validateThreadIdArg_ok_not_reserved (tid : SeLe4n.ThreadId)
    (vtid : SeLe4n.ValidThreadId) (h : validateThreadIdArg tid = .ok vtid) :
    SeLe4n.Kernel.isIdleThreadId tid = false := by
  unfold validateThreadIdArg at h
  split at h
  · exact absurd h (by simp)
  · rename_i hIdle
    simpa using hIdle

/-- **PR #889 review round 11**: and the refusal is `.invalidArgument` — the
answer an out-of-range id gives, so it discloses nothing about the
reservation. -/
theorem validateThreadIdArg_idle_refused (tid : SeLe4n.ThreadId)
    (h : SeLe4n.Kernel.isIdleThreadId tid = true) :
    validateThreadIdArg tid = .error (.invalidArgument 0) := by
  unfold validateThreadIdArg
  simp [h]

/-- **WS-LS LS2.3**: a validated thread operand is the one `ThreadId.toValid?`
promotes — what ties an arm's `ValidThreadId` to the footprint resolver's,
which promotes the same raw id through the same function. -/
theorem validateThreadIdArg_ok_toValid? (tid : SeLe4n.ThreadId)
    (vtid : SeLe4n.ValidThreadId) (h : validateThreadIdArg tid = .ok vtid) :
    tid.toValid? = some vtid := by
  unfold validateThreadIdArg at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · rename_i hV
      rw [hV]
      injection h with h
      rw [h]

/-- **WS-SX SX6.4 (D11): the priority authority** — seL4's `authCap`
(`decodeSetPriority` / `decodeSetMCPriority`, `tcb.c:1217`): the capability in
the slot the caller's extra capability 0 resolved to must be a thread
capability, else `seL4_InvalidCapability` with cap number 1; the thread it names
is the authority whose maximum controlled priority bounds the new value. -/
@[inline] def priorityAuthorityAt (st : SystemState) (cnode : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) : Except KernelError SeLe4n.ValidThreadId :=
  match st.lookupSlotCap { cnode := cnode, slot := slot } with
  | none => .error (.invalidCapability 1)
  | some authCap =>
    match authCap.target with
    | .object id =>
      match st.getTcb? (SeLe4n.ThreadId.ofNat id.toNat) with
      | none => .error (.invalidCapability 1)
      | some _ => validateThreadIdArg (SeLe4n.ThreadId.ofNat id.toNat)
    | _ => .error (.invalidCapability 1)

/-- **WS-SX SX6.4 (D11)**: the authority of a SetPriority or SetMCPriority —
the caller's extra capability 0 (`authCap?`, seL4's `excaprefs[0]`; none is
`truncatedMessage`), resolved as a slot through the caller's CSpace, then
`priorityAuthorityAt` on that slot. -/
@[inline] def resolvePriorityAuthority (st : SystemState) (callerTid : SeLe4n.ThreadId)
    (authCap? : Option SeLe4n.CPtr) : Except KernelError SeLe4n.ValidThreadId :=
  match authCap? with
  | none => .error .truncatedMessage
  | some cptr =>
    match st.getTcb? callerTid with
    | none => .error .objectNotFound
    | some callerTcb =>
      match lookupSlot callerTcb cptr st with
      | .error f => .error (.failedLookup false f)
      | .ok src => priorityAuthorityAt st src.cnode src.slot

/-- A resolved authority is a stored thread. -/
theorem resolvePriorityAuthority_ok_tcb {st : SystemState} {callerTid : SeLe4n.ThreadId}
    {authCap? : Option SeLe4n.CPtr} {vAuth : SeLe4n.ValidThreadId}
    (h : resolvePriorityAuthority st callerTid authCap? = .ok vAuth) :
    (st.getTcb? vAuth.val).isSome := by
  unfold resolvePriorityAuthority at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  unfold priorityAuthorityAt at h
  split at h; · cases h
  split at h
  · split at h
    · cases h
    · rename_i hT
      have hV := SeLe4n.ThreadId.toValid?_some_val_eq _ _
        (validateThreadIdArg_ok_toValid? _ _ h)
      rw [hV, hT]; rfl
  · cases h

/-- WS-AL AL7-A (cascades AK7-E): lift a raw `SchedContextId` to
`ValidSchedContextId` at the dispatch boundary. Mirrors
`validateThreadIdArg`; rejects `SchedContextId.sentinel`. -/
@[inline] private def validateSchedContextIdArg (scId : SeLe4n.SchedContextId) :
    Except KernelError SeLe4n.ValidSchedContextId :=
  match scId.toValid? with
  | none => .error (.invalidArgument 0)
  | some v => .ok v

/-- WS-AL AL8 (cascades AK7-E): lift a raw `ObjId` to `ValidObjId`.
Used by dispatch arms whose handlers operate on `ObjId` directly (e.g.,
`schedContextConfigure` which does `st.objects[scId]?` rather than
going through `SchedContextId.toObjId`). Rejects `ObjId.sentinel`. -/
@[inline] def validateObjIdArg (oid : SeLe4n.ObjId) :
    Except KernelError SeLe4n.ValidObjId :=
  if SeLe4n.Kernel.isIdleObjId oid then .error (.invalidArgument 0)
  else
    match oid.toValid? with
    | none => .error (.invalidArgument 0)
    | some v => .ok v

/-- **WS-LS LS2.3**: a validated object operand carries the raw id it was
promoted from — what ties an arm's `ValidObjId` to the footprint resolver's
raw operand. -/
theorem validateObjIdArg_ok_val (oid : SeLe4n.ObjId)
    (void : SeLe4n.ValidObjId) (h : validateObjIdArg oid = .ok void) :
    void.val = oid := by
  unfold validateObjIdArg at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · rename_i hV
      injection h with h
      rw [← h]
      unfold SeLe4n.ObjId.toValid? at hV
      split at hV
      · exact absurd hV (by simp)
      · injection hV with hV
        rw [← hV]

/-- **PR #889 review round 11**: the object-operand sibling of
`validateThreadIdArg_ok_not_reserved`.  Every live use of this validator today
lifts an id taken from a resolved capability's target, which the chokepoint
already refused; the refusal is here so that a *raw* object operand — the
shape `.schedContextBind`'s thread operand had — is covered on the day it is
written rather than on the day it is reviewed. -/
theorem validateObjIdArg_ok_not_reserved (oid : SeLe4n.ObjId)
    (void : SeLe4n.ValidObjId) (h : validateObjIdArg oid = .ok void) :
    SeLe4n.Kernel.isIdleObjId oid = false := by
  unfold validateObjIdArg at h
  split at h
  · exact absurd h (by simp)
  · rename_i hIdle
    simpa using hIdle

/-- **Capability binding for the VSpace syscalls** (PR #845 review, P1).

`syscallLookupCap` verifies only that the caller holds *a* capability carrying
the syscall's required right; it does not tie that capability to the operand the
syscall acts on.  For `.vspaceMap` / `.vspaceUnmap` / `.vspaceUnifyInstruction`
the operand is an **ASID the caller supplies in a message register**, so without
this binding a caller holding any writable object capability — its own TCB, say
— could name an arbitrary address space and have the kernel act on it.  That is
a confused deputy in the strict sense: authority would flow from a name the
caller chose rather than from the capability it holds, which is precisely what a
capability system exists to prevent.

The predicate is stated against **`resolveAsidRoot`** — the root the transition
itself will act on — rather than against the `asid` field of the capability's
own object.  The two differ when distinct roots carry the same ASID
(`storeObject` rebinds `asidTable` on a colliding install; that is the hazard
SM7.F.4 closed on the TLB side), and only the former is sound: checking the
capability's own field would let a holder of the *shadowed* root authorize an
operation that lands on the *bound* one.

Fails closed: an ASID that resolves to no root is authorized by no capability,
so an unbound ASID is rejected here rather than deeper in the transition.  That
also removes an ASID-existence oracle from the unauthorized path. -/
def vspaceCapAuthorizesAsid (cap : Capability) (asid : SeLe4n.ASID)
    (st : SystemState) : Bool :=
  match cap.target, Architecture.resolveAsidRoot st asid with
  | .object rid, some (rootId, _) => rid == rootId
  | _, _ => false

/-- The binding holds exactly when the capability names the VSpace root that
`resolveAsidRoot` yields for the operand ASID. -/
theorem vspaceCapAuthorizesAsid_iff (cap : Capability) (asid : SeLe4n.ASID)
    (st : SystemState) :
    vspaceCapAuthorizesAsid cap asid st = true ↔
      ∃ rid root, cap.target = .object rid ∧
        Architecture.resolveAsidRoot st asid = some (rid, root) := by
  unfold vspaceCapAuthorizesAsid
  cases hcap : cap.target <;>
    cases hres : Architecture.resolveAsidRoot st asid <;>
    simp_all
  rename_i rid pair
  obtain ⟨rootId, root⟩ := pair
  constructor
  · rintro rfl; exact ⟨root, rfl⟩
  · rintro ⟨_, h⟩; exact (Prod.mk.injEq .. ▸ h).1.symm

/-- **Fail-closed**: a capability naming a *different* object than the operand
ASID's root authorizes nothing.  This is the regression statement for the
confused-deputy defect — before the binding, a writable capability to any
object at all (an attacker's own TCB) passed the gate. -/
theorem vspaceCapAuthorizesAsid_false_of_ne {cap : Capability}
    {asid : SeLe4n.ASID} {st : SystemState} {rid rootId : SeLe4n.ObjId} {root : VSpaceRoot}
    (hcap : cap.target = .object rid)
    (hres : Architecture.resolveAsidRoot st asid = some (rootId, root))
    (hne : rid ≠ rootId) :
    vspaceCapAuthorizesAsid cap asid st = false := by
  simp [vspaceCapAuthorizesAsid, hcap, hres, hne]

/-- **Fail-closed**: an unbound ASID is authorized by no capability. -/
theorem vspaceCapAuthorizesAsid_false_of_unbound {cap : Capability}
    {asid : SeLe4n.ASID} {st : SystemState}
    (hres : Architecture.resolveAsidRoot st asid = none) :
    vspaceCapAuthorizesAsid cap asid st = false := by
  unfold vspaceCapAuthorizesAsid
  rw [hres]
  cases cap.target <;> rfl

/-- A non-object capability authorizes no address space, whatever the ASID. -/
theorem vspaceCapAuthorizesAsid_false_of_not_object {cap : Capability}
    {asid : SeLe4n.ASID} {st : SystemState}
    (hcap : ∀ rid, cap.target ≠ .object rid) :
    vspaceCapAuthorizesAsid cap asid st = false := by
  unfold vspaceCapAuthorizesAsid
  cases hc : cap.target
  case object rid => exact absurd hc (hcap rid)
  all_goals cases Architecture.resolveAsidRoot st asid <;> rfl

/-! ### Argument-capability numbers

seL4 numbers the capability a refusal names (`invalidCapNumber`): `0` for the
invoked capability and `i + 1` for argument capability `i`.  Each operation's
argument capabilities, in the current word layout's order, are numbered here,
once (an operation below this module numbers its own: `pageTableMapRootCapNumber`,
`irqHandlerNotificationCapNumber`, the `.tcbSetSpace` fault endpoint's
`setSpaceFaultHandlerCapNumber`); the
specification's resolver and its compiled continuation form both read the
number, so the two cannot answer a refusal with different numbers.  A
resolution failure of the argument (an empty or reserved slot; a lookup fault
stays seL4's `failedLookup`) and an argument capability of the wrong kind
are refused `invalidCapability` with its number (`KernelError.forArgumentCap`);
a missing right stays `illegalAuthority`. -/

/-- The context a `.schedContextConfigure` names as extra capability 0: its argument
capability `0` (seL4's `decodeSchedControl_ConfigureFlags` answers a target
that is no scheduling context `invalidCapNumber = 1`). -/
def configureContextCapNumber : UInt64 := 1

/-- The thread a `.schedContextBind` names as extra capability 0: its argument
capability `0`
(seL4's `decodeSchedContext_Bind`, `invalidCapNumber = 1`). -/
def bindThreadCapNumber : UInt64 := 1

/-- The frame a `.vspaceMap` maps: the invoked capability, number `0`
(WS-SX SX6.3, D6: `seL4_ARM_Page_Map` is an invocation of the frame
capability). -/
def vspaceMapFrameCapNumber : UInt64 := 0

/-- The address space a `.vspaceMap` maps into, extra capability 0: its
argument capability `0` (seL4's `decodeARMFrameInvocation` answers a root that
is not a valid native root, or not the one its ASID names, and a remap whose
recorded ASID is another's, `invalidCapNumber = 1`). -/
def pageMapVSpaceCapNumber : UInt64 := 1

/-- **seL4's `decodeBindNotification` on extra capability 0** (`tcb.c`): the
notification a `.tcbBindNotification` binds.  A lookup that fails answers its
own lookup fault (seL4's `lookupExtraCaps`, before the decode).  The slot it
names must hold a notification capability — an empty slot, a capability to a
kernel-reserved object or one to any other kind is `seL4_IllegalOperation`
(`.illegalState`, "Notification is invalid") — and that capability must carry
`CanReceive` (`.read`; without it `seL4_IllegalOperation` too, "Insufficient
access rights").  The type is checked before the right, seL4's order.  The
resolution reads the state and changes nothing. -/
def resolveBindNotificationCap (gate : SyscallGate) (st : SystemState) :
    Except KernelError SeLe4n.ObjId :=
  match gate.lookupSlot st with
  | .error f => .error (.failedLookup false f)
  | .ok ref =>
    match SystemState.lookupSlotCap st ref with
    | none => .error .illegalState
    | some ntfnCap =>
      if SeLe4n.Kernel.capTargetsReservedKernelObject ntfnCap then .error .illegalState
      else match ntfnCap.target with
        | .object notifId =>
          match st.getNotification? notifId with
          | none => .error .illegalState
          | some _ => if ntfnCap.hasRight .read then .ok notifId else .error .illegalState
        | _ => .error .illegalState

/-- **WS-SX SX6.4: the thread a `.schedContextBind` binds is extra capability
0** — seL4-MCS's `decodeSchedContext_Bind` reads `excaprefs[0]` and refuses a
message that names none `seL4_TruncatedMessage`; no message word carries it. -/
@[inline] def schedContextBindArgsOf (st : SystemState) (tid : SeLe4n.ThreadId) (xc : Nat) :
    Except KernelError SchedContextBindArgs :=
  match callerExtraCapAddr? st tid xc 0 with
  | none => .error .truncatedMessage
  | some cptr => .ok { tcbCPtr := cptr }

/-- **WS-SX SX6.4: the notification a `.tcbBindNotification` binds is extra
capability 0** — seL4's `decodeBindNotification` reads `excaprefs[0]` and
refuses a message that names none `seL4_TruncatedMessage`. -/
@[inline] def tcbBindNotificationArgsOf (st : SystemState) (tid : SeLe4n.ThreadId) (xc : Nat) :
    Except KernelError TcbBindNotificationArgs :=
  match callerExtraCapAddr? st tid xc 0 with
  | none => .error .truncatedMessage
  | some cptr => .ok { notificationCPtr := cptr }

/-- **WS-SX SX6.4: the notification an `.irqHandlerSetNotification` installs is
extra capability 0** — seL4's `decodeIRQHandlerInvocation` reads
`excaprefs[0]` and refuses a message that names none `seL4_TruncatedMessage`. -/
@[inline] def irqHandlerSetNotificationArgsOf (st : SystemState) (tid : SeLe4n.ThreadId)
    (xc : Nat) : Except KernelError IrqHandlerSetNotificationArgs :=
  match callerExtraCapAddr? st tid xc 0 with
  | none => .error .truncatedMessage
  | some cptr => .ok { notificationCPtr := cptr }

/-- **`v0.35.204`: the thread a `.schedContextBind` binds is a CAPABILITY the
caller holds, resolved through the caller's own CSpace — never a raw thread id.**

Until this version the arm read MR0 as a bare `ThreadId`
(`SchedContextBindArgs.threadId`), validated it against the reserved idle range
and the sentinel, and bound whatever thread it named.  A holder of an ordinary
SchedContext capability could therefore bind that context to any unbound thread
in the same domain — and `schedContextBind` then writes `sc.priority` into that
thread's own base priority (Z5-G3) and, since WS-RR RR8.12 Cut B2, places a
parked thread on a run queue: an integrity write on a thread the caller holds no
authority over, composable with the registered CB0.3 gap (a SchedContext's
priority and domain are set under its own write right).  seL4-MCS's
`seL4_SchedContext_Bind` takes the TCB as a capability, and this tree had already
refused the same shape one arm over: `.tcbBindNotification` resolves its
notification through a capability *"not a raw ObjId — a TCB-cap holder must also
hold a notification capability to redirect that notification's signals"*.  The
rule was applied at one site and not at its sibling; this is the sibling.

The operand is `SchedContextBindArgs.tcbCPtr` now — extra capability 0 since
WS-SX SX6.4 (`schedContextBindArgsOf`, seL4-MCS's `excaprefs[0]`) — resolved
exactly as that arm resolves its notification: `syscallLookupCap` on a gate at the caller's CSpace root and
depth, requiring `.write` — so the reserved-idle refusal is the chokepoint's own
(`syscallResolveCap_ok_not_reserved`) rather than a second lift-point check — and
the resolved capability must target a **TCB** the store holds (a capability to any
other kind of object is `.invalidCapability`).  `validateThreadIdArg` still promotes the id, so the
sentinel is refused where every raw operand is and `schedContextBind`'s
`ValidThreadId` signature is met without a second proof.

**One resolver, two askers.**  The live arm (`dispatchCapabilityOnly`) and the
scheduler-domain operand builder (`abiEntryLockOperands`) both read this
definition, so the thread the footprint declares a run-queue lock for and the
thread the transition binds cannot be two readings of one register.
`resolveSchedContextBindThread_ok_authorised` is the fact the arm rests on, stated
so a revert to a raw operand has to break a proof rather than a review. -/
def resolveSchedContextBindThread (callerTid : SeLe4n.ThreadId)
    (args? : Except KernelError SchedContextBindArgs) (st : SystemState) :
    Except KernelError SeLe4n.ValidThreadId :=
  match args? with
  | .error e => .error e
  | .ok args =>
    match st.getTcb? callerTid with
    | none => .error .objectNotFound
    | some callerTcb =>
      let tcbGate : SyscallGate := {
        callerId      := callerTid
        cspaceRootCap := callerTcb.spaceCells[0]
        capAddr       := args.tcbCPtr
        requiredRight := .write
      }
      match syscallLookupArgumentCap bindThreadCapNumber tcbGate st with
      | .error e => .error e
      | .ok (tcbCap, _) =>
        match tcbCap.target with
        | .object tcbObjId =>
          match st.getTcb? (SeLe4n.ThreadId.ofNat tcbObjId.toNat) with
          | none => .error (.invalidCapability bindThreadCapNumber)
          | some _ => validateThreadIdArg (SeLe4n.ThreadId.ofNat tcbObjId.toNat)
        | _ => .error (.invalidCapability bindThreadCapNumber)

/-- **`v0.35.204` (the authority fact)**: a thread the resolver answers is one
the caller holds a **writable capability** to, found at the operand's address
(extra capability 0) in the caller's own CSpace, and it is a TCB the store holds.  The read-only lookup
returns the state it was given (`syscallLookupCap_preserves_state`), so the
capability is exhibited at `st` itself. -/
theorem resolveSchedContextBindThread_ok_authorised
    (callerTid : SeLe4n.ThreadId) (args? : Except KernelError SchedContextBindArgs)
    (st : SystemState)
    (v : SeLe4n.ValidThreadId)
    (h : resolveSchedContextBindThread callerTid args? st = .ok v) :
    ∃ (args : SchedContextBindArgs) (callerTcb : TCB)
      (tcbCap : Capability),
      args? = .ok args ∧
      st.getTcb? callerTid = some callerTcb ∧
      syscallLookupCap
        { callerId := callerTid, cspaceRootCap := callerTcb.spaceCells[0],
          capAddr := args.tcbCPtr,
          requiredRight := .write } st = .ok (tcbCap, st) ∧
      tcbCap.hasRight .write = true ∧
      tcbCap.target = .object v.val.toObjId ∧
      (∃ tcb, st.getTcb? v.val = some tcb) := by
  unfold resolveSchedContextBindThread syscallLookupArgumentCap at h
  cases hArgs : args? with
  | error e => rw [hArgs] at h; cases h
  | ok args =>
    rw [hArgs] at h
    simp only at h
    cases hCaller : st.getTcb? callerTid with
    | none => rw [hCaller] at h; cases h
    | some callerTcb =>
      rw [hCaller] at h
      simp only at h
      cases hLk : syscallLookupCap
          { callerId := callerTid, cspaceRootCap := callerTcb.spaceCells[0],
            capAddr := args.tcbCPtr,
            requiredRight := .write } st with
      | error e => rw [hLk] at h; cases h
      | ok pair =>
        obtain ⟨tcbCap, s'⟩ := pair
        rw [hLk] at h
        simp only at h
        obtain ⟨_, _, _, hRight, hSt⟩ :=
          syscallLookupCap_implies_capability_held _ st tcbCap s' hLk
        rw [hSt] at hLk
        cases hTgt : tcbCap.target
        case object tcbObjId =>
          rw [hTgt] at h
          simp only at h
          cases hTcb : st.getTcb? (SeLe4n.ThreadId.ofNat tcbObjId.toNat) with
          | none => rw [hTcb] at h; cases h
          | some tcb =>
            rw [hTcb] at h
            simp only at h
            have hVal : v.val = SeLe4n.ThreadId.ofNat tcbObjId.toNat := by
              unfold validateThreadIdArg at h
              split at h
              · cases h
              · split at h
                · cases h
                · rename_i v' hV
                  have hvv : v' = v := Except.ok.inj h
                  subst hvv
                  exact SeLe4n.ThreadId.toValid?_some_val_eq _ v' hV
            -- `cases h : e` rewrites `e` in the goal, so the conjuncts the
            -- scrutinees appear in are closed by `rfl` where they were
            -- rewritten and by the hypothesis where they were not.
            refine ⟨args, callerTcb, tcbCap,
              by first | exact hArgs | rfl,
              by first | exact hCaller | rfl,
              by first | exact hLk | rw [hSt],
              hRight, ?_, ⟨tcb, by rw [hVal]; exact hTcb⟩⟩
            rw [hVal]
            first
              | exact hTgt
              | exact congrArg CapTarget.object rfl
        all_goals (rw [hTgt] at h; cases h)

/-- **seL4-MCS's `decodeSchedContext_Bind` on a notification capability**: the
notification a `.schedContextBind` binds when its extra capability 0 is a
notification capability, as a code — `0` when it is not one, the
notification's id plus one when it is.

The capability is resolved on the gate `resolveSchedContextBindThread` resolves
it on (the caller's own CSpace, extra capability 0, `.write`), so the two
readings of one operand are one lookup: a code of `0` leaves every refusal —
the truncated message, the lookup fault, the missing right, the capability to
an object of another kind — to the thread resolver, which answers them as it
always has.  A nonzero code is a capability the caller holds, through the
chokepoint's own reserved-object refusal, to a notification the store holds.
The resolution reads the state and changes nothing, and builds no value but a
number. -/
def resolveSchedContextBindNotificationCode (callerTid : SeLe4n.ThreadId)
    (args? : Except KernelError SchedContextBindArgs) (st : SystemState) : Nat :=
  match args? with
  | .error _ => 0
  | .ok args =>
    match st.getTcb? callerTid with
    | none => 0
    | some callerTcb =>
      let gate : SyscallGate := {
        callerId      := callerTid
        cspaceRootCap := callerTcb.spaceCells[0]
        capAddr       := args.tcbCPtr
        requiredRight := .write
      }
      match syscallLookupArgumentCap bindThreadCapNumber gate st with
      | .error _ => 0
      | .ok (c, _) =>
        match c.target with
        | .object o =>
          match st.getNotification? o with
          | some _ => o.val + 1
          | none => 0
        | _ => 0

/-- **The two readings of extra capability 0 are exclusive**: a capability the
thread resolver answers is a TCB capability, so it is no notification's. -/
theorem resolveSchedContextBindNotificationCode_eq_zero_of_thread
    {callerTid : SeLe4n.ThreadId} {args? : Except KernelError SchedContextBindArgs}
    {st : SystemState} {v : SeLe4n.ValidThreadId}
    (h : resolveSchedContextBindThread callerTid args? st = .ok v) :
    resolveSchedContextBindNotificationCode callerTid args? st = 0 := by
  obtain ⟨args, callerTcb, tcbCap, hA, hC, hLk, -, hT, tcb, hTcb⟩ :=
    resolveSchedContextBindThread_ok_authorised callerTid args? st v h
  have hN : st.getNotification? v.val.toObjId = none := by
    cases e : st.getNotification? v.val.toObjId with
    | none => rfl
    | some n =>
      have a := (SystemState.getNotification?_eq_some_iff _ _ _).mp e
      have b := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTcb
      rw [a] at b; cases b
  unfold resolveSchedContextBindNotificationCode syscallLookupArgumentCap
  simp only [hA, hC, hLk, hT, hN]

/-- **WS-ZA ZA6.4**: the scheduling context a configure through core `core`'s
scheduling control names: seL4-MCS's `decodeSchedControl_ConfigureFlags` takes the
context as extra capability 0 (WS-SX SX6.4), the address `scCPtr` the arm reads
from the caller's IPC buffer, looked up in the caller's own CSpace as
`lookupExtraCaps` looks it up: the slot, with **no right asked of its
capability** — seL4 checks only that the capability names a scheduling context
(`cap_get_capType(targetCap) != cap_sched_context_cap`).  The dispatch's gate
(`syscallInvokeTyped`, seL4's `handleInvocation`) has looked every extra
capability up before this arm runs, so an extra capability that does not look
up is refused there, as the capability fault the entry raises, before the
message length is read.  The checks here: the message length `len`
(`decodeSchedControl_ConfigureFlags`'s `TruncatedMessage` below
`truncationMinimum .schedContextConfigure` words, seL4's
`TIME_ARG_SIZE * 2 + 3`; the arm refuses a short invocation before reading its
arguments, `dispatchWithCapChecked_eq_truncated`); then the lookup, which the
gate has made succeed on every dispatched state and which is repeated here for
the resolver's second asker; then the capability's kind: an empty slot, a
capability naming a kernel-reserved object (`syscallResolveCap`'s chokepoint)
or one naming anything but a scheduling context the store holds is
`.invalidCapability configureContextCapNumber`.  The words' range checks,
the extra refills among them, come after this resolution
(`decodeSchedContextConfigureArgsChecked`).  The control must name a core the
kernel runs (`.invalidCapability` otherwise; boot installs a control for each
core it runs), and `validateObjIdArg` promotes the id.  A context homed on another core
is not refused: the configure moves it to the control's core with its thread, as
seL4 does (`SchedContextOps.schedControlConfigure`).  Every check reads the state
handed in; nothing is written.

**One resolver, two askers.**  The live arm (`dispatchCapabilityOnly`) and the
scheduler-domain operand builder (`abiEntryLockOperands`) both read this
definition, so the context the footprint declares and the context the transition
configures are one reading of one extra-capability address. -/
def resolveSchedControlConfigureTarget (callerTid : SeLe4n.ThreadId) (core : Nat)
    (scCPtr : SeLe4n.CPtr) (len : Nat) (st : SystemState) :
    Except KernelError SeLe4n.ValidObjId :=
  if len < truncationMinimum .schedContextConfigure then .error .truncatedMessage else
  match st.getTcb? callerTid with
  | none => .error .objectNotFound
  | some callerTcb =>
    match lookupSlot callerTcb scCPtr st with
    | .error f => .error (.failedLookup false f)
    | .ok ref =>
      match SystemState.lookupSlotCap st ref with
      | none => .error (.invalidCapability configureContextCapNumber)
      | some scCap =>
        if SeLe4n.Kernel.capTargetsReservedKernelObject scCap then
          .error (.invalidCapability configureContextCapNumber)
        else
        match scCap.target with
        | .object scObjId =>
          match st.getSchedContext? (SchedContextId.ofObjId scObjId) with
          | none => .error (.invalidCapability configureContextCapNumber)
          | some _ =>
            if core < SeLe4n.Kernel.Concurrency.numCores then validateObjIdArg scObjId
            else .error (.invalidCapability 0)
        | _ => .error (.invalidCapability configureContextCapNumber)

/-- **WS-ZA ZA6.4 (the authority fact)**: a context the resolver answers is one the
caller holds a capability to, found at `scCPtr` in the caller's own CSpace, of
the scheduling-context kind (no right is asked of it, as seL4 asks none); the
store holds it as a scheduling context, and the control names a core the kernel
runs. -/
theorem resolveSchedControlConfigureTarget_ok_authorised
    (callerTid : SeLe4n.ThreadId) (core : Nat) (scCPtr : SeLe4n.CPtr) (len : Nat)
    (st : SystemState) (v : SeLe4n.ValidObjId)
    (h : resolveSchedControlConfigureTarget callerTid core scCPtr len st = .ok v) :
    ∃ (callerTcb : TCB) (ref : CSpaceAddr) (scCap : Capability) (sc : SchedContext),
      st.getTcb? callerTid = some callerTcb ∧
      lookupSlot callerTcb scCPtr st = .ok ref ∧
      SystemState.lookupSlotCap st ref = some scCap ∧
      scCap.target = .object v.val ∧
      st.getSchedContext? (SchedContextId.ofObjId v.val) = some sc ∧
      core < SeLe4n.Kernel.Concurrency.numCores := by
  unfold resolveSchedControlConfigureTarget at h
  by_cases hLen : len < truncationMinimum .schedContextConfigure
  · rw [if_pos hLen] at h; cases h
  rw [if_neg hLen] at h
  cases hCaller : st.getTcb? callerTid with
  | none => rw [hCaller] at h; cases h
  | some callerTcb =>
    rw [hCaller] at h
    simp only at h
    cases hLk : lookupSlot callerTcb scCPtr st with
    | error f => rw [hLk] at h; cases h
    | ok ref =>
      rw [hLk] at h
      simp only at h
      cases hCap : SystemState.lookupSlotCap st ref with
      | none => rw [hCap] at h; cases h
      | some scCap =>
        rw [hCap] at h
        simp only at h
        by_cases hRes : SeLe4n.Kernel.capTargetsReservedKernelObject scCap = true
        · rw [if_pos hRes] at h; cases h
        rw [if_neg hRes] at h
        cases hTgt : scCap.target with
        | object scObjId =>
          rw [hTgt] at h
          simp only at h
          cases hSc : st.getSchedContext? (SchedContextId.ofObjId scObjId) with
          | none => rw [hSc] at h; cases h
          | some sc =>
            rw [hSc] at h
            simp only at h
            by_cases hCov : core < SeLe4n.Kernel.Concurrency.numCores
            · rw [if_pos hCov] at h
              have hVal : v.val = scObjId := validateObjIdArg_ok_val _ _ h
              subst hVal
              exact ⟨callerTcb, ref, scCap, sc, rfl, hLk, hCap, hTgt, hSc, hCov⟩
            · rw [if_neg hCov] at h; cases h
        | _ => rw [hTgt] at h; cases h

/-- A configure's resolution reads the message length only through the
truncation test: every length at or past the configure's minimum resolves as the
minimum does. -/
theorem resolveSchedControlConfigureTarget_len_of_le (callerTid : SeLe4n.ThreadId)
    (core : Nat) (scCPtr : SeLe4n.CPtr) (st : SystemState) {len : Nat}
    (h : truncationMinimum .schedContextConfigure ≤ len) :
    resolveSchedControlConfigureTarget callerTid core scCPtr len st =
      resolveSchedControlConfigureTarget callerTid core scCPtr
        (truncationMinimum .schedContextConfigure) st := by
  unfold resolveSchedControlConfigureTarget
  simp only [Nat.not_lt.mpr h, Nat.lt_irrefl, ↓reduceIte]

/-- A configure shorter than its words is refused `TruncatedMessage` before its
context is resolved. -/
theorem resolveSchedControlConfigureTarget_short (callerTid : SeLe4n.ThreadId)
    (core : Nat) (scCPtr : SeLe4n.CPtr) (st : SystemState) {len : Nat}
    (h : len < truncationMinimum .schedContextConfigure) :
    resolveSchedControlConfigureTarget callerTid core scCPtr len st = .error .truncatedMessage := by
  unfold resolveSchedControlConfigureTarget
  simp only [h, ↓reduceIte]

/-- **`v0.35.204`**: a TCB capability naming a reserved idle object is refused at
the capability chokepoint — `syscallResolveCap`'s own refusal, reached through
the resolver's lookup — with `.invalidCapability`, the answer an empty slot gives.
The successor of `dispatchCapabilityOnly_schedContextBind_idle_operand_refused`
(retired with the raw operand it was about): the idle threads are the kernel's
own scheduling reserve, and no capability a thread can hold names one. -/
theorem resolveSchedContextBindThread_refuses_idle_capability
    (callerTid : SeLe4n.ThreadId) (args? : Except KernelError SchedContextBindArgs)
    (st : SystemState)
    (args : SchedContextBindArgs) (callerTcb : TCB) (ref : SlotRef)
    (idleCap : Capability)
    (hArgs : args? = .ok args)
    (hCaller : st.getTcb? callerTid = some callerTcb)
    (hRef : lookupSlot callerTcb (args.tcbCPtr) st = .ok ref)
    (hSlot : SystemState.lookupSlotCap st ref = some idleCap)
    (hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject idleCap = true) :
    resolveSchedContextBindThread callerTid args? st =
      .error (.invalidCapability bindThreadCapNumber) := by
  unfold resolveSchedContextBindThread
  rw [hArgs]
  simp only
  rw [hCaller]
  simp only
  unfold syscallLookupArgumentCap syscallLookupCap syscallResolveCap
  simp only [SyscallGate.lookupSlot_mk, hRef, hSlot, hIdle, if_true, KernelError.forArgumentCap]

/-- **WS-BP BP7.1 (`v0.36.4`): the frame a `.vspaceMap` installs is one the
caller holds a capability to, resolved through the caller's own CSpace — never
a raw physical address.**

Until this version MR2 was a physical address, checked only for range and
alignment: a holder of any writable VSpace capability could map any physical
memory into that address space — the kernel image, the boot tables, another
domain's pages.  seL4's `seL4_ARM_Page_Map` is an invocation *of a frame
capability*; the address is the frame object's own, and holding the capability
is the authority over the memory.  This is that resolution, spelled exactly as
`resolveSchedContextBindThread` resolves its extra capability: `syscallLookupCap`
on a gate at the caller's CSpace root and depth, requiring `.read` — every
mapping grants at least read access to the page, so a capability without it
authorises none — and the resolved capability must name a **frame** the store
holds (any other target is `.invalidCapability`, the answer an empty slot
gives).  The reserved-idle refusal is the chokepoint's own
(`syscallResolveCap_ok_not_reserved`).  `resolveVSpaceMapFrame_ok_authorised`
is the fact the arm rests on. -/
def resolveVSpaceMapFrame (callerTid : SeLe4n.ThreadId) (args : VSpaceMapArgs)
    (st : SystemState) : Except KernelError (CSpaceAddr × Capability × FrameObject) :=
  match st.getTcb? callerTid with
  | none => .error .objectNotFound
  | some callerTcb =>
    let frameGate : SyscallGate := {
      callerId      := callerTid
      cspaceRootCap := callerTcb.spaceCells[0]
      capAddr       := args.frame
      requiredRight := .read
    }
    match syscallLookupArgumentCap vspaceMapFrameCapNumber frameGate st with
    | .error e => .error e
    | .ok (frameCap, _) =>
      match frameCap.target with
      | .object frameObjId =>
        match st.getFrame? frameObjId with
        | none => .error (.invalidCapability vspaceMapFrameCapNumber)
        | some frame =>
          -- WS-BP BP7.1 (`v0.36.7`): the slot the capability sits in, which
          -- is where the mapping is recorded.  The same pure resolution the
          -- gate's lookup ran (`resolveVSpaceMapFrame_ok_slot`), so it names
          -- the slot the capability was read from.
          match lookupSlot callerTcb args.frame st with
          | .error f => .error ((KernelError.failedLookup false f).forArgumentCap vspaceMapFrameCapNumber)
          | .ok frameSlot => .ok (frameSlot, frameCap, frame)
      | _ => .error (.invalidCapability vspaceMapFrameCapNumber)

/-- **WS-BP BP7.1 (`v0.36.11`): the slot a capability address names in the
caller's own CSpace**, with the capability it holds and the object that
capability names — the one resolution of a capability the caller holds, which
`resolveCallerCapObject` answers from.  The shape `resolveVSpaceMapFrame` and
`resolveSchedContextBindThread` each spell inline: the slot resolved at the
caller's CSpace root capability (`lookupSlot`), its capability read, a
capability naming a kernel-reserved idle object refused as an empty slot is
(`syscallResolveCap`), the `right` asked for checked (`syscallLookupCap`'s
gate), and the capability must name an object.  Inlined, so a caller that
reads part of the answer builds no triple. -/
@[inline] def resolveCallerCapSlot (callerTid : SeLe4n.ThreadId) (addr : SeLe4n.CPtr)
    (right : AccessRight) (st : SystemState) :
    Except KernelError (CSpaceAddr × Capability × SeLe4n.ObjId) :=
  match st.getTcb? callerTid with
  | none => .error .objectNotFound
  | some callerTcb =>
    match lookupSlot callerTcb addr st with
    | .error f => .error (.failedLookup false f)
    | .ok ref =>
      match SystemState.lookupSlotCap st ref with
      | none => .error (.invalidCapability 0)
      | some cap =>
        if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability 0)
        else if cap.hasRight right then
          match cap.target with
          | .object oid => .ok (ref, cap, oid)
          | _ => .error (.invalidCapability 0)
        else .error .illegalAuthority

/-- What `resolveCallerCapSlot` answers is a slot of the caller's CSpace holding
a capability with the right asked for, naming the object returned. -/
theorem resolveCallerCapSlot_ok (callerTid : SeLe4n.ThreadId) (addr : SeLe4n.CPtr)
    (right : AccessRight) (st : SystemState) (ref : CSpaceAddr) (cap : Capability)
    (oid : SeLe4n.ObjId) (h : resolveCallerCapSlot callerTid addr right st = .ok (ref, cap, oid)) :
    ∃ (callerTcb : TCB),
      st.getTcb? callerTid = some callerTcb ∧
      lookupSlot callerTcb addr st = .ok ref ∧
      SystemState.lookupSlotCap st ref = some cap ∧
      cap.hasRight right = true ∧ cap.target = .object oid := by
  unfold resolveCallerCapSlot at h
  cases hCaller : st.getTcb? callerTid with
  | none => rw [hCaller] at h; cases h
  | some callerTcb =>
    rw [hCaller] at h
    simp only at h
    cases hRes : lookupSlot callerTcb addr st with
    | error e => rw [hRes] at h; cases h
    | ok ref' =>
      rw [hRes] at h
      simp only at h
      cases hL : SystemState.lookupSlotCap st ref' with
      | none => rw [hL] at h; cases h
      | some cap' =>
        rw [hL] at h
        simp only at h
        split at h
        · cases h
        · split at h
          · rename_i hR
            cases hT : cap'.target with
            | object o =>
              rw [hT] at h
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact ⟨callerTcb, rfl, hRes, hL, hR, hT⟩
            | _ => rw [hT] at h; cases h
          · cases h

/-- **A capability the caller holds, resolved through its own CSpace at a
message-register address** — `resolveCallerCapSlot`'s answer without the slot,
so the two cannot disagree on a resolution or a refusal.  Returned with the
capability, so a caller may ask for a second right beside the gate's. -/
def resolveCallerCapObject (callerTid : SeLe4n.ThreadId) (addr : SeLe4n.CPtr)
    (right : AccessRight) (st : SystemState) :
    Except KernelError (Capability × SeLe4n.ObjId) :=
  match resolveCallerCapSlot callerTid addr right st with
  | .error e => .error e
  | .ok (_, cap, oid) => .ok (cap, oid)

/-- What `resolveCallerCapObject` answers is a capability the caller holds in
its own CSpace, carrying the right asked for, naming the object returned. -/
theorem resolveCallerCapObject_ok (callerTid : SeLe4n.ThreadId) (addr : SeLe4n.CPtr)
    (right : AccessRight) (st : SystemState) (cap : Capability) (oid : SeLe4n.ObjId)
    (h : resolveCallerCapObject callerTid addr right st = .ok (cap, oid)) :
    ∃ (callerTcb : TCB) (ref : CSpaceAddr),
      st.getTcb? callerTid = some callerTcb ∧
      lookupSlot callerTcb addr st = .ok ref ∧
      SystemState.lookupSlotCap st ref = some cap ∧
      cap.hasRight right = true ∧ cap.target = .object oid := by
  unfold resolveCallerCapObject at h
  cases hS : resolveCallerCapSlot callerTid addr right st with
  | error e => rw [hS] at h; cases h
  | ok r =>
    obtain ⟨ref, cap', oid'⟩ := r
    rw [hS] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨callerTcb, hT, hRes, hL, hR, hTg⟩ :=
      resolveCallerCapSlot_ok callerTid addr right st ref cap' oid' hS
    exact ⟨callerTcb, ref, hT, hRes, hL, hR, hTg⟩

/-- **WS-BP BP7.1 (`v0.36.11`), WS-SX SX6.5: the three slots a `.tcbSetSpace`
copies from, resolved through the caller's own CSpace** — seL4-MCS's
`TCB_SetSpace` operands, at the addresses the message's extra capabilities give:
the CSpace root at `cnAddr` (extra capability 1), the VSpace root at `vrAddr`
(extra capability 2), the fault endpoint at `fhAddr` (extra capability 0).

In `decodeSetSpace`'s order: the CSpace root's slot must hold a capability to a
CNode whose root data word (`cspace_root_data`) fits it
(`cspaceRootSourceAdmitted`), or the call is refused `.illegalState` (seL4's
`updateCapData` null capability or wrong type, then `seL4_IllegalOperation`; an
empty slot is seL4's null capability, refused the same way); then the VSpace
root's slot must hold a capability to a VSpace root (`isValidVTableRoot`,
`.illegalState`); then the fault endpoint must be a valid handler
(`validFaultHandler`: an empty slot, or an endpoint capability with send and a
grant right, `faultHandlerSourceAdmitted`; anything else `invalidCapability
1`).  No right is asked of either root capability, as seL4 asks none
(its CNode and VSpace capabilities carry no rights): the copy installed in the
thread's slot keeps only the rights the source holds (`spaceCopyOf`), and the
installed capability is never invoked, so it reaches nothing the caller could
not already reach through the capability it named.  The operation checks every source again against the store, so a
resolver and an operation that disagreed would refuse rather than install.
The slots are returned, not the objects: the operation copies each slot's
capability into the thread's slot, derived from it. -/
def resolveSetSpaceAt (callerTid : SeLe4n.ThreadId) (cnAddr vrAddr fhAddr : SeLe4n.CPtr)
    (args : SeLe4n.Kernel.Architecture.SyscallArgDecode.SetSpaceArgs) (st : SystemState) :
    Except KernelError (CSpaceAddr × CSpaceAddr × CSpaceAddr) :=
  match st.getTcb? callerTid with
  | none => .error .objectNotFound
  | some callerTcb =>
    match lookupSlot callerTcb cnAddr st with
    | .error f => .error (.failedLookup false f)
    | .ok cnSrc =>
      if !cspaceRootSourceAdmitted st cnSrc args.cspaceRootData then .error .illegalState
      else
        match lookupSlot callerTcb vrAddr st with
        | .error f => .error (.failedLookup false f)
        | .ok vrSrc =>
          if !vspaceRootSourceAdmitted st vrSrc then .error .illegalState
          else
            match lookupSlot callerTcb fhAddr st with
            | .error f => .error (.failedLookup false f)
            | .ok fhSrc =>
              if faultHandlerSourceAdmitted st fhSrc then .ok (cnSrc, vrSrc, fhSrc)
              else .error (.invalidCapability setSpaceFaultHandlerCapNumber)

/-- **The `.tcbSetSpace` operands from the message**: the fault endpoint, CSpace
root and VSpace root are extra capabilities 0, 1 and 2 (seL4-MCS's
`decodeSetSpace` reads `current_extra_caps.excaprefs[0..2]`), and a message
naming fewer is `.truncatedMessage`, as seL4 refuses a null `excaprefs[i]` in
its length check; then `resolveSetSpaceAt`. -/
def resolveSetSpace (callerTid : SeLe4n.ThreadId) (xc : Nat)
    (args : SeLe4n.Kernel.Architecture.SyscallArgDecode.SetSpaceArgs) (st : SystemState) :
    Except KernelError (CSpaceAddr × CSpaceAddr × CSpaceAddr) :=
  match callerExtraCapAddr? st callerTid xc 0, callerExtraCapAddr? st callerTid xc 1,
      callerExtraCapAddr? st callerTid xc 2 with
  | some fhAddr, some cnAddr, some vrAddr => resolveSetSpaceAt callerTid cnAddr vrAddr fhAddr args st
  | _, _, _ => .error .truncatedMessage

/-- `resolveCallerCapSlot` in continuation form: the slot is resolved through
`lookupSlotK` and handed on as its CNode's and slot's words, so no gate, slot
reference or result triple is built (`resolveCallerCapSlotK_eq`); a failed
lookup reaches `onErr` as seL4's `FailedLookup` rebuilt from the walk's
words. -/
@[inline] def resolveCallerCapSlotK {α : Type} (callerTid : SeLe4n.ThreadId)
    (addr : SeLe4n.CPtr) (right : AccessRight) (st : SystemState)
    (onErr : KernelError → α)
    (onOk : SeLe4n.ObjId → SeLe4n.Slot → Capability → SeLe4n.ObjId → α) : α :=
  match st.getTcb? callerTid with
  | none => onErr .objectNotFound
  | some callerTcb =>
    lookupSlotK callerTcb addr st
      (fun t a b c => onErr (.failedLookup false (LookupFault.ofWords t a b c)))
      (fun cnode slot =>
        match SystemState.lookupSlotCap st { cnode := cnode, slot := slot } with
        | none => onErr (.invalidCapability 0)
        | some cap =>
          if SeLe4n.Kernel.capTargetsReservedKernelObject cap then onErr (.invalidCapability 0)
          else if cap.hasRight right then
            match cap.target with
            | .object oid => onOk cnode slot cap oid
            | _ => onErr (.invalidCapability 0)
          else onErr .illegalAuthority)

theorem resolveCallerCapSlotK_eq {α : Type} (callerTid : SeLe4n.ThreadId)
    (addr : SeLe4n.CPtr) (right : AccessRight) (st : SystemState)
    (onErr : KernelError → α)
    (onOk : SeLe4n.ObjId → SeLe4n.Slot → Capability → SeLe4n.ObjId → α) :
    resolveCallerCapSlotK callerTid addr right st onErr onOk =
      match resolveCallerCapSlot callerTid addr right st with
      | .error e => onErr e
      | .ok (ref, cap, oid) => onOk ref.cnode ref.slot cap oid := by
  unfold resolveCallerCapSlotK resolveCallerCapSlot
  cases st.getTcb? callerTid with
  | none => rfl
  | some callerTcb =>
    simp only []
    rw [lookupSlotK_eq]
    cases lookupSlot callerTcb addr st with
    | error f => simp only [LookupFault.ofWords_word]
    | ok ref =>
      obtain ⟨cnode, slot⟩ := ref
      simp only []
      cases SystemState.lookupSlotCap st { cnode := cnode, slot := slot } with
      | none => rfl
      | some cap =>
        simp only []
        by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
        · simp only [hIdle, ↓reduceIte]
        · by_cases hR : cap.hasRight right = true
          · simp only [hIdle, hR, Bool.false_eq_true, ↓reduceIte]
            cases cap.target <;> rfl
          · simp only [hIdle, hR, Bool.false_eq_true, ↓reduceIte]

/-- WS-ZA ZA5.2: `resolveCallerCapObject` in continuation form —
`resolveCallerCapSlotK` with the slot's words dropped, so the two continuation
forms share one resolution as their direct forms do; no gate, slot reference,
capability pair or result cell is built (`resolveCallerCapObjectK_eq`). -/
@[inline] def resolveCallerCapObjectK {α : Type} (callerTid : SeLe4n.ThreadId)
    (addr : SeLe4n.CPtr) (right : AccessRight) (st : SystemState)
    (onErr : KernelError → α) (onOk : Capability → SeLe4n.ObjId → α) : α :=
  resolveCallerCapSlotK callerTid addr right st onErr (fun _ _ cap oid => onOk cap oid)

theorem resolveCallerCapObjectK_eq {α : Type} (callerTid : SeLe4n.ThreadId)
    (addr : SeLe4n.CPtr) (right : AccessRight) (st : SystemState)
    (onErr : KernelError → α) (onOk : Capability → SeLe4n.ObjId → α) :
    resolveCallerCapObjectK callerTid addr right st onErr onOk =
      match resolveCallerCapObject callerTid addr right st with
      | .error e => onErr e
      | .ok (cap, oid) => onOk cap oid := by
  unfold resolveCallerCapObjectK resolveCallerCapObject
  rw [resolveCallerCapSlotK_eq]
  cases resolveCallerCapSlot callerTid addr right st with
  | error e => rfl
  | ok r => obtain ⟨_, _, _⟩ := r; rfl

/-- WS-SX SX6.7: the argument capability number a declassification's object
answers to — extra capability 0, numbered `1` as seL4 numbers an extra
capability's `invalidCapNumber`. -/
def declassifyTargetCapNumber : UInt64 := 1

/-- WS-SX SX6.7: the right a declassification asks of the object it releases
into.  The flow runs from the caller into the object, so the authority is the
**write** right on the object's capability: a read-only holder can observe the
object, it cannot make the kernel record that its own domain was downgraded into
the object's. -/
def declassifyTargetRight : AccessRight := .write

/-- **WS-SX SX6.7: the object a declassification releases into, extra
capability 0.**  `.declassify` and `.declassifySignal` are invocations of the
audit-trail capability, so no label selects an operation on an endpoint or a
notification; the object (for the signal, the notification) is the caller's
extra capability 0, resolved through the caller's own CSpace with
`declassifyTargetRight`.  A message naming no extra capability is
`.truncatedMessage`; an empty slot, a capability to a kernel-reserved object or
one naming no object is `invalidCapability 1`, a capability without the right
`.illegalAuthority`. -/
def resolveDeclassifyTarget (tid : SeLe4n.ThreadId) (xc : Nat) (st : SystemState) :
    Except KernelError (Capability × SeLe4n.ObjId) :=
  match callerExtraCapAddr? st tid xc 0 with
  | none => .error .truncatedMessage
  | some addr =>
    match resolveCallerCapObject tid addr declassifyTargetRight st with
    | .error e => .error (e.forArgumentCap declassifyTargetCapNumber)
    | .ok r => .ok r

/-- **WS-SX SX6.7: the notification a `.declassifySignal` signals**, extra
capability 0 (`resolveDeclassifyTarget`), which must name a notification
(`objectKindIs`; anything else is `invalidCapability 1`). -/
def resolveDeclassifySignalTarget (tid : SeLe4n.ThreadId) (xc : Nat) (st : SystemState) :
    Except KernelError (Capability × SeLe4n.ObjId) :=
  match resolveDeclassifyTarget tid xc st with
  | .error e => .error e
  | .ok (cap, oid) =>
    if objectKindIs st oid .notification then .ok (cap, oid)
    else .error (.invalidCapability declassifyTargetCapNumber)

/-- What `resolveDeclassifyTarget` answers is extra capability 0's capability,
as the taint planner reads it (`syscallOperandCap?`), naming the object
returned and carrying the right. -/
theorem resolveDeclassifyTarget_ok (tid : SeLe4n.ThreadId) (xc : Nat) (st : SystemState)
    (cap : Capability) (oid : SeLe4n.ObjId)
    (h : resolveDeclassifyTarget tid xc st = .ok (cap, oid)) :
    ∃ addr, callerExtraCapAddr? st tid xc 0 = some addr ∧
      syscallOperandCap? st tid addr = some cap ∧ cap.target = .object oid ∧
      cap.hasRight declassifyTargetRight = true := by
  unfold resolveDeclassifyTarget at h
  cases hA : callerExtraCapAddr? st tid xc 0 with
  | none => rw [hA] at h; cases h
  | some addr =>
    rw [hA] at h
    simp only at h
    cases hR : resolveCallerCapObject tid addr declassifyTargetRight st with
    | error e => rw [hR] at h; cases h
    | ok r =>
      rw [hR] at h
      cases h
      obtain ⟨callerTcb, ref, hT, hL, hC, hRt, hTg⟩ :=
        resolveCallerCapObject_ok tid addr declassifyTargetRight st cap oid hR
      exact ⟨addr, rfl, by simp only [syscallOperandCap?, hT, hL, hC], hTg, hRt⟩

/-- `resolveDeclassifyTarget` in continuation form, through
`resolveCallerCapObjectK`: no capability pair or result cell is built
(`resolveDeclassifyTargetK_eq`). -/
@[inline] def resolveDeclassifyTargetK {α : Type} (tid : SeLe4n.ThreadId) (xc : Nat)
    (st : SystemState) (onErr : KernelError → α) (onOk : Capability → SeLe4n.ObjId → α) : α :=
  match callerExtraCapAddr? st tid xc 0 with
  | none => onErr .truncatedMessage
  | some addr =>
    resolveCallerCapObjectK tid addr declassifyTargetRight st
      (KernelError.argumentCapRefusal declassifyTargetCapNumber onErr) onOk

theorem resolveDeclassifyTargetK_eq {α : Type} (tid : SeLe4n.ThreadId) (xc : Nat)
    (st : SystemState) (onErr : KernelError → α) (onOk : Capability → SeLe4n.ObjId → α) :
    resolveDeclassifyTargetK tid xc st onErr onOk =
      match resolveDeclassifyTarget tid xc st with
      | .error e => onErr e
      | .ok (cap, oid) => onOk cap oid := by
  unfold resolveDeclassifyTargetK resolveDeclassifyTarget
  cases callerExtraCapAddr? st tid xc 0 with
  | none => rfl
  | some addr =>
    simp only []
    rw [resolveCallerCapObjectK_eq]
    cases resolveCallerCapObject tid addr declassifyTargetRight st with
    | error e => rfl
    | ok r => obtain ⟨_, _⟩ := r; rfl

/-- `resolveDeclassifySignalTarget` in continuation form
(`resolveDeclassifySignalTargetK_eq`). -/
@[inline] def resolveDeclassifySignalTargetK {α : Type} (tid : SeLe4n.ThreadId) (xc : Nat)
    (st : SystemState) (onErr : KernelError → α) (onOk : Capability → SeLe4n.ObjId → α) : α :=
  resolveDeclassifyTargetK tid xc st onErr fun cap oid =>
    if objectKindIs st oid .notification then onOk cap oid
    else onErr (.invalidCapability declassifyTargetCapNumber)

theorem resolveDeclassifySignalTargetK_eq {α : Type} (tid : SeLe4n.ThreadId) (xc : Nat)
    (st : SystemState) (onErr : KernelError → α) (onOk : Capability → SeLe4n.ObjId → α) :
    resolveDeclassifySignalTargetK tid xc st onErr onOk =
      match resolveDeclassifySignalTarget tid xc st with
      | .error e => onErr e
      | .ok (cap, oid) => onOk cap oid := by
  unfold resolveDeclassifySignalTargetK resolveDeclassifySignalTarget
  rw [resolveDeclassifyTargetK_eq]
  cases resolveDeclassifyTarget tid xc st with
  | error e => rfl
  | ok r =>
    obtain ⟨cap, oid⟩ := r
    simp only []
    split <;> rfl

/-- WS-SX SX6.7: the argument capability number a service-registry
invocation's endpoint answers to — extra capability 0, numbered `1` as seL4
numbers an extra capability's `invalidCapNumber`. -/
def serviceEndpointCapNumber : UInt64 := 1

/-- **WS-SX SX6.7: the endpoint a service-registry invocation names, extra
capability 0.**  `serviceRegister`, `serviceRevoke` and `serviceQuery` are
invocations of the service-registry capability, so no label selects an
operation on an endpoint (whose Send and Call are IPC in seL4 whatever the
label); the endpoint is the caller's extra capability 0, resolved through the
caller's own CSpace with the syscall's own right (`syscallRequiredRight`:
`.write` to register or revoke, `.read` to query), so the endpoint's authority
is checked as it was when the endpoint was the invoked capability.  A message
naming no extra capability is `.truncatedMessage`; an empty slot, a capability
to a kernel-reserved object, one naming no object or naming an object that is
not an endpoint is `invalidCapability 1`, a capability without the right
`.illegalAuthority`. -/
def resolveServiceEndpoint (sid : SyscallId) (tid : SeLe4n.ThreadId) (xc : Nat)
    (st : SystemState) : Except KernelError (Capability × SeLe4n.ObjId) :=
  match callerExtraCapAddr? st tid xc 0 with
  | none => .error .truncatedMessage
  | some addr =>
    match resolveCallerCapObject tid addr (syscallRequiredRight sid) st with
    | .error e => .error (e.forArgumentCap serviceEndpointCapNumber)
    | .ok (cap, epId) =>
      if objectKindIs st epId .endpoint then .ok (cap, epId)
      else .error (.invalidCapability serviceEndpointCapNumber)

/-- What `resolveServiceEndpoint` answers is extra capability 0's capability,
as the taint planner reads it (`syscallOperandCap?`), naming the endpoint
returned and carrying the syscall's right. -/
theorem resolveServiceEndpoint_ok (sid : SyscallId) (tid : SeLe4n.ThreadId) (xc : Nat)
    (st : SystemState) (cap : Capability) (epId : SeLe4n.ObjId)
    (h : resolveServiceEndpoint sid tid xc st = .ok (cap, epId)) :
    ∃ addr, callerExtraCapAddr? st tid xc 0 = some addr ∧
      syscallOperandCap? st tid addr = some cap ∧ cap.target = .object epId ∧
      cap.hasRight (syscallRequiredRight sid) = true ∧
      objectKindIs st epId .endpoint = true := by
  unfold resolveServiceEndpoint at h
  cases hA : callerExtraCapAddr? st tid xc 0 with
  | none => rw [hA] at h; cases h
  | some addr =>
    rw [hA] at h
    simp only at h
    cases hR : resolveCallerCapObject tid addr (syscallRequiredRight sid) st with
    | error e => rw [hR] at h; cases h
    | ok r =>
      obtain ⟨c, oid⟩ := r
      rw [hR] at h
      simp only at h
      by_cases hK : objectKindIs st oid .endpoint = true
      · rw [if_pos hK] at h
        cases h
        obtain ⟨callerTcb, ref, hT, hL, hC, hRt, hTg⟩ :=
          resolveCallerCapObject_ok tid addr (syscallRequiredRight sid) st cap epId hR
        exact ⟨addr, rfl, by simp only [syscallOperandCap?, hT, hL, hC], hTg, hRt, hK⟩
      · rw [if_neg hK] at h; cases h

/-- `resolveServiceEndpoint` in continuation form, through
`resolveCallerCapObjectK`: no capability pair or result cell is built
(`resolveServiceEndpointK_eq`). -/
@[inline] def resolveServiceEndpointK {α : Type} (sid : SyscallId) (tid : SeLe4n.ThreadId)
    (xc : Nat) (st : SystemState) (onErr : KernelError → α)
    (onOk : Capability → SeLe4n.ObjId → α) : α :=
  match callerExtraCapAddr? st tid xc 0 with
  | none => onErr .truncatedMessage
  | some addr =>
    resolveCallerCapObjectK tid addr (syscallRequiredRight sid) st
      (KernelError.argumentCapRefusal serviceEndpointCapNumber onErr) fun cap epId =>
        if objectKindIs st epId .endpoint then onOk cap epId
        else onErr (.invalidCapability serviceEndpointCapNumber)

theorem resolveServiceEndpointK_eq {α : Type} (sid : SyscallId) (tid : SeLe4n.ThreadId)
    (xc : Nat) (st : SystemState) (onErr : KernelError → α)
    (onOk : Capability → SeLe4n.ObjId → α) :
    resolveServiceEndpointK sid tid xc st onErr onOk =
      match resolveServiceEndpoint sid tid xc st with
      | .error e => onErr e
      | .ok (cap, epId) => onOk cap epId := by
  unfold resolveServiceEndpointK resolveServiceEndpoint
  cases callerExtraCapAddr? st tid xc 0 with
  | none => rfl
  | some addr =>
    simp only []
    rw [resolveCallerCapObjectK_eq]
    cases resolveCallerCapObject tid addr (syscallRequiredRight sid) st with
    | error e => rfl
    | ok r =>
      obtain ⟨cap, epId⟩ := r
      simp only []
      split <;> rfl

/-- **WS-SX SX6.7: a service-registry arm on its endpoint**: the endpoint
resolved (`resolveServiceEndpoint`), then `k` on its capability and id; a
refused resolution is the arm's refusal. -/
@[inline] def serviceEndpointArm (sid : SyscallId) (tid : SeLe4n.ThreadId) (xc : Nat)
    (k : Capability → SeLe4n.ObjId → Kernel Unit) : Kernel Unit :=
  fun st =>
    match resolveServiceEndpoint sid tid xc st with
    | .error e => .error e
    | .ok (cap, epId) => k cap epId st

/-- A success of a service arm is a success of its continuation on the endpoint
extra capability 0 resolved to. -/
theorem serviceEndpointArm_ok {sid : SyscallId} {tid : SeLe4n.ThreadId} {xc : Nat}
    {k : Capability → SeLe4n.ObjId → Kernel Unit} {st : SystemState} {r : Unit × SystemState}
    (h : serviceEndpointArm sid tid xc k st = .ok r) :
    ∃ epCap epId, resolveServiceEndpoint sid tid xc st = .ok (epCap, epId) ∧
      k epCap epId st = .ok r := by
  unfold serviceEndpointArm at h
  cases hR : resolveServiceEndpoint sid tid xc st with
  | error e => rw [hR] at h; cases h
  | ok p => obtain ⟨c, e⟩ := p; rw [hR] at h; exact ⟨c, e, rfl, h⟩

/-- WS-ZA ZA6.4: `resolveSchedControlConfigureTarget` in continuation form,
through `lookupSlotK`: no gate, slot reference, capability pair or result cell is
built, so the configure's resolution allocates nothing
(`resolveSchedControlConfigureTargetK_eq`). -/
@[inline] def resolveSchedControlConfigureTargetK {α : Type} (callerTid : SeLe4n.ThreadId)
    (core : Nat) (scCPtr : SeLe4n.CPtr) (len : Nat) (st : SystemState)
    (onErr : KernelError → α)
    (onOk : SeLe4n.ValidObjId → α) : α :=
  if len < truncationMinimum .schedContextConfigure then onErr .truncatedMessage else
  match st.getTcb? callerTid with
  | none => onErr .objectNotFound
  | some callerTcb =>
    lookupSlotK callerTcb scCPtr st
      (fun t a b c => onErr (.failedLookup false (LookupFault.ofWords t a b c))) (fun cnode slot =>
      match SystemState.lookupSlotCap st { cnode := cnode, slot := slot } with
      | none => onErr (.invalidCapability configureContextCapNumber)
      | some scCap =>
        if SeLe4n.Kernel.capTargetsReservedKernelObject scCap then
          onErr (.invalidCapability configureContextCapNumber)
        else
        match scCap.target with
        | .object scObjId =>
          match st.getSchedContext? (SchedContextId.ofObjId scObjId) with
          | none => onErr (.invalidCapability configureContextCapNumber)
          | some _ =>
            if core < SeLe4n.Kernel.Concurrency.numCores then
              match validateObjIdArg scObjId with
              | .error e => onErr e
              | .ok v => onOk v
            else onErr (.invalidCapability 0)
        | _ => onErr (.invalidCapability configureContextCapNumber))

theorem resolveSchedControlConfigureTargetK_eq {α : Type} (callerTid : SeLe4n.ThreadId)
    (core : Nat) (scCPtr : SeLe4n.CPtr) (len : Nat) (st : SystemState)
    (onErr : KernelError → α) (onOk : SeLe4n.ValidObjId → α) :
    resolveSchedControlConfigureTargetK callerTid core scCPtr len st onErr onOk =
      match resolveSchedControlConfigureTarget callerTid core scCPtr len st with
      | .error e => onErr e
      | .ok v => onOk v := by
  unfold resolveSchedControlConfigureTargetK resolveSchedControlConfigureTarget
  by_cases hLen : len < truncationMinimum .schedContextConfigure
  · simp only [hLen, ↓reduceIte]
  simp only [hLen, ↓reduceIte]
  cases st.getTcb? callerTid with
  | none => rfl
  | some callerTcb =>
    simp only []
    rw [lookupSlotK_eq]
    cases lookupSlot callerTcb scCPtr st with
    | error f => simp only [LookupFault.ofWords_word]
    | ok ref =>
      obtain ⟨cnode, slot⟩ := ref
      simp only []
      cases SystemState.lookupSlotCap st { cnode := cnode, slot := slot } with
      | none => rfl
      | some cap =>
        simp only []
        by_cases hI : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
        · simp only [hI, ↓reduceIte]
        · simp only [hI, Bool.false_eq_true, ↓reduceIte]
          cases cap.target with
          | object oid =>
            dsimp only
            cases st.getSchedContext? (SchedContextId.ofObjId oid) with
            | none => rfl
            | some _ =>
              dsimp only
              split
              · cases validateObjIdArg oid <;> rfl
              · rfl
          | _ => rfl

/-- WS-ZA ZA5.2: `resolveSetSpaceAt` in continuation form, through `lookupSlotK`,
the three source slots handed on as words (`resolveSetSpaceAtK_eq`). -/
@[inline] def resolveSetSpaceAtK {α : Type} (callerTid : SeLe4n.ThreadId)
    (cnAddr vrAddr fhAddr : SeLe4n.CPtr)
    (args : SeLe4n.Kernel.Architecture.SyscallArgDecode.SetSpaceArgs) (st : SystemState)
    (onErr : KernelError → α)
    (onOk : SeLe4n.ObjId → SeLe4n.Slot → SeLe4n.ObjId → SeLe4n.Slot → SeLe4n.ObjId →
      SeLe4n.Slot → α) : α :=
  match st.getTcb? callerTid with
  | none => onErr .objectNotFound
  | some callerTcb =>
    lookupSlotK callerTcb cnAddr st
      (fun t a b c => onErr (.failedLookup false (LookupFault.ofWords t a b c))) (fun cnC cnS =>
      if !cspaceRootSourceAdmitted st { cnode := cnC, slot := cnS } args.cspaceRootData then
        onErr .illegalState
      else
        lookupSlotK callerTcb vrAddr st
          (fun t a b c => onErr (.failedLookup false (LookupFault.ofWords t a b c))) (fun vrC vrS =>
          if !vspaceRootSourceAdmitted st { cnode := vrC, slot := vrS } then onErr .illegalState
          else
            lookupSlotK callerTcb fhAddr st
              (fun t a b c => onErr (.failedLookup false (LookupFault.ofWords t a b c)))
              (fun fhC fhS =>
                if faultHandlerSourceAdmitted st { cnode := fhC, slot := fhS } then
                  onOk cnC cnS vrC vrS fhC fhS
                else onErr (.invalidCapability setSpaceFaultHandlerCapNumber))))

theorem resolveSetSpaceAtK_eq {α : Type} (callerTid : SeLe4n.ThreadId)
    (cnAddr vrAddr fhAddr : SeLe4n.CPtr)
    (args : SeLe4n.Kernel.Architecture.SyscallArgDecode.SetSpaceArgs) (st : SystemState)
    (onErr : KernelError → α)
    (onOk : SeLe4n.ObjId → SeLe4n.Slot → SeLe4n.ObjId → SeLe4n.Slot → SeLe4n.ObjId →
      SeLe4n.Slot → α) :
    resolveSetSpaceAtK callerTid cnAddr vrAddr fhAddr args st onErr onOk =
      match resolveSetSpaceAt callerTid cnAddr vrAddr fhAddr args st with
      | .error e => onErr e
      | .ok (cnSrc, vrSrc, fhSrc) =>
        onOk cnSrc.cnode cnSrc.slot vrSrc.cnode vrSrc.slot fhSrc.cnode fhSrc.slot := by
  unfold resolveSetSpaceAtK resolveSetSpaceAt
  cases st.getTcb? callerTid with
  | none => rfl
  | some callerTcb =>
    simp only []
    rw [lookupSlotK_eq]
    cases lookupSlot callerTcb cnAddr st with
    | error f => simp only [LookupFault.ofWords_word]
    | ok cnSrc =>
      simp only []
      by_cases hC : cspaceRootSourceAdmitted st cnSrc args.cspaceRootData = true
      · simp only [hC, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rw [lookupSlotK_eq]
        cases lookupSlot callerTcb vrAddr st with
        | error f => simp only [LookupFault.ofWords_word]
        | ok vrSrc =>
          simp only []
          by_cases hV : vspaceRootSourceAdmitted st vrSrc = true
          · simp only [hV, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            rw [lookupSlotK_eq]
            cases lookupSlot callerTcb fhAddr st with
            | error f => simp only [LookupFault.ofWords_word]
            | ok fhSrc =>
              simp only []
              by_cases hF : faultHandlerSourceAdmitted st fhSrc = true
              · simp only [hF, ↓reduceIte]
              · simp only [hF, Bool.false_eq_true, ↓reduceIte]
          · simp only [hV, Bool.not_false, ↓reduceIte]
      · simp only [hC, Bool.not_false, ↓reduceIte]

/-- WS-ZA ZA5.4: `resolveVSpaceMapFrame` in continuation form: the frame
capability's slot is resolved once, through `lookupSlotK`, and
handed on as its CNode and slot, so no gate, slot reference, capability pair or
result triple is built (`resolveVSpaceMapFrameK_eq`). -/
@[inline] def resolveVSpaceMapFrameK {α : Type} (callerTid : SeLe4n.ThreadId)
    (args : VSpaceMapArgs) (st : SystemState) (onErr : KernelError → α)
    (onOk : SeLe4n.ObjId → SeLe4n.Slot → Capability → FrameObject → α) : α :=
  match st.getTcb? callerTid with
  | none => onErr .objectNotFound
  | some callerTcb =>
    lookupSlotK callerTcb args.frame st
      (fun t a b c => KernelError.argumentCapRefusal vspaceMapFrameCapNumber onErr
        (.failedLookup false (LookupFault.ofWords t a b c)))
      (fun cnode slot =>
        match SystemState.lookupSlotCap st { cnode := cnode, slot := slot } with
        | none => onErr (.invalidCapability vspaceMapFrameCapNumber)
        | some cap =>
          if SeLe4n.Kernel.capTargetsReservedKernelObject cap then
            onErr (.invalidCapability vspaceMapFrameCapNumber)
          else if cap.hasRight .read then
            match cap.target with
            | .object frameObjId =>
              match st.getFrame? frameObjId with
              | none => onErr (.invalidCapability vspaceMapFrameCapNumber)
              | some frame => onOk cnode slot cap frame
            | _ => onErr (.invalidCapability vspaceMapFrameCapNumber)
          else onErr .illegalAuthority)

theorem resolveVSpaceMapFrameK_eq {α : Type} (callerTid : SeLe4n.ThreadId)
    (args : VSpaceMapArgs) (st : SystemState) (onErr : KernelError → α)
    (onOk : SeLe4n.ObjId → SeLe4n.Slot → Capability → FrameObject → α) :
    resolveVSpaceMapFrameK callerTid args st onErr onOk =
      match resolveVSpaceMapFrame callerTid args st with
      | .error e => onErr e
      | .ok (frameSlot, frameCap, frame) => onOk frameSlot.cnode frameSlot.slot frameCap frame := by
  unfold resolveVSpaceMapFrameK resolveVSpaceMapFrame
  cases st.getTcb? callerTid with
  | none => rfl
  | some callerTcb =>
    simp only []
    simp only [syscallLookupArgumentCap, KernelError.argumentCapRefusal, syscallLookupCap,
      syscallResolveCap, SyscallGate.lookupSlot_mk]
    rw [lookupSlotK_eq]
    cases hRes : lookupSlot callerTcb args.frame st with
    | error f => simp only [LookupFault.ofWords_word, KernelError.forArgumentCap]
    | ok ref =>
      obtain ⟨cnode, slot⟩ := ref
      simp only []
      cases SystemState.lookupSlotCap st { cnode := cnode, slot := slot } with
      | none => rfl
      | some cap =>
        simp only []
        by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
        · simp only [hIdle, ↓reduceIte, KernelError.forArgumentCap]
        · by_cases hR : cap.hasRight .read = true
          · simp only [hIdle, hR, Bool.false_eq_true, ↓reduceIte]
            cases cap.target with
            | object fid =>
              simp only []
              cases st.getFrame? fid with
              | none => rfl
              | some frame => simp only [hRes]
            | _ => rfl
          · simp only [hIdle, hR, Bool.false_eq_true, ↓reduceIte, KernelError.forArgumentCap]

/-- **The source facts the `.tcbSetSpace` arm rests on**: the CSpace root's
source is a slot of the caller's CSpace holding a capability to a CNode that
admits the root data word, the VSpace root's a slot holding a capability to a
VSpace root, and the fault endpoint's a slot that is empty or holds a valid
fault-handler capability.  No right is asked of either root (seL4's
`decodeSetSpace` asks none). -/
theorem resolveSetSpaceAt_ok_sources (callerTid : SeLe4n.ThreadId)
    (cnAddr vrAddr fhAddr : SeLe4n.CPtr)
    (args : SeLe4n.Kernel.Architecture.SyscallArgDecode.SetSpaceArgs) (st : SystemState)
    (cnSrc vrSrc fhSrc : CSpaceAddr)
    (h : resolveSetSpaceAt callerTid cnAddr vrAddr fhAddr args st = .ok (cnSrc, vrSrc, fhSrc)) :
    ∃ callerTcb, st.getTcb? callerTid = some callerTcb ∧
      lookupSlot callerTcb cnAddr st = .ok cnSrc ∧ lookupSlot callerTcb vrAddr st = .ok vrSrc ∧
      lookupSlot callerTcb fhAddr st = .ok fhSrc ∧
      cspaceRootSourceAdmitted st cnSrc args.cspaceRootData = true ∧
      vspaceRootSourceAdmitted st vrSrc = true ∧
      faultHandlerSourceAdmitted st fhSrc = true := by
  unfold resolveSetSpaceAt at h
  cases hT : st.getTcb? callerTid with
  | none => rw [hT] at h; cases h
  | some callerTcb =>
    rw [hT] at h
    simp only at h
    cases hLc : lookupSlot callerTcb cnAddr st with
    | error f => rw [hLc] at h; cases h
    | ok c =>
      rw [hLc] at h
      simp only at h
      by_cases hC : cspaceRootSourceAdmitted st c args.cspaceRootData = true
      · simp only [hC, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        cases hLv : lookupSlot callerTcb vrAddr st with
        | error f => rw [hLv] at h; cases h
        | ok v =>
          rw [hLv] at h
          simp only at h
          by_cases hV : vspaceRootSourceAdmitted st v = true
          · simp only [hV, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
            cases hLf : lookupSlot callerTcb fhAddr st with
            | error f => rw [hLf] at h; cases h
            | ok fh =>
              rw [hLf] at h
              simp only at h
              by_cases hF : faultHandlerSourceAdmitted st fh = true
              · simp only [hF, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                exact ⟨callerTcb, rfl, hLc, hLv, hLf, hC, hV, hF⟩
              · simp only [hF, Bool.false_eq_true, ↓reduceIte] at h; cases h
          · simp only [hV, Bool.not_false, ↓reduceIte] at h; cases h
      · simp only [hC, Bool.not_false, ↓reduceIte] at h; cases h

/-- **WS-SX SX6.3 (D10): the two slots of a handler issue** (seL4's
`decodeIRQControlInvocation`).  The *source* is the slot the invoked capability
was resolved from (`lookupSlot` at `srcAddr`, as `resolveRetypeSlots`).  The
*destination* is seL4's `lookupTargetSlot`: the CNode capability the caller
names as extra capability 0 (`rootAddr`, its address in the caller's CSpace,
looked up as the dispatch prologue's `lookupExtraCaps` looks it up — a failed
walk is `seL4_FailedLookup`, an empty slot `invalidRoot`), then
`lookupSlotForCNodeOp` on it by `index` and `depth`, seL4's order and answers.
No right is required of the root: seL4's `lookupTargetSlot` checks none. -/
def resolveIssuingSlotsAt (callerTid : SeLe4n.ThreadId) (srcAddr rootAddr index : SeLe4n.CPtr)
    (depth : Nat) (st : SystemState) : Except KernelError (CSpaceAddr × CSpaceAddr) :=
  match st.getTcb? callerTid with
  | none => .error .objectNotFound
  | some callerTcb =>
    match lookupSlot callerTcb srcAddr st with
    | .error f => .error (.failedLookup false f)
    | .ok src =>
      match lookupSlot callerTcb rootAddr st with
      | .error f => .error (.failedLookup false f)
      | .ok rootRef =>
        match SystemState.lookupSlotCap st rootRef with
        | none => .error (.failedLookup false .invalidRoot)
        | some rootCap =>
          match lookupSlotForCNodeOp false rootCap index depth st with
          | .error e => .error e
          | .ok dst => .ok (src, dst)

/-- `resolveIssuingSlotsAt` in continuation form: the walks are `lookupSlotK`'s
and `lookupSlotForCNodeOpK`'s, each slot handed on as words, so no slot
reference or pair is built (`resolveIssuingSlotsAtK_eq`). -/
@[inline] def resolveIssuingSlotsAtK {α : Type} (callerTid : SeLe4n.ThreadId)
    (srcAddr rootAddr index : SeLe4n.CPtr) (depth : Nat) (st : SystemState)
    (onErr : KernelError → α)
    (onOk : SeLe4n.ObjId → SeLe4n.Slot → SeLe4n.ObjId → SeLe4n.Slot → α) : α :=
  match st.getTcb? callerTid with
  | none => onErr .objectNotFound
  | some callerTcb =>
    lookupSlotK callerTcb srcAddr st
      (fun t a b c => onErr (.failedLookup false (LookupFault.ofWords t a b c)))
      (fun srcCnode srcSlot =>
        lookupSlotK callerTcb rootAddr st
          (fun t a b c => onErr (.failedLookup false (LookupFault.ofWords t a b c)))
          (fun rCn rSlot =>
            match SystemState.lookupSlotCap st { cnode := rCn, slot := rSlot } with
            | none => onErr (.failedLookup false .invalidRoot)
            | some rootCap =>
              lookupSlotForCNodeOpK false rootCap index depth st onErr
                (fun dCn dSlot => onOk srcCnode srcSlot dCn dSlot)))

theorem resolveIssuingSlotsAtK_eq {α : Type} (callerTid : SeLe4n.ThreadId)
    (srcAddr rootAddr index : SeLe4n.CPtr) (depth : Nat) (st : SystemState)
    (onErr : KernelError → α)
    (onOk : SeLe4n.ObjId → SeLe4n.Slot → SeLe4n.ObjId → SeLe4n.Slot → α) :
    resolveIssuingSlotsAtK callerTid srcAddr rootAddr index depth st onErr onOk =
      match resolveIssuingSlotsAt callerTid srcAddr rootAddr index depth st with
      | .error e => onErr e
      | .ok (src, dst) => onOk src.cnode src.slot dst.cnode dst.slot := by
  unfold resolveIssuingSlotsAtK resolveIssuingSlotsAt
  cases st.getTcb? callerTid with
  | none => rfl
  | some callerTcb =>
    simp only []
    rw [lookupSlotK_eq]
    cases lookupSlot callerTcb srcAddr st with
    | error f => simp only [LookupFault.ofWords_word]
    | ok src =>
      simp only []
      rw [lookupSlotK_eq]
      cases lookupSlot callerTcb rootAddr st with
      | error f => simp only [LookupFault.ofWords_word]
      | ok rootRef =>
        simp only []
        cases SystemState.lookupSlotCap st rootRef with
        | none => rfl
        | some rootCap =>
          simp only []
          rw [lookupSlotForCNodeOpK_eq]
          cases lookupSlotForCNodeOp false rootCap index depth st <;> rfl

/-- **WS-SX SX6.3 (D9): the destination CNode a retype's root, index and depth
name** (seL4's `decodeUntypedInvocation`).  At depth 0 the destination is the
root capability itself; past it, the slot `lookupTargetSlot` (`lookupSlotForCNodeOp`)
finds under the root at `index`, read to the capability it holds.  A destination
that is not a CNode capability — an empty root slot or target slot included — is
`seL4_FailedLookup` (destination) `MissingCapability` with the depth as its bits
left, seL4's answer; the walk's own refusals are its own.  No right is required
of either: seL4's lookup checks none.  The CNode is handed on with its slot
count. -/
def retypeDestinationCNode (rootCap? : Option Capability) (index : SeLe4n.CPtr)
    (depth : Nat) (st : SystemState) : Except KernelError (SeLe4n.ObjId × Nat) :=
  let nodeCap? : Except KernelError (Option Capability) :=
    if depth = 0 then .ok rootCap? else
    match rootCap? with
    | none => .error (.failedLookup false .invalidRoot)
    | some rootCap =>
      match lookupSlotForCNodeOp false rootCap index depth st with
      | .error e => .error e
      | .ok ref => .ok (SystemState.lookupSlotCap st ref)
  match nodeCap? with
  | .error e => .error e
  | .ok nodeCap? =>
    match nodeCap? with
    | some nodeCap =>
      match nodeCap.target with
      | .object cnodeId =>
        match st.getCNode? cnodeId with
        | some cn => .ok (cnodeId, 2 ^ cn.radixWidth)
        | none => .error (.failedLookup false (.missingCapability depth.toUInt8))
      | _ => .error (.failedLookup false (.missingCapability depth.toUInt8))
    | none => .error (.failedLookup false (.missingCapability depth.toUInt8))

/-- **WS-SX SX6.3 (D9): the window a retype names in its destination CNode**,
seL4's checks in its order: an offset past the last slot is
`seL4_RangeError (0, size - 1)`; a count of none or past the fan-out limit
(`Concurrency.retypeFanOutLimit`, seL4's `CONFIG_RETYPE_FAN_OUT_LIMIT`)
`seL4_RangeError (1, limit)`; a window past the CNode's end
`seL4_RangeError (1, size - offset)`. -/
def retypeWindowRefusal (size offset count : Nat) : Option KernelError :=
  if size - 1 < offset then some (.rangeError 0 (size - 1).toUInt64)
  else if count < 1 ∨ Concurrency.retypeFanOutLimit < count then
    some (.rangeError 1 Concurrency.retypeFanOutLimit.toUInt64)
  else if size - offset < count then some (.rangeError 1 (size - offset).toUInt64)
  else none

/-- **WS-SX SX6.3 (D9): the two slots of a carve** (seL4's
`decodeUntypedInvocation`).  The *source* is the slot the invoked untyped
capability was resolved from (`lookupSlot` at `srcAddr`).  The *destination* is
the first slot of the window: the root is the capability the caller names as
extra capability 0 (`rootAddr`, looked up as the dispatch prologue's
`lookupExtraCaps` looks it up — a failed walk is `seL4_FailedLookup`), the CNode
the one the root, index and depth name (`retypeDestinationCNode`), and the slot
the window's offset in it once the window is in range (`retypeWindowRefusal`).
The slot's emptiness is the carve's own check (`cspaceDstRefusal`). -/
def resolveRetypeSlots (callerTid : SeLe4n.ThreadId) (srcAddr rootAddr index : SeLe4n.CPtr)
    (depth offset count : Nat) (st : SystemState) : Except KernelError (CSpaceAddr × CSpaceAddr) :=
  match st.getTcb? callerTid with
  | none => .error .objectNotFound
  | some callerTcb =>
    match lookupSlot callerTcb srcAddr st with
    | .error f => .error (.failedLookup false f)
    | .ok src =>
      match lookupSlot callerTcb rootAddr st with
      | .error f => .error (.failedLookup false f)
      | .ok rootRef =>
        match retypeDestinationCNode (SystemState.lookupSlotCap st rootRef) index depth st with
        | .error e => .error e
        | .ok (cnodeId, size) =>
          match retypeWindowRefusal size offset count with
          | some e => .error e
          | none => .ok (src, { cnode := cnodeId, slot := SeLe4n.Slot.ofNat offset })

/-- `retypeDestinationCNode` in continuation form: the walk is
`lookupSlotForCNodeOpK`'s and the CNode is handed on as words, so no slot
reference, option or pair is built (`retypeDestinationCNodeK_eq`). -/
@[inline] def retypeDestinationCNodeK {α : Type} (rootCap? : Option Capability)
    (index : SeLe4n.CPtr) (depth : Nat) (st : SystemState) (onErr : KernelError → α)
    (onOk : SeLe4n.ObjId → Nat → α) : α :=
  let ofNode : Option Capability → α := fun nodeCap? =>
    match nodeCap? with
    | some nodeCap =>
      match nodeCap.target with
      | .object cnodeId =>
        match st.getCNode? cnodeId with
        | some cn => onOk cnodeId (2 ^ cn.radixWidth)
        | none => onErr (.failedLookup false (.missingCapability depth.toUInt8))
      | _ => onErr (.failedLookup false (.missingCapability depth.toUInt8))
    | none => onErr (.failedLookup false (.missingCapability depth.toUInt8))
  if depth = 0 then ofNode rootCap? else
  match rootCap? with
  | none => onErr (.failedLookup false .invalidRoot)
  | some rootCap =>
    lookupSlotForCNodeOpK false rootCap index depth st onErr
      (fun cn sl => ofNode (SystemState.lookupSlotCap st { cnode := cn, slot := sl }))

theorem retypeDestinationCNodeK_eq {α : Type} (rootCap? : Option Capability)
    (index : SeLe4n.CPtr) (depth : Nat) (st : SystemState) (onErr : KernelError → α)
    (onOk : SeLe4n.ObjId → Nat → α) :
    retypeDestinationCNodeK rootCap? index depth st onErr onOk =
      match retypeDestinationCNode rootCap? index depth st with
      | .error e => onErr e
      | .ok (cnodeId, size) => onOk cnodeId size := by
  unfold retypeDestinationCNodeK retypeDestinationCNode
  by_cases hD : depth = 0
  · simp only [hD, ↓reduceIte]
    rcases rootCap? with _ | cap
    · rfl
    · simp only []
      cases hT : cap.target <;> simp only [hT]
      rename_i cnodeId
      cases st.getCNode? cnodeId <;> rfl
  · simp only [hD, ↓reduceIte]
    rcases rootCap? with _ | rootCap
    · rfl
    · simp only []
      rw [lookupSlotForCNodeOpK_eq]
      cases lookupSlotForCNodeOp false rootCap index depth st with
      | error e => rfl
      | ok ref =>
        simp only []
        rcases SystemState.lookupSlotCap st ref with _ | cap
        · rfl
        · simp only []
          cases hT : cap.target <;> simp only [hT]
          rename_i cnodeId
          cases st.getCNode? cnodeId <;> rfl

/-- `resolveRetypeSlots` in continuation form: the walks are `lookupSlotK`'s and
`retypeDestinationCNodeK`'s, each slot handed on as words, so no slot reference
or pair is built (`resolveRetypeSlotsK_eq`). -/
@[inline] def resolveRetypeSlotsK {α : Type} (callerTid : SeLe4n.ThreadId)
    (srcAddr rootAddr index : SeLe4n.CPtr) (depth offset count : Nat) (st : SystemState)
    (onErr : KernelError → α)
    (onOk : SeLe4n.ObjId → SeLe4n.Slot → SeLe4n.ObjId → SeLe4n.Slot → α) : α :=
  match st.getTcb? callerTid with
  | none => onErr .objectNotFound
  | some callerTcb =>
    lookupSlotK callerTcb srcAddr st
      (fun t a b c => onErr (.failedLookup false (LookupFault.ofWords t a b c)))
      (fun srcCnode srcSlot =>
        lookupSlotK callerTcb rootAddr st
          (fun t a b c => onErr (.failedLookup false (LookupFault.ofWords t a b c)))
          (fun rCn rSlot =>
            retypeDestinationCNodeK
              (SystemState.lookupSlotCap st { cnode := rCn, slot := rSlot }) index depth st onErr
              (fun cnodeId size =>
                match retypeWindowRefusal size offset count with
                | some e => onErr e
                | none => onOk srcCnode srcSlot cnodeId (SeLe4n.Slot.ofNat offset))))

theorem resolveRetypeSlotsK_eq {α : Type} (callerTid : SeLe4n.ThreadId)
    (srcAddr rootAddr index : SeLe4n.CPtr) (depth offset count : Nat) (st : SystemState)
    (onErr : KernelError → α)
    (onOk : SeLe4n.ObjId → SeLe4n.Slot → SeLe4n.ObjId → SeLe4n.Slot → α) :
    resolveRetypeSlotsK callerTid srcAddr rootAddr index depth offset count st onErr onOk =
      match resolveRetypeSlots callerTid srcAddr rootAddr index depth offset count st with
      | .error e => onErr e
      | .ok (src, dst) => onOk src.cnode src.slot dst.cnode dst.slot := by
  unfold resolveRetypeSlotsK resolveRetypeSlots
  cases st.getTcb? callerTid with
  | none => rfl
  | some callerTcb =>
    simp only []
    rw [lookupSlotK_eq]
    cases lookupSlot callerTcb srcAddr st with
    | error f => simp only [LookupFault.ofWords_word]
    | ok src =>
      simp only []
      rw [lookupSlotK_eq]
      cases lookupSlot callerTcb rootAddr st with
      | error f => simp only [LookupFault.ofWords_word]
      | ok rootRef =>
        simp only []
        rw [retypeDestinationCNodeK_eq]
        cases retypeDestinationCNode (SystemState.lookupSlotCap st rootRef) index depth st with
        | error e => rfl
        | ok p =>
          obtain ⟨cnodeId, size⟩ := p
          simp only []
          cases retypeWindowRefusal size offset count <;> rfl

/-- **WS-BP BP7.1 slice 4 (`v0.36.8`), every kind since WS-ZA ZA5.4 part 14: the
carve a decoded `.untypedRetype` requests.**  A kind of fixed size — a frame, a
page table, a VSpace root, a thread, an endpoint, a notification or a reply —
takes `sizeBits = 0`, the value a frame's MR0 carried before the field existed;
a child untyped takes `sizeBits` in `[minUntypedSizeBits, maxUntypedSizeBits]`,
a CNode its radix in `[minCNodeRadixBits, maxCNodeRadixBits]` and a scheduling
context its size in `[minSchedContextSizeBits, maxUntypedSizeBits]`, the bounds
seL4's `decodeUntypedInvocation` puts on `userObjSize`.  The arm supplies what
the creating core decides: a VSpace root's ASID, the least free one
(`freshAsid?`; `.resourceExhausted` when every ASID is taken), and a thread's
domain and affinity, the core's current domain and the core itself, as seL4's
`createObject` takes `ksCurDomain` and `getCurrentCPUIndex`.  Anything else is
`.invalidArgument`. -/
def carveRequestOf? (st : SystemState) (executingCore : Concurrency.CoreId)
    (newType : KernelObjectType) (sizeBits : Nat) : Except KernelError CarveRequest :=
  match newType with
  | .frame => if sizeBits = 0 then .ok .frame else .error (.invalidArgument 0)
  -- WS-BP BP7.1 (`v0.36.12`): a page table is one page, like a frame.
  | .pageTable => if sizeBits = 0 then .ok .pageTable else .error (.invalidArgument 0)
  | .untyped =>
      if minUntypedSizeBits ≤ sizeBits ∧ sizeBits ≤ maxUntypedSizeBits then
        .ok (.untyped sizeBits)
      else .error (.invalidArgument 0)
  | .vspaceRoot =>
      if sizeBits = 0 then
        match freshAsid? st with
        | some asid => .ok (.vspaceRoot asid)
        | none => .error .resourceExhausted
      else .error (.invalidArgument 0)
  | .tcb =>
      if sizeBits = 0 then
        .ok (.tcb (st.scheduler.activeDomainOnCore executingCore) executingCore)
      else .error (.invalidArgument 0)
  | .endpoint => if sizeBits = 0 then .ok .endpoint else .error (.invalidArgument 0)
  | .notification => if sizeBits = 0 then .ok .notification else .error (.invalidArgument 0)
  | .reply => if sizeBits = 0 then .ok .reply else .error (.invalidArgument 0)
  | .cnode =>
      if hB : minCNodeRadixBits ≤ sizeBits ∧ sizeBits ≤ maxCNodeRadixBits then
        .ok (.cnode sizeBits (Nat.le_trans hB.2 maxCNodeRadixBits_le_maxCSpaceDepth))
      else .error (.invalidArgument 0)
  | .schedContext =>
      if minSchedContextSizeBits ≤ sizeBits ∧ sizeBits ≤ maxUntypedSizeBits then
        .ok (.schedContext sizeBits)
      else .error (.invalidArgument 0)

/-- **WS-BP BP7.1**: the requests the decode accepts — each kind at the size
bounds the decode states, a VSpace root under an ASID `freshAsid?` answered and
(WS-ZA ZA5.4 part 14) a thread in the creating core's domain with that core as
its affinity.  These are the only requests the arm ever hands the carve. -/
theorem carveRequestOf?_ok (st : SystemState) (executingCore : Concurrency.CoreId)
    (newType : KernelObjectType) (sizeBits : Nat)
    (req : CarveRequest) (h : carveRequestOf? st executingCore newType sizeBits = .ok req) :
    (newType = .frame ∧ sizeBits = 0 ∧ req = .frame) ∨
    (newType = .untyped ∧ minUntypedSizeBits ≤ sizeBits ∧ sizeBits ≤ maxUntypedSizeBits ∧
      req = .untyped sizeBits) ∨
    (newType = .vspaceRoot ∧ sizeBits = 0 ∧
      ∃ asid, freshAsid? st = some asid ∧ req = .vspaceRoot asid) ∨
    (newType = .pageTable ∧ sizeBits = 0 ∧ req = .pageTable) ∨
    (newType = .tcb ∧ sizeBits = 0 ∧
      req = .tcb (st.scheduler.activeDomainOnCore executingCore) executingCore) ∨
    (newType = .endpoint ∧ sizeBits = 0 ∧ req = .endpoint) ∨
    (newType = .notification ∧ sizeBits = 0 ∧ req = .notification) ∨
    (newType = .reply ∧ sizeBits = 0 ∧ req = .reply) ∨
    (newType = .cnode ∧ minCNodeRadixBits ≤ sizeBits ∧ sizeBits ≤ maxCNodeRadixBits ∧
      ∃ hB, req = .cnode sizeBits hB) ∨
    (newType = .schedContext ∧ minSchedContextSizeBits ≤ sizeBits ∧
      sizeBits ≤ maxUntypedSizeBits ∧ req = .schedContext sizeBits) := by
  cases newType <;> simp only [carveRequestOf?] at h
  case vspaceRoot =>
    by_cases hB : sizeBits = 0
    · simp only [hB, ↓reduceIte] at h
      cases hF : freshAsid? st with
      | none => rw [hF] at h; cases h
      | some asid =>
        rw [hF] at h; cases h
        exact Or.inr (Or.inr (Or.inl ⟨rfl, hB, asid, rfl, rfl⟩))
    · simp [hB] at h
  all_goals (split at h <;> (try cases h))
  all_goals first
    | (left; exact ⟨rfl, by assumption, rfl⟩)
    | (right; left; exact ⟨rfl, (by assumption : _ ∧ _).1, (by assumption : _ ∧ _).2, rfl⟩)
    | (right; right; right; left; exact ⟨rfl, by assumption, rfl⟩)
    | (right; right; right; right; left; exact ⟨rfl, by assumption, rfl⟩)
    | (right; right; right; right; right; left; exact ⟨rfl, by assumption, rfl⟩)
    | (right; right; right; right; right; right; left; exact ⟨rfl, by assumption, rfl⟩)
    | (right; right; right; right; right; right; right; left; exact ⟨rfl, by assumption, rfl⟩)
    | (right; right; right; right; right; right; right; right; left;
        exact ⟨rfl, (by assumption : _ ∧ _).1, (by assumption : _ ∧ _).2, _, rfl⟩)
    | (right; right; right; right; right; right; right; right; right;
        exact ⟨rfl, (by assumption : _ ∧ _).1, (by assumption : _ ∧ _).2, rfl⟩)

/-- WS-ZA ZA6.35: **`carveRequestOf?` as words, handed to a continuation** —
the kind's code, the size, the thread's domain and core and the root's ASID
(`CarveRequest.ofWords`), so the decode builds neither a request nor an
`Except` (`carveRequestWordsK_eq`).  A kind other than a thread carries the
domain `0` and the executing core, and one other than a VSpace root the ASID
`0`, which nothing reads. -/
@[inline] def carveRequestWordsK {α : Type} (st : SystemState) (executingCore : Concurrency.CoreId)
    (newType : KernelObjectType) (sizeBits : Nat) (kErr : KernelError → α)
    (kOk : Nat → Nat → SeLe4n.DomainId → Concurrency.CoreId → SeLe4n.ASID → α) : α :=
  match newType with
  | .frame =>
      if sizeBits = 0 then kOk 0 0 (.ofNat 0) executingCore (.ofNat 0) else kErr (.invalidArgument 0)
  | .pageTable =>
      if sizeBits = 0 then kOk 3 0 (.ofNat 0) executingCore (.ofNat 0) else kErr (.invalidArgument 0)
  | .untyped =>
      if minUntypedSizeBits ≤ sizeBits ∧ sizeBits ≤ maxUntypedSizeBits then
        kOk 1 sizeBits (.ofNat 0) executingCore (.ofNat 0)
      else kErr (.invalidArgument 0)
  | .vspaceRoot =>
      if sizeBits = 0 then
        match freshAsidCodeFrom st st.machine.maxASID 1 with
        | 0 => kErr .resourceExhausted
        | a + 1 => kOk 2 0 (.ofNat 0) executingCore (SeLe4n.ASID.ofNat a)
      else kErr (.invalidArgument 0)
  | .tcb =>
      if sizeBits = 0 then
        kOk 4 0 (st.scheduler.activeDomainOnCore executingCore) executingCore (.ofNat 0)
      else kErr (.invalidArgument 0)
  | .endpoint =>
      if sizeBits = 0 then kOk 5 0 (.ofNat 0) executingCore (.ofNat 0) else kErr (.invalidArgument 0)
  | .notification =>
      if sizeBits = 0 then kOk 6 0 (.ofNat 0) executingCore (.ofNat 0) else kErr (.invalidArgument 0)
  | .reply =>
      if sizeBits = 0 then kOk 8 0 (.ofNat 0) executingCore (.ofNat 0) else kErr (.invalidArgument 0)
  | .cnode =>
      if minCNodeRadixBits ≤ sizeBits ∧ sizeBits ≤ maxCNodeRadixBits then
        kOk 7 sizeBits (.ofNat 0) executingCore (.ofNat 0)
      else kErr (.invalidArgument 0)
  | .schedContext =>
      if minSchedContextSizeBits ≤ sizeBits ∧ sizeBits ≤ maxUntypedSizeBits then
        kOk 9 sizeBits (.ofNat 0) executingCore (.ofNat 0)
      else kErr (.invalidArgument 0)

theorem carveRequestWordsK_eq {α : Type} (st : SystemState) (executingCore : Concurrency.CoreId)
    (newType : KernelObjectType) (sizeBits : Nat) (kErr : KernelError → α)
    (kOk : Nat → Nat → SeLe4n.DomainId → Concurrency.CoreId → SeLe4n.ASID → α) :
    carveRequestWordsK st executingCore newType sizeBits kErr kOk =
      match carveRequestOf? st executingCore newType sizeBits with
      | .error e => kErr e
      | .ok req => kOk req.kindWord req.sizeWord (req.domainWord (.ofNat 0))
          (req.coreWord executingCore) (req.asidWord (.ofNat 0)) := by
  cases newType
  case vspaceRoot =>
    simp only [carveRequestWordsK, carveRequestOf?, freshAsid?,
      freshAsidFrom_eq_code st st.machine.maxASID 1]
    by_cases hB : sizeBits = 0
    · simp only [hB, ↓reduceIte]
      cases freshAsidCodeFrom st st.machine.maxASID 1 <;> rfl
    · simp only [hB, ↓reduceIte]
  all_goals
    simp only [carveRequestWordsK, carveRequestOf?]
    split <;> rfl

/-- **WS-SX SX6.3 (D9): the ids of a window's objects `i, i + 1, …`** (`k` of
them), each a raw operand the first object's id names (`retypeChildId`), so each
passes `validateObjIdArg` as the first does — no reserved idle object — and is
refused with the same error, at the id's argument word. -/
def retypeChildIdsRefusal (childId : SeLe4n.ObjId) : Nat → Nat → Option KernelError
  | _, 0 => none
  | i, k + 1 =>
    match validateObjIdArg (retypeChildId childId i) with
    | .error e => some (e.forArgumentWord UntypedRetypeArgs.childIdWord)
    | .ok _ => retypeChildIdsRefusal childId (i + 1) k

/-- **WS-BP BP7.1 (`v0.36.5`, child untypeds at slice 4, `v0.36.8`): the live
`.untypedRetype` arm's transition** — seL4's `seL4_Untyped_Retype`, at every
object kind since WS-ZA ZA5.4 part 14.

The destination root first, the caller's extra capability 0 (`root?`; none is
`seL4_TruncatedMessage`, checked with the length and before the type as seL4's
`decodeUntypedInvocation` checks it — WS-SX SX6.3, D9), then the arm's decode of
the message registers (`args?`), then the carve request (`carveRequestOf?`: each kind at its size
bounds, a VSpace root under a fresh ASID and a thread in the creating core's
domain — anything else `.invalidArgument`).  The child id is a raw operand, so it
passes `validateObjIdArg` — no reserved idle object and not the sentinel —
before anything is resolved.  Then the two slots (`resolveRetypeSlots`: the
invoked capability's own slot, and the window's first slot in the CNode the root,
index and depth name, in range and with a count of 1 to seL4's fan-out limit),
then the ids of the window's other objects, `childId + 1` onward
(`retypeChildIdsRefusal`, WS-SX SX6.3), then the window (`untypedRetypeWindow`):
every refusal before any write, then one carve per object, object `i` at id
`childId + i` into slot `offset + i`. -/
def untypedRetypeFromCap (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (srcAddr : SeLe4n.CPtr) (root? : Option SeLe4n.CPtr)
    (args? : Except KernelError UntypedRetypeArgs) : Kernel Unit :=
  fun st =>
    match root? with
    | none => .error .truncatedMessage
    | some rootAddr =>
    match args? with
    | .error e => .error e
    | .ok args =>
      match carveRequestOf? st executingCore args.newType args.sizeBits with
      | .error e => .error e
      | .ok req =>
        match validateObjIdArg args.childId with
        | .error e => .error (e.forArgumentWord UntypedRetypeArgs.childIdWord)
        | .ok vChild =>
          match resolveRetypeSlots tid srcAddr rootAddr args.nodeIndex args.nodeDepth
              args.nodeOffset args.numObjects st with
          | .error e => .error e
          | .ok (src, dst) =>
            match retypeChildIdsRefusal vChild.val 1 (args.numObjects - 1) with
            | some e => .error e
            | none => untypedRetypeWindow src vChild.val dst req args.numObjects st

/-- A retype whose message is short is `seL4_TruncatedMessage` whether or not it
names its root: seL4 answers both with the one error. -/
theorem untypedRetypeFromCap_truncated (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (srcAddr : SeLe4n.CPtr) (root? : Option SeLe4n.CPtr)
    (st : SystemState) :
    untypedRetypeFromCap tid executingCore srcAddr root? (.error .truncatedMessage) st =
      .error .truncatedMessage := by
  cases root? <;> rfl

/-- **WS-ZA ZA6.32: the live `.irqControlGet` arm's transition** — seL4's
`seL4_IRQControl_Get`.  The decode, then the destination root, the caller's
extra capability 0 (`root?`; none is `seL4_TruncatedMessage`, checked with the
length as seL4's `decodeIRQControlInvocation` checks it — WS-SX SX6.3, D10),
then the line checks (`irqControlLineRefusal`: a line no greater than the
board's last, `seL4_RangeError` otherwise, then a device line of the board with
its node, held by no handler — seL4's `Arch_checkIRQ` and `isIRQActive`, read
before the slots as seL4 reads them), then the two slots
(`resolveIssuingSlotsAt`: the invoked interrupt-control capability's own slot
and the slot the root names by the index and depth words, seL4's
`lookupTargetSlot`), then `irqControlGet`. -/
def irqControlGetFromCap (tid : SeLe4n.ThreadId) (srcAddr : SeLe4n.CPtr)
    (root? : Option SeLe4n.CPtr) (args? : Except KernelError IrqControlGetArgs) : Kernel Unit :=
  fun st =>
    match args? with
    | .error e => .error e
    | .ok args =>
      match root? with
      | none => .error .truncatedMessage
      | some rootAddr =>
      match irqControlLineRefusal st args.line with
      | some e => .error e
      | none =>
        match resolveIssuingSlotsAt tid srcAddr rootAddr args.dstIndex args.dstDepth st with
        | .error e => .error e
        | .ok (control, dst) => irqControlGet control dst args.line st

/-- **WS-ZA ZA6.32: the live `.irqHandlerSetNotification` arm's transition** —
seL4's `seL4_IRQHandler_SetNotification`.  The decode, then the notification
capability's slot resolved through the caller's own CSpace with the send right
(`resolveCallerCapSlot … .write`, seL4's `capNtfnCanSend`), then
`irqHandlerSetNotification`. -/
def irqHandlerSetNotificationFromCap (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (line : Nat)
    (args? : Except KernelError IrqHandlerSetNotificationArgs) : Kernel Unit :=
  fun st =>
    match args? with
    | .error e => .error e
    | .ok args =>
      match resolveCallerCapSlot tid args.notificationCPtr .write st with
      | .error e => .error (e.forArgumentCap irqHandlerNotificationCapNumber)
      | .ok (src, _, _) => irqHandlerSetNotification executingCore line src st

/-- **WS-ZA ZA6.32**: what a successful `.irqControlGet` consists of — the
decode, the line checks, the resolved slots, and the issue. -/
theorem irqControlGetFromCap_ok (tid : SeLe4n.ThreadId) (srcAddr : SeLe4n.CPtr)
    (root? : Option SeLe4n.CPtr)
    (args? : Except KernelError IrqControlGetArgs) (st st' : SystemState)
    (h : irqControlGetFromCap tid srcAddr root? args? st = .ok ((), st')) :
    ∃ (args : IrqControlGetArgs) (control dst : CSpaceAddr),
      args? = .ok args ∧ irqControlLineRefusal st args.line = none ∧
      (∃ rootAddr, root? = some rootAddr ∧
        resolveIssuingSlotsAt tid srcAddr rootAddr args.dstIndex args.dstDepth st
          = .ok (control, dst)) ∧
      irqControlGet control dst args.line st = .ok ((), st') := by
  unfold irqControlGetFromCap at h
  cases hD : args? with
  | error e => rw [hD] at h; cases h
  | ok args =>
    rw [hD] at h
    simp only at h
    cases hRt : root? with
    | none => rw [hRt] at h; cases h
    | some rootAddr =>
    rw [hRt] at h
    simp only at h
    cases hR : irqControlLineRefusal st args.line with
    | some e => rw [hR] at h; cases h
    | none =>
      rw [hR] at h
      simp only at h
      cases hS : resolveIssuingSlotsAt tid srcAddr rootAddr args.dstIndex args.dstDepth st with
      | error e => rw [hS] at h; cases h
      | ok pr =>
        obtain ⟨control, dst⟩ := pr
        rw [hS] at h
        exact ⟨args, control, dst, rfl, hR, ⟨rootAddr, rfl, hS⟩, h⟩

/-- **WS-ZA ZA6.32**: what a successful `.irqHandlerSetNotification` consists
of — the decode, the notification capability's slot, and the bind. -/
theorem irqHandlerSetNotificationFromCap_ok (tid : SeLe4n.ThreadId)
    (ec : Concurrency.CoreId) (line : Nat)
    (args? : Except KernelError IrqHandlerSetNotificationArgs) (st st' : SystemState)
    (h : irqHandlerSetNotificationFromCap tid ec line args? st = .ok ((), st')) :
    ∃ (args : IrqHandlerSetNotificationArgs) (src : CSpaceAddr),
      args? = .ok args ∧
      irqHandlerSetNotification ec line src st = .ok ((), st') := by
  unfold irqHandlerSetNotificationFromCap at h
  cases hD : args? with
  | error e => rw [hD] at h; cases h
  | ok args =>
    rw [hD] at h
    simp only at h
    cases hS : resolveCallerCapSlot tid args.notificationCPtr .write st with
    | error e => rw [hS] at h; cases h
    | ok q =>
      obtain ⟨src, _, _⟩ := q
      rw [hS] at h
      exact ⟨args, src, rfl, h⟩

/-- **WS-BP BP7.1**: what a successful `.untypedRetype` consists of — the typed
decode, the carve request, the validated child id, the resolved slots, the
window's other ids, and the window (WS-SX SX6.3: every refusal before any
write, then the carves).  The case analysis has one owner, so the invariant and
non-interference proofs read these equations. -/
theorem untypedRetypeFromCap_ok (tid : SeLe4n.ThreadId) (ec : Concurrency.CoreId)
    (srcAddr : SeLe4n.CPtr) (root? : Option SeLe4n.CPtr)
    (args? : Except KernelError UntypedRetypeArgs) (st st' : SystemState)
    (h : untypedRetypeFromCap tid ec srcAddr root? args? st = .ok ((), st')) :
    ∃ (args : UntypedRetypeArgs) (rootAddr : SeLe4n.CPtr) (req : CarveRequest)
      (vChild : SeLe4n.ValidObjId) (src dst : CSpaceAddr),
      args? = .ok args ∧ root? = some rootAddr ∧
      carveRequestOf? st ec args.newType args.sizeBits = .ok req ∧
      validateObjIdArg args.childId = .ok vChild ∧
      resolveRetypeSlots tid srcAddr rootAddr args.nodeIndex args.nodeDepth args.nodeOffset
        args.numObjects st = .ok (src, dst) ∧
      retypeChildIdsRefusal vChild.val 1 (args.numObjects - 1) = none ∧
      untypedRetypeWindow src vChild.val dst req args.numObjects st = .ok ((), st') := by
  unfold untypedRetypeFromCap at h
  cases hRt : root? with
  | none => rw [hRt] at h; cases h
  | some rootAddr =>
  rw [hRt] at h
  simp only at h
  cases hD : args? with
  | error e => rw [hD] at h; cases h
  | ok args =>
    rw [hD] at h
    simp only at h
    cases hQ : carveRequestOf? st ec args.newType args.sizeBits with
    | error e => rw [hQ] at h; cases h
    | ok req =>
      rw [hQ] at h
      simp only at h
      cases hV : validateObjIdArg args.childId with
      | error e => rw [hV] at h; cases h
      | ok vChild =>
        rw [hV] at h
        simp only at h
        cases hR : resolveRetypeSlots tid srcAddr rootAddr args.nodeIndex args.nodeDepth
            args.nodeOffset args.numObjects st with
        | error e => rw [hR] at h; cases h
        | ok pr =>
          obtain ⟨src, dst⟩ := pr
          rw [hR] at h
          simp only at h
          cases hI : retypeChildIdsRefusal vChild.val 1 (args.numObjects - 1) with
          | some e => rw [hI] at h; cases h
          | none =>
            rw [hI] at h
            exact ⟨args, rootAddr, req, vChild, src, dst, rfl, rfl, hQ, hV, hR, hI, h⟩

/-- **A successful `.untypedRetype` is a chain of successful carves**
(`untypedRetypeWindow_ok`): every invariant a single carve keeps, the arm keeps
(`RetypeCarveChain.preserves`, `RetypeCarveChain.rel`). -/
theorem untypedRetypeFromCap_chain {tid : SeLe4n.ThreadId} {ec : Concurrency.CoreId}
    {srcAddr : SeLe4n.CPtr} {root? : Option SeLe4n.CPtr}
    {args? : Except KernelError UntypedRetypeArgs} {st st' : SystemState}
    (h : untypedRetypeFromCap tid ec srcAddr root? args? st = .ok ((), st')) :
    RetypeCarveChain st st' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hW⟩ :=
    untypedRetypeFromCap_ok tid ec srcAddr root? args? st st' h
  exact (untypedRetypeWindow_ok hW).2

/-- **WS-ZA ZA5.4 part 17: the `.untypedRetype` arm preserves the capability
bundle** — every carve of the window keeps every conjunct
(`untypedRetypeObject_preserves_capabilityInvariantBundle`). -/
theorem untypedRetypeFromCap_preserves_capabilityInvariantBundle (tid : SeLe4n.ThreadId)
    (ec : Concurrency.CoreId) (srcAddr : SeLe4n.CPtr) (root? : Option SeLe4n.CPtr)
    (args? : Except KernelError UntypedRetypeArgs) (st st' : SystemState)
    (hInv : capabilityInvariantBundle st)
    (h : untypedRetypeFromCap tid ec srcAddr root? args? st = .ok ((), st')) :
    capabilityInvariantBundle st' :=
  (untypedRetypeFromCap_chain h).preserves
    (fun hP hC => untypedRetypeObject_preserves_capabilityInvariantBundle _ _ _ _ _ _ hP hC) hInv

/-- **WS-BP BP7.1 (the authority fact)**: a frame the resolver answers is one the
caller holds a **readable capability** to, found at MR2's address in the caller's
own CSpace, and it is a frame the store holds at the capability's target.  The
read-only lookup returns the state it was given
(`syscallLookupCap_preserves_state`), so the capability is exhibited at `st`
itself. -/
theorem resolveVSpaceMapFrame_ok_authorised
    (callerTid : SeLe4n.ThreadId) (args : VSpaceMapArgs) (st : SystemState)
    (frameSlot : CSpaceAddr) (frameCap : Capability) (frame : FrameObject)
    (h : resolveVSpaceMapFrame callerTid args st = .ok (frameSlot, frameCap, frame)) :
    ∃ (callerTcb : TCB) (frameObjId : SeLe4n.ObjId),
      st.getTcb? callerTid = some callerTcb ∧
      syscallLookupCap
        { callerId := callerTid, cspaceRootCap := callerTcb.spaceCells[0],
          capAddr := args.frame,
          requiredRight := .read } st = .ok (frameCap, st) ∧
      frameCap.hasRight .read = true ∧
      frameCap.target = .object frameObjId ∧
      st.getFrame? frameObjId = some frame ∧
      lookupSlot callerTcb args.frame st = .ok frameSlot ∧
      SystemState.lookupSlotCap st frameSlot = some frameCap := by
  unfold resolveVSpaceMapFrame syscallLookupArgumentCap at h
  cases hCaller : st.getTcb? callerTid with
  | none => rw [hCaller] at h; cases h
  | some callerTcb =>
    rw [hCaller] at h
    simp only at h
    cases hLk : syscallLookupCap
        { callerId := callerTid, cspaceRootCap := callerTcb.spaceCells[0],
          capAddr := args.frame,
          requiredRight := .read } st with
    | error e => rw [hLk] at h; cases h
    | ok pair =>
      obtain ⟨cap', s'⟩ := pair
      rw [hLk] at h
      simp only at h
      obtain ⟨_, _, _, hRight, hSt⟩ :=
        syscallLookupCap_implies_capability_held _ st cap' s' hLk
      rw [hSt] at hLk
      -- The slot the gate's lookup read the capability from.
      obtain ⟨ref0, hRes0, hLk0, -, -⟩ :=
        syscallLookupCap_implies_capability_held _ st cap' st hLk
      have hSlotOf : ∀ ref, lookupSlot callerTcb args.frame st = .ok ref → SystemState.lookupSlotCap st ref = some cap' := by
        intro ref hRef
        have : ref0 = ref := by
          have h2 : (Except.ok ref0 : Except LookupFault CSpaceAddr) = .ok ref :=
            hRes0.symm.trans hRef
          cases h2; rfl
        subst this; exact hLk0
      cases hTgt : cap'.target
      case object frameObjId =>
        rw [hTgt] at h
        simp only at h
        cases hF : st.getFrame? frameObjId with
        | none => rw [hF] at h; cases h
        | some f =>
          rw [hF] at h
          simp only at h
          cases hRef : lookupSlot callerTcb args.frame st with
          | error e => rw [hRef] at h; cases h
          | ok ref =>
            rw [hRef] at h
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨hS, hCap, hFr⟩ := h
            subst hS; subst hCap; subst hFr
            exact ⟨callerTcb, frameObjId,
              by first | exact hCaller | rfl,
              hLk, hRight, hTgt, hF, hRef, hSlotOf _ hRef⟩
      all_goals (rw [hTgt] at h; cases h)

/-- **WS-BP BP7.1: what a frame capability authorises a mapping to do.**

Two refusals, each the fact a hardware mapping of this frame would otherwise
violate.  (W^X needs no third: the front already refuses a writable-and-
executable request, through `vspaceMapArgsOfWords`.)  A **writable** mapping needs a frame capability carrying `.write` —
the capability bounds the access the mapping grants, as seL4's `maskVMRights`
bounds it; here an over-reaching request is refused rather than silently
narrowed, so a caller learns the mapping it asked for is not the one it holds
authority for.

And a mapping carries **the frame's own memory type** (`.policyDenied`, the
error `validateVSpaceMapPermsForMemoryKind` already returns for a device
execute).  A **device** frame is mapped uncached and never executable
(execution from Device memory is unpredictable on ARMv8, and a device register
read through a cache line is not a device access).  A **RAM** frame is mapped
cacheable, and only cacheable (the WS-BP post-landing audit, `v0.36.32`): the
kernel's identity map aliases every page of RAM as Normal write-back, and a
thread's uncached mapping of the same page — which `userPageAttributes` encodes
as Device-nGnRnE — is the **mismatched-attribute** alias ARM ARM B2.8 says
loses coherency.  It was a leak, not a curiosity: the carve zeroes a frame
through the cacheable alias, so the zeroes can sit dirty in the data cache
while DRAM still holds the page's previous owner's bytes, and an uncached read
goes past the cache to DRAM — reporting to the new owner what the previous one
wrote.  With the memory type fixed by the frame, no thread holds a second
memory type for a page of RAM, and the only uncached mappings are of device
memory, which the kernel never writes (`HardwareTables.lean`'s module
docstring states the encoding this makes exact).  A thread that needs RAM
shared with a non-coherent bus master has no such master to share it with:
the model admits none (`CoherentAgent`'s tripwire), and adding one is where
the buffer protocol belongs. -/
def frameMappingAdmissible (frameCap : Capability) (frame : FrameObject)
    (perms : PagePermissions) : Except KernelError Unit :=
  if perms.write && !frameCap.hasRight .write then .error .illegalAuthority
  else if perms.cacheable == frame.isDevice || (frame.isDevice && perms.execute) then
    .error .policyDenied
  else .ok ()

/-- **WS-BP BP7.1**: an admitted writable mapping is backed by a writable frame
capability. -/
theorem frameMappingAdmissible_write (frameCap : Capability) (frame : FrameObject)
    (perms : PagePermissions) (h : frameMappingAdmissible frameCap frame perms = .ok ())
    (hW : perms.write = true) : frameCap.hasRight .write = true := by
  unfold frameMappingAdmissible at h
  cases hR : frameCap.hasRight .write
  · simp [hW, hR] at h
  · rfl

/-- **WS-BP BP7.1**: an admitted mapping of a device frame is neither executable
nor cacheable. -/
theorem frameMappingAdmissible_device (frameCap : Capability) (frame : FrameObject)
    (perms : PagePermissions) (h : frameMappingAdmissible frameCap frame perms = .ok ())
    (hDev : frame.isDevice = true) : perms.execute = false ∧ perms.cacheable = false := by
  unfold frameMappingAdmissible at h
  split at h
  · cases h
  · rw [hDev] at h
    cases hE : perms.execute <;> cases hC : perms.cacheable <;> simp_all

/-- **WS-BP post-landing audit (`v0.36.32`)**: an admitted mapping of a RAM frame
is cacheable — the memory type the kernel's own identity map gives every page
of RAM, so no thread's mapping aliases a page of RAM with a second memory type.
This is the fact that makes the carve's zeroing through the kernel's cacheable
alias what every later read of the page observes. -/
theorem frameMappingAdmissible_ram (frameCap : Capability) (frame : FrameObject)
    (perms : PagePermissions) (h : frameMappingAdmissible frameCap frame perms = .ok ())
    (hRam : frame.isDevice = false) : perms.cacheable = true := by
  unfold frameMappingAdmissible at h
  split at h
  · cases h
  · rw [hRam] at h
    cases hC : perms.cacheable <;> simp_all

/-- **WS-BP post-landing audit (`v0.36.32`)**: every admitted mapping's
cacheability **is** its frame's memory type — cacheable exactly when the frame
is RAM.  `frameMappingAdmissible_device` and `frameMappingAdmissible_ram` are
its two halves; this is the statement a consumer reasoning about memory types
reads. -/
theorem frameMappingAdmissible_cacheable_iff_ram (frameCap : Capability)
    (frame : FrameObject) (perms : PagePermissions)
    (h : frameMappingAdmissible frameCap frame perms = .ok ()) :
    perms.cacheable = !frame.isDevice := by
  cases hDev : frame.isDevice
  · exact frameMappingAdmissible_ram frameCap frame perms h hDev
  · exact (frameMappingAdmissible_device frameCap frame perms h hDev).2

/-- The object a frame capability names — `resolveVSpaceMapFrame` admits only a
capability naming an object, so the fallback is never taken on the map path. -/
def frameCapObjId (cap : Capability) : SeLe4n.ObjId :=
  match cap.target with
  | .object id => id
  | _ => SeLe4n.ObjId.sentinel

/-- **WS-BP BP7.1: the `.vspaceMap` arm past its address-space check, named.**

Resolve the invoked frame capability (`resolveVSpaceMapFrame`), check what
that capability authorises the mapping to be (`frameMappingAdmissible`), check
the frame's address against the platform memory map
(`validateVSpaceMapPermsForMemoryKind`), and install the frame's own `base`
through the per-core shootdown wrapper.  Named so the arm and every theorem
about it read one definition: `vspaceMapFromFrameCap_ok` is the decomposition
each consumer takes instead of re-splitting four matches. -/
def vspaceMapFromFrameCap (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (args : VSpaceMapArgs) : Kernel Unit :=
  fun st =>
    match resolveVSpaceMapFrame tid args st with
    | .error e => .error e
    | .ok (frameSlot, frameCap, frame) =>
      match frameMappingAdmissible frameCap frame args.perms with
      | .error e => .error e
      | .ok () =>
        -- WS-BP BP7.1 (`v0.36.7`): a frame capability maps its frame once, as
        -- in seL4 — a capability whose recorded mapping is still in place is
        -- refused; mapping the frame again takes a copy of the capability,
        -- which carries no record.  A record gone stale (its address space
        -- unmapped the address, or was destroyed) is simply overwritten.
        -- WS-BP BP7.2: a thread maps only inside the user window — level-0
        -- entry 0 of every user root is the kernel's own window, installed
        -- beside the thread's tables in `TTBR0_EL1`.
        if !args.vaddr.inUserWindow then .error .addressOutOfBounds
        else if capabilityMappingLive st frameCap then
          .error (.invalidCapability vspaceMapFrameCapNumber)
        -- WS-BP BP7.1 (`v0.36.12`): a carved address space maps a frame only
        -- where every level of its walk is present — seL4's
        -- `seL4_FailedLookup` from `seL4_ARM_Page_Map` when a table is missing.
        else if !Architecture.asidTranslationReady st args.asid args.vaddr then
          .error .translationFault
        else
        -- AH1-D (M-01 fix): Validate permissions against memory kind before mapping.
        -- Device regions must not receive execute permission (undefined on ARM64).
        match validateVSpaceMapPermsForMemoryKind frame.base args.perms
                st.machine.memoryMap with
        | .error e => .error e
        | .ok perms =>
          -- X2-E: Use state-aware PA bounds (reads physicalAddressWidth from machine state)
          -- WS-SM SM7.B.9: a remap that replaces a live translation
          -- leaves the old one cached on remote cores — the wrapper
          -- adds the cross-core shootdown round to the local flush.
          -- WS-SM SM7.F.4(a)+(b)(ii): route through the per-core wrapper,
          -- which additionally (a) caches the freshly-established
          -- translation on the executing core's `perCoreTlb` view — the
          -- live *fill* that finally holds a real entry on the syscall
          -- path — and (b) retires any stale initiator entry atomically.
          -- Trace-safe: both are `perCoreTlb`-only, ∉ `projectState`.
          match Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore
              executingCore args.asid args.vaddr frame.base perms st with
          | .error e => .error e
          | .ok ((), st1) =>
            -- PR #904 review (`v0.36.41`): the mapping takes the frame's next
            -- epoch, written beside the translation, so the record below names
            -- this mapping and no later one (`mappedPageLive`).
            match tagFrameMapping args.asid args.vaddr (frameCapObjId frameCap) st1 with
            | .error e => .error e
            | .ok (epoch, st2) =>
            -- WS-BP BP7.1 (`v0.36.7`): the mapping now belongs to the
            -- capability that made it — recorded on it, in its own slot, so
            -- destroying the capability removes it (`cspaceDeleteSlotFinalising`,
            -- `cspaceRevokeCdtFinalising`).
            cspaceRecordFrameMapping frameSlot
              { asid := args.asid, vaddr := args.vaddr, epoch := epoch } st2

/-- **WS-BP BP7.1**: a successful frame-capability mapping resolved a frame the
caller holds a capability to, admitted the requested permissions, and installed
**that frame's** `base` with them — the decomposition every consumer of the arm
reads. -/
theorem vspaceMapFromFrameCap_ok (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (args : VSpaceMapArgs)
    (st st' : SystemState)
    (h : vspaceMapFromFrameCap tid executingCore args st = .ok ((), st')) :
    ∃ (frameSlot : CSpaceAddr) (frameCap : Capability) (frame : FrameObject)
      (st1 : SystemState),
      resolveVSpaceMapFrame tid args st = .ok (frameSlot, frameCap, frame) ∧
      frameMappingAdmissible frameCap frame args.perms = .ok () ∧
      capabilityMappingLive st frameCap = false ∧
      Architecture.asidTranslationReady st args.asid args.vaddr = true ∧
      validateVSpaceMapPermsForMemoryKind frame.base args.perms st.machine.memoryMap
        = .ok args.perms ∧
      Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore
        executingCore args.asid args.vaddr frame.base args.perms st
        = .ok ((), st1) ∧
      ∃ (epoch : Nat) (st2 : SystemState),
        tagFrameMapping args.asid args.vaddr (frameCapObjId frameCap) st1 = .ok (epoch, st2) ∧
        cspaceRecordFrameMapping frameSlot
          { asid := args.asid, vaddr := args.vaddr, epoch := epoch } st2 = .ok ((), st') := by
  unfold vspaceMapFromFrameCap at h
  cases hR : resolveVSpaceMapFrame tid args st with
  | error e => rw [hR] at h; cases h
  | ok triple =>
    obtain ⟨frameSlot, frameCap, frame⟩ := triple
    rw [hR] at h
    simp only at h
    cases hA : frameMappingAdmissible frameCap frame args.perms with
    | error e => rw [hA] at h; cases h
    | ok u =>
      cases u
      rw [hA] at h
      simp only at h
      cases hW : args.vaddr.inUserWindow
      · rw [hW] at h; simp at h
      rw [hW] at h
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases hLive : capabilityMappingLive st frameCap
      · rw [hLive] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        cases hReady : Architecture.asidTranslationReady st args.asid args.vaddr
        · rw [hReady] at h; simp at h
        rw [hReady] at h
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        cases hV : validateVSpaceMapPermsForMemoryKind frame.base args.perms
            st.machine.memoryMap with
        | error e => rw [hV] at h; cases h
        | ok perms =>
          rw [hV] at h
          have hEq := validateVSpaceMapPermsForMemoryKind_ok_eq _ _ _ _ hV
          subst hEq
          simp only at h
          cases hM : Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore
              executingCore args.asid args.vaddr frame.base args.perms st with
          | error e => rw [hM] at h; cases h
          | ok pr =>
            obtain ⟨u, st1⟩ := pr; cases u
            rw [hM] at h
            simp only at h
            cases hT : tagFrameMapping args.asid args.vaddr (frameCapObjId frameCap) st1 with
            | error e => rw [hT] at h; cases h
            | ok pr =>
              obtain ⟨epoch, st2⟩ := pr
              rw [hT] at h
              exact ⟨frameSlot, frameCap, frame, st1, by first | exact hR | rfl,
                by first | exact hA | rfl, hLive, rfl, hV, by first | exact hM | rfl,
                epoch, st2, hT, h⟩
      · rw [hLive] at h; simp at h

/-- **WS-BP BP7.2: a successful mapping is inside the user window** — the arm
refuses an address below `VAddr.userWindowBase`, whose walk would enter the
level-0 slot every user root gives to the kernel's own window. -/
theorem vspaceMapFromFrameCap_ok_inUserWindow (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (args : VSpaceMapArgs)
    (st st' : SystemState) (h : vspaceMapFromFrameCap tid executingCore args st = .ok ((), st')) :
    args.vaddr.inUserWindow = true := by
  unfold vspaceMapFromFrameCap at h
  cases hR : resolveVSpaceMapFrame tid args st with
  | error e => rw [hR] at h; cases h
  | ok triple =>
    obtain ⟨frameSlot, frameCap, frame⟩ := triple
    rw [hR] at h
    simp only at h
    cases hA : frameMappingAdmissible frameCap frame args.perms with
    | error e => rw [hA] at h; cases h
    | ok u =>
      rw [hA] at h
      simp only at h
      cases hW : args.vaddr.inUserWindow
      · rw [hW] at h; simp at h
      · rfl

/-- **WS-BP BP7.1 (`v0.36.7`): a successful mapping records itself on the
capability that made it** — the slot the capability was resolved from now holds
it with the mapping record `⟨asid, vaddr, epoch⟩`, so destroying it removes the
mapping.  The epoch (PR #904 review, `v0.36.41`) is the one the address space's
entry now carries, which is what makes the record this mapping's alone. -/
theorem vspaceMapFromFrameCap_ok_records (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (args : VSpaceMapArgs)
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (h : vspaceMapFromFrameCap tid executingCore args st = .ok ((), st')) :
    ∃ (frameSlot : CSpaceAddr) (frameCap : Capability) (epoch : Nat),
      SystemState.lookupSlotCap st frameSlot = some frameCap ∧
      SystemState.lookupSlotCap st' frameSlot =
        some (frameCap.withMapping (some { asid := args.asid, vaddr := args.vaddr, epoch := epoch })) := by
  obtain ⟨frameSlot, frameCap, frame, st1, hR, -, -, -, -, hMap, epoch, st2, hT, hRec⟩ :=
    vspaceMapFromFrameCap_ok tid executingCore args st st' h
  obtain ⟨_, _, _, _, _, _, _, -, hSlotCap⟩ :=
    resolveVSpaceMapFrame_ok_authorised tid args st frameSlot frameCap frame hR
  refine ⟨frameSlot, frameCap, epoch, hSlotCap, ?_⟩
  obtain ⟨cn, cap, hCn, hLk, hStore⟩ := cspaceRecordFrameMapping_ok_decompose _ _ st2 st' hRec
  obtain ⟨hInv1, hW, -⟩ :=
    vspaceMapPageCheckedWithShootdownFromStatePerCore_ok_frame _ _ _ _ _ st st1 hObjInv hMap
  obtain ⟨hInv2, -, -, hTagW⟩ := tagFrameMapping_ok_frame _ _ _ st1 st2 epoch hInv1 hT
  have hAt := storeObject_objects_eq st2 st' frameSlot.cnode _ hInv2 hStore
  -- The map writes VSpace roots only and the tag a root and a frame, so the slot
  -- held the resolved capability at `st` too.
  have hCn2 := (SystemState.getCNode?_eq_some_iff st2 frameSlot.cnode cn).mp hCn
  have hCn1 : st1.objects[frameSlot.cnode]? = some (.cnode cn) := by
    rcases hTagW frameSlot.cnode with e | ⟨-, ⟨r, hr⟩⟩ | ⟨-, ⟨g, hg⟩⟩
    · rw [← e]; exact hCn2
    · rw [hCn2] at hr; cases hr
    · rw [hCn2] at hg; cases hg
  have hCnPre : st.objects[frameSlot.cnode]? = some (.cnode cn) := by
    rw [← hW.eq_of_not_root' (fun r hr => by rw [hCn1] at hr; cases hr)]
    exact hCn1
  have hCapEq : cap = frameCap := by
    unfold SystemState.lookupSlotCap SystemState.lookupCNode at hSlotCap
    rw [hCnPre] at hSlotCap
    simp only at hSlotCap
    rw [hLk] at hSlotCap
    exact Option.some.inj hSlotCap
  subst hCapEq
  unfold SystemState.lookupSlotCap SystemState.lookupCNode
  rw [hAt]
  simp only
  exact CNode.lookup_insert_eq cn frameSlot.slot _ (CNode.slotsUnique_holds cn)
    (CNode.slotAddressable_of_lookup cn _ _ hLk)

/-- **The remap's refusals, in seL4's order, read before any write.**  seL4's
`decodeARMFrameInvocation` (`ARMPageMap`) decides every refusal of a remap
before `performPageInvocationMap` writes anything: the address space the call
names must resolve (`findVSpaceForASID`, here `.asidNotBound`), the address must
be page-aligned (`checkVPAlignment`, `.alignmentError`), the capability's record
must name that address space (`.invalidCapability`) and that address
(`.invalidArgument`), and the walk to the address must be complete
(`lookupPTSlot`'s `ptBitsLeft`, here `.translationFault`).  After them come the
checks this kernel adds to the decode, in the fresh mapping's order: the rights
the capability grants and the memory type (`frameMappingAdmissible`), the user
window, the frame's memory kind, the canonical address and the physical-address
width, and W^X.  Every check the fresh mapping makes is here except the two the
unmap clears (the capability's live record and the address already mapped), so
a remap that passes these is refused by nothing the unmap leaves behind. -/
@[inline] def vspaceRemapRefusal (st : SystemState) (args : VSpaceMapArgs) (frameCap : Capability)
    (frame : FrameObject) : Except KernelError Unit :=
  match Architecture.resolveAsidRoot st args.asid with
  | none => .error .asidNotBound
  | some (_, root) =>
    if !Architecture.pageMappingAligned args.vaddr frame.base then .error .alignmentError
    else if frameCap.mapAsid != args.asid then .error (.invalidCapability pageMapVSpaceCapNumber)
    else if frameCap.mapVaddr != args.vaddr then .error (.invalidArgument 0)
    else if !root.translationReady args.vaddr then .error .translationFault
    else
      match frameMappingAdmissible frameCap frame args.perms with
      | .error e => .error e
      | .ok () =>
        if !args.vaddr.inUserWindow then .error .addressOutOfBounds
        else
          match validateVSpaceMapPermsForMemoryKind frame.base args.perms st.machine.memoryMap with
          | .error e => .error e
          | .ok _ =>
            if !args.vaddr.isCanonical then .error .addressOutOfBounds
            else if !(frame.base.toNat < 2 ^ st.machine.physicalAddressWidth) then
              .error .addressOutOfBounds
            else if !args.perms.wxCompliant then .error .policyDenied
            else .ok ()

/-- **WS-SX SX6.3 (D6): `seL4_ARM_Page_Map`'s address space and operands.**
The address space is extra capability 0 (`vspaceRootCap =
current_extra_caps.excaprefs[0]->cap`), resolved through the caller's own
CSpace with `.write` as `PageTable_Map`'s is (a lookup refusal numbered as
argument capability 0, `pageMapVSpaceCapNumber`).  In
`decodeARMFrameInvocation`'s order: a capability naming no address space is
`isValidNativeRoot`'s refusal, `invalidCapability 1`; the root's own ASID
(`capVSMappedASID`) must resolve (`findVSpaceForASID`, `.asidNotBound`) and to
this root (`find_ret.vspace_root != vspaceRoot`, `invalidCapability 1`); then
the address is tested (`vspaceMapArgsOfWords`).  The answer is the root and
the operands the map arm acts on, its ASID the root's own and its frame the
invoked capability `frameCPtr`. -/
def resolvePageMapOperands (tid : SeLe4n.ThreadId) (frameCPtr rootCPtr : SeLe4n.CPtr)
    (words : PageMapArgs) (st : SystemState) :
    Except KernelError (SeLe4n.ObjId × VSpaceMapArgs) :=
  match resolveCallerCapObject tid rootCPtr .write st with
  | .error e => .error (e.forArgumentCap pageMapVSpaceCapNumber)
  | .ok (_, rootId) =>
    match st.getVSpaceRoot? rootId with
    | none => .error (.invalidCapability pageMapVSpaceCapNumber)
    | some root =>
      match Architecture.resolveAsidRoot st root.asid with
      | none => .error .asidNotBound
      | some (boundId, _) =>
        if boundId != rootId then .error (.invalidCapability pageMapVSpaceCapNumber)
        else
          match vspaceMapArgsOfWords words root.asid frameCPtr with
          | .error e => .error e
          | .ok args => .ok (rootId, args)

/-- `resolvePageMapOperands` in continuation form, through
`resolveCallerCapObjectK`: no capability pair, root pair or result pair is
built (`resolvePageMapOperandsK_eq`). -/
@[inline] def resolvePageMapOperandsK {α : Type} (tid : SeLe4n.ThreadId)
    (frameCPtr rootCPtr : SeLe4n.CPtr) (words : PageMapArgs) (st : SystemState)
    (onErr : KernelError → α) (onOk : SeLe4n.ObjId → VSpaceMapArgs → α) : α :=
  resolveCallerCapObjectK tid rootCPtr .write st
    (KernelError.argumentCapRefusal pageMapVSpaceCapNumber onErr)
    (fun _ rootId =>
      match st.getVSpaceRoot? rootId with
      | none => onErr (.invalidCapability pageMapVSpaceCapNumber)
      | some root =>
        match Architecture.resolveAsidRoot st root.asid with
        | none => onErr .asidNotBound
        | some (boundId, _) =>
          if boundId != rootId then onErr (.invalidCapability pageMapVSpaceCapNumber)
          else
            match vspaceMapArgsOfWords words root.asid frameCPtr with
            | .error e => onErr e
            | .ok args => onOk rootId args)

theorem resolvePageMapOperandsK_eq {α : Type} (tid : SeLe4n.ThreadId)
    (frameCPtr rootCPtr : SeLe4n.CPtr) (words : PageMapArgs) (st : SystemState)
    (onErr : KernelError → α) (onOk : SeLe4n.ObjId → VSpaceMapArgs → α) :
    resolvePageMapOperandsK tid frameCPtr rootCPtr words st onErr onOk =
      match resolvePageMapOperands tid frameCPtr rootCPtr words st with
      | .error e => onErr e
      | .ok (rootId, args) => onOk rootId args := by
  unfold resolvePageMapOperandsK resolvePageMapOperands
  rw [resolveCallerCapObjectK_eq]
  cases resolveCallerCapObject tid rootCPtr .write st with
  | error e => rfl
  | ok p =>
    obtain ⟨_, rootId⟩ := p
    simp only []
    cases st.getVSpaceRoot? rootId with
    | none => rfl
    | some root =>
      simp only []
      cases Architecture.resolveAsidRoot st root.asid with
      | none => rfl
      | some pr =>
        obtain ⟨boundId, _⟩ := pr
        simp only []
        split
        · rfl
        · cases vspaceMapArgsOfWords words root.asid frameCPtr <;> rfl

/-- **What an admitted `seL4_ARM_Page_Map` front answers**: the root is one the
caller holds a writable capability to, a VSpace root in the store, the one its
own ASID resolves to (`vspaceCapAuthorizesAsid` holds of that capability and
the operands' ASID), and the operands name the invoked frame capability. -/
theorem resolvePageMapOperands_ok {tid : SeLe4n.ThreadId} {frameCPtr rootCPtr : SeLe4n.CPtr}
    {words : PageMapArgs} {st : SystemState} {rootId : SeLe4n.ObjId} {args : VSpaceMapArgs}
    (h : resolvePageMapOperands tid frameCPtr rootCPtr words st = .ok (rootId, args)) :
    ∃ rootCap root,
      resolveCallerCapObject tid rootCPtr .write st = .ok (rootCap, rootId) ∧
      st.getVSpaceRoot? rootId = some root ∧ args.asid = root.asid ∧
      args.frame = frameCPtr ∧
      ∃ r, Architecture.resolveAsidRoot st args.asid = some (rootId, r) := by
  unfold resolvePageMapOperands at h
  cases hR : resolveCallerCapObject tid rootCPtr .write st with
  | error e => rw [hR] at h; cases h
  | ok p =>
    obtain ⟨rootCap, rid⟩ := p
    rw [hR] at h
    simp only at h
    cases hV : st.getVSpaceRoot? rid with
    | none => rw [hV] at h; cases h
    | some root =>
      rw [hV] at h
      simp only at h
      cases hA : Architecture.resolveAsidRoot st root.asid with
      | none => rw [hA] at h; cases h
      | some pr =>
        obtain ⟨boundId, r⟩ := pr
        rw [hA] at h
        simp only at h
        split at h
        · cases h
        · rename_i hB
          have hEq : boundId = rid := by simpa using hB
          cases hW : vspaceMapArgsOfWords words root.asid frameCPtr with
          | error e => rw [hW] at h; cases h
          | ok a =>
            rw [hW] at h
            cases h
            unfold vspaceMapArgsOfWords at hW
            split at hW
            · cases hW
            · split at hW
              · cases hW
              · cases hW
                exact ⟨rootCap, root, rfl, hV, rfl, rfl, r, by rw [hA, hEq]⟩

/-- **`seL4_ARM_Page_Map` on a frame capability: a fresh mapping, or a remap.**
seL4's `decodeARMFrameInvocation` takes a capability whose recorded mapping is
in place as a remap, and decides all of its refusals before it writes
(`vspaceRemapRefusal`): a refused remap changes nothing
(`vspaceMapOrRemapFromFrameCap_of_remapRefused`).  The remap's writes are the
mapping taken down where it stands
(`vspaceUnmapPageWithShootdownAndIcacheBroadcast`: the invalid descriptor, the
flush and the shootdown round, so no core keeps the old rights) and the frame
mapped again in its place (`vspaceMapFromFrameCap`, which records the new
mapping on the same capability).  Either half refusing refuses the whole call,
which then writes nothing; on a store the checks admit, neither does
(`vspaceMapOrRemapFromFrameCap_of_remapAdmitted`).  A capability whose record
has gone stale, or that records none, maps as a fresh mapping. -/
def vspaceMapOrRemapFromFrameCap (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (args : VSpaceMapArgs) : Kernel Unit :=
  fun st =>
    match resolveVSpaceMapFrame tid args st with
    | .error e => .error e
    | .ok (_, frameCap, frame) =>
      if capabilityMappingLive st frameCap then
        match vspaceRemapRefusal st args frameCap frame with
        | .error e => .error e
        | .ok () =>
          match Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast executingCore
              args.asid args.vaddr st with
          | .error e => .error e
          | .ok ((), st0) => vspaceMapFromFrameCap tid executingCore args st0
      else vspaceMapFromFrameCap tid executingCore args st

/-- **A refused remap changes nothing**: a capability whose mapping is in place,
refused by the remap's checks, is refused on the state the call was made in,
before the unmap writes anything. -/
theorem vspaceMapOrRemapFromFrameCap_of_remapRefused (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (args : VSpaceMapArgs) (st : SystemState)
    (frameSlot : CSpaceAddr) (frameCap : Capability) (frame : FrameObject) (e : KernelError)
    (hRes : resolveVSpaceMapFrame tid args st = .ok (frameSlot, frameCap, frame))
    (hLive : capabilityMappingLive st frameCap = true)
    (hR : vspaceRemapRefusal st args frameCap frame = .error e) :
    vspaceMapOrRemapFromFrameCap tid executingCore args st = .error e := by
  unfold vspaceMapOrRemapFromFrameCap
  simp only [hRes, hLive, ↓reduceIte, hR]

/-- **What a successful map or remap consists of**: a fresh mapping from the
pre-state, or the unmap of the address the capability records followed by a
fresh mapping from the state it leaves. -/
theorem vspaceMapOrRemapFromFrameCap_cases {tid : SeLe4n.ThreadId}
    {executingCore : Concurrency.CoreId} {args : VSpaceMapArgs} {st st' : SystemState}
    (h : vspaceMapOrRemapFromFrameCap tid executingCore args st = .ok ((), st')) :
    vspaceMapFromFrameCap tid executingCore args st = .ok ((), st') ∨
      ∃ st0, Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast executingCore
          args.asid args.vaddr st = .ok ((), st0) ∧
        vspaceMapFromFrameCap tid executingCore args st0 = .ok ((), st') := by
  unfold vspaceMapOrRemapFromFrameCap at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · split at h
        · cases h
        · next st0 hU => exact .inr ⟨st0, hU, h⟩
    · exact .inl h

/-- **A property both the unmap and a fresh mapping keep, and that composes,
holds across a map or remap.** -/
theorem vspaceMapOrRemapFromFrameCap_closed {tid : SeLe4n.ThreadId}
    {executingCore : Concurrency.CoreId} {args : VSpaceMapArgs} {st st' : SystemState}
    (R : SystemState → SystemState → Prop)
    (hMap : ∀ s s', vspaceMapFromFrameCap tid executingCore args s = .ok ((), s') → R s s')
    (hUnmap : ∀ s s', Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast executingCore
      args.asid args.vaddr s = .ok ((), s') → R s s')
    (hTrans : ∀ a b c, R a b → R b c → R a c)
    (h : vspaceMapOrRemapFromFrameCap tid executingCore args st = .ok ((), st')) :
    R st st' := by
  rcases vspaceMapOrRemapFromFrameCap_cases h with hM | ⟨st0, hU, hM⟩
  · exact hMap _ _ hM
  · exact hTrans _ _ _ (hUnmap _ _ hU) (hMap _ _ hM)

/-- V8-H/Z5-J/D1/AE1-A/AE1-B: Shared dispatch for capability-only syscalls — these arms
derive authority entirely from capability possession and require no
information-flow checks. `dispatchWithCapChecked` delegates to this helper
for: `.cspaceDelete`, `.vspaceMap`,
`.vspaceUnmap`, `.serviceRevoke`, `.serviceQuery`, `.schedContextConfigure`,
`.schedContextBind`, `.schedContextUnbind`, `.tcbSuspend`, `.tcbResume`,
`.tcbSetPriority` (AE1-A), `.tcbSetMCPriority` (AE1-A), `.tcbSetIPCBuffer` (AE1-B).

Returns `none` if the syscall ID is not a capability-only arm (i.e., it
requires IPC/cross-domain handling). -/
def dispatchCapabilityOnly (decoded : SyscallDecodeResult)
    (cap : Capability) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) :
    Option (Kernel Unit) :=
  match decoded.syscallId with
  | .cspaceDelete =>
    some <| match cap.target with
    | .object cnodeId =>
        fun st => match decodeCSpaceDeleteArgs decoded with
        | .error e => .error e
        | .ok args =>
            if !cnodeInvoked cnodeId st then .error .objectNotFound else
            let addr : CSpaceAddr := { cnode := cnodeId, slot := args.targetSlot }
            -- WS-BP BP7.1 (`v0.36.7`): the finalising delete — seL4's
            -- `cteDelete` → `finaliseCap`: a frame capability's recorded
            -- mapping is removed with it, through the `.vspaceUnmap` arm's own
            -- transition, the invoking thread's core initiating the shootdown.
            cspaceDeleteSlotZombie executingCore addr st
    | _ => fun _ => .error (.invalidCapability 0)
  -- **WS-RR RR8.16 (`v0.35.190`)**: `seL4_CNode_Revoke`, the arm the
  -- revocation family had never had.
  --
  -- Three things this arm decides.  It destroys exactly the source's CDT
  -- descendants, in every CNode, which is seL4's `cteRevoke` (read at
  -- `13.0.0`): the local `cspaceRevoke` reaches only the containing CNode, so a
  -- derived capability copied into any other CSpace would survive it, and it
  -- matches on the **target**, so it also destroys capabilities that are not
  -- derivations at all.  Since WS-ZA ZA5.3 part 8 (`v0.36.111`) the revocation is
  -- `cteRevoke`'s own loop, `cspaceRevokeCdtFinalising`: the source's first child
  -- deleted and finalised until it has none.  It takes the **delete's** ABI
  -- (`decodeCSpaceDeleteArgs`, one message register naming the slot), since both
  -- name one slot of the invoked CNode and a second decoder for one operand is a
  -- spelling nobody needs.  And the source slot **survives**: revocation destroys
  -- the derivations of a capability, not the capability itself, which is what
  -- distinguishes it from the delete.
  | .cspaceRevoke =>
    some <| match cap.target with
    | .object cnodeId =>
        fun st => match decodeCSpaceDeleteArgs decoded with
        | .error e => .error e
        | .ok args =>
            if !cnodeInvoked cnodeId st then .error .objectNotFound else
            let addr : CSpaceAddr := { cnode := cnodeId, slot := args.targetSlot }
            -- WS-BP BP7.1 (`v0.36.7`): the finalising revocation — every
            -- mapping a destroyed frame capability recorded is removed with it.
            cspaceRevokeCdtFinalising executingCore addr st
    | _ => fun _ => .error (.invalidCapability 0)
  -- PR #822 Phase H: mint a reply cap from an `.object`-to-Reply cap.  Two slots of the
  -- invoked CNode (`decodeMintReplyCapArgs`); the cap names the CNode, and
  -- `mintReplyCapWithCdt` derives `.replyCap (ReplyId.ofObjId target)` at the dst slot
  -- (fail-closed when the src is not an `.object`-to-Reply cap).  CDT-tracked so the
  -- minted reply cap is revocable through `.cspaceRevoke`.
  | .mintReplyCap =>
    some <| match cap.target with
    | .object cnodeId =>
        fun st => match decodeMintReplyCapArgs decoded with
        | .error e => .error e
        | .ok args =>
            if !cnodeInvoked cnodeId st then .error .objectNotFound else
            let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
            let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
            mintReplyCapWithCdt src dst st
    | _ => fun _ => .error (.invalidCapability 0)
  -- **WS-BP BP7.1 (`v0.36.5`)**: `seL4_Untyped_Retype` — the only path by
  -- which an object comes to exist on a live state (since WS-ZA ZA5.4 part 14
  -- every kind, as in seL4): the caller presents an untyped capability, names a
  -- fresh object id, a destination root as extra capability 0 and a window in
  -- the CNode under it (WS-SX SX6.3, D9), and receives a capability to the
  -- object carved at that capability's free index.
  -- `.vspaceMap` maps a carved frame and no other page.
  | .untypedRetype =>
    some <| match cap.target with
    | .object _ => fun st =>
        untypedRetypeFromCap tid executingCore decoded.capAddr
          (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0)
          (decodeUntypedRetypeArgs decoded) st
    | _ => fun _ => .error (.invalidCapability 0)
  -- **WS-SX SX6.3 (D6)**: `seL4_ARM_Page_Map` is an invocation of the frame
  -- capability: the words are the address, the rights and the attributes
  -- (`decodePageMapArgs`), and the address space is extra capability 0, a
  -- message naming none refused `.truncatedMessage` as seL4 refuses a null
  -- `excaprefs[0]`.  The root must be the one its own ASID resolves to
  -- (`resolvePageMapOperands`), so the mapping's address space is the
  -- capability's, never a name the caller chose (the confused deputy PR #845
  -- closed); the page mapped is the invoked frame's, its address the frame's
  -- own `base`.
  | .vspaceMap =>
    some <| match cap.target with
    | .object _ =>
        fun st =>
          match decodePageMapArgs decoded with
          | .error e => .error e
          | .ok words =>
            match callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0 with
            | none => .error .truncatedMessage
            | some rootCPtr =>
              match resolvePageMapOperands tid decoded.capAddr rootCPtr words st with
              | .error e => .error e
              | .ok (_, args) => vspaceMapOrRemapFromFrameCap tid executingCore args st
    | _ => fun _ => .error (.invalidCapability 0)
  -- `seL4_ARM_Page_Unmap` is an invocation of the frame capability and reads
  -- no message word (seL4's `decodeARMFrameInvocation`, `ARMPageUnmap`): the
  -- mapping taken down is the one the capability records, and the capability
  -- then records none (`vspaceUnmapFrameCap`, seL4's
  -- `performPageInvocationUnmap`).  The slot is the one the invoked address
  -- resolves to in the caller's CSpace, where the record is kept.  The
  -- teardown goes through `vspaceUnmapPageWithShootdownAndIcacheBroadcast`, so
  -- every core's TLB entry and, for an executable mapping, every instruction
  -- cache line for the page is retired with it (WS-SM SM7.B.9, SM7.D.1).
  | .vspaceUnmap =>
    some <| match cap.target with
    | .object _ =>
        fun st =>
          match resolveCallerCapSlot tid decoded.capAddr (syscallRequiredRight .vspaceUnmap) st with
          | .error e => .error e
          | .ok (slot, _, _) => vspaceUnmapFrameCap executingCore slot st
    | _ => fun _ => .error (.invalidCapability 0)
  | .vspaceUnifyInstruction =>
    some <| match cap.target with
    | .object _ =>
        -- WS-SM SM7.D: publish freshly-written code — seLe4n's equivalent of
        -- seL4's `Page_Unify_Instruction`.  After a loader or JIT writes
        -- instructions through a *data* mapping, the stores sit in the data
        -- cache while an instruction fetch reads at the Point of Unification,
        -- so without an explicit `DC CVAU` → `DSB` → `IC IVAU` → `DSB` → `ISB`
        -- the fetch may observe the old content — even on the PE that wrote it.
        -- The kernel cannot do this implicitly: it cannot know when a writer
        -- has finished emitting code, and a JIT patching an already-mapped page
        -- never re-enters a mapping operation at all.  The operand is recorded
        -- domain-wide, because a remote PE may hold lines from a previous
        -- incarnation of the same physical page.
        fun st => match decodeVSpaceUnifyInstructionArgs decoded st.machine.maxASID with
        | .error e => .error e
        | .ok args =>
          -- PR #845 review (P1): bind the capability to the operand address
          -- space.  Without this a holder of any writable object capability
          -- could run cache maintenance against — and so probe the mapping
          -- structure of — an arbitrary address space.
          if !vspaceCapAuthorizesAsid cap args.asid st then
            .error .illegalAuthority
          else
            Architecture.vspaceUnifyInstructionPage args.asid args.vaddr st
    | _ => fun _ => .error (.invalidCapability 0)
  | .serviceRevoke =>
    -- The revoke removes the registration the endpoint records: the
    -- service-registry capability and the capability to the endpoint, extra
    -- capability 0 (WS-SX SX6.7, `resolveServiceEndpoint`), are the
    -- authority, and no service id is read from the caller's registers
    -- (`revokeServiceByRecordedRegistration`).
    some <| match cap.target with
    | .serviceRegistry _ =>
      serviceEndpointArm .serviceRevoke tid decoded.msgInfo.extraCaps fun _ epId st =>
        revokeServiceByRecordedRegistration epId st
    | _ => fun _ => .error (.invalidCapability 0)
  | .serviceQuery =>
    some <| match cap.target with
    | .serviceRegistry _ =>
      serviceEndpointArm .serviceQuery tid decoded.msgInfo.extraCaps fun _ epId st =>
        match lookupServiceByRecordedRegistration epId st with
        | .ok (reg, st') =>
            -- WS-RA RA.B.7: the query answers — the resolved registration's
            -- `ServiceId` is staged as the caller's return word instead of
            -- being discarded (`x0` = sid, success `x1`, no message
            -- registers).  The lookup itself is read-only (`st' = st`).
            .ok ((), Architecture.writeCallReturnWord st' tid reg.sid.val.toUInt64)
        | .error e => .error e
    | _ => fun _ => .error (.invalidCapability 0)
  -- Z5-J: SchedContext configure — decode args, validate, configure
  -- AK3-J (A-M07 / MEDIUM): `decodeSchedContextConfigureArgsChecked` enforces
  -- seL4-MCS's budget and period ranges at decode time.  WS-SX SX6.4: the words
  -- are seL4's `SchedControl_ConfigureFlags` words — budget, period,
  -- extra_refills, badge, flags.
  --
  -- WS-ZA ZA6.4: the configure is invoked on core `core`'s SCHEDULING CONTROL
  -- capability, seL4-MCS's `SchedControl`, the one authority to set a context's
  -- budget and period; the context is extra capability 0
  -- (`resolveSchedControlConfigureTarget`).  A scheduling-context capability
  -- configures nothing: a holder of one could otherwise reset the budget it was
  -- handed, period after period.
  | .schedContextConfigure =>
    some <| match cap.target with
    | .schedControl core =>
      fun st =>
      -- WS-SX SX6.4: the context is extra capability 0, read before any word
      -- (seL4-MCS's `decodeSchedControl_ConfigureFlags` refuses a message that
      -- names none `seL4_TruncatedMessage` first).
      match callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0 with
      | none => .error .truncatedMessage
      | some scCPtr =>
      -- seL4-MCS's order: the extra capability looked up (`lookupExtraCaps`,
      -- before the decode), the length, its kind, then the words' ranges.
      -- AL7-G / WS-AL AL8 (cascades AK7-E): type-level sentinel rejection
      -- via the ValidObjId signature on schedContextConfigure; the
      -- context's promotion is the resolver's.
      match resolveSchedControlConfigureTarget tid core scCPtr decoded.msgInfo.length st with
      | .error e => .error e
      | .ok vScId =>
      match decodeSchedContextConfigureArgsChecked decoded with
      | .error e => .error e
      | .ok args =>
              -- The configure runs on the control's core, moving a context
              -- homed elsewhere there with its thread (seL4's
              -- `invokeSchedControl_ConfigureFlags`).
              if hCore : core < SeLe4n.Kernel.Concurrency.numCores then
                SchedContextOps.schedControlConfigure ⟨core, hCore⟩ vScId args.budget
                  args.period args.extraRefills args.badge args.flags st
              else .error (.invalidCapability 0)
    | _ => fun _ => .error (.invalidCapability 0)
  -- Z5-J: SchedContext bind — the SchedContext from the capability target, the
  -- thread from a TCB CAPABILITY the caller holds (`v0.35.204`; a raw thread id
  -- until then — see `resolveSchedContextBindThread` for what that let a
  -- SchedContext-capability holder do to a thread it held no authority over).
  | .schedContextBind =>
    some <| match cap.target with
    | .object scId =>
      -- seL4-MCS's `decodeSchedContext_Bind` switches on extra capability 0's
      -- type: a notification capability binds the context to the notification
      -- (`schedContext_bindNtfn`); every other capability is the thread path.
      fun st => match resolveSchedContextBindNotificationCode tid
          (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st with
      | k + 1 =>
        match validateObjIdArg scId with
        | .error e => .error e
        | .ok vScId => schedContextBindNotification vScId ⟨k⟩ st
      | 0 =>
      match resolveSchedContextBindThread tid (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st with
      | .error e => .error e
      | .ok vThreadId =>
          -- AL7-H / WS-AL AL8 (cascades AK7-E): type-level sentinel rejection
          -- via the ValidObjId signature on schedContextBind; the thread's
          -- promotion is the resolver's.
          match validateObjIdArg scId with
          | .error e => .error e
          | .ok vScId =>
              SchedContextOps.schedContextBind vScId vThreadId st
    | _ => fun _ => .error (.invalidCapability 0)
  -- Z5-J: SchedContext unbind — no extra args, SchedContext from cap target
  | .schedContextUnbind =>
    some <| match cap.target with
    | .object scId =>
      fun st => match decodeSchedContextUnbindArgs decoded with
      | .error e => .error e
      | .ok _ =>
          -- AL7-I / WS-AL AL8 (cascades AK7-E): type-level sentinel rejection
          -- via ValidObjId signature on schedContextUnbind.
          match validateObjIdArg scId with
          | .error e => .error e
          | .ok vScId =>
              -- seL4-MCS's `SchedContext_Unbind` (`invokeSchedContext_Unbind`):
              -- refused `IllegalOperation` when the context's thread is the
              -- executing core's current one; otherwise the thread unbind
              -- (the **per-core** form, WS-SM SM8.B: a thread running on a
              -- remote core is rescheduled there through its `.reschedule`
              -- SGI) and then the notification unbind.  A context bound to no
              -- thread is unbound from its notification alone.
              match SchedContextOps.schedContextUnbindAllOnCore vScId
                  executingCore st with
              | .ok (st', _) => .ok ((), st')
              | .error e => .error e
    | _ => fun _ => .error (.invalidCapability 0)
  -- WS-SX SX8.3: seL4-MCS's `SchedContext_UnbindObject` — extra capability 0
  -- is read as the bind reads it: a notification capability unbinds the
  -- context's notification (`schedContext_unbindNtfn`), every other capability
  -- is the thread path (`schedContext_unbindTCB`).
  | .schedContextUnbindObject =>
    some <| match cap.target with
    | .object scId =>
      fun st => match resolveSchedContextBindNotificationCode tid
          (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st with
      | k + 1 =>
        match validateObjIdArg scId with
        | .error e => .error e
        | .ok vScId => SchedContextOps.schedContextUnbindNotificationObject vScId ⟨k⟩ st
      | 0 =>
      match resolveSchedContextBindThread tid
          (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st with
      | .error e => .error e
      | .ok vThreadId =>
          match validateObjIdArg scId with
          | .error e => .error e
          | .ok vScId =>
              match SchedContextOps.schedContextUnbindThreadObjectOnCore vScId
                  vThreadId.val executingCore st with
              | .ok (st', _) => .ok ((), st')
              | .error e => .error e
    | _ => fun _ => .error (.invalidCapability 0)
  -- WS-ZA ZA6.9: seL4-MCS's `seL4_SchedContext_Consumed` — no arguments; the
  -- context from the capability target, the caller the executing core's
  -- current thread (`schedContextConsumedOnCore`).
  | .schedContextConsumed =>
    some <| match cap.target with
    | .object scId =>
      fun st => match validateObjIdArg scId with
      | .error e => .error e
      | .ok vScId =>
          match schedContextConsumedOnCore (SeLe4n.SchedContextId.ofObjId vScId.val)
              executingCore st with
          | .ok st' => .ok ((), st')
          | .error e => .error e
    | _ => fun _ => .error (.invalidCapability 0)
  -- WS-ZA ZA6.29: seL4-MCS's `seL4_SchedContext_YieldTo` — no arguments; the
  -- context from the capability target, the caller the executing core's
  -- current thread (`schedContextYieldToOnCore`).
  | .schedContextYieldTo =>
    some <| match cap.target with
    | .object scId =>
      fun st => match validateObjIdArg scId with
      | .error e => .error e
      | .ok vScId =>
          match SchedContextOps.schedContextYieldToOnCore
              (SeLe4n.SchedContextId.ofObjId vScId.val) executingCore st with
          | .ok st' => .ok ((), st')
          | .error e => .error e
    | _ => fun _ => .error (.invalidCapability 0)
  -- WS-ZA ZA6.32: seL4's `seL4_IRQHandler_Ack` — no arguments; the line from
  -- the capability target, unmasked at the interrupt controller
  -- (`Architecture.irqHandlerAck`, seL4's `invokeIRQHandler_AckIRQ`).
  | .irqHandlerAck =>
    some <| match cap.target with
    | .irqHandler line => Architecture.irqHandlerAck line
    | _ => fun _ => .error (.invalidCapability 0)
  -- WS-ZA ZA6.32: seL4's `seL4_IRQControl_Get` — the interrupt-control
  -- capability issues line MR0's handler capability into the slot the CNode
  -- named as extra capability 0 names by MR1 (index) and MR2 (depth) (WS-SX
  -- SX6.3, D10), as a derivation child of the invoked slot
  -- (`irqControlGetFromCap`).
  | .irqControlGet =>
    some <| match cap.target with
    | .irqControl _ => fun st =>
        irqControlGetFromCap tid decoded.capAddr
          (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0)
          (decodeIrqControlGetArgs decoded) st
    | _ => fun _ => .error (.invalidCapability 0)
  -- WS-ZA ZA6.32: seL4's `seL4_IRQHandler_SetNotification` — the notification
  -- capability named as extra capability 0 (WS-SX SX6.4) bound to the
  -- handler's line (`irqHandlerSetNotificationFromCap`).
  | .irqHandlerSetNotification =>
    some <| match cap.target with
    | .irqHandler line => fun st =>
        irqHandlerSetNotificationFromCap tid executingCore line
          (irqHandlerSetNotificationArgsOf st tid decoded.msgInfo.extraCaps) st
    | _ => fun _ => .error (.invalidCapability 0)
  -- WS-ZA ZA6.32: seL4's `seL4_IRQHandler_Clear` — no arguments; the line's
  -- node slot emptied (`irqHandlerClear`).
  | .irqHandlerClear =>
    some <| match cap.target with
    | .irqHandler line => irqHandlerClear executingCore line
    | _ => fun _ => .error (.invalidCapability 0)
  -- WS-SM SM6.B: bind a notification to the capability-target TCB (seL4
  -- BindNotification).  Cap target = the TCB; the notification is the
  -- capability named as extra capability 0 (WS-SX SX6.4,
  -- `tcbBindNotificationArgsOf`).
  | .tcbBindNotification =>
    some <| match cap.target with
    | .object tcbObjId =>
      fun st => match tcbBindNotificationArgsOf st tid decoded.msgInfo.extraCaps with
      | .error e => .error e
      | .ok args =>
          -- WS-SM SM6.B (review #1): resolve the notification through a CAPABILITY in
          -- the caller's CSpace (seL4 BindNotification takes a notification cap), not a
          -- raw ObjId.  A TCB-cap holder must *also* hold a notification capability
          -- that may receive (Read: seL4's `CanReceive`, checked by
          -- `decodeBindNotification`) to redirect that notification's signals — otherwise it could hijack
          -- or deny any notification merely by naming its ObjId.  The type is
          -- checked before the right, each refusal seL4's `IllegalOperation`
          -- (`resolveBindNotificationCap`).
          -- Typed accessors (AK7 cascade discipline): `getTcb?` / `getCNode?`
          -- instead of raw `st.objects[…]?` matches.
          match st.getTcb? tid with
          | some callerTcb =>
            let ntfnGate : SyscallGate := {
              callerId      := tid
              cspaceRootCap := callerTcb.spaceCells[0]
              capAddr       := args.notificationCPtr
              requiredRight := .read
            }
            match resolveBindNotificationCap ntfnGate st with
            | .error e => .error e
            | .ok notifId => bindNotification notifId (SeLe4n.ThreadId.ofNat tcbObjId.toNat) st
          | none => .error .objectNotFound
    | _ => fun _ => .error (.invalidCapability 0)
  -- WS-SM SM6.B: unbind the capability-target TCB's bound notification.
  | .tcbUnbindNotification =>
    some <| match cap.target with
    | .object tcbObjId =>
      fun st =>
        match unbindNotification (SeLe4n.ThreadId.ofNat tcbObjId.toNat) st with
        | .error e => .error e
        | .ok ((), st') => .ok ((), st')
    | _ => fun _ => .error (.invalidCapability 0)
  -- D1: TCB suspend — target thread from capability
  -- WS-SM SM6.E (live cross-core wiring): route through the per-core
  -- `suspendThreadOnCore` — the victim is descheduled on its *home* core
  -- (`determineTargetCore`), not the boot core, and a remote-running victim's
  -- home core is poked.  The executing core is the caller's: the core the
  -- syscall trapped on, threaded from the entry as `executingCore`.
  -- The surfaced SGI is dropped at this pure layer: on the live path the
  -- FFI seam (`syscallDispatchCrossCoreEntry`) re-derives and fires it from
  -- the state diff (`crossCoreSgiBody`'s SM6.E descheduled-current rule).
  | .tcbSuspend =>
    some <| match cap.target with
    | .object objId =>
      fun st => match decodeSuspendArgs decoded with
      | .error e => .error e
      | .ok _ =>
        -- AL7-B / WS-AL AL8 (cascades AK7-E): type-level sentinel rejection.
        match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | .error e => .error e
        | .ok vtid =>
            match Lifecycle.Suspend.suspendThreadOnCore st vtid
                executingCore with
            | .ok (st', _) => .ok ((), st')
            | .error e => .error e
    | _ => fun _ => .error (.invalidCapability 0)
  -- D1: TCB resume — target thread from capability
  | .tcbResume =>
    some <| match cap.target with
    | .object objId =>
      fun st => match decodeResumeArgs decoded with
      | .error e => .error e
      | .ok _ =>
        -- AL7-C / WS-AL AL8 (cascades AK7-E): type-level sentinel rejection.
        -- `validateThreadIdArg` returns `ValidThreadId`; the handler ACCEPTS
        -- `ValidThreadId` — the type system forbids sentinel IDs from reaching
        -- it. No runtime double-check needed.
        --
        -- WS-SM (PR #861 review round 10): route through the **per-core** resume.
        -- The boot-pinned `resumeThread` enqueues on `bootCoreId` unconditionally,
        -- so resuming a thread whose `cpuAffinity` homes it on a secondary core
        -- put it on the wrong run queue — it would never be dispatched by its own
        -- core, and the boot core would treat it as runnable.  `resumeThreadOnCore`
        -- enqueues on `determineTargetCore` and runs the reschedule locally or
        -- hands the home core a `.reschedule` SGI.  The SGI is dropped here for
        -- the same reason `.tcbSuspend` drops its own: the diff seam re-derives
        -- cross-core pokes from the committed `(pre, post)` states, and a thread
        -- newly runnable on a remote home core is exactly
        -- `crossCoreSgiBody_remote_wake`.
        --
        -- Review round (PR #887): a thread suspended fail-closed by the fault
        -- path keeps its fault as a diagnostic.  Resuming it must retire that
        -- fault — restart at the faulting instruction with the register window
        -- it held at the trap, clearing `pendingFault` — or the thread's next
        -- ordinary Call would be answered through the reply seam's fault
        -- branch and rewound to the old fault PC.  A thread carrying no fault
        -- is untouched (`retirePendingFaultForResume_of_no_fault`).
        --
        -- WS-SX SX4: the arm is seL4's `restart` (`restartThreadOnCore`): a
        -- thread blocked in an IPC is stopped too, so its IPC is cancelled and
        -- it is resumed; a thread that is not stopped is left as it is.
        match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | .error e => .error e
        | .ok vtid =>
            match Lifecycle.Suspend.restartThreadOnCore st vtid executingCore with
            | .ok (st', _) => .ok ((), st')
            | .error e => .error e
    | _ => fun _ => .error (.invalidCapability 0)
  -- AE1-A: D2-K TCB setPriority — priority from message register, target from capability
  -- Moved here from explicit dispatch arms to unify checked/unchecked paths (U-01 fix).
  | .tcbSetPriority =>
    some <| match cap.target with
    | .object objId =>
      fun st => match decodeSetPriorityArgs decoded with
      | .error e => .error e
      | .ok args =>
        -- AL7-D / WS-AL AL8 (cascades AK7-E): type-level sentinel rejection
        -- via ValidThreadId signature on setPriorityOp.
        -- WS-SX SX6.4 (D11): the authority is the thread capability the
        -- caller names as extra capability 0 (seL4's `authCap`).
        match resolvePriorityAuthority st tid
            (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0) with
        | .error e => .error e
        | .ok vCallerTid =>
            match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
            | .error e => .error e
            | .ok vTargetTid =>
                -- WS-SM SM8.B (PR #861 review round 12): route through the
                -- **per-core** priority op.  `setPriorityOp` re-buckets on
                -- `runQueueOnCore bootCoreId`, so for a target queued on a
                -- secondary core the membership test failed and the migration was
                -- a silent no-op — the priority field moved while the run queue's
                -- cached band did not, leaving the scheduler dispatching the
                -- thread at its OLD priority.  `setPriorityOnCore` migrates on the
                -- target's home core and preempts the core actually running it.
                match SchedContext.PriorityManagement.setPriorityOnCore st
                    vCallerTid vTargetTid
                    (Priority.ofNat args.newPriority) executingCore with
                | .ok (st', _) => .ok ((), st')
                | .error e => .error e
    | _ => fun _ => .error (.invalidCapability 0)
  -- AE1-A: D2-K TCB setMCPriority — MCP from message register, target from capability
  | .tcbSetMCPriority =>
    some <| match cap.target with
    | .object objId =>
      fun st => match decodeSetMCPriorityArgs decoded with
      | .error e => .error e
      | .ok args =>
        -- AL7-E / WS-AL AL8 (cascades AK7-E): type-level sentinel rejection
        -- via ValidThreadId signature on setMCPriorityOp.
        -- WS-SX SX6.4 (D11): the authority is the thread capability the
        -- caller names as extra capability 0 (seL4's `authCap`).
        match resolvePriorityAuthority st tid
            (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0) with
        | .error e => .error e
        | .ok vCallerTid =>
            match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
            | .error e => .error e
            | .ok vTargetTid =>
                -- WS-SM SM8.B (PR #861 review round 12): the per-core MCP op —
                -- same boot-pinned re-bucket and preemption defects as
                -- `.tcbSetPriority`, reached whenever the new ceiling caps a
                -- target's current priority.
                match SchedContext.PriorityManagement.setMCPriorityOnCore st
                    vCallerTid vTargetTid
                    (Priority.ofNat args.newMCP) executingCore with
                | .ok (st', _) => .ok ((), st')
                | .error e => .error e
    | _ => fun _ => .error (.invalidCapability 0)
  -- AE1-B: D3-H TCB setIPCBuffer — buffer address from message register, target from capability
  -- Moved here from duplicate arms in both dispatch paths (U-06 fix).
  -- WS-SX SX6.6: the buffer's frame capability is the caller's extra capability
  -- 0, derived into the thread's buffer slot (seL4's `decodeSetIPCBuffer`).
  | .tcbSetIPCBuffer =>
    some <| match cap.target with
    | .object objId =>
      fun st => match decodeSetIPCBufferArgs decoded with
      | .error e => .error e
      | .ok args =>
        -- AL7-F / WS-AL AL8 (cascades AK7-E): type-level sentinel rejection
        -- via ValidThreadId signature on setIPCBufferOp.
        match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | .error e => .error e
        | .ok vtid =>
            match Architecture.IpcBufferValidation.setIPCBufferOp executingCore st vtid tid
                (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0) args.bufferAddr with
            | .ok st' => .ok ((), st')
            | .error e => .error e
    | _ => fun _ => .error (.invalidCapability 0)
  -- WS-SM SM5.H.4: TCB setAffinity — affinity word from message register, target
  -- from capability.  Authority is the `.write` right on the target TCB
  -- (`syscallRequiredRight .tcbSetAffinity = .write`, identical to setPriority).
  | .tcbSetAffinity =>
    some <| match cap.target with
    | .object objId =>
      fun st => match Architecture.SyscallArgDecode.decodeSetAffinityArgs decoded with
      | .error e => .error e
      | .ok args =>
        match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | .error e => .error e
        | .ok vtid =>
            match decodeAffinity args.affinityRaw with
            | .error e => .error e
            | .ok affinity =>
                -- WS-SM SM8.B (round 37): the per-core form.  The committed
                -- state is identical at every executing core
                -- (`setThreadCpuAffinityOnCore_state_core_independent`), so this
                -- is trace-safe; what changes is that the migration's SGI is
                -- computed against the caller's real core instead of the boot
                -- core, and is no longer discarded before the diff seam sees it.
                match setThreadCpuAffinityOnCore st vtid affinity
                        executingCore with
                | .ok (st', _) => .ok ((), st')
                | .error e => .error e
    | _ => fun _ => .error (.invalidCapability 0)
  -- **WS-BP BP7.1 (`v0.36.11`), WS-SX SX6.5**: seL4-MCS's `TCB_SetSpace` — the
  -- target from the invoked TCB capability (with the write right); the fault
  -- endpoint, CSpace root and VSpace root are extra capabilities 0 to 2,
  -- resolved through the *caller's* CSpace (`resolveSetSpace`), and the two
  -- words are the roots' data words.  The target must be suspended: the
  -- operation refuses a thread whose spaces are in use.
  | .tcbSetSpace =>
    some <| match cap.target with
    | .object objId =>
      fun st => match Architecture.SyscallArgDecode.decodeSetSpaceArgs decoded with
      | .error e => .error e
      | .ok args =>
        match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | .error e => .error e
        | .ok vtid =>
            match resolveSetSpace tid decoded.msgInfo.extraCaps args st with
            | .error e => .error e
            | .ok (cnSrc, vrSrc, fhSrc) =>
                match copyThreadSpacesZombie executingCore st vtid cnSrc vrSrc args.cspaceRootData
                    fhSrc with
                | .ok st' => .ok ((), st')
                | .error e => .error e
    | _ => fun _ => .error (.invalidCapability 0)
  -- **WS-BP BP7.1 (`v0.36.12`)**: `seL4_ARM_PageTable_Map` — the table from the
  -- invoked capability (with the write right), the address from MR0 (MR1 is
  -- the attributes word).  **WS-SX SX6.3**: the address space is extra
  -- capability 0 (`current_extra_caps.excaprefs[0]`), resolved through the
  -- *caller's* CSpace with `.write`; a message naming none is
  -- `.truncatedMessage`, as seL4 refuses a null `excaprefs[0]`.
  | .pageTableMap =>
    some <| match cap.target with
    | .object objId =>
      fun st => match Architecture.SyscallArgDecode.decodePageTableMapArgs decoded with
      | .error e => .error e
      | .ok args =>
        match callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0 with
        | none => .error .truncatedMessage
        | some rootCPtr =>
          match resolveCallerCapObject tid rootCPtr .write st with
          | .error e => .error (e.forArgumentCap Architecture.pageTableMapRootCapNumber)
          | .ok (_, rootId) => Architecture.pageTableMap objId rootId args.vaddr st
    | _ => fun _ => .error (.invalidCapability 0)
  -- **WS-BP BP7.1 (`v0.36.12`)**: `seL4_ARM_PageTable_Unmap` — the table from the
  -- invoked capability; the address space is the one its own record names.
  | .pageTableUnmap =>
    some <| match cap.target with
    | .object objId => fun st => Architecture.pageTableUnmap objId st
    | _ => fun _ => .error (.invalidCapability 0)
  | _ => none

/-- WS-RR RR3.23: the pre-state quiescence facts `dispatchCapabilityOnly`'s
arms consume, keyed to the decode and capability shapes each arm actually
resolves.  Every field is a pre-state fact — dischargeable before the step —
so the payoff theorem below carries no post-state obligation. -/
structure capabilityDispatchQuiescence (decoded : SyscallDecodeResult)
    (cap : Capability) (st : SystemState) : Prop where
  /-- **The scheduling links a final delete's context retire reads against**
  (`schedContextLinkInvariant`): no thread holds a timeout budget, the binding
  pair, and every context a replenishment queue holds is bound and queued on its
  holder's home core.  The retire reads a context's own links alone — bound to no
  thread, lent from none, heading no stack — and these are what make that the
  whole truth; the delete's own steps keep them
  (`cspaceDeleteSlotFinalising_preserves_finalisingDeleteBundle`).  The binding
  pair's thread-side half the arms read is their consequence with the IPC
  bundle's loan record (`schedContextBindingBidirectional_of_consistent`). -/
  schedContextLinks : schedContextLinkInvariant st
  /-- **`v0.35.204`**: keyed to the resolver the arm binds through, quantified
  over the caller — the pack carries no caller, and a fact about *every* thread
  any caller's CSpace resolves its extra capability 0 to is a pre-state fact
  all the same. -/
  boundThreadNotDonationOwner : ∀ (callerTid : SeLe4n.ThreadId)
      (vThreadId : SeLe4n.ValidThreadId),
    decoded.syscallId = .schedContextBind →
    resolveSchedContextBindThread callerTid
      (schedContextBindArgsOf st callerTid decoded.msgInfo.extraCaps) st =
      .ok vThreadId →
    ∀ (s : SeLe4n.ThreadId) (sTcb : TCB) (sc0 : SeLe4n.SchedContextId),
      st.objects[s.toObjId]? = some (.tcb sTcb) →
      sTcb.schedContextBinding ≠ .donated sc0 vThreadId.val
  targetThreadQuiescent : ∀ (objId : SeLe4n.ObjId),
    decoded.syscallId = .tcbSuspend ∨ decoded.syscallId = .tcbResume →
    cap.target = .object objId →
    ∀ vtid, validateThreadIdArg (ThreadId.ofNat objId.toNat) = .ok vtid →
    threadIpcFieldsQuiescent st vtid.val
  /-- **WS-OD OD4.4**: the outer caller every donation pop the dispatch can reach
  would settle a scheduling context on is a proper waiting donor nobody else
  owns.

  A pre-state fact about the *reply stacks*, and the one half of the pop's
  outer-caller obligation no O(1) guard can decide (`donationOuterUnowned`); the
  other three clauses are consequences of the pop's own `outerCallerAcceptable`
  check.  Vacuous on every state whose scheduling contexts head no reply stack,
  which is every state this tree reached before OD4.1's push and every depth-1
  state after it — so the field costs the existing discharges nothing.

  It is quantified over all three arguments rather than resolved from the
  syscall, because `.tcbSuspend` reaches the pop through the cancellation
  reclaim's *holder* and through thread destruction, and those name contexts the
  decode does not. -/
  replyStacksSettleOnWaitingDonors : ∀ scId serverTid originalOwner,
    replyStackOuterCallerValid st scId serverTid originalOwner
  /-- **WS-ZA ZA5.4 part 25**: every lent scheduling context is headed by its
  lender's reply frame (seL4 MCS lends a context in the step that pushes the
  lender's reply as its stack head).  A pre-state fact the finalising delete and
  revocation read in place of a walk of the whole store: a reply heading no stack
  has a caller that lends to no one (`replyCaller_lendsNone`).  The delete's own
  steps keep it (`cspaceDeleteSlotFinalising_preserves_finalisingDeleteBundle`), so
  the revocation loop carries it from this one fact.  Stated, not derived: it is
  one of the stated coherence hypotheses `docs/REGISTERED_DEBT.md` carries to
  v1.0.0.  Vacuous on every state that lends no context. -/
  lentContextsHeadedByLender : lentContextHeadsLenderFrame st

/-- WS-RR RR3.23 (**the capability-only dispatch payoff**): every syscall
`dispatchCapabilityOnly` routes preserves `ipcInvariantFull`, over the
RR3.15–RR3.21 per-arm bundles.  The hypotheses are the object-store invariant,
the bundle itself, and the pre-state quiescence pack — nothing is bound on the
post-state. -/
theorem dispatchCapabilityOnly_preserves_ipcInvariantFull
    (decoded : SyscallDecodeResult) (cap : Capability) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (k : Kernel Unit) (st st' : SystemState)
    (hArm : dispatchCapabilityOnly decoded cap tid executingCore = some k)
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st)
    (hPack : capabilityDispatchQuiescence decoded cap st)
    (hR : st.runQueueRefined)
    (hStep : k st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold dispatchCapabilityOnly at hArm
  cases hSy : decoded.syscallId <;> simp only [hSy] at hArm <;> try cases hArm
  case cspaceDelete =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object cnodeId =>
      try dsimp only [] at hStep
      cases hDec : decodeCSpaceDeleteArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          exact cspaceDeleteSlotZombie_preserves_ipcInvariantFull _ _ st st' hObjInv hInv
            hPack.lentContextsHeadedByLender hPack.schedContextLinks hStep
    all_goals try cases hStep
  case cspaceRevoke =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object cnodeId =>
      try dsimp only [] at hStep
      cases hDec : decodeCSpaceDeleteArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          exact cspaceRevokeCdtFinalising_preserves_ipcInvariantFull _ _ st st' hObjInv hInv
            hPack.lentContextsHeadedByLender hPack.schedContextLinks hStep
    all_goals try cases hStep
  case mintReplyCap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object cnodeId =>
      try dsimp only [] at hStep
      cases hDec : decodeMintReplyCapArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          exact mintReplyCapWithCdt_preserves_ipcInvariantFull st st' _ _ hObjInv hInv hStep
    all_goals try cases hStep
  case untypedRetype =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object _ =>
      exact ((untypedRetypeFromCap_chain hStep).preserves
        (P := fun s => s.objects.invExt ∧ ipcInvariantFull s)
        (fun hP hC => ⟨untypedRetypeObject_preserves_objects_invExt hP.1 hC,
          untypedRetypeObject_preserves_ipcInvariantFull _ _ _ _ _ _ hP.1 hP.2 hC⟩)
        ⟨hObjInv, hInv⟩).2
    all_goals try cases hStep
  case vspaceMap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hDec : decodePageMapArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok words =>
          simp only [hDec] at hStep
          cases hX : callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0 with
          | none => simp only [hX] at hStep; cases hStep
          | some rootCPtr =>
          simp only [hX] at hStep
          cases hOps : resolvePageMapOperands tid decoded.capAddr rootCPtr words st with
          | error e => simp only [hOps] at hStep; cases hStep
          | ok p =>
          obtain ⟨_, args⟩ := p
          simp only [hOps] at hStep
          · have hFresh : ∀ s s', s.objects.invExt → ipcInvariantFull s →
                vspaceMapFromFrameCap tid executingCore args s = .ok ((), s') →
                ipcInvariantFull s' := by
              intro s s' hObjInv hInv hStep
              obtain ⟨_, _, _, st1, _, _, _, _, _, hMap, epoch, st2, hT, hRec⟩ :=
                vspaceMapFromFrameCap_ok tid executingCore args s s' hStep
              have hTag := tagFrameMapping_preserves_ipcInvariantFull _ _ _ st1 st2 epoch
                (vspaceMapPageCheckedWithShootdownFromStatePerCore_ok_frame _ _ _ _ _ s st1
                  hObjInv hMap).1
                (vspaceMapPageCheckedWithShootdownFromStatePerCore_preserves_ipcInvariantFull
                  s st1 _ _ _ _ _ hObjInv hInv hMap) hT
              exact (cspaceRecordFrameMapping_preserves_ipcInvariantFull _ _ st2 s'
                hTag.2 hTag.1 hRec).1
            rcases vspaceMapOrRemapFromFrameCap_cases hStep with hM | ⟨st0, hU, hM⟩
            · exact hFresh _ _ hObjInv hInv hM
            · exact hFresh _ _
                (vspaceUnmapPageWithShootdownAndIcacheBroadcast_ok_frame _ _ _ _ _ hObjInv hU).1
                (vspaceUnmapPageWithShootdownAndIcacheBroadcast_preserves_ipcInvariantFull
                  _ _ _ _ _ hObjInv hInv hU) hM
    all_goals try cases hStep
  case vspaceUnmap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hR : resolveCallerCapSlot tid decoded.capAddr (syscallRequiredRight .vspaceUnmap) st with
      | error e => simp only [hR] at hStep; cases hStep
      | ok r =>
          obtain ⟨slot, _, _⟩ := r
          simp only [hR] at hStep
          exact (vspaceUnmapFrameCap_preserves_ipcInvariantFull _ _ st st' hObjInv hInv hStep).1
    all_goals try cases hStep
  case vspaceUnifyInstruction =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hDec : decodeVSpaceUnifyInstructionArgs decoded st.machine.maxASID with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          · exact vspaceUnifyInstructionPage_preserves_ipcInvariantFull hInv hStep
    all_goals try cases hStep
  case serviceRevoke =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case serviceRegistry _ =>
      obtain ⟨_, oid, -, hK⟩ := serviceEndpointArm_ok hStep
      obtain ⟨_, hRev⟩ := revokeServiceByRecordedRegistration_revokeService hK
      exact revokeService_preserves_ipcInvariantFull st st' _ hObjInv hInv hRev
    all_goals try cases hStep
  case serviceQuery =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case serviceRegistry _ =>
      obtain ⟨_, epId, -, hK⟩ := serviceEndpointArm_ok hStep
      clear hStep
      cases hLkS : lookupServiceByRecordedRegistration epId st with
      | error e => simp only [hLkS] at hK; cases hK
      | ok pair =>
          obtain ⟨reg, st1⟩ := pair
          simp only [hLkS] at hK
          have hStEq : st1 = st := lookupServiceByRecordedRegistration_preserves_state epId st reg st1 hLkS
          subst hStEq
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hK
          subst hK
          exact Architecture.writeCallReturnWord_of_frame _ hInv
            (fun _ => writeReturnFrameToTcb_preserves_ipcInvariantFull st1 tid _ hObjInv hInv)
    all_goals try cases hStep
  case schedContextConfigure =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case schedControl core =>
      try dsimp only [] at hStep
      rcases hXc : callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0 with _ | scCPtr
      · simp only [hXc] at hStep; cases hStep
      simp only [hXc] at hStep
      cases hVal : resolveSchedControlConfigureTarget tid core scCPtr decoded.msgInfo.length st with
      | error e => simp only [hVal] at hStep; cases hStep
      | ok vScId =>
          simp only [hVal] at hStep
          cases hDec : decodeSchedContextConfigureArgsChecked decoded with
          | error e => simp only [hDec] at hStep; cases hStep
          | ok args =>
              simp only [hDec] at hStep
              split at hStep
              · exact schedControlConfigure_preserves_ipcInvariantFull st st' _ vScId _ _ _ _ _
                  hObjInv hInv hStep
              · cases hStep
    all_goals try cases hStep
  case schedContextBind =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hN : resolveSchedContextBindNotificationCode tid
          (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st with
      | succ k =>
          simp only [hN] at hStep
          cases hVal : validateObjIdArg scId with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vScId =>
              simp only [hVal] at hStep
              exact schedContextBindNotification_preserves_ipcInvariantFull st st' vScId _ hObjInv hInv hStep
      | zero =>
          simp only [hN] at hStep
          cases hRes : resolveSchedContextBindThread tid (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st with
          | error e => simp only [hRes] at hStep; cases hStep
          | ok vThreadId =>
              simp only [hRes] at hStep
              cases hVal : validateObjIdArg scId with
              | error e => simp only [hVal] at hStep; cases hStep
              | ok vScId =>
                  simp only [hVal] at hStep
                  exact schedContextBind_preserves_ipcInvariantFull st st' vScId vThreadId
                    hObjInv hInv (schedContextBindingBidirectional_of_consistent
                      hPack.schedContextLinks.binding hInv.donationOwnerValid)
                    (hPack.boundThreadNotDonationOwner tid vThreadId hSy hRes) hStep
    all_goals try cases hStep
  case schedContextUnbind =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hDec : decodeSchedContextUnbindArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateObjIdArg scId with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vScId =>
              simp only [hVal] at hStep
              cases hUn : SchedContextOps.schedContextUnbindAllOnCore vScId
                  executingCore st with
              | error e => simp only [hUn] at hStep; cases hStep
              | ok pair =>
                  obtain ⟨stU, sgiU⟩ := pair
                  simp only [hUn] at hStep
                  cases hStep
                  exact schedContextUnbindAllOnCore_preserves_ipcInvariantFull st st' vScId _
                    sgiU hObjInv hInv
                    hR hUn
    all_goals try cases hStep
  case schedContextUnbindObject =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hN : resolveSchedContextBindNotificationCode tid
          (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st with
      | succ k =>
          simp only [hN] at hStep
          cases hVal : validateObjIdArg scId with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vScId =>
              simp only [hVal] at hStep
              exact schedContextUnbindNotificationObject_preserves_ipcInvariantFull st st' vScId _
                hObjInv hInv hStep
      | zero =>
          simp only [hN] at hStep
          cases hRes : resolveSchedContextBindThread tid (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st with
          | error e => simp only [hRes] at hStep; cases hStep
          | ok vThreadId =>
              simp only [hRes] at hStep
              cases hVal : validateObjIdArg scId with
              | error e => simp only [hVal] at hStep; cases hStep
              | ok vScId =>
                  simp only [hVal] at hStep
                  cases hUn : SchedContextOps.schedContextUnbindThreadObjectOnCore vScId
                      vThreadId.val executingCore st with
                  | error e => simp only [hUn] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨stU, sgiU⟩ := pair
                      simp only [hUn] at hStep
                      cases hStep
                      exact schedContextUnbindThreadObjectOnCore_preserves_ipcInvariantFull st _
                        vScId _ _ sgiU hObjInv hInv hUn
    all_goals try cases hStep
  case schedContextConsumed =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hVal : validateObjIdArg scId with
      | error e => simp only [hVal] at hStep; cases hStep
      | ok vScId =>
          simp only [hVal] at hStep
          cases hC : schedContextConsumedOnCore (SeLe4n.SchedContextId.ofObjId vScId.val)
              executingCore st with
          | error e => simp only [hC] at hStep; cases hStep
          | ok stC =>
              simp only [hC] at hStep
              cases hStep
              exact schedContextConsumedOnCore_preserves_ipcInvariantFull hObjInv hInv hC
    all_goals try cases hStep
  case schedContextYieldTo =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hVal : validateObjIdArg scId with
      | error e => simp only [hVal] at hStep; cases hStep
      | ok vScId =>
          simp only [hVal] at hStep
          cases hC : SchedContextOps.schedContextYieldToOnCore
              (SeLe4n.SchedContextId.ofObjId vScId.val) executingCore st with
          | error e => simp only [hC] at hStep; cases hStep
          | ok stC =>
              simp only [hC] at hStep
              cases hStep
              exact schedContextYieldToOnCore_preserves_ipcInvariantFull hObjInv hInv hC
    all_goals try cases hStep
  case irqHandlerAck =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqHandler line =>
      exact ipcInvariantFull_of_objects_eq
        (by rw [Architecture.irqHandlerAck_ok hStep]; rfl) hInv
    all_goals try cases hStep
  case irqControlGet =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqControl =>
      obtain ⟨_, _, _, _, _, _, hG⟩ := irqControlGetFromCap_ok tid _ _ _ st st' hStep
      exact irqControlGet_preserves_ipcInvariantFull hObjInv hInv hG
    all_goals try cases hStep
  case irqHandlerSetNotification =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqHandler line =>
      obtain ⟨_, _, _, hS⟩ := irqHandlerSetNotificationFromCap_ok tid executingCore line _ st st' hStep
      exact irqHandlerSetNotification_preserves_ipcInvariantFull hObjInv hInv
        hPack.lentContextsHeadedByLender hPack.schedContextLinks hS
    all_goals try cases hStep
  case irqHandlerClear =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case irqHandler line =>
      exact cspaceDeleteSlotZombie_preserves_ipcInvariantFull _ _ st st' hObjInv hInv
        hPack.lentContextsHeadedByLender hPack.schedContextLinks (irqHandlerClear_ok hStep).2
    all_goals try cases hStep
  case tcbBindNotification =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object tcbObjId =>
      try dsimp only [] at hStep
      cases hDec : tcbBindNotificationArgsOf st tid decoded.msgInfo.extraCaps with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hCaller : st.getTcb? tid with
          | none => simp only [hCaller] at hStep; cases hStep
          | some callerTcb =>
              simp only [hCaller] at hStep
              try dsimp only [] at hStep
              cases hCap2 : resolveBindNotificationCap { callerId := tid, cspaceRootCap := callerTcb.spaceCells[0], capAddr := args.notificationCPtr, requiredRight := .read } st with
              | error e => simp only [hCap2] at hStep; cases hStep
              | ok notifId =>
                  simp only [hCap2] at hStep
                  exact bindNotification_preserves_ipcInvariantFull st st' notifId _
                    hObjInv hInv hStep
    all_goals try cases hStep
  case tcbUnbindNotification =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object tcbObjId =>
      try dsimp only [] at hStep
      cases hUn : unbindNotification (SeLe4n.ThreadId.ofNat tcbObjId.toNat) st with
      | error e => simp only [hUn] at hStep; cases hStep
      | ok pair =>
          obtain ⟨u, stU⟩ := pair; cases u
          simp only [hUn] at hStep
          cases hStep
          exact unbindNotification_preserves_ipcInvariantFull st st' _ hObjInv hInv hUn
    all_goals try cases hStep
  case tcbSuspend =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSuspendArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hSus : Lifecycle.Suspend.suspendThreadOnCore st vtid
                  executingCore with
              | error e => simp only [hSus] at hStep; cases hStep
              | ok pair =>
                  obtain ⟨stU, sgiU⟩ := pair
                  simp only [hSus] at hStep
                  cases hStep
                  exact suspendThreadOnCore_preserves_ipcInvariantFull st st' vtid _ sgiU
                    hObjInv (hPack.targetThreadQuiescent objId (Or.inl hSy) hTgt vtid hVal)
                    hInv hSus
    all_goals try cases hStep
  case tcbResume =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeResumeArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
      | error e => simp only [hVal] at hStep; cases hStep
      | ok vtid =>
          simp only [hVal] at hStep
          cases hRes : Lifecycle.Suspend.restartThreadOnCore st vtid executingCore with
          | error e => simp only [hRes] at hStep; cases hStep
          | ok pair =>
              obtain ⟨stU, sgiU⟩ := pair
              simp only [hRes] at hStep
              cases hStep
              have hQ := hPack.targetThreadQuiescent objId (Or.inr hSy) hTgt vtid hVal
              rcases Lifecycle.Suspend.restartThreadOnCore_cases_of_ready hQ.ready hRes with
                hRes | ⟨rfl, _⟩
              · exact resumeThreadOnCore_preserves_ipcInvariantFull
                  (retirePendingFaultForResume st vtid.val) st' vtid _ sgiU
                  (retirePendingFaultForResume_preserves_objects_invExt st _ hObjInv)
                  (threadIpcFieldsQuiescent_retirePendingFaultForResume st _ hObjInv hQ)
                  (retirePendingFaultForResume_noFault st _ hObjInv)
                  (retirePendingFaultForResume_preserves_ipcInvariantFull st _ hObjInv hInv) hRes
              · exact hInv
    all_goals try cases hStep
  case tcbSetPriority =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSetPriorityArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hValC : resolvePriorityAuthority st tid
              (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0) with
          | error e => simp only [hValC] at hStep; cases hStep
          | ok vCallerTid =>
              simp only [hValC] at hStep
              cases hValT : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
              | error e => simp only [hValT] at hStep; cases hStep
              | ok vTargetTid =>
                  simp only [hValT] at hStep
                  cases hSet : SchedContext.PriorityManagement.setPriorityOnCore st
                      vCallerTid vTargetTid (Priority.ofNat args.newPriority)
                      executingCore with
                  | error e => simp only [hSet] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨stU, sgiU⟩ := pair
                      simp only [hSet] at hStep
                      cases hStep
                      exact setPriorityOnCore_preserves_ipcInvariantFull st st' vCallerTid
                        vTargetTid _ _ sgiU hObjInv hInv hSet
    all_goals try cases hStep
  case tcbSetMCPriority =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSetMCPriorityArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hValC : resolvePriorityAuthority st tid
              (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0) with
          | error e => simp only [hValC] at hStep; cases hStep
          | ok vCallerTid =>
              simp only [hValC] at hStep
              cases hValT : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
              | error e => simp only [hValT] at hStep; cases hStep
              | ok vTargetTid =>
                  simp only [hValT] at hStep
                  cases hSet : SchedContext.PriorityManagement.setMCPriorityOnCore st
                      vCallerTid vTargetTid (Priority.ofNat args.newMCP)
                      executingCore with
                  | error e => simp only [hSet] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨stU, sgiU⟩ := pair
                      simp only [hSet] at hStep
                      cases hStep
                      exact setMCPriorityOnCore_preserves_ipcInvariantFull st st' vCallerTid
                        vTargetTid _ _ sgiU hObjInv hInv hSet
    all_goals try cases hStep
  case tcbSetIPCBuffer =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSetIPCBufferArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hSet : Architecture.IpcBufferValidation.setIPCBufferOp executingCore st
                  vtid tid (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0)
                  args.bufferAddr with
              | error e => simp only [hSet] at hStep; cases hStep
              | ok stU =>
                  simp only [hSet] at hStep
                  cases hStep
                  exact setIPCBufferOp_preserves_ipcInvariantFull executingCore st st' vtid _ _ _
                    hObjInv hInv hPack.schedContextLinks.budgets hSet
    all_goals try cases hStep
  case tcbSetAffinity =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : Architecture.SyscallArgDecode.decodeSetAffinityArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hAff : decodeAffinity args.affinityRaw with
              | error e => simp only [hAff] at hStep; cases hStep
              | ok affinity =>
                  simp only [hAff] at hStep
                  cases hSet : setThreadCpuAffinityOnCore st vtid affinity
                      executingCore with
                  | error e => simp only [hSet] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨stU, sgiU⟩ := pair
                      simp only [hSet] at hStep
                      cases hStep
                      exact setThreadCpuAffinityOnCore_preserves_ipcInvariantFull st st'
                        vtid affinity _ sgiU hObjInv hInv hSet
    all_goals try cases hStep
  case tcbSetSpace =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : Architecture.SyscallArgDecode.decodeSetSpaceArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hR : resolveSetSpace tid decoded.msgInfo.extraCaps args st with
              | error e => simp only [hR] at hStep; cases hStep
              | ok p =>
                  obtain ⟨cn, vr, fh⟩ := p
                  simp only [hR] at hStep
                  cases hSet : copyThreadSpacesZombie executingCore st vtid cn vr
                      args.cspaceRootData fh with
                  | error e => simp only [hSet] at hStep; cases hStep
                  | ok stU =>
                      simp only [hSet] at hStep
                      cases hStep
                      exact copyThreadSpacesZombie_preserves_ipcInvariantFull executingCore st st'
                        vtid cn vr _ fh hObjInv hInv hPack.lentContextsHeadedByLender
                        hPack.schedContextLinks hSet
    all_goals try cases hStep
  case pageTableMap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : Architecture.SyscallArgDecode.decodePageTableMapArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hX : callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0 with
          | none => simp only [hX] at hStep; cases hStep
          | some rootCPtr =>
            simp only [hX] at hStep
            cases hR : resolveCallerCapObject tid rootCPtr .write st with
            | error e => simp only [hR] at hStep; cases hStep
            | ok p =>
                obtain ⟨_, rootId⟩ := p
                simp only [hR] at hStep
                exact pageTableMap_preserves_ipcInvariantFull objId rootId args.vaddr st st'
                  hObjInv hInv hStep
    all_goals try cases hStep
  case pageTableUnmap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      exact pageTableUnmap_preserves_ipcInvariantFull objId st st' hObjInv hInv hStep
    all_goals try cases hStep

-- ============================================================================
-- T6-I/M-IF-1: Information-flow-checked dispatch
-- ============================================================================

/-- **The flow gates of the two capability-only service arms.**  The service
query reads the registration its endpoint records, and the revoke removes it,
so each is a read or a write of the endpoint its extra capability 0 names
(WS-SX SX6.7, `resolveServiceEndpoint`); a
capability alone does not admit a flow its holder's label does not.  The query
runs only when the endpoint's label flows to the caller's
(`serviceEndpointReadAdmitted`), the revoke only when the caller's flows to the
endpoint's (`serviceEndpointWriteAdmitted`), and either is `flowDenied`
otherwise.  The checked tier runs the policy-checked wrappers themselves —
`serviceQueryStaged` (`lookupServiceChecked` under the query arm's return-word
staging) and `revokeServiceChecked` — so the dispatcher and the enforcement inventory name
one function for each.  The gate reads labels only and runs before the arm, so
a refusal reveals nothing about the registry.  Every other arm, and a
capability naming no object (which each arm refuses itself), runs the
capability-only arm `k` as it is; `dispatchCapabilityOnlyChecked_ok` is the bridge
back to `k` for a success. -/
def dispatchCapabilityOnlyChecked (ctx : LabelingContext) (sid : SyscallId) (xc : Nat)
    (tid : SeLe4n.ThreadId) (cap : Capability) (k : Kernel Unit) : Kernel Unit :=
  match sid with
  | .serviceQuery =>
    match cap.target with
    | .serviceRegistry _ =>
      serviceEndpointArm .serviceQuery tid xc fun _ epId => serviceQueryStaged ctx tid epId
    | _ => k
  | .serviceRevoke =>
    match cap.target with
    | .serviceRegistry _ =>
      serviceEndpointArm .serviceRevoke tid xc fun _ epId => revokeServiceChecked ctx tid epId
    | _ => k
  | _ => k

/-- A success through the gate is a success of the capability-only arm it
stands for: each checked service arm is the unchecked arm once its gate
admits, and a refusal is no success. -/
theorem dispatchCapabilityOnlyChecked_ok {ctx : LabelingContext} {decoded : SyscallDecodeResult}
    {tid : SeLe4n.ThreadId} {e : Concurrency.CoreId} {cap : Capability} {k : Kernel Unit}
    {st : SystemState} {r : Unit × SystemState}
    (hC : dispatchCapabilityOnly decoded cap tid e = some k)
    (h : dispatchCapabilityOnlyChecked ctx decoded.syscallId decoded.msgInfo.extraCaps tid cap k st
      = .ok r) : k st = .ok r := by
  unfold dispatchCapabilityOnlyChecked at h
  cases hS : decoded.syscallId <;> rw [hS] at h <;> try exact h
  all_goals
    unfold dispatchCapabilityOnly at hC
    rw [hS] at hC
    cases hT : cap.target <;> rw [hT] at h hC <;> simp only [Option.some.injEq] at hC <;>
      subst hC <;> try exact h
  · simp only [serviceEndpointArm] at h ⊢
    cases hR : resolveServiceEndpoint .serviceRevoke tid decoded.msgInfo.extraCaps st with
    | error e => simp only [hR] at h; cases h
    | ok p =>
      obtain ⟨_, epId⟩ := p
      simp only [hR] at h ⊢
      by_cases hA : serviceEndpointWriteAdmitted ctx tid epId = true
      · simpa [revokeServiceChecked, hA] using h
      · simp [revokeServiceChecked, hA] at h
  · simp only [serviceEndpointArm] at h ⊢
    cases hR : resolveServiceEndpoint .serviceQuery tid decoded.msgInfo.extraCaps st with
    | error e => simp only [hR] at h; cases h
    | ok p =>
      obtain ⟨_, epId⟩ := p
      simp only [hR] at h ⊢
      by_cases hA : serviceEndpointReadAdmitted ctx tid epId = true
      · simpa [serviceQueryStaged, lookupServiceChecked, hA] using h
      · simp [serviceQueryStaged, lookupServiceChecked, hA] at h

/-- Every arm but the two service arms is ungated. -/
@[simp] theorem dispatchCapabilityOnlyChecked_of_not_service (ctx : LabelingContext) {sid : SyscallId}
    (xc : Nat) (tid : SeLe4n.ThreadId) (cap : Capability) (k : Kernel Unit)
    (hQ : sid ≠ .serviceQuery) (hR : sid ≠ .serviceRevoke) :
    dispatchCapabilityOnlyChecked ctx sid xc tid cap k = k := by
  unfold dispatchCapabilityOnlyChecked
  split
  · exact absurd rfl hQ
  · exact absurd rfl hR
  · rfl

/-! ### The non-blocking syscalls (WS-SX SX7.2)

seL4's `handleSyscall` hands `isBlocking` down from the syscall number to
`sendIPC`, `receiveIPC` and `receiveSignal`.  The model reads it from the word
that named the syscall, the caller's trapped `x7`, as the arm acts: a send
only `Send` or `Call` did not issue (`Syscall.wordSendBlocks`) to an endpoint
with no receiver waiting drops the message, and `NBRecv` or
`NBWait` with nothing to take returns at once with `0` in the badge register
(`doNBRecvFailedTransfer`). -/

/-- **seL4's `sendIPC` with `blocking = false` on an endpoint no receiver
waits on**: the message is dropped and nothing is written.  Asked only once
the sender's flow to the endpoint is admitted (`endpointFlowGate`, the send's
own gate), so a sender denied that flow is refused whatever the queue holds
and learns nothing of it. -/
@[inline] def sendDropsMessage (ctx : LabelingContext) (blocks : Bool) (st : SystemState)
    (tid : SeLe4n.ThreadId) (epId : SeLe4n.ObjId) : Bool :=
  !blocks &&
  (match st.getEndpoint? epId with
   | some ep => ep.receiveQ.head.isNone
   | none => false) &&
  endpointFlowGate ctx epId (ctx.threadLabelOf tid) (ctx.endpointLabelOf epId)

/-- A blocking send never drops its message. -/
theorem sendDropsMessage_blocking (ctx : LabelingContext) (st : SystemState)
    (tid : SeLe4n.ThreadId) (epId : SeLe4n.ObjId) :
    sendDropsMessage ctx true st tid epId = false := rfl

/-- An `NBSend` whose flow to the endpoint is denied drops nothing, whatever
the endpoint's queue holds: it is refused by the send's own gate, so the
sender learns nothing of whether a receiver waits. -/
theorem sendDropsMessage_false_of_flowDenied (ctx : LabelingContext) (blocks : Bool)
    (st : SystemState) (tid : SeLe4n.ThreadId) (epId : SeLe4n.ObjId)
    (hDeny : endpointFlowGate ctx epId (ctx.threadLabelOf tid) (ctx.endpointLabelOf epId) = false) :
    sendDropsMessage ctx blocks st tid epId = false := by
  simp [sendDropsMessage, hDeny]

/-- The endpoint view the drop test reads: whether no receiver waits on it. -/
def endpointReceiveIdleOf? : Option KernelObject → Option Bool
  | some (.endpoint e) => some e.receiveQ.head.isNone
  | _ => none

theorem endpointReceiveIdleOf?_project (ctx : LabelingContext) (observer : IfObserver)
    (o : Option KernelObject) :
    endpointReceiveIdleOf? (o.map (projectKernelObject ctx observer)) =
      endpointReceiveIdleOf? o := by
  rcases o with _ | k
  · rfl
  · cases k <;> rfl

/-- The drop test, read through the endpoint view. -/
theorem sendDropsMessage_eq_view (ctx : LabelingContext) (blocks : Bool) (st : SystemState)
    (tid : SeLe4n.ThreadId) (epId : SeLe4n.ObjId) :
    sendDropsMessage ctx blocks st tid epId =
      (!blocks && (endpointReceiveIdleOf? st.objects[epId]?).getD false &&
        endpointFlowGate ctx epId (ctx.threadLabelOf tid) (ctx.endpointLabelOf epId)) := by
  unfold sendDropsMessage SystemState.getEndpoint?
  cases h : st.objects[epId]? with
  | none => rfl
  | some k => cases k <;> rfl

/-- **Non-interference of the `NBSend` drop, sender side**: two states an
observer cannot tell apart give the same drop decision, for an endpoint the
observer sees.  The decision reads only the endpoint's receive queue (which the
projection keeps), behind the send's own flow gate.  A drop writes nothing,
and, as seL4's `NBSend`, a delivered message and a dropped one alike return to
the sender with no register written (`.resumes`). -/
theorem sendDropsMessage_lowEquivalent (ctx : LabelingContext) (observer : IfObserver)
    (blocks : Bool) (st₁ st₂ : SystemState) (tid : SeLe4n.ThreadId) (epId : SeLe4n.ObjId)
    (hLow : lowEquivalent ctx observer st₁ st₂)
    (hEpObs : objectObservable ctx observer epId = true) :
    sendDropsMessage ctx blocks st₁ tid epId = sendDropsMessage ctx blocks st₂ tid epId := by
  have h := congrFun (congrArg ObservableState.objects hLow) epId
  have hObj : (st₁.objects[epId]?).map (projectKernelObject ctx observer) =
      (st₂.objects[epId]?).map (projectKernelObject ctx observer) := by
    simpa [projectState, projectObjects, hEpObs, SystemState.getObject?] using h
  have hV : endpointReceiveIdleOf? st₁.objects[epId]? = endpointReceiveIdleOf? st₂.objects[epId]? := by
    rw [← endpointReceiveIdleOf?_project ctx observer,
      ← endpointReceiveIdleOf?_project ctx observer (st₂.objects[epId]?), hObj]
  rw [sendDropsMessage_eq_view, sendDropsMessage_eq_view, hV]

/-- **seL4's `receiveIPC` with `isBlocking = false` on an endpoint no sender
waits on** (`doNBRecvFailedTransfer`). -/
@[inline] def receiveFindsNothing (blocks : Bool) (st : SystemState) (epId : SeLe4n.ObjId) :
    Bool :=
  !blocks &&
  (match st.getEndpoint? epId with
   | some ep => ep.sendQ.head.isNone
   | none => false)

/-- A blocking receive never takes the non-blocking failure. -/
theorem receiveFindsNothing_blocking (st : SystemState) (epId : SeLe4n.ObjId) :
    receiveFindsNothing true st epId = false := rfl

/-- **seL4's `receiveSignal` with `isBlocking = false` on a notification with
no pending signal** (`doNBRecvFailedTransfer`), asked once the wait's flow and
binding checks have admitted it. -/
@[inline] def waitFindsNothing (ctx : LabelingContext) (blocks : Bool) (st : SystemState)
    (tid : SeLe4n.ThreadId) (notifId : SeLe4n.ObjId) : Bool :=
  !blocks &&
  (match st.getNotification? notifId with
   | some ntfn => ntfn.pendingBadge.isNone
   | none => false) &&
  securityFlowsTo (ctx.objectLabelOf notifId) (ctx.threadLabelOf tid) &&
  !notificationBoundElsewhere st notifId tid

/-- A blocking wait never takes the non-blocking failure. -/
theorem waitFindsNothing_blocking (ctx : LabelingContext) (st : SystemState)
    (tid : SeLe4n.ThreadId) (notifId : SeLe4n.ObjId) :
    waitFindsNothing ctx true st tid notifId = false := rfl

/-- A wait that consumed a badge was not the non-blocking failure: a badge is
consumed only from a notification holding one. -/
theorem waitFindsNothing_of_consumed {ctx : LabelingContext} {notifId : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {executingCore : Concurrency.CoreId} {st st1 : SystemState}
    {badge : SeLe4n.Badge} (blocks : Bool)
    (h : notificationWaitCrossCoreDispatchChecked ctx notifId tid executingCore st =
      (st1, .ok (some badge))) :
    waitFindsNothing ctx blocks st tid notifId = false := by
  unfold waitFindsNothing
  cases hN : st.getNotification? notifId with
  | none => simp
  | some ntfn =>
    cases hP : ntfn.pendingBadge with
    | some b => simp [hP]
    | none =>
      exfalso
      unfold notificationWaitCrossCoreDispatchChecked notificationWaitOnCore at h
      simp only [hN, hP] at h
      repeat' split at h
      all_goals simp_all

/-! ### A receive that completes its bound notification (seL4 `receiveIPC`)

seL4's `receiveIPC` (`endpoint.c`) asks one question before it looks at the
endpoint: is the receiver's bound notification active?  If it is, the receive
is `completeSignal(ntfnPtr, thread)` — the notification's word in the badge
register, the notification idle — and the endpoint is not touched; the thread
does not block.  The model asks it once the endpoint's flow gate has admitted
the receive and its reply object is resolved, as seL4's `handleRecv` looks the
reply capability up before `receiveIPC` runs, and it gates the completion on
the notification → receiver flow — the gate a `Wait` on that notification
passes (`notificationWaitCrossCoreDispatchChecked`).  A receive denied that
flow does not complete the signal: it receives on the endpoint as if the
notification were idle, so the receiver learns nothing of the notification
(`receiveCompletesSignal_lowEquivalent`).  seL4-MCS's
`maybeDonateSchedContext` moves a context bound to the notification
(`Notification.schedContext`, which `.schedContextBind` on a notification
capability sets) to a receiver that holds none: `completeSignalArm` donates it
after the word is taken (WS-SX SX8.2). -/

/-- **seL4-MCS `receiveIPC`'s first test**: the receiver has a bound
notification, it is active (holds a pending word, seL4's `NtfnState_Active`),
and the notification's label flows to the receiver's. -/
@[inline] def receiveCompletesSignal (ctx : LabelingContext) (st : SystemState)
    (tid : SeLe4n.ThreadId) : Bool :=
  match st.getTcb? tid with
  | some t =>
      t.boundNotificationCode != 0 &&
      (match st.getNotification? ⟨t.boundNotificationCode - 1⟩ with
       | some ntfn => ntfn.pendingBadge.isSome
       | none => false) &&
      securityFlowsTo (ctx.objectLabelOf ⟨t.boundNotificationCode - 1⟩) (ctx.threadLabelOf tid)
  | none => false

/-- **seL4's `completeSignal` on the receiver**: the bound notification's word
consumed and written to the badge register (`x0`), every other register as it
was, and then seL4-MCS's `maybeDonateSchedContext`: a context bound to the
notification and to no thread is donated to a receiver holding none
(`maybeDonateSchedContext`, the bind's ok-state, the receiver's `.bound`
binding with the notification link kept), under the checked kernel's
context-label check (`maybeDonateSchedContextFlowing`): the notification's
context is lent only to a receiver the context's label flows to.  A wait that finds no word blocks,
and then, as seL4-MCS's `receiveSignal` does, returns the notification's context
where it is the waiter's own (`maybeReturnSchedContext`: seL4's writes and the
purge under seL4's guard, the receive's return; `isActive` and the donation
origin are kept).  The consumption is the one a
`Wait` on an active notification performs
(`notificationWaitCrossCoreDispatchChecked`), so a receive and a wait that
take a notification's word ask one transition. -/
@[inline] def completeSignalArm (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (notifId : SeLe4n.ObjId) (executingCore : Concurrency.CoreId) : Kernel Unit :=
  fun st =>
    match notificationWaitCrossCoreDispatchChecked ctx notifId tid executingCore st with
    | (st', .ok (some badge)) =>
        .ok ((), maybeDonateSchedContextFlowing ctx (Architecture.writeReturnFrameToTcb st' tid
          (Architecture.badgeReturnFrame st' tid badge)) notifId tid)
    | (st', .ok none) => .ok ((), maybeReturnSchedContext st' notifId tid)
    | (_, .error e) => .error e

/-- A wait that consumed a badge moved no scheduler state: the consumption is a
notification store and the waiter's IPC state, nothing on any core. -/
theorem notificationWaitOnCore_consumed_scheduler_eq {notifId : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {c : Concurrency.CoreId} {st st1 : SystemState}
    {badge : SeLe4n.Badge}
    (h : notificationWaitOnCore notifId tid c st = (st1, .ok (some badge))) :
    st1.scheduler = st.scheduler := by
  unfold notificationWaitOnCore at h
  cases hN : st.getNotification? notifId with
  | none =>
    rw [hN] at h
    by_cases hO : (st.getObject? notifId).isSome = true
    · simp only [hO, ↓reduceIte] at h; cases h
    · simp only [hO, Bool.false_eq_true, ↓reduceIte] at h; cases h
  | some ntfn =>
    rw [hN] at h
    cases hB : ntfn.pendingBadge with
    | some b =>
      simp only [hB] at h
      generalize hS : storeObject notifId _ st = rS at h
      cases rS with
      | error e => cases h
      | ok v =>
        obtain ⟨⟨⟩, stA⟩ := v
        dsimp only at h
        cases hT : storeTcbIpcState stA tid .ready with
        | error e => rw [hT] at h; cases h
        | ok stB =>
          rw [hT] at h
          cases h
          rw [storeTcbIpcState_scheduler_eq _ _ _ _ hT, storeObject_scheduler_eq _ _ _ _ hS]
    | none =>
      simp only [hB] at h
      repeat' split at h
      all_goals simp_all

/-- A wait on a notification holding a word does not block. -/
theorem notificationWaitOnCore_not_blocked_of_pending {notifId : SeLe4n.ObjId}
    {tid : SeLe4n.ThreadId} {c : Concurrency.CoreId} {st st1 : SystemState}
    {ntfn : Notification} (hN : st.getNotification? notifId = some ntfn)
    (hP : ntfn.pendingBadge.isSome = true)
    (h : notificationWaitOnCore notifId tid c st = (st1, .ok none)) : False := by
  unfold notificationWaitOnCore at h
  rw [hN] at h
  cases hB : ntfn.pendingBadge with
  | none => rw [hB] at hP; cases hP
  | some b =>
    simp only [hB] at h
    generalize hS : storeObject notifId _ st = rS at h
    cases rS with
    | error e => cases h
    | ok v =>
      obtain ⟨⟨⟩, stA⟩ := v
      dsimp only at h
      cases hT : storeTcbIpcState stA tid .ready with
      | error e => rw [hT] at h; cases h
      | ok stB => rw [hT] at h; cases h

/-- A checked wait that returns a result returned the unchecked wait's. -/
theorem notificationWaitCrossCoreDispatchChecked_ok_inner {ctx : LabelingContext}
    {notifId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId} {c : Concurrency.CoreId}
    {st st1 : SystemState} {r : Option SeLe4n.Badge}
    (h : notificationWaitCrossCoreDispatchChecked ctx notifId tid c st = (st1, .ok r)) :
    notificationWaitOnCore notifId tid c st = (st1, .ok r) := by
  unfold notificationWaitCrossCoreDispatchChecked at h
  by_cases hF : securityFlowsTo (ctx.objectLabelOf notifId) (ctx.threadLabelOf tid) = true
  · by_cases hE : notificationBoundElsewhere st notifId tid = true
    · simp only [hF, hE, ↓reduceIte] at h; cases h
    · simp only [hF, hE, Bool.false_eq_true, ↓reduceIte] at h; exact h
  · simp only [hF, Bool.false_eq_true, ↓reduceIte] at h; cases h

/-- **A receive that completes its bound notification** took the wait's
consumption: the consumed word, a pre-state scheduler, and the badge register
written over it. -/
theorem completeSignalArm_consumes {ctx : LabelingContext} {tid : SeLe4n.ThreadId}
    {c : Concurrency.CoreId} {st st' : SystemState}
    (hSig : receiveCompletesSignal ctx st tid = true)
    (h : completeSignalArm ctx tid (receiverBoundNotification st tid) c st = .ok ((), st')) :
    ∃ st1 badge,
      notificationWaitCrossCoreDispatchChecked ctx (receiverBoundNotification st tid) tid c st =
        (st1, .ok (some badge)) ∧
      st1.scheduler = st.scheduler ∧
      st' = maybeDonateSchedContextFlowing ctx
        (Architecture.writeReturnFrameToTcb st1 tid (Architecture.badgeReturnFrame st1 tid badge))
        (receiverBoundNotification st tid) tid := by
  unfold completeSignalArm at h
  generalize hW : notificationWaitCrossCoreDispatchChecked ctx (receiverBoundNotification st tid) tid c st = w at h
  obtain ⟨st1, r⟩ := w
  cases r with
  | error e => cases h
  | ok o =>
    cases o with
    | some badge =>
      cases h
      exact ⟨st1, badge, rfl, notificationWaitOnCore_consumed_scheduler_eq
        (notificationWaitCrossCoreDispatchChecked_ok_inner hW), rfl⟩
    | none =>
      exfalso
      have hI := notificationWaitCrossCoreDispatchChecked_ok_inner hW
      unfold receiveCompletesSignal at hSig
      unfold receiverBoundNotification at hI
      cases hT : st.getTcb? tid with
      | none => rw [hT] at hSig; cases hSig
      | some t =>
        rw [hT] at hSig hI
        simp only [Bool.and_eq_true] at hSig
        obtain ⟨⟨_, hPend⟩, _⟩ := hSig
        cases hN : st.getNotification? ⟨t.boundNotificationCode - 1⟩ with
        | none => rw [hN] at hPend; cases hPend
        | some ntfn =>
          rw [hN] at hPend
          exact notificationWaitOnCore_not_blocked_of_pending hN hPend hI

/-- **The completion's scheduler change is the donation's**: the wait's
consumption keeps the scheduler (`notificationWaitOnCore_consumed_scheduler_eq`,
which stays the wait's own statement) and so does the badge frame, so the arm's
state is the checked donation (`maybeDonateSchedContextFlowing`) over a state
whose scheduler is the entry state's.  Every scheduler write the arm makes is the
bind's. -/
theorem completeSignalArm_scheduler_of_donation {ctx : LabelingContext} {tid : SeLe4n.ThreadId}
    {c : Concurrency.CoreId} {st st' : SystemState}
    (hSig : receiveCompletesSignal ctx st tid = true)
    (h : completeSignalArm ctx tid (receiverBoundNotification st tid) c st = .ok ((), st')) :
    ∃ stD, stD.scheduler = st.scheduler ∧
      st' = maybeDonateSchedContextFlowing ctx stD (receiverBoundNotification st tid) tid := by
  obtain ⟨st1, badge, -, hS, rfl⟩ := completeSignalArm_consumes hSig h
  exact ⟨_, (Architecture.writeReturnFrameToTcb_scheduler_eq _ _ _).trans hS, rfl⟩

/-- A receive whose notification → receiver flow is denied does not complete
the signal, whatever the notification holds. -/
theorem receiveCompletesSignal_false_of_flowDenied (ctx : LabelingContext)
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hDeny : securityFlowsTo (ctx.objectLabelOf (receiverBoundNotification st tid))
      (ctx.threadLabelOf tid) = false) :
    receiveCompletesSignal ctx st tid = false := by
  unfold receiveCompletesSignal
  unfold receiverBoundNotification at hDeny
  cases h : st.getTcb? tid with
  | none => rfl
  | some t => rw [h] at hDeny; simp [hDeny]

/-- The TCB view the completion test reads: a thread's bound-notification code. -/
def tcbBoundNotificationCodeOf? : Option KernelObject → Option Nat
  | some (.tcb t) => some t.boundNotificationCode
  | _ => none

/-- The notification view the completion test reads: whether it holds a word. -/
def notificationPendingOf? : Option KernelObject → Option Bool
  | some (.notification n) => some n.pendingBadge.isSome
  | _ => none

theorem tcbBoundNotificationCodeOf?_project (ctx : LabelingContext) (observer : IfObserver)
    (o : Option KernelObject) :
    tcbBoundNotificationCodeOf? (o.map (projectKernelObject ctx observer)) =
      tcbBoundNotificationCodeOf? o := by
  rcases o with _ | k
  · rfl
  · cases k <;> rfl

theorem notificationPendingOf?_project (ctx : LabelingContext) (observer : IfObserver)
    (o : Option KernelObject) :
    notificationPendingOf? (o.map (projectKernelObject ctx observer)) =
      notificationPendingOf? o := by
  rcases o with _ | k
  · rfl
  · cases k <;> rfl

/-- The completion test, read through the two views. -/
theorem receiveCompletesSignal_eq_views (ctx : LabelingContext) (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    receiveCompletesSignal ctx st tid =
      match tcbBoundNotificationCodeOf? st.objects[tid.toObjId]? with
      | some c =>
          c != 0 && (notificationPendingOf? st.objects[(⟨c - 1⟩ : SeLe4n.ObjId)]?).getD false &&
            securityFlowsTo (ctx.objectLabelOf ⟨c - 1⟩) (ctx.threadLabelOf tid)
      | none => false := by
  unfold receiveCompletesSignal SystemState.getTcb? SystemState.getNotification?
  cases h : st.objects[tid.toObjId]? with
  | none => rfl
  | some k =>
    cases k <;> try rfl
    rename_i t
    simp only [tcbBoundNotificationCodeOf?]
    cases h' : st.objects[(⟨t.boundNotificationCode - 1⟩ : SeLe4n.ObjId)]? with
    | none => rfl
    | some k' => cases k' <;> rfl

/-- **Non-interference of the completion test**: two states an observer
cannot tell apart give the same answer, for a receiver the observer sees.  The
test reads the receiver's TCB (its bound notification's code, which the
projection keeps) and, only when the notification's label flows to the
receiver's, the notification's pending word -- a notification the observer then
sees too (`securityFlowsTo_trans`).  So a receive's choice between completing
its bound notification and receiving on its endpoint reveals nothing the
observer could not already read. -/
theorem receiveCompletesSignal_lowEquivalent (ctx : LabelingContext)
    (observer : IfObserver) (st₁ st₂ : SystemState) (tid : SeLe4n.ThreadId)
    (hLow : lowEquivalent ctx observer st₁ st₂)
    (hTcbObs : objectObservable ctx observer tid.toObjId = true)
    (hThreadObs : threadObservable ctx observer tid = true) :
    receiveCompletesSignal ctx st₁ tid = receiveCompletesSignal ctx st₂ tid := by
  have hObj : ∀ oid, objectObservable ctx observer oid = true →
      (st₁.objects[oid]?).map (projectKernelObject ctx observer) =
        (st₂.objects[oid]?).map (projectKernelObject ctx observer) := by
    intro oid hO
    have h := congrFun (congrArg ObservableState.objects hLow) oid
    simpa [projectState, projectObjects, hO, SystemState.getObject?] using h
  have hT : tcbBoundNotificationCodeOf? st₁.objects[tid.toObjId]? =
      tcbBoundNotificationCodeOf? st₂.objects[tid.toObjId]? := by
    rw [← tcbBoundNotificationCodeOf?_project ctx observer,
      ← tcbBoundNotificationCodeOf?_project ctx observer (st₂.objects[tid.toObjId]?),
      hObj _ hTcbObs]
  rw [receiveCompletesSignal_eq_views, receiveCompletesSignal_eq_views, hT]
  cases tcbBoundNotificationCodeOf? st₂.objects[tid.toObjId]? with
  | none => rfl
  | some c =>
    by_cases hF : securityFlowsTo (ctx.objectLabelOf ⟨c - 1⟩) (ctx.threadLabelOf tid) = true
    · have hNO : objectObservable ctx observer ⟨c - 1⟩ = true :=
        securityFlowsTo_trans _ _ _ hF hThreadObs
      have hN : notificationPendingOf? st₁.objects[(⟨c - 1⟩ : SeLe4n.ObjId)]? =
          notificationPendingOf? st₂.objects[(⟨c - 1⟩ : SeLe4n.ObjId)]? := by
        rw [← notificationPendingOf?_project ctx observer,
          ← notificationPendingOf?_project ctx observer (st₂.objects[(⟨c - 1⟩ : SeLe4n.ObjId)]?),
          hObj _ hNO]
      simp only [hN]
    · simp only [Bool.not_eq_true] at hF
      simp [hF]


/-- **The checked receive arm once its gate has passed and its busy reply is
cancelled** (`dispatchWithCapChecked`'s `.receive` arm, WS-SX SX4): the reply
object resolved, the per-core receive with its capabilities, the rendezvous
hand-off and the delivery staged. -/
def receiveResolvedArm (ctx : LabelingContext) (decoded : SyscallDecodeResult) (gate : SyscallGate)
    (tid : SeLe4n.ThreadId) (epId : SeLe4n.ObjId) (executingCore : Concurrency.CoreId) :
    Kernel Unit :=
  fun st =>
      -- PR #822 review: an explicit (length ≥ 1) bad reply cap fails before the
      -- receive (mirrors the unchecked arm); only length 0 means "no reply object".
      match resolveRecvReplyId gate decoded st with
      | .error e => .error e
      | .ok replyIdOpt =>
        -- seL4-MCS `receiveIPC`: an active bound notification is completed
        -- (`completeSignal`) and the endpoint is not touched, the notification →
        -- receiver flow admitting it (`receiveCompletesSignal`).
        if receiveCompletesSignal ctx st tid then
          completeSignalArm ctx tid (receiverBoundNotification st tid) executingCore st
        else
        -- WS-SX SX7.2: `NBRecv` with no sender waiting returns at once,
        -- `0` in its badge register (seL4's `doNBRecvFailedTransfer`).
        if receiveFindsNothing (Syscall.wordReceiveBlocks (callerSyscallWord st tid)) st epId then
          .ok ((), Architecture.nbRecvFailedTransfer st tid)
        else
        -- WS-SM SM6.D (PR #822 review): route through the per-core receive
        -- transition (the endpoint→receiver flow is already gated above, so the
        -- *unchecked* `endpointReceiveDualOnCore` is correct here).  Per-core block
        -- placement mirrors the unchecked arm; boot-core-equivalent to the prior
        -- `endpointReceiveDualChecked` when the flow is permitted.
        -- WS-SM SM6.D (#7.2 fold): reply object threaded into the per-core receive
        -- transition (the endpoint→receiver flow is gated above); the dequeued
        -- `Call` caller is linked atomically (former `linkReceivedCaller` step).
        -- PR #873 round 6: the checked twin of the unchecked arm's WithCaps
        -- routing — a send that parked before its receiver arrived delivers
        -- its capabilities here too, gated on the authority the sender
        -- recorded on the message.  The endpoint→receiver flow is gated
        -- above, so the *unchecked* per-core WithCaps receive is correct
        -- here for the same reason the bare one was.
        -- seL4-MCS `receiveIPC`: a blocking receive that did not complete its
        -- bound notification returns that notification's context first, before
        -- the endpoint is looked at (`maybeReturnSchedContext`, WS-SX SX8.2), so
        -- a passive server can then be donated a caller's context.
        match endpointReceiveDualWithCapsOnCore epId tid replyIdOpt executingCore
            (receiveReturnSchedContext (Syscall.wordReceiveBlocks (callerSyscallWord st tid)) st tid)
            with
        | (st', .ok (dequeued, summary, _sgi)) =>
            -- **WS-OD OD3.6**: the checked twin of the unchecked arm's
            -- `maybeDonateSchedContext` step, and the *same* definition, at
            -- the lend admission of the caller it takes (WS-SX ruling (u)):
            -- the call's context is lent only where the caller's label flows
            -- to the context's (`receiveLendAdmits`, the call's admission of
            -- the send queue's head on the state the arm is handed); otherwise
            -- the receive goes on and lends nothing, as at the call
            -- rendezvous.  The admission reads that caller's own binding and
            -- static labels alone (`callLendAdmits_congr`).
            --
            -- **WS-OD OD3.14**: the priority half runs on every `Call`
            -- rendezvous, lent or not -- `projectKernelObject` strips
            -- `pipBoost` (AJ2-B), and the run-queue re-bucketing the walk
            -- performs is bounded by `receiveRendezvousHandoffWriteSet`,
            -- exactly as the flow-checked `.call` arm's own walk is bounded
            -- by `endpointCallLiveWriteSet`.
            match applyReceiveRendezvousHandoff st' tid dequeued executingCore
                (receiveLendAdmits ctx st epId) with
            | .error e => .error e
            | .ok stDon =>
              -- WS-RA RA.B.6: stage the non-blocking consume's delivery (the
              -- checked twin of the unchecked arm's staging; the endpoint
              -- flow gate above governs the consumed message).  PR #873
              -- round 6: `extraCaps` is the summary's INSTALLED count, the
              -- same honest figure the send and call paths report — it was
              -- hardcoded to zero while the receive installed nothing.
              .ok ((), Architecture.stageDeliveredMessage
                        stDon tid
                        summary.capInfo)
        | (_, .error e) => .error e

/-- **The receiver is ready in IPC**: a TCB whose IPC state is `.ready`, as the
thread running a syscall is. -/
@[inline] def receiverIpcReady (st : SystemState) (tid : SeLe4n.ThreadId) : Bool :=
  match st.getTcb? tid with
  | some t => decide (t.ipcState = .ready)
  | none => false

theorem receiverIpcReady_iff (st : SystemState) (tid : SeLe4n.ThreadId) :
    receiverIpcReady st tid = true ↔ ∃ t, st.getTcb? tid = some t ∧ t.ipcState = .ready := by
  unfold receiverIpcReady
  cases st.getTcb? tid with
  | none => simp
  | some t => simp

/-- **seL4-MCS `handleReplyRecv` when its receive completes a signal.**
`SysReplyRecv` runs `handleInvocation` on the reply capability, whose
`doReplyTransfer` answers the caller, and then `handleRecv`, whose
`receiveIPC` finds the receiver's bound notification active and runs
`completeSignal` instead of touching the endpoint.  So the answer is the
`.reply` arm's own transition (`replyTransferOnCoreChecked`: the caller woken
with the reply or its fault answered, the donated context returned, the
priority-inheritance boost reverted), and the receive is the wait's
consumption with the badge register written (`completeSignalArm`).

The receive tests the notification on the state the reply left, as seL4's
does, for the replier it leaves running (`receiverIpcReady`): the arm chose
this path on the entry state, and the reply writes no notification, not the
replier's binding and not its IPC state, so the tests agree
(`replyRecvCompletesSignalArm_completes`) and the last branch, which returns
with the reply made and nothing received, is never taken.

No receive leg runs, so the reply object is not re-linked and no donation is
made: a passive server whose context the reply returned is left descheduled,
as seL4-MCS leaves a thread with no scheduling context unschedulable. -/
def replyRecvCompletesSignalArm (ctx : LabelingContext) (tid prevCaller : SeLe4n.ThreadId)
    (label : Nat) (msg : IpcMessage) (grant : Bool) (executingCore : Concurrency.CoreId) :
    Kernel Unit :=
  fun st =>
    match replyTransferOnCoreChecked ctx tid prevCaller (replyRecvReplyMessageInfo label msg)
        msg.registers msg grant executingCore st with
    | .error e => .error e
    | .ok ((), st1) =>
        if receiveCompletesSignal ctx st1 tid && receiverIpcReady st1 tid then
          completeSignalArm ctx tid (receiverBoundNotification st1 tid) executingCore st1
        else .ok ((), st1)

/-- **The two halves of a reply-receive that completes a signal**: the reply
transition, then, when the receive's test holds on the state it left, the
receive's completion of the bound notification; otherwise the reply alone. -/
theorem replyRecvCompletesSignalArm_split {ctx : LabelingContext}
    {tid prevCaller : SeLe4n.ThreadId} {label : Nat} {msg : IpcMessage} {grant : Bool}
    {c : Concurrency.CoreId} {st st' : SystemState}
    (h : replyRecvCompletesSignalArm ctx tid prevCaller label msg grant c st = .ok ((), st')) :
    ∃ st1, replyTransferOnCoreChecked ctx tid prevCaller (replyRecvReplyMessageInfo label msg)
        msg.registers msg grant c st = .ok ((), st1) ∧
      (st' = st1 ∨
        (receiveCompletesSignal ctx st1 tid = true ∧
          (∃ t, st1.getTcb? tid = some t ∧ t.ipcState = .ready) ∧
          completeSignalArm ctx tid (receiverBoundNotification st1 tid) c st1 = .ok ((), st'))) := by
  unfold replyRecvCompletesSignalArm at h
  generalize hR : replyTransferOnCoreChecked ctx tid prevCaller
    (replyRecvReplyMessageInfo label msg) msg.registers msg grant c st = r at h
  cases r with
  | error e => cases h
  | ok v =>
    obtain ⟨⟨⟩, st1⟩ := v
    refine ⟨st1, rfl, ?_⟩
    dsimp only at h
    by_cases hSig : (receiveCompletesSignal ctx st1 tid && receiverIpcReady st1 tid) = true
    · rw [if_pos hSig] at h
      simp only [Bool.and_eq_true] at hSig
      exact .inr ⟨hSig.1, (receiverIpcReady_iff st1 tid).mp hSig.2, h⟩
    · rw [if_neg hSig] at h
      cases h
      exact .inl rfl

/-- ...and the completion, when it runs, is the wait's consumption with the badge
register written over it, moving no scheduler state. -/
theorem replyRecvCompletesSignalArm_cases {ctx : LabelingContext}
    {tid prevCaller : SeLe4n.ThreadId} {label : Nat} {msg : IpcMessage} {grant : Bool}
    {c : Concurrency.CoreId} {st st' : SystemState}
    (h : replyRecvCompletesSignalArm ctx tid prevCaller label msg grant c st = .ok ((), st')) :
    ∃ st1, replyTransferOnCoreChecked ctx tid prevCaller (replyRecvReplyMessageInfo label msg)
        msg.registers msg grant c st = .ok ((), st1) ∧
      (st' = st1 ∨
        ∃ st2 badge, receiveCompletesSignal ctx st1 tid = true ∧
          (∃ t, st1.getTcb? tid = some t ∧ t.ipcState = .ready) ∧
          notificationWaitCrossCoreDispatchChecked ctx (receiverBoundNotification st1 tid) tid c
            st1 = (st2, .ok (some badge)) ∧
          st2.scheduler = st1.scheduler ∧
          st' = maybeDonateSchedContextFlowing ctx (Architecture.writeReturnFrameToTcb st2 tid
            (Architecture.badgeReturnFrame st2 tid badge)) (receiverBoundNotification st1 tid) tid) := by
  obtain ⟨st1, hR, hOr⟩ := replyRecvCompletesSignalArm_split h
  refine ⟨st1, hR, ?_⟩
  rcases hOr with hEq | ⟨hSig, hRdy, hC⟩
  · exact .inl hEq
  · obtain ⟨st2, badge, hW, hS, hP⟩ := completeSignalArm_consumes hSig hC
    exact .inr ⟨st2, badge, hSig, hRdy, hW, hS, hP⟩

/-- T6-I/M-IF-1/U5-A: Policy-checked dispatch — replaces unchecked operations
with their information-flow-checked equivalents. All cross-domain operations
(IPC send/receive/call/reply, CSpace mint/copy/move, service register) are
gated by `securityFlowsTo` before execution via enforcement wrappers.

U5-B/U-M01: `.call` now routes through `endpointCallChecked` wrapper instead
of an inline `securityFlowsTo` guard, ensuring consistent enforcement layer.

U5-C/U-M04 (updated WS-SM SM6.C/D): `.reply` routes through the
info-flow-checked **cross-core** dispatch `endpointReplyCrossCoreDispatchChecked`
(the SM-IF flow gate that superseded the single-core `endpointReplyChecked`
wrapper) for defense-in-depth, even though reply caps are single-use authority;
the single-use consume is folded into `endpointReplyOnCore` (PR #827 review #3).

**Design**: Operations that don't cross domain boundaries (CSpace delete,
lifecycle retype, VSpace map/unmap, service revoke/query) are left unchecked
because they derive authority entirely from capability possession.

V2-A/V2-C: `notificationSignal`, `notificationWait`, and `replyRecv` are now
in the `SyscallId` enum and wired into both dispatch paths. The checked variants
`notificationSignalChecked`, `notificationWaitChecked`, and
`endpointReplyRecvChecked` gate cross-domain flows.

V8-H: Capability-only arms delegate to `dispatchCapabilityOnly`.

**The caller/core pair.**  This tier takes `tid` and `executingCore` as given.
The entry reaches it through `dispatchSyscallChecked`, whose first step refuses
a `tid` that is not current on `executingCore`
(`dispatchSyscallChecked_ok_caller_current`), so it only ever runs on a
consistent pair. -/
def dispatchWithCapChecked (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability) : Kernel Unit :=
  match dispatchCapabilityOnly decoded cap tid executingCore with
  | some k => dispatchCapabilityOnlyChecked ctx decoded.syscallId decoded.msgInfo.extraCaps tid cap k
  | none =>
  match decoded.syscallId with
  -- T6-I: IPC send — checked for sender→endpoint flow
  | .send =>
    match cap.target with
    | .object epId =>
      fun st =>
        -- WS-SX SX7.2: `NBSend` to an endpoint no receiver waits on drops the
        -- message (seL4's `sendIPC` with `blocking = false`).
        if sendDropsMessage ctx (Syscall.wordSendBlocks (callerSyscallWord st tid)) st tid epId then
          .ok ((), st)
        else
        -- WS-ZA ZA4.7 (seL4 `sendIPC`): the send is handed only the badge and
        -- the grant bit of the invoked capability.  The words are read from the
        -- sender's own frame at delivery, and the extra capabilities are looked up
        -- only on the arm that delivers (a send that blocks resolves none; its
        -- receiver looks them up at the rendezvous).
        let payload : SendPayload := .frame cap.badge (cap.rights.mem .grant) (cap.rights.mem .grantReply)
        -- AH1-B (H-01 fix): Pass capability transfer params to checked send
        -- WS-SM SM6.D (PR #822 review): clear the woken receiver's server-first reply
        -- stash (mirrors the unchecked `.send` arm).
        let wokenReceiver? := (st.getEndpoint? epId).bind (·.receiveQ.head)
        -- WS-SM SM8.B (PR #861 review round 10): the cross-core checked send
        -- (mirrors the unchecked arm; `endpointSendDualChecked` was boot-pinned
        -- through `endpointSendDualWithCaps`).  Bounds first, then the
        -- sender→endpoint flow gate, then the per-core transition.
        match endpointSendCrossCoreDispatchChecked ctx epId tid payload executingCore st with
        | (_, .error e) => .error e
        | (st', .ok (summary, _)) =>
            match clearWokenReceiverStash wokenReceiver? st' with
            | .error e => .error e
            | .ok ((), st'') =>
                -- WS-RA RA.B.5b: the checked twin of the unchecked arm's
                -- woken-receiver staging (the send's own flow gate ran inside
                -- the checked dispatch, before the wake).  PR #866 round-2:
                -- `extraCaps` = the summary's INSTALLED count, like the
                -- unchecked arm.
                .ok ((), Architecture.stageWokenDelivery st'' wokenReceiver?
                          summary.capInfo)
    | _ => fun _ => .error (.invalidCapability 0)
  -- T6-I: IPC receive — checked for endpoint→receiver flow
  | .receive =>
    match cap.target with
    | .object epId =>
      -- WS-SM SM6.D (faithful seL4-MCS receive linkage, flow-checked): mirrors the
      -- unchecked `.receive` arm — resolve the server-supplied reply cap at
      -- `RecvArgs.replyCPtr` and, on a `Call` rendezvous, link the woken caller to
      -- the server's reply object.
      fun st =>
        -- WS-SM SM6.D (PR #822 review, IF-ordering): gate the endpoint→receiver flow
        -- *before* probing the reply cap.  `resolveRecvReplyId` validates the reply
        -- cap and scans `replyIsStashed` across all TCBs, so running it ahead of the
        -- flow gate let a receiver with a copied reply cap distinguish "some blocked
        -- server has this Reply stashed" (`.replyCapInvalid`) from "no stash"
        -- (`.flowDenied`) even when `endpoint→receiver` is denied — a covert channel
        -- on reply state the low projection otherwise strips.  This is the exact
        -- predicate `endpointReceiveDualChecked` applies internally, so a *permitted*
        -- receive is behaviourally unchanged; a denied receive now returns
        -- `.flowDenied` without ever probing reply state.
        -- WS-SM SM8.C: the gate is the global lattice check AND this endpoint's
        -- configured override (`endpointFlowGate`).  A conjunction, so an
        -- override can only narrow, and an unconfigured deployment is unchanged
        -- (`endpointFlowGate_eq_securityFlowsTo_of_no_override`).
        if !endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) then
          .error .flowDenied
        else
          -- WS-SX SX4: a reply busy with another thread has that thread's IPC
          -- cancelled first (seL4-MCS `receiveIPC`'s `cancelIPC(replyTCB)`), every
          -- check that can refuse the receive asked of the state it was handed;
          -- the cancel is committed and the receive runs on the cancelled state.
          receiveResolvedArm ctx decoded gate tid epId executingCore
            (cancelRecvBusyReply ctx tid gate decoded executingCore st)
    | _ => fun _ => .error (.invalidCapability 0)
  -- U5-B/U-M01: IPC call — routed through enforcement wrapper (previously inline check).
  -- This ensures `.call` uses the same enforcement layer as all other policy-gated
  -- operations, rather than an ad-hoc inline `securityFlowsTo` guard.
  | .call =>
    match cap.target with
    | .object epId =>
      fun st =>
        -- WS-ZA ZA4.7 (seL4 `sendIPC`): the send is handed only the badge and
        -- the grant bit of the invoked capability.  The words are read from the
        -- sender's own frame at delivery, and the extra capabilities are looked up
        -- only on the arm that delivers (a send that blocks resolves none; its
        -- receiver looks them up at the rendezvous).
        let payload : SendPayload := .frame cap.badge (cap.rights.mem .grant) (cap.rights.mem .grantReply)
        -- WS-SM SM6.A (live cross-core `.call`): route the checked `.call`
        -- through the cross-core dispatch.  `endpointCallCrossCoreDispatchChecked`
        -- is the cross-core analogue of `endpointCallChecked` + inline donation:
        -- the same SM-IF flow guard, then the cross-core WithCaps call (the
        -- receiver is woken on its *home* core via `wakeThread`, surfacing a
        -- `.reschedule` SGI the FFI seam fires), then `applyCallDonation` + PIP.
        -- The caller is descheduled from `executingCore` (the core running this
        -- syscall, `currentOnCore executingCore`); the cross-core syscall seam
        -- recovers the SGI from the `(pre, post)` diff.
        -- WS-SM SM6.D (#7.3b fold): the server-first reply linkage is now atomic
        -- with the rendezvous inside `endpointCallOnCore` (`linkServerStashedReply`);
        -- mirror the unchecked arm — no separate post-dispatch link step.
        -- WS-RA RA.B.5b: the woken receiver's staged frame (checked twin; the
        -- call's own flow gate ran inside the checked dispatch, before the wake).
        let wokenReceiver? := (st.getEndpoint? epId).bind (·.receiveQ.head)
        match endpointCallCrossCoreDispatchChecked ctx epId tid payload executingCore st with
        -- PR #866 round-2: `extraCaps` = the summary's INSTALLED count, like
        -- the unchecked arm.
        | (st', .ok (summary, _)) =>
            .ok ((), Architecture.stageWokenDelivery st' wokenReceiver?
                      summary.capInfo)
        | (_, .error e) => .error e
    | _ => fun _ => .error (.invalidCapability 0)
  -- U5-C/U-M04: Reply — routed through enforcement wrapper for defense-in-depth.
  -- In seL4, the reply capability is single-use authority consumed upon use.
  -- The flow check here is a defense-in-depth measure ensuring the reply path
  -- is auditable and consistent with all other cross-domain operations.
  | .reply =>
    match cap.target with
    | .replyCap rid =>
      fun st =>
        let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
        -- WS-SM SM6.D (seL4-MCS reply object, checked): resolve the reply cap's
        -- `ReplyId` to its recorded caller (`reply.caller`), then route through
        -- the info-flow-checked cross-core dispatch (same SM-IF flow guard
        -- `securityFlowsTo replierLabel callerLabel`, caller woken on its *home*
        -- core, donated-SC return, cross-core PIP reversion).  The single-use
        -- linkage consume is **folded into `endpointReplyOnCore`** (PR #827
        -- review #3) — atomic with the delivery, no separate dispatch step.
        -- Fails closed (`.replyCapInvalid`) on a dangling reply or an unlinked
        -- caller.
        -- WS-RR RR7.11: the answered thread is `replyAnsweredCaller?`, the same
        -- resolution the unchecked arm and the declared-footprint resolver read.
        match replyAnsweredCaller? st rid with
        | none => .error .replyCapInvalid
        | some callerTid =>
            -- WS-SM SM6.D (PR #822 review, IF-ordering): a denied replier→caller flow
            -- must be **indistinguishable** from an unlinked/consumed reply.  Probing
            -- `reply.caller` (above) is unavoidable — the flow gate needs the caller
            -- identity — so we collapse a denied flow to the *same* `.replyCapInvalid`
            -- the `none` arms return, rather than letting `.flowDenied` leak that the
            -- Reply *is* linked (to a caller the holder may not flow to).  When the
            -- flow is permitted the body is exactly the prior checked dispatch +
            -- consume, so `checkedDispatch_reply_eq_unchecked_when_allowed` holds.
            if securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf callerTid) then
              -- WS-RR RR4.14/RR4.15: seL4's `doReplyTransfer` fault branch, in
              -- the checked twin.  Ordinary callers take the prior body verbatim
              -- (checked cross-core reply + the RA.B.5b delivered-message
              -- staging); a faulted caller takes the fault reply.  Both are
              -- already behind the replier→caller flow gate above, which is the
              -- same test the checked reply dispatch applies — so the arm equals
              -- the unchecked one exactly when that gate admits
              -- (`replyTransferOnCoreChecked_eq_unchecked_of_flow_allowed`).
              replyTransferOnCoreChecked ctx tid callerTid decoded.msgInfo decoded.msgRegs
                { registers := body, badge := cap.badge } (cap.rights.mem .grant) executingCore st
            else .error .replyCapInvalid
    | _ => fun _ => .error (.invalidCapability 0)
  -- T6-I: CSpace mint — checked for source→destination CNode flow
  -- U5-H/U-M03: Badge value 0 is treated as "no badge" by design, matching seL4
  -- semantics where badge 0 indicates an unbadged capability.
  -- C-01: cspaceMintChecked delegates to cspaceMintWithCdt for CDT tracking.
  | .cspaceMint =>
    match cap.target with
    | .object cnodeId =>
        fun st => match decodeCSpaceMintArgs decoded with
        | .error e => .error e
        | .ok args =>
            if !cnodeInvoked cnodeId st then .error .objectNotFound else
            match resolveCNodeOpSlots tid cap args.destIndex args.destDepth
                (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0)
                args.srcIndex args.srcDepth st with
            | .error e => .error e
            | .ok (src, dst) =>
                let badge : Option SeLe4n.Badge :=
                  if args.badge.word = 0 then none else some args.badge
                cspaceMintChecked ctx src dst (mintMaskedRights st src args.rights) badge st
    | _ => fun _ => .error (.invalidCapability 0)
  -- T6-I: CSpace copy — checked for source→destination CNode flow
  | .cspaceCopy =>
    match cap.target with
    | .object cnodeId =>
        fun st => match decodeCSpaceCopyArgs decoded with
        | .error e => .error e
        | .ok args =>
            if !cnodeInvoked cnodeId st then .error .objectNotFound else
            match resolveCNodeOpSlots tid cap args.destIndex args.destDepth
                (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0)
                args.srcIndex args.srcDepth st with
            | .error e => .error e
            | .ok (src, dst) => cspaceCopyChecked ctx src dst args.rights st
    | _ => fun _ => .error (.invalidCapability 0)
  -- T6-I: CSpace move — checked for source→destination CNode flow
  | .cspaceMove =>
    match cap.target with
    | .object cnodeId =>
        fun st => match decodeCSpaceMoveArgs decoded with
        | .error e => .error e
        | .ok args =>
            if !cnodeInvoked cnodeId st then .error .objectNotFound else
            match resolveCNodeOpSlots tid cap args.destIndex args.destDepth
                (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0)
                args.srcIndex args.srcDepth st with
            | .error e => .error e
            | .ok (src, dst) => cspaceMoveChecked ctx src dst st
    | _ => fun _ => .error (.invalidCapability 0)
  -- V8-H/D1: cspaceDelete, vspaceMap, vspaceUnmap, serviceRevoke,
  -- serviceQuery, schedContextConfigure, schedContextBind, schedContextUnbind,
  -- tcbSuspend, tcbResume are all handled by dispatchCapabilityOnly above.
  -- T6-I: Service register — checked for thread→service flow
  -- WS-SX SX6.7: invoked on the service-registry capability; the endpoint the
  -- service is registered on is extra capability 0 (`resolveServiceEndpoint`).
  | .serviceRegister =>
    match cap.target with
    | .serviceRegistry _ =>
      fun st => match decodeServiceRegisterArgs decoded with
      | .error e => .error e
      | .ok args =>
          serviceEndpointArm .serviceRegister tid decoded.msgInfo.extraCaps (fun epCap _ st =>
            let iface : InterfaceSpec := {
              ifaceId         := args.interfaceId
              methodCount     := args.methodCount
              maxMessageSize  := args.maxMessageSize
              maxResponseSize := args.maxResponseSize
              requiresGrant   := args.requiresGrant
            }
            let reg : ServiceRegistration := {
              iface := iface
              endpointCap := epCap
            }
            registerServiceChecked ctx tid reg st) st
    | _ => fun _ => .error (.invalidCapability 0)
  -- V2-A/T6-I: Notification signal — checked for signaler→notification flow
  | .notificationSignal =>
    match cap.target with
    | .object notifId =>
      fun st =>
          -- WS-SM SM6.B (live checked bound-aware cross-core signal): the
          -- info-flow-checked analogue of the unchecked arm, gating on
          -- `securityFlowsTo signaler→notification` before the bound-aware
          -- cross-core dispatch.
          -- WS-SX SX7: the wake writes the badge into the woken thread's badge
          -- register and clears a woken bound receiver's server-first reply stash
          -- itself (`TCB.signalBoundWoken`; seL4's `sendSignal` runs `cancelIPC`,
          -- whose `reply_unlink` drops the receiver's reply), so nothing runs
          -- after it.
          match notificationSignalBoundCrossCoreDispatchChecked ctx notifId tid cap.signalBadge executingCore st with
          | (st', .ok _) =>
              .ok ((), st')
          | (_, .error e) => .error e
    | _ => fun _ => .error (.invalidCapability 0)
  -- V2-A/T6-I: Notification wait — checked for notification→waiter flow
  | .notificationWait =>
    match cap.target with
    | .object notifId =>
      fun st =>
        -- WS-SX SX7.2: `NBWait` (or `NBRecv`) on a notification with no pending
        -- signal returns at once, `0` in its badge register (seL4's
        -- `receiveSignal` with `isBlocking = false`, `doNBRecvFailedTransfer`).
        if waitFindsNothing ctx (Syscall.wordReceiveBlocks (callerSyscallWord st tid)) st tid
            notifId then
          .ok ((), Architecture.nbRecvFailedTransfer st tid)
        else
        -- WS-SM SM6.B: per-core checked cross-core wait (gates notification→waiter
        -- flow, then deschedules the caller on its own core); the consumed badge
        -- is staged by `completeSignalArm`, the one body the wait and the receive
        -- that completes its bound notification share (WS-SX SX8.2).
        completeSignalArm ctx tid notifId executingCore st
    | _ => fun _ => .error (.invalidCapability 0)
  -- V2-C/T6-I: ReplyRecv — checked for both reply and receive legs
  | .replyRecv =>
    match cap.target with
    | .object epId =>
      -- WS-SM SM6.D (faithful checked `.replyRecv`): gate BOTH legs — the receive leg
      -- (`securityFlowsTo endpoint→receiver`) and the reply leg (`securityFlowsTo
      -- receiver→prevCaller`) — around the *same* `replyRecvTransferOnCore` as the unchecked
      -- arm, so `checkedDispatch_replyRecv_eq_unchecked_when_allowed` stays provable.
      -- WS-SM SM6.D (PR #822 review, IF-ordering): the receive-leg flow is independent
      -- of the reply cap, so it is checked **first** — a denied receive returns
      -- `.flowDenied` without `resolveReplyRecvReply` ever probing reply state.  The
      -- reply-leg gate needs `prevCaller` (so the resolve is unavoidable there), but a
      -- denied reply-leg flow collapses to the *same* `.replyCapInvalid` a resolve
      -- failure returns, rather than leaking via `.flowDenied` that the reply *is*
      -- linked to an outstanding caller the receiver may not flow to.
      fun st =>
        -- WS-SM SM8.C: the receive leg carries the endpoint override too; the
        -- reply leg below deliberately does not (the override governs flows that
        -- cross this endpoint, and `receiver → prevCaller` does not).
        if !endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) then
          .error .flowDenied
        else
          -- WS-SX SX6.1: the reply half is seL4-MCS's `handleInvocation` with
          -- `isBlocking = false` on the reply capability: an extra capability
          -- of the message that does not look up skips the reply with no fault,
          -- and the receive half (`handleRecv`) still runs, as `.receive` runs.
          match callerExtraCapsFault? st tid decoded.msgInfo.extraCaps with
          | some _ =>
            receiveResolvedArm ctx decoded gate tid epId executingCore
              (cancelRecvBusyReply ctx tid gate decoded executingCore st)
          | none =>
          match resolveReplyRecvReply gate decoded st with
          | .error e => .error e
          -- WS-SX SX7.2: a reply with no caller to answer replies to no one
          -- (seL4-MCS `doReplyTransfer` returns), and the receive still runs.
          | .ok none =>
            receiveResolvedArm ctx decoded gate tid epId executingCore
              (cancelRecvBusyReply ctx tid gate decoded executingCore st)
          | .ok (some (rid, prevCaller, replyBadge, replyGrant)) =>
              -- WS-SX SX7.3: the reply capability is named by `replyRegister`
              -- (x6), so the reply's payload is the whole message, MR0 on.
              -- The reply badge is the *reply cap's* badge (`replyBadge`), not
              -- the endpoint receive cap's.
              let msg : IpcMessage :=
                { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo,
                  badge := replyBadge }
              if securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf prevCaller) then
                -- seL4-MCS `handleReplyRecv`: the reply, then `receiveIPC`, which
                -- completes an active bound notification and leaves the endpoint
                -- alone (the notification → receiver flow admitting it).
                if receiveCompletesSignal ctx st tid then
                  replyRecvCompletesSignalArm ctx tid prevCaller decoded.msgInfo.label msg
                    replyGrant executingCore st
                else
                -- WS-RA RA.B.6: stage the receive leg's delivery (the checked
                -- twin of the unchecked arm's staging; the receive leg's own
                -- flow gate governs the consumed message).
                -- WS-SX ruling D28: the receive leg lends a taken `Call`'s
                -- context only at the call's admission of the send queue's head
                -- (`receiveLendAdmits`), read on the state the arm is handed,
                -- as the `.receive` arm reads it.
                match replyRecvTransferOnCore epId tid rid prevCaller decoded.msgInfo.label msg
                replyGrant executingCore st (receiveLendAdmits ctx st epId) with
                -- PR #873 round 7: the checked twin of the unchecked arm's
                -- WithCaps receive leg — the endpoint→receiver flow is gated
                -- above, so the *unchecked* per-core WithCaps receive inside
                -- the shared body is correct here for the same reason the bare
                -- one was, and `extraCaps` is the summary's installed count.
                | .ok (summary, st') =>
                    .ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo)
                | .error e => .error e
              else .error .replyCapInvalid
    | _ => fun _ => .error (.invalidCapability 0)
  -- WS-SM SM8.C.9: **the live declassification.**
  --
  -- WS-SX SX6.7: an invocation of the audit-trail capability, the object it
  -- releases into extra capability 0 (`resolveDeclassifyTarget`).  A capability
  -- names the target object, so there is no confused deputy: the operand is a
  -- capability, not a caller-supplied id.  Neither domain comes
  -- from the caller either — `declassifyObjectFromCore` reads the source off the
  -- subject the executing core is running and the destination off the target
  -- object — so both endpoints of the recorded downgrade are facts about the
  -- state.
  --
  -- The base policy is the embedded legacy lattice (`liftLegacyContext`) and the
  -- declassification policy is the context's, which defaults to deny-all: an
  -- operator who has not configured one gets `.declassificationDenied` on every
  -- call, exactly as on the unchecked path.
  | .declassify =>
    match cap.target with
    | .auditTrail _ =>
        fun st =>
          match resolveDeclassifyTarget tid decoded.msgInfo.extraCaps st with
          | .error e => .error e
          | .ok (_, targetId) =>
            declassifyObjectFromCore (liftLegacyContext ctx) ctx.declassificationPolicy
              executingCore targetId st
    | _ => fun _ => .error (.invalidCapability 0)
  -- WS-SM SM9.C.8: **the live data-carrying declassification.**
  --
  -- WS-SX SX6.7: an invocation of the audit-trail capability, the notification
  -- extra capability 0 (`resolveDeclassifySignalTarget`).
  -- Structurally the `.notificationSignal` arm — same notification, same
  -- badge (the notification capability's, `Capability.signalBadge`: no message register is
  -- read, so the declassified datum is the identity the capability was minted
  -- with, never a caller-chosen word) — with the
  -- bound-aware cross-core dispatch replaced by the declassifying one.  Keeping
  -- the surrounding shape identical is deliberate: the transition really does
  -- perform the ordinary signal's writes
  -- (`declassifiedSignal_ordinary_eq_signal`), so the woken thread's badge
  -- register and a woken bound receiver's reply stash are written by the wake
  -- itself, as on the ordinary path, and nothing runs after it.
  --
  -- Neither domain is an operand.  The source is the *actor's* — read off the
  -- subject the executing core is running — and the two destinations are the
  -- notification's own domain and the **resolved receiver's**, so a signaller
  -- authorized into the notification but not onward to the thread that will
  -- receive the badge is refused at the second hop
  -- (`.declassificationDeniedAtReceiver`).
  | .declassifySignal =>
    match cap.target with
    | .auditTrail _ =>
      fun st =>
        match resolveDeclassifySignalTarget tid decoded.msgInfo.extraCaps st with
        | .error e => .error e
        | .ok (ntfnCap, notifId) =>
          match notificationSignalDeclassifiedCrossCoreDispatch (liftLegacyContext ctx)
                  ctx.declassificationPolicy notifId ntfnCap.signalBadge executingCore st with
          | (st', .ok _) =>
              .ok ((), st')
          | (_, .error e) => .error e
    | _ => fun _ => .error (.invalidCapability 0)
  -- WS-SM SM9.A.10: **the live audit read.**
  --
  -- The authority is `extractAuditAuthority` — the capability must *target* the
  -- audit trail.  The gate checks the same type, then the right, before this
  -- arm runs (`syscallInvokeTyped`), so a wrong-kind capability is
  -- `.invalidCapability` whatever rights it carries (the v0.32.97
  -- confused-deputy class is the reason the target gate exists at all); the
  -- arm's own checks restate the gate's.
  --
  -- The reader's clearance is not an operand: `auditReadFromCore` reads it off
  -- the subject the executing core is running.  A caller that could name its own
  -- clearance could read the whole trail.  Since PR #870 round 6 the transition
  -- also refuses a resolved subject the monitor gate refuses — the live
  -- facility is monitor-only, because a partial reader's visible length moves
  -- under a monitor's drain (a one-bit-per-drain downward signal;
  -- `auditReadFromCore_partial_reader_denied` / `auditDrain_moves_partial_readers_status`).
  --
  -- **The result is written into the caller's return register.**  Without this
  -- the reader would gate correctly, compute correctly and hand back the
  -- caller's own preloaded `x0` — the failure WS-RA's return-frame path exists
  -- to prevent.  `auditReadFromCore` guarantees the word is below `2 ^ 64`
  -- (`auditReadFromCore_word_fits`), so the conversion here is lossless.
  | .auditRead =>
    fun st =>
      match extractAuditAuthority cap with
      | .error e => .error e
      | .ok () =>
        if cap.hasRight gate.requiredRight then
          match decodeAuditReadArgs decoded with
          | .error e => .error e
          | .ok args =>
              match decodeAuditReadOp args.opcode args.index args.chunk with
              | none => .error .invalidSyscallArgument
              | some op =>
                  -- PR #870 review (P1): the VALIDATED clearance, so a
                  -- misconfigured deployment (a clearance that does not
                  -- dominate every subject label) has no monitor at all —
                  -- no epoch, no global identities — rather than a monitor
                  -- with blind spots.  Round 2: the validated clearance is
                  -- also the read facility's on/off switch — the transition
                  -- refuses outright when it is `none`
                  -- (`auditRead_unconfigured_denied`), so a boot-provisioned
                  -- audit capability cannot open a reader the deployment's
                  -- configuration never did.
                  match auditReadFromCore (liftLegacyContext ctx)
                      (validatedAuditMonitorClearance ctx)
                      executingCore op st with
                  | .error e => .error e
                  | .ok (w, st') =>
                      .ok ((), Architecture.writeCallReturnWord st' tid w.toUInt64)
        else .error .illegalAuthority
  -- WS-SM SM9.A.10: **the live audit drain**, which is what makes the
  -- fail-closed 256-entry capacity bound survivable rather than a feature that
  -- disables itself.
  --
  -- Same first gate (`extractAuditAuthority`), a stronger second one: the
  -- `.write` right — checked here in the arm since PR #870 round 5, after the
  -- target — so a monitoring deployment can mint a read-only audit capability
  -- that provably cannot drain.  The third gate is inside the transition — the
  -- configured `auditMonitorClearance` — and it is *not* computed from the
  -- trail's current rows, because a rows-derived dominance predicate goes
  -- vacuously true on a trail drained to empty.
  --
  -- Returns the new visible length, staged into the caller's return register.
  | .auditDrain =>
    fun st =>
      match extractAuditAuthority cap with
      | .error e => .error e
      | .ok () =>
        if cap.hasRight gate.requiredRight then
          match decodeAuditDrainArgs decoded with
          | .error e => .error e
          | .ok args =>
              -- PR #870 review (P1): the VALIDATED clearance — a misconfigured
              -- deployment cannot drain, exactly as an unconfigured one cannot
              -- (`misconfiguredDeployment_cannot_drain`); the transition's own
              -- `auditDrainViewComplete` guard is the defense in depth behind
              -- it.
              match auditDrainVisiblePrefix (liftLegacyContext ctx)
                  (validatedAuditMonitorClearance ctx)
                  executingCore args.count st with
              | .error e => .error e
              | .ok (n, st') =>
                  .ok ((), Architecture.writeCallReturnWord st' tid n.toUInt64)
        else .error .illegalAuthority
  -- AE1-A/AE1-B/AE1-C: All remaining capability-only arms (tcbSetPriority,
  -- tcbSetMCPriority, tcbSetIPCBuffer, cspaceDelete, vspaceMap,
  -- vspaceUnmap, serviceRevoke, serviceQuery, schedContextConfigure,
  -- schedContextBind, schedContextUnbind, tcbSuspend, tcbResume) are handled by
  -- dispatchCapabilityOnly returning `some` above. This wildcard is provably
  -- unreachable (see dispatchWithCapChecked_wildcard_unreachable below).
  -- WS-ZA ZA4.3: a yield never reaches this tier (`dispatchYield` runs it first).
  | .yield => fun _ => .error .illegalState
  | _ => fun _ => .error .illegalState

/-- **WS-ZA ZA4.3**: the yield syscall at the dispatcher — `yieldOnCore` on the
executing core, which the dispatcher has already confirmed the caller is
current on.  A yield wakes no thread and so sends no SGI; a core whose decision
the caller's moved key stales is flagged by the key hook, and the commit seam
derives the pokes from the state it commits. -/
def dispatchYield (executingCore : Concurrency.CoreId) : Kernel Unit :=
  fun st =>
    match yieldOnCore st executingCore with
    | .error e => .error e
    | .ok st' => .ok ((), st')

/-- T6-I: Policy-checked dispatch variant. Routes syscalls through
    information-flow-checked wrappers when a `LabelingContext` is provided.

    **WS-SM SM9.D.7 (PR #873 round 6): the taint seam is applied here, not at the
    entry above it.**

    It used to live in `syscallEntryChecked`, one layer up — which was wrong
    because this function is what an integrator writing a production
    user-space entry calls.  An integrator who did so called *this*
    function directly and never reached the seam, so a successful send or receive
    moved tagged content with no provenance following it, and a successful retype
    kept the replaced object's tags on its replacement.  The recommendation was
    right; the seam was in the wrong place.

    Applied to the state **this** function was given, so composing it under an
    entry that pre-processes the state (the SM7.F.5 TLB fill) is unchanged: the
    entry passes the filled state, and the plan and the pre-state are both that.
    Nothing is applied on the error arm, because nothing moved. -/
def dispatchSyscallChecked (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : Kernel Unit :=
  fun st =>
    -- The caller and the executing core are one fact: `tid` must be the
    -- thread current on `executingCore`.  Capability resolution and the flow
    -- checks act as `tid`, while the `.declassify`, `.declassifySignal` and
    -- audit arms take their acting subject from `currentOnCore executingCore`;
    -- a mismatched pair would let one core's subject authorize or attribute a
    -- downgrade for another core's caller.  Refused before any lookup, with
    -- the state untouched (`dispatchSyscallChecked_ok_caller_current`).
    if st.scheduler.currentOnCore executingCore ≠ some tid then .error .illegalState
    -- WS-ZA ZA4.3: a yield invokes no capability, so it runs before the
    -- caller's CSpace is consulted and moves no content (`contentFlowClass
    -- .yield = .inert`), so no taint step follows it.
    else if decoded.syscallId = .yield then dispatchYield executingCore st
    else
    match st.getObject? tid.toObjId with
    | some (.tcb tcb) =>
      let gate : SyscallGate := {
        callerId     := tid
        cspaceRootCap := tcb.spaceCells[0]
        capAddr      := decoded.capAddr
        requiredRight := syscallRequiredRight decoded.syscallId
      }
      -- PR #870 round 5: the target-first syscalls (the audit pair) take the
      -- resolve-only lookup, so their arms see the capability BEFORE any
      -- rights verdict and can honour the documented order — target first
      -- (`.invalidCapability` for every non-audit target, whatever its
      -- rights), right second.  Everything else keeps the classic
      -- rights-gated lookup.
      match (syscallInvokeTyped decoded.syscallId gate (decodedExtraCapsFault? st tid decoded)
          (dispatchWithCapChecked ctx decoded tid executingCore gate)) st with
      | .error e => .error e
      | .ok ((), stPost) =>
          .ok ((), applySyscallTaint (syscallTaintPlan st tid decoded) st stPost)
    | some _ => .error .illegalState
    | none   => .error .objectNotFound

/-- WS-ZA ZA1.1: `dispatchSyscallChecked`'s arm and taint step, given what the
taint step reads of the pre-state (`applySyscallTaintAfter`): the audit epoch,
the trail's length and the taint at the plan's flow sources.  A separate,
non-inlined function so its arguments are read before the arm runs. -/
@[noinline] def dispatchCheckedArmThenTaint (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (xf : Option (SeLe4n.CPtr × LookupFault))
    (plan : TaintPlan) (preEpoch : Nat) (preLength : Nat)
    (preTaint : TaintMap) : Kernel Unit :=
  fun st =>
    match (syscallInvokeTyped decoded.syscallId gate xf (dispatchWithCapChecked ctx decoded tid executingCore gate)) st with
    | .error e => .error e
    | .ok ((), stPost) => .ok ((), applySyscallTaintAfter plan preEpoch preLength preTaint stPost)

/-- WS-ZA ZA5.12: a `.declassify`'s arm, then its fused taint step
(`declassifyTaintStep`), given the scalars standing for its plan's `noRelease`
and the audit epoch and trail length read before the arm. -/
@[noinline] def dispatchCheckedArmThenDeclassifyTaint (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (xf : Option (SeLe4n.CPtr × LookupFault))
    (nrB : Bool) (nrId : SeLe4n.ObjId) (preEpoch preLength : Nat) : Kernel Unit :=
  fun st =>
    match (syscallInvokeTyped decoded.syscallId gate xf (dispatchWithCapChecked ctx decoded tid executingCore gate)) st with
    | .error e => .error e
    | .ok ((), stPost) => .ok ((), declassifyTaintStep nrB nrId preEpoch preLength stPost)

/-- WS-ZA ZA5.12: a `.declassifySignal`'s arm, then its fused taint step
(`declassifySignalTaintStep`), given its taint case as a word, the notification
its operand names, the caller's and the notification's taint words as scalars,
and the audit epoch and trail length — all read before the arm. -/
@[noinline] def dispatchCheckedArmThenDeclassifySignalTaint (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (xf : Option (SeLe4n.CPtr × LookupFault))
    (taintCode : Nat) (nid : SeLe4n.ObjId)
    (a0 a1 a2 a3 a4 a5 a6 a7 : UInt64) (ac : Nat) (as : Bool)
    (b0 b1 b2 b3 b4 b5 b6 b7 : UInt64) (bc : Nat) (bs : Bool)
    (preEpoch preLength : Nat) : Kernel Unit :=
  fun st =>
    match (syscallInvokeTyped decoded.syscallId gate xf (dispatchWithCapChecked ctx decoded tid executingCore gate)) st with
    | .error e => .error e
    | .ok ((), stPost) =>
        .ok ((), declassifySignalTaintStep (SignalTaintCase.ofCode taintCode) nid tid
          ⟨a0, a1, a2, a3, a4, a5, a6, a7, ac, as⟩ ⟨b0, b1, b2, b3, b4, b5, b6, b7, bc, bs⟩
          preEpoch preLength stPost)

/-- WS-ZA ZA5.12: an audit call's arm; its taint step is the identity
(`auditTaintStep_eq`). -/
@[noinline] def dispatchCheckedArmOnly (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (xf : Option (SeLe4n.CPtr × LookupFault)) : Kernel Unit :=
  fun st =>
    match (syscallInvokeTyped decoded.syscallId gate xf (dispatchWithCapChecked ctx decoded tid executingCore gate)) st with
    | .error e => .error e
    | .ok ((), stPost) => .ok ((), stPost)

/-- WS-ZA ZA5.12: **the arm and taint step the compiled general dispatcher
runs.**  The declassifications and the audit pair take their fused steps, their
source words and plan scalars captured before the arm; every other syscall
reaching the general dispatcher takes the specification's step over the words
captured at its plan's flow sources (`planSourceWords`).  Equal to the arm and
step over the pre-state's taint (`dispatchCheckedArmThenTaintFused_eq`). -/
@[inline] def dispatchCheckedArmThenTaintFused (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) : Kernel Unit :=
  fun st =>
    match decoded.syscallId with
    | .declassify =>
        let operand := declassifyPlanOperand? st tid decoded.capAddr decoded.msgInfo.extraCaps
        dispatchCheckedArmThenDeclassifyTaint ctx decoded tid executingCore gate
          (decodedExtraCapsFault? st tid decoded)
          (declassifyBypassB st operand) (operandObjectId operand)
          st.declassificationAuditEpoch st.declassificationAudit.length st
    | .declassifySignal =>
        let operand := declassifyPlanOperand? st tid decoded.capAddr decoded.msgInfo.extraCaps
        let nid := operandObjectId operand
        withTaintWordsAt st tid.toObjId fun a0 a1 a2 a3 a4 a5 a6 a7 ac as =>
        withTaintWordsAt st nid fun b0 b1 b2 b3 b4 b5 b6 b7 bc bs =>
        dispatchCheckedArmThenDeclassifySignalTaint ctx decoded tid executingCore gate
          (decodedExtraCapsFault? st tid decoded)
          (signalTaintCaseOf st operand).code nid a0 a1 a2 a3 a4 a5 a6 a7 ac as
          b0 b1 b2 b3 b4 b5 b6 b7 bc bs
          st.declassificationAuditEpoch st.declassificationAudit.length st
    | .auditRead | .auditDrain =>
        dispatchCheckedArmOnly ctx decoded tid executingCore gate (decodedExtraCapsFault? st tid decoded) st
    | _ =>
        dispatchCheckedArmThenTaint ctx decoded tid executingCore gate
          (decodedExtraCapsFault? st tid decoded) (syscallTaintPlan st tid decoded) st.declassificationAuditEpoch
          st.declassificationAudit.length
          (sourceTaint (planSourceWords (syscallTaintPlan st tid decoded) st)) st

/-- WS-ZA ZA1.1: the compiled `dispatchSyscallChecked`.  It reads what the taint
step needs of the pre-state before the arm, so the arm owns the state it writes
(WS-ZA D1).  WS-ZA ZA5.12: the taint it reads is the
words stored at the plan's flow sources, captured before the arm
(`planSourceWords`), never the reader over the whole store. -/
def dispatchSyscallCheckedImpl (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : Kernel Unit :=
  fun st =>
    if st.scheduler.currentOnCore executingCore ≠ some tid then .error .illegalState
    -- WS-ZA ZA4.3: a yield invokes no capability, so it runs before the
    -- caller's CSpace is consulted and moves no content (`contentFlowClass
    -- .yield = .inert`), so no taint step follows it.
    else if decoded.syscallId = .yield then dispatchYield executingCore st
    else
    match st.getObject? tid.toObjId with
    | some (.tcb tcb) =>
      let gate : SyscallGate := {
        callerId     := tid
        cspaceRootCap := tcb.spaceCells[0]
        capAddr      := decoded.capAddr
        requiredRight := syscallRequiredRight decoded.syscallId
      }
      dispatchCheckedArmThenTaintFused ctx decoded tid executingCore gate st
    | some _ => .error .illegalState
    | none   => .error .objectNotFound

/-- WS-ZA ZA5.12 (**the decode lemma at the general dispatcher**): the arm and
taint step over the captured source words is the one over the pre-state's taint
(`applySyscallTaintAfter_planSourceWords`). -/
theorem dispatchCheckedArmThenTaint_planSourceWords (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (xf : Option (SeLe4n.CPtr × LookupFault)) (plan : TaintPlan)
    (st : SystemState) :
    dispatchCheckedArmThenTaint ctx decoded tid executingCore gate xf plan
        st.declassificationAuditEpoch st.declassificationAudit.length
        (sourceTaint (planSourceWords plan st)) st =
      dispatchCheckedArmThenTaint ctx decoded tid executingCore gate xf plan
        st.declassificationAuditEpoch st.declassificationAudit.length
        st.declassificationTaint st := by
  unfold dispatchCheckedArmThenTaint
  split
  · rfl
  · rw [applySyscallTaintAfter_planSourceWords]; rfl

/-- WS-ZA ZA5.12 (**the decode lemma at each fused declassify and audit step**):
the arm and step the compiled general dispatcher runs is the arm and the
specification's step over the pre-state's taint.  The declassified signal's
captured words are discharged by `decode_taintWordsAt`. -/
theorem dispatchCheckedArmThenTaintFused_eq (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (st : SystemState) :
    dispatchCheckedArmThenTaintFused ctx decoded tid executingCore gate st =
      dispatchCheckedArmThenTaint ctx decoded tid executingCore gate
        (decodedExtraCapsFault? st tid decoded)
        (syscallTaintPlan st tid decoded) st.declassificationAuditEpoch
        st.declassificationAudit.length st.declassificationTaint st := by
  unfold dispatchCheckedArmThenTaintFused
  split
  next h =>
    unfold dispatchCheckedArmThenDeclassifyTaint dispatchCheckedArmThenTaint
    split
    · rfl
    · rw [declassifyTaintStep_eq st tid decoded h]
  next h =>
    simp only [withTaintWordsAt_eq, TaintWords.mk_fields]
    unfold dispatchCheckedArmThenDeclassifySignalTaint dispatchCheckedArmThenTaint
    split
    · rfl
    · rw [declassifySignalTaintStep_eq st tid decoded h _ _ st.declassificationTaint
        (st.taintWordsAt tid.toObjId)
        (st.taintWordsAt (operandObjectId (declassifyPlanOperand? st tid decoded.capAddr decoded.msgInfo.extraCaps)))
        (decode_taintWordsAt st _) (decode_taintWordsAt st _), SignalTaintCase.ofCode_code]
  next h =>
    unfold dispatchCheckedArmOnly dispatchCheckedArmThenTaint
    split
    · rfl
    · rw [auditTaintStep_eq st tid decoded (Or.inl h)]
  next h =>
    unfold dispatchCheckedArmOnly dispatchCheckedArmThenTaint
    split
    · rfl
    · rw [auditTaintStep_eq st tid decoded (Or.inr h)]
  next => exact dispatchCheckedArmThenTaint_planSourceWords ctx decoded tid executingCore gate _ _ st

@[csimp] theorem dispatchSyscallChecked_eq_impl :
    @dispatchSyscallChecked = @dispatchSyscallCheckedImpl := by
  funext ctx decoded tid executingCore st
  simp only [dispatchSyscallCheckedImpl, dispatchCheckedArmThenTaintFused_eq]
  rfl

/-- T6-I/M-IF-1: Top-level register-sourced syscall entry point with
    information-flow enforcement. All cross-domain operations are gated by
    `securityFlowsTo` before execution.

    AI5-C (M-19): Rejects the insecure `defaultLabelingContext` at the entry
    point. The `isInsecureDefaultContext` detector fires once per syscall entry,
    returning `.policyDenied` if the labeling context assigns `publicLabel` to
    all four entity classes. This prevents accidental deployment with a context
    that defeats all information-flow enforcement.

    This is the kernel's one register-sourced syscall entry: the live seam
    (`Platform.FFI.syscallDispatchFromAbi`) runs it with the deployment's
    labeling context, and the model's exception dispatch, the trace harness
    and the suites run it too.  The unchecked, boot-pinned entry it once sat
    beside was retired (owner decision 2026-11-13). -/
def syscallEntryChecked (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout)
    (executingCore : Concurrency.CoreId)
    (regCount : Nat := 32) : Kernel Unit :=
  fun st =>
    -- AI5-C (M-19): Reject insecure default labeling context in checked mode
    if isInsecureDefaultContext ctx then .error .policyDenied
    else
    -- WS-SM SM6.A: identify the caller on its *own* core (the trapping core),
    -- not the boot core — so a syscall issued from a secondary core decodes and
    -- mutates *that* core's current TCB.  `executingCore` is read from the
    -- hardware (`currentCoreId`) by the cross-core dispatch seam.
    match (st.scheduler.currentOnCore executingCore) with
    | none => .error .illegalState
    | some tid =>
      match lookupThreadRegisterContext tid st with
      | .error e => .error e
      | .ok (regs, _) =>
        -- AK4-A.6 (R-ABI-C01): Use state-aware decode so 5-arg syscalls
        -- (`serviceRegister`, `schedContextConfigure`) merge IPC-buffer
        -- overflow registers into `msgRegs` per seL4 convention.
        -- WS-SX SX7: the operation is selected as seL4's `handleSyscall` and
        -- `decodeInvocation` select it -- from the syscall `x7` names, the type
        -- of the capability `x0` names and the label `x1` carries -- never
        -- read off a register (`threadOperationCode`).
        match SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
                (threadOperationCode st tid layout regs) st tid layout regs regCount with
        | .error e => .error e
        | .ok decoded =>
          -- WS-SX SX6.6: the decode above read the overflow words at their
          -- physical addresses, through the kernel's own mapping of RAM (the
          -- HAL's entry reads them there, as seL4 reads the buffer through
          -- `lookupIPCBuffer`'s kernel pointer), so no user translation is
          -- cached on this core and the dispatcher is handed the entry's own
          -- state.
          -- WS-SM SM9.D.7: **the taint propagation seam is inherited, not
          -- repeated.**  `dispatchSyscallChecked` applies the plan to the state
          -- it was handed, so every entry, including one written tomorrow,
          -- inherits it.  The classification `contentFlowClass` is total on
          -- `SyscallId`, so a new syscall is a missing case at elaboration; that
          -- its *callees* do not move content the declared edges miss is checked
          -- by reach, in `scripts/check_content_flow_coverage.py`.
          dispatchSyscallChecked ctx decoded tid executingCore st

-- ============================================================================
-- U5-A/U5-D: Dispatch structural equivalence theorems
-- ============================================================================

/-- The checked `.serviceRevoke` arm is the unchecked one behind the write gate:
the policy-checked revoke `revokeServiceChecked` at the endpoint extra
capability 0 names (WS-SX SX6.7, `serviceEndpointArm`). -/
theorem dispatchWithCapChecked_serviceRevoke_eq
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (code : Nat)
    (hSyscall : decoded.syscallId = .serviceRevoke) (hTarget : cap.target = .serviceRegistry code) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
    serviceEndpointArm .serviceRevoke tid decoded.msgInfo.extraCaps
      (fun _ epId => revokeServiceChecked ctx tid epId) := by
  simp only [dispatchWithCapChecked, dispatchCapabilityOnly, hSyscall, hTarget,
    dispatchCapabilityOnlyChecked]

/-- The checked `.serviceQuery` arm is the unchecked one behind the read gate:
`serviceQueryStaged`, the arm's staging over the policy-checked lookup
`lookupServiceChecked`, at the endpoint extra capability 0 names. -/
theorem dispatchWithCapChecked_serviceQuery_eq
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (code : Nat)
    (hSyscall : decoded.syscallId = .serviceQuery) (hTarget : cap.target = .serviceRegistry code) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
      serviceEndpointArm .serviceQuery tid decoded.msgInfo.extraCaps
        (fun _ epId => serviceQueryStaged ctx tid epId) := by
  simp only [dispatchWithCapChecked, dispatchCapabilityOnly, hSyscall, hTarget,
    dispatchCapabilityOnlyChecked]

/-- A service arm on an endpoint that resolves is its continuation on it. -/
theorem serviceEndpointArm_of_resolved {sid : SyscallId} {tid : SeLe4n.ThreadId} {xc : Nat}
    {st : SystemState} {epCap : Capability} {epId : SeLe4n.ObjId}
    (k : Capability → SeLe4n.ObjId → Kernel Unit)
    (hRes : resolveServiceEndpoint sid tid xc st = .ok (epCap, epId)) :
    serviceEndpointArm sid tid xc k st = k epCap epId st := by
  simp [serviceEndpointArm, hRes]

/-- **The query refuses an endpoint the caller may not read**, before any lookup:
whatever the endpoint records, and whether it records anything, the checked
`.serviceQuery` arm answers `flowDenied` when the endpoint's label does not flow
to the caller's.  The refusal reads labels only, so it says nothing about the
registry or the endpoint. -/
theorem dispatchWithCapChecked_serviceQuery_refuses_unreadable_endpoint
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (code : Nat) (epCap : Capability)
    (epId : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .serviceQuery) (hTarget : cap.target = .serviceRegistry code)
    (hRes : resolveServiceEndpoint .serviceQuery tid decoded.msgInfo.extraCaps st = .ok (epCap, epId))
    (hAdm : serviceEndpointReadAdmitted ctx tid epId = false) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .error .flowDenied := by
  rw [dispatchWithCapChecked_serviceQuery_eq ctx decoded tid executingCore gate cap code
    hSyscall hTarget, serviceEndpointArm_of_resolved _ hRes]
  simp [serviceQueryStaged, lookupServiceChecked, hAdm]

/-- **The revoke refuses an endpoint the caller may not write**, before reading
what it records. -/
theorem dispatchWithCapChecked_serviceRevoke_refuses_unwritable_endpoint
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (code : Nat) (epCap : Capability)
    (epId : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .serviceRevoke) (hTarget : cap.target = .serviceRegistry code)
    (hRes : resolveServiceEndpoint .serviceRevoke tid decoded.msgInfo.extraCaps st = .ok (epCap, epId))
    (hAdm : serviceEndpointWriteAdmitted ctx tid epId = false) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .error .flowDenied := by
  rw [dispatchWithCapChecked_serviceRevoke_eq ctx decoded tid executingCore gate cap code
    hSyscall hTarget, serviceEndpointArm_of_resolved _ hRes]
  simp [revokeServiceChecked, hAdm]

/-- **The revoke removes the registration the named endpoint records, and no
other.**  The service is the one the endpoint records (`serviceRegistered`,
under the endpoint's own id), never named by a caller-supplied word: the arm
reads no message register. -/
theorem dispatchWithCapChecked_serviceRevoke_removes_recorded_registration
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (code : Nat) (epCap : Capability)
    (epId : SeLe4n.ObjId) (st : SystemState)
    (ep : Endpoint)
    (hSyscall : decoded.syscallId = .serviceRevoke) (hTarget : cap.target = .serviceRegistry code)
    (hRes : resolveServiceEndpoint .serviceRevoke tid decoded.msgInfo.extraCaps st = .ok (epCap, epId))
    (hAdm : serviceEndpointWriteAdmitted ctx tid epId = true)
    (hEp : st.objects[epId]? = some (.endpoint ep)) (hCode : ep.serviceRegistered = true) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      revokeService (ServiceId.ofNat epId.toNat) st := by
  rw [dispatchWithCapChecked_serviceRevoke_eq ctx decoded tid executingCore gate cap code
    hSyscall hTarget, serviceEndpointArm_of_resolved _ hRes]
  simp [revokeServiceChecked, hAdm, revokeServiceByRecordedRegistration, SystemState.getObject?, hEp,
    hCode]

/-- **A revoke on an endpoint that records no service fails with
`objectNotFound` and removes nothing**: a missing object, or an endpoint whose
registration was already revoked.  An endpoint capability therefore cannot
reach another endpoint's registration. -/
theorem dispatchWithCapChecked_serviceRevoke_objectNotFound_of_unrecorded
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (code : Nat) (epCap : Capability)
    (epId : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .serviceRevoke) (hTarget : cap.target = .serviceRegistry code)
    (hRes : resolveServiceEndpoint .serviceRevoke tid decoded.msgInfo.extraCaps st = .ok (epCap, epId))
    (hAdm : serviceEndpointWriteAdmitted ctx tid epId = true)
    (hNone : ∀ ep, st.objects[epId]? = some (.endpoint ep) → ep.serviceRegistered = false) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .error .objectNotFound := by
  rw [dispatchWithCapChecked_serviceRevoke_eq ctx decoded tid executingCore gate cap code
    hSyscall hTarget, serviceEndpointArm_of_resolved _ hRes]
  simp only [revokeServiceChecked, hAdm, if_true]
  unfold revokeServiceByRecordedRegistration SystemState.getObject?
  split
  · rename_i ep hEp
    rw [hNone ep hEp]
  · rfl

/-- **Registration refuses an endpoint the caller may not write**: the gate reads
the endpoint's own label (`objectLabelOf`), so a caller cannot record a
service on an endpoint above it whatever service id it would be given. -/
theorem dispatchWithCapChecked_serviceRegister_refuses_unwritable_endpoint
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (code : Nat) (epCap : Capability)
    (epId : SeLe4n.ObjId) (st : SystemState)
    (args : Architecture.SyscallArgDecode.ServiceRegisterArgs)
    (hSyscall : decoded.syscallId = .serviceRegister) (hTarget : cap.target = .serviceRegistry code)
    (hArgs : Architecture.SyscallArgDecode.decodeServiceRegisterArgs decoded = .ok args)
    (hRes : resolveServiceEndpoint .serviceRegister tid decoded.msgInfo.extraCaps st = .ok (epCap, epId))
    (hAdm : serviceEndpointWriteAdmitted ctx tid epId = false) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .error .flowDenied := by
  obtain ⟨_, _, _, hTg, _, _⟩ := resolveServiceEndpoint_ok _ _ _ _ _ _ hRes
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, hSyscall, hTarget, hArgs,
    serviceEndpointArm, hRes, registerServiceChecked, registrationWriteAdmitted, hTg, hAdm]

-- ============================================================================
-- AJ1-D (M-01): Reply/ReplyRecv conditional equivalence theorems
-- ============================================================================

/-- WS-SM SM6.D (PR #822 review, IF-ordering): a checked `.reply` whose replier→caller
flow is **denied** returns `.replyCapInvalid` — the *same* error the `none`/unlinked
arms return — so a reply-cap holder cannot distinguish a Reply linked to a caller it
may not flow to (which would leak `Reply.caller`, erased from the low projection) from
an unlinked/consumed Reply.  Together with `checkedDispatch_reply_eq_unchecked_when_allowed`
this pins the full arm: identical to the unchecked path when the flow is permitted,
collapsed to `.replyCapInvalid` when it is not. -/
theorem checkedDispatch_reply_flow_denied_collapses
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .reply)
    (rid : SeLe4n.ReplyId)
    (hCap : cap.target = .replyCap rid)
    (st : SystemState)
    (reply : SeLe4n.Kernel.Reply) (callerTid : SeLe4n.ThreadId)
    (hReply : st.getReply? rid = some reply)
    (hCaller : reply.caller = some callerTid)
    (hDenied : securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf callerTid) = false) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .error .replyCapInvalid := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, hSyscall, hCap,
    replyAnsweredCaller?, hReply, hCaller, Option.bind, hDenied]

/-- WS-SM SM6.D (PR #822 review, IF-ordering): a checked `.receive` whose
endpoint→receiver flow is **denied** returns `.flowDenied` *for every state and decode*
— the result is independent of `st` and the reply CPtr, so `resolveRecvReplyId`'s
reply-cap validation + `replyIsStashed` scan never run.  A denied receiver therefore
cannot probe "is some blocked server holding this Reply stashed" through the error
code: the flow gate fires strictly before any reply-state read. -/
theorem checkedDispatch_receive_flow_denied
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .receive)
    (epId : SeLe4n.ObjId)
    (hCap : cap.target = .object epId)
    (st : SystemState)
    (hDenied : securityFlowsTo (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = false) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .error .flowDenied := by
  -- WS-SM SM8.C: a denied global flow denies the gate whatever the endpoint's
  -- override says, so this theorem keeps the hypothesis it always had.
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, hSyscall, hCap,
    endpointFlowGate_false_of_securityFlowsTo_false ctx epId _ _ hDenied]

/-- WS-SM SM6.D (PR #822 review, IF-ordering): a checked `.replyRecv` whose receive-leg
(endpoint→receiver) flow is **denied** returns `.flowDenied` *for every state and decode*
— `resolveReplyRecvReply` never runs, so the denied receiver cannot probe whether the
reply cap is linked.  The receive-leg gate is checked outermost, ahead of the reply
probe; the reply-leg denial (after a successful resolve) collapses to `.replyCapInvalid`
in the arm body. -/
theorem checkedDispatch_replyRecv_recv_flow_denied
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .replyRecv)
    (epId : SeLe4n.ObjId)
    (hCap : cap.target = .object epId)
    (st : SystemState)
    (hDenied : securityFlowsTo (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = false) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .error .flowDenied := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, hSyscall, hCap,
    endpointFlowGate_false_of_securityFlowsTo_false ctx epId _ _ hDenied]

-- ============================================================================
-- W2-C (MED-04): the dispatcher's wildcard arm is unreachable
-- ============================================================================

/-- AE1-D: Every `SyscallId` variant is handled by either `dispatchCapabilityOnly`
    (returning `some`) or one of the 11 explicit match arms in
    `dispatchWithCapChecked`. This proves the wildcard arm is unreachable:
    the proof enumerates every `SyscallId` constructor, so a new constructor
    that neither tier handles fails it. -/
theorem dispatchWithCapChecked_wildcard_unreachable (sid : SyscallId) :
    sid ∈ ([.send, .receive, .call, .reply, .cspaceMint, .cspaceCopy,
            .cspaceMove, .cspaceDelete, .vspaceMap,
            .vspaceUnmap, .serviceRegister, .serviceRevoke, .serviceQuery,
            .notificationSignal, .notificationWait, .replyRecv,
            .schedContextConfigure, .schedContextBind,
            .schedContextUnbind, .tcbSuspend, .tcbResume,
            .tcbSetPriority, .tcbSetMCPriority,
            .tcbSetIPCBuffer, .tcbSetAffinity,
            .tcbBindNotification, .tcbUnbindNotification, .mintReplyCap,
            .vspaceUnifyInstruction, .declassify, .declassifySignal,
            .auditRead, .auditDrain,
            .cspaceRevoke, .untypedRetype, .tcbSetSpace,
            .pageTableMap, .pageTableUnmap, .yield, .schedContextConsumed,
            .schedContextYieldTo, .irqHandlerAck, .irqControlGet,
            .irqHandlerSetNotification, .irqHandlerClear,
            .schedContextUnbindObject] : List SyscallId) := by
  cases sid <;> simp [List.mem_cons]

-- ============================================================================
-- WS-J1-C: Soundness theorems
-- ============================================================================

/-- WS-J1-C: `lookupThreadRegisterContext` does not modify kernel state. -/
theorem lookupThreadRegisterContext_state_unchanged
    (tid : SeLe4n.ThreadId) (st : SystemState) (regs : SeLe4n.RegisterFile) (st' : SystemState)
    (hOk : lookupThreadRegisterContext tid st = .ok (regs, st')) :
    st' = st := by
  unfold lookupThreadRegisterContext SystemState.getObject? at hOk
  split at hOk <;> simp at hOk
  exact hOk.2.symm

/-- WS-J1-C: `syscallRequiredRight` is total — every `SyscallId` maps to
exactly one `AccessRight`. -/
theorem syscallRequiredRight_total (sid : SyscallId) :
    ∃ r, syscallRequiredRight sid = r := ⟨_, rfl⟩

-- ============================================================================
-- WS-K-C: CSpace dispatch delegation theorems
-- ============================================================================

/-- WS-K-C: When cspaceMint dispatch succeeds, the kernel-level `cspaceMintWithCdt`
is invoked with the source and destination slots the arguments name
(`resolveCNodeOpSlots`, seL4's CNode addressing, the source root extra
capability 0), the requested rights masked
by the source capability's (`mintMaskedRights`, seL4's `maskCapRights`) and
the badge. CDT-tracked (C-01).  The arm first refuses with `.objectNotFound`
unless the invoked object is a CNode (`cnodeInvoked`). -/
theorem dispatchWithCapChecked_cspaceMint_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (cnodeId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.CSpaceMintArgs)
    (hSyscall : decoded.syscallId = .cspaceMint)
    (hTarget : cap.target = .object cnodeId)
    (hDecode : decodeCSpaceMintArgs decoded = .ok args) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
      fun st => if !cnodeInvoked cnodeId st then .error .objectNotFound else
        match resolveCNodeOpSlots tid cap args.destIndex args.destDepth
            (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0) args.srcIndex args.srcDepth st with
        | .error e => .error e
        | .ok (src, dst) =>
            let badge : Option SeLe4n.Badge :=
              if args.badge.word = 0 then none else some args.badge
            cspaceMintChecked ctx src dst (mintMaskedRights st src args.rights) badge st := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, hSyscall, hTarget, hDecode]

/-- WS-K-C: When cspaceCopy dispatch succeeds, the kernel-level `cspaceCopy`
is invoked with the source and destination slots the arguments name
(`resolveCNodeOpSlots`, seL4's CNode addressing) and the rights mask, once the
invoked object is a CNode (`cnodeInvoked`; `.objectNotFound` otherwise). -/
theorem dispatchWithCapChecked_cspaceCopy_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (cnodeId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.CSpaceCopyArgs)
    (hSyscall : decoded.syscallId = .cspaceCopy)
    (hTarget : cap.target = .object cnodeId)
    (hDecode : decodeCSpaceCopyArgs decoded = .ok args) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
      fun st => if !cnodeInvoked cnodeId st then .error .objectNotFound else
        match resolveCNodeOpSlots tid cap args.destIndex args.destDepth
            (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0) args.srcIndex args.srcDepth st with
        | .error e => .error e
        | .ok (src, dst) => cspaceCopyChecked ctx src dst args.rights st := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, hSyscall, hTarget, hDecode]

/-- WS-K-C: When cspaceMove dispatch succeeds, the kernel-level `cspaceMove`
is invoked with the source and destination slots the arguments name
(`resolveCNodeOpSlots`, seL4's CNode addressing), once the invoked object is a
CNode (`cnodeInvoked`; `.objectNotFound` otherwise). -/
theorem dispatchWithCapChecked_cspaceMove_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (cnodeId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.CSpaceMoveArgs)
    (hSyscall : decoded.syscallId = .cspaceMove)
    (hTarget : cap.target = .object cnodeId)
    (hDecode : decodeCSpaceMoveArgs decoded = .ok args) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
      fun st => if !cnodeInvoked cnodeId st then .error .objectNotFound else
        match resolveCNodeOpSlots tid cap args.destIndex args.destDepth
            (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0) args.srcIndex args.srcDepth st with
        | .error e => .error e
        | .ok (src, dst) => cspaceMoveChecked ctx src dst st := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, hSyscall, hTarget, hDecode]

/-- WS-K-C / WS-BP BP7.1 (`v0.36.7`): When cspaceDelete dispatch succeeds, the
**finalising** delete runs on the decoded target slot, with the invoking thread's
core as the initiator of the teardown's shootdown rounds: the capability is
deleted and the mapping it recorded, if it records one, is removed.  The arm
first refuses with `.objectNotFound` unless the invoked object is a CNode
(`cnodeInvoked`): a thread's root slots are reachable only by its own TCB
invocations and the kernel's internal teardown. -/
theorem dispatchWithCapChecked_cspaceDelete_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (cnodeId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.CSpaceDeleteArgs) (st : SystemState)
    (hSyscall : decoded.syscallId = .cspaceDelete)
    (hTarget : cap.target = .object cnodeId)
    (hDecode : decodeCSpaceDeleteArgs decoded = .ok args) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      if !cnodeInvoked cnodeId st then .error .objectNotFound else
        cspaceDeleteSlotZombie executingCore
          { cnode := cnodeId, slot := args.targetSlot } st := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchCapabilityOnlyChecked, hSyscall, hTarget, hDecode]

/-- WS-BP BP7.1 (`v0.36.7`): When cspaceRevoke dispatch succeeds, the
**finalising** CDT revocation runs on the decoded source slot: every derivation
of the capability is destroyed, and every mapping a destroyed frame capability
recorded is removed.  The arm first refuses with `.objectNotFound` unless the
invoked object is a CNode (`cnodeInvoked`). -/
theorem dispatchWithCapChecked_cspaceRevoke_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (cnodeId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.CSpaceDeleteArgs) (st : SystemState)
    (hSyscall : decoded.syscallId = .cspaceRevoke)
    (hTarget : cap.target = .object cnodeId)
    (hDecode : decodeCSpaceDeleteArgs decoded = .ok args) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      if !cnodeInvoked cnodeId st then .error .objectNotFound else
        cspaceRevokeCdtFinalising executingCore
          { cnode := cnodeId, slot := args.targetSlot } st := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchCapabilityOnlyChecked, hSyscall, hTarget, hDecode]

-- ============================================================================
-- WS-K-D: Lifecycle and VSpace dispatch delegation theorems
-- ============================================================================

/-- WS-K-D/S6-A/T6-C/X2-E / WS-SM SM7.B.9 / WS-SM SM7.F.4(a)+(b)(ii) / WS-BP
BP7.1: When vspaceMap dispatch passes its address-space check it is exactly
`vspaceMapOrRemapFromFrameCap`: seL4's remap of a capability whose mapping is in
place, or the fresh mapping `vspaceMapFromFrameCap` — resolve the invoked frame capability, admit the
requested permissions against that capability and the frame's memory kind, and
invoke `vspaceMapPageCheckedWithShootdownFromStatePerCore` with the caller's
executing core, the decoded ASID and vaddr, the **frame's own `base`**, and the
validated permissions (`vspaceMapFromFrameCap_ok`).  The state-aware variant reads `physicalAddressWidth`
from `SystemState.machine` for platform-specific PA bounds enforcement; the
`…PerCore` wrapper additionally caches the freshly-established translation on the
executing core's `perCoreTlb` view (the live fill, SM7.F.4(a)) and retires any
stale initiator entry (SM7.F.4(b)(ii)).  This is projection-invisible —
`perCoreTlb ∉ projectState` — so the delegation is trace-equivalent to the plain
`vspaceMapPageCheckedWithShootdownFromState` on every observable field.
T6-C: Permissions are now typed as `PagePermissions` (validated at decode).
WS-BP BP7.1 retired AK3-E's decode-time PA bound with the physical-address
operand it bounded. -/
theorem dispatchWithCapChecked_vspaceMap_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId) (words : PageMapArgs) (rootCPtr : SeLe4n.CPtr)
    (rootId : SeLe4n.ObjId) (args : Architecture.SyscallArgDecode.VSpaceMapArgs)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .vspaceMap)
    (hTarget : cap.target = .object objId)
    (hDecode : decodePageMapArgs decoded = .ok words)
    (hRoot : callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0 = some rootCPtr)
    -- PR #845 review (P1), WS-SX SX6.3 (D6): the address space is the one
    -- extra capability 0 names, and that root is the one its own ASID
    -- resolves to; without this premise the delegation is *false*, because
    -- such a call is refused before the transition runs.
    (hOps : resolvePageMapOperands tid decoded.capAddr rootCPtr words st = .ok (rootId, args)) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      vspaceMapOrRemapFromFrameCap tid executingCore args st := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchCapabilityOnlyChecked, hSyscall,
    hTarget, hDecode, hRoot, hOps]

/-- WS-SM SM7.D: When `.vspaceUnifyInstruction` dispatch succeeds,
`vspaceUnifyInstructionPage` is invoked with the decoded ASID and vaddr.

This is seLe4n's `Page_Unify_Instruction`: the mechanism by which user software
discharges the code-modification obligation ARMv8-A places on it (an
instruction fetch reads at the Point of Unification, so freshly written
instructions must be cleaned there before they can be fetched).  It takes no
executing core because it modifies no per-core scheduler or TLB state — the
maintenance is issued domain-wide, since a remote PE may hold lines from a
previous incarnation of the same physical page.  It modifies no page table
(`vspaceUnifyInstructionPage_frame`), so its lock set takes the VSpaceRoot in
**read** mode (`lockSet_vspaceUnifyInstruction`). -/
theorem dispatchWithCapChecked_vspaceUnifyInstruction_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.VSpaceUnifyInstructionArgs)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .vspaceUnifyInstruction)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeVSpaceUnifyInstructionArgs decoded st.machine.maxASID = .ok args)
    -- PR #845 review (P1): the capability must name the operand ASID's VSpace
    -- root; an unauthorized caller is rejected with `.illegalAuthority`.
    (hAuth : vspaceCapAuthorizesAsid cap args.asid st = true) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      Architecture.vspaceUnifyInstructionPage args.asid args.vaddr st := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchCapabilityOnlyChecked, hSyscall, hTarget, hDecode, hAuth]

/-- `seL4_ARM_Page_Unmap`: when the `.vspaceUnmap` dispatch runs, it is
`vspaceUnmapFrameCap` on the slot the invoked frame capability sits in — the
mapping the capability records taken down (through
`vspaceUnmapPageWithShootdownAndIcacheBroadcast`, so every core's TLB entry
and, for an executable mapping, the instruction-cache lines for the page are
retired with it: WS-SM SM7.B.9, SM7.F.4(b)(i), SM7.D.1), then the record
cleared.  No message word names an address space or an address, so no caller
can name one its capability does not record (the confused deputy PR #845
closed is closed by construction). -/
theorem dispatchWithCapChecked_vspaceUnmap_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId) (slot : CSpaceAddr) (slotCap : Capability)
    (slotObj : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .vspaceUnmap)
    (hTarget : cap.target = .object objId)
    (hRes : resolveCallerCapSlot tid decoded.capAddr (syscallRequiredRight .vspaceUnmap) st =
      .ok (slot, slotCap, slotObj)) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      vspaceUnmapFrameCap executingCore slot st := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchCapabilityOnlyChecked, hSyscall, hTarget, hRes]

/-- WS-ZA ZA5.4 part 14: the live `.untypedRetype` arm *is* the carve — every
kernel object is made this way — at the invoking thread's executing core, whose
domain and affinity a carved thread takes, and the untyped the capability names.
The arm's operands are the decoded message registers and the destination root,
extra capability 0. -/
theorem dispatchWithCapChecked_untypedRetype_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (untypedId : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .untypedRetype)
    (hTarget : cap.target = .object untypedId) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      untypedRetypeFromCap tid executingCore decoded.capAddr
        (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0)
        (decodeUntypedRetypeArgs decoded) st := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchCapabilityOnlyChecked, hSyscall, hTarget]

-- ============================================================================
-- PR #845 review (P1) — the fail-closed duals of the three VSpace delegations
--
-- The `…_delegates` theorems above say what an *authorized* caller gets.  These
-- say what an unauthorized one gets: rejection, with the address space
-- untouched.  Stated as separate theorems rather than left implicit because the
-- rejection is the security property — a regression that dropped the gate would
-- still satisfy the delegations (they carry `hAuth` as a hypothesis) but would
-- break these.
-- ============================================================================

/-- **Fail-closed**: `.vspaceMap` dispatch refuses an address space its front
does not admit — extra capability 0 names no VSpace root, or one its own ASID
does not resolve to — without running the transition. -/
theorem dispatchWithCapChecked_vspaceMap_unauthorized
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId) (words : PageMapArgs) (rootCPtr : SeLe4n.CPtr)
    (st : SystemState) (e : KernelError)
    (hSyscall : decoded.syscallId = .vspaceMap)
    (hTarget : cap.target = .object objId)
    (hDecode : decodePageMapArgs decoded = .ok words)
    (hRoot : callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0 = some rootCPtr)
    (hOps : resolvePageMapOperands tid decoded.capAddr rootCPtr words st = .error e) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .error e := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchCapabilityOnlyChecked, hSyscall,
    hTarget, hDecode, hRoot, hOps]

/-- **WS-SX SX6.3 (D6)**: a root its own ASID does not resolve to — the ASID
bound to another root, the `storeObject` rebinding SM7.F.4 names — is refused
`invalidCapability 1`, seL4's `find_ret.vspace_root != vspaceRoot`: holding a
capability to the *shadowed* root authorises nothing on the bound one. -/
theorem resolvePageMapOperands_shadowed_root (tid : SeLe4n.ThreadId)
    (frameCPtr rootCPtr : SeLe4n.CPtr) (words : PageMapArgs) (st : SystemState)
    (rootCap : Capability) (rootId boundId : SeLe4n.ObjId) (root bound : VSpaceRoot)
    (hR : resolveCallerCapObject tid rootCPtr .write st = .ok (rootCap, rootId))
    (hV : st.getVSpaceRoot? rootId = some root)
    (hA : Architecture.resolveAsidRoot st root.asid = some (boundId, bound))
    (hNe : boundId ≠ rootId) :
    resolvePageMapOperands tid frameCPtr rootCPtr words st =
      .error (.invalidCapability pageMapVSpaceCapNumber) := by
  simp [resolvePageMapOperands, hR, hV, hA, hNe]

/-- **No extra capability, no mapping**: a `.vspaceMap` whose message names no
address space is refused `.truncatedMessage`, as seL4 refuses a null
`excaprefs[0]`. -/
theorem dispatchWithCapChecked_vspaceMap_no_root
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId) (words : PageMapArgs) (st : SystemState)
    (hSyscall : decoded.syscallId = .vspaceMap)
    (hTarget : cap.target = .object objId)
    (hDecode : decodePageMapArgs decoded = .ok words)
    (hRoot : callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0 = none) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .error .truncatedMessage := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchCapabilityOnlyChecked, hSyscall,
    hTarget, hDecode, hRoot]

/-- **WS-BP BP7.1 (fail-closed, the vulnerability's closure)**: authority over
the address space is not authority over the memory.  A caller whose extra
capability names the address space still maps nothing unless the invoked
capability resolves, through the caller's own CSpace with `.read`, to a
capability naming a frame the store holds: the resolver's error is returned
and no page table is touched.  Before `v0.36.4` the arm mapped a raw physical
address from a message register, so a VSpace capability alone was authority
over every page of physical memory. -/
theorem dispatchWithCapChecked_vspaceMap_requires_frame_cap
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId) (words : PageMapArgs) (rootCPtr : SeLe4n.CPtr)
    (rootId : SeLe4n.ObjId) (args : Architecture.SyscallArgDecode.VSpaceMapArgs)
    (st : SystemState) (e : KernelError)
    (hSyscall : decoded.syscallId = .vspaceMap)
    (hTarget : cap.target = .object objId)
    (hDecode : decodePageMapArgs decoded = .ok words)
    (hRoot : callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0 = some rootCPtr)
    (hOps : resolvePageMapOperands tid decoded.capAddr rootCPtr words st = .ok (rootId, args))
    (hNoFrame : resolveVSpaceMapFrame tid args st = .error e) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .error e := by
  rw [dispatchWithCapChecked_vspaceMap_delegates ctx decoded tid executingCore gate cap objId
    words rootCPtr rootId args st hSyscall hTarget hDecode hRoot hOps]
  simp [vspaceMapOrRemapFromFrameCap, hNoFrame]

/-- **WS-BP BP7.1**: and a successful `.vspaceMap` installs the frame the caller
holds a capability to — the physical address is that frame's `base`, taken from
the object the capability names and from nothing the caller wrote.  A remap
first takes the capability's own mapping down (`st0`), and the frame is
resolved and installed from the state that leaves. -/
theorem dispatchWithCapChecked_vspaceMap_maps_frame_base
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId) (words : PageMapArgs) (rootCPtr : SeLe4n.CPtr)
    (rootId : SeLe4n.ObjId) (args : Architecture.SyscallArgDecode.VSpaceMapArgs)
    (st st' : SystemState)
    (hSyscall : decoded.syscallId = .vspaceMap)
    (hTarget : cap.target = .object objId)
    (hDecode : decodePageMapArgs decoded = .ok words)
    (hRoot : callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0 = some rootCPtr)
    (hOps : resolvePageMapOperands tid decoded.capAddr rootCPtr words st = .ok (rootId, args))
    (hOk : dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), st')) :
    ∃ (st0 : SystemState) (frameSlot : CSpaceAddr) (frameCap : Capability) (frame : FrameObject)
      (st1 : SystemState),
      (st0 = st ∨ Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast executingCore
        args.asid args.vaddr st = .ok ((), st0)) ∧
      resolveVSpaceMapFrame tid args st0 = .ok (frameSlot, frameCap, frame) ∧
      Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore
        executingCore args.asid args.vaddr frame.base args.perms st0
        = .ok ((), st1) ∧
      ∃ (epoch : Nat) (st2 : SystemState),
        tagFrameMapping args.asid args.vaddr (frameCapObjId frameCap) st1 = .ok (epoch, st2) ∧
        cspaceRecordFrameMapping frameSlot
          { asid := args.asid, vaddr := args.vaddr, epoch := epoch } st2 = .ok ((), st') := by
  rw [dispatchWithCapChecked_vspaceMap_delegates ctx decoded tid executingCore gate cap objId
    words rootCPtr rootId args st hSyscall hTarget hDecode hRoot hOps] at hOk
  have hFresh : ∀ s, vspaceMapFromFrameCap tid executingCore args s = .ok ((), st') →
      ∃ (frameSlot : CSpaceAddr) (frameCap : Capability) (frame : FrameObject)
        (st1 : SystemState),
        resolveVSpaceMapFrame tid args s = .ok (frameSlot, frameCap, frame) ∧
        Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore
          executingCore args.asid args.vaddr frame.base args.perms s = .ok ((), st1) ∧
        ∃ (epoch : Nat) (st2 : SystemState),
          tagFrameMapping args.asid args.vaddr (frameCapObjId frameCap) st1 = .ok (epoch, st2) ∧
          cspaceRecordFrameMapping frameSlot
            { asid := args.asid, vaddr := args.vaddr, epoch := epoch } st2 = .ok ((), st') := by
    intro s hS
    obtain ⟨frameSlot, frameCap, frame, st1, hR, _, _, _, _, hMap, hRec⟩ :=
      vspaceMapFromFrameCap_ok tid executingCore args s st' hS
    exact ⟨frameSlot, frameCap, frame, st1, hR, hMap, hRec⟩
  rcases vspaceMapOrRemapFromFrameCap_cases hOk with hM | ⟨st0, hU, hM⟩
  · obtain ⟨a, b, c, d, e⟩ := hFresh st hM
    exact ⟨st, a, b, c, d, .inl rfl, e⟩
  · obtain ⟨a, b, c, d, e⟩ := hFresh st0 hM
    exact ⟨st0, a, b, c, d, .inr hU, e⟩

/-- **Fail-closed**: `.vspaceUnifyInstruction` dispatch rejects a capability that
does not name the operand ASID's VSpace root, so the cache-maintenance path
cannot be used to probe another address space's mappings. -/
theorem dispatchWithCapChecked_vspaceUnifyInstruction_unauthorized
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.VSpaceUnifyInstructionArgs)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .vspaceUnifyInstruction)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeVSpaceUnifyInstructionArgs decoded st.machine.maxASID = .ok args)
    (hAuth : vspaceCapAuthorizesAsid cap args.asid st = false) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .error .illegalAuthority := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchCapabilityOnlyChecked, hSyscall, hTarget, hDecode, hAuth]

-- ============================================================================
-- WS-K-E: Service policy and IPC message population delegation theorems
-- ============================================================================

/-- WS-K-E/M-D01 / WS-SM SM6.A: When call dispatch is invoked, the IPC message
includes resolved extra capabilities and routes through the **cross-core** call
dispatch (`endpointCallCrossCoreDispatch` — the WithCaps call with home-core
receiver wake + donation), at `executingCore` — the core the syscall trapped
on, threaded from the entry. -/
theorem dispatchWithCapChecked_call_uses_crossCoreDispatch
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (epId : SeLe4n.ObjId)
    (hSyscall : decoded.syscallId = .call)
    (hTarget : cap.target = .object epId) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
      fun st =>
        -- WS-ZA ZA4.7 (seL4 `sendIPC`): the send is handed only the badge and
        -- the grant bit of the invoked capability.  The words are read from the
        -- sender's own frame at delivery, and the extra capabilities are looked up
        -- only on the arm that delivers (a send that blocks resolves none; its
        -- receiver looks them up at the rendezvous).
        let payload : SendPayload := .frame cap.badge (cap.rights.mem .grant) (cap.rights.mem .grantReply)
        -- WS-SM SM6.D (#7.3b fold): server-first reply linkage is atomic with the
        -- rendezvous inside `endpointCallOnCore` (`linkServerStashedReply`); no
        -- separate post-dispatch link step.
        -- WS-RA RA.B.5b: the woken receiver's staged frame rides in the RHS.
        let wokenReceiver? := (st.getEndpoint? epId).bind (·.receiveQ.head)
        match endpointCallCrossCoreDispatchChecked ctx epId tid payload executingCore st with
        | (st', .ok (summary, _)) =>
            .ok ((), Architecture.stageWokenDelivery st' wokenReceiver?
                      summary.capInfo)
        | (_, .error e) => .error e := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, hSyscall, hTarget]

/-- WS-K-E / WS-SM SM6.D: When reply dispatch is invoked, the IPC message body is
populated from decoded message registers via `extractMessageRegisters`; the reply
cap's `ReplyId` is resolved to its recorded caller (`reply.caller`) and the reply is
routed through the reply seam `replyTransferOnCore` (WS-RR RR4.14) at
`executingCore` — the core the replier trapped on.  On an unfaulted caller
that seam is the **cross-core** dispatch (`endpointReplyCrossCoreDispatch` — the
caller woken on its home core, the donated SchedContext returned, and
priority-inheritance reverted cross-core) plus the RA.B.5b delivered-message
staging; on a faulted one it is the fault reply, decoding the handler's message
against the fault the thread carries.  The single-use linkage consume is folded into
`endpointReplyOnCore` (PR #827 review #3) — atomic with the delivery.  Fails
closed on a dangling reply or an unlinked caller. -/
theorem dispatchWithCapChecked_reply_populates_msg
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (rid : SeLe4n.ReplyId)
    (hSyscall : decoded.syscallId = .reply)
    (hTarget : cap.target = .replyCap rid) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
      fun st =>
        let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
        -- WS-RR RR7.11: the answered thread is `replyAnsweredCaller?`, the
        -- expression the declared footprint resolver reads.  The two-level
        -- match this replaces collapsed a dangling reply and an unlinked one
        -- onto the same error, so this is that arm verbatim with the
        -- resolution named once.
        match replyAnsweredCaller? st rid with
        | none => .error .replyCapInvalid
        | some callerTid =>
            -- WS-RR RR4.14/RR4.15: seL4's `doReplyTransfer` branch on the
            -- answered thread's `tcbFault`.  On an unfaulted caller this is the
            -- pre-RR4 body verbatim — cross-core reply plus the RA.B.5b
            -- delivered-message staging (`replyTransferOnCore_of_no_fault`).
            if securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf callerTid) then
              replyTransferOnCoreChecked ctx tid callerTid decoded.msgInfo decoded.msgRegs
                { registers := body, badge := cap.badge } (cap.rights.mem .grant) executingCore st
            else .error .replyCapInvalid := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, hSyscall, hTarget]

-- ============================================================================
-- WS-RA RA.B.8 — the arms and the return-shape classification cannot disagree
-- ============================================================================
--
-- `syscallReturnShape` (RA.A.2) classifies the frame each syscall returns and
-- the boundary composes frames by it (`frameForShape`).  The `.unit` half is
-- **structural**: the boundary CONSTRUCTS unit frames (`frameForShape_unit`),
-- never reading the staged registers, so no arm can leak stale content
-- through a unit shape — the plan's draft phrasing ("a unit arm leaves the
-- caller's staged frame untouched") is deliberately NOT the theorem, because
-- it is false of any arm that context-switches (`saveOutgoingContext` writes
-- `registerContext`) and unnecessary once the read is constructed.  What
-- needs per-arm proof is the VALUE half: each value-shaped syscall's success
-- path stages exactly the value its shape declares, so the boundary's
-- pass-through read is of fresh data, never the caller's staged arguments.
-- `syscallReturnShape_value_returning` pins the value surface at exactly
-- {.receive, .call, .serviceQuery, .notificationWait, .replyRecv, .auditRead,
-- .auditDrain}; the seven theorems below cover it (`.call` through the reply
-- arm, per §3.5: a call never returns at its own boundary).  WS-SM SM9.A.10
-- added the last two, and for them the staging step is not a refinement but
-- the point: a reader that computes the right word and does not stage it hands
-- back the caller's own preloaded `x0`.

/-- **A donation leaves every return frame**: it writes no register
(`maybeDonateSchedContext_registersAgree`). -/
theorem readReturnFrame_maybeDonateSchedContext (st : SystemState) (n : SeLe4n.ObjId)
    (tid t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    Architecture.readReturnFrame (maybeDonateSchedContext st n tid) t =
      Architecture.readReturnFrame st t := by
  have h := maybeDonateSchedContext_registersAgree st n tid hInv t
  unfold Architecture.readReturnFrame
  cases h1 : (maybeDonateSchedContext st n tid).getTcb? t with
  | none =>
    rw [h1] at h
    cases h2 : st.getTcb? t with
    | none => rfl
    | some _ => rw [h2] at h; cases h
  | some a =>
    rw [h1] at h
    cases h2 : st.getTcb? t with
    | none => rw [h2] at h; cases h
    | some b =>
      rw [h2] at h
      simp only [Option.map_some, Option.some.injEq] at h
      simp only [h]

/-- **A checked donation leaves every return frame**, as the donation does. -/
theorem readReturnFrame_maybeDonateSchedContextFlowing (ctx : LabelingContext) (st : SystemState)
    (n : SeLe4n.ObjId) (tid t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    Architecture.readReturnFrame (maybeDonateSchedContextFlowing ctx st n tid) t =
      Architecture.readReturnFrame st t :=
  maybeDonateSchedContextFlowing_induct
    (fun s => Architecture.readReturnFrame s t = Architecture.readReturnFrame st t) ctx st n tid
    rfl (readReturnFrame_maybeDonateSchedContext st n tid t hInv)

/-- RA.B.8, `.notificationWait` (`.badge`): the arm's badge-consume path
stages exactly the consumed badge, and the boundary read recovers it. -/
theorem dispatchArm_notificationWait_matches_returnShape
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (notifId : SeLe4n.ObjId) (st st1 : SystemState)
    (badge : SeLe4n.Badge) (tcb : TCB)
    (hSyscall : decoded.syscallId = .notificationWait)
    (hTarget : cap.target = .object notifId)
    (hDispatch : notificationWaitCrossCoreDispatchChecked ctx notifId tid executingCore st
        = (st1, .ok (some badge)))
    (hTcb : st1.getTcb? tid = some tcb)
    (hObjInv : st1.objects.invExt) :
    Architecture.syscallReturnShape .notificationWait = .badge ∧
    ∃ stPost, dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), stPost) ∧
      Architecture.readReturnFrame stPost tid
        = Architecture.badgeReturnFrame st1 tid badge := by
  refine ⟨rfl, maybeDonateSchedContextFlowing ctx
    (Architecture.writeReturnFrameToTcb st1 tid (Architecture.badgeReturnFrame st1 tid badge))
    notifId tid, ?_, ?_⟩
  · simp [dispatchWithCapChecked, dispatchCapabilityOnly, completeSignalArm, hSyscall, hTarget, hDispatch,
      waitFindsNothing_of_consumed _ hDispatch]
  · rw [readReturnFrame_maybeDonateSchedContextFlowing _ _ _ _ _
      (writeReturnFrameToTcb_preserves_objects_invExt _ _ _ hObjInv)]
    exact Architecture.readReturnFrame_writeReturnFrame st1 tid _ tcb hTcb hObjInv

/-- RA.B.8, `.serviceQuery` (`.word`): the arm stages the resolved
registration's `ServiceId` — the answer it used to discard — and, the caller
having trapped with `Call` (`hCall`; seL4 replies only on `Call`), the boundary
read recovers it beside the success label and the message registers the caller
held.  Stated like its four siblings, over the live
dispatch at the given state, so the lookup hypothesis is load-bearing (a
first draft concluded only the arm's generic function equality and never
consumed `hLookup` — the decorative-hypothesis defect class SM8.D's
review history records). -/
theorem dispatchArm_serviceQuery_matches_returnShape
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (code : Nat) (epCap : Capability) (epId : SeLe4n.ObjId)
    (st st' : SystemState) (reg : ServiceRegistration) (tcb : TCB)
    (hSyscall : decoded.syscallId = .serviceQuery)
    (hTarget : cap.target = .serviceRegistry code)
    (hRes : resolveServiceEndpoint .serviceQuery tid decoded.msgInfo.extraCaps st = .ok (epCap, epId))
    (hLookup : lookupServiceChecked ctx tid epId st = .ok (reg, st'))
    (hTcb : st'.getTcb? tid = some tcb)
    (hCall : tcb.trappedCall = true)
    (hObjInv : st'.objects.invExt) :
    Architecture.syscallReturnShape .serviceQuery = .word ∧
    ∃ stPost, dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), stPost) ∧
      Architecture.readReturnFrame stPost tid
        = { Architecture.readReturnFrame st' tid with x0 := reg.sid.val.toUInt64, x1 := 0 } := by
  refine ⟨rfl,
    Architecture.writeCallReturnWord st' tid reg.sid.val.toUInt64,
    ?_, ?_⟩
  · simp [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchCapabilityOnlyChecked,
      serviceEndpointArm, hRes, serviceQueryStaged, hSyscall, hTarget, hLookup]
  · exact Architecture.readReturnFrame_writeCallReturnWord st' tid _ tcb hTcb hObjInv hCall

/-- RA.B.8 / WS-SM SM9.A.10, `.auditRead` (`.word`): the arm stages **the
selected word** — the entry the caller's index names, at the caller's own
clearance — and the boundary read recovers it.

The theorem the sub-phase's whole point rests on.  Without the staging step the
reader gates correctly, computes correctly, and the boundary hands back the
caller's own preloaded `x0`; the `hRead` hypothesis is what makes this a
statement about the *selected* word rather than about the arm's generic shape,
so it is load-bearing rather than decorative. -/
theorem dispatchArm_auditRead_matches_returnShape
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (args : Architecture.SyscallArgDecode.AuditReadArgs) (op : AuditReadOp)
    (st st' : SystemState) (w : Nat) (tcb : TCB)
    (hSyscall : decoded.syscallId = .auditRead)
    {code : Nat} (hTarget : cap.target = .auditTrail code)
    (hRight : cap.hasRight gate.requiredRight = true)
    (hArgs : Architecture.SyscallArgDecode.decodeAuditReadArgs decoded = .ok args)
    (hOp : decodeAuditReadOp args.opcode args.index args.chunk = some op)
    (hRead : auditReadFromCore (liftLegacyContext ctx) (validatedAuditMonitorClearance ctx)
      executingCore op st = .ok (w, st'))
    (hTcb : st'.getTcb? tid = some tcb)
    (hCall : tcb.trappedCall = true)
    (hObjInv : st'.objects.invExt) :
    Architecture.syscallReturnShape .auditRead = .word ∧
    ∃ stPost, dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), stPost) ∧
      Architecture.readReturnFrame stPost tid
        = { Architecture.readReturnFrame st' tid with x0 := w.toUInt64, x1 := 0 } := by
  refine ⟨rfl,
    Architecture.writeCallReturnWord st' tid w.toUInt64,
    ?_, ?_⟩
  · unfold dispatchWithCapChecked dispatchCapabilityOnly
    rw [hSyscall]
    simp only [extractAuditAuthority, hTarget, hRight, hArgs, hOp, hRead, if_true]
  · exact Architecture.readReturnFrame_writeCallReturnWord st' tid _ tcb hTcb hObjInv hCall

/-- RA.B.8 / WS-SM SM9.A.10, `.auditDrain` (`.word`): the arm stages the **new
visible length**, which is what a monitor recovering from the capacity cliff
reads to confirm the trail is drained. -/
theorem dispatchArm_auditDrain_matches_returnShape
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (args : Architecture.SyscallArgDecode.AuditDrainArgs)
    (st st' : SystemState) (n : Nat) (tcb : TCB)
    (hSyscall : decoded.syscallId = .auditDrain)
    {code : Nat} (hTarget : cap.target = .auditTrail code)
    (hRight : cap.hasRight gate.requiredRight = true)
    (hArgs : Architecture.SyscallArgDecode.decodeAuditDrainArgs decoded = .ok args)
    (hDrain : auditDrainVisiblePrefix (liftLegacyContext ctx)
      (validatedAuditMonitorClearance ctx)
      executingCore args.count st = .ok (n, st'))
    (hTcb : st'.getTcb? tid = some tcb)
    (hCall : tcb.trappedCall = true)
    (hObjInv : st'.objects.invExt) :
    Architecture.syscallReturnShape .auditDrain = .word ∧
    ∃ stPost, dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), stPost) ∧
      Architecture.readReturnFrame stPost tid
        = { Architecture.readReturnFrame st' tid with x0 := n.toUInt64, x1 := 0 } := by
  refine ⟨rfl,
    Architecture.writeCallReturnWord st' tid n.toUInt64,
    ?_, ?_⟩
  · unfold dispatchWithCapChecked dispatchCapabilityOnly
    rw [hSyscall]
    simp only [extractAuditAuthority, hTarget, hRight, hArgs, hDrain, if_true]
  · exact Architecture.readReturnFrame_writeCallReturnWord st' tid _ tcb hTcb hObjInv hCall

/-- RA.B.8, `.receive` (`.message`): the arm's non-blocking consume stages
the delivered message — the boundary read is of the fresh delivery, not the
caller's staged arguments.  The delivery hypotheses are read at the state
the caller-staging runs from (post the sender-completion staging, which
writes only the *sender's* saved context). -/
theorem dispatchArm_receive_matches_returnShape
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (epId : SeLe4n.ObjId)
    (replyIdOpt : Option SeLe4n.ReplyId) (st st' stDon : SystemState)
    (next : SeLe4n.ThreadId) (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (summary : CapTransferSummary) (msg : IpcMessage) (tcb : TCB)
    (st0 : SystemState)
    -- WS-SX SX4: `st` is the state the receive runs on, its busy reply's holder
    -- cancelled (`cancelRecvBusyReply`) from the state `st0` the arm is handed.
    (hCancel : cancelRecvBusyReply ctx tid gate decoded executingCore st0 = st)
    (hSyscall : decoded.syscallId = .receive)
    (hTarget : cap.target = .object epId)
    (hFlow : endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = true)
    (hReply : resolveRecvReplyId gate decoded st = .ok replyIdOpt)
    -- WS-SX SX7.2: the receive is not `NBRecv`'s failure with no sender waiting.
    (hNb : receiveFindsNothing (Syscall.wordReceiveBlocks (callerSyscallWord st tid)) st epId = false)
    -- seL4-MCS `receiveIPC`: the receive does not complete a bound notification.
    (hSig : receiveCompletesSignal ctx st tid = false)
    -- PR #873 round 6: the arm runs the WithCaps per-core receive, so the
    -- hypothesis names that transition and the staged `extraCaps` is the
    -- transfer summary's installed count rather than a hardcoded zero.
    -- WS-SX SX8.2: the receive runs on the state seL4's return leaves.
    (hDispatch : endpointReceiveDualWithCapsOnCore epId tid replyIdOpt executingCore
        (receiveReturnSchedContext (Syscall.wordReceiveBlocks (callerSyscallWord st tid)) st tid)
        = (st', .ok (next, summary, sgi)))
    -- WS-OD OD3.6: the arm's `maybeDonateSchedContext` step runs between the
    -- receive and the staging, so the boundary read is of the state it leaves.
    -- It writes only `schedContextBinding` and `SchedContext.boundThread` and so
    -- cannot disturb a return frame; naming it here rather than assuming it away
    -- is what keeps this theorem a statement about the arm the kernel runs.
    -- WS-OD OD3.14: and the priority half runs with it, under one guard, so the
    -- hypothesis names the hand-off rather than the donation alone -- the chain
    -- walk writes `pipBoost` and run-queue buckets, neither of which is a
    -- register context, so the frame conclusion is unchanged.
    (hDon : applyReceiveRendezvousHandoff st' tid next executingCore
        (receiveLendAdmits ctx st epId) = .ok stDon)
    (hTcb : stDon.getTcb? tid = some tcb)
    (hReady : tcb.ipcState = .ready)
    (hMsg : tcb.pendingMessage = some msg)
    (hObjInv : stDon.objects.invExt) :
    Architecture.syscallReturnShape .receive = .message ∧
    ∃ stPost, dispatchWithCapChecked ctx decoded tid executingCore gate cap st0 = .ok ((), stPost) ∧
      Architecture.readReturnFrame stPost tid
        = (Architecture.returnFrameOfMessage msg summary.capInfo
            (Architecture.messageOverflowWrites stDon tcb msg).length).deliveredOver
            tcb.registerContext := by
  refine ⟨rfl,
    Architecture.stageDeliveredMessage
      stDon tid summary.capInfo,
    ?_, ?_⟩
  · subst hCancel
    simp [dispatchWithCapChecked, dispatchCapabilityOnly, receiveResolvedArm, hSyscall, hTarget, hFlow,
      hReply, hSig, hNb, hDispatch, hDon]
  · exact Architecture.blockedReturn_staged_in_waiter_frame _ tid tcb msg
      summary.capInfo hTcb hReady hMsg hObjInv

/-- RA.B.8, `.replyRecv` (`.message`): the compound arm's receive leg stages
the delivered message for the server exactly as `.receive` does — and, since
PR #873 round 7, with the same honest `extraCaps`: the transfer summary the
WithCaps receive leg returns, not a zero. -/
theorem dispatchArm_replyRecv_matches_returnShape
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (epId : SeLe4n.ObjId)
    (rid : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (replyBadge : Option SeLe4n.Badge)
    (replyGrant : Bool)
    (st stB : SystemState) (msg : IpcMessage) (tcb : TCB) (summary : CapTransferSummary)
    (hSyscall : decoded.syscallId = .replyRecv)
    (hTarget : cap.target = .object epId)
    (hFlow : endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = true)
    (hXc : callerExtraCapsFault? st tid decoded.msgInfo.extraCaps = none)
    (hResolve : resolveReplyRecvReply gate decoded st =
      .ok (some (rid, prevCaller, replyBadge, replyGrant)))
    (hReplyFlow : securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf prevCaller) = true)
    (hSig : receiveCompletesSignal ctx st tid = false)
    (hBody : replyRecvTransferOnCore epId tid rid prevCaller decoded.msgInfo.label
        { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo,
          badge := replyBadge }
        replyGrant executingCore st (receiveLendAdmits ctx st epId) = .ok (summary, stB))
    (hTcb : stB.getTcb? tid = some tcb)
    (hReady : tcb.ipcState = .ready)
    (hMsg : tcb.pendingMessage = some msg)
    (hObjInv : stB.objects.invExt) :
    Architecture.syscallReturnShape .replyRecv = .message ∧
    ∃ stPost, dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), stPost) ∧
      Architecture.readReturnFrame stPost tid
        = (Architecture.returnFrameOfMessage msg summary.capInfo
            (Architecture.messageOverflowWrites stB tcb msg).length).deliveredOver
            tcb.registerContext := by
  refine ⟨rfl, Architecture.stageDeliveredMessage stB tid summary.capInfo, ?_, ?_⟩
  · simp [dispatchWithCapChecked, dispatchCapabilityOnly, hSyscall, hTarget, hFlow, hXc, hResolve,
      hReplyFlow, hSig, hBody]
  · exact Architecture.blockedReturn_staged_in_waiter_frame stB tid tcb msg
      summary.capInfo hTcb hReady hMsg hObjInv

/-- RA.B.8, `.replyRecv` whose receive **completes the bound notification**
(seL4-MCS `receiveIPC`'s `completeSignal`): the reply leg answers the caller, and
the receive stages exactly the consumed badge in the badge register
(`badgeReturnFrame`), every other register as the replier left it, as a `Wait`
on the notification stages it (`dispatchArm_notificationWait_matches_returnShape`).
The `.message` shape's pass-through read is of that fresh frame. -/
theorem dispatchArm_replyRecv_signal_matches_returnShape
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (epId : SeLe4n.ObjId)
    (rid : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (replyBadge : Option SeLe4n.Badge)
    (replyGrant : Bool) (st st1 st2 : SystemState) (badge : SeLe4n.Badge) (tcb : TCB)
    (hSyscall : decoded.syscallId = .replyRecv)
    (hTarget : cap.target = .object epId)
    (hFlow : endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = true)
    (hXc : callerExtraCapsFault? st tid decoded.msgInfo.extraCaps = none)
    (hResolve : resolveReplyRecvReply gate decoded st =
      .ok (some (rid, prevCaller, replyBadge, replyGrant)))
    (hReplyFlow : securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf prevCaller) = true)
    (hSig : receiveCompletesSignal ctx st tid = true)
    (hReply : replyTransferOnCoreChecked ctx tid prevCaller
        (replyRecvReplyMessageInfo decoded.msgInfo.label
          { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo,
            badge := replyBadge })
        (extractMessageRegisters decoded.msgRegs decoded.msgInfo)
        { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo,
          badge := replyBadge }
        replyGrant executingCore st = .ok ((), st1))
    (hSig1 : receiveCompletesSignal ctx st1 tid = true)
    (hReady1 : receiverIpcReady st1 tid = true)
    (hWait : notificationWaitCrossCoreDispatchChecked ctx (receiverBoundNotification st1 tid) tid
        executingCore st1 = (st2, .ok (some badge)))
    (hTcb : st2.getTcb? tid = some tcb)
    (hObjInv : st2.objects.invExt) :
    Architecture.syscallReturnShape .replyRecv = .message ∧
    ∃ stPost, dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), stPost) ∧
      Architecture.readReturnFrame stPost tid = Architecture.badgeReturnFrame st2 tid badge := by
  refine ⟨rfl, maybeDonateSchedContextFlowing ctx
    (Architecture.writeReturnFrameToTcb st2 tid (Architecture.badgeReturnFrame st2 tid badge))
    (receiverBoundNotification st1 tid) tid, ?_, ?_⟩
  · simp only [dispatchWithCapChecked, dispatchCapabilityOnly, hSyscall, hTarget, hFlow,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, hXc, hResolve, hReplyFlow, hSig]
    unfold replyRecvCompletesSignalArm
    rw [hReply]
    simp only [hSig1, hReady1, Bool.and_self, ↓reduceIte, completeSignalArm, hWait]
  · rw [readReturnFrame_maybeDonateSchedContextFlowing _ _ _ _ _
      (writeReturnFrameToTcb_preserves_objects_invExt _ _ _ hObjInv)]
    exact Architecture.readReturnFrame_writeReturnFrame st2 tid _ tcb hTcb hObjInv

/-- RA.B.8, `.call` (`.message`) — **through the reply arm**, per §3.5: a
successful call leaves the caller `blockedOnReply` in every ordering, so
its `.message` frame is delivered entirely by the reply path's RA.B.5b
staging.  The theorem is therefore the cross-arm statement: a `.reply`
dispatched at the server stages the *caller's* frame, and the boundary
read at the caller recovers the delivered reply.

**WS-RR RR4.14** adds the one pre-state hypothesis this statement always
needed and previously got for free: the answered caller must carry **no**
pending fault.  A faulted caller's reply is seL4's fault reply — it installs a
restart frame or abandons the thread — and delivers no message, so there is no
`.message` frame for the boundary to read.  `hNoFault` is a fact about the
pre-state of an ordinary `.call`, whose caller faulted at no point: a fault
delivery is itself a Call, and the two cannot be the same one.

The frame reports the reply's capability transfer (`replyTransferCaps`, seL4's
`doReplyTransfer` → `doIPCTransfer` under the reply capability's grant right):
the boundary reads the delivered reply with the transfer's `capInfo`, in the
state the transfer leaves. -/
theorem dispatchArm_call_frame_delivered_by_reply
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (rid : SeLe4n.ReplyId) (reply : Reply)
    (callerTid : SeLe4n.ThreadId) (st st1 : SystemState)
    (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (msg : IpcMessage) (tcb : TCB)
    (hSyscall : decoded.syscallId = .reply)
    (hTarget : cap.target = .replyCap rid)
    (hReply : st.getReply? rid = some reply)
    (hCaller : reply.caller = some callerTid)
    (hNoFault : threadHasPendingFault st callerTid = false)
    (hFlow : securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf callerTid) = true)
    (hDispatch : endpointReplyCrossCoreDispatchChecked ctx tid callerTid
        { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo,
          badge := cap.badge }
        executingCore st = (st1, .ok sgi))
    (summary : CapTransferSummary) (stX : SystemState)
    (hX : replyTransferCaps st tid callerTid (cap.rights.mem .grant) st1 = .ok (summary, stX))
    (hTcb : stX.getTcb? callerTid = some tcb)
    (hReady : tcb.ipcState = .ready)
    (hMsg : tcb.pendingMessage = some msg)
    (hObjInv : stX.objects.invExt) :
    Architecture.syscallReturnShape .call = .message ∧
    ∃ stPost, dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), stPost) ∧
      Architecture.readReturnFrame stPost callerTid
        = (Architecture.returnFrameOfMessage msg summary.capInfo
            (Architecture.messageOverflowWrites stX tcb msg).length).deliveredOver
            tcb.registerContext := by
  refine ⟨rfl, Architecture.stageDeliveredMessage stX callerTid summary.capInfo, ?_, ?_⟩
  · simp [dispatchWithCapChecked, dispatchCapabilityOnly, hSyscall, hTarget,
      replyAnsweredCaller?, hReply, hCaller, hFlow, replyTransferOnCoreChecked, hNoFault, hDispatch, hX]
  · exact Architecture.blockedReturn_staged_in_waiter_frame stX callerTid tcb msg summary.capInfo
      hTcb hReady hMsg hObjInv

-- ============================================================================
-- WS-J1-D: Invariant preservation for syscall entry
-- ============================================================================

/-- WS-J1-D: `syscallLookupCap` is read-only — state is unchanged on success. -/
theorem syscallLookupCap_preserves_state
    (gate : SyscallGate) (st st' : SystemState) (cap : Capability)
    (hOk : syscallLookupCap gate st = .ok (cap, st')) :
    st' = st := by
  rcases syscallLookupCap_implies_capability_held gate st cap st' hOk with ⟨_, _, _, _, hEq⟩
  exact hEq

/-- WS-J1-D: `lookupThreadRegisterContext` preserves `proofLayerInvariantBundle`
because it is read-only. -/
theorem lookupThreadRegisterContext_preserves_proofLayerInvariantBundle
    (tid : SeLe4n.ThreadId) (st st' : SystemState)
    (regs : SeLe4n.RegisterFile)
    (hInv : Architecture.proofLayerInvariantBundle st)
    (hOk : lookupThreadRegisterContext tid st = .ok (regs, st')) :
    Architecture.proofLayerInvariantBundle st' := by
  have hEq := lookupThreadRegisterContext_state_unchanged tid st regs st' hOk
  subst hEq; exact hInv

/-- WS-J1-D: a refused `syscallEntryChecked` commits no state, so the bundle the
pre-state satisfied is the bundle the caller is left with. -/
theorem syscallEntryChecked_error_preserves_proofLayerInvariantBundle
    (ctx : LabelingContext) (layout : SeLe4n.SyscallRegisterLayout)
    (executingCore : Concurrency.CoreId) (regCount : Nat)
    (st : SystemState) (e : KernelError)
    (hInv : Architecture.proofLayerInvariantBundle st)
    (_hErr : syscallEntryChecked ctx layout executingCore regCount st = .error e) :
    Architecture.proofLayerInvariantBundle st :=
  hInv

/-- WS-J1-D: the success path of the live syscall entry — if the pre-state
satisfies `proofLayerInvariantBundle` and the flow-checked dispatcher preserves
it, the post-state satisfies it.

Compositional: the context check is state-free, the register lookup is
read-only and the decode is pure, so the dispatcher is handed the entry's own
state, which satisfies it.  The caller provides the
dispatcher's preservation, which composes its per-arm results with the taint
seam's (`applySyscallTaint_preserves_proofLayerInvariantBundle`). -/
theorem syscallEntryChecked_preserves_proofLayerInvariantBundle
    (ctx : LabelingContext) (layout : SeLe4n.SyscallRegisterLayout)
    (executingCore : Concurrency.CoreId) (regCount : Nat)
    (st st' : SystemState)
    (hInv : Architecture.proofLayerInvariantBundle st)
    (hOk : syscallEntryChecked ctx layout executingCore regCount st = .ok ((), st'))
    (hDispatchPres : ∀ decoded tid stD stD',
        Architecture.proofLayerInvariantBundle stD →
        dispatchSyscallChecked ctx decoded tid executingCore stD = .ok ((), stD') →
        Architecture.proofLayerInvariantBundle stD') :
    Architecture.proofLayerInvariantBundle st' := by
  unfold syscallEntryChecked at hOk
  split at hOk
  · exact absurd hOk (by simp)
  · split at hOk
    · exact absurd hOk (by simp)
    · next tid _ =>
      split at hOk
      · exact absurd hOk (by simp)
      · split at hOk
        · exact absurd hOk (by simp)
        · next decoded _ =>
          exact hDispatchPres decoded tid _ st' hInv hOk

-- ============================================================================
-- WS-J1-D: Non-interference theorems for the syscall decode path
-- ============================================================================

/-- WS-J1-D: `decodeSyscallArgs` is a pure function over the register file —
it does not access or modify kernel state. Any two low-equivalent states remain
low-equivalent regardless of the decode result, because decode operates on the
register file (a `RegisterFile` value, not part of `SystemState`) and produces
a `SyscallDecodeResult` without state side-effects. -/
theorem decodeSyscallArgs_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂) :
    lowEquivalent ctx observer s₁ s₂ :=
  hLow

/-- WS-J1-D: `lookupThreadRegisterContext` is read-only and preserves
the observer's projection. -/
theorem lookupThreadRegisterContext_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (tid : SeLe4n.ThreadId) (st st' : SystemState)
    (regs : SeLe4n.RegisterFile)
    (hOk : lookupThreadRegisterContext tid st = .ok (regs, st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  have hEq := lookupThreadRegisterContext_state_unchanged tid st regs st' hOk
  subst hEq; rfl

/-- WS-J1-D: `lookupThreadRegisterContext` is read-only and preserves
low-equivalence. Two low-equivalent states remain so after lookup. -/
theorem lookupThreadRegisterContext_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (tid : SeLe4n.ThreadId)
    (s₁ s₂ s₁' s₂' : SystemState)
    (regs₁ regs₂ : SeLe4n.RegisterFile)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hOk₁ : lookupThreadRegisterContext tid s₁ = .ok (regs₁, s₁'))
    (hOk₂ : lookupThreadRegisterContext tid s₂ = .ok (regs₂, s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  have h₁ := lookupThreadRegisterContext_state_unchanged tid s₁ regs₁ s₁' hOk₁
  have h₂ := lookupThreadRegisterContext_state_unchanged tid s₂ regs₂ s₂' hOk₂
  subst h₁; subst h₂; exact hLow

/-- WS-J1-D: `syscallLookupCap` is read-only and preserves the observer's
projection. Capability resolution and right-checking do not modify state. -/
theorem syscallLookupCap_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (gate : SyscallGate) (st st' : SystemState) (cap : Capability)
    (hOk : syscallLookupCap gate st = .ok (cap, st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  have hEq := syscallLookupCap_preserves_state gate st st' cap hOk
  subst hEq; rfl

-- ============================================================================
-- WS-K-F4: Dispatch decode purity and preservation composition
-- ============================================================================

/-- WS-K-F4: Layer 2 decode functions within `dispatchWithCapChecked` are pure —
they operate on the `SyscallDecodeResult` value and never access or modify
`SystemState`. This means any decode failure is a state-preserving error,
and any decode success passes the original state unmodified to the delegated
kernel operation.

Proved by showing that two `SyscallDecodeResult` values with the same
`msgRegs` field and the same message length produce identical decode results
for all 6 structures — confirming that decode depends only on `msgRegs` and
the length its truncation check reads (`requireMessageLength`), not on
`capAddr`, the rest of `msgInfo`, or `syscallId`. -/
theorem dispatchWithCapChecked_layer2_decode_pure
    (d₁ d₂ : SyscallDecodeResult) (hRegs : d₁.msgRegs = d₂.msgRegs)
    (hLen : d₁.msgInfo.length = d₂.msgInfo.length) :
    (decodeCSpaceMintArgs d₁ = decodeCSpaceMintArgs d₂) ∧
    (decodeCSpaceCopyArgs d₁ = decodeCSpaceCopyArgs d₂) ∧
    (decodeCSpaceMoveArgs d₁ = decodeCSpaceMoveArgs d₂) ∧
    (decodeCSpaceDeleteArgs d₁ = decodeCSpaceDeleteArgs d₂) ∧
    (decodePageMapArgs d₁ = decodePageMapArgs d₂) ∧
    -- AH3-C: a function equality (parameterized by maxASID)
    (decodeVSpaceUnifyInstructionArgs d₁ = decodeVSpaceUnifyInstructionArgs d₂) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [decodeCSpaceMintArgs, decodeCSpaceCopyArgs, decodeCSpaceMoveArgs,
      decodeCSpaceDeleteArgs, decodePageMapArgs, requireMessageLength, requireMsgReg, hRegs,
      hLen]) <;>
    (try funext maxASID; simp only [decodeVSpaceUnifyInstructionArgs,
      requireMessageLength, requireMsgReg, hRegs, hLen])

-- ============================================================================
-- AK6-F (NI-H02): Composed projection preservation for dispatchCapabilityOnly
-- ============================================================================

/-- AK6-F (NI-H02): Compositional bridge for projection preservation over the
    capability-only dispatch path. This theorem provides the structural hook
    that composes any per-arm preservation witness into a single conclusion
    on the outer `dispatchCapabilityOnly`. Concretely:

    - Input: `hArmProj` — a per-arm preservation witness parameterised by the
      kernel operation that `dispatchCapabilityOnly` returns. The caller
      supplies one such witness, obtained by case-analysis on
      `decoded.syscallId` plus `cap.target`, and discharges it using
      existing per-op `_preserves_projection` theorems in
      `InformationFlow/Invariant/Operations.lean` or
      `storeObject_preserves_projection` at a non-observable cap target.
    - Output: projection preservation over `dispatchCapabilityOnly decoded
      cap tid = some kop, kop st = .ok ((), st')`.

    **Closure status (v0.29.12, post-audit classification):** `hArmProj`
    remains externally-supplied, BUT every cap-only arm now has a NAMED
    per-op preservation theorem in `InformationFlow/Invariant/Operations.lean`
    that the caller can directly reference. The 14 arms fall into THREE
    substantiveness tiers:

    **Fully substantive (7/14)** — proof uses only observability
    hypotheses, store invariants and pre-proven frame lemmas; NO abstract
    closures:
    - `.schedContextBind` → `schedContextBind_preserves_projection` (AK6F.14,
       `InformationFlow/PerCoreSchedulerNonInterference.lean`): the bind's
       per-core frame `schedContextBind_lowEquivalent` read at the boot core,
       whose view is the single-core projection.
    - `.cspaceDelete` → `cspaceDeleteSlot_preserves_projection`
    - `.serviceRevoke` → `revokeServiceChecked_preserves_projection`; the
       admitted revoke removes the registration the invoked endpoint records
       (`revokeServiceByRecordedRegistration_preserves_projection`), which the
       projected registry hides because its endpoint is one the caller may
       write and so one the observer cannot see.  Paired NI:
       `revokeServiceChecked_NI`.
    - `.serviceQuery` → `serviceQueryStaged_preserves_projection` for the
       state, and `serviceQueryStaged_answer_lowEquivalent` for the answer:
       the arm's outcome in two low-equivalent states is the same refusal or
       the same `x0` word, because the read gate admits only an endpoint the
       caller may read and the projected registry carries that endpoint's
       registration.  Paired NI: `serviceQueryStaged_NI`.
    - `.tcbSetIPCBuffer` → `setIPCBufferOp_preserves_projection`
    - `.vspaceMap` → `vspaceMapPageCheckedWithFlushFromState_preserves_projection`
    - `.vspaceUnmap` → `vspaceUnmapPageWithFlush_preserves_projection`

    **Hybrid substantive + legitimate closure (2/14)** — proof body
    uses frame lemmas for most phases but takes ONE closure over an
    external call (the schedule) whose preservation depends on
    invariants varying per caller:
    - `.tcbSetPriority` → `setPriorityOnCore_preserves_projection` (WS-SM SM8.B;
      the arm was rerouted off the boot-pinned `setPriorityOp` in PR #861 review
      round 12, and `setPriorityOp_preserves_projection` (v0.29.10) remains the
      statement for the pre-SMP operation) body uses
      `updatePrioritySource_preserves_projection` +
      `migrateRunQueueBucketOnCore_preserves_projection`; takes `hReschedProj`
      for the optional local preemption branch.
    - `.tcbSetMCPriority` → `setMCPriorityOnCore_preserves_projection` (WS-SM
      SM8.B; same reroute) mirror structure to setPriorityOnCore.

    **Closure-form (5/14)** — theorem takes `hProjEq` abstract closure;
    body is `hProjEq st' hStep`. NOT tautological for callers — each has
    DOCUMENTED FRAME LEMMAS letting a caller discharge `hProjEq` in
    ≈25-60 LOC using substantively-proven building blocks. Listed here
    WITH their discharge recipes:
    - `.schedContextUnbind` → `schedContextUnbind_preserves_projection` (AK6F.15);
      discharge via `projectState_scheduler_current_cleared_when_high` +
      `removeRunnable_preserves_projection` + `objects_insert_preserves_projection_high` × 2 +
      `projectState_replenishQueue_eq`.
    - `.schedContextConfigure` → `schedContextConfigure_preserves_projection` (AK6F.13);
      discharge via `projectState_replenishQueue_eq` +
      `objects_insert_preserves_projection_high` × 2 +
      `schedContextBind_frame_runQueue_rebucket`.
    - `.tcbSuspend` → `suspendThread_preserves_projection` (AK6F.18);
      hardest discharge (9 phases): `storeObject_preserves_projection` × 3 +
      `removeRunnable_preserves_projection` + `cancelDonation_preserves_projection`
      + `schedule_preserves_projection` (via `hSchedProj`).
    - `.tcbResume` → `resumeThread_preserves_projection` (AK6F.19);
      discharge via `resumeThread_frame_insert` + `resumeThread_frame_ensureRunnable`
      + `schedule_preserves_projection` (via `hSchedProj`).

    Plus helper: `cancelDonation_preserves_projection` (AK6F.17) — closure
    form, 3-arm discharge (`.unbound` trivial, `.bound` via
    `objects_insert_preserves_projection_high`, `.donated` via
    `returnDonatedSchedContext` preservation).

    Substantive closure of the 5 closure-form theorems is estimated at
    ≈300 LOC aggregate, tracked as continuation work AK6F.20b. Lean
    4.28.0's `split`/`split_ifs` interaction with `Except.ok` on
    deeply-nested `match`-based Bool conditions currently prevents clean destructuring; the frame lemmas above are
    the building blocks that a future patch will compose once a stable
    destructuring idiom is available.

    **Per-arm discharge table** (for callers constructing `hArmProj`):

    | Arm | Discharge |
    |-----|-----------|
    | `.cspaceDelete` | `cspaceDeleteSlot_preserves_projection` (Operations.lean:969) |
    | `.vspaceMap` | `vspaceMapPage_preserves_projection` (Operations.lean:753); requires `hRootHigh` via ASID resolution |
    | `.vspaceUnmap` | `vspaceUnmapPage_preserves_projection` (Operations.lean:797) |
    | `.serviceRevoke` | reduces to `cspaceRevoke_preserves_projection` (Operations.lean:1000) through the orchestrator |
    | `.serviceQuery` | read-only (`lookupServiceByRecordedRegistration` does not mutate state) |
    | `.schedContextBind` | **`schedContextBind_preserves_projection`** (PerCoreSchedulerNonInterference.lean), at a hidden context and thread |
    | `.schedContextConfigure/Unbind` | `storeObject_preserves_projection` / `objects_insert_preserves_projection_high` (Operations.lean) at non-observable SchedContext target + TCB/RunQueue field preservation |
    | `.tcbSetIPCBuffer` | **`setIPCBufferOp_preserves_projection`** (Operations.lean — AK6-F.2b, v0.29.10) |
    | `.tcbSetPriority/SetMCPriority` | `objects_insert_preserves_projection_high` at non-observable TCB/SC — uses the universal direct-insert frame lemma (Operations.lean — AK6-F Step A, v0.29.10) |
    | `.tcbSetAffinity` | **`setThreadCpuAffinityOnCore_preserves_projection`** (Operations.lean — WS-SM SM8.B, review round 42) at non-observable target — the **live** wrapper, which round 37 rerouted this arm to; the boot-core `setThreadCpuAffinityOp_preserves_projection` (SM5.H.4) is its `bootCoreId` instance, reachable through `setThreadCpuAffinityOp_eq_onCore_state` but not needed here.  The affinity write is `cpuAffinity`-erased (invisible); the run-queue migration's write, at the executing core rather than a pinned boot core, preserves the filtered `projectRunnable` for a high thread (`migrateRunQueueOnAffinityChange_preserves_projection`); the replenishment migration is invisible when the target's bound context is non-observable (`migrateSchedContextReplenishment_preserves_projection`; the projection keeps each context's release core, WS-ZA ZA6.30). |
    | `.tcbSuspend/Resume` | `storeObject_preserves_projection` at non-observable TCB target; the review-round retire prefix is `applyFaultRestart`, a register + `pendingFault` write on the same target |

    **New AK6-F building blocks in v0.29.10:**
    - `objects_insert_preserves_projection_high` — universal direct-insert
      frame lemma; enables discharge of every arm whose underlying op uses
      `{ st with objects := st.objects.insert … }` instead of `storeObject`.
    - `setIPCBufferOp_preserves_projection` — full per-op preservation for
      the `.tcbSetIPCBuffer` arm.
    - `projectState_replenishQueue_eq` and
      `projectState_scheduler_current_cleared_when_high` — frame helpers
      for scheduler-field mutations that don't affect projection
      (`Projection.lean` — AK6-F.2a). -/
theorem dispatchCapabilityOnly_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (decoded : SyscallDecodeResult) (cap : Capability) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (st st' : SystemState)
    (hArmProj : ∀ kop, dispatchCapabilityOnly decoded cap tid executingCore = some kop →
                       kop st = .ok ((), st') →
                       projectState ctx observer st' = projectState ctx observer st)
    (hKop : ∃ kop, dispatchCapabilityOnly decoded cap tid executingCore = some kop ∧
                    kop st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  obtain ⟨kop, hSome, hRun⟩ := hKop
  exact hArmProj kop hSome hRun

-- ============================================================================
-- WS-SM SM9.D.7 (PR #873 round 6): the seam is at the dispatcher
-- ============================================================================

/-- **No success path through the checked dispatcher skips the taint seam.**

The property that makes moving the seam down a layer worth anything: whatever
route a successful `dispatchSyscallChecked` takes — the target-first resolve or
the classic rights-gated lookup, any of the 33 arms — the state it returns is the
plan applied to the state the invoke committed, keyed on the state the dispatcher
itself was given and on the decoded syscall.

Stated existentially over the committed state rather than as an equation against
a named inner function, because there is no inner function: the seam wraps the
invoke in place.  That is the stronger form for this purpose — it quantifies over
every path rather than pinning one spelling, so an arm added tomorrow either
satisfies it or stops this elaborating.

`entryDecode_some_entry_dispatches` (SM8.D) pins the *entry* to the dispatcher;
this pins the dispatcher to the seam.  Together they say what the old
entry-level equation said, one layer down and over every caller rather than
over one. -/
theorem dispatchSyscallChecked_applies_taint_plan
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (st st' : SystemState)
    (h : dispatchSyscallChecked ctx decoded tid executingCore st = .ok ((), st')) :
    ∃ stPost, st' = applySyscallTaint (syscallTaintPlan st tid decoded) st stPost := by
  simp only [dispatchSyscallChecked, SystemState.getObject?] at h
  -- The caller/core guard: a mismatched pair is refused before any lookup.
  split at h
  · exact absurd h (by simp)
  -- WS-ZA ZA4.3: a yield's plan is inert, so the step leaves its state as is.
  by_cases hY : decoded.syscallId = .yield
  · exact ⟨st', by rw [syscallTaintPlan_yield st tid decoded hY, applySyscallTaint_inert]⟩
  rw [if_neg hY] at h
  split at h
  · split at h
    · exact absurd h (by simp)
    · next stPost _ => exact ⟨stPost, by simpa using h.symm⟩
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **The caller and the executing core are one fact.**  A mismatched pair —
`tid` not the thread current on `executingCore` — is refused `.illegalState`
by the checked dispatcher before any lookup.

Capability resolution and the flow checks act as `tid`, while the
`.declassify`, `.declassifySignal` and audit arms take their acting subject from
`currentOnCore executingCore`.  An integrator calling the dispatcher directly
with a core on which `tid` is not current would otherwise have had one core's
subject authorize or attribute a downgrade for another core's caller. -/
theorem dispatchSyscallChecked_refuses_mismatched_core
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (hMismatch : st.scheduler.currentOnCore executingCore ≠ some tid) :
    dispatchSyscallChecked ctx decoded tid executingCore st = .error .illegalState := by
  simp only [dispatchSyscallChecked, hMismatch, ne_eq, not_false_eq_true, ↓reduceIte]

/-- **A successful checked dispatch acted as the executing core's current
thread.**  Every arm's subject — `tid` for resolution and flow checks,
`currentOnCore executingCore` for the declassification and audit arms — is
therefore the same thread. -/
theorem dispatchSyscallChecked_ok_caller_current
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (st st' : SystemState)
    (h : dispatchSyscallChecked ctx decoded tid executingCore st = .ok ((), st')) :
    st.scheduler.currentOnCore executingCore = some tid := by
  by_cases hCur : st.scheduler.currentOnCore executingCore = some tid
  · exact hCur
  · rw [dispatchSyscallChecked_refuses_mismatched_core ctx decoded tid executingCore st
      hCur] at h
    exact absurd h (by simp)

-- ============================================================================
-- AE1-G3: Master dispatch NI theorem
-- ============================================================================

/-- AE1-G3: Master dispatch NI theorem — `dispatchSyscallChecked` preserves
the observer's projection when the calling thread is non-observable.

This theorem decomposes `dispatchSyscallChecked` through its three layers:
1. **TCB/CNode lookup** — read-only (pattern match on `objects`)
2. **Capability resolution** — read-only (proved by
   `syscallLookupCap_implies_capability_held`)
3. **Inner dispatch** — the actual state-modifying operation

The `hInnerProj` hypothesis captures the NI property of the inner dispatch
(layer 3). It is dischargeable per-arm from existing per-operation NI
theorems:
- 14 capability-only arms (via `dispatchCapabilityOnly`):
  `storeObject_preserves_projection` + operation-specific frame lemmas
- 11 explicit arms (via `dispatchWithCapChecked` match):
  `endpointSendDual_preserves_projection`, `endpointCall_preserves_projection`,
  `propagatePIP_preserves_projection`, `applyCallDonation_preserves_projection`,
  etc.

Combined with `projPreserving_preserves_lowEquivalent` (AE1-G2 in
Composition.lean), this yields the full two-sided NI guarantee for the
complete syscall dispatch path. -/
theorem dispatchSyscallChecked_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (st st' : SystemState)
    (_hTidHigh : threadObservable ctx observer tid = false)
    (hInnerProj : ∀ (gate : SyscallGate) (cap : Capability),
        syscallResolveCap gate st = .ok (cap, st) →
        ∀ stOut, dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), stOut) →
        projectState ctx observer stOut = projectState ctx observer st)
    (hYieldProj : decoded.syscallId = .yield →
        ∀ stOut, dispatchYield executingCore st = .ok ((), stOut) →
        projectState ctx observer stOut = projectState ctx observer st)
    (hStep : dispatchSyscallChecked ctx decoded tid executingCore st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  simp only [dispatchSyscallChecked, SystemState.getObject?] at hStep
  -- The caller/core guard: a mismatched pair is refused before any lookup.
  split at hStep
  · exact absurd hStep (by simp)
  -- WS-ZA ZA4.3: the capability-free yield, carried by its own hypothesis.
  by_cases hY : decoded.syscallId = .yield
  · rw [if_pos hY] at hStep; exact hYieldProj hY st' hStep
  rw [if_neg hY] at hStep
  -- Layer 1: TCB lookup (read-only)
  split at hStep
  · -- some (.tcb tcb)
    -- PR #873 round 6: layer 4 — the provenance seam.  It writes only
    -- `declassificationTaint`, which is not on the projection surface
    -- (`applySyscallTaint_preserves_projection`), so the observer's view of
    -- the sealed state is the view of the state the invoke committed, and the
    -- inner-NI hypothesis carries the rest.
    split at hStep
    · simp at hStep
    next stPost hInvoke =>
      have hSt : st' = applySyscallTaint (syscallTaintPlan st tid decoded) st stPost := by
        simpa using hStep.symm
      rw [hSt, applySyscallTaint_preserves_projection]
      -- The typed gate ran the arm only on a capability the full lookup
      -- returned, so the inner-NI hypothesis, stated over the resolve, covers
      -- it (`syscallResolveCap_of_lookup`).
      obtain ⟨cap, hCap, _, hArm⟩ := syscallInvokeTyped_ok _ _ _ st () stPost hInvoke
      exact hInnerProj _ cap (syscallResolveCap_of_lookup _ st cap st hCap) stPost hArm
  · -- some (not .tcb): error
    simp at hStep
  · -- none: error
    simp at hStep

-- ============================================================================
-- PR #861 review (architectural) — delegation theorems for the CROSS-CORE arms
--
-- Three of the nine review rounds on this PR found the same defect in different
-- clothes: an inventory in `NonInterferenceCrossCore.lean` claiming that some
-- function is "the arm the live dispatch reaches", where the claim was wrong
-- (round 4: three arms missing; round 5: `.reply`/`.replyRecv`/`.tcbSuspend`
-- naming the below-API transition rather than the wrapper; round 8: `.receive`
-- classified a leg when the live arm calls it directly).
--
-- The eight `dispatchWithCap_…_delegates` theorems above never drifted, and the
-- reason is structural rather than lucky: they *are* the tie between the table
-- and this file, so a wrong entry does not compile.  The cross-core arms had no
-- such tie, and every one of the three drifts happened there.
--
-- These supply it.  `syscallDelegates` below turns each into a proposition
-- *indexed by the syscall*, and `crossCoreLiveArmEvidence`
-- (NonInterferenceCrossCore §7) carries a proof of it — so "X is the live arm
-- for syscall S" is a claim the type checker enforces.  A proof cannot be
-- borrowed between arms, and syscalls with no delegation theorem map to
-- `False`, so evidence for them cannot be constructed at all.
--
-- The first cut of this recorded a theorem *name* instead, which review round 11
-- rightly rejected: a name check establishes that some declaration exists, not
-- that it says anything about the arm citing it.
-- ============================================================================

/-- **WS-SM SM8.C.9: the live `.declassify` arm routes to
`declassifyObjectFromCore`.**

Checked dispatch only — `.declassify` is the one syscall with no unchecked twin
(`dispatchWithCap_declassify_denied` is its dual), because "unchecked
declassification" would mean "every downgrade authorized". -/
theorem dispatchWithCapChecked_declassify_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (code : Nat) (targetCap : Capability)
    (targetId : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .declassify)
    (hTarget : cap.target = .auditTrail code)
    (hRes : resolveDeclassifyTarget tid decoded.msgInfo.extraCaps st = .ok (targetCap, targetId)) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      declassifyObjectFromCore (liftLegacyContext ctx) ctx.declassificationPolicy
        executingCore targetId st := by
  unfold dispatchWithCapChecked dispatchCapabilityOnly
  rw [hSyscall]
  simp only [hTarget, hRes]

/-- **WS-SM SM8.C.9**: an unconfigured deployment cannot declassify.

`LabelingContext.declassificationPolicy` defaults to deny-all, so the checked
arm refuses too — the fail-closed default, stated where an operator reading the
dispatch would look for it. -/
theorem dispatchWithCapChecked_declassify_default_denied
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (code : Nat) (targetCap : Capability)
    (targetId : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .declassify)
    (hTarget : cap.target = .auditTrail code)
    (hRes : resolveDeclassifyTarget tid decoded.msgInfo.extraCaps st = .ok (targetCap, targetId))
    (hDefault : ctx.declassificationPolicy.canDeclassify = fun _ _ => false) :
    ¬ ∃ st', dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), st') := by
  rintro ⟨st', hStep⟩
  rw [dispatchWithCapChecked_declassify_delegates ctx decoded tid executingCore gate cap code
    targetCap targetId st hSyscall hTarget hRes] at hStep
  obtain ⟨cur, hCur⟩ : ∃ x, st.scheduler.currentOnCore executingCore = x :=
    ⟨_, rfl⟩
  cases cur with
  | none =>
    rw [declassifyObjectFromCore_no_subject _ _ _ _ _ hCur] at hStep
    simp at hStep
  | some tid' =>
    obtain ⟨ty, hTy⟩ : ∃ t, st.getObjectType? targetId = t := ⟨_, rfl⟩
    cases ty with
    | none =>
      rw [declassifyObjectFromCore_absent_target _ _ _ _ _ _ hCur hTy] at hStep
      simp at hStep
    | some t =>
      obtain ⟨_, hDecl⟩ := declassifyObjectFromCore_authorized _ _ _ _ _ _ _ t hCur hTy hStep
      rw [hDefault] at hDecl
      exact Bool.noConfusion hDecl

/-- **WS-SM SM9.C.8/SM9.C.9: the live `.declassifySignal` arm routes to
`notificationSignalDeclassifiedCrossCoreDispatch`.**

Checked dispatch only, like `.declassify` (`dispatchWithCap_declassifySignal_denied`
is its dual).

The conclusion names the **whole arm**, not just the transition: the arm runs
nothing after the declassifying signal, exactly as on the ordinary
`.notificationSignal` path (the wake itself writes the badge register and drops
a woken bound receiver's reply stash).  Stating it that way is the point — an
arm that ran anything else around the transition would not satisfy this, and the
per-core routing gate and the cross-core inventory both consume this equation
as their tie to the dispatch. -/
theorem dispatchWithCapChecked_declassifySignal_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (code : Nat) (ntfnCap : Capability)
    (notifId : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .declassifySignal)
    (hTarget : cap.target = .auditTrail code)
    (hRes : resolveDeclassifySignalTarget tid decoded.msgInfo.extraCaps st = .ok (ntfnCap, notifId)) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      (match notificationSignalDeclassifiedCrossCoreDispatch (liftLegacyContext ctx)
              ctx.declassificationPolicy notifId ntfnCap.signalBadge executingCore st with
       | (st', .ok _) =>
           .ok ((), st')
       | (_, .error e) => .error e) := by
  unfold dispatchWithCapChecked dispatchCapabilityOnly
  rw [hSyscall]
  simp only [hTarget, hRes]

/-- The checked signal arm's badge is its capability's too
(`dispatchWithCap_notificationSignal_badge_of_cap`'s checked twin). -/
theorem dispatchWithCapChecked_notificationSignal_badge_of_cap (ctx : LabelingContext)
    (decoded decoded' : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (h : decoded.syscallId = .notificationSignal)
    (h' : decoded'.syscallId = .notificationSignal) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
      dispatchWithCapChecked ctx decoded' tid executingCore gate cap := by
  unfold dispatchWithCapChecked dispatchCapabilityOnly
  rw [h, h']

/-- The declassifying signal's badge is its notification capability's: no word
of the decode reaches it (`dispatchWithCapChecked_declassifySignal_delegates`
names `ntfnCap.signalBadge`, extra capability 0's), so two calls naming the same
extra capabilities are the same arm, and neither can forge a badge. -/
theorem dispatchWithCapChecked_declassifySignal_badge_of_cap (ctx : LabelingContext)
    (decoded decoded' : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (h : decoded.syscallId = .declassifySignal)
    (h' : decoded'.syscallId = .declassifySignal)
    (hXc : decoded.msgInfo.extraCaps = decoded'.msgInfo.extraCaps) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
      dispatchWithCapChecked ctx decoded' tid executingCore gate cap := by
  unfold dispatchWithCapChecked dispatchCapabilityOnly
  rw [h, h', hXc]

/-- **WS-SM SM9.C.8**: an unconfigured deployment performs no downgrade through
a signal.

`LabelingContext.declassificationPolicy` defaults to deny-all, and the honest
statement of what that buys is *not* "the syscall fails".  A declassifying
signal whose hops the base lattice already permits is an ordinary signal, and
refusing it under the default would be a usability decision dressed up as a
security one.  What the default guarantees is that the **audit trail cannot
grow** — and since an entry is appended exactly when a downgrade is authorized
(`declassifiedSignal_never_unaudited`), that is precisely "no downgrade
happened".

Stated at the dispatch, over the committed post-state of the whole arm, because
the post-processing after the transition (the stash clear) must not touch the
trail either — an arm that appended there would
falsify this while the transition's own theorem stayed true. -/
theorem dispatchWithCapChecked_declassifySignal_default_no_downgrade
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (code : Nat) (ntfnCap : Capability)
    (notifId : SeLe4n.ObjId)
    (st st' : SystemState)
    (hSyscall : decoded.syscallId = .declassifySignal)
    (hTarget : cap.target = .auditTrail code)
    (hRes : resolveDeclassifySignalTarget tid decoded.msgInfo.extraCaps st = .ok (ntfnCap, notifId))
    (hDefault : ctx.declassificationPolicy.canDeclassify = fun _ _ => false)
    (hStep : dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), st')) :
    st'.declassificationAuditLog = st.declassificationAuditLog := by
  rw [dispatchWithCapChecked_declassifySignal_delegates ctx decoded tid executingCore gate cap code
    ntfnCap notifId st hSyscall hTarget hRes] at hStep
  unfold notificationSignalDeclassifiedCrossCoreDispatch at hStep
  obtain ⟨pair, hPair⟩ : ∃ p, notificationSignalDeclassifiedOnCore (liftLegacyContext ctx)
      ctx.declassificationPolicy notifId ntfnCap.signalBadge executingCore st = p :=
    ⟨_, rfl⟩
  rw [hPair] at hStep
  obtain ⟨stT, res⟩ := pair
  cases res with
  | error e => exact absurd hStep (by simp)
  | ok sgi =>
    simp only at hStep
    -- The transition's own trail statement: the arm runs nothing after it.
    have hTrail := declassifiedSignal_default_policy_never_downgrades (liftLegacyContext ctx)
      ctx.declassificationPolicy notifId ntfnCap.signalBadge executingCore st stT
      sgi hDefault hPair
    simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
    obtain ⟨-, hSt'⟩ := hStep
    -- seL4's `sendSignal` donation after the record writes no audit entry.
    rw [← hSt', donateToSignalledFlowingGeneric_declassificationAuditLog_eq]
    exact hTrail

/-- **WS-SM SM9.A.10: the live `.auditRead` arm routes to `auditReadFromCore`,
and writes the selected word into the caller's return register.**

Checked dispatch only, like `.declassify`, and for a neighbouring reason: every
value the reader returns is selected by the caller's *clearance*, which lives in
the `LabelingContext` the unchecked path does not carry
(`dispatchWithCap_auditRead_denied` is its dual).

The conclusion names the return-frame write, not just the transition.  That is
the load-bearing part: a reader that gates correctly, computes correctly and
does not stage its result hands the caller back its own preloaded `x0`. -/
theorem dispatchWithCapChecked_auditRead_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (args : Architecture.SyscallArgDecode.AuditReadArgs) (op : AuditReadOp)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .auditRead)
    {code : Nat} (hTarget : cap.target = .auditTrail code)
    (hRight : cap.hasRight gate.requiredRight = true)
    (hArgs : Architecture.SyscallArgDecode.decodeAuditReadArgs decoded = .ok args)
    (hOp : decodeAuditReadOp args.opcode args.index args.chunk = some op) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      (match auditReadFromCore (liftLegacyContext ctx) (validatedAuditMonitorClearance ctx)
          executingCore op st with
       | .error e => .error e
       | .ok (w, st') =>
           .ok ((), Architecture.writeCallReturnWord st' tid w.toUInt64)) := by
  unfold dispatchWithCapChecked dispatchCapabilityOnly
  rw [hSyscall]
  simp only [extractAuditAuthority, hTarget, hRight, hArgs, hOp, if_true]

/-- **WS-SM SM9.A.10: the live `.auditDrain` arm routes to
`auditDrainVisiblePrefix`, and writes the new visible length back.** -/
theorem dispatchWithCapChecked_auditDrain_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (args : Architecture.SyscallArgDecode.AuditDrainArgs) (st : SystemState)
    (hSyscall : decoded.syscallId = .auditDrain)
    {code : Nat} (hTarget : cap.target = .auditTrail code)
    (hRight : cap.hasRight gate.requiredRight = true)
    (hArgs : Architecture.SyscallArgDecode.decodeAuditDrainArgs decoded = .ok args) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      (match auditDrainVisiblePrefix (liftLegacyContext ctx)
          (validatedAuditMonitorClearance ctx)
          executingCore args.count st with
       | .error e => .error e
       | .ok (n, st') =>
           .ok ((), Architecture.writeCallReturnWord st' tid n.toUInt64)) := by
  unfold dispatchWithCapChecked dispatchCapabilityOnly
  rw [hSyscall]
  simp only [extractAuditAuthority, hTarget, hRight, hArgs, if_true]

/-- **WS-SM SM9.A.9 (the confused-deputy gate, at the arm)**: a capability that
carries the required right but does **not** target the audit trail is rejected,
on both audit syscalls.

The v0.32.97 class stated where a reviewer of the dispatch would look for it.
`syscallLookupCap` has already accepted the capability by the time this arm
runs — it checks the right and nothing about the target — so without this the
reader would be reachable by any thread holding any readable capability. -/
theorem dispatchWithCapChecked_audit_rejects_non_audit_capability
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (oid : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .auditRead ∨ decoded.syscallId = .auditDrain)
    (hTarget : cap.target = .object oid) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .error (.invalidCapability 0) := by
  unfold dispatchWithCapChecked dispatchCapabilityOnly
  rcases hSyscall with h | h <;> rw [h] <;> simp only [extractAuditAuthority, hTarget]

/-- **WS-SM SM9.A.9 (PR #870 round 5, the second gate at the arm)**: an audit
capability that lacks the required right is refused `.illegalAuthority` — by
the ARM, after the target check, which is what "target first, right second"
means now that the checked dispatch routes the audit ids through the
resolve-only lookup. -/
theorem dispatchWithCapChecked_audit_insufficient_right_denied
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (st : SystemState)
    (hSyscall : decoded.syscallId = .auditRead ∨ decoded.syscallId = .auditDrain)
    {code : Nat} (hTarget : cap.target = .auditTrail code)
    (hRight : cap.hasRight gate.requiredRight = false) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .error .illegalAuthority := by
  unfold dispatchWithCapChecked dispatchCapabilityOnly
  rcases hSyscall with h | h <;> rw [h] <;>
    simp only [extractAuditAuthority, hTarget, hRight, if_false, Bool.false_eq_true]

/-- **The type check precedes every right, at the dispatch the syscall takes**:
a resolvable capability that is not of the syscall's type
(`syscallTargetAccepted`) is refused `.invalidCapability` **whatever rights it
carries**, as seL4's `decodeInvocation` dispatches on the capability's type
before any decoder checks a right.  There is no `hasRight` hypothesis, which is
the theorem's point. -/
theorem dispatchSyscallChecked_type_before_rights
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId)
    (tcb : TCB) (ref : SlotRef) (cap : Capability) (st : SystemState)
    (hNotYield : decoded.syscallId ≠ .yield)
    (hCur : st.scheduler.currentOnCore executingCore = some tid)
    (hTcb : st.getTcb? tid = some tcb)
    (hResolve : lookupSlot tcb decoded.capAddr st = .ok ref)
    (hLookup : SystemState.lookupSlotCap st ref = some cap)
    (hXf : decodedExtraCapsFault? st tid decoded = none)
    (hType : syscallTargetAccepted decoded.syscallId st cap = false) :
    dispatchSyscallChecked ctx decoded tid executingCore st = .error (.invalidCapability 0) := by
  simp only [dispatchSyscallChecked, hCur, ne_eq, not_true_eq_false, ↓reduceIte, hNotYield,
    SystemState.getObject?,
    (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb,
    syscallInvokeTyped, syscallResolveCap, SyscallGate.lookupSlot_mk, hResolve, hLookup, hXf]
  by_cases hRes : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true <;>
    simp [hRes, hType]

/-- **The extra capabilities are looked up after the invoked capability and
before its type** (seL4's `handleInvocation`: `lookupCapAndSlot`, then
`lookupExtraCaps`, then `decodeInvocation`): a capability that resolves to one
user space may hold, with an extra capability whose address does not resolve,
is refused with that lookup's failure in the send phase, whatever the
capability's type and rights. -/
theorem dispatchSyscallChecked_extraCaps_before_type
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId)
    (tcb : TCB) (ref : SlotRef) (cap : Capability) (st : SystemState)
    (a : SeLe4n.CPtr) (f : LookupFault)
    (hNotYield : decoded.syscallId ≠ .yield)
    (hCur : st.scheduler.currentOnCore executingCore = some tid)
    (hTcb : st.getTcb? tid = some tcb)
    (hResolve : lookupSlot tcb decoded.capAddr st = .ok ref)
    (hLookup : SystemState.lookupSlotCap st ref = some cap)
    (hNotReserved : SeLe4n.Kernel.capTargetsReservedKernelObject cap = false)
    (hXf : decodedExtraCapsFault? st tid decoded = some (a, f)) :
    dispatchSyscallChecked ctx decoded tid executingCore st = .error (.failedLookup false f) := by
  simp only [dispatchSyscallChecked, hCur, ne_eq, not_true_eq_false, ↓reduceIte, hNotYield,
    SystemState.getObject?,
    (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb,
    syscallInvokeTyped, syscallResolveCap, SyscallGate.lookupSlot_mk, hResolve, hLookup, hXf,
    hNotReserved, Bool.false_eq_true]

/-- **An empty slot is refused after the extra capabilities' lookup** (seL4's
`lookupCapAndSlot` hands the null capability on, `lookupExtraCaps` runs, and
only `decodeInvocation` refuses the null capability): a slot holding no
capability, with an extra capability whose address does not resolve, is refused
with that lookup's failure in the send phase. -/
theorem dispatchSyscallChecked_extraCaps_before_null
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId)
    (tcb : TCB) (ref : SlotRef) (st : SystemState)
    (a : SeLe4n.CPtr) (f : LookupFault)
    (hNotYield : decoded.syscallId ≠ .yield)
    (hCur : st.scheduler.currentOnCore executingCore = some tid)
    (hTcb : st.getTcb? tid = some tcb)
    (hResolve : lookupSlot tcb decoded.capAddr st = .ok ref)
    (hLookup : SystemState.lookupSlotCap st ref = none)
    (hXf : decodedExtraCapsFault? st tid decoded = some (a, f)) :
    dispatchSyscallChecked ctx decoded tid executingCore st = .error (.failedLookup false f) := by
  simp only [dispatchSyscallChecked, hCur, ne_eq, not_true_eq_false, ↓reduceIte, hNotYield,
    SystemState.getObject?,
    (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb,
    syscallInvokeTyped, syscallResolveCap, SyscallGate.lookupSlot_mk, hResolve, hLookup, hXf,
    syscallResolveRefusal]

/-- **The right is checked after the type**: a capability of the syscall's
type without the syscall's right is refused with the syscall's missing-right
answer (`syscallMissingRightError`) before the arm runs.  Together with
`dispatchSyscallChecked_type_before_rights` this pins the composed order. -/
theorem dispatchSyscallChecked_right_after_type
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId)
    (tcb : TCB) (ref : SlotRef) (cap : Capability) (st : SystemState)
    (hNotYield : decoded.syscallId ≠ .yield)
    (hCur : st.scheduler.currentOnCore executingCore = some tid)
    (hTcb : st.getTcb? tid = some tcb)
    (hResolve : lookupSlot tcb decoded.capAddr st = .ok ref)
    (hLookup : SystemState.lookupSlotCap st ref = some cap)
    (hNotReserved : SeLe4n.Kernel.capTargetsReservedKernelObject cap = false)
    (hXf : decodedExtraCapsFault? st tid decoded = none)
    (hType : syscallTargetAccepted decoded.syscallId st cap = true)
    (hRight : cap.hasRight (syscallRequiredRight decoded.syscallId) = false) :
    dispatchSyscallChecked ctx decoded tid executingCore st =
      .error (syscallMissingRightError decoded.syscallId) := by
  simp only [dispatchSyscallChecked, hCur, ne_eq, not_true_eq_false, ↓reduceIte, hNotYield,
    SystemState.getObject?,
    (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb,
    syscallInvokeTyped, syscallResolveCap, SyscallGate.lookupSlot_mk, hResolve, hLookup, hXf]
  simp [hNotReserved, hType, hRight]

-- ============================================================================
-- WS-RR RR7.3: the capability-held guarantee on the LIVE checked dispatch path
--
-- Register §4 finding 5: the capability-held guarantee was stated over the
-- *legacy* entry, which was `bootCoreId`-pinned and whose only non-test callers
-- were the trace harness and the exception model (that entry was retired by
-- owner decision 2026-11-13, its callers moved here).  The path the hardware
-- takes is
-- `@[export lean_syscall_dispatch_cross_core]` → `syscallDispatchCrossCoreEntry`
-- → `Platform.FFI.syscallDispatchFromAbi` → `syscallEntryChecked` →
-- `dispatchSyscallChecked`, and nothing covered it.  These are the analogues,
-- parameterized over the executing core rather than the boot core.
--
-- Every arm runs behind one gate, `syscallInvokeTyped`: the type, then the
-- right, then the arm.
-- ============================================================================

/-- **WS-RR RR7.3**: if the **flow-checked** dispatch succeeds, the caller held a
capability with the required access right for the invoked syscall.

Stated through the typed gate every arm runs behind (`syscallInvokeTyped_requires_right`). -/
theorem dispatchSyscallChecked_requires_right
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (st : SystemState) (st' : SystemState)
    (hCap : decoded.syscallId ≠ .yield)
    (hOk : dispatchSyscallChecked ctx decoded tid executingCore st = .ok ((), st')) :
    ∃ tcb, st.getTcb? tid = some tcb ∧
        ∃ cap ref,
          lookupSlot tcb decoded.capAddr st = .ok ref ∧
          SystemState.lookupSlotCap st ref = some cap ∧
          cap.hasRight (syscallRequiredRight decoded.syscallId) = true := by
  simp only [dispatchSyscallChecked, SystemState.getObject?] at hOk
  -- The caller/core guard: a mismatched pair is refused before any lookup.
  split at hOk
  · exact absurd hOk (by simp)
  split at hOk
  next tcb hTcb =>
    refine ⟨tcb, (SystemState.getTcb?_eq_some_iff st tid tcb).mpr hTcb, ?_⟩
    split at hOk
    · simp at hOk
    next stPost hInvokeOk =>
      -- Every arm runs behind the typed gate, which checks the right after
      -- the type and before the arm.
      obtain ⟨cap, ref, hResolve, hSlot, hRight⟩ :=
        syscallInvokeTyped_requires_right decoded.syscallId _
          (dispatchWithCapChecked ctx decoded tid executingCore _) _ () stPost hInvokeOk
      exact ⟨cap, ref, hResolve, hSlot, hRight⟩
  · simp at hOk
  · simp at hOk

/-- **WS-RR RR7.3**: if the **flow-checked** syscall entry succeeds, the caller
held the required access right.  It also states that the register decode
succeeded on the caller's own register file, which subsumes the retired
entry's decode-validity theorem.

Three properties of the statement, all of them the point:

* the caller is identified on the **executing** core (`currentOnCore
  executingCore`), not on `bootCoreId`, so the guarantee covers a syscall issued
  from a secondary PE;
* the capability is resolved against the state the caller trapped in, which is
  the state the dispatcher is handed (the decode writes nothing) and the one
  user space could have arranged;
* the entry's own `isInsecureDefaultContext` refusal is part of the chain, so a
  success also witnesses that a deployment labeling context was installed. -/
theorem syscallEntryChecked_implies_capability_held
    (ctx : LabelingContext) (layout : SeLe4n.SyscallRegisterLayout)
    (executingCore : Concurrency.CoreId) (regCount : Nat)
    (st : SystemState) (st' : SystemState)
    (hOk : syscallEntryChecked ctx layout executingCore regCount st = .ok ((), st')) :
    isInsecureDefaultContext ctx = false ∧
    ∃ tid regs decoded,
      (st.scheduler.currentOnCore executingCore) = some tid ∧
      lookupThreadRegisterContext tid st = .ok (regs, st) ∧
      SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
        (threadOperationCode st tid layout regs)
        st tid layout regs regCount = .ok decoded ∧
      (decoded.syscallId ≠ .yield →
      ∃ tcb, st.getTcb? tid = some tcb ∧
          ∃ cap ref,
            lookupSlot tcb decoded.capAddr st = .ok ref ∧
            SystemState.lookupSlotCap st ref = some cap ∧
            cap.hasRight (syscallRequiredRight decoded.syscallId) = true) := by
  unfold syscallEntryChecked at hOk
  split at hOk
  · simp at hOk
  next hCtx =>
    simp only [Bool.not_eq_true] at hCtx
    refine ⟨hCtx, ?_⟩
    split at hOk
    · simp at hOk
    next tid hCurrent =>
      split at hOk
      · simp at hOk
      next regs _stRegs hLookup =>
        split at hOk
        · simp at hOk
        next decoded hDecode =>
          have hStEq : _stRegs = st := by
            unfold lookupThreadRegisterContext SystemState.getObject? at hLookup
            split at hLookup <;> simp at hLookup
            exact hLookup.2.symm
          subst hStEq
          exact ⟨tid, regs, decoded, hCurrent, hLookup, hDecode, fun hCap =>
            dispatchSyscallChecked_requires_right ctx decoded tid executingCore _ st' hCap hOk⟩

/-- **WS-SM SM9.A.10**: an unconfigured deployment cannot drain.

`LabelingContext.auditMonitorClearance` defaults to `none`, which denies every
caller, so the 256-entry cliff stays until an operator names a monitor.  That is
the conservative default and it is the operator's to know about — stated where a
reviewer of the dispatch would look for it. -/
theorem dispatchWithCapChecked_auditDrain_default_denied
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (args : Architecture.SyscallArgDecode.AuditDrainArgs) (st : SystemState)
    (hSyscall : decoded.syscallId = .auditDrain)
    {code : Nat} (hTarget : cap.target = .auditTrail code)
    (hRight : cap.hasRight gate.requiredRight = true)
    (hArgs : Architecture.SyscallArgDecode.decodeAuditDrainArgs decoded = .ok args)
    (hDefault : ctx.auditMonitorClearance = none) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .error .illegalAuthority := by
  rw [dispatchWithCapChecked_auditDrain_delegates ctx decoded tid executingCore gate cap args st
    hSyscall hTarget hRight hArgs,
    validatedAuditMonitorClearance_none ctx hDefault,
    auditDrain_unconfigured_denied (liftLegacyContext ctx) executingCore
      args.count st]

/-- **WS-SM SM9.A.10 (PR #870 round 2)**: an unconfigured deployment cannot
read — the `.auditRead` sibling of `dispatchWithCapChecked_auditDrain_default_denied`,
and the arm-level witness of the reviewer's exact scenario: a boot-provisioned
`.auditTrail` capability with the `.read` right, a well-formed operation, and no
configured monitor clearance.  The refusal comes from the transition's own
configuration gate (`auditRead_unconfigured_denied`), not from the capability
checks the capability was provisioned to pass. -/
theorem dispatchWithCapChecked_auditRead_default_denied
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (args : Architecture.SyscallArgDecode.AuditReadArgs) (op : AuditReadOp)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .auditRead)
    {code : Nat} (hTarget : cap.target = .auditTrail code)
    (hRight : cap.hasRight gate.requiredRight = true)
    (hArgs : Architecture.SyscallArgDecode.decodeAuditReadArgs decoded = .ok args)
    (hOp : decodeAuditReadOp args.opcode args.index args.chunk = some op)
    (hDefault : ctx.auditMonitorClearance = none) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .error .illegalAuthority := by
  rw [dispatchWithCapChecked_auditRead_delegates ctx decoded tid executingCore gate cap args op st
    hSyscall hTarget hRight hArgs hOp,
    validatedAuditMonitorClearance_none ctx hDefault,
    auditRead_unconfigured_denied (liftLegacyContext ctx) executingCore
      op st]

/-- **WS-SM SM9.A.9 (PR #870 round 2, the universal half of the acceptance
witness)**: in an unconfigured deployment, **no capability whatsoever makes an
audit syscall succeed** — not an ordinary object capability (rejected by the
target gate), and not a boot-provisioned full-rights `.auditTrail` capability
either (the transition's configuration gate refuses the read, the monitor gate
refuses the drain).  Capability provisioning is an axis the labeling context
cannot see, so a claim quantified over a *particular* capability shape would be
silent about exactly the deployment that provisions one; this one is quantified
over the capability. -/
theorem unconfiguredDeployment_audit_never_succeeds
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (st st' : SystemState)
    (hSyscall : decoded.syscallId = .auditRead ∨ decoded.syscallId = .auditDrain)
    (hNoMonitor : ctx.auditMonitorClearance = none) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st ≠ .ok ((), st') := by
  intro hOk
  unfold dispatchWithCapChecked dispatchCapabilityOnly at hOk
  rcases hSyscall with h | h <;> rw [h, validatedAuditMonitorClearance_none ctx hNoMonitor] at hOk
  · simp only [auditRead_unconfigured_denied] at hOk
    split at hOk
    · exact absurd hOk (by simp)
    · split at hOk
      · split at hOk
        · exact absurd hOk (by simp)
        · split at hOk
          · exact absurd hOk (by simp)
          · exact absurd hOk (by simp)
      · exact absurd hOk (by simp)
  · simp only [auditDrain_unconfigured_denied] at hOk
    split at hOk
    · exact absurd hOk (by simp)
    · split at hOk
      · split at hOk
        · exact absurd hOk (by simp)
        · exact absurd hOk (by simp)
      · exact absurd hOk (by simp)

/-- **WS-SM SM9.A.9 (the acceptance witness): an unconfigured deployment has no
audit reader at all.**

Five facts, in one place, because "no audit reader by default" is a claim about
their conjunction rather than about any one of them — and every one of the five
is a **conjunct**, not a citation, so none can drift out from under the claim:

1. with **any** capability — including a boot-provisioned full-rights audit
   capability, the shape capability provisioning can install without the
   labeling context's knowledge — **neither audit syscall can succeed**: the
   read is refused by the transition's own configuration gate
   (`auditRead_unconfigured_denied`), the drain by the monitor gate (PR #870
   round 2; before it, this claim was silent about provisioned capabilities
   and false of them);
2. an ordinary capability — the shape every thread holds to its own TCB — is
   **rejected** on both audit syscalls with `.invalidCapability`, so the reader
   is not reachable by right alone (the v0.32.97 confused-deputy class);
3. audit authority cannot be **forged** by minting — the kernel's capability
   derivation path preserves targets — so a deployment holds an audit
   capability exactly where its boot/CSpace layer put one (discharged by
   `mintDerivedCap_no_audit_forgery`, whose home is the mint);
4. with no configured monitor clearance nothing may **drain**, so the trail
   cannot be emptied by a caller that merely holds a capability; and
5. a read-only audit capability provably lacks the drain's right, so a
   monitoring deployment can hand out a reader that cannot remove evidence.

Stated over the *checked* dispatch, since that is the only path the audit
syscalls have. -/
theorem unconfiguredDeployment_has_no_audit_reader
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (oid : SeLe4n.ObjId) (c : Concurrency.CoreId) (count : Nat)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .auditRead ∨ decoded.syscallId = .auditDrain)
    (hNoMonitor : ctx.auditMonitorClearance = none) :
    (∀ (anyCap : Capability) (st' : SystemState),
      dispatchWithCapChecked ctx decoded tid executingCore gate anyCap st ≠ .ok ((), st')) ∧
    dispatchWithCapChecked ctx decoded tid executingCore gate
        { target := .object oid, rights := AccessRightSet.ofList AccessRight.all, } st = .error (.invalidCapability 0) ∧
    (∀ (parent : NonNullCap) (rights : AccessRightSet) (kind : CapDataKind)
        (badge : Option SeLe4n.Badge) (child : Capability) (code : Nat),
      mintDerivedCap parent rights kind badge = .ok child → child.target = .auditTrail code →
        parent.val.target = .auditTrail code) ∧
    auditDrainVisiblePrefix (liftLegacyContext ctx) (validatedAuditMonitorClearance ctx)
        c count st =
      .error .illegalAuthority ∧
    Capability.auditTrailRead.hasRight .write = false := by
  refine ⟨fun anyCap st' =>
      unconfiguredDeployment_audit_never_succeeds ctx decoded tid executingCore gate anyCap st st'
        hSyscall hNoMonitor,
    dispatchWithCapChecked_audit_rejects_non_audit_capability ctx decoded tid executingCore gate _ oid st
      hSyscall rfl,
    fun parent rights kind badge child _ hMint hChild =>
      mintDerivedCap_no_audit_forgery parent rights kind badge child hMint hChild,
    ?_, Capability.auditTrailRead_cannot_drain.2⟩
  rw [validatedAuditMonitorClearance_none ctx hNoMonitor]
  exact auditDrain_unconfigured_denied (liftLegacyContext ctx) c count st

/-- **The live `.tcbSuspend` arm routes to `suspendThreadOnCore`.**  Capability-only,
and `dispatchWithCapChecked` consults `dispatchCapabilityOnly` first. -/
theorem dispatchWithCapChecked_tcbSuspend_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId) (vtid : SeLe4n.ValidThreadId)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .tcbSuspend)
    (hTarget : cap.target = .object objId)
    (hDecode : ∃ a, Architecture.SyscallArgDecode.decodeSuspendArgs decoded = .ok a)
    (hValid : validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vtid) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      (match Lifecycle.Suspend.suspendThreadOnCore st vtid
              executingCore with
       | .ok (st', _) => .ok ((), st')
       | .error e => .error e) := by
  obtain ⟨a, hD⟩ := hDecode
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchCapabilityOnlyChecked, hSyscall, hTarget, hD, hValid]

/-- WS-ZA ZA5.4 part 22: **the live `.tcbSetSpace` arm is the space change** at
the invoking thread's executing core, on the thread the capability names and the
two roots resolved through the caller's CSpace (`resolveSetSpace`).  It takes
the core for the retire of what each slot's old capability took with it. -/
theorem dispatchWithCapChecked_tcbSetSpace_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.SetSpaceArgs) (vtid : SeLe4n.ValidThreadId)
    (cnSrc vrSrc fhSrc : CSpaceAddr) (st : SystemState)
    (hSyscall : decoded.syscallId = .tcbSetSpace)
    (hTarget : cap.target = .object objId)
    (hDecode : Architecture.SyscallArgDecode.decodeSetSpaceArgs decoded = .ok args)
    (hValid : validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vtid)
    (hResolve : resolveSetSpace tid decoded.msgInfo.extraCaps args st = .ok (cnSrc, vrSrc, fhSrc)) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      (match copyThreadSpacesZombie executingCore st vtid cnSrc vrSrc args.cspaceRootData fhSrc with
       | .ok st' => .ok ((), st')
       | .error e => .error e) := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchCapabilityOnlyChecked, hSyscall, hTarget, hDecode, hValid, hResolve]

/-- WS-SX SX6.6: **the live `.tcbSetIPCBuffer` arm routes to `setIPCBufferOp`**
with the buffer's frame capability as extra capability 0. -/
theorem dispatchWithCapChecked_tcbSetIPCBuffer_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.SetIPCBufferArgs) (vtid : SeLe4n.ValidThreadId)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .tcbSetIPCBuffer)
    (hTarget : cap.target = .object objId)
    (hDecode : Architecture.SyscallArgDecode.decodeSetIPCBufferArgs decoded = .ok args)
    (hValid : validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vtid) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      (match Architecture.IpcBufferValidation.setIPCBufferOp executingCore st vtid tid
          (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0) args.bufferAddr with
       | .ok st' => .ok ((), st')
       | .error e => .error e) := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchCapabilityOnlyChecked, hSyscall, hTarget, hDecode, hValid]

/-- **The live `.tcbResume` arm routes to `resumeThreadOnCore`.**

Round 10 of the PR #861 review found this arm still calling the boot-pinned
`resumeThread`, which enqueues on `bootCoreId` regardless of the target's
`cpuAffinity` — so resuming a thread homed on a secondary core put it on the
wrong run queue.  The reroute is the fix; this theorem is what stops the
inventory claiming the arm is covered while it points somewhere else. -/
theorem dispatchWithCapChecked_tcbResume_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId) (vtid : SeLe4n.ValidThreadId)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .tcbResume)
    (hTarget : cap.target = .object objId)
    (hDecode : ∃ a, Architecture.SyscallArgDecode.decodeResumeArgs decoded = .ok a)
    (hValid : validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vtid) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      (match Lifecycle.Suspend.restartThreadOnCore st vtid executingCore with
       | .ok (st', _) => .ok ((), st')
       | .error e => .error e) := by
  obtain ⟨a, hD⟩ := hDecode
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchCapabilityOnlyChecked, hSyscall, hTarget, hD, hValid]

/-- **The live `.receive` arm routes to `endpointReceiveDualOnCore`.**

Round 8 of the PR #861 review classified this transition a below-API "leg" of
`endpointReplyRecvOnCore`.  It is that — and it is also what the checked `.receive` arm
calls directly, once its own `endpoint→receiver` gate has passed.  A theorem
saying so is the thing that was missing: with it, the misclassification is a
broken citation rather than a prose disagreement between two tables. -/
theorem dispatchWithCapChecked_receive_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (epId : SeLe4n.ObjId)
    (replyIdOpt : Option SeLe4n.ReplyId) (st st0 : SystemState)
    -- WS-SX SX4: `st` is the state the receive runs on, its busy reply's holder
    -- cancelled from the state `st0` the arm is handed.
    (hCancel : cancelRecvBusyReply ctx tid gate decoded executingCore st0 = st)
    (hSyscall : decoded.syscallId = .receive)
    (hTarget : cap.target = .object epId)
    (hFlow : securityFlowsTo (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = true)
    -- WS-SM SM8.C: the arm's gate is the global check AND the endpoint override.
    (hOverride : endpointOverrideAllows ctx epId (ctx.endpointLabelOf epId)
      (ctx.threadLabelOf tid) = true)
    (hReply : resolveRecvReplyId gate decoded st = .ok replyIdOpt) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st0 =
      -- seL4-MCS `receiveIPC`: an active bound notification is completed.
      if receiveCompletesSignal ctx st tid then
        completeSignalArm ctx tid (receiverBoundNotification st tid) executingCore st else
      -- WS-SX SX7.2: `NBRecv` with no sender waiting returns at once.
      if receiveFindsNothing (Syscall.wordReceiveBlocks (callerSyscallWord st tid)) st epId then .ok ((), Architecture.nbRecvFailedTransfer st tid) else
      -- PR #873 round 6: the arm routes through the WithCaps per-core receive, so
      -- a send that parked before its receiver arrived delivers its capabilities
      -- too, and the staged `extraCaps` is the summary's installed count.
      -- WS-OD OD3.6: including the rendezvous donation, which the checked arm
      -- performs with the *same* definition at the dequeued caller's lend
      -- admission -- the delegation claim is about the whole arm, so it names
      -- every step of it.
      -- WS-SX SX8.2: seL4-MCS's `maybeReturnSchedContext` first, on a blocking
      -- receive with a bound notification.
      (match endpointReceiveDualWithCapsOnCore epId tid replyIdOpt executingCore
          (receiveReturnSchedContext (Syscall.wordReceiveBlocks (callerSyscallWord st tid)) st tid)
          with
       | (st', .ok (dequeued, summary, _)) =>
           (match applyReceiveRendezvousHandoff st' tid dequeued
                    executingCore (receiveLendAdmits ctx st epId) with
            | .error e => .error e
            | .ok stDon =>
                .ok ((), Architecture.stageDeliveredMessage
                          stDon tid
                          summary.capInfo))
       | (_, .error e) => .error e) := by
  by_cases hS : receiveCompletesSignal ctx st tid = true
  · subst hCancel
    simp [dispatchWithCapChecked, dispatchCapabilityOnly, receiveResolvedArm, hSyscall, hTarget,
      endpointFlowGate_of ctx epId _ _ hFlow hOverride, hReply, hS]
  by_cases hN : receiveFindsNothing (Syscall.wordReceiveBlocks (callerSyscallWord st tid)) st epId = true
  · subst hCancel
    simp [dispatchWithCapChecked, dispatchCapabilityOnly, receiveResolvedArm, hSyscall, hTarget,
      endpointFlowGate_of ctx epId _ _ hFlow hOverride, hReply, hS, hN]
  · subst hCancel
    simp [dispatchWithCapChecked, dispatchCapabilityOnly, receiveResolvedArm, hSyscall, hTarget,
      endpointFlowGate_of ctx epId _ _ hFlow hOverride, hReply, hS, hN]

/-- **The live checked `.send` arm routes to `endpointSendCrossCoreDispatchChecked`.**
The checked mirror of `dispatchWithCap_send_delegates`; the gate is inside the
cross-core operation (the `sender → endpoint` flow check), exactly as
`endpointSendDualChecked` carried it before the reroute. -/
theorem dispatchWithCapChecked_send_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (epId : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .send)
    (hTarget : cap.target = .object epId) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      -- WS-SX SX7.2: `NBSend` with no receiver waiting drops the message.
      if sendDropsMessage ctx (Syscall.wordSendBlocks (callerSyscallWord st tid)) st tid epId then .ok ((), st) else
      (match endpointSendCrossCoreDispatchChecked ctx epId tid (.frame cap.badge (cap.rights.mem .grant) (cap.rights.mem .grantReply))
              executingCore st with
       | (_, .error e) => .error e
       | (st', .ok (summary, _)) =>
           match clearWokenReceiverStash ((st.getEndpoint? epId).bind (·.receiveQ.head)) st' with
           | .error e => .error e
           | .ok ((), st'') =>
               .ok ((), Architecture.stageWokenDelivery st''
                         ((st.getEndpoint? epId).bind (·.receiveQ.head))
                         summary.capInfo)) := by
  by_cases hD : sendDropsMessage ctx (Syscall.wordSendBlocks (callerSyscallWord st tid)) st tid epId = true
  · simp [dispatchWithCapChecked, dispatchCapabilityOnly, hSyscall, hTarget, hD]
  · simp [dispatchWithCapChecked, dispatchCapabilityOnly, hSyscall, hTarget, hD]

/-- **The live `.tcbSetPriority` arm routes to `setPriorityOnCore`.**

Round 12 of the PR #861 review found this arm still calling `setPriorityOp`,
which is boot-pinned twice: `migrateRunQueueBucket` tests membership in
`runQueueOnCore bootCoreId` — so for a target queued on any other core the
re-bucket is a silent no-op and the run queue keeps the *old* priority band —
and the preemption check reads `currentOnCore bootCoreId`. -/
theorem dispatchWithCapChecked_tcbSetPriority_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId) (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
    (args : Architecture.SyscallArgDecode.SetPriorityArgs) (st : SystemState)
    (hSyscall : decoded.syscallId = .tcbSetPriority)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeSetPriorityArgs decoded = .ok args)
    (hCaller : resolvePriorityAuthority st tid
      (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0) = .ok vCallerTid)
    (hValid : validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vTargetTid) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      (match SchedContext.PriorityManagement.setPriorityOnCore st vCallerTid vTargetTid
              (SeLe4n.Priority.ofNat args.newPriority) executingCore with
       | .ok (st', _) => .ok ((), st')
       | .error e => .error e) := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchCapabilityOnlyChecked, hSyscall, hTarget, hDecode, hCaller, hValid]

/-- **The live `.schedContextUnbind` arm routes to `schedContextUnbindAllOnCore`**,
seL4-MCS's `SchedContext_Unbind`: the current thread's context refused, then the
per-core thread unbind and the notification unbind.

Round 15 of the PR #861 review found the arm calling the single-core
`schedContextUnbind`, whose cleared `current` slot no scheduling point followed,
so a thread that unbound its own context kept running on a core the model
recorded as idle (`vacatedCore_next_syscall_rejected`).  seL4 refuses that
invocation, and so does this arm; a thread running on a remote core is
rescheduled there through the per-core form's `.reschedule` SGI. -/
theorem dispatchWithCapChecked_schedContextUnbind_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (scId : SeLe4n.ObjId) (vScId : SeLe4n.ValidObjId)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .schedContextUnbind)
    (hTarget : cap.target = .object scId)
    (hDecode : ∃ a, decodeSchedContextUnbindArgs decoded = .ok a)
    (hValid : validateObjIdArg scId = .ok vScId) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      (match SchedContextOps.schedContextUnbindAllOnCore vScId
              executingCore st with
       | .ok (st', _) => .ok ((), st')
       | .error e => .error e) := by
  obtain ⟨a, hArgs⟩ := hDecode
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchCapabilityOnlyChecked, hSyscall, hTarget, hArgs, hValid]

/-- **The live `.tcbSetMCPriority` arm routes to `setMCPriorityOnCore`.**  Same
reroute, reached whenever the new ceiling caps the target's current priority. -/
theorem dispatchWithCapChecked_tcbSetMCPriority_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId) (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
    (args : Architecture.SyscallArgDecode.SetMCPriorityArgs) (st : SystemState)
    (hSyscall : decoded.syscallId = .tcbSetMCPriority)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeSetMCPriorityArgs decoded = .ok args)
    (hCaller : resolvePriorityAuthority st tid
      (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0) = .ok vCallerTid)
    (hValid : validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vTargetTid) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      (match SchedContext.PriorityManagement.setMCPriorityOnCore st vCallerTid vTargetTid
              (SeLe4n.Priority.ofNat args.newMCP) executingCore with
       | .ok (st', _) => .ok ((), st')
       | .error e => .error e) := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchCapabilityOnlyChecked, hSyscall, hTarget, hDecode, hCaller, hValid]

/-- **The delegation obligation for a syscall, as a proposition indexed by it.**

PR #861 review round 11: the first cut of this mechanism recorded delegation
evidence as a `String` validated by `niName!`.  That checks only that *some*
declaration by that name exists — the `.receive` entry could have cited
`dispatchWithCapChecked_tcbSuspend_delegates` and every count would still have passed.
It was the same defect the mechanism existed to prevent, one level up: a claim
("this theorem backs this arm") held by prose rather than by a type.

Here the obligation is a `Prop` computed *from the syscall*, so a proof of it
cannot be borrowed from another arm — `syscallDelegates .receive` and
`syscallDelegates .tcbSuspend` are different propositions.  Arms with no
delegation theorem yet map to `False`, which is deliberate: evidence for them
cannot be fabricated, so the inventory's backed/unbacked split is enforced by
the type checker rather than by a `Bool` someone can flip. -/
def syscallDelegates : SyscallId → Prop
  | .send =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (epId : SeLe4n.ObjId) (st : SystemState),
        decoded.syscallId = .send →
        cap.target = .object epId →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
          -- WS-SX SX7.2: `NBSend` with no receiver waiting drops the message.
          if sendDropsMessage ctx (Syscall.wordSendBlocks (callerSyscallWord st tid)) st tid epId then .ok ((), st) else
          (match endpointSendCrossCoreDispatchChecked ctx epId tid
                  (.frame cap.badge (cap.rights.mem .grant) (cap.rights.mem .grantReply)) executingCore st with
           | (_, .error e) => .error e
           | (st', .ok (summary, _)) =>
               match clearWokenReceiverStash ((st.getEndpoint? epId).bind (·.receiveQ.head)) st' with
               | .error e => .error e
               | .ok ((), st'') =>
                   .ok ((), Architecture.stageWokenDelivery st''
                             ((st.getEndpoint? epId).bind (·.receiveQ.head))
                             summary.capInfo))
  | .tcbSetPriority =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (objId : SeLe4n.ObjId)
        (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
        (args : Architecture.SyscallArgDecode.SetPriorityArgs) (st : SystemState),
        decoded.syscallId = .tcbSetPriority →
        cap.target = .object objId →
        decodeSetPriorityArgs decoded = .ok args →
        resolvePriorityAuthority st tid
          (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0) = .ok vCallerTid →
        validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vTargetTid →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
          (match SchedContext.PriorityManagement.setPriorityOnCore st vCallerTid vTargetTid
                  (SeLe4n.Priority.ofNat args.newPriority) executingCore with
           | .ok (st', _) => .ok ((), st')
           | .error e => .error e)
  | .tcbSetMCPriority =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (objId : SeLe4n.ObjId)
        (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
        (args : Architecture.SyscallArgDecode.SetMCPriorityArgs) (st : SystemState),
        decoded.syscallId = .tcbSetMCPriority →
        cap.target = .object objId →
        decodeSetMCPriorityArgs decoded = .ok args →
        resolvePriorityAuthority st tid
          (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0) = .ok vCallerTid →
        validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vTargetTid →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
          (match SchedContext.PriorityManagement.setMCPriorityOnCore st vCallerTid vTargetTid
                  (SeLe4n.Priority.ofNat args.newMCP) executingCore with
           | .ok (st', _) => .ok ((), st')
           | .error e => .error e)
  | .receive =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
        (gate : SyscallGate) (cap : Capability) (epId : SeLe4n.ObjId)
        (replyIdOpt : Option SeLe4n.ReplyId) (st st0 : SystemState),
        -- WS-SX SX4: the receive runs on `st`, the state `st0` the arm is handed
        -- with its busy reply's holder cancelled.
        cancelRecvBusyReply ctx tid gate decoded executingCore st0 = st →
        decoded.syscallId = .receive →
        cap.target = .object epId →
        securityFlowsTo (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = true →
        -- WS-SM SM8.C: the arm's gate is the global lattice check AND this
        -- endpoint's configured override, so the obligation carries both.
        endpointOverrideAllows ctx epId (ctx.endpointLabelOf epId)
          (ctx.threadLabelOf tid) = true →
        resolveRecvReplyId gate decoded st = .ok replyIdOpt →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st0 =
          -- seL4-MCS `receiveIPC`: an active bound notification is completed.
          if receiveCompletesSignal ctx st tid then
            completeSignalArm ctx tid (receiverBoundNotification st tid) executingCore st else
          -- WS-SX SX7.2: `NBRecv` with no sender waiting returns at once.
          if receiveFindsNothing (Syscall.wordReceiveBlocks (callerSyscallWord st tid)) st epId then .ok ((), Architecture.nbRecvFailedTransfer st tid) else
          -- WS-SX SX8.2: seL4-MCS's `maybeReturnSchedContext` first.
          (match endpointReceiveDualWithCapsOnCore epId tid replyIdOpt executingCore
              (receiveReturnSchedContext (Syscall.wordReceiveBlocks (callerSyscallWord st tid)) st tid)
              with
           -- WS-RA RA.B.6: the arm stages the non-blocking consume's delivery
           -- into the caller's return frame.  PR #873 round 6: with the receive
           -- routed through the WithCaps transition, the staged `extraCaps` is
           -- the transfer summary's installed count rather than a hardcoded 0.
           -- WS-OD OD3.6: and the rendezvous donation runs between them, in the
           -- checked arm as in the unchecked one, at the dequeued caller's lend
           -- admission.  The obligation names it: a delegation claim that omitted
           -- a step would be a claim about a different program.
           | (st', .ok (dequeued, summary, _)) =>
               (match applyReceiveRendezvousHandoff st' tid dequeued
                        executingCore (receiveLendAdmits ctx st epId) with
                | .error e => .error e
                | .ok stDon =>
                    .ok ((), Architecture.stageDeliveredMessage
                              stDon tid
                              summary.capInfo))
           | (_, .error e) => .error e)
  | .tcbSuspend =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (objId : SeLe4n.ObjId) (vtid : SeLe4n.ValidThreadId)
        (st : SystemState),
        decoded.syscallId = .tcbSuspend →
        cap.target = .object objId →
        (∃ a, Architecture.SyscallArgDecode.decodeSuspendArgs decoded = .ok a) →
        validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vtid →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
          (match Lifecycle.Suspend.suspendThreadOnCore st vtid
                  executingCore with
           | .ok (st', _) => .ok ((), st')
           | .error e => .error e)
  | .tcbResume =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (objId : SeLe4n.ObjId) (vtid : SeLe4n.ValidThreadId)
        (st : SystemState),
        decoded.syscallId = .tcbResume →
        cap.target = .object objId →
        (∃ a, Architecture.SyscallArgDecode.decodeResumeArgs decoded = .ok a) →
        validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vtid →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
          (match Lifecycle.Suspend.restartThreadOnCore st vtid executingCore with
           | .ok (st', _) => .ok ((), st')
           | .error e => .error e)
  | .schedContextUnbind =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (scId : SeLe4n.ObjId) (vScId : SeLe4n.ValidObjId)
        (st : SystemState),
        decoded.syscallId = .schedContextUnbind →
        cap.target = .object scId →
        (∃ a, decodeSchedContextUnbindArgs decoded = .ok a) →
        validateObjIdArg scId = .ok vScId →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
          (match SchedContextOps.schedContextUnbindAllOnCore vScId
                  executingCore st with
           | .ok (st', _) => .ok ((), st')
           | .error e => .error e)
  | .vspaceMap =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (objId : SeLe4n.ObjId) (words : PageMapArgs) (rootCPtr : SeLe4n.CPtr)
        (rootId : SeLe4n.ObjId) (args : Architecture.SyscallArgDecode.VSpaceMapArgs)
        (st : SystemState),
        decoded.syscallId = .vspaceMap →
        cap.target = .object objId →
        decodePageMapArgs decoded = .ok words →
        callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0 = some rootCPtr →
        resolvePageMapOperands tid decoded.capAddr rootCPtr words st = .ok (rootId, args) →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st = vspaceMapOrRemapFromFrameCap tid executingCore args st
  | .vspaceUnmap =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (objId : SeLe4n.ObjId) (slot : CSpaceAddr) (slotCap : Capability)
        (slotObj : SeLe4n.ObjId) (st : SystemState),
        decoded.syscallId = .vspaceUnmap →
        cap.target = .object objId →
        resolveCallerCapSlot tid decoded.capAddr (syscallRequiredRight .vspaceUnmap) st =
          .ok (slot, slotCap, slotObj) →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
          vspaceUnmapFrameCap executingCore slot st
  -- Every other syscall: no delegation theorem exists yet.  `False` rather than
  -- `True` so the absence is unforgeable — an inventory entry claiming
  -- delegation evidence for one of these cannot be constructed.
  -- WS-SM SM8.C.9: the live `.declassify` arm.  Stated over the *checked*
  -- dispatch, like `.receive`, because that is the only path it has: the
  -- unchecked one fails closed (`dispatchWithCap_declassify_denied`).
  | .declassify =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
        (gate : SyscallGate) (cap : Capability) (code : Nat) (targetCap : Capability)
        (targetId : SeLe4n.ObjId) (st : SystemState),
        decoded.syscallId = .declassify →
        cap.target = .auditTrail code →
        resolveDeclassifyTarget tid decoded.msgInfo.extraCaps st = .ok (targetCap, targetId) →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
          declassifyObjectFromCore (liftLegacyContext ctx) ctx.declassificationPolicy
            executingCore targetId st
  -- WS-SM SM9.C.9: the live data-carrying declassification.  Checked dispatch
  -- only, like `.declassify` — and the conclusion names the *whole arm*, so an
  -- arm that ran anything after the transition would not satisfy this.
  | .declassifySignal =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
        (gate : SyscallGate) (cap : Capability) (code : Nat) (ntfnCap : Capability)
        (notifId : SeLe4n.ObjId) (st : SystemState),
        decoded.syscallId = .declassifySignal →
        cap.target = .auditTrail code →
        resolveDeclassifySignalTarget tid decoded.msgInfo.extraCaps st = .ok (ntfnCap, notifId) →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
          (match notificationSignalDeclassifiedCrossCoreDispatch (liftLegacyContext ctx)
                  ctx.declassificationPolicy notifId ntfnCap.signalBadge executingCore st with
           | (st', .ok _) =>
               .ok ((), st')
           | (_, .error e) => .error e)
  -- WS-SM SM9.A.10: the live audit arms.  Stated over the *checked* dispatch,
  -- like `.declassify`, because that is the only path they have — and the
  -- conclusion names the return-frame write, so an arm that computed the right
  -- word and failed to stage it would not satisfy this.
  | .auditRead =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
        (gate : SyscallGate) (cap : Capability)
        (args : Architecture.SyscallArgDecode.AuditReadArgs) (op : AuditReadOp)
        (st : SystemState) (code : Nat),
        decoded.syscallId = .auditRead →
        cap.target = .auditTrail code →
        cap.hasRight gate.requiredRight = true →
        Architecture.SyscallArgDecode.decodeAuditReadArgs decoded = .ok args →
        decodeAuditReadOp args.opcode args.index args.chunk = some op →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
          (match auditReadFromCore (liftLegacyContext ctx) (validatedAuditMonitorClearance ctx)
              executingCore op st with
           | .error e => .error e
           | .ok (w, st') =>
               .ok ((), Architecture.writeCallReturnWord st' tid w.toUInt64))
  | .auditDrain =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
        (gate : SyscallGate) (cap : Capability)
        (args : Architecture.SyscallArgDecode.AuditDrainArgs) (st : SystemState) (code : Nat),
        decoded.syscallId = .auditDrain →
        cap.target = .auditTrail code →
        cap.hasRight gate.requiredRight = true →
        Architecture.SyscallArgDecode.decodeAuditDrainArgs decoded = .ok args →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
          (match auditDrainVisiblePrefix (liftLegacyContext ctx)
              (validatedAuditMonitorClearance ctx)
              executingCore args.count st with
           | .error e => .error e
           | .ok (n, st') =>
               .ok ((), Architecture.writeCallReturnWord st' tid n.toUInt64))
  -- WS-ZA ZA5.4 part 14: the carve, the one way a kernel object is made.
  | .untypedRetype =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (untypedId : SeLe4n.ObjId) (st : SystemState),
        decoded.syscallId = .untypedRetype →
        cap.target = .object untypedId →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
          untypedRetypeFromCap tid executingCore decoded.capAddr
            (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0)
            (decodeUntypedRetypeArgs decoded) st
  -- WS-BP BP7.1 (`v0.36.7`): the two destroying arms.  Each names the finalising
  -- composite — the delete or the revocation, then the removal of every mapping a
  -- destroyed frame capability recorded — at the invoking thread's core.
  | .cspaceDelete =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (cnodeId : SeLe4n.ObjId)
        (args : Architecture.SyscallArgDecode.CSpaceDeleteArgs) (st : SystemState),
        decoded.syscallId = .cspaceDelete →
        cap.target = .object cnodeId →
        decodeCSpaceDeleteArgs decoded = .ok args →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
          if !cnodeInvoked cnodeId st then .error .objectNotFound else
            cspaceDeleteSlotZombie executingCore
              { cnode := cnodeId, slot := args.targetSlot } st
  | .cspaceRevoke =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (cnodeId : SeLe4n.ObjId)
        (args : Architecture.SyscallArgDecode.CSpaceDeleteArgs) (st : SystemState),
        decoded.syscallId = .cspaceRevoke →
        cap.target = .object cnodeId →
        decodeCSpaceDeleteArgs decoded = .ok args →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
          if !cnodeInvoked cnodeId st then .error .objectNotFound else
            cspaceRevokeCdtFinalising executingCore
              { cnode := cnodeId, slot := args.targetSlot } st
  -- WS-ZA ZA5.4 part 22: the space change, which retires what each slot's old
  -- capability took with it at the invoking thread's core.
  | .tcbSetSpace =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (objId : SeLe4n.ObjId)
        (args : Architecture.SyscallArgDecode.SetSpaceArgs) (vtid : SeLe4n.ValidThreadId)
        (cnSrc vrSrc fhSrc : CSpaceAddr) (st : SystemState),
        decoded.syscallId = .tcbSetSpace →
        cap.target = .object objId →
        Architecture.SyscallArgDecode.decodeSetSpaceArgs decoded = .ok args →
        validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vtid →
        resolveSetSpace tid decoded.msgInfo.extraCaps args st = .ok (cnSrc, vrSrc, fhSrc) →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
          (match copyThreadSpacesZombie executingCore st vtid cnSrc vrSrc args.cspaceRootData fhSrc with
           | .ok st' => .ok ((), st')
           | .error e => .error e)
  -- WS-SX SX6.6: the buffer change, which replaces the thread's buffer slot
  -- and retires what its old capability took with it at the invoking core.
  | .tcbSetIPCBuffer =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (objId : SeLe4n.ObjId)
        (args : Architecture.SyscallArgDecode.SetIPCBufferArgs) (vtid : SeLe4n.ValidThreadId)
        (st : SystemState),
        decoded.syscallId = .tcbSetIPCBuffer →
        cap.target = .object objId →
        Architecture.SyscallArgDecode.decodeSetIPCBufferArgs decoded = .ok args →
        validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vtid →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
          (match Architecture.IpcBufferValidation.setIPCBufferOp executingCore st vtid tid
              (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0) args.bufferAddr with
           | .ok st' => .ok ((), st')
           | .error e => .error e)
  -- WS-ZA ZA4.3: the capability-free yield.  The dispatcher runs it from the
  -- guard ahead of the caller's CSpace lookup, so the obligation is stated
  -- over the dispatcher itself: once the caller is current on the executing
  -- core, it IS the yield's own transition.
  | .yield =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
        (executingCore : Concurrency.CoreId) (st : SystemState),
        decoded.syscallId = .yield →
        st.scheduler.currentOnCore executingCore = some tid →
        dispatchSyscallChecked ctx decoded tid executingCore st = dispatchYield executingCore st
  -- WS-ZA ZA6.9: the Consumed arm IS the Consumed invocation of the context the
  -- capability names, on the executing core.
  | .schedContextConsumed =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
        (gate : SyscallGate) (cap : Capability) (scId : SeLe4n.ObjId) (vScId : SeLe4n.ValidObjId)
        (st : SystemState),
        decoded.syscallId = .schedContextConsumed →
        cap.target = .object scId →
        validateObjIdArg scId = .ok vScId →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
          (match schedContextConsumedOnCore (SeLe4n.SchedContextId.ofObjId vScId.val)
                  executingCore st with
           | .ok st' => .ok ((), st')
           | .error e => .error e)
  -- WS-ZA ZA6.29: the yieldTo arm IS the yieldTo invocation of the context the
  -- capability names, on the executing core.
  | .schedContextYieldTo =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
        (gate : SyscallGate) (cap : Capability) (scId : SeLe4n.ObjId) (vScId : SeLe4n.ValidObjId)
        (st : SystemState),
        decoded.syscallId = .schedContextYieldTo →
        cap.target = .object scId →
        validateObjIdArg scId = .ok vScId →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
          (match SchedContextOps.schedContextYieldToOnCore
                  (SeLe4n.SchedContextId.ofObjId vScId.val) executingCore st with
           | .ok st' => .ok ((), st')
           | .error e => .error e)
  -- WS-ZA ZA6.32: the acknowledge arm IS the acknowledge of the line the
  -- capability names.
  | .irqHandlerAck =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
        (gate : SyscallGate) (cap : Capability) (line : Nat),
        decoded.syscallId = .irqHandlerAck →
        cap.target = .irqHandler line →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap = Architecture.irqHandlerAck line
  -- WS-ZA ZA6.32: the issue arm IS the issue from the invoked interrupt-control
  -- capability's slot.
  | .irqControlGet =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
        (gate : SyscallGate) (cap : Capability) (code : Nat),
        decoded.syscallId = .irqControlGet →
        cap.target = .irqControl code →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap =
          fun st => irqControlGetFromCap tid decoded.capAddr
            (callerExtraCapAddr? st tid decoded.msgInfo.extraCaps 0)
            (decodeIrqControlGetArgs decoded) st
  -- WS-ZA ZA6.32: the bind arm IS the bind of the line the capability names.
  | .irqHandlerSetNotification =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
        (gate : SyscallGate) (cap : Capability) (line : Nat),
        decoded.syscallId = .irqHandlerSetNotification →
        cap.target = .irqHandler line →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap = fun st =>
          irqHandlerSetNotificationFromCap tid executingCore line
            (irqHandlerSetNotificationArgsOf st tid decoded.msgInfo.extraCaps) st
  -- WS-ZA ZA6.32: the clear arm IS the clear of the line the capability names.
  | .irqHandlerClear =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
        (gate : SyscallGate) (cap : Capability) (line : Nat),
        decoded.syscallId = .irqHandlerClear →
        cap.target = .irqHandler line →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap = irqHandlerClear executingCore line
  -- WS-SX SX8.3: the unbind-object arm IS the bind's reading of extra
  -- capability 0, then the notification or the thread unbind-object.
  | .schedContextUnbindObject =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
        (gate : SyscallGate) (cap : Capability) (scId : SeLe4n.ObjId),
        decoded.syscallId = .schedContextUnbindObject →
        cap.target = .object scId →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap = fun st =>
          match resolveSchedContextBindNotificationCode tid
              (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st with
          | k + 1 =>
            match validateObjIdArg scId with
            | .error e => .error e
            | .ok vScId => SchedContextOps.schedContextUnbindNotificationObject vScId ⟨k⟩ st
          | 0 =>
            match resolveSchedContextBindThread tid
                (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st with
            | .error e => .error e
            | .ok vThreadId =>
              match validateObjIdArg scId with
              | .error e => .error e
              | .ok vScId =>
                match SchedContextOps.schedContextUnbindThreadObjectOnCore vScId
                    vThreadId.val executingCore st with
                | .ok (st', _) => .ok ((), st')
                | .error e => .error e
  | _ => False

/-- WS-ZA ZA4.3: the `.yield` obligation, discharged. -/
theorem syscallDelegates_yield : syscallDelegates .yield := by
  intro ctx decoded tid executingCore st hSyscall hCur
  simp [dispatchSyscallChecked, hSyscall, hCur]

/-- WS-ZA ZA6.9: the `.schedContextConsumed` obligation, discharged. -/
theorem syscallDelegates_schedContextConsumed : syscallDelegates .schedContextConsumed := by
  intro ctx decoded tid executingCore gate cap scId vScId st hSyscall hTarget hValid
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchCapabilityOnlyChecked, hSyscall, hTarget, hValid]

/-- WS-ZA ZA6.29: the `.schedContextYieldTo` obligation, discharged. -/
theorem syscallDelegates_schedContextYieldTo : syscallDelegates .schedContextYieldTo := by
  intro ctx decoded tid executingCore gate cap scId vScId st hSyscall hTarget hValid
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchCapabilityOnlyChecked, hSyscall, hTarget, hValid]

/-- WS-SX SX8.3: the `.schedContextUnbindObject` obligation, discharged. -/
theorem syscallDelegates_schedContextUnbindObject : syscallDelegates .schedContextUnbindObject := by
  intro ctx decoded tid executingCore gate cap scId hSyscall hTarget
  funext st
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchCapabilityOnlyChecked, hSyscall, hTarget]

/-- WS-ZA ZA6.32: the `.irqHandlerAck` obligation, discharged. -/
theorem syscallDelegates_irqHandlerAck : syscallDelegates .irqHandlerAck := by
  intro ctx decoded tid executingCore gate cap line hSyscall hTarget
  funext st
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchCapabilityOnlyChecked, hSyscall, hTarget]

/-- WS-ZA ZA6.32: the `.irqControlGet` obligation, discharged. -/
theorem syscallDelegates_irqControlGet : syscallDelegates .irqControlGet := by
  intro ctx decoded tid executingCore gate cap code hSyscall hTarget
  funext st
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchCapabilityOnlyChecked, hSyscall, hTarget]

/-- WS-ZA ZA6.32: the `.irqHandlerSetNotification` obligation, discharged. -/
theorem syscallDelegates_irqHandlerSetNotification :
    syscallDelegates .irqHandlerSetNotification := by
  intro ctx decoded tid executingCore gate cap line hSyscall hTarget
  funext st
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchCapabilityOnlyChecked, hSyscall, hTarget]

/-- WS-ZA ZA6.32: the `.irqHandlerClear` obligation, discharged. -/
theorem syscallDelegates_irqHandlerClear : syscallDelegates .irqHandlerClear := by
  intro ctx decoded tid executingCore gate cap line hSyscall hTarget
  funext st
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, dispatchCapabilityOnlyChecked, hSyscall, hTarget]

/-- The `.receive` obligation, discharged. -/
theorem syscallDelegates_receive : syscallDelegates .receive := by
  intro ctx decoded tid executingCore gate cap epId replyIdOpt st st0 hCancel hSyscall hTarget hFlow
    hOverride hReply
  exact dispatchWithCapChecked_receive_delegates ctx decoded tid executingCore gate cap epId replyIdOpt st
    st0 hCancel hSyscall hTarget hFlow hOverride hReply

/-- The `.tcbResume` obligation, discharged. -/
theorem syscallDelegates_tcbResume : syscallDelegates .tcbResume := by
  intro ctx decoded tid executingCore gate cap objId vtid st hSyscall hTarget hDecode hValid
  exact dispatchWithCapChecked_tcbResume_delegates ctx decoded tid executingCore gate cap objId vtid st
    hSyscall hTarget hDecode hValid

/-- The `.tcbSuspend` obligation, discharged. -/
theorem syscallDelegates_tcbSuspend : syscallDelegates .tcbSuspend := by
  intro ctx decoded tid executingCore gate cap objId vtid st hSyscall hTarget hDecode hValid
  exact dispatchWithCapChecked_tcbSuspend_delegates ctx decoded tid executingCore gate cap objId vtid st
    hSyscall hTarget hDecode hValid

/-- WS-SM SM8.B: the `.vspaceMap` obligation, discharged. -/
theorem syscallDelegates_vspaceMap : syscallDelegates .vspaceMap := by
  intro ctx decoded tid executingCore gate cap objId words rootCPtr rootId args st hSyscall hTarget
    hDecode hRoot hOps
  exact dispatchWithCapChecked_vspaceMap_delegates ctx decoded tid executingCore gate cap objId
    words rootCPtr rootId args st hSyscall hTarget hDecode hRoot hOps

/-- WS-SM SM8.C.9: the `.declassify` obligation, discharged. -/
theorem syscallDelegates_declassify : syscallDelegates .declassify := by
  intro ctx decoded tid executingCore gate cap code targetCap targetId st hSyscall hTarget hRes
  exact dispatchWithCapChecked_declassify_delegates ctx decoded tid executingCore gate cap code
    targetCap targetId st hSyscall hTarget hRes

/-- WS-SM SM9.C.9: the `.declassifySignal` obligation, discharged. -/
theorem syscallDelegates_declassifySignal : syscallDelegates .declassifySignal := by
  intro ctx decoded tid executingCore gate cap code ntfnCap notifId st hSyscall hTarget hRes
  exact dispatchWithCapChecked_declassifySignal_delegates ctx decoded tid executingCore gate cap code
    ntfnCap notifId st hSyscall hTarget hRes

/-- WS-SM SM9.A.10: the `.auditRead` obligation, discharged. -/
theorem syscallDelegates_auditRead : syscallDelegates .auditRead := by
  intro ctx decoded tid executingCore gate cap args op st _ hSyscall hTarget hRight hArgs hOp
  exact dispatchWithCapChecked_auditRead_delegates ctx decoded tid executingCore gate cap args op st
    hSyscall hTarget hRight hArgs hOp

/-- WS-SM SM9.A.10: the `.auditDrain` obligation, discharged. -/
theorem syscallDelegates_auditDrain : syscallDelegates .auditDrain := by
  intro ctx decoded tid executingCore gate cap args st _ hSyscall hTarget hRight hArgs
  exact dispatchWithCapChecked_auditDrain_delegates ctx decoded tid executingCore gate cap args st
    hSyscall hTarget hRight hArgs

/-- WS-SM SM8.B: the `.vspaceUnmap` obligation, discharged. -/
theorem syscallDelegates_vspaceUnmap : syscallDelegates .vspaceUnmap := by
  intro ctx decoded tid executingCore gate cap objId slot slotCap slotObj st hSyscall hTarget hRes
  exact dispatchWithCapChecked_vspaceUnmap_delegates ctx decoded tid executingCore gate cap objId
    slot slotCap slotObj st hSyscall hTarget hRes

/-- WS-ZA ZA5.4 part 14: the `.untypedRetype` obligation, discharged — the
carve's cross-core inventory entry rests on it. -/
theorem syscallDelegates_untypedRetype : syscallDelegates .untypedRetype := by
  intro ctx decoded tid executingCore gate cap untypedId st hSyscall hTarget
  exact dispatchWithCapChecked_untypedRetype_delegates ctx decoded tid executingCore gate cap untypedId st
    hSyscall hTarget

/-- WS-BP BP7.1 (`v0.36.7`): the `.cspaceDelete` obligation, discharged. -/
theorem syscallDelegates_cspaceDelete : syscallDelegates .cspaceDelete := by
  intro ctx decoded tid executingCore gate cap cnodeId args st hSyscall hTarget hDecode
  exact dispatchWithCapChecked_cspaceDelete_delegates ctx decoded tid executingCore gate cap cnodeId args st
    hSyscall hTarget hDecode

/-- WS-BP BP7.1 (`v0.36.7`): the `.cspaceRevoke` obligation, discharged. -/
theorem syscallDelegates_cspaceRevoke : syscallDelegates .cspaceRevoke := by
  intro ctx decoded tid executingCore gate cap cnodeId args st hSyscall hTarget hDecode
  exact dispatchWithCapChecked_cspaceRevoke_delegates ctx decoded tid executingCore gate cap cnodeId args st
    hSyscall hTarget hDecode

/-- WS-ZA ZA5.4 part 22: the `.tcbSetSpace` obligation, discharged — the space
change's cross-core inventory entry rests on it. -/
theorem syscallDelegates_tcbSetSpace : syscallDelegates .tcbSetSpace := by
  intro ctx decoded tid executingCore gate cap objId args vtid cnSrc vrSrc fhSrc st hSyscall hTarget hDecode
    hValid hResolve
  exact dispatchWithCapChecked_tcbSetSpace_delegates ctx decoded tid executingCore gate cap objId args vtid
    cnSrc vrSrc fhSrc st hSyscall hTarget hDecode hValid hResolve

/-- WS-SX SX6.6: the `.tcbSetIPCBuffer` obligation, discharged — the buffer
change's cross-core inventory entry rests on it. -/
theorem syscallDelegates_tcbSetIPCBuffer : syscallDelegates .tcbSetIPCBuffer := by
  intro ctx decoded tid executingCore gate cap objId args vtid st hSyscall hTarget hDecode hValid
  exact dispatchWithCapChecked_tcbSetIPCBuffer_delegates ctx decoded tid executingCore gate cap objId args vtid
    st hSyscall hTarget hDecode hValid

/-- The `.send` obligation, discharged. -/
theorem syscallDelegates_send : syscallDelegates .send := by
  intro ctx decoded tid executingCore gate cap epId st hSyscall hTarget
  exact dispatchWithCapChecked_send_delegates ctx decoded tid executingCore gate cap epId st hSyscall hTarget

/-- The `.tcbSetPriority` obligation, discharged. -/
theorem syscallDelegates_tcbSetPriority : syscallDelegates .tcbSetPriority := by
  intro ctx decoded tid executingCore gate cap objId vCallerTid vTargetTid args st hSyscall hTarget hDecode
    hCaller hValid
  exact dispatchWithCapChecked_tcbSetPriority_delegates ctx decoded tid executingCore gate cap objId vCallerTid
    vTargetTid args st hSyscall hTarget hDecode hCaller hValid

/-- The `.tcbSetMCPriority` obligation, discharged. -/
theorem syscallDelegates_tcbSetMCPriority : syscallDelegates .tcbSetMCPriority := by
  intro ctx decoded tid executingCore gate cap objId vCallerTid vTargetTid args st hSyscall hTarget hDecode
    hCaller hValid
  exact dispatchWithCapChecked_tcbSetMCPriority_delegates ctx decoded tid executingCore gate cap objId vCallerTid
    vTargetTid args st hSyscall hTarget hDecode hCaller hValid

/-- The `.schedContextUnbind` obligation, discharged. -/
theorem syscallDelegates_schedContextUnbind : syscallDelegates .schedContextUnbind := by
  intro ctx decoded tid executingCore gate cap scId vScId st hSyscall hTarget hDecode hValid
  exact dispatchWithCapChecked_schedContextUnbind_delegates ctx decoded tid executingCore gate cap scId vScId st
    hSyscall hTarget hDecode hValid

/-- **`v0.35.204`: the bind arm IS the resolved bind.**  Under a SchedContext
capability and a thread the caller's CSpace resolves extra capability 0 to, the
arm's answer is
`schedContextBind` of exactly that pair — so what the arm binds is what
`resolveSchedContextBindThread_ok_authorised` says the caller holds a writable
TCB capability to.  Stated at the state, because the resolver reads it. -/
theorem dispatchCapabilityOnly_schedContextBind_eq
    (decoded : SyscallDecodeResult) (cap : Capability) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (st : SystemState) (scId : SeLe4n.ObjId) (vScId : SeLe4n.ValidObjId)
    (vThreadId : SeLe4n.ValidThreadId)
    (hSyscall : decoded.syscallId = .schedContextBind)
    (hTarget : cap.target = .object scId)
    (hRes : resolveSchedContextBindThread tid (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st =
      .ok vThreadId)
    (hSc : validateObjIdArg scId = .ok vScId) :
    (dispatchCapabilityOnly decoded cap tid executingCore).map (fun f => f st)
      = some (SchedContextOps.schedContextBind vScId vThreadId st) := by
  unfold dispatchCapabilityOnly
  rw [hSyscall, hTarget]
  simp only [Option.map_some, resolveSchedContextBindNotificationCode_eq_zero_of_thread hRes, hRes,
    hSc]

/-- **The bind arm on a notification capability IS the notification bind**
(seL4-MCS's `decodeSchedContext_Bind`, `cap_notification_cap`): under a
SchedContext capability and extra capability 0 resolving to notification `n`,
the arm's answer is `schedContextBindNotification` of the context and `n`. -/
theorem dispatchCapabilityOnly_schedContextBind_notification_eq
    (decoded : SyscallDecodeResult) (cap : Capability) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (st : SystemState) (scId : SeLe4n.ObjId) (vScId : SeLe4n.ValidObjId) (k : Nat)
    (hSyscall : decoded.syscallId = .schedContextBind)
    (hTarget : cap.target = .object scId)
    (hN : resolveSchedContextBindNotificationCode tid
      (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st = k + 1)
    (hSc : validateObjIdArg scId = .ok vScId) :
    (dispatchCapabilityOnly decoded cap tid executingCore).map (fun f => f st)
      = some (schedContextBindNotification vScId ⟨k⟩ st) := by
  unfold dispatchCapabilityOnly
  rw [hSyscall, hTarget]
  simp only [Option.map_some, hN, hSc]

/-- **`v0.35.204`**: the dispatch-level consequence of the resolver's refusal —
a `.schedContextBind` whose extra capability 0 is no notification capability
(a notification capability is the notification bind's,
`dispatchCapabilityOnly_schedContextBind_notification_eq`) and whose TCB
capability the resolver refuses commits nothing and answers that refusal,
whatever SchedContext capability the caller holds.
With `resolveSchedContextBindThread_refuses_idle_capability` this is the successor
of PR #889 review round 11's `dispatchCapabilityOnly_schedContextBind_idle_operand_refused`:
the idle TCB is unreachable through the bind because the chokepoint refuses the
capability, not because a raw operand was checked at its lift point. -/
theorem dispatchCapabilityOnly_schedContextBind_idle_capability_refused
    (decoded : SyscallDecodeResult) (cap : Capability) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (st : SystemState) (scId : SeLe4n.ObjId) (e : KernelError)
    (hSyscall : decoded.syscallId = .schedContextBind)
    (hTarget : cap.target = .object scId)
    (hN : resolveSchedContextBindNotificationCode tid
      (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st = 0)
    (hRes : resolveSchedContextBindThread tid (schedContextBindArgsOf st tid decoded.msgInfo.extraCaps) st = .error e) :
    (dispatchCapabilityOnly decoded cap tid executingCore).map (fun f => f st) = some (.error e) := by
  unfold dispatchCapabilityOnly
  rw [hSyscall, hTarget]
  simp only [Option.map_some, hN, hRes]

end SeLe4n.Kernel
