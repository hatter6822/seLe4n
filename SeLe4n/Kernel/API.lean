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
import SeLe4n.Kernel.Architecture.SyscallArgDecode

import SeLe4n.Kernel.SchedContext.Operations
import SeLe4n.Kernel.SchedContext.SchedControl
import SeLe4n.Kernel.Lifecycle.Suspend
import SeLe4n.Kernel.SchedContext.PriorityManagement
import SeLe4n.Kernel.SchedContext.PriorityManagementPerCore
import SeLe4n.Kernel.SchedContext.OperationsPerCore
import SeLe4n.Kernel.IPC.Operations.Donation
import SeLe4n.Kernel.IPC.Invariant.DispatchArmPreservation
import SeLe4n.Kernel.IPC.Invariant.YieldPreservation
import SeLe4n.Kernel.SchedContext.BindingAffinity

import SeLe4n.Kernel.Architecture.Adapter
import SeLe4n.Kernel.Architecture.Invariant
import SeLe4n.Kernel.Architecture.VSpace
import SeLe4n.Kernel.Architecture.VSpaceInvariant
import SeLe4n.Kernel.Architecture.IpcBufferValidation
-- WS-SM SM7.F.4: the per-core-TLB-aware VSpace shootdown wrappers the live
-- `.vspaceMap` / `.vspaceUnmap` arms dispatch through (initiator-atomic
-- `perCoreTlb` retirement + translation-walk fill; projection-invisible).
import SeLe4n.Kernel.Architecture.PerCoreTlbModel
import SeLe4n.Kernel.Architecture.IpcBufferTlbFill

/-!
# L-01/WS-E6: Unified Public Kernel API

This module provides the public entry-point surface for the seLe4n kernel model.
Previously it was just an import barrel (finding L-01); it now defines:

1. **`apiInvariantBundle`** — a top-level alias for the composed proof-layer
   invariant bundle, giving API consumers a single entry point.
2. **`apiInvariantBundle_default`** — base-case theorem proving the bundle
   holds for the default (empty) state.
3. **Entry-point stability table** — documents which subsystem operations
   are considered part of the stable public API.

## Entry-point stability classification

| Entry point | Subsystem | Stability |
|---|---|---|
| `schedule`, `handleYield` | Scheduler | Single-core reference, proof-only (WS-ZA ZA4.5: writes the run queue through its ghost; the live forms are `scheduleEffectiveOnCore`, `yieldOnCore`) |
| `scheduleChecked`, `handleYieldChecked` | Scheduler (X2-I) | Single-core reference, proof-only — `withOutgoingContextChecked` guard |
| `timerTick` | Scheduler (M-04) | Single-core reference, proof-only (live form `timerTickOnCore`) |
| `timerTickChecked` | Scheduler (M-04/X2-I) | Single-core reference, proof-only — `withOutgoingContextChecked` guard |
| `scheduleDomain`, `switchDomain` | Scheduler (M-05) | Single-core reference, proof-only (live forms `scheduleDomainOnCore`, `switchDomainOnCore`) |
| `switchDomainChecked` | Scheduler (M-05/X2-I) | Single-core reference, proof-only — `withOutgoingContextChecked` guard |
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
| ~~`apiEndpointSend`, `apiEndpointReceive`~~ | Syscall IPC (WS-H15c) | **Removed** (S5-A v0.19.4) — replaced by `syscallEntry` |
| ~~`apiEndpointCall`, `apiEndpointReply`~~ | Syscall IPC (WS-H15c) | **Removed** (S5-A v0.19.4) — replaced by `syscallEntry` |
| ~~`apiCspaceMint`, `apiCspaceCopy`, `apiCspaceMove`~~ | Syscall Capability (WS-H15c) | **Removed** (S5-A v0.19.4) — replaced by `syscallEntry` |
| ~~`apiCspaceDelete`~~ | Syscall Capability (WS-H15c) | **Removed** (S5-A v0.19.4) — replaced by `syscallEntry` |
| ~~`apiLifecycleRetype`~~ | Syscall Lifecycle (WS-H15c) | **Removed** (S5-A v0.19.4) — replaced by `syscallEntry` |
| ~~`apiVspaceMap`, `apiVspaceUnmap`~~ | Syscall VSpace (WS-H15c) | **Removed** (S5-A v0.19.4) — replaced by `syscallEntry` |
| ~~`apiServiceRegister`, `apiServiceRevoke`, `apiServiceQuery`~~ | Syscall Service (WS-Q1-D) | **Removed** (S5-A v0.19.4) — replaced by `syscallEntry` |
| `syscallEntry` | Syscall dispatch (WS-J1-C) | Stable (unchecked — for proofs and internal kernel paths) |
| `syscallEntryChecked` | Syscall dispatch (T6-I) | Stable (**production entry point** — information-flow-checked) |
| `lookupThreadRegisterContext` | Syscall dispatch (WS-J1-C) | Stable |
| `dispatchSyscall` | Syscall dispatch (WS-J1-C) | Stable (unchecked internal) |
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
| `resume` | `seL4_TCB_Resume` | **IMPLEMENTED** (D1, v0.24.0; per-core reroute WS-SM SM8.B, PR #861 round 10). Wired as `SyscallId.tcbResume` to `resumeThreadOnCore` in `Lifecycle/Suspend.lean` (`resumeThread` remains its boot-core form). | Complete |
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

/-- L-01/WS-E6: The default (empty) state satisfies the API invariant bundle.
This is the base case for inductive invariant arguments: the system starts
in a valid state. -/
theorem apiInvariantBundle_default :
    apiInvariantBundle (default : SystemState) :=
  Architecture.default_system_state_proofLayerInvariantBundle

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

/-- X2-I: Checked `schedule` wrapper. Verifies the outgoing context save
succeeds before delegating to the core scheduler. Under `currentThreadValid`
the failure branch is unreachable. -/
noncomputable def scheduleChecked : Kernel Unit :=
  withOutgoingContextChecked schedule

/-- X2-I: Checked `handleYield` wrapper. Verifies the outgoing context save
succeeds before delegating to the core yield handler. -/
noncomputable def handleYieldChecked : Kernel Unit :=
  withOutgoingContextChecked handleYield

/-- X2-I: Checked `timerTick` wrapper. Verifies the outgoing context save
succeeds before delegating to the core timer tick handler. -/
noncomputable def timerTickChecked : Kernel Unit :=
  withOutgoingContextChecked timerTick

/-- X2-I: Checked `switchDomain` wrapper. Verifies the outgoing context save
succeeds before delegating to the core domain switch. Note: `switchDomain`
also calls `saveOutgoingContext` internally; the outer check ensures failure
is detected before any scheduler state mutation. -/
noncomputable def switchDomainChecked : Kernel Unit :=
  withOutgoingContextChecked switchDomain

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

The production syscall path is `syscallEntry → dispatchSyscall → syscallInvoke
→ dispatchWithCap`, which reads the caller's register file, decodes typed
arguments, resolves capabilities, and dispatches to the appropriate internal
operation. The legacy `api*` wrappers were removed in S5-A (v0.19.4).

### Internal vs syscall operations

| Category | Capability check? | Invoked by |
|---|---|---|
| **Internal** (`schedule`, `endpointSendDual`, etc.) | No | Kernel paths |
| **Syscall** (`syscallEntry` → `dispatchSyscall`) | Yes | User-space |
| **Scheduler** (`schedule`, `handleYield`, `timerTick`) | No | Timer IRQ, kernel |
-/

/-- WS-H15c/A-42: Syscall gate descriptor. Encodes the caller's identity,
CSpace root, capability address, address depth, and the required access right
for the requested operation. -/
structure SyscallGate where
  /-- Thread ID of the invoking user-space thread. -/
  callerId     : SeLe4n.ThreadId
  /-- ObjId of the caller's CSpace root CNode. -/
  cspaceRoot   : SeLe4n.ObjId
  /-- Capability address to resolve within the CSpace. -/
  capAddr      : SeLe4n.CPtr
  /-- Number of address bits to consume during resolution. -/
  capDepth     : Nat
  /-- The access right required for this syscall. -/
  requiredRight : AccessRight
  deriving Repr, DecidableEq

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
    match resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st with
    | .error e => .error e
    | .ok ref =>
      match SystemState.lookupSlotCap st ref with
      | none => .error .invalidCapability
      | some cap =>
        -- PR #889 review round 2: a capability naming a kernel-reserved idle
        -- object is not a capability user space may hold — seL4 has none to
        -- its idle thread — so it resolves like an empty slot.  This is the
        -- one resolution every invoked capability passes through
        -- (`syscallLookupCap` is defined as it plus the rights gate), which
        -- is what makes `syscallResolveCap_ok_not_reserved` a statement about
        -- every syscall rather than about the arms that happen to check.
        if SeLe4n.Kernel.capTargetsReservedIdleObject cap then .error .invalidCapability
        else .ok (cap, st)

/-- WS-H15c/A-42: Resolve and validate a capability from a syscall gate.

Performs the full seL4 syscall capability-checking sequence:
1. Resolves the capability address through the CSpace root via `resolveCapAddress`.
2. Looks up the capability at the resolved slot.
3. Verifies the capability grants the required access right.

Returns the resolved capability if all checks pass; an error otherwise.
The state is unchanged (capability lookup is read-only).  Since PR #870
round 5 the resolution half is the shared `syscallResolveCap`; the syscalls
that check the target first (`syscallChecksTargetFirst`) take that half alone
and own both authority checks in their arms. -/
def syscallLookupCap (gate : SyscallGate) : Kernel Capability :=
  fun st =>
    match syscallResolveCap gate st with
    | .error e => .error e
    | .ok (cap, st') =>
      if cap.hasRight gate.requiredRight
      then .ok (cap, st')
      else .error .illegalAuthority

/-- WS-H15c/A-42: Gated operation combinator. Resolves and validates a
capability, then invokes the operation with the resolved capability. -/
def syscallInvoke (gate : SyscallGate) (op : Capability → Kernel α) : Kernel α :=
  fun st =>
    match syscallLookupCap gate st with
    | .error e => .error e
    | .ok (cap, st') => op cap st'

/-- PR #870 round 5: gated operation combinator over the **resolve-only**
lookup — for arms that own *both* authority checks themselves, target first.
The audit arms are the consumers: their authority is a dedicated `CapTarget`,
so the informative refusal for a wrong-kind capability is `.invalidCapability`
regardless of what rights it happens to carry, and only an arm that sees the
capability before any rights verdict can promise that. -/
def syscallInvokeResolved (gate : SyscallGate) (op : Capability → Kernel α) : Kernel α :=
  fun st =>
    match syscallResolveCap gate st with
    | .error e => .error e
    | .ok (cap, st') => op cap st'

/-- WS-SM SM6.D (faithful seL4-MCS, server-supplied reply objects): extract the
single-use `ReplyId` a reply capability authorizes.  Fails `.invalidCapability`
if the capability does not target a reply object. -/
def extractReplyId (cap : Capability) : Except KernelError SeLe4n.ReplyId :=
  match cap.target with
  | .replyCap rid => .ok rid
  | _ => .error .invalidCapability

/-- WS-SM SM6.D: resolve a reply capability held at a CSpace slot to its
`ReplyId`.  Under faithful seL4-MCS the *server* passes the reply *capability*
slot (a CPtr through the verified `syscallLookupCap`, like `tcbBindNotification`),
not a raw `ReplyId`, so authority flows from *holding* a reply capability rather
than naming an arbitrary reply object.  Read-only (state unchanged on success). -/
def syscallLookupReplyId (gate : SyscallGate) : Kernel SeLe4n.ReplyId :=
  fun st =>
    match syscallLookupCap gate st with
    | .error e => .error e
    | .ok (cap, st') =>
        match extractReplyId cap with
        | .error e => .error e
        | .ok rid => .ok (rid, st')

/-- `extractReplyId` succeeds with `rid` exactly when the capability targets the
reply object `rid`. -/
theorem extractReplyId_eq_ok_iff (cap : Capability) (rid : SeLe4n.ReplyId) :
    extractReplyId cap = .ok rid ↔ cap.target = .replyCap rid := by
  unfold extractReplyId
  cases cap.target <;> simp

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

Written in the shape `extractReplyId` already uses.  Unlike the reply arms —
whose full lookup answers a missing right before `extractReplyId` runs — the
audit arms really are target-first on the composed path: since PR #870
round 5 the checked dispatch routes them through the resolve-only lookup
(`syscallChecksTargetFirst` → `syscallInvokeResolved`), so the target is
checked first and the right second, with
`dispatchSyscallChecked_audit_target_first` the composed witness. -/
def extractAuditAuthority (cap : Capability) : Except KernelError Unit :=
  match cap.target with
  | .auditTrail => .ok ()
  | _ => .error .invalidCapability

/-- WS-SM SM9.A.9: the authority check succeeds exactly on an audit
capability. -/
theorem extractAuditAuthority_eq_ok_iff (cap : Capability) :
    extractAuditAuthority cap = .ok () ↔ cap.target = .auditTrail := by
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
        { target := .object oid, rights := AccessRightSet.ofList AccessRight.all, } = .error .invalidCapability := rfl

/-- WS-SM SM6.D (faithful seL4-MCS receive linkage): resolve the *server-supplied*
reply capability the `Recv` syscall names in `RecvArgs.replyCPtr` (msgRegs[0]) to
its `ReplyId`.  Crucially the reply cap lives at a **different** CSpace slot than
the endpoint receive cap, so we resolve it through a gate whose `capAddr` is
`replyCPtr` (not the primary syscall gate, which names the endpoint).  Read-only.
Returns `none` for a plain `Recv` that omits a reply object (the source may be a
`Send`/`Notification`), an unresolvable slot, or a non-reply cap — the caller arm
then links only on a genuine `Call` rendezvous. -/
def resolveRecvReplyId (gate : SyscallGate) (decoded : SyscallDecodeResult)
    (st : SystemState) : Except KernelError (Option SeLe4n.ReplyId) :=
  -- A plain `Recv` *omits* the reply object via message length 0 (PR #822 review):
  -- the ARM64 register decoder always materializes x2..x5, so MR0 is present even
  -- for a no-reply receive (the Rust `endpoint_receive` wrapper sends length 0 /
  -- x2 = 0).  Gate on the declared `msgInfo.length`: **only** length 0 means "no
  -- reply object" (→ `.ok none`).  At length ≥ 1 MR0 names an *explicit* reply
  -- cap, so a failed resolution is a hard error (`.ok none` would silently
  -- downgrade a bad/stale CPtr to a plain receive and then strand a later Call);
  -- `endpoint_receive_with_reply` declares length 1.
  if decoded.msgInfo.length == 0 then .ok none else
  match Architecture.SyscallArgDecode.decodeRecvArgs decoded with
  | .error e => .error e
  | .ok rargs =>
      let replyGate : SyscallGate :=
        { gate with capAddr := rargs.replyCPtr, requiredRight := .write }
      match syscallLookupCap replyGate st with
      | .error e => .error e
      | .ok (rcap, _) =>
          match extractReplyId rcap with
          | .error e => .error e
          | .ok rid =>
              -- PR #822 review: validate the reply object exists AND is FREE before
              -- treating the cap as usable.  "Free" means BOTH `caller = none` (no
              -- caller-first link) AND not already stashed in some server's
              -- `pendingReceiveReply` (`replyIsStashed` — a server-first link in
              -- progress); else a second `endpoint_receive_with_reply` via a copied
              -- cap could block another server on the same `rid` and later roll back
              -- `.replyCapInvalid` on a stale stash.  Matches the lifecycle-cleanup
              -- in-use treatment.  Explicit-MR0 failure is fail-closed before receive.
              match st.getReply? rid with
              | some r =>
                  if r.caller.isNone && !st.replyStashedAt rid r then .ok (some rid)
                  else .error .replyCapInvalid
              | none => .error .replyCapInvalid

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
capability named in `ReplyRecvArgs.replyCPtr` to the `(ReplyId, prevCaller)` pair
it authorizes — `prevCaller` is the reply object's `caller`, the previous caller
the reply leg answers.  Resolves the reply cap from the caller's CSpace at
`replyCPtr` (a gate whose `capAddr` is that slot), then `getReply?` + reads
`reply.caller`.  Read-only.  Returns `Except KernelError`: a CSpace / cap
resolution failure (`decodeReplyRecvArgs` / `syscallLookupCap` / `extractReplyId`)
**propagates** its explicit error (`invalidCapability` / `illegalAuthority` / …),
mirroring `resolveRecvReplyId`, so a malformed or unauthorized reply-cap slot is
distinguishable from a valid-but-consumed Reply.  `.replyCapInvalid` is reserved for
a missing MR0, a missing Reply object, or a present Reply object with **no
outstanding caller** (authority now flows from *holding* the reply cap, exactly like
the `.reply` arm — no raw-thread bypass). -/
def resolveReplyRecvReply (gate : SyscallGate) (decoded : SyscallDecodeResult)
    (st : SystemState) :
    Except KernelError (SeLe4n.ReplyId × SeLe4n.ThreadId × Option SeLe4n.Badge) :=
  -- PR #822 review: require MR0 explicitly present (`msgInfo.length ≥ 1`) before
  -- reading the reply CPtr — the ARM64 register decoder always materializes x2..x5,
  -- so a length-0 `ReplyRecv` must not resolve/consume a stale (x2) reply cap.
  if decoded.msgInfo.length == 0 then .error .replyCapInvalid else
  match Architecture.SyscallArgDecode.decodeReplyRecvArgs decoded with
  | .error e => .error e
  | .ok rargs =>
      let replyGate : SyscallGate :=
        { gate with capAddr := rargs.replyCPtr, requiredRight := .write }
      -- PR #822 review: propagate the explicit CSpace cap error (a missing slot or a
      -- cap without write authority is `invalidCapability` / `illegalAuthority`), not
      -- a collapsed `.replyCapInvalid` — the latter is reserved for a resolved Reply
      -- object with no outstanding caller (mirrors `resolveRecvReplyId`).
      match syscallLookupCap replyGate st with
      | .error e => .error e
      | .ok (rcap, _) =>
          match extractReplyId rcap with
          | .error e => .error e
          | .ok rid =>
              -- WS-RR RR7.11: one resolution of "which thread does this reply
              -- capability answer", shared with the `.reply` arm and with the
              -- declared-footprint resolver.  Both former `none` arms produced
              -- `.replyCapInvalid`, so this is behaviour-identical.
              match replyAnsweredCaller? st rid with
              -- PR #822 review: carry the *reply cap's* badge (the reply
              -- authority), not the endpoint receive cap's, so the previous
              -- caller receives the badge associated with the reply cap (as in
              -- the `.reply` arm) when the two differ.
              | some prevCaller => .ok (rid, prevCaller, rcap.badge)
              | none => .error .replyCapInvalid

-- ============================================================================
-- Syscall soundness theorems
-- ============================================================================

/-- **WS-LS LS2.3**: the reply a `.replyRecv` resolves is one the state records
an answered caller for — the resolver's own last check, read back out so the
scheduler footprint's `replyAnsweredCaller?` read is the arm's. -/
theorem resolveReplyRecvReply_answered (gate : SyscallGate) (decoded : SyscallDecodeResult)
    (st : SystemState) (rid : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId)
    (badge : Option SeLe4n.Badge)
    (h : resolveReplyRecvReply gate decoded st = .ok (rid, prevCaller, badge)) :
    replyAnsweredCaller? st rid = some prevCaller := by
  unfold resolveReplyRecvReply at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · dsimp only at h
      split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · split at h
          · rename_i hAns
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
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
  rw [resolveCapAddress_congr_objects st₁ st₂ hObj gate.capAddr gate.capDepth gate.cspaceRoot]
    at h
  cases hRef : resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st₂ with
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
      by_cases hRes : capTargetsReservedIdleObject cap' = true
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
    ∃ ref, resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st = .ok ref ∧
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
    SeLe4n.Kernel.capTargetsReservedIdleObject cap = false := by
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
    ∃ ref, resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st = .ok ref ∧
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

/-- WS-H15c/A-42: If `syscallInvoke` succeeds, the caller held the required
capability. -/
theorem syscallInvoke_requires_right
    (gate : SyscallGate) (op : Capability → Kernel α) (st : SystemState)
    (a : α) (st' : SystemState)
    (hOk : syscallInvoke gate op st = .ok (a, st')) :
    ∃ cap ref, resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st = .ok ref ∧
               SystemState.lookupSlotCap st ref = some cap ∧
               cap.hasRight gate.requiredRight = true := by
  unfold syscallInvoke at hOk
  split at hOk
  · simp at hOk
  next cap stLookup hLookupOk =>
    obtain ⟨ref, hResolve, hSlot, hRight, hStEq⟩ :=
      syscallLookupCap_implies_capability_held gate st cap stLookup hLookupOk
    exact ⟨cap, ref, hResolve, hSlot, hRight⟩

/-- V3-F (M-PRF-3): All callers of `resolveCapAddress` perform post-resolution
    rights checks. Any successful `syscallInvoke` — the sole gateway used by
    both `dispatchSyscall` and `dispatchSyscallChecked` — implies the resolved
    capability holds the required access right. The gate architecture ensures
    every syscall path composes `resolveCapAddress` → `lookupSlotCap` →
    `hasRight` before any operation is executed. -/
theorem resolveCapAddress_callers_check_rights
    (gate : SyscallGate) (op : Capability → Kernel α)
    (st : SystemState) (a : α) (st' : SystemState)
    (hOk : syscallInvoke gate op st = .ok (a, st')) :
    ∃ cap ref,
      resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st = .ok ref ∧
      SystemState.lookupSlotCap st ref = some cap ∧
      cap.hasRight gate.requiredRight = true :=
  syscallInvoke_requires_right gate op st a st' hOk

-- ============================================================================
-- S5-A: Deprecated api* wrappers removed (v0.19.4)
--
-- All 14 deprecated wrappers (apiEndpointSend, apiEndpointReceive,
-- apiEndpointCall, apiEndpointReply, apiCspaceMint, apiCspaceCopy,
-- apiCspaceMove, apiCspaceDelete, apiLifecycleRetype, apiVspaceMap,
-- apiVspaceUnmap, apiServiceRegister, apiServiceRevoke, apiServiceQuery)
-- were removed in S5-A. The production syscall path is:
--   syscallEntry → dispatchSyscall → syscallInvoke → dispatchWithCap
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
   `syscallInvoke`.

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
  -- **WS-BP BP7.1 (`v0.36.6`)**: a reset hands the untyped's memory back to it,
  -- which is authority over that memory — the retype right, as for the carve.
  | .untypedReset    => .retype
  | .vspaceMap       => .write
  | .vspaceUnmap     => .write
  -- WS-SM SM7.D: publishing freshly-written code requires the **write** right
  -- on the page's capability.  seL4's `Page_Unify_Instruction` needs only the
  -- frame cap; requiring write is the least-privilege reading of the same
  -- authority — the operation exists to push *the caller's own stores* to the
  -- Point of Unification, so the subject that needs it is by construction one
  -- that could write the page.  A read-only holder gains nothing by unifying.
  | .vspaceUnifyInstruction => .write
  -- WS-SM SM8.C.9: declassifying releases the caller's information *into* the
  -- target object's domain, so the flow direction is subject → object and the
  -- authority is the **write** right on the target's capability.  A read-only
  -- holder can observe the object; it cannot make the kernel record that its
  -- own domain was downgraded into that object's.
  | .declassify         => .write
  -- WS-SM SM9.C.8: the data-carrying declassification signals a notification,
  -- so its authority is the same **write** right the ordinary
  -- `.notificationSignal` requires on the notification's capability — the
  -- declassification is an *additional* gate on top of that authority, never a
  -- substitute for it.  A read-only notification cap holder cannot signal, and
  -- so cannot declassify through a signal either, whatever the policy says.
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
  | .tcbSuspend            => .write
  | .tcbResume             => .write
  | .tcbSetPriority        => .write
  | .tcbSetMCPriority      => .write
  | .tcbSetIPCBuffer       => .write
  | .tcbSetAffinity        => .write
  | .tcbSetFaultHandler    => .write
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
  -- WS-ZA ZA4.3: a yield invokes no capability — `dispatchSyscall` and
  -- `dispatchSyscallChecked` run it before any gate is built — so no right is
  -- ever checked for it.  `.read`, the weakest, is the value a gate would carry.
  | .yield                 => .read
  -- WS-ZA ZA6.9: the Consumed invocation writes the context (its consumed time
  -- is reset), so it carries the write right Bind and Unbind carry; seL4's
  -- scheduling-context capability has no rights of its own to check.
  | .schedContextConsumed  => .write

/-- PR #870 round 5: **which syscalls validate the capability's target before
its rights.**

Exactly the audit pair.  Their authority is a dedicated `CapTarget`
(`extractAuditAuthority`), so the informative refusal for a wrong-kind
capability is `.invalidCapability` regardless of what rights it happens to
carry — and the only way to promise that is to route them through the
resolve-only lookup (`syscallInvokeResolved`) and let the arm check target
first, right second.  Every other syscall keeps the classic order: the full
lookup's rights gate, then whatever operand binding its arm performs.

No wildcard, matching `syscallRequiredRight`: a new syscall is a missing case
at elaboration and must state its choice. -/
def syscallChecksTargetFirst : SyscallId → Bool
  | .send            => false
  | .receive         => false
  | .call            => false
  | .reply           => false
  | .cspaceMint      => false
  | .cspaceCopy      => false
  | .cspaceMove      => false
  | .cspaceDelete    => false
  -- **WS-RR RR8.16 (`v0.35.190`)**: classic order.  The authority is an ordinary
  -- CNode capability rather than a dedicated `CapTarget`, so there is no
  -- wrong-kind refusal to sequence ahead of the rights gate.
  | .cspaceRevoke    => false
  -- **WS-BP BP7.1 (`v0.36.5`)**: classic order.  An untyped capability is an
  -- ordinary `.object` capability, so there is no wrong-kind refusal to
  -- sequence ahead of the rights gate.
  | .untypedRetype   => false
  | .untypedReset    => false
  | .vspaceMap       => false
  | .vspaceUnmap     => false
  | .vspaceUnifyInstruction => false
  | .declassify         => false
  -- WS-SM SM9.C.8: classic order.  The authority is an ordinary notification
  -- capability, not a dedicated `CapTarget`, so there is no wrong-kind refusal
  -- to sequence ahead of the rights gate.
  | .declassifySignal   => false
  | .auditRead          => true
  | .auditDrain         => true
  | .serviceRegister    => false
  | .serviceRevoke      => false
  | .serviceQuery       => false
  | .notificationSignal => false
  | .notificationWait   => false
  | .replyRecv          => false
  | .schedContextConfigure => false
  | .schedContextBind      => false
  | .schedContextUnbind    => false
  | .tcbSuspend            => false
  | .tcbResume             => false
  | .tcbSetPriority        => false
  | .tcbSetMCPriority      => false
  | .tcbSetIPCBuffer       => false
  | .tcbSetAffinity        => false
  | .tcbSetFaultHandler    => false
  | .tcbSetSpace           => false
  | .pageTableMap          => false
  | .pageTableUnmap        => false
  | .yield                 => false
  | .schedContextConsumed  => false
  | .tcbBindNotification   => false
  | .tcbUnbindNotification => false
  | .mintReplyCap          => false

/-- PR #870 round 5: the classifier's semantics, pinned — target-first is
exactly the audit pair. -/
theorem syscallChecksTargetFirst_iff (id : SyscallId) :
    syscallChecksTargetFirst id = true ↔ id = .auditRead ∨ id = .auditDrain := by
  cases id <;> simp [syscallChecksTargetFirst]

/-- AN7-E (API-M01): the resolver on an empty address array resolves
    nothing, granted or not. -/
theorem resolveExtraCaps_empty
    (cspaceRoot : SeLe4n.ObjId) (depth : Nat) (granted : Bool) (st : SystemState) :
    resolveExtraCaps cspaceRoot #[] depth granted st = #[] := by
  cases granted <;> rfl

/-- **PR #873 round 14: a sender without Grant resolves nothing, whatever it
asked for.**  The statement the gate is for: its addresses are not even looked
up.  Stated over an arbitrary address array, so it is the resolver's contract
rather than a fact about one input. -/
theorem resolveExtraCaps_ungranted
    (cspaceRoot : SeLe4n.ObjId) (capAddrs : Array SeLe4n.CPtr) (depth : Nat)
    (st : SystemState) :
    resolveExtraCaps cspaceRoot capAddrs depth false st = #[] := rfl

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
narrative above describes `.schedContextBind` as it was.  MR0 is a TCB
capability address now (`SchedContextBindArgs.tcbCPtr`), resolved through the
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
  if SeLe4n.Kernel.isIdleThreadId tid then .error .invalidArgument
  else
    match tid.toValid? with
    | none => .error .invalidArgument
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
    validateThreadIdArg tid = .error .invalidArgument := by
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


/-- WS-AL AL7-A (cascades AK7-E): lift a raw `SchedContextId` to
`ValidSchedContextId` at the dispatch boundary. Mirrors
`validateThreadIdArg`; rejects `SchedContextId.sentinel`. -/
@[inline] private def validateSchedContextIdArg (scId : SeLe4n.SchedContextId) :
    Except KernelError SeLe4n.ValidSchedContextId :=
  match scId.toValid? with
  | none => .error .invalidArgument
  | some v => .ok v

/-- WS-AL AL8 (cascades AK7-E): lift a raw `ObjId` to `ValidObjId`.
Used by dispatch arms whose handlers operate on `ObjId` directly (e.g.,
`schedContextConfigure` which does `st.objects[scId]?` rather than
going through `SchedContextId.toObjId`). Rejects `ObjId.sentinel`. -/
@[inline] def validateObjIdArg (oid : SeLe4n.ObjId) :
    Except KernelError SeLe4n.ValidObjId :=
  if SeLe4n.Kernel.isIdleObjId oid then .error .invalidArgument
  else
    match oid.toValid? with
    | none => .error .invalidArgument
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

MR0 is `SchedContextBindArgs.tcbCPtr` now, resolved exactly as that arm resolves
its extra capability: `syscallLookupCap` on a gate at the caller's CSpace root and
depth, requiring `.write` — so the reserved-idle refusal is the chokepoint's own
(`syscallResolveCap_ok_not_reserved`) rather than a second lift-point check — and
the resolved capability must target a **TCB** the store holds (a capability to any
other kind of object is `.invalidCapability`, the answer `bindNotification` gives a
non-notification target).  `validateThreadIdArg` still promotes the id, so the
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
      match st.getCNode? callerTcb.cspaceRoot with
      | none => .error .invalidCapability
      | some rootCn =>
        let tcbGate : SyscallGate := {
          callerId      := callerTid
          cspaceRoot    := callerTcb.cspaceRoot
          capAddr       := args.tcbCPtr
          capDepth      := rootCn.depth
          requiredRight := .write
        }
        match syscallLookupCap tcbGate st with
        | .error e => .error e
        | .ok (tcbCap, _) =>
          match tcbCap.target with
          | .object tcbObjId =>
            match st.getTcb? (SeLe4n.ThreadId.ofNat tcbObjId.toNat) with
            | none => .error .invalidCapability
            | some _ => validateThreadIdArg (SeLe4n.ThreadId.ofNat tcbObjId.toNat)
          | _ => .error .invalidCapability

/-- **`v0.35.204` (the authority fact)**: a thread the resolver answers is one
the caller holds a **writable capability** to, found at MR0's address in the
caller's own CSpace, and it is a TCB the store holds.  The read-only lookup
returns the state it was given (`syscallLookupCap_preserves_state`), so the
capability is exhibited at `st` itself. -/
theorem resolveSchedContextBindThread_ok_authorised
    (callerTid : SeLe4n.ThreadId) (args? : Except KernelError SchedContextBindArgs)
    (st : SystemState)
    (v : SeLe4n.ValidThreadId)
    (h : resolveSchedContextBindThread callerTid args? st = .ok v) :
    ∃ (args : SchedContextBindArgs) (callerTcb : TCB) (rootCn : CNode)
      (tcbCap : Capability),
      args? = .ok args ∧
      st.getTcb? callerTid = some callerTcb ∧
      st.getCNode? callerTcb.cspaceRoot = some rootCn ∧
      syscallLookupCap
        { callerId := callerTid, cspaceRoot := callerTcb.cspaceRoot,
          capAddr := args.tcbCPtr, capDepth := rootCn.depth,
          requiredRight := .write } st = .ok (tcbCap, st) ∧
      tcbCap.hasRight .write = true ∧
      tcbCap.target = .object v.val.toObjId ∧
      (∃ tcb, st.getTcb? v.val = some tcb) := by
  unfold resolveSchedContextBindThread at h
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
      cases hRoot : st.getCNode? callerTcb.cspaceRoot with
      | none => rw [hRoot] at h; cases h
      | some rootCn =>
        rw [hRoot] at h
        simp only at h
        cases hLk : syscallLookupCap
            { callerId := callerTid, cspaceRoot := callerTcb.cspaceRoot,
              capAddr := args.tcbCPtr, capDepth := rootCn.depth,
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
              refine ⟨args, callerTcb, rootCn, tcbCap,
                by first | exact hArgs | rfl,
                by first | exact hCaller | rfl,
                by first | exact hRoot | rfl,
                by first | exact hLk | rw [hSt],
                hRight, ?_, ⟨tcb, by rw [hVal]; exact hTcb⟩⟩
              rw [hVal]
              first
                | exact hTgt
                | exact congrArg CapTarget.object rfl
          all_goals (rw [hTgt] at h; cases h)

/-- **WS-ZA ZA6.4**: the scheduling context a configure through core `core`'s
scheduling control names: seL4-MCS's `decodeSchedControl_ConfigureFlags` takes the
context as an extra capability, and here, as `.schedContextBind` takes its thread,
it is a capability at MR0 in the caller's own CSpace, resolved by
`syscallLookupCap` requiring `.write`.  The capability must name a scheduling
context the store holds (anything else is `.invalidCapability`, seL4's answer to
an extra capability of the wrong type), the control must name a core the kernel
runs (`.invalidCapability` otherwise; boot installs a control for each core it
runs), and `validateObjIdArg` promotes the id.  A context homed on another core
is not refused: the configure moves it to the control's core with its thread, as
seL4 does (`SchedContextOps.schedControlConfigure`).  Every check reads the state
handed in; nothing is written.

**One resolver, two askers.**  The live arm (`dispatchCapabilityOnly`) and the
scheduler-domain operand builder (`abiEntryLockOperands`) both read this
definition, so the context the footprint declares and the context the transition
configures are one reading of one register. -/
def resolveSchedControlConfigureTarget (callerTid : SeLe4n.ThreadId) (core : Nat)
    (scCPtr : SeLe4n.CPtr) (st : SystemState) : Except KernelError SeLe4n.ValidObjId :=
  match st.getTcb? callerTid with
  | none => .error .objectNotFound
  | some callerTcb =>
    match st.getCNode? callerTcb.cspaceRoot with
    | none => .error .invalidCapability
    | some rootCn =>
      let scGate : SyscallGate := {
        callerId      := callerTid
        cspaceRoot    := callerTcb.cspaceRoot
        capAddr       := scCPtr
        capDepth      := rootCn.depth
        requiredRight := .write
      }
      match syscallLookupCap scGate st with
      | .error e => .error e
      | .ok (scCap, _) =>
        match scCap.target with
        | .object scObjId =>
          match st.getSchedContext? (SchedContextId.ofObjId scObjId) with
          | none => .error .invalidCapability
          | some _ =>
            if core < SeLe4n.Kernel.Concurrency.numCores then validateObjIdArg scObjId
            else .error .invalidCapability
        | _ => .error .invalidCapability

/-- **WS-ZA ZA6.4 (the authority fact)**: a context the resolver answers is one the
caller holds a **writable capability** to, found at `scCPtr` in the caller's own
CSpace; the store holds it as a scheduling context, and the control names a core
the kernel runs. -/
theorem resolveSchedControlConfigureTarget_ok_authorised
    (callerTid : SeLe4n.ThreadId) (core : Nat) (scCPtr : SeLe4n.CPtr) (st : SystemState)
    (v : SeLe4n.ValidObjId)
    (h : resolveSchedControlConfigureTarget callerTid core scCPtr st = .ok v) :
    ∃ (callerTcb : TCB) (rootCn : CNode) (scCap : Capability) (sc : SchedContext),
      st.getTcb? callerTid = some callerTcb ∧
      st.getCNode? callerTcb.cspaceRoot = some rootCn ∧
      syscallLookupCap
        { callerId := callerTid, cspaceRoot := callerTcb.cspaceRoot,
          capAddr := scCPtr, capDepth := rootCn.depth,
          requiredRight := .write } st = .ok (scCap, st) ∧
      scCap.hasRight .write = true ∧
      scCap.target = .object v.val ∧
      st.getSchedContext? (SchedContextId.ofObjId v.val) = some sc ∧
      core < SeLe4n.Kernel.Concurrency.numCores := by
  unfold resolveSchedControlConfigureTarget at h
  cases hCaller : st.getTcb? callerTid with
  | none => rw [hCaller] at h; cases h
  | some callerTcb =>
    rw [hCaller] at h
    simp only at h
    cases hRoot : st.getCNode? callerTcb.cspaceRoot with
    | none => rw [hRoot] at h; cases h
    | some rootCn =>
      rw [hRoot] at h
      simp only at h
      cases hLk : syscallLookupCap
          { callerId := callerTid, cspaceRoot := callerTcb.cspaceRoot,
            capAddr := scCPtr, capDepth := rootCn.depth,
            requiredRight := .write } st with
      | error e => rw [hLk] at h; cases h
      | ok pair =>
        obtain ⟨scCap, s'⟩ := pair
        rw [hLk] at h
        simp only at h
        obtain ⟨_, _, _, hRight, hSt⟩ :=
          syscallLookupCap_implies_capability_held _ st scCap s' hLk
        rw [hSt] at hLk
        cases hTgt : scCap.target
        case object scObjId =>
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
              exact ⟨callerTcb, rootCn, scCap, sc, rfl, hRoot, hLk, hRight, hTgt, hSc, hCov⟩
            · rw [if_neg hCov] at h; cases h
        all_goals (rw [hTgt] at h; cases h)

/-- **`v0.35.204`**: a TCB capability naming a reserved idle object is refused at
the capability chokepoint — `syscallResolveCap`'s own refusal, reached through
the resolver's lookup — with `.invalidCapability`, the answer an empty slot gives.
The successor of `dispatchCapabilityOnly_schedContextBind_idle_operand_refused`
(retired with the raw operand it was about): the idle threads are the kernel's
own scheduling reserve, and no capability a thread can hold names one. -/
theorem resolveSchedContextBindThread_refuses_idle_capability
    (callerTid : SeLe4n.ThreadId) (args? : Except KernelError SchedContextBindArgs)
    (st : SystemState)
    (args : SchedContextBindArgs) (callerTcb : TCB) (rootCn : CNode) (ref : SlotRef)
    (idleCap : Capability)
    (hArgs : args? = .ok args)
    (hCaller : st.getTcb? callerTid = some callerTcb)
    (hRoot : st.getCNode? callerTcb.cspaceRoot = some rootCn)
    (hRef : resolveCapAddress callerTcb.cspaceRoot (args.tcbCPtr)
      rootCn.depth st = .ok ref)
    (hSlot : SystemState.lookupSlotCap st ref = some idleCap)
    (hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject idleCap = true) :
    resolveSchedContextBindThread callerTid args? st = .error .invalidCapability := by
  unfold resolveSchedContextBindThread
  rw [hArgs]
  simp only
  rw [hCaller]
  simp only
  rw [hRoot]
  simp only
  unfold syscallLookupCap syscallResolveCap
  simp only [hRef, hSlot, hIdle, if_true]

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
    match st.getCNode? callerTcb.cspaceRoot with
    | none => .error .invalidCapability
    | some rootCn =>
      let frameGate : SyscallGate := {
        callerId      := callerTid
        cspaceRoot    := callerTcb.cspaceRoot
        capAddr       := args.frame
        capDepth      := rootCn.depth
        requiredRight := .read
      }
      match syscallLookupCap frameGate st with
      | .error e => .error e
      | .ok (frameCap, _) =>
        match frameCap.target with
        | .object frameObjId =>
          match st.getFrame? frameObjId with
          | none => .error .invalidCapability
          | some frame =>
            -- WS-BP BP7.1 (`v0.36.7`): the slot the capability sits in, which
            -- is where the mapping is recorded.  The same pure resolution the
            -- gate's lookup ran (`resolveVSpaceMapFrame_ok_slot`), so it names
            -- the slot the capability was read from.
            match resolveCapAddress callerTcb.cspaceRoot args.frame rootCn.depth st with
            | .error e => .error e
            | .ok frameSlot => .ok (frameSlot, frameCap, frame)
        | _ => .error .invalidCapability

/-- **WS-BP BP7.1 (`v0.36.11`): the slot a capability address names in the
caller's own CSpace**, with the capability it holds and the object that
capability names — the one resolution of a capability the caller holds, which
`resolveCallerCapObject` answers from.  The shape `resolveVSpaceMapFrame` and
`resolveSchedContextBindThread` each spell inline: the slot resolved at the
caller's CSpace root and depth (`resolveCapAddress`), its capability read, a
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
    match st.getCNode? callerTcb.cspaceRoot with
    | none => .error .invalidCapability
    | some rootCn =>
      match resolveCapAddress callerTcb.cspaceRoot addr rootCn.depth st with
      | .error e => .error e
      | .ok ref =>
        match SystemState.lookupSlotCap st ref with
        | none => .error .invalidCapability
        | some cap =>
          if SeLe4n.Kernel.capTargetsReservedIdleObject cap then .error .invalidCapability
          else if cap.hasRight right then
            match cap.target with
            | .object oid => .ok (ref, cap, oid)
            | _ => .error .invalidCapability
          else .error .illegalAuthority

/-- What `resolveCallerCapSlot` answers is a slot of the caller's CSpace holding
a capability with the right asked for, naming the object returned. -/
theorem resolveCallerCapSlot_ok (callerTid : SeLe4n.ThreadId) (addr : SeLe4n.CPtr)
    (right : AccessRight) (st : SystemState) (ref : CSpaceAddr) (cap : Capability)
    (oid : SeLe4n.ObjId) (h : resolveCallerCapSlot callerTid addr right st = .ok (ref, cap, oid)) :
    ∃ (callerTcb : TCB) (rootCn : CNode),
      st.getTcb? callerTid = some callerTcb ∧
      st.getCNode? callerTcb.cspaceRoot = some rootCn ∧
      resolveCapAddress callerTcb.cspaceRoot addr rootCn.depth st = .ok ref ∧
      SystemState.lookupSlotCap st ref = some cap ∧
      cap.hasRight right = true ∧ cap.target = .object oid := by
  unfold resolveCallerCapSlot at h
  cases hCaller : st.getTcb? callerTid with
  | none => rw [hCaller] at h; cases h
  | some callerTcb =>
    rw [hCaller] at h
    simp only at h
    cases hRoot : st.getCNode? callerTcb.cspaceRoot with
    | none => rw [hRoot] at h; cases h
    | some rootCn =>
      rw [hRoot] at h
      simp only at h
      cases hRes : resolveCapAddress callerTcb.cspaceRoot addr rootCn.depth st with
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
                exact ⟨callerTcb, rootCn, rfl, hRoot, hRes, hL, hR, hT⟩
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
    ∃ (callerTcb : TCB) (rootCn : CNode) (ref : CSpaceAddr),
      st.getTcb? callerTid = some callerTcb ∧
      st.getCNode? callerTcb.cspaceRoot = some rootCn ∧
      resolveCapAddress callerTcb.cspaceRoot addr rootCn.depth st = .ok ref ∧
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
    obtain ⟨callerTcb, rootCn, hT, hC, hRes, hL, hR, hTg⟩ :=
      resolveCallerCapSlot_ok callerTid addr right st ref cap' oid' hS
    exact ⟨callerTcb, rootCn, ref, hT, hC, hRes, hL, hR, hTg⟩

/-- **WS-BP BP7.1 (`v0.36.11`): the two slots a `.tcbSetSpace` copies from,
resolved through the caller's own CSpace** — seL4's `TCB_SetSpace` operands.

MR0 addresses a capability to the new **CSpace root**, and the caller must hold
it with `.grant` **and** `.write`: making a CNode a thread's CSpace root hands
that thread every capability the CNode holds and the ability to write the CNode's
slots, so it is authority to pass capabilities on — the right `.cspaceMint` and
`.cspaceCopy` gate on — and to change what the CNode holds.  MR1 addresses a
capability to the new **VSpace root**, held with `.write`, the right
`.vspaceMap` gates a change to an address space on.  Each must name an object of
its kind; the operation checks the kinds again against the store, so a resolver
and an operation that disagreed about them would refuse rather than install.
The slots are returned, not the objects: the operation copies each slot's
capability into the thread's slot, derived from it. -/
def resolveSetSpace (callerTid : SeLe4n.ThreadId)
    (args : SeLe4n.Kernel.Architecture.SyscallArgDecode.SetSpaceArgs) (st : SystemState) :
    Except KernelError (CSpaceAddr × CSpaceAddr) :=
  match resolveCallerCapSlot callerTid args.cspaceRoot .grant st with
  | .error e => .error e
  | .ok (cnSrc, cnCap, cnId) =>
    if !cnCap.hasRight .write then .error .illegalAuthority
    else if (st.getCNode? cnId).isNone then .error .invalidCapability
    else
      match resolveCallerCapSlot callerTid args.vspaceRoot .write st with
      | .error e => .error e
      | .ok (vrSrc, _, vrId) =>
        if (st.getVSpaceRoot? vrId).isNone then .error .invalidCapability
        else .ok (cnSrc, vrSrc)

/-- `resolveCallerCapSlot` in continuation form: the slot is resolved through
`resolveCapAddressKUnrolled` and handed on as its CNode's and slot's words, so no
gate, slot reference or result triple is built (`resolveCallerCapSlotK_eq`). -/
@[inline] def resolveCallerCapSlotK {α : Type} (callerTid : SeLe4n.ThreadId)
    (addr : SeLe4n.CPtr) (right : AccessRight) (st : SystemState)
    (onErr : KernelError → α)
    (onOk : SeLe4n.ObjId → SeLe4n.Slot → Capability → SeLe4n.ObjId → α) : α :=
  match st.getTcb? callerTid with
  | none => onErr .objectNotFound
  | some callerTcb =>
    match st.getCNode? callerTcb.cspaceRoot with
    | none => onErr .invalidCapability
    | some rootCn =>
      resolveCapAddressKUnrolled callerTcb.cspaceRoot addr rootCn.depth st onErr
        (fun cnode slot =>
          match SystemState.lookupSlotCap st { cnode := cnode, slot := slot } with
          | none => onErr .invalidCapability
          | some cap =>
            if SeLe4n.Kernel.capTargetsReservedIdleObject cap then onErr .invalidCapability
            else if cap.hasRight right then
              match cap.target with
              | .object oid => onOk cnode slot cap oid
              | _ => onErr .invalidCapability
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
    cases st.getCNode? callerTcb.cspaceRoot with
    | none => rfl
    | some rootCn =>
      simp only []
      rw [resolveCapAddressKUnrolled_eq, resolveCapAddressK_eq]
      cases resolveCapAddress callerTcb.cspaceRoot addr rootCn.depth st with
      | error e => rfl
      | ok ref =>
        obtain ⟨cnode, slot⟩ := ref
        simp only []
        cases SystemState.lookupSlotCap st { cnode := cnode, slot := slot } with
        | none => rfl
        | some cap =>
          simp only []
          by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true
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

/-- WS-ZA ZA6.4: `resolveSchedControlConfigureTarget` in continuation form,
through `resolveCallerCapObjectK`: no gate, slot reference, capability pair or
result cell is built, so the configure's resolution allocates nothing
(`resolveSchedControlConfigureTargetK_eq`). -/
@[inline] def resolveSchedControlConfigureTargetK {α : Type} (callerTid : SeLe4n.ThreadId)
    (core : Nat) (scCPtr : SeLe4n.CPtr) (st : SystemState) (onErr : KernelError → α)
    (onOk : SeLe4n.ValidObjId → α) : α :=
  resolveCallerCapObjectK callerTid scCPtr .write st onErr (fun _ scObjId =>
    match st.getSchedContext? (SchedContextId.ofObjId scObjId) with
    | none => onErr .invalidCapability
    | some _ =>
      if core < SeLe4n.Kernel.Concurrency.numCores then
        match validateObjIdArg scObjId with
        | .error e => onErr e
        | .ok v => onOk v
      else onErr .invalidCapability)

theorem resolveSchedControlConfigureTargetK_eq {α : Type} (callerTid : SeLe4n.ThreadId)
    (core : Nat) (scCPtr : SeLe4n.CPtr) (st : SystemState) (onErr : KernelError → α)
    (onOk : SeLe4n.ValidObjId → α) :
    resolveSchedControlConfigureTargetK callerTid core scCPtr st onErr onOk =
      match resolveSchedControlConfigureTarget callerTid core scCPtr st with
      | .error e => onErr e
      | .ok v => onOk v := by
  unfold resolveSchedControlConfigureTargetK
  rw [resolveCallerCapObjectK_eq]
  unfold resolveCallerCapObject resolveCallerCapSlot resolveSchedControlConfigureTarget
    syscallLookupCap syscallResolveCap
  cases st.getTcb? callerTid with
  | none => rfl
  | some callerTcb =>
    dsimp only
    cases st.getCNode? callerTcb.cspaceRoot with
    | none => rfl
    | some rootCn =>
      dsimp only
      cases resolveCapAddress callerTcb.cspaceRoot scCPtr rootCn.depth st with
      | error e => rfl
      | ok ref =>
        dsimp only
        cases SystemState.lookupSlotCap st ref with
        | none => rfl
        | some cap =>
          dsimp only
          by_cases hI : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true
          · simp only [hI, if_true]
          · simp only [hI, Bool.false_eq_true, ↓reduceIte]
            by_cases hR : cap.hasRight .write = true
            · simp only [hR, ↓reduceIte]
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
            · simp [hR]

/-- WS-ZA ZA5.2: `resolveSetSpace` in continuation form, through
`resolveCallerCapSlotK`, the two source slots handed on as words
(`resolveSetSpaceK_eq`). -/
@[inline] def resolveSetSpaceK {α : Type} (callerTid : SeLe4n.ThreadId)
    (args : SeLe4n.Kernel.Architecture.SyscallArgDecode.SetSpaceArgs) (st : SystemState)
    (onErr : KernelError → α)
    (onOk : SeLe4n.ObjId → SeLe4n.Slot → SeLe4n.ObjId → SeLe4n.Slot → α) : α :=
  resolveCallerCapSlotK callerTid args.cspaceRoot .grant st onErr (fun cnC cnS cnCap cnId =>
    if !cnCap.hasRight .write then onErr .illegalAuthority
    else if (st.getCNode? cnId).isNone then onErr .invalidCapability
    else
      resolveCallerCapSlotK callerTid args.vspaceRoot .write st onErr (fun vrC vrS _ vrId =>
        if (st.getVSpaceRoot? vrId).isNone then onErr .invalidCapability
        else onOk cnC cnS vrC vrS))

theorem resolveSetSpaceK_eq {α : Type} (callerTid : SeLe4n.ThreadId)
    (args : SeLe4n.Kernel.Architecture.SyscallArgDecode.SetSpaceArgs) (st : SystemState)
    (onErr : KernelError → α)
    (onOk : SeLe4n.ObjId → SeLe4n.Slot → SeLe4n.ObjId → SeLe4n.Slot → α) :
    resolveSetSpaceK callerTid args st onErr onOk =
      match resolveSetSpace callerTid args st with
      | .error e => onErr e
      | .ok (cnSrc, vrSrc) => onOk cnSrc.cnode cnSrc.slot vrSrc.cnode vrSrc.slot := by
  unfold resolveSetSpaceK resolveSetSpace
  rw [resolveCallerCapSlotK_eq]
  cases resolveCallerCapSlot callerTid args.cspaceRoot .grant st with
  | error e => rfl
  | ok p =>
    obtain ⟨cnSrc, cnCap, cnId⟩ := p
    simp only []
    by_cases hW : cnCap.hasRight .write = true
    · simp only [hW, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hC : (st.getCNode? cnId).isNone = true
      · simp only [hC, ↓reduceIte]
      · simp only [hC, Bool.false_eq_true, ↓reduceIte]
        rw [resolveCallerCapSlotK_eq]
        cases resolveCallerCapSlot callerTid args.vspaceRoot .write st with
        | error e => rfl
        | ok q =>
          obtain ⟨vrSrc, _, vrId⟩ := q
          simp only []
          by_cases hV : (st.getVSpaceRoot? vrId).isNone = true
          · simp only [hV, ↓reduceIte]
          · simp only [hV, Bool.false_eq_true, ↓reduceIte]
    · simp only [hW, Bool.not_false, ↓reduceIte]

/-- WS-ZA ZA5.4: `resolveVSpaceMapFrame` in continuation form: the frame
capability's slot is resolved once, through `resolveCapAddressKUnrolled`, and
handed on as its CNode and slot, so no gate, slot reference, capability pair or
result triple is built (`resolveVSpaceMapFrameK_eq`). -/
@[inline] def resolveVSpaceMapFrameK {α : Type} (callerTid : SeLe4n.ThreadId)
    (args : VSpaceMapArgs) (st : SystemState) (onErr : KernelError → α)
    (onOk : SeLe4n.ObjId → SeLe4n.Slot → Capability → FrameObject → α) : α :=
  match st.getTcb? callerTid with
  | none => onErr .objectNotFound
  | some callerTcb =>
    match st.getCNode? callerTcb.cspaceRoot with
    | none => onErr .invalidCapability
    | some rootCn =>
      resolveCapAddressKUnrolled callerTcb.cspaceRoot args.frame rootCn.depth st onErr
        (fun cnode slot =>
          match SystemState.lookupSlotCap st { cnode := cnode, slot := slot } with
          | none => onErr .invalidCapability
          | some cap =>
            if SeLe4n.Kernel.capTargetsReservedIdleObject cap then onErr .invalidCapability
            else if cap.hasRight .read then
              match cap.target with
              | .object frameObjId =>
                match st.getFrame? frameObjId with
                | none => onErr .invalidCapability
                | some frame => onOk cnode slot cap frame
              | _ => onErr .invalidCapability
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
    cases st.getCNode? callerTcb.cspaceRoot with
    | none => rfl
    | some rootCn =>
      simp only [syscallLookupCap, syscallResolveCap]
      rw [resolveCapAddressKUnrolled_eq, resolveCapAddressK_eq]
      cases hRes : resolveCapAddress callerTcb.cspaceRoot args.frame rootCn.depth st with
      | error e => rfl
      | ok ref =>
        obtain ⟨cnode, slot⟩ := ref
        simp only []
        cases SystemState.lookupSlotCap st { cnode := cnode, slot := slot } with
        | none => rfl
        | some cap =>
          simp only []
          by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true
          · simp only [hIdle, ↓reduceIte]
          · by_cases hR : cap.hasRight .read = true
            · simp only [hIdle, hR, Bool.false_eq_true, ↓reduceIte]
              cases cap.target with
              | object fid =>
                simp only []
                cases st.getFrame? fid with
                | none => rfl
                | some frame => simp only [hRes]
              | _ => rfl
            · simp only [hIdle, hR, Bool.false_eq_true, ↓reduceIte]

/-- **The authority fact the `.tcbSetSpace` arm rests on**: the CSpace root's
source is a slot of the caller's CSpace holding a capability with `.grant` and
`.write` to a CNode, and the VSpace root's a slot holding a capability with
`.write` to a VSpace root. -/
theorem resolveSetSpace_ok_authorised (callerTid : SeLe4n.ThreadId)
    (args : SeLe4n.Kernel.Architecture.SyscallArgDecode.SetSpaceArgs) (st : SystemState)
    (cnSrc vrSrc : CSpaceAddr) (h : resolveSetSpace callerTid args st = .ok (cnSrc, vrSrc)) :
    (∃ cnCap cnId, resolveCallerCapSlot callerTid args.cspaceRoot .grant st = .ok (cnSrc, cnCap, cnId) ∧
        SystemState.lookupSlotCap st cnSrc = some cnCap ∧ cnCap.target = .object cnId ∧
        cnCap.hasRight .grant = true ∧ cnCap.hasRight .write = true ∧ (st.getCNode? cnId).isSome) ∧
      (∃ vrCap vrId, resolveCallerCapSlot callerTid args.vspaceRoot .write st = .ok (vrSrc, vrCap, vrId) ∧
        SystemState.lookupSlotCap st vrSrc = some vrCap ∧ vrCap.target = .object vrId ∧
        vrCap.hasRight .write = true ∧ (st.getVSpaceRoot? vrId).isSome) := by
  unfold resolveSetSpace at h
  cases hC : resolveCallerCapSlot callerTid args.cspaceRoot .grant st with
  | error e => rw [hC] at h; cases h
  | ok p =>
    obtain ⟨cn, cnCap, cnId⟩ := p
    rw [hC] at h
    simp only at h
    by_cases hW : cnCap.hasRight .write = true
    · have hB : (!cnCap.hasRight .write) = false := by simp [hW]
      rw [hB] at h
      cases hCn : st.getCNode? cnId with
      | none => simp [hCn] at h
      | some _ =>
        simp only [hCn, Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at h
        cases hV : resolveCallerCapSlot callerTid args.vspaceRoot .write st with
        | error e => rw [hV] at h; cases h
        | ok q =>
          obtain ⟨vr, vrCap, vrId⟩ := q
          rw [hV] at h
          simp only at h
          cases hVr : st.getVSpaceRoot? vrId with
          | none => simp [hVr] at h
          | some _ =>
            simp only [hVr, Option.isNone_some, Bool.false_eq_true, ↓reduceIte,
              Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨_, _, _, _, _, hLc, hG, hTc⟩ := resolveCallerCapSlot_ok callerTid _ _ st _ _ _ hC
            obtain ⟨_, _, _, _, _, hLv, hVW, hTv⟩ := resolveCallerCapSlot_ok callerTid _ _ st _ _ _ hV
            exact ⟨⟨cnCap, cnId, rfl, hLc, hTc, hG, hW, by simp [hCn]⟩,
              ⟨vrCap, vrId, rfl, hLv, hTv, hVW, by simp [hVr]⟩⟩
    · have hB : (!cnCap.hasRight .write) = true := by simpa using hW
      rw [hB] at h; cases h

/-- **WS-BP BP7.1 (`v0.36.5`): the two slots a carve names, resolved through the
caller's own CSpace.**

The *source* is the slot the syscall's own capability was resolved from — the
caller's CSpace root, the invoked address, the root's depth, which is exactly the
resolution `syscallResolveCap` performed — so the untyped capability the carve
checks and records its derivation from is the one the caller presented.  The
*destination* CNode is MR2, resolved with `.write`, as `resolveVSpaceMapFrame`
resolves its frame: a carve installs a capability, and installing into a CNode is
writing it, so a caller can deposit the new capability only in a CNode it holds a
writable capability to.  The destination slot is MR3 verbatim — the install
primitive refuses an index its CNode cannot address. -/
def resolveUntypedRetype (callerTid : SeLe4n.ThreadId) (srcAddr : SeLe4n.CPtr)
    (args : UntypedRetypeArgs) (st : SystemState) :
    Except KernelError (CSpaceAddr × CSpaceAddr) :=
  match st.getTcb? callerTid with
  | none => .error .objectNotFound
  | some callerTcb =>
    match st.getCNode? callerTcb.cspaceRoot with
    | none => .error .invalidCapability
    | some rootCn =>
      match resolveCapAddress callerTcb.cspaceRoot srcAddr rootCn.depth st with
      | .error e => .error e
      | .ok src =>
        let dstGate : SyscallGate := {
          callerId      := callerTid
          cspaceRoot    := callerTcb.cspaceRoot
          capAddr       := args.dstCNode
          capDepth      := rootCn.depth
          requiredRight := .write
        }
        match syscallLookupCap dstGate st with
        | .error e => .error e
        | .ok (dstCap, _) =>
          match dstCap.target with
          | .object cnodeId =>
            match st.getCNode? cnodeId with
            | none => .error .invalidCapability
            | some _ => .ok (src, { cnode := cnodeId, slot := args.dstSlot })
          | _ => .error .invalidCapability

/-- WS-ZA ZA5.4: `resolveUntypedRetype` in continuation form: the source slot
through `resolveCapAddressKUnrolled` and the destination CNode through
`resolveCallerCapObjectK`, each handed on as words, so no slot reference, pair or
result cell is built (`resolveUntypedRetypeK_eq`). -/
@[inline] def resolveUntypedRetypeK {α : Type} (callerTid : SeLe4n.ThreadId)
    (srcAddr : SeLe4n.CPtr) (args : UntypedRetypeArgs) (st : SystemState)
    (onErr : KernelError → α)
    (onOk : SeLe4n.ObjId → SeLe4n.Slot → SeLe4n.ObjId → SeLe4n.Slot → α) : α :=
  match st.getTcb? callerTid with
  | none => onErr .objectNotFound
  | some callerTcb =>
    match st.getCNode? callerTcb.cspaceRoot with
    | none => onErr .invalidCapability
    | some rootCn =>
      resolveCapAddressKUnrolled callerTcb.cspaceRoot srcAddr rootCn.depth st onErr
        (fun srcCnode srcSlot =>
          resolveCallerCapObjectK callerTid args.dstCNode .write st onErr (fun _ cnodeId =>
            match st.getCNode? cnodeId with
            | none => onErr .invalidCapability
            | some _ => onOk srcCnode srcSlot cnodeId args.dstSlot))

theorem resolveUntypedRetypeK_eq {α : Type} (callerTid : SeLe4n.ThreadId)
    (srcAddr : SeLe4n.CPtr) (args : UntypedRetypeArgs) (st : SystemState)
    (onErr : KernelError → α)
    (onOk : SeLe4n.ObjId → SeLe4n.Slot → SeLe4n.ObjId → SeLe4n.Slot → α) :
    resolveUntypedRetypeK callerTid srcAddr args st onErr onOk =
      match resolveUntypedRetype callerTid srcAddr args st with
      | .error e => onErr e
      | .ok (src, dst) => onOk src.cnode src.slot dst.cnode dst.slot := by
  unfold resolveUntypedRetypeK resolveUntypedRetype
  cases hT : st.getTcb? callerTid with
  | none => rfl
  | some callerTcb =>
    simp only []
    cases hC : st.getCNode? callerTcb.cspaceRoot with
    | none => rfl
    | some rootCn =>
      simp only []
      rw [resolveCapAddressKUnrolled_eq, resolveCapAddressK_eq]
      cases resolveCapAddress callerTcb.cspaceRoot srcAddr rootCn.depth st with
      | error e => rfl
      | ok src =>
        simp only []
        rw [resolveCallerCapObjectK_eq]
        unfold resolveCallerCapObject resolveCallerCapSlot
        simp only [hT, hC, syscallLookupCap, syscallResolveCap]
        cases resolveCapAddress callerTcb.cspaceRoot args.dstCNode rootCn.depth st with
        | error e => rfl
        | ok dst =>
          simp only []
          cases SystemState.lookupSlotCap st dst with
          | none => rfl
          | some dstCap =>
            simp only []
            by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject dstCap = true
            · simp only [hIdle, ↓reduceIte]
            · by_cases hR : dstCap.hasRight .write = true
              · simp only [hIdle, hR, Bool.false_eq_true, ↓reduceIte]
                cases dstCap.target with
                | object cnodeId =>
                  simp only []
                  cases st.getCNode? cnodeId <;> rfl
                | _ => rfl
              · simp only [hIdle, hR, Bool.false_eq_true, ↓reduceIte]

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
  | .frame => if sizeBits = 0 then .ok .frame else .error .invalidArgument
  -- WS-BP BP7.1 (`v0.36.12`): a page table is one page, like a frame.
  | .pageTable => if sizeBits = 0 then .ok .pageTable else .error .invalidArgument
  | .untyped =>
      if minUntypedSizeBits ≤ sizeBits ∧ sizeBits ≤ maxUntypedSizeBits then
        .ok (.untyped sizeBits)
      else .error .invalidArgument
  | .vspaceRoot =>
      if sizeBits = 0 then
        match freshAsid? st with
        | some asid => .ok (.vspaceRoot asid)
        | none => .error .resourceExhausted
      else .error .invalidArgument
  | .tcb =>
      if sizeBits = 0 then
        .ok (.tcb (st.scheduler.activeDomainOnCore executingCore) executingCore)
      else .error .invalidArgument
  | .endpoint => if sizeBits = 0 then .ok .endpoint else .error .invalidArgument
  | .notification => if sizeBits = 0 then .ok .notification else .error .invalidArgument
  | .reply => if sizeBits = 0 then .ok .reply else .error .invalidArgument
  | .cnode =>
      if hB : minCNodeRadixBits ≤ sizeBits ∧ sizeBits ≤ maxCNodeRadixBits then
        .ok (.cnode sizeBits (Nat.le_trans hB.2 maxCNodeRadixBits_le_maxCSpaceDepth))
      else .error .invalidArgument
  | .schedContext =>
      if minSchedContextSizeBits ≤ sizeBits ∧ sizeBits ≤ maxUntypedSizeBits then
        .ok (.schedContext sizeBits)
      else .error .invalidArgument

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

/-- **WS-BP BP7.1 (`v0.36.5`, child untypeds at slice 4, `v0.36.8`): the live
`.untypedRetype` arm's transition** — seL4's `seL4_Untyped_Retype`, at every
object kind since WS-ZA ZA5.4 part 14.

The arm's decode of the message registers (`args?`), then the carve request
(`carveRequestOf?`: each kind at its size bounds, a VSpace root under a fresh
ASID and a thread in the creating core's domain — anything else
`.invalidArgument`).  The
child id is a raw operand, so it passes `validateObjIdArg` — no reserved idle object and not
the sentinel — before anything is resolved.  Then the two slots, then
`untypedRetypeObject`, whose own guards decide everything else. -/
def untypedRetypeFromCap (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (srcAddr : SeLe4n.CPtr) (args? : Except KernelError UntypedRetypeArgs) : Kernel Unit :=
  fun st =>
    match args? with
    | .error e => .error e
    | .ok args =>
      match carveRequestOf? st executingCore args.newType args.sizeBits with
      | .error e => .error e
      | .ok req =>
        match validateObjIdArg args.childId with
        | .error e => .error e
        | .ok vChild =>
          match resolveUntypedRetype tid srcAddr args st with
          | .error e => .error e
          | .ok (src, dst) => untypedRetypeObject src vChild.val dst req st

/-- **WS-BP BP7.1**: what a successful `.untypedRetype` consists of — the typed
decode, the carve request, the validated child id, the resolved slots, and the
carve.  The case analysis has one owner, so the invariant and non-interference
proofs read these equations. -/
theorem untypedRetypeFromCap_ok (tid : SeLe4n.ThreadId) (ec : Concurrency.CoreId)
    (srcAddr : SeLe4n.CPtr)
    (args? : Except KernelError UntypedRetypeArgs) (st st' : SystemState)
    (h : untypedRetypeFromCap tid ec srcAddr args? st = .ok ((), st')) :
    ∃ (args : UntypedRetypeArgs) (req : CarveRequest) (vChild : SeLe4n.ValidObjId)
      (src dst : CSpaceAddr),
      args? = .ok args ∧
      carveRequestOf? st ec args.newType args.sizeBits = .ok req ∧
      validateObjIdArg args.childId = .ok vChild ∧
      resolveUntypedRetype tid srcAddr args st = .ok (src, dst) ∧
      untypedRetypeObject src vChild.val dst req st = .ok ((), st') := by
  unfold untypedRetypeFromCap at h
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
        cases hR : resolveUntypedRetype tid srcAddr args st with
        | error e => rw [hR] at h; cases h
        | ok pr =>
          obtain ⟨src, dst⟩ := pr
          rw [hR] at h
          exact ⟨args, req, vChild, src, dst, by first | exact hD | rfl,
            by first | exact hQ | rfl,
            by first | exact hV | rfl, by first | exact hR | rfl, h⟩

/-- **WS-ZA ZA5.4 part 17: the `.untypedRetype` arm preserves the capability
bundle** — the carve keeps every conjunct
(`untypedRetypeObject_preserves_capabilityInvariantBundle`) of whatever request
the decode built. -/
theorem untypedRetypeFromCap_preserves_capabilityInvariantBundle (tid : SeLe4n.ThreadId)
    (ec : Concurrency.CoreId) (srcAddr : SeLe4n.CPtr)
    (args? : Except KernelError UntypedRetypeArgs) (st st' : SystemState)
    (hInv : capabilityInvariantBundle st)
    (h : untypedRetypeFromCap tid ec srcAddr args? st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  obtain ⟨_, req, _, _, _, _, _, _, _, hCarve⟩ := untypedRetypeFromCap_ok tid ec srcAddr args? st st' h
  exact untypedRetypeObject_preserves_capabilityInvariantBundle _ _ _ req st st' hInv hCarve

/-- WS-ZA ZA5.4: **`.untypedReset` on the invoked slot.**  The free index is in
the invoked capability, so the arm resolves the capability address to its slot
again (the dispatcher's lookup returns the capability, not where it sits), with
the right the dispatcher demanded, and resets through that slot
(`untypedResetSlot`, seL4's `resetUntypedCap` behind `ensureNoChildren`).  The
resolution reads the state the dispatcher's lookup read, so it finds the same
slot and capability. -/
def untypedResetFromCap (tid : SeLe4n.ThreadId) (srcAddr : SeLe4n.CPtr) : Kernel Unit :=
  fun st =>
    resolveCallerCapSlotK tid srcAddr .retype st (fun e => .error e)
      (fun srcCnode srcSlot _ _ => untypedResetSlot srcCnode srcSlot st)

/-- **What a successful `.untypedReset` consists of**: the resolved slot holds a
capability, and the slot reset succeeded on it. -/
theorem untypedResetFromCap_ok (tid : SeLe4n.ThreadId) (srcAddr : SeLe4n.CPtr)
    (st st' : SystemState) (h : untypedResetFromCap tid srcAddr st = .ok ((), st')) :
    ∃ (src : CSpaceAddr) (cap : Capability) (cn : CNode),
      st.objects[src.cnode]? = some (.cnode cn) ∧ cn.lookup src.slot = some cap ∧
      untypedResetSlot src.cnode src.slot st = .ok ((), st') := by
  unfold untypedResetFromCap at h
  rw [resolveCallerCapSlotK_eq] at h
  cases hR : resolveCallerCapSlot tid srcAddr .retype st with
  | error e => rw [hR] at h; cases h
  | ok r =>
    obtain ⟨src, cap, oid⟩ := r
    rw [hR] at h
    obtain ⟨-, -, -, -, -, hLk, -, -⟩ := resolveCallerCapSlot_ok tid srcAddr .retype st src cap oid hR
    obtain ⟨cn, hO, hL⟩ := SystemState.lookupSlotCap_cnode hLk
    exact ⟨src, cap, cn, hO, hL, h⟩

/-- WS-ZA ZA5.4 part 36: **the live `.untypedReset` arm preserves the capability
bundle** — the slot reset's (`untypedResetSlot_preserves_capabilityInvariantBundle`). -/
theorem untypedResetFromCap_preserves_capabilityInvariantBundle (tid : SeLe4n.ThreadId)
    (srcAddr : SeLe4n.CPtr) (st st' : SystemState) (hInv : capabilityInvariantBundle st)
    (h : untypedResetFromCap tid srcAddr st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  obtain ⟨_, _, _, -, -, hS⟩ := untypedResetFromCap_ok tid srcAddr st st' h
  exact untypedResetSlot_preserves_capabilityInvariantBundle hInv hS

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
    ∃ (callerTcb : TCB) (rootCn : CNode) (frameObjId : SeLe4n.ObjId),
      st.getTcb? callerTid = some callerTcb ∧
      st.getCNode? callerTcb.cspaceRoot = some rootCn ∧
      syscallLookupCap
        { callerId := callerTid, cspaceRoot := callerTcb.cspaceRoot,
          capAddr := args.frame, capDepth := rootCn.depth,
          requiredRight := .read } st = .ok (frameCap, st) ∧
      frameCap.hasRight .read = true ∧
      frameCap.target = .object frameObjId ∧
      st.getFrame? frameObjId = some frame ∧
      resolveCapAddress callerTcb.cspaceRoot args.frame rootCn.depth st = .ok frameSlot ∧
      SystemState.lookupSlotCap st frameSlot = some frameCap := by
  unfold resolveVSpaceMapFrame at h
  cases hCaller : st.getTcb? callerTid with
  | none => rw [hCaller] at h; cases h
  | some callerTcb =>
    rw [hCaller] at h
    simp only at h
    cases hRoot : st.getCNode? callerTcb.cspaceRoot with
    | none => rw [hRoot] at h; cases h
    | some rootCn =>
      rw [hRoot] at h
      simp only at h
      cases hLk : syscallLookupCap
          { callerId := callerTid, cspaceRoot := callerTcb.cspaceRoot,
            capAddr := args.frame, capDepth := rootCn.depth,
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
        have hSlotOf : ∀ ref, resolveCapAddress callerTcb.cspaceRoot args.frame
            rootCn.depth st = .ok ref → SystemState.lookupSlotCap st ref = some cap' := by
          intro ref hRef
          have : ref0 = ref := by
            have h2 : (Except.ok ref0 : Except KernelError CSpaceAddr) = .ok ref :=
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
            cases hRef : resolveCapAddress callerTcb.cspaceRoot args.frame rootCn.depth st with
            | error e => rw [hRef] at h; cases h
            | ok ref =>
              rw [hRef] at h
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨hS, hCap, hFr⟩ := h
              subst hS; subst hCap; subst hFr
              exact ⟨callerTcb, rootCn, frameObjId,
                by first | exact hCaller | rfl,
                by first | exact hRoot | rfl,
                hLk, hRight, hTgt, hF, hRef, hSlotOf _ hRef⟩
        all_goals (rw [hTgt] at h; cases h)

/-- **WS-BP BP7.1: what a frame capability authorises a mapping to do.**

Two refusals, each the fact a hardware mapping of this frame would otherwise
violate.  (W^X needs no third: the decode already refuses a writable-and-
executable request, through `PagePermissions.ofNat?`.)  A **writable** mapping needs a frame capability carrying `.write` —
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

Resolve the frame MR2's capability names (`resolveVSpaceMapFrame`), check what
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
        else if capabilityMappingLive st frameCap then .error .invalidCapability
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
  obtain ⟨_, _, _, _, _, _, _, _, _, -, hSlotCap⟩ :=
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

/-- V8-H/Z5-J/D1/AE1-A/AE1-B: Shared dispatch for capability-only syscalls — these arms
derive authority entirely from capability possession and require no
information-flow checks. Both `dispatchWithCap` and `dispatchWithCapChecked`
delegate to this helper for: `.cspaceDelete`, `.vspaceMap`,
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
    | _ => fun _ => .error .invalidCapability
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
    | _ => fun _ => .error .invalidCapability
  -- PR #822 Phase H: mint a reply cap from an `.object`-to-Reply cap.  Same src/dst-slot
  -- ABI as `cspaceCopy` (reuses `decodeCSpaceCopyArgs`); the cap names the CNode, and
  -- `mintReplyCapWithCdt` derives `.replyCap (ReplyId.ofObjId target)` at the dst slot
  -- (fail-closed when the src is not an `.object`-to-Reply cap).  CDT-tracked so the
  -- minted reply cap is revocable through `.cspaceRevoke`.
  | .mintReplyCap =>
    some <| match cap.target with
    | .object cnodeId =>
        fun st => match decodeCSpaceCopyArgs decoded with
        | .error e => .error e
        | .ok args =>
            if !cnodeInvoked cnodeId st then .error .objectNotFound else
            let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
            let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
            mintReplyCapWithCdt src dst st
    | _ => fun _ => .error .invalidCapability
  -- **WS-BP BP7.1 (`v0.36.5`)**: `seL4_Untyped_Retype` — the only path by
  -- which an object comes to exist on a live state (since WS-ZA ZA5.4 part 14
  -- every kind, as in seL4): the caller presents an untyped capability, names a
  -- fresh object id and an empty slot in a CNode it can write, and receives a
  -- capability to the object carved at that capability's free index.
  -- `.vspaceMap` maps a carved frame and no other page.
  | .untypedRetype =>
    some <| match cap.target with
    | .object _ =>
        untypedRetypeFromCap tid executingCore decoded.capAddr (decodeUntypedRetypeArgs decoded)
    | _ => fun _ => .error .invalidCapability
  -- **WS-BP BP7.1 (`v0.36.6`)**: seL4's `resetUntypedCap`.  The free index is the
  -- invoked capability's, so the arm resets through the invoked slot
  -- (`untypedResetFromCap`): refused while that slot has a derivation child or
  -- its untyped records a carved object, and otherwise its free index is
  -- rewound to 0.  Takes no message registers: the capability is the whole
  -- operand.
  | .untypedReset =>
    some <| match cap.target with
    | .object _ => untypedResetFromCap tid decoded.capAddr
    | _ => fun _ => .error .invalidCapability
  | .vspaceMap =>
    some <| match cap.target with
    | .object _ =>
        -- AH3-C (L-14): Pass platform-configured maxASID to decode.
        -- WS-BP BP7.1: MR2 is a frame capability address, so there is no
        -- decode-time physical address to bound (AK3-E's checked decode is
        -- retired); the physical-address bound applies to the resolved frame's
        -- `base` inside `vspaceMapPageCheckedWithFlushFromState`.
        fun st =>
          match decodeVSpaceMapArgs decoded st.machine.maxASID with
          | .error e => .error e
          | .ok args =>
            -- PR #845 review (P1): bind the capability to the operand address
            -- space.  `syscallLookupCap` proved only that the caller holds
            -- *some* capability carrying `.write`; the ASID arrives in a
            -- message register, so without this a holder of any writable object
            -- capability could map into an arbitrary address space.  Checked
            -- before the permission validation so an unauthorized caller does
            -- no further work and learns nothing about the target.
            if !vspaceCapAuthorizesAsid cap args.asid st then
              .error .illegalAuthority
            else
              -- WS-BP BP7.1: the page mapped is the frame MR2's capability names,
              -- resolved through the caller's own CSpace; its address is the
              -- frame's own `base`, never a register value.
              vspaceMapFromFrameCap tid executingCore args st
    | _ => fun _ => .error .invalidCapability
  | .vspaceUnmap =>
    some <| match cap.target with
    | .object _ =>
        -- AH3-C (L-14): Pass platform-configured maxASID to decode
        fun st => match decodeVSpaceUnmapArgs decoded st.machine.maxASID with
        | .error e => .error e
        | .ok args =>
          -- PR #845 review (P1): bind the capability to the operand address
          -- space.  Without this a holder of any writable object capability —
          -- its own TCB, say — could tear down mappings in an arbitrary address
          -- space, since the ASID is caller-supplied and the rights gate above
          -- never looks at what the capability names.
          if !vspaceCapAuthorizesAsid cap args.asid st then
            .error .illegalAuthority
          else
            -- WS-SM SM7.B.9: the SMP-C4 use-after-unmap closure — local
            -- flush + `.vae1` shootdown round to every other core.  WS-SM
            -- SM7.F.4(b)(i): route through the initiator-atomic per-core
            -- wrapper so the caller's own `perCoreTlb` view retires the
            -- unmapped operand *atomically* with the transition (rather than
            -- only in the deferred `completeShootdownRounds` catch-up),
            -- closing the transient committed-state window where the
            -- initiator's view would be stale-and-uncovered.  Trace-safe:
            -- `perCoreTlb` ∉ `projectState`, and the extra drain touches no
            -- field the SGI/round diff-recovery reads (`tlbShootdown`).
            -- WS-SM SM7.D.1: and through the instruction-cache seam on top,
            -- which broadcasts a targeted `IC IVAU` over the shareability
            -- domain when the *retired mapping was executable* — otherwise a
            -- core could keep fetching the previous owner's instructions from
            -- its own instruction cache after the frame is re-purposed (the
            -- instruction-side twin of the SMP-C4 stale-TLB hazard; the TLB
            -- round does not close it, because instruction caches are tagged
            -- by physical address, not by translation).  A non-executable
            -- unmap owes nothing and is provably inert.
            Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast
              executingCore args.asid args.vaddr st
    | _ => fun _ => .error .invalidCapability
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
    | _ => fun _ => .error .invalidCapability
  | .serviceRevoke =>
    -- The revoke removes the registration the invoked endpoint records: the
    -- capability to the endpoint is the authority, and no service id is read
    -- from the caller's registers (`revokeServiceByRecordedRegistration`).
    some <| match cap.target with
    | .object epId => fun st => revokeServiceByRecordedRegistration epId st
    | _ => fun _ => .error .invalidCapability
  | .serviceQuery =>
    some <| match cap.target with
    | .object epId =>
      fun st =>
        match lookupServiceByRecordedRegistration epId st with
        | .ok (reg, st') =>
            -- WS-RA RA.B.7: the query answers — the resolved registration's
            -- `ServiceId` is staged as the caller's return word instead of
            -- being discarded (`x0` = sid, success `x1`, no message
            -- registers).  The lookup itself is read-only (`st' = st`).
            .ok ((), Architecture.writeReturnFrameToTcb st' tid
              (Architecture.returnFrameOfWord reg.sid.val.toUInt64))
        | .error e => .error e
    | _ => fun _ => .error .invalidCapability
  -- Z5-J: SchedContext configure — decode args, validate, configure
  -- AK3-J (A-M07 / MEDIUM): Use `decodeSchedContextConfigureArgsChecked` to
  -- enforce priority ≤ 255, domain < 16, budget > 0, period > 0 at decode
  -- time (prevents malformed CBS servers before scheduler subsystem).
  --
  -- WS-ZA ZA6.4: the configure is invoked on core `core`'s SCHEDULING CONTROL
  -- capability, seL4-MCS's `SchedControl`, the one authority to set a context's
  -- budget and period; the context is a capability at MR0
  -- (`resolveSchedControlConfigureTarget`).  A scheduling-context capability
  -- configures nothing: a holder of one could otherwise reset the budget it was
  -- handed, period after period.
  | .schedContextConfigure =>
    some <| match cap.target with
    | .schedControl core =>
      fun st => match decodeSchedContextConfigureArgsChecked decoded with
      | .error e => .error e
      | .ok args =>
          -- AL7-G / WS-AL AL8 (cascades AK7-E): type-level sentinel rejection
          -- via the ValidObjId signature on schedContextConfigure; the
          -- context's promotion is the resolver's.
          match resolveSchedControlConfigureTarget tid core args.scCPtr st with
          | .error e => .error e
          | .ok vScId =>
              -- The configure runs on the control's core, moving a context
              -- homed elsewhere there with its thread (seL4's
              -- `invokeSchedControl_ConfigureFlags`).
              if hCore : core < SeLe4n.Kernel.Concurrency.numCores then
                SchedContextOps.schedControlConfigure ⟨core, hCore⟩ vScId args.budget
                  args.period args.priority args.deadline args.domain st
              else .error .invalidCapability
    | _ => fun _ => .error .invalidCapability
  -- Z5-J: SchedContext bind — the SchedContext from the capability target, the
  -- thread from a TCB CAPABILITY the caller holds (`v0.35.204`; a raw thread id
  -- until then — see `resolveSchedContextBindThread` for what that let a
  -- SchedContext-capability holder do to a thread it held no authority over).
  | .schedContextBind =>
    some <| match cap.target with
    | .object scId =>
      fun st => match resolveSchedContextBindThread tid (decodeSchedContextBindArgs decoded) st with
      | .error e => .error e
      | .ok vThreadId =>
          -- AL7-H / WS-AL AL8 (cascades AK7-E): type-level sentinel rejection
          -- via the ValidObjId signature on schedContextBind; the thread's
          -- promotion is the resolver's.
          match validateObjIdArg scId with
          | .error e => .error e
          | .ok vScId =>
              SchedContextOps.schedContextBind vScId vThreadId st
    | _ => fun _ => .error .invalidCapability
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
              -- WS-SM SM8.B (PR #861 review round 15): route through the
              -- **per-core** unbind.  Revoking a SchedContext demotes its bound
              -- thread to the legacy TCB priority, and the single-core form
              -- cleared that thread's `current` slot without any scheduling
              -- point — nothing in `syscallDispatchCrossCoreEntry` reschedules
              -- locally, and `crossCoreSgiBody` deliberately emits nothing for
              -- the executing core — so a thread that unbound its own
              -- SchedContext kept running while the model said its core had no
              -- current thread, so its next syscall is refused outright
              -- (`vacatedCore_next_syscall_rejected`; round 43 corrected this
              -- note, which claimed a boot-core misroute — that fallback sits
              -- behind caller resolution and is never reached).
              match SchedContextOps.schedContextUnbindOnCore vScId
                  executingCore st with
              | .ok (st', _) => .ok ((), st')
              | .error e => .error e
    | _ => fun _ => .error .invalidCapability
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
    | _ => fun _ => .error .invalidCapability
  -- WS-SM SM6.B: bind a notification to the capability-target TCB (seL4
  -- NotificationBind).  Cap target = the TCB; msgRegs[0] = the notification ObjId.
  | .tcbBindNotification =>
    some <| match cap.target with
    | .object tcbObjId =>
      fun st => match decodeTcbBindNotificationArgs decoded with
      | .error e => .error e
      | .ok args =>
          -- WS-SM SM6.B (review #1): resolve the notification through a CAPABILITY in
          -- the caller's CSpace (seL4 BindNotification takes a notification cap), not a
          -- raw ObjId.  A TCB-cap holder must *also* hold a notification capability
          -- (Write) to redirect that notification's signals — otherwise it could hijack
          -- or deny any notification merely by naming its ObjId.  `bindNotification`
          -- still rejects a resolved cap whose target is not a notification object.
          -- Typed accessors (AK7 cascade discipline): `getTcb?` / `getCNode?`
          -- instead of raw `st.objects[…]?` matches.
          match st.getTcb? tid with
          | some callerTcb =>
            match st.getCNode? callerTcb.cspaceRoot with
            | some rootCn =>
              let ntfnGate : SyscallGate := {
                callerId      := tid
                cspaceRoot    := callerTcb.cspaceRoot
                capAddr       := args.notificationCPtr
                capDepth      := rootCn.depth
                requiredRight := .write
              }
              match syscallLookupCap ntfnGate st with
              | .error e => .error e
              | .ok (ntfnCap, _) =>
                match ntfnCap.target with
                | .object notifId =>
                    bindNotification notifId (SeLe4n.ThreadId.ofNat tcbObjId.toNat) st
                | _ => .error .invalidCapability
            | none => .error .invalidCapability
          | none => .error .objectNotFound
    | _ => fun _ => .error .invalidCapability
  -- WS-SM SM6.B: unbind the capability-target TCB's bound notification.
  | .tcbUnbindNotification =>
    some <| match cap.target with
    | .object tcbObjId =>
      fun st =>
        match unbindNotification (SeLe4n.ThreadId.ofNat tcbObjId.toNat) st with
        | .error e => .error e
        | .ok ((), st') => .ok ((), st')
    | _ => fun _ => .error .invalidCapability
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
    | _ => fun _ => .error .invalidCapability
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
        match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | .error e => .error e
        | .ok vtid =>
            match Lifecycle.Suspend.resumeThreadOnCore
                (retirePendingFaultForResume st vtid.val) vtid
                executingCore with
            | .ok (st', _) => .ok ((), st')
            | .error e => .error e
    | _ => fun _ => .error .invalidCapability
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
        match validateThreadIdArg tid with
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
    | _ => fun _ => .error .invalidCapability
  -- AE1-A: D2-K TCB setMCPriority — MCP from message register, target from capability
  | .tcbSetMCPriority =>
    some <| match cap.target with
    | .object objId =>
      fun st => match decodeSetMCPriorityArgs decoded with
      | .error e => .error e
      | .ok args =>
        -- AL7-E / WS-AL AL8 (cascades AK7-E): type-level sentinel rejection
        -- via ValidThreadId signature on setMCPriorityOp.
        match validateThreadIdArg tid with
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
    | _ => fun _ => .error .invalidCapability
  -- AE1-B: D3-H TCB setIPCBuffer — buffer address from message register, target from capability
  -- Moved here from duplicate arms in both dispatch paths (U-06 fix).
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
            match Architecture.IpcBufferValidation.setIPCBufferOp st
                vtid args.bufferAddr with
            | .ok st' => .ok ((), st')
            | .error e => .error e
    | _ => fun _ => .error .invalidCapability
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
    | _ => fun _ => .error .invalidCapability
  -- Review round (PR #887): `seL4_TCB_SetSpace`'s fault endpoint.  The CPtr
  -- is interpreted in the *target* thread's CSpace and validated at set time
  -- by the same resolution the fault path runs (`resolveFaultHandlerCPtr`),
  -- so a handler that could never be delivered to is refused here rather than
  -- discovered as a suspended thread later.  Authority: the write right on the
  -- target TCB capability, like every other thread-configuration arm.
  | .tcbSetFaultHandler =>
    some <| match cap.target with
    | .object objId =>
      fun st => match Architecture.SyscallArgDecode.decodeSetFaultHandlerArgs decoded with
      | .error e => .error e
      | .ok args =>
        match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | .error e => .error e
        | .ok vtid =>
            match setThreadFaultHandlerOp st vtid args.handlerCPtr with
            | .ok st' => .ok ((), st')
            | .error e => .error e
    | _ => fun _ => .error .invalidCapability
  -- **WS-BP BP7.1 (`v0.36.11`)**: `seL4_TCB_SetSpace` — the target from the
  -- invoked TCB capability (with the write right), the two roots from MR0/MR1
  -- resolved through the *caller's* CSpace (`resolveSetSpace`).  The target must
  -- be suspended: the operation refuses a thread whose spaces are in use.
  | .tcbSetSpace =>
    some <| match cap.target with
    | .object objId =>
      fun st => match Architecture.SyscallArgDecode.decodeSetSpaceArgs decoded with
      | .error e => .error e
      | .ok args =>
        match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | .error e => .error e
        | .ok vtid =>
            match resolveSetSpace tid args st with
            | .error e => .error e
            | .ok (cnSrc, vrSrc) =>
                match copyThreadSpacesZombie executingCore st vtid cnSrc vrSrc with
                | .ok st' => .ok ((), st')
                | .error e => .error e
    | _ => fun _ => .error .invalidCapability
  -- **WS-BP BP7.1 (`v0.36.12`)**: `seL4_ARM_PageTable_Map` — the table from the
  -- invoked capability (with the write right), the address space from MR0
  -- resolved through the *caller's* CSpace with `.write`, the address from MR1.
  | .pageTableMap =>
    some <| match cap.target with
    | .object objId =>
      fun st => match Architecture.SyscallArgDecode.decodePageTableMapArgs decoded with
      | .error e => .error e
      | .ok args =>
          match resolveCallerCapObject tid args.vspaceRoot .write st with
          | .error e => .error e
          | .ok (_, rootId) => Architecture.pageTableMap objId rootId args.vaddr st
    | _ => fun _ => .error .invalidCapability
  -- **WS-BP BP7.1 (`v0.36.12`)**: `seL4_ARM_PageTable_Unmap` — the table from the
  -- invoked capability; the address space is the one its own record names.
  | .pageTableUnmap =>
    some <| match cap.target with
    | .object objId => fun st => Architecture.pageTableUnmap objId st
    | _ => fun _ => .error .invalidCapability
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
  any caller's CSpace resolves MR0 to is a pre-state fact all the same. -/
  boundThreadNotDonationOwner : ∀ (callerTid : SeLe4n.ThreadId)
      (vThreadId : SeLe4n.ValidThreadId),
    decoded.syscallId = .schedContextBind →
    resolveSchedContextBindThread callerTid (decodeSchedContextBindArgs decoded) st =
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
      cases hDec : decodeCSpaceCopyArgs decoded with
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
      obtain ⟨_, _, _, _, _, _, _, _, _, hCarve⟩ := untypedRetypeFromCap_ok tid _ _ _ st st' hStep
      exact untypedRetypeObject_preserves_ipcInvariantFull _ _ _ _ st st' hObjInv hInv hCarve
    all_goals try cases hStep
  case untypedReset =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object _ =>
      obtain ⟨_, _, _, -, -, hS⟩ := untypedResetFromCap_ok _ _ st st' hStep
      exact untypedResetSlot_preserves_ipcInvariantFull hObjInv hInv hS
    all_goals try cases hStep
  case vspaceMap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hDec : decodeVSpaceMapArgs decoded st.machine.maxASID with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          · obtain ⟨_, _, _, st1, _, _, _, _, _, hMap, epoch, st2, hT, hRec⟩ :=
              vspaceMapFromFrameCap_ok tid executingCore args st st' hStep
            have hTag := tagFrameMapping_preserves_ipcInvariantFull _ _ _ st1 st2 epoch
              (vspaceMapPageCheckedWithShootdownFromStatePerCore_ok_frame _ _ _ _ _ st st1
                hObjInv hMap).1
              (vspaceMapPageCheckedWithShootdownFromStatePerCore_preserves_ipcInvariantFull
                st st1 _ _ _ _ _ hObjInv hInv hMap) hT
            exact (cspaceRecordFrameMapping_preserves_ipcInvariantFull _ _ st2 st'
              hTag.2 hTag.1 hRec).1
    all_goals try cases hStep
  case vspaceUnmap =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object oid =>
      try dsimp only [] at hStep
      cases hDec : decodeVSpaceUnmapArgs decoded st.machine.maxASID with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          split at hStep
          · cases hStep
          · exact vspaceUnmapPageWithShootdownAndIcacheBroadcast_preserves_ipcInvariantFull
              st st' _ _ _ hObjInv hInv hStep
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
    case object oid =>
      try dsimp only [] at hStep
      obtain ⟨_, hRev⟩ := revokeServiceByRecordedRegistration_revokeService hStep
      exact revokeService_preserves_ipcInvariantFull st st' _ hObjInv hInv hRev
    all_goals try cases hStep
  case serviceQuery =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object epId =>
      try dsimp only [] at hStep
      cases hLkS : lookupServiceByRecordedRegistration epId st with
      | error e => simp only [hLkS] at hStep; cases hStep
      | ok pair =>
          obtain ⟨reg, st1⟩ := pair
          simp only [hLkS] at hStep
          have hStEq : st1 = st := lookupServiceByRecordedRegistration_preserves_state epId st reg st1 hLkS
          subst hStEq
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
          subst hStep
          exact writeReturnFrameToTcb_preserves_ipcInvariantFull st1 tid _ hObjInv hInv
    all_goals try cases hStep
  case schedContextConfigure =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case schedControl core =>
      try dsimp only [] at hStep
      cases hDec : decodeSchedContextConfigureArgsChecked decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : resolveSchedControlConfigureTarget tid core args.scCPtr st with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vScId =>
              simp only [hVal] at hStep
              split at hStep
              · exact schedControlConfigure_preserves_ipcInvariantFull st st' _ vScId _ _ _ _ _
                  hObjInv hInv hStep
              · cases hStep
    all_goals try cases hStep
  case schedContextBind =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object scId =>
      try dsimp only [] at hStep
      cases hRes : resolveSchedContextBindThread tid (decodeSchedContextBindArgs decoded) st with
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
              cases hUn : SchedContextOps.schedContextUnbindOnCore vScId
                  executingCore st with
              | error e => simp only [hUn] at hStep; cases hStep
              | ok pair =>
                  obtain ⟨stU, sgiU⟩ := pair
                  simp only [hUn] at hStep
                  cases hStep
                  exact schedContextUnbindOnCore_preserves_ipcInvariantFull st st' vScId _
                    sgiU hObjInv hInv
                    hR hUn
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
  case tcbBindNotification =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object tcbObjId =>
      try dsimp only [] at hStep
      cases hDec : decodeTcbBindNotificationArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hCaller : st.getTcb? tid with
          | none => simp only [hCaller] at hStep; cases hStep
          | some callerTcb =>
              simp only [hCaller] at hStep
              cases hRoot : st.getCNode? callerTcb.cspaceRoot with
              | none => simp only [hRoot] at hStep; cases hStep
              | some rootCn =>
                  simp only [hRoot] at hStep
                  try dsimp only [] at hStep
                  cases hCap2 : syscallLookupCap { callerId := tid, cspaceRoot := callerTcb.cspaceRoot, capAddr := args.notificationCPtr, capDepth := rootCn.depth, requiredRight := .write } st with
                  | error e => simp only [hCap2] at hStep; cases hStep
                  | ok pair =>
                      obtain ⟨ntfnCap, stL⟩ := pair
                      simp only [hCap2] at hStep
                      cases hNT : ntfnCap.target with
                      | object notifId =>
                          simp only [hNT] at hStep
                          exact bindNotification_preserves_ipcInvariantFull st st' notifId _
                            hObjInv hInv hStep
                      | _ => simp only [hNT] at hStep; cases hStep
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
                    (schedContextBindingBidirectional_of_consistent
                      hPack.schedContextLinks.binding hInv.donationOwnerValid) hInv
                    hPack.replyStacksSettleOnWaitingDonors hSus
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
          cases hRes : Lifecycle.Suspend.resumeThreadOnCore
              (retirePendingFaultForResume st vtid.val) vtid
              executingCore with
          | error e => simp only [hRes] at hStep; cases hStep
          | ok pair =>
              obtain ⟨stU, sgiU⟩ := pair
              simp only [hRes] at hStep
              cases hStep
              exact resumeThreadOnCore_preserves_ipcInvariantFull
                (retirePendingFaultForResume st vtid.val) st' vtid _ sgiU
                (retirePendingFaultForResume_preserves_objects_invExt st _ hObjInv)
                (threadIpcFieldsQuiescent_retirePendingFaultForResume st _ hObjInv
                  (hPack.targetThreadQuiescent objId (Or.inr hSy) hTgt vtid hVal))
                (retirePendingFaultForResume_preserves_ipcInvariantFull st _ hObjInv hInv) hRes
    all_goals try cases hStep
  case tcbSetPriority =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : decodeSetPriorityArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hValC : validateThreadIdArg tid with
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
          cases hValC : validateThreadIdArg tid with
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
              cases hSet : Architecture.IpcBufferValidation.setIPCBufferOp st vtid
                  args.bufferAddr with
              | error e => simp only [hSet] at hStep; cases hStep
              | ok stU =>
                  simp only [hSet] at hStep
                  cases hStep
                  exact setIPCBufferOp_preserves_ipcInvariantFull st st' vtid _
                    hObjInv hInv hSet
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
  case tcbSetFaultHandler =>
    cases hTgt : cap.target <;> simp only [hTgt] at hStep
    case object objId =>
      try dsimp only [] at hStep
      cases hDec : Architecture.SyscallArgDecode.decodeSetFaultHandlerArgs decoded with
      | error e => simp only [hDec] at hStep; cases hStep
      | ok args =>
          simp only [hDec] at hStep
          cases hVal : validateThreadIdArg (ThreadId.ofNat objId.toNat) with
          | error e => simp only [hVal] at hStep; cases hStep
          | ok vtid =>
              simp only [hVal] at hStep
              cases hSet : setThreadFaultHandlerOp st vtid args.handlerCPtr with
              | error e => simp only [hSet] at hStep; cases hStep
              | ok stU =>
                  simp only [hSet] at hStep
                  cases hStep
                  exact setThreadFaultHandlerOp_preserves_ipcInvariantFull st st' vtid _
                    hObjInv hInv hSet
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
              cases hR : resolveSetSpace tid args st with
              | error e => simp only [hR] at hStep; cases hStep
              | ok p =>
                  obtain ⟨cn, vr⟩ := p
                  simp only [hR] at hStep
                  cases hSet : copyThreadSpacesZombie executingCore st vtid cn vr with
                  | error e => simp only [hSet] at hStep; cases hStep
                  | ok stU =>
                      simp only [hSet] at hStep
                      cases hStep
                      exact copyThreadSpacesZombie_preserves_ipcInvariantFull executingCore st st'
                        vtid cn vr hObjInv hInv hPack.lentContextsHeadedByLender
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
          cases hR : resolveCallerCapObject tid args.vspaceRoot .write st with
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

/-- WS-J1-C/K-C/K-D: Dispatch a decoded syscall to the appropriate internal
kernel operation using the resolved capability's target. Called after cap
resolution succeeds inside `syscallInvoke`.

WS-K-C: Accepts full `SyscallDecodeResult` so dispatch arms can extract
per-syscall arguments from `decoded.msgRegs` via the typed decode functions
in `SyscallArgDecode`.

WS-K-D: Lifecycle and VSpace stubs replaced with full dispatch. All 13
syscalls now route to real kernel operations — zero `.illegalState` stubs
remain.

V8-H: Capability-only arms delegate to `dispatchCapabilityOnly`, behind the
two service arms' flow gates (`dispatchCapabilityOnlyChecked`): the query reads the
registration its endpoint records, and the revoke removes it.

**W6-D (L-8): Two-tier dispatch design rationale.** The dispatch is split into
`dispatchCapabilityOnly` (handles syscalls needing only the resolved capability
and no additional decoded arguments) and this explicit match (handles syscalls
requiring per-syscall argument decoding from `decoded.msgRegs`). This split:
1. Shares a single checked/unchecked dispatch implementation (V8-H)
2. Enables the wildcard unreachability proof (`dispatchWithCap_wildcard_unreachable`)
   showing all 25 `SyscallId` variants are handled by one of the two tiers
3. Keeps argument-free dispatch arms concise via `dispatchCapabilityOnly`
The wildcard `| _ =>` arm is provably dead code (W2-C).

**The caller/core pair.**  This tier takes `tid` and `executingCore` as given.
Every entry reaches it through `dispatchSyscall`/`dispatchSyscallChecked`, whose
first step refuses a `tid` that is not current on `executingCore`
(`dispatchSyscall_ok_caller_current`, `dispatchSyscallChecked_ok_caller_current`),
so it only ever runs on a consistent pair. -/
def dispatchWithCap (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability) : Kernel Unit :=
  match dispatchCapabilityOnly decoded cap tid executingCore with
  | some k => k
  | none =>
  match decoded.syscallId with
  -- WS-K-E/M-D01: IPC send — message body + extra caps from decoded message registers.
  | .send =>
    match cap.target with
    | .object epId =>
      fun st =>
        -- WS-ZA ZA4.7 (seL4 `sendIPC`): the send is handed only the badge and
        -- the grant bit of the invoked capability.  The words are read from the
        -- sender's own frame at delivery, and the extra capabilities are looked up
        -- only on the arm that delivers (a send that blocks resolves none; its
        -- receiver looks them up at the rendezvous).
        let payload : SendPayload := .frame cap.badge (cap.rights.mem .grant)
        -- WS-SM SM6.D (PR #822 review): capture the receive-queue head the send will
        -- wake, so its server-first reply stash is cleared once it leaves
        -- `.blockedOnReceive` (a stash lives only on a blocked receiver).
        let wokenReceiver? := (st.getEndpoint? epId).bind (·.receiveQ.head)
        -- WS-SM SM8.B (PR #861 review round 10): route through the **per-core**
        -- send transition, like `.call`/`.receive`/`.reply`.  The single-core
        -- `endpointSendDual` wakes a rendezvous receiver with the boot-pinned
        -- `ensureRunnable` and deschedules a blocking sender with the boot-pinned
        -- `removeRunnable`, so on a multi-core system a receiver woken by a remote
        -- sender lands on a run queue its own core never dispatches from, and a
        -- sender blocking on a secondary core stays current/runnable there.
        -- `endpointSendDualWithCapsOnCore … executingCore` wakes the receiver on
        -- *its* home core and removes the sender from *its own* core; on the boot
        -- core it is the single-core transition.
        match endpointSendDualWithCapsOnCore epId tid payload
            decoded.capRecvSlot executingCore st with
        | (_, .error e) => .error e
        | (st', .ok (summary, _)) =>
            match clearWokenReceiverStash wokenReceiver? st' with
            | .error e => .error e
            | .ok ((), st'') =>
                -- WS-RA RA.B.5b: a rendezvous woke the blocked receiver with the
                -- message in its `pendingMessage`; stage its return frame now
                -- (its own boundary crossing ended `.blocks` — delivery is the
                -- context restore, WS-BP BP7.6).  Inert when the send parked instead.
                -- PR #866 round-2: the frame's `extraCaps` is the transfer
                -- summary's INSTALLED count — a grant-denied or slot-exhausted
                -- transfer reports zero, never the number of addresses the sender named.
                .ok ((), Architecture.stageWokenDelivery st'' wokenReceiver?
                          summary.installedCount)
    | _ => fun _ => .error .invalidCapability
  | .receive =>
    match cap.target with
    | .object epId =>
      -- WS-SM SM6.D (faithful seL4-MCS, server-supplied reply objects): the
      -- server supplies a Reply object capability at `RecvArgs.replyCPtr`
      -- (msgRegs[0]) — a *separate* CPtr from the endpoint receive cap, resolved
      -- from the caller's own CSpace via a gate whose `capAddr` is that slot.
      -- On a `Call` rendezvous (the popped sender lands `.blockedOnReply`) the
      -- kernel links that caller to the server's reply object so the server's
      -- later `.reply` resolves authority through `reply.caller`.
      fun st =>
        -- PR #822 review: an explicit (length ≥ 1) but bad reply cap fails BEFORE
        -- the receive, so a server is never blocked as a plain receive on a
        -- stale/non-reply CPtr (only length 0 means "no reply object").
        match resolveRecvReplyId gate decoded st with
        | .error e => .error e
        | .ok replyIdOpt =>
          -- WS-SM SM6.D (PR #822 review): route through the **per-core** receive
          -- transition (like `.call`/`.replyRecv`).  The single-core `endpointReceiveDual`
          -- block path removes the receiver with the boot-core `removeRunnable`, so a
          -- server receiving on a non-boot core could block `.blockedOnReceive` yet stay
          -- current/runnable on its actual core; `endpointReceiveDualOnCore … executingCore`
          -- removes it from *its own* core and routes a woken `blockedOnSend` sender to
          -- *its* home core.  On the boot core this is definitionally `endpointReceiveDual`.
          -- WS-SM SM6.D (#7.2 fold): the resolved reply object is threaded into the
          -- per-core receive transition, which links a dequeued `Call` caller to it
          -- atomically (the former post-receive `linkReceivedCaller` step).
          -- WS-RA RA.B.5b: capture the send-queue head the consume will dequeue —
          -- a *plain* sender's send completes at the rendezvous (woken `.ready`,
          -- payload consumed) and is owed the unit success frame; a `Call` sender
          -- lands `.blockedOnReply` and the completion stager's guard skips it.
          let wokenSender? := (st.getEndpoint? epId).bind (·.sendQ.head)
          -- PR #873 round 6: route through the **WithCaps** per-core receive, so
          -- a send that parked before its receiver arrived delivers its
          -- capabilities too.  It did not: the bare `endpointReceiveDualOnCore`
          -- moves the parked sender's `pendingMessage` across wholesale and
          -- installs nothing, while an immediate rendezvous transferred the
          -- capabilities through `endpointSendDualWithCapsOnCore` — so whether a
          -- capability arrived depended on which side reached the endpoint
          -- first.  The authority is the sender's, recorded on its blocked
          -- thread state (`TCB.ipcCanGrant`, seL4's `blockingIPCCanGrant`) and
          -- read by the request the receive resolves (`blockedSenderCapRequest`),
          -- which is what makes the two orderings agree rather than merely both
          -- do something.
          match endpointReceiveDualWithCapsOnCore epId tid replyIdOpt gate.cspaceRoot
              decoded.capRecvSlot executingCore st with
          | (st', .ok (dequeued, summary, _sgi)) =>
              -- **WS-OD OD3.6: seL4-MCS's `maybeDonateSchedContext`.**  A receive
              -- that rendezvoused with a queued `Call` hands the caller's
              -- scheduling context to this receiver, so a passive server runs the
              -- request on the client's own reservation.  This arm performed no
              -- donation at all: a passive server taking its FIRST request with
              -- `seL4_Recv` got no budget, while the same server taking its second
              -- and later requests with `seL4_ReplyRecv` was charged correctly —
              -- one condition, two API paths, and the asymmetric one silently
              -- defeating the budget enforcement the CBS surface exists to
              -- provide.  Literally the step `replyRecvPostReceiveDonation`
              -- runs, so the two arms cannot drift.
              --
              -- Guarded and total: `rendezvousDequeuedCall` is false for a receive
              -- that blocked (the returned id is the receiver itself, which is
              -- `.blockedOnReceive`) and for a plain `Send` rendezvous (the woken
              -- sender is `.ready`), and `applyCallDonation` is itself the
              -- identity unless the receiver is `.unbound` and the donor `.bound`.
              --
              -- **WS-OD OD3.14: and the priority the donation does not carry.**
              -- The dequeued caller is `.blockedOnReply _ (some tid)`, and
              -- `resolveEffectivePrioDeadline` is `max basePrio pipBoost` -- the
              -- donation moves the SchedContext, hence the *base* priority, and
              -- moves no boost at all, so a chain blocked behind that caller
              -- stopped dead at it.  This arm ran no chain walk while `.call`
              -- (`endpointCallCrossCoreDispatch`) and `.replyRecv` both did:
              -- one condition, three API paths, and the two that dequeue a
              -- parked `Call` disagreeing about it.  `applyReceiveRendezvousHandoff`
              -- is the donation and the walk under ONE reading of the guard.
              match applyReceiveRendezvousHandoff st' tid dequeued executingCore with
              | .error e => .error e
              | .ok stDon =>
                -- WS-RA RA.B.6: a non-blocking consume delivered into the caller's
                -- own `pendingMessage`; stage it as the return frame (badge → x0,
                -- synthesized MessageInfo → x1, inline window → x2-x5).  A caller
                -- that blocked stages nothing (the `.ready` guard inside) — its
                -- frame is owed by the unblocking transition per plan §3.5.
                -- PR #866 round-2 / PR #873 round 6: the `extraCaps` count is the
                -- transfer summary's INSTALLED count, the same honest figure the
                -- send and call paths report.  It was hardcoded to zero while the
                -- receive installed nothing; now it says what actually arrived, so
                -- a grant-denied or slot-exhausted transfer still reports zero.
                .ok ((), Architecture.stageDeliveredMessage
                          (Architecture.stageWokenSendCompletion stDon wokenSender?) tid
                          summary.installedCount)
          | (_, .error e) => .error e
    | _ => fun _ => .error .invalidCapability
  -- WS-K-E/M-D01: IPC call — message body + extra caps from decoded message registers.
  | .call =>
    match cap.target with
    | .object epId =>
      fun st =>
        -- WS-ZA ZA4.7 (seL4 `sendIPC`): the send is handed only the badge and
        -- the grant bit of the invoked capability.  The words are read from the
        -- sender's own frame at delivery, and the extra capabilities are looked up
        -- only on the arm that delivers (a send that blocks resolves none; its
        -- receiver looks them up at the rendezvous).
        let payload : SendPayload := .frame cap.badge (cap.rights.mem .grant)
        -- WS-SM SM6.A (live cross-core `.call`): route the unchecked `.call`
        -- through the cross-core dispatch (receiver woken on its *home* core,
        -- surfacing a `.reschedule` SGI). `endpointCallCrossCoreDispatch` is the
        -- cross-core analogue of `endpointCallWithCaps` + inline donation; the
        -- caller is descheduled from its own core (derived from the live state).
        -- WS-SM SM6.D (#7.3b fold): the server-first reply linkage is now atomic
        -- with the rendezvous — `endpointCallOnCore` itself links the caller to the
        -- server's stashed reply object (`linkServerStashedReply`) at the moment the
        -- caller lands `.blockedOnReply`, so there is no separate post-dispatch step.
        -- WS-RA RA.B.5b: a rendezvous woke the blocked receiver with the call
        -- message in its `pendingMessage`; stage its return frame (the CALLER
        -- itself always blocks — §3.5 — and is owed its frame by the reply path).
        let wokenReceiver? := (st.getEndpoint? epId).bind (·.receiveQ.head)
        match endpointCallCrossCoreDispatch epId tid payload
            decoded.capRecvSlot executingCore st with
        -- PR #866 round-2: the woken receiver's `extraCaps` is the transfer
        -- summary's INSTALLED count (zero on grant-denied / slot-exhausted
        -- transfers), never the number of addresses the sender named.
        | (st', .ok (summary, _)) =>
            .ok ((), Architecture.stageWokenDelivery st' wokenReceiver?
                      summary.installedCount)
        | (_, .error e) => .error e
    | _ => fun _ => .error .invalidCapability
  -- WS-K-E: IPC reply — message body populated from decoded message registers.
  | .reply =>
    match cap.target with
    | .replyCap rid =>
      fun st =>
        let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
        -- WS-SM SM6.D (seL4-MCS reply object): resolve the reply cap's `ReplyId`
        -- to its recorded caller (`reply.caller`), reply to that caller through
        -- the cross-core dispatch (the `blockedOnReply` caller woken on its
        -- *home* core via `wakeThread`, donated SchedContext returned, PIP
        -- reverted cross-core; replier descheduled on `executingCore`).  The
        -- single-use linkage consume (`reply.caller := none` +
        -- `caller.replyObject := none`) is **folded into `endpointReplyOnCore`**
        -- (PR #827 review #3) — atomic with the delivery, no separate dispatch
        -- step.  Fails closed (`.replyCapInvalid`) on a dangling reply or an
        -- unlinked caller.
        -- WS-RR RR7.11: the answered thread is `replyAnsweredCaller?`, the
        -- expression the declared footprint resolver reads.  The two-level
        -- match this replaces collapsed a dangling reply and an unlinked one
        -- onto the same error, so this is that arm verbatim with the
        -- resolution named once.
        match replyAnsweredCaller? st rid with
        | none => .error .replyCapInvalid
        | some callerTid =>
            -- WS-RR RR4.14/RR4.15: seL4's `doReplyTransfer` branches on the
            -- answered thread's `tcbFault` before it transfers anything.  On an
            -- unfaulted caller this is the pre-RR4 arm verbatim — the cross-core
            -- reply plus the RA.B.5b delivered-message staging
            -- (`replyTransferOnCore_of_no_fault`).  On a faulted one it is the
            -- fault reply: the handler's message is decoded against the fault the
            -- thread carries and the thread is restarted at a chosen PC or
            -- abandoned, with no delivered message to stage.  Without this branch
            -- the fault handler's reply would wake the faulted thread `.ready`
            -- with its saved PC still addressing the instruction that faulted.
            replyTransferOnCore tid callerTid decoded.msgInfo decoded.msgRegs
              { registers := body, badge := cap.badge } executingCore st
    | _ => fun _ => .error .invalidCapability
  -- WS-K-C: CSpace operations — cap targets a CNode, message registers
  -- carry slot indices, rights, and badge. Decoded via SyscallArgDecode.
  -- U5-H/U-M03: Badge value 0 is treated as "no badge" by design, matching seL4
  -- semantics where badge 0 indicates an unbadged capability. This means callers
  -- cannot explicitly set badge 0 — a deliberate simplification that matches
  -- seL4's treatment of zero-valued badges as "no badge specified".
  -- X5-I (L-5): Confirmed v0.22.17 audit — badge zero indistinguishability
  -- matches seL4 semantics. No security impact.
  -- C-01: Uses cspaceMintWithCdt for CDT-tracked derivation so minted
  -- capabilities are revocable via cspaceRevoke.
  | .cspaceMint =>
    match cap.target with
    | .object cnodeId =>
        fun st => match decodeCSpaceMintArgs decoded with
        | .error e => .error e
        | .ok args =>
            if !cnodeInvoked cnodeId st then .error .objectNotFound else
            let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
            let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
            let badge : Option SeLe4n.Badge :=
              if args.badge.val = 0 then none else some args.badge
            cspaceMintWithCdt src dst args.rights badge st
    | _ => fun _ => .error .invalidCapability
  | .cspaceCopy =>
    match cap.target with
    | .object cnodeId =>
        fun st => match decodeCSpaceCopyArgs decoded with
        | .error e => .error e
        | .ok args =>
            if !cnodeInvoked cnodeId st then .error .objectNotFound else
            let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
            let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
            cspaceCopy src dst st
    | _ => fun _ => .error .invalidCapability
  | .cspaceMove =>
    match cap.target with
    | .object cnodeId =>
        fun st => match decodeCSpaceMoveArgs decoded with
        | .error e => .error e
        | .ok args =>
            if !cnodeInvoked cnodeId st then .error .objectNotFound else
            let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
            let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
            cspaceMove src dst st
    | _ => fun _ => .error .invalidCapability
  -- V8-H/D1: cspaceDelete, vspaceMap, vspaceUnmap, serviceRevoke,
  -- serviceQuery, schedContextConfigure, schedContextBind, schedContextUnbind,
  -- tcbSuspend, tcbResume are all handled by dispatchCapabilityOnly above.
  -- WS-Q1-D: Service register — decode interface spec from message registers,
  -- construct ServiceRegistration, and register the service.
  | .serviceRegister =>
    match cap.target with
    | .object epId =>
      fun st => match decodeServiceRegisterArgs decoded with
      | .error e => .error e
      | .ok args =>
          let iface : InterfaceSpec := {
            ifaceId         := args.interfaceId
            methodCount     := args.methodCount
            maxMessageSize  := args.maxMessageSize
            maxResponseSize := args.maxResponseSize
            requiresGrant   := args.requiresGrant
          }
          let reg : ServiceRegistration := {
            iface := iface
            endpointCap := cap
          }
          registerService reg st
    | _ => fun _ => .error .invalidCapability
  -- V2-A: Notification signal — badge merge or wake a waiter.
  -- The notification object comes from the capability target, badge from MR[0].
  | .notificationSignal =>
    match cap.target with
    | .object notifId =>
      fun st => match decodeNotificationSignalArgs decoded with
      | .error e => .error e
      | .ok args =>
          -- WS-SM SM6.B (live bound-aware cross-core signal): route through
          -- `notificationSignalBoundCrossCoreDispatch` — when the notification is
          -- bound to a `BlockedOnReceive` TCB the badge is delivered directly to
          -- it, otherwise the cross-core `notificationSignalOnCore` runs (head
          -- waiter woken on its home core).  The surfaced cross-core SGI is
          -- re-derived from the committed state diff by the runtime entry.
          -- WS-SM SM6.D (PR #822 review): a bound delivery wakes a `.blockedOnReceive`
          -- bound TCB to `.ready`; if that server stashed a server-first reply object,
          -- clear the stash (it lives only on a blocked receiver) — symmetric to the
          -- plain-Send wake (`clearWokenReceiverStash`).  No-op when no bound receiver
          -- is woken or it carries no stash, so the trace is byte-identical.
          let woken? := (boundDeliveryTarget? st notifId).map (·.1)
          -- WS-RA RA.B.5b: the wait-before-signal ordering — a signal waking a
          -- blocked plain waiter (the head of the wait queue) or a bound
          -- `.blockedOnReceive` TCB delivers the badge into its
          -- `pendingMessage`; stage the woken thread's return frame (its own
          -- wait blocked with no frame — §3.5's split, now closed on the
          -- staging side; delivery is the context restore (WS-BP BP7.6)).  The two
          -- targets are mutually exclusive (the bound path requires an empty
          -- wait queue), and each stager is inert when its target was not
          -- woken.
          let plainWaiter? := notificationSignalWaiter? st notifId
          match notificationSignalBoundCrossCoreDispatch notifId args.badge executingCore st with
          | (st', .ok _) =>
              match clearWokenReceiverStash woken? st' with
              | .error e => .error e
              | .ok ((), st'') =>
                  -- Installed count 0 for both stagers: a notification wake
                  -- delivers a badge-only message (no caps, no unwrap).
                  .ok ((), Architecture.stageWokenDelivery
                            (Architecture.stageWokenDelivery st'' woken? 0)
                            plainWaiter? 0)
          | (_, .error e) => .error e
    | _ => fun _ => .error .invalidCapability
  -- V2-A: Notification wait — consume pending badge or block.
  -- The notification object comes from the capability target, waiter is current thread.
  | .notificationWait =>
    match cap.target with
    | .object notifId =>
      fun st =>
        -- WS-SM SM6.B: route through the per-core cross-core wait so the blocked
        -- caller is descheduled on *its own* core (not the boot core).
        match notificationWaitCrossCoreDispatch notifId tid executingCore st with
        | (st', .ok (some badge)) =>
            -- WS-RA RA.B.5 (the SM9.C.0 closure, signal-before-wait ordering):
            -- the consumed pending badge is staged into the caller's return
            -- frame instead of being discarded.  The blocking arm (`.ok none`)
            -- stages nothing — the badge does not exist yet, and the signal
            -- path owes the waiter's frame per plan §3.5.
            .ok ((), Architecture.writeReturnFrameToTcb st' tid
              (Architecture.returnFrameOfBadge badge))
        | (st', .ok none) => .ok ((), st')
        | (_, .error e) => .error e
    | _ => fun _ => .error .invalidCapability
  -- V2-C: ReplyRecv — compound reply + receive in one transition.
  -- Cap targets the endpoint for the receive leg. Reply target from MR[0].
  -- Message body for the reply leg comes from the standard message registers.
  | .replyRecv =>
    match cap.target with
    | .object epId =>
      -- WS-SM SM6.D (faithful seL4-MCS `.replyRecv`): resolve the server-supplied
      -- reply cap (`ReplyRecvArgs.replyCPtr`) to its `(rid, prevCaller)` — authority
      -- flows from *holding* the reply cap (`reply.caller`), exactly like `.reply`,
      -- closing the prior raw-thread bypass.  `endpointReplyRecvOnCore` then replies to the
      -- prev caller, **consumes** the answered reply link, receives the next
      -- message, and **re-links** the same reply object to the next caller.
      fun st =>
        match resolveReplyRecvReply gate decoded st with
        | .error e => .error e
        | .ok (rid, prevCaller, replyBadge) =>
            -- WS-SM SM6.D (PR #822 review): MR0 carries the reply CPtr (a control
            -- register), so the reply *payload* delivered to the previous caller is
            -- MR1.. — strip the leading control register before building the reply.
            -- The reply badge is the *reply cap's* badge (`replyBadge`), not the
            -- endpoint receive cap's, matching the `.reply` arm.
            let full := extractMessageRegisters decoded.msgRegs decoded.msgInfo
            let body := full.extract 1 full.size
            let msg : IpcMessage := { registers := body, badge := replyBadge }
            -- WS-RA RA.B.6: the receive leg may have consumed a queued sender
            -- into the caller's `pendingMessage`; stage it as the return frame.
            -- A caller that blocked on the receive leg stages nothing (the
            -- `.ready` guard inside `stageDeliveredMessage`).
            match endpointReplyRecvOnCore epId tid rid prevCaller msg gate.cspaceRoot
                decoded.capRecvSlot executingCore st with
            -- PR #873 round 7: the receive leg inside `endpointReplyRecvOnCore` now runs
            -- the **WithCaps** per-core receive, so a capability-bearing sender
            -- that parked before this `.replyRecv` delivers its capabilities
            -- too — the arrival-order dependence the `.receive` arms shed one
            -- round earlier, closed in the arm that is a receive without being
            -- spelled `.receive`.  `extraCaps` is the summary's INSTALLED
            -- count, the same honest figure `.send`, `.call` and `.receive`
            -- report; it was hardcoded to zero while this leg installed nothing.
            | .ok (summary, st') =>
                .ok ((), Architecture.stageDeliveredMessage st' tid summary.installedCount)
            | .error e => .error e
    | _ => fun _ => .error .invalidCapability
  -- WS-SM SM8.C.9: **there is no unchecked declassification.**
  --
  -- Every other arm here is the unchecked twin of a policy-gated one: it derives
  -- authority from the capability and skips a `securityFlowsTo` guard the caller
  -- has opted out of.  Declassification cannot work that way — its authority
  -- *is* a policy (the base lattice must deny the flow and the declassification
  -- policy must permit it), so "unchecked" would mean "every downgrade is
  -- authorized", which is the opposite of what the operation exists to control.
  --
  -- So this path fails closed with the error a denied downgrade produces.  A
  -- deployment that wants declassification enters through `dispatchSyscallChecked`
  -- with a configured `LabelingContext.declassificationPolicy`.
  | .declassify => fun _ => .error .declassificationDenied
  -- WS-SM SM9.C.8: **and there is no unchecked declassifying signal**, for the
  -- same reason one step over — and one more.
  --
  -- Its authority is a policy at *two* hops, so an unchecked arm would mean
  -- "every downgrade into this notification, and every onward delivery out of
  -- it, is authorized".  The second half is the sharper one: the ordinary
  -- checked `.notificationSignal` already gates notification → receiver (the
  -- v0.31.73 badge-leak closure), so an unchecked declassifying variant would
  -- be strictly *weaker* than the syscall it wraps while carrying stronger
  -- authority — a downgrade path that skips a gate the ordinary path enforces.
  | .declassifySignal => fun _ => .error .declassificationDenied
  -- WS-SM SM9.A.10: **there is no unchecked audit read either**, and the reason
  -- is the same shape one step over.
  --
  -- Every value the reader returns is selected by the caller's *clearance*: the
  -- visible view is `auditLogVisibleTo` at the running subject's domain, and
  -- whether the caller sees a global identity or a view-local index turns on the
  -- configured monitor clearance.  Both live in the `LabelingContext`, which the
  -- unchecked path does not carry.  An unchecked arm would therefore have to
  -- pick a clearance, and the only clearances available are "the caller's, from
  -- a context we do not have" and "all of them" — the second being an audit
  -- reader that hands every entry to every capability holder.
  --
  -- So this path fails closed.  A deployment that wants audit reads enters
  -- through `dispatchSyscallChecked` with a configured
  -- `LabelingContext.auditMonitorClearance`, and mints a `.auditTrail`
  -- capability from its boot/CSpace layer.
  | .auditRead | .auditDrain => fun _ => .error .illegalAuthority
  -- AE1-A/AE1-B: tcbSetPriority, tcbSetMCPriority, tcbSetIPCBuffer are now handled
  -- by dispatchCapabilityOnly above. Together with cspaceDelete,
  -- vspaceMap, vspaceUnmap, serviceRevoke, serviceQuery, schedContextConfigure,
  -- schedContextBind, schedContextUnbind, tcbSuspend, tcbResume — 13 total arms
  -- handled by dispatchCapabilityOnly. The wildcard satisfies Lean's exhaustiveness
  -- checker and is provably unreachable (dispatchWithCap_wildcard_unreachable).
  -- WS-ZA ZA4.3: a yield invokes no capability, so `dispatchSyscall` runs it
  -- before this tier (`dispatchYield`) and this tier never receives one.
  | .yield => fun _ => .error .illegalState
  | _ => fun _ => .error .illegalState

-- ============================================================================
-- T6-I/M-IF-1: Information-flow-checked dispatch
-- ============================================================================

/-- **The flow gates of the two capability-only service arms.**  The service
query reads the registration its endpoint records, and the revoke removes it,
so each is a read or a write of the endpoint the invoked capability names; a
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
def dispatchCapabilityOnlyChecked (ctx : LabelingContext) (sid : SyscallId) (tid : SeLe4n.ThreadId)
    (cap : Capability) (k : Kernel Unit) : Kernel Unit :=
  match sid with
  | .serviceQuery =>
    match cap.target with
    | .object epId => serviceQueryStaged ctx tid epId
    | _ => k
  | .serviceRevoke =>
    match cap.target with
    | .object epId => revokeServiceChecked ctx tid epId
    | _ => k
  | _ => k

/-- A success through the gate is a success of the capability-only arm it
stands for: each checked service arm is the unchecked arm once its gate
admits, and a refusal is no success. -/
theorem dispatchCapabilityOnlyChecked_ok {ctx : LabelingContext} {decoded : SyscallDecodeResult}
    {tid : SeLe4n.ThreadId} {e : Concurrency.CoreId} {cap : Capability} {k : Kernel Unit}
    {st : SystemState} {r : Unit × SystemState}
    (hC : dispatchCapabilityOnly decoded cap tid e = some k)
    (h : dispatchCapabilityOnlyChecked ctx decoded.syscallId tid cap k st = .ok r) : k st = .ok r := by
  unfold dispatchCapabilityOnlyChecked at h
  cases hS : decoded.syscallId <;> rw [hS] at h <;> try exact h
  all_goals
    unfold dispatchCapabilityOnly at hC
    rw [hS] at hC
    cases hT : cap.target <;> rw [hT] at h hC <;> simp only [Option.some.injEq] at hC <;>
      subst hC <;> try exact h
  · rename_i epId
    by_cases hA : serviceEndpointWriteAdmitted ctx tid epId = true
    · simpa [revokeServiceChecked, hA] using h
    · simp [revokeServiceChecked, hA] at h
  · rename_i epId
    by_cases hA : serviceEndpointReadAdmitted ctx tid epId = true
    · simpa [serviceQueryStaged, lookupServiceChecked, hA] using h
    · simp [serviceQueryStaged, lookupServiceChecked, hA] at h

/-- Every arm but the two service arms is ungated. -/
@[simp] theorem dispatchCapabilityOnlyChecked_of_not_service (ctx : LabelingContext) {sid : SyscallId}
    (tid : SeLe4n.ThreadId) (cap : Capability) (k : Kernel Unit)
    (hQ : sid ≠ .serviceQuery) (hR : sid ≠ .serviceRevoke) :
    dispatchCapabilityOnlyChecked ctx sid tid cap k = k := by
  unfold dispatchCapabilityOnlyChecked
  split
  · exact absurd rfl hQ
  · exact absurd rfl hR
  · rfl

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
Every entry reaches it through `dispatchSyscall`/`dispatchSyscallChecked`, whose
first step refuses a `tid` that is not current on `executingCore`
(`dispatchSyscall_ok_caller_current`, `dispatchSyscallChecked_ok_caller_current`),
so it only ever runs on a consistent pair. -/
def dispatchWithCapChecked (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability) : Kernel Unit :=
  match dispatchCapabilityOnly decoded cap tid executingCore with
  | some k => dispatchCapabilityOnlyChecked ctx decoded.syscallId tid cap k
  | none =>
  match decoded.syscallId with
  -- T6-I: IPC send — checked for sender→endpoint flow
  | .send =>
    match cap.target with
    | .object epId =>
      fun st =>
        -- WS-ZA ZA4.7 (seL4 `sendIPC`): the send is handed only the badge and
        -- the grant bit of the invoked capability.  The words are read from the
        -- sender's own frame at delivery, and the extra capabilities are looked up
        -- only on the arm that delivers (a send that blocks resolves none; its
        -- receiver looks them up at the rendezvous).
        let payload : SendPayload := .frame cap.badge (cap.rights.mem .grant)
        -- AH1-B (H-01 fix): Pass capability transfer params to checked send
        -- WS-SM SM6.D (PR #822 review): clear the woken receiver's server-first reply
        -- stash (mirrors the unchecked `.send` arm).
        let wokenReceiver? := (st.getEndpoint? epId).bind (·.receiveQ.head)
        -- WS-SM SM8.B (PR #861 review round 10): the cross-core checked send
        -- (mirrors the unchecked arm; `endpointSendDualChecked` was boot-pinned
        -- through `endpointSendDualWithCaps`).  Bounds first, then the
        -- sender→endpoint flow gate, then the per-core transition.
        match endpointSendCrossCoreDispatchChecked ctx epId tid payload
            decoded.capRecvSlot executingCore st with
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
                          summary.installedCount)
    | _ => fun _ => .error .invalidCapability
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
          -- PR #822 review: an explicit (length ≥ 1) bad reply cap fails before the
          -- receive (mirrors the unchecked arm); only length 0 means "no reply object".
          match resolveRecvReplyId gate decoded st with
          | .error e => .error e
          | .ok replyIdOpt =>
            -- WS-SM SM6.D (PR #822 review): route through the per-core receive
            -- transition (the endpoint→receiver flow is already gated above, so the
            -- *unchecked* `endpointReceiveDualOnCore` is correct here).  Per-core block
            -- placement mirrors the unchecked arm; boot-core-equivalent to the prior
            -- `endpointReceiveDualChecked` when the flow is permitted.
            -- WS-SM SM6.D (#7.2 fold): reply object threaded into the per-core receive
            -- transition (the endpoint→receiver flow is gated above); the dequeued
            -- `Call` caller is linked atomically (former `linkReceivedCaller` step).
            -- WS-RA RA.B.5b: the woken plain sender's unit frame (checked twin).
            let wokenSender? := (st.getEndpoint? epId).bind (·.sendQ.head)
            -- PR #873 round 6: the checked twin of the unchecked arm's WithCaps
            -- routing — a send that parked before its receiver arrived delivers
            -- its capabilities here too, gated on the authority the sender
            -- recorded on the message.  The endpoint→receiver flow is gated
            -- above, so the *unchecked* per-core WithCaps receive is correct
            -- here for the same reason the bare one was.
            match endpointReceiveDualWithCapsOnCore epId tid replyIdOpt gate.cspaceRoot
                decoded.capRecvSlot executingCore st with
            | (st', .ok (dequeued, summary, _sgi)) =>
                -- **WS-OD OD3.6**: the checked twin of the unchecked arm's
                -- `maybeDonateSchedContext` step, and the *same* definition.  No
                -- extra flow gate is owed: the donation writes only
                -- `schedContextBinding` and `SchedContext.boundThread`, both of
                -- which `projectKernelObject` erases, so it is invisible to every
                -- observer (`returnDonatedSchedContext_preserves_projection` makes
                -- the same argument for the hand-off's other direction); and the
                -- endpoint→receiver flow this donation follows is gated above.
                --
                -- **WS-OD OD3.14**: likewise the priority half, and for the same
                -- reason no extra gate is owed -- `projectKernelObject` strips
                -- `pipBoost` (AJ2-B), and the run-queue re-bucketing the walk
                -- performs is bounded by `receiveRendezvousHandoffWriteSet`,
                -- exactly as the flow-checked `.call` arm's own walk is bounded
                -- by `endpointCallLiveWriteSet`.
                match applyReceiveRendezvousHandoff st' tid dequeued executingCore with
                | .error e => .error e
                | .ok stDon =>
                  -- WS-RA RA.B.6: stage the non-blocking consume's delivery (the
                  -- checked twin of the unchecked arm's staging; the endpoint
                  -- flow gate above governs the consumed message).  PR #873
                  -- round 6: `extraCaps` is the summary's INSTALLED count, the
                  -- same honest figure the send and call paths report — it was
                  -- hardcoded to zero while the receive installed nothing.
                  .ok ((), Architecture.stageDeliveredMessage
                            (Architecture.stageWokenSendCompletion stDon wokenSender?) tid
                            summary.installedCount)
            | (_, .error e) => .error e
    | _ => fun _ => .error .invalidCapability
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
        let payload : SendPayload := .frame cap.badge (cap.rights.mem .grant)
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
        match endpointCallCrossCoreDispatchChecked ctx epId tid payload
            decoded.capRecvSlot executingCore st with
        -- PR #866 round-2: `extraCaps` = the summary's INSTALLED count, like
        -- the unchecked arm.
        | (st', .ok (summary, _)) =>
            .ok ((), Architecture.stageWokenDelivery st' wokenReceiver?
                      summary.installedCount)
        | (_, .error e) => .error e
    | _ => fun _ => .error .invalidCapability
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
                { registers := body, badge := cap.badge } executingCore st
            else .error .replyCapInvalid
    | _ => fun _ => .error .invalidCapability
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
            let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
            let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
            let badge : Option SeLe4n.Badge :=
              if args.badge.val = 0 then none else some args.badge
            cspaceMintChecked ctx src dst args.rights badge st
    | _ => fun _ => .error .invalidCapability
  -- T6-I: CSpace copy — checked for source→destination CNode flow
  | .cspaceCopy =>
    match cap.target with
    | .object cnodeId =>
        fun st => match decodeCSpaceCopyArgs decoded with
        | .error e => .error e
        | .ok args =>
            if !cnodeInvoked cnodeId st then .error .objectNotFound else
            let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
            let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
            cspaceCopyChecked ctx src dst st
    | _ => fun _ => .error .invalidCapability
  -- T6-I: CSpace move — checked for source→destination CNode flow
  | .cspaceMove =>
    match cap.target with
    | .object cnodeId =>
        fun st => match decodeCSpaceMoveArgs decoded with
        | .error e => .error e
        | .ok args =>
            if !cnodeInvoked cnodeId st then .error .objectNotFound else
            let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
            let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
            cspaceMoveChecked ctx src dst st
    | _ => fun _ => .error .invalidCapability
  -- V8-H/D1: cspaceDelete, vspaceMap, vspaceUnmap, serviceRevoke,
  -- serviceQuery, schedContextConfigure, schedContextBind, schedContextUnbind,
  -- tcbSuspend, tcbResume are all handled by dispatchCapabilityOnly above.
  -- T6-I: Service register — checked for thread→service flow
  | .serviceRegister =>
    match cap.target with
    | .object epId =>
      fun st => match decodeServiceRegisterArgs decoded with
      | .error e => .error e
      | .ok args =>
          let iface : InterfaceSpec := {
            ifaceId         := args.interfaceId
            methodCount     := args.methodCount
            maxMessageSize  := args.maxMessageSize
            maxResponseSize := args.maxResponseSize
            requiresGrant   := args.requiresGrant
          }
          let reg : ServiceRegistration := {
            iface := iface
            endpointCap := cap
          }
          registerServiceChecked ctx tid reg st
    | _ => fun _ => .error .invalidCapability
  -- V2-A/T6-I: Notification signal — checked for signaler→notification flow
  | .notificationSignal =>
    match cap.target with
    | .object notifId =>
      fun st => match decodeNotificationSignalArgs decoded with
      | .error e => .error e
      | .ok args =>
          -- WS-SM SM6.B (live checked bound-aware cross-core signal): the
          -- info-flow-checked analogue of the unchecked arm, gating on
          -- `securityFlowsTo signaler→notification` before the bound-aware
          -- cross-core dispatch.
          -- WS-SM SM6.D (PR #822 review): clear a woken bound receiver's server-first
          -- reply stash (mirrors the unchecked arm + the plain-Send wake).
          let woken? := (boundDeliveryTarget? st notifId).map (·.1)
          -- WS-RA RA.B.5b: the woken waiter's staged badge frame (checked twin;
          -- the checked dispatch's notification→receiver gate ran before the
          -- wake, so a denied delivery errors and stages nothing).
          let plainWaiter? := notificationSignalWaiter? st notifId
          match notificationSignalBoundCrossCoreDispatchChecked ctx notifId tid args.badge executingCore st with
          | (st', .ok _) =>
              match clearWokenReceiverStash woken? st' with
              | .error e => .error e
              | .ok ((), st'') =>
                  -- Installed count 0 for both stagers: badge-only deliveries.
                  .ok ((), Architecture.stageWokenDelivery
                            (Architecture.stageWokenDelivery st'' woken? 0)
                            plainWaiter? 0)
          | (_, .error e) => .error e
    | _ => fun _ => .error .invalidCapability
  -- V2-A/T6-I: Notification wait — checked for notification→waiter flow
  | .notificationWait =>
    match cap.target with
    | .object notifId =>
      fun st =>
        -- WS-SM SM6.B: per-core checked cross-core wait (gates notification→waiter
        -- flow, then deschedules the caller on its own core).
        match notificationWaitCrossCoreDispatchChecked ctx notifId tid executingCore st with
        | (st', .ok (some badge)) =>
            -- WS-RA RA.B.5: stage the consumed badge (the checked twin of the
            -- unchecked arm's staging; the flow gate already admitted
            -- notification → waiter, which is the authority for the value).
            .ok ((), Architecture.writeReturnFrameToTcb st' tid
              (Architecture.returnFrameOfBadge badge))
        | (st', .ok none) => .ok ((), st')
        | (_, .error e) => .error e
    | _ => fun _ => .error .invalidCapability
  -- V2-C/T6-I: ReplyRecv — checked for both reply and receive legs
  | .replyRecv =>
    match cap.target with
    | .object epId =>
      -- WS-SM SM6.D (faithful checked `.replyRecv`): gate BOTH legs — the receive leg
      -- (`securityFlowsTo endpoint→receiver`) and the reply leg (`securityFlowsTo
      -- receiver→prevCaller`) — around the *same* `endpointReplyRecvOnCore` as the unchecked
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
          match resolveReplyRecvReply gate decoded st with
          | .error e => .error e
          | .ok (rid, prevCaller, replyBadge) =>
              -- WS-SM SM6.D (PR #822 review): strip the leading reply-CPtr control
              -- register (MR0); the reply payload is MR1.. (mirrors the unchecked arm).
              -- The reply badge is the *reply cap's* badge (`replyBadge`), not the
              -- endpoint receive cap's.
              let full := extractMessageRegisters decoded.msgRegs decoded.msgInfo
              let body := full.extract 1 full.size
              let msg : IpcMessage := { registers := body, badge := replyBadge }
              if securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf prevCaller) then
                -- WS-RA RA.B.6: stage the receive leg's delivery (the checked
                -- twin of the unchecked arm's staging; the receive leg's own
                -- flow gate governs the consumed message).
                match endpointReplyRecvOnCore epId tid rid prevCaller msg gate.cspaceRoot
                    decoded.capRecvSlot executingCore st with
                -- PR #873 round 7: the checked twin of the unchecked arm's
                -- WithCaps receive leg — the endpoint→receiver flow is gated
                -- above, so the *unchecked* per-core WithCaps receive inside
                -- the shared body is correct here for the same reason the bare
                -- one was, and `extraCaps` is the summary's installed count.
                | .ok (summary, st') =>
                    .ok ((), Architecture.stageDeliveredMessage st' tid summary.installedCount)
                | .error e => .error e
              else .error .replyCapInvalid
    | _ => fun _ => .error .invalidCapability
  -- WS-SM SM8.C.9: **the live declassification.**
  --
  -- The capability names the target object, so there is no confused deputy: the
  -- operand is the capability, not a caller-supplied id.  Neither domain comes
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
    | .object targetId =>
        fun st =>
          declassifyObjectFromCore (liftLegacyContext ctx) ctx.declassificationPolicy
            executingCore targetId st
    | _ => fun _ => .error .invalidCapability
  -- WS-SM SM9.C.8: **the live data-carrying declassification.**
  --
  -- Structurally the `.notificationSignal` arm — same capability target, same
  -- badge decode, same woken-stash clear, same WS-RA staging — with the
  -- bound-aware cross-core dispatch replaced by the declassifying one.  Keeping
  -- the surrounding shape identical is deliberate: the transition really does
  -- perform the ordinary signal's writes
  -- (`declassifiedSignal_ordinary_eq_signal`), so any post-processing the
  -- ordinary arm owes its woken threads, this arm owes them too.  Dropping the
  -- stash clear would leave a woken bound receiver holding a server-first reply
  -- stash the ordinary path clears; dropping the stagers would leave the woken
  -- thread's badge undeliverable at the context restore (WS-BP BP7.6).
  --
  -- Neither domain is an operand.  The source is the *actor's* — read off the
  -- subject the executing core is running — and the two destinations are the
  -- notification's own domain and the **resolved receiver's**, so a signaller
  -- authorized into the notification but not onward to the thread that will
  -- receive the badge is refused at the second hop
  -- (`.declassificationDeniedAtReceiver`).
  | .declassifySignal =>
    match cap.target with
    | .object notifId =>
      fun st => match decodeNotificationSignalArgs decoded with
      | .error e => .error e
      | .ok args =>
          let woken? := (boundDeliveryTarget? st notifId).map (·.1)
          let plainWaiter? := notificationSignalWaiter? st notifId
          match notificationSignalDeclassifiedCrossCoreDispatch (liftLegacyContext ctx)
                  ctx.declassificationPolicy notifId args.badge executingCore st with
          | (st', .ok _) =>
              match clearWokenReceiverStash woken? st' with
              | .error e => .error e
              | .ok ((), st'') =>
                  -- Installed count 0 for both stagers: badge-only deliveries.
                  .ok ((), Architecture.stageWokenDelivery
                            (Architecture.stageWokenDelivery st'' woken? 0)
                            plainWaiter? 0)
          | (_, .error e) => .error e
    | _ => fun _ => .error .invalidCapability
  -- WS-SM SM9.A.10: **the live audit read.**
  --
  -- The authority is `extractAuditAuthority` — the capability must *target* the
  -- audit trail — checked before anything else, and since PR #870 round 5 that
  -- is true of the whole path, not just this arm: the checked dispatch routes
  -- the audit ids through the resolve-only lookup (`syscallChecksTargetFirst`
  -- → `syscallInvokeResolved`), so no rights verdict front-runs the target
  -- check and a wrong-kind capability is `.invalidCapability` whatever rights
  -- it carries (the v0.32.97 confused-deputy class is the reason the target
  -- gate exists at all).  The right is the second gate, checked HERE rather
  -- than in the lookup.
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
                      .ok ((), Architecture.writeReturnFrameToTcb st' tid
                        (Architecture.returnFrameOfWord w.toUInt64))
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
                  .ok ((), Architecture.writeReturnFrameToTcb st' tid
                    (Architecture.returnFrameOfWord n.toUInt64))
        else .error .illegalAuthority
  -- AE1-A/AE1-B/AE1-C: All remaining capability-only arms (tcbSetPriority,
  -- tcbSetMCPriority, tcbSetIPCBuffer, cspaceDelete, vspaceMap,
  -- vspaceUnmap, serviceRevoke, serviceQuery, schedContextConfigure,
  -- schedContextBind, schedContextUnbind, tcbSuspend, tcbResume) are handled by
  -- dispatchCapabilityOnly returning `some` above. This wildcard is provably
  -- unreachable (see dispatchWithCapChecked_wildcard_unreachable below).
  -- WS-ZA ZA4.3: as in `dispatchWithCap`, a yield never reaches this tier.
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

    It used to live in `syscallEntryChecked`, one layer up — which was wrong for a
    reason this function's own sibling documents: `dispatchSyscall`'s docstring
    tells integrators that "for production user-space entry points, use
    `dispatchSyscallChecked`".  An integrator who took that advice called *this*
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
      match st.getObject? tcb.cspaceRoot with
      | some (.cnode rootCn) =>
        let gate : SyscallGate := {
          callerId     := tid
          cspaceRoot   := tcb.cspaceRoot
          capAddr      := decoded.capAddr
          capDepth     := rootCn.depth
          requiredRight := syscallRequiredRight decoded.syscallId
        }
        -- PR #870 round 5: the target-first syscalls (the audit pair) take the
        -- resolve-only lookup, so their arms see the capability BEFORE any
        -- rights verdict and can honour the documented order — target first
        -- (`.invalidCapability` for every non-audit target, whatever its
        -- rights), right second.  Everything else keeps the classic
        -- rights-gated lookup.
        match (if syscallChecksTargetFirst decoded.syscallId then
                 syscallInvokeResolved gate (dispatchWithCapChecked ctx decoded tid executingCore gate)
               else
                 syscallInvoke gate (dispatchWithCapChecked ctx decoded tid executingCore gate)) st with
        | .error e => .error e
        | .ok ((), stPost) =>
            .ok ((), applySyscallTaint (syscallTaintPlan st tid decoded) st stPost)
      | some _ => .error .invalidCapability
      | none   => .error .objectNotFound
    | some _ => .error .illegalState
    | none   => .error .objectNotFound

/-- WS-ZA ZA1.1: `dispatchSyscallChecked`'s arm and taint step, given what the
taint step reads of the pre-state (`applySyscallTaintAfter`): the audit epoch,
the trail's length and the taint at the plan's flow sources.  A separate,
non-inlined function so its arguments are read before the arm runs. -/
@[noinline] def dispatchCheckedArmThenTaint (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (plan : TaintPlan) (preEpoch : Nat) (preLength : Nat)
    (preTaint : TaintMap) : Kernel Unit :=
  fun st =>
    match (if syscallChecksTargetFirst decoded.syscallId then
             syscallInvokeResolved gate (dispatchWithCapChecked ctx decoded tid executingCore gate)
           else
             syscallInvoke gate (dispatchWithCapChecked ctx decoded tid executingCore gate)) st with
    | .error e => .error e
    | .ok ((), stPost) => .ok ((), applySyscallTaintAfter plan preEpoch preLength preTaint stPost)

/-- WS-ZA ZA5.12: a `.declassify`'s arm, then its fused taint step
(`declassifyTaintStep`), given the scalars standing for its plan's `noRelease`
and the audit epoch and trail length read before the arm. -/
@[noinline] def dispatchCheckedArmThenDeclassifyTaint (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (nrB : Bool) (nrId : SeLe4n.ObjId) (preEpoch preLength : Nat) : Kernel Unit :=
  fun st =>
    match (if syscallChecksTargetFirst decoded.syscallId then
             syscallInvokeResolved gate (dispatchWithCapChecked ctx decoded tid executingCore gate)
           else
             syscallInvoke gate (dispatchWithCapChecked ctx decoded tid executingCore gate)) st with
    | .error e => .error e
    | .ok ((), stPost) => .ok ((), declassifyTaintStep nrB nrId preEpoch preLength stPost)

/-- WS-ZA ZA5.12: a `.declassifySignal`'s arm, then its fused taint step
(`declassifySignalTaintStep`), given its taint case as a word, the notification
its operand names, the caller's and the notification's taint words as scalars,
and the audit epoch and trail length — all read before the arm. -/
@[noinline] def dispatchCheckedArmThenDeclassifySignalTaint (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (taintCode : Nat) (nid : SeLe4n.ObjId)
    (a0 a1 a2 a3 a4 a5 a6 a7 : UInt64) (ac : Nat) (as : Bool)
    (b0 b1 b2 b3 b4 b5 b6 b7 : UInt64) (bc : Nat) (bs : Bool)
    (preEpoch preLength : Nat) : Kernel Unit :=
  fun st =>
    match (if syscallChecksTargetFirst decoded.syscallId then
             syscallInvokeResolved gate (dispatchWithCapChecked ctx decoded tid executingCore gate)
           else
             syscallInvoke gate (dispatchWithCapChecked ctx decoded tid executingCore gate)) st with
    | .error e => .error e
    | .ok ((), stPost) =>
        .ok ((), declassifySignalTaintStep (SignalTaintCase.ofCode taintCode) nid tid
          ⟨a0, a1, a2, a3, a4, a5, a6, a7, ac, as⟩ ⟨b0, b1, b2, b3, b4, b5, b6, b7, bc, bs⟩
          preEpoch preLength stPost)

/-- WS-ZA ZA5.12: an audit call's arm; its taint step is the identity
(`auditTaintStep_eq`). -/
@[noinline] def dispatchCheckedArmOnly (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) : Kernel Unit :=
  fun st =>
    match (if syscallChecksTargetFirst decoded.syscallId then
             syscallInvokeResolved gate (dispatchWithCapChecked ctx decoded tid executingCore gate)
           else
             syscallInvoke gate (dispatchWithCapChecked ctx decoded tid executingCore gate)) st with
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
        let operand := syscallOperandCap? st tid decoded.capAddr
        dispatchCheckedArmThenDeclassifyTaint ctx decoded tid executingCore gate
          (declassifyBypassB st operand) (operandObjectId operand)
          st.declassificationAuditEpoch st.declassificationAudit.length st
    | .declassifySignal =>
        let operand := syscallOperandCap? st tid decoded.capAddr
        let nid := operandObjectId operand
        withTaintWordsAt st tid.toObjId fun a0 a1 a2 a3 a4 a5 a6 a7 ac as =>
        withTaintWordsAt st nid fun b0 b1 b2 b3 b4 b5 b6 b7 bc bs =>
        dispatchCheckedArmThenDeclassifySignalTaint ctx decoded tid executingCore gate
          (signalTaintCaseOf st operand).code nid a0 a1 a2 a3 a4 a5 a6 a7 ac as
          b0 b1 b2 b3 b4 b5 b6 b7 bc bs
          st.declassificationAuditEpoch st.declassificationAudit.length st
    | .auditRead | .auditDrain => dispatchCheckedArmOnly ctx decoded tid executingCore gate st
    | _ =>
        dispatchCheckedArmThenTaint ctx decoded tid executingCore gate
          (syscallTaintPlan st tid decoded) st.declassificationAuditEpoch
          st.declassificationAudit.length
          (sourceTaint (planSourceWords (syscallTaintPlan st tid decoded) st)) st

/-- WS-ZA ZA1.1: the compiled `dispatchSyscallChecked`.  It reads what the taint
step needs of the pre-state before the arm, so the arm owns the state it writes
(`ZERO_ALLOCATION_SYSCALL_PLAN.md` D1).  WS-ZA ZA5.12: the taint it reads is the
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
      match st.getObject? tcb.cspaceRoot with
      | some (.cnode rootCn) =>
        let gate : SyscallGate := {
          callerId     := tid
          cspaceRoot   := tcb.cspaceRoot
          capAddr      := decoded.capAddr
          capDepth     := rootCn.depth
          requiredRight := syscallRequiredRight decoded.syscallId
        }
        dispatchCheckedArmThenTaintFused ctx decoded tid executingCore gate st
      | some _ => .error .invalidCapability
      | none   => .error .objectNotFound
    | some _ => .error .illegalState
    | none   => .error .objectNotFound

/-- WS-ZA ZA5.12 (**the decode lemma at the general dispatcher**): the arm and
taint step over the captured source words is the one over the pre-state's taint
(`applySyscallTaintAfter_planSourceWords`). -/
theorem dispatchCheckedArmThenTaint_planSourceWords (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (plan : TaintPlan)
    (st : SystemState) :
    dispatchCheckedArmThenTaint ctx decoded tid executingCore gate plan
        st.declassificationAuditEpoch st.declassificationAudit.length
        (sourceTaint (planSourceWords plan st)) st =
      dispatchCheckedArmThenTaint ctx decoded tid executingCore gate plan
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
        (st.taintWordsAt (operandObjectId (syscallOperandCap? st tid decoded.capAddr)))
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
  next => exact dispatchCheckedArmThenTaint_planSourceWords ctx decoded tid executingCore gate _ st

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

    This is the recommended entry point for production systems with
    information-flow policies. The unchecked `syscallEntry` remains
    available for trusted kernel paths and backward compatibility. -/
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
        match SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
                st tid layout regs regCount with
        | .error e => .error e
        | .ok decoded =>
          -- WS-SM SM7.F.5: the decode above walked this thread's IPC buffer
          -- for each overflow message register.  On hardware that walk fills
          -- the *executing* core's TLB; record it, so `perCoreTlb` holds the
          -- translations a core acquired by access rather than only those it
          -- established by mapping.  Purely a TLB-model event
          -- (`tlbFillIpcBufferOnCore_frame`), and inert when the syscall
          -- carried no overflow registers.
          -- WS-SM SM9.D.7: **the taint propagation seam is inherited, not
          -- repeated.**  `dispatchSyscallChecked` applies the plan to the state
          -- it was handed, so this entry gets it by passing the filled state and
          -- returning what comes back — the same plan, the same pre-state, the
          -- same post-state as when the two lines lived here.
          --
          -- It moved down one layer in PR #873 round 6.  `dispatchSyscall`'s own
          -- docstring points integrators at `dispatchSyscallChecked` for
          -- production user-space entry, and an integrator who took that advice
          -- called the dispatcher directly and never reached a seam that sat
          -- above it: content moved with no provenance, and a retype kept the
          -- destroyed object's tags.  Putting the seam at the dispatcher makes
          -- every entry inherit it, including one written tomorrow.
          --
          -- One writer, at the dispatcher rather than at the arms, for the
          -- SM7.F.5 reason one layer on: keeping the write out of the
          -- transitions leaves every IPC frame, invariant and non-interference
          -- result untouched (`applySyscallTaint_frame`,
          -- `storeObject_declassificationTaint_eq`).  The classification
          -- `contentFlowClass` is total on `SyscallId`, so a new syscall is a
          -- missing case at elaboration; that its *callees* do not move content
          -- the declared edges miss is checked by reach, in
          -- `scripts/check_content_flow_coverage.py`.
          --
          -- The filled state is bound ONCE.  It used to be spelled out three
          -- times — for the dispatch, for the taint plan, and as the plan's
          -- pre-state — on the reasoning that an intermediate binding would stop
          -- the downstream carriage proofs from `split`ting on a bare `match`.
          -- That is true of `have`, which is opaque, but not of `let`, which
          -- zeta-reduces and stays transparent to `split`.  Three evaluations of
          -- a TCB/VSpace resolution (and, with overflow registers, of the page
          -- fold and the TLB-table update) on every successful syscall was the
          -- cost of the stronger reading.
          let stFilled :=
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore
              st executingCore tid decoded.overflowCount
          dispatchSyscallChecked ctx decoded tid executingCore stFilled

-- ============================================================================
-- U5-A/U5-D: Dispatch structural equivalence theorems
-- ============================================================================

/-- U5-A/U-M02/V8-H/D1: The capability-only syscalls are handled identically by
both checked and unchecked dispatch paths, since both delegate to
`dispatchCapabilityOnly`. These arms derive authority entirely from
capability possession and do not cross security domains.

The shared arms are: `.cspaceDelete`, `.vspaceMap`,
`.vspaceUnmap`, `.schedContextConfigure`,
`.schedContextBind`, `.schedContextUnbind`, `.tcbSuspend`, `.tcbResume`.  The
two service arms, `.serviceRevoke` and `.serviceQuery`, are the unchecked arm
behind a flow gate (`dispatchCapabilityOnlyChecked`), equal to it when the gate
admits.

V8-H/D3: With the shared helper extraction, each per-arm theorem follows
directly from the shared `dispatchCapabilityOnly` delegation. -/
theorem checkedDispatch_cspaceDelete_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .cspaceDelete) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
    dispatchWithCap decoded tid executingCore gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- U5-A/V8-H: Structural equivalence for `.vspaceMap`. -/
theorem checkedDispatch_vspaceMap_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .vspaceMap) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
    dispatchWithCap decoded tid executingCore gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- U5-A/V8-H: Structural equivalence for `.vspaceUnmap`. -/
theorem checkedDispatch_vspaceUnmap_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .vspaceUnmap) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
    dispatchWithCap decoded tid executingCore gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- The checked `.serviceRevoke` arm is the unchecked one behind the write gate:
the policy-checked revoke `revokeServiceChecked` at the endpoint the capability
names. -/
theorem dispatchWithCapChecked_serviceRevoke_eq
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (epId : SeLe4n.ObjId)
    (hSyscall : decoded.syscallId = .serviceRevoke) (hTarget : cap.target = .object epId) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
    revokeServiceChecked ctx tid epId := by
  simp only [dispatchWithCapChecked, dispatchCapabilityOnly, hSyscall, hTarget,
    dispatchCapabilityOnlyChecked]

/-- ...and when the write is admitted it is the unchecked arm. -/
theorem checkedDispatch_serviceRevoke_eq_unchecked_of_admitted
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (epId : SeLe4n.ObjId)
    (hSyscall : decoded.syscallId = .serviceRevoke) (hTarget : cap.target = .object epId)
    (hAdm : serviceEndpointWriteAdmitted ctx tid epId = true) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
    dispatchWithCap decoded tid executingCore gate cap := by
  funext st
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget,
    dispatchCapabilityOnlyChecked, revokeServiceChecked, hAdm]

/-- The checked `.serviceQuery` arm is the unchecked one behind the read gate:
`serviceQueryStaged`, the arm's staging over the policy-checked lookup
`lookupServiceChecked`. -/
theorem dispatchWithCapChecked_serviceQuery_eq
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (epId : SeLe4n.ObjId)
    (hSyscall : decoded.syscallId = .serviceQuery) (hTarget : cap.target = .object epId) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
      serviceQueryStaged ctx tid epId := by
  simp only [dispatchWithCapChecked, dispatchCapabilityOnly, hSyscall, hTarget,
    dispatchCapabilityOnlyChecked]

/-- ...and when the read is admitted it is the unchecked arm. -/
theorem checkedDispatch_serviceQuery_eq_unchecked_of_admitted
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (epId : SeLe4n.ObjId)
    (hSyscall : decoded.syscallId = .serviceQuery) (hTarget : cap.target = .object epId)
    (hAdm : serviceEndpointReadAdmitted ctx tid epId = true) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
    dispatchWithCap decoded tid executingCore gate cap := by
  funext st
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget,
    dispatchCapabilityOnlyChecked, serviceQueryStaged, lookupServiceChecked, hAdm]
  rfl

/-- **The query refuses an endpoint the caller may not read**, before any lookup:
whatever the endpoint records, and whether it records anything, the checked
`.serviceQuery` arm answers `flowDenied` when the endpoint's label does not flow
to the caller's.  The refusal reads labels only, so it says nothing about the
registry or the endpoint. -/
theorem dispatchWithCapChecked_serviceQuery_refuses_unreadable_endpoint
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (epId : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .serviceQuery) (hTarget : cap.target = .object epId)
    (hAdm : serviceEndpointReadAdmitted ctx tid epId = false) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .error .flowDenied := by
  rw [dispatchWithCapChecked_serviceQuery_eq ctx decoded tid executingCore gate cap epId
    hSyscall hTarget]
  simp [serviceQueryStaged, lookupServiceChecked, hAdm]

/-- **The revoke refuses an endpoint the caller may not write**, before reading
what it records. -/
theorem dispatchWithCapChecked_serviceRevoke_refuses_unwritable_endpoint
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (epId : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .serviceRevoke) (hTarget : cap.target = .object epId)
    (hAdm : serviceEndpointWriteAdmitted ctx tid epId = false) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .error .flowDenied := by
  rw [dispatchWithCapChecked_serviceRevoke_eq ctx decoded tid executingCore gate cap epId
    hSyscall hTarget]
  simp [revokeServiceChecked, hAdm]

/-- **The revoke removes the registration the invoked endpoint records, and no
other.**  The service is the one the endpoint records (`serviceRegistered`,
under the endpoint's own id), never named by a caller-supplied word: the arm
reads no message register. -/
theorem dispatchWithCapChecked_serviceRevoke_removes_recorded_registration
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (epId : SeLe4n.ObjId) (st : SystemState)
    (ep : Endpoint)
    (hSyscall : decoded.syscallId = .serviceRevoke) (hTarget : cap.target = .object epId)
    (hAdm : serviceEndpointWriteAdmitted ctx tid epId = true)
    (hEp : st.objects[epId]? = some (.endpoint ep)) (hCode : ep.serviceRegistered = true) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      revokeService (ServiceId.ofNat epId.toNat) st := by
  rw [dispatchWithCapChecked_serviceRevoke_eq ctx decoded tid executingCore gate cap epId
    hSyscall hTarget]
  simp [revokeServiceChecked, hAdm, revokeServiceByRecordedRegistration, SystemState.getObject?, hEp,
    hCode]

/-- **A revoke through a capability to an object that records no service fails
with `objectNotFound` and removes nothing**: a non-endpoint, a missing object,
or an endpoint whose registration was already revoked.  A capability to an
unrelated object therefore cannot reach another endpoint's registration. -/
theorem dispatchWithCapChecked_serviceRevoke_objectNotFound_of_unrecorded
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (epId : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .serviceRevoke) (hTarget : cap.target = .object epId)
    (hAdm : serviceEndpointWriteAdmitted ctx tid epId = true)
    (hNone : ∀ ep, st.objects[epId]? = some (.endpoint ep) → ep.serviceRegistered = false) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .error .objectNotFound := by
  rw [dispatchWithCapChecked_serviceRevoke_eq ctx decoded tid executingCore gate cap epId
    hSyscall hTarget]
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
    (gate : SyscallGate) (cap : Capability) (epId : SeLe4n.ObjId) (st : SystemState)
    (args : Architecture.SyscallArgDecode.ServiceRegisterArgs)
    (hSyscall : decoded.syscallId = .serviceRegister) (hTarget : cap.target = .object epId)
    (hArgs : Architecture.SyscallArgDecode.decodeServiceRegisterArgs decoded = .ok args)
    (hAdm : serviceEndpointWriteAdmitted ctx tid epId = false) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .error .flowDenied := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, hSyscall, hTarget, hArgs,
    registerServiceChecked, registrationWriteAdmitted, hAdm]

/-- Z5-J: Structural equivalence for `.schedContextConfigure`. -/
theorem checkedDispatch_schedContextConfigure_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .schedContextConfigure) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
    dispatchWithCap decoded tid executingCore gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- Z5-J: Structural equivalence for `.schedContextBind`. -/
theorem checkedDispatch_schedContextBind_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .schedContextBind) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
    dispatchWithCap decoded tid executingCore gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- Z5-J: Structural equivalence for `.schedContextUnbind`. -/
theorem checkedDispatch_schedContextUnbind_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .schedContextUnbind) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
    dispatchWithCap decoded tid executingCore gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- D1: Structural equivalence for `.tcbSuspend`. -/
theorem checkedDispatch_tcbSuspend_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .tcbSuspend) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
    dispatchWithCap decoded tid executingCore gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- D1: Structural equivalence for `.tcbResume`. -/
theorem checkedDispatch_tcbResume_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .tcbResume) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
    dispatchWithCap decoded tid executingCore gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- AE1-A: Structural equivalence for `.tcbSetPriority`. -/
theorem checkedDispatch_tcbSetPriority_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .tcbSetPriority) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
    dispatchWithCap decoded tid executingCore gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- AE1-A: Structural equivalence for `.tcbSetMCPriority`. -/
theorem checkedDispatch_tcbSetMCPriority_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .tcbSetMCPriority) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
    dispatchWithCap decoded tid executingCore gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- AE1-B: Structural equivalence for `.tcbSetIPCBuffer`. -/
theorem checkedDispatch_tcbSetIPCBuffer_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .tcbSetIPCBuffer) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
    dispatchWithCap decoded tid executingCore gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- **WS-SM SM7.D** (PR #845 review, P2): Structural equivalence for
`.vspaceUnifyInstruction`.  Its arm lives in the shared `dispatchCapabilityOnly`
helper like its siblings, so the checked and unchecked paths are identical. -/
theorem checkedDispatch_vspaceUnifyInstruction_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .vspaceUnifyInstruction) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
    dispatchWithCap decoded tid executingCore gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- **PR #822 Phase H** (PR #845 review, P2): Structural equivalence for
`.mintReplyCap` — the other arm that was handled by `dispatchCapabilityOnly`
without a per-arm equivalence theorem. -/
theorem checkedDispatch_mintReplyCap_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .mintReplyCap) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
    dispatchWithCap decoded tid executingCore gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- U5-D/U-L20/V8-H/Z5-J/D1/AE1-A/AE1-B: Complete dispatch equivalence — for ALL
capability-only syscalls, the checked and unchecked dispatch paths produce identical
results.

Both `dispatchWithCap` and `dispatchWithCapChecked` delegate to the shared
`dispatchCapabilityOnly` helper for these 13 arms, making structural identity
trivial; the two service arms are the shared arm behind a flow gate, equal to
it when the gate admits (`checkedDispatch_serviceQuery_eq_unchecked_of_admitted`,
`checkedDispatch_serviceRevoke_eq_unchecked_of_admitted`).  PR #845 review (P2): `.vspaceUnifyInstruction` (WS-SM SM7.D) and
`.mintReplyCap` (PR #822 Phase H) were handled by the shared helper but had been
omitted from this enumeration, so a theorem advertised as *complete* did not in
fact cover them.

**Production recommendation**: Use `syscallEntryChecked` for user-space entry.
The unchecked `syscallEntry` is retained for backward compatibility with
existing proofs and internal kernel paths that operate within the TCB. -/
theorem checkedDispatch_capabilityOnly_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (hCapOnly : decoded.syscallId = .cspaceDelete ∨
                decoded.syscallId = .vspaceMap ∨
                decoded.syscallId = .vspaceUnmap ∨
                decoded.syscallId = .schedContextConfigure ∨
                decoded.syscallId = .schedContextBind ∨
                decoded.syscallId = .schedContextUnbind ∨
                decoded.syscallId = .tcbSuspend ∨
                decoded.syscallId = .tcbResume ∨
                decoded.syscallId = .tcbSetPriority ∨
                decoded.syscallId = .tcbSetMCPriority ∨
                decoded.syscallId = .tcbSetIPCBuffer ∨
                decoded.syscallId = .mintReplyCap ∨
                decoded.syscallId = .vspaceUnifyInstruction) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
    dispatchWithCap decoded tid executingCore gate cap := by
  rcases hCapOnly with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, h]

-- ============================================================================
-- AJ1-D (M-01): Reply/ReplyRecv conditional equivalence theorems
-- ============================================================================

/-- AJ1-D (M-01) / WS-SM SM6.C: When the information flow policy allows the reply,
checked and unchecked `.reply` dispatch produce identical results. The checked path
(`endpointReplyCrossCoreDispatchChecked`) gates on `securityFlowsTo replierLabel
targetLabel`; when this condition holds it is *exactly* the unchecked cross-core
dispatch (`endpointReplyCrossCoreDispatchChecked_flow_allowed`), so the two arms —
which apply the identical outer `match … | (st', .ok _) => …` wrapping to the same
dispatch — coincide.

This is a conditional equivalence: unlike the capability-only arms which are
structurally identical (unconditional), `.reply` requires the flow hypothesis.

WS-SM SM6.D: the reply cap names a `ReplyId`; both arms perform the identical
`getReply? rid → reply.caller` resolution, differing only in the
checked-vs-unchecked cross-core dispatch (the single-use consume is folded into
`endpointReplyOnCore` — PR #827 review #3 — so it is identical by construction).
The equivalence therefore holds, at a state where the resolution yields
`callerTid`, exactly when the flow to that resolved caller is allowed. -/
theorem checkedDispatch_reply_eq_unchecked_when_allowed
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .reply)
    (rid : SeLe4n.ReplyId)
    (hCap : cap.target = .replyCap rid)
    (st : SystemState)
    (reply : SeLe4n.Kernel.Reply) (callerTid : SeLe4n.ThreadId)
    (hReply : st.getReply? rid = some reply)
    (hCaller : reply.caller = some callerTid)
    (hFlow : securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf callerTid) = true)
    : dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
    dispatchWithCap decoded tid executingCore gate cap st := by
  -- Unfold both dispatch to the `.reply` arm; resolve the reply linkage with the
  -- resolution hypotheses so both arms reduce to the same cross-core dispatch
  -- (which folds the consume), then collapse checked → unchecked under the flow
  -- guard.
  simp only [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly,
    hSyscall, hCap, replyAnsweredCaller?, hReply, hCaller, Option.bind,
    hFlow, if_true]
  -- WS-RR RR4.14: the seam collapses on *both* branches under the same flow
  -- guard, so the fault branch costs this proof nothing.
  rw [replyTransferOnCoreChecked_eq_unchecked_of_flow_allowed ctx tid callerTid
    decoded.msgInfo decoded.msgRegs _ _ st hFlow]

/-- AJ1-D (M-01) / WS-SM SM6.D: When the information-flow policy allows both legs
(reply + receive), checked and unchecked `.replyRecv` dispatch produce identical
results.  Faithful seL4-MCS: the reply target is the reply object's recorded
`caller` resolved from the server-supplied reply cap
(`resolveReplyRecvReply … = .ok (rid, prevCaller)`); the checked arm gates both
legs — (1) endpoint → receiver (receive leg, checked first, ahead of the reply
probe), (2) receiver → prevCaller (reply leg) — around the *same* `endpointReplyRecvOnCore`
the unchecked arm runs, so when both flows hold the two arms coincide. -/
theorem checkedDispatch_replyRecv_eq_unchecked_when_allowed
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .replyRecv)
    (epId : SeLe4n.ObjId)
    (hCap : cap.target = .object epId)
    (st : SystemState)
    (rid : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (replyBadge : Option SeLe4n.Badge)
    (hResolve : resolveReplyRecvReply gate decoded st = .ok (rid, prevCaller, replyBadge))
    (hFlowReply : securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf prevCaller) = true)
    (hFlowRecv : securityFlowsTo (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = true)
    -- WS-SM SM8.C: the receive leg also consults this endpoint's configured
    -- override, so the two arms coincide only when that admits the flow too.
    (hOverrideRecv : endpointOverrideAllows ctx epId (ctx.endpointLabelOf epId)
      (ctx.threadLabelOf tid) = true) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
    dispatchWithCap decoded tid executingCore gate cap st := by
  have hGate := endpointFlowGate_of ctx epId _ _ hFlowRecv hOverrideRecv
  simp only [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly,
    hSyscall, hCap, hResolve]
  -- The checked arm now gates in two nested steps: the receive leg (`!flowRecv →
  -- .flowDenied`) outermost, then the reply leg (`flowReply → endpointReplyRecvOnCore`,
  -- else `.replyCapInvalid`).  With both flows `true` the outer `!true` is `false`
  -- (else branch) and the inner `if true` selects the same `endpointReplyRecvOnCore` the
  -- unchecked arm runs.
  simp [hGate, hFlowReply]

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
-- W2-C (MED-04): dispatchWithCap wildcard arm unreachability
-- ============================================================================

/-- W2-C (MED-04)/D1/D2/D3/AE1-A/AE1-B: Every `SyscallId` variant is handled by either
    `dispatchCapabilityOnly` (returning `some`) or one of the 11 explicit match
    arms in `dispatchWithCap`. This proves the `| _ => fun _ => .error .illegalState`
    wildcard arm is unreachable at runtime.

    The proof enumerates every `SyscallId` constructor.  The partition is
    `dispatchCapabilityOnly`'s own `match` — which arms it answers `some` for —
    and `dispatchWithCap`'s explicit arms
    (`.send`, `.receive`, `.call`, `.reply`, `.cspaceMint`, `.cspaceCopy`,
    `.cspaceMove`, `.serviceRegister`, `.notificationSignal`, `.notificationWait`,
    `.replyRecv`, `.declassify`, `.declassifySignal`, `.auditRead`,
    `.auditDrain`); everything else is capability-only.

    `v0.35.190`: the two hand-kept totals that used to open this paragraph
    ("15 … the remaining 11") were stale — they summed to 26 against a
    `SyscallId.count` that has been past that since SM9, and neither list was
    the definition's.  A number beside a `match` is a second answer to a
    question the `match` already decides, which is the substitution this project
    retires everywhere else; the list below is the inventory, and `cases sid`
    is what makes it exhaustive.

    AE1-D: The same completeness proof applies to `dispatchWithCapChecked`
    (see `dispatchWithCapChecked_wildcard_unreachable` below). -/
theorem dispatchWithCap_wildcard_unreachable (sid : SyscallId) :
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
            .auditRead, .auditDrain, .tcbSetFaultHandler,
            .cspaceRevoke, .untypedRetype, .untypedReset, .tcbSetSpace,
            .pageTableMap, .pageTableUnmap, .yield, .schedContextConsumed] : List SyscallId) := by
  cases sid <;> simp [List.mem_cons]

/-- AE1-D: Every `SyscallId` variant is handled by either `dispatchCapabilityOnly`
    (returning `some`) or one of the 11 explicit match arms in
    `dispatchWithCapChecked`. This proves the wildcard arm is unreachable.

    This is the checked-dispatch counterpart of `dispatchWithCap_wildcard_unreachable`.
    The proof is identical because both functions share `dispatchCapabilityOnly` and
    have the same set of explicit match arms (modulo checked wrappers). -/
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
            .auditRead, .auditDrain, .tcbSetFaultHandler,
            .cspaceRevoke, .untypedRetype, .untypedReset, .tcbSetSpace,
            .pageTableMap, .pageTableUnmap, .yield, .schedContextConsumed] : List SyscallId) := by
  cases sid <;> simp [List.mem_cons]

/-- WS-J1-C: Route decoded syscall arguments to the appropriate capability-gated
kernel operation. Looks up the caller's TCB and CSpace root, constructs a
`SyscallGate`, and dispatches via `syscallInvoke`.

**Note (T6-I)**: This is the UNCHECKED dispatch path. It does not perform
information-flow checks. For production user-space entry points, use
`dispatchSyscallChecked` which gates cross-domain operations via
`securityFlowsTo` wrappers. This function is retained for:
1. Backward compatibility with existing dispatch delegation theorems
2. Internal kernel paths that operate within the TCB
3. Proof infrastructure (delegation/preservation theorems reference this)

**WS-SM SM9.D.7 (PR #873 round 6): it does carry the taint seam.**  "Unchecked"
names what it does not *gate* — no `securityFlowsTo` wrapper decides whether a
flow is permitted — and provenance is not a gate: it records where content came
from, whatever authority moved it.  A path that skipped it would leave content
moved through this dispatcher untraceable, which is worse on the unchecked route
than on the checked one, not better.  So both dispatchers apply the plan and both
entries inherit it, and the seam is one sentence rather than a list of call sites
that each have to remember. -/
def dispatchSyscall (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : Kernel Unit :=
  fun st =>
    -- Symmetric with `dispatchSyscallChecked`: the caller must be the thread
    -- current on the executing core, or the pair is refused before any lookup
    -- (`dispatchSyscall_ok_caller_current`).
    if st.scheduler.currentOnCore executingCore ≠ some tid then .error .illegalState
    -- WS-ZA ZA4.3: a yield invokes no capability, so it runs before the
    -- caller's CSpace is consulted and moves no content (`contentFlowClass
    -- .yield = .inert`), so no taint step follows it.
    else if decoded.syscallId = .yield then dispatchYield executingCore st
    else
    match st.getObject? tid.toObjId with
    | some (.tcb tcb) =>
      match st.getObject? tcb.cspaceRoot with
      | some (.cnode rootCn) =>
        let gate : SyscallGate := {
          callerId     := tid
          cspaceRoot   := tcb.cspaceRoot
          capAddr      := decoded.capAddr
          capDepth     := rootCn.depth
          requiredRight := syscallRequiredRight decoded.syscallId
        }
        match (syscallInvoke gate (dispatchWithCap decoded tid executingCore gate)) st with
        | .error e => .error e
        | .ok ((), stPost) =>
            .ok ((), applySyscallTaint (syscallTaintPlan st tid decoded) st stPost)
      | some _ => .error .invalidCapability
      | none   => .error .objectNotFound
    | some _ => .error .illegalState
    | none   => .error .objectNotFound

/-- WS-J1-C: Top-level register-sourced syscall entry point.

Reads the current thread's register file, decodes raw register values into
typed kernel references (merging IPC-buffer overflow for 5+ arg syscalls via
`decodeSyscallArgsFromState` — AK4-A), and dispatches to the appropriate
kernel operation. This is the single authoritative user-space → kernel
transition boundary.

The `regCount` parameter (default 32 for ARM64) should match
`MachineConfig.registerCount` of the active platform binding. It is used by
`decodeSyscallArgs` (the legacy register-only decoder that
`decodeSyscallArgsFromState` wraps) to validate that all layout register
indices are within architectural bounds. -/
def syscallEntry (layout : SeLe4n.SyscallRegisterLayout)
    (regCount : Nat := 32) : Kernel Unit :=
  fun st =>
    match (st.scheduler.currentOnCore bootCoreId) with
    | none => .error .illegalState
    | some tid =>
      match lookupThreadRegisterContext tid st with
      | .error e => .error e
      | .ok (regs, _) =>
        -- AK4-A.6 (R-ABI-C01): Use state-aware decode so 5-arg syscalls
        -- merge IPC-buffer overflow registers into `msgRegs`.
        match SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
                st tid layout regs regCount with
        | .error e => .error e
        | .ok decoded =>
          -- WS-SM SM7.F.5: deliberately **no** access-time `perCoreTlb` fill
          -- here.  This is the boot-pinned pre-SMP entry, whose TLB view is
          -- the scalar `st.tlb`; `perCoreTlb` is its per-core refinement and
          -- is filled at the per-core entry (`syscallEntryChecked`), which is
          -- what the SMP dispatch path actually runs.  Filling the per-core
          -- model from the boot-pinned entry would mix the two models.
          --
          -- WS-SM SM9.D.7: the taint seam applies on this route **too**, and
          -- for the opposite reason to the TLB fill above.  The per-core TLB
          -- model is a refinement this entry deliberately does not participate
          -- in; taint is not — provenance is a property of the content a syscall
          -- moves, and this entry moves the same content through the same
          -- transitions.  The modelled SVC route
          -- (`dispatchSynchronousException`) reaches the kernel through here, so
          -- leaving the step out let a send or receive taken by that route carry
          -- content without its provenance following.
          --
          -- PR #873 round 6: inherited from `dispatchSyscall` rather than
          -- repeated here, the same way `syscallEntryChecked` inherits it from
          -- the checked dispatcher.  Both dispatchers carry the seam and both
          -- entries delegate, so the rule is one sentence — *the taint seam sits
          -- at the dispatcher* — instead of a list of entry points that each
          -- have to remember.  An entry written tomorrow inherits it; a caller
          -- who enters at a dispatcher gets it too.
          dispatchSyscall decoded tid bootCoreId st

-- ============================================================================
-- WS-J1-C: Soundness theorems
-- ============================================================================

/-- WS-J1-C / AK4-A.6: If `syscallEntry` succeeds, the state-aware register
    decode (including IPC-buffer overflow merge) returned `.ok`. -/
theorem syscallEntry_requires_valid_decode
    (layout : SeLe4n.SyscallRegisterLayout) (regCount : Nat)
    (st : SystemState) (st' : SystemState)
    (hOk : syscallEntry layout regCount st = .ok ((), st')) :
    ∃ tid regs decoded,
      (st.scheduler.currentOnCore bootCoreId) = some tid ∧
      lookupThreadRegisterContext tid st = .ok (regs, st) ∧
      SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
        st tid layout regs regCount = .ok decoded := by
  unfold syscallEntry at hOk
  split at hOk
  · simp at hOk
  next tid hCurrent =>
    split at hOk
    · simp at hOk
    next regs _st_regs hLookup =>
      split at hOk
      · simp at hOk
      next decoded hDecode =>
        have hStEq : _st_regs = st := by
          unfold lookupThreadRegisterContext SystemState.getObject? at hLookup
          split at hLookup <;> simp at hLookup
          exact hLookup.2.symm
        subst hStEq
        exact ⟨tid, regs, decoded, hCurrent, hLookup, hDecode⟩

/-- WS-J1-C: If `dispatchSyscall` succeeds, the caller held a capability
with the required access right for the invoked syscall. Threads through
`syscallInvoke_requires_right`. -/
theorem dispatchSyscall_requires_right
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (st : SystemState) (st' : SystemState)
    (hCap : decoded.syscallId ≠ .yield)
    (hOk : dispatchSyscall decoded tid executingCore st = .ok ((), st')) :
    ∃ tcb, (SystemState.objects st)[tid.toObjId]? = some (KernelObject.tcb tcb) ∧
      ∃ rootCn, (SystemState.objects st)[tcb.cspaceRoot]? = some (KernelObject.cnode rootCn) ∧
        ∃ cap ref,
          resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth st = .ok ref ∧
          SystemState.lookupSlotCap st ref = some cap ∧
          cap.hasRight (syscallRequiredRight decoded.syscallId) = true := by
  -- `simp only` rather than `unfold`: the gate binding elaborates to a `have`,
  -- which is opaque to `split` (the same distinction `syscallEntryChecked`
  -- records above), and the seam's `match` sits inside it.
  simp only [dispatchSyscall, SystemState.getObject?] at hOk
  -- The caller/core guard: a mismatched pair is refused before any lookup.
  split at hOk
  · exact absurd hOk (by simp)
  split at hOk
  next tcb hTcb =>
    refine ⟨tcb, hTcb, ?_⟩
    split at hOk
    next rootCn hRoot =>
      refine ⟨rootCn, hRoot, ?_⟩
      -- PR #873 round 6: the taint seam wraps the invoke inside the dispatcher,
      -- so the invoke's own success has to be opened before it can be used.
      split at hOk
      · simp at hOk
      next stPost hInvokeOk =>
        have hInvoke := syscallInvoke_requires_right
          { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
            capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
          (dispatchWithCap decoded tid executingCore
            { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
              capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId })
          st () stPost hInvokeOk
        obtain ⟨cap, ref, hResolve, hSlot, hRight⟩ := hInvoke
        exact ⟨cap, ref, hResolve, hSlot, hRight⟩
    · simp at hOk
    · simp at hOk
  · simp at hOk
  · simp at hOk

/-- WS-J1-C: If `syscallEntry` succeeds for a capability-gated operation,
the caller held the required access right. Threads through the existing
`syscallInvoke_requires_right` theorem via `dispatchSyscall_requires_right`.

The conclusion proves the full chain: there exists a current thread with a
valid TCB and CSpace root CNode, the register decode succeeded, and a
capability with the required access right was resolved from the decoded
capAddr through the caller's CSpace. -/
theorem syscallEntry_implies_capability_held
    (layout : SeLe4n.SyscallRegisterLayout) (regCount : Nat)
    (st : SystemState) (st' : SystemState)
    (hOk : syscallEntry layout regCount st = .ok ((), st')) :
    ∃ tid regs decoded,
      (st.scheduler.currentOnCore bootCoreId) = some tid ∧
      lookupThreadRegisterContext tid st = .ok (regs, st) ∧
      SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
        st tid layout regs regCount = .ok decoded ∧
      (decoded.syscallId ≠ .yield →
      ∃ tcb, (SystemState.objects st)[tid.toObjId]? = some (KernelObject.tcb tcb) ∧
        ∃ rootCn, (SystemState.objects st)[tcb.cspaceRoot]? = some (KernelObject.cnode rootCn) ∧
          ∃ cap ref,
            resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth st = .ok ref ∧
            SystemState.lookupSlotCap st ref = some cap ∧
            cap.hasRight (syscallRequiredRight decoded.syscallId) = true) := by
  unfold syscallEntry at hOk
  split at hOk
  · simp at hOk
  next tid hCurrent =>
    split at hOk
    · simp at hOk
    next regs _st_regs hLookup =>
      split at hOk
      · simp at hOk
      next decoded hDecode =>
        have hStEq : _st_regs = st := by
          unfold lookupThreadRegisterContext SystemState.getObject? at hLookup
          split at hLookup <;> simp at hLookup
          exact hLookup.2.symm
        -- PR #873 round 6: the seam moved into `dispatchSyscall`, so the entry
        -- delegates and this hypothesis IS the dispatch's own success.
        subst hStEq
        refine ⟨tid, regs, decoded, hCurrent, hLookup, hDecode, fun hCap => ?_⟩
        exact dispatchSyscall_requires_right decoded tid bootCoreId _ st' hCap hOk

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
is invoked with the decoded source slot, destination slot, rights, and badge
from message registers. CDT-tracked (C-01).  The arm first refuses with
`.objectNotFound` unless the invoked object is a CNode (`cnodeInvoked`). -/
theorem dispatchWithCap_cspaceMint_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (cnodeId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.CSpaceMintArgs)
    (hSyscall : decoded.syscallId = .cspaceMint)
    (hTarget : cap.target = .object cnodeId)
    (hDecode : decodeCSpaceMintArgs decoded = .ok args) :
    dispatchWithCap decoded tid executingCore gate cap =
      let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
      let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
      let badge : Option SeLe4n.Badge :=
        if args.badge.val = 0 then none else some args.badge
      fun st => if !cnodeInvoked cnodeId st then .error .objectNotFound else
        cspaceMintWithCdt src dst args.rights badge st := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode]

/-- WS-K-C: When cspaceCopy dispatch succeeds, the kernel-level `cspaceCopy`
is invoked with the decoded source and destination slots, once the invoked
object is a CNode (`cnodeInvoked`; `.objectNotFound` otherwise). -/
theorem dispatchWithCap_cspaceCopy_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (cnodeId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.CSpaceCopyArgs)
    (hSyscall : decoded.syscallId = .cspaceCopy)
    (hTarget : cap.target = .object cnodeId)
    (hDecode : decodeCSpaceCopyArgs decoded = .ok args) :
    dispatchWithCap decoded tid executingCore gate cap =
      let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
      let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
      fun st => if !cnodeInvoked cnodeId st then .error .objectNotFound else
        cspaceCopy src dst st := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode]

/-- WS-K-C: When cspaceMove dispatch succeeds, the kernel-level `cspaceMove`
is invoked with the decoded source and destination slots, once the invoked
object is a CNode (`cnodeInvoked`; `.objectNotFound` otherwise). -/
theorem dispatchWithCap_cspaceMove_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (cnodeId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.CSpaceMoveArgs)
    (hSyscall : decoded.syscallId = .cspaceMove)
    (hTarget : cap.target = .object cnodeId)
    (hDecode : decodeCSpaceMoveArgs decoded = .ok args) :
    dispatchWithCap decoded tid executingCore gate cap =
      let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
      let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
      fun st => if !cnodeInvoked cnodeId st then .error .objectNotFound else
        cspaceMove src dst st := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode]

/-- WS-K-C / WS-BP BP7.1 (`v0.36.7`): When cspaceDelete dispatch succeeds, the
**finalising** delete runs on the decoded target slot, with the invoking thread's
core as the initiator of the teardown's shootdown rounds: the capability is
deleted and the mapping it recorded, if it records one, is removed.  The arm
first refuses with `.objectNotFound` unless the invoked object is a CNode
(`cnodeInvoked`): a thread's root slots are reachable only by its own TCB
invocations and the kernel's internal teardown. -/
theorem dispatchWithCap_cspaceDelete_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (cnodeId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.CSpaceDeleteArgs) (st : SystemState)
    (hSyscall : decoded.syscallId = .cspaceDelete)
    (hTarget : cap.target = .object cnodeId)
    (hDecode : decodeCSpaceDeleteArgs decoded = .ok args) :
    dispatchWithCap decoded tid executingCore gate cap st =
      if !cnodeInvoked cnodeId st then .error .objectNotFound else
        cspaceDeleteSlotZombie executingCore
          { cnode := cnodeId, slot := args.targetSlot } st := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode]

/-- WS-BP BP7.1 (`v0.36.7`): When cspaceRevoke dispatch succeeds, the
**finalising** CDT revocation runs on the decoded source slot: every derivation
of the capability is destroyed, and every mapping a destroyed frame capability
recorded is removed.  The arm first refuses with `.objectNotFound` unless the
invoked object is a CNode (`cnodeInvoked`). -/
theorem dispatchWithCap_cspaceRevoke_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (cnodeId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.CSpaceDeleteArgs) (st : SystemState)
    (hSyscall : decoded.syscallId = .cspaceRevoke)
    (hTarget : cap.target = .object cnodeId)
    (hDecode : decodeCSpaceDeleteArgs decoded = .ok args) :
    dispatchWithCap decoded tid executingCore gate cap st =
      if !cnodeInvoked cnodeId st then .error .objectNotFound else
        cspaceRevokeCdtFinalising executingCore
          { cnode := cnodeId, slot := args.targetSlot } st := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode]

-- ============================================================================
-- WS-K-D: Lifecycle and VSpace dispatch delegation theorems
-- ============================================================================

/-- WS-K-D/S6-A/T6-C/X2-E / WS-SM SM7.B.9 / WS-SM SM7.F.4(a)+(b)(ii) / WS-BP
BP7.1: When vspaceMap dispatch passes its address-space check it is exactly
`vspaceMapFromFrameCap` — resolve the frame MR2's capability names, admit the
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
theorem dispatchWithCap_vspaceMap_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.VSpaceMapArgs)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .vspaceMap)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeVSpaceMapArgs decoded st.machine.maxASID = .ok args)
    -- PR #845 review (P1): the capability must name the operand ASID's VSpace
    -- root.  Without this premise the delegation is *false*, because an
    -- unauthorized caller is now rejected with `.illegalAuthority` before the
    -- transition runs.
    (hAuth : vspaceCapAuthorizesAsid cap args.asid st = true) :
    dispatchWithCap decoded tid executingCore gate cap st = vspaceMapFromFrameCap tid executingCore args st := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode, hAuth]

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
theorem dispatchWithCap_vspaceUnifyInstruction_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.VSpaceUnifyInstructionArgs)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .vspaceUnifyInstruction)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeVSpaceUnifyInstructionArgs decoded st.machine.maxASID = .ok args)
    -- PR #845 review (P1): the capability must name the operand ASID's VSpace
    -- root; an unauthorized caller is rejected with `.illegalAuthority`.
    (hAuth : vspaceCapAuthorizesAsid cap args.asid st = true) :
    dispatchWithCap decoded tid executingCore gate cap st =
      Architecture.vspaceUnifyInstructionPage args.asid args.vaddr st := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode, hAuth]

/-- WS-K-D/S6-A / WS-SM SM7.B.9 / SM7.F.4(b)(i) / SM7.D.1: When vspaceUnmap
dispatch succeeds, `vspaceUnmapPageWithShootdownAndIcacheBroadcast` is invoked
with the caller's executing core and the decoded ASID and vaddr.  The layers, in
order: the flushing + cross-core-shootdown variant prevents use-after-unmap on
every core (SM7.B.9); the `…PerCore` layer additionally retires the operand on
the initiator's own `perCoreTlb` view atomically with the transition
(SM7.F.4(b)(i)); and the SM7.D.1 layer broadcasts a targeted `IC IVAU` across
the shareability domain when the *retired mapping was executable*, so no core
keeps an instruction line fetched through it (the instruction-side twin of the
stale-TLB hazard — the shootdown retires translations, while instruction caches
are tagged by physical address).  A non-executable unmap owes nothing and is
provably inert
(`vspaceUnmapPageWithShootdownAndIcacheBroadcast_non_executable_inert`).  Both
added layers are projection-invisible — `perCoreTlb`, `perCoreICache ∉
projectState` — so the delegation stays trace-equivalent to the plain
`vspaceUnmapPageWithShootdown` on every observable field (`tlbShootdown`
posting, page-table erasure, scalar flush all unchanged). -/
theorem dispatchWithCap_vspaceUnmap_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.VSpaceUnmapArgs)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .vspaceUnmap)
    (hTarget : cap.target = .object objId)
    -- AH3-C: decode now takes st.machine.maxASID from the platform config
    (hDecode : decodeVSpaceUnmapArgs decoded st.machine.maxASID = .ok args)
    -- PR #845 review (P1): the capability must name the operand ASID's VSpace
    -- root; an unauthorized caller is rejected with `.illegalAuthority`.
    (hAuth : vspaceCapAuthorizesAsid cap args.asid st = true) :
    dispatchWithCap decoded tid executingCore gate cap st =
      Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast
        executingCore args.asid args.vaddr st := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode, hAuth]

/-- WS-ZA ZA5.4 part 14: the live `.untypedRetype` arm *is* the carve — every
kernel object is made this way — at the invoking thread's executing core, whose
domain and affinity a carved thread takes, and the untyped the capability names.
The arm's operands are the decoded message registers. -/
theorem dispatchWithCap_untypedRetype_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (untypedId : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .untypedRetype)
    (hTarget : cap.target = .object untypedId) :
    dispatchWithCap decoded tid executingCore gate cap st =
      untypedRetypeFromCap tid executingCore decoded.capAddr
        (decodeUntypedRetypeArgs decoded) st := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget]

/-- WS-BP BP7.1 (slice 3): the live `.untypedReset` arm *is* the reset, through
the invoked slot (`untypedResetFromCap`), for a capability naming an object.  The
arm decodes no message register: the capability is the whole operand. -/
theorem dispatchWithCap_untypedReset_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (untypedId : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .untypedReset)
    (hTarget : cap.target = .object untypedId) :
    dispatchWithCap decoded tid executingCore gate cap st =
      untypedResetFromCap tid decoded.capAddr st := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget]

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

/-- **Fail-closed**: `.vspaceMap` dispatch rejects a capability that does not
name the operand ASID's VSpace root, without running the transition. -/
theorem dispatchWithCap_vspaceMap_unauthorized
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.VSpaceMapArgs)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .vspaceMap)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeVSpaceMapArgs decoded st.machine.maxASID = .ok args)
    (hAuth : vspaceCapAuthorizesAsid cap args.asid st = false) :
    dispatchWithCap decoded tid executingCore gate cap st = .error .illegalAuthority := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode, hAuth]

/-- **WS-BP BP7.1 (fail-closed, the vulnerability's closure)**: authority over
the address space is not authority over the memory.  A caller whose capability
*does* name the operand ASID's VSpace root — the full address-space authority
PR #845's binding asks for — still maps nothing unless MR2 resolves, through the
caller's own CSpace with `.read`, to a capability naming a frame the store
holds: the resolver's error is returned and no page table is touched.  Before
this version the arm mapped a raw physical address from MR2, so that VSpace
capability alone was authority over every page of physical memory. -/
theorem dispatchWithCap_vspaceMap_requires_frame_cap
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.VSpaceMapArgs)
    (st : SystemState) (e : KernelError)
    (hSyscall : decoded.syscallId = .vspaceMap)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeVSpaceMapArgs decoded st.machine.maxASID = .ok args)
    (hAuth : vspaceCapAuthorizesAsid cap args.asid st = true)
    (hNoFrame : resolveVSpaceMapFrame tid args st = .error e) :
    dispatchWithCap decoded tid executingCore gate cap st = .error e := by
  rw [dispatchWithCap_vspaceMap_delegates decoded tid executingCore gate cap objId args st
    hSyscall hTarget hDecode hAuth]
  simp [vspaceMapFromFrameCap, hNoFrame]

/-- **WS-BP BP7.1**: and a successful `.vspaceMap` installs the frame the caller
holds a capability to — the physical address is that frame's `base`, taken from
the object the capability names and from nothing the caller wrote. -/
theorem dispatchWithCap_vspaceMap_maps_frame_base
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.VSpaceMapArgs)
    (st st' : SystemState)
    (hSyscall : decoded.syscallId = .vspaceMap)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeVSpaceMapArgs decoded st.machine.maxASID = .ok args)
    (hAuth : vspaceCapAuthorizesAsid cap args.asid st = true)
    (hOk : dispatchWithCap decoded tid executingCore gate cap st = .ok ((), st')) :
    ∃ (frameSlot : CSpaceAddr) (frameCap : Capability) (frame : FrameObject)
      (st1 : SystemState),
      resolveVSpaceMapFrame tid args st = .ok (frameSlot, frameCap, frame) ∧
      Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore
        executingCore args.asid args.vaddr frame.base args.perms st
        = .ok ((), st1) ∧
      ∃ (epoch : Nat) (st2 : SystemState),
        tagFrameMapping args.asid args.vaddr (frameCapObjId frameCap) st1 = .ok (epoch, st2) ∧
        cspaceRecordFrameMapping frameSlot
          { asid := args.asid, vaddr := args.vaddr, epoch := epoch } st2 = .ok ((), st') := by
  rw [dispatchWithCap_vspaceMap_delegates decoded tid executingCore gate cap objId args st
    hSyscall hTarget hDecode hAuth] at hOk
  obtain ⟨frameSlot, frameCap, frame, st1, hR, _, _, _, _, hMap, hRec⟩ :=
    vspaceMapFromFrameCap_ok tid executingCore args st st' hOk
  exact ⟨frameSlot, frameCap, frame, st1, hR, hMap, hRec⟩

/-- **Fail-closed**: `.vspaceUnmap` dispatch rejects a capability that does not
name the operand ASID's VSpace root, leaving the address space intact.  This is
the theorem that would have failed before the binding landed: a caller holding a
writable capability to *any* object could unmap pages in an address space it had
no capability for. -/
theorem dispatchWithCap_vspaceUnmap_unauthorized
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.VSpaceUnmapArgs)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .vspaceUnmap)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeVSpaceUnmapArgs decoded st.machine.maxASID = .ok args)
    (hAuth : vspaceCapAuthorizesAsid cap args.asid st = false) :
    dispatchWithCap decoded tid executingCore gate cap st = .error .illegalAuthority := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode, hAuth]

/-- **Fail-closed**: `.vspaceUnifyInstruction` dispatch rejects a capability that
does not name the operand ASID's VSpace root, so the cache-maintenance path
cannot be used to probe another address space's mappings. -/
theorem dispatchWithCap_vspaceUnifyInstruction_unauthorized
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.VSpaceUnifyInstructionArgs)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .vspaceUnifyInstruction)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeVSpaceUnifyInstructionArgs decoded st.machine.maxASID = .ok args)
    (hAuth : vspaceCapAuthorizesAsid cap args.asid st = false) :
    dispatchWithCap decoded tid executingCore gate cap st = .error .illegalAuthority := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode, hAuth]

-- ============================================================================
-- WS-K-E: Service policy and IPC message population delegation theorems
-- ============================================================================

/-- WS-K-E/M-D01 / WS-SM SM8.B: When send dispatch is invoked, the IPC message
includes resolved extra capabilities and routes through the **cross-core**
WithCaps send (`endpointSendDualWithCapsOnCore` — the per-core send with home-core
receiver wake and executing-core sender deschedule), at `executingCore` — the
core the syscall trapped on, threaded from the entry. -/
theorem dispatchWithCap_send_uses_withCaps
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (epId : SeLe4n.ObjId)
    (hSyscall : decoded.syscallId = .send)
    (hTarget : cap.target = .object epId) :
    dispatchWithCap decoded tid executingCore gate cap =
      fun st =>
        -- WS-ZA ZA4.7 (seL4 `sendIPC`): the send is handed only the badge and
        -- the grant bit of the invoked capability.  The words are read from the
        -- sender's own frame at delivery, and the extra capabilities are looked up
        -- only on the arm that delivers (a send that blocks resolves none; its
        -- receiver looks them up at the rendezvous).
        let payload : SendPayload := .frame cap.badge (cap.rights.mem .grant)
        let wokenReceiver? := (st.getEndpoint? epId).bind (·.receiveQ.head)
        match endpointSendDualWithCapsOnCore epId tid payload
            decoded.capRecvSlot executingCore st with
        | (_, .error e) => .error e
        | (st', .ok (summary, _)) =>
            match clearWokenReceiverStash wokenReceiver? st' with
            | .error e => .error e
            | .ok ((), st'') =>
                .ok ((), Architecture.stageWokenDelivery st'' wokenReceiver?
                          summary.installedCount) := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget]

/-- WS-K-E/M-D01 / WS-SM SM6.A: When call dispatch is invoked, the IPC message
includes resolved extra capabilities and routes through the **cross-core** call
dispatch (`endpointCallCrossCoreDispatch` — the WithCaps call with home-core
receiver wake + donation), at `executingCore` — the core the syscall trapped
on, threaded from the entry. -/
theorem dispatchWithCap_call_uses_crossCoreDispatch
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (epId : SeLe4n.ObjId)
    (hSyscall : decoded.syscallId = .call)
    (hTarget : cap.target = .object epId) :
    dispatchWithCap decoded tid executingCore gate cap =
      fun st =>
        -- WS-ZA ZA4.7 (seL4 `sendIPC`): the send is handed only the badge and
        -- the grant bit of the invoked capability.  The words are read from the
        -- sender's own frame at delivery, and the extra capabilities are looked up
        -- only on the arm that delivers (a send that blocks resolves none; its
        -- receiver looks them up at the rendezvous).
        let payload : SendPayload := .frame cap.badge (cap.rights.mem .grant)
        -- WS-SM SM6.D (#7.3b fold): server-first reply linkage is atomic with the
        -- rendezvous inside `endpointCallOnCore` (`linkServerStashedReply`); no
        -- separate post-dispatch link step.
        -- WS-RA RA.B.5b: the woken receiver's staged frame rides in the RHS.
        let wokenReceiver? := (st.getEndpoint? epId).bind (·.receiveQ.head)
        match endpointCallCrossCoreDispatch epId tid payload
            decoded.capRecvSlot executingCore st with
        | (st', .ok (summary, _)) =>
            .ok ((), Architecture.stageWokenDelivery st' wokenReceiver?
                      summary.installedCount)
        | (_, .error e) => .error e := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget]

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
theorem dispatchWithCap_reply_populates_msg
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (rid : SeLe4n.ReplyId)
    (hSyscall : decoded.syscallId = .reply)
    (hTarget : cap.target = .replyCap rid) :
    dispatchWithCap decoded tid executingCore gate cap =
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
            replyTransferOnCore tid callerTid decoded.msgInfo decoded.msgRegs
              { registers := body, badge := cap.badge } executingCore st := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget]

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

/-- RA.B.8, `.notificationWait` (`.badge`): the arm's badge-consume path
stages exactly the consumed badge, and the boundary read recovers it. -/
theorem dispatchArm_notificationWait_matches_returnShape
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (notifId : SeLe4n.ObjId) (st st1 : SystemState)
    (badge : SeLe4n.Badge) (tcb : TCB)
    (hSyscall : decoded.syscallId = .notificationWait)
    (hTarget : cap.target = .object notifId)
    (hDispatch : notificationWaitCrossCoreDispatch notifId tid executingCore st = (st1, .ok (some badge)))
    (hTcb : st1.getTcb? tid = some tcb)
    (hObjInv : st1.objects.invExt) :
    Architecture.syscallReturnShape .notificationWait = .badge ∧
    ∃ stPost, dispatchWithCap decoded tid executingCore gate cap st = .ok ((), stPost) ∧
      Architecture.readReturnFrame stPost tid
        = Architecture.returnFrameOfBadge badge := by
  refine ⟨rfl,
    Architecture.writeReturnFrameToTcb st1 tid (Architecture.returnFrameOfBadge badge),
    ?_, ?_⟩
  · simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDispatch]
  · exact Architecture.readReturnFrame_writeReturnFrame st1 tid _ tcb hTcb hObjInv

/-- RA.B.8, `.serviceQuery` (`.word`): the arm stages the resolved
registration's `ServiceId` — the answer it used to discard — and the
boundary read recovers it.  Stated like its four siblings, over the live
dispatch at the given state, so the lookup hypothesis is load-bearing (a
first draft concluded only the arm's generic function equality and never
consumed `hLookup` — the decorative-hypothesis defect class SM8.D's
review history records). -/
theorem dispatchArm_serviceQuery_matches_returnShape
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (epId : SeLe4n.ObjId) (st st' : SystemState)
    (reg : ServiceRegistration) (tcb : TCB)
    (hSyscall : decoded.syscallId = .serviceQuery)
    (hTarget : cap.target = .object epId)
    (hLookup : lookupServiceByRecordedRegistration epId st = .ok (reg, st'))
    (hTcb : st'.getTcb? tid = some tcb)
    (hObjInv : st'.objects.invExt) :
    Architecture.syscallReturnShape .serviceQuery = .word ∧
    ∃ stPost, dispatchWithCap decoded tid executingCore gate cap st = .ok ((), stPost) ∧
      Architecture.readReturnFrame stPost tid
        = Architecture.returnFrameOfWord reg.sid.val.toUInt64 := by
  refine ⟨rfl,
    Architecture.writeReturnFrameToTcb st' tid
      (Architecture.returnFrameOfWord reg.sid.val.toUInt64),
    ?_, ?_⟩
  · simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hLookup]
  · exact Architecture.readReturnFrame_writeReturnFrame st' tid _ tcb hTcb hObjInv

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
    (hTarget : cap.target = .auditTrail)
    (hRight : cap.hasRight gate.requiredRight = true)
    (hArgs : Architecture.SyscallArgDecode.decodeAuditReadArgs decoded = .ok args)
    (hOp : decodeAuditReadOp args.opcode args.index args.chunk = some op)
    (hRead : auditReadFromCore (liftLegacyContext ctx) (validatedAuditMonitorClearance ctx)
      executingCore op st = .ok (w, st'))
    (hTcb : st'.getTcb? tid = some tcb)
    (hObjInv : st'.objects.invExt) :
    Architecture.syscallReturnShape .auditRead = .word ∧
    ∃ stPost, dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), stPost) ∧
      Architecture.readReturnFrame stPost tid
        = Architecture.returnFrameOfWord w.toUInt64 := by
  refine ⟨rfl,
    Architecture.writeReturnFrameToTcb st' tid (Architecture.returnFrameOfWord w.toUInt64),
    ?_, ?_⟩
  · unfold dispatchWithCapChecked dispatchCapabilityOnly
    rw [hSyscall]
    simp only [extractAuditAuthority, hTarget, hRight, hArgs, hOp, hRead, if_true]
  · exact Architecture.readReturnFrame_writeReturnFrame st' tid _ tcb hTcb hObjInv

/-- RA.B.8 / WS-SM SM9.A.10, `.auditDrain` (`.word`): the arm stages the **new
visible length**, which is what a monitor recovering from the capacity cliff
reads to confirm the trail is drained. -/
theorem dispatchArm_auditDrain_matches_returnShape
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability)
    (args : Architecture.SyscallArgDecode.AuditDrainArgs)
    (st st' : SystemState) (n : Nat) (tcb : TCB)
    (hSyscall : decoded.syscallId = .auditDrain)
    (hTarget : cap.target = .auditTrail)
    (hRight : cap.hasRight gate.requiredRight = true)
    (hArgs : Architecture.SyscallArgDecode.decodeAuditDrainArgs decoded = .ok args)
    (hDrain : auditDrainVisiblePrefix (liftLegacyContext ctx)
      (validatedAuditMonitorClearance ctx)
      executingCore args.count st = .ok (n, st'))
    (hTcb : st'.getTcb? tid = some tcb)
    (hObjInv : st'.objects.invExt) :
    Architecture.syscallReturnShape .auditDrain = .word ∧
    ∃ stPost, dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), stPost) ∧
      Architecture.readReturnFrame stPost tid
        = Architecture.returnFrameOfWord n.toUInt64 := by
  refine ⟨rfl,
    Architecture.writeReturnFrameToTcb st' tid (Architecture.returnFrameOfWord n.toUInt64),
    ?_, ?_⟩
  · unfold dispatchWithCapChecked dispatchCapabilityOnly
    rw [hSyscall]
    simp only [extractAuditAuthority, hTarget, hRight, hArgs, hDrain, if_true]
  · exact Architecture.readReturnFrame_writeReturnFrame st' tid _ tcb hTcb hObjInv

/-- RA.B.8, `.receive` (`.message`): the arm's non-blocking consume stages
the delivered message — the boundary read is of the fresh delivery, not the
caller's staged arguments.  The delivery hypotheses are read at the state
the caller-staging runs from (post the sender-completion staging, which
writes only the *sender's* saved context). -/
theorem dispatchArm_receive_matches_returnShape
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (epId : SeLe4n.ObjId)
    (replyIdOpt : Option SeLe4n.ReplyId) (st st' stDon : SystemState)
    (next : SeLe4n.ThreadId) (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (summary : CapTransferSummary) (msg : IpcMessage) (tcb : TCB)
    (hSyscall : decoded.syscallId = .receive)
    (hTarget : cap.target = .object epId)
    (hReply : resolveRecvReplyId gate decoded st = .ok replyIdOpt)
    -- PR #873 round 6: the arm runs the WithCaps per-core receive, so the
    -- hypothesis names that transition and the staged `extraCaps` is the
    -- transfer summary's installed count rather than a hardcoded zero.
    (hDispatch : endpointReceiveDualWithCapsOnCore epId tid replyIdOpt gate.cspaceRoot
        decoded.capRecvSlot executingCore st
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
        = .ok stDon)
    (hTcb : (Architecture.stageWokenSendCompletion stDon
        ((st.getEndpoint? epId).bind (·.sendQ.head))).getTcb? tid = some tcb)
    (hReady : tcb.ipcState = .ready)
    (hMsg : tcb.pendingMessage = some msg)
    (hObjInv : (Architecture.stageWokenSendCompletion stDon
        ((st.getEndpoint? epId).bind (·.sendQ.head))).objects.invExt) :
    Architecture.syscallReturnShape .receive = .message ∧
    ∃ stPost, dispatchWithCap decoded tid executingCore gate cap st = .ok ((), stPost) ∧
      Architecture.readReturnFrame stPost tid
        = Architecture.returnFrameOfMessage msg summary.installedCount
            (Architecture.messageOverflowWrites (Architecture.stageWokenSendCompletion stDon
              ((st.getEndpoint? epId).bind (·.sendQ.head))) tcb msg).length := by
  refine ⟨rfl,
    Architecture.stageDeliveredMessage
      (Architecture.stageWokenSendCompletion stDon
        ((st.getEndpoint? epId).bind (·.sendQ.head))) tid summary.installedCount,
    ?_, ?_⟩
  · simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hReply, hDispatch, hDon]
  · exact Architecture.blockedReturn_staged_in_waiter_frame _ tid tcb msg
      summary.installedCount hTcb hReady hMsg hObjInv

/-- RA.B.8, `.replyRecv` (`.message`): the compound arm's receive leg stages
the delivered message for the server exactly as `.receive` does — and, since
PR #873 round 7, with the same honest `extraCaps`: the transfer summary the
WithCaps receive leg returns, not a zero. -/
theorem dispatchArm_replyRecv_matches_returnShape
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (epId : SeLe4n.ObjId)
    (rid : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (replyBadge : Option SeLe4n.Badge)
    (st stB : SystemState) (msg : IpcMessage) (tcb : TCB) (summary : CapTransferSummary)
    (hSyscall : decoded.syscallId = .replyRecv)
    (hTarget : cap.target = .object epId)
    (hResolve : resolveReplyRecvReply gate decoded st = .ok (rid, prevCaller, replyBadge))
    (hBody : endpointReplyRecvOnCore epId tid rid prevCaller
        { registers := (extractMessageRegisters decoded.msgRegs decoded.msgInfo).extract 1
            (extractMessageRegisters decoded.msgRegs decoded.msgInfo).size,
          badge := replyBadge }
        gate.cspaceRoot decoded.capRecvSlot
        executingCore st = .ok (summary, stB))
    (hTcb : stB.getTcb? tid = some tcb)
    (hReady : tcb.ipcState = .ready)
    (hMsg : tcb.pendingMessage = some msg)
    (hObjInv : stB.objects.invExt) :
    Architecture.syscallReturnShape .replyRecv = .message ∧
    ∃ stPost, dispatchWithCap decoded tid executingCore gate cap st = .ok ((), stPost) ∧
      Architecture.readReturnFrame stPost tid
        = Architecture.returnFrameOfMessage msg summary.installedCount
            (Architecture.messageOverflowWrites stB tcb msg).length := by
  refine ⟨rfl, Architecture.stageDeliveredMessage stB tid summary.installedCount, ?_, ?_⟩
  · simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hResolve, hBody]
  · exact Architecture.blockedReturn_staged_in_waiter_frame stB tid tcb msg
      summary.installedCount hTcb hReady hMsg hObjInv

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
delivery is itself a Call, and the two cannot be the same one. -/
theorem dispatchArm_call_frame_delivered_by_reply
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (rid : SeLe4n.ReplyId) (reply : Reply)
    (callerTid : SeLe4n.ThreadId) (st st1 : SystemState)
    (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (msg : IpcMessage) (tcb : TCB)
    (hSyscall : decoded.syscallId = .reply)
    (hTarget : cap.target = .replyCap rid)
    (hReply : st.getReply? rid = some reply)
    (hCaller : reply.caller = some callerTid)
    (hNoFault : threadHasPendingFault st callerTid = false)
    (hDispatch : endpointReplyCrossCoreDispatch tid callerTid
        { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo,
          badge := cap.badge }
        executingCore st = (st1, .ok sgi))
    (hTcb : st1.getTcb? callerTid = some tcb)
    (hReady : tcb.ipcState = .ready)
    (hMsg : tcb.pendingMessage = some msg)
    (hObjInv : st1.objects.invExt) :
    Architecture.syscallReturnShape .call = .message ∧
    ∃ stPost, dispatchWithCap decoded tid executingCore gate cap st = .ok ((), stPost) ∧
      Architecture.readReturnFrame stPost callerTid
        = Architecture.returnFrameOfMessage msg 0
            (Architecture.messageOverflowWrites st1 tcb msg).length := by
  refine ⟨rfl, Architecture.stageDeliveredMessage st1 callerTid 0, ?_, ?_⟩
  · simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget,
      replyAnsweredCaller?, hReply, hCaller, replyTransferOnCore, hNoFault, hDispatch]
  · exact Architecture.blockedReturn_staged_in_waiter_frame st1 callerTid tcb msg 0
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

/-- WS-SM SM6.D: `syscallLookupReplyId` is read-only — it only resolves and
inspects a capability, so the state is unchanged on success. -/
theorem syscallLookupReplyId_preserves_state
    (gate : SyscallGate) (st st' : SystemState) (rid : SeLe4n.ReplyId)
    (hOk : syscallLookupReplyId gate st = .ok (rid, st')) :
    st' = st := by
  unfold syscallLookupReplyId at hOk
  split at hOk
  · simp at hOk
  · next cap st'' hLook =>
    split at hOk
    · simp at hOk
    · next rid' hExtract =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
      exact hOk.2 ▸ syscallLookupCap_preserves_state gate st st'' cap hLook

/-- WS-J1-D: `syscallEntry` error paths preserve `proofLayerInvariantBundle`
trivially — the state is unchanged on error. -/
theorem syscallEntry_error_preserves_proofLayerInvariantBundle
    (layout : SeLe4n.SyscallRegisterLayout) (regCount : Nat)
    (st : SystemState) (e : KernelError)
    (hInv : Architecture.proofLayerInvariantBundle st)
    (_hErr : syscallEntry layout regCount st = .error e) :
    Architecture.proofLayerInvariantBundle st :=
  hInv

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

/-- WS-J1-D: `syscallEntry` success path — if the pre-state satisfies
`proofLayerInvariantBundle` and the underlying dispatched operation preserves
it, then the post-state also satisfies the bundle.

This theorem is compositional: it factors the proof into (1) pure decode
(no state change), (2) read-only cap lookup (no state change), and
(3) the underlying operation's preservation property. The caller provides
the operation-level preservation hypothesis. -/
theorem syscallEntry_preserves_proofLayerInvariantBundle
    (layout : SeLe4n.SyscallRegisterLayout) (regCount : Nat)
    (st st' : SystemState)
    (hInv : Architecture.proofLayerInvariantBundle st)
    (hOk : syscallEntry layout regCount st = .ok ((), st'))
    (hDispatchPres : ∀ decoded tid stD stD',
        Architecture.proofLayerInvariantBundle stD →
        dispatchSyscall decoded tid bootCoreId stD = .ok ((), stD') →
        Architecture.proofLayerInvariantBundle stD') :
    Architecture.proofLayerInvariantBundle st' := by
  -- Extract the successful decode chain
  obtain ⟨tid, regs, decoded, hCur, hLookup, hDecode⟩ :=
    syscallEntry_requires_valid_decode layout regCount st st' hOk
  -- The dispatch operates on the original state (decode is pure, lookup is read-only)
  unfold syscallEntry at hOk
  rw [hCur] at hOk; simp at hOk
  rw [hLookup] at hOk; simp at hOk
  rw [hDecode] at hOk; simp at hOk
  -- PR #873 round 6: the taint seam moved into `dispatchSyscall`, so the entry's
  -- post-state IS the dispatcher's and this is a delegation.  The seam's own
  -- bundle preservation has not gone anywhere — it is
  -- `applySyscallTaint_preserves_proofLayerInvariantBundle` (the table write and,
  -- since WS-ZA ZA5.11, the taint-word write), which is what a discharger of
  -- `hDispatchPres` composes with its per-arm result.
  exact hDispatchPres decoded tid st st' hInv hOk

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

/-- WS-J1-D: `syscallEntry` preserves the observer's projection when the
projection is preserved for any outcome. This follows from the compositional
structure: decode is pure (no state change), register lookup is read-only,
and the dispatch delegates to an existing operation.

The hypothesis `hDispatchProj` must be supplied by the caller with knowledge
of which operation was dispatched and its projection-preservation proof. -/
theorem syscallEntry_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (layout : SeLe4n.SyscallRegisterLayout) (regCount : Nat)
    (st st' : SystemState)
    (hOk : syscallEntry layout regCount st = .ok ((), st'))
    (hDispatchProj : ∀ decoded tid stPost,
        dispatchSyscall decoded tid bootCoreId st = .ok ((), stPost) →
        projectState ctx observer stPost = projectState ctx observer st) :
    projectState ctx observer st' = projectState ctx observer st := by
  obtain ⟨tid, regs, decoded, hCur, hLookup, hDecode⟩ :=
    syscallEntry_requires_valid_decode layout regCount st st' hOk
  unfold syscallEntry at hOk
  rw [hCur] at hOk; simp at hOk
  rw [hLookup] at hOk; simp at hOk
  rw [hDecode] at hOk; simp at hOk
  -- PR #873 round 6: the taint seam moved into `dispatchSyscall`, so the entry's
  -- post-state IS the dispatcher's and the hypothesis applies directly.  The
  -- seam is still projection-invisible — `applySyscallTaint_preserves_projection`
  -- holds by `rfl` — which is what lets a discharger of `hDispatchProj` reduce it
  -- to a statement about the transition the arm ran.
  exact hDispatchProj decoded tid st' hOk

-- ============================================================================
-- WS-J1-D: NonInterferenceStep bridge theorems for syscallEntry
-- ============================================================================

/-- WS-J1-D: A failed `syscallEntry` (decode error, lookup error, etc.)
yields a `syscallDecodeError` NI step since the state is unchanged. -/
theorem syscallEntry_error_yields_NI_step
    (ctx : LabelingContext) (observer : IfObserver)
    (layout : SeLe4n.SyscallRegisterLayout) (regCount : Nat)
    (st : SystemState) (e : KernelError)
    (_hErr : syscallEntry layout regCount st = .error e) :
    NonInterferenceStep ctx observer st st :=
  .syscallDecodeError rfl

/-- WS-J1-D: A successful `syscallEntry` where the current thread is
non-observable yields a `syscallDispatchHigh` NI step, provided the
dispatched operation preserves the projection.

This is the primary bridge theorem: it composes the pure decode (no state
change), read-only register lookup, and the dispatched operation's
projection-preservation proof into a single `NonInterferenceStep`. -/
theorem syscallEntry_success_yields_NI_step
    (ctx : LabelingContext) (observer : IfObserver)
    (layout : SeLe4n.SyscallRegisterLayout) (regCount : Nat)
    (st st' : SystemState)
    (hOk : syscallEntry layout regCount st = .ok ((), st'))
    (hCurrentHigh : ∀ t, (st.scheduler.currentOnCore bootCoreId) = some t →
        threadObservable ctx observer t = false)
    (hDispatchProj : ∀ decoded tid stPost,
        dispatchSyscall decoded tid bootCoreId st = .ok ((), stPost) →
        projectState ctx observer stPost = projectState ctx observer st) :
    NonInterferenceStep ctx observer st st' :=
  .syscallDispatchHigh hCurrentHigh
    (syscallEntry_preserves_projection ctx observer layout regCount st st' hOk hDispatchProj)

-- ============================================================================
-- WS-K-F4: Dispatch decode purity and preservation composition
-- ============================================================================

/-- WS-K-F4: Layer 2 decode functions within `dispatchWithCap` are pure —
they operate on the `SyscallDecodeResult` value and never access or modify
`SystemState`. This means any decode failure is a state-preserving error,
and any decode success passes the original state unmodified to the delegated
kernel operation.

Proved by showing that two `SyscallDecodeResult` values with the same
`msgRegs` field produce identical decode results for all 6 structures —
confirming that decode depends only on `msgRegs`, not on `capAddr`,
`msgInfo`, or `syscallId`. -/
theorem dispatchWithCap_layer2_decode_pure
    (d₁ d₂ : SyscallDecodeResult) (hRegs : d₁.msgRegs = d₂.msgRegs) :
    (decodeCSpaceMintArgs d₁ = decodeCSpaceMintArgs d₂) ∧
    (decodeCSpaceCopyArgs d₁ = decodeCSpaceCopyArgs d₂) ∧
    (decodeCSpaceMoveArgs d₁ = decodeCSpaceMoveArgs d₂) ∧
    (decodeCSpaceDeleteArgs d₁ = decodeCSpaceDeleteArgs d₂) ∧
    -- AH3-C: These are now function equalities (parameterized by maxASID)
    (decodeVSpaceMapArgs d₁ = decodeVSpaceMapArgs d₂) ∧
    (decodeVSpaceUnmapArgs d₁ = decodeVSpaceUnmapArgs d₂) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [decodeCSpaceMintArgs, decodeCSpaceCopyArgs, decodeCSpaceMoveArgs,
      decodeCSpaceDeleteArgs, requireMsgReg, hRegs]) <;>
    (try funext maxASID; simp only [decodeVSpaceMapArgs, decodeVSpaceUnmapArgs,
      requireMsgReg, hRegs])

/-- WS-K-F4: Composition verification — `syscallEntry_preserves_proofLayerInvariantBundle`
composes decode purity (no state change), read-only cap lookup (state unchanged),
and the delegated operation's preservation property. The `hDispatchPres` hypothesis
is dischargeable per-dispatch-arm using existing subsystem preservation theorems:

- CSpace mint/copy/move/delete: `Capability/Invariant/Preservation.lean`
- Untyped carve: `Lifecycle/Operations/ScrubAndUntyped.lean`
- VSpace map/unmap: `Architecture/VSpaceInvariant.lean`
- Service register/revoke: `Service/Registry/Invariant.lean`
- IPC send/call/reply/recv: `IPC/Invariant/EndpointPreservation.lean`

This theorem witnesses that the composition is structurally complete. -/
theorem dispatchWithCap_preservation_composition_witness :
    (∀ layout regCount st st' (_hInv : Architecture.proofLayerInvariantBundle st)
        (_hOk : syscallEntry layout regCount st = .ok ((), st'))
        (_hDispatchPres : ∀ decoded tid stD stD',
            Architecture.proofLayerInvariantBundle stD →
            dispatchSyscall decoded tid bootCoreId stD = .ok ((), stD') →
            Architecture.proofLayerInvariantBundle stD'),
        Architecture.proofLayerInvariantBundle st') :=
  fun layout regCount st st' hInv hOk hDP =>
    syscallEntry_preserves_proofLayerInvariantBundle layout regCount st st' hInv hOk hDP

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

    **Fully substantive (6/14)** — proof uses only observability
    hypotheses, store invariants and pre-proven frame lemmas; NO abstract
    closures:
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

    **Closure-form (6/14)** — theorem takes `hProjEq` abstract closure;
    body is `hProjEq st' hStep`. NOT tautological for callers — each has
    DOCUMENTED FRAME LEMMAS letting a caller discharge `hProjEq` in
    ≈25-60 LOC using substantively-proven building blocks. Listed here
    WITH their discharge recipes:
    - `.schedContextBind` → `schedContextBind_preserves_projection` (AK6F.14);
      discharge via `objects_insert_preserves_projection_high` × 2 +
      `schedContextBind_frame_runQueue_rebucket`.
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

    Substantive closure of the 6 closure-form theorems is estimated at
    ≈300 LOC aggregate, tracked as continuation work AK6F.20b. Lean
    4.28.0's `split`/`split_ifs` interaction with `Except.ok` on
    deeply-nested `match`-based Bool conditions (e.g., `schedContextBind`
    has 5 nested matches before the first success-arm mutation)
    currently prevents clean destructuring; the frame lemmas above are
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
    | `.schedContextConfigure/Bind/Unbind` | `storeObject_preserves_projection` / `objects_insert_preserves_projection_high` (Operations.lean) at non-observable SchedContext target + TCB/RunQueue field preservation |
    | `.tcbSetIPCBuffer` | **`setIPCBufferOp_preserves_projection`** (Operations.lean — AK6-F.2b, v0.29.10) |
    | `.tcbSetPriority/SetMCPriority` | `objects_insert_preserves_projection_high` at non-observable TCB/SC — uses the universal direct-insert frame lemma (Operations.lean — AK6-F Step A, v0.29.10) |
    | `.tcbSetAffinity` | **`setThreadCpuAffinityOnCore_preserves_projection`** (Operations.lean — WS-SM SM8.B, review round 42) at non-observable target — the **live** wrapper, which round 37 rerouted this arm to; the boot-core `setThreadCpuAffinityOp_preserves_projection` (SM5.H.4) is its `bootCoreId` instance, reachable through `setThreadCpuAffinityOp_eq_onCore_state` but not needed here.  The affinity write is `cpuAffinity`-erased (invisible); the run-queue migration's write, at the executing core rather than a pinned boot core, preserves the filtered `projectRunnable` for a high thread (`migrateRunQueueOnAffinityChange_preserves_projection`); the replenishment migration is never projected (`migrateSchedContextReplenishment_preserves_projection`). |
    | `.tcbSuspend/Resume` | `storeObject_preserves_projection` at non-observable TCB target; the review-round retire prefix is `applyFaultRestart`, a register + `pendingFault` write on the same target |
    | `.tcbSetFaultHandler` | `objects_insert_preserves_projection_high` at non-observable TCB target (a `faultHandler` field write) |

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
    · split at h
      · exact absurd h (by simp)
      · next stPost _ => exact ⟨stPost, by simpa using h.symm⟩
    · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **And no success path through the unchecked dispatcher skips it either.**

The twin of the theorem above, and the reason the two are stated as a pair: the
seam sits at the dispatcher on *both* routes, so "which entry did the caller
use" stops being a question provenance depends on. -/
theorem dispatchSyscall_applies_taint_plan
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (st st' : SystemState)
    (h : dispatchSyscall decoded tid executingCore st = .ok ((), st')) :
    ∃ stPost, st' = applySyscallTaint (syscallTaintPlan st tid decoded) st stPost := by
  simp only [dispatchSyscall, SystemState.getObject?] at h
  -- The caller/core guard: a mismatched pair is refused before any lookup.
  split at h
  · exact absurd h (by simp)
  -- WS-ZA ZA4.3: a yield's plan is inert, so the step leaves its state as is.
  by_cases hY : decoded.syscallId = .yield
  · exact ⟨st', by rw [syscallTaintPlan_yield st tid decoded hY, applySyscallTaint_inert]⟩
  rw [if_neg hY] at h
  split at h
  · split at h
    · split at h
      · exact absurd h (by simp)
      · next stPost _ => exact ⟨stPost, by simpa using h.symm⟩
    · exact absurd h (by simp)
    · exact absurd h (by simp)
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

/-- The unchecked twin of `dispatchSyscallChecked_refuses_mismatched_core`: the
two dispatchers carry the same caller/core guard. -/
theorem dispatchSyscall_refuses_mismatched_core
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (hMismatch : st.scheduler.currentOnCore executingCore ≠ some tid) :
    dispatchSyscall decoded tid executingCore st = .error .illegalState := by
  simp only [dispatchSyscall, hMismatch, ne_eq, not_false_eq_true, ↓reduceIte]

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

/-- The unchecked twin of `dispatchSyscallChecked_ok_caller_current`. -/
theorem dispatchSyscall_ok_caller_current
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (st st' : SystemState)
    (h : dispatchSyscall decoded tid executingCore st = .ok ((), st')) :
    st.scheduler.currentOnCore executingCore = some tid := by
  by_cases hCur : st.scheduler.currentOnCore executingCore = some tid
  · exact hCur
  · rw [dispatchSyscall_refuses_mismatched_core decoded tid executingCore st hCur] at h
    exact absurd h (by simp)

/-- The entry never trips the guard: `syscallEntryChecked` resolves `tid` as
`currentOnCore executingCore` and dispatches on the IPC-buffer-filled state,
whose scheduler is the pre-state's (`tlbFillIpcBufferOnCore_scheduler`), so the
guard reads back the very thread the entry resolved. -/
theorem syscallEntryChecked_dispatch_caller_current
    (executingCore : Concurrency.CoreId) (tid : SeLe4n.ThreadId) (overflowCount : Nat)
    (st : SystemState) (hCur : st.scheduler.currentOnCore executingCore = some tid) :
    (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid
        overflowCount).scheduler.currentOnCore executingCore = some tid := by
  rw [SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_scheduler]
  exact hCur


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
    -- Layer 1b: CNode lookup (read-only)
    split at hStep
    · -- some (.cnode rootCn)
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
        -- PR #870 round 5: the target-first syscalls take the resolve-only
        -- lookup, everything else the classic rights-gated one.  The inner-NI
        -- hypothesis is stated over the resolve (the weaker premise, so the
        -- stronger hypothesis) and covers both branches — a full-lookup success
        -- is a resolve success (`syscallResolveCap_of_lookup`).
        split at hInvoke
        · -- target-first branch: resolve-only lookup
          unfold syscallInvokeResolved at hInvoke
          split at hInvoke
          · -- syscallResolveCap returned error
            simp at hInvoke
          · rename_i cap stCap hCap
            have ⟨_, _, _, hStEq⟩ :=
              syscallResolveCap_implies_capability_at_slot _ st cap stCap hCap
            rw [hStEq] at hInvoke hCap
            exact hInnerProj _ cap hCap stPost hInvoke
        · -- classic branch: full lookup
          unfold syscallInvoke at hInvoke
          split at hInvoke
          · -- syscallLookupCap returned error
            simp at hInvoke
          · rename_i cap stCap hCap
            have ⟨_, _, _, _, hStEq⟩ :=
              syscallLookupCap_implies_capability_held _ st cap stCap hCap
            rw [hStEq] at hInvoke hCap
            exact hInnerProj _ cap (syscallResolveCap_of_lookup _ st cap st hCap) stPost hInvoke
    · -- some (not .cnode): error
      simp at hStep
    · -- none: error
      simp at hStep
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
    (gate : SyscallGate) (cap : Capability) (targetId : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .declassify)
    (hTarget : cap.target = .object targetId) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      declassifyObjectFromCore (liftLegacyContext ctx) ctx.declassificationPolicy
        executingCore targetId st := by
  unfold dispatchWithCapChecked dispatchCapabilityOnly
  rw [hSyscall]
  simp only [hTarget]

/-- **WS-SM SM8.C.9: there is no unchecked declassification.**

The unchecked dispatch fails closed with the error a denied downgrade produces.
Stated as a theorem rather than left to the reader of the arm, because "the
unchecked path skips the flow check" is the pattern every *other* arm follows,
and following it here would authorize every downgrade. -/
theorem dispatchWithCap_declassify_denied
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (st : SystemState)
    (hSyscall : decoded.syscallId = .declassify) :
    dispatchWithCap decoded tid executingCore gate cap st = .error .declassificationDenied := by
  unfold dispatchWithCap dispatchCapabilityOnly
  rw [hSyscall]

/-- **WS-SM SM8.C.9**: an unconfigured deployment cannot declassify.

`LabelingContext.declassificationPolicy` defaults to deny-all, so the checked
arm refuses too — the fail-closed default, stated where an operator reading the
dispatch would look for it. -/
theorem dispatchWithCapChecked_declassify_default_denied
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (targetId : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .declassify)
    (hTarget : cap.target = .object targetId)
    (hDefault : ctx.declassificationPolicy.canDeclassify = fun _ _ => false) :
    ¬ ∃ st', dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), st') := by
  rintro ⟨st', hStep⟩
  rw [dispatchWithCapChecked_declassify_delegates ctx decoded tid executingCore gate cap targetId st
    hSyscall hTarget] at hStep
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

The conclusion names the **whole arm**, not just the transition: the woken
bound receiver's server-first reply stash is cleared and both WS-RA stagers
run, exactly as on the ordinary `.notificationSignal` path.  Stating it that
way is the point — an arm that ran the right transition and then skipped the
post-processing its woken threads are owed would not satisfy this, and the
per-core routing gate and the cross-core inventory both consume this equation
as their tie to the dispatch. -/
theorem dispatchWithCapChecked_declassifySignal_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (notifId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.NotificationSignalArgs) (st : SystemState)
    (hSyscall : decoded.syscallId = .declassifySignal)
    (hTarget : cap.target = .object notifId)
    (hDecode : decodeNotificationSignalArgs decoded = .ok args) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      (match notificationSignalDeclassifiedCrossCoreDispatch (liftLegacyContext ctx)
              ctx.declassificationPolicy notifId args.badge executingCore st with
       | (st', .ok _) =>
           (match clearWokenReceiverStash ((boundDeliveryTarget? st notifId).map (·.1)) st' with
            | .error e => .error e
            | .ok ((), st'') =>
                .ok ((), Architecture.stageWokenDelivery
                          (Architecture.stageWokenDelivery st''
                            ((boundDeliveryTarget? st notifId).map (·.1)) 0)
                          (notificationSignalWaiter? st notifId) 0))
       | (_, .error e) => .error e) := by
  unfold dispatchWithCapChecked dispatchCapabilityOnly
  rw [hSyscall]
  simp only [hTarget, hDecode]

/-- **WS-SM SM9.C.8: there is no unchecked declassifying signal.**

The dual of `dispatchWithCapChecked_declassifySignal_delegates`, and the
stronger of the pair to state explicitly: the unchecked path is the one an arm
author would be tempted to fill in by analogy with `.notificationSignal`, and
doing so would produce a signal that skips *both* declassification gates while
carrying the authority to cross a boundary the lattice denies. -/
theorem dispatchWithCap_declassifySignal_denied
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (st : SystemState)
    (hSyscall : decoded.syscallId = .declassifySignal) :
    dispatchWithCap decoded tid executingCore gate cap st = .error .declassificationDenied := by
  unfold dispatchWithCap dispatchCapabilityOnly
  rw [hSyscall]

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
the post-processing after the transition (the stash clear and both WS-RA
stagers) must not touch the trail either — an arm that appended there would
falsify this while the transition's own theorem stayed true. -/
theorem dispatchWithCapChecked_declassifySignal_default_no_downgrade
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (notifId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.NotificationSignalArgs)
    (st st' : SystemState)
    (hSyscall : decoded.syscallId = .declassifySignal)
    (hTarget : cap.target = .object notifId)
    (hDecode : decodeNotificationSignalArgs decoded = .ok args)
    (hDefault : ctx.declassificationPolicy.canDeclassify = fun _ _ => false)
    (hStep : dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), st')) :
    st'.declassificationAuditLog = st.declassificationAuditLog := by
  rw [dispatchWithCapChecked_declassifySignal_delegates ctx decoded tid executingCore gate cap notifId
    args st hSyscall hTarget hDecode] at hStep
  unfold notificationSignalDeclassifiedCrossCoreDispatch at hStep
  obtain ⟨pair, hPair⟩ : ∃ p, notificationSignalDeclassifiedOnCore (liftLegacyContext ctx)
      ctx.declassificationPolicy notifId args.badge executingCore st = p :=
    ⟨_, rfl⟩
  rw [hPair] at hStep
  obtain ⟨stT, res⟩ := pair
  cases res with
  | error e => exact absurd hStep (by simp)
  | ok sgi =>
    simp only at hStep
    -- The transition's own trail statement, then the arm's post-processing —
    -- neither the stash clear nor either stager touches the trail.
    have hTrail := declassifiedSignal_default_policy_never_downgrades (liftLegacyContext ctx)
      ctx.declassificationPolicy notifId args.badge executingCore st stT
      sgi hDefault hPair
    obtain ⟨stash, hStash⟩ : ∃ r, clearWokenReceiverStash
        ((boundDeliveryTarget? st notifId).map (·.1)) stT = r := ⟨_, rfl⟩
    rw [hStash] at hStep
    cases stash with
    | error e => exact absurd hStep (by simp)
    | ok pr =>
      obtain ⟨u, st2⟩ := pr
      cases u
      simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      obtain ⟨-, hSt'⟩ := hStep
      rw [← hSt']
      rw [Architecture.stageWokenDelivery_declassificationAuditLog_eq,
        Architecture.stageWokenDelivery_declassificationAuditLog_eq,
        clearWokenReceiverStash_declassificationAuditLog_eq _ _ _ hStash]
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
    (hTarget : cap.target = .auditTrail)
    (hRight : cap.hasRight gate.requiredRight = true)
    (hArgs : Architecture.SyscallArgDecode.decodeAuditReadArgs decoded = .ok args)
    (hOp : decodeAuditReadOp args.opcode args.index args.chunk = some op) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      (match auditReadFromCore (liftLegacyContext ctx) (validatedAuditMonitorClearance ctx)
          executingCore op st with
       | .error e => .error e
       | .ok (w, st') =>
           .ok ((), Architecture.writeReturnFrameToTcb st' tid
             (Architecture.returnFrameOfWord w.toUInt64))) := by
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
    (hTarget : cap.target = .auditTrail)
    (hRight : cap.hasRight gate.requiredRight = true)
    (hArgs : Architecture.SyscallArgDecode.decodeAuditDrainArgs decoded = .ok args) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      (match auditDrainVisiblePrefix (liftLegacyContext ctx)
          (validatedAuditMonitorClearance ctx)
          executingCore args.count st with
       | .error e => .error e
       | .ok (n, st') =>
           .ok ((), Architecture.writeReturnFrameToTcb st' tid
             (Architecture.returnFrameOfWord n.toUInt64))) := by
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
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .error .invalidCapability := by
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
    (hTarget : cap.target = .auditTrail)
    (hRight : cap.hasRight gate.requiredRight = false) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .error .illegalAuthority := by
  unfold dispatchWithCapChecked dispatchCapabilityOnly
  rcases hSyscall with h | h <;> rw [h] <;>
    simp only [extractAuditAuthority, hTarget, hRight, if_false, Bool.false_eq_true]

/-- **WS-SM SM9.A.9 (PR #870 round 5, THE ordering contract, at the dispatch
the syscall actually takes)**: a resolvable capability that does not target
the audit trail is refused `.invalidCapability` on the audit syscalls
**whatever rights it carries** — there is no `hasRight` hypothesis, which is
the theorem's point.

Before this round the full lookup's rights gate front-ran the arm, so a
capability wrong on *both* axes was answered `.illegalAuthority` — the
documented target-first order held only for rights-bearing capabilities.  The
checked dispatch now routes the audit ids through the resolve-only lookup
(`syscallChecksTargetFirst` → `syscallInvokeResolved`), and this theorem is
the composed path's witness. -/
theorem dispatchSyscallChecked_audit_target_first
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (tcb : TCB) (rootCn : CNode) (ref : SlotRef) (cap : Capability)
    (oid : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .auditRead ∨ decoded.syscallId = .auditDrain)
    (hCur : st.scheduler.currentOnCore executingCore = some tid)
    (hTcb : st.getTcb? tid = some tcb)
    (hRoot : st.getCNode? tcb.cspaceRoot = some rootCn)
    (hResolve : resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth st = .ok ref)
    (hLookup : SystemState.lookupSlotCap st ref = some cap)
    (hTarget : cap.target = .object oid) :
    dispatchSyscallChecked ctx decoded tid executingCore st = .error .invalidCapability := by
  -- PR #873 round 6: the taint seam wraps the invoke inside the dispatcher, so
  -- the arm's refusal is rewritten under the wrapping `match` rather than being
  -- the goal outright — and the gate is spelled out, because a `_` under that
  -- match no longer determines itself.
  rcases hSyscall with h | h
  · have hArm := dispatchWithCapChecked_audit_rejects_non_audit_capability ctx decoded tid executingCore
      { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
        capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
      cap oid st (Or.inl h) hTarget
    rw [h] at hArm
    simp only [dispatchSyscallChecked, hCur, ne_eq, not_true_eq_false, ↓reduceIte,
      SystemState.getObject?,
      (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb,
      (SystemState.getCNode?_eq_some_iff st tcb.cspaceRoot rootCn).mp hRoot,
      h, syscallChecksTargetFirst,
      syscallInvokeResolved, syscallResolveCap, hResolve, hLookup]
    -- PR #889 review round 2: the resolution now refuses a capability naming a
    -- reserved idle object before the arm runs; either way the answer is
    -- `.invalidCapability`.
    by_cases hRes : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true <;> simp [hRes, hArm]
  · have hArm := dispatchWithCapChecked_audit_rejects_non_audit_capability ctx decoded tid executingCore
      { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
        capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
      cap oid st (Or.inr h) hTarget
    rw [h] at hArm
    simp only [dispatchSyscallChecked, hCur, ne_eq, not_true_eq_false, ↓reduceIte,
      SystemState.getObject?,
      (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb,
      (SystemState.getCNode?_eq_some_iff st tcb.cspaceRoot rootCn).mp hRoot,
      h, syscallChecksTargetFirst,
      syscallInvokeResolved, syscallResolveCap, hResolve, hLookup]
    -- PR #889 review round 2: the resolution now refuses a capability naming a
    -- reserved idle object before the arm runs; either way the answer is
    -- `.invalidCapability`.
    by_cases hRes : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true <;> simp [hRes, hArm]

/-- **WS-SM SM9.A.9 (PR #870 round 5, the order's other half)**: an audit-target
capability lacking the required right is refused `.illegalAuthority` — after
the target check, from the arm.  Together with
`dispatchSyscallChecked_audit_target_first` this pins the composed order: the
refusal class depends on the *target* first, and on the rights only once the
target is the audit trail. -/
theorem dispatchSyscallChecked_audit_right_checked_second
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (tcb : TCB) (rootCn : CNode) (ref : SlotRef) (cap : Capability)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .auditRead ∨ decoded.syscallId = .auditDrain)
    (hCur : st.scheduler.currentOnCore executingCore = some tid)
    (hTcb : st.getTcb? tid = some tcb)
    (hRoot : st.getCNode? tcb.cspaceRoot = some rootCn)
    (hResolve : resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth st = .ok ref)
    (hLookup : SystemState.lookupSlotCap st ref = some cap)
    (hTarget : cap.target = .auditTrail)
    (hRight : cap.hasRight (syscallRequiredRight decoded.syscallId) = false) :
    dispatchSyscallChecked ctx decoded tid executingCore st = .error .illegalAuthority := by
  -- PR #873 round 6: as above — the refusal is rewritten under the seam's
  -- `match`, and the gate is named rather than inferred.
  rcases hSyscall with h | h
  · have hArm := dispatchWithCapChecked_audit_insufficient_right_denied ctx decoded tid executingCore
      { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
        capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
      cap st (Or.inl h) hTarget hRight
    rw [h] at hArm
    simp only [dispatchSyscallChecked, hCur, ne_eq, not_true_eq_false, ↓reduceIte,
      SystemState.getObject?,
      (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb,
      (SystemState.getCNode?_eq_some_iff st tcb.cspaceRoot rootCn).mp hRoot,
      h, syscallChecksTargetFirst,
      syscallInvokeResolved, syscallResolveCap, hResolve, hLookup]
    -- PR #889 review round 2: an audit-trail capability names no reserved idle
    -- object, so the resolution's reservation refusal does not fire and the
    -- arm's rights verdict is the answer.
    have hRes : SeLe4n.Kernel.capTargetsReservedIdleObject cap = false := by
      simp [SeLe4n.Kernel.capTargetsReservedIdleObject, hTarget]
    simp [hRes, hArm]
  · have hArm := dispatchWithCapChecked_audit_insufficient_right_denied ctx decoded tid executingCore
      { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
        capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
      cap st (Or.inr h) hTarget hRight
    rw [h] at hArm
    simp only [dispatchSyscallChecked, hCur, ne_eq, not_true_eq_false, ↓reduceIte,
      SystemState.getObject?,
      (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb,
      (SystemState.getCNode?_eq_some_iff st tcb.cspaceRoot rootCn).mp hRoot,
      h, syscallChecksTargetFirst,
      syscallInvokeResolved, syscallResolveCap, hResolve, hLookup]
    -- PR #889 review round 2: an audit-trail capability names no reserved idle
    -- object, so the resolution's reservation refusal does not fire and the
    -- arm's rights verdict is the answer.
    have hRes : SeLe4n.Kernel.capTargetsReservedIdleObject cap = false := by
      simp [SeLe4n.Kernel.capTargetsReservedIdleObject, hTarget]
    simp [hRes, hArm]


-- ============================================================================
-- WS-RR RR7.3: the capability-held guarantee on the LIVE checked dispatch path
--
-- Register §4 finding 5: `syscallEntry_implies_capability_held` and
-- `dispatchSyscall_requires_right` are stated over the *legacy* entry, which is
-- `bootCoreId`-pinned and whose only non-test callers are the trace harness and
-- the exception model.  The path the hardware takes is
-- `@[export lean_syscall_dispatch_cross_core]` → `syscallDispatchCrossCoreEntry`
-- → `Platform.FFI.syscallDispatchFromAbi` → `syscallEntryChecked` →
-- `dispatchSyscallChecked`, and nothing covered it.  These are the analogues,
-- parameterized over the executing core rather than the boot core.
--
-- The checked dispatcher has two gate shapes and the guarantee holds through
-- both: the 31 ordinary arms take the rights-checking `syscallInvoke`, and the
-- two `syscallChecksTargetFirst` arms take the resolve-only
-- `syscallInvokeResolved` and check the right in the arm, after the target.
-- The second half is what the first attempt at this theorem would have missed —
-- a rights conclusion read off the gate alone is false for the audit pair.
-- ============================================================================

/-- **WS-RR RR7.3**: a successful audit arm of the flow-checked dispatch implies
the capability carried the required right.

The arm's own gate, stated in the direction the entry-point guarantee needs.
`dispatchWithCapChecked_audit_insufficient_right_denied` is the contrapositive
for a capability that already targets the audit trail; this form takes no
`hTarget` hypothesis, because `extractAuditAuthority` is total and a
non-audit-trail target refuses before the rights test is reached. -/
theorem dispatchWithCapChecked_audit_success_requires_right
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (st : SystemState) (st' : SystemState)
    (hSyscall : decoded.syscallId = .auditRead ∨ decoded.syscallId = .auditDrain)
    (hOk : dispatchWithCapChecked ctx decoded tid executingCore gate cap st = .ok ((), st')) :
    cap.hasRight gate.requiredRight = true := by
  by_cases hRight : cap.hasRight gate.requiredRight
  · exact hRight
  · exfalso
    simp only [Bool.not_eq_true] at hRight
    simp only [dispatchWithCapChecked, dispatchCapabilityOnly] at hOk
    rcases hSyscall with h | h <;> rw [h] at hOk <;>
      · simp only [extractAuditAuthority] at hOk
        cases hTgt : cap.target <;> rw [hTgt] at hOk <;>
          simp only [hRight, if_false, Bool.false_eq_true] at hOk <;>
          exact absurd hOk (by simp)

/-- **WS-RR RR7.3**: if the **flow-checked** dispatch succeeds, the caller held a
capability with the required access right for the invoked syscall.

The live-path analogue of `dispatchSyscall_requires_right`.  Both gate shapes
are covered: the ordinary arms through `syscallInvoke_requires_right`, and the
target-first (audit) pair through `syscallResolveCap`'s resolution plus
`dispatchWithCapChecked_audit_success_requires_right` — the arm's own rights
test, which is where the audit pair's second gate lives since PR #870 round 5. -/
theorem dispatchSyscallChecked_requires_right
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (st : SystemState) (st' : SystemState)
    (hCap : decoded.syscallId ≠ .yield)
    (hOk : dispatchSyscallChecked ctx decoded tid executingCore st = .ok ((), st')) :
    ∃ tcb, st.getTcb? tid = some tcb ∧
      ∃ rootCn, st.getCNode? tcb.cspaceRoot = some rootCn ∧
        ∃ cap ref,
          resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth st = .ok ref ∧
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
    next rootCn hRoot =>
      refine ⟨rootCn, (SystemState.getCNode?_eq_some_iff st tcb.cspaceRoot rootCn).mpr hRoot, ?_⟩
      split at hOk
      · simp at hOk
      next stPost hInvokeOk =>
        -- The gate the dispatcher chose is the `if` inside the invoke's own
        -- `match`; split it so each shape supplies its own rights witness.
        split at hInvokeOk
        next hTargetFirst =>
          -- The audit pair: resolve-only lookup, rights checked in the arm.
          simp only [syscallInvokeResolved] at hInvokeOk
          split at hInvokeOk
          · simp at hInvokeOk
          next cap stRes hResolveOk =>
            obtain ⟨ref, hResolve, hSlot, hStEq⟩ :=
              syscallResolveCap_implies_capability_at_slot _ _ cap stRes hResolveOk
            subst hStEq
            refine ⟨cap, ref, hResolve, hSlot, ?_⟩
            exact dispatchWithCapChecked_audit_success_requires_right ctx decoded tid executingCore _ cap
              _ stPost ((syscallChecksTargetFirst_iff decoded.syscallId).mp hTargetFirst)
              hInvokeOk
        next =>
          -- Every other arm: the classic rights-gated lookup.
          obtain ⟨cap, ref, hResolve, hSlot, hRight⟩ :=
            syscallInvoke_requires_right _ (dispatchWithCapChecked ctx decoded tid executingCore _)
              _ () stPost hInvokeOk
          exact ⟨cap, ref, hResolve, hSlot, hRight⟩
    · simp at hOk
    · simp at hOk
  · simp at hOk
  · simp at hOk

/-- **WS-RR RR7.3**: if the **flow-checked** syscall entry succeeds, the caller
held the required access right — the live-path analogue of
`syscallEntry_implies_capability_held`.

Three differences from the legacy statement, all of them the point:

* the caller is identified on the **executing** core (`currentOnCore
  executingCore`), not on `bootCoreId`, so the guarantee covers a syscall issued
  from a secondary PE;
* the capability is resolved against the state the decode's TLB fill produced
  (`tlbFillIpcBufferOnCore`), which is the state the dispatcher is handed — a
  statement about `st` would be about a state no arm ever sees;
* the entry's own `isInsecureDefaultContext` refusal is part of the chain, so a
  success also witnesses that a deployment labeling context was installed.

`resolveCapAddress` and `lookupSlotCap` read only the object store, which the
TLB fill leaves alone (`tlbFillIpcBufferOnCore_frame`), so the resolution is
equally a resolution against `st`; that corollary is
`syscallEntryChecked_implies_capability_held_of_pre_state` below. -/
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
        st tid layout regs regCount = .ok decoded ∧
      ∃ stFilled,
        SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore
          st executingCore tid decoded.overflowCount = stFilled ∧
        (decoded.syscallId ≠ .yield →
        ∃ tcb, stFilled.getTcb? tid = some tcb ∧
          ∃ rootCn, stFilled.getCNode? tcb.cspaceRoot = some rootCn ∧
            ∃ cap ref,
              resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth stFilled =
                .ok ref ∧
              SystemState.lookupSlotCap stFilled ref = some cap ∧
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
          exact ⟨tid, regs, decoded, hCurrent, hLookup, hDecode, _, rfl, fun hCap =>
            dispatchSyscallChecked_requires_right ctx decoded tid executingCore _ st' hCap hOk⟩


/-- **WS-RR RR7.3**: the live-path capability guarantee, stated on the state the
caller trapped in.

`syscallEntryChecked_implies_capability_held` resolves against the state the
decode's TLB fill produced, because that is the state the dispatcher is handed.
The fill touches only the per-core TLB view (`tlbFillIpcBufferOnCore_frame`) and
the CSpace walk reads only the object store
(`resolveCapAddress_congr_objects`), so the same capability is at the same slot
of the pre-state — which is the form a reader of "every syscall is capability
gated" wants, since the pre-state is the one user space could have arranged. -/
theorem syscallEntryChecked_implies_capability_held_of_pre_state
    (ctx : LabelingContext) (layout : SeLe4n.SyscallRegisterLayout)
    (executingCore : Concurrency.CoreId) (regCount : Nat)
    (st : SystemState) (st' : SystemState)
    (hOk : syscallEntryChecked ctx layout executingCore regCount st = .ok ((), st')) :
    isInsecureDefaultContext ctx = false ∧
    ∃ tid regs decoded,
      (st.scheduler.currentOnCore executingCore) = some tid ∧
      lookupThreadRegisterContext tid st = .ok (regs, st) ∧
      SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
        st tid layout regs regCount = .ok decoded ∧
      (decoded.syscallId ≠ .yield →
      ∃ tcb, st.getTcb? tid = some tcb ∧
        ∃ rootCn, st.getCNode? tcb.cspaceRoot = some rootCn ∧
          ∃ cap ref,
            resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth st = .ok ref ∧
            SystemState.lookupSlotCap st ref = some cap ∧
            cap.hasRight (syscallRequiredRight decoded.syscallId) = true) := by
  obtain ⟨hCtx, tid, regs, decoded, hCurrent, hLookup, hDecode, stFilled, hFill, hHeld⟩ :=
    syscallEntryChecked_implies_capability_held ctx layout executingCore regCount st st' hOk
  refine ⟨hCtx, tid, regs, decoded, hCurrent, hLookup, hDecode, fun hCap => ?_⟩
  obtain ⟨tcb, hTcb, rootCn, hRoot, cap, ref, hResolve, hSlot, hRight⟩ := hHeld hCap
  subst hFill
  have hObjects :
      (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore
        st executingCore tid decoded.overflowCount).objects = st.objects :=
    (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_frame
      st executingCore tid decoded.overflowCount).1
  refine ⟨tcb, ?_, rootCn, ?_, cap, ref, ?_, ?_, hRight⟩
  · simpa only [SystemState.getTcb?, hObjects] using hTcb
  · simpa only [SystemState.getCNode?, hObjects] using hRoot
  · rw [← resolveCapAddress_congr_objects _ st hObjects]; exact hResolve
  · rw [← lookupSlotCap_congr_objects _ st ref hObjects]; exact hSlot

/-- **WS-SM SM9.A.10: there is no unchecked audit read.**

The unchecked dispatch fails closed on both audit syscalls.  Stated as a theorem
because "the unchecked path skips the flow check" is the pattern every *other*
arm follows, and following it here would mean picking a clearance — and the only
clearance available without a context is "all of them", which is an audit reader
that hands every entry to every capability holder. -/
theorem dispatchWithCap_auditRead_denied
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (st : SystemState)
    (hSyscall : decoded.syscallId = .auditRead ∨ decoded.syscallId = .auditDrain) :
    dispatchWithCap decoded tid executingCore gate cap st = .error .illegalAuthority := by
  unfold dispatchWithCap dispatchCapabilityOnly
  rcases hSyscall with h | h <;> rw [h]

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
    (hTarget : cap.target = .auditTrail)
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
    (hTarget : cap.target = .auditTrail)
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
        { target := .object oid, rights := AccessRightSet.ofList AccessRight.all, } st = .error .invalidCapability ∧
    (∀ (parent : NonNullCap) (rights : AccessRightSet) (badge : Option SeLe4n.Badge)
        (child : Capability),
      mintDerivedCap parent rights badge = .ok child → child.target = .auditTrail →
        parent.val.target = .auditTrail) ∧
    auditDrainVisiblePrefix (liftLegacyContext ctx) (validatedAuditMonitorClearance ctx)
        c count st =
      .error .illegalAuthority ∧
    Capability.auditTrailRead.hasRight .write = false := by
  refine ⟨fun anyCap st' =>
      unconfiguredDeployment_audit_never_succeeds ctx decoded tid executingCore gate anyCap st st'
        hSyscall hNoMonitor,
    dispatchWithCapChecked_audit_rejects_non_audit_capability ctx decoded tid executingCore gate _ oid st
      hSyscall rfl,
    fun parent rights badge child hMint hChild =>
      mintDerivedCap_no_audit_forgery parent rights badge child hMint hChild,
    ?_, Capability.auditTrailRead_cannot_drain.2⟩
  rw [validatedAuditMonitorClearance_none ctx hNoMonitor]
  exact auditDrain_unconfigured_denied (liftLegacyContext ctx) c count st

/-- **The live `.tcbSuspend` arm routes to `suspendThreadOnCore`.**  Capability-only,
so this covers both `dispatchWithCap` and `dispatchWithCapChecked` (the latter
consults `dispatchCapabilityOnly` first). -/
theorem dispatchWithCap_tcbSuspend_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId) (vtid : SeLe4n.ValidThreadId)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .tcbSuspend)
    (hTarget : cap.target = .object objId)
    (hDecode : ∃ a, Architecture.SyscallArgDecode.decodeSuspendArgs decoded = .ok a)
    (hValid : validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vtid) :
    dispatchWithCap decoded tid executingCore gate cap st =
      (match Lifecycle.Suspend.suspendThreadOnCore st vtid
              executingCore with
       | .ok (st', _) => .ok ((), st')
       | .error e => .error e) := by
  obtain ⟨a, hD⟩ := hDecode
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hD, hValid]

/-- WS-ZA ZA5.4 part 22: **the live `.tcbSetSpace` arm is the space change** at
the invoking thread's executing core, on the thread the capability names and the
two roots resolved through the caller's CSpace (`resolveSetSpace`).  It takes
the core for the retire of what each slot's old capability took with it. -/
theorem dispatchWithCap_tcbSetSpace_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.SetSpaceArgs) (vtid : SeLe4n.ValidThreadId)
    (cnSrc vrSrc : CSpaceAddr) (st : SystemState)
    (hSyscall : decoded.syscallId = .tcbSetSpace)
    (hTarget : cap.target = .object objId)
    (hDecode : Architecture.SyscallArgDecode.decodeSetSpaceArgs decoded = .ok args)
    (hValid : validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vtid)
    (hResolve : resolveSetSpace tid args st = .ok (cnSrc, vrSrc)) :
    dispatchWithCap decoded tid executingCore gate cap st =
      (match copyThreadSpacesZombie executingCore st vtid cnSrc vrSrc with
       | .ok st' => .ok ((), st')
       | .error e => .error e) := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode, hValid, hResolve]

/-- **The live `.tcbResume` arm routes to `resumeThreadOnCore`.**

Round 10 of the PR #861 review found this arm still calling the boot-pinned
`resumeThread`, which enqueues on `bootCoreId` regardless of the target's
`cpuAffinity` — so resuming a thread homed on a secondary core put it on the
wrong run queue.  The reroute is the fix; this theorem is what stops the
inventory claiming the arm is covered while it points somewhere else. -/
theorem dispatchWithCap_tcbResume_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId) (vtid : SeLe4n.ValidThreadId)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .tcbResume)
    (hTarget : cap.target = .object objId)
    (hDecode : ∃ a, Architecture.SyscallArgDecode.decodeResumeArgs decoded = .ok a)
    (hValid : validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vtid) :
    dispatchWithCap decoded tid executingCore gate cap st =
      (match Lifecycle.Suspend.resumeThreadOnCore
              (retirePendingFaultForResume st vtid.val) vtid
              executingCore with
       | .ok (st', _) => .ok ((), st')
       | .error e => .error e) := by
  obtain ⟨a, hD⟩ := hDecode
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hD, hValid]

/-- **The live `.receive` arm routes to `endpointReceiveDualOnCore`.**

Round 8 of the PR #861 review classified this transition a below-API "leg" of
`endpointReplyRecvOnCore`.  It is that — and it is also what the checked `.receive` arm
calls directly, once its own `endpoint→receiver` gate has passed.  A theorem
saying so is the thing that was missing: with it, the misclassification is a
broken citation rather than a prose disagreement between two tables. -/
theorem dispatchWithCapChecked_receive_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (gate : SyscallGate) (cap : Capability) (epId : SeLe4n.ObjId)
    (replyIdOpt : Option SeLe4n.ReplyId) (st : SystemState)
    (hSyscall : decoded.syscallId = .receive)
    (hTarget : cap.target = .object epId)
    (hFlow : securityFlowsTo (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = true)
    -- WS-SM SM8.C: the arm's gate is the global check AND the endpoint override.
    (hOverride : endpointOverrideAllows ctx epId (ctx.endpointLabelOf epId)
      (ctx.threadLabelOf tid) = true)
    (hReply : resolveRecvReplyId gate decoded st = .ok replyIdOpt) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      -- PR #873 round 6: the arm routes through the WithCaps per-core receive, so
      -- a send that parked before its receiver arrived delivers its capabilities
      -- too, and the staged `extraCaps` is the summary's installed count.
      -- WS-OD OD3.6: including the rendezvous donation, which the checked arm
      -- performs with the *same* definition and behind no extra gate -- the
      -- delegation claim is about the whole arm, so it names every step of it.
      (match endpointReceiveDualWithCapsOnCore epId tid replyIdOpt gate.cspaceRoot
              decoded.capRecvSlot executingCore st with
       | (st', .ok (dequeued, summary, _)) =>
           (match applyReceiveRendezvousHandoff st' tid dequeued
                    executingCore with
            | .error e => .error e
            | .ok stDon =>
                .ok ((), Architecture.stageDeliveredMessage
                          (Architecture.stageWokenSendCompletion stDon
                            ((st.getEndpoint? epId).bind (·.sendQ.head))) tid
                          summary.installedCount))
       | (_, .error e) => .error e) := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, hSyscall, hTarget,
    endpointFlowGate_of ctx epId _ _ hFlow hOverride, hReply]

/-- **The live unchecked `.send` arm routes to `endpointSendDualWithCapsOnCore`.**

Round 10 of the PR #861 review found this arm still calling the boot-pinned
`endpointSendDualWithCaps`, whose two scheduling effects both target `bootCoreId`:
a rendezvous receiver is woken with `ensureRunnable` (wrong run queue when the
receiver is homed elsewhere), and a sender with no receiver is descheduled with
`removeRunnable` (so a sender blocking on a secondary core stays current and
runnable there).  The reroute is the fix; this theorem is the tie that stops the
per-core inventory claiming the arm is covered while it points somewhere else. -/
theorem dispatchWithCap_send_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (epId : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .send)
    (hTarget : cap.target = .object epId) :
    dispatchWithCap decoded tid executingCore gate cap st =
      (match endpointSendDualWithCapsOnCore epId tid (.frame cap.badge (cap.rights.mem .grant))
              decoded.capRecvSlot
              executingCore st with
       | (_, .error e) => .error e
       | (st', .ok (summary, _)) =>
           match clearWokenReceiverStash ((st.getEndpoint? epId).bind (·.receiveQ.head)) st' with
           | .error e => .error e
           | .ok ((), st'') =>
               .ok ((), Architecture.stageWokenDelivery st''
                         ((st.getEndpoint? epId).bind (·.receiveQ.head))
                         summary.installedCount)) := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget]

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
      (match endpointSendCrossCoreDispatchChecked ctx epId tid (.frame cap.badge (cap.rights.mem .grant))
              decoded.capRecvSlot
              executingCore st with
       | (_, .error e) => .error e
       | (st', .ok (summary, _)) =>
           match clearWokenReceiverStash ((st.getEndpoint? epId).bind (·.receiveQ.head)) st' with
           | .error e => .error e
           | .ok ((), st'') =>
               .ok ((), Architecture.stageWokenDelivery st''
                         ((st.getEndpoint? epId).bind (·.receiveQ.head))
                         summary.installedCount)) := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, hSyscall, hTarget]

/-- **The live `.tcbSetPriority` arm routes to `setPriorityOnCore`.**

Round 12 of the PR #861 review found this arm still calling `setPriorityOp`,
which is boot-pinned twice: `migrateRunQueueBucket` tests membership in
`runQueueOnCore bootCoreId` — so for a target queued on any other core the
re-bucket is a silent no-op and the run queue keeps the *old* priority band —
and the preemption check reads `currentOnCore bootCoreId`. -/
theorem dispatchWithCap_tcbSetPriority_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId) (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
    (args : Architecture.SyscallArgDecode.SetPriorityArgs) (st : SystemState)
    (hSyscall : decoded.syscallId = .tcbSetPriority)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeSetPriorityArgs decoded = .ok args)
    (hCaller : validateThreadIdArg tid = .ok vCallerTid)
    (hValid : validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vTargetTid) :
    dispatchWithCap decoded tid executingCore gate cap st =
      (match SchedContext.PriorityManagement.setPriorityOnCore st vCallerTid vTargetTid
              (SeLe4n.Priority.ofNat args.newPriority) executingCore with
       | .ok (st', _) => .ok ((), st')
       | .error e => .error e) := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode, hCaller, hValid]

/-- **The live `.schedContextUnbind` arm routes to `schedContextUnbindOnCore`.**

Round 15 of the PR #861 review found the arm calling the single-core
`schedContextUnbind`, which clears the demoted thread's `current` slot and stops
there.  No scheduling point follows it — `syscallDispatchCrossCoreEntry` only
commits and fires the diff-recovered SGIs, and `crossCoreSgiBody` emits nothing
for the executing core — so the thread returned to userspace still running while
the model recorded its core as having no current thread, and its next syscall is
refused (`vacatedCore_next_syscall_rejected`; round 43 corrected the earlier
claim of a boot-core misroute, which caller resolution rules out). -/
theorem dispatchWithCap_schedContextUnbind_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (scId : SeLe4n.ObjId) (vScId : SeLe4n.ValidObjId)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .schedContextUnbind)
    (hTarget : cap.target = .object scId)
    (hDecode : ∃ a, decodeSchedContextUnbindArgs decoded = .ok a)
    (hValid : validateObjIdArg scId = .ok vScId) :
    dispatchWithCap decoded tid executingCore gate cap st =
      (match SchedContextOps.schedContextUnbindOnCore vScId
              executingCore st with
       | .ok (st', _) => .ok ((), st')
       | .error e => .error e) := by
  obtain ⟨a, hArgs⟩ := hDecode
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hArgs, hValid]

/-- **The live `.tcbSetMCPriority` arm routes to `setMCPriorityOnCore`.**  Same
reroute, reached whenever the new ceiling caps the target's current priority. -/
theorem dispatchWithCap_tcbSetMCPriority_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId) (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
    (args : Architecture.SyscallArgDecode.SetMCPriorityArgs) (st : SystemState)
    (hSyscall : decoded.syscallId = .tcbSetMCPriority)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeSetMCPriorityArgs decoded = .ok args)
    (hCaller : validateThreadIdArg tid = .ok vCallerTid)
    (hValid : validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vTargetTid) :
    dispatchWithCap decoded tid executingCore gate cap st =
      (match SchedContext.PriorityManagement.setMCPriorityOnCore st vCallerTid vTargetTid
              (SeLe4n.Priority.ofNat args.newMCP) executingCore with
       | .ok (st', _) => .ok ((), st')
       | .error e => .error e) := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode, hCaller, hValid]

/-- **The delegation obligation for a syscall, as a proposition indexed by it.**

PR #861 review round 11: the first cut of this mechanism recorded delegation
evidence as a `String` validated by `niName!`.  That checks only that *some*
declaration by that name exists — the `.receive` entry could have cited
`dispatchWithCap_tcbSuspend_delegates` and every count would still have passed.
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
      ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (epId : SeLe4n.ObjId) (st : SystemState),
        decoded.syscallId = .send →
        cap.target = .object epId →
        dispatchWithCap decoded tid executingCore gate cap st =
          (match endpointSendDualWithCapsOnCore epId tid (.frame cap.badge (cap.rights.mem .grant))
                  decoded.capRecvSlot
                  executingCore st with
           | (_, .error e) => .error e
           | (st', .ok (summary, _)) =>
               match clearWokenReceiverStash ((st.getEndpoint? epId).bind (·.receiveQ.head)) st' with
               | .error e => .error e
               | .ok ((), st'') =>
                   .ok ((), Architecture.stageWokenDelivery st''
                             ((st.getEndpoint? epId).bind (·.receiveQ.head))
                             summary.installedCount))
  | .tcbSetPriority =>
      ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (objId : SeLe4n.ObjId)
        (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
        (args : Architecture.SyscallArgDecode.SetPriorityArgs) (st : SystemState),
        decoded.syscallId = .tcbSetPriority →
        cap.target = .object objId →
        decodeSetPriorityArgs decoded = .ok args →
        validateThreadIdArg tid = .ok vCallerTid →
        validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vTargetTid →
        dispatchWithCap decoded tid executingCore gate cap st =
          (match SchedContext.PriorityManagement.setPriorityOnCore st vCallerTid vTargetTid
                  (SeLe4n.Priority.ofNat args.newPriority) executingCore with
           | .ok (st', _) => .ok ((), st')
           | .error e => .error e)
  | .tcbSetMCPriority =>
      ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (objId : SeLe4n.ObjId)
        (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
        (args : Architecture.SyscallArgDecode.SetMCPriorityArgs) (st : SystemState),
        decoded.syscallId = .tcbSetMCPriority →
        cap.target = .object objId →
        decodeSetMCPriorityArgs decoded = .ok args →
        validateThreadIdArg tid = .ok vCallerTid →
        validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vTargetTid →
        dispatchWithCap decoded tid executingCore gate cap st =
          (match SchedContext.PriorityManagement.setMCPriorityOnCore st vCallerTid vTargetTid
                  (SeLe4n.Priority.ofNat args.newMCP) executingCore with
           | .ok (st', _) => .ok ((), st')
           | .error e => .error e)
  | .receive =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
        (gate : SyscallGate) (cap : Capability) (epId : SeLe4n.ObjId)
        (replyIdOpt : Option SeLe4n.ReplyId) (st : SystemState),
        decoded.syscallId = .receive →
        cap.target = .object epId →
        securityFlowsTo (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = true →
        -- WS-SM SM8.C: the arm's gate is the global lattice check AND this
        -- endpoint's configured override, so the obligation carries both.
        endpointOverrideAllows ctx epId (ctx.endpointLabelOf epId)
          (ctx.threadLabelOf tid) = true →
        resolveRecvReplyId gate decoded st = .ok replyIdOpt →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
          (match endpointReceiveDualWithCapsOnCore epId tid replyIdOpt gate.cspaceRoot
                  decoded.capRecvSlot executingCore st with
           -- WS-RA RA.B.6: the arm stages the non-blocking consume's delivery
           -- into the caller's return frame.  PR #873 round 6: with the receive
           -- routed through the WithCaps transition, the staged `extraCaps` is
           -- the transfer summary's installed count rather than a hardcoded 0.
           -- WS-OD OD3.6: and the rendezvous donation runs between them, in the
           -- checked arm as in the unchecked one and behind no extra gate.  The
           -- obligation names it: a delegation claim that omitted a step would
           -- be a claim about a different program.
           | (st', .ok (dequeued, summary, _)) =>
               (match applyReceiveRendezvousHandoff st' tid dequeued
                        executingCore with
                | .error e => .error e
                | .ok stDon =>
                    .ok ((), Architecture.stageDeliveredMessage
                              (Architecture.stageWokenSendCompletion stDon
                                ((st.getEndpoint? epId).bind (·.sendQ.head))) tid
                              summary.installedCount))
           | (_, .error e) => .error e)
  | .tcbSuspend =>
      ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (objId : SeLe4n.ObjId) (vtid : SeLe4n.ValidThreadId)
        (st : SystemState),
        decoded.syscallId = .tcbSuspend →
        cap.target = .object objId →
        (∃ a, Architecture.SyscallArgDecode.decodeSuspendArgs decoded = .ok a) →
        validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vtid →
        dispatchWithCap decoded tid executingCore gate cap st =
          (match Lifecycle.Suspend.suspendThreadOnCore st vtid
                  executingCore with
           | .ok (st', _) => .ok ((), st')
           | .error e => .error e)
  | .tcbResume =>
      ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (objId : SeLe4n.ObjId) (vtid : SeLe4n.ValidThreadId)
        (st : SystemState),
        decoded.syscallId = .tcbResume →
        cap.target = .object objId →
        (∃ a, Architecture.SyscallArgDecode.decodeResumeArgs decoded = .ok a) →
        validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vtid →
        dispatchWithCap decoded tid executingCore gate cap st =
          (match Lifecycle.Suspend.resumeThreadOnCore
                  (retirePendingFaultForResume st vtid.val) vtid
                  executingCore with
           | .ok (st', _) => .ok ((), st')
           | .error e => .error e)
  | .schedContextUnbind =>
      ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (scId : SeLe4n.ObjId) (vScId : SeLe4n.ValidObjId)
        (st : SystemState),
        decoded.syscallId = .schedContextUnbind →
        cap.target = .object scId →
        (∃ a, decodeSchedContextUnbindArgs decoded = .ok a) →
        validateObjIdArg scId = .ok vScId →
        dispatchWithCap decoded tid executingCore gate cap st =
          (match SchedContextOps.schedContextUnbindOnCore vScId
                  executingCore st with
           | .ok (st', _) => .ok ((), st')
           | .error e => .error e)
  | .vspaceMap =>
      ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (objId : SeLe4n.ObjId)
        (args : Architecture.SyscallArgDecode.VSpaceMapArgs) (st : SystemState),
        decoded.syscallId = .vspaceMap →
        cap.target = .object objId →
        decodeVSpaceMapArgs decoded st.machine.maxASID = .ok args →
        vspaceCapAuthorizesAsid cap args.asid st = true →
        dispatchWithCap decoded tid executingCore gate cap st = vspaceMapFromFrameCap tid executingCore args st
  | .vspaceUnmap =>
      ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (objId : SeLe4n.ObjId)
        (args : Architecture.SyscallArgDecode.VSpaceUnmapArgs) (st : SystemState),
        decoded.syscallId = .vspaceUnmap →
        cap.target = .object objId →
        decodeVSpaceUnmapArgs decoded st.machine.maxASID = .ok args →
        vspaceCapAuthorizesAsid cap args.asid st = true →
        dispatchWithCap decoded tid executingCore gate cap st =
          Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast
            executingCore args.asid args.vaddr st
  -- Every other syscall: no delegation theorem exists yet.  `False` rather than
  -- `True` so the absence is unforgeable — an inventory entry claiming
  -- delegation evidence for one of these cannot be constructed.
  -- WS-SM SM8.C.9: the live `.declassify` arm.  Stated over the *checked*
  -- dispatch, like `.receive`, because that is the only path it has: the
  -- unchecked one fails closed (`dispatchWithCap_declassify_denied`).
  | .declassify =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
        (gate : SyscallGate) (cap : Capability) (targetId : SeLe4n.ObjId) (st : SystemState),
        decoded.syscallId = .declassify →
        cap.target = .object targetId →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
          declassifyObjectFromCore (liftLegacyContext ctx) ctx.declassificationPolicy
            executingCore targetId st
  -- WS-SM SM9.C.9: the live data-carrying declassification.  Checked dispatch
  -- only, like `.declassify` — and the conclusion names the *whole arm*, so an
  -- arm that ran the transition and skipped the stash clear or either stager
  -- would not satisfy this.
  | .declassifySignal =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
        (gate : SyscallGate) (cap : Capability) (notifId : SeLe4n.ObjId)
        (args : Architecture.SyscallArgDecode.NotificationSignalArgs) (st : SystemState),
        decoded.syscallId = .declassifySignal →
        cap.target = .object notifId →
        decodeNotificationSignalArgs decoded = .ok args →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
          (match notificationSignalDeclassifiedCrossCoreDispatch (liftLegacyContext ctx)
                  ctx.declassificationPolicy notifId args.badge executingCore st with
           | (st', .ok _) =>
               (match clearWokenReceiverStash ((boundDeliveryTarget? st notifId).map (·.1)) st' with
                | .error e => .error e
                | .ok ((), st'') =>
                    .ok ((), Architecture.stageWokenDelivery
                              (Architecture.stageWokenDelivery st''
                                ((boundDeliveryTarget? st notifId).map (·.1)) 0)
                              (notificationSignalWaiter? st notifId) 0))
           | (_, .error e) => .error e)
  -- WS-SM SM9.A.10: the live audit arms.  Stated over the *checked* dispatch,
  -- like `.declassify`, because that is the only path they have — and the
  -- conclusion names the return-frame write, so an arm that computed the right
  -- word and failed to stage it would not satisfy this.
  | .auditRead =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
        (gate : SyscallGate) (cap : Capability)
        (args : Architecture.SyscallArgDecode.AuditReadArgs) (op : AuditReadOp)
        (st : SystemState),
        decoded.syscallId = .auditRead →
        cap.target = .auditTrail →
        cap.hasRight gate.requiredRight = true →
        Architecture.SyscallArgDecode.decodeAuditReadArgs decoded = .ok args →
        decodeAuditReadOp args.opcode args.index args.chunk = some op →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
          (match auditReadFromCore (liftLegacyContext ctx) (validatedAuditMonitorClearance ctx)
              executingCore op st with
           | .error e => .error e
           | .ok (w, st') =>
               .ok ((), Architecture.writeReturnFrameToTcb st' tid
                 (Architecture.returnFrameOfWord w.toUInt64)))
  | .auditDrain =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
        (gate : SyscallGate) (cap : Capability)
        (args : Architecture.SyscallArgDecode.AuditDrainArgs) (st : SystemState),
        decoded.syscallId = .auditDrain →
        cap.target = .auditTrail →
        cap.hasRight gate.requiredRight = true →
        Architecture.SyscallArgDecode.decodeAuditDrainArgs decoded = .ok args →
        dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
          (match auditDrainVisiblePrefix (liftLegacyContext ctx)
              (validatedAuditMonitorClearance ctx)
              executingCore args.count st with
           | .error e => .error e
           | .ok (n, st') =>
               .ok ((), Architecture.writeReturnFrameToTcb st' tid
                 (Architecture.returnFrameOfWord n.toUInt64)))
  -- WS-BP BP7.1 (slice 3): the live `.untypedReset` arm.  No decode and no
  -- authority conjunct beyond the dispatcher's own `.retype` right check: the
  -- reset's refusals are its own, and the conclusion names the whole operation.
  -- WS-ZA ZA5.4 part 14: the carve, the one way a kernel object is made.
  | .untypedRetype =>
      ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (untypedId : SeLe4n.ObjId) (st : SystemState),
        decoded.syscallId = .untypedRetype →
        cap.target = .object untypedId →
        dispatchWithCap decoded tid executingCore gate cap st =
          untypedRetypeFromCap tid executingCore decoded.capAddr
            (decodeUntypedRetypeArgs decoded) st
  | .untypedReset =>
      ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (untypedId : SeLe4n.ObjId) (st : SystemState),
        decoded.syscallId = .untypedReset →
        cap.target = .object untypedId →
        dispatchWithCap decoded tid executingCore gate cap st =
          untypedResetFromCap tid decoded.capAddr st
  -- WS-BP BP7.1 (`v0.36.7`): the two destroying arms.  Each names the finalising
  -- composite — the delete or the revocation, then the removal of every mapping a
  -- destroyed frame capability recorded — at the invoking thread's core.
  | .cspaceDelete =>
      ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (cnodeId : SeLe4n.ObjId)
        (args : Architecture.SyscallArgDecode.CSpaceDeleteArgs) (st : SystemState),
        decoded.syscallId = .cspaceDelete →
        cap.target = .object cnodeId →
        decodeCSpaceDeleteArgs decoded = .ok args →
        dispatchWithCap decoded tid executingCore gate cap st =
          if !cnodeInvoked cnodeId st then .error .objectNotFound else
            cspaceDeleteSlotZombie executingCore
              { cnode := cnodeId, slot := args.targetSlot } st
  | .cspaceRevoke =>
      ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (cnodeId : SeLe4n.ObjId)
        (args : Architecture.SyscallArgDecode.CSpaceDeleteArgs) (st : SystemState),
        decoded.syscallId = .cspaceRevoke →
        cap.target = .object cnodeId →
        decodeCSpaceDeleteArgs decoded = .ok args →
        dispatchWithCap decoded tid executingCore gate cap st =
          if !cnodeInvoked cnodeId st then .error .objectNotFound else
            cspaceRevokeCdtFinalising executingCore
              { cnode := cnodeId, slot := args.targetSlot } st
  -- WS-ZA ZA5.4 part 22: the space change, which retires what each slot's old
  -- capability took with it at the invoking thread's core.
  | .tcbSetSpace =>
      ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (gate : SyscallGate)
        (cap : Capability) (objId : SeLe4n.ObjId)
        (args : Architecture.SyscallArgDecode.SetSpaceArgs) (vtid : SeLe4n.ValidThreadId)
        (cnSrc vrSrc : CSpaceAddr) (st : SystemState),
        decoded.syscallId = .tcbSetSpace →
        cap.target = .object objId →
        Architecture.SyscallArgDecode.decodeSetSpaceArgs decoded = .ok args →
        validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vtid →
        resolveSetSpace tid args st = .ok (cnSrc, vrSrc) →
        dispatchWithCap decoded tid executingCore gate cap st =
          (match copyThreadSpacesZombie executingCore st vtid cnSrc vrSrc with
           | .ok st' => .ok ((), st')
           | .error e => .error e)
  -- WS-ZA ZA4.3: the capability-free yield.  Both dispatchers run it from the
  -- guard ahead of the caller's CSpace lookup, so the obligation is stated
  -- over the dispatchers themselves: once the caller is current on the
  -- executing core, each IS the yield's own transition.
  | .yield =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
        (executingCore : Concurrency.CoreId) (st : SystemState),
        decoded.syscallId = .yield →
        st.scheduler.currentOnCore executingCore = some tid →
        dispatchSyscall decoded tid executingCore st = dispatchYield executingCore st ∧
        dispatchSyscallChecked ctx decoded tid executingCore st = dispatchYield executingCore st
  -- WS-ZA ZA6.9: the Consumed arm IS the Consumed invocation of the context the
  -- capability names, on the executing core.
  | .schedContextConsumed =>
      ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
        (gate : SyscallGate) (cap : Capability) (scId : SeLe4n.ObjId) (vScId : SeLe4n.ValidObjId)
        (st : SystemState),
        decoded.syscallId = .schedContextConsumed →
        cap.target = .object scId →
        validateObjIdArg scId = .ok vScId →
        dispatchWithCap decoded tid executingCore gate cap st =
          (match schedContextConsumedOnCore (SeLe4n.SchedContextId.ofObjId vScId.val)
                  executingCore st with
           | .ok st' => .ok ((), st')
           | .error e => .error e)
  | _ => False

/-- WS-ZA ZA4.3: the `.yield` obligation, discharged. -/
theorem syscallDelegates_yield : syscallDelegates .yield := by
  intro ctx decoded tid executingCore st hSyscall hCur
  exact ⟨by simp [dispatchSyscall, hSyscall, hCur], by simp [dispatchSyscallChecked, hSyscall, hCur]⟩

/-- WS-ZA ZA6.9: the `.schedContextConsumed` obligation, discharged. -/
theorem syscallDelegates_schedContextConsumed : syscallDelegates .schedContextConsumed := by
  intro decoded tid executingCore gate cap scId vScId st hSyscall hTarget hValid
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hValid]

/-- The `.receive` obligation, discharged. -/
theorem syscallDelegates_receive : syscallDelegates .receive := by
  intro ctx decoded tid executingCore gate cap epId replyIdOpt st hSyscall hTarget hFlow hOverride hReply
  exact dispatchWithCapChecked_receive_delegates ctx decoded tid executingCore gate cap epId replyIdOpt st
    hSyscall hTarget hFlow hOverride hReply

/-- The `.tcbResume` obligation, discharged. -/
theorem syscallDelegates_tcbResume : syscallDelegates .tcbResume := by
  intro decoded tid executingCore gate cap objId vtid st hSyscall hTarget hDecode hValid
  exact dispatchWithCap_tcbResume_delegates decoded tid executingCore gate cap objId vtid st
    hSyscall hTarget hDecode hValid

/-- The `.tcbSuspend` obligation, discharged. -/
theorem syscallDelegates_tcbSuspend : syscallDelegates .tcbSuspend := by
  intro decoded tid executingCore gate cap objId vtid st hSyscall hTarget hDecode hValid
  exact dispatchWithCap_tcbSuspend_delegates decoded tid executingCore gate cap objId vtid st
    hSyscall hTarget hDecode hValid

/-- WS-SM SM8.B: the `.vspaceMap` obligation, discharged. -/
theorem syscallDelegates_vspaceMap : syscallDelegates .vspaceMap := by
  intro decoded tid executingCore gate cap objId args st hSyscall hTarget hDecode hAuth
  exact dispatchWithCap_vspaceMap_delegates decoded tid executingCore gate cap objId args st
    hSyscall hTarget hDecode hAuth

/-- WS-SM SM8.C.9: the `.declassify` obligation, discharged. -/
theorem syscallDelegates_declassify : syscallDelegates .declassify := by
  intro ctx decoded tid executingCore gate cap targetId st hSyscall hTarget
  exact dispatchWithCapChecked_declassify_delegates ctx decoded tid executingCore gate cap targetId st
    hSyscall hTarget

/-- WS-SM SM9.C.9: the `.declassifySignal` obligation, discharged. -/
theorem syscallDelegates_declassifySignal : syscallDelegates .declassifySignal := by
  intro ctx decoded tid executingCore gate cap notifId args st hSyscall hTarget hDecode
  exact dispatchWithCapChecked_declassifySignal_delegates ctx decoded tid executingCore gate cap notifId
    args st hSyscall hTarget hDecode

/-- WS-SM SM9.A.10: the `.auditRead` obligation, discharged. -/
theorem syscallDelegates_auditRead : syscallDelegates .auditRead := by
  intro ctx decoded tid executingCore gate cap args op st hSyscall hTarget hRight hArgs hOp
  exact dispatchWithCapChecked_auditRead_delegates ctx decoded tid executingCore gate cap args op st
    hSyscall hTarget hRight hArgs hOp

/-- WS-SM SM9.A.10: the `.auditDrain` obligation, discharged. -/
theorem syscallDelegates_auditDrain : syscallDelegates .auditDrain := by
  intro ctx decoded tid executingCore gate cap args st hSyscall hTarget hRight hArgs
  exact dispatchWithCapChecked_auditDrain_delegates ctx decoded tid executingCore gate cap args st
    hSyscall hTarget hRight hArgs

/-- WS-SM SM8.B: the `.vspaceUnmap` obligation, discharged. -/
theorem syscallDelegates_vspaceUnmap : syscallDelegates .vspaceUnmap := by
  intro decoded tid executingCore gate cap objId args st hSyscall hTarget hDecode hAuth
  exact dispatchWithCap_vspaceUnmap_delegates decoded tid executingCore gate cap objId args st
    hSyscall hTarget hDecode hAuth

/-- WS-ZA ZA5.4 part 14: the `.untypedRetype` obligation, discharged — the
carve's cross-core inventory entry rests on it. -/
theorem syscallDelegates_untypedRetype : syscallDelegates .untypedRetype := by
  intro decoded tid executingCore gate cap untypedId st hSyscall hTarget
  exact dispatchWithCap_untypedRetype_delegates decoded tid executingCore gate cap untypedId st
    hSyscall hTarget

/-- WS-BP BP7.1 (slice 3): the `.untypedReset` obligation, discharged. -/
theorem syscallDelegates_untypedReset : syscallDelegates .untypedReset := by
  intro decoded tid executingCore gate cap untypedId st hSyscall hTarget
  exact dispatchWithCap_untypedReset_delegates decoded tid executingCore gate cap untypedId st
    hSyscall hTarget

/-- WS-BP BP7.1 (`v0.36.7`): the `.cspaceDelete` obligation, discharged. -/
theorem syscallDelegates_cspaceDelete : syscallDelegates .cspaceDelete := by
  intro decoded tid executingCore gate cap cnodeId args st hSyscall hTarget hDecode
  exact dispatchWithCap_cspaceDelete_delegates decoded tid executingCore gate cap cnodeId args st
    hSyscall hTarget hDecode

/-- WS-BP BP7.1 (`v0.36.7`): the `.cspaceRevoke` obligation, discharged. -/
theorem syscallDelegates_cspaceRevoke : syscallDelegates .cspaceRevoke := by
  intro decoded tid executingCore gate cap cnodeId args st hSyscall hTarget hDecode
  exact dispatchWithCap_cspaceRevoke_delegates decoded tid executingCore gate cap cnodeId args st
    hSyscall hTarget hDecode

/-- WS-ZA ZA5.4 part 22: the `.tcbSetSpace` obligation, discharged — the space
change's cross-core inventory entry rests on it. -/
theorem syscallDelegates_tcbSetSpace : syscallDelegates .tcbSetSpace := by
  intro decoded tid executingCore gate cap objId args vtid cnSrc vrSrc st hSyscall hTarget hDecode
    hValid hResolve
  exact dispatchWithCap_tcbSetSpace_delegates decoded tid executingCore gate cap objId args vtid
    cnSrc vrSrc st hSyscall hTarget hDecode hValid hResolve

/-- The `.send` obligation, discharged. -/
theorem syscallDelegates_send : syscallDelegates .send := by
  intro decoded tid executingCore gate cap epId st hSyscall hTarget
  exact dispatchWithCap_send_delegates decoded tid executingCore gate cap epId st hSyscall hTarget

/-- The `.tcbSetPriority` obligation, discharged. -/
theorem syscallDelegates_tcbSetPriority : syscallDelegates .tcbSetPriority := by
  intro decoded tid executingCore gate cap objId vCallerTid vTargetTid args st hSyscall hTarget hDecode
    hCaller hValid
  exact dispatchWithCap_tcbSetPriority_delegates decoded tid executingCore gate cap objId vCallerTid
    vTargetTid args st hSyscall hTarget hDecode hCaller hValid

/-- The `.tcbSetMCPriority` obligation, discharged. -/
theorem syscallDelegates_tcbSetMCPriority : syscallDelegates .tcbSetMCPriority := by
  intro decoded tid executingCore gate cap objId vCallerTid vTargetTid args st hSyscall hTarget hDecode
    hCaller hValid
  exact dispatchWithCap_tcbSetMCPriority_delegates decoded tid executingCore gate cap objId vCallerTid
    vTargetTid args st hSyscall hTarget hDecode hCaller hValid

/-- The `.schedContextUnbind` obligation, discharged. -/
theorem syscallDelegates_schedContextUnbind : syscallDelegates .schedContextUnbind := by
  intro decoded tid executingCore gate cap scId vScId st hSyscall hTarget hDecode hValid
  exact dispatchWithCap_schedContextUnbind_delegates decoded tid executingCore gate cap scId vScId st
    hSyscall hTarget hDecode hValid

/-- **`v0.35.204`: the bind arm IS the resolved bind.**  Under a SchedContext
capability and a thread the caller's CSpace resolves MR0 to, the arm's answer is
`schedContextBind` of exactly that pair — so what the arm binds is what
`resolveSchedContextBindThread_ok_authorised` says the caller holds a writable
TCB capability to.  Stated at the state, because the resolver reads it. -/
theorem dispatchCapabilityOnly_schedContextBind_eq
    (decoded : SyscallDecodeResult) (cap : Capability) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (st : SystemState) (scId : SeLe4n.ObjId) (vScId : SeLe4n.ValidObjId)
    (vThreadId : SeLe4n.ValidThreadId)
    (hSyscall : decoded.syscallId = .schedContextBind)
    (hTarget : cap.target = .object scId)
    (hRes : resolveSchedContextBindThread tid (decodeSchedContextBindArgs decoded) st =
      .ok vThreadId)
    (hSc : validateObjIdArg scId = .ok vScId) :
    (dispatchCapabilityOnly decoded cap tid executingCore).map (fun f => f st)
      = some (SchedContextOps.schedContextBind vScId vThreadId st) := by
  unfold dispatchCapabilityOnly
  rw [hSyscall, hTarget]
  simp only [Option.map_some, hRes, hSc]

/-- **`v0.35.204`**: the dispatch-level consequence of the resolver's refusal —
a `.schedContextBind` whose TCB capability the resolver refuses commits nothing
and answers that refusal, whatever SchedContext capability the caller holds.
With `resolveSchedContextBindThread_refuses_idle_capability` this is the successor
of PR #889 review round 11's `dispatchCapabilityOnly_schedContextBind_idle_operand_refused`:
the idle TCB is unreachable through the bind because the chokepoint refuses the
capability, not because a raw operand was checked at its lift point. -/
theorem dispatchCapabilityOnly_schedContextBind_idle_capability_refused
    (decoded : SyscallDecodeResult) (cap : Capability) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (st : SystemState) (scId : SeLe4n.ObjId) (e : KernelError)
    (hSyscall : decoded.syscallId = .schedContextBind)
    (hTarget : cap.target = .object scId)
    (hRes : resolveSchedContextBindThread tid (decodeSchedContextBindArgs decoded) st = .error e) :
    (dispatchCapabilityOnly decoded cap tid executingCore).map (fun f => f st) = some (.error e) := by
  unfold dispatchCapabilityOnly
  rw [hSyscall, hTarget]
  simp only [Option.map_some, hRes]



end SeLe4n.Kernel
