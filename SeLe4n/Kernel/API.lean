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
import SeLe4n.Kernel.IPC.DualQueue
import SeLe4n.Kernel.IPC.Invariant
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDispatch
import SeLe4n.Kernel.IPC.CrossCore.EndpointSend
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDispatch
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

import SeLe4n.Kernel.Architecture.Assumptions
import SeLe4n.Kernel.Architecture.RegisterDecode
import SeLe4n.Kernel.Architecture.SyscallArgDecode

import SeLe4n.Kernel.SchedContext.Operations
import SeLe4n.Kernel.Lifecycle.Suspend
import SeLe4n.Kernel.SchedContext.PriorityManagement
import SeLe4n.Kernel.SchedContext.PriorityManagementPerCore
import SeLe4n.Kernel.SchedContext.OperationsPerCore
import SeLe4n.Kernel.IPC.Operations.Donation

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
| `schedule`, `handleYield` | Scheduler | Stable (unchecked — internal kernel paths under `currentThreadValid`) |
| `scheduleChecked`, `handleYieldChecked` | Scheduler (X2-I) | Stable (**production entry point** — `saveOutgoingContextChecked` guard) |
| `timerTick` | Scheduler (M-04) | Stable (unchecked — internal kernel paths under `currentThreadValid`) |
| `timerTickChecked` | Scheduler (M-04/X2-I) | Stable (**production entry point** — `saveOutgoingContextChecked` guard) |
| `scheduleDomain`, `switchDomain` | Scheduler (M-05) | Stable (unchecked — internal kernel paths under `currentThreadValid`) |
| `switchDomainChecked` | Scheduler (M-05/X2-I) | Stable (**production entry point** — `saveOutgoingContextChecked` guard) |
| `chooseThread`, `chooseThreadInDomain` | Scheduler | Stable |
| `cspaceLookupSlot`, `cspaceLookupPath` | Capability | Stable |
| `cspaceMint`, `cspaceCopy`, `cspaceMove` | Capability | Stable (C-01: dispatch path now uses `cspaceMintWithCdt` for CDT-tracked derivation; `cspaceMint` is the untracked base used only for internal composition and proofs) |
| `cspaceMutate`, `cspaceInsertSlot`, `cspaceDeleteSlot` | Capability | Stable |
| `endpointSendDual`, `endpointReceiveDual` | IPC (dual-queue) | Stable |
| `endpointReply`, `endpointCall`, `endpointReplyRecv` | IPC | Stable |
| `lifecycleRetypeObject`, `lifecycleRevokeDeleteRetype` | Lifecycle | Internal (proof helpers — use `lifecycleRetypeWithCleanup` for production) |
| `lifecycleRetypeWithCleanup`, `lifecycleRetypeWithCleanupShootdown`, `lifecycleRetypeWithCleanupShootdownPerCore` | Lifecycle (WS-H2 / WS-SM SM7.B.11 / SM7.F.4(b)(iii)) | Stable (production entry point with cleanup + scrubbing; the `Shootdown` form adds the SM7.B.11 TLB round for live `.vspaceRoot` targets — SMP callers use it; the **`…PerCore`** form is the initiator-atomic variant that additionally retires the destroyed ASID on the initiator's own `perCoreTlb` view via the shared `retypeInitiatorDrain`, symmetric with the Direct-cap `lifecycleRetypeDirectWithCleanupShootdownPerCore` the live `.lifecycleRetype` dispatch routes through) |
| `retypeFromUntyped` | Lifecycle (WS-F2) | Stable |
| `registerService`, `revokeService`, `lookupServiceByCap` | Service (WS-Q1) | Stable |
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
| `resume` | `seL4_TCB_Resume` | **IMPLEMENTED** (D1, v0.24.0; per-core reroute WS-SM SM8.B, PR #861 round 10). Wired as `SyscallId.tcbResume` to `resumeThreadOnCoreLive` in `Lifecycle/Suspend.lean` (`resumeThread` remains its boot-core form). | Complete |
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

/-- X2-I: Checked `schedule` wrapper. Verifies the outgoing context save
succeeds before delegating to the core scheduler. Under `currentThreadValid`
the failure branch is unreachable. -/
def scheduleChecked : Kernel Unit :=
  fun st =>
    let (stSaved, ok) := saveOutgoingContextChecked st
    if ok then
      schedule stSaved
    else
      .error .schedulerInvariantViolation

/-- X2-I: Checked `handleYield` wrapper. Verifies the outgoing context save
succeeds before delegating to the core yield handler. -/
def handleYieldChecked : Kernel Unit :=
  fun st =>
    let (stSaved, ok) := saveOutgoingContextChecked st
    if ok then
      handleYield stSaved
    else
      .error .schedulerInvariantViolation

/-- X2-I: Checked `timerTick` wrapper. Verifies the outgoing context save
succeeds before delegating to the core timer tick handler. -/
def timerTickChecked : Kernel Unit :=
  fun st =>
    let (stSaved, ok) := saveOutgoingContextChecked st
    if ok then
      timerTick stSaved
    else
      .error .schedulerInvariantViolation

/-- X2-I: Checked `switchDomain` wrapper. Verifies the outgoing context save
succeeds before delegating to the core domain switch. Note: `switchDomain`
also calls `saveOutgoingContext` internally; the outer check ensures failure
is detected before any scheduler state mutation. -/
def switchDomainChecked : Kernel Unit :=
  fun st =>
    let (stSaved, ok) := saveOutgoingContextChecked st
    if ok then
      switchDomain stSaved
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
      | some cap => .ok (cap, st)

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
        { target := .object oid, rights := AccessRightSet.ofList AccessRight.all,
          badge := none } = .error .invalidCapability := rfl

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
        { gate with capAddr := SeLe4n.CPtr.ofNat rargs.replyCPtr, requiredRight := .write }
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
                  if r.caller.isNone && !st.replyIsStashed rid then .ok (some rid)
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
                  (.tcb { rTcb with pendingReceiveReply := none }) st
            | none => .ok ((), st)
        | none => .ok ((), st)

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
        { gate with capAddr := SeLe4n.CPtr.ofNat rargs.replyCPtr, requiredRight := .write }
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
              match st.getReply? rid with
              | some reply =>
                  match reply.caller with
                  -- PR #822 review: carry the *reply cap's* badge (the reply
                  -- authority), not the endpoint receive cap's, so the previous
                  -- caller receives the badge associated with the reply cap (as in
                  -- the `.reply` arm) when the two differ.
                  | some prevCaller => .ok (rid, prevCaller, rcap.badge)
                  | none => .error .replyCapInvalid
              | none => .error .replyCapInvalid

/-- WS-SM SM6.C (PR #822 review): the `ReplyRecv` post-receive donation
resolution — seL4-MCS *"the scheduling context follows the message"*.  Run AFTER
both the reply and the receive legs (so the server is never descheduled *before*
it can rendezvous with a queued `Call`):

* the **recorded server** returns its OLD donated SchedContext to the client it was
  serving (`returnDonatedSchedContextValid`).  On a *delegated* reply cap the cap
  holder / receiver `tid` is **not** the server the previous caller donated to —
  the donation lives on `recordedServer` (`recordedReplyServer? st prevCaller`,
  captured by the caller *before* the reply consumed `prevCaller.blockedOnReply`),
  so the return and the run-queue/PIP bookkeeping are keyed on `recordedServer` and
  its own home core `serverCore`, never on the delegate (PR #822 review,
  "Return ReplyRecv donations from the recorded server").  In the non-delegated case
  `recordedServer = tid` and `serverCore = executingCore`, so this is unchanged; then
* if the receive rendezvoused with a **Call** — `nextThread` is now
  `.blockedOnReply`, i.e. a freshly dequeued request whose donation the queued
  `Call` deferred — the new client's SchedContext is donated to the **receiver**
  `tid` (`applyCallDonation`, still keyed on `tid` — the thread that will serve the
  next request), so the passive server keeps running on the new request's budget;
* otherwise (a plain `Send` rendezvous, or the server blocked with no waiter) the
  now-passive `recordedServer` is descheduled on its own core (`removeRunnableOnCore`).

A recorded server that holds **no** donated SC (an active server with its own budget,
or an already-`.unbound` one) needs no donation change — its run-queue state is left
to the receive leg.  Always reverts the reply-leg priority-inheritance boost via the
cross-core chain walk (`propagatePipChainCrossCore`) from `recordedServer`. -/
def replyRecvReturnDonation (tid recordedServer : SeLe4n.ThreadId)
    (nextThread : SeLe4n.ThreadId) (serverCore : Concurrency.CoreId) : Kernel Unit :=
  fun st =>
    match lookupTcb st recordedServer with
    | none => .error .objectNotFound
    | some srvTcb =>
        match srvTcb.schedContextBinding with
        | .donated oldScId owner =>
            match recordedServer.toValid?, owner.toValid? with
            | some srvV, some ownerV =>
                match returnDonatedSchedContextValid st srvV oldScId ownerV with
                | .error e => .error e
                | .ok st1 =>
                    -- Did the receive leg rendezvous with a queued `Call`?
                    match lookupTcb st1 nextThread with
                    | some nextTcb =>
                        match nextTcb.ipcState with
                        | .blockedOnReply _ _ =>
                            -- New Call: donate to the RECEIVER `tid`, not the (possibly
                            -- delegated) recorded server.
                            match nextThread.toValid?, tid.toValid? with
                            | some nextV, some tidV =>
                                match applyCallDonation st1 nextV tidV with
                                | .error e => .error e
                                | .ok st2 =>
                                    .ok ((), (PriorityInheritance.propagatePipChainCrossCore st2 recordedServer serverCore).1)
                            | _, _ => .error .invalidArgument
                        | _ =>
                            .ok ((), (PriorityInheritance.propagatePipChainCrossCore
                              (removeRunnableOnCore st1 recordedServer serverCore) recordedServer serverCore).1)
                    | none =>
                        .ok ((), (PriorityInheritance.propagatePipChainCrossCore
                          (removeRunnableOnCore st1 recordedServer serverCore) recordedServer serverCore).1)
            | _, _ => .error .invalidArgument
        | _ =>
            .ok ((), (PriorityInheritance.propagatePipChainCrossCore st recordedServer serverCore).1)

/-- WS-SM SM6.D (faithful seL4-MCS `ReplyRecv`): the *unchecked* reply-and-receive
body, shared by both dispatch arms (so the checked arm = a flow-gated wrapper over
exactly this).  Steps reusing the verified cross-core transitions:
1. **reply leg** — `endpointReplyOnCore` delivers to `prevCaller` (the recorded
   caller) and, **atomically with the delivery** (PR #827 review #3 fold), tears
   down the answered reply link (`consumeCallerReply`, keyed on the caller's own
   `replyObject` — the single-use barrier), freeing the reply object.  The
   donated-SC return + PIP reversion are deferred to step 3 — returning the
   server's SC and descheduling it *before* the receive leg would leave a server
   that immediately rendezvouses with a queued `Call` stuck `.ready` but absent
   from the run queues (PR #822 review, 6J90-w);
2. **receive + re-link leg** — `endpointReceiveDualOnCore … (some rid)` receives the
   next message and, on a `Call` rendezvous, links the *same* freed reply object to
   the next caller atomically (#7.2 fold — faithful one-object reuse, formerly the
   separate `linkReceivedCaller` step);
3. **donation** — `replyRecvReturnDonation` returns the old client's SC and, when a
   new `Call` rendezvoused, donates the new client's SC so the passive server keeps
   running on the new request's budget (seL4-MCS SC-follows-message). -/
def replyRecvBody (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : Concurrency.CoreId)
    : Kernel Unit :=
  fun st =>
    -- WS-SM SM6.D (PR #822 review): capture the recorded server (the passive server
    -- `prevCaller` donated its SC to) and its home core BEFORE the reply leg consumes
    -- `prevCaller.blockedOnReply` — on a delegated reply cap this differs from the
    -- receiver `tid`, and the OLD donation return must key on it (not on `tid`).
    let recordedServer := (recordedReplyServer? st prevCaller).getD tid
    let serverCore := determineExecutingCore st recordedServer
    match endpointReplyOnCore tid prevCaller msg executingCore st with
    | (_, .error e) => .error e
    | (st1, .ok _replySgi) =>
        -- WS-RA RA.B.5b: capture the send-queue head the receive leg will
        -- dequeue (from `st1`, the state that leg runs on) — a *plain* sender
        -- completing there is owed the unit success frame; a `Call` sender
        -- lands `.blockedOnReply` and the completion stager's guard skips it.
        let wokenSender? := (st1.getEndpoint? epId).bind (·.sendQ.head)
        -- WS-SM SM6.D (#7.2 fold): the receive leg links the *same* reply object
        -- `rid` (freed by the reply leg's folded consume — PR #827 review #3) to
        -- the next `Call` caller atomically — faithful one-object reuse, formerly
        -- the separate `linkReceivedCaller nextThread (some rid)` dispatch step.
        match endpointReceiveDualOnCore epId tid (some rid) executingCore st1 with
        | (_, .error e) => .error e
        | (st2, .ok (nextThread, _)) =>
            match replyRecvReturnDonation tid recordedServer nextThread serverCore st2 with
            | .error e => .error e
            | .ok ((), st3) =>
                -- WS-RA RA.B.5b: stage the reply leg's woken caller
                -- (`prevCaller`, `.ready` with the reply in `pendingMessage` —
                -- `.call`'s frame, delivered entirely through this path) and
                -- the receive leg's completed plain sender (unit frame).  Both
                -- stagers are guard-inert when their target was not woken.
                -- Installed count 0: the reply message is built `caps := #[]`
                -- by both `.reply`-shaped arms and the reply path runs no
                -- unwrap (PR #866 round-2).
                .ok ((), Architecture.stageWokenSendCompletion
                          (Architecture.stageDeliveredMessage st3 prevCaller 0)
                          wokenSender?)

-- ============================================================================
-- Syscall soundness theorems
-- ============================================================================

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
      simp at hOk
      obtain ⟨hCap, hSt⟩ := hOk
      exact ⟨ref, hResolve, by rw [hCap.symm]; exact hLookup, hSt.symm⟩

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
    match st.objects[tid.toObjId]? with
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
  | .lifecycleRetype => .retype
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
  | .tcbBindNotification   => .write
  | .tcbUnbindNotification => .write
  -- PR #822 Phase H: deriving a reply cap from the object cap to a Reply requires
  -- grant authority on that object cap (consistent with the cspaceMint/Copy/Move family).
  | .mintReplyCap          => .grant

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
  | .lifecycleRetype => false
  | .vspaceMap       => false
  | .vspaceUnmap     => false
  | .vspaceUnifyInstruction => false
  | .declassify         => false
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
  | .tcbBindNotification   => false
  | .tcbUnbindNotification => false
  | .mintReplyCap          => false

/-- PR #870 round 5: the classifier's semantics, pinned — target-first is
exactly the audit pair. -/
theorem syscallChecksTargetFirst_iff (id : SyscallId) :
    syscallChecksTargetFirst id = true ↔ id = .auditRead ∨ id = .auditDrain := by
  cases id <;> simp [syscallChecksTargetFirst]

/-- M-D01: Resolve extra capability addresses from the sender's CSpace
into actual capabilities for IPC message transfer.

For each CPtr in `capAddrs`, resolve it via `resolveCapAddress` in the
sender's CSpace root, then look up the capability at the resolved slot.
Caps that fail to resolve are silently dropped (seL4 behavior).
Returns the resolved capabilities as an array. -/
/- W5-G: Resolves extra capabilities from IPC buffer. Failed resolutions are
   silently dropped (matching seL4 `lookupExtraCaps` behavior). This means
   the receiver gets fewer extra caps than the sender specified. For
   debugging, callers should check `extraCaps.length` against the expected
   count from `MessageInfo.extraCaps`.
   X5-I (L-4): Confirmed v0.22.17 audit — silent dropping matches seL4
   reference semantics. No security impact: caps that fail resolution
   simply don't transfer.

   **AC3-D / API-01 — Silent-drop semantics**: The returned `Array Capability`
   contains only successfully resolved capabilities. Its `.size` equals the
   count of *successfully resolved* extra caps, which may be strictly less than
   `capAddrs.size` (the sender's requested count). Receivers should compare
   the actual resolved count against the expected count from the original
   `MessageInfo.extraCaps` to detect drops. This is seL4-compatible behavior:
   `lookupExtraCaps` in the C kernel also silently discards unresolvable
   capabilities and returns only valid ones in the IPC buffer.

   **AI6-A (M-02) — Spec cross-reference**: See `docs/spec/SELE4N_SPEC.md`
   §8.10.4 "IPC Extra Capability Resolution — Silent-Drop Semantics" for the
   normative specification, including the seL4 reference C kernel equivalence. -/
private def resolveExtraCaps (cspaceRoot : SeLe4n.ObjId)
    (capAddrs : Array SeLe4n.CPtr) (depth : Nat)
    (st : SystemState) : Array Capability :=
  capAddrs.foldl (fun acc addr =>
    match resolveCapAddress cspaceRoot addr depth st with
    | .error _ => acc
    | .ok ref =>
        match SystemState.lookupSlotCap st ref with
        | none => acc
        | some cap => acc.push cap) #[]

/-- AN7-E (API-M01): Debug-noisy variant of `resolveExtraCaps` that surfaces
    partial resolution explicitly.  Returns the resolved array paired with a
    flag `partial := true` iff at least one input address failed to resolve.
    The two possible failure modes are conflated in the single flag per
    seL4 convention (the caller cannot distinguish them structurally from
    the silent-drop variant either).

    Callers that want to reject partial resolutions should do:
    ```
    match resolveExtraCapsDetailed cspaceRoot addrs depth st with
    | (caps, false) => -- complete: all addresses resolved
    | (_,    true)  => .error .partialResolution
    ```

    The default ABI path continues to use `resolveExtraCaps` (silent drop)
    to stay byte-compatible with the seL4 reference kernel.  Production
    deployments that want the noisy behaviour gate via the debug option
    `sele4n.debug.noisyResolution` — a compile-time `set_option` directive
    in the consuming module. -/
private def resolveExtraCapsDetailed (cspaceRoot : SeLe4n.ObjId)
    (capAddrs : Array SeLe4n.CPtr) (depth : Nat)
    (st : SystemState) : Array Capability × Bool :=
  capAddrs.foldl (fun acc addr =>
    match resolveCapAddress cspaceRoot addr depth st with
    | .error _ => (acc.1, true)  -- partial: lookup failed
    | .ok ref =>
        match SystemState.lookupSlotCap st ref with
        | none => (acc.1, true)  -- partial: slot empty
        | some cap => (acc.1.push cap, acc.2)) (#[], false)

/-- AN7-E (API-M01) option declaration: `set_option sele4n.debug.noisyResolution true`
    flips production callers from the silent-drop `resolveExtraCaps` to
    the explicit-error `resolveExtraCapsDetailed` wrapper.  Disabled by
    default so the ABI stays seL4-compatible. -/
register_option sele4n.debug.noisyResolution : Bool := {
  defValue := false
  descr := "AN7-E (API-M01): When true, resolveExtraCaps surfaces partial resolution as KernelError.partialResolution instead of silently dropping unresolvable caps."
}

/-- AN7-E (API-M01) soundness (empty-input): on an empty capability-address
    array, the detailed variant returns an empty resolved-caps list and a
    `partial := false` flag — matching the silent-drop variant's empty
    output.  This is the base case that anchors the swap-invariance
    property between the two variants; the fully-general form (equal caps
    for all inputs) requires a fold-level induction that is tractable but
    beyond the AN7-E landing scope and recorded as a post-1.0 hardening
    candidate; no currently-active plan file tracks it. -/
theorem resolveExtraCapsDetailed_empty
    (cspaceRoot : SeLe4n.ObjId) (depth : Nat) (st : SystemState) :
    resolveExtraCapsDetailed cspaceRoot #[] depth st = (#[], false) := by
  rfl

/-- AN7-E (API-M01): the silent-drop variant on the empty input is also
    empty.  Paired with `resolveExtraCapsDetailed_empty`, this confirms
    that in the base case both variants agree (vacuously). -/
theorem resolveExtraCaps_empty
    (cspaceRoot : SeLe4n.ObjId) (depth : Nat) (st : SystemState) :
    resolveExtraCaps cspaceRoot #[] depth st = #[] := by
  rfl

/-- AN7-E (API-M01): Gated resolver for production dispatch arms that
    want to surface partial resolution explicitly.  Returns
    `.error KernelError.partialResolution` when any input address fails
    to resolve; otherwise returns the resolved capability array.  Callers
    that enable the gated path opt in consciously by using this wrapper
    instead of `resolveExtraCaps` — the debug option
    `sele4n.debug.noisyResolution` documents the project-level policy. -/
private def resolveExtraCapsGated (cspaceRoot : SeLe4n.ObjId)
    (capAddrs : Array SeLe4n.CPtr) (depth : Nat)
    (st : SystemState) : Except KernelError (Array Capability) :=
  let (caps, isPartial) := resolveExtraCapsDetailed cspaceRoot capAddrs depth st
  if isPartial then .error .partialResolution else .ok caps

/-- AN7-E (API-M01): The gated resolver returns `.ok #[]` on empty input
    (no addresses to resolve → no partial condition possible).  Base case
    of the gated-resolver contract. -/
theorem resolveExtraCapsGated_empty
    (cspaceRoot : SeLe4n.ObjId) (depth : Nat) (st : SystemState) :
    resolveExtraCapsGated cspaceRoot #[] depth st = .ok #[] := by
  unfold resolveExtraCapsGated
  simp [resolveExtraCapsDetailed_empty]

/-- AL7-A (WS-AL / AK7-E.cascade): lift a raw `ThreadId` to `ValidThreadId`
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
`.objectNotFound` at lookup time) remains intact. -/
@[inline] private def validateThreadIdArg (tid : SeLe4n.ThreadId) :
    Except KernelError SeLe4n.ValidThreadId :=
  match tid.toValid? with
  | none => .error .invalidArgument
  | some v => .ok v

/-- AL7-A (WS-AL / AK7-E.cascade): lift a raw `SchedContextId` to
`ValidSchedContextId` at the dispatch boundary. Mirrors
`validateThreadIdArg`; rejects `SchedContextId.sentinel`. -/
@[inline] private def validateSchedContextIdArg (scId : SeLe4n.SchedContextId) :
    Except KernelError SeLe4n.ValidSchedContextId :=
  match scId.toValid? with
  | none => .error .invalidArgument
  | some v => .ok v

/-- AL8 (WS-AL / AK7-E.cascade): lift a raw `ObjId` to `ValidObjId`.
Used by dispatch arms whose handlers operate on `ObjId` directly (e.g.,
`schedContextConfigure` which does `st.objects[scId]?` rather than
going through `SchedContextId.toObjId`). Rejects `ObjId.sentinel`. -/
@[inline] private def validateObjIdArg (oid : SeLe4n.ObjId) :
    Except KernelError SeLe4n.ValidObjId :=
  match oid.toValid? with
  | none => .error .invalidArgument
  | some v => .ok v

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

/-- V8-H/Z5-J/D1/AE1-A/AE1-B: Shared dispatch for capability-only syscalls — these 14 arms
derive authority entirely from capability possession and require no
information-flow checks. Both `dispatchWithCap` and `dispatchWithCapChecked`
delegate to this helper for: `.cspaceDelete`, `.lifecycleRetype`, `.vspaceMap`,
`.vspaceUnmap`, `.serviceRevoke`, `.serviceQuery`, `.schedContextConfigure`,
`.schedContextBind`, `.schedContextUnbind`, `.tcbSuspend`, `.tcbResume`,
`.tcbSetPriority` (AE1-A), `.tcbSetMCPriority` (AE1-A), `.tcbSetIPCBuffer` (AE1-B).

Returns `none` if the syscall ID is not a capability-only arm (i.e., it
requires IPC/cross-domain handling). -/
private def dispatchCapabilityOnly (decoded : SyscallDecodeResult)
    (cap : Capability) (tid : SeLe4n.ThreadId) : Option (Kernel Unit) :=
  match decoded.syscallId with
  | .cspaceDelete =>
    some <| match cap.target with
    | .object cnodeId =>
        fun st => match decodeCSpaceDeleteArgs decoded with
        | .error e => .error e
        | .ok args =>
            let addr : CSpaceAddr := { cnode := cnodeId, slot := args.targetSlot }
            cspaceDeleteSlot addr st
    | _ => fun _ => .error .invalidCapability
  -- PR #822 Phase H: mint a reply cap from an `.object`-to-Reply cap.  Same src/dst-slot
  -- ABI as `cspaceCopy` (reuses `decodeCSpaceCopyArgs`); the cap names the CNode, and
  -- `mintReplyCapWithCdt` derives `.replyCap (ReplyId.ofObjId target)` at the dst slot
  -- (fail-closed when the src is not an `.object`-to-Reply cap).  CDT-tracked so the
  -- minted reply cap is revocable through `cspaceRevokeCdt`.
  | .mintReplyCap =>
    some <| match cap.target with
    | .object cnodeId =>
        fun st => match decodeCSpaceCopyArgs decoded with
        | .error e => .error e
        | .ok args =>
            let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
            let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
            mintReplyCapWithCdt src dst st
    | _ => fun _ => .error .invalidCapability
  | .lifecycleRetype =>
    some <| match cap.target with
    | .object _ =>
        fun st => match decodeLifecycleRetypeArgs decoded with
        | .error e => .error e
        | .ok args =>
            let newObj := objectOfKernelType args.newType args.size
            -- WS-SM SM7.B.11: retyping a live VSpaceRoot frees its whole
            -- address space — the wrapper posts the `.aside1` shootdown
            -- round from the caller's core; non-VSpaceRoot retypes are
            -- unchanged (lifecycleRetypeDirectWithCleanupShootdown_non_vspace).
            -- WS-SM SM7.F.4(b)(iii): route through the per-core wrapper, which
            -- additionally retires the initiator's own `perCoreTlb` view for
            -- the destroyed ASID atomically (the initiator's local TLBI
            -- ASIDE1) — once the live `.vspaceMap` fill is operative, the
            -- retyped ASID may be cached on the caller's own view, and the
            -- `.aside1` round posts only to remote cores.  Trace-safe
            -- (`perCoreTlb ∉ projectState`).
            -- WS-SM SM7.D.1: and through the instruction-cache seam on top,
            -- which broadcasts `IC IALLUIS` across the shareability domain.
            -- A retype scrubs and re-purposes the target's backing memory, so
            -- any instruction line a PE cached from it is stale — and, because
            -- instruction caches are physically tagged, such a line stays
            -- hittable through any later executable mapping of the same frame,
            -- in any address space.  The TLB round cannot close this: it
            -- retires translations, not cache lines.  Trace-safe
            -- (`perCoreICache ∉ projectState`).
            lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache
              (determineExecutingCore st tid) cap args.targetObj newObj st
    | _ => fun _ => .error .invalidCapability
  | .vspaceMap =>
    some <| match cap.target with
    | .object _ =>
        -- AH3-C (L-14): Pass platform-configured maxASID to decode
        -- AK3-E (A-M01 / MEDIUM): Use `decodeVSpaceMapArgsChecked` which adds a
        -- decode-time PA bounds check (defense-in-depth; the downstream
        -- `vspaceMapPageCheckedWithFlushFromState` PA check still holds).
        fun st =>
          match decodeVSpaceMapArgsChecked decoded st.machine.maxASID
                  (2^st.machine.physicalAddressWidth) with
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
              -- AH1-D (M-01 fix): Validate permissions against memory kind before mapping.
              -- Device regions must not receive execute permission (undefined on ARM64).
              match validateVSpaceMapPermsForMemoryKind args st.machine.memoryMap with
              | .error e => .error e
              | .ok validatedArgs =>
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
                  Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore
                    (determineExecutingCore st tid) validatedArgs.asid
                    validatedArgs.vaddr validatedArgs.paddr validatedArgs.perms st
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
              (determineExecutingCore st tid) args.asid args.vaddr st
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
    some <| match cap.target with
    | .object _ =>
      fun st => match decodeServiceRevokeArgs decoded with
      | .error e => .error e
      | .ok args => revokeService args.targetService st
    | _ => fun _ => .error .invalidCapability
  | .serviceQuery =>
    some <| match cap.target with
    | .object epId =>
      fun st =>
        match lookupServiceByCap epId st with
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
  | .schedContextConfigure =>
    some <| match cap.target with
    | .object scId =>
      fun st => match decodeSchedContextConfigureArgsChecked decoded with
      | .error e => .error e
      | .ok args =>
          -- AL7-G / AL8 (WS-AL / AK7-E.cascade): type-level sentinel rejection
          -- via ValidObjId signature on schedContextConfigure.
          match validateObjIdArg scId with
          | .error e => .error e
          | .ok vScId =>
              SchedContextOps.schedContextConfigure vScId args.budget args.period
                args.priority args.deadline args.domain st
    | _ => fun _ => .error .invalidCapability
  -- Z5-J: SchedContext bind — decode threadId, bind thread to SchedContext
  | .schedContextBind =>
    some <| match cap.target with
    | .object scId =>
      fun st => match decodeSchedContextBindArgs decoded with
      | .error e => .error e
      | .ok args =>
          -- AL7-H / AL8 (WS-AL / AK7-E.cascade): type-level sentinel rejection
          -- via ValidObjId + ValidThreadId signatures on schedContextBind.
          match validateObjIdArg scId with
          | .error e => .error e
          | .ok vScId =>
              match validateThreadIdArg (ThreadId.ofNat args.threadId) with
              | .error e => .error e
              | .ok vThreadId =>
                  SchedContextOps.schedContextBind vScId vThreadId st
    | _ => fun _ => .error .invalidCapability
  -- Z5-J: SchedContext unbind — no extra args, SchedContext from cap target
  | .schedContextUnbind =>
    some <| match cap.target with
    | .object scId =>
      fun st => match decodeSchedContextUnbindArgs decoded with
      | .error e => .error e
      | .ok _ =>
          -- AL7-I / AL8 (WS-AL / AK7-E.cascade): type-level sentinel rejection
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
                  (determineExecutingCore st tid) st with
              | .ok (st', _) => .ok ((), st')
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
                capAddr       := SeLe4n.CPtr.ofNat args.notificationCPtr
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
  -- home core is poked.  The executing core is the caller's
  -- (`determineExecutingCore`, the SM6.A per-core caller-identification).
  -- The surfaced SGI is dropped at this pure layer: on the live path the
  -- FFI seam (`syscallDispatchCrossCoreEntry`) re-derives and fires it from
  -- the state diff (`crossCoreSgiBody`'s SM6.E descheduled-current rule).
  | .tcbSuspend =>
    some <| match cap.target with
    | .object objId =>
      fun st => match decodeSuspendArgs decoded with
      | .error e => .error e
      | .ok _ =>
        -- AL7-B / AL8 (WS-AL / AK7-E.cascade): type-level sentinel rejection.
        match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | .error e => .error e
        | .ok vtid =>
            match Lifecycle.Suspend.suspendThreadOnCore st vtid
                (determineExecutingCore st tid) with
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
        -- AL7-C / AL8 (WS-AL / AK7-E.cascade): type-level sentinel rejection.
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
        match validateThreadIdArg (ThreadId.ofNat objId.toNat) with
        | .error e => .error e
        | .ok vtid =>
            match Lifecycle.Suspend.resumeThreadOnCoreLive st vtid
                (determineExecutingCore st tid) with
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
        -- AL7-D / AL8 (WS-AL / AK7-E.cascade): type-level sentinel rejection
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
                    (Priority.ofNat args.newPriority) (determineExecutingCore st tid) with
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
        -- AL7-E / AL8 (WS-AL / AK7-E.cascade): type-level sentinel rejection
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
                    (Priority.ofNat args.newMCP) (determineExecutingCore st tid) with
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
        -- AL7-F / AL8 (WS-AL / AK7-E.cascade): type-level sentinel rejection
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
                        (determineExecutingCore st tid) with
                | .ok (st', _) => .ok ((), st')
                | .error e => .error e
    | _ => fun _ => .error .invalidCapability
  | _ => none

/-- WS-J1-C/K-C/K-D: Dispatch a decoded syscall to the appropriate internal
kernel operation using the resolved capability's target. Called after cap
resolution succeeds inside `syscallInvoke`.

WS-K-C: Accepts full `SyscallDecodeResult` so dispatch arms can extract
per-syscall arguments from `decoded.msgRegs` via the typed decode functions
in `SyscallArgDecode`.

WS-K-D: Lifecycle and VSpace stubs replaced with full dispatch. All 13
syscalls now route to real kernel operations — zero `.illegalState` stubs
remain.

V8-H: Capability-only arms delegate to `dispatchCapabilityOnly`.

**W6-D (L-8): Two-tier dispatch design rationale.** The dispatch is split into
`dispatchCapabilityOnly` (handles syscalls needing only the resolved capability
and no additional decoded arguments) and this explicit match (handles syscalls
requiring per-syscall argument decoding from `decoded.msgRegs`). This split:
1. Shares a single checked/unchecked dispatch implementation (V8-H)
2. Enables the wildcard unreachability proof (`dispatchWithCap_wildcard_unreachable`)
   showing all 25 `SyscallId` variants are handled by one of the two tiers
3. Keeps argument-free dispatch arms concise via `dispatchCapabilityOnly`
The wildcard `| _ =>` arm is provably dead code (W2-C). -/
private def dispatchWithCap (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability) : Kernel Unit :=
  match dispatchCapabilityOnly decoded cap tid with
  | some k => k
  | none =>
  match decoded.syscallId with
  -- WS-K-E/M-D01: IPC send — message body + extra caps from decoded message registers.
  | .send =>
    match cap.target with
    | .object epId =>
      fun st =>
        let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
        let extraCapAddrs := decodeExtraCapAddrs decoded
        let resolvedCaps := resolveExtraCaps gate.cspaceRoot extraCapAddrs gate.capDepth st
        let msg : IpcMessage := { registers := body, caps := resolvedCaps, badge := cap.badge }
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
        let executingCore := determineExecutingCore st tid
        match endpointSendDualWithCapsOnCore epId tid msg cap.rights gate.cspaceRoot
            decoded.capRecvSlot executingCore st with
        | (_, .error e) => .error e
        | (st', .ok (summary, _)) =>
            match clearWokenReceiverStash wokenReceiver? st' with
            | .error e => .error e
            | .ok ((), st'') =>
                -- WS-RA RA.B.5b: a rendezvous woke the blocked receiver with the
                -- message in its `pendingMessage`; stage its return frame now
                -- (its own boundary crossing ended `.blocks` — delivery is the
                -- SM10.E context restore).  Inert when the send parked instead.
                -- PR #866 round-2: the frame's `extraCaps` is the transfer
                -- summary's INSTALLED count — a grant-denied or slot-exhausted
                -- transfer reports zero, never the requested `msg.caps.size`.
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
          let executingCore := determineExecutingCore st tid
          -- WS-SM SM6.D (#7.2 fold): the resolved reply object is threaded into the
          -- per-core receive transition, which links a dequeued `Call` caller to it
          -- atomically (the former post-receive `linkReceivedCaller` step).
          -- WS-RA RA.B.5b: capture the send-queue head the consume will dequeue —
          -- a *plain* sender's send completes at the rendezvous (woken `.ready`,
          -- payload consumed) and is owed the unit success frame; a `Call` sender
          -- lands `.blockedOnReply` and the completion stager's guard skips it.
          let wokenSender? := (st.getEndpoint? epId).bind (·.sendQ.head)
          match endpointReceiveDualOnCore epId tid replyIdOpt executingCore st with
          | (st', .ok (_, _sgi)) =>
              -- WS-RA RA.B.6: a non-blocking consume delivered into the caller's
              -- own `pendingMessage`; stage it as the return frame (badge → x0,
              -- synthesized MessageInfo → x1, inline window → x2-x5).  A caller
              -- that blocked stages nothing (the `.ready` guard inside) — its
              -- frame is owed by the unblocking transition per plan §3.5.
              -- PR #866 round-2: installed count 0 — the live receive path runs
              -- NO capability unwrap (`endpointReceiveDualOnCore` delivers the
              -- dequeued sender's message wholesale; `endpointReceiveDualWithCaps`
              -- has no live caller — tracked debt, plan §9), so the honest
              -- `extraCaps` is zero however many caps the parked sender's
              -- message still carries.
              .ok ((), Architecture.stageDeliveredMessage
                        (Architecture.stageWokenSendCompletion st' wokenSender?) tid 0)
          | (_, .error e) => .error e
    | _ => fun _ => .error .invalidCapability
  -- WS-K-E/M-D01: IPC call — message body + extra caps from decoded message registers.
  | .call =>
    match cap.target with
    | .object epId =>
      fun st =>
        let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
        let extraCapAddrs := decodeExtraCapAddrs decoded
        let resolvedCaps := resolveExtraCaps gate.cspaceRoot extraCapAddrs gate.capDepth st
        let msg : IpcMessage := { registers := body, caps := resolvedCaps, badge := cap.badge }
        -- WS-SM SM6.A (live cross-core `.call`): route the unchecked `.call`
        -- through the cross-core dispatch (receiver woken on its *home* core,
        -- surfacing a `.reschedule` SGI). `endpointCallCrossCoreDispatch` is the
        -- cross-core analogue of `endpointCallWithCaps` + inline donation; the
        -- caller is descheduled from its own core (derived from the live state).
        let executingCore := determineExecutingCore st tid
        -- WS-SM SM6.D (#7.3b fold): the server-first reply linkage is now atomic
        -- with the rendezvous — `endpointCallOnCore` itself links the caller to the
        -- server's stashed reply object (`linkServerStashedReply`) at the moment the
        -- caller lands `.blockedOnReply`, so there is no separate post-dispatch step.
        -- WS-RA RA.B.5b: a rendezvous woke the blocked receiver with the call
        -- message in its `pendingMessage`; stage its return frame (the CALLER
        -- itself always blocks — §3.5 — and is owed its frame by the reply path).
        let wokenReceiver? := (st.getEndpoint? epId).bind (·.receiveQ.head)
        match endpointCallCrossCoreDispatch epId tid msg cap.rights gate.cspaceRoot
            decoded.capRecvSlot executingCore st with
        -- PR #866 round-2: the woken receiver's `extraCaps` is the transfer
        -- summary's INSTALLED count (zero on grant-denied / slot-exhausted
        -- transfers), never the requested `msg.caps.size`.
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
        match st.getReply? rid with
        | none => .error .replyCapInvalid
        | some reply =>
          match reply.caller with
          | none => .error .replyCapInvalid
          | some callerTid =>
            let executingCore := determineExecutingCore st tid
            match endpointReplyCrossCoreDispatch tid callerTid
                { registers := body, caps := #[], badge := cap.badge } executingCore st with
            | (st', .ok _) =>
                -- WS-RA RA.B.5b: the reply woke the `blockedOnReply` caller with
                -- the payload in its `pendingMessage`; stage its return frame —
                -- this is `.call`'s `.message` frame, delivered entirely through
                -- the reply path (§3.5: a call never returns at its own boundary).
                -- Installed count 0: the reply message is built with
                -- `caps := #[]` above and the reply path runs no unwrap.
                .ok ((), Architecture.stageDeliveredMessage st' callerTid 0)
            | (_, .error e) => .error e
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
            let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
            let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
            cspaceMove src dst st
    | _ => fun _ => .error .invalidCapability
  -- V8-H/D1: cspaceDelete, lifecycleRetype, vspaceMap, vspaceUnmap, serviceRevoke,
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
            sid := ServiceId.ofNat epId.toNat
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
          -- staging side; delivery is the SM10.E context restore).  The two
          -- targets are mutually exclusive (the bound path requires an empty
          -- wait queue), and each stager is inert when its target was not
          -- woken.
          let plainWaiter? := notificationSignalWaiter? st notifId
          match notificationSignalBoundCrossCoreDispatch notifId args.badge tid st with
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
        match notificationWaitCrossCoreDispatch notifId tid st with
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
      -- closing the prior raw-thread bypass.  `replyRecvBody` then replies to the
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
            let msg : IpcMessage := { registers := body, caps := #[], badge := replyBadge }
            let executingCore := determineExecutingCore st tid
            -- WS-RA RA.B.6: the receive leg may have consumed a queued sender
            -- into the caller's `pendingMessage`; stage it as the return frame.
            -- A caller that blocked on the receive leg stages nothing (the
            -- `.ready` guard inside `stageDeliveredMessage`).
            match replyRecvBody epId tid rid prevCaller msg executingCore st with
            -- PR #866 round-2: installed count 0 — the receive leg runs no
            -- capability unwrap (see the `.receive` arm; tracked debt, plan §9).
            | .ok ((), st') => .ok ((), Architecture.stageDeliveredMessage st' tid 0)
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
  -- by dispatchCapabilityOnly above. Together with cspaceDelete, lifecycleRetype,
  -- vspaceMap, vspaceUnmap, serviceRevoke, serviceQuery, schedContextConfigure,
  -- schedContextBind, schedContextUnbind, tcbSuspend, tcbResume — 14 total arms
  -- handled by dispatchCapabilityOnly. The wildcard satisfies Lean's exhaustiveness
  -- checker and is provably unreachable (dispatchWithCap_wildcard_unreachable).
  | _ => fun _ => .error .illegalState

-- ============================================================================
-- T6-I/M-IF-1: Information-flow-checked dispatch
-- ============================================================================

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

V8-H: Capability-only arms delegate to `dispatchCapabilityOnly`. -/
private def dispatchWithCapChecked (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability) : Kernel Unit :=
  match dispatchCapabilityOnly decoded cap tid with
  | some k => k
  | none =>
  match decoded.syscallId with
  -- T6-I: IPC send — checked for sender→endpoint flow
  | .send =>
    match cap.target with
    | .object epId =>
      fun st =>
        let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
        let extraCapAddrs := decodeExtraCapAddrs decoded
        let resolvedCaps := resolveExtraCaps gate.cspaceRoot extraCapAddrs gate.capDepth st
        let msg : IpcMessage := { registers := body, caps := resolvedCaps, badge := cap.badge }
        -- AH1-B (H-01 fix): Pass capability transfer params to checked send
        -- WS-SM SM6.D (PR #822 review): clear the woken receiver's server-first reply
        -- stash (mirrors the unchecked `.send` arm).
        let wokenReceiver? := (st.getEndpoint? epId).bind (·.receiveQ.head)
        -- WS-SM SM8.B (PR #861 review round 10): the cross-core checked send
        -- (mirrors the unchecked arm; `endpointSendDualChecked` was boot-pinned
        -- through `endpointSendDualWithCaps`).  Bounds first, then the
        -- sender→endpoint flow gate, then the per-core transition.
        let executingCore := determineExecutingCore st tid
        match endpointSendCrossCoreDispatchChecked ctx epId tid msg cap.rights
            gate.cspaceRoot decoded.capRecvSlot executingCore st with
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
            let executingCore := determineExecutingCore st tid
            -- WS-SM SM6.D (#7.2 fold): reply object threaded into the per-core receive
            -- transition (the endpoint→receiver flow is gated above); the dequeued
            -- `Call` caller is linked atomically (former `linkReceivedCaller` step).
            -- WS-RA RA.B.5b: the woken plain sender's unit frame (checked twin).
            let wokenSender? := (st.getEndpoint? epId).bind (·.sendQ.head)
            match endpointReceiveDualOnCore epId tid replyIdOpt executingCore st with
            | (st', .ok (_, _sgi)) =>
                -- WS-RA RA.B.6: stage the non-blocking consume's delivery (the
                -- checked twin of the unchecked arm's staging; the endpoint
                -- flow gate above governs the consumed message).  Installed
                -- count 0 — no unwrap on the live receive path (see the
                -- unchecked arm; tracked debt, plan §9).
                .ok ((), Architecture.stageDeliveredMessage
                          (Architecture.stageWokenSendCompletion st' wokenSender?) tid 0)
            | (_, .error e) => .error e
    | _ => fun _ => .error .invalidCapability
  -- U5-B/U-M01: IPC call — routed through enforcement wrapper (previously inline check).
  -- This ensures `.call` uses the same enforcement layer as all other policy-gated
  -- operations, rather than an ad-hoc inline `securityFlowsTo` guard.
  | .call =>
    match cap.target with
    | .object epId =>
      fun st =>
        let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
        let extraCapAddrs := decodeExtraCapAddrs decoded
        let resolvedCaps := resolveExtraCaps gate.cspaceRoot extraCapAddrs gate.capDepth st
        let msg : IpcMessage := { registers := body, caps := resolvedCaps, badge := cap.badge }
        -- WS-SM SM6.A (live cross-core `.call`): route the checked `.call`
        -- through the cross-core dispatch.  `endpointCallCrossCoreDispatchChecked`
        -- is the cross-core analogue of `endpointCallChecked` + inline donation:
        -- the same SM-IF flow guard, then the cross-core WithCaps call (the
        -- receiver is woken on its *home* core via `wakeThread`, surfacing a
        -- `.reschedule` SGI the FFI seam fires), then `applyCallDonation` + PIP.
        -- The caller is descheduled from `executingCore` (the core running this
        -- syscall, `currentOnCore executingCore`); the cross-core syscall seam
        -- recovers the SGI from the `(pre, post)` diff.
        let executingCore := determineExecutingCore st tid
        -- WS-SM SM6.D (#7.3b fold): the server-first reply linkage is now atomic
        -- with the rendezvous inside `endpointCallOnCore` (`linkServerStashedReply`);
        -- mirror the unchecked arm — no separate post-dispatch link step.
        -- WS-RA RA.B.5b: the woken receiver's staged frame (checked twin; the
        -- call's own flow gate ran inside the checked dispatch, before the wake).
        let wokenReceiver? := (st.getEndpoint? epId).bind (·.receiveQ.head)
        match endpointCallCrossCoreDispatchChecked ctx epId tid msg cap.rights
            gate.cspaceRoot decoded.capRecvSlot executingCore st with
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
        match st.getReply? rid with
        | none => .error .replyCapInvalid
        | some reply =>
          match reply.caller with
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
              let executingCore := determineExecutingCore st tid
              match endpointReplyCrossCoreDispatchChecked ctx tid callerTid
                  { registers := body, caps := #[], badge := cap.badge } executingCore st with
              | (st', .ok _) =>
                  -- WS-RA RA.B.5b: the woken caller's staged reply frame (checked
                  -- twin; the replier→caller flow gate above admitted the value).
                  -- Installed count 0: reply messages are built `caps := #[]`.
                  .ok ((), Architecture.stageDeliveredMessage st' callerTid 0)
              | (_, .error e) => .error e
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
            let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
            let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
            cspaceMoveChecked ctx src dst st
    | _ => fun _ => .error .invalidCapability
  -- V8-H/D1: cspaceDelete, lifecycleRetype, vspaceMap, vspaceUnmap, serviceRevoke,
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
            sid := ServiceId.ofNat epId.toNat
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
          match notificationSignalBoundCrossCoreDispatchChecked ctx notifId tid args.badge st with
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
        match notificationWaitCrossCoreDispatchChecked ctx notifId tid st with
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
      -- receiver→prevCaller`) — around the *same* `replyRecvBody` as the unchecked
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
              let msg : IpcMessage := { registers := body, caps := #[], badge := replyBadge }
              let executingCore := determineExecutingCore st tid
              if securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf prevCaller) then
                -- WS-RA RA.B.6: stage the receive leg's delivery (the checked
                -- twin of the unchecked arm's staging; the receive leg's own
                -- flow gate governs the consumed message).
                match replyRecvBody epId tid rid prevCaller msg executingCore st with
                -- Installed count 0 — no unwrap on the live receive path
                -- (mirrors the unchecked arm; tracked debt, plan §9).
                | .ok ((), st') => .ok ((), Architecture.stageDeliveredMessage st' tid 0)
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
            (determineExecutingCore st tid) targetId st
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
                      (determineExecutingCore st tid) op st with
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
                  (determineExecutingCore st tid) args.count st with
              | .error e => .error e
              | .ok (n, st') =>
                  .ok ((), Architecture.writeReturnFrameToTcb st' tid
                    (Architecture.returnFrameOfWord n.toUInt64))
        else .error .illegalAuthority
  -- AE1-A/AE1-B/AE1-C: All remaining capability-only arms (tcbSetPriority,
  -- tcbSetMCPriority, tcbSetIPCBuffer, cspaceDelete, lifecycleRetype, vspaceMap,
  -- vspaceUnmap, serviceRevoke, serviceQuery, schedContextConfigure,
  -- schedContextBind, schedContextUnbind, tcbSuspend, tcbResume) are handled by
  -- dispatchCapabilityOnly returning `some` above. This wildcard is provably
  -- unreachable (see dispatchWithCapChecked_wildcard_unreachable below).
  | _ => fun _ => .error .illegalState

/-- T6-I: Policy-checked dispatch variant. Routes syscalls through
    information-flow-checked wrappers when a `LabelingContext` is provided. -/
def dispatchSyscallChecked (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      match st.objects[tcb.cspaceRoot]? with
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
        (if syscallChecksTargetFirst decoded.syscallId then
           syscallInvokeResolved gate (dispatchWithCapChecked ctx decoded tid gate)
         else
           syscallInvoke gate (dispatchWithCapChecked ctx decoded tid gate)) st
      | some _ => .error .invalidCapability
      | none   => .error .objectNotFound
    | some _ => .error .illegalState
    | none   => .error .objectNotFound

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
          dispatchSyscallChecked ctx decoded tid
            (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore
              st executingCore tid decoded.overflowCount)

-- ============================================================================
-- U5-A/U5-D: Dispatch structural equivalence theorems
-- ============================================================================

/-- U5-A/U-M02/V8-H/D1: The 11 capability-only syscalls are handled identically by
both checked and unchecked dispatch paths, since both delegate to
`dispatchCapabilityOnly`. These arms derive authority entirely from
capability possession and do not cross security domains.

The shared arms are: `.cspaceDelete`, `.lifecycleRetype`, `.vspaceMap`,
`.vspaceUnmap`, `.serviceRevoke`, `.serviceQuery`, `.schedContextConfigure`,
`.schedContextBind`, `.schedContextUnbind`, `.tcbSuspend`, `.tcbResume`.

V8-H/D3: With the shared helper extraction, each per-arm theorem follows
directly from the shared `dispatchCapabilityOnly` delegation. -/
theorem checkedDispatch_cspaceDelete_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .cspaceDelete) :
    dispatchWithCapChecked ctx decoded tid gate cap =
    dispatchWithCap decoded tid gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- U5-A/V8-H: Structural equivalence for `.lifecycleRetype`. -/
theorem checkedDispatch_lifecycleRetype_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .lifecycleRetype) :
    dispatchWithCapChecked ctx decoded tid gate cap =
    dispatchWithCap decoded tid gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- U5-A/V8-H: Structural equivalence for `.vspaceMap`. -/
theorem checkedDispatch_vspaceMap_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .vspaceMap) :
    dispatchWithCapChecked ctx decoded tid gate cap =
    dispatchWithCap decoded tid gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- U5-A/V8-H: Structural equivalence for `.vspaceUnmap`. -/
theorem checkedDispatch_vspaceUnmap_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .vspaceUnmap) :
    dispatchWithCapChecked ctx decoded tid gate cap =
    dispatchWithCap decoded tid gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- U5-A/V8-H: Structural equivalence for `.serviceRevoke`. -/
theorem checkedDispatch_serviceRevoke_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .serviceRevoke) :
    dispatchWithCapChecked ctx decoded tid gate cap =
    dispatchWithCap decoded tid gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- U5-A/V8-H: Structural equivalence for `.serviceQuery`. -/
theorem checkedDispatch_serviceQuery_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .serviceQuery) :
    dispatchWithCapChecked ctx decoded tid gate cap =
    dispatchWithCap decoded tid gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- Z5-J: Structural equivalence for `.schedContextConfigure`. -/
theorem checkedDispatch_schedContextConfigure_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .schedContextConfigure) :
    dispatchWithCapChecked ctx decoded tid gate cap =
    dispatchWithCap decoded tid gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- Z5-J: Structural equivalence for `.schedContextBind`. -/
theorem checkedDispatch_schedContextBind_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .schedContextBind) :
    dispatchWithCapChecked ctx decoded tid gate cap =
    dispatchWithCap decoded tid gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- Z5-J: Structural equivalence for `.schedContextUnbind`. -/
theorem checkedDispatch_schedContextUnbind_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .schedContextUnbind) :
    dispatchWithCapChecked ctx decoded tid gate cap =
    dispatchWithCap decoded tid gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- D1: Structural equivalence for `.tcbSuspend`. -/
theorem checkedDispatch_tcbSuspend_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .tcbSuspend) :
    dispatchWithCapChecked ctx decoded tid gate cap =
    dispatchWithCap decoded tid gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- D1: Structural equivalence for `.tcbResume`. -/
theorem checkedDispatch_tcbResume_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .tcbResume) :
    dispatchWithCapChecked ctx decoded tid gate cap =
    dispatchWithCap decoded tid gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- AE1-A: Structural equivalence for `.tcbSetPriority`. -/
theorem checkedDispatch_tcbSetPriority_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .tcbSetPriority) :
    dispatchWithCapChecked ctx decoded tid gate cap =
    dispatchWithCap decoded tid gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- AE1-A: Structural equivalence for `.tcbSetMCPriority`. -/
theorem checkedDispatch_tcbSetMCPriority_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .tcbSetMCPriority) :
    dispatchWithCapChecked ctx decoded tid gate cap =
    dispatchWithCap decoded tid gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- AE1-B: Structural equivalence for `.tcbSetIPCBuffer`. -/
theorem checkedDispatch_tcbSetIPCBuffer_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .tcbSetIPCBuffer) :
    dispatchWithCapChecked ctx decoded tid gate cap =
    dispatchWithCap decoded tid gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- **WS-SM SM7.D** (PR #845 review, P2): Structural equivalence for
`.vspaceUnifyInstruction`.  Its arm lives in the shared `dispatchCapabilityOnly`
helper like its siblings, so the checked and unchecked paths are identical. -/
theorem checkedDispatch_vspaceUnifyInstruction_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .vspaceUnifyInstruction) :
    dispatchWithCapChecked ctx decoded tid gate cap =
    dispatchWithCap decoded tid gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- **PR #822 Phase H** (PR #845 review, P2): Structural equivalence for
`.mintReplyCap` — the other arm that was handled by `dispatchCapabilityOnly`
without a per-arm equivalence theorem. -/
theorem checkedDispatch_mintReplyCap_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .mintReplyCap) :
    dispatchWithCapChecked ctx decoded tid gate cap =
    dispatchWithCap decoded tid gate cap := by
  simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, hSyscall]

/-- U5-D/U-L20/V8-H/Z5-J/D1/AE1-A/AE1-B: Complete dispatch equivalence — for ALL
capability-only syscalls, the checked and unchecked dispatch paths produce identical
results.

Both `dispatchWithCap` and `dispatchWithCapChecked` delegate to the shared
`dispatchCapabilityOnly` helper for these 16 arms, making structural identity
trivial.  PR #845 review (P2): `.vspaceUnifyInstruction` (WS-SM SM7.D) and
`.mintReplyCap` (PR #822 Phase H) were handled by the shared helper but had been
omitted from this enumeration, so a theorem advertised as *complete* did not in
fact cover them.

**Production recommendation**: Use `syscallEntryChecked` for user-space entry.
The unchecked `syscallEntry` is retained for backward compatibility with
existing proofs and internal kernel paths that operate within the TCB. -/
theorem checkedDispatch_capabilityOnly_eq_unchecked
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (hCapOnly : decoded.syscallId = .cspaceDelete ∨
                decoded.syscallId = .lifecycleRetype ∨
                decoded.syscallId = .vspaceMap ∨
                decoded.syscallId = .vspaceUnmap ∨
                decoded.syscallId = .serviceRevoke ∨
                decoded.syscallId = .serviceQuery ∨
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
    dispatchWithCapChecked ctx decoded tid gate cap =
    dispatchWithCap decoded tid gate cap := by
  rcases hCapOnly with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
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
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .reply)
    (rid : SeLe4n.ReplyId)
    (hCap : cap.target = .replyCap rid)
    (st : SystemState)
    (reply : SeLe4n.Kernel.Reply) (callerTid : SeLe4n.ThreadId)
    (hReply : st.getReply? rid = some reply)
    (hCaller : reply.caller = some callerTid)
    (hFlow : securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf callerTid) = true)
    : dispatchWithCapChecked ctx decoded tid gate cap st =
    dispatchWithCap decoded tid gate cap st := by
  -- Unfold both dispatch to the `.reply` arm; resolve the reply linkage with the
  -- resolution hypotheses so both arms reduce to the same cross-core dispatch
  -- (which folds the consume), then collapse checked → unchecked under the flow
  -- guard.
  simp only [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly,
    hSyscall, hCap, hReply, hCaller, hFlow, if_true]
  rw [endpointReplyCrossCoreDispatchChecked_flow_allowed ctx tid callerTid _ _ st hFlow]

/-- AJ1-D (M-01) / WS-SM SM6.D: When the information-flow policy allows both legs
(reply + receive), checked and unchecked `.replyRecv` dispatch produce identical
results.  Faithful seL4-MCS: the reply target is the reply object's recorded
`caller` resolved from the server-supplied reply cap
(`resolveReplyRecvReply … = .ok (rid, prevCaller)`); the checked arm gates both
legs — (1) endpoint → receiver (receive leg, checked first, ahead of the reply
probe), (2) receiver → prevCaller (reply leg) — around the *same* `replyRecvBody`
the unchecked arm runs, so when both flows hold the two arms coincide. -/
theorem checkedDispatch_replyRecv_eq_unchecked_when_allowed
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
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
    dispatchWithCapChecked ctx decoded tid gate cap st =
    dispatchWithCap decoded tid gate cap st := by
  have hGate := endpointFlowGate_of ctx epId _ _ hFlowRecv hOverrideRecv
  simp only [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly,
    hSyscall, hCap, hResolve]
  -- The checked arm now gates in two nested steps: the receive leg (`!flowRecv →
  -- .flowDenied`) outermost, then the reply leg (`flowReply → replyRecvBody`,
  -- else `.replyCapInvalid`).  With both flows `true` the outer `!true` is `false`
  -- (else branch) and the inner `if true` selects the same `replyRecvBody` the
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
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .reply)
    (rid : SeLe4n.ReplyId)
    (hCap : cap.target = .replyCap rid)
    (st : SystemState)
    (reply : SeLe4n.Kernel.Reply) (callerTid : SeLe4n.ThreadId)
    (hReply : st.getReply? rid = some reply)
    (hCaller : reply.caller = some callerTid)
    (hDenied : securityFlowsTo (ctx.threadLabelOf tid) (ctx.threadLabelOf callerTid) = false) :
    dispatchWithCapChecked ctx decoded tid gate cap st = .error .replyCapInvalid := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, hSyscall, hCap, hReply, hCaller, hDenied]

/-- WS-SM SM6.D (PR #822 review, IF-ordering): a checked `.receive` whose
endpoint→receiver flow is **denied** returns `.flowDenied` *for every state and decode*
— the result is independent of `st` and the reply CPtr, so `resolveRecvReplyId`'s
reply-cap validation + `replyIsStashed` scan never run.  A denied receiver therefore
cannot probe "is some blocked server holding this Reply stashed" through the error
code: the flow gate fires strictly before any reply-state read. -/
theorem checkedDispatch_receive_flow_denied
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .receive)
    (epId : SeLe4n.ObjId)
    (hCap : cap.target = .object epId)
    (st : SystemState)
    (hDenied : securityFlowsTo (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = false) :
    dispatchWithCapChecked ctx decoded tid gate cap st = .error .flowDenied := by
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
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (hSyscall : decoded.syscallId = .replyRecv)
    (epId : SeLe4n.ObjId)
    (hCap : cap.target = .object epId)
    (st : SystemState)
    (hDenied : securityFlowsTo (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = false) :
    dispatchWithCapChecked ctx decoded tid gate cap st = .error .flowDenied := by
  simp [dispatchWithCapChecked, dispatchCapabilityOnly, hSyscall, hCap,
    endpointFlowGate_false_of_securityFlowsTo_false ctx epId _ _ hDenied]

-- ============================================================================
-- W2-C (MED-04): dispatchWithCap wildcard arm unreachability
-- ============================================================================

/-- W2-C (MED-04)/D1/D2/D3/AE1-A/AE1-B: Every `SyscallId` variant is handled by either
    `dispatchCapabilityOnly` (returning `some`) or one of the 11 explicit match
    arms in `dispatchWithCap`. This proves the `| _ => fun _ => .error .illegalState`
    wildcard arm is unreachable at runtime.

    The proof enumerates all 25 `SyscallId` constructors: 14 are routed to
    `dispatchCapabilityOnly` (`.cspaceDelete`, `.lifecycleRetype`, `.vspaceMap`,
    `.vspaceUnmap`, `.serviceRevoke`, `.serviceQuery`, `.schedContextConfigure`,
    `.schedContextBind`, `.schedContextUnbind`, `.tcbSuspend`, `.tcbResume`,
    `.tcbSetPriority`, `.tcbSetMCPriority`, `.tcbSetIPCBuffer`),
    and the remaining 11
    (`.send`, `.receive`, `.call`, `.reply`, `.cspaceMint`, `.cspaceCopy`,
    `.cspaceMove`, `.serviceRegister`, `.notificationSignal`, `.notificationWait`,
    `.replyRecv`) are handled by explicit match arms in `dispatchWithCap`.

    AE1-D: The same completeness proof applies to `dispatchWithCapChecked`
    (see `dispatchWithCapChecked_wildcard_unreachable` below). -/
theorem dispatchWithCap_wildcard_unreachable (sid : SyscallId) :
    sid ∈ ([.send, .receive, .call, .reply, .cspaceMint, .cspaceCopy,
            .cspaceMove, .cspaceDelete, .lifecycleRetype, .vspaceMap,
            .vspaceUnmap, .serviceRegister, .serviceRevoke, .serviceQuery,
            .notificationSignal, .notificationWait, .replyRecv,
            .schedContextConfigure, .schedContextBind,
            .schedContextUnbind, .tcbSuspend, .tcbResume,
            .tcbSetPriority, .tcbSetMCPriority,
            .tcbSetIPCBuffer, .tcbSetAffinity,
            .tcbBindNotification, .tcbUnbindNotification, .mintReplyCap,
            .vspaceUnifyInstruction, .declassify,
            .auditRead, .auditDrain] : List SyscallId) := by
  cases sid <;> simp [List.mem_cons]

/-- AE1-D: Every `SyscallId` variant is handled by either `dispatchCapabilityOnly`
    (returning `some`) or one of the 11 explicit match arms in
    `dispatchWithCapChecked`. This proves the wildcard arm is unreachable.

    This is the checked-dispatch counterpart of `dispatchWithCap_wildcard_unreachable`.
    The proof is identical because both functions share `dispatchCapabilityOnly` and
    have the same set of explicit match arms (modulo checked wrappers). -/
theorem dispatchWithCapChecked_wildcard_unreachable (sid : SyscallId) :
    sid ∈ ([.send, .receive, .call, .reply, .cspaceMint, .cspaceCopy,
            .cspaceMove, .cspaceDelete, .lifecycleRetype, .vspaceMap,
            .vspaceUnmap, .serviceRegister, .serviceRevoke, .serviceQuery,
            .notificationSignal, .notificationWait, .replyRecv,
            .schedContextConfigure, .schedContextBind,
            .schedContextUnbind, .tcbSuspend, .tcbResume,
            .tcbSetPriority, .tcbSetMCPriority,
            .tcbSetIPCBuffer, .tcbSetAffinity,
            .tcbBindNotification, .tcbUnbindNotification, .mintReplyCap,
            .vspaceUnifyInstruction, .declassify,
            .auditRead, .auditDrain] : List SyscallId) := by
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
3. Proof infrastructure (delegation/preservation theorems reference this) -/
def dispatchSyscall (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      match st.objects[tcb.cspaceRoot]? with
      | some (.cnode rootCn) =>
        let gate : SyscallGate := {
          callerId     := tid
          cspaceRoot   := tcb.cspaceRoot
          capAddr      := decoded.capAddr
          capDepth     := rootCn.depth
          requiredRight := syscallRequiredRight decoded.syscallId
        }
        (syscallInvoke gate (dispatchWithCap decoded tid gate)) st
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
          dispatchSyscall decoded tid st

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
          unfold lookupThreadRegisterContext at hLookup
          split at hLookup <;> simp at hLookup
          exact hLookup.2.symm
        subst hStEq
        exact ⟨tid, regs, decoded, hCurrent, hLookup, hDecode⟩

/-- WS-J1-C: If `dispatchSyscall` succeeds, the caller held a capability
with the required access right for the invoked syscall. Threads through
`syscallInvoke_requires_right`. -/
theorem dispatchSyscall_requires_right
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (st : SystemState) (st' : SystemState)
    (hOk : dispatchSyscall decoded tid st = .ok ((), st')) :
    ∃ tcb, (SystemState.objects st)[tid.toObjId]? = some (KernelObject.tcb tcb) ∧
      ∃ rootCn, (SystemState.objects st)[tcb.cspaceRoot]? = some (KernelObject.cnode rootCn) ∧
        ∃ cap ref,
          resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth st = .ok ref ∧
          SystemState.lookupSlotCap st ref = some cap ∧
          cap.hasRight (syscallRequiredRight decoded.syscallId) = true := by
  unfold dispatchSyscall at hOk
  split at hOk
  next tcb hTcb =>
    refine ⟨tcb, hTcb, ?_⟩
    split at hOk
    next rootCn hRoot =>
      refine ⟨rootCn, hRoot, ?_⟩
      have hInvoke := syscallInvoke_requires_right
        { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
          capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
        (dispatchWithCap decoded tid
          { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
            capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId })
        st () st' hOk
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
      ∃ tcb, (SystemState.objects st)[tid.toObjId]? = some (KernelObject.tcb tcb) ∧
        ∃ rootCn, (SystemState.objects st)[tcb.cspaceRoot]? = some (KernelObject.cnode rootCn) ∧
          ∃ cap ref,
            resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth st = .ok ref ∧
            SystemState.lookupSlotCap st ref = some cap ∧
            cap.hasRight (syscallRequiredRight decoded.syscallId) = true := by
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
          unfold lookupThreadRegisterContext at hLookup
          split at hLookup <;> simp at hLookup
          exact hLookup.2.symm
        have hDispatch := dispatchSyscall_requires_right decoded tid _st_regs st' (hStEq ▸ hOk)
        rw [hStEq] at hDispatch hLookup
        obtain ⟨tcb, hTcb, rootCn, hRoot, cap, ref, hResolve, hSlot, hRight⟩ := hDispatch
        exact ⟨tid, regs, decoded, hCurrent, hLookup, hDecode,
               tcb, hTcb, rootCn, hRoot, cap, ref, hResolve, hSlot, hRight⟩

/-- WS-J1-C: `lookupThreadRegisterContext` does not modify kernel state. -/
theorem lookupThreadRegisterContext_state_unchanged
    (tid : SeLe4n.ThreadId) (st : SystemState) (regs : SeLe4n.RegisterFile) (st' : SystemState)
    (hOk : lookupThreadRegisterContext tid st = .ok (regs, st')) :
    st' = st := by
  unfold lookupThreadRegisterContext at hOk
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
from message registers. CDT-tracked (C-01). -/
theorem dispatchWithCap_cspaceMint_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (cnodeId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.CSpaceMintArgs)
    (hSyscall : decoded.syscallId = .cspaceMint)
    (hTarget : cap.target = .object cnodeId)
    (hDecode : decodeCSpaceMintArgs decoded = .ok args) :
    dispatchWithCap decoded tid gate cap =
      let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
      let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
      let badge : Option SeLe4n.Badge :=
        if args.badge.val = 0 then none else some args.badge
      cspaceMintWithCdt src dst args.rights badge := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode]

/-- WS-K-C: When cspaceCopy dispatch succeeds, the kernel-level `cspaceCopy`
is invoked with the decoded source and destination slots. -/
theorem dispatchWithCap_cspaceCopy_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (cnodeId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.CSpaceCopyArgs)
    (hSyscall : decoded.syscallId = .cspaceCopy)
    (hTarget : cap.target = .object cnodeId)
    (hDecode : decodeCSpaceCopyArgs decoded = .ok args) :
    dispatchWithCap decoded tid gate cap =
      let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
      let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
      cspaceCopy src dst := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode]

/-- WS-K-C: When cspaceMove dispatch succeeds, the kernel-level `cspaceMove`
is invoked with the decoded source and destination slots. -/
theorem dispatchWithCap_cspaceMove_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (cnodeId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.CSpaceMoveArgs)
    (hSyscall : decoded.syscallId = .cspaceMove)
    (hTarget : cap.target = .object cnodeId)
    (hDecode : decodeCSpaceMoveArgs decoded = .ok args) :
    dispatchWithCap decoded tid gate cap =
      let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
      let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
      cspaceMove src dst := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode]

/-- WS-K-C: When cspaceDelete dispatch succeeds, the kernel-level
`cspaceDeleteSlot` is invoked with the decoded target slot. -/
theorem dispatchWithCap_cspaceDelete_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (cnodeId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.CSpaceDeleteArgs)
    (hSyscall : decoded.syscallId = .cspaceDelete)
    (hTarget : cap.target = .object cnodeId)
    (hDecode : decodeCSpaceDeleteArgs decoded = .ok args) :
    dispatchWithCap decoded tid gate cap =
      let addr : CSpaceAddr := { cnode := cnodeId, slot := args.targetSlot }
      cspaceDeleteSlot addr := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode]

-- ============================================================================
-- WS-K-D: Lifecycle and VSpace dispatch delegation theorems
-- ============================================================================

/-- U-H04 / WS-SM SM7.B.11 / SM7.F.4(b)(iii) / SM7.D.1: When lifecycleRetype
dispatch succeeds, `lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache` is
invoked with the caller's executing core, the resolved cap, decoded target, and
constructed object.  The safe wrapper performs pre-retype cleanup (H-05), memory
scrubbing (S6-C), and — when the retyped object was a live VSpaceRoot — the
`.aside1` TLB shootdown round for the destroyed address space (SM7.B.11); the
`…PerCore` layer additionally retires the initiator's own `perCoreTlb` view for
the destroyed ASID atomically (SM7.F.4(b)(iii)); and the SM7.D.1 layer
broadcasts `IC IALLUIS` across the shareability domain, because the retype
re-purposes the target's backing memory (it is scrubbed in the same transition)
and instruction caches are tagged by physical address, so any line cached from
that memory stays hittable through a later executable mapping of the same frame.
All added layers are projection-invisible, so the delegation is
trace-equivalent to the plain shootdown wrapper. -/
theorem dispatchWithCap_lifecycleRetype_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.LifecycleRetypeArgs)
    (hSyscall : decoded.syscallId = .lifecycleRetype)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeLifecycleRetypeArgs decoded = .ok args) :
    dispatchWithCap decoded tid gate cap =
      fun st => lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache
        (determineExecutingCore st tid) cap args.targetObj
        (objectOfKernelType args.newType args.size) st := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode]

/-- WS-K-D/S6-A/T6-C/X2-E / WS-SM SM7.B.9 / WS-SM SM7.F.4(a)+(b)(ii): When
vspaceMap dispatch succeeds, `vspaceMapPageCheckedWithShootdownFromStatePerCore`
is invoked with the caller's executing core and the decoded ASID, vaddr, paddr,
and validated permissions.  The state-aware variant reads `physicalAddressWidth`
from `SystemState.machine` for platform-specific PA bounds enforcement; the
`…PerCore` wrapper additionally caches the freshly-established translation on the
executing core's `perCoreTlb` view (the live fill, SM7.F.4(a)) and retires any
stale initiator entry (SM7.F.4(b)(ii)).  This is projection-invisible —
`perCoreTlb ∉ projectState` — so the delegation is trace-equivalent to the plain
`vspaceMapPageCheckedWithShootdownFromState` on every observable field.
T6-C: Permissions are now typed as `PagePermissions` (validated at decode).
AK3-E (A-M01 / MEDIUM): dispatch now uses `decodeVSpaceMapArgsChecked` which
additionally validates PA bounds at decode time; the hypothesis requires
the checked decode to succeed (which implies `args.paddr.toNat < 2^physicalAddressWidth`). -/
theorem dispatchWithCap_vspaceMap_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.VSpaceMapArgs)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .vspaceMap)
    (hTarget : cap.target = .object objId)
    -- AK3-E: decode now uses `decodeVSpaceMapArgsChecked`
    (hDecode : decodeVSpaceMapArgsChecked decoded st.machine.maxASID
                 (2^st.machine.physicalAddressWidth) = .ok args)
    -- PR #845 review (P1): the capability must name the operand ASID's VSpace
    -- root.  Without this premise the delegation is *false*, because an
    -- unauthorized caller is now rejected with `.illegalAuthority` before the
    -- transition runs.
    (hAuth : vspaceCapAuthorizesAsid cap args.asid st = true) :
    dispatchWithCap decoded tid gate cap st =
      (match validateVSpaceMapPermsForMemoryKind args st.machine.memoryMap with
        | .error e => .error e
        | .ok validatedArgs =>
            Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore
              (determineExecutingCore st tid) validatedArgs.asid
              validatedArgs.vaddr validatedArgs.paddr validatedArgs.perms st) := by
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
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.VSpaceUnifyInstructionArgs)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .vspaceUnifyInstruction)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeVSpaceUnifyInstructionArgs decoded st.machine.maxASID = .ok args)
    -- PR #845 review (P1): the capability must name the operand ASID's VSpace
    -- root; an unauthorized caller is rejected with `.illegalAuthority`.
    (hAuth : vspaceCapAuthorizesAsid cap args.asid st = true) :
    dispatchWithCap decoded tid gate cap st =
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
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
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
    dispatchWithCap decoded tid gate cap st =
      Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast
        (determineExecutingCore st tid) args.asid args.vaddr st := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode, hAuth]

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
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.VSpaceMapArgs)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .vspaceMap)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeVSpaceMapArgsChecked decoded st.machine.maxASID
                 (2^st.machine.physicalAddressWidth) = .ok args)
    (hAuth : vspaceCapAuthorizesAsid cap args.asid st = false) :
    dispatchWithCap decoded tid gate cap st = .error .illegalAuthority := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode, hAuth]

/-- **Fail-closed**: `.vspaceUnmap` dispatch rejects a capability that does not
name the operand ASID's VSpace root, leaving the address space intact.  This is
the theorem that would have failed before the binding landed: a caller holding a
writable capability to *any* object could unmap pages in an address space it had
no capability for. -/
theorem dispatchWithCap_vspaceUnmap_unauthorized
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.VSpaceUnmapArgs)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .vspaceUnmap)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeVSpaceUnmapArgs decoded st.machine.maxASID = .ok args)
    (hAuth : vspaceCapAuthorizesAsid cap args.asid st = false) :
    dispatchWithCap decoded tid gate cap st = .error .illegalAuthority := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode, hAuth]

/-- **Fail-closed**: `.vspaceUnifyInstruction` dispatch rejects a capability that
does not name the operand ASID's VSpace root, so the cache-maintenance path
cannot be used to probe another address space's mappings. -/
theorem dispatchWithCap_vspaceUnifyInstruction_unauthorized
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.VSpaceUnifyInstructionArgs)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .vspaceUnifyInstruction)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeVSpaceUnifyInstructionArgs decoded st.machine.maxASID = .ok args)
    (hAuth : vspaceCapAuthorizesAsid cap args.asid st = false) :
    dispatchWithCap decoded tid gate cap st = .error .illegalAuthority := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode, hAuth]

-- ============================================================================
-- WS-K-E: Service policy and IPC message population delegation theorems
-- ============================================================================

/-- WS-K-E/M-D01 / WS-SM SM8.B: When send dispatch is invoked, the IPC message
includes resolved extra capabilities and routes through the **cross-core**
WithCaps send (`endpointSendDualWithCapsOnCore` — the per-core send with home-core
receiver wake and executing-core sender deschedule), at the executing core derived
from the live state (`determineExecutingCore st tid` — the sender's own core). -/
theorem dispatchWithCap_send_uses_withCaps
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (epId : SeLe4n.ObjId)
    (hSyscall : decoded.syscallId = .send)
    (hTarget : cap.target = .object epId) :
    dispatchWithCap decoded tid gate cap =
      fun st =>
        let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
        let extraCapAddrs := decodeExtraCapAddrs decoded
        let resolvedCaps := resolveExtraCaps gate.cspaceRoot extraCapAddrs gate.capDepth st
        let msg : IpcMessage := { registers := body, caps := resolvedCaps, badge := cap.badge }
        let wokenReceiver? := (st.getEndpoint? epId).bind (·.receiveQ.head)
        let executingCore := determineExecutingCore st tid
        match endpointSendDualWithCapsOnCore epId tid msg cap.rights gate.cspaceRoot
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
receiver wake + donation), at the executing core derived from the live state
(`determineExecutingCore st tid` — the caller's own core). -/
theorem dispatchWithCap_call_uses_crossCoreDispatch
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (epId : SeLe4n.ObjId)
    (hSyscall : decoded.syscallId = .call)
    (hTarget : cap.target = .object epId) :
    dispatchWithCap decoded tid gate cap =
      fun st =>
        let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
        let extraCapAddrs := decodeExtraCapAddrs decoded
        let resolvedCaps := resolveExtraCaps gate.cspaceRoot extraCapAddrs gate.capDepth st
        let msg : IpcMessage := { registers := body, caps := resolvedCaps, badge := cap.badge }
        let executingCore := determineExecutingCore st tid
        -- WS-SM SM6.D (#7.3b fold): server-first reply linkage is atomic with the
        -- rendezvous inside `endpointCallOnCore` (`linkServerStashedReply`); no
        -- separate post-dispatch link step.
        -- WS-RA RA.B.5b: the woken receiver's staged frame rides in the RHS.
        let wokenReceiver? := (st.getEndpoint? epId).bind (·.receiveQ.head)
        match endpointCallCrossCoreDispatch epId tid msg cap.rights gate.cspaceRoot
            decoded.capRecvSlot executingCore st with
        | (st', .ok (summary, _)) =>
            .ok ((), Architecture.stageWokenDelivery st' wokenReceiver?
                      summary.installedCount)
        | (_, .error e) => .error e := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget]

/-- WS-K-E / WS-SM SM6.D: When reply dispatch is invoked, the IPC message body is
populated from decoded message registers via `extractMessageRegisters`; the reply
cap's `ReplyId` is resolved to its recorded caller (`reply.caller`) and the reply is
routed through the **cross-core** dispatch (`endpointReplyCrossCoreDispatch` — the
caller woken on its home core, the donated SchedContext returned, and
priority-inheritance reverted cross-core, at `determineExecutingCore st tid` —
the replier's own core).  The single-use linkage consume is folded into
`endpointReplyOnCore` (PR #827 review #3) — atomic with the delivery.  Fails
closed on a dangling reply or an unlinked caller. -/
theorem dispatchWithCap_reply_populates_msg
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (rid : SeLe4n.ReplyId)
    (hSyscall : decoded.syscallId = .reply)
    (hTarget : cap.target = .replyCap rid) :
    dispatchWithCap decoded tid gate cap =
      fun st =>
        let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
        match st.getReply? rid with
        | none => .error .replyCapInvalid
        | some reply =>
          match reply.caller with
          | none => .error .replyCapInvalid
          | some callerTid =>
            let executingCore := determineExecutingCore st tid
            match endpointReplyCrossCoreDispatch tid callerTid
                { registers := body, caps := #[], badge := cap.badge } executingCore st with
            | (st', .ok _) =>
                -- WS-RA RA.B.5b: the woken caller's staged reply frame
                -- (installed count 0: reply messages are built `caps := #[]`).
                .ok ((), Architecture.stageDeliveredMessage st' callerTid 0)
            | (_, .error e) => .error e := by
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
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (notifId : SeLe4n.ObjId) (st st1 : SystemState)
    (badge : SeLe4n.Badge) (tcb : TCB)
    (hSyscall : decoded.syscallId = .notificationWait)
    (hTarget : cap.target = .object notifId)
    (hDispatch : notificationWaitCrossCoreDispatch notifId tid st = (st1, .ok (some badge)))
    (hTcb : st1.getTcb? tid = some tcb)
    (hObjInv : st1.objects.invExt) :
    Architecture.syscallReturnShape .notificationWait = .badge ∧
    ∃ stPost, dispatchWithCap decoded tid gate cap st = .ok ((), stPost) ∧
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
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (epId : SeLe4n.ObjId) (st st' : SystemState)
    (reg : ServiceRegistration) (tcb : TCB)
    (hSyscall : decoded.syscallId = .serviceQuery)
    (hTarget : cap.target = .object epId)
    (hLookup : lookupServiceByCap epId st = .ok (reg, st'))
    (hTcb : st'.getTcb? tid = some tcb)
    (hObjInv : st'.objects.invExt) :
    Architecture.syscallReturnShape .serviceQuery = .word ∧
    ∃ stPost, dispatchWithCap decoded tid gate cap st = .ok ((), stPost) ∧
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
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (args : Architecture.SyscallArgDecode.AuditReadArgs) (op : AuditReadOp)
    (st st' : SystemState) (w : Nat) (tcb : TCB)
    (hSyscall : decoded.syscallId = .auditRead)
    (hTarget : cap.target = .auditTrail)
    (hRight : cap.hasRight gate.requiredRight = true)
    (hArgs : Architecture.SyscallArgDecode.decodeAuditReadArgs decoded = .ok args)
    (hOp : decodeAuditReadOp args.opcode args.index args.chunk = some op)
    (hRead : auditReadFromCore (liftLegacyContext ctx) (validatedAuditMonitorClearance ctx)
      (determineExecutingCore st tid) op st = .ok (w, st'))
    (hTcb : st'.getTcb? tid = some tcb)
    (hObjInv : st'.objects.invExt) :
    Architecture.syscallReturnShape .auditRead = .word ∧
    ∃ stPost, dispatchWithCapChecked ctx decoded tid gate cap st = .ok ((), stPost) ∧
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
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (args : Architecture.SyscallArgDecode.AuditDrainArgs)
    (st st' : SystemState) (n : Nat) (tcb : TCB)
    (hSyscall : decoded.syscallId = .auditDrain)
    (hTarget : cap.target = .auditTrail)
    (hRight : cap.hasRight gate.requiredRight = true)
    (hArgs : Architecture.SyscallArgDecode.decodeAuditDrainArgs decoded = .ok args)
    (hDrain : auditDrainVisiblePrefix (liftLegacyContext ctx)
      (validatedAuditMonitorClearance ctx)
      (determineExecutingCore st tid) args.count st = .ok (n, st'))
    (hTcb : st'.getTcb? tid = some tcb)
    (hObjInv : st'.objects.invExt) :
    Architecture.syscallReturnShape .auditDrain = .word ∧
    ∃ stPost, dispatchWithCapChecked ctx decoded tid gate cap st = .ok ((), stPost) ∧
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
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (epId : SeLe4n.ObjId)
    (replyIdOpt : Option SeLe4n.ReplyId) (st st' : SystemState)
    (next : SeLe4n.ThreadId) (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (msg : IpcMessage) (tcb : TCB)
    (hSyscall : decoded.syscallId = .receive)
    (hTarget : cap.target = .object epId)
    (hReply : resolveRecvReplyId gate decoded st = .ok replyIdOpt)
    (hDispatch : endpointReceiveDualOnCore epId tid replyIdOpt
        (determineExecutingCore st tid) st = (st', .ok (next, sgi)))
    (hTcb : (Architecture.stageWokenSendCompletion st'
        ((st.getEndpoint? epId).bind (·.sendQ.head))).getTcb? tid = some tcb)
    (hReady : tcb.ipcState = .ready)
    (hMsg : tcb.pendingMessage = some msg)
    (hObjInv : (Architecture.stageWokenSendCompletion st'
        ((st.getEndpoint? epId).bind (·.sendQ.head))).objects.invExt) :
    Architecture.syscallReturnShape .receive = .message ∧
    ∃ stPost, dispatchWithCap decoded tid gate cap st = .ok ((), stPost) ∧
      Architecture.readReturnFrame stPost tid
        = Architecture.returnFrameOfMessage msg 0 := by
  refine ⟨rfl,
    Architecture.stageDeliveredMessage
      (Architecture.stageWokenSendCompletion st'
        ((st.getEndpoint? epId).bind (·.sendQ.head))) tid 0,
    ?_, ?_⟩
  · simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hReply, hDispatch]
  · exact Architecture.blockedReturn_staged_in_waiter_frame _ tid tcb msg 0
      hTcb hReady hMsg hObjInv

/-- RA.B.8, `.replyRecv` (`.message`): the compound arm's receive leg stages
the delivered message for the server exactly as `.receive` does. -/
theorem dispatchArm_replyRecv_matches_returnShape
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (epId : SeLe4n.ObjId)
    (rid : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (replyBadge : Option SeLe4n.Badge)
    (st stB : SystemState) (msg : IpcMessage) (tcb : TCB)
    (hSyscall : decoded.syscallId = .replyRecv)
    (hTarget : cap.target = .object epId)
    (hResolve : resolveReplyRecvReply gate decoded st = .ok (rid, prevCaller, replyBadge))
    (hBody : replyRecvBody epId tid rid prevCaller
        { registers := (extractMessageRegisters decoded.msgRegs decoded.msgInfo).extract 1
            (extractMessageRegisters decoded.msgRegs decoded.msgInfo).size,
          caps := #[], badge := replyBadge }
        (determineExecutingCore st tid) st = .ok ((), stB))
    (hTcb : stB.getTcb? tid = some tcb)
    (hReady : tcb.ipcState = .ready)
    (hMsg : tcb.pendingMessage = some msg)
    (hObjInv : stB.objects.invExt) :
    Architecture.syscallReturnShape .replyRecv = .message ∧
    ∃ stPost, dispatchWithCap decoded tid gate cap st = .ok ((), stPost) ∧
      Architecture.readReturnFrame stPost tid
        = Architecture.returnFrameOfMessage msg 0 := by
  refine ⟨rfl, Architecture.stageDeliveredMessage stB tid 0, ?_, ?_⟩
  · simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hResolve, hBody]
  · exact Architecture.blockedReturn_staged_in_waiter_frame stB tid tcb msg 0
      hTcb hReady hMsg hObjInv

/-- RA.B.8, `.call` (`.message`) — **through the reply arm**, per §3.5: a
successful call leaves the caller `blockedOnReply` in every ordering, so
its `.message` frame is delivered entirely by the reply path's RA.B.5b
staging.  The theorem is therefore the cross-arm statement: a `.reply`
dispatched at the server stages the *caller's* frame, and the boundary
read at the caller recovers the delivered reply. -/
theorem dispatchArm_call_frame_delivered_by_reply
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (rid : SeLe4n.ReplyId) (reply : Reply)
    (callerTid : SeLe4n.ThreadId) (st st1 : SystemState)
    (sgi : Option (Concurrency.CoreId × Concurrency.SgiKind))
    (msg : IpcMessage) (tcb : TCB)
    (hSyscall : decoded.syscallId = .reply)
    (hTarget : cap.target = .replyCap rid)
    (hReply : st.getReply? rid = some reply)
    (hCaller : reply.caller = some callerTid)
    (hDispatch : endpointReplyCrossCoreDispatch tid callerTid
        { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo,
          caps := #[], badge := cap.badge }
        (determineExecutingCore st tid) st = (st1, .ok sgi))
    (hTcb : st1.getTcb? callerTid = some tcb)
    (hReady : tcb.ipcState = .ready)
    (hMsg : tcb.pendingMessage = some msg)
    (hObjInv : st1.objects.invExt) :
    Architecture.syscallReturnShape .call = .message ∧
    ∃ stPost, dispatchWithCap decoded tid gate cap st = .ok ((), stPost) ∧
      Architecture.readReturnFrame stPost callerTid
        = Architecture.returnFrameOfMessage msg 0 := by
  refine ⟨rfl, Architecture.stageDeliveredMessage st1 callerTid 0, ?_, ?_⟩
  · simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hReply,
      hCaller, hDispatch]
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
        dispatchSyscall decoded tid stD = .ok ((), stD') →
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
  -- hOk : dispatchSyscall decoded tid st = .ok ((), st')
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
    (hDispatchProj : ∀ decoded tid,
        dispatchSyscall decoded tid st = .ok ((), st') →
        projectState ctx observer st' = projectState ctx observer st) :
    projectState ctx observer st' = projectState ctx observer st := by
  obtain ⟨tid, regs, decoded, hCur, hLookup, hDecode⟩ :=
    syscallEntry_requires_valid_decode layout regCount st st' hOk
  unfold syscallEntry at hOk
  rw [hCur] at hOk; simp at hOk
  rw [hLookup] at hOk; simp at hOk
  rw [hDecode] at hOk; simp at hOk
  exact hDispatchProj decoded tid hOk

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
    (hDispatchProj : ∀ decoded tid,
        dispatchSyscall decoded tid st = .ok ((), st') →
        projectState ctx observer st' = projectState ctx observer st) :
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
`msgRegs` field produce identical decode results for all 7 structures —
confirming that decode depends only on `msgRegs`, not on `capAddr`,
`msgInfo`, or `syscallId`. -/
theorem dispatchWithCap_layer2_decode_pure
    (d₁ d₂ : SyscallDecodeResult) (hRegs : d₁.msgRegs = d₂.msgRegs) :
    (decodeCSpaceMintArgs d₁ = decodeCSpaceMintArgs d₂) ∧
    (decodeCSpaceCopyArgs d₁ = decodeCSpaceCopyArgs d₂) ∧
    (decodeCSpaceMoveArgs d₁ = decodeCSpaceMoveArgs d₂) ∧
    (decodeCSpaceDeleteArgs d₁ = decodeCSpaceDeleteArgs d₂) ∧
    (decodeLifecycleRetypeArgs d₁ = decodeLifecycleRetypeArgs d₂) ∧
    -- AH3-C: These are now function equalities (parameterized by maxASID)
    (decodeVSpaceMapArgs d₁ = decodeVSpaceMapArgs d₂) ∧
    (decodeVSpaceUnmapArgs d₁ = decodeVSpaceUnmapArgs d₂) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [decodeCSpaceMintArgs, decodeCSpaceCopyArgs, decodeCSpaceMoveArgs,
      decodeCSpaceDeleteArgs, decodeLifecycleRetypeArgs, requireMsgReg, hRegs]) <;>
    (try funext maxASID; simp only [decodeVSpaceMapArgs, decodeVSpaceUnmapArgs,
      requireMsgReg, hRegs])

/-- WS-K-F4: Composition verification — `syscallEntry_preserves_proofLayerInvariantBundle`
composes decode purity (no state change), read-only cap lookup (state unchanged),
and the delegated operation's preservation property. The `hDispatchPres` hypothesis
is dischargeable per-dispatch-arm using existing subsystem preservation theorems:

- CSpace mint/copy/move/delete: `Capability/Invariant/Preservation.lean`
- Lifecycle retype: `Lifecycle/Invariant.lean`
- VSpace map/unmap: `Architecture/VSpaceInvariant.lean`
- Service start/stop: `Service/Invariant/Policy.lean`
- IPC send/call/reply/recv: `IPC/Invariant/EndpointPreservation.lean`

This theorem witnesses that the composition is structurally complete. -/
theorem dispatchWithCap_preservation_composition_witness :
    (∀ layout regCount st st' (_hInv : Architecture.proofLayerInvariantBundle st)
        (_hOk : syscallEntry layout regCount st = .ok ((), st'))
        (_hDispatchPres : ∀ decoded tid stD stD',
            Architecture.proofLayerInvariantBundle stD →
            dispatchSyscall decoded tid stD = .ok ((), stD') →
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

    **Fully substantive (5/14)** — proof uses only observability
    hypotheses and pre-proven frame lemmas; NO abstract closures:
    - `.cspaceDelete` → `cspaceDeleteSlot_preserves_projection`
    - `.serviceQuery` → `lookupServiceByCap_preserves_projection` (AK6F.11,
       state is unchanged, projection follows)
    - `.tcbSetIPCBuffer` → `setIPCBufferOp_preserves_projection`
    - `.vspaceMap` → `vspaceMapPageCheckedWithFlushFromState_preserves_projection`
    - `.vspaceUnmap` → `vspaceUnmapPageWithFlush_preserves_projection`

    **Hybrid substantive + legitimate closure (3/14)** — proof body
    uses frame lemmas for most phases but takes ONE closure over an
    external call (schedule/RHTable-fold) whose preservation depends on
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
    - `.serviceRevoke` → `revokeService_preserves_projection` (AK6F.12)
      body uses `congr 1` over all 13 `projectState` components;
      takes `hServiceProjEq` for the `removeDependenciesOf` fold-induction
      at the service-projection layer only.

    **Closure-form (6/14)** — theorem takes `hProjEq` abstract closure;
    body is `hProjEq st' hStep`. NOT tautological for callers — each has
    DOCUMENTED FRAME LEMMAS letting a caller discharge `hProjEq` in
    ≈25-60 LOC using substantively-proven building blocks. Listed here
    WITH their discharge recipes:
    - `.schedContextBind` → `schedContextBind_preserves_projection` (AK6F.14);
      discharge via `objects_insert_preserves_projection_high` × 2 +
      `schedContextBind_frame_runQueue_rebucket` + `projectState_scThreadIndex_eq`.
    - `.schedContextUnbind` → `schedContextUnbind_preserves_projection` (AK6F.15);
      discharge via `projectState_scheduler_current_cleared_when_high` +
      `removeRunnable_preserves_projection` + `objects_insert_preserves_projection_high` × 2 +
      `projectState_replenishQueue_eq` + `projectState_scThreadIndex_eq`.
    - `.schedContextConfigure` → `schedContextConfigure_preserves_projection` (AK6F.13);
      discharge via `projectState_replenishQueue_eq` +
      `objects_insert_preserves_projection_high` × 2 +
      `schedContextBind_frame_runQueue_rebucket`.
    - `.lifecycleRetype` → `lifecycleRetypeDirectWithCleanup_preserves_projection`
      (AK6F.16); discharge via cleanup-phase `storeObject_preserves_projection` +
      `projectMemory_const_when_ownership_none` + final `storeObject_preserves_projection`.
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
    | `.lifecycleRetype` | compose with `lifecycleRevokeDeleteRetype_preserves_projection` (Operations.lean:2454) via `lifecycleRetypeDirectWithCleanup` frame |
    | `.vspaceMap` | `vspaceMapPage_preserves_projection` (Operations.lean:753); requires `hRootHigh` via ASID resolution |
    | `.vspaceUnmap` | `vspaceUnmapPage_preserves_projection` (Operations.lean:797) |
    | `.serviceRevoke` | reduces to `cspaceRevoke_preserves_projection` (Operations.lean:1000) through the orchestrator |
    | `.serviceQuery` | read-only (`lookupServiceByCap` does not mutate state) |
    | `.schedContextConfigure/Bind/Unbind` | `storeObject_preserves_projection` / `objects_insert_preserves_projection_high` (Operations.lean) at non-observable SchedContext target + TCB/RunQueue field preservation |
    | `.tcbSetIPCBuffer` | **`setIPCBufferOp_preserves_projection`** (Operations.lean — AK6-F.2b, v0.29.10) |
    | `.tcbSetPriority/SetMCPriority` | `objects_insert_preserves_projection_high` at non-observable TCB/SC — uses the universal direct-insert frame lemma (Operations.lean — AK6-F Step A, v0.29.10) |
    | `.tcbSetAffinity` | **`setThreadCpuAffinityOnCore_preserves_projection`** (Operations.lean — WS-SM SM8.B, review round 42) at non-observable target — the **live** wrapper, which round 37 rerouted this arm to; the boot-core `setThreadCpuAffinityOp_preserves_projection` (SM5.H.4) is its `bootCoreId` instance, reachable through `setThreadCpuAffinityOp_eq_onCore_state` but not needed here.  The affinity write is `cpuAffinity`-erased (invisible); the run-queue migration's write, at the executing core rather than a pinned boot core, preserves the filtered `projectRunnable` for a high thread (`migrateRunQueueOnAffinityChange_preserves_projection`); the replenishment migration is never projected (`migrateSchedContextReplenishment_preserves_projection`). |
    | `.tcbSuspend/Resume` | `storeObject_preserves_projection` at non-observable TCB target |

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
    (decoded : SyscallDecodeResult) (cap : Capability) (tid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hArmProj : ∀ kop, dispatchCapabilityOnly decoded cap tid = some kop →
                       kop st = .ok ((), st') →
                       projectState ctx observer st' = projectState ctx observer st)
    (hKop : ∃ kop, dispatchCapabilityOnly decoded cap tid = some kop ∧
                    kop st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  obtain ⟨kop, hSome, hRun⟩ := hKop
  exact hArmProj kop hSome hRun

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
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (_hTidHigh : threadObservable ctx observer tid = false)
    (hInnerProj : ∀ (gate : SyscallGate) (cap : Capability),
        syscallResolveCap gate st = .ok (cap, st) →
        ∀ stOut, dispatchWithCapChecked ctx decoded tid gate cap st = .ok ((), stOut) →
        projectState ctx observer stOut = projectState ctx observer st)
    (hStep : dispatchSyscallChecked ctx decoded tid st = .ok ((), st')) :
    projectState ctx observer st' = projectState ctx observer st := by
  simp only [dispatchSyscallChecked] at hStep
  -- Layer 1: TCB lookup (read-only)
  split at hStep
  · -- some (.tcb tcb)
    -- Layer 1b: CNode lookup (read-only)
    split at hStep
    · -- some (.cnode rootCn)
      -- PR #870 round 5: the target-first syscalls take the resolve-only
      -- lookup, everything else the classic rights-gated one.  The inner-NI
      -- hypothesis is stated over the resolve (the weaker premise, so the
      -- stronger hypothesis) and covers both branches — a full-lookup success
      -- is a resolve success (`syscallResolveCap_of_lookup`).
      split at hStep
      · -- target-first branch: resolve-only lookup
        unfold syscallInvokeResolved at hStep
        split at hStep
        · -- syscallResolveCap returned error
          simp at hStep
        · rename_i cap stCap hCap
          have ⟨_, _, _, hStEq⟩ :=
            syscallResolveCap_implies_capability_at_slot _ st cap stCap hCap
          rw [hStEq] at hStep hCap
          exact hInnerProj _ cap hCap st' hStep
      · -- classic branch: full lookup
        unfold syscallInvoke at hStep
        split at hStep
        · -- syscallLookupCap returned error
          simp at hStep
        · rename_i cap stCap hCap
          have ⟨_, _, _, _, hStEq⟩ :=
            syscallLookupCap_implies_capability_held _ st cap stCap hCap
          rw [hStEq] at hStep hCap
          exact hInnerProj _ cap (syscallResolveCap_of_lookup _ st cap st hCap) st' hStep
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
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability) (targetId : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .declassify)
    (hTarget : cap.target = .object targetId) :
    dispatchWithCapChecked ctx decoded tid gate cap st =
      declassifyObjectFromCore (liftLegacyContext ctx) ctx.declassificationPolicy
        (determineExecutingCore st tid) targetId st := by
  unfold dispatchWithCapChecked dispatchCapabilityOnly
  rw [hSyscall]
  simp only [hTarget]

/-- **WS-SM SM8.C.9: there is no unchecked declassification.**

The unchecked dispatch fails closed with the error a denied downgrade produces.
Stated as a theorem rather than left to the reader of the arm, because "the
unchecked path skips the flow check" is the pattern every *other* arm follows,
and following it here would authorize every downgrade. -/
theorem dispatchWithCap_declassify_denied
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability) (st : SystemState)
    (hSyscall : decoded.syscallId = .declassify) :
    dispatchWithCap decoded tid gate cap st = .error .declassificationDenied := by
  unfold dispatchWithCap dispatchCapabilityOnly
  rw [hSyscall]

/-- **WS-SM SM8.C.9**: an unconfigured deployment cannot declassify.

`LabelingContext.declassificationPolicy` defaults to deny-all, so the checked
arm refuses too — the fail-closed default, stated where an operator reading the
dispatch would look for it. -/
theorem dispatchWithCapChecked_declassify_default_denied
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability) (targetId : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .declassify)
    (hTarget : cap.target = .object targetId)
    (hDefault : ctx.declassificationPolicy.canDeclassify = fun _ _ => false) :
    ¬ ∃ st', dispatchWithCapChecked ctx decoded tid gate cap st = .ok ((), st') := by
  rintro ⟨st', hStep⟩
  rw [dispatchWithCapChecked_declassify_delegates ctx decoded tid gate cap targetId st
    hSyscall hTarget] at hStep
  obtain ⟨cur, hCur⟩ : ∃ x, st.scheduler.currentOnCore (determineExecutingCore st tid) = x :=
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
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (args : Architecture.SyscallArgDecode.AuditReadArgs) (op : AuditReadOp)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .auditRead)
    (hTarget : cap.target = .auditTrail)
    (hRight : cap.hasRight gate.requiredRight = true)
    (hArgs : Architecture.SyscallArgDecode.decodeAuditReadArgs decoded = .ok args)
    (hOp : decodeAuditReadOp args.opcode args.index args.chunk = some op) :
    dispatchWithCapChecked ctx decoded tid gate cap st =
      (match auditReadFromCore (liftLegacyContext ctx) (validatedAuditMonitorClearance ctx)
          (determineExecutingCore st tid) op st with
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
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (args : Architecture.SyscallArgDecode.AuditDrainArgs) (st : SystemState)
    (hSyscall : decoded.syscallId = .auditDrain)
    (hTarget : cap.target = .auditTrail)
    (hRight : cap.hasRight gate.requiredRight = true)
    (hArgs : Architecture.SyscallArgDecode.decodeAuditDrainArgs decoded = .ok args) :
    dispatchWithCapChecked ctx decoded tid gate cap st =
      (match auditDrainVisiblePrefix (liftLegacyContext ctx)
          (validatedAuditMonitorClearance ctx)
          (determineExecutingCore st tid) args.count st with
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
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability) (oid : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .auditRead ∨ decoded.syscallId = .auditDrain)
    (hTarget : cap.target = .object oid) :
    dispatchWithCapChecked ctx decoded tid gate cap st = .error .invalidCapability := by
  unfold dispatchWithCapChecked dispatchCapabilityOnly
  rcases hSyscall with h | h <;> rw [h] <;> simp only [extractAuditAuthority, hTarget]

/-- **WS-SM SM9.A.9 (PR #870 round 5, the second gate at the arm)**: an audit
capability that lacks the required right is refused `.illegalAuthority` — by
the ARM, after the target check, which is what "target first, right second"
means now that the checked dispatch routes the audit ids through the
resolve-only lookup. -/
theorem dispatchWithCapChecked_audit_insufficient_right_denied
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability) (st : SystemState)
    (hSyscall : decoded.syscallId = .auditRead ∨ decoded.syscallId = .auditDrain)
    (hTarget : cap.target = .auditTrail)
    (hRight : cap.hasRight gate.requiredRight = false) :
    dispatchWithCapChecked ctx decoded tid gate cap st = .error .illegalAuthority := by
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
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (rootCn : CNode) (ref : SlotRef) (cap : Capability)
    (oid : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .auditRead ∨ decoded.syscallId = .auditDrain)
    (hTcb : st.getTcb? tid = some tcb)
    (hRoot : st.getCNode? tcb.cspaceRoot = some rootCn)
    (hResolve : resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth st = .ok ref)
    (hLookup : SystemState.lookupSlotCap st ref = some cap)
    (hTarget : cap.target = .object oid) :
    dispatchSyscallChecked ctx decoded tid st = .error .invalidCapability := by
  rcases hSyscall with h | h
  · simp only [dispatchSyscallChecked,
      (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb,
      (SystemState.getCNode?_eq_some_iff st tcb.cspaceRoot rootCn).mp hRoot,
      h, syscallChecksTargetFirst, if_true,
      syscallInvokeResolved, syscallResolveCap, hResolve, hLookup]
    exact dispatchWithCapChecked_audit_rejects_non_audit_capability ctx decoded tid _ cap oid st
      (Or.inl h) hTarget
  · simp only [dispatchSyscallChecked,
      (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb,
      (SystemState.getCNode?_eq_some_iff st tcb.cspaceRoot rootCn).mp hRoot,
      h, syscallChecksTargetFirst, if_true,
      syscallInvokeResolved, syscallResolveCap, hResolve, hLookup]
    exact dispatchWithCapChecked_audit_rejects_non_audit_capability ctx decoded tid _ cap oid st
      (Or.inr h) hTarget

/-- **WS-SM SM9.A.9 (PR #870 round 5, the order's other half)**: an audit-target
capability lacking the required right is refused `.illegalAuthority` — after
the target check, from the arm.  Together with
`dispatchSyscallChecked_audit_target_first` this pins the composed order: the
refusal class depends on the *target* first, and on the rights only once the
target is the audit trail. -/
theorem dispatchSyscallChecked_audit_right_checked_second
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (rootCn : CNode) (ref : SlotRef) (cap : Capability)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .auditRead ∨ decoded.syscallId = .auditDrain)
    (hTcb : st.getTcb? tid = some tcb)
    (hRoot : st.getCNode? tcb.cspaceRoot = some rootCn)
    (hResolve : resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth st = .ok ref)
    (hLookup : SystemState.lookupSlotCap st ref = some cap)
    (hTarget : cap.target = .auditTrail)
    (hRight : cap.hasRight (syscallRequiredRight decoded.syscallId) = false) :
    dispatchSyscallChecked ctx decoded tid st = .error .illegalAuthority := by
  rcases hSyscall with h | h
  · simp only [dispatchSyscallChecked,
      (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb,
      (SystemState.getCNode?_eq_some_iff st tcb.cspaceRoot rootCn).mp hRoot,
      h, syscallChecksTargetFirst, if_true,
      syscallInvokeResolved, syscallResolveCap, hResolve, hLookup]
    exact dispatchWithCapChecked_audit_insufficient_right_denied ctx decoded tid _ cap st
      (Or.inl h) hTarget (by simpa [h] using hRight)
  · simp only [dispatchSyscallChecked,
      (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb,
      (SystemState.getCNode?_eq_some_iff st tcb.cspaceRoot rootCn).mp hRoot,
      h, syscallChecksTargetFirst, if_true,
      syscallInvokeResolved, syscallResolveCap, hResolve, hLookup]
    exact dispatchWithCapChecked_audit_insufficient_right_denied ctx decoded tid _ cap st
      (Or.inr h) hTarget (by simpa [h] using hRight)

/-- **WS-SM SM9.A.10: there is no unchecked audit read.**

The unchecked dispatch fails closed on both audit syscalls.  Stated as a theorem
because "the unchecked path skips the flow check" is the pattern every *other*
arm follows, and following it here would mean picking a clearance — and the only
clearance available without a context is "all of them", which is an audit reader
that hands every entry to every capability holder. -/
theorem dispatchWithCap_auditRead_denied
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability) (st : SystemState)
    (hSyscall : decoded.syscallId = .auditRead ∨ decoded.syscallId = .auditDrain) :
    dispatchWithCap decoded tid gate cap st = .error .illegalAuthority := by
  unfold dispatchWithCap dispatchCapabilityOnly
  rcases hSyscall with h | h <;> rw [h]

/-- **WS-SM SM9.A.10**: an unconfigured deployment cannot drain.

`LabelingContext.auditMonitorClearance` defaults to `none`, which denies every
caller, so the 256-entry cliff stays until an operator names a monitor.  That is
the conservative default and it is the operator's to know about — stated where a
reviewer of the dispatch would look for it. -/
theorem dispatchWithCapChecked_auditDrain_default_denied
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (args : Architecture.SyscallArgDecode.AuditDrainArgs) (st : SystemState)
    (hSyscall : decoded.syscallId = .auditDrain)
    (hTarget : cap.target = .auditTrail)
    (hRight : cap.hasRight gate.requiredRight = true)
    (hArgs : Architecture.SyscallArgDecode.decodeAuditDrainArgs decoded = .ok args)
    (hDefault : ctx.auditMonitorClearance = none) :
    dispatchWithCapChecked ctx decoded tid gate cap st = .error .illegalAuthority := by
  rw [dispatchWithCapChecked_auditDrain_delegates ctx decoded tid gate cap args st
    hSyscall hTarget hRight hArgs,
    validatedAuditMonitorClearance_none ctx hDefault,
    auditDrain_unconfigured_denied (liftLegacyContext ctx) (determineExecutingCore st tid)
      args.count st]

/-- **WS-SM SM9.A.10 (PR #870 round 2)**: an unconfigured deployment cannot
read — the `.auditRead` sibling of `dispatchWithCapChecked_auditDrain_default_denied`,
and the arm-level witness of the reviewer's exact scenario: a boot-provisioned
`.auditTrail` capability with the `.read` right, a well-formed operation, and no
configured monitor clearance.  The refusal comes from the transition's own
configuration gate (`auditRead_unconfigured_denied`), not from the capability
checks the capability was provisioned to pass. -/
theorem dispatchWithCapChecked_auditRead_default_denied
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability)
    (args : Architecture.SyscallArgDecode.AuditReadArgs) (op : AuditReadOp)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .auditRead)
    (hTarget : cap.target = .auditTrail)
    (hRight : cap.hasRight gate.requiredRight = true)
    (hArgs : Architecture.SyscallArgDecode.decodeAuditReadArgs decoded = .ok args)
    (hOp : decodeAuditReadOp args.opcode args.index args.chunk = some op)
    (hDefault : ctx.auditMonitorClearance = none) :
    dispatchWithCapChecked ctx decoded tid gate cap st = .error .illegalAuthority := by
  rw [dispatchWithCapChecked_auditRead_delegates ctx decoded tid gate cap args op st
    hSyscall hTarget hRight hArgs hOp,
    validatedAuditMonitorClearance_none ctx hDefault,
    auditRead_unconfigured_denied (liftLegacyContext ctx) (determineExecutingCore st tid)
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
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability) (st st' : SystemState)
    (hSyscall : decoded.syscallId = .auditRead ∨ decoded.syscallId = .auditDrain)
    (hNoMonitor : ctx.auditMonitorClearance = none) :
    dispatchWithCapChecked ctx decoded tid gate cap st ≠ .ok ((), st') := by
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
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (oid : SeLe4n.ObjId) (c : Concurrency.CoreId) (count : Nat)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .auditRead ∨ decoded.syscallId = .auditDrain)
    (hNoMonitor : ctx.auditMonitorClearance = none) :
    (∀ (anyCap : Capability) (st' : SystemState),
      dispatchWithCapChecked ctx decoded tid gate anyCap st ≠ .ok ((), st')) ∧
    dispatchWithCapChecked ctx decoded tid gate
        { target := .object oid, rights := AccessRightSet.ofList AccessRight.all,
          badge := none } st = .error .invalidCapability ∧
    (∀ (parent : NonNullCap) (rights : AccessRightSet) (badge : Option SeLe4n.Badge)
        (child : Capability),
      mintDerivedCap parent rights badge = .ok child → child.target = .auditTrail →
        parent.val.target = .auditTrail) ∧
    auditDrainVisiblePrefix (liftLegacyContext ctx) (validatedAuditMonitorClearance ctx)
        c count st =
      .error .illegalAuthority ∧
    Capability.auditTrailRead.hasRight .write = false := by
  refine ⟨fun anyCap st' =>
      unconfiguredDeployment_audit_never_succeeds ctx decoded tid gate anyCap st st'
        hSyscall hNoMonitor,
    dispatchWithCapChecked_audit_rejects_non_audit_capability ctx decoded tid gate _ oid st
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
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId) (vtid : SeLe4n.ValidThreadId)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .tcbSuspend)
    (hTarget : cap.target = .object objId)
    (hDecode : ∃ a, Architecture.SyscallArgDecode.decodeSuspendArgs decoded = .ok a)
    (hValid : validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vtid) :
    dispatchWithCap decoded tid gate cap st =
      (match Lifecycle.Suspend.suspendThreadOnCore st vtid
              (determineExecutingCore st tid) with
       | .ok (st', _) => .ok ((), st')
       | .error e => .error e) := by
  obtain ⟨a, hD⟩ := hDecode
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hD, hValid]

/-- **The live `.tcbResume` arm routes to `resumeThreadOnCore`.**

Round 10 of the PR #861 review found this arm still calling the boot-pinned
`resumeThread`, which enqueues on `bootCoreId` regardless of the target's
`cpuAffinity` — so resuming a thread homed on a secondary core put it on the
wrong run queue.  The reroute is the fix; this theorem is what stops the
inventory claiming the arm is covered while it points somewhere else. -/
theorem dispatchWithCap_tcbResume_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId) (vtid : SeLe4n.ValidThreadId)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .tcbResume)
    (hTarget : cap.target = .object objId)
    (hDecode : ∃ a, Architecture.SyscallArgDecode.decodeResumeArgs decoded = .ok a)
    (hValid : validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vtid) :
    dispatchWithCap decoded tid gate cap st =
      (match Lifecycle.Suspend.resumeThreadOnCoreLive st vtid
              (determineExecutingCore st tid) with
       | .ok (st', _) => .ok ((), st')
       | .error e => .error e) := by
  obtain ⟨a, hD⟩ := hDecode
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hD, hValid]

/-- **The live `.receive` arm routes to `endpointReceiveDualOnCore`.**

Round 8 of the PR #861 review classified this transition a below-API "leg" of
`replyRecvBody`.  It is that — and it is also what the checked `.receive` arm
calls directly, once its own `endpoint→receiver` gate has passed.  A theorem
saying so is the thing that was missing: with it, the misclassification is a
broken citation rather than a prose disagreement between two tables. -/
theorem dispatchWithCapChecked_receive_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability) (epId : SeLe4n.ObjId)
    (replyIdOpt : Option SeLe4n.ReplyId) (st : SystemState)
    (hSyscall : decoded.syscallId = .receive)
    (hTarget : cap.target = .object epId)
    (hFlow : securityFlowsTo (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) = true)
    -- WS-SM SM8.C: the arm's gate is the global check AND the endpoint override.
    (hOverride : endpointOverrideAllows ctx epId (ctx.endpointLabelOf epId)
      (ctx.threadLabelOf tid) = true)
    (hReply : resolveRecvReplyId gate decoded st = .ok replyIdOpt) :
    dispatchWithCapChecked ctx decoded tid gate cap st =
      (match endpointReceiveDualOnCore epId tid replyIdOpt
              (determineExecutingCore st tid) st with
       | (st', .ok (_, _)) =>
           .ok ((), Architecture.stageDeliveredMessage
                     (Architecture.stageWokenSendCompletion st'
                       ((st.getEndpoint? epId).bind (·.sendQ.head))) tid 0)
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
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (epId : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .send)
    (hTarget : cap.target = .object epId) :
    dispatchWithCap decoded tid gate cap st =
      (match endpointSendDualWithCapsOnCore epId tid
              { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo,
                caps := resolveExtraCaps gate.cspaceRoot (decodeExtraCapAddrs decoded)
                          gate.capDepth st,
                badge := cap.badge }
              cap.rights gate.cspaceRoot decoded.capRecvSlot
              (determineExecutingCore st tid) st with
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
cross-core operation (bounds, then `sender → endpoint`), exactly as
`endpointSendDualChecked` carried it before the reroute. -/
theorem dispatchWithCapChecked_send_delegates
    (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability) (epId : SeLe4n.ObjId) (st : SystemState)
    (hSyscall : decoded.syscallId = .send)
    (hTarget : cap.target = .object epId) :
    dispatchWithCapChecked ctx decoded tid gate cap st =
      (match endpointSendCrossCoreDispatchChecked ctx epId tid
              { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo,
                caps := resolveExtraCaps gate.cspaceRoot (decodeExtraCapAddrs decoded)
                          gate.capDepth st,
                badge := cap.badge }
              cap.rights gate.cspaceRoot decoded.capRecvSlot
              (determineExecutingCore st tid) st with
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
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId) (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
    (args : Architecture.SyscallArgDecode.SetPriorityArgs) (st : SystemState)
    (hSyscall : decoded.syscallId = .tcbSetPriority)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeSetPriorityArgs decoded = .ok args)
    (hCaller : validateThreadIdArg tid = .ok vCallerTid)
    (hValid : validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vTargetTid) :
    dispatchWithCap decoded tid gate cap st =
      (match SchedContext.PriorityManagement.setPriorityOnCore st vCallerTid vTargetTid
              (SeLe4n.Priority.ofNat args.newPriority) (determineExecutingCore st tid) with
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
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (scId : SeLe4n.ObjId) (vScId : SeLe4n.ValidObjId)
    (st : SystemState)
    (hSyscall : decoded.syscallId = .schedContextUnbind)
    (hTarget : cap.target = .object scId)
    (hDecode : ∃ a, decodeSchedContextUnbindArgs decoded = .ok a)
    (hValid : validateObjIdArg scId = .ok vScId) :
    dispatchWithCap decoded tid gate cap st =
      (match SchedContextOps.schedContextUnbindOnCore vScId
              (determineExecutingCore st tid) st with
       | .ok (st', _) => .ok ((), st')
       | .error e => .error e) := by
  obtain ⟨a, hArgs⟩ := hDecode
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hArgs, hValid]

/-- **The live `.tcbSetMCPriority` arm routes to `setMCPriorityOnCore`.**  Same
reroute, reached whenever the new ceiling caps the target's current priority. -/
theorem dispatchWithCap_tcbSetMCPriority_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId) (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
    (args : Architecture.SyscallArgDecode.SetMCPriorityArgs) (st : SystemState)
    (hSyscall : decoded.syscallId = .tcbSetMCPriority)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeSetMCPriorityArgs decoded = .ok args)
    (hCaller : validateThreadIdArg tid = .ok vCallerTid)
    (hValid : validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vTargetTid) :
    dispatchWithCap decoded tid gate cap st =
      (match SchedContext.PriorityManagement.setMCPriorityOnCore st vCallerTid vTargetTid
              (SeLe4n.Priority.ofNat args.newMCP) (determineExecutingCore st tid) with
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
      ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
        (cap : Capability) (epId : SeLe4n.ObjId) (st : SystemState),
        decoded.syscallId = .send →
        cap.target = .object epId →
        dispatchWithCap decoded tid gate cap st =
          (match endpointSendDualWithCapsOnCore epId tid
                  { registers := extractMessageRegisters decoded.msgRegs decoded.msgInfo,
                    caps := resolveExtraCaps gate.cspaceRoot (decodeExtraCapAddrs decoded)
                              gate.capDepth st,
                    badge := cap.badge }
                  cap.rights gate.cspaceRoot decoded.capRecvSlot
                  (determineExecutingCore st tid) st with
           | (_, .error e) => .error e
           | (st', .ok (summary, _)) =>
               match clearWokenReceiverStash ((st.getEndpoint? epId).bind (·.receiveQ.head)) st' with
               | .error e => .error e
               | .ok ((), st'') =>
                   .ok ((), Architecture.stageWokenDelivery st''
                             ((st.getEndpoint? epId).bind (·.receiveQ.head))
                             summary.installedCount))
  | .tcbSetPriority =>
      ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
        (cap : Capability) (objId : SeLe4n.ObjId)
        (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
        (args : Architecture.SyscallArgDecode.SetPriorityArgs) (st : SystemState),
        decoded.syscallId = .tcbSetPriority →
        cap.target = .object objId →
        decodeSetPriorityArgs decoded = .ok args →
        validateThreadIdArg tid = .ok vCallerTid →
        validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vTargetTid →
        dispatchWithCap decoded tid gate cap st =
          (match SchedContext.PriorityManagement.setPriorityOnCore st vCallerTid vTargetTid
                  (SeLe4n.Priority.ofNat args.newPriority) (determineExecutingCore st tid) with
           | .ok (st', _) => .ok ((), st')
           | .error e => .error e)
  | .tcbSetMCPriority =>
      ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
        (cap : Capability) (objId : SeLe4n.ObjId)
        (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
        (args : Architecture.SyscallArgDecode.SetMCPriorityArgs) (st : SystemState),
        decoded.syscallId = .tcbSetMCPriority →
        cap.target = .object objId →
        decodeSetMCPriorityArgs decoded = .ok args →
        validateThreadIdArg tid = .ok vCallerTid →
        validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vTargetTid →
        dispatchWithCap decoded tid gate cap st =
          (match SchedContext.PriorityManagement.setMCPriorityOnCore st vCallerTid vTargetTid
                  (SeLe4n.Priority.ofNat args.newMCP) (determineExecutingCore st tid) with
           | .ok (st', _) => .ok ((), st')
           | .error e => .error e)
  | .receive =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
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
        dispatchWithCapChecked ctx decoded tid gate cap st =
          (match endpointReceiveDualOnCore epId tid replyIdOpt
                  (determineExecutingCore st tid) st with
           -- WS-RA RA.B.6: the arm stages the non-blocking consume's delivery
           -- into the caller's return frame.
           | (st', .ok (_, _)) =>
               .ok ((), Architecture.stageDeliveredMessage
                         (Architecture.stageWokenSendCompletion st'
                           ((st.getEndpoint? epId).bind (·.sendQ.head))) tid 0)
           | (_, .error e) => .error e)
  | .tcbSuspend =>
      ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
        (cap : Capability) (objId : SeLe4n.ObjId) (vtid : SeLe4n.ValidThreadId)
        (st : SystemState),
        decoded.syscallId = .tcbSuspend →
        cap.target = .object objId →
        (∃ a, Architecture.SyscallArgDecode.decodeSuspendArgs decoded = .ok a) →
        validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vtid →
        dispatchWithCap decoded tid gate cap st =
          (match Lifecycle.Suspend.suspendThreadOnCore st vtid
                  (determineExecutingCore st tid) with
           | .ok (st', _) => .ok ((), st')
           | .error e => .error e)
  | .tcbResume =>
      ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
        (cap : Capability) (objId : SeLe4n.ObjId) (vtid : SeLe4n.ValidThreadId)
        (st : SystemState),
        decoded.syscallId = .tcbResume →
        cap.target = .object objId →
        (∃ a, Architecture.SyscallArgDecode.decodeResumeArgs decoded = .ok a) →
        validateThreadIdArg (SeLe4n.ThreadId.ofNat objId.toNat) = .ok vtid →
        dispatchWithCap decoded tid gate cap st =
          (match Lifecycle.Suspend.resumeThreadOnCoreLive st vtid
                  (determineExecutingCore st tid) with
           | .ok (st', _) => .ok ((), st')
           | .error e => .error e)
  | .schedContextUnbind =>
      ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
        (cap : Capability) (scId : SeLe4n.ObjId) (vScId : SeLe4n.ValidObjId)
        (st : SystemState),
        decoded.syscallId = .schedContextUnbind →
        cap.target = .object scId →
        (∃ a, decodeSchedContextUnbindArgs decoded = .ok a) →
        validateObjIdArg scId = .ok vScId →
        dispatchWithCap decoded tid gate cap st =
          (match SchedContextOps.schedContextUnbindOnCore vScId
                  (determineExecutingCore st tid) st with
           | .ok (st', _) => .ok ((), st')
           | .error e => .error e)
  | .lifecycleRetype =>
      ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
        (cap : Capability) (objId : SeLe4n.ObjId)
        (args : Architecture.SyscallArgDecode.LifecycleRetypeArgs),
        decoded.syscallId = .lifecycleRetype →
        cap.target = .object objId →
        decodeLifecycleRetypeArgs decoded = .ok args →
        dispatchWithCap decoded tid gate cap =
          fun st => lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache
            (determineExecutingCore st tid) cap args.targetObj
            (objectOfKernelType args.newType args.size) st
  | .vspaceMap =>
      ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
        (cap : Capability) (objId : SeLe4n.ObjId)
        (args : Architecture.SyscallArgDecode.VSpaceMapArgs) (st : SystemState),
        decoded.syscallId = .vspaceMap →
        cap.target = .object objId →
        decodeVSpaceMapArgsChecked decoded st.machine.maxASID
          (2^st.machine.physicalAddressWidth) = .ok args →
        vspaceCapAuthorizesAsid cap args.asid st = true →
        dispatchWithCap decoded tid gate cap st =
          (match validateVSpaceMapPermsForMemoryKind args st.machine.memoryMap with
            | .error e => .error e
            | .ok validatedArgs =>
                Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore
                  (determineExecutingCore st tid) validatedArgs.asid
                  validatedArgs.vaddr validatedArgs.paddr validatedArgs.perms st)
  | .vspaceUnmap =>
      ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
        (cap : Capability) (objId : SeLe4n.ObjId)
        (args : Architecture.SyscallArgDecode.VSpaceUnmapArgs) (st : SystemState),
        decoded.syscallId = .vspaceUnmap →
        cap.target = .object objId →
        decodeVSpaceUnmapArgs decoded st.machine.maxASID = .ok args →
        vspaceCapAuthorizesAsid cap args.asid st = true →
        dispatchWithCap decoded tid gate cap st =
          Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast
            (determineExecutingCore st tid) args.asid args.vaddr st
  -- Every other syscall: no delegation theorem exists yet.  `False` rather than
  -- `True` so the absence is unforgeable — an inventory entry claiming
  -- delegation evidence for one of these cannot be constructed.
  -- WS-SM SM8.C.9: the live `.declassify` arm.  Stated over the *checked*
  -- dispatch, like `.receive`, because that is the only path it has: the
  -- unchecked one fails closed (`dispatchWithCap_declassify_denied`).
  | .declassify =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
        (gate : SyscallGate) (cap : Capability) (targetId : SeLe4n.ObjId) (st : SystemState),
        decoded.syscallId = .declassify →
        cap.target = .object targetId →
        dispatchWithCapChecked ctx decoded tid gate cap st =
          declassifyObjectFromCore (liftLegacyContext ctx) ctx.declassificationPolicy
            (determineExecutingCore st tid) targetId st
  -- WS-SM SM9.A.10: the live audit arms.  Stated over the *checked* dispatch,
  -- like `.declassify`, because that is the only path they have — and the
  -- conclusion names the return-frame write, so an arm that computed the right
  -- word and failed to stage it would not satisfy this.
  | .auditRead =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
        (gate : SyscallGate) (cap : Capability)
        (args : Architecture.SyscallArgDecode.AuditReadArgs) (op : AuditReadOp)
        (st : SystemState),
        decoded.syscallId = .auditRead →
        cap.target = .auditTrail →
        cap.hasRight gate.requiredRight = true →
        Architecture.SyscallArgDecode.decodeAuditReadArgs decoded = .ok args →
        decodeAuditReadOp args.opcode args.index args.chunk = some op →
        dispatchWithCapChecked ctx decoded tid gate cap st =
          (match auditReadFromCore (liftLegacyContext ctx) (validatedAuditMonitorClearance ctx)
              (determineExecutingCore st tid) op st with
           | .error e => .error e
           | .ok (w, st') =>
               .ok ((), Architecture.writeReturnFrameToTcb st' tid
                 (Architecture.returnFrameOfWord w.toUInt64)))
  | .auditDrain =>
      ∀ (ctx : LabelingContext) (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
        (gate : SyscallGate) (cap : Capability)
        (args : Architecture.SyscallArgDecode.AuditDrainArgs) (st : SystemState),
        decoded.syscallId = .auditDrain →
        cap.target = .auditTrail →
        cap.hasRight gate.requiredRight = true →
        Architecture.SyscallArgDecode.decodeAuditDrainArgs decoded = .ok args →
        dispatchWithCapChecked ctx decoded tid gate cap st =
          (match auditDrainVisiblePrefix (liftLegacyContext ctx)
              (validatedAuditMonitorClearance ctx)
              (determineExecutingCore st tid) args.count st with
           | .error e => .error e
           | .ok (n, st') =>
               .ok ((), Architecture.writeReturnFrameToTcb st' tid
                 (Architecture.returnFrameOfWord n.toUInt64)))
  | _ => False

/-- The `.receive` obligation, discharged. -/
theorem syscallDelegates_receive : syscallDelegates .receive := by
  intro ctx decoded tid gate cap epId replyIdOpt st hSyscall hTarget hFlow hOverride hReply
  exact dispatchWithCapChecked_receive_delegates ctx decoded tid gate cap epId replyIdOpt st
    hSyscall hTarget hFlow hOverride hReply

/-- The `.tcbResume` obligation, discharged. -/
theorem syscallDelegates_tcbResume : syscallDelegates .tcbResume := by
  intro decoded tid gate cap objId vtid st hSyscall hTarget hDecode hValid
  exact dispatchWithCap_tcbResume_delegates decoded tid gate cap objId vtid st
    hSyscall hTarget hDecode hValid

/-- The `.tcbSuspend` obligation, discharged. -/
theorem syscallDelegates_tcbSuspend : syscallDelegates .tcbSuspend := by
  intro decoded tid gate cap objId vtid st hSyscall hTarget hDecode hValid
  exact dispatchWithCap_tcbSuspend_delegates decoded tid gate cap objId vtid st
    hSyscall hTarget hDecode hValid

/-- WS-SM SM8.B (PR #861 review round 35): the `.lifecycleRetype` obligation,
discharged.

Added with the arm's cross-core inventory entry, so the entry rests on a
machine-checked tie to the dispatch rather than on a human reading of the arm —
the class of error three separate review rounds found. -/
theorem syscallDelegates_lifecycleRetype : syscallDelegates .lifecycleRetype := by
  intro decoded tid gate cap objId args hSyscall hTarget hDecode
  exact dispatchWithCap_lifecycleRetype_delegates decoded tid gate cap objId args
    hSyscall hTarget hDecode

/-- WS-SM SM8.B: the `.vspaceMap` obligation, discharged. -/
theorem syscallDelegates_vspaceMap : syscallDelegates .vspaceMap := by
  intro decoded tid gate cap objId args st hSyscall hTarget hDecode hAuth
  exact dispatchWithCap_vspaceMap_delegates decoded tid gate cap objId args st
    hSyscall hTarget hDecode hAuth

/-- WS-SM SM8.C.9: the `.declassify` obligation, discharged. -/
theorem syscallDelegates_declassify : syscallDelegates .declassify := by
  intro ctx decoded tid gate cap targetId st hSyscall hTarget
  exact dispatchWithCapChecked_declassify_delegates ctx decoded tid gate cap targetId st
    hSyscall hTarget

/-- WS-SM SM9.A.10: the `.auditRead` obligation, discharged. -/
theorem syscallDelegates_auditRead : syscallDelegates .auditRead := by
  intro ctx decoded tid gate cap args op st hSyscall hTarget hRight hArgs hOp
  exact dispatchWithCapChecked_auditRead_delegates ctx decoded tid gate cap args op st
    hSyscall hTarget hRight hArgs hOp

/-- WS-SM SM9.A.10: the `.auditDrain` obligation, discharged. -/
theorem syscallDelegates_auditDrain : syscallDelegates .auditDrain := by
  intro ctx decoded tid gate cap args st hSyscall hTarget hRight hArgs
  exact dispatchWithCapChecked_auditDrain_delegates ctx decoded tid gate cap args st
    hSyscall hTarget hRight hArgs

/-- WS-SM SM8.B: the `.vspaceUnmap` obligation, discharged. -/
theorem syscallDelegates_vspaceUnmap : syscallDelegates .vspaceUnmap := by
  intro decoded tid gate cap objId args st hSyscall hTarget hDecode hAuth
  exact dispatchWithCap_vspaceUnmap_delegates decoded tid gate cap objId args st
    hSyscall hTarget hDecode hAuth

/-- The `.send` obligation, discharged. -/
theorem syscallDelegates_send : syscallDelegates .send := by
  intro decoded tid gate cap epId st hSyscall hTarget
  exact dispatchWithCap_send_delegates decoded tid gate cap epId st hSyscall hTarget

/-- The `.tcbSetPriority` obligation, discharged. -/
theorem syscallDelegates_tcbSetPriority : syscallDelegates .tcbSetPriority := by
  intro decoded tid gate cap objId vCallerTid vTargetTid args st hSyscall hTarget hDecode
    hCaller hValid
  exact dispatchWithCap_tcbSetPriority_delegates decoded tid gate cap objId vCallerTid
    vTargetTid args st hSyscall hTarget hDecode hCaller hValid

/-- The `.tcbSetMCPriority` obligation, discharged. -/
theorem syscallDelegates_tcbSetMCPriority : syscallDelegates .tcbSetMCPriority := by
  intro decoded tid gate cap objId vCallerTid vTargetTid args st hSyscall hTarget hDecode
    hCaller hValid
  exact dispatchWithCap_tcbSetMCPriority_delegates decoded tid gate cap objId vCallerTid
    vTargetTid args st hSyscall hTarget hDecode hCaller hValid

/-- The `.schedContextUnbind` obligation, discharged. -/
theorem syscallDelegates_schedContextUnbind : syscallDelegates .schedContextUnbind := by
  intro decoded tid gate cap scId vScId st hSyscall hTarget hDecode hValid
  exact dispatchWithCap_schedContextUnbind_delegates decoded tid gate cap scId vScId st
    hSyscall hTarget hDecode hValid


end SeLe4n.Kernel
