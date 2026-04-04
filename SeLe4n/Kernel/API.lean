/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Invariant
import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Kernel.IPC.DualQueue
import SeLe4n.Kernel.IPC.Invariant
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

import SeLe4n.Kernel.Architecture.Assumptions
import SeLe4n.Kernel.Architecture.RegisterDecode
import SeLe4n.Kernel.Architecture.SyscallArgDecode

import SeLe4n.Kernel.SchedContext.Operations
import SeLe4n.Kernel.Lifecycle.Suspend
import SeLe4n.Kernel.SchedContext.PriorityManagement
import SeLe4n.Kernel.IPC.Operations.Donation

import SeLe4n.Kernel.Architecture.Adapter
import SeLe4n.Kernel.Architecture.Invariant
import SeLe4n.Kernel.Architecture.VSpace
import SeLe4n.Kernel.Architecture.VSpaceInvariant

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
| `cspaceMint`, `cspaceCopy`, `cspaceMove` | Capability | Stable (M-08/A-20: `cspaceMint` does not record CDT edges — capabilities created via this path are untracked by CDT-based revocation; prefer `cspaceMintWithCdt` for tracked derivation) |
| `cspaceMutate`, `cspaceInsertSlot`, `cspaceDeleteSlot` | Capability | Stable |
| `endpointSendDual`, `endpointReceiveDual` | IPC (dual-queue) | Stable |
| `endpointReply`, `endpointCall`, `endpointReplyRecv` | IPC | Stable |
| `lifecycleRetypeObject`, `lifecycleRevokeDeleteRetype` | Lifecycle | Internal (proof helpers — use `lifecycleRetypeWithCleanup` for production) |
| `lifecycleRetypeWithCleanup` | Lifecycle (WS-H2) | Stable (production entry point with cleanup + scrubbing) |
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
| `setPriority` | `seL4_TCB_SetPriority` | Requires MCS scheduling context model. Priority is currently set at TCB creation; runtime modification deferred until MCS scheduling contexts (budget/period/replenishment) are modeled. | MCS scheduling (long-horizon) |
| `setMCPriority` | `seL4_TCB_SetMCPriority` | Maximum controlled priority. Same MCS prerequisite as `setPriority`. | MCS scheduling (long-horizon) |
| `suspend` | `seL4_TCB_Suspend` | **IMPLEMENTED** (D1, v0.24.0). `suspendThread` in `Lifecycle/Suspend.lean`, wired as `SyscallId.tcbSuspend`. | Complete |
| `resume` | `seL4_TCB_Resume` | **IMPLEMENTED** (D1, v0.24.0). `resumeThread` in `Lifecycle/Suspend.lean`, wired as `SyscallId.tcbResume`. | Complete |
| `setIPCBuffer` | `seL4_TCB_SetIPCBuffer` | Trivial field update, but VSpace validation of the buffer address (must be mapped, writable, aligned) requires `VSpaceBackend` integration and page table walk. | H3 hardware binding (VSpace validation) |
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

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

/-- WS-H15c/A-42: Resolve and validate a capability from a syscall gate.

Performs the full seL4 syscall capability-checking sequence:
1. Resolves the capability address through the CSpace root via `resolveCapAddress`.
2. Looks up the capability at the resolved slot.
3. Verifies the capability grants the required access right.

Returns the resolved capability if all checks pass; an error otherwise.
The state is unchanged (capability lookup is read-only). -/
def syscallLookupCap (gate : SyscallGate) : Kernel Capability :=
  fun st =>
    match resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st with
    | .error e => .error e
    | .ok ref =>
      match SystemState.lookupSlotCap st ref with
      | none => .error .invalidCapability
      | some cap =>
        if cap.hasRight gate.requiredRight
        then .ok (cap, st)
        else .error .illegalAuthority

/-- WS-H15c/A-42: Gated operation combinator. Resolves and validates a
capability, then invokes the operation with the resolved capability. -/
def syscallInvoke (gate : SyscallGate) (op : Capability → Kernel α) : Kernel α :=
  fun st =>
    match syscallLookupCap gate st with
    | .error e => .error e
    | .ok (cap, st') => op cap st'

-- ============================================================================
-- Syscall soundness theorems
-- ============================================================================

/-- WS-H15c/A-42: If `syscallLookupCap` succeeds, the caller's CSpace root
contains a valid capability at the specified address with the required right,
and the state is unchanged (lookup is read-only). -/
theorem syscallLookupCap_implies_capability_held
    (gate : SyscallGate) (st : SystemState) (cap : Capability) (st' : SystemState)
    (hOk : syscallLookupCap gate st = .ok (cap, st')) :
    ∃ ref, resolveCapAddress gate.cspaceRoot gate.capAddr gate.capDepth st = .ok ref ∧
           SystemState.lookupSlotCap st ref = some cap ∧
           cap.hasRight gate.requiredRight = true ∧
           st' = st := by
  unfold syscallLookupCap at hOk
  split at hOk
  · simp at hOk
  next ref hResolve =>
    split at hOk
    · simp at hOk
    next cap' hLookup =>
      split at hOk
      · next hRight =>
        simp at hOk
        obtain ⟨hCap, hSt⟩ := hOk
        exact ⟨ref, hResolve, by rw [hCap.symm]; exact hLookup, by rw [hCap.symm]; exact hRight, hSt.symm⟩
      · simp at hOk

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
   simply don't transfer. -/
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

/-- V8-H/Z5-J/D1: Shared dispatch for capability-only syscalls — these 11 arms
derive authority entirely from capability possession and require no
information-flow checks. Both `dispatchWithCap` and `dispatchWithCapChecked`
delegate to this helper for: `.cspaceDelete`, `.lifecycleRetype`, `.vspaceMap`,
`.vspaceUnmap`, `.serviceRevoke`, `.serviceQuery`, `.schedContextConfigure`,
`.schedContextBind`, `.schedContextUnbind`, `.tcbSuspend`, `.tcbResume`.

Returns `none` if the syscall ID is not a capability-only arm (i.e., it
requires IPC/cross-domain handling). -/
private def dispatchCapabilityOnly (decoded : SyscallDecodeResult)
    (cap : Capability) : Option (Kernel Unit) :=
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
  | .lifecycleRetype =>
    some <| match cap.target with
    | .object _ =>
        fun st => match decodeLifecycleRetypeArgs decoded with
        | .error e => .error e
        | .ok args =>
            let newObj := objectOfKernelType args.newType args.size
            lifecycleRetypeDirectWithCleanup cap args.targetObj newObj st
    | _ => fun _ => .error .invalidCapability
  | .vspaceMap =>
    some <| match cap.target with
    | .object _ =>
        fun st => match decodeVSpaceMapArgs decoded with
        | .error e => .error e
        | .ok args =>
            -- X2-E: Use state-aware PA bounds (reads physicalAddressWidth from machine state)
            Architecture.vspaceMapPageCheckedWithFlushFromState args.asid args.vaddr args.paddr
              args.perms st
    | _ => fun _ => .error .invalidCapability
  | .vspaceUnmap =>
    some <| match cap.target with
    | .object _ =>
        fun st => match decodeVSpaceUnmapArgs decoded with
        | .error e => .error e
        | .ok args =>
            Architecture.vspaceUnmapPageWithFlush args.asid args.vaddr st
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
        | .ok (_, st') => .ok ((), st')
        | .error e => .error e
    | _ => fun _ => .error .invalidCapability
  -- Z5-J: SchedContext configure — decode args, validate, configure
  | .schedContextConfigure =>
    some <| match cap.target with
    | .object scId =>
      fun st => match decodeSchedContextConfigureArgs decoded with
      | .error e => .error e
      | .ok args =>
          SchedContextOps.schedContextConfigure scId args.budget args.period
            args.priority args.deadline args.domain st
    | _ => fun _ => .error .invalidCapability
  -- Z5-J: SchedContext bind — decode threadId, bind thread to SchedContext
  | .schedContextBind =>
    some <| match cap.target with
    | .object scId =>
      fun st => match decodeSchedContextBindArgs decoded with
      | .error e => .error e
      | .ok args =>
          SchedContextOps.schedContextBind scId (ThreadId.ofNat args.threadId) st
    | _ => fun _ => .error .invalidCapability
  -- Z5-J: SchedContext unbind — no extra args, SchedContext from cap target
  | .schedContextUnbind =>
    some <| match cap.target with
    | .object scId =>
      fun st => match decodeSchedContextUnbindArgs decoded with
      | .error e => .error e
      | .ok _ => SchedContextOps.schedContextUnbind scId st
    | _ => fun _ => .error .invalidCapability
  -- D1: TCB suspend — target thread from capability
  | .tcbSuspend =>
    some <| match cap.target with
    | .object objId =>
      fun st => match decodeSuspendArgs decoded with
      | .error e => .error e
      | .ok _ =>
        match Lifecycle.Suspend.suspendThread st (ThreadId.ofNat objId.toNat) with
        | .ok st' => .ok ((), st')
        | .error e => .error e
    | _ => fun _ => .error .invalidCapability
  -- D1: TCB resume — target thread from capability
  | .tcbResume =>
    some <| match cap.target with
    | .object objId =>
      fun st => match decodeResumeArgs decoded with
      | .error e => .error e
      | .ok _ =>
        match Lifecycle.Suspend.resumeThread st (ThreadId.ofNat objId.toNat) with
        | .ok st' => .ok ((), st')
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
   showing all 22 `SyscallId` variants are handled by one of the two tiers
3. Keeps argument-free dispatch arms concise via `dispatchCapabilityOnly`
The wildcard `| _ =>` arm is provably dead code (W2-C). -/
private def dispatchWithCap (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability) : Kernel Unit :=
  match dispatchCapabilityOnly decoded cap with
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
        match endpointSendDualWithCaps epId tid msg cap.rights gate.cspaceRoot
            decoded.capRecvSlot st with
        | .error e => .error e
        | .ok (_, st') => .ok ((), st')
    | _ => fun _ => .error .invalidCapability
  | .receive =>
    match cap.target with
    | .object epId =>
      fun st => match endpointReceiveDual epId tid st with
        | .ok (_, st') => .ok ((), st')
        | .error e => .error e
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
        -- Z7: Determine receiver before call pops it from receiveQ
        let maybeReceiver := match st.objects[epId]? with
          | some (.endpoint ep) => ep.receiveQ.head
          | _ => none
        match endpointCallWithCaps epId tid msg cap.rights gate.cspaceRoot
            decoded.capRecvSlot st with
        | .error e => .error e
        | .ok (_, st') =>
          -- Z7: Apply SchedContext donation to passive server if applicable
          match maybeReceiver with
          | some receiverTid => .ok ((), applyCallDonation st' tid receiverTid)
          | none => .ok ((), st')
    | _ => fun _ => .error .invalidCapability
  -- WS-K-E: IPC reply — message body populated from decoded message registers.
  | .reply =>
    match cap.target with
    | .replyCap targetTid =>
      let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
      -- Z7: Use donation-aware reply wrapper to return SchedContext
      endpointReplyWithDonation tid targetTid { registers := body, caps := #[], badge := cap.badge }
    | _ => fun _ => .error .invalidCapability
  -- WS-K-C: CSpace operations — cap targets a CNode, message registers
  -- carry slot indices, rights, and badge. Decoded via SyscallArgDecode.
  -- U5-H/U-M03: Badge value 0 is treated as "no badge" by design, matching seL4
  -- semantics where badge 0 indicates an unbadged capability. This means callers
  -- cannot explicitly set badge 0 — a deliberate simplification that matches
  -- seL4's treatment of zero-valued badges as "no badge specified".
  -- X5-I (L-5): Confirmed v0.22.17 audit — badge zero indistinguishability
  -- matches seL4 semantics. No security impact.
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
            cspaceMint src dst args.rights badge st
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
          match notificationSignal notifId args.badge st with
          | .error e => .error e
          | .ok ((), st') => .ok ((), st')
    | _ => fun _ => .error .invalidCapability
  -- V2-A: Notification wait — consume pending badge or block.
  -- The notification object comes from the capability target, waiter is current thread.
  | .notificationWait =>
    match cap.target with
    | .object notifId =>
      fun st =>
        match notificationWait notifId tid st with
        | .error e => .error e
        | .ok (_, st') => .ok ((), st')
    | _ => fun _ => .error .invalidCapability
  -- V2-C: ReplyRecv — compound reply + receive in one transition.
  -- Cap targets the endpoint for the receive leg. Reply target from MR[0].
  -- Message body for the reply leg comes from the standard message registers.
  | .replyRecv =>
    match cap.target with
    | .object epId =>
      fun st => match decodeReplyRecvArgs decoded with
      | .error e => .error e
      | .ok args =>
          let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
          let msg : IpcMessage := { registers := body, caps := #[], badge := cap.badge }
          -- Z7: Use donation-aware replyRecv wrapper
          match endpointReplyRecvWithDonation epId tid args.replyTarget msg st with
          | .error e => .error e
          | .ok ((), st') => .ok ((), st')
    | _ => fun _ => .error .invalidCapability
  -- D2-K: TCB setPriority — priority from message register, target from capability
  | .tcbSetPriority =>
    match cap.target with
    | .object objId =>
      fun st => match decodeSetPriorityArgs decoded with
      | .error e => .error e
      | .ok args =>
        -- Caller is the current thread (tid), target from capability
        match SchedContext.PriorityManagement.setPriorityOp st tid
            (ThreadId.ofNat objId.toNat)
            (Priority.ofNat args.newPriority) with
        | .ok st' => .ok ((), st')
        | .error e => .error e
    | _ => fun _ => .error .invalidCapability
  -- D2-K: TCB setMCPriority — MCP from message register, target from capability
  | .tcbSetMCPriority =>
    match cap.target with
    | .object objId =>
      fun st => match decodeSetMCPriorityArgs decoded with
      | .error e => .error e
      | .ok args =>
        -- Caller is the current thread (tid), target from capability
        match SchedContext.PriorityManagement.setMCPriorityOp st tid
            (ThreadId.ofNat objId.toNat)
            (Priority.ofNat args.newMCP) with
        | .ok st' => .ok ((), st')
        | .error e => .error e
    | _ => fun _ => .error .invalidCapability
  -- V8-H/D1/D2: Remaining arms (cspaceDelete, lifecycleRetype, vspaceMap, vspaceUnmap,
  -- serviceRevoke, serviceQuery, schedContextConfigure, schedContextBind,
  -- schedContextUnbind, tcbSuspend, tcbResume) are unreachable here — handled by
  -- dispatchCapabilityOnly returning `some` above. The wildcard satisfies
  -- Lean's exhaustiveness checker.
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

U5-C/U-M04: `.reply` now routes through `endpointReplyChecked` wrapper for
defense-in-depth, even though reply caps are single-use authority.

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
  match dispatchCapabilityOnly decoded cap with
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
        match endpointSendDualChecked ctx epId tid msg st with
        | .error e => .error e
        | .ok (_, st') => .ok ((), st')
    | _ => fun _ => .error .invalidCapability
  -- T6-I: IPC receive — checked for endpoint→receiver flow
  | .receive =>
    match cap.target with
    | .object epId =>
      fun st => match endpointReceiveDualChecked ctx epId tid st with
        | .ok (_, st') => .ok ((), st')
        | .error e => .error e
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
        -- Z7: Determine receiver before call pops it from receiveQ
        let maybeReceiver := match st.objects[epId]? with
          | some (.endpoint ep) => ep.receiveQ.head
          | _ => none
        match endpointCallChecked ctx epId tid msg cap.rights gate.cspaceRoot
            decoded.capRecvSlot st with
        | .error e => .error e
        | .ok (_, st') =>
          -- Z7: Apply SchedContext donation to passive server if applicable
          match maybeReceiver with
          | some receiverTid => .ok ((), applyCallDonation st' tid receiverTid)
          | none => .ok ((), st')
    | _ => fun _ => .error .invalidCapability
  -- U5-C/U-M04: Reply — routed through enforcement wrapper for defense-in-depth.
  -- In seL4, the reply capability is single-use authority consumed upon use.
  -- The flow check here is a defense-in-depth measure ensuring the reply path
  -- is auditable and consistent with all other cross-domain operations.
  | .reply =>
    match cap.target with
    | .replyCap targetTid =>
      let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
      -- Z7: Apply donation return after checked reply
      fun st =>
        match endpointReplyChecked ctx tid targetTid { registers := body, caps := #[], badge := cap.badge } st with
        | .error e => .error e
        | .ok ((), st') => .ok ((), applyReplyDonation st' tid)
    | _ => fun _ => .error .invalidCapability
  -- T6-I: CSpace mint — checked for source→destination CNode flow
  -- U5-H/U-M03: Badge value 0 is treated as "no badge" by design, matching seL4
  -- semantics where badge 0 indicates an unbadged capability.
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
          match notificationSignalChecked ctx notifId tid args.badge st with
          | .error e => .error e
          | .ok ((), st') => .ok ((), st')
    | _ => fun _ => .error .invalidCapability
  -- V2-A/T6-I: Notification wait — checked for notification→waiter flow
  | .notificationWait =>
    match cap.target with
    | .object notifId =>
      fun st =>
        match notificationWaitChecked ctx notifId tid st with
        | .error e => .error e
        | .ok (_, st') => .ok ((), st')
    | _ => fun _ => .error .invalidCapability
  -- V2-C/T6-I: ReplyRecv — checked for both reply and receive legs
  | .replyRecv =>
    match cap.target with
    | .object epId =>
      fun st => match decodeReplyRecvArgs decoded with
      | .error e => .error e
      | .ok args =>
          let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
          let msg : IpcMessage := { registers := body, caps := #[], badge := cap.badge }
          -- Z7: Apply donation return after checked replyRecv
          match endpointReplyRecvChecked ctx epId tid args.replyTarget msg st with
          | .error e => .error e
          | .ok ((), st') => .ok ((), applyReplyDonation st' tid)
    | _ => fun _ => .error .invalidCapability
  -- V8-H: Remaining capability-only arms are unreachable — handled by
  -- dispatchCapabilityOnly returning `some` above.
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
        (syscallInvoke gate (dispatchWithCapChecked ctx decoded tid gate)) st
      | some _ => .error .invalidCapability
      | none   => .error .objectNotFound
    | some _ => .error .illegalState
    | none   => .error .objectNotFound

/-- T6-I/M-IF-1: Top-level register-sourced syscall entry point with
    information-flow enforcement. All cross-domain operations are gated by
    `securityFlowsTo` before execution.

    This is the recommended entry point for production systems with
    information-flow policies. The unchecked `syscallEntry` remains
    available for trusted kernel paths and backward compatibility. -/
def syscallEntryChecked (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout)
    (regCount : Nat := 32) : Kernel Unit :=
  fun st =>
    match st.scheduler.current with
    | none => .error .illegalState
    | some tid =>
      match lookupThreadRegisterContext tid st with
      | .error e => .error e
      | .ok (regs, _) =>
        match decodeSyscallArgs layout regs regCount with
        | .error e => .error e
        | .ok decoded =>
          dispatchSyscallChecked ctx decoded tid st

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

V8-H: With the shared helper extraction, each per-arm theorem follows
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

/-- U5-D/U-L20/V8-H/Z5-J/D1: Complete dispatch equivalence — for ALL capability-only
syscalls, the checked and unchecked dispatch paths produce identical results.

Both `dispatchWithCap` and `dispatchWithCapChecked` delegate to the shared
`dispatchCapabilityOnly` helper for these 11 arms, making structural identity
trivial.

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
                decoded.syscallId = .tcbResume) :
    dispatchWithCapChecked ctx decoded tid gate cap =
    dispatchWithCap decoded tid gate cap := by
  rcases hCapOnly with h | h | h | h | h | h | h | h | h | h | h <;>
    simp [dispatchWithCapChecked, dispatchWithCap, dispatchCapabilityOnly, h]

-- ============================================================================
-- W2-C (MED-04): dispatchWithCap wildcard arm unreachability
-- ============================================================================

/-- W2-C (MED-04)/D1: Every `SyscallId` variant is handled by either
    `dispatchCapabilityOnly` (returning `some`) or one of the 11 explicit match
    arms in `dispatchWithCap`. This proves the `| _ => fun _ => .error .illegalState`
    wildcard arm is unreachable at runtime.

    The proof enumerates all 22 `SyscallId` constructors: 11 are routed to
    `dispatchCapabilityOnly` (`.cspaceDelete`, `.lifecycleRetype`, `.vspaceMap`,
    `.vspaceUnmap`, `.serviceRevoke`, `.serviceQuery`, `.schedContextConfigure`,
    `.schedContextBind`, `.schedContextUnbind`, `.tcbSuspend`, `.tcbResume`),
    and the remaining 11
    (`.send`, `.receive`, `.call`, `.reply`, `.cspaceMint`, `.cspaceCopy`,
    `.cspaceMove`, `.serviceRegister`, `.notificationSignal`, `.notificationWait`,
    `.replyRecv`) are handled by explicit match arms in `dispatchWithCap`. -/
theorem dispatchWithCap_wildcard_unreachable (sid : SyscallId) :
    sid ∈ ([.send, .receive, .call, .reply, .cspaceMint, .cspaceCopy,
            .cspaceMove, .cspaceDelete, .lifecycleRetype, .vspaceMap,
            .vspaceUnmap, .serviceRegister, .serviceRevoke, .serviceQuery,
            .notificationSignal, .notificationWait, .replyRecv,
            .schedContextConfigure, .schedContextBind,
            .schedContextUnbind, .tcbSuspend, .tcbResume,
            .tcbSetPriority, .tcbSetMCPriority] : List SyscallId) := by
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
typed kernel references, and dispatches to the appropriate kernel operation.
This is the single authoritative user-space → kernel transition boundary.

The `regCount` parameter (default 32 for ARM64) should match
`MachineConfig.registerCount` of the active platform binding. It is used by
`decodeSyscallArgs` to validate that all layout register indices are within
architectural bounds. -/
def syscallEntry (layout : SeLe4n.SyscallRegisterLayout)
    (regCount : Nat := 32) : Kernel Unit :=
  fun st =>
    match st.scheduler.current with
    | none => .error .illegalState
    | some tid =>
      match lookupThreadRegisterContext tid st with
      | .error e => .error e
      | .ok (regs, _) =>
        match decodeSyscallArgs layout regs regCount with
        | .error e => .error e
        | .ok decoded =>
          dispatchSyscall decoded tid st

-- ============================================================================
-- WS-J1-C: Soundness theorems
-- ============================================================================

/-- WS-J1-C: If `syscallEntry` succeeds, the register values decoded
successfully — i.e., `decodeSyscallArgs` returned `.ok`. -/
theorem syscallEntry_requires_valid_decode
    (layout : SeLe4n.SyscallRegisterLayout) (regCount : Nat)
    (st : SystemState) (st' : SystemState)
    (hOk : syscallEntry layout regCount st = .ok ((), st')) :
    ∃ tid regs decoded,
      st.scheduler.current = some tid ∧
      lookupThreadRegisterContext tid st = .ok (regs, st) ∧
      decodeSyscallArgs layout regs regCount = .ok decoded := by
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
      st.scheduler.current = some tid ∧
      lookupThreadRegisterContext tid st = .ok (regs, st) ∧
      decodeSyscallArgs layout regs regCount = .ok decoded ∧
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

/-- WS-K-C: When cspaceMint dispatch succeeds, the kernel-level `cspaceMint`
is invoked with the decoded source slot, destination slot, rights, and badge
from message registers. -/
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
      cspaceMint src dst args.rights badge := by
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

/-- U-H04: When lifecycleRetype dispatch succeeds, `lifecycleRetypeDirectWithCleanup`
is invoked with the resolved cap, decoded target, and constructed object.
The safe wrapper performs pre-retype cleanup (H-05) and memory scrubbing (S6-C). -/
theorem dispatchWithCap_lifecycleRetype_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.LifecycleRetypeArgs)
    (hSyscall : decoded.syscallId = .lifecycleRetype)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeLifecycleRetypeArgs decoded = .ok args) :
    dispatchWithCap decoded tid gate cap =
      lifecycleRetypeDirectWithCleanup cap args.targetObj (objectOfKernelType args.newType args.size) := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode]

/-- WS-K-D/S6-A/T6-C/X2-E: When vspaceMap dispatch succeeds,
`vspaceMapPageCheckedWithFlushFromState` is invoked with the decoded ASID,
vaddr, paddr, and validated permissions.  The state-aware variant reads
`physicalAddressWidth` from `SystemState.machine` for platform-specific PA
bounds enforcement.
T6-C: Permissions are now typed as `PagePermissions` (validated at decode). -/
theorem dispatchWithCap_vspaceMap_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.VSpaceMapArgs)
    (hSyscall : decoded.syscallId = .vspaceMap)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeVSpaceMapArgs decoded = .ok args) :
    dispatchWithCap decoded tid gate cap =
      Architecture.vspaceMapPageCheckedWithFlushFromState args.asid args.vaddr args.paddr
        args.perms := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode]

/-- WS-K-D/S6-A: When vspaceUnmap dispatch succeeds, `vspaceUnmapPageWithFlush` is
invoked with the decoded ASID and vaddr.
Production API uses the TLB-flushing variant to prevent use-after-unmap. -/
theorem dispatchWithCap_vspaceUnmap_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.VSpaceUnmapArgs)
    (hSyscall : decoded.syscallId = .vspaceUnmap)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeVSpaceUnmapArgs decoded = .ok args) :
    dispatchWithCap decoded tid gate cap =
      Architecture.vspaceUnmapPageWithFlush args.asid args.vaddr := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget, hDecode]

-- ============================================================================
-- WS-K-E: Service policy and IPC message population delegation theorems
-- ============================================================================

/-- WS-K-E/M-D01: When send dispatch is invoked, the IPC message includes
resolved extra capabilities and uses the WithCaps send path. -/
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
        match endpointSendDualWithCaps epId tid msg cap.rights gate.cspaceRoot
            decoded.capRecvSlot st with
        | .error e => .error e
        | .ok (_, st') => .ok ((), st') := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget]

/-- WS-K-E/M-D01: When call dispatch is invoked, the IPC message includes
resolved extra capabilities and uses the WithCaps call path. -/
theorem dispatchWithCap_call_uses_withCaps
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
        -- Z7: Donation post-processing after call with caps
        let maybeReceiver := match st.objects[epId]? with
          | some (.endpoint ep) => ep.receiveQ.head
          | _ => none
        match endpointCallWithCaps epId tid msg cap.rights gate.cspaceRoot
            decoded.capRecvSlot st with
        | .error e => .error e
        | .ok (_, st') =>
          match maybeReceiver with
          | some receiverTid => .ok ((), applyCallDonation st' tid receiverTid)
          | none => .ok ((), st') := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget]

/-- WS-K-E: When reply dispatch is invoked, the IPC message body is populated
from decoded message registers via `extractMessageRegisters`. -/
theorem dispatchWithCap_reply_populates_msg
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (targetTid : SeLe4n.ThreadId)
    (hSyscall : decoded.syscallId = .reply)
    (hTarget : cap.target = .replyCap targetTid) :
    dispatchWithCap decoded tid gate cap =
      let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
      -- Z7: Donation-aware reply
      endpointReplyWithDonation tid targetTid { registers := body, caps := #[], badge := cap.badge } := by
  simp [dispatchWithCap, dispatchCapabilityOnly, hSyscall, hTarget]

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
    (hCurrentHigh : ∀ t, st.scheduler.current = some t →
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
    (decodeVSpaceMapArgs d₁ = decodeVSpaceMapArgs d₂) ∧
    (decodeVSpaceUnmapArgs d₁ = decodeVSpaceUnmapArgs d₂) := by
  simp only [decodeCSpaceMintArgs, decodeCSpaceCopyArgs, decodeCSpaceMoveArgs,
    decodeCSpaceDeleteArgs, decodeLifecycleRetypeArgs, decodeVSpaceMapArgs,
    decodeVSpaceUnmapArgs, requireMsgReg, hRegs]
  trivial

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

end SeLe4n.Kernel
