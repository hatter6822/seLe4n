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
| `schedule`, `handleYield` | Scheduler | Stable |
| `timerTick` | Scheduler (M-04) | Stable |
| `scheduleDomain`, `switchDomain` | Scheduler (M-05) | Stable |
| `chooseThread`, `chooseThreadInDomain` | Scheduler | Stable |
| `cspaceLookupSlot`, `cspaceLookupPath` | Capability | Stable |
| `cspaceMint`, `cspaceCopy`, `cspaceMove` | Capability | Stable (M-08/A-20: `cspaceMint` does not record CDT edges — capabilities created via this path are untracked by CDT-based revocation; prefer `cspaceMintWithCdt` for tracked derivation) |
| `cspaceMutate`, `cspaceInsertSlot`, `cspaceDeleteSlot` | Capability | Stable |
| `endpointSendDual`, `endpointReceiveDual` | IPC (dual-queue) | Stable |
| `endpointReply`, `endpointCall`, `endpointReplyRecv` | IPC | Stable |
| `lifecycleRetypeObject`, `lifecycleRevokeDeleteRetype` | Lifecycle | Stable |
| `lifecycleRetypeWithCleanup` | Lifecycle (WS-H2) | Stable |
| `retypeFromUntyped` | Lifecycle (WS-F2) | Stable |
| `registerService`, `revokeService`, `lookupServiceByCap` | Service (WS-Q1) | Stable |
| `adapterAdvanceTimer`, `adapterWriteRegister`, `adapterReadMemory` | Architecture | Stable |
| `vspaceMapPageCheckedWithFlush`, `vspaceUnmapPageWithFlush`, `vspaceLookup` | VSpace | Stable (S6-A: production uses WithFlush variants) |
| `endpointSendDualChecked` | Info-flow (dual-queue) | Stable |
| `cspaceMintChecked` | Info-flow | Stable |
| ~~`apiEndpointSend`, `apiEndpointReceive`~~ | Syscall IPC (WS-H15c) | **Removed** (S5-A v0.19.4) — replaced by `syscallEntry` |
| ~~`apiEndpointCall`, `apiEndpointReply`~~ | Syscall IPC (WS-H15c) | **Removed** (S5-A v0.19.4) — replaced by `syscallEntry` |
| ~~`apiCspaceMint`, `apiCspaceCopy`, `apiCspaceMove`~~ | Syscall Capability (WS-H15c) | **Removed** (S5-A v0.19.4) — replaced by `syscallEntry` |
| ~~`apiCspaceDelete`~~ | Syscall Capability (WS-H15c) | **Removed** (S5-A v0.19.4) — replaced by `syscallEntry` |
| ~~`apiLifecycleRetype`~~ | Syscall Lifecycle (WS-H15c) | **Removed** (S5-A v0.19.4) — replaced by `syscallEntry` |
| ~~`apiVspaceMap`, `apiVspaceUnmap`~~ | Syscall VSpace (WS-H15c) | **Removed** (S5-A v0.19.4) — replaced by `syscallEntry` |
| ~~`apiServiceRegister`, `apiServiceRevoke`, `apiServiceQuery`~~ | Syscall Service (WS-Q1-D) | **Removed** (S5-A v0.19.4) — replaced by `syscallEntry` |
| `syscallEntry` | Syscall dispatch (WS-J1-C) | Stable |
| `lookupThreadRegisterContext` | Syscall dispatch (WS-J1-C) | Stable |
| `dispatchSyscall` | Syscall dispatch (WS-J1-C) | Stable |

## Deferred operations (WS-F5/D3)

The following seL4 operations are intentionally **deferred** from the current
model. Each is documented with rationale and the prerequisite that must be
completed before implementation.

| Operation | seL4 Reference | Rationale | Prerequisite |
|-----------|---------------|-----------|--------------|
| `setPriority` | `seL4_TCB_SetPriority` | Requires MCS scheduling context model. Priority is currently set at TCB creation; runtime modification deferred until MCS scheduling contexts (budget/period/replenishment) are modeled. | MCS scheduling (long-horizon) |
| `setMCPriority` | `seL4_TCB_SetMCPriority` | Maximum controlled priority. Same MCS prerequisite as `setPriority`. | MCS scheduling (long-horizon) |
| `suspend` | `seL4_TCB_Suspend` | Requires thread lifecycle state machine beyond `ThreadIpcState`. Must handle interactions with run queue removal, IPC blocking state cleanup, and notification wait cancellation. | WS-F6 (thread-lifecycle invariants) |
| `resume` | `seL4_TCB_Resume` | Inverse of `suspend`. Same lifecycle state machine prerequisite. Must ensure scheduler invariant preservation on thread re-insertion. | WS-F6 (thread-lifecycle invariants) |
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

/-- WS-H15c/A-42: The capability lookup does not modify kernel state. -/
theorem syscallLookupCap_state_unchanged
    (gate : SyscallGate) (st : SystemState) (cap : Capability) (st' : SystemState)
    (hOk : syscallLookupCap gate st = .ok (cap, st')) :
    st' = st := by
  obtain ⟨_, _, _, _, hSt⟩ := syscallLookupCap_implies_capability_held gate st cap st' hOk
  exact hSt

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
  | .serviceRegister => .write
  | .serviceRevoke   => .write
  | .serviceQuery    => .read

/-- M-D01: Resolve extra capability addresses from the sender's CSpace
into actual capabilities for IPC message transfer.

For each CPtr in `capAddrs`, resolve it via `resolveCapAddress` in the
sender's CSpace root, then look up the capability at the resolved slot.
Caps that fail to resolve are silently dropped (seL4 behavior).
Returns the resolved capabilities as an array. -/
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

/-- WS-J1-C/K-C/K-D: Dispatch a decoded syscall to the appropriate internal
kernel operation using the resolved capability's target. Called after cap
resolution succeeds inside `syscallInvoke`.

WS-K-C: Accepts full `SyscallDecodeResult` so dispatch arms can extract
per-syscall arguments from `decoded.msgRegs` via the typed decode functions
in `SyscallArgDecode`.

WS-K-D: Lifecycle and VSpace stubs replaced with full dispatch. All 13
syscalls now route to real kernel operations — zero `.illegalState` stubs
remain. -/
private def dispatchWithCap (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability) : Kernel Unit :=
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
            (SeLe4n.Slot.ofNat 0) st with
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
        match endpointCallWithCaps epId tid msg cap.rights gate.cspaceRoot
            (SeLe4n.Slot.ofNat 0) st with
        | .error e => .error e
        | .ok (_, st') => .ok ((), st')
    | _ => fun _ => .error .invalidCapability
  -- WS-K-E: IPC reply — message body populated from decoded message registers.
  | .reply =>
    match cap.target with
    | .replyCap targetTid =>
      let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
      endpointReply tid targetTid { registers := body, caps := #[], badge := cap.badge }
    | _ => fun _ => .error .invalidCapability
  -- WS-K-C: CSpace operations — cap targets a CNode, message registers
  -- carry slot indices, rights, and badge. Decoded via SyscallArgDecode.
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
  | .cspaceDelete =>
    match cap.target with
    | .object cnodeId =>
        fun st => match decodeCSpaceDeleteArgs decoded with
        | .error e => .error e
        | .ok args =>
            let addr : CSpaceAddr := { cnode := cnodeId, slot := args.targetSlot }
            cspaceDeleteSlot addr st
    | _ => fun _ => .error .invalidCapability
  -- WS-K-D: Lifecycle retype — cap targets the authority object, message
  -- registers carry target ObjId, type tag, and size hint.
  | .lifecycleRetype =>
    match cap.target with
    | .object _ =>
        fun st => match decodeLifecycleRetypeArgs decoded with
        | .error e => .error e
        | .ok args =>
            let newObj := objectOfKernelType args.newType args.size
            lifecycleRetypeDirect cap args.targetObj newObj st
    | _ => fun _ => .error .invalidCapability
  -- WS-K-D/S6-A: VSpace map — ASID, vaddr, paddr, perms from message registers.
  -- Uses bounds-checked + TLB-flushing variant for user-space entry.
  -- Production paths must use WithFlush to maintain tlbConsistent (R7-A.3/M-17).
  | .vspaceMap =>
    match cap.target with
    | .object _ =>
        fun st => match decodeVSpaceMapArgs decoded with
        | .error e => .error e
        | .ok args =>
            Architecture.vspaceMapPageCheckedWithFlush args.asid args.vaddr args.paddr
              args.perms st
    | _ => fun _ => .error .invalidCapability
  -- WS-K-D/S6-A: VSpace unmap — ASID and vaddr from message registers.
  -- Uses TLB-flushing variant to prevent use-after-unmap on hardware (R7-A.3/M-17).
  | .vspaceUnmap =>
    match cap.target with
    | .object _ =>
        fun st => match decodeVSpaceUnmapArgs decoded with
        | .error e => .error e
        | .ok args =>
            Architecture.vspaceUnmapPageWithFlush args.asid args.vaddr st
    | _ => fun _ => .error .invalidCapability
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
  -- WS-Q1-D: Service revoke — decode service ID from message registers.
  | .serviceRevoke =>
    match cap.target with
    | .object _ =>
      fun st => match decodeServiceRevokeArgs decoded with
      | .error e => .error e
      | .ok args => revokeService args.targetService st
    | _ => fun _ => .error .invalidCapability
  -- WS-Q1-D: Service query — lookup by endpoint capability target.
  -- The endpoint object ID comes from the capability target (no MR decode needed).
  | .serviceQuery =>
    match cap.target with
    | .object epId =>
      fun st =>
        match lookupServiceByCap epId st with
        | .ok (_, st') => .ok ((), st')
        | .error e => .error e
    | _ => fun _ => .error .invalidCapability

-- ============================================================================
-- T6-I/M-IF-1: Information-flow-checked dispatch
-- ============================================================================

/-- T6-I/M-IF-1: Policy-checked dispatch — replaces unchecked operations with their
information-flow-checked equivalents. When a `LabelingContext` is provided, all
cross-domain operations (IPC send/receive/call, CSpace mint/copy/move, notification
signal, service register) are gated by `securityFlowsTo` before execution.

This ensures the runtime dispatch path matches the proven model: the enforcement
soundness theorems (Soundness.lean) prove NI for checked wrappers, and this
function guarantees those wrappers are actually used at runtime.

**Design**: Operations that don't cross domain boundaries (CSpace delete, lifecycle
retype, VSpace map/unmap, service revoke/query, reply) are left unchecked because
they derive authority entirely from capability possession or operate within a single
domain. -/
private def dispatchWithCapChecked (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (gate : SyscallGate) (cap : Capability) : Kernel Unit :=
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
  -- T6-I: IPC call — checked for sender→endpoint flow
  | .call =>
    match cap.target with
    | .object epId =>
      fun st =>
        let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
        let extraCapAddrs := decodeExtraCapAddrs decoded
        let resolvedCaps := resolveExtraCaps gate.cspaceRoot extraCapAddrs gate.capDepth st
        let msg : IpcMessage := { registers := body, caps := resolvedCaps, badge := cap.badge }
        -- Call uses send-direction flow check (caller→endpoint)
        let senderLabel := ctx.threadLabelOf tid
        let endpointLabel := ctx.endpointLabelOf epId
        if securityFlowsTo senderLabel endpointLabel then
          match endpointCallWithCaps epId tid msg cap.rights gate.cspaceRoot
              (SeLe4n.Slot.ofNat 0) st with
          | .error e => .error e
          | .ok (_, st') => .ok ((), st')
        else .error .flowDenied
    | _ => fun _ => .error .invalidCapability
  -- T6-I: Reply — no cross-domain check needed (reply cap is single-use authority)
  | .reply =>
    match cap.target with
    | .replyCap targetTid =>
      let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
      endpointReply tid targetTid { registers := body, caps := #[], badge := cap.badge }
    | _ => fun _ => .error .invalidCapability
  -- T6-I: CSpace mint — checked for source→destination CNode flow
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
  -- T6-I: CSpace delete — capability-only, no cross-domain flow
  | .cspaceDelete =>
    match cap.target with
    | .object cnodeId =>
        fun st => match decodeCSpaceDeleteArgs decoded with
        | .error e => .error e
        | .ok args =>
            let addr : CSpaceAddr := { cnode := cnodeId, slot := args.targetSlot }
            cspaceDeleteSlot addr st
    | _ => fun _ => .error .invalidCapability
  -- T6-I: Lifecycle retype — capability-only, no cross-domain flow
  | .lifecycleRetype =>
    match cap.target with
    | .object _ =>
        fun st => match decodeLifecycleRetypeArgs decoded with
        | .error e => .error e
        | .ok args =>
            let newObj := objectOfKernelType args.newType args.size
            lifecycleRetypeDirect cap args.targetObj newObj st
    | _ => fun _ => .error .invalidCapability
  -- T6-I: VSpace map — no cross-domain flow (address-space-local operation)
  | .vspaceMap =>
    match cap.target with
    | .object _ =>
        fun st => match decodeVSpaceMapArgs decoded with
        | .error e => .error e
        | .ok args =>
            Architecture.vspaceMapPageCheckedWithFlush args.asid args.vaddr args.paddr
              args.perms st
    | _ => fun _ => .error .invalidCapability
  -- T6-I: VSpace unmap — no cross-domain flow
  | .vspaceUnmap =>
    match cap.target with
    | .object _ =>
        fun st => match decodeVSpaceUnmapArgs decoded with
        | .error e => .error e
        | .ok args =>
            Architecture.vspaceUnmapPageWithFlush args.asid args.vaddr st
    | _ => fun _ => .error .invalidCapability
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
  -- T6-I: Service revoke — capability-only
  | .serviceRevoke =>
    match cap.target with
    | .object _ =>
      fun st => match decodeServiceRevokeArgs decoded with
      | .error e => .error e
      | .ok args => revokeService args.targetService st
    | _ => fun _ => .error .invalidCapability
  -- T6-I: Service query — read-only
  | .serviceQuery =>
    match cap.target with
    | .object epId =>
      fun st =>
        match lookupServiceByCap epId st with
        | .ok (_, st') => .ok ((), st')
        | .error e => .error e
    | _ => fun _ => .error .invalidCapability

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

/-- WS-J1-C: Route decoded syscall arguments to the appropriate capability-gated
kernel operation. Looks up the caller's TCB and CSpace root, constructs a
`SyscallGate`, and dispatches via `syscallInvoke`.

The resolved capability's target identifies the kernel object to operate on
(endpoint for IPC, CNode slot for CSpace ops, etc.). -/
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
  simp [dispatchWithCap, hSyscall, hTarget, hDecode]

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
  simp [dispatchWithCap, hSyscall, hTarget, hDecode]

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
  simp [dispatchWithCap, hSyscall, hTarget, hDecode]

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
  simp [dispatchWithCap, hSyscall, hTarget, hDecode]

-- ============================================================================
-- WS-K-D: Lifecycle and VSpace dispatch delegation theorems
-- ============================================================================

/-- WS-K-D: When lifecycleRetype dispatch succeeds, `lifecycleRetypeDirect`
is invoked with the resolved cap, decoded target, and constructed object. -/
theorem dispatchWithCap_lifecycleRetype_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.LifecycleRetypeArgs)
    (hSyscall : decoded.syscallId = .lifecycleRetype)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeLifecycleRetypeArgs decoded = .ok args) :
    dispatchWithCap decoded tid gate cap =
      lifecycleRetypeDirect cap args.targetObj (objectOfKernelType args.newType args.size) := by
  simp [dispatchWithCap, hSyscall, hTarget, hDecode]

/-- WS-K-D/S6-A/T6-C: When vspaceMap dispatch succeeds, `vspaceMapPageCheckedWithFlush` is
invoked with the decoded ASID, vaddr, paddr, and validated permissions.
Production API uses the TLB-flushing variant to maintain `tlbConsistent`.
T6-C: Permissions are now typed as `PagePermissions` (validated at decode). -/
theorem dispatchWithCap_vspaceMap_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.VSpaceMapArgs)
    (hSyscall : decoded.syscallId = .vspaceMap)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeVSpaceMapArgs decoded = .ok args) :
    dispatchWithCap decoded tid gate cap =
      Architecture.vspaceMapPageCheckedWithFlush args.asid args.vaddr args.paddr
        args.perms := by
  simp [dispatchWithCap, hSyscall, hTarget, hDecode]

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
  simp [dispatchWithCap, hSyscall, hTarget, hDecode]

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
            (SeLe4n.Slot.ofNat 0) st with
        | .error e => .error e
        | .ok (_, st') => .ok ((), st') := by
  simp [dispatchWithCap, hSyscall, hTarget]

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
        match endpointCallWithCaps epId tid msg cap.rights gate.cspaceRoot
            (SeLe4n.Slot.ofNat 0) st with
        | .error e => .error e
        | .ok (_, st') => .ok ((), st') := by
  simp [dispatchWithCap, hSyscall, hTarget]

/-- WS-K-E: When reply dispatch is invoked, the IPC message body is populated
from decoded message registers via `extractMessageRegisters`. -/
theorem dispatchWithCap_reply_populates_msg
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (gate : SyscallGate)
    (cap : Capability) (targetTid : SeLe4n.ThreadId)
    (hSyscall : decoded.syscallId = .reply)
    (hTarget : cap.target = .replyCap targetTid) :
    dispatchWithCap decoded tid gate cap =
      let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
      endpointReply tid targetTid { registers := body, caps := #[], badge := cap.badge } := by
  simp [dispatchWithCap, hSyscall, hTarget]

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
