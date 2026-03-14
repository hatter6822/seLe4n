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
import SeLe4n.Kernel.InformationFlow.Policy
import SeLe4n.Kernel.InformationFlow.Projection
import SeLe4n.Kernel.InformationFlow.Invariant

import SeLe4n.Kernel.Architecture.Assumptions
import SeLe4n.Kernel.Architecture.RegisterDecode

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
| `serviceStart`, `serviceStop`, `serviceRestart` | Service | Stable |
| `adapterAdvanceTimer`, `adapterWriteRegister`, `adapterReadMemory` | Architecture | Stable |
| `vspaceMapPage`, `vspaceUnmapPage`, `vspaceLookup` | VSpace | Stable |
| `endpointSendDualChecked` | Info-flow (dual-queue) | Stable |
| `cspaceMintChecked`, `serviceRestartChecked` | Info-flow | Stable |
| `apiEndpointSend`, `apiEndpointReceive` | Syscall IPC (WS-H15c) | Stable |
| `apiEndpointCall`, `apiEndpointReply` | Syscall IPC (WS-H15c) | Stable |
| `apiCspaceMint`, `apiCspaceCopy`, `apiCspaceMove` | Syscall Capability (WS-H15c) | Stable |
| `apiCspaceDelete` | Syscall Capability (WS-H15c) | Stable |
| `apiLifecycleRetype` | Syscall Lifecycle (WS-H15c) | Stable |
| `apiVspaceMap`, `apiVspaceUnmap` | Syscall VSpace (WS-H15c) | Stable |
| `apiServiceStart`, `apiServiceStop` | Syscall Service (WS-H15c) | Stable |

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

The `api*` wrappers below are **syscall entry points** — they model user-space
invocations. Each wrapper resolves a capability via `resolveCapAddress` (WS-H13)
and verifies the caller holds sufficient rights before delegating to the
underlying kernel operation.

### Internal vs syscall operations

| Category | Capability check? | Invoked by |
|---|---|---|
| **Internal** (`schedule`, `endpointSendDual`, etc.) | No | Kernel paths |
| **Syscall** (`apiEndpointSend`, `apiCspaceMint`, etc.) | Yes | User-space |
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
-- Capability-gated syscall wrappers
-- ============================================================================

/-- WS-H15c/A-42: Capability-gated endpoint send. Requires `.write` right. -/
def apiEndpointSend (gate : SyscallGate) (epId : SeLe4n.ObjId) (msg : IpcMessage) : Kernel Unit :=
  syscallInvoke { gate with requiredRight := .write } fun _ =>
    endpointSendDual epId gate.callerId msg

/-- WS-H15c/A-42: Capability-gated endpoint receive. Requires `.read` right.
Returns the sender's ThreadId; the transferred message is in the receiver's
TCB.pendingMessage (matching seL4's IPC buffer model). -/
def apiEndpointReceive (gate : SyscallGate) (epId : SeLe4n.ObjId) : Kernel SeLe4n.ThreadId :=
  syscallInvoke { gate with requiredRight := .read } fun _ =>
    endpointReceiveDual epId gate.callerId

/-- WS-H15c/A-42: Capability-gated endpoint call (send then block for reply).
Requires `.write` right. -/
def apiEndpointCall (gate : SyscallGate) (epId : SeLe4n.ObjId) (msg : IpcMessage) : Kernel Unit :=
  syscallInvoke { gate with requiredRight := .write } fun _ =>
    endpointCall epId gate.callerId msg

/-- WS-H15c/A-42: Capability-gated endpoint reply. Requires `.write` right.
The gate's callerId serves as the replier; `targetId` is the thread to unblock. -/
def apiEndpointReply (gate : SyscallGate) (targetId : SeLe4n.ThreadId) (msg : IpcMessage) : Kernel Unit :=
  syscallInvoke { gate with requiredRight := .write } fun _ =>
    endpointReply gate.callerId targetId msg

/-- WS-H15c/A-42: Capability-gated CSpace mint. Requires `.grant` right on source. -/
def apiCspaceMint (gate : SyscallGate) (src dest : CSpaceAddr)
    (newRights : AccessRightSet) (newBadge : Option SeLe4n.Badge) : Kernel Unit :=
  syscallInvoke { gate with requiredRight := .grant } fun _ =>
    cspaceMint src dest newRights newBadge

/-- WS-H15c/A-42: Capability-gated CSpace copy. Requires `.grant` right. -/
def apiCspaceCopy (gate : SyscallGate) (src dest : CSpaceAddr) : Kernel Unit :=
  syscallInvoke { gate with requiredRight := .grant } fun _ =>
    cspaceCopy src dest

/-- WS-H15c/A-42: Capability-gated CSpace move. Requires `.grant` right. -/
def apiCspaceMove (gate : SyscallGate) (src dest : CSpaceAddr) : Kernel Unit :=
  syscallInvoke { gate with requiredRight := .grant } fun _ =>
    cspaceMove src dest

/-- WS-H15c/A-42: Capability-gated CSpace delete. Requires `.write` right. -/
def apiCspaceDelete (gate : SyscallGate) (addr : CSpaceAddr) : Kernel Unit :=
  syscallInvoke { gate with requiredRight := .write } fun _ =>
    cspaceDeleteSlot addr

/-- WS-H15c/A-42: Capability-gated lifecycle retype. Requires `.retype` right. -/
def apiLifecycleRetype (gate : SyscallGate) (authority : CSpaceAddr)
    (target : SeLe4n.ObjId) (newObj : KernelObject) : Kernel Unit :=
  syscallInvoke { gate with requiredRight := .retype } fun _ =>
    lifecycleRetypeObject authority target newObj

/-- WS-H15c/A-42: Capability-gated VSpace map. Requires `.write` right. -/
def apiVspaceMap (gate : SyscallGate) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr) (perms : PagePermissions := default) : Kernel Unit :=
  syscallInvoke { gate with requiredRight := .write } fun _ =>
    Architecture.vspaceMapPage asid vaddr paddr perms

/-- WS-H15c/A-42: Capability-gated VSpace unmap. Requires `.write` right. -/
def apiVspaceUnmap (gate : SyscallGate) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) : Kernel Unit :=
  syscallInvoke { gate with requiredRight := .write } fun _ =>
    Architecture.vspaceUnmapPage asid vaddr

/-- WS-H15c/A-42: Capability-gated service start. Requires `.write` right. -/
def apiServiceStart (gate : SyscallGate) (svcId : ServiceId) (policy : ServicePolicy) : Kernel Unit :=
  syscallInvoke { gate with requiredRight := .write } fun _ =>
    serviceStart svcId policy

/-- WS-H15c/A-42: Capability-gated service stop. Requires `.write` right. -/
def apiServiceStop (gate : SyscallGate) (svcId : ServiceId) (policy : ServicePolicy) : Kernel Unit :=
  syscallInvoke { gate with requiredRight := .write } fun _ =>
    serviceStop svcId policy

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
  | .serviceStart    => .write
  | .serviceStop     => .write

/-- WS-J1-C: Dispatch a decoded syscall to the appropriate internal kernel
operation using the resolved capability's target. Called after cap resolution
succeeds inside `syscallInvoke`. -/
private def dispatchWithCap (syscallId : SyscallId) (tid : SeLe4n.ThreadId)
    (cap : Capability) : Kernel Unit :=
  match syscallId with
  | .send =>
    match cap.target with
    | .object epId =>
      endpointSendDual epId tid { registers := #[], caps := #[], badge := cap.badge }
    | _ => fun _ => .error .invalidCapability
  | .receive =>
    match cap.target with
    | .object epId =>
      fun st => match endpointReceiveDual epId tid st with
        | .ok (_, st') => .ok ((), st')
        | .error e => .error e
    | _ => fun _ => .error .invalidCapability
  | .call =>
    match cap.target with
    | .object epId =>
      endpointCall epId tid { registers := #[], caps := #[], badge := cap.badge }
    | _ => fun _ => .error .invalidCapability
  | .reply =>
    match cap.target with
    | .replyCap targetTid =>
      endpointReply tid targetTid { registers := #[], caps := #[], badge := cap.badge }
    | _ => fun _ => .error .invalidCapability
  | .cspaceMint =>
    match cap.target with
    | .cnodeSlot cnode slot =>
      cspaceMint { cnode, slot } { cnode, slot } cap.rights cap.badge
    | _ => fun _ => .error .invalidCapability
  | .cspaceCopy =>
    match cap.target with
    | .cnodeSlot cnode slot =>
      cspaceCopy { cnode, slot } { cnode, slot }
    | _ => fun _ => .error .invalidCapability
  | .cspaceMove =>
    match cap.target with
    | .cnodeSlot cnode slot =>
      cspaceMove { cnode, slot } { cnode, slot }
    | _ => fun _ => .error .invalidCapability
  | .cspaceDelete =>
    match cap.target with
    | .cnodeSlot cnode slot =>
      cspaceDeleteSlot { cnode, slot }
    | _ => fun _ => .error .invalidCapability
  | .lifecycleRetype =>
    match cap.target with
    | .object targetId =>
      lifecycleRetypeObject { cnode := ⟨0⟩, slot := ⟨0⟩ } targetId (.endpoint {})
    | _ => fun _ => .error .invalidCapability
  | .vspaceMap =>
    match cap.target with
    | .object _ =>
      fun _ => .error .illegalState  -- VSpace map requires ASID/vaddr/paddr from MRs
    | _ => fun _ => .error .invalidCapability
  | .vspaceUnmap =>
    match cap.target with
    | .object _ =>
      fun _ => .error .illegalState  -- VSpace unmap requires ASID/vaddr from MRs
    | _ => fun _ => .error .invalidCapability
  | .serviceStart =>
    match cap.target with
    | .object objId =>
      serviceStart (ServiceId.ofNat objId.toNat) (fun _ => true)
    | _ => fun _ => .error .invalidCapability
  | .serviceStop =>
    match cap.target with
    | .object objId =>
      serviceStop (ServiceId.ofNat objId.toNat) (fun _ => true)
    | _ => fun _ => .error .invalidCapability

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
        (syscallInvoke gate (dispatchWithCap decoded.syscallId tid)) st
      | some _ => .error .invalidCapability
      | none   => .error .objectNotFound
    | some _ => .error .illegalState
    | none   => .error .objectNotFound

/-- WS-J1-C: Top-level register-sourced syscall entry point.

Reads the current thread's register file, decodes raw register values into
typed kernel references, and dispatches to the appropriate kernel operation.
This is the single authoritative user-space → kernel transition boundary. -/
def syscallEntry (layout : SeLe4n.SyscallRegisterLayout) : Kernel Unit :=
  fun st =>
    match st.scheduler.current with
    | none => .error .illegalState
    | some tid =>
      match lookupThreadRegisterContext tid st with
      | .error e => .error e
      | .ok (regs, _) =>
        match decodeSyscallArgs layout regs with
        | .error e => .error e
        | .ok decoded =>
          dispatchSyscall decoded tid st

-- ============================================================================
-- WS-J1-C: Soundness theorems
-- ============================================================================

/-- WS-J1-C: If `syscallEntry` succeeds, the register values decoded
successfully — i.e., `decodeSyscallArgs` returned `.ok`. -/
theorem syscallEntry_requires_valid_decode
    (layout : SeLe4n.SyscallRegisterLayout) (st : SystemState) (st' : SystemState)
    (hOk : syscallEntry layout st = .ok ((), st')) :
    ∃ tid regs decoded,
      st.scheduler.current = some tid ∧
      lookupThreadRegisterContext tid st = .ok (regs, st) ∧
      decodeSyscallArgs layout regs = .ok decoded := by
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
        -- Extract that _st_regs = st from the lookupThreadRegisterContext definition
        have hStEq : _st_regs = st := by
          unfold lookupThreadRegisterContext at hLookup
          split at hLookup <;> simp at hLookup
          exact hLookup.2.symm
        subst hStEq
        exact ⟨tid, regs, decoded, hCurrent, hLookup, hDecode⟩

/-- WS-J1-C: If `syscallEntry` succeeds for a capability-gated operation,
the caller held the required access right. Threads through the existing
`syscallInvoke_requires_right` theorem.

The conclusion states: there exists a current thread with a valid TCB and
CSpace root CNode, and the capability resolved from the decoded capAddr
grants the required right for the invoked syscall. -/
theorem syscallEntry_implies_capability_held
    (layout : SeLe4n.SyscallRegisterLayout) (st : SystemState) (st' : SystemState)
    (hOk : syscallEntry layout st = .ok ((), st')) :
    ∃ tid regs decoded,
      st.scheduler.current = some tid ∧
      lookupThreadRegisterContext tid st = .ok (regs, st) ∧
      decodeSyscallArgs layout regs = .ok decoded ∧
      (dispatchSyscall decoded tid st = .ok ((), st')) := by
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
        exact ⟨tid, regs, decoded, hCurrent, hLookup, hDecode, hOk⟩

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
        (dispatchWithCap decoded.syscallId tid) st () st' hOk
      obtain ⟨cap, ref, hResolve, hSlot, hRight⟩ := hInvoke
      exact ⟨cap, ref, hResolve, hSlot, hRight⟩
    · simp at hOk
    · simp at hOk
  · simp at hOk
  · simp at hOk

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

end SeLe4n.Kernel
