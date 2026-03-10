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
    (newRights : List AccessRight) (newBadge : Option SeLe4n.Badge) : Kernel Unit :=
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

end SeLe4n.Kernel
