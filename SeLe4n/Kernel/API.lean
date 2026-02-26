import SeLe4n.Kernel.Scheduler.Invariant
import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Kernel.IPC.Operations
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
# WS-E6/L-01: Unified Public Kernel API

This module defines the public interface of the seLe4n kernel model. It
aggregates subsystem operations and invariant bundles into a single entry point
for consumers (executable harness, proof clients, test infrastructure).

## API stability

| Category | Operations | Stability |
|---|---|---|
| **Scheduler** | `schedule`, `handleYield`, `chooseThread`, `tickPreempt`, `timerTick` | Stable |
| **Capability** | `cspaceLookupSlot`, `cspaceLookupPath`, `cspaceInsertSlot`, `cspaceMint`, `cspaceCopy`, `cspaceDeleteSlot`, `cspaceRevoke` | Stable |
| **IPC** | `endpointSend`, `endpointReceive`, `endpointAwaitReceive`, `endpointReply`, `endpointSendDual`, `notificationSignal`, `notificationWait` | Stable |
| **Lifecycle** | `lifecycleRetypeObject`, `lifecycleRevokeDeleteRetype` | Stable |
| **Service** | `serviceStart`, `serviceStop`, `serviceRestart`, `serviceRegisterDependency` | Stable |
| **Architecture** | `adapterAdvanceTimer`, `adapterWriteRegister`, `adapterReadMemory` | Stable |
| **VSpace** | `vspaceMapPage`, `vspaceUnmapPage`, `vspaceLookup` | Stable |
| **Info-flow** | `securityFlowsTo`, `projectState`, `lowEquivalent` | Experimental (WS-E5) |

## Invariant bundles

The composed invariant entrypoint is `proofLayerInvariantBundle` (defined in
`Architecture/Invariant.lean`), which conjoins:
1. `schedulerInvariantBundle` — queue/current consistency, uniqueness
2. `capabilityInvariantBundle` — slot uniqueness, lookup soundness, attenuation
3. `m3IpcSeedInvariantBundle` — scheduler + capability + IPC
4. `m35IpcSchedulerInvariantBundle` — IPC-scheduler coherence
5. `lifecycleInvariantBundle` — metadata consistency
6. `serviceLifecycleCapabilityInvariantBundle` — service policy surface
7. `vspaceInvariantBundle` — ASID uniqueness, non-overlap

## Preconditions

All operations require a well-formed `SystemState`. The default state satisfies
`proofLayerInvariantBundle` (proven by `default_system_state_proofLayerInvariantBundle`).
Operations return `Except KernelError` — error branches leave the state unchanged.
-/

namespace SeLe4n.Kernel.API

open SeLe4n.Model

/-- WS-E6/L-01: API-level invariant bundle that composes the full proof-layer
invariant with the information-flow security policy. This is the top-level
invariant that callers should target. -/
def kernelAPIInvariantBundle (st : SystemState) : Prop :=
  Architecture.proofLayerInvariantBundle st

/-- WS-E6/L-01: The default (empty) system state satisfies the API-level
invariant bundle. This serves as the base case for invariant induction. -/
theorem default_system_state_kernelAPIInvariantBundle :
    kernelAPIInvariantBundle (default : SystemState) :=
  Architecture.default_system_state_proofLayerInvariantBundle

end SeLe4n.Kernel.API
