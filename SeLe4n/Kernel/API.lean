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
# L-01/WS-E6: Unified Kernel API Surface

This module is the single public entry point for the seLe4n kernel model. It
re-exports all subsystem modules and defines the composed API-level invariant
bundle that aggregates all subsystem invariants.

## Entry-point taxonomy

| Category | Entry points | Module |
|---|---|---|
| **Scheduler** | `schedule`, `handleYield`, `chooseThread`, `timerTick`, `switchDomain`, `scheduleDomain` | `Scheduler.Operations` |
| **Capability** | `cspaceLookupSlot`, `cspaceLookupPath`, `cspaceInsertSlot`, `cspaceMint`, `cspaceCopy`, `cspaceMove`, `cspaceMutate`, `cspaceRevokeCdt` | `Capability.Operations` |
| **IPC** | `endpointSend`, `endpointReceive`, `endpointAwaitReceive`, `endpointSendDual`, `endpointReceiveDual`, `endpointReply`, `endpointCall`, `endpointReplyRecv`, `notificationSignal`, `notificationWait` | `IPC.Operations` |
| **Lifecycle** | `lifecycleRetypeObject`, `lifecycleRevokeDeleteRetype` | `Lifecycle.Operations` |
| **Service** | `serviceStart`, `serviceStop`, `serviceRestart`, `serviceRegisterDependency`, `serviceIsolate` | `Service.Operations` |
| **Architecture** | `adapterAdvanceTimer`, `adapterWriteRegister`, `adapterReadMemory`, `vspaceMapPage`, `vspaceUnmapPage`, `vspaceLookup` | `Architecture.Adapter`, `Architecture.VSpace` |

## Invariant bundles

The `apiInvariantBundle` composes all subsystem invariant bundles into a single
predicate over `SystemState`. It is a synonym for `proofLayerInvariantBundle`
from the Architecture module, ensuring that the API surface and proof surface
use the same composed invariant.
-/

namespace SeLe4n.Kernel.API

open SeLe4n.Model
open SeLe4n.Kernel

/-- L-01/WS-E6: Composed API-level invariant bundle. This is the top-level
invariant that should hold before and after every public kernel API call. It
composes all subsystem invariants:

1. `schedulerInvariantBundle` — queue consistency, uniqueness, current-thread validity
2. `capabilityInvariantBundle` — CNode slot uniqueness, lookup soundness, attenuation
3. `m3IpcSeedInvariantBundle` — IPC endpoint/notification queue invariants
4. `m35IpcSchedulerInvariantBundle` — IPC-scheduler cross-subsystem contract
5. `lifecycleInvariantBundle` — lifecycle metadata consistency
6. `serviceLifecycleCapabilityInvariantBundle` — service graph policy + lifecycle + capability
7. `vspaceInvariantBundle` — ASID uniqueness, mapping non-overlap -/
abbrev apiInvariantBundle := Architecture.proofLayerInvariantBundle

/-- L-01/WS-E6: The default (empty) system state satisfies the API invariant bundle.
This is the base case for invariant induction. -/
theorem apiInvariantBundle_default :
    apiInvariantBundle (default : SystemState) :=
  Architecture.default_system_state_proofLayerInvariantBundle

end SeLe4n.Kernel.API
