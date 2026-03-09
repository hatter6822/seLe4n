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

end SeLe4n.Kernel
