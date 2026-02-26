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
# L-01/WS-E6: Unified Kernel Public API

This module defines the coherent public surface for the seLe4n kernel model.
Prior to WS-E6, `API.lean` was a bare import aggregator. It now provides:

1. **Re-exported subsystem imports** — all kernel subsystems are reachable through
   a single `import SeLe4n.Kernel.API`.
2. **`apiInvariantBundle`** — a composed invariant predicate that represents the
   full proof obligation for any kernel transition visible to external callers.
3. **`KernelAPI` namespace** — canonical aliases for all public-facing kernel
   transitions, providing a single discovery point and stable API surface.

## Design note

The aliases in `KernelAPI` are intentionally `abbrev`s (not `def`s) so they
unfold transparently in proofs. This means existing subsystem-level preservation
theorems apply directly without additional unfolding lemmas.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- L-01/WS-E6: Composed API-level invariant bundle
-- ============================================================================

/-- L-01/WS-E6: API-level invariant bundle.

This is the top-level composed invariant that must hold before and after every
public kernel transition. It includes all subsystem invariant bundles from the
`proofLayerInvariantBundle` (scheduler, capability, IPC, lifecycle, service,
VSpace) and is semantically equivalent to it.

External callers should use this as the single entry-point predicate for
reasoning about kernel state validity. -/
abbrev apiInvariantBundle (st : SystemState) : Prop :=
  Architecture.proofLayerInvariantBundle st

/-- L-01/WS-E6: The default (empty) system state satisfies the API invariant bundle. -/
theorem default_system_state_apiInvariantBundle :
    apiInvariantBundle (default : SystemState) :=
  Architecture.default_system_state_proofLayerInvariantBundle

-- ============================================================================
-- L-01/WS-E6: Kernel public API namespace
-- ============================================================================

-- L-01/WS-E6: Canonical public-facing kernel transition surface.
--
-- All transitions that external callers (userspace model, test harness, or
-- future refinement layers) should invoke are aliased here. Internal helpers
-- (e.g., `chooseBestRunnable`, `storeTcbIpcState`, `removeRunnable`) are
-- intentionally excluded.
namespace KernelAPI

-- Scheduler transitions
abbrev schedule := @Kernel.schedule
abbrev chooseThread := @Kernel.chooseThread
abbrev handleYield := @Kernel.handleYield
abbrev timerTick := @Kernel.timerTick
abbrev nextDomain := @Kernel.nextDomain
abbrev chooseThreadDomain := @Kernel.chooseThreadDomain

-- Capability / CSpace transitions
abbrev cspaceLookupPath := @Kernel.cspaceLookupPath
abbrev cspaceLookupSlot := @Kernel.cspaceLookupSlot
abbrev cspaceMint := @Kernel.cspaceMint
abbrev cspaceInsertSlot := @Kernel.cspaceInsertSlot
abbrev cspaceDeleteSlot := @Kernel.cspaceDeleteSlot
abbrev cspaceRevoke := @Kernel.cspaceRevoke
abbrev cspaceCopy := @Kernel.cspaceCopy
abbrev cspaceMove := @Kernel.cspaceMove
abbrev cspaceMutate := @Kernel.cspaceMutate
abbrev cspaceMintWithCdt := @Kernel.cspaceMintWithCdt
abbrev cspaceRevokeCdt := @Kernel.cspaceRevokeCdt

-- IPC transitions (legacy single-queue)
abbrev endpointSend := @Kernel.endpointSend
abbrev endpointAwaitReceive := @Kernel.endpointAwaitReceive
abbrev endpointReceive := @Kernel.endpointReceive
abbrev notificationSignal := @Kernel.notificationSignal
abbrev notificationWait := @Kernel.notificationWait

-- IPC transitions (dual-queue / bidirectional)
abbrev endpointSendDual := @Kernel.endpointSendDual
abbrev endpointReceiveDual := @Kernel.endpointReceiveDual
abbrev endpointCall := @Kernel.endpointCall
abbrev endpointReply := @Kernel.endpointReply
abbrev endpointReplyRecv := @Kernel.endpointReplyRecv

-- Lifecycle transitions
abbrev lifecycleRetypeObject := @Kernel.lifecycleRetypeObject
abbrev lifecycleRevokeDeleteRetype := @Kernel.lifecycleRevokeDeleteRetype

-- Service transitions
abbrev serviceStart := @Kernel.serviceStart
abbrev serviceStop := @Kernel.serviceStop
abbrev serviceRestart := @Kernel.serviceRestart
abbrev serviceRegisterDependency := @Kernel.serviceRegisterDependency

-- VSpace transitions
abbrev vspaceMapPage := @Architecture.vspaceMapPage
abbrev vspaceUnmapPage := @Architecture.vspaceUnmapPage
abbrev vspaceLookup := @Architecture.vspaceLookup

-- Architecture adapter transitions
abbrev adapterAdvanceTimer := @Architecture.adapterAdvanceTimer
abbrev adapterWriteRegister := @Architecture.adapterWriteRegister
abbrev adapterReadMemory := @Architecture.adapterReadMemory

end KernelAPI

end SeLe4n.Kernel
