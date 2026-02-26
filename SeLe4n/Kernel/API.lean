-- Subsystem re-exports (unchanged from prior barrel)
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
# Unified Kernel API (L-01/WS-E6)

This module defines the public kernel API surface, composing entry-point
operations from all kernel subsystems into a unified interface with an
API-level invariant bundle.

Previously this file was a bare barrel of imports. L-01/WS-E6 expands it
to define:
1. **Re-exports** of all kernel subsystem modules (unchanged).
2. **`KernelAPIInvariant`**: the composed API-level invariant bundle that
   clients must establish before calling and that operations must preserve.
3. **Entry-point wrappers** that provide a stable, discoverable API surface
   for each kernel operation family (scheduler, capability, IPC, lifecycle,
   service, architecture).
4. **API-level preservation theorem** showing the composed invariant bundle
   is equivalent to `proofLayerInvariantBundle`.
-/

namespace SeLe4n.Kernel.API

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Architecture

-- ============================================================================
-- L-01/WS-E6: API-level invariant bundle
-- ============================================================================

/-- L-01/WS-E6: The API-level invariant bundle is the canonical entry
requirement for all public kernel operations. It composes all subsystem
invariant bundles through `proofLayerInvariantBundle`.

Clients establishing a valid `SystemState` must satisfy this predicate.
All kernel API operations preserve it (when they succeed). -/
abbrev KernelAPIInvariant (st : SystemState) : Prop :=
  proofLayerInvariantBundle st

/-- L-01/WS-E6: The API invariant bundle is precisely the composed proof-layer
invariant bundle. This identity allows clients to use either name. -/
theorem kernelAPIInvariant_eq_proofLayerInvariantBundle (st : SystemState) :
    KernelAPIInvariant st ↔ proofLayerInvariantBundle st :=
  Iff.rfl

/-- L-01/WS-E6: The default (empty) system state satisfies the API invariant. -/
theorem default_satisfies_kernelAPIInvariant :
    KernelAPIInvariant (default : SystemState) :=
  default_system_state_proofLayerInvariantBundle

-- ============================================================================
-- L-01/WS-E6: Scheduler API entry points
-- ============================================================================

/-- Schedule the next runnable thread. See `Kernel.schedule`. -/
abbrev apiSchedule : Kernel Unit := schedule

/-- Yield the current thread's CPU time. See `Kernel.handleYield`. -/
abbrev apiHandleYield : Kernel Unit := handleYield

/-- M-04/WS-E6: Handle a timer tick (time-slice preemption).
See `Kernel.handleTimerTick`. -/
abbrev apiHandleTimerTick : Kernel Unit := handleTimerTick

/-- M-05/WS-E6: Handle a domain scheduling tick.
See `Kernel.handleDomainTick`. -/
abbrev apiHandleDomainTick (sched : List DomainScheduleEntry) : Kernel Unit :=
  handleDomainTick sched

-- ============================================================================
-- L-01/WS-E6: Capability API entry points
-- ============================================================================

/-- Mint a derived capability. See `Kernel.cspaceMint`. -/
abbrev apiCspaceMint := @cspaceMint

/-- Copy a capability with CDT edge. See `Kernel.cspaceCopy`. -/
abbrev apiCspaceCopy := @cspaceCopy

/-- Move a capability with CDT reparenting. See `Kernel.cspaceMove`. -/
abbrev apiCspaceMove := @cspaceMove

/-- Mutate capability rights in-place. See `Kernel.cspaceMutate`. -/
abbrev apiCspaceMutate := @cspaceMutate

/-- Revoke via CDT traversal. See `Kernel.cspaceRevokeCdt`. -/
abbrev apiCspaceRevokeCdt := @cspaceRevokeCdt

-- ============================================================================
-- L-01/WS-E6: IPC API entry points
-- ============================================================================

/-- Send a message on an endpoint. See `Kernel.endpointSend`. -/
abbrev apiEndpointSend := @endpointSend

/-- Receive from an endpoint. See `Kernel.endpointReceive`. -/
abbrev apiEndpointReceive := @endpointReceive

/-- Reply to a blocked sender. See `Kernel.endpointReply`. -/
abbrev apiEndpointReply := @endpointReply

/-- Atomic call (send + block for reply). See `Kernel.endpointCall`. -/
abbrev apiEndpointCall := @endpointCall

-- ============================================================================
-- L-01/WS-E6: Service API entry points
-- ============================================================================

/-- Start a service. See `Kernel.serviceStart`. -/
abbrev apiServiceStart := @serviceStart

/-- Stop a running service. See `Kernel.serviceStop`. -/
abbrev apiServiceStop := @serviceStop

/-- Restart a service (stop + start). See `Kernel.serviceRestart`. -/
abbrev apiServiceRestart := @serviceRestart

-- ============================================================================
-- L-01/WS-E6: Architecture adapter API entry points
-- ============================================================================

/-- Advance the machine timer. See `Architecture.adapterAdvanceTimer`. -/
abbrev apiAdapterAdvanceTimer := @adapterAdvanceTimer

/-- Write a machine register. See `Architecture.adapterWriteRegister`. -/
abbrev apiAdapterWriteRegister := @adapterWriteRegister

/-- Read from physical memory. See `Architecture.adapterReadMemory`. -/
abbrev apiAdapterReadMemory := @adapterReadMemory

/-- Map a virtual page. See `Architecture.vspaceMapPage`. -/
abbrev apiVspaceMapPage := @vspaceMapPage

/-- Unmap a virtual page. See `Architecture.vspaceUnmapPage`. -/
abbrev apiVspaceUnmapPage := @vspaceUnmapPage

/-- Resolve a virtual address. See `Architecture.vspaceLookup`. -/
abbrev apiVspaceLookup := @vspaceLookup

-- ============================================================================
-- L-01/WS-E6: API preservation theorems
-- ============================================================================

/-- L-01/WS-E6: `apiSchedule` preserves the scheduler invariant bundle. -/
theorem apiSchedule_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (hInv : schedulerInvariantBundle st)
    (hStep : apiSchedule st = .ok ((), st')) :
    schedulerInvariantBundle st' :=
  schedule_preserves_schedulerInvariantBundle st st' hInv hStep

/-- L-01/WS-E6: `apiHandleYield` preserves the scheduler invariant bundle. -/
theorem apiHandleYield_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (hInv : schedulerInvariantBundle st)
    (hStep : apiHandleYield st = .ok ((), st')) :
    schedulerInvariantBundle st' :=
  handleYield_preserves_schedulerInvariantBundle st st' hInv hStep

/-- L-01/WS-E6: `apiHandleDomainTick` preserves the scheduler invariant bundle. -/
theorem apiHandleDomainTick_preserves_schedulerInvariantBundle
    (sched : List DomainScheduleEntry)
    (st st' : SystemState)
    (hInv : schedulerInvariantBundle st)
    (hStep : apiHandleDomainTick sched st = .ok ((), st')) :
    schedulerInvariantBundle st' :=
  handleDomainTick_preserves_schedulerInvariantBundle sched st st' hInv hStep

end SeLe4n.Kernel.API
