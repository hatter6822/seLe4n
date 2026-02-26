import SeLe4n.Model.State

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model

/-- Enumerated architecture-facing assumptions extracted in WS-M6-A. -/
inductive ArchAssumption where
  | deterministicTimerProgress
  | deterministicRegisterContext
  | memoryAccessSafety
  | bootObjectTyping
  | irqRoutingTotality
  deriving Repr, DecidableEq

/-- Existing transition/API surfaces that consume architecture-facing assumptions. -/
inductive TransitionSurface where
  | chooseThread
  | schedule
  | handleYield
  | endpointSend
  | endpointAwaitReceive
  | endpointReceive
  | lifecycleRetype
  deriving Repr, DecidableEq

/-- Existing invariant bundles that must remain architecture-neutral. -/
inductive InvariantSurface where
  | schedulerInvariantBundle
  | capabilityInvariantBundle
  | coreIpcInvariantBundle
  | ipcSchedulerCouplingInvariantBundle
  | lifecycleInvariantBundle
  | serviceInvariantBundle
  deriving Repr, DecidableEq

/-- Typed boot-boundary contract skeleton consumed by later adapters. -/
structure BootBoundaryContract where
  objectTypeMetadataConsistent : Prop
  capabilityRefMetadataConsistent : Prop

/-- Typed runtime-boundary contract skeleton consumed by scheduler/IPC adapters. -/
structure RuntimeBoundaryContract where
  timerMonotonic : SystemState → SystemState → Prop
  registerContextStable : SystemState → SystemState → Prop
  memoryAccessAllowed : SystemState → SeLe4n.PAddr → Prop
  timerMonotonicDecidable : ∀ st st', Decidable (timerMonotonic st st')
  registerContextStableDecidable : ∀ st st', Decidable (registerContextStable st st')
  memoryAccessAllowedDecidable : ∀ st addr, Decidable (memoryAccessAllowed st addr)

/-- Typed interrupt-boundary contract skeleton consumed by IRQ adapter paths. -/
structure InterruptBoundaryContract where
  irqLineSupported : SeLe4n.Irq → Prop
  irqHandlerMapped : SystemState → SeLe4n.Irq → Prop

/-- First-class references to extracted boundary contract obligations. -/
inductive ContractRef where
  | bootObjectTypeMetadataConsistent
  | bootCapabilityRefMetadataConsistent
  | runtimeTimerMonotonic
  | runtimeRegisterContextStable
  | runtimeMemoryAccessAllowed
  | interruptIrqLineSupported
  | interruptIrqHandlerMapped
  deriving Repr, DecidableEq

/-- Assumption inventory map: each extracted assumption points to required contract obligations. -/
def assumptionContractMap : ArchAssumption → List ContractRef
  | .deterministicTimerProgress => [.runtimeTimerMonotonic]
  | .deterministicRegisterContext => [.runtimeRegisterContextStable]
  | .memoryAccessSafety => [.runtimeMemoryAccessAllowed]
  | .bootObjectTyping => [.bootObjectTypeMetadataConsistent, .bootCapabilityRefMetadataConsistent]
  | .irqRoutingTotality => [.interruptIrqLineSupported, .interruptIrqHandlerMapped]

/-- Assumption-to-transition mapping extracted from current semantics. -/
def assumptionTransitionMap : ArchAssumption → List TransitionSurface
  | .deterministicTimerProgress => [.chooseThread, .schedule, .handleYield]
  | .deterministicRegisterContext => [.chooseThread, .schedule, .handleYield]
  | .memoryAccessSafety => [.endpointSend, .endpointAwaitReceive, .endpointReceive]
  | .bootObjectTyping => [.lifecycleRetype]
  | .irqRoutingTotality => [.handleYield]

/-- Assumption-to-invariant mapping extracted from current theorem bundles. -/
def assumptionInvariantMap : ArchAssumption → List InvariantSurface
  | .deterministicTimerProgress => [.schedulerInvariantBundle]
  | .deterministicRegisterContext => [.schedulerInvariantBundle, .ipcSchedulerCouplingInvariantBundle]
  | .memoryAccessSafety => [.coreIpcInvariantBundle, .ipcSchedulerCouplingInvariantBundle]
  | .bootObjectTyping => [.capabilityInvariantBundle, .lifecycleInvariantBundle]
  | .irqRoutingTotality => [.schedulerInvariantBundle, .serviceInvariantBundle]

/-- Canonical WS-M6-A inventory list used by docs/tests for discoverability checks. -/
def assumptionInventory : List ArchAssumption :=
  [ .deterministicTimerProgress
  , .deterministicRegisterContext
  , .memoryAccessSafety
  , .bootObjectTyping
  , .irqRoutingTotality
  ]

/-- Boundary extraction completeness marker for WS-M6-A. -/
def assumptionInventoryComplete : Prop :=
  ∀ a, a ∈ assumptionInventory

theorem assumptionInventoryComplete_holds : assumptionInventoryComplete := by
  intro a
  cases a <;> simp [assumptionInventory]

/-- Every extracted assumption has at least one boundary-contract obligation. -/
theorem assumptionContractMap_nonempty (a : ArchAssumption) : (assumptionContractMap a).length > 0 := by
  cases a <;> decide

/-- Every extracted assumption maps to at least one transition-level touchpoint. -/
theorem assumptionTransitionMap_nonempty (a : ArchAssumption) : (assumptionTransitionMap a).length > 0 := by
  cases a <;> decide

/-- Every extracted assumption maps to at least one invariant-level touchpoint. -/
theorem assumptionInvariantMap_nonempty (a : ArchAssumption) : (assumptionInvariantMap a).length > 0 := by
  cases a <;> decide

-- ============================================================================
-- M-08/WS-E6: Assumption consumption documentation
-- ============================================================================

/-! ## M-08/WS-E6: How assumptions are consumed

Each architecture assumption above is not merely declared — it is actively
consumed by the adapter preservation proofs in `Invariant.lean`. The consumption
chain works as follows:

1. **Declaration** (this file): Each `ArchAssumption` enumerates a hardware
   property the model relies on.
2. **Contract** (this file): `RuntimeBoundaryContract` and companions encode
   the assumption as a typed, decidable predicate.
3. **Adapter** (`Adapter.lean`): Each adapter operation (`adapterAdvanceTimer`,
   etc.) checks the relevant contract predicate at runtime, failing with
   `unsupportedBinding` if the assumption is violated.
4. **Preservation** (`Invariant.lean`): `AdapterProofHooks` requires a proof
   that the invariant bundle is preserved when the contract holds. The
   consumption bridge theorems (`deterministicTimerProgress_consumed_by_advanceTimer`,
   etc.) witness this chain explicitly.

This four-step chain ensures every declared assumption has a concrete proof-level
consumer, closing the gap identified in finding M-08. -/

end SeLe4n.Kernel.Architecture
