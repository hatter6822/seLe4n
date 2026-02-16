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
  | m3IpcSeedInvariantBundle
  | m35IpcSchedulerInvariantBundle
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
  | .deterministicRegisterContext => [.schedulerInvariantBundle, .m35IpcSchedulerInvariantBundle]
  | .memoryAccessSafety => [.m3IpcSeedInvariantBundle, .m35IpcSchedulerInvariantBundle]
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

end SeLe4n.Kernel.Architecture
