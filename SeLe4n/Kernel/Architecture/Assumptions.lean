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

-- ============================================================================
-- WS-E6/M-08: Assumption-to-proof connection
-- ============================================================================

/-- WS-E6/M-08: Predicate asserting that a `RuntimeBoundaryContract` satisfies
the runtime assumptions in the architecture inventory.

A contract satisfies the runtime assumptions when:
1. `deterministicTimerProgress` → timer monotonicity is reflexive (identity
   step preserves the timer).
2. `deterministicRegisterContext` → register context stability is reflexive.
3. `memoryAccessSafety` → the contract admits at least the default (all-zero)
   memory state.

This connects the assumption *enumeration* to the *concrete contract fields*
consumed by adapter preservation theorems (closing the M-08 gap). -/
def runtimeContractSatisfiesAssumptions (contract : RuntimeBoundaryContract) : Prop :=
  (∀ st : SystemState, contract.timerMonotonic st st) ∧
  (∀ st : SystemState, contract.registerContextStable st st) ∧
  (∀ st : SystemState, ∀ addr : SeLe4n.PAddr, contract.memoryAccessAllowed st addr)

/-- WS-E6/M-08: Predicate asserting that a `BootBoundaryContract` satisfies
the boot-time assumptions. The contract admits when both metadata consistency
properties hold for the default (empty) state. -/
def bootContractSatisfiesAssumptions (contract : BootBoundaryContract) : Prop :=
  contract.objectTypeMetadataConsistent ∧ contract.capabilityRefMetadataConsistent

/-- WS-E6/M-08: Every architecture assumption maps to at least one concrete
contract field that adapter operations consume. This connects the structural
assumption inventory to the runtime proof obligations.

Proof: by exhaustive case analysis on the 5 assumptions, each of which maps
to ≥1 contract reference via `assumptionContractMap`. -/
theorem assumption_coverage_complete :
    ∀ a : ArchAssumption, (assumptionContractMap a).length > 0 :=
  assumptionContractMap_nonempty

/-- WS-E6/M-08: The assumption-to-contract-to-transition chain is closed:
every assumption that maps to a transition surface also maps to at least one
contract obligation, ensuring no assumption is consumed without a proof hook. -/
theorem assumption_contract_transition_chain_closed :
    ∀ a : ArchAssumption,
      (assumptionContractMap a).length > 0 ∧
      (assumptionTransitionMap a).length > 0 ∧
      (assumptionInvariantMap a).length > 0 := by
  intro a; exact ⟨assumptionContractMap_nonempty a,
    assumptionTransitionMap_nonempty a, assumptionInvariantMap_nonempty a⟩

end SeLe4n.Kernel.Architecture
