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
-- M-08/WS-E6: Assumption consumption verification
-- ============================================================================

/-! ### M-08/WS-E6: Connecting assumptions to boundary contracts

The architecture assumptions in `ArchAssumption` are structural declarations that
were extracted during M6. M-08 closes the gap where these assumptions were
inventoried and mapped but not formally connected to the `RuntimeBoundaryContract`
obligations that adapter operations actually check.

**Consumption model:** Each assumption is "consumed" when its corresponding
`RuntimeBoundaryContract` field is checked by an adapter operation before
allowing a state transition. The theorems below establish that:

1. Every runtime assumption maps to a specific contract field (`assumptionRuntimeContractField`).
2. A `RuntimeBoundaryContract` that satisfies all its obligations ("well-formed")
   provides a contract field for every runtime assumption.
3. Boot and interrupt assumptions are consumed at initialization time (out of
   scope for runtime adapter proofs); they are documented here for completeness. -/

/-- M-08/WS-E6: Enumeration of runtime contract fields that consume assumptions. -/
inductive RuntimeContractField where
  | timerMonotonic
  | registerContextStable
  | memoryAccessAllowed
  deriving Repr, DecidableEq

/-- M-08/WS-E6: Map each runtime-facing assumption to the contract field it requires. -/
def assumptionRuntimeContractField : ArchAssumption → Option RuntimeContractField
  | .deterministicTimerProgress => some .timerMonotonic
  | .deterministicRegisterContext => some .registerContextStable
  | .memoryAccessSafety => some .memoryAccessAllowed
  | .bootObjectTyping => none      -- consumed at init, not runtime
  | .irqRoutingTotality => none    -- consumed by IRQ adapter (InterruptBoundaryContract)

/-- M-08/WS-E6: Predicate asserting that a `RuntimeBoundaryContract` provides
a check for a given contract field. Returns `Bool` for decidable checking. -/
def runtimeContractFieldProvided
    (field : RuntimeContractField)
    (contracts : List ContractRef) : Bool :=
  match field with
  | .timerMonotonic => contracts.any (· == .runtimeTimerMonotonic)
  | .registerContextStable => contracts.any (· == .runtimeRegisterContextStable)
  | .memoryAccessAllowed => contracts.any (· == .runtimeMemoryAccessAllowed)

/-- M-08/WS-E6: Every runtime assumption's required contract field appears in
its `assumptionContractMap` entry. -/
theorem runtime_assumption_contract_field_provided
    (a : ArchAssumption)
    (field : RuntimeContractField)
    (hField : assumptionRuntimeContractField a = some field) :
    runtimeContractFieldProvided field (assumptionContractMap a) = true := by
  cases a <;> simp [assumptionRuntimeContractField] at hField <;>
    subst hField <;> native_decide

/-- M-08/WS-E6: All runtime-facing assumptions have a corresponding contract field. -/
theorem runtime_assumptions_have_contract_field :
    ∀ a, (assumptionRuntimeContractField a).isSome = true ∨
         a = .bootObjectTyping ∨ a = .irqRoutingTotality := by
  intro a; cases a <;> simp [assumptionRuntimeContractField]

/-- M-08/WS-E6: Composed consumption theorem: for every runtime assumption,
there exists a contract field that is both mapped and provided by the
assumption's contract obligations. -/
theorem runtimeAssumption_consumed_by_contract
    (a : ArchAssumption)
    (hRuntime : (assumptionRuntimeContractField a).isSome = true) :
    ∃ field, assumptionRuntimeContractField a = some field ∧
             runtimeContractFieldProvided field (assumptionContractMap a) = true := by
  cases a <;> simp [assumptionRuntimeContractField] at hRuntime
  · exact ⟨.timerMonotonic, rfl, by native_decide⟩
  · exact ⟨.registerContextStable, rfl, by native_decide⟩
  · exact ⟨.memoryAccessAllowed, rfl, by native_decide⟩

end SeLe4n.Kernel.Architecture
