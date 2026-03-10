/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

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
  | endpointSendDual
  | endpointReceiveDual
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
  | .memoryAccessSafety => [.endpointSendDual, .endpointReceiveDual]
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

-- ============================================================================
-- H3 preparation: Extended boot boundary contract
-- ============================================================================

/-- H3-prep: Exception level at which the kernel receives control from the
    bootloader. Relevant for ARM64 platforms where EL1 vs EL2 entry
    determines available system registers and MMU configuration. -/
inductive ExceptionLevel where
  | el1
  | el2
  deriving Repr, DecidableEq

/-- H3-prep: Extended boot boundary contract with platform-specific fields.

    The base `BootBoundaryContract` declares abstract consistency propositions.
    `ExtendedBootBoundaryContract` adds platform-visible boot parameters that
    the H3 workstream needs:

    - **Entry exception level**: EL1 or EL2 (determines available system regs).
    - **Initial page table state**: Whether the MMU is identity-mapped at entry.
    - **Device tree location**: Physical address of the DTB.
    - **Kernel entry point**: Physical address of the kernel's `_start` symbol.
    - **Initial stack pointer**: Physical address of the initial kernel stack.

    The base `BootBoundaryContract` is embedded, so all existing proofs that
    depend on it continue to work through the `.base` projection. -/
structure ExtendedBootBoundaryContract extends BootBoundaryContract where
  /-- Exception level at kernel entry. -/
  entryLevel : ExceptionLevel
  /-- Whether the MMU is identity-mapped at kernel entry. -/
  mmuIdentityMapped : Bool
  /-- Physical address of the device tree blob. -/
  deviceTreeBase : SeLe4n.PAddr
  /-- Physical address of the kernel entry point (`_start`). -/
  kernelEntryPoint : SeLe4n.PAddr
  /-- Physical address of the initial kernel stack top. -/
  initialStackPointer : SeLe4n.PAddr

end SeLe4n.Kernel.Architecture
