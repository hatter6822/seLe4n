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

/-- Typed boot-boundary contract skeleton consumed by later adapters.
    V4-G/M-HW-6: Extended with substantive boot precondition checks for
    object store validation and IRQ range checking. -/
structure BootBoundaryContract where
  objectTypeMetadataConsistent : Prop
  capabilityRefMetadataConsistent : Prop
  /-- V4-G: Object store must be non-empty after boot (at least idle thread). -/
  objectStoreNonEmpty : Prop := True
  /-- V4-G: All IRQ line numbers must be within the GIC-supported range. -/
  irqRangeValid : Prop := True

/-- Typed runtime-boundary contract skeleton consumed by scheduler/IPC adapters. -/
structure RuntimeBoundaryContract where
  timerMonotonic : SystemState → SystemState → Prop
  registerContextStable : SystemState → SystemState → Prop
  memoryAccessAllowed : SystemState → SeLe4n.PAddr → Prop
  timerMonotonicDecidable : ∀ st st', Decidable (timerMonotonic st st')
  registerContextStableDecidable : ∀ st st', Decidable (registerContextStable st st')
  memoryAccessAllowedDecidable : ∀ st addr, Decidable (memoryAccessAllowed st addr)

/-- Typed interrupt-boundary contract skeleton consumed by IRQ adapter paths.

WS-H15a/M-13: Now includes `Decidable` instance fields matching the pattern
in `RuntimeBoundaryContract`. This enables adapter code to branch on interrupt
predicates at runtime using `if` without manual instance threading. -/
structure InterruptBoundaryContract where
  irqLineSupported : SeLe4n.Irq → Prop
  irqHandlerMapped : SystemState → SeLe4n.Irq → Prop
  irqLineSupportedDecidable : ∀ irq, Decidable (irqLineSupported irq)
  irqHandlerMappedDecidable : ∀ st irq, Decidable (irqHandlerMapped st irq)

/-- WS-H15a/M-13: The `Decidable` instance for `irqLineSupported` agrees with
the predicate: `decide` returns `true` if and only if the predicate holds. -/
theorem irqLineSupported_decidable_consistent
    (contract : InterruptBoundaryContract) (irq : SeLe4n.Irq) :
    @decide (contract.irqLineSupported irq) (contract.irqLineSupportedDecidable irq) = true ↔
    contract.irqLineSupported irq := by
  letI := contract.irqLineSupportedDecidable irq
  constructor
  · intro h; exact of_decide_eq_true h
  · intro h; exact decide_eq_true h

/-- WS-H15a/M-13: The `Decidable` instance for `irqHandlerMapped` agrees with
the predicate. -/
theorem irqHandlerMapped_decidable_consistent
    (contract : InterruptBoundaryContract) (st : SystemState) (irq : SeLe4n.Irq) :
    @decide (contract.irqHandlerMapped st irq) (contract.irqHandlerMappedDecidable st irq) = true ↔
    contract.irqHandlerMapped st irq := by
  letI := contract.irqHandlerMappedDecidable st irq
  constructor
  · intro h; exact of_decide_eq_true h
  · intro h; exact decide_eq_true h


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
