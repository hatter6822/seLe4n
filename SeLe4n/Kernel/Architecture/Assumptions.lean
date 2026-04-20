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
    object store validation and IRQ range checking.

    AJ3-D (M-19): `objectStoreEmptyAtBoot` and `irqRangeValid` are now required
    fields (no default). Each platform must explicitly state its boot guarantee,
    preventing vacuously-true contracts that would allow booting with zero
    objects (no idle thread) or unbounded IRQ ranges.

    AK9-B (P-H02): Renamed `objectStoreNonEmpty → objectStoreEmptyAtBoot`.
    Both platform instantiations (Sim, RPi5) have always asserted
    `(default : SystemState).objects.size = 0` — i.e., the object store is
    EMPTY at boot time, populated subsequently by PlatformConfig. The prior
    name inverted the semantic meaning and was a readability/spec hazard. -/
structure BootBoundaryContract where
  objectTypeMetadataConsistent : Prop
  capabilityRefMetadataConsistent : Prop
  /-- V4-G/AJ3-D/AK9-B: Object store state at boot. Platform-specific
      assertion about initial object store size (typically empty: the boot
      pipeline populates the store from `PlatformConfig.initialObjects`). -/
  objectStoreEmptyAtBoot : Prop
  /-- V4-G/AJ3-D: IRQ range guarantee. Platform-specific assertion about
      IRQ line validity (e.g., all registered IRQs within GIC range). -/
  irqRangeValid : Prop

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

-- ============================================================================
-- AG10-C: Hardware Model Documentation (AG3–AG8 Architecture Modules)
-- ============================================================================

/-! ## AG10-C: ARM64 Architecture Model Summary

The following architecture modules were added during WS-AG phases AG3–AG8 to
bridge the abstract Lean kernel model to concrete ARM64 hardware semantics on
Raspberry Pi 5 (BCM2712, Cortex-A76). Each module uses no unproved
declarations and maintains the zero-tracked-obligation invariant.

### AG3-C: Exception Model (`ExceptionModel.lean`)

Models the ARM64 exception vector table: 4 exception types (synchronous, IRQ,
FIQ, SError) × 4 execution states = 16 vector entries. The ESR_EL1 Exception
Syndrome Register is classified by its EC field (bits [31:26]) to route
synchronous exceptions. SVC instructions dispatch to the kernel syscall entry
point. IRQs route to the interrupt dispatch model (AG3-D). FIQs return
`.notSupported`; SErrors return `.hardwareFault`.

Key types: `ExceptionType`, `ExceptionSource`, `SynchronousExceptionClass`,
`ExceptionContext`. The `dispatchException` function is total and deterministic.

AG3-F extends the model with ARM64 privilege levels EL0 (user) and EL1 (kernel),
setting the appropriate level on exception entry/exit. Eight preservation
theorems prove kernel state consistency across exception and interrupt
boundaries (context save/restore, thread selection, dispatch, scheduling,
timer tick, and interrupt handling).

### AG3-D: Interrupt Dispatch Model (`InterruptDispatch.lean`)

Models the GIC-400 interrupt controller dispatch path: acknowledge (GICC_IAR
read) → dispatch (route by INTID) → end-of-interrupt (GICC_EOIR write). The
GIC-400 INTID space is partitioned into SGIs (0–15), PPIs (16–31), and SPIs
(32–223). The non-secure physical timer PPI (INTID 30) routes to `timerTick`.
Mapped SPIs route to `notificationSignal` for the registered handler endpoint.
Spurious interrupts (INTID ≥ 1020) are silently dropped.

The `handleInterrupt` operation is the 35th `KernelOperation` constructor and
has a corresponding non-interference step in the information flow model.

### AG3-E: Timer Model Binding (`TimerModel.lean`)

Bridges the abstract model timer (`Nat` incremented by `timerTick`) to the ARM
Generic Timer on RPi5. Hardware registers: CNTPCT_EL0 (physical counter, 54 MHz),
CNTP_CVAL_EL0 (comparator), CNTFRQ_EL0 (frequency). One model `timerTick`
corresponds to one timer interrupt event when the counter reaches the comparator
value. `hardwareTimerToModelTick` converts counter values to abstract ticks;
`hardwareTimerToModelTick_monotone` proves the conversion is monotonically
non-decreasing.

The `TimerInterruptBinding` structure captures the bidirectional relationship
between hardware timer events and model timer ticks, enabling proofs that
abstract timer semantics correctly represent hardware behavior.

### AG3-F: Exception Level Model (in `ExceptionModel.lean`)

Models ARM64 privilege levels EL0 (user) and EL1 (kernel). The `ExceptionLevel`
type captures the current privilege state. `exceptionEntry_setsEL1` and
`exceptionReturn_restoresEL0` prove that exception boundaries correctly
transition between privilege levels.

### AG6-A/B: ARMv8 Page Table Model (`PageTable.lean`)

Models the ARMv8-A 4-level page table structure: `PageTableLevel` (L0–L3),
`PageTableDescriptor` (invalid/block/table/page), `PageAttributes` (W^X
permissions, shareability, access flag). `pageTableWalk` performs a structural
recursion walk (no fuel required). `pageTableWalk_fault_on_non_table_l0` proves
translation faults on invalid L0 entries. `pageTableWalkPerms_wx_bridge`
composes the walk with W^X compliance transfer. `hwDescriptor_wxCompliant_bridge`
bridges hardware descriptor W^X compliance to the abstract VSpace W^X invariant.

### AG6-C/D: VSpace ARMv8 Instance (`VSpaceARMv8.lean`)

Provides the `VSpaceBackend` instance for ARMv8 using a shadow `VSpaceRoot`
structure. All 7 typeclass obligations are discharged. The `simulationRelation`
connects the shadow state to the abstract HashMap-based VSpace, with
`hwLookupPage_refines` and `vspaceProperty_transfer` proving refinement.

### AG6-H: ASID Manager (`AsidManager.lean`)

Models the ARM64 ASID pool allocator with generation tracking, free list reuse,
and exhaustion guard. `wellFormed` predicate with 3 preservation theorems.
`asidPoolUnique` invariant ensures no two active address spaces share an ASID.

### AG6-F/G: TLB Model (`TlbModel.lean`)

Models TLB flush operations: TLBI VMALLE1 (flush all), TLBI VAE1 (flush by VA),
TLBI ASIDE1 (flush by ASID), TLBI VALE1 (flush last-level by VA). Hardware
adapter integration functions with 3 equivalence theorems, 3 consistency
preservation theorems, and `tlbBarrierComplete` composition.

### AG8-B: Cache Coherency Model (`CacheModel.lean`)

Models D-cache and I-cache line states (Invalid/Clean/Dirty for D-cache,
Invalid/Valid for I-cache). Five maintenance operations (DC CIVAC, DC CVAC,
DC IVAC, IC IALLU, IC IALLUIS) with 17 preservation theorems. Sequential
model — cache coherency is trivially satisfied under single-core operation.

### ARM64-Specific Constraints

The following hardware constraints are assumed for the Raspberry Pi 5 target:

- **Single-core operation**: H3 uses core 0 only. Other cores are held in WFE
  loop. Per-core assumptions (run queues, TLB, cache) are simplified to
  single-core semantics. SMP support is deferred to WS-V.
- **Sequential memory model**: All memory operations are sequentially ordered.
  DMB/DSB/ISB barriers are modeled as no-ops in the sequential model but are
  emitted in the Rust HAL for hardware correctness.
- **GIC-400 interrupt range**: BCM2712 implements 192 SPIs (INTIDs 32–223),
  bounded by `InterruptId := Fin 224`.
- **Timer frequency**: 54 MHz crystal oscillator (CNTFRQ_EL0 = 54000000).
  Default tick rate: 1000 Hz (1ms ticks, 54000 counter increments per tick).
- **ARMv8-A page granule**: 4 KiB pages with 4-level translation (L0–L3).
  48-bit virtual address space with TTBR0_EL1 (user) / TTBR1_EL1 (kernel).
-/

end SeLe4n.Kernel.Architecture
