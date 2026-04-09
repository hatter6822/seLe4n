/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.API
import SeLe4n.Kernel.IPC.Operations

/-!
# AG3-D (FINDING-06): Interrupt Dispatch Model

Models the ARM64 interrupt dispatch path: acknowledge → dispatch → EOI.
Integrates with the GIC-400 interrupt controller on Raspberry Pi 5.

## Interrupt Flow

1. **Acknowledge**: Read GICC_IAR to get the interrupt ID (INTID)
2. **Dispatch**: Route to handler based on INTID
   - Timer interrupt (PPI 30) → `timerTick`
   - Mapped IRQ → `notificationSignal` to registered handler
   - Unmapped IRQ → error
3. **End-of-Interrupt**: Write GICC_EOIR to signal completion

## GIC-400 Interrupt ID Space

- INTIDs 0–15: SGIs (Software Generated Interrupts)
- INTIDs 16–31: PPIs (Private Peripheral Interrupts)
- INTIDs 32–223: SPIs (Shared Peripheral Interrupts)
- INTIDs 1020–1023: Special (spurious)
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel

-- ============================================================================
-- AG3-D-i: Types and constants
-- ============================================================================

/-- AG3-D: GIC-400 interrupt ID.
    Bounded to 224 INTIDs (0–223): SGIs (0–15), PPIs (16–31), SPIs (32–223). -/
abbrev InterruptId := Fin 224

/-- AG3-D: Non-secure physical timer PPI (INTID 30). -/
def timerInterruptId : InterruptId := ⟨30, by omega⟩

/-- AG3-D: Spurious interrupt threshold. INTIDs ≥ 1020 are spurious
    (returned by GICC_IAR when no pending interrupt exists). -/
def spuriousInterruptThreshold : Nat := 1020

-- ============================================================================
-- AG3-D-ii: Acknowledge and EOI operations
-- ============================================================================

/-- AG3-D: Acknowledge an interrupt by reading the interrupt ID.
    Models reading GICC_IAR. Returns `none` for spurious interrupts
    (INTID ≥ 1020), which require no further handling.

    In the abstract model, the interrupt ID is provided as a parameter
    rather than read from hardware. The spurious check models the
    hardware's behavior of returning INTID 1023 when no interrupt
    is pending. -/
def acknowledgeInterrupt (rawIntId : Nat) :
    Option InterruptId :=
  if rawIntId ≥ spuriousInterruptThreshold then none
  else if h : rawIntId < 224 then some ⟨rawIntId, h⟩
  else none  -- Out of GIC-400 range

/-- AG3-D: End-of-interrupt signal. Models writing GICC_EOIR.
    In the abstract model this is a no-op — the EOI write is a
    hardware-level operation that has no effect on kernel state.
    Included for completeness of the acknowledge→dispatch→EOI sequence. -/
def endOfInterrupt (_st : SystemState) (_intId : InterruptId) : SystemState :=
  _st  -- No state change; EOI is a hardware-level acknowledgment

-- ============================================================================
-- AG3-D-iii: Interrupt handler dispatch
-- ============================================================================

/-- AG3-D: Handle a single interrupt by ID.
    Routes based on interrupt type:
    - Timer interrupt (PPI 30): Delegate to `timerTick`
    - Mapped IRQ: Deliver notification via `notificationSignal`
    - Unmapped IRQ: Return `.invalidIrq` error -/
def handleInterrupt (st : SystemState) (intId : InterruptId) :
    Except KernelError (Unit × SystemState) :=
  if intId = timerInterruptId then
    timerTick st
  else
    let irq : Irq := ⟨intId.val⟩
    match st.irqHandlers[irq]? with
    | some handlerId =>
        -- Deliver signal to the notification object bound to this IRQ
        notificationSignal handlerId (Badge.ofNatMasked intId.val) st
    | none => .error .invalidIrq

-- ============================================================================
-- AG3-D-iv: Full dispatch sequence
-- ============================================================================

/-- AG3-D: Full interrupt dispatch sequence: acknowledge → handle → EOI.
    Models the complete IRQ entry path.
    Spurious interrupts (INTID ≥ 1020) return the state unchanged. -/
def interruptDispatchSequence (st : SystemState) (rawIntId : Nat) :
    Except KernelError (Unit × SystemState) :=
  match acknowledgeInterrupt rawIntId with
  | none => .ok ((), st)  -- Spurious: no action needed
  | some intId =>
    match handleInterrupt st intId with
    | .ok ((), st') => .ok ((), endOfInterrupt st' intId)
    | .error e => .error e

-- ============================================================================
-- AG3-D-vi: Preservation theorems
-- ============================================================================

/-- AG3-D: Spurious interrupts preserve state unchanged. -/
theorem interruptDispatchSequence_spurious (st : SystemState) (rawIntId : Nat)
    (hSpurious : rawIntId ≥ spuriousInterruptThreshold) :
    interruptDispatchSequence st rawIntId = .ok ((), st) := by
  simp [interruptDispatchSequence, acknowledgeInterrupt, hSpurious]

/-- AG3-D: End-of-interrupt preserves state (it is a no-op in the model). -/
theorem endOfInterrupt_eq (st : SystemState) (intId : InterruptId) :
    endOfInterrupt st intId = st := rfl

/-- AG3-D: Unmapped IRQ returns `.invalidIrq`. -/
theorem handleInterrupt_unmapped (st : SystemState) (intId : InterruptId)
    (hNotTimer : intId ≠ timerInterruptId)
    (hNoHandler : st.irqHandlers[(⟨intId.val⟩ : Irq)]? = none) :
    handleInterrupt st intId = .error .invalidIrq := by
  unfold handleInterrupt
  simp [hNotTimer, hNoHandler]

end SeLe4n.Kernel.Architecture
