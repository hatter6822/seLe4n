/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.RPi5.Board
import SeLe4n.Kernel.Architecture.Assumptions
import SeLe4n.Model.State

/-!
# Raspberry Pi 5 — Boot Boundary Contract

Platform-specific boot boundary contract for the BCM2712 SoC. Declares the
assumptions about initial system state when the kernel receives control from
the bootloader (ATF / U-Boot).

## Boot sequence assumptions

1. ARM Trusted Firmware (ATF) has initialized EL3 and handed off to EL2/EL1.
2. U-Boot has loaded the kernel image and device tree blob into RAM.
3. The MMU is disabled or in identity-map mode at kernel entry.
4. The BSS section is zeroed (matches `default_memory_returns_zero`).

## Status

WS-H15b/A-41: Boot and interrupt contracts hardened with substantive predicates.
Boot contract validates empty initial state. Interrupt contract validates
GIC-400 IRQ range with decidable predicates (WS-H15a/M-13).
-/

namespace SeLe4n.Platform.RPi5

open SeLe4n.Kernel.Architecture
open SeLe4n.Model

/-- WS-H15b/A-41: RPi5 boot contract with substantive initial-state predicates.

    Object-type metadata consistency: the default (initial) object store is
    empty — no pre-existing kernel objects at boot time. This models the
    assumption that ATF/U-Boot do not pre-populate the kernel's object store.

    Capability-ref metadata consistency: the default capability reference table
    is empty — no pre-existing capability derivations at boot time. -/
def rpi5BootContract : BootBoundaryContract :=
  {
    objectTypeMetadataConsistent :=
      (default : SystemState).objects.size = 0
    capabilityRefMetadataConsistent :=
      (default : SystemState).lifecycle.capabilityRefs.size = 0
  }

/-- WS-H15b: RPi5 boot contract predicates are satisfied by the default state. -/
theorem rpi5BootContract_objectType_holds : rpi5BootContract.objectTypeMetadataConsistent := by
  show ({} : KernelHashMap SeLe4n.ObjId KernelObject).size = 0
  rfl

/-- WS-H15b: RPi5 boot contract capability ref predicate holds for default state. -/
theorem rpi5BootContract_capabilityRef_holds : rpi5BootContract.capabilityRefMetadataConsistent := by
  show ({} : KernelHashMap SlotRef CapTarget).size = 0
  rfl

/-- WS-H15b/A-41: RPi5 interrupt contract with GIC-400 range validation.

    **Supported range:** INTIDs 0–223 (SGIs 0–15, PPIs 16–31, SPIs 32–223).
    SGIs (software-generated interrupts) are included because the GIC-400
    distributes them like any other interrupt.

    **Handler mapping:** For supported IRQ lines, the handler must be
    registered in the kernel's IRQ handler table (`st.irqHandlers`).
    Unsupported IRQ lines (INTID ≥ 224) have no mapping requirement.

    WS-H15a/M-13: Decidable fields provided for both predicates. -/
def rpi5InterruptContract : InterruptBoundaryContract :=
  {
    irqLineSupported := fun irq => irq.toNat < gicSpiCount + 32  -- SGIs + PPIs + SPIs
    irqHandlerMapped := fun st irq =>
      irq.toNat < gicSpiCount + 32 →   -- only for supported IRQs
      st.irqHandlers[irq]? ≠ none       -- handler must be registered
    irqLineSupportedDecidable := by intro irq; infer_instance
    irqHandlerMappedDecidable := by intro st irq; infer_instance
  }

end SeLe4n.Platform.RPi5
