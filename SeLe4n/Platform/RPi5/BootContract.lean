import SeLe4n.Platform.RPi5.Board
import SeLe4n.Kernel.Architecture.Assumptions

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

H3-prep stub. Object-type and capability-ref metadata consistency are
declared as `True` placeholders. Full boot-state verification requires
the H3 platform-binding workstream to define the concrete initial state
construction and prove it satisfies these contracts.
-/

namespace SeLe4n.Platform.RPi5

open SeLe4n.Kernel.Architecture

/-- RPi5 boot contract: initial state consistency is asserted by the bootloader.

    In H3, these will become substantive propositions verified against the
    concrete initial `SystemState` constructed by the boot sequence.
    For now, they are `True` placeholders. -/
def rpi5BootContract : BootBoundaryContract :=
  {
    objectTypeMetadataConsistent := True
    capabilityRefMetadataConsistent := True
  }

/-- RPi5 interrupt contract: declares which IRQ lines the GIC-400 supports
    and assumes all supported lines have handler mappings.

    In H3, `irqLineSupported` will check against the actual GIC-400 SPI
    count and PPI assignments. `irqHandlerMapped` will verify that the
    IRQ handler table has been populated during boot. -/
def rpi5InterruptContract : InterruptBoundaryContract :=
  {
    irqLineSupported := fun irq => irq.toNat < gicSpiCount + 32  -- SPIs + PPIs
    irqHandlerMapped := fun _ _ => True  -- placeholder: all mapped
  }

end SeLe4n.Platform.RPi5
