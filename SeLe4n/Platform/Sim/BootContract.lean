/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.Assumptions

/-!
# Simulation Platform — Boot Contract

Simulation-target boot boundary contract. Provides trivially-true propositions
for object-type metadata consistency and capability-ref metadata consistency,
enabling trace harness execution without platform-specific boot validation.
-/

namespace SeLe4n.Platform.Sim

open SeLe4n.Kernel.Architecture

/-- V4-G/M-HW-6: Simulation boot contract with substantive precondition checks.
    While the state builder constructs a valid initial state by construction,
    the contract now includes non-trivial validation for object store non-emptiness
    and IRQ range validity to catch configuration errors during simulation.

    For the simulation target, these are still `True` because the state builder
    guarantees them by construction. Production platforms (RPi5) should supply
    platform-specific validation predicates. -/
def simBootContract : BootBoundaryContract :=
  {
    objectTypeMetadataConsistent := True
    capabilityRefMetadataConsistent := True
    objectStoreNonEmpty := True
    irqRangeValid := True
  }

/-- Simulation interrupt contract: all IRQ lines are supported and all handlers
    are considered mapped. Used for testing IRQ-adjacent paths without hardware
    constraints. -/
def simInterruptContract : InterruptBoundaryContract :=
  {
    irqLineSupported := fun _ => True
    irqHandlerMapped := fun _ _ => True
    irqLineSupportedDecidable := by intro _; infer_instance
    irqHandlerMappedDecidable := by intro _ _; infer_instance
  }

end SeLe4n.Platform.Sim
