import SeLe4n.Platform.RPi5.Board
import SeLe4n.Kernel.Architecture.Assumptions

/-!
# Raspberry Pi 5 — Runtime Boundary Contract

Platform-specific runtime boundary contract for the BCM2712 SoC. This contract
encodes the hardware assumptions that the abstract kernel model relies on:

1. **Timer monotonicity**: The ARM Generic Timer (CNTPCT_EL0) is monotonically
   non-decreasing. Counter rollover is outside the operational lifetime.
2. **Register context stability**: Context switches preserve the full ARMv8-A
   general-purpose register file (X0–X30, SP, PC, PSTATE).
3. **Memory access permissions**: Access is allowed only to addresses within
   declared RAM regions of the platform memory map. Device and reserved
   regions require explicit MMIO adapter calls (not modeled here).

## Status

H3-prep stub. The predicates are well-typed and decidable but not yet
validated against actual hardware behavior. Full hardware validation is
part of the H4 evidence-convergence workstream.
-/

namespace SeLe4n.Platform.RPi5

open SeLe4n.Kernel.Architecture
open SeLe4n.Model

/-- WS-H15b/A-41: RPi5 runtime contract with substantive predicates.

Timer monotonicity: ARM Generic Timer (CNTPCT_EL0) is monotonically
non-decreasing. Counter rollover is outside the operational lifetime.

Register context stability: Validates that either the stack pointer is
preserved across a state transition (callee-save guarantee) OR a context
switch is in progress (scheduler transitions may update SP as part of
thread dispatch). This replaces the previous `True` placeholder with a
non-trivial hardware-aligned predicate.

Memory access: Restricted to declared RAM regions in the BCM2712 memory map.
Device and reserved regions require explicit MMIO adapter calls. -/
def rpi5RuntimeContract : RuntimeBoundaryContract :=
  {
    timerMonotonic := fun st st' => st.machine.timer ≤ st'.machine.timer
    registerContextStable := fun st st' =>
      -- ARMv8 context-switch guarantee: SP preserved OR context switch in progress
      st.machine.regs.sp = st'.machine.regs.sp ∨
      st'.scheduler.current ≠ st.scheduler.current
    memoryAccessAllowed := fun _ addr =>
      rpi5MachineConfig.memoryMap.any fun region =>
        region.kind == .ram && region.contains addr
    timerMonotonicDecidable := by intro st st'; infer_instance
    registerContextStableDecidable := by intro st st'; infer_instance
    memoryAccessAllowedDecidable := by
      intro _ addr
      simp only [rpi5MachineConfig, rpi5MemoryMap]
      infer_instance
  }

/-- WS-H15d/A-33: Restrictive RPi5 runtime contract for `AdapterProofHooks`
instantiation. The production contract (`rpi5RuntimeContract`) admits all
register writes because `writeReg` never modifies `sp`, making
`registerContextStable` trivially `True` for every write. Since
`contextMatchesCurrent` requires full register-file equality, the production
contract cannot prove invariant preservation for arbitrary register writes.

This restrictive contract preserves the RPi5 timer monotonicity and memory
access predicates (substantive, hardware-aligned) but denies all register
writes. Adapter timer and memory-read operations are accepted with the same
validation as the production contract; register writes are rejected, making
the `preserveWriteRegister` proof obligation vacuously satisfiable.

**Design note**: when a future workstream introduces a context-switch-aware
adapter (combining register-file load with `scheduler.current` update in a
single atomic operation), the production contract can instantiate
`AdapterProofHooks` directly because the combined operation preserves
`contextMatchesCurrent` by construction. -/
def rpi5RuntimeContractRestrictive : RuntimeBoundaryContract :=
  {
    timerMonotonic := fun st st' => st.machine.timer ≤ st'.machine.timer
    registerContextStable := fun _ _ => False
    memoryAccessAllowed := fun _ addr =>
      rpi5MachineConfig.memoryMap.any fun region =>
        region.kind == .ram && region.contains addr
    timerMonotonicDecidable := by intro st st'; infer_instance
    registerContextStableDecidable := by intro st st'; infer_instance
    memoryAccessAllowedDecidable := by
      intro _ addr
      simp only [rpi5MachineConfig, rpi5MemoryMap]
      infer_instance
  }

end SeLe4n.Platform.RPi5
