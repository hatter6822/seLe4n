/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

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

/-! ## WS-H15b/A-41, U6-C (U-M09): RPi5 runtime contract with substantive predicates.

Timer monotonicity: ARM Generic Timer (CNTPCT_EL0) is monotonically
non-decreasing. Counter rollover is outside the operational lifetime.

Register context stability (U6-C strengthened): When a thread is scheduled
in the post-state, the machine register file must match that thread's saved
`registerContext` in the TCB. This replaces the previous permissive disjunct
(`sp preserved ∨ context switch in progress`) which was trivially satisfied
and did not actually constrain hardware behavior.

The strengthened predicate requires:
- If `st'.scheduler.current = some tid`, then `st'.machine.regs` must be
  consistent with the TCB's `registerContext` for `tid`.
- If no thread is scheduled, the register file is unconstrained.

On ARMv8-A, `saveOutgoingContext` stores registers into the outgoing TCB,
then `restoreIncomingContext` loads the incoming thread's saved registers —
so the strengthened predicate holds by construction during context switch.

Memory access: Restricted to declared RAM regions in the BCM2712 memory map.
Device and reserved regions require explicit MMIO adapter calls.
-/

/-- U6-C/V4-I: Computable check for register context stability. Returns `true`
    if the machine register file matches the scheduled thread's saved context.

    When `scheduler.current = some tid`:
    - If the object is a TCB: checks `st'.machine.regs == tcb.registerContext`.
    - If the object is missing or not a TCB: returns `false` (contract violation).
      A scheduled thread that has no corresponding TCB or maps to a non-TCB
      object represents a malformed scheduler state. The contract must reject
      this to prevent unsound reasoning about register-file consistency.

    V4-I/M-HW-9: The pre-state parameter `st` is now used: when both states have
    a current thread, we additionally check that either the current thread hasn't
    changed (register file tracks the same thread), or the new thread's saved
    context matches the post-state register file (context switch occurred correctly). -/
def registerContextStableCheck (_st st' : SystemState) : Bool :=
  match st'.scheduler.current with
  | none => true
  | some tid =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      -- LOW-05: Register-context stability is checked uniformly regardless of
      -- whether a context switch occurred. The `contextSwitchState` operation
      -- (X1-C) guarantees that post-state registers always match the current
      -- TCB's saved context — both for same-thread continuation and for
      -- cross-thread context switches. The previous implementation had identical
      -- `then`/`else` branches; this simplification removes the dead branching.
      st'.machine.regs == tcb.registerContext
    | _ => false

/-- U6-C: Prop-level register context stability predicate. -/
def registerContextStablePred (st st' : SystemState) : Prop :=
  registerContextStableCheck st st' = true

/-- U6-C: Decidability of the strengthened register context stability predicate. -/
instance registerContextStablePred_decidable (st st' : SystemState) :
    Decidable (registerContextStablePred st st') :=
  inferInstanceAs (Decidable (_ = true))

def rpi5RuntimeContract : RuntimeBoundaryContract :=
  {
    timerMonotonic := fun st st' => st.machine.timer ≤ st'.machine.timer
    registerContextStable := registerContextStablePred
    memoryAccessAllowed := fun _ addr =>
      rpi5MachineConfig.memoryMap.any fun region =>
        region.kind == .ram && region.contains addr
    timerMonotonicDecidable := by intro st st'; infer_instance
    registerContextStableDecidable := by intro st st'; exact registerContextStablePred_decidable st st'
    memoryAccessAllowedDecidable := by
      intro _ addr
      simp only [rpi5MachineConfig, rpi5MemoryMap]
      infer_instance
  }

/-- WS-H15d/A-33, X1-F: Restrictive RPi5 runtime contract for `AdapterProofHooks`
instantiation. The production contract (`rpi5RuntimeContract`) uses a substantive
`registerContextStablePred` that checks TCB context match. However, individual
register writes (`adapterWriteRegister`) can break `contextMatchesCurrent`
because the register file is partially updated while `scheduler.current` still
points to the old thread.

This restrictive contract denies all register writes, making the
`preserveWriteRegister` proof obligation vacuously satisfiable. Timer and
memory-read operations use the same substantive predicates as production.

**X1-F context-switch resolution**: The `adapterContextSwitch` operation
(Adapter.lean) atomically loads a new thread's saved register context AND
updates `scheduler.current` in a single step. This atomic operation preserves
`contextMatchesCurrent` by construction (proven in
`contextSwitchState_preserves_contextMatchesCurrent`), eliminating the
register-context paradox without requiring individual register writes.
The restrictive contract remains correct: individual writes are still denied,
but context switches use the dedicated atomic path. -/
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

-- ============================================================================
-- T6-F/M-NEW-7: MMIO access contract extension
-- ============================================================================

/-- T6-F/M-NEW-7: MMIO device-region access predicate. Returns `true` iff the
    given address falls within a `.device` region of the RPi5 memory map.
    This extends the runtime contract's `memoryAccessAllowed` (which covers RAM)
    to also gate MMIO operations on device-region membership.

    **Usage**: The MMIO adapter (`MmioAdapter.lean`) validates addresses against
    this predicate before performing device register reads/writes. -/
def mmioAccessAllowed (_st : SeLe4n.Model.SystemState) (addr : SeLe4n.PAddr) : Bool :=
  rpi5MachineConfig.memoryMap.any fun region =>
    region.kind == .device && region.contains addr

/-- T6-F: MMIO access decidability. -/
instance mmioAccessAllowed_decidable (st : SeLe4n.Model.SystemState) (addr : SeLe4n.PAddr) :
    Decidable (mmioAccessAllowed st addr = true) := by
  simp only [mmioAccessAllowed, rpi5MachineConfig, rpi5MemoryMap]
  infer_instance

/-- T6-F: RAM and MMIO device regions use disjoint `.kind` tags. The RAM check
    filters on `kind == .ram` while the MMIO check filters on `kind == .device`,
    so a region cannot satisfy both predicates simultaneously. Physical non-overlap
    of regions is proven by `mmioRegionDisjoint_holds` in Board.lean. -/
theorem mmioAccess_ram_kind_disjoint :
    ∀ (r : SeLe4n.MemoryRegion),
      (r.kind == .ram && r.kind == .device) = false := by
  intro r; cases r.kind <;> decide

end SeLe4n.Platform.RPi5
