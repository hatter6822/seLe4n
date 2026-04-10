/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.RPi5.Board
import SeLe4n.Kernel.Architecture.Adapter
import SeLe4n.Kernel.Scheduler.Invariant

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

Register context stability (U6-C strengthened, AG7-D comprehensive): When a
thread is scheduled in the post-state, the contract validates ALL properties
required to maintain `proofLayerInvariantBundle` for the current-thread
predicates:

1. **Register-context match**: `machine.regs == tcb.registerContext`
2. **Dequeue-on-dispatch**: current thread not in runnable queue
3. **Time-slice positivity**: `tcb.timeSlice > 0`
4. **IPC readiness**: `tcb.ipcState == .ready` (ensures the current thread
   is not blocked on any IPC operation, enabling derivation of
   `currentNotEndpointQueueHead` and `currentNotOnNotificationWaitList`
   from the IPC invariants)
5. **EDF compatibility**: `tcb.deadline.toNat == 0` (zero-deadline threads
   trivially satisfy `edfCurrentHasEarliestDeadline`; the scheduler always
   clears deadlines before dispatch on RPi5)
6. **Budget sufficiency**: if the thread is SchedContext-bound, the bound
   SchedContext has `budgetRemaining > 0`

This comprehensive check enables non-vacuous `AdapterProofHooks` for both
`preserveWriteRegister` and `preserveContextSwitch` on the production
contract.

Memory access: Restricted to declared RAM regions in the BCM2712 memory map.
Device and reserved regions require explicit MMIO adapter calls.
-/

/-- AG7-D: Budget sufficiency check for the current thread's SchedContext.
    Returns `true` if the thread is unbound (vacuously sufficient) or if the
    bound SchedContext has `budgetRemaining > 0`. -/
private def budgetSufficientCheck (st' : SystemState) (tcb : TCB) : Bool :=
  match tcb.schedContextBinding with
  | .unbound => true
  | .bound scId | .donated scId _ =>
    match st'.objects[scId.toObjId]? with
    | some (.schedContext sc) => sc.budgetRemaining.val > 0
    | _ => true

/-- U6-C/V4-I/AG7-D: Computable check for register context stability with
    comprehensive current-thread validation. Returns `true` if the post-state
    satisfies all current-thread predicates required by `proofLayerInvariantBundle`.

    When `scheduler.current = some tid`:
    - If the object is a TCB: checks register match, dequeue-on-dispatch,
      time-slice positivity, IPC readiness, EDF compatibility, and budget.
    - If the object is missing or not a TCB: returns `false` (contract violation).

    LOW-05 / Y2-B: The pre-state parameter `_st` is retained for signature
    compatibility with the `RuntimeBoundaryContract.registerContextStable` field
    but is not inspected. All checks examine the post-state only. -/
def registerContextStableCheck (_st st' : SystemState) : Bool :=
  match st'.scheduler.current with
  | none => true
  | some tid =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      -- Core register-context match (U6-C)
      st'.machine.regs == tcb.registerContext &&
      -- Dequeue-on-dispatch: current not in runnable queue (AG7-D)
      !st'.scheduler.runnable.contains tid &&
      -- Time-slice positivity (AG7-D)
      (tcb.timeSlice > 0) &&
      -- IPC readiness (AG7-D): enables derivation of currentNotEndpointQueueHead
      -- and currentNotOnNotificationWaitList from pre-state IPC invariants
      (tcb.ipcState == .ready) &&
      -- EDF compatibility: zero deadline trivially satisfies earliest-deadline
      -- ordering (AG7-D)
      (tcb.deadline.toNat == 0) &&
      -- Budget sufficiency (AG7-D)
      budgetSufficientCheck st' tcb
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

/-- AG7-D: When `registerContextStableCheck` passes for a context-switch
    post-state, extract `currentBudgetPositive` from the budget-sufficiency
    conjunct. The budget check in `registerContextStableCheck` mirrors
    the structure of `currentBudgetPositive` exactly. -/
theorem registerContextStableCheck_budget
    (newTid : SeLe4n.ThreadId) (newRegs : SeLe4n.RegisterFile) (st : SeLe4n.Model.SystemState)
    (tcb : SeLe4n.Model.TCB)
    (hObj : st.objects[newTid.toObjId]? = some (.tcb tcb))
    (hStable : registerContextStableCheck st (contextSwitchState newTid newRegs st) = true) :
    SeLe4n.Kernel.currentBudgetPositive (contextSwitchState newTid newRegs st) := by
  unfold registerContextStableCheck contextSwitchState at hStable
  simp only [hObj, Bool.and_eq_true] at hStable
  unfold SeLe4n.Kernel.currentBudgetPositive contextSwitchState; simp only [hObj]
  have hBud := hStable.2
  -- budgetSufficientCheck mirrors currentBudgetPositive structure
  match hBind : tcb.schedContextBinding with
  | .unbound => trivial
  | .bound scId | .donated scId _ =>
    simp only [hBind, budgetSufficientCheck] at hBud
    simp only []
    match hSc : st.objects[scId.toObjId]? with
    | some (.schedContext sc) =>
      simp only [hSc] at hBud ⊢
      simp at hBud; exact hBud
    | some (.endpoint _) | some (.notification _) | some (.tcb _) |
      some (.cnode _) | some (.vspaceRoot _) | some (.untyped _) | none =>
      simp

end SeLe4n.Platform.RPi5
