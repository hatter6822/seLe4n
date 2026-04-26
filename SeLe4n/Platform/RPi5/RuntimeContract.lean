-- SPDX-License-Identifier: GPL-3.0-or-later
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

AI6-E (L-24): Substantive runtime contract implementing 6-condition register
consistency checks: (1) register-context match, (2) dequeue-on-dispatch
readiness, (3) time-slice positivity, (4) IPC readiness, (5) EDF
compatibility, and (6) budget sufficiency validation. These predicates
are well-typed and decidable, enabling non-vacuous `AdapterProofHooks`
for both `preserveWriteRegister` and `preserveContextSwitch` on the
production contract. Full hardware validation against actual RPi5 behavior
is part of AN9 (hardware binding) per
docs/dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md §12.
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

/-- AG7-D / AK9-E: Budget sufficiency check for the current thread's
    SchedContext. Returns `true` if the thread is unbound (vacuously sufficient)
    or if the bound SchedContext has `budgetRemaining > 0`.

    AK9-E (P-M03): When `schedContextBinding = .bound/.donated scId` but
    `st'.objects[scId.toObjId]?` resolves to a variant OTHER than
    `.schedContext` (or is `none`), this indicates a contract violation —
    the TCB claims a binding to a non-existent or wrong-kind object. Such
    states used to return `true` (silently permissive), letting an inconsistent
    post-state pass the `registerContextStableCheck`. It now returns `false`
    so the check fails loudly. -/
private def budgetSufficientCheck (st' : SystemState) (tcb : TCB) : Bool :=
  match tcb.schedContextBinding with
  | .unbound => true
  | .bound scId | .donated scId _ =>
    match st'.objects[scId.toObjId]? with
    | some (.schedContext sc) => sc.budgetRemaining.val > 0
    | _ => false   -- AK9-E: missing / wrong-variant binding is a violation

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

/-- AG7-D / AK9-E: When `registerContextStableCheck` passes for a context-switch
    post-state, extract `currentBudgetPositive` from the budget-sufficiency
    conjunct. The budget check in `registerContextStableCheck` mirrors
    the structure of `currentBudgetPositive` exactly.

    AK9-E (P-M03): With the tightened `budgetSufficientCheck` (returns `false`
    for missing / wrong-variant bindings), the wrong-variant branches now
    produce a direct contradiction from `hBud : false = true`. -/
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
      -- AK9-E: budgetSufficientCheck now returns false for these cases,
      -- so hBud : false = true is a direct contradiction — no SC to
      -- discharge currentBudgetPositive from.
      simp [hSc] at hBud

/-! ## AN7-C (H-16): Per-conjunct soundness theorems for `registerContextStableCheck`

Each of the six AG7-D conjuncts projected into a standalone soundness theorem,
following the AK9-E pattern (see `registerContextStableCheck_budget` above).
Rationale: allow callers that only need ONE consequence of the bundled check
to discharge their obligation without re-unfolding the full 6-conjunct
conjunction. Every extraction theorem fails loudly on the "current thread
present but not a TCB" branch where the raw check already returns `false` —
so a passing witness for `registerContextStableCheck` implies the TCB lookup
succeeds.

"Silent-true" audit: the ONE branch where the raw check returns `true`
unconditionally is `scheduler.current = none`.  This is not a silent bypass
— it is the "no current thread, no obligation to check" case, documented by
`registerContextStableCheck_none_current` below.  All OTHER branches are
fail-closed (return `false` when the expected TCB / binding / condition is
missing).
-/

/-- AN7-C: When `scheduler.current = none`, the check returns `true` by
    construction (no current thread means no register-context obligation).
    This is the ONE vacuous-true branch and is semantically correct: there is
    no thread whose register file must match. -/
theorem registerContextStableCheck_none_current
    (st st' : SeLe4n.Model.SystemState)
    (hNone : st'.scheduler.current = none) :
    registerContextStableCheck st st' = true := by
  unfold registerContextStableCheck
  rw [hNone]

/-- AN7-C: Conversely, when the check passes, either there is no current
    thread OR the current thread's ObjId resolves to a TCB (every other
    variant causes the raw check to fall to the `| _ => false` branch). -/
theorem registerContextStableCheck_implies_tcb_present
    (st st' : SeLe4n.Model.SystemState)
    (hStable : registerContextStableCheck st st' = true) :
    st'.scheduler.current = none ∨
    ∃ tid tcb,
      st'.scheduler.current = some tid ∧
      st'.objects[tid.toObjId]? = some (.tcb tcb) := by
  unfold registerContextStableCheck at hStable
  cases hCur : st'.scheduler.current with
  | none => exact Or.inl rfl
  | some tid =>
    simp only [hCur] at hStable
    cases hObj : st'.objects[tid.toObjId]? with
    | none => simp only [hObj] at hStable; simp at hStable
    | some o =>
      simp only [hObj] at hStable
      match o, hObj, hStable with
      | .tcb tcb, hObj, _ => exact Or.inr ⟨tid, tcb, rfl, hObj⟩
      | .endpoint _, _, hStable => simp at hStable
      | .notification _, _, hStable => simp at hStable
      | .cnode _, _, hStable => simp at hStable
      | .vspaceRoot _, _, hStable => simp at hStable
      | .untyped _, _, hStable => simp at hStable
      | .schedContext _, _, hStable => simp at hStable

/-- AN7-C: Register-context conjunct soundness (Boolean form) — when the
    check passes for a TCB-present state, the post-state register file's
    decidable `==` against the TCB's stored context is `true`.  This is the
    strongest form available because `BEq RegisterFile` is NOT `LawfulBEq`
    (see AK7-G, `TCB.not_lawfulBEq`); callers that need structural equality
    compose this with `RegisterFile.ext` on a per-field basis. -/
theorem registerContextStableCheck_register_match
    (st st' : SeLe4n.Model.SystemState)
    (tid : SeLe4n.ThreadId) (tcb : SeLe4n.Model.TCB)
    (hCur : st'.scheduler.current = some tid)
    (hObj : st'.objects[tid.toObjId]? = some (.tcb tcb))
    (hStable : registerContextStableCheck st st' = true) :
    (st'.machine.regs == tcb.registerContext) = true := by
  unfold registerContextStableCheck at hStable
  simp only [hCur, hObj, Bool.and_eq_true] at hStable
  exact hStable.1.1.1.1.1

/-- AN7-C: Dequeue-on-dispatch conjunct — when the check passes the current
    thread is NOT in the runnable queue (a runnable-queue membership would
    violate EDF dispatch semantics). -/
theorem registerContextStableCheck_dequeue_on_dispatch
    (st st' : SeLe4n.Model.SystemState)
    (tid : SeLe4n.ThreadId) (tcb : SeLe4n.Model.TCB)
    (hCur : st'.scheduler.current = some tid)
    (hObj : st'.objects[tid.toObjId]? = some (.tcb tcb))
    (hStable : registerContextStableCheck st st' = true) :
    st'.scheduler.runnable.contains tid = false := by
  unfold registerContextStableCheck at hStable
  simp only [hCur, hObj, Bool.and_eq_true] at hStable
  have h := hStable.1.1.1.1.2
  exact Bool.not_eq_true' _ |>.mp h

/-- AN7-C: Time-slice positivity conjunct — the dispatched TCB's time slice
    is strictly positive. -/
theorem registerContextStableCheck_timeSlice_positive
    (st st' : SeLe4n.Model.SystemState)
    (tid : SeLe4n.ThreadId) (tcb : SeLe4n.Model.TCB)
    (hCur : st'.scheduler.current = some tid)
    (hObj : st'.objects[tid.toObjId]? = some (.tcb tcb))
    (hStable : registerContextStableCheck st st' = true) :
    tcb.timeSlice > 0 := by
  unfold registerContextStableCheck at hStable
  simp only [hCur, hObj, Bool.and_eq_true] at hStable
  have h := hStable.1.1.1.2
  exact decide_eq_true_eq.mp h

/-- AN7-C: IPC readiness conjunct — the dispatched TCB's IPC state is
    `.ready` (not blocked on any send/receive/reply). -/
theorem registerContextStableCheck_ipcReady
    (st st' : SeLe4n.Model.SystemState)
    (tid : SeLe4n.ThreadId) (tcb : SeLe4n.Model.TCB)
    (hCur : st'.scheduler.current = some tid)
    (hObj : st'.objects[tid.toObjId]? = some (.tcb tcb))
    (hStable : registerContextStableCheck st st' = true) :
    tcb.ipcState = .ready := by
  unfold registerContextStableCheck at hStable
  simp only [hCur, hObj, Bool.and_eq_true] at hStable
  have h := hStable.1.1.2
  exact beq_iff_eq.mp h

/-- AN7-C: EDF compatibility conjunct — the dispatched TCB's deadline is
    zero (trivially earliest among any EDF ordering). -/
theorem registerContextStableCheck_edfCompatible
    (st st' : SeLe4n.Model.SystemState)
    (tid : SeLe4n.ThreadId) (tcb : SeLe4n.Model.TCB)
    (hCur : st'.scheduler.current = some tid)
    (hObj : st'.objects[tid.toObjId]? = some (.tcb tcb))
    (hStable : registerContextStableCheck st st' = true) :
    tcb.deadline.toNat = 0 := by
  unfold registerContextStableCheck at hStable
  simp only [hCur, hObj, Bool.and_eq_true] at hStable
  have h := hStable.1.2
  exact beq_iff_eq.mp h

/-- AN7-C: Budget sufficiency conjunct — the dispatched TCB's
    `budgetSufficientCheck` passes.  Combined with AK9-E, this fails closed
    on missing/wrong-variant SchedContext bindings. -/
theorem registerContextStableCheck_budget_conjunct
    (st st' : SeLe4n.Model.SystemState)
    (tid : SeLe4n.ThreadId) (tcb : SeLe4n.Model.TCB)
    (hCur : st'.scheduler.current = some tid)
    (hObj : st'.objects[tid.toObjId]? = some (.tcb tcb))
    (hStable : registerContextStableCheck st st' = true) :
    budgetSufficientCheck st' tcb = true := by
  unfold registerContextStableCheck at hStable
  simp only [hCur, hObj, Bool.and_eq_true] at hStable
  exact hStable.2

end SeLe4n.Platform.RPi5
