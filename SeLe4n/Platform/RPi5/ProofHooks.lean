-- SPDX-License-Identifier: GPL-3.0-or-later
import SeLe4n.Kernel.Architecture.Invariant
import SeLe4n.Platform.RPi5.RuntimeContract

/-!
# Raspberry Pi 5 — Concrete AdapterProofHooks

WS-H15d/A-33: Concrete `AdapterProofHooks` instantiation for the RPi5
platform's restrictive runtime contract.

The restrictive contract (`rpi5RuntimeContractRestrictive`) shares the
production contract's timer monotonicity and RAM-only memory access
predicates but denies all register writes (`registerContextStable := False`).

## Timer preservation

Timer advancement only modifies `machine.timer`, leaving all invariant-relevant
fields unchanged. The proof delegates to the generic
`advanceTimerState_preserves_proofLayerInvariantBundle` lemma, which handles
the decomposition of all 7 invariant-bundle components.

## Register write preservation

The restrictive contract rejects all register writes, making the proof
obligation vacuously satisfiable: the contract hypothesis is `False`, from
which any conclusion follows via `absurd`.

## Memory read preservation

Read operations are state-preserving — the pre-state is returned unchanged.
The proof is `fun _ st hInv _ => hInv`.

## Design note: production contract (U6-C/D strengthened)

The production `rpi5RuntimeContract` was strengthened in U6-C to require
that when a thread is scheduled, the machine register file matches the
TCB's `registerContext` field. This replaces the previous permissive
disjunct (`sp preserved ∨ context switch in progress`).

The restrictive contract still denies all register writes
(`registerContextStable := False`), so proof hooks remain vacuously correct
for the write path. A future context-switch-aware adapter (closed by
AN9-D — DEF-C-M04 suspendThread atomicity — per
docs/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md §12) will combine register-
file load with `scheduler.current` update atomically, enabling proof
hooks for the production contract.
-/

namespace SeLe4n.Platform.RPi5

open SeLe4n.Kernel.Architecture
open SeLe4n.Model

/-- WS-H15d/A-33: Concrete `AdapterProofHooks` for the RPi5 restrictive
runtime contract. Timer preservation uses the generic lemma;
register write is vacuous; memory read is state-preserving. -/
def rpi5RestrictiveAdapterProofHooks :
    AdapterProofHooks rpi5RuntimeContractRestrictive where
  preserveAdvanceTimer := fun ticks st hInv _ _ =>
    advanceTimerState_preserves_proofLayerInvariantBundle ticks st hInv
  preserveWriteRegister := fun _ _ _ _ hStable =>
    absurd hStable (by simp [rpi5RuntimeContractRestrictive])
  preserveReadMemory := fun _ st hInv _ => hInv
  preserveContextSwitch := fun _ _ _ _ hStable =>
    absurd hStable (by simp [rpi5RuntimeContractRestrictive])

/-- WS-H15d/A-33: End-to-end timer advancement preservation for RPi5.
Composes the restrictive proof hooks with the generic adapter preservation
theorem. Since the restrictive contract rejects register writes, only
timer and memory-read paths can succeed; the theorem is substantive for
timer advancement. -/
theorem rpi5Restrictive_adapterAdvanceTimer_preserves
    (st st' : SystemState) (ticks : Nat)
    (hInv : proofLayerInvariantBundle st)
    (hOk : adapterAdvanceTimer rpi5RuntimeContractRestrictive ticks st = .ok ((), st')) :
    proofLayerInvariantBundle st' :=
  adapterAdvanceTimer_ok_preserves_proofLayerInvariantBundle
    rpi5RuntimeContractRestrictive rpi5RestrictiveAdapterProofHooks
    ticks st st' hInv hOk

/-- WS-H15d/A-33: End-to-end register write preservation for RPi5 (vacuous).
The restrictive contract rejects all register writes; the theorem is
vacuously true because no successful write path exists. -/
theorem rpi5Restrictive_adapterWriteRegister_preserves
    (st st' : SystemState) (reg : SeLe4n.RegName) (value : SeLe4n.RegValue)
    (hInv : proofLayerInvariantBundle st)
    (hOk : adapterWriteRegister rpi5RuntimeContractRestrictive reg value st = .ok ((), st')) :
    proofLayerInvariantBundle st' :=
  adapterWriteRegister_ok_preserves_proofLayerInvariantBundle
    rpi5RuntimeContractRestrictive rpi5RestrictiveAdapterProofHooks
    reg value st st' hInv hOk

/-- WS-H15d/A-33: End-to-end memory read preservation for RPi5.
Read operations are state-preserving — the pre-state invariant carries
through directly. -/
theorem rpi5Restrictive_adapterReadMemory_preserves
    (st st' : SystemState) (addr : SeLe4n.PAddr) (byte : UInt8)
    (hInv : proofLayerInvariantBundle st)
    (hOk : adapterReadMemory rpi5RuntimeContractRestrictive addr st = .ok (byte, st')) :
    proofLayerInvariantBundle st' :=
  adapterReadMemory_ok_preserves_proofLayerInvariantBundle
    rpi5RuntimeContractRestrictive rpi5RestrictiveAdapterProofHooks
    addr st st' byte hInv hOk

/-- X1-F: End-to-end context-switch preservation for RPi5 (vacuous).
The restrictive contract rejects all register-context transitions, so
`adapterContextSwitch` always fails — the theorem is vacuously true. -/
theorem rpi5Restrictive_adapterContextSwitch_preserves
    (st st' : SystemState) (newTid : SeLe4n.ThreadId) (newRegs : SeLe4n.RegisterFile)
    (hInv : proofLayerInvariantBundle st)
    (hOk : adapterContextSwitch rpi5RuntimeContractRestrictive newTid newRegs st = .ok ((), st')) :
    proofLayerInvariantBundle st' :=
  adapterContextSwitch_ok_preserves_proofLayerInvariantBundle
    rpi5RuntimeContractRestrictive rpi5RestrictiveAdapterProofHooks
    newTid newRegs st st' hInv hOk

-- ============================================================================
-- AG7-D: Production AdapterProofHooks for rpi5RuntimeContract
-- ============================================================================

open SeLe4n.Kernel in
/-- AG7-D: Extract `contextMatchesCurrent` from the production contract's
    `registerContextStablePred` applied to `writeRegisterState`.
    `writeRegisterState` doesn't change `scheduler.current` or `objects`, so
    if the check passes, the register match implies `contextMatchesCurrent`. -/
private theorem registerContextStable_writeRegister_contextMatch
    (reg : SeLe4n.RegName) (value : SeLe4n.RegValue) (st : SystemState)
    (hStable : registerContextStablePred st (writeRegisterState reg value st)) :
    contextMatchesCurrent (writeRegisterState reg value st) := by
  -- registerContextStableCheck examines post-state; writeRegisterState only changes regs
  -- When check passes for some tid / .tcb tcb case, the && chain has regs == ctx as first conjunct
  unfold contextMatchesCurrent; simp only [writeRegisterState]
  match hCurr : st.scheduler.current with
  | none => simp
  | some tid =>
    simp only []
    match hObj : st.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
      simp only []
      -- Goal: (writeReg ... == tcb.registerContext) = true
      -- Extract register match from the && chain in registerContextStableCheck
      unfold registerContextStablePred registerContextStableCheck at hStable
      simp only [writeRegisterState, hCurr, hObj] at hStable
      -- hStable : (regs == ctx && ...) = true; Bool.and_eq_true decomposes
      simp only [Bool.and_eq_true] at hStable
      exact hStable.1.1.1.1.1
    | some (.endpoint _) | some (.notification _) | some (.cnode _) |
      some (.vspaceRoot _) | some (.schedContext _) | some (.untyped _) | none =>
      trivial

open SeLe4n.Kernel in
/-- AG7-D: Production `AdapterProofHooks` for `rpi5RuntimeContract`.

The production contract uses substantive `registerContextStablePred` that
validates 6 conditions on the post-state's current thread. The proof hooks
extract these conditions and delegate to the generic preservation theorems
in `Invariant.lean`.

- **Timer**: delegates to `advanceTimerState_preserves_proofLayerInvariantBundle`
- **Register write**: extracts `contextMatchesCurrent` from the contract check
  and delegates to `writeRegisterState_preserves_proofLayerInvariantBundle`
- **Memory read**: state-preserving (identity)
- **Context switch**: extracts all 6 TCB conditions from the contract check
  and delegates to `contextSwitchState_preserves_proofLayerInvariantBundle` -/
def rpi5ProductionAdapterProofHooks :
    AdapterProofHooks rpi5RuntimeContract where
  preserveAdvanceTimer := fun ticks st hInv _ _ =>
    advanceTimerState_preserves_proofLayerInvariantBundle ticks st hInv
  preserveWriteRegister := fun reg value st hInv hStable =>
    writeRegisterState_preserves_proofLayerInvariantBundle reg value st hInv
      (registerContextStable_writeRegister_contextMatch reg value st hStable)
  preserveReadMemory := fun _ st hInv _ => hInv
  preserveContextSwitch := fun newTid newRegs st hInv hStable => by
    -- Save raw check for budget bridge before decomposition
    have hRaw : registerContextStableCheck st (contextSwitchState newTid newRegs st) = true := by
      unfold rpi5RuntimeContract at hStable; exact hStable
    -- Extract all conditions from registerContextStablePred
    unfold rpi5RuntimeContract at hStable
    simp only [registerContextStablePred, registerContextStableCheck,
      contextSwitchState] at hStable
    -- Match on objects[newTid.toObjId]?
    match hObj : st.objects[newTid.toObjId]? with
    | some (.tcb tcb) =>
      simp only [hObj, Bool.and_eq_true] at hStable
      have hRegs : (newRegs == tcb.registerContext) = true :=
        hStable.1.1.1.1.1
      have hNotRunnable : newTid ∉ st.scheduler.runnable := by
        have h := hStable.1.1.1.1.2; simp at h; exact h
      have hTimeSlice : tcb.timeSlice > 0 := by
        have h := hStable.1.1.1.2; simp at h; exact h
      have hIpcReady : tcb.ipcState = .ready := by
        have h := hStable.1.1.2; exact eq_of_beq h
      have hDeadline : tcb.deadline.toNat = 0 := by
        have h := hStable.1.2; exact eq_of_beq h
      have hBudgetPost : currentBudgetPositive (contextSwitchState newTid newRegs st) :=
        registerContextStableCheck_budget newTid newRegs st tcb hObj hRaw
      exact contextSwitchState_preserves_proofLayerInvariantBundle
        newTid newRegs st tcb hInv hObj hRegs hNotRunnable hTimeSlice
        hIpcReady hDeadline hBudgetPost
    | some (.endpoint _) | some (.notification _) | some (.cnode _) |
      some (.vspaceRoot _) | some (.schedContext _) | some (.untyped _) | none =>
      simp [hObj] at hStable

/-- AG7-D/F: End-to-end context-switch preservation for RPi5 production contract.
    When `adapterContextSwitch` succeeds under the production runtime contract,
    the post-state satisfies `proofLayerInvariantBundle`. This is the key
    theorem for hardware-binding correctness: the production contract's
    substantive `registerContextStablePred` validates all 6 TCB conditions,
    and the proof hooks compose them with the generic preservation lemma. -/
theorem rpi5Production_adapterContextSwitch_preserves
    (st st' : SystemState) (newTid : SeLe4n.ThreadId) (newRegs : SeLe4n.RegisterFile)
    (hInv : proofLayerInvariantBundle st)
    (hOk : adapterContextSwitch rpi5RuntimeContract newTid newRegs st = .ok ((), st')) :
    proofLayerInvariantBundle st' :=
  adapterContextSwitch_ok_preserves_proofLayerInvariantBundle
    rpi5RuntimeContract rpi5ProductionAdapterProofHooks
    newTid newRegs st st' hInv hOk

/-- AG7-D: End-to-end timer preservation for RPi5 production contract. -/
theorem rpi5Production_adapterAdvanceTimer_preserves
    (st st' : SystemState) (ticks : Nat)
    (hInv : proofLayerInvariantBundle st)
    (hOk : adapterAdvanceTimer rpi5RuntimeContract ticks st = .ok ((), st')) :
    proofLayerInvariantBundle st' :=
  adapterAdvanceTimer_ok_preserves_proofLayerInvariantBundle
    rpi5RuntimeContract rpi5ProductionAdapterProofHooks
    ticks st st' hInv hOk

/-- AG7-D: End-to-end register write preservation for RPi5 production contract.
    Unlike the restrictive contract, the production contract permits register
    writes when the post-state satisfies `registerContextStablePred`. -/
theorem rpi5Production_adapterWriteRegister_preserves
    (st st' : SystemState) (reg : SeLe4n.RegName) (value : SeLe4n.RegValue)
    (hInv : proofLayerInvariantBundle st)
    (hOk : adapterWriteRegister rpi5RuntimeContract reg value st = .ok ((), st')) :
    proofLayerInvariantBundle st' :=
  adapterWriteRegister_ok_preserves_proofLayerInvariantBundle
    rpi5RuntimeContract rpi5ProductionAdapterProofHooks
    reg value st st' hInv hOk

end SeLe4n.Platform.RPi5
