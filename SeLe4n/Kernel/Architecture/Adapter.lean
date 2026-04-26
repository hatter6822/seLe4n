-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.Assumptions

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model

/-- Explicit architecture-binding failure branches for WS-M6-B adapter entrypoints. -/
inductive AdapterErrorKind where
  | invalidContext
  | unsupportedBinding
  deriving Repr, DecidableEq

/-- Deterministic mapping from adapter failures onto kernel-visible error tags. -/
def mapAdapterError : AdapterErrorKind → KernelError
  | .invalidContext => .illegalState
  | .unsupportedBinding => .notImplemented

/-- Deterministic pure timer projection used by runtime-boundary adapters. -/
def advanceTimerState (ticks : Nat) (st : SystemState) : SystemState :=
  { st with machine := { st.machine with timer := st.machine.timer + ticks } }

/-- Deterministic pure register projection used by runtime-boundary adapters. -/
def writeRegisterState (reg : SeLe4n.RegName) (value : SeLe4n.RegValue) (st : SystemState) : SystemState :=
  { st with machine := { st.machine with regs := SeLe4n.writeReg st.machine.regs reg value } }

/-- Runtime adapter: advance timer only for non-zero ticks and when contract monotonicity admits the step. -/
def adapterAdvanceTimer (contract : RuntimeBoundaryContract) (ticks : Nat) : Kernel Unit :=
  fun st =>
    if _hTicks : ticks = 0 then
      .error (mapAdapterError .invalidContext)
    else
      let st' := advanceTimerState ticks st
      letI : Decidable (contract.timerMonotonic st st') := contract.timerMonotonicDecidable st st'
      if contract.timerMonotonic st st' then
        .ok ((), st')
      else
        .error (mapAdapterError .unsupportedBinding)

/-- Runtime adapter: write a register only when context-stability admits the update. -/
def adapterWriteRegister
    (contract : RuntimeBoundaryContract)
    (reg : SeLe4n.RegName)
    (value : SeLe4n.RegValue) : Kernel Unit :=
  fun st =>
    let st' := writeRegisterState reg value st
    letI : Decidable (contract.registerContextStable st st') :=
      contract.registerContextStableDecidable st st'
    if contract.registerContextStable st st' then
      .ok ((), st')
    else
      .error (mapAdapterError .unsupportedBinding)

/-- Runtime adapter: memory read is admitted only when contract allows the address. -/
def adapterReadMemory
    (contract : RuntimeBoundaryContract)
    (addr : SeLe4n.PAddr) : Kernel UInt8 :=
  fun st =>
    letI : Decidable (contract.memoryAccessAllowed st addr) :=
      contract.memoryAccessAllowedDecidable st addr
    if contract.memoryAccessAllowed st addr then
      .ok (SeLe4n.readMem st.machine addr, st)
    else
      .error (mapAdapterError .unsupportedBinding)

theorem adapterAdvanceTimer_error_invalidContext
    (contract : RuntimeBoundaryContract)
    (st : SystemState) :
    adapterAdvanceTimer contract 0 st = .error (mapAdapterError .invalidContext) := by
  simp [adapterAdvanceTimer]

theorem adapterAdvanceTimer_error_unsupportedBinding
    (contract : RuntimeBoundaryContract)
    (ticks : Nat)
    (st : SystemState)
    (hTicks : ticks ≠ 0)
    (hReject : ¬ contract.timerMonotonic st (advanceTimerState ticks st)) :
    adapterAdvanceTimer contract ticks st = .error (mapAdapterError .unsupportedBinding) := by
  simp [adapterAdvanceTimer, hTicks, hReject]

theorem adapterWriteRegister_error_unsupportedBinding
    (contract : RuntimeBoundaryContract)
    (reg : SeLe4n.RegName)
    (value : SeLe4n.RegValue)
    (st : SystemState)
    (hReject : ¬ contract.registerContextStable st (writeRegisterState reg value st)) :
    adapterWriteRegister contract reg value st = .error (mapAdapterError .unsupportedBinding) := by
  simp [adapterWriteRegister, hReject]

theorem adapterReadMemory_error_unsupportedBinding
    (contract : RuntimeBoundaryContract)
    (addr : SeLe4n.PAddr)
    (st : SystemState)
    (hDeny : ¬ contract.memoryAccessAllowed st addr) :
    adapterReadMemory contract addr st = .error (mapAdapterError .unsupportedBinding) := by
  simp [adapterReadMemory, hDeny]

-- ============================================================================
-- X1-F: Context-switch atomic operation
-- ============================================================================

/-- X1-F: Atomic context-switch state transformation. Atomically:
    1. Loads `newRegs` (the incoming thread's saved register context) into
       the machine register file
    2. Updates `scheduler.current` to `newTid`

    By performing both updates in a single operation, `contextMatchesCurrent`
    is preserved by construction: the register file and scheduler state are
    updated together, so the post-state always satisfies
    `st'.machine.regs = tcb.registerContext` for the new current thread.

    **Caller obligations** (enforced at proof level via `AdapterProofHooks`):
    - `newRegs = tcb.registerContext` for the TCB at `newTid` (register match)
    - `newTid ∉ st.scheduler.runnable` (dequeue before dispatch, for
      `queueCurrentConsistent`)
    - The outgoing thread's registers must be saved to its TCB before this
      call (handled by `saveOutgoingContext` in the scheduler)

    This function is a pure state transformation. It does **not** save the
    outgoing thread's context, dequeue from the run queue, or read the
    object store. The scheduler (`Operations/Core.lean:schedule`) orchestrates
    these steps before calling `setCurrentThread`; this adapter provides
    a single-step alternative for hardware-binding paths.

    **Design note**: This replaces the individual `writeRegisterState` approach
    for context switches. Individual register writes break `contextMatchesCurrent`
    because the register file is partially updated while `scheduler.current`
    still points to the old thread. The atomic operation eliminates this window.

    **AI6-C (M-17) — TLB/ASID maintenance gap**: This context switch operation
    does not model TLB invalidation or ASID switching. On hardware, switching
    between threads in different address spaces requires ASID-tagged TLB
    management to prevent stale translation entries. ASID switching is performed
    by VSpace operations (`VSpaceBackend` / `VSpaceARMv8.lean`) independently
    of the context switch path. Atomic TLB + ASID + register context switch
    coordination closes DEF-A-M06 / DEF-A-M08 / DEF-A-M09 under AN9-A / AN9-B
    / AN9-C / AN9-D of docs/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md §12. -/
def contextSwitchState (newTid : SeLe4n.ThreadId) (newRegs : SeLe4n.RegisterFile)
    (st : SystemState) : SystemState :=
  { st with
      machine := { st.machine with regs := newRegs }
      scheduler := { st.scheduler with current := some newTid } }

/-- X1-F: Context-switch adapter operation. Performs an atomic context switch
    guarded by the runtime contract's `registerContextStable` predicate.

    The contract validates that the combined register-file load + scheduler
    update is admissible. For the RPi5 production contract, this succeeds
    when the loaded registers match the new thread's TCB context
    (`registerContextStablePred`). -/
def adapterContextSwitch
    (contract : RuntimeBoundaryContract)
    (newTid : SeLe4n.ThreadId) (newRegs : SeLe4n.RegisterFile) : Kernel Unit :=
  fun st =>
    let st' := contextSwitchState newTid newRegs st
    letI : Decidable (contract.registerContextStable st st') :=
      contract.registerContextStableDecidable st st'
    if contract.registerContextStable st st' then
      .ok ((), st')
    else
      .error (mapAdapterError .unsupportedBinding)

/-- X1-F: Context-switch error when contract rejects the transition. -/
theorem adapterContextSwitch_error_unsupportedBinding
    (contract : RuntimeBoundaryContract)
    (newTid : SeLe4n.ThreadId) (newRegs : SeLe4n.RegisterFile)
    (st : SystemState)
    (hReject : ¬ contract.registerContextStable st (contextSwitchState newTid newRegs st)) :
    adapterContextSwitch contract newTid newRegs st =
      .error (mapAdapterError .unsupportedBinding) := by
  simp [adapterContextSwitch, hReject]

theorem adapterReadMemory_ok_returns_machine_byte
    (contract : RuntimeBoundaryContract)
    (addr : SeLe4n.PAddr)
    (st st' : SystemState)
    (byte : UInt8)
    (hStep : adapterReadMemory contract addr st = .ok (byte, st')) :
    st' = st ∧ byte = SeLe4n.readMem st.machine addr := by
  by_cases hAllow : contract.memoryAccessAllowed st addr
  · simp [adapterReadMemory, hAllow] at hStep
    rcases hStep with ⟨hByte, hSt⟩
    exact ⟨hSt.symm, hByte.symm⟩
  · simp [adapterReadMemory, hAllow] at hStep

end SeLe4n.Kernel.Architecture
