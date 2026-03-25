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
