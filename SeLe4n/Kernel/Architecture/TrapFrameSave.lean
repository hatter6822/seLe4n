-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

/-!
# WS-BP BP7.3 — the whole outgoing frame, saved at every kernel entry

A thread's context is its general-purpose registers `x0`–`x30`, its stack
pointer (`SP_EL0`), its program counter (`ELR_EL1`) and its processor state
(`SPSR_EL1`).  The trap assembly saves every one of them into the in-flight
`TrapFrame` (`rust/sele4n-hal/src/trap.S`), and until this cut the Lean kernel
read back only the syscall window — `x0`–`x5` and `x7`
(`Platform.FFI.writeFfiRegistersToTcb`) — so the executing core's register bank
(`MachineState.regsOnCore`) and the thread's saved `registerContext` were stale
for `x6`, `x8`–`x30`, `SP`, `PC` and the flags.  A context switch saves the
outgoing thread from that bank (`saveOutgoingContextOnCore`), so a thread
switched out and back in would have resumed with another state.

`saveTrapFrameOnCore` is the fix: at every kernel entry that can switch threads,
the whole frame — read from the HAL word by word (`trapFrameWord`, the
`TrapFrame` layout) — is written into **both** the executing core's bank and the
current thread's `registerContext`, so `contextMatchesCurrentOnCore` holds on
the state the transition runs on and a switch saves exactly the registers the
thread trapped with.

## Only a thread's frame is saved

A frame is a thread's only when the trap was taken **from EL0** (`SPSR_EL1.M[3:0]
= 0b0000`, `EL0t`, `trapFromEl0`).  A timer interrupt taken while the kernel
itself is running — an idle core waiting at EL1 — carries the kernel's own
registers, and writing those into a thread would hand the kernel's stack
pointer and return address to user mode.  Such a frame saves nothing.

## Word layout

Words `0`–`30` are `x0`–`x30`, `31` is `SP_EL0`, `32` is `ELR_EL1` and `33` is
`SPSR_EL1` — the order of `TrapFrame`'s fields, which the HAL's
`trap_frame_word` reads by the same index.
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- The number of words a thread's context occupies in the trap frame. -/
def trapFrameWordCount : Nat := 34

/-- The index of `SP_EL0` in the trap frame's word layout. -/
def trapFrameSpWord : Nat := 31

/-- The index of `ELR_EL1` (the program counter the thread resumes at). -/
def trapFramePcWord : Nat := 32

/-- The index of `SPSR_EL1` (the processor state the thread resumes with). -/
def trapFramePstateWord : Nat := 33

/-- **The register file a trap frame holds**, from its words (`word i` is the
`i`-th word of the layout above).  `x31` — the zero register's index — reads as
zero. -/
def registerFileOfTrapWords (word : Nat → UInt64) : SeLe4n.RegisterFile :=
  { pc := ⟨(word trapFramePcWord).toNat⟩
    sp := ⟨(word trapFrameSpWord).toNat⟩
    gpr := fun r => if r.val < 31 then ⟨(word r.val).toNat⟩ else ⟨0⟩
    pstate := ⟨(word trapFramePstateWord).toNat⟩ }

/-- **Was the trap taken from EL0?**  `SPSR_EL1.M[3:0] = 0b0000` (`EL0t`): the
frame is a thread's.  Any other mode is the kernel's own. -/
def trapFromEl0 (rf : SeLe4n.RegisterFile) : Bool :=
  rf.pstate.val % 16 == 0

/-- **WS-BP BP7.3: save the frame a thread trapped with.**  When the trap was
taken from EL0 and core `c` runs a thread with a TCB, both the core's register
bank and the thread's saved `registerContext` become `rf`; otherwise nothing is
written. -/
def saveTrapFrameOnCore (st : SystemState) (c : CoreId) (rf : SeLe4n.RegisterFile) :
    SystemState :=
  if trapFromEl0 rf then
    match st.scheduler.currentOnCore c with
    | some tid =>
      match st.getTcb? tid with
      | some _ =>
        let st1 := st.updateTcb tid fun t => { t with registerContext := rf }
        { st1 with machine := st1.machine.setRegsOnCore c rf }
      | none => st
    | none => st
  else st

/-- **The save an entry performs**: the captured frame, if the HAL published
one (`Platform.FFI.captureTrapFrame`); a handler with no frame saves nothing. -/
def saveCapturedTrapFrame (st : SystemState) (c : CoreId) :
    Option SeLe4n.RegisterFile → SystemState
  | none => st
  | some rf => saveTrapFrameOnCore st c rf

/-- A frame taken at EL1 saves nothing. -/
theorem saveTrapFrameOnCore_of_not_el0 (st : SystemState) (c : CoreId)
    (rf : SeLe4n.RegisterFile) (h : trapFromEl0 rf = false) :
    saveTrapFrameOnCore st c rf = st := by
  simp [saveTrapFrameOnCore, h]

/-- A core running no thread saves nothing. -/
theorem saveTrapFrameOnCore_of_idle (st : SystemState) (c : CoreId)
    (rf : SeLe4n.RegisterFile) (h : st.scheduler.currentOnCore c = none) :
    saveTrapFrameOnCore st c rf = st := by
  unfold saveTrapFrameOnCore; split <;> simp [h]

/-- **The save, when it writes**: the current thread's TCB with its
`registerContext` replaced, and the core's bank. -/
theorem saveTrapFrameOnCore_eq_of_current (st : SystemState) (c : CoreId)
    (rf : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hEl0 : trapFromEl0 rf = true) (hCur : st.scheduler.currentOnCore c = some tid)
    (hTcb : st.getTcb? tid = some tcb) :
    saveTrapFrameOnCore st c rf =
      let st1 := st.updateTcb tid fun t => { t with registerContext := rf }
      { st1 with machine := st1.machine.setRegsOnCore c rf } := by
  simp [saveTrapFrameOnCore, hEl0, hCur, hTcb]

/-- The save writes no scheduler state. -/
theorem saveTrapFrameOnCore_scheduler (st : SystemState) (c : CoreId)
    (rf : SeLe4n.RegisterFile) :
    (saveTrapFrameOnCore st c rf).scheduler = st.scheduler := by
  unfold saveTrapFrameOnCore
  split
  · split
    · split
      · simp [SystemState.updateTcb_scheduler]
      · rfl
    · rfl
  · rfl

/-- The save is either the identity or a TCB rewrite followed by a bank write:
every field but `objects` and `machine` is the input's. -/
theorem saveTrapFrameOnCore_frame (st : SystemState) (c : CoreId)
    (rf : SeLe4n.RegisterFile) :
    saveTrapFrameOnCore st c rf = st ∨
    ∃ tid tcb, trapFromEl0 rf = true ∧ st.scheduler.currentOnCore c = some tid ∧
      st.getTcb? tid = some tcb ∧
      saveTrapFrameOnCore st c rf =
        { st.updateTcb tid (fun t => { t with registerContext := rf }) with
            machine := st.machine.setRegsOnCore c rf } := by
  by_cases hEl0 : trapFromEl0 rf = true
  · cases hCur : st.scheduler.currentOnCore c with
    | none => exact Or.inl (saveTrapFrameOnCore_of_idle st c rf hCur)
    | some tid =>
      cases hTcb : st.getTcb? tid with
      | none => left; simp [saveTrapFrameOnCore, hEl0, hCur, hTcb]
      | some tcb =>
        right
        refine ⟨tid, tcb, hEl0, rfl, hTcb, ?_⟩
        rw [saveTrapFrameOnCore_eq_of_current st c rf tid tcb hEl0 hCur hTcb]
        simp [SystemState.updateTcb_machine]
  · exact Or.inl (saveTrapFrameOnCore_of_not_el0 st c rf (by simpa using hEl0))

/-- The object store stays well-formed. -/
theorem saveTrapFrameOnCore_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (rf : SeLe4n.RegisterFile) (hInv : st.objects.invExt) :
    (saveTrapFrameOnCore st c rf).objects.invExt := by
  rcases saveTrapFrameOnCore_frame st c rf with h | ⟨tid, tcb, _, _, _, h⟩
  · rw [h]; exact hInv
  · rw [h]; exact SystemState.updateTcb_preserves_objects_invExt st tid _ hInv

/-- **The payoff**: after a save the core's bank is the frame, and the current
thread's saved context is the same frame. -/
theorem saveTrapFrameOnCore_saves (st : SystemState) (c : CoreId)
    (rf : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hEl0 : trapFromEl0 rf = true) (hCur : st.scheduler.currentOnCore c = some tid)
    (hTcb : st.getTcb? tid = some tcb) (hInv : st.objects.invExt) :
    (saveTrapFrameOnCore st c rf).machine.regsOnCore c = rf ∧
    (saveTrapFrameOnCore st c rf).getTcb? tid = some { tcb with registerContext := rf } := by
  rw [saveTrapFrameOnCore_eq_of_current st c rf tid tcb hEl0 hCur hTcb]
  refine ⟨by simp, ?_⟩
  show (st.updateTcb tid fun t => { t with registerContext := rf }).getTcb? tid = _
  rw [SystemState.updateTcb_getTcb?_self st tid _ hInv, hTcb]; rfl

end SeLe4n.Kernel.Architecture
