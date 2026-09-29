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

Words `0`–`30` are `x0`–`x30`, `31` is `SP_EL0`, `32` is `ELR_EL1`, `33` is
`SPSR_EL1` and `34` is `TPIDR_EL0` — the order of `TrapFrame`'s fields, which
the HAL's `trap_frame_word` reads by the same index.

`TPIDR_EL0` is in the layout because EL0 writes it with no trap, so it is part
of a thread's context whether the model names it or not: a switch that leaves it
in the core hands one thread's value to the next.  It was absent until v0.36.30,
and every other register EL0 can write is either in this layout or in the lazily
switched FP/SIMD context (WS-BP BP7.9).
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- The number of words a thread's context occupies in the trap frame. -/
def trapFrameWordCount : Nat := 35

/-- The index of `SP_EL0` in the trap frame's word layout. -/
def trapFrameSpWord : Nat := 31

/-- The index of `ELR_EL1` (the program counter the thread resumes at). -/
def trapFramePcWord : Nat := 32

/-- The index of `SPSR_EL1` (the processor state the thread resumes with). -/
def trapFramePstateWord : Nat := 33

/-- The index of `TPIDR_EL0` (the thread pointer the thread resumes with). -/
def trapFrameTpidrWord : Nat := 34

/-- **The register file a trap frame holds**, from its words (`word i` is the
`i`-th word of the layout above).  `x31` — the zero register's index — reads as
zero. -/
def registerFileOfTrapWords (word : Nat → UInt64) : SeLe4n.RegisterFile :=
  { pc := ⟨(word trapFramePcWord).toNat⟩
    sp := ⟨(word trapFrameSpWord).toNat⟩
    gpr := fun r => if r.val < 31 then ⟨(word r.val).toNat⟩ else ⟨0⟩
    pstate := ⟨(word trapFramePstateWord).toNat⟩
    tpidr := ⟨(word trapFrameTpidrWord).toNat⟩ }

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

/-- **PR #904 review (`v0.36.41`): save a vacated core's frame into the thread
that was running there.**  A remote deschedule clears core `c`'s `current` slot
while `c`'s hardware still runs the thread at EL0, so the next exception `c`
takes from EL0 carries that thread's live registers and the slot names nobody.
`saveTrapFrameOnCore` saves nothing then (it is keyed on the slot), and the
frame used to be dropped — the thread later resumed from its stale saved
context, rewinding or corrupting it.  This step writes the frame into the core's
**resident** thread (`MachineState.residentOnCore`), the thread the core's last
restore resumed; the bank is left alone, since no thread is current on `c`.

`saved` is the context to record, which is the trapped frame except for a
syscall — the syscall entry passes the frame rewound to the `SVC`
(`restartAtSvc`), so the thread re-issues the syscall its remote deschedule
interrupted rather than resuming past it with its arguments as a result. -/
def saveVacatedFrameOnCore (st : SystemState) (c : CoreId) (rf saved : SeLe4n.RegisterFile) :
    SystemState :=
  if trapFromEl0 rf then
    match st.scheduler.currentOnCore c, st.machine.residentOnCore c with
    | none, some tid =>
      match st.getTcb? tid with
      | some _ => st.updateTcb tid fun t => { t with registerContext := saved }
      | none => st
    | _, _ => st
  else st

/-- **The frame of a syscall, rewound to its `SVC`** — the program counter four
bytes back, so a resume re-issues the syscall (`Platform.FFI.svcFaultIP`'s
arithmetic, on the saved context). -/
def restartAtSvc (rf : SeLe4n.RegisterFile) : SeLe4n.RegisterFile :=
  { rf with pc := ⟨rf.pc.val - 4⟩ }

/-- **The save an entry performs**: the captured frame, if the HAL published
one (`Platform.FFI.captureTrapFrame`); a handler with no frame saves nothing.
The current thread's frame is `saveTrapFrameOnCore`'s; a vacated core's is the
resident thread's (`saveVacatedFrameOnCore`). -/
def saveCapturedTrapFrame (st : SystemState) (c : CoreId) :
    Option SeLe4n.RegisterFile → SystemState
  | none => st
  | some rf => saveVacatedFrameOnCore (saveTrapFrameOnCore st c rf) c rf rf

/-- **The syscall entry's save**: `saveCapturedTrapFrame`, with a vacated core's
frame rewound to the `SVC` (`restartAtSvc`). -/
def saveCapturedSyscallFrame (st : SystemState) (c : CoreId) :
    Option SeLe4n.RegisterFile → SystemState
  | none => st
  | some rf => saveVacatedFrameOnCore (saveTrapFrameOnCore st c rf) c rf (restartAtSvc rf)

/-- A core with a current thread saves nothing through the vacated path. -/
theorem saveVacatedFrameOnCore_of_current (st : SystemState) (c : CoreId)
    (rf saved : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some tid) :
    saveVacatedFrameOnCore st c rf saved = st := by
  unfold saveVacatedFrameOnCore; split <;> simp [hCur]

/-- **The payoff**: on a vacated core, a frame from EL0 is saved into the
resident thread's context — nothing is dropped. -/
theorem saveVacatedFrameOnCore_saves (st : SystemState) (c : CoreId)
    (rf saved : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hEl0 : trapFromEl0 rf = true) (hCur : st.scheduler.currentOnCore c = none)
    (hRes : st.machine.residentOnCore c = some tid) (hTcb : st.getTcb? tid = some tcb)
    (hInv : st.objects.invExt) :
    (saveVacatedFrameOnCore st c rf saved).getTcb? tid =
      some { tcb with registerContext := saved } := by
  simp only [saveVacatedFrameOnCore, hEl0, hCur, hRes, hTcb, if_true]
  rw [SystemState.updateTcb_getTcb?_self st tid _ hInv, hTcb]; rfl

/-- The vacated save writes no scheduler state. -/
theorem saveVacatedFrameOnCore_scheduler (st : SystemState) (c : CoreId)
    (rf saved : SeLe4n.RegisterFile) :
    (saveVacatedFrameOnCore st c rf saved).scheduler = st.scheduler := by
  unfold saveVacatedFrameOnCore
  split
  · split
    · split
      · simp [SystemState.updateTcb_scheduler]
      · rfl
    · rfl
  · rfl

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
