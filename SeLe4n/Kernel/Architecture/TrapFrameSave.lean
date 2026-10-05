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
the whole frame — handed over by the HAL in one call (`TrapContext`, the
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
the HAL's `trap_frame_context` copies in the same order.

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

/-- **The context a trap frame carries, as the HAL hands it over** — the
thirty-five words of the layout above as fixed-width scalars, in layout order.

This is the boundary representation of a thread's context: the HAL moves the
whole of it across the FFI in **one** call each way (`Platform.FFI.ffiTrapContext`
in, `Platform.FFI.ffiRestoreStageContext` out), where the seam used to issue one
call per word.  A structure whose fields are all `UInt64` compiles to a single
constructor object with no object fields and `8 · 35` scalar bytes, field `i` at
byte offset `8 · i` — the layout `rust/sele4n-hal/src/ffi.rs` reads and writes
(`TRAP_CONTEXT_SCALAR_BYTES`).  The model's register file stays the proofs'
view of a context; `registerFileOfTrapContext` is the conversion. -/
structure TrapContext where
  /-- `x0`. -/
  x0 : UInt64
  /-- `x1`. -/
  x1 : UInt64
  /-- `x2`. -/
  x2 : UInt64
  /-- `x3`. -/
  x3 : UInt64
  /-- `x4`. -/
  x4 : UInt64
  /-- `x5`. -/
  x5 : UInt64
  /-- `x6`. -/
  x6 : UInt64
  /-- `x7`. -/
  x7 : UInt64
  /-- `x8`. -/
  x8 : UInt64
  /-- `x9`. -/
  x9 : UInt64
  /-- `x10`. -/
  x10 : UInt64
  /-- `x11`. -/
  x11 : UInt64
  /-- `x12`. -/
  x12 : UInt64
  /-- `x13`. -/
  x13 : UInt64
  /-- `x14`. -/
  x14 : UInt64
  /-- `x15`. -/
  x15 : UInt64
  /-- `x16`. -/
  x16 : UInt64
  /-- `x17`. -/
  x17 : UInt64
  /-- `x18`. -/
  x18 : UInt64
  /-- `x19`. -/
  x19 : UInt64
  /-- `x20`. -/
  x20 : UInt64
  /-- `x21`. -/
  x21 : UInt64
  /-- `x22`. -/
  x22 : UInt64
  /-- `x23`. -/
  x23 : UInt64
  /-- `x24`. -/
  x24 : UInt64
  /-- `x25`. -/
  x25 : UInt64
  /-- `x26`. -/
  x26 : UInt64
  /-- `x27`. -/
  x27 : UInt64
  /-- `x28`. -/
  x28 : UInt64
  /-- `x29`. -/
  x29 : UInt64
  /-- `x30`. -/
  x30 : UInt64
  /-- `SP_EL0` (word 31). -/
  sp : UInt64
  /-- `ELR_EL1`, the program counter (word 32). -/
  pc : UInt64
  /-- `SPSR_EL1`, the processor state (word 33). -/
  pstate : UInt64
  /-- `TPIDR_EL0`, the thread pointer (word 34). -/
  tpidr : UInt64

namespace TrapContext

/-- Word `i` of the layout; `0` past it. -/
def word (c : TrapContext) : Nat → UInt64
  | 0 => c.x0
  | 1 => c.x1
  | 2 => c.x2
  | 3 => c.x3
  | 4 => c.x4
  | 5 => c.x5
  | 6 => c.x6
  | 7 => c.x7
  | 8 => c.x8
  | 9 => c.x9
  | 10 => c.x10
  | 11 => c.x11
  | 12 => c.x12
  | 13 => c.x13
  | 14 => c.x14
  | 15 => c.x15
  | 16 => c.x16
  | 17 => c.x17
  | 18 => c.x18
  | 19 => c.x19
  | 20 => c.x20
  | 21 => c.x21
  | 22 => c.x22
  | 23 => c.x23
  | 24 => c.x24
  | 25 => c.x25
  | 26 => c.x26
  | 27 => c.x27
  | 28 => c.x28
  | 29 => c.x29
  | 30 => c.x30
  | 31 => c.sp
  | 32 => c.pc
  | 33 => c.pstate
  | 34 => c.tpidr
  | _ => 0

/-- The context whose word `i` is `w i`.  Inlined, so a caller's `w` is applied
at each index directly rather than through a closure. -/
@[inline] def ofWords (w : Nat → UInt64) : TrapContext :=
  ⟨w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7, w 8, w 9, w 10, w 11, w 12, w 13, w 14, w 15, w 16, w 17, w 18, w 19, w 20, w 21, w 22, w 23, w 24, w 25, w 26, w 27, w 28, w 29, w 30, w 31, w 32, w 33, w 34⟩

/-- **Encoding a context's words and decoding them is the identity.** -/
theorem ofWords_word (c : TrapContext) : ofWords c.word = c := by
  cases c; rfl

/-- **Decoding then encoding is the identity on the layout's words** — every
word below `trapFrameWordCount` crosses the boundary unchanged. -/
theorem word_ofWords (w : Nat → UInt64) :
    ∀ i, i < trapFrameWordCount → (ofWords w).word i = w i
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | 12, _ => rfl
  | 13, _ => rfl
  | 14, _ => rfl
  | 15, _ => rfl
  | 16, _ => rfl
  | 17, _ => rfl
  | 18, _ => rfl
  | 19, _ => rfl
  | 20, _ => rfl
  | 21, _ => rfl
  | 22, _ => rfl
  | 23, _ => rfl
  | 24, _ => rfl
  | 25, _ => rfl
  | 26, _ => rfl
  | 27, _ => rfl
  | 28, _ => rfl
  | 29, _ => rfl
  | 30, _ => rfl
  | 31, _ => rfl
  | 32, _ => rfl
  | 33, _ => rfl
  | 34, _ => rfl
  | n + 35, h => absurd h (by unfold trapFrameWordCount; omega)

end TrapContext

/-- **The register file a trap context holds** — the model's view of the words
the HAL handed over: `registerFileOfTrapWords` on `TrapContext.word`
(`registerFileOfTrapContext_eq`), with the named registers read off their
fields. -/
def registerFileOfTrapContext (c : TrapContext) : SeLe4n.RegisterFile :=
  { pc := ⟨c.pc.toNat⟩
    sp := ⟨c.sp.toNat⟩
    gpr := fun r => if r.val < 31 then ⟨(c.word r.val).toNat⟩ else ⟨0⟩
    pstate := ⟨c.pstate.toNat⟩
    tpidr := ⟨c.tpidr.toNat⟩ }

/-- The context's register file is the one its words describe. -/
theorem registerFileOfTrapContext_eq (c : TrapContext) :
    registerFileOfTrapContext c = registerFileOfTrapWords c.word := rfl

/-- The bulk boundary loses nothing: a context built from words reads back as
the register file those words describe. -/
theorem registerFileOfTrapContext_ofWords (w : Nat → UInt64) :
    registerFileOfTrapContext (TrapContext.ofWords w) = registerFileOfTrapWords w := by
  have h := TrapContext.word_ofWords w
  simp only [registerFileOfTrapContext_eq, registerFileOfTrapWords, trapFramePcWord, trapFrameSpWord,
    trapFramePstateWord, trapFrameTpidrWord]
  rw [h 32 (by decide), h 31 (by decide), h 33 (by decide), h 34 (by decide)]
  congr 1
  funext r
  split
  · rename_i hr
    rw [h r.val (by unfold trapFrameWordCount; omega)]
  · rfl

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
