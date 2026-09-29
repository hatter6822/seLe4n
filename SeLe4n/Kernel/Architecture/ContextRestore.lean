-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.TrapFrameSave
import SeLe4n.Kernel.Architecture.SyscallReturn
import SeLe4n.Kernel.Architecture.HardwareTables
import SeLe4n.Kernel.Scheduler.IdleThread
import SeLe4n.Kernel.Architecture.FpContext

/-!
# WS-BP BP7.4 — what a core returns to, staged per core

A kernel entry ends by returning to whatever thread the committed state runs on
the executing core.  Two things decide what that is, and this module states
both.

## The caller's return frame is its context before anything else runs

A syscall that returns stages its result into the caller's saved registers
(`x0`–`x5`, `TCB.withReturnFrame`) — but only where an arm staged it, and never
into the core's register bank.  A context switch in the same entry saves the
outgoing thread **from the bank** (`saveOutgoingContextOnCore`), so a caller
preempted by the thread its own syscall woke would have its result overwritten
with its request registers.  `stageCallerReturn` writes the outcome's frame into
both the caller's context and the bank, while the caller is still the core's
current thread and before any local reschedule, so whatever happens next saves
the result.

## What the core resumes

`restoreTargetOnCore` reads the committed state: the core's current thread's
saved context and the translation it runs under (`threadTranslationOperands`),
or **idle** when that thread is the core's idle thread — which is the kernel's
own wait loop at EL1, never a context at EL0 — or **nothing** when the core runs
no thread.  The HAL stages it per core and commits it into the in-flight trap
frame (`Platform.FFI.restoreTrapFrame`), so the trap handler returns through the
thread the model chose rather than through whichever thread trapped.
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- The `RegisterFile` with a return frame in `x0`–`x5`. -/
abbrev stageFrameRegs (rf : SeLe4n.RegisterFile) (f : SyscallReturnFrame) : SeLe4n.RegisterFile :=
  rf.stageReturnFrame f

/-- **WS-BP BP7.4: the returning caller's result, staged where a switch saves
from.**  When the syscall returned a frame, the frame goes into the core's
pre-entry thread's saved context, and — while that thread is still the core's
current thread — into the core's bank as well.  A blocked or faulted caller
stages nothing.

**BP7.6: the frame goes into the context whether or not the caller is still
current.**  An arm may switch the caller out *inside* the syscall — a
`.tcbResume` of a higher-priority thread, a `.tcbSetPriority` that demotes the
caller below a queued thread — and the preempt saves the caller from the bank,
which holds its request registers.  Staging only a still-current caller left
exactly that caller resuming later with its own arguments as the result. -/
def stageCallerReturn (pre post : SystemState) (c : CoreId) :
    SyscallOutcome → SystemState
  | .returns f =>
    match pre.scheduler.currentOnCore c with
    | some tid =>
      let s1 := writeReturnFrameToTcb post tid f
      if post.scheduler.currentOnCore c = some tid then
        { s1 with machine := s1.machine.setRegsOnCore c (stageFrameRegs (s1.machine.regsOnCore c) f) }
      else s1
    | none => post
  | .blocks => post
  | .faulted => post

/-- A blocked or faulted caller stages nothing. -/
theorem stageCallerReturn_blocks (pre post : SystemState) (c : CoreId) :
    stageCallerReturn pre post c .blocks = post := rfl

theorem stageCallerReturn_faulted (pre post : SystemState) (c : CoreId) :
    stageCallerReturn pre post c .faulted = post := rfl

/-- The staging writes no scheduler state. -/
theorem stageCallerReturn_scheduler (pre post : SystemState) (c : CoreId)
    (o : SyscallOutcome) : (stageCallerReturn pre post c o).scheduler = post.scheduler := by
  unfold stageCallerReturn
  split
  · split
    · split
      · simp [writeReturnFrameToTcb, SystemState.updateTcb_scheduler]
      · simp [writeReturnFrameToTcb, SystemState.updateTcb_scheduler]
    · rfl
  · rfl
  · rfl

/-- **The payoff**: a caller still current on the core has its result in its
saved context and in the bank. -/
theorem stageCallerReturn_stages (pre post : SystemState) (c : CoreId)
    (f : SyscallReturnFrame) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hPre : pre.scheduler.currentOnCore c = some tid)
    (hPost : post.scheduler.currentOnCore c = some tid)
    (hTcb : post.getTcb? tid = some tcb) (hInv : post.objects.invExt) :
    (stageCallerReturn pre post c (.returns f)).getTcb? tid = some (tcb.withReturnFrame f) ∧
    (stageCallerReturn pre post c (.returns f)).machine.regsOnCore c =
      (post.machine.regsOnCore c).stageReturnFrame f := by
  simp only [stageCallerReturn, hPre, hPost, if_true]
  refine ⟨?_, ?_⟩
  · show (writeReturnFrameToTcb post tid f).getTcb? tid = _
    unfold writeReturnFrameToTcb
    rw [SystemState.updateTcb_getTcb?_self post tid _ hInv, hTcb]; rfl
  · simp [writeReturnFrameToTcb, SystemState.updateTcb_machine]

/-- **BP7.6: and a caller switched out inside its own syscall** has its result
in its saved context, so the thread that preempted it does not cost it the
answer. -/
theorem stageCallerReturn_stages_switched_out (pre post : SystemState) (c : CoreId)
    (f : SyscallReturnFrame) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hPre : pre.scheduler.currentOnCore c = some tid)
    (hPost : post.scheduler.currentOnCore c ≠ some tid)
    (hTcb : post.getTcb? tid = some tcb) (hInv : post.objects.invExt) :
    (stageCallerReturn pre post c (.returns f)).getTcb? tid = some (tcb.withReturnFrame f) := by
  simp only [stageCallerReturn, hPre, hPost, if_false]
  unfold writeReturnFrameToTcb
  rw [SystemState.updateTcb_getTcb?_self post tid _ hInv, hTcb]; rfl

/-- **What a core resumes when a kernel entry ends.** -/
inductive RestoreTarget where
  /-- A thread at EL0: its saved context, and the `TTBR0_EL1` operands of its
  address space (`threadTranslationOperands`).  **WS-BP BP7.9**: `fpLive` is
  whether the core's registers hold the thread's own FP/SIMD values
  (`fpLiveFor`) — the trap is lifted exactly then, and armed otherwise, so a
  thread never runs with another's FP/SIMD state accessible. -/
  | user (context : SeLe4n.RegisterFile) (tableBase asid : UInt64) (fpLive : Bool)
  /-- The core's idle thread: the kernel's wait loop at EL1. -/
  | idle
  /-- The core runs no thread: nothing to install. -/
  | none
  deriving Inhabited

/-- **WS-BP BP7.4: the target the committed state names for core `c`.** -/
def restoreTargetOnCore (st : SystemState) (c : CoreId) : RestoreTarget :=
  match st.scheduler.currentOnCore c with
  | some tid =>
    if SeLe4n.Kernel.isIdleThreadId tid then .idle
    else
      match st.getTcb? tid with
      | some tcb =>
        let ops := threadTranslationOperands st tid
        .user tcb.registerContext ops.1 ops.2 (fpLiveFor st c tid)
      | none => .none
  | none => .none

/-- An idle current thread resumes the wait loop, whatever its record holds. -/
theorem restoreTargetOnCore_idle (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some tid)
    (hIdle : SeLe4n.Kernel.isIdleThreadId tid = true) :
    restoreTargetOnCore st c = .idle := by
  simp [restoreTargetOnCore, hCur, hIdle]

/-- A thread resumes **its own** saved context under **its own** translation. -/
theorem restoreTargetOnCore_user (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (hCur : st.scheduler.currentOnCore c = some tid)
    (hIdle : SeLe4n.Kernel.isIdleThreadId tid = false) (hTcb : st.getTcb? tid = some tcb) :
    restoreTargetOnCore st c =
      .user tcb.registerContext (threadTranslationOperands st tid).1
        (threadTranslationOperands st tid).2 (fpLiveFor st c tid) := by
  simp [restoreTargetOnCore, hCur, hIdle, hTcb]

/-- **The words a context occupies in the trap frame**, the inverse of
`registerFileOfTrapWords` on the layout's thirty-five words. -/
def trapWordsOfRegisterFile (rf : SeLe4n.RegisterFile) (i : Nat) : UInt64 :=
  if i < 31 then (rf.gpr ⟨i⟩).val.toUInt64
  else if i = trapFrameSpWord then rf.sp.val.toUInt64
  else if i = trapFramePcWord then rf.pc.val.toUInt64
  else if i = trapFramePstateWord then rf.pstate.val.toUInt64
  else if i = trapFrameTpidrWord then rf.tpidr.val.toUInt64
  else 0

/-- **Save then restore is the identity** on a context whose registers fit in
64 bits — which every context a trap frame produced does. -/
theorem registerFileOfTrapWords_trapWordsOfRegisterFile (rf : SeLe4n.RegisterFile)
    (hGpr : ∀ r : SeLe4n.RegName, r.val < 31 → (rf.gpr r).val < 2 ^ 64)
    (hSp : rf.sp.val < 2 ^ 64) (hPc : rf.pc.val < 2 ^ 64) (hPs : rf.pstate.val < 2 ^ 64)
    (hTp : rf.tpidr.val < 2 ^ 64) :
    (registerFileOfTrapWords (trapWordsOfRegisterFile rf)).pc = rf.pc ∧
    (registerFileOfTrapWords (trapWordsOfRegisterFile rf)).sp = rf.sp ∧
    (registerFileOfTrapWords (trapWordsOfRegisterFile rf)).pstate = rf.pstate ∧
    (registerFileOfTrapWords (trapWordsOfRegisterFile rf)).tpidr = rf.tpidr ∧
    (∀ r : SeLe4n.RegName, r.val < 31 →
      (registerFileOfTrapWords (trapWordsOfRegisterFile rf)).gpr r = rf.gpr r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [registerFileOfTrapWords, trapWordsOfRegisterFile, trapFramePcWord, trapFrameSpWord,
      trapFramePstateWord]
    cases h : rf.pc; simp_all [Nat.toUInt64, Nat.mod_eq_of_lt]
  · simp only [registerFileOfTrapWords, trapWordsOfRegisterFile, trapFramePcWord, trapFrameSpWord,
      trapFramePstateWord]
    cases h : rf.sp; simp_all [Nat.toUInt64, Nat.mod_eq_of_lt]
  · simp only [registerFileOfTrapWords, trapWordsOfRegisterFile, trapFramePcWord, trapFrameSpWord,
      trapFramePstateWord]
    cases h : rf.pstate; simp_all [Nat.toUInt64, Nat.mod_eq_of_lt]
  · simp only [registerFileOfTrapWords, trapWordsOfRegisterFile, trapFramePcWord, trapFrameSpWord,
      trapFramePstateWord, trapFrameTpidrWord]
    cases h : rf.tpidr; simp_all [Nat.toUInt64, Nat.mod_eq_of_lt]
  · intro r hr
    have hLt := hGpr r hr
    simp only [registerFileOfTrapWords, trapWordsOfRegisterFile, hr, if_true]
    cases h : rf.gpr r
    rw [h] at hLt
    simp_all [Nat.toUInt64, Nat.mod_eq_of_lt]

end SeLe4n.Kernel.Architecture
