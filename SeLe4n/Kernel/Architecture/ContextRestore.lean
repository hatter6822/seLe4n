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
exactly that caller resuming later with its own arguments as the result.

`caller?` is the pre-entry thread of core `c`.  The commit seams capture it
before the transition consumes the pre-state, so the pre-state is not kept
alive across the transition (KSC-1). -/
def stageCallerReturnFor (caller? : Option SeLe4n.ThreadId) (post : SystemState) (c : CoreId) :
    SyscallOutcome → SystemState
  | .returns f =>
    match caller? with
    | some tid =>
      let s1 := writeReturnFrameToTcb post tid f
      if post.scheduler.currentOnCore c = some tid then
        { s1 with machine := s1.machine.setRegsOnCore c (stageFrameRegs (s1.machine.regsOnCore c) f) }
      else s1
    | none => post
  | .blocks => post
  | .faulted => post

/-- `stageCallerReturnFor` as compiled: the current-thread test through
`Option.isEqSome`, so it builds no `some tid` and no equality closure.
WS-ZA ZA2.2. -/
def stageCallerReturnForImpl (caller? : Option SeLe4n.ThreadId) (post : SystemState)
    (c : CoreId) : SyscallOutcome → SystemState
  | .returns f =>
    match caller? with
    | some tid =>
      let s1 := writeReturnFrameToTcb post tid f
      if (post.scheduler.currentOnCore c).isEqSome tid then
        { s1 with machine := s1.machine.setRegsOnCore c (stageFrameRegs (s1.machine.regsOnCore c) f) }
      else s1
    | none => post
  | .blocks => post
  | .faulted => post

@[csimp] theorem stageCallerReturnFor_eq_impl :
    @stageCallerReturnFor = @stageCallerReturnForImpl := by
  funext caller? post c o
  have hEq : ∀ (cur : Option SeLe4n.ThreadId) (tid : SeLe4n.ThreadId),
      (cur.isEqSome tid = true) = (cur = some tid) := by
    intro cur tid; cases cur <;> simp [Option.isEqSome]
  cases o <;> cases caller? <;> simp only [stageCallerReturnFor, stageCallerReturnForImpl, hEq]

/-- `stageCallerReturnFor` with the caller read off the pre-state. -/
def stageCallerReturn (pre post : SystemState) (c : CoreId) (o : SyscallOutcome) :
    SystemState :=
  stageCallerReturnFor (pre.scheduler.currentOnCore c) post c o

/-- A blocked or faulted caller stages nothing. -/
theorem stageCallerReturn_blocks (pre post : SystemState) (c : CoreId) :
    stageCallerReturn pre post c .blocks = post := rfl

theorem stageCallerReturn_faulted (pre post : SystemState) (c : CoreId) :
    stageCallerReturn pre post c .faulted = post := rfl

/-- **WS-LS LS2.3**: staging a caller's result writes a register context and
the core's bank, never the scheduler — whichever caller the seam captured. -/
theorem stageCallerReturnFor_scheduler (caller? : Option SeLe4n.ThreadId)
    (post : SystemState) (c : CoreId) (o : SyscallOutcome) :
    (stageCallerReturnFor caller? post c o).scheduler = post.scheduler := by
  unfold stageCallerReturnFor
  split
  · split
    · split
      · simp [writeReturnFrameToTcb, SystemState.updateTcb_scheduler]
      · simp [writeReturnFrameToTcb, SystemState.updateTcb_scheduler]
    · rfl
  · rfl
  · rfl

/-- The staging writes no scheduler state. -/
theorem stageCallerReturn_scheduler (pre post : SystemState) (c : CoreId)
    (o : SyscallOutcome) : (stageCallerReturn pre post c o).scheduler = post.scheduler :=
  stageCallerReturnFor_scheduler _ post c o

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
  simp only [stageCallerReturn, stageCallerReturnFor, hPre, hPost, if_true]
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
  simp only [stageCallerReturn, stageCallerReturnFor, hPre, hPost, if_false]
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
  /-- The kernel's wait loop at EL1: the core's idle thread, or a core whose
  slot is empty. -/
  | idle
  /-- The core's current thread has no TCB (a broken state the invariants
  exclude): nothing to install. -/
  | none
  deriving Inhabited

/-- **WS-BP BP7.4: the target the committed state names for core `c`.**

A core with no current thread resumes the wait loop.  Nothing else is safe: the
trap layer returns through the frame it captured when no restore is installed,
and on an empty core that frame belongs to the thread the model just took off
it (a block, a deschedule, a domain switch or an eviction with nothing
runnable in the active domain, where the idle thread is not admitted). -/
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
  | none => .idle

/-- `restoreTargetOnCore` as compiled: the translation words handed straight to
the `.user` constructor (`threadTranslationOperandsK`), so a caller that
matches the target, and a target built, cost no pair and no boxed words.
WS-ZA ZA3.1. -/
@[inline] def restoreTargetOnCoreImpl (st : SystemState) (c : CoreId) : RestoreTarget :=
  match st.scheduler.currentOnCore c with
  | some tid =>
    if SeLe4n.Kernel.isIdleThreadId tid then .idle
    else
      match st.getTcb? tid with
      | some tcb =>
        threadTranslationOperandsK st tid fun tableBase asid =>
          .user tcb.registerContext tableBase asid (fpLiveFor st c tid)
      | none => .none
  | none => .idle

@[csimp] theorem restoreTargetOnCore_eq_impl : @restoreTargetOnCore = @restoreTargetOnCoreImpl := by
  funext st c
  simp only [restoreTargetOnCore, restoreTargetOnCoreImpl, threadTranslationOperandsK_eq]

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

/-- **The words a context occupies in the trap frame**: the register file's own
words, in the layout `SeLe4n.RegisterFile` declares. -/
@[inline] def trapWordsOfRegisterFile (rf : SeLe4n.RegisterFile) (i : Nat) : UInt64 :=
  rf.word i

/-- **Save then restore is the identity**: the register file a context's words
describe is that context — the file holds machine words, so nothing narrows. -/
@[simp] theorem registerFileOfTrapWords_trapWordsOfRegisterFile (rf : SeLe4n.RegisterFile) :
    registerFileOfTrapWords (trapWordsOfRegisterFile rf) = rf :=
  SeLe4n.RegisterFile.ofWords_word rf

/-- **The context the HAL installs**, as the boundary carries it: the register
file's thirty-five layout words in one `TrapContext` (`Platform.FFI.restoreTrapFrame`
hands it to the HAL in one call). -/
def trapContextOfRegisterFile (rf : SeLe4n.RegisterFile) : TrapContext :=
  TrapContext.ofWords (trapWordsOfRegisterFile rf)

/-- **The bulk restore stages exactly the words the layout names** — word `i` of
the context handed over is `trapWordsOfRegisterFile rf i`, for every word of the
layout. -/
@[simp] theorem trapContextOfRegisterFile_word (rf : SeLe4n.RegisterFile) (i : Nat)
    (h : i < trapFrameWordCount) :
    (trapContextOfRegisterFile rf).word i = trapWordsOfRegisterFile rf i :=
  TrapContext.word_ofWords _ i h

/-- The words of the register file some words describe are those words, on the
layout. -/
theorem trapWordsOfRegisterFile_registerFileOfTrapWords (w : Nat → UInt64) (i : Nat)
    (h : i < trapFrameWordCount) :
    trapWordsOfRegisterFile (registerFileOfTrapWords w) i = w i :=
  SeLe4n.RegisterFile.word_ofWords w i h

/-- **Save then restore is the identity on the boundary representation**: a
context the HAL handed over, read as the model's register file and handed back,
is the same thirty-five words.  The words the HAL then installs are these, with
`SPSR_EL1` masked to the condition flags at the commit
(`rust/sele4n-hal/src/trap.rs`, `sanitise_user_spsr`), so the cross-language trip
is the identity on every word but `pstate`. -/
@[simp] theorem trapContextOfRegisterFile_registerFileOfTrapContext (c : TrapContext) :
    trapContextOfRegisterFile (registerFileOfTrapContext c) = c := by
  rw [trapContextOfRegisterFile, registerFileOfTrapContext]
  exact (TrapContext.ofWords_congr _ _ fun i h =>
    trapWordsOfRegisterFile_registerFileOfTrapWords c.word i h).trans (TrapContext.ofWords_word c)

/-- **Restore then save is the identity**: the context handed to the HAL, read
back as the model's register file, is the file that was restored — every one of
its thirty-five registers, with no hypothesis.  The HAL masks `pstate` to the
condition flags at the commit, so the cross-language trip is not the identity on
`pstate`. -/
@[simp] theorem registerFileOfTrapContext_trapContextOfRegisterFile (rf : SeLe4n.RegisterFile) :
    registerFileOfTrapContext (trapContextOfRegisterFile rf) = rf := by
  rw [trapContextOfRegisterFile, registerFileOfTrapContext_ofWords]
  exact SeLe4n.RegisterFile.ofWords_word rf

end SeLe4n.Kernel.Architecture
