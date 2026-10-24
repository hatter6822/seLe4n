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

/-- The staging of a current caller, as compiled: the frame written into the
caller's saved context in its object slot (`writeReturnFrameToTcb`) and into
the core's bank in its slot (`modifyRegsOnCore`).  Each holder keeps a file of
its own — the save writes one into each (`saveCapturedFrameImpl`) — so on an
exclusively owned state both are staged in place and nothing is allocated. -/
@[inline] def stageCurrentCallerReturn (post : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (f : SyscallReturnFrame) : SystemState :=
  let s1 := writeReturnFrameToTcb post tid f
  { s1 with machine := s1.machine.modifyRegsOnCore c (stageFrameRegs · f) }

/-- `stageCallerReturnFor` as compiled: the current-thread test through
`Option.isEqSome`, so it builds no `some tid` and no equality closure
(WS-ZA ZA2.2), and a current caller's context and bank each staged in its
slot (`stageCurrentCallerReturn`). -/
@[inline] def stageCallerReturnForImpl (caller? : Option SeLe4n.ThreadId) (post : SystemState)
    (c : CoreId) : SyscallOutcome → SystemState
  | .returns f =>
    match caller? with
    | some tid =>
      if (post.scheduler.currentOnCore c).isEqSome tid then
        stageCurrentCallerReturn post c tid f
      else writeReturnFrameToTcb post tid f
    | none => post
  | .blocks => post
  | .faulted => post

theorem stageCurrentCallerReturn_eq (post : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (f : SyscallReturnFrame) :
    stageCurrentCallerReturn post c tid f =
      let s1 := writeReturnFrameToTcb post tid f
      { s1 with machine := s1.machine.setRegsOnCore c (stageFrameRegs (s1.machine.regsOnCore c) f) } := by
  simp only [stageCurrentCallerReturn, MachineState.modifyRegsOnCore_eq]

@[csimp] theorem stageCallerReturnFor_eq_impl :
    @stageCallerReturnFor = @stageCallerReturnForImpl := by
  funext caller? post c o
  have hEq : ∀ (cur : Option SeLe4n.ThreadId) (tid : SeLe4n.ThreadId),
      (cur.isEqSome tid = true) = (cur = some tid) := by
    intro cur tid; cases cur <;> simp [Option.isEqSome]
  cases o <;> cases caller? <;>
    simp only [stageCallerReturnFor, stageCallerReturnForImpl, hEq, stageCurrentCallerReturn_eq]

/-- **A destroyed caller's return writes nothing**: a caller whose thread the
syscall finalised and retired — its own last capability deleted — has no TCB
left to take the frame and is current on no core, so neither its saved
context nor the core's register bank is written; the core resumes the
successor or the idle loop the reschedule chose. -/
theorem stageCallerReturnFor_destroyed (tid : SeLe4n.ThreadId) (post : SystemState)
    (c : CoreId) (o : SyscallOutcome) (hT : post.getTcb? tid = none)
    (hC : post.scheduler.currentOnCore c ≠ some tid) :
    stageCallerReturnFor (some tid) post c o = post := by
  cases o with
  | returns f =>
    simp only [stageCallerReturnFor, hC, if_false]
    exact SystemState.updateTcb_eq_self_of_none hT _
  | blocks => rfl
  | faulted => rfl

/-- WS-ZA ZA4: a return frame's six words written into `x0`-`x5`
(`stageReturnFrame` of the frame they make).  A call, so the file arrives as
an owned argument and an exclusive one is written in place. -/
def stageReturnWords (rf : SeLe4n.RegisterFile) (w0 w1 w2 w3 w4 w5 : UInt64) :
    SeLe4n.RegisterFile :=
  { rf with x0 := w0, x1 := w1, x2 := w2, x3 := w3, x4 := w4, x5 := w5 }

/-- WS-ZA ZA4: `TCB.withReturnFrame` from the frame's six words.  A call, so
the TCB arrives owned and its context is handed on with one reference. -/
def _root_.SeLe4n.Model.TCB.withReturnWords (t : TCB) (w0 w1 w2 w3 w4 w5 : UInt64) : TCB :=
  { t with registerContext := stageReturnWords t.registerContext w0 w1 w2 w3 w4 w5 }

/-- WS-ZA ZA4: `stageCallerReturnFor` from the outcome's boundary words
(`SyscallOutcome.words`, `stageCallerReturnFor_eq_words`): a returning
caller's frame is written from the six words straight into its saved context
and, when it is current, the core's bank, each in its slot, so no frame
record is passed.  A call, not inlined, so the state arrives exclusive: inlined
into the entry, the branches that answer `post` unchanged kept it alive across
the writes. -/
@[noinline] def stageCallerReturnWords (callerCode : Nat) (post : SystemState)
    (c : CoreId) (tag w0 w1 w2 w3 w4 w5 : UInt64) : SystemState :=
  if tag = 0 then
    match callerCode with
    | k + 1 =>
      let tid : SeLe4n.ThreadId := ⟨k⟩
      -- The current-thread test reads `post` before either write, so the
      -- writes find the state exclusive.
      if (post.scheduler.currentOnCore c).isEqSome tid then
        let s1 := post.updateTcb tid (TCB.withReturnWords · w0 w1 w2 w3 w4 w5)
        let m := s1.machine.modifyRegsOnCore c (stageReturnWords · w0 w1 w2 w3 w4 w5)
        { s1 with machine := m }
      else
        post.updateTcb tid (TCB.withReturnWords · w0 w1 w2 w3 w4 w5)
    | 0 => post
  else post

theorem stageCallerReturnFor_eq_words (caller? : Option SeLe4n.ThreadId) (post : SystemState)
    (c : CoreId) (o : SyscallOutcome) :
    stageCallerReturnFor caller? post c o =
      stageCallerReturnWords (SeLe4n.ThreadId.optCode caller?) post c o.words.1 o.words.2.1 o.words.2.2.1
        o.words.2.2.2.1 o.words.2.2.2.2.1 o.words.2.2.2.2.2.1 o.words.2.2.2.2.2.2 := by
  rw [stageCallerReturnFor_eq_impl]
  cases o <;> cases caller? <;>
    simp only [stageCallerReturnForImpl, stageCallerReturnWords, SyscallOutcome.words,
      SeLe4n.ThreadId.optCode,
      SyscallOutcome.tagWord, SyscallOutcome.mailboxFrame, ↓reduceIte, stageCurrentCallerReturn,
      writeReturnFrameToTcb, SeLe4n.Model.TCB.withReturnFrame, stageFrameRegs,
      SeLe4n.RegisterFile.stageReturnFrame, stageReturnWords,
      SeLe4n.Model.TCB.withReturnWords] <;>
    simp

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

/-! ### The target as words (WS-ZA ZA3.1)

The entry hands the HAL a target's parts after the commit, and a part is a
word or the thread's own register file: a `RestoreTarget` held across the
commit is a heap cell, its parts are not.  Each part is read off the
committed state by its own function, proven to be that part of
`restoreTargetOnCore`. -/

/-- The `ffiRestoreCommit` kind a target installs: `0` a thread with its
FP/SIMD trap armed, `2` with it lifted, `1` the wait loop, and `3` nothing to
install (`RestoreTarget.none`). -/
def RestoreTarget.commitKind : RestoreTarget → UInt32
  | .user _ _ _ fpLive => if fpLive then 2 else 0
  | .idle => 1
  | .none => 3

/-- The context a target installs; the wait loop and the empty target install
none, and read as the zero file. -/
def RestoreTarget.context : RestoreTarget → SeLe4n.RegisterFile
  | .user ctx _ _ _ => ctx
  | _ => default

/-- The `TTBR0_EL1` table operand a target installs (`0`, the kernel's own,
for the wait loop). -/
def RestoreTarget.tableBase : RestoreTarget → UInt64
  | .user _ tableBase _ _ => tableBase
  | _ => 0

/-- The ASID operand a target installs (`0`, the kernel's, for the wait loop). -/
def RestoreTarget.asid : RestoreTarget → UInt64
  | .user _ _ asid _ => asid
  | _ => 0

/-- `(restoreTargetOnCore st c).commitKind`, with no target built. -/
def restoreCommitKindOnCore (st : SystemState) (c : CoreId) : UInt32 :=
  match st.scheduler.currentOnCore c with
  | some tid =>
    if SeLe4n.Kernel.isIdleThreadId tid then 1
    else
      match st.getTcb? tid with
      | some _ => if fpLiveFor st c tid then 2 else 0
      | none => 3
  | none => 1

/-- `(restoreTargetOnCore st c).context`, with no target built: the thread's
own register file, shared, never copied. -/
def restoreContextOnCore (st : SystemState) (c : CoreId) : SeLe4n.RegisterFile :=
  match st.scheduler.currentOnCore c with
  | some tid =>
    if SeLe4n.Kernel.isIdleThreadId tid then default
    else
      match st.getTcb? tid with
      | some tcb => tcb.registerContext
      | none => default
  | none => default

/-- `(restoreTargetOnCore st c).tableBase`, with no target built. -/
def restoreTableBaseOnCore (st : SystemState) (c : CoreId) : UInt64 :=
  match st.scheduler.currentOnCore c with
  | some tid =>
    if SeLe4n.Kernel.isIdleThreadId tid then 0
    else threadTranslationOperandsK st tid fun tableBase _ => tableBase
  | none => 0

/-- `(restoreTargetOnCore st c).asid`, with no target built. -/
def restoreAsidOnCore (st : SystemState) (c : CoreId) : UInt64 :=
  match st.scheduler.currentOnCore c with
  | some tid =>
    if SeLe4n.Kernel.isIdleThreadId tid then 0
    else threadTranslationOperandsK st tid fun _ asid => asid
  | none => 0

/-- A thread with no TCB installs no translation: its operands are the
kernel's `(0, 0)`. -/
theorem threadTranslationOperands_of_getTcb?_none (st : SystemState) (tid : SeLe4n.ThreadId)
    (h : st.getTcb? tid = none) : threadTranslationOperands st tid = (0, 0) := by
  unfold threadTranslationOperands; rw [h]

theorem restoreCommitKindOnCore_eq (st : SystemState) (c : CoreId) :
    restoreCommitKindOnCore st c = (restoreTargetOnCore st c).commitKind := by
  unfold restoreCommitKindOnCore restoreTargetOnCore
  cases st.scheduler.currentOnCore c with
  | none => rfl
  | some tid =>
    simp only []
    split
    · rfl
    · cases st.getTcb? tid <;> rfl

theorem restoreContextOnCore_eq (st : SystemState) (c : CoreId) :
    restoreContextOnCore st c = (restoreTargetOnCore st c).context := by
  unfold restoreContextOnCore restoreTargetOnCore
  cases st.scheduler.currentOnCore c with
  | none => rfl
  | some tid =>
    simp only []
    split
    · rfl
    · cases st.getTcb? tid <;> rfl

theorem restoreTableBaseOnCore_eq (st : SystemState) (c : CoreId) :
    restoreTableBaseOnCore st c = (restoreTargetOnCore st c).tableBase := by
  unfold restoreTableBaseOnCore restoreTargetOnCore
  cases st.scheduler.currentOnCore c with
  | none => rfl
  | some tid =>
    simp only [threadTranslationOperandsK_eq]
    split
    · rfl
    · cases h : st.getTcb? tid
      · simp [RestoreTarget.tableBase, threadTranslationOperands_of_getTcb?_none st tid h]
      · rfl

theorem restoreAsidOnCore_eq (st : SystemState) (c : CoreId) :
    restoreAsidOnCore st c = (restoreTargetOnCore st c).asid := by
  unfold restoreAsidOnCore restoreTargetOnCore
  cases st.scheduler.currentOnCore c with
  | none => rfl
  | some tid =>
    simp only [threadTranslationOperandsK_eq]
    split
    · rfl
    · cases h : st.getTcb? tid
      · simp [RestoreTarget.asid, threadTranslationOperands_of_getTcb?_none st tid h]
      · rfl

end SeLe4n.Kernel.Architecture
