/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Model.State

/-! # The yield link: its cancel and its completion

WS-ZA ZA6.6.  seL4-MCS links a thread that has yielded to a scheduling context
with that context: the thread's `tcbYieldTo` names the context and the
context's `scYieldFrom` names the thread.  Here both ends are codes in the
objects' own fields (`TCB.yieldToCode`, `SchedContext.yieldFromCode`: `0` for
no link, `n + 1` for the object `n`), as `boundThreadCode` holds a binding, so a
link is written and cleared without a `some` cell.

- `cancelYieldTo` is seL4-MCS's `schedContext_cancelYieldTo`: both ends
  cleared, the context's then the thread's.  It runs on the yielder's suspend
  and its finalisation.
- `setConsumed` is seL4-MCS's `setConsumed`: the context's consumed time, at
  most a word (`SchedContext.consumedReading`), is written into a thread's
  first message register with a one-register message info, and taken off the
  context (`SchedContext.updateConsumed`, seL4's `schedContext_updateConsumed`).
- `completeYieldTo` is seL4-MCS's `schedContext_completeYieldTo`: a linked
  yielder is handed the consumed time of the context it yielded to, then the
  link is cancelled.  `completeYieldFrom` completes the yield a context records,
  as seL4's context finalisation (`if (sc->scYieldFrom)
  schedContext_completeYieldTo(sc->scYieldFrom)`) and its next yieldTo do; its
  cancel is read from the context's side (`cancelYieldFrom`), which on agreeing
  links is the yielder's `cancelYieldTo`.

Until the yieldTo invocation sets a link, every link is empty and each of these
is the identity on every reachable state.

The consumed time goes into the **yielder's** saved registers.  seL4-MCS's
`setConsumed` writes them into `ksCurThread`'s registers, which is the yielder
exactly when the completion runs at the yielder's activation, the case the
yield's own return value is for; when it runs at a context's finalisation seL4
writes the deleting thread's registers while passing the yielder's IPC buffer,
and the deleting thread's `msgInfo` is then overwritten by its own reply.  The
yielder is the thread the reading is for, so this kernel writes the yielder's. -/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- The message-info word `setConsumed` writes: one message register, no
capabilities, label `0` (seL4-MCS's `seL4_MessageInfo_new(0, 0, 0, length)`
with `length` the one register `mode_setTimeArg` fills on a 64-bit word). -/
def consumedInfoWord : UInt64 :=
  (({ length := 1, extraCaps := 0, label := 0 } : MessageInfo).encode).toUInt64

/-- A register file after `setConsumed`: the message info in `x1` and the
consumed time in `x2`, the first message register; every other register as it
was, as seL4 writes only `msgInfoRegister` and the one message register. -/
@[inline] def _root_.SeLe4n.RegisterFile.withConsumed (rf : SeLe4n.RegisterFile)
    (w : UInt64) : SeLe4n.RegisterFile :=
  { rf with x1 := consumedInfoWord, x2 := w }

/-- A thread after `setConsumed` wrote its saved registers. -/
@[inline] def _root_.SeLe4n.Model.TCB.withConsumed (t : TCB) (w : UInt64) : TCB :=
  { t with registerContext := t.registerContext.withConsumed w }

/-- A thread's end of the yield link, cleared. -/
@[inline] def _root_.SeLe4n.Model.TCB.yieldCleared (t : TCB) : TCB :=
  { t with yieldToCode := 0 }

/-- A context's end of the yield link, cleared. -/
@[inline] def SchedContext.yieldCleared (sc : SchedContext) : SchedContext :=
  { sc with yieldFromCode := 0 }

/-- The context thread `tid` has yielded to, as its yield-to code names it: the
context a cancel of its link writes.  `none` on a thread with no link and on an
absent one. -/
def yieldToContextOf? (st : SystemState) (tid : SeLe4n.ThreadId) : Option SeLe4n.SchedContextId :=
  match st.getTcb? tid with
  | some t =>
    match t.yieldToCode with
    | 0 => none
    | k + 1 => some ⟨k⟩
  | none => none

/-- The thread that yielded to context `s`, as its yield-from code names it: the
thread a completion of its recorded yield writes.  `none` on a context with no
yielder and on an absent one. -/
def yieldFromThreadOf? (st : SystemState) (s : SeLe4n.SchedContextId) : Option SeLe4n.ThreadId :=
  match st.getSchedContext? s with
  | some sc =>
    match sc.yieldFromCode with
    | 0 => none
    | k + 1 => some ⟨k⟩
  | none => none

/-- **seL4-MCS's `schedContext_cancelYieldTo`**: a thread linked to the context
it yielded to has both ends cleared, the context's (`scYieldFrom = NULL`) then
its own (`tcbYieldTo = NULL`), each in its slot.  The identity on a thread with
no link and on an absent one. -/
def cancelYieldTo (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  match st.getTcb? tid with
  | some t =>
    match t.yieldToCode with
    | 0 => st
    | k + 1 => (st.updateSchedContext ⟨k⟩ SchedContext.yieldCleared).updateTcb tid TCB.yieldCleared
  | none => st

/-- **seL4-MCS's `setConsumed`**: the consumed time of context `s` — at most a
word (`SchedContext.consumedReading`) — taken off it
(`schedContext_updateConsumed`) and written into thread `t`'s first message
register, with the one-register message info (`TCB.withConsumed`).  The
identity when `s` names no context. -/
def setConsumed (st : SystemState) (s : SeLe4n.SchedContextId) (t : SeLe4n.ThreadId) :
    SystemState :=
  match st.getSchedContext? s with
  | some sc =>
    let w := sc.consumedReading.toUInt64
    (st.updateSchedContext s SchedContext.updateConsumed).updateTcb t (TCB.withConsumed · w)
  | none => st

/-- **seL4-MCS's `schedContext_completeYieldTo`**: a yielder linked to a
context is handed that context's consumed time (`setConsumed`) and its link
cancelled (`cancelYieldTo`).  The identity on a thread with no link. -/
def completeYieldTo (st : SystemState) (yielder : SeLe4n.ThreadId) : SystemState :=
  match st.getTcb? yielder with
  | some t =>
    match t.yieldToCode with
    | 0 => st
    | k + 1 => cancelYieldTo (setConsumed st ⟨k⟩ yielder) yielder
  | none => st

/-- **A context's end of the cancel**: a context naming a yielder has both
ends cleared, its own (`scYieldFrom = NULL`) then the yielder's
(`tcbYieldTo = NULL`), each in its slot.  On a state whose links agree
(`SystemState.yieldLinksAgree`) the yielder names this context, so this is
`cancelYieldTo` of the yielder; read from the context's side it clears the
context's end on every state, which is what its finalisation needs.  The
identity on a context with no yielder and on an absent one. -/
def cancelYieldFrom (st : SystemState) (s : SeLe4n.SchedContextId) : SystemState :=
  match st.getSchedContext? s with
  | some sc =>
    match sc.yieldFromCode with
    | 0 => st
    | k + 1 => (st.updateSchedContext s SchedContext.yieldCleared).updateTcb ⟨k⟩ TCB.yieldCleared
  | none => st

/-- **The completion of the yield a context records** (seL4-MCS's
`if (sc->scYieldFrom) schedContext_completeYieldTo(sc->scYieldFrom)`): the
thread the context names as its yielder is handed the context's consumed time
(`setConsumed`) and the link cancelled (`cancelYieldFrom`).  On a state whose
links agree it is `completeYieldTo` of that yielder
(`completeYieldFrom_eq_completeYieldTo`).  It runs on the context's
finalisation and on its next yieldTo.  The identity on a context with no
yielder and on an absent one. -/
def completeYieldFrom (st : SystemState) (s : SeLe4n.SchedContextId) : SystemState :=
  match st.getSchedContext? s with
  | some sc =>
    match sc.yieldFromCode with
    | 0 => st
    | k + 1 => cancelYieldFrom (setConsumed st s ⟨k⟩) s
  | none => st

/-- **The completion half of seL4-MCS's `unbindFromSC`**: once a thread is
unbound from the context it held, the yield that context records is completed
(`if (sc->scYieldFrom) schedContext_completeYieldTo(sc->scYieldFrom)`,
`completeYieldFrom`).  `held` is the code of the context the thread held
(`TCB.scBindingScCode`: `0` for none, `n + 1` for the context `n`), read by the
caller before its first write.  The identity when the thread held none. -/
def completeHeldYield (st : SystemState) (held : Nat) : SystemState :=
  match held with
  | 0 => st
  | k + 1 => completeYieldFrom st ⟨k⟩

/-- **seL4-MCS's `invokeSchedContext_Consumed`** (WS-ZA ZA6.9, the
`seL4_SchedContext_Consumed` invocation on the executing core `c`): the invoked
context's consumed time is returned in the caller's first message register and
reset (`setConsumed`).  seL4 decodes nothing for it, so the only refusals are the
ones a well-formed entry never meets: a core with no current thread has no
caller (`.illegalState`, as `yieldOnCore`), and a capability whose target is no
scheduling context names nothing to read (`.invalidCapability`). -/
def schedContextConsumedOnCore (s : SeLe4n.SchedContextId) (c : Concurrency.CoreId)
    (st : SystemState) : Except KernelError SystemState :=
  match st.scheduler.currentOnCore c with
  | none => .error .illegalState
  | some caller =>
    match st.getSchedContext? s with
    | none => .error .invalidCapability
    | some _ => .ok (setConsumed st s caller)

/-- A Consumed invocation that succeeds is `setConsumed` for the core's current
thread. -/
theorem schedContextConsumedOnCore_ok {s : SeLe4n.SchedContextId} {c : Concurrency.CoreId}
    {st st' : SystemState} (h : schedContextConsumedOnCore s c st = .ok st') :
    ∃ caller, st.scheduler.currentOnCore c = some caller ∧ st' = setConsumed st s caller := by
  unfold schedContextConsumedOnCore at h
  split at h
  · cases h
  · rename_i caller hCur
    split at h
    · cases h
    · cases h; exact ⟨caller, hCur, rfl⟩

/-- The Consumed invocation's checks, read before its write: a current thread
on the core and a scheduling context at the invoked object. -/
@[inline] def schedContextConsumedAdmitted (st : SystemState) (s : SeLe4n.SchedContextId)
    (c : Concurrency.CoreId) : Bool :=
  (st.scheduler.currentOnCore c).isSome && (st.getSchedContext? s).isSome

/-- The Consumed invocation's write once admitted: `setConsumed` for the core's
current thread. -/
@[inline] def schedContextConsumedPerform (st : SystemState) (s : SeLe4n.SchedContextId)
    (c : Concurrency.CoreId) : SystemState :=
  match st.scheduler.currentOnCore c with
  | some caller => setConsumed st s caller
  | none => st

theorem schedContextConsumedOnCore_of_admitted (st : SystemState) (s : SeLe4n.SchedContextId)
    (c : Concurrency.CoreId) (h : schedContextConsumedAdmitted st s c = true) :
    schedContextConsumedOnCore s c st = .ok (schedContextConsumedPerform st s c) := by
  unfold schedContextConsumedAdmitted at h
  unfold schedContextConsumedOnCore schedContextConsumedPerform
  cases hC : st.scheduler.currentOnCore c with
  | none => rw [hC] at h; cases h
  | some caller =>
    cases hS : st.getSchedContext? s with
    | none => rw [hC, hS] at h; cases h
    | some _ => rfl

end SeLe4n.Kernel

namespace SeLe4n.Model.SystemState

open SeLe4n.Kernel

theorem cancelYieldFrom_eq_objects (st : SystemState) (s : SeLe4n.SchedContextId) :
    cancelYieldFrom st s = { st with objects := (cancelYieldFrom st s).objects } := by
  unfold cancelYieldFrom
  split
  · split
    · rfl
    · rw [updateTcb_eq_objects_update, updateSchedContext_eq_objects_update]
  · rfl

theorem cancelYieldFrom_scheduler (st : SystemState) (s : SeLe4n.SchedContextId) :
    (cancelYieldFrom st s).scheduler = st.scheduler := by
  rw [cancelYieldFrom_eq_objects]

/-- The cancel writes the object store alone. -/
theorem cancelYieldTo_eq_objects (st : SystemState) (tid : SeLe4n.ThreadId) :
    cancelYieldTo st tid = { st with objects := (cancelYieldTo st tid).objects } := by
  unfold cancelYieldTo
  split
  · split
    · rfl
    · rw [updateTcb_eq_objects_update, updateSchedContext_eq_objects_update]
  · rfl

theorem cancelYieldTo_scheduler (st : SystemState) (tid : SeLe4n.ThreadId) :
    (cancelYieldTo st tid).scheduler = st.scheduler := by
  rw [cancelYieldTo_eq_objects]

/-- `setConsumed` writes the object store alone. -/
theorem setConsumed_eq_objects (st : SystemState) (s : SeLe4n.SchedContextId)
    (t : SeLe4n.ThreadId) :
    setConsumed st s t = { st with objects := (setConsumed st s t).objects } := by
  unfold setConsumed
  split
  · rw [updateTcb_eq_objects_update, updateSchedContext_eq_objects_update]
  · rfl

theorem setConsumed_scheduler (st : SystemState) (s : SeLe4n.SchedContextId)
    (t : SeLe4n.ThreadId) : (setConsumed st s t).scheduler = st.scheduler := by
  rw [setConsumed_eq_objects]

theorem completeYieldTo_eq_objects (st : SystemState) (y : SeLe4n.ThreadId) :
    completeYieldTo st y = { st with objects := (completeYieldTo st y).objects } := by
  unfold completeYieldTo
  split
  · split
    · rfl
    · rw [cancelYieldTo_eq_objects, setConsumed_eq_objects]
  · rfl

/-- The completion of a context's recorded yield writes the object store alone. -/
theorem completeYieldFrom_eq_objects (st : SystemState) (s : SeLe4n.SchedContextId) :
    completeYieldFrom st s = { st with objects := (completeYieldFrom st s).objects } := by
  unfold completeYieldFrom
  split
  · split
    · rfl
    · rw [cancelYieldFrom_eq_objects, setConsumed_eq_objects]
  · rfl

/-- The completion of a held context's yield writes the object store alone. -/
theorem completeHeldYield_eq_objects (st : SystemState) (held : Nat) :
    completeHeldYield st held = { st with objects := (completeHeldYield st held).objects } := by
  unfold completeHeldYield
  split
  · rfl
  · exact completeYieldFrom_eq_objects _ _

theorem completeYieldFrom_scheduler (st : SystemState) (s : SeLe4n.SchedContextId) :
    (completeYieldFrom st s).scheduler = st.scheduler := by
  rw [completeYieldFrom_eq_objects]

theorem completeYieldFrom_tlbShootdown (st : SystemState) (s : SeLe4n.SchedContextId) :
    (completeYieldFrom st s).tlbShootdown = st.tlbShootdown := by
  rw [completeYieldFrom_eq_objects]

theorem completeHeldYield_scheduler (st : SystemState) (held : Nat) :
    (completeHeldYield st held).scheduler = st.scheduler := by
  rw [completeHeldYield_eq_objects]

theorem completeHeldYield_tlbShootdown (st : SystemState) (held : Nat) :
    (completeHeldYield st held).tlbShootdown = st.tlbShootdown := by
  rw [completeHeldYield_eq_objects]

theorem cancelYieldTo_tlbShootdown (st : SystemState) (tid : SeLe4n.ThreadId) :
    (cancelYieldTo st tid).tlbShootdown = st.tlbShootdown := by
  rw [cancelYieldTo_eq_objects]

theorem cancelYieldTo_machine (st : SystemState) (tid : SeLe4n.ThreadId) :
    (cancelYieldTo st tid).machine = st.machine := by
  rw [cancelYieldTo_eq_objects]

end SeLe4n.Model.SystemState
