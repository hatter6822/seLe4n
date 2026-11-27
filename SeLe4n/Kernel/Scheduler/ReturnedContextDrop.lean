-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.Selection

/-!
# The current slot of a thread whose context went back (WS-SX SX36.2)

The owner ruling "seL4 order" (plan D63): after the reply step of a ReplyRecv
returns a passive server's context and the server's receive is then refused, the
server stays its core's current thread until the scheduling point, as seL4's
`rescheduleRequired` leaves `ksCurThread`.  Two steps carry it:

* `descheduleKeepingCurrentOnCore`, the holder-only deschedule:
  `descheduleAtPlacement`, except that a holder current on the named core keeps
  the slot.  `descheduleAtPlacement` itself is unchanged.
* `dropReturnedContextCaller`, run at the scheduling point before the local
  successor is chosen: a caller that held a context on loan at entry of a
  ReplyRecv and is still current, now with no context, is taken off the core
  without re-enqueueing it (`removeRunnableOnCore` at the core it is current
  on).  The slot is then vacated, so `scheduleLocalSuccessorFrom` chooses a
  successor, and no thread runs without a context.

The drop is gated, not keyed on "unbound" alone: an unbound thread is fully
schedulable in this model (`hasSufficientBudget`'s `.unbound` arm), and a
thread that loses its context any other way keeps today's behaviour (plan D63
lists each such path).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- **Deschedule a holder, keeping core `c`'s current slot** (WS-SX SX36.2, the
owner ruling "seL4 order"): `descheduleAtPlacement`, except that a holder that is
core `c`'s current thread stays current.  That is seL4's `rescheduleRequired`,
which leaves `ksCurThread` in place until the scheduling point.  A current thread
is on no run queue (dequeue-on-dispatch), so removing it would only have cleared
the slot.  The scheduling point takes the thread off the core without
re-enqueueing it (`dropReturnedContextCaller`), so no thread
runs without a context.  A holder that is not current on `c` is removed exactly
as `descheduleAtPlacement` removes it. -/
def descheduleKeepingCurrentOnCore (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) :
    SystemState :=
  if st.scheduler.currentOnCore c = some tid then st else descheduleAtPlacement st tid

/-- The holder-only deschedule leaves a holder that is current on `c` current. -/
theorem descheduleKeepingCurrentOnCore_of_current (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) (h : st.scheduler.currentOnCore c = some tid) :
    descheduleKeepingCurrentOnCore st tid c = st := by
  unfold descheduleKeepingCurrentOnCore; rw [if_pos h]

/-- Off the current slot, the holder-only deschedule is `descheduleAtPlacement`. -/
theorem descheduleKeepingCurrentOnCore_of_not_current (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) (h : st.scheduler.currentOnCore c ≠ some tid) :
    descheduleKeepingCurrentOnCore st tid c = descheduleAtPlacement st tid := by
  unfold descheduleKeepingCurrentOnCore; rw [if_neg h]

/-- **One deschedule, either outcome**: a property the identity and
`descheduleAtPlacement` both carry, the holder-only deschedule carries.  Every
frame of the holder-only deschedule is this lemma over the two existing ones. -/
theorem descheduleKeepingCurrentOnCore_induct (P : SystemState → SystemState → Prop)
    (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (hId : P st st) (hD : P st (descheduleAtPlacement st tid)) :
    P st (descheduleKeepingCurrentOnCore st tid c) := by
  by_cases h : st.scheduler.currentOnCore c = some tid
  · rw [descheduleKeepingCurrentOnCore_of_current st tid c h]; exact hId
  · rw [descheduleKeepingCurrentOnCore_of_not_current st tid c h]; exact hD

/-- The holder-only deschedule keeps the run queues in agreement with the links. -/
theorem descheduleKeepingCurrentOnCore_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) : SystemState.RunQueueStage st (descheduleKeepingCurrentOnCore st tid c) :=
  descheduleKeepingCurrentOnCore_induct (fun a b => SystemState.RunQueueStage a b) st tid c
    (SystemState.RunQueueStage.refl st) (descheduleAt_runQueueStage st tid _)

/-- Does `t` hold a context on loan (a `.donated` binding)?  Read at the entry
of a ReplyRecv, before the reply step can return the context. -/
@[inline] def threadOnLoanAt (st : SystemState) (t : SeLe4n.ThreadId) : Bool :=
  match st.getTcb? t with
  | some tcb => tcb.scBindingScCode != 0 && tcb.scBindingOwnerCode != 0
  | none => false

/-- Does `t` hold no context (an `.unbound` binding)? -/
@[inline] def threadUnboundAt (st : SystemState) (t : SeLe4n.ThreadId) : Bool :=
  match st.getTcb? t with
  | some tcb => tcb.scBindingScCode == 0
  | none => false

/-- Is the syscall number the seam took ReplyRecv's (`Syscall.number`)? -/
@[inline] def syscallNumberIsReplyRecv (n : UInt32) : Bool :=
  n.toNat == SeLe4n.Model.Syscall.replyRecv.number

/-- **The entry's gate for the drop**: the syscall is a ReplyRecv and its caller
holds a context on loan.  The ReplyRecv's only step that can unbind its caller is
the reply step's pop returning that loan (a receive that dequeues a `Call`
donates to the caller, and no other step writes its binding), so a caller that
passes this gate and is unbound after the transition is a caller whose context
the pop returned. -/
@[inline] def contextReturnableAtEntry (isReplyRecv : Bool) (st : SystemState)
    (caller? : Option SeLe4n.ThreadId) : Bool :=
  isReplyRecv &&
    match caller? with
    | some t => threadOnLoanAt st t
    | none => false

/-- **The scheduling point's drop** (WS-SX SX36.2): where the entry's gate held
(`returnable`, `contextReturnableAtEntry` on the pre-state), a caller that is
still core `c`'s current thread and now holds no context is taken off the core,
not re-enqueued (`removeRunnableOnCore`, which raises the core's reschedule
flag).  Every other state passes through unchanged. -/
def dropReturnedContextCaller (returnable : Bool) (caller? : Option SeLe4n.ThreadId)
    (post : SystemState) (c : CoreId) : SystemState :=
  if returnable then
    match caller? with
    | some t =>
        if post.scheduler.currentOnCore c = some t ∧ threadUnboundAt post t = true then
          removeRunnableOnCore post t c
        else post
    | none => post
  else post

/-- A closed gate drops nothing. -/
theorem dropReturnedContextCaller_of_not_returnable (caller? : Option SeLe4n.ThreadId)
    (post : SystemState) (c : CoreId) :
    dropReturnedContextCaller false caller? post c = post := by
  unfold dropReturnedContextCaller; rw [if_neg Bool.false_ne_true]

/-- **One drop, either outcome**: a property the identity and the removal of a
thread at core `c` both carry, the drop carries. -/
theorem dropReturnedContextCaller_induct (P : SystemState → SystemState → Prop)
    (returnable : Bool) (caller? : Option SeLe4n.ThreadId) (post : SystemState) (c : CoreId)
    (hId : P post post) (hD : ∀ t, P post (removeRunnableOnCore post t c)) :
    P post (dropReturnedContextCaller returnable caller? post c) := by
  unfold dropReturnedContextCaller
  by_cases hR : returnable = true
  · rw [if_pos hR]
    cases caller? with
    | none => exact hId
    | some t =>
      dsimp only
      by_cases hC : post.scheduler.currentOnCore c = some t ∧ threadUnboundAt post t = true
      · rw [if_pos hC]; exact hD t
      · rw [if_neg hC]; exact hId
  · rw [if_neg hR]; exact hId

/-- The drop keeps the run queues in agreement with the links. -/
theorem dropReturnedContextCaller_runQueueStage (returnable : Bool)
    (caller? : Option SeLe4n.ThreadId) (post : SystemState) (c : CoreId) :
    SystemState.RunQueueStage post (dropReturnedContextCaller returnable caller? post c) :=
  dropReturnedContextCaller_induct (fun a b => SystemState.RunQueueStage a b) returnable caller?
    post c (SystemState.RunQueueStage.refl post) (fun t => removeRunnableOnCore_runQueueStage post t c)

/-- The drop keeps the object store's extensional invariant. -/
theorem dropReturnedContextCaller_objects_invExt (returnable : Bool)
    (caller? : Option SeLe4n.ThreadId) (post : SystemState) (c : CoreId)
    (hInv : post.objects.invExt) :
    (dropReturnedContextCaller returnable caller? post c).objects.invExt :=
  dropReturnedContextCaller_induct (fun _ b => b.objects.invExt) returnable caller? post c hInv
    (fun t => removeRunnableOnCore_objects_invExt post t c hInv)

/-- **No thread runs without a context it was lent** (temporal isolation at the
scheduling point): after the drop, a caller that passed the entry's gate is not
core `c`'s current thread while it holds no context. -/
theorem dropReturnedContextCaller_not_current_unbound (caller : SeLe4n.ThreadId)
    (post : SystemState) (c : CoreId) :
    ¬ ((dropReturnedContextCaller true (some caller) post c).scheduler.currentOnCore c =
        some caller ∧
      threadUnboundAt (dropReturnedContextCaller true (some caller) post c) caller = true) := by
  unfold dropReturnedContextCaller
  rw [if_pos rfl]
  dsimp only
  by_cases hC : post.scheduler.currentOnCore c = some caller ∧ threadUnboundAt post caller = true
  · rw [if_pos hC]
    intro ⟨hCur, _⟩
    rw [removeRunnableOnCore_scheduler] at hCur
    simp [hC.1] at hCur
  · rw [if_neg hC]; exact hC

/-- **The drop vacates the slot it takes**, so the local successor rule
(`PriorityInheritance.localSuccessorNeededFrom`, keyed on a vacated slot) chooses
a successor. -/
theorem dropReturnedContextCaller_currentOnCore_none (caller : SeLe4n.ThreadId)
    (post : SystemState) (c : CoreId) (hCur : post.scheduler.currentOnCore c = some caller)
    (hU : threadUnboundAt post caller = true) :
    (dropReturnedContextCaller true (some caller) post c).scheduler.currentOnCore c = none := by
  unfold dropReturnedContextCaller
  rw [if_pos rfl]
  dsimp only
  rw [if_pos ⟨hCur, hU⟩, removeRunnableOnCore_scheduler]
  simp [hCur]

end SeLe4n.Kernel
