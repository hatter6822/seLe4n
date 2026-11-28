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

/-- **The reply return's holder deschedule** (WS-SX SX36.2, the owner ruling
"seL4 everywhere"): the deschedule a reply runs on the thread its return takes a
context from.  A `.reply` and a ReplyRecv whose receive runs pass `false`, and it
is `descheduleAtPlacement`; the reply step of a ReplyRecv whose receive completes
the bound notification passes `true` with its executing core, and it is the
holder-only deschedule, so a passive server whose loan the reply returned stays
current until the scheduling point, as seL4's `rescheduleRequired` leaves
`ksCurThread`. -/
@[inline] def descheduleReturnedHolder (keepCurrent : Bool) (c : CoreId) (st : SystemState)
    (holder : SeLe4n.ThreadId) : SystemState :=
  if keepCurrent then descheduleKeepingCurrentOnCore st holder c else descheduleAtPlacement st holder

@[simp] theorem descheduleReturnedHolder_false (c : CoreId) (st : SystemState)
    (holder : SeLe4n.ThreadId) :
    descheduleReturnedHolder false c st holder = descheduleAtPlacement st holder := rfl

theorem descheduleReturnedHolder_true (c : CoreId) (st : SystemState)
    (holder : SeLe4n.ThreadId) :
    descheduleReturnedHolder true c st holder = descheduleKeepingCurrentOnCore st holder c := rfl

/-- **Either flag, one deschedule**: a property the identity and
`descheduleAtPlacement` both carry, the reply return's holder deschedule carries. -/
theorem descheduleReturnedHolder_induct (P : SystemState → SystemState → Prop)
    (keepCurrent : Bool) (c : CoreId) (st : SystemState) (holder : SeLe4n.ThreadId)
    (hId : P st st) (hD : P st (descheduleAtPlacement st holder)) :
    P st (descheduleReturnedHolder keepCurrent c st holder) := by
  cases keepCurrent
  · exact hD
  · exact descheduleKeepingCurrentOnCore_induct P st holder c hId hD

/-- **A field neither deschedule moves**: a projection `descheduleAtPlacement`
leaves alone, the reply return's holder deschedule leaves alone on either flag. -/
theorem descheduleReturnedHolder_congr_field {α : Sort _} (f : SystemState → α)
    (keepCurrent : Bool) (c : CoreId) (st : SystemState) (holder : SeLe4n.ThreadId)
    (hD : f (descheduleAtPlacement st holder) = f st) :
    f (descheduleReturnedHolder keepCurrent c st holder) = f st :=
  descheduleReturnedHolder_induct (fun a b => f b = f a) keepCurrent c st holder rfl hD

/-- The reply return's holder deschedule writes no replenish queue. -/
@[simp] theorem descheduleReturnedHolder_replenishQueueOnCore (keepCurrent : Bool) (c : CoreId)
    (st : SystemState) (holder : SeLe4n.ThreadId) (c' : CoreId) :
    (descheduleReturnedHolder keepCurrent c st holder).scheduler.replenishQueueOnCore c' =
      st.scheduler.replenishQueueOnCore c' :=
  descheduleReturnedHolder_congr_field (·.scheduler.replenishQueueOnCore c') keepCurrent c st
    holder (descheduleAtPlacement_replenishQueueOnCore st holder c')

/-- The reply return's holder deschedule writes objects only off their run links. -/
theorem descheduleReturnedHolder_objectsAgreeOffRunLinks (keepCurrent : Bool) (c : CoreId)
    (st : SystemState) (holder : SeLe4n.ThreadId) :
    (descheduleReturnedHolder keepCurrent c st holder).objectsAgreeOffRunLinks st :=
  descheduleReturnedHolder_induct (fun a b => b.objectsAgreeOffRunLinks a) keepCurrent c st
    holder (fun _ => rfl) (descheduleAtPlacement_objectsAgreeOffRunLinks st holder)

/-- The reply return's holder deschedule keeps the derivation tree. -/
@[simp] theorem descheduleReturnedHolder_cdt (keepCurrent : Bool) (c : CoreId)
    (st : SystemState) (holder : SeLe4n.ThreadId) :
    (descheduleReturnedHolder keepCurrent c st holder).cdt = st.cdt :=
  descheduleReturnedHolder_congr_field (·.cdt) keepCurrent c st holder
    (descheduleAtPlacement_cdt st holder)

/-- The reply return's holder deschedule keeps the object store's extension
invariant. -/
theorem descheduleReturnedHolder_preserves_objects_invExt (keepCurrent : Bool) (c : CoreId)
    (st : SystemState) (holder : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    (descheduleReturnedHolder keepCurrent c st holder).objects.invExt :=
  descheduleReturnedHolder_induct (fun a b => a.objects.invExt → b.objects.invExt) keepCurrent c
    st holder id (descheduleAtPlacement_preserves_objects_invExt st holder) hInv

/-- The fields the holder deschedule leaves alone, on either flag. -/
@[simp] theorem descheduleReturnedHolder_objects_capacity (keepCurrent : Bool) (c : CoreId)
    (st : SystemState) (holder : SeLe4n.ThreadId) :
    (descheduleReturnedHolder keepCurrent c st holder).objects.capacity = st.objects.capacity :=
  descheduleReturnedHolder_congr_field (·.objects.capacity) keepCurrent c st holder
    (descheduleAtPlacement_objects_capacity st holder)
@[simp] theorem descheduleReturnedHolder_lifecycle (keepCurrent : Bool) (c : CoreId)
    (st : SystemState) (holder : SeLe4n.ThreadId) :
    (descheduleReturnedHolder keepCurrent c st holder).lifecycle = st.lifecycle :=
  descheduleReturnedHolder_congr_field (·.lifecycle) keepCurrent c st holder
    (descheduleAtPlacement_lifecycle st holder)
@[simp] theorem descheduleReturnedHolder_objectIndex (keepCurrent : Bool) (c : CoreId)
    (st : SystemState) (holder : SeLe4n.ThreadId) :
    (descheduleReturnedHolder keepCurrent c st holder).objectIndex = st.objectIndex :=
  descheduleReturnedHolder_congr_field (·.objectIndex) keepCurrent c st holder
    (descheduleAtPlacement_objectIndex st holder)
@[simp] theorem descheduleReturnedHolder_objectIndexSet (keepCurrent : Bool) (c : CoreId)
    (st : SystemState) (holder : SeLe4n.ThreadId) :
    (descheduleReturnedHolder keepCurrent c st holder).objectIndexSet = st.objectIndexSet :=
  descheduleReturnedHolder_congr_field (·.objectIndexSet) keepCurrent c st holder
    (descheduleAtPlacement_objectIndexSet st holder)
@[simp] theorem descheduleReturnedHolder_asidTable (keepCurrent : Bool) (c : CoreId)
    (st : SystemState) (holder : SeLe4n.ThreadId) :
    (descheduleReturnedHolder keepCurrent c st holder).asidTable = st.asidTable :=
  descheduleReturnedHolder_congr_field (·.asidTable) keepCurrent c st holder
    (descheduleAtPlacement_asidTable st holder)
@[simp] theorem descheduleReturnedHolder_machine_eq (keepCurrent : Bool) (c : CoreId)
    (st : SystemState) (holder : SeLe4n.ThreadId) :
    (descheduleReturnedHolder keepCurrent c st holder).machine = st.machine :=
  descheduleReturnedHolder_congr_field (·.machine) keepCurrent c st holder
    (descheduleAtPlacement_machine_eq st holder)
@[simp] theorem descheduleReturnedHolder_releaseSlots (keepCurrent : Bool) (c : CoreId)
    (st : SystemState) (holder : SeLe4n.ThreadId) :
    (descheduleReturnedHolder keepCurrent c st holder).scheduler.releaseSlots = st.scheduler.releaseSlots :=
  descheduleReturnedHolder_congr_field (·.scheduler.releaseSlots) keepCurrent c st holder
    (descheduleAtPlacement_releaseSlots st holder)
@[simp] theorem descheduleReturnedHolder_determineTargetCore (keepCurrent : Bool) (c : CoreId)
    (st : SystemState) (holder x : SeLe4n.ThreadId) :
    determineTargetCore (descheduleReturnedHolder keepCurrent c st holder) x =
      determineTargetCore st x :=
  descheduleReturnedHolder_congr_field (determineTargetCore · x) keepCurrent c st holder
    (descheduleAtPlacement_determineTargetCore st holder x)

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
the reply's return of that loan: the reply step's pop on the receive route, and
the reply leg's own return on the signal route (`replyTransferOnCoreChecked`
with the keep flag).  A receive that dequeues a `Call` donates to the caller,
the signal route's completion can only donate the notification's context to it,
and no other step writes its binding, so a caller that passes this gate and is
unbound after the transition is a caller whose context the reply returned. -/
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
