-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude
-- WS-SM SM6.D: per-Reply lock field requires the abstract operational RwLock
-- specification from SM2.C.  This import does not introduce a cycle:
-- `Concurrency.Locks.RwLock` depends transitively only on `Prelude`.
import SeLe4n.Kernel.Concurrency.Locks.RwLock

/-! # Reply object — WS-SM SM6.D

First-class Reply kernel object backing the `Call` / `Reply` IPC rendezvous,
mirroring `SchedContext`.  A `Reply` records the linkage between a blocked
caller and the authority to reply to it:

- `caller`: back-link to the TCB currently `blockedOnReply` on this object.
  Replying delivers to this thread and then **consumes** the linkage
  (`caller := none`), giving reply capabilities their single-use semantics.
- `prev` / `next`: the MCS reply stack, **doubly linked** exactly as seL4's
  `replyPrev` / `replyNext` (`src/object/reply.c`).  `prev` names the frame
  below this one — the enclosing (outer) call's reply; `next` names the frame
  above it, or, on the head frame alone, the scheduling context whose stack
  this is (`ReplyStackLink.head`).  The context is therefore recorded **at the
  head only**: a frame below the head does not know which context it carries,
  which is what makes taking a frame out of the *middle* of a stack an `O(1)`
  operation on three objects (seL4's `reply_remove_tcb`) rather than a walk
  over every frame below it.  Written by the donation push, cleared by the
  pop and by the frame detach (WS-OD); the stack they form is constrained by
  `donationChainWellFormed` (`SeLe4n/Kernel/IPC/Invariant/Defs.lean`), whose
  head is `SchedContext.scReply`.
- `lock`: per-object reader-writer lock state (SM3 per-object lock discipline),
  defaulting to `unheld` for a freshly-allocated object.
-/

namespace SeLe4n.Kernel

/-- WS-OD (`v0.35.4`): **the upward link of a reply-stack frame** — seL4's
`replyNext`, a `call_stack_t` whose `isHead` bit says whether the pointer names
the frame pushed above this one or the scheduling context whose stack this frame
heads.  A sum type rather than two fields, so "head", "has a frame above" and
"off every stack" (`none`) are three states of one value and no object can claim
two of them at once.

Only the head carries the context.  That is the whole point of the encoding: a
frame taken out of the middle of a stack repairs its two neighbours and nothing
else (`detachReplyFrameAbove` above the cut, `Reply.consumed` at the frame
itself), where a per-frame context field would have to be
cleared on every frame below the cut — an `O(depth)` walk, or, left undone, a
frame that names a context forever and can never be retyped or linked again. -/
inductive ReplyStackLink where
  /-- The frame pushed **above** this one on the same stack. -/
  | frame (above : SeLe4n.ReplyId)
  /-- This frame **heads** the stack of the named scheduling context. -/
  | head (sc : SeLe4n.SchedContextId)
deriving DecidableEq, Repr, Inhabited

namespace ReplyStackLink

/-- The reply id a `.frame` link names, if it is one. -/
@[inline] def frame? : ReplyStackLink → Option SeLe4n.ReplyId
  | .frame above => some above
  | .head _ => none

/-- The scheduling context a `.head` link names, if it is one. -/
@[inline] def head? : ReplyStackLink → Option SeLe4n.SchedContextId
  | .frame _ => none
  | .head sc => some sc

@[simp] theorem frame?_frame (above : SeLe4n.ReplyId) :
    (ReplyStackLink.frame above).frame? = some above := rfl
@[simp] theorem frame?_head (sc : SeLe4n.SchedContextId) :
    (ReplyStackLink.head sc).frame? = none := rfl
@[simp] theorem head?_frame (above : SeLe4n.ReplyId) :
    (ReplyStackLink.frame above).head? = none := rfl
@[simp] theorem head?_head (sc : SeLe4n.SchedContextId) :
    (ReplyStackLink.head sc).head? = some sc := rfl

end ReplyStackLink

/-- WS-SM SM6.D: first-class Reply kernel object.  See the module docstring. -/
structure Reply where
  replyId   : SeLe4n.ReplyId
  caller    : Option SeLe4n.ThreadId       := none
  prev      : Option SeLe4n.ReplyId        := none
  next      : Option ReplyStackLink         := none
  lock      : SeLe4n.Kernel.Concurrency.RwLockState :=
    SeLe4n.Kernel.Concurrency.RwLockState.unheld
deriving Repr

namespace Reply

/-- Default Reply: the given id, no caller, no stack links, lock unheld.  Used by
`retypeFromUntyped` when creating a new Reply object. -/
def empty (rid : SeLe4n.ReplyId) : Reply := { replyId := rid }

/-- Default instance uses the sentinel id and an empty linkage. -/
instance : Inhabited Reply where
  default := empty SeLe4n.ReplyId.sentinel

/-- Manual `BEq` mirroring `BEq SchedContext`: dispatches to constituent `BEq`
instances so `BEq KernelObject`'s `.reply` arm has a comparator.  `RwLockState`
derives `DecidableEq`, so its `==` agrees with `=`; the lock state participates
in structural equality so lock-state regressions are not masked. -/
instance : BEq Reply where
  beq a b :=
    a.replyId == b.replyId && a.caller == b.caller &&
    a.prev == b.prev && a.next == b.next && a.lock == b.lock

/-- WS-OD (`v0.35.4`): **a Reply is on a stack iff it carries a stack link**,
and **an unlinked Reply is off every stack** — the object-local half of the
reply-stack discipline, seL4's `reply_unlink` invariant (`replyTCB == NULL ⟹
replyPrev == replyNext == 0`, `src/object/reply.c`).

Every stack link is put in place by a push that has just linked the frame to a
blocked caller, and no operation leaves a link behind once the caller is gone.
The pop at the head clears the popped frame's two links in its own store
(`storeDonationHeadClear`), *before* the caller link is consumed; a frame cut out
of the middle loses both of its own links in the very record that clears its
caller (`Reply.consumed`, which is not the head arm), while the neighbour above
it is repaired first by `detachReplyFrameAbove`.  Either way a Reply whose
`caller` is `none` carries no link, and conversely a Reply that carries a link
has a caller still blocked on it.  That is what makes
`Reply.isFree` — no caller, no links — the exact `O(1)` test for "this object may
be linked to a new caller or retyped": a linked frame always has a live caller,
which `linkReply`'s single-use barrier already refuses, and a frame whose caller
is gone has already been taken off its stack.

What this predicate deliberately does **not** say is anything about *which*
stack: `prev = some _ ∧ next = none` is a legitimate shape — the top frame of a
part the detach has cut off, seL4's "start of call chain" — and a frame below the
head never names its context at all.  Both halves of the stack relation that read
the store — a `prev` link is reciprocated by the frame it names, a `.head` link by
the context it names — are `donationChainWellFormed`'s, beside the data they
read; `donationChainWellFormed.replyWellFormed` is the bridge. -/
def wellFormed (r : Reply) : Prop :=
  r.caller = none → r.prev = none ∧ r.next = none

/-- WS-OD (`v0.35.4`): **the Reply may be linked to a caller or retyped** — no
blocked caller and no stack link in either direction.  The one spelling of that
question: `linkReply`, `replyStashValid`, the retype guard and the boot check all
read it, so a fourth guard cannot decide it differently
(PR audit of WS-OD: the stash admission checked `caller` alone while the link
checked the stack too, and a server's `Recv` stashed a Reply its next `Call`
could not link). -/
@[inline] def isFree (r : Reply) : Bool :=
  r.caller.isNone && r.prev.isNone && r.next.isNone

/-- `isFree` is the decidable form of "no caller and no links". -/
theorem isFree_iff (r : Reply) :
    r.isFree = true ↔ r.caller = none ∧ r.prev = none ∧ r.next = none := by
  simp only [isFree, Bool.and_eq_true, Option.isNone_iff_eq_none]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

/-- A Reply on no stack (no links) is free exactly when it has no caller. -/
theorem isFree_of_unlinked (r : Reply) (hPrev : r.prev = none) (hNext : r.next = none) :
    r.isFree = r.caller.isNone := by
  simp [isFree, hPrev, hNext]

/-- WS-OD (`v0.35.4`): **the record a consumed Reply becomes** — seL4's
`reply_remove` applied at the moment the caller link is consumed.  The caller is
cleared always.  The stack links are cleared too **unless this frame heads a
stack**: a head is taken off its stack by the donation pop, which runs in the
same transition right after the reply leg (plan §3.3 — the leg consumes the
caller first, the pop reads the head afterwards and validates it by this very
link), so clearing a head here would make the pop refuse the frame it is about
to pop.  A frame that is *not* a head and still carries links is the top of a
part the detach cut off (seL4's "start of call chain"); nothing will ever pop
it, so its consumption is where it leaves the structure.

The frame **below** a consumed non-head frame keeps an upward link that now
names an unlinked Reply.  That is deliberate and safe: the stack relation is
stated **downward** (`donationChainWellFormed.prevLinkReciprocal` — every `prev`
link is answered by the frame it names), every walk and every pop validator
follows `prev` and checks the answer, and no reader trusts an upward `.frame`
link on its own.  The stale link lives only in a cut-off part, which no head
reaches, and is cleared when that frame's own caller is consumed.  Clearing it
eagerly would cost a second object write on every reply for a case only a
cancellation deeper than three creates.

**Precondition, and who discharges it** (WS-RM, `v0.35.6`).  The frame **above**
is the other direction, and it is *not* safe to ignore: if some frame still
links **down** to this one (`above.prev = some rid`), clearing this frame's
`next` falsifies `prevLinkReciprocal` at that frame, and the pop that later
walks to it refuses (fail-closed, `.invalidArgument`) rather than returning the
context.  So a removal path must take the frame above off this one *before*
consuming.  Which value it writes into that frame's `prev` is the
`cancelledMiddleCallerPolicy` decision: this kernel writes `none`
(`severAtCut`), so the frames below the cut leave the stack, where seL4-MCS's
`reply_remove` writes the cut frame's own `replyPrev` and keeps them.

**Both paths do.**  The cancellation path runs `detachFrameAboveThreadReply`
immediately before `consumeReplyLink`, and the reply path runs
`removeCallerReplyFrame` — the detach and the consume as one step, called by
`endpointReplyOnCore` and by both single-core spines.  Until WS-RM the reply path
did not: it relied on the answered frame being the head, which every reply of the
nested Call pattern satisfies but which a *delegated* reply capability answering
its caller out of order does not.  New code on a reply path calls
`removeCallerReplyFrame` rather than reaching for the consume; a Tier 3 negative
refuses the bare spelling in either spine, and
`SeLe4n/Testing/ReplyStackWriteCensus.lean` fails the build for a new write site
that names no chain result. -/
def consumed (r : Reply) : Reply :=
  match r.next with
  | some (.head _) => { r with caller := none }
  | _ => { r with caller := none, prev := none, next := none }

@[simp] theorem consumed_caller (r : Reply) : r.consumed.caller = none := by
  unfold consumed; split <;> rfl

@[simp] theorem consumed_replyId (r : Reply) : r.consumed.replyId = r.replyId := by
  unfold consumed; split <;> rfl

@[simp] theorem consumed_lock (r : Reply) : r.consumed.lock = r.lock := by
  unfold consumed; split <;> rfl

/-- A head keeps its links across consumption — the pop that follows clears them. -/
theorem consumed_of_head (r : Reply) (sc : SeLe4n.SchedContextId)
    (h : r.next = some (.head sc)) : r.consumed = { r with caller := none } := by
  unfold consumed; rw [h]

/-- A frame that is not a head leaves the structure when it is consumed. -/
theorem consumed_of_not_head (r : Reply) (h : ∀ sc, r.next ≠ some (.head sc)) :
    r.consumed = { r with caller := none, prev := none, next := none } := by
  unfold consumed
  cases hn : r.next with
  | none => rfl
  | some l =>
    cases l with
    | frame _ => rfl
    | head sc => exact absurd hn (h sc)

/-- On a Reply carrying no links, consumption is the caller clear alone — which
is every Reply the tree consumed before WS-OD, and every Reply the reply path
consumes below the first cut-off part. -/
theorem consumed_of_unlinked (r : Reply) (hPrev : r.prev = none) (hNext : r.next = none) :
    r.consumed = { r with caller := none } := by
  unfold consumed; rw [hNext]; simp [hPrev]

/-- A consumed Reply that is not a head is well formed and free. -/
theorem consumed_isFree_of_not_head (r : Reply) (h : ∀ sc, r.next ≠ some (.head sc)) :
    r.consumed.isFree = true := by
  rw [consumed_of_not_head r h]; rfl

/-- A consumed Reply is well formed exactly when it is not a linked head — the
head case is the one the pop closes in the same transition. -/
theorem consumed_wellFormed_of_not_head (r : Reply) (h : ∀ sc, r.next ≠ some (.head sc)) :
    r.consumed.wellFormed := by
  rw [consumed_of_not_head r h]; intro _; exact ⟨rfl, rfl⟩

/-- WS-OD OD2.3: an inert Reply — the shape `KernelObject.wellFormed`'s `.reply`
arm and `bootSafeReplyCheck` both admit — is well-formed. -/
theorem empty_wellFormed (rid : SeLe4n.ReplyId) : (empty rid).wellFormed :=
  fun _ => ⟨rfl, rfl⟩

/-- An inert Reply is free. -/
@[simp] theorem empty_isFree (rid : SeLe4n.ReplyId) : (empty rid).isFree = true := rfl

/-- WS-OD OD2.3: well-formedness is decidable, so a Boolean checker can mirror
it without a second reading of the property. -/
instance (r : Reply) : Decidable r.wellFormed := by
  unfold wellFormed; infer_instance

end Reply
end SeLe4n.Kernel
