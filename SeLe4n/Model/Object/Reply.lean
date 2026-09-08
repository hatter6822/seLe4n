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
- `donatedSc` / `prev`: the MCS reply-stack — the SchedContext donated through
  this reply and the link to the enclosing (outer) reply for nested calls.
  Written by the donation push and cleared by the pop (WS-OD); the stack they
  form is constrained by `donationChainWellFormed`
  (`SeLe4n/Kernel/IPC/Invariant/Defs.lean`), whose head is
  `SchedContext.scReply`.
- `lock`: per-object reader-writer lock state (SM3 per-object lock discipline),
  defaulting to `unheld` for a freshly-allocated object.
-/

namespace SeLe4n.Kernel

/-- WS-SM SM6.D: first-class Reply kernel object.  See the module docstring. -/
structure Reply where
  replyId   : SeLe4n.ReplyId
  caller    : Option SeLe4n.ThreadId       := none
  donatedSc : Option SeLe4n.SchedContextId := none
  prev      : Option SeLe4n.ReplyId        := none
  lock      : SeLe4n.Kernel.Concurrency.RwLockState :=
    SeLe4n.Kernel.Concurrency.RwLockState.unheld
deriving Repr

namespace Reply

/-- Default Reply: the given id, no caller, no donation, lock unheld.  Used by
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
    a.donatedSc == b.donatedSc && a.prev == b.prev && a.lock == b.lock

/-- WS-OD OD2.3: Reply well-formedness — the half of the reply-stack discipline
that is a property of the object **alone**.

A Reply is on a scheduling context's donation stack exactly when it carries that
context (`donatedSc = some scId`), and `prev` is the link to the reply *below* it
on that same stack.  So a Reply that is on no stack carries no link: without a
`donatedSc` there is no stack for `prev` to be a position in, and a link without
one would name a neighbour in a stack this reply is not a member of.

That is also the direction the chain walk validates in.  `donationChainFrom`
follows `prev` only after checking the **target's own** `donatedSc`, never its
`caller`: Reply objects are re-linked to new callers (`replyIdEstablishFresh`),
so a stale link over a reused Reply would otherwise let a donation return read
the *new* caller and hand the original thread's scheduling context to an
unrelated thread, in another domain, driven by object reuse.

**Where the rest of the SM6.D promise lives.**  The docstring this replaces also
promised that `donatedSc` *resolves* and that `donatedSc.scReply` *agrees with
this reply*.  Both read the object store, and a `Reply → Prop` has no store to
read — `Model.Object.Reply` is imported *by* `KernelObject`, not the other way
round — so they are stated where their data is, and nothing is dropped:
`donationChainWellFormed` (`SeLe4n/Kernel/IPC/Invariant/Defs.lean`) carries this
predicate as its own first conjunct, requires every `donatedSc` to resolve to a
SchedContext, and requires each context's `scReply` to head a terminating chain
holding **exactly** the replies that name it — which is the general form of
"agrees with this reply", true at every stack depth rather than only at the top.
`donationChainWellFormed.replyWellFormed` is the bridge between the two. -/
def wellFormed (r : Reply) : Prop :=
  r.donatedSc = none → r.prev = none

/-- WS-OD OD2.3: an inert Reply — the shape `KernelObject.wellFormed`'s `.reply`
arm and `bootSafeReplyCheck` both admit — is well-formed. -/
theorem empty_wellFormed (rid : SeLe4n.ReplyId) : (empty rid).wellFormed :=
  fun _ => rfl

/-- WS-OD OD2.3: well-formedness is decidable, so a Boolean checker can mirror
it without a second reading of the property. -/
instance (r : Reply) : Decidable r.wellFormed := by
  unfold wellFormed; infer_instance

end Reply
end SeLe4n.Kernel
