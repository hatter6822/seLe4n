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
  Populated in the donation-re-homing slices (Phase E); `none` until then.
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

/-- WS-SM SM6.D: Reply well-formedness.  Trivial in this slice; strengthened
when the reply-stack and donation linkage land (Phase E) — `donatedSc` resolves,
`prev` is acyclic, and `donatedSc.scReply` agrees with this reply. -/
def wellFormed (_r : Reply) : Prop := True

end Reply
end SeLe4n.Kernel
