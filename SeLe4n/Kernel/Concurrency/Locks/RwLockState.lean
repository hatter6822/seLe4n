-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Concurrency.Types

/-!
# RwLock state types (WS-SM SM2.C.1)

The data types of the abstract reader-writer lock — `AccessMode`,
`RwLockState` and its canonical initial state `RwLockState.unheld` —
split out of `Locks/RwLock.lean` so that a consumer of the lock word's
shape (the ghost lock table, `Locks/LockState.lean`) need not import the
lock's operational specification and its proofs.

`Locks/LockKey.lean` imports only this module.  `Locks/RwLock.lean` imports it and
builds the transition system (`RwLockOp`, `applyOp`), the five-conjunct
`wf` predicate and every RwLock theorem on top, so `import
SeLe4n.Kernel.Concurrency.Locks.RwLock` still brings every name defined
here into scope.

This module needs only `CoreId` (`Kernel.Concurrency.Types`).
-/

namespace SeLe4n.Kernel.Concurrency

-- ============================================================================
-- SM2.C.1 — AccessMode + RwLockState
-- ============================================================================

/-- **WS-SM SM2.C.1**: lock access mode.

* `.read` — shared read access.  Multiple cores can hold a read lock
  simultaneously.  Refines the Rust impl's reader-count
  (bits 0..62 of the `AtomicU64` state).
* `.write` — exclusive write access.  At most one core holds a write
  lock at a time, and no readers may hold simultaneously.  Refines the
  Rust impl's writer-bit (bit 63 of the `AtomicU64` state).

`DecidableEq` is derived so filter operations on `List (CoreId ×
AccessMode)` are decidable at elaboration time. -/
inductive AccessMode where
  /-- Reader (shared) access. -/
  | read
  /-- Writer (exclusive) access. -/
  | write
  deriving DecidableEq, Repr, Inhabited

/-- **WS-SM SM2.C.1**: the abstract state of an RwLock primitive.

The three fields capture every observable aspect of a reader-writer
lock at the operational-semantics level:

* `writerHeld` — `Option CoreId` carrying the current writer (if any).
  At most one writer holds at a time, witnessed by
  `rwLock_writer_readers_exclusion`.  Refines the Rust impl's bit 63 of
  the packed `state : AtomicU64`.
* `readers` — the list of cores currently holding the lock in read
  mode.  Refines the Rust impl's bits 0..62 of the packed state.  The
  abstract model uses an explicit list because the spec proves reader
  multiplicity and no-double-acquire; the Rust impl tracks this
  implicitly through the count.
* `waiters` — the FIFO queue of cores blocked waiting for the lock,
  each tagged with their requested access mode.  Used for FIFO
  admission ordering (`rwLock_fifo_admission`) and writer-starvation
  freedom (`rwLock_no_writer_starvation`).  The **deployed** Rust lock
  represents this queue: `queued_rw_lock::QueuedRwLock` is a ticket
  protocol, and `queuedSim` (WS-RR RR6.6) relates `waiters` to the
  half-open ticket interval `[now_serving, next_ticket)` in order, so
  FIFO admission is a theorem of the implementation
  (`queuedRwLock_admits_in_spec_order`).  The *other* Rust lock,
  `rw_lock::RwLock`, tracks waiters implicitly through its CAS-retry
  spin-loop and does not preserve FIFO (documented in SM2.C.20); it is
  retained as the second implementation the Tier-5 oracle cross-checks
  (WS-RR RR6.11) and is no longer what `lock_bridge.rs` deploys
  (WS-RR RR6.10).

`Inhabited` is derived (every field has `Inhabited` — `Option` via
`none`, `List` via `[]`).  Per WS-SM SM3.A audit-pass-5, the
derived `default` is structurally identical to `RwLockState.unheld`,
witnessed by `default_eq_unheld` below.  Downstream code that
writes `lock := default` simp-normalises to `lock := .unheld`. -/
structure RwLockState where
  /-- The current writer holder, if any.  At most one writer at a time. -/
  writerHeld : Option CoreId
  /-- The list of cores currently holding the lock in read mode. -/
  readers    : List CoreId
  /-- The FIFO queue of (waiter core, requested mode) pairs. -/
  waiters    : List (CoreId × AccessMode)
  deriving Repr, Inhabited, DecidableEq

-- ============================================================================
-- SM2.C.1 — unheld constructor
-- ============================================================================

/-- **WS-SM SM2.C.1**: the canonical initial state.

No writer holds; no readers; the wait queue is empty.  This is the
state every reachable trace begins in (the operational-semantics seed
for the reachability theorem). -/
def RwLockState.unheld : RwLockState where
  writerHeld := none
  readers    := []
  waiters    := []

/-- Witness: `unheld.writerHeld = none`. -/
theorem RwLockState.unheld_writerHeld : unheld.writerHeld = none := rfl

/-- Witness: `unheld.readers = []`. -/
theorem RwLockState.unheld_readers : unheld.readers = ([] : List CoreId) := rfl

/-- Witness: `unheld.waiters = []`. -/
theorem RwLockState.unheld_waiters :
    unheld.waiters = ([] : List (CoreId × AccessMode)) := rfl

/-- **WS-SM SM3.A audit-pass-5**: the `Inhabited`-derived `default` of
`RwLockState` is structurally identical to `RwLockState.unheld`.

`RwLockState` derives `Inhabited`, which Lean synthesises by
combining the `Inhabited` instances of every field
(`Option CoreId` → `none`, `List CoreId` → `[]`,
`List (CoreId × AccessMode)` → `[]`).  The result is the same
record as `RwLockState.unheld`.

This equivalence is **not** trivially `rfl` in every Lean context
because the `Inhabited` derivation produces an explicit
`Inhabited.mk { writerHeld := default, ... }` term whose
definitional unfolding requires reducing each field's `Inhabited`
instance.  We provide an explicit witness so downstream code that
writes `lock := default` is machine-checkably equivalent to code
that writes `lock := RwLockState.unheld`. -/
@[simp] theorem RwLockState.default_eq_unheld :
    (default : RwLockState) = RwLockState.unheld := rfl

end SeLe4n.Kernel.Concurrency
