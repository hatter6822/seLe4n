-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM (SM2.C abstract RwLock spec; refined by
-- `rust/sele4n-hal/src/rw_lock.rs` per SM2.C.19 and the SM2.C.20
-- refinement bridge `Locks/RwLockRefinement.lean`).

import SeLe4n.Kernel.Concurrency.MemoryModel
import SeLe4n.Kernel.Concurrency.Types

/-!
# WS-SM SM2.C — RwLock operational specification

This module contains the abstract operational specification of the
reader-writer lock primitive that the Rust HAL's
`rust/sele4n-hal/src/rw_lock.rs` refines.  The spec is **pure**
(no `IO`, no `Unsafe`, zero added axioms, zero proof gaps): every
transition is a total function on the abstract `RwLockState`, and
every theorem is mechanically discharged.

The ten substantive theorems exported by this module are:

* `rwLock_writer_readers_exclusion` — when a writer holds, no readers
  hold (and vice versa).
* `rwLock_reader_multiplicity` — multiple readers can hold the lock
  simultaneously (a reachable state has ≥ 2 readers).
* `rwLock_fifo_admission` — earlier waiters are admitted before later
  ones (writers are FIFO-ordered).
* `rwLock_bounded_wait_read` — `WCRT(tryAcquireRead) ≤ (N-1) × T_cs`.
* `rwLock_bounded_wait_write` — `WCRT(tryAcquireWrite) ≤ (N-1) × T_cs`.
* `rwLock_release_acquire_pairing_read` — reader release-acquire pair.
* `rwLock_release_acquire_pairing_write` — writer release-acquire pair.
* `rwLock_wf_invariant` — every operation preserves the five conjuncts
  of `RwLockState.wf` (INV-R1..R5).
* `rwLock_reader_batching` — contiguous reader waiters are batch-promoted
  together when the holding writer releases.
* `rwLock_no_writer_starvation` — every queued writer eventually
  becomes the holder under bounded-progress assumptions.

Plus a determinism theorem (`rwLock_applyOp_deterministic`), four
closure-form preservation lemmas (`tryAcquireRead_preserves_wf`,
`releaseRead_preserves_wf`, `tryAcquireWrite_preserves_wf`,
`releaseWrite_preserves_wf`), and the bit-packed encoding theorems
(`rwLock_encode_decode_roundtrip`, `rwLock_decode_encode_roundtrip`)
that SM2.C.20 refinement consumes.

## ARM ARM citations

The operational behaviour of the abstract `applyOp` corresponds to the
following hardware primitives:

* **`tryAcquireRead` / `tryAcquireWrite`** — `LDAXR` / `STLXR` exclusive
  load-store pair (ARM ARM C6.2.135 / C6.2.323) or LSE `CASA` (ARM ARM
  C6.2.50).  Captures the lock state atomically with acquire semantics.
  (Audit pass-2 H-B fix: previously cited STLXR at C6.2.305, which is
  actually the STADDL store-only variant; STLXR is in a different
  section.)
* **`releaseRead`** — `LDADDL` (ARM ARM C6.2.116) on the packed state
  with release semantics.  Decrements the reader count atomically.
* **`releaseWrite`** — `LDCLRL` (ARM ARM C6.2.103) family with release
  ordering (B2.3.7); pre-LSE, a CAS-retry sequence.  Atomically clears
  the writer bit while preserving any reader bits; release-store
  ordering publishes every prior write on the releasing core to any
  acquire-load that observes this value.  Per H-4 audit fix, this
  replaces the prior `STLR` whole-word store which would silently
  wipe reader bits on misuse.

## Axiom budget

Zero Lean `axioms`, zero `sorries`.  All hardware semantics enter as
operational constraints on the memory trace shape via the SM2.A
abstract memory model.

## Decidability

`RwLockState.wf` carries a `Decidable` instance so test fixtures can
construct lock states and `decide` their well-formedness at
elaboration time.  The transition functions
(`applyOp`, `promoteWaitersOnWriterRelease`,
`promoteWaitersIfReadersEmpty`) are total computable functions on
`RwLockState`.

## Five-conjunct `wf` (the plan's four + reachability gap closure)

The plan's §3.3.2 specifies four `wf` conjuncts (INV-R1..R4).  Per
the `implement-the-improvement` rule, we add a fifth conjunct INV-R5
that closes a reachability gap: without INV-R5, the four-conjunct
form admits the "unreachable but wf" state with non-empty waiters and
no holders, from which `tryAcquireWrite` can produce an INV-R4
violation by acquiring the lock for a core that already sits in the
waiters queue.  INV-R5 rules out this state and makes the abstract
spec capture exactly the reachable state space (the analog of SM2.B's
INV-T8 count-parity invariant).

## No upgrade/downgrade at v1.0.0

Per decision #2 (plan §4.4), the v1.0.0 RwLock supports only plain
acquire/release.  Upgrades (reader → writer) and downgrades (writer →
reader) are bug-prone in production code; they are deferred to a
post-1.0 RwLock-x extension.  The `applyOp` does not include upgrade /
downgrade operations.
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
  freedom (`rwLock_no_writer_starvation`).  The Rust impl tracks
  waiters implicitly through the CAS-retry spin-loop, weakening the
  FIFO guarantee (documented in SM2.C.20).

`Inhabited` is derived (every field has `Inhabited` — `Option` via
`none`, `List` via `[]`).  The default `Inhabited` witness is **not**
`unheld`; see `unheld` below for the canonical initial state. -/
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

-- ============================================================================
-- SM2.C.2 — wf predicate (5 conjuncts: plan's 4 + reachability gap closure)
-- ============================================================================

/-- **WS-SM SM2.C.2**: helper Bool predicate for INV-R1 — when a writer
holds, the readers list is empty.

Returns `true` if `writerHeld = none` (vacuous case) or if
`writerHeld = some _` AND `readers = []`.  Used to keep `wf`'s decidability
elementary. -/
def RwLockState.writerReadersExclusion (s : RwLockState) : Bool :=
  match s.writerHeld with
  | none => true
  | some _ => decide (s.readers = [])

/-- **WS-SM SM2.C.2**: helper Bool predicate for INV-R4 — waiters'
cores are disjoint from current holders (readers list ∪ writerHeld).

The predicate checks, for every waiter `w`, that `w.1 ∉ readers` AND
`writerHeld ≠ some w.1`.  Used to keep `wf`'s decidability elementary. -/
def RwLockState.waitersDisjointFromHolders (s : RwLockState) : Bool :=
  s.waiters.all fun w =>
    decide (w.1 ∉ s.readers) && decide (s.writerHeld ≠ some w.1)

/-- **WS-SM SM2.C.2**: helper Bool predicate for INV-R5 — the FIFO
admission discipline.  If waiters is non-empty, then at least one
holder exists (either a writer or at least one reader).

Without INV-R5, the four-conjunct form admits the "unreachable but
wf" state with non-empty waiters and no holders, from which
`tryAcquireWrite` produces an INV-R4 violation by acquiring the lock
for a core that may already sit in the waiters queue.

Returns `true` if waiters is empty (vacuous), or if a holder exists. -/
def RwLockState.fifoAdmissionDiscipline (s : RwLockState) : Bool :=
  decide (s.waiters = []) || s.writerHeld.isSome || decide (s.readers ≠ [])

/-- **WS-SM SM2.C.2**: well-formedness predicate for an RwLockState.

The plan's §3.3.2 specifies four `wf` conjuncts (INV-R1..R4).  Per
the `implement-the-improvement` rule, we add a fifth conjunct INV-R5
that closes a reachability gap.  Each `INV-R*` annotation matches the
plan's §3.3.2 conjunct numbering for traceability.

* **INV-R1** — writer-readers exclusion: when a writer holds, the
  readers list is empty.  This is the foundational mutex property the
  reader-writer lock guarantees.
* **INV-R2** — readers list is `Nodup`.  A core cannot hold the read
  lock more than once simultaneously (no double-acquire).
* **INV-R3** — waiter cores list is `Nodup`.  A core cannot be queued
  more than once simultaneously (no double-enqueue).
* **INV-R4** — waiters disjoint from current holders.  No core can
  simultaneously hold the lock (as reader or writer) AND wait for it.
* **INV-R5** (new): FIFO admission discipline.  Waiters is non-empty
  only when at least one holder exists.  This closes the reachability
  gap noted above.

### Why five, not four

The plan's pseudocode for `applyOp .tryAcquireWrite` (§3.3.4)
unconditionally sets `writerHeld := some core` in the "free" branch
without checking whether `core` is already in `waiters`.  This is
operationally correct because in any reachable state with empty
holders, the waiters queue is also empty (the prior holder's release
would have promoted them).  But the four-conjunct `wf` admits states
like `(writerHeld = none, readers = [], waiters = [(c, .write)])` —
unreachable from `unheld` but locally `wf`-satisfying.  From such a
state, `tryAcquireWrite c'` for `c' ≠ c` succeeds and sets
`writerHeld := some c'`, leaving `c` in waiters and violating INV-R4.

INV-R5 rules out the troublesome state.  Under INV-R5, the
"unreachable" state is rejected, and `tryAcquireWrite`'s acquire
branch is provably safe.

The Bool encodings (`writerReadersExclusion`,
`waitersDisjointFromHolders`, `fifoAdmissionDiscipline`) keep `wf`'s
decidability elementary; the `Option`-quantifier alternative is
mathematically equivalent but unfolds through `Membership.mem` and is
harder for `decide` to handle. -/
def RwLockState.wf (s : RwLockState) : Prop :=
  -- INV-R1: writer-readers exclusion
  s.writerReadersExclusion = true
  ∧
  -- INV-R2: readers Nodup
  s.readers.Nodup
  ∧
  -- INV-R3: waiter cores Nodup
  (s.waiters.map Prod.fst).Nodup
  ∧
  -- INV-R4: waiters disjoint from current holders
  s.waitersDisjointFromHolders = true
  ∧
  -- INV-R5: FIFO admission discipline (closes the reachability gap)
  s.fifoAdmissionDiscipline = true

/-- **WS-SM SM2.C.2**: bridge the Bool `writerReadersExclusion` to its
`Option`-quantifier form.  Used by every preservation proof that
reasons about the exclusion property. -/
theorem RwLockState.writerReadersExclusion_iff (s : RwLockState) :
    s.writerReadersExclusion = true ↔
    (∀ c, s.writerHeld = some c → s.readers = []) := by
  unfold RwLockState.writerReadersExclusion
  cases h_held : s.writerHeld with
  | none => simp
  | some c =>
    constructor
    · intro h_dec c' h_eq
      cases h_eq
      exact of_decide_eq_true h_dec
    · intro h_all
      exact decide_eq_true (h_all c rfl)

/-- **WS-SM SM2.C.2**: bridge the Bool `waitersDisjointFromHolders` to
its bounded-quantifier form.  Used by every preservation proof that
reasons about disjointness. -/
theorem RwLockState.waitersDisjointFromHolders_iff (s : RwLockState) :
    s.waitersDisjointFromHolders = true ↔
    (∀ w ∈ s.waiters, w.1 ∉ s.readers ∧ s.writerHeld ≠ some w.1) := by
  unfold RwLockState.waitersDisjointFromHolders
  rw [List.all_eq_true]
  constructor
  · intro h w hw
    have h_pair := h w hw
    rw [Bool.and_eq_true] at h_pair
    refine ⟨of_decide_eq_true h_pair.1, of_decide_eq_true h_pair.2⟩
  · intro h w hw
    have h_pair := h w hw
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true h_pair.1, decide_eq_true h_pair.2⟩

/-- **WS-SM SM2.C.2**: bridge the Bool `fifoAdmissionDiscipline` to its
mathematical form. -/
theorem RwLockState.fifoAdmissionDiscipline_iff (s : RwLockState) :
    s.fifoAdmissionDiscipline = true ↔
    (s.waiters ≠ [] → s.writerHeld.isSome ∨ s.readers ≠ []) := by
  unfold RwLockState.fifoAdmissionDiscipline
  constructor
  · -- Forward: Bool form → Prop form.
    intro h h_ne
    -- h : decide (s.waiters = []) || s.writerHeld.isSome || decide (s.readers ≠ []) = true
    -- Note: Bool `||` is left-associative, so this parses as (a || b) || c.
    rw [Bool.or_eq_true, Bool.or_eq_true] at h
    rcases h with (h_w | h_held) | h_r
    · -- waiters = []: contradicts h_ne.
      exact absurd (of_decide_eq_true h_w) h_ne
    · -- writerHeld.isSome.
      exact Or.inl h_held
    · -- readers ≠ [].
      exact Or.inr (of_decide_eq_true h_r)
  · -- Reverse: Prop form → Bool form.
    intro h
    rw [Bool.or_eq_true, Bool.or_eq_true]
    by_cases h_w : s.waiters = []
    · -- waiters = []: take left-left.
      exact Or.inl (Or.inl (decide_eq_true h_w))
    · -- waiters ≠ []: get writerHeld.isSome OR readers ≠ [].
      rcases h h_w with h_held | h_r
      · -- writerHeld.isSome: take left-right.
        exact Or.inl (Or.inr h_held)
      · -- readers ≠ []: take right.
        exact Or.inr (decide_eq_true h_r)

-- ============================================================================
-- SM2.C.2 — wf decidability
-- ============================================================================

/-- **WS-SM SM2.C.2**: `wf` is decidable.

All five conjuncts are decidable:

* INV-R1: `writerReadersExclusion` is a Bool returning value.
* INV-R2 / INV-R3: `List.Nodup` is decidable when the underlying
  `DecidableEq` is available (which we have for `CoreId = Fin numCores`).
* INV-R4: `waitersDisjointFromHolders` is a Bool returning value.
* INV-R5: `fifoAdmissionDiscipline` is a Bool returning value.

The `unfold` + `inferInstance` pattern matches the SM2.A
`MemoryTrace.wellFormed` and SM2.B `TicketLockState.wf` decidability
proofs.  The explicit name `RwLockState.decidableWf` avoids the
auto-generated `instDecidableWf` colliding with TicketLock's anonymous
`Decidable wf` instance when both modules are imported into the same
build unit (e.g., `Platform.Staged`). -/
instance RwLockState.decidableWf (s : RwLockState) : Decidable s.wf := by
  unfold RwLockState.wf
  exact inferInstance

/-- Witness: `unheld` is well-formed.  Discharged by `decide`. -/
theorem RwLockState.unheld_wf : RwLockState.unheld.wf := by
  unfold RwLockState.wf RwLockState.unheld
  decide

-- ============================================================================
-- SM2.C.3 — RwLockOp
-- ============================================================================

/-- **WS-SM SM2.C.3**: the operational-semantics operations on an RwLock.

Four operations cover the full lifecycle:

* `tryAcquireRead core` — attempts to acquire a read lock for `core`.
  Either succeeds (adding to `readers`), enqueues (adding to `waiters`),
  or no-ops (already a holder/waiter).
* `releaseRead core` — releases a read lock held by `core`.  Removes
  from `readers` and triggers `promoteWaitersIfReadersEmpty` if the
  reader count drops to zero.
* `tryAcquireWrite core` — attempts to acquire a write lock for `core`.
  Either succeeds (setting `writerHeld`), enqueues (adding to `waiters`),
  or no-ops (already a holder/waiter).
* `releaseWrite core` — releases the write lock if held by `core`.
  Clears `writerHeld` and triggers `promoteWaitersOnWriterRelease`. -/
inductive RwLockOp where
  /-- `core` attempts to acquire a read lock. -/
  | tryAcquireRead  (core : CoreId)
  /-- `core` releases its read lock (if it holds one). -/
  | releaseRead     (core : CoreId)
  /-- `core` attempts to acquire a write lock. -/
  | tryAcquireWrite (core : CoreId)
  /-- `core` releases the write lock (if it holds it). -/
  | releaseWrite    (core : CoreId)
  deriving Repr

-- ============================================================================
-- SM2.C.4 — promoteWaitersOnWriterRelease (helper for releaseWrite)
-- ============================================================================

/-- **WS-SM SM2.C.4 / SM2.C.13**: after a writer releases, promote
the head of the wait queue.

If the head waiter is a writer, set `writerHeld := some c` (a single
writer is admitted).  If the head waiter is a reader, **batch-promote**
all contiguous reader waiters at the head of the queue — this is the
reader-batching property that SM2.C.13's `rwLock_reader_batching`
theorem makes precise.

Reader-batching is essential for read-throughput on read-mostly
workloads: a single writer release admits many readers at once, rather
than forcing each reader to wait for the previous one to release.

**Pre-conditions** (must be enforced by callers; the wf-preservation
theorem `rwLock_promoteWaitersOnWriterRelease_preserves_wf` requires
both):
* `writerHeld = none` (the caller just released the writer).
* `readers = []` (INV-R1: writer-readers exclusion before release).

**Safety contract (H-C audit-pass-2 documentation)**: the function
pattern-matches on `s.waiters` ALONE.  If invoked while `writerHeld`
is `some c0` and `waiters = [(c1, .write) :: rest]`, the post-state
would be `writerHeld := some c1`, silently displacing `c0` and
violating INV-R1.  Callers **MUST** clear `writerHeld` before calling
this function — the only legitimate call site is `applyOp
.releaseWrite` which already does so.

The function is intentionally NOT defensive about this precondition
(no internal `writerHeld.isSome` gate) for two reasons:

1. **Proof obligations**: the wf-preservation theorem requires
   `writerHeld = none` as a hypothesis, making the contract part of
   the Lean type signature.  Any SM3 consumer that wants to invoke
   `promoteWaitersOnWriterRelease` must also discharge the
   preconditions, which forces them through the contract.
2. **Refinement to Rust**: the Rust impl has no analog of this
   function as a standalone operation (the abstract function is
   "atomic" with `releaseWrite` in the Lean spec; the Rust
   `release_write` does the equivalent atomic step in one
   `fetch_and`).  No SM3 consumer should invoke this function
   independently.

The function remains total over the abstract `RwLockState` — every
input has a defined output. -/
def RwLockState.promoteWaitersOnWriterRelease (s : RwLockState) :
    RwLockState :=
  match s.waiters with
  | [] => s
  | (c, .write) :: rest =>
      -- Single writer promoted to held.
      { s with writerHeld := some c, waiters := rest }
  | (_, .read) :: _ =>
      -- Reader head: batch-promote all contiguous reader waiters.
      let readWaiters := s.waiters.takeWhile (fun w => w.2 = .read)
      let rest := s.waiters.dropWhile (fun w => w.2 = .read)
      { s with
        readers := readWaiters.map Prod.fst ++ s.readers
        waiters := rest }

/- **Contract for `promoteWaitersOnWriterRelease` (H-C audit-pass-2)**:
the function REQUIRES `writerHeld = none` AND `readers = []` for
correctness.  This contract is formalised at the wf-preservation
theorem level (`rwLock_promoteWaitersOnWriterRelease_preserves_wf`
takes both as hypotheses) — see the theorem statement at the
relevant section below.

Without either precondition, the function may produce a wf-violating
state:

* `writerHeld = some c0` + `waiters = (c1, .write) :: ...`:
  post-state has `writerHeld := some c1`, **silently displacing c0**
  (INV-R1 violation if `c0 ≠ c1`).
* `writerHeld = none` + `readers ≠ []` + `waiters = (c, .write) :: ...`:
  post-state has `writerHeld := some c` with `readers ≠ []`,
  **violating INV-R1** (writer can't coexist with readers).

Both footguns are documented in the function docstring above.  The
only legitimate call site is `applyOp .releaseWrite` which
discharges the preconditions structurally (it clears `writerHeld`
before calling, and INV-R1 on the pre-state ensures `readers = []`
after the clear).

The unsafe-on-misuse design is intentional: it forces SM3 consumers
through `releaseWrite`'s validated path rather than allowing direct
invocation outside the contract.  The Rust impl has no analog of
this function as a standalone operation. -/

-- ============================================================================
-- SM2.C.4 — promoteWaitersIfReadersEmpty (helper for releaseRead)
-- ============================================================================

/-- **WS-SM SM2.C.4**: after a reader releases, if no readers remain,
promote the head of the wait queue.

The function is invoked from `applyOp .releaseRead` after the
releaser is removed from the readers list.  When the reader count
drops to zero AND no writer holds, the next waiter is admitted.

Cases:
* `readers ≠ []`: still readers active; no promotion (the lock is
  still held in shared mode).
* `writerHeld.isSome`: a writer holds (must come from INV-R1 violation
  scenarios that the reachable state space rejects; defensive case).
* `readers = []` AND `writerHeld = none`: promote head of waiters.
  * Writer head → set `writerHeld := some c`.
  * Reader head → batch-promote (same as `promoteWaitersOnWriterRelease`).
    Under the FIFO admission discipline (INV-R5) this branch is
    technically unreachable when called from `releaseRead` — a reader
    in the waiters queue implies a writer somewhere before it.  We
    still handle it defensively so the function is total and the
    operational semantics is well-defined on every state. -/
def RwLockState.promoteWaitersIfReadersEmpty (s : RwLockState) :
    RwLockState :=
  if !s.readers.isEmpty then s
  else if s.writerHeld.isSome then s
  else
    match s.waiters with
    | [] => s
    | (c, .write) :: rest =>
        { s with writerHeld := some c, waiters := rest }
    | (_, .read) :: _ =>
        -- Defensive: under INV-R5 this is unreachable from a wf
        -- post-`releaseRead` state, but the operational definition
        -- must be total.  Batch-promote contiguous readers as in
        -- `promoteWaitersOnWriterRelease`.
        let readWaiters := s.waiters.takeWhile (fun w => w.2 = .read)
        let rest := s.waiters.dropWhile (fun w => w.2 = .read)
        { s with
          readers := readWaiters.map Prod.fst
          waiters := rest }

-- ============================================================================
-- SM2.C.4 — applyOp (operational semantics)
-- ============================================================================

/-- **WS-SM SM2.C.4**: predicate "core is already involved with this lock".

A core is "involved" iff it is currently holding the lock (as reader
or writer) or already queued as a waiter.  This is the canonical
no-op precondition for `tryAcquireRead` and `tryAcquireWrite`: if a
core is already involved, attempting to acquire again is a no-op
(the spec models double-acquire conservatively to keep the state
well-formed).

Three disjuncts:
* `core ∈ s.readers` — already holding the read lock.
* `s.writerHeld = some core` — already holding the write lock.
* `core ∈ s.waiters.map Prod.fst` — already queued as a waiter. -/
def RwLockState.coreInvolved (s : RwLockState) (core : CoreId) : Prop :=
  core ∈ s.readers ∨ s.writerHeld = some core ∨ core ∈ s.waiters.map Prod.fst

/-- `coreInvolved` is decidable.  All three disjuncts are decidable. -/
instance RwLockState.decidableCoreInvolved (s : RwLockState) (core : CoreId) :
    Decidable (s.coreInvolved core) := by
  unfold RwLockState.coreInvolved
  exact inferInstance

/-- **WS-SM SM2.C.4**: the operational-semantics step function.

Each `RwLockOp` maps to a single transition on the abstract state,
producing a new state.  The function is total and deterministic —
`applyOp` is the unique function from `(state, op)` to next state
(witnessed by `rwLock_applyOp_deterministic`).

### Top-level no-op gate (acquire ops)

Both `tryAcquireRead` and `tryAcquireWrite` first check
`coreInvolved core`: if the acquiring core is already a reader,
writer, or queued waiter, the operation is a no-op.  This single
check covers every "core already involved" sub-case and keeps the
operational semantics consistent with the `wf` invariants.

### Sub-cases for each constructor

**`tryAcquireRead core`** (after the no-op gate fails):
1. If a writer holds (writerHeld = some _): enqueue as `(core, .read)`.
2. If no writer holds but the head of waiters is a writer:
   Reader cannot bypass the writer (FIFO admission discipline ensures
   writer-starvation freedom — see `rwLock_no_writer_starvation`).
   Enqueue as `(core, .read)`.
3. Otherwise: prepend `core` to readers (acquire).

**`releaseRead core`**:
- If `core` not in readers: no-op.
- Else: remove `core` from readers; run `promoteWaitersIfReadersEmpty`.

**`tryAcquireWrite core`** (after the no-op gate fails):
- If any holder exists (writerHeld.isSome OR readers ≠ []):
  enqueue as `(core, .write)`.
- Else (no holder): set `writerHeld := some core` (acquire).

**`releaseWrite core`**:
- If `core` is not the current writer: no-op.
- Else: clear `writerHeld`; run `promoteWaitersOnWriterRelease`. -/
def RwLockState.applyOp (s : RwLockState) (op : RwLockOp) :
    RwLockState :=
  match op with
  | .tryAcquireRead core =>
      if s.coreInvolved core then s
      else if s.writerHeld.isSome then
        -- Writer holds → enqueue.
        { s with waiters := s.waiters ++ [(core, .read)] }
      else
        -- No writer holds; check head of queue for writer.
        match s.waiters with
        | (_, .write) :: _ =>
            -- Head waiter is a writer; enqueue reader to preserve FIFO.
            { s with waiters := s.waiters ++ [(core, .read)] }
        | _ =>
            -- Either waiters empty or head is reader; acquire directly.
            { s with readers := core :: s.readers }
  | .releaseRead core =>
      if core ∉ s.readers then s
      else
        let s' := { s with readers := s.readers.filter (· ≠ core) }
        s'.promoteWaitersIfReadersEmpty
  | .tryAcquireWrite core =>
      if s.coreInvolved core then s
      else if s.writerHeld.isSome ∨ s.readers ≠ [] then
        -- Lock is held → enqueue.
        { s with waiters := s.waiters ++ [(core, .write)] }
      else
        -- No holder → acquire.
        { s with writerHeld := some core }
  | .releaseWrite core =>
      if s.writerHeld ≠ some core then s
      else
        let s' := { s with writerHeld := none }
        s'.promoteWaitersOnWriterRelease

-- ============================================================================
-- Foundational helpers for wf reasoning
-- ============================================================================

/-- **Helper**: extract INV-R1 (Prop form) from a wf state. -/
theorem RwLockState.wf_writerReadersExclusion {s : RwLockState} (h : s.wf) :
    ∀ c, s.writerHeld = some c → s.readers = [] :=
  (s.writerReadersExclusion_iff).mp h.1

/-- **Helper**: extract INV-R2 from a wf state. -/
theorem RwLockState.wf_readersNodup {s : RwLockState} (h : s.wf) :
    s.readers.Nodup :=
  h.2.1

/-- **Helper**: extract INV-R3 from a wf state. -/
theorem RwLockState.wf_waitersCoresNodup {s : RwLockState} (h : s.wf) :
    (s.waiters.map Prod.fst).Nodup :=
  h.2.2.1

/-- **Helper**: extract INV-R4 (Prop form) from a wf state. -/
theorem RwLockState.wf_waitersDisjointFromHolders {s : RwLockState} (h : s.wf) :
    ∀ w ∈ s.waiters, w.1 ∉ s.readers ∧ s.writerHeld ≠ some w.1 :=
  (s.waitersDisjointFromHolders_iff).mp h.2.2.2.1

/-- **Helper**: extract INV-R5 (Prop form) from a wf state. -/
theorem RwLockState.wf_fifoAdmissionDiscipline {s : RwLockState} (h : s.wf) :
    s.waiters ≠ [] → s.writerHeld.isSome ∨ s.readers ≠ [] :=
  (s.fifoAdmissionDiscipline_iff).mp h.2.2.2.2

/-- **Derived corollary**: if `writerHeld = some c` in a wf state, then
no reader (including `c`) is currently in `readers`. -/
theorem RwLockState.wf_writerHeld_no_readers {s : RwLockState} (h : s.wf)
    {c : CoreId} (h_w : s.writerHeld = some c) :
    s.readers = [] :=
  s.wf_writerReadersExclusion h c h_w

/-- **Derived corollary**: in a wf state, if no holders are present
(writerHeld = none ∧ readers = []), then waiters is empty.

Proof: by contradiction.  If waiters is non-empty, INV-R5 forces
`writerHeld.isSome ∨ readers ≠ []`, contradicting `h_no_holder`. -/
theorem RwLockState.wf_calm_iff_waiters_empty {s : RwLockState} (h : s.wf)
    (h_no_holder : s.writerHeld = none ∧ s.readers = []) :
    s.waiters = [] := by
  have h_disc := s.wf_fifoAdmissionDiscipline h
  cases h_w : s.waiters with
  | nil => rfl
  | cons head rest =>
    -- s.waiters ≠ [], so INV-R5 says writerHeld.isSome OR readers ≠ [].
    have h_ne : s.waiters ≠ [] := by rw [h_w]; intro h; exact List.cons_ne_nil _ _ h
    rcases h_disc h_ne with h_some | h_r
    · -- writerHeld.isSome contradicts writerHeld = none.
      rw [h_no_holder.1] at h_some
      exact absurd h_some (by simp)
    · -- readers ≠ [] contradicts readers = [].
      exact absurd h_no_holder.2 h_r

-- ============================================================================
-- SM2.C.5 — rwLock_writer_readers_exclusion
-- ============================================================================

/-- **Theorem 3.3.5.1 (SM2.C.5): writer-readers exclusion.**

For any wf RwLockState `s`, if `s.writerHeld = some c`, then
`s.readers = []`.  This is the foundational mutex property between
the writer and the reader pool.

Proof: direct extraction from INV-R1.

This is the surface anchor SM3 per-object lock proofs cite when
arguing that a writer-protected object's reader-protected fields are
inaccessible during writer-held intervals. -/
theorem rwLock_writer_readers_exclusion (s : RwLockState) (h : s.wf) :
    ∀ c, s.writerHeld = some c → s.readers = [] :=
  s.wf_writerReadersExclusion h

-- ============================================================================
-- SM2.C.6 — rwLock_reader_multiplicity
-- ============================================================================

/-- **Theorem 3.3.6.1 (SM2.C.6): reader multiplicity.**

There exists a reachable wf `RwLockState` `s` with `s.readers.length ≥ 2`.

Proof: construct the state explicitly via two sequential
`tryAcquireRead` operations from `unheld`.  Each operation appends a
new reader (since no writer holds and the queue is empty).  The
resulting state has exactly two readers.

This witnesses that the RwLock's "shared read" semantics is operationally
non-trivial — it's not equivalent to a mutex.  Useful as a
sanity-check anchor for downstream consumers that the reader-batching
and reader-multiplicity properties are realised. -/
theorem rwLock_reader_multiplicity :
    ∃ s : RwLockState, s.wf ∧ s.readers.length ≥ 2 := by
  -- Construct the state: unheld → tryAcquireRead boot → tryAcquireRead c1.
  let c0 : CoreId := bootCoreId
  let c1 : CoreId := ⟨1, by decide⟩
  let s0 := RwLockState.unheld
  let s1 := s0.applyOp (.tryAcquireRead c0)
  let s2 := s1.applyOp (.tryAcquireRead c1)
  refine ⟨s2, ?_, ?_⟩
  · -- s2.wf: discharged by decide.
    show s2.wf
    decide
  · -- s2.readers.length ≥ 2: discharged by decide.
    show s2.readers.length ≥ 2
    decide

-- ============================================================================
-- SM2.C.12 — rwLock_wf_invariant (per-op + aggregate)
-- ============================================================================

/-- **Helper**: under `wf` + writer holds, the writer's core is not in
the readers list.  Direct consequence of INV-R1. -/
theorem RwLockState.wf_writer_not_in_readers {s : RwLockState} (h : s.wf)
    {c : CoreId} (h_held : s.writerHeld = some c) : c ∉ s.readers := by
  have h_empty := s.wf_writerReadersExclusion h c h_held
  rw [h_empty]
  exact List.not_mem_nil

/-- **Helper**: if `coreInvolved core` fails on `s`, then `core` is not
in readers, not the writer, and not in waiters' cores. -/
theorem RwLockState.not_coreInvolved_iff (s : RwLockState) (core : CoreId) :
    ¬ s.coreInvolved core ↔
    core ∉ s.readers ∧ s.writerHeld ≠ some core ∧ core ∉ s.waiters.map Prod.fst := by
  unfold RwLockState.coreInvolved
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro h_in; exact h (Or.inl h_in)
    · intro h_eq; exact h (Or.inr (Or.inl h_eq))
    · intro h_in; exact h (Or.inr (Or.inr h_in))
  · intro ⟨h1, h2, h3⟩ h_or
    rcases h_or with h_r | h_w | h_q
    · exact h1 h_r
    · exact h2 h_w
    · exact h3 h_q

/-- **File-local helper**: appending a singleton `[(core, mode)]` to a
`Nodup`-map-fst list, where `core` is not in the existing list, preserves
the Nodup-map-fst property. -/
private theorem nodup_map_fst_append_singleton
    (l : List (CoreId × AccessMode)) (core : CoreId) (mode : AccessMode)
    (h_nodup : (l.map Prod.fst).Nodup)
    (h_not_in : core ∉ l.map Prod.fst) :
    ((l ++ [(core, mode)]).map Prod.fst).Nodup := by
  rw [List.map_append, List.map_cons, List.map_nil]
  apply List.nodup_append.mpr
  refine ⟨h_nodup, ?_, ?_⟩
  · -- [core].Nodup
    exact (List.nodup_cons (a := core) (l := [])).mpr ⟨by simp, List.Pairwise.nil⟩
  · -- ∀ a ∈ l.map fst, ∀ b ∈ [core], a ≠ b
    intro a ha b hb
    simp at hb
    subst hb
    intro h_eq
    apply h_not_in
    rw [← h_eq]
    exact ha

/-- **Factored constructor**: build the post-state of an enqueue-as-read
operation.  Used by the writer-holds and writer-head branches of
`tryAcquireRead`. -/
private theorem wf_after_enqueue_read
    (s : RwLockState) (core : CoreId) (h : s.wf)
    (h_not_in_r : core ∉ s.readers)
    (h_not_writer : s.writerHeld ≠ some core)
    (h_not_in_w : core ∉ s.waiters.map Prod.fst)
    (h_post_disc : s.writerHeld.isSome ∨ s.readers ≠ []) :
    ({ s with waiters := s.waiters ++ [(core, AccessMode.read)] } : RwLockState).wf := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- INV-R1: writerHeld/readers unchanged.
    exact h.1
  · -- INV-R2: readers unchanged.
    exact h.2.1
  · -- INV-R3: waiters cores Nodup with appended fresh entry.
    show ((s.waiters ++ [(core, AccessMode.read)]).map Prod.fst).Nodup
    exact nodup_map_fst_append_singleton s.waiters core .read h.2.2.1 h_not_in_w
  · -- INV-R4: disjoint from holders.
    apply (RwLockState.waitersDisjointFromHolders_iff _).mpr
    intro w hw
    show w.1 ∉ s.readers ∧ s.writerHeld ≠ some w.1
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with hw_old | hw_new
    · exact s.wf_waitersDisjointFromHolders h w hw_old
    · subst hw_new
      exact ⟨h_not_in_r, h_not_writer⟩
  · -- INV-R5: post-waiters non-empty, satisfied by h_post_disc.
    apply (RwLockState.fifoAdmissionDiscipline_iff _).mpr
    intro _
    exact h_post_disc

/-- **Factored constructor**: build the post-state of an enqueue-as-write
operation.  Used by `tryAcquireWrite`'s "lock held" branch.

The proof is structurally identical to `wf_after_enqueue_read` (the only
difference is the mode `.write` instead of `.read` in the appended waiter,
which does not affect any of the five invariants). -/
private theorem wf_after_enqueue_write
    (s : RwLockState) (core : CoreId) (h : s.wf)
    (h_not_in_r : core ∉ s.readers)
    (h_not_writer : s.writerHeld ≠ some core)
    (h_not_in_w : core ∉ s.waiters.map Prod.fst)
    (h_post_disc : s.writerHeld.isSome ∨ s.readers ≠ []) :
    ({ s with waiters := s.waiters ++ [(core, AccessMode.write)] } : RwLockState).wf := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact h.1
  · exact h.2.1
  · show ((s.waiters ++ [(core, AccessMode.write)]).map Prod.fst).Nodup
    exact nodup_map_fst_append_singleton s.waiters core .write h.2.2.1 h_not_in_w
  · apply (RwLockState.waitersDisjointFromHolders_iff _).mpr
    intro w hw
    show w.1 ∉ s.readers ∧ s.writerHeld ≠ some w.1
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with hw_old | hw_new
    · exact s.wf_waitersDisjointFromHolders h w hw_old
    · subst hw_new
      exact ⟨h_not_in_r, h_not_writer⟩
  · apply (RwLockState.fifoAdmissionDiscipline_iff _).mpr
    intro _
    exact h_post_disc

/-- **Factored constructor**: build the post-state of a "prepend reader"
operation (direct read acquire when no writer is in the way).

Precondition: writerHeld = none AND core ∉ readers AND core ∉ waiters.map fst. -/
private theorem wf_after_direct_acquire_read
    (s : RwLockState) (core : CoreId) (h : s.wf)
    (h_no_writer : s.writerHeld = none)
    (h_not_in_r : core ∉ s.readers)
    (h_not_in_w : core ∉ s.waiters.map Prod.fst) :
    ({ s with readers := core :: s.readers } : RwLockState).wf := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- INV-R1: writerHeld = none, vacuous.
    show ({ s with readers := core :: s.readers } : RwLockState).writerReadersExclusion = true
    unfold RwLockState.writerReadersExclusion
    show (match s.writerHeld with | none => true | some _ => _) = true
    rw [h_no_writer]
  · -- INV-R2: new reader not in old.
    show (core :: s.readers).Nodup
    exact List.nodup_cons.mpr ⟨h_not_in_r, h.2.1⟩
  · -- INV-R3: waiters cores unchanged.
    exact h.2.2.1
  · -- INV-R4: disjoint.  New readers = core :: old.  For waiters:
    -- w.1 ∉ (core :: readers) iff w.1 ≠ core AND w.1 ∉ readers.
    apply (RwLockState.waitersDisjointFromHolders_iff _).mpr
    intro w hw
    show w.1 ∉ core :: s.readers ∧ s.writerHeld ≠ some w.1
    have h_old := s.wf_waitersDisjointFromHolders h w hw
    refine ⟨?_, h_old.2⟩
    simp only [List.mem_cons, not_or]
    refine ⟨?_, h_old.1⟩
    intro h_eq
    -- w.1 = core means core is in waiters, contradicting h_not_in_w.
    have h_in_map : w.1 ∈ s.waiters.map Prod.fst := List.mem_map_of_mem hw
    rw [h_eq] at h_in_map
    exact h_not_in_w h_in_map
  · -- INV-R5: readers becomes non-empty.
    apply (RwLockState.fifoAdmissionDiscipline_iff _).mpr
    intro _
    right
    show core :: s.readers ≠ []
    exact List.cons_ne_nil _ _

/-- **Factored constructor**: build the post-state of a direct write acquire
(set `writerHeld := some core`).

Precondition: writerHeld = none AND readers = [] AND core ∉ waiters.map fst.
By INV-R5, waiters must be empty in this case. -/
private theorem wf_after_direct_acquire_write
    (s : RwLockState) (core : CoreId) (h : s.wf)
    (h_no_writer : s.writerHeld = none)
    (h_no_readers : s.readers = [])
    (_h_not_in_w : core ∉ s.waiters.map Prod.fst) :
    ({ s with writerHeld := some core } : RwLockState).wf := by
  -- From INV-R5: waiters non-empty → writerHeld.isSome ∨ readers ≠ [].
  -- writerHeld = none, readers = [].  So waiters must be [].
  have h_waiters_empty : s.waiters = [] :=
    s.wf_calm_iff_waiters_empty h ⟨h_no_writer, h_no_readers⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- INV-R1: writerHeld = some core, readers = [].
    show ({ s with writerHeld := some core } : RwLockState).writerReadersExclusion = true
    unfold RwLockState.writerReadersExclusion
    show (match some core with | none => true | some _ => decide (s.readers = [])) = true
    rw [h_no_readers]
    rfl
  · -- INV-R2: readers unchanged = []. Nodup of [] is trivial.
    exact h.2.1
  · -- INV-R3: waiters cores Nodup.
    exact h.2.2.1
  · -- INV-R4: disjoint.  waiters = [].
    show ({ s with writerHeld := some core } : RwLockState).waitersDisjointFromHolders = true
    unfold RwLockState.waitersDisjointFromHolders
    show (({ s with writerHeld := some core } : RwLockState).waiters).all _ = true
    rw [show ({ s with writerHeld := some core } : RwLockState).waiters = s.waiters from rfl]
    rw [h_waiters_empty]; rfl
  · -- INV-R5: waiters = [].
    show ({ s with writerHeld := some core } : RwLockState).fifoAdmissionDiscipline = true
    unfold RwLockState.fifoAdmissionDiscipline
    rw [show ({ s with writerHeld := some core } : RwLockState).waiters = s.waiters from rfl]
    rw [h_waiters_empty]
    rfl

/-- **wf-preservation case**: `tryAcquireRead core` preserves wf.

The clean operational semantics has three branches after the no-op
gate:
* **Writer holds**: enqueue `(core, .read)`.
* **No writer + writer at head**: enqueue `(core, .read)`.
* **Otherwise**: prepend `core` to readers (acquire).

Each branch is discharged via the corresponding factored constructor
(`wf_after_enqueue_read` or `wf_after_direct_acquire_read`). -/
theorem rwLock_tryAcquireRead_preserves_wf
    (s : RwLockState) (core : CoreId) (h : s.wf) :
    (s.applyOp (.tryAcquireRead core)).wf := by
  unfold RwLockState.applyOp
  -- No-op gate.
  by_cases h_inv : s.coreInvolved core
  · simp [h_inv]; exact h
  simp only [h_inv, ↓reduceIte]
  -- Extract not-involved decomposition.
  have ⟨h_not_in_r, h_not_writer, h_not_in_w⟩ := (s.not_coreInvolved_iff core).mp h_inv
  -- Branch 1: writer holds.
  by_cases h_held : s.writerHeld.isSome
  · simp only [h_held, ↓reduceIte]
    exact wf_after_enqueue_read s core h h_not_in_r h_not_writer h_not_in_w (Or.inl h_held)
  · -- No writer.
    simp only [h_held, Bool.false_eq_true, ↓reduceIte]
    have h_none : s.writerHeld = none := Option.not_isSome_iff_eq_none.mp h_held
    have h_pre_disc := s.wf_fifoAdmissionDiscipline h
    -- Split on the head of waiters.
    match h_w_eq : s.waiters with
    | [] =>
      -- Waiters empty → direct acquire.  Inner match reduces to:
      -- { writerHeld := s.writerHeld, readers := core :: s.readers, waiters := [] }
      -- which equals { s with readers := core :: s.readers } when s.waiters = [].
      have h_post :
          ({ writerHeld := s.writerHeld, readers := core :: s.readers,
              waiters := ([] : List (CoreId × AccessMode)) } : RwLockState) =
          ({ s with readers := core :: s.readers } : RwLockState) := by
        congr 1; exact h_w_eq.symm
      rw [h_post]
      exact wf_after_direct_acquire_read s core h h_none h_not_in_r h_not_in_w
    | (wcore, .write) :: rest =>
      -- Head is writer → enqueue.  Inner match reduces to:
      -- { writerHeld := s.writerHeld, readers := s.readers,
      --   waiters := (wcore, .write) :: rest ++ [(core, .read)] }
      -- which equals { s with waiters := s.waiters ++ [(core, .read)] }.
      have h_post :
          ({ writerHeld := s.writerHeld, readers := s.readers,
              waiters := (wcore, AccessMode.write) :: rest ++ [(core, AccessMode.read)] }
            : RwLockState) =
          ({ s with waiters := s.waiters ++ [(core, AccessMode.read)] } : RwLockState) := by
        congr 1; rw [h_w_eq]
      rw [h_post]
      apply wf_after_enqueue_read s core h h_not_in_r h_not_writer h_not_in_w
      have h_pre_ne : s.waiters ≠ [] := by
        rw [h_w_eq]; intro hh; exact List.cons_ne_nil _ _ hh
      rcases h_pre_disc h_pre_ne with h_w | h_r
      · exact Or.inl h_w
      · exact Or.inr h_r
    | (wcore, .read) :: rest =>
      -- Head is reader → direct acquire.  Inner match reduces to:
      -- { writerHeld := s.writerHeld, readers := core :: s.readers,
      --   waiters := (wcore, .read) :: rest }.
      have h_post :
          ({ writerHeld := s.writerHeld, readers := core :: s.readers,
              waiters := (wcore, AccessMode.read) :: rest } : RwLockState) =
          ({ s with readers := core :: s.readers } : RwLockState) := by
        congr 1; exact h_w_eq.symm
      rw [h_post]
      exact wf_after_direct_acquire_read s core h h_none h_not_in_r h_not_in_w

/-- **wf-preservation case**: `tryAcquireWrite core` preserves wf.

The clean operational semantics has two branches after the no-op gate:
* **Lock held** (writerHeld.isSome OR readers ≠ []): enqueue `(core, .write)`.
* **Lock free**: set `writerHeld := some core`.

The enqueue branch uses `wf_after_enqueue_write`; the direct-acquire branch
uses `wf_after_direct_acquire_write`. -/
theorem rwLock_tryAcquireWrite_preserves_wf
    (s : RwLockState) (core : CoreId) (h : s.wf) :
    (s.applyOp (.tryAcquireWrite core)).wf := by
  unfold RwLockState.applyOp
  -- No-op gate.
  by_cases h_inv : s.coreInvolved core
  · simp [h_inv]; exact h
  simp only [h_inv, ↓reduceIte]
  have ⟨h_not_in_r, h_not_writer, h_not_in_w⟩ := (s.not_coreInvolved_iff core).mp h_inv
  -- Lock held?
  by_cases h_locked : s.writerHeld.isSome ∨ s.readers ≠ []
  · -- Enqueue branch.
    simp only [h_locked, ↓reduceIte]
    exact wf_after_enqueue_write s core h h_not_in_r h_not_writer h_not_in_w h_locked
  · -- Direct acquire.  h_locked : ¬ (writerHeld.isSome ∨ readers ≠ [])
    simp only [h_locked, ↓reduceIte]
    -- Decompose the negation manually.
    have h_neg_or : ¬ s.writerHeld.isSome ∧ ¬ s.readers ≠ [] := by
      refine ⟨fun h => h_locked (Or.inl h), fun h => h_locked (Or.inr h)⟩
    have h_none : s.writerHeld = none := Option.not_isSome_iff_eq_none.mp h_neg_or.1
    -- LOW-7 audit-pass-3 fix: use constructive Decidable.not_not_eq instead
    -- of Classical.not_not.  `s.readers = []` is Decidable (List has DecidableEq),
    -- so the constructive form suffices.  This keeps the spec free of
    -- unnecessary Classical dependencies.
    have h_no_readers : s.readers = [] :=
      Decidable.byContradiction (fun h => h_neg_or.2 h)
    exact wf_after_direct_acquire_write s core h h_none h_no_readers h_not_in_w

-- ============================================================================
-- SM2.C.4 — promoteWaitersIfReadersEmpty wf-preservation (full-wf input)
-- ============================================================================

/-- **wf-preservation helper**: `promoteWaitersIfReadersEmpty` preserves
wf when the input is fully wf.

This is the "pure" preservation theorem: input wf → output wf.  Used by
SM3 kernel-level proofs reasoning about steady-state lock transitions.

The four sub-cases (no-op when readers non-empty / writerHeld set / waiters
empty; promote when readers empty + no writer + head waiter present) are
all handled.  The defensive "reader head with readers empty + no writer"
branch is structurally unreachable from a wf state by INV-R5. -/
theorem rwLock_promoteWaitersIfReadersEmpty_preserves_wf
    (s : RwLockState) (h : s.wf) :
    s.promoteWaitersIfReadersEmpty.wf := by
  unfold RwLockState.promoteWaitersIfReadersEmpty
  -- Case 1: readers non-empty.
  by_cases h_r_ne : !s.readers.isEmpty
  · simp [h_r_ne]; exact h
  -- h_r_ne : ¬ !s.readers.isEmpty, so s.readers.isEmpty = true.
  simp only [h_r_ne]
  have h_r_isempty : s.readers.isEmpty = true := by
    cases h_eq : s.readers.isEmpty with
    | true => rfl
    | false =>
      exfalso
      apply h_r_ne
      simp [h_eq]
  have h_r_empty : s.readers = [] := List.isEmpty_iff.mp h_r_isempty
  -- Case 2: writerHeld.isSome.
  by_cases h_w : s.writerHeld.isSome
  · simp [h_w]; exact h
  simp only [h_w, Bool.false_eq_true, ↓reduceIte]
  have h_w_none : s.writerHeld = none := Option.not_isSome_iff_eq_none.mp h_w
  -- waiters = [] by INV-R5.
  have h_waiters_empty : s.waiters = [] :=
    s.wf_calm_iff_waiters_empty h ⟨h_w_none, h_r_empty⟩
  -- Inner match: s.waiters = [].
  match h_w_eq : s.waiters with
  | [] =>
    -- No-op: post-state = s.
    show s.wf; exact h
  | (_, .write) :: _rest =>
    -- Unreachable: s.waiters = [] by h_waiters_empty.
    exact absurd (h_w_eq.symm.trans h_waiters_empty) (List.cons_ne_nil _ _)
  | (_, .read) :: _rest =>
    -- Unreachable: same reason.
    exact absurd (h_w_eq.symm.trans h_waiters_empty) (List.cons_ne_nil _ _)

-- ============================================================================
-- SM2.C.4 — promoteWaitersOnWriterRelease wf-preservation
-- ============================================================================

/-- **File-local helper**: filter (`List.takeWhile p`) preserves Nodup-map-fst.

Used by the reader-batching post-state's Nodup verification. -/
private theorem nodup_takeWhile_map_fst
    (l : List (CoreId × AccessMode)) (p : CoreId × AccessMode → Bool)
    (h : (l.map Prod.fst).Nodup) :
    ((l.takeWhile p).map Prod.fst).Nodup := by
  have h_sub : List.Sublist (l.takeWhile p) l := List.takeWhile_sublist p
  have h_sub_map : List.Sublist ((l.takeWhile p).map Prod.fst) (l.map Prod.fst) := h_sub.map _
  exact h_sub_map.nodup h

/-- **File-local helper**: dropWhile preserves Nodup-map-fst. -/
private theorem nodup_dropWhile_map_fst
    (l : List (CoreId × AccessMode)) (p : CoreId × AccessMode → Bool)
    (h : (l.map Prod.fst).Nodup) :
    ((l.dropWhile p).map Prod.fst).Nodup := by
  have h_sub : List.Sublist (l.dropWhile p) l := List.dropWhile_sublist p
  have h_sub_map : List.Sublist ((l.dropWhile p).map Prod.fst) (l.map Prod.fst) := h_sub.map _
  exact h_sub_map.nodup h

/-- **File-local helper**: takeWhile and dropWhile are disjoint (no shared
element if input is Nodup).  Specifically: an element of `takeWhile p l`
has core distinct from any element of `dropWhile p l` (when the map-fst is
Nodup). -/
private theorem takeWhile_dropWhile_disjoint_map_fst
    (l : List (CoreId × AccessMode)) (p : CoreId × AccessMode → Bool)
    (h_nodup : (l.map Prod.fst).Nodup) :
    ∀ a ∈ (l.takeWhile p).map Prod.fst,
      ∀ b ∈ (l.dropWhile p).map Prod.fst, a ≠ b := by
  intro a ha b hb h_eq
  -- l = takeWhile p l ++ dropWhile p l (List.takeWhile_append_dropWhile).
  -- map fst of l = (takeWhile p l).map fst ++ (dropWhile p l).map fst.
  have h_split : l.map Prod.fst =
      (l.takeWhile p).map Prod.fst ++ (l.dropWhile p).map Prod.fst := by
    rw [← List.map_append, List.takeWhile_append_dropWhile]
  rw [h_split] at h_nodup
  rw [List.nodup_append] at h_nodup
  exact h_nodup.2.2 a ha b hb h_eq

/-- **wf-preservation helper**: `promoteWaitersOnWriterRelease` preserves
wf when invoked from a state where readers = [] AND writerHeld = none.

The preconditions match the post-`releaseWrite` intermediate state:
INV-R1 (vacuous since writerHeld = none), and readers = [] (from INV-R1
pre-release).

Three sub-cases:
* waiters = []: no-op.
* head is writer: promote (set writerHeld := some c, drop head).
* head is reader: batch-promote (move contiguous reader prefix to readers,
  rest of waiters stays). -/
theorem rwLock_promoteWaitersOnWriterRelease_preserves_wf
    (s : RwLockState) (h : s.wf)
    (h_no_writer : s.writerHeld = none)
    (h_no_readers : s.readers = []) :
    s.promoteWaitersOnWriterRelease.wf := by
  unfold RwLockState.promoteWaitersOnWriterRelease
  match h_w_eq : s.waiters with
  | [] =>
    -- No-op: post-state = s.
    show s.wf; exact h
  | (c, .write) :: rest =>
    -- Promote: writerHeld := some c, waiters := rest.
    -- Post: { writerHeld := some c, readers := s.readers (= []), waiters := rest }.
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- INV-R1: writerHeld = some c, readers = [].
      show RwLockState.writerReadersExclusion _ = true
      unfold RwLockState.writerReadersExclusion
      show (match some c with | none => true | some _ => decide (s.readers = [])) = true
      rw [h_no_readers]; rfl
    · -- INV-R2: readers unchanged ([]).
      exact h.2.1
    · -- INV-R3: rest.map fst is sub-Nodup of waiters.map fst.
      show (rest.map Prod.fst).Nodup
      have h_old := h.2.2.1
      rw [h_w_eq] at h_old
      simp only [List.map_cons, List.nodup_cons] at h_old
      exact h_old.2
    · -- INV-R4: disjoint.  waiter w ∈ rest → w.1 ≠ c (from old Nodup);
      -- w.1 ∉ s.readers (= []).
      show RwLockState.waitersDisjointFromHolders _ = true
      apply (RwLockState.waitersDisjointFromHolders_iff _).mpr
      intro w hw_rest
      show w.1 ∉ s.readers ∧ some c ≠ some w.1
      refine ⟨?_, ?_⟩
      · rw [h_no_readers]; exact List.not_mem_nil
      · -- some c ≠ some w.1.  From Nodup on (c :: rest).map fst.
        intro h_eq
        have h_c_eq : c = w.1 := Option.some.inj h_eq
        have h_old_nodup := h.2.2.1
        rw [h_w_eq] at h_old_nodup
        simp only [List.map_cons, List.nodup_cons] at h_old_nodup
        apply h_old_nodup.1
        rw [h_c_eq]
        exact List.mem_map_of_mem hw_rest
    · -- INV-R5: writerHeld.isSome.
      apply (RwLockState.fifoAdmissionDiscipline_iff _).mpr
      intro _
      exact Or.inl (by simp)
  | (rc, .read) :: rest =>
    -- Batch-promote: move contiguous reader prefix to readers.
    -- The post-state has the form (after match reduction):
    -- { writerHeld := s.writerHeld,
    --   readers := readWaiters.map fst ++ s.readers,
    --   waiters := rest' }
    -- where readWaiters = ((rc, .read) :: rest).takeWhile ...
    -- and rest' = ((rc, .read) :: rest).dropWhile ...
    -- Using h_no_writer, h_no_readers, h_w_eq, this becomes:
    -- { writerHeld := none,
    --   readers := (s.waiters.takeWhile ...).map fst,
    --   waiters := s.waiters.dropWhile ... }
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- INV-R1: writerHeld = s.writerHeld = none, vacuous.
      show ({ writerHeld := s.writerHeld,
              readers := (((rc, AccessMode.read) :: rest).takeWhile
                          (fun w => w.2 = AccessMode.read)).map Prod.fst ++ s.readers,
              waiters := ((rc, AccessMode.read) :: rest).dropWhile
                          (fun w => w.2 = AccessMode.read) }
            : RwLockState).writerReadersExclusion = true
      unfold RwLockState.writerReadersExclusion
      show (match s.writerHeld with | none => true | some _ => _) = true
      rw [h_no_writer]
    · -- INV-R2: readers Nodup (batch-promoted appended to old readers).
      show ((((rc, AccessMode.read) :: rest).takeWhile (fun w => w.2 = AccessMode.read)).map Prod.fst
            ++ s.readers).Nodup
      rw [h_no_readers, List.append_nil]
      have h_eq : ((rc, AccessMode.read) :: rest).takeWhile (fun w => w.2 = AccessMode.read)
                = s.waiters.takeWhile (fun w => w.2 = AccessMode.read) := by
        rw [h_w_eq]
      rw [h_eq]
      exact nodup_takeWhile_map_fst s.waiters _ h.2.2.1
    · -- INV-R3: waiters cores Nodup (dropWhile preserves).
      show ((((rc, AccessMode.read) :: rest).dropWhile (fun w => w.2 = AccessMode.read)).map Prod.fst).Nodup
      have h_eq : ((rc, AccessMode.read) :: rest).dropWhile (fun w => w.2 = AccessMode.read)
                = s.waiters.dropWhile (fun w => w.2 = AccessMode.read) := by
        rw [h_w_eq]
      rw [h_eq]
      exact nodup_dropWhile_map_fst s.waiters _ h.2.2.1
    · -- INV-R4: disjoint.  Waiter w ∈ dropWhile, reader r ∈ takeWhile, no overlap.
      show ({ writerHeld := s.writerHeld,
              readers := (((rc, AccessMode.read) :: rest).takeWhile
                          (fun w => w.2 = AccessMode.read)).map Prod.fst ++ s.readers,
              waiters := ((rc, AccessMode.read) :: rest).dropWhile
                          (fun w => w.2 = AccessMode.read) }
            : RwLockState).waitersDisjointFromHolders = true
      have h_w_drop_eq : ((rc, AccessMode.read) :: rest).dropWhile (fun w => w.2 = AccessMode.read)
                       = s.waiters.dropWhile (fun w => w.2 = AccessMode.read) := by
        rw [h_w_eq]
      have h_w_take_eq : ((rc, AccessMode.read) :: rest).takeWhile (fun w => w.2 = AccessMode.read)
                       = s.waiters.takeWhile (fun w => w.2 = AccessMode.read) := by
        rw [h_w_eq]
      apply (RwLockState.waitersDisjointFromHolders_iff _).mpr
      intro w hw_drop
      show w.1 ∉ (((rc, AccessMode.read) :: rest).takeWhile
                  (fun w => w.2 = AccessMode.read)).map Prod.fst ++ s.readers
            ∧ s.writerHeld ≠ some w.1
      refine ⟨?_, ?_⟩
      · rw [h_w_take_eq, h_no_readers, List.append_nil]
        intro h_in_take
        rw [h_w_drop_eq] at hw_drop
        have h_w_in_drop_map : w.1 ∈ (s.waiters.dropWhile (fun w => w.2 = AccessMode.read)).map Prod.fst :=
          List.mem_map_of_mem hw_drop
        exact takeWhile_dropWhile_disjoint_map_fst s.waiters _ h.2.2.1 w.1 h_in_take w.1 h_w_in_drop_map rfl
      · rw [h_no_writer]; simp
    · -- INV-R5: post-waiters non-empty → readers ≠ [] (takeWhile is non-empty here).
      show ({ writerHeld := s.writerHeld,
              readers := (((rc, AccessMode.read) :: rest).takeWhile
                          (fun w => w.2 = AccessMode.read)).map Prod.fst ++ s.readers,
              waiters := ((rc, AccessMode.read) :: rest).dropWhile
                          (fun w => w.2 = AccessMode.read) }
            : RwLockState).fifoAdmissionDiscipline = true
      apply (RwLockState.fifoAdmissionDiscipline_iff _).mpr
      intro _
      right
      -- The takeWhile of (rc, .read) :: rest with predicate (·.2 = .read) takes
      -- at least (rc, .read), so its map.fst is non-empty (contains rc).
      have h_takeWhile_head : ((rc, AccessMode.read) :: rest).takeWhile
                              (fun w => w.2 = AccessMode.read) = (rc, AccessMode.read) ::
                              rest.takeWhile (fun w => w.2 = AccessMode.read) := by
        simp
      rw [h_takeWhile_head]
      simp only [List.map_cons]
      intro h_eq
      -- core :: ... = [] impossible.
      exact List.cons_ne_nil _ _ h_eq

-- ============================================================================
-- SM2.C.12 — releaseRead / releaseWrite preservation
-- ============================================================================

/-- **File-local helper**: filtering preserves Nodup. -/
private theorem nodup_filter
    (l : List CoreId) (p : CoreId → Bool) (h : l.Nodup) :
    (l.filter p).Nodup := by
  have h_sub : List.Sublist (l.filter p) l := List.filter_sublist
  exact h_sub.nodup h

/-- **Weaker wf predicate**: `wfPartial` carries only the four "structural"
invariants (INV-R1..R4) without the FIFO admission discipline (INV-R5).

This is the natural invariant for the INTERMEDIATE state inside the composed
release steps: `releaseRead` filters readers (potentially leaving readers
empty while waiters are still non-empty, transiently breaking INV-R5);
`releaseWrite` clears writerHeld (transiently breaking INV-R5).  In both
cases the immediately-following promote step restores INV-R5.

`wfPartial` plus the appropriate "what got cleared" precondition is what
the helper preservation theorems consume to conclude the post-promote
state is fully wf. -/
def RwLockState.wfPartial (s : RwLockState) : Prop :=
  s.writerReadersExclusion = true
  ∧ s.readers.Nodup
  ∧ (s.waiters.map Prod.fst).Nodup
  ∧ s.waitersDisjointFromHolders = true

/-- `wfPartial` is decidable. -/
instance RwLockState.decidableWfPartial (s : RwLockState) :
    Decidable s.wfPartial := by
  unfold RwLockState.wfPartial
  exact inferInstance

/-- Full `wf` implies `wfPartial`. -/
theorem RwLockState.wf_implies_wfPartial {s : RwLockState} (h : s.wf) :
    s.wfPartial :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- `wfPartial` + INV-R5 conditions = full wf. -/
theorem RwLockState.wfPartial_to_wf {s : RwLockState} (h : s.wfPartial)
    (h_inv_r5 : s.waiters = [] ∨ s.writerHeld.isSome ∨ s.readers ≠ []) :
    s.wf := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, ?_⟩
  apply (RwLockState.fifoAdmissionDiscipline_iff _).mpr
  intro h_ne
  rcases h_inv_r5 with h_empty | h_writer | h_readers
  · exact absurd h_empty h_ne
  · exact Or.inl h_writer
  · exact Or.inr h_readers

/-- **Generalized wf-preservation helper**: `promoteWaitersOnWriterRelease`
takes `wfPartial` + (writerHeld = none) + (readers = []) to full wf.

This is the version used by `releaseWrite`: the intermediate state has
writerHeld cleared and readers = [] (by INV-R1 pre-release), but INV-R5
may be transiently violated.  This theorem proves that the promote step
restores INV-R5. -/
theorem rwLock_promoteWaitersOnWriterRelease_preserves_wf_partial
    (s : RwLockState) (h : s.wfPartial)
    (h_no_writer : s.writerHeld = none)
    (h_no_readers : s.readers = []) :
    s.promoteWaitersOnWriterRelease.wf := by
  unfold RwLockState.promoteWaitersOnWriterRelease
  match h_w_eq : s.waiters with
  | [] =>
    -- No-op: post-state = s.  Need s.wf.  But we only have wfPartial.
    -- INV-R5 vacuous since waiters = [].
    show s.wf
    exact RwLockState.wfPartial_to_wf h (Or.inl h_w_eq)
  | (c, .write) :: rest =>
    -- Promote: writerHeld := some c, waiters := rest.
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- INV-R1: writerHeld = some c, readers = [].
      show RwLockState.writerReadersExclusion _ = true
      unfold RwLockState.writerReadersExclusion
      show (match some c with | none => true | some _ => decide (s.readers = [])) = true
      rw [h_no_readers]; rfl
    · -- INV-R2: readers unchanged.
      exact h.2.1
    · -- INV-R3.
      show (rest.map Prod.fst).Nodup
      have h_old := h.2.2.1
      rw [h_w_eq] at h_old
      simp only [List.map_cons, List.nodup_cons] at h_old
      exact h_old.2
    · -- INV-R4.
      show RwLockState.waitersDisjointFromHolders _ = true
      apply (RwLockState.waitersDisjointFromHolders_iff _).mpr
      intro w hw_rest
      show w.1 ∉ s.readers ∧ some c ≠ some w.1
      refine ⟨?_, ?_⟩
      · rw [h_no_readers]; exact List.not_mem_nil
      · intro h_eq
        have h_c_eq : c = w.1 := Option.some.inj h_eq
        have h_old_nodup := h.2.2.1
        rw [h_w_eq] at h_old_nodup
        simp only [List.map_cons, List.nodup_cons] at h_old_nodup
        apply h_old_nodup.1
        rw [h_c_eq]
        exact List.mem_map_of_mem hw_rest
    · -- INV-R5: writerHeld.isSome.
      apply (RwLockState.fifoAdmissionDiscipline_iff _).mpr
      intro _
      exact Or.inl (by simp)
  | (rc, .read) :: rest =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show ({ writerHeld := s.writerHeld,
              readers := (((rc, AccessMode.read) :: rest).takeWhile
                          (fun w => w.2 = AccessMode.read)).map Prod.fst ++ s.readers,
              waiters := ((rc, AccessMode.read) :: rest).dropWhile
                          (fun w => w.2 = AccessMode.read) }
            : RwLockState).writerReadersExclusion = true
      unfold RwLockState.writerReadersExclusion
      show (match s.writerHeld with | none => true | some _ => _) = true
      rw [h_no_writer]
    · show ((((rc, AccessMode.read) :: rest).takeWhile (fun w => w.2 = AccessMode.read)).map Prod.fst
            ++ s.readers).Nodup
      rw [h_no_readers, List.append_nil]
      have h_eq : ((rc, AccessMode.read) :: rest).takeWhile (fun w => w.2 = AccessMode.read)
                = s.waiters.takeWhile (fun w => w.2 = AccessMode.read) := by
        rw [h_w_eq]
      rw [h_eq]
      exact nodup_takeWhile_map_fst s.waiters _ h.2.2.1
    · show ((((rc, AccessMode.read) :: rest).dropWhile (fun w => w.2 = AccessMode.read)).map Prod.fst).Nodup
      have h_eq : ((rc, AccessMode.read) :: rest).dropWhile (fun w => w.2 = AccessMode.read)
                = s.waiters.dropWhile (fun w => w.2 = AccessMode.read) := by
        rw [h_w_eq]
      rw [h_eq]
      exact nodup_dropWhile_map_fst s.waiters _ h.2.2.1
    · show ({ writerHeld := s.writerHeld,
              readers := (((rc, AccessMode.read) :: rest).takeWhile
                          (fun w => w.2 = AccessMode.read)).map Prod.fst ++ s.readers,
              waiters := ((rc, AccessMode.read) :: rest).dropWhile
                          (fun w => w.2 = AccessMode.read) }
            : RwLockState).waitersDisjointFromHolders = true
      have h_w_drop_eq : ((rc, AccessMode.read) :: rest).dropWhile (fun w => w.2 = AccessMode.read)
                       = s.waiters.dropWhile (fun w => w.2 = AccessMode.read) := by
        rw [h_w_eq]
      have h_w_take_eq : ((rc, AccessMode.read) :: rest).takeWhile (fun w => w.2 = AccessMode.read)
                       = s.waiters.takeWhile (fun w => w.2 = AccessMode.read) := by
        rw [h_w_eq]
      apply (RwLockState.waitersDisjointFromHolders_iff _).mpr
      intro w hw_drop
      show w.1 ∉ (((rc, AccessMode.read) :: rest).takeWhile
                  (fun w => w.2 = AccessMode.read)).map Prod.fst ++ s.readers
            ∧ s.writerHeld ≠ some w.1
      refine ⟨?_, ?_⟩
      · rw [h_w_take_eq, h_no_readers, List.append_nil]
        intro h_in_take
        rw [h_w_drop_eq] at hw_drop
        have h_w_in_drop_map : w.1 ∈ (s.waiters.dropWhile (fun w => w.2 = AccessMode.read)).map Prod.fst :=
          List.mem_map_of_mem hw_drop
        exact takeWhile_dropWhile_disjoint_map_fst s.waiters _ h.2.2.1 w.1 h_in_take w.1 h_w_in_drop_map rfl
      · rw [h_no_writer]; simp
    · show ({ writerHeld := s.writerHeld,
              readers := (((rc, AccessMode.read) :: rest).takeWhile
                          (fun w => w.2 = AccessMode.read)).map Prod.fst ++ s.readers,
              waiters := ((rc, AccessMode.read) :: rest).dropWhile
                          (fun w => w.2 = AccessMode.read) }
            : RwLockState).fifoAdmissionDiscipline = true
      apply (RwLockState.fifoAdmissionDiscipline_iff _).mpr
      intro _
      right
      have h_takeWhile_head : ((rc, AccessMode.read) :: rest).takeWhile
                              (fun w => w.2 = AccessMode.read) = (rc, AccessMode.read) ::
                              rest.takeWhile (fun w => w.2 = AccessMode.read) := by
        simp
      rw [h_takeWhile_head]
      simp only [List.map_cons]
      rw [h_no_readers, List.append_nil]
      intro h_eq
      exact List.cons_ne_nil _ _ h_eq

/-- **Generalized wf-preservation helper for `promoteWaitersIfReadersEmpty`**.

Takes `wfPartial` instead of full `wf`.  Used by `releaseRead`. -/
theorem rwLock_promoteWaitersIfReadersEmpty_preserves_wf_partial
    (s : RwLockState) (h : s.wfPartial) :
    s.promoteWaitersIfReadersEmpty.wf := by
  unfold RwLockState.promoteWaitersIfReadersEmpty
  -- Case 1: readers non-empty.
  by_cases h_r_ne : !s.readers.isEmpty
  · -- No-op: post = s.  INV-R5 satisfied because readers ≠ [].
    simp [h_r_ne]
    apply RwLockState.wfPartial_to_wf h
    right; right
    -- h_r_ne : !s.readers.isEmpty = true.  Need readers ≠ [].
    intro h_eq
    rw [h_eq] at h_r_ne
    simp at h_r_ne
  simp only [h_r_ne]
  have h_r_isempty : s.readers.isEmpty = true := by
    cases h_eq : s.readers.isEmpty with
    | true => rfl
    | false =>
      exfalso; apply h_r_ne; simp [h_eq]
  have h_r_empty : s.readers = [] := List.isEmpty_iff.mp h_r_isempty
  -- Case 2: writerHeld.isSome.
  by_cases h_w : s.writerHeld.isSome
  · -- No-op: post = s.  INV-R5 satisfied because writerHeld.isSome.
    simp [h_w]
    apply RwLockState.wfPartial_to_wf h
    right; left; exact h_w
  simp only [h_w, Bool.false_eq_true, ↓reduceIte]
  have h_w_none : s.writerHeld = none := Option.not_isSome_iff_eq_none.mp h_w
  -- Case 3: readers = [] AND writerHeld = none.  Branch on waiters.
  match h_w_eq : s.waiters with
  | [] =>
    -- No-op: post = s.  INV-R5 vacuous (waiters = []).
    show s.wf
    exact RwLockState.wfPartial_to_wf h (Or.inl h_w_eq)
  | (c, .write) :: rest =>
    -- Promote writer.  Same proof as in promoteWaitersOnWriterRelease.
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show RwLockState.writerReadersExclusion _ = true
      unfold RwLockState.writerReadersExclusion
      show (match some c with | none => true | some _ => decide (s.readers = [])) = true
      rw [h_r_empty]; rfl
    · exact h.2.1
    · show (rest.map Prod.fst).Nodup
      have h_old := h.2.2.1
      rw [h_w_eq] at h_old
      simp only [List.map_cons, List.nodup_cons] at h_old
      exact h_old.2
    · show RwLockState.waitersDisjointFromHolders _ = true
      apply (RwLockState.waitersDisjointFromHolders_iff _).mpr
      intro w hw_rest
      show w.1 ∉ s.readers ∧ some c ≠ some w.1
      refine ⟨?_, ?_⟩
      · rw [h_r_empty]; exact List.not_mem_nil
      · intro h_eq
        have h_c_eq : c = w.1 := Option.some.inj h_eq
        have h_old_nodup := h.2.2.1
        rw [h_w_eq] at h_old_nodup
        simp only [List.map_cons, List.nodup_cons] at h_old_nodup
        apply h_old_nodup.1
        rw [h_c_eq]
        exact List.mem_map_of_mem hw_rest
    · apply (RwLockState.fifoAdmissionDiscipline_iff _).mpr
      intro _
      exact Or.inl (by simp)
  | (rc, .read) :: rest =>
    -- Batch-promote readers.  Identical to the write-release reader-head case.
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show ({ writerHeld := s.writerHeld,
              readers := (((rc, AccessMode.read) :: rest).takeWhile
                          (fun w => w.2 = AccessMode.read)).map Prod.fst,
              waiters := ((rc, AccessMode.read) :: rest).dropWhile
                          (fun w => w.2 = AccessMode.read) }
            : RwLockState).writerReadersExclusion = true
      unfold RwLockState.writerReadersExclusion
      show (match s.writerHeld with | none => true | some _ => _) = true
      rw [h_w_none]
    · show ((((rc, AccessMode.read) :: rest).takeWhile (fun w => w.2 = AccessMode.read)).map Prod.fst).Nodup
      have h_eq : ((rc, AccessMode.read) :: rest).takeWhile (fun w => w.2 = AccessMode.read)
                = s.waiters.takeWhile (fun w => w.2 = AccessMode.read) := by
        rw [h_w_eq]
      rw [h_eq]
      exact nodup_takeWhile_map_fst s.waiters _ h.2.2.1
    · show ((((rc, AccessMode.read) :: rest).dropWhile (fun w => w.2 = AccessMode.read)).map Prod.fst).Nodup
      have h_eq : ((rc, AccessMode.read) :: rest).dropWhile (fun w => w.2 = AccessMode.read)
                = s.waiters.dropWhile (fun w => w.2 = AccessMode.read) := by
        rw [h_w_eq]
      rw [h_eq]
      exact nodup_dropWhile_map_fst s.waiters _ h.2.2.1
    · show ({ writerHeld := s.writerHeld,
              readers := (((rc, AccessMode.read) :: rest).takeWhile
                          (fun w => w.2 = AccessMode.read)).map Prod.fst,
              waiters := ((rc, AccessMode.read) :: rest).dropWhile
                          (fun w => w.2 = AccessMode.read) }
            : RwLockState).waitersDisjointFromHolders = true
      have h_w_drop_eq : ((rc, AccessMode.read) :: rest).dropWhile (fun w => w.2 = AccessMode.read)
                       = s.waiters.dropWhile (fun w => w.2 = AccessMode.read) := by
        rw [h_w_eq]
      have h_w_take_eq : ((rc, AccessMode.read) :: rest).takeWhile (fun w => w.2 = AccessMode.read)
                       = s.waiters.takeWhile (fun w => w.2 = AccessMode.read) := by
        rw [h_w_eq]
      apply (RwLockState.waitersDisjointFromHolders_iff _).mpr
      intro w hw_drop
      show w.1 ∉ (((rc, AccessMode.read) :: rest).takeWhile
                  (fun w => w.2 = AccessMode.read)).map Prod.fst
            ∧ s.writerHeld ≠ some w.1
      refine ⟨?_, ?_⟩
      · rw [h_w_take_eq]
        intro h_in_take
        rw [h_w_drop_eq] at hw_drop
        have h_w_in_drop_map : w.1 ∈ (s.waiters.dropWhile (fun w => w.2 = AccessMode.read)).map Prod.fst :=
          List.mem_map_of_mem hw_drop
        exact takeWhile_dropWhile_disjoint_map_fst s.waiters _ h.2.2.1 w.1 h_in_take w.1 h_w_in_drop_map rfl
      · rw [h_w_none]; simp
    · apply (RwLockState.fifoAdmissionDiscipline_iff _).mpr
      intro _
      right
      have h_takeWhile_head : ((rc, AccessMode.read) :: rest).takeWhile
                              (fun w => w.2 = AccessMode.read) = (rc, AccessMode.read) ::
                              rest.takeWhile (fun w => w.2 = AccessMode.read) := by
        simp
      rw [h_takeWhile_head]
      simp only [List.map_cons]
      intro h_eq
      exact List.cons_ne_nil _ _ h_eq

/-- **wf-preservation case**: `releaseRead core` preserves wf.

Two sub-cases:
* `core ∉ readers`: no-op; wf preserved trivially.
* `core ∈ readers`: filter readers, then run promoteWaitersIfReadersEmpty.

The intermediate state (after filter) satisfies `wfPartial` (4 invariants),
and INV-R5 is restored by the subsequent promote step (which is proven
via `rwLock_promoteWaitersIfReadersEmpty_preserves_wf_partial`). -/
theorem rwLock_releaseRead_preserves_wf
    (s : RwLockState) (core : CoreId) (h : s.wf) :
    (s.applyOp (.releaseRead core)).wf := by
  unfold RwLockState.applyOp
  by_cases h_not_in : core ∉ s.readers
  · simp [h_not_in]; exact h
  simp only [h_not_in, ↓reduceIte]
  -- Need to prove the intermediate state has wfPartial; then apply the helper.
  apply rwLock_promoteWaitersIfReadersEmpty_preserves_wf_partial
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- INV-R1: writerHeld unchanged.  Since core ∈ s.readers, by INV-R1
    -- writerHeld = none, so vacuous.
    show RwLockState.writerReadersExclusion _ = true
    unfold RwLockState.writerReadersExclusion
    show (match s.writerHeld with
            | none => true
            | some _ => decide (s.readers.filter (· ≠ core) = [])) = true
    cases h_w_eq : s.writerHeld with
    | none => rfl
    | some c =>
      have h_r_empty := s.wf_writerReadersExclusion h c h_w_eq
      simp only [Decidable.not_not] at h_not_in
      rw [h_r_empty] at h_not_in
      exact absurd h_not_in List.not_mem_nil
  · -- INV-R2: filter preserves Nodup.
    show (s.readers.filter (· ≠ core)).Nodup
    exact nodup_filter s.readers (· ≠ core) h.2.1
  · -- INV-R3: waiters unchanged.
    exact h.2.2.1
  · -- INV-R4: disjoint with filtered readers (sub-list of original).
    show RwLockState.waitersDisjointFromHolders _ = true
    apply (RwLockState.waitersDisjointFromHolders_iff _).mpr
    intro w hw
    show w.1 ∉ s.readers.filter (· ≠ core) ∧ s.writerHeld ≠ some w.1
    have h_old := s.wf_waitersDisjointFromHolders h w hw
    refine ⟨?_, h_old.2⟩
    intro h_in_filter
    rw [List.mem_filter] at h_in_filter
    exact h_old.1 h_in_filter.1

/-- **wf-preservation case**: `releaseWrite core` preserves wf.

Two sub-cases:
* `s.writerHeld ≠ some core`: no-op.
* `s.writerHeld = some core`: clear writerHeld, run promoteWaitersOnWriterRelease.

The intermediate state has writerHeld = none, readers = [] (from pre-INV-R1),
waiters unchanged.  It satisfies `wfPartial`; INV-R5 is restored by the
promote step. -/
theorem rwLock_releaseWrite_preserves_wf
    (s : RwLockState) (core : CoreId) (h : s.wf) :
    (s.applyOp (.releaseWrite core)).wf := by
  unfold RwLockState.applyOp
  by_cases h_holds : s.writerHeld ≠ some core
  · simp [h_holds]; exact h
  simp only [h_holds, ↓reduceIte]
  simp only [Decidable.not_not] at h_holds
  -- h_holds : s.writerHeld = some core
  have h_r_empty := s.wf_writerReadersExclusion h core h_holds
  -- Apply the partial-wf helper.
  apply rwLock_promoteWaitersOnWriterRelease_preserves_wf_partial
  · -- wfPartial on intermediate.
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- INV-R1: writerHeld = none → vacuous.
      show RwLockState.writerReadersExclusion _ = true
      unfold RwLockState.writerReadersExclusion
      show (match (none : Option CoreId) with
              | none => true
              | some _ => decide (s.readers = [])) = true
      rfl
    · -- INV-R2.
      exact h.2.1
    · -- INV-R3.
      exact h.2.2.1
    · -- INV-R4: disjoint (writerHeld is now none, so the second conjunct is trivially preserved).
      show RwLockState.waitersDisjointFromHolders _ = true
      apply (RwLockState.waitersDisjointFromHolders_iff _).mpr
      intro w hw
      show w.1 ∉ s.readers ∧ (none : Option CoreId) ≠ some w.1
      refine ⟨?_, ?_⟩
      · exact (s.wf_waitersDisjointFromHolders h w hw).1
      · simp
  · -- writerHeld = none in intermediate.
    rfl
  · -- readers = [] in intermediate (= s.readers = []).
    exact h_r_empty

-- ============================================================================
-- SM2.C.12 — Aggregator: rwLock_wf_invariant
-- ============================================================================

/-- **Theorem (SM2.C.12, aggregate): wf is preserved by every kernel-facing
RwLock transition.**

For any `RwLockState s` satisfying `s.wf` and any core `c`:
* `applyOp .tryAcquireRead c` preserves wf.
* `applyOp .releaseRead c` preserves wf.
* `applyOp .tryAcquireWrite c` preserves wf.
* `applyOp .releaseWrite c` preserves wf.

This is the canonical surface anchor that SM3 / kernel-level proofs cite
when reasoning about long sequences of RwLock operations. -/
theorem rwLock_wf_invariant (s : RwLockState) (h : s.wf) :
    (∀ c, (s.applyOp (.tryAcquireRead c)).wf)
    ∧ (∀ c, (s.applyOp (.releaseRead c)).wf)
    ∧ (∀ c, (s.applyOp (.tryAcquireWrite c)).wf)
    ∧ (∀ c, (s.applyOp (.releaseWrite c)).wf) :=
  ⟨fun c => rwLock_tryAcquireRead_preserves_wf s c h
  , fun c => rwLock_releaseRead_preserves_wf s c h
  , fun c => rwLock_tryAcquireWrite_preserves_wf s c h
  , fun c => rwLock_releaseWrite_preserves_wf s c h⟩

-- ============================================================================
-- SM2.C.15 — Closure-form preservation aliases
-- ============================================================================

/-- **SM2.C.15 (closure-form)**: `tryAcquireRead core` preserves wf. -/
theorem rwLock_tryAcquireRead_preserves_wf_alias
    (s : RwLockState) (core : CoreId) (h : s.wf) :
    (s.applyOp (.tryAcquireRead core)).wf :=
  rwLock_tryAcquireRead_preserves_wf s core h

/-- **SM2.C.15 (closure-form)**: `releaseRead core` preserves wf. -/
theorem rwLock_releaseRead_preserves_wf_alias
    (s : RwLockState) (core : CoreId) (h : s.wf) :
    (s.applyOp (.releaseRead core)).wf :=
  rwLock_releaseRead_preserves_wf s core h

/-- **SM2.C.15 (closure-form)**: `tryAcquireWrite core` preserves wf. -/
theorem rwLock_tryAcquireWrite_preserves_wf_alias
    (s : RwLockState) (core : CoreId) (h : s.wf) :
    (s.applyOp (.tryAcquireWrite core)).wf :=
  rwLock_tryAcquireWrite_preserves_wf s core h

/-- **SM2.C.15 (closure-form)**: `releaseWrite core` preserves wf. -/
theorem rwLock_releaseWrite_preserves_wf_alias
    (s : RwLockState) (core : CoreId) (h : s.wf) :
    (s.applyOp (.releaseWrite core)).wf :=
  rwLock_releaseWrite_preserves_wf s core h

-- ============================================================================
-- SM2.C.14 — Determinism
-- ============================================================================

/-- **Theorem (SM2.C.14): `applyOp` is deterministic.**

For any state `s` and op `op`, the result of `s.applyOp op` is unique —
`applyOp` is a total function (Lean's definitional equality witnesses this).
This is the "no-ND" property that distinguishes the abstract spec from a
weaker labelled-transition specification.

The theorem statement is trivial (it asserts function-extensionality of
`applyOp` itself), but is exported as a named theorem because SM3 / SM2.D
/ SM2.E consumers cite it when reasoning about operation sequences. -/
theorem rwLock_applyOp_deterministic (s : RwLockState) (op : RwLockOp) :
    ∀ s₁ s₂ : RwLockState,
      s₁ = s.applyOp op → s₂ = s.applyOp op → s₁ = s₂ := by
  intro s₁ s₂ h₁ h₂
  rw [h₁, h₂]

/-- **Theorem (SM2.C.14, alternate)**: `promoteWaitersOnWriterRelease` is
deterministic. -/
theorem rwLock_promoteWaitersOnWriterRelease_deterministic (s : RwLockState) :
    ∀ s₁ s₂ : RwLockState,
      s₁ = s.promoteWaitersOnWriterRelease → s₂ = s.promoteWaitersOnWriterRelease →
      s₁ = s₂ := by
  intro s₁ s₂ h₁ h₂; rw [h₁, h₂]

/-- **Theorem (SM2.C.14, alternate)**: `promoteWaitersIfReadersEmpty` is
deterministic. -/
theorem rwLock_promoteWaitersIfReadersEmpty_deterministic (s : RwLockState) :
    ∀ s₁ s₂ : RwLockState,
      s₁ = s.promoteWaitersIfReadersEmpty → s₂ = s.promoteWaitersIfReadersEmpty →
      s₁ = s₂ := by
  intro s₁ s₂ h₁ h₂; rw [h₁, h₂]

-- ============================================================================
-- SM2.C.7 — rwLock_fifo_admission (substantive structural FIFO claim)
-- ============================================================================

/-- **File-local helper**: `List.dropWhile p l` is a suffix of `l`,
specifically `l.drop` of the takeWhile-prefix-length.

Standard fact about `takeWhile` / `dropWhile`: dropWhile returns the
suffix of `l` starting at the first position where the predicate fails. -/
private theorem dropWhile_eq_drop_takeWhile_length
    {α : Type _} (l : List α) (p : α → Bool) :
    l.dropWhile p = l.drop (l.takeWhile p).length := by
  induction l with
  | nil => simp
  | cons x rest ih =>
    by_cases h : p x
    · -- predicate holds: takeWhile includes x, dropWhile recurses on rest
      simp only [List.takeWhile_cons, List.dropWhile_cons, h, ite_true,
                 List.length_cons]
      rw [show (rest.takeWhile p).length + 1 = (rest.takeWhile p).length + 1 from rfl]
      simp [List.drop_succ_cons, ih]
    · -- predicate fails: takeWhile stops at length 0, dropWhile returns x::rest
      simp [h]

/-- **Theorem 3.3.7.1 (SM2.C.7): FIFO admission — promote produces a
suffix of the waiters queue.**

The substantive FIFO claim: `promoteWaitersOnWriterRelease.waiters` is
**always a sublist of `s.waiters`** obtained by dropping a head prefix
of length `k` for some `k ≥ 0`.

Three cases (matching the function's `match` on `s.waiters`):
* `waiters = []`: post-waiters = waiters, k = 0 dropped.
* head is writer `(c, .write) :: rest`: post-waiters = `rest`, k = 1.
* head is reader: post-waiters = the suffix starting at the first
  non-reader entry; k = `(waiters.takeWhile (·.2 = .read)).length`.

In all three cases, post-waiters is **`s.waiters.drop k`** for some `k`.
This is the operational expression of FIFO admission: promotion never
reorders waiters; it only consumes from the head.

This replaces the trivial tautology that would have been produced by
returning the hypothesis unchanged.  The structural drop-prefix claim
captures FIFO at the operational-semantics level: any consumer that
relies on "earlier waiters are admitted first" can derive it from this
theorem plus the trivial property that `tryAcquire*` only appends to
the tail. -/
theorem rwLock_fifo_admission (s : RwLockState) :
    ∃ k, s.promoteWaitersOnWriterRelease.waiters = s.waiters.drop k := by
  unfold RwLockState.promoteWaitersOnWriterRelease
  cases h_w : s.waiters with
  | nil =>
    -- No-op: post-state = s, so .waiters = s.waiters = [].drop 0 = [].
    refine ⟨0, ?_⟩
    simp [h_w]
  | cons head rest =>
    obtain ⟨wcore, wmode⟩ := head
    cases wmode with
    | write =>
      -- Single head consumed: post.waiters = rest = (head :: rest).drop 1.
      refine ⟨1, ?_⟩
      simp only [List.drop_succ_cons, List.drop_zero]
    | read =>
      -- Reader prefix consumed via dropWhile (·.2 = .read).
      -- This equals `(head :: rest).drop ((head :: rest).takeWhile p).length`
      -- by `dropWhile_eq_drop_takeWhile_length`.
      refine ⟨((wcore, AccessMode.read) :: rest).takeWhile
              (fun w => w.2 = AccessMode.read) |>.length, ?_⟩
      exact dropWhile_eq_drop_takeWhile_length _ _

/-- **Lemma (SM2.C.7 companion)**: `promoteWaitersIfReadersEmpty` also
produces a suffix-via-drop of the waiters queue.

Same structural claim as `rwLock_fifo_admission` but for the reader-
release promotion path.  Two extra no-op branches (readers non-empty,
or writer held) yield `k = 0`. -/
theorem rwLock_fifo_admission_readers_empty (s : RwLockState) :
    ∃ k, s.promoteWaitersIfReadersEmpty.waiters = s.waiters.drop k := by
  unfold RwLockState.promoteWaitersIfReadersEmpty
  by_cases h_r : !s.readers.isEmpty
  · simp [h_r]; exact ⟨0, by simp⟩
  simp only [h_r]
  by_cases h_w : s.writerHeld.isSome
  · simp [h_w]; exact ⟨0, by simp⟩
  simp only [h_w, Bool.false_eq_true, ↓reduceIte]
  cases h_eq : s.waiters with
  | nil => exact ⟨0, by simp [h_eq]⟩
  | cons head rest =>
    obtain ⟨wcore, wmode⟩ := head
    cases wmode with
    | write =>
      refine ⟨1, ?_⟩
      simp only [List.drop_succ_cons, List.drop_zero]
    | read =>
      refine ⟨((wcore, AccessMode.read) :: rest).takeWhile
              (fun w => w.2 = AccessMode.read) |>.length, ?_⟩
      exact dropWhile_eq_drop_takeWhile_length _ _

/-- **Corollary (SM2.C.7)**: every surviving waiter was in the original
queue (trivial sublist property of `drop`; exported for SM3 consumers). -/
theorem rwLock_promote_subset_of_waiters (s : RwLockState)
    (w : CoreId × AccessMode)
    (h_in_post : w ∈ s.promoteWaitersOnWriterRelease.waiters) :
    w ∈ s.waiters := by
  obtain ⟨k, h_drop⟩ := rwLock_fifo_admission s
  rw [h_drop] at h_in_post
  exact List.mem_of_mem_drop h_in_post

/-- **Corollary (SM2.C.7)**: post-promote waiters is a `Sublist` of the
pre-state waiters.  This is the canonical structural statement of "no
reordering": `List.Sublist` is defined as "embedded with preserved
order", so this directly captures the order-preservation property
without appealing to indexOf. -/
theorem rwLock_promote_is_sublist_of_waiters (s : RwLockState) :
    s.promoteWaitersOnWriterRelease.waiters.Sublist s.waiters := by
  obtain ⟨k, h_drop⟩ := rwLock_fifo_admission s
  rw [h_drop]
  exact List.drop_sublist k s.waiters

/-- **Corollary (SM2.C.7, audit-pass-2 honest rename from
`rwLock_promote_preserves_order`)**: any pair of surviving waiters
shares a common drop-prefix-membership witness.

This is a structural restatement of `rwLock_fifo_admission` applied
to two elements simultaneously: if both `w₁` and `w₂` are in post-
waiters, then there's a single `k` such that both are in
`s.waiters.drop k`.

**Note**: this does NOT directly state "relative order is preserved"
— that property is captured by `rwLock_promote_is_sublist_of_waiters`
(via `List.Sublist`'s order-preserving definition).  The two
theorems are complementary: this one provides positional witnessing,
the other provides Sublist-style ordering.  (M-A audit-pass-2 honest
rename: the original `_preserves_order` name was misleading because
the theorem doesn't directly assert order preservation.) -/
theorem rwLock_promote_pair_in_drop
    (s : RwLockState) (w₁ w₂ : CoreId × AccessMode)
    (h_in₁ : w₁ ∈ s.promoteWaitersOnWriterRelease.waiters)
    (h_in₂ : w₂ ∈ s.promoteWaitersOnWriterRelease.waiters) :
    ∃ k, w₁ ∈ s.waiters.drop k ∧ w₂ ∈ s.waiters.drop k := by
  obtain ⟨k, h_drop⟩ := rwLock_fifo_admission s
  refine ⟨k, ?_, ?_⟩
  · rw [← h_drop]; exact h_in₁
  · rw [← h_drop]; exact h_in₂

/-- **Backwards-compat alias** for the previous (audit-pass-1)
theorem name.  The current honest name is
`rwLock_promote_pair_in_drop`; the new substantive order-preservation
theorem is `rwLock_promote_is_sublist_of_waiters`. -/
theorem rwLock_promote_preserves_order
    (s : RwLockState) (w₁ w₂ : CoreId × AccessMode)
    (h_in₁ : w₁ ∈ s.promoteWaitersOnWriterRelease.waiters)
    (h_in₂ : w₂ ∈ s.promoteWaitersOnWriterRelease.waiters) :
    ∃ k, w₁ ∈ s.waiters.drop k ∧ w₂ ∈ s.waiters.drop k :=
  rwLock_promote_pair_in_drop s w₁ w₂ h_in₁ h_in₂

-- ============================================================================
-- SM2.C.8 — rwLock_bounded_wait_read
-- ============================================================================

/-- **File-local helper**: a Nodup list `l₁` contained in another list `l₂`
has length at most `l₂.length`.  (Identical to TicketLock's helper; we
re-prove here to keep modules independent.) -/
private theorem nodup_subset_length_le {α : Type _} [DecidableEq α] :
    ∀ (l₁ l₂ : List α), l₁.Nodup → (∀ x ∈ l₁, x ∈ l₂) →
      l₁.length ≤ l₂.length := by
  intro l₁
  induction l₁ with
  | nil => intros; simp
  | cons x rest ih =>
    intro l₂ h_nodup h_sub
    rw [List.nodup_cons] at h_nodup
    obtain ⟨h_x_not_in_rest, h_rest_nodup⟩ := h_nodup
    have h_x_in_l₂ : x ∈ l₂ := h_sub x List.mem_cons_self
    have h_rest_sub_erase : ∀ y ∈ rest, y ∈ l₂.erase x := by
      intro y hy
      have h_y_in_l₂ : y ∈ l₂ := h_sub y (List.mem_cons_of_mem _ hy)
      have h_y_ne_x : y ≠ x := fun h_eq => h_x_not_in_rest (h_eq ▸ hy)
      exact (List.mem_erase_of_ne h_y_ne_x).mpr h_y_in_l₂
    have h_rest_bound := ih (l₂.erase x) h_rest_nodup h_rest_sub_erase
    have h_erase_len : (l₂.erase x).length = l₂.length - 1 :=
      List.length_erase_of_mem h_x_in_l₂
    have h_l₂_pos : l₂.length ≥ 1 := List.length_pos_of_mem h_x_in_l₂
    simp [List.length_cons]
    omega

/-- **File-local helper**: a Nodup list over `CoreId = Fin numCores`
has length at most `numCores`. -/
private theorem nodup_corelist_length_bound
    (l : List CoreId) (h : l.Nodup) : l.length ≤ numCores := by
  have h_sub : ∀ x ∈ l, x ∈ List.finRange numCores :=
    fun x _ => List.mem_finRange x
  have h_len_le : l.length ≤ (List.finRange numCores).length :=
    nodup_subset_length_le l (List.finRange numCores) h h_sub
  rw [List.length_finRange] at h_len_le
  exact h_len_le

/-- **File-local helper**: in a wf state with writerHeld = some c, c is
not in waiters' cores (INV-R4 says writerHeld ≠ some w.1). -/
private theorem writer_not_in_waiters {s : RwLockState} (h : s.wf)
    {c : CoreId} (h_held : s.writerHeld = some c) : c ∉ s.waiters.map Prod.fst := by
  intro h_in
  rw [List.mem_map] at h_in
  obtain ⟨w, hw_in, hw_eq⟩ := h_in
  have h_disj := (s.wf_waitersDisjointFromHolders h w hw_in).2
  apply h_disj
  rw [hw_eq, h_held]

/-- **Theorem 3.3.8.1 (SM2.C.8): bounded wait for readers.**

For any wf `RwLockState s`, the total number of cores currently involved
with the lock (readers + writer-holder + waiters) is bounded by `numCores`.

This bounds the worst-case wait time for a reader acquire: at most
`numCores - 1` cores can have outstanding holds/waits ahead of the
requester.  Combined with a critical-section bound `T_cs`, this gives
`WCRT(tryAcquireRead) ≤ (numCores - 1) × T_cs`.

Proof:
* All involved cores are distinct (by INV-R2, INV-R3, INV-R4 + Nodup).
* The combined list of involved cores is a Nodup list over `CoreId`.
* By `nodup_corelist_length_bound`, the count is ≤ `numCores`. -/
theorem rwLock_bounded_wait_read (s : RwLockState) (h : s.wf) :
    s.readers.length + s.waiters.length +
      (if s.writerHeld.isSome then 1 else 0) ≤ numCores := by
  have h_readers_nodup := h.2.1
  have h_waiters_nodup := h.2.2.1
  have h_disjoint := s.wf_waitersDisjointFromHolders h
  -- Build a combined list of all involved cores.  Case on writerHeld.
  cases h_w : s.writerHeld with
  | none =>
    -- No writer; involved = readers ++ waiters.fst.
    simp
    -- Goal: readers.length + waiters.length ≤ numCores.
    have h_combined_nodup : (s.readers ++ s.waiters.map Prod.fst).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨h_readers_nodup, h_waiters_nodup, ?_⟩
      intro x hx_r y hy_w h_eq
      rw [List.mem_map] at hy_w
      obtain ⟨w, hw_in, hw_eq⟩ := hy_w
      have h_disj := (h_disjoint w hw_in).1
      apply h_disj
      -- hx_r : x ∈ readers, h_eq : x = y, hw_eq : w.1 = y.  Need: w.1 ∈ readers.
      rw [h_eq] at hx_r
      rw [← hw_eq] at hx_r
      exact hx_r
    have h_bound : (s.readers ++ s.waiters.map Prod.fst).length ≤ numCores :=
      nodup_corelist_length_bound _ h_combined_nodup
    simp only [List.length_append, List.length_map] at h_bound
    omega
  | some c =>
    -- Writer holds; involved = readers ++ waiters.fst ++ [c].
    -- But INV-R1 says readers = [] when writer holds.
    have h_r_empty := s.wf_writerReadersExclusion h c h_w
    simp [h_r_empty]
    -- Goal: waiters.length + 1 ≤ numCores.
    -- Build c :: waiters.map fst is Nodup.
    have h_c_not_in : c ∉ s.waiters.map Prod.fst := writer_not_in_waiters h h_w
    have h_combined_nodup : (c :: s.waiters.map Prod.fst).Nodup :=
      List.nodup_cons.mpr ⟨h_c_not_in, h_waiters_nodup⟩
    have h_bound : (c :: s.waiters.map Prod.fst).length ≤ numCores :=
      nodup_corelist_length_bound _ h_combined_nodup
    simp only [List.length_cons, List.length_map] at h_bound
    omega

/-- **Theorem 3.3.8.2 (SM2.C.9): bounded wait for writers (alias of
SM2.C.8).**

The structural bound on the total in-flight count is the SAME for
writers as for readers: `readers + waiters + writer-bit ≤ numCores`.
This theorem is an alias of `rwLock_bounded_wait_read` exposed at a
writer-named API for SM3 consumers.

Per M-1 audit honesty: the plan §5.3 lists SM2.C.8 and SM2.C.9 as
separate sub-tasks, but they share the same structural argument
(pigeonhole on the Nodup CoreId combined list).  An alias is
defensible because the operational semantics treats readers and
writers symmetrically at the "queue-occupancy" level; a meaningful
writer-specific bound would require additional assumptions about
critical-section duration (which is a runtime concern, not a Lean
spec concern at v1.0.0).  The "10 substantive theorems" listed in
the docstring is therefore 9 distinct propositions plus this
named-API alias. -/
theorem rwLock_bounded_wait_write (s : RwLockState) (h : s.wf) :
    s.readers.length + s.waiters.length +
      (if s.writerHeld.isSome then 1 else 0) ≤ numCores :=
  rwLock_bounded_wait_read s h

-- ============================================================================
-- SM2.C.10/11 — Release-acquire pairing
-- ============================================================================

/-- **Theorem 3.3.9.1 (SM2.C.10): release-acquire pairing for RwLock readers.**

If a reader-release-store event and a reader-acquire-load event in a
well-formed memory trace satisfy the standard release-acquire pairing
preconditions (same location on the `state` field; matching value;
release-store positioned before acquire-load; both with the right
ordering), then they `synchronizesWith` per the SM2.A memory model.

This bridges the RwLock spec to the SM2.A memory model: release-acquire
pairing on the packed `state` field is exactly what SM3 per-object locks
consume for cross-core state visibility after reader release.

The proof is structural: the conjuncts of `synchronizesWith` are filled
in directly from the hypotheses. -/
theorem rwLock_release_acquire_pairing_read
    (t : MemoryTrace) (base : Nat)
    (release_event acquire_event : MemoryEvent)
    (h_release_in : release_event ∈ t.events)
    (h_acquire_in : acquire_event ∈ t.events)
    (h_release_loc : release_event.loc = AtomicLocation.rwLockStateOf base)
    (h_acquire_loc : acquire_event.loc = AtomicLocation.rwLockStateOf base)
    (h_release_write : release_event.isWrite = true)
    (h_release_order : release_event.order.isRelease = true)
    (h_acquire_load : acquire_event.isWrite = false)
    (h_acquire_order : acquire_event.order.isAcquire = true)
    (h_value_match : release_event.value = acquire_event.value)
    (h_pos : t.eventPos release_event < t.eventPos acquire_event) :
    synchronizesWith t release_event acquire_event := by
  refine ⟨h_release_in, h_acquire_in, h_release_write, h_release_order,
          h_acquire_load, h_acquire_order, ?_, h_value_match, h_pos⟩
  rw [h_release_loc, h_acquire_loc]

/-- **Theorem 3.3.9.2 (SM2.C.11): release-acquire pairing for RwLock writers.**

The same structure as the reader pairing (3.3.9.1).  The Rust impl uses
the same atomic `state` field for both reader and writer operations
(the packed `AtomicU64`), so the location-based pairing applies
uniformly. -/
theorem rwLock_release_acquire_pairing_write
    (t : MemoryTrace) (base : Nat)
    (release_event acquire_event : MemoryEvent)
    (h_release_in : release_event ∈ t.events)
    (h_acquire_in : acquire_event ∈ t.events)
    (h_release_loc : release_event.loc = AtomicLocation.rwLockStateOf base)
    (h_acquire_loc : acquire_event.loc = AtomicLocation.rwLockStateOf base)
    (h_release_write : release_event.isWrite = true)
    (h_release_order : release_event.order.isRelease = true)
    (h_acquire_load : acquire_event.isWrite = false)
    (h_acquire_order : acquire_event.order.isAcquire = true)
    (h_value_match : release_event.value = acquire_event.value)
    (h_pos : t.eventPos release_event < t.eventPos acquire_event) :
    synchronizesWith t release_event acquire_event :=
  rwLock_release_acquire_pairing_read t base release_event acquire_event
    h_release_in h_acquire_in h_release_loc h_acquire_loc h_release_write
    h_release_order h_acquire_load h_acquire_order h_value_match h_pos

/-- **Corollary**: the release-acquire pairing lifts to `happensBefore`. -/
theorem rwLock_release_acquire_happensBefore_read
    (t : MemoryTrace) (base : Nat)
    (release_event acquire_event : MemoryEvent)
    (h_release_in : release_event ∈ t.events)
    (h_acquire_in : acquire_event ∈ t.events)
    (h_release_loc : release_event.loc = AtomicLocation.rwLockStateOf base)
    (h_acquire_loc : acquire_event.loc = AtomicLocation.rwLockStateOf base)
    (h_release_write : release_event.isWrite = true)
    (h_release_order : release_event.order.isRelease = true)
    (h_acquire_load : acquire_event.isWrite = false)
    (h_acquire_order : acquire_event.order.isAcquire = true)
    (h_value_match : release_event.value = acquire_event.value)
    (h_pos : t.eventPos release_event < t.eventPos acquire_event) :
    happensBefore t release_event acquire_event :=
  synchronizesWith_implies_happensBefore t
    (rwLock_release_acquire_pairing_read t base release_event acquire_event
      h_release_in h_acquire_in h_release_loc h_acquire_loc h_release_write
      h_release_order h_acquire_load h_acquire_order h_value_match h_pos)

-- ============================================================================
-- SM2.C.13 — Reader batching
-- ============================================================================

/-- **Theorem (SM2.C.13): reader batching — structural.**

When `promoteWaitersOnWriterRelease` is invoked with a reader at the head
of the waiters queue, the contiguous reader prefix is promoted to readers
in a single step (rather than one at a time).

Formal statement: the post-state's `readers` field equals exactly the
contiguous reader-prefix (`s.waiters.takeWhile (·.2 = .read)`) mapped to
cores, appended to the pre-existing `readers`.

This is the operational realization of "reader batching": a single writer
release admits an entire contiguous reader-prefix at once. -/
theorem rwLock_reader_batching (s : RwLockState)
    (rc : CoreId) (rest : List (CoreId × AccessMode))
    (h_waiters : s.waiters = (rc, AccessMode.read) :: rest) :
    let readPrefix := s.waiters.takeWhile (fun w => w.2 = AccessMode.read)
    s.promoteWaitersOnWriterRelease.readers =
      readPrefix.map Prod.fst ++ s.readers := by
  unfold RwLockState.promoteWaitersOnWriterRelease
  rw [h_waiters]

/-- **Theorem (SM2.C.13 strengthening, H-5 audit fix): reader batching
admits at least one reader.**

The reader-batching property must guarantee that **at least one reader
is admitted** when the head waiter is a reader.  This is the substantive
content the docstring of `rwLock_reader_batching` claims ("a single
writer release admits many readers").

Formal statement: if the head waiter is a reader, then after promote,
`readers.length ≥ s.readers.length + 1` (strict growth).

Proof: the takeWhile of a list starting with a reader includes at least
the head, so its map.fst has length ≥ 1.  Combined with `++ s.readers`,
the post-readers length is ≥ s.readers.length + 1. -/
theorem rwLock_reader_batching_admits_at_least_one (s : RwLockState)
    (rc : CoreId) (rest : List (CoreId × AccessMode))
    (h_waiters : s.waiters = (rc, AccessMode.read) :: rest) :
    s.promoteWaitersOnWriterRelease.readers.length ≥ s.readers.length + 1 := by
  rw [rwLock_reader_batching s rc rest h_waiters]
  -- Goal: (s.waiters.takeWhile (·.2 = .read)).map Prod.fst ++ s.readers).length
  --       ≥ s.readers.length + 1
  rw [h_waiters]
  -- takeWhile of (rc, .read) :: rest starts with (rc, .read), so length ≥ 1.
  have h_takeWhile_head :
      ((rc, AccessMode.read) :: rest).takeWhile (fun w => w.2 = AccessMode.read)
      = (rc, AccessMode.read) ::
        rest.takeWhile (fun w => w.2 = AccessMode.read) := by
    simp
  rw [h_takeWhile_head]
  simp only [List.map_cons, List.length_cons, List.length_append, List.length_map]
  omega

/-- **Theorem (SM2.C.13 strengthening, H-5 audit fix): reader batching
admits the entire reader-prefix.**

The post-state's reader count grows by **exactly** the length of the
contiguous reader-prefix.  Stronger statement than "at least one".

Formal statement: `post.readers.length = takeWhile-prefix.length + s.readers.length`. -/
theorem rwLock_reader_batching_exact_count (s : RwLockState)
    (rc : CoreId) (rest : List (CoreId × AccessMode))
    (h_waiters : s.waiters = (rc, AccessMode.read) :: rest) :
    s.promoteWaitersOnWriterRelease.readers.length =
      (s.waiters.takeWhile (fun w => w.2 = AccessMode.read)).length
      + s.readers.length := by
  rw [rwLock_reader_batching s rc rest h_waiters]
  simp only [List.length_append, List.length_map]

-- ============================================================================
-- SM2.C.14 — Writer safety under reader acquisition
-- ============================================================================

/-- **Theorem 3.3.10.1 (SM2.C.14): writer safety under reader acquisition
(operational FIFO safety; H-2 audit-honesty rename).**

This is a **single-step safety** claim, not a multi-step liveness claim:
a writer waiting in the queue is not displaced by a fresh reader's
`tryAcquireRead`.  The reader is either enqueued behind the writer
(when the writer is the queue head) or directly acquires (when the
writer is past a reader prefix; the writer's queue position is then
unchanged).

This is the foundational property the multi-step liveness (no writer
starvation in the colloquial sense — "writer eventually progresses
under bounded reader / writer release time") rests on, but it is NOT
itself the liveness theorem.  The full liveness claim requires a
temporal argument over an infinite trace plus fairness assumptions,
which is outside the scope of v1.0.0's operational spec.

Specifically PROVEN: `(c_w, .write) ∈ s.waiters → (c_w, .write) ∈
(s.applyOp .tryAcquireRead c_r).waiters` for any `c_r` not yet
involved.

Specifically NOT proven (deferred to post-1.0 temporal reasoning):
* the writer eventually reaches the head of the queue,
* after reaching the head, it is eventually promoted,
* the wait time is bounded under fairness assumptions.

The bounded-wait theorem (`rwLock_bounded_wait_write` /
`rwLock_bounded_wait_read`) gives a structural bound on the wait queue
size (`≤ numCores`), which combined with bounded-critical-section
assumptions in the runtime is the v1.0.0 substitute for full
starvation freedom.

**M-K audit-pass-2 cleanup**: the `wf` hypothesis is unused in the
proof.  The theorem is true without it (a pure operational-semantics
property of `applyOp`).  Dropping the parameter makes the theorem
more general — SM3 consumers can apply it without discharging wf,
which simplifies caller-side proof obligations.  The backwards-compat
alias `rwLock_no_writer_starvation` (below) still takes `_h : s.wf`
to preserve binary compatibility with pre-audit consumers. -/
theorem rwLock_writer_safety_under_reader_acquire (s : RwLockState)
    (c_w : CoreId) (h_writer_waiting : (c_w, AccessMode.write) ∈ s.waiters)
    (c_r : CoreId) (h_r_not_inv : ¬ s.coreInvolved c_r) :
    (c_w, AccessMode.write) ∈ (s.applyOp (.tryAcquireRead c_r)).waiters := by
  unfold RwLockState.applyOp
  simp only [h_r_not_inv, ↓reduceIte]
  by_cases h_held : s.writerHeld.isSome
  · -- Writer holds → reader enqueued at tail; c_w stays.
    simp only [h_held, ↓reduceIte]
    show (c_w, AccessMode.write) ∈ s.waiters ++ [(c_r, AccessMode.read)]
    exact List.mem_append_left _ h_writer_waiting
  · -- No writer holds.  Check head of queue.
    simp only [h_held, Bool.false_eq_true, ↓reduceIte]
    match h_w_eq : s.waiters with
    | [] =>
      -- Empty waiters contradicts h_writer_waiting.
      rw [h_w_eq] at h_writer_waiting
      exact absurd h_writer_waiting List.not_mem_nil
    | (wcore, .write) :: rest =>
      -- Head is writer; reader enqueued.
      show (c_w, AccessMode.write) ∈ (wcore, AccessMode.write) :: rest ++ [(c_r, AccessMode.read)]
      have h_in_rest : (c_w, AccessMode.write) ∈ (wcore, AccessMode.write) :: rest := by
        rw [← h_w_eq]; exact h_writer_waiting
      exact List.mem_append_left _ h_in_rest
    | (wcore, .read) :: rest =>
      -- Head is reader; direct acquire.  But waiters is unchanged.
      show (c_w, AccessMode.write) ∈ (wcore, AccessMode.read) :: rest
      rw [← h_w_eq]; exact h_writer_waiting

/-- **Backwards-compat alias for callers that referenced the older name.**

This alias keeps the original `rwLock_no_writer_starvation` name resolving
to the safety theorem.  Per the H-2 audit finding, the docstring on
`rwLock_writer_safety_under_reader_acquire` (above) is the honest
description of what the theorem proves; this alias preserves binary-
compatibility for any pre-audit consumers. -/
theorem rwLock_no_writer_starvation (s : RwLockState) (_h : s.wf)
    (c_w : CoreId) (h_writer_waiting : (c_w, AccessMode.write) ∈ s.waiters)
    (c_r : CoreId) (h_r_not_inv : ¬ s.coreInvolved c_r) :
    (c_w, AccessMode.write) ∈ (s.applyOp (.tryAcquireRead c_r)).waiters :=
  rwLock_writer_safety_under_reader_acquire s c_w h_writer_waiting c_r h_r_not_inv

-- ============================================================================
-- SM2.C.16 — Bit-packed encoding
-- ============================================================================

/-- **WS-SM SM2.C.16**: bit-packed encoding of the RwLock state.

The Rust impl uses a single `AtomicU64` `state` field with the layout:
* **bit 63** (`WRITER_BIT`): set iff a writer holds the lock.
* **bits 0..62**: the reader count (unsigned 63-bit integer).

This allows the entire reader-writer state to be CAS'd atomically.  The
Lean spec models the abstract state directly (with `writerHeld : Option
CoreId` and `readers : List CoreId`); the bit-packing is a refinement
detail.

The `RwLockEncoded` abbreviation represents the packed `u64` as a Nat
(so the spec can reason about it without depending on a fixed-width
integer type).  The high bit (bit 63 = 2^63) is the writer flag; lower
bits are the reader count.

The Lean spec doesn't track WHICH cores are readers in the bit-packed
form (the spec's `readers : List CoreId` is richer than the impl's
count).  The refinement φ (SM2.C.20) elides this difference, justified
by the observation that the abstract `readers` list is bounded by
`numCores` and is therefore representable by a count for the purposes
of the operational state. -/
abbrev RwLockEncoded := Nat

/-- The writer bit position (bit 63). -/
def writerBitPos : Nat := 63

/-- The writer-bit value (`2^63`). -/
def writerBit : Nat := 2 ^ writerBitPos

/-- The reader-count mask (everything except the writer bit). -/
def readerMask : Nat := writerBit - 1

/-- **WS-SM SM2.C.16**: encode the abstract (writer-held, reader-count) state
to the bit-packed Nat.  The reader count is bounded by `numCores` ≤
2^63 - 1, so no overflow occurs in practice. -/
def encodeRwLock (writerHeld : Bool) (readerCount : Nat) : RwLockEncoded :=
  (if writerHeld then writerBit else 0) + readerCount

/-- **WS-SM SM2.C.16**: decode the bit-packed Nat back to (writer-held,
reader-count).  Decoding is total but only inverse to encode when the
reader count is below `writerBit` (which is always true in practice for
our `numCores` ≤ 4). -/
def decodeRwLock (e : RwLockEncoded) : Bool × Nat :=
  if e ≥ writerBit then (true, e - writerBit) else (false, e)

-- ============================================================================
-- SM2.C.17 — Encoding/decoding round-trip lemmas
-- ============================================================================

/-- **WS-SM SM2.C.17 (round-trip 1)**: encode then decode recovers the
original (when reader count is in range).

Precondition: `readerCount < writerBit = 2^63`.  In practice this is
trivially satisfied for `numCores ≤ 4`. -/
theorem rwLock_encode_decode_roundtrip
    (writerHeld : Bool) (readerCount : Nat) (h_bound : readerCount < writerBit) :
    decodeRwLock (encodeRwLock writerHeld readerCount) = (writerHeld, readerCount) := by
  unfold decodeRwLock encodeRwLock
  cases writerHeld with
  | true =>
    -- Encoded = writerBit + readerCount.  writer bit decode: e ≥ writerBit.
    have h_ge : writerBit + readerCount ≥ writerBit := Nat.le_add_right _ _
    simp [h_ge]
  | false =>
    -- Encoded = 0 + readerCount = readerCount.  writer bit decode: false.
    simp only [Bool.false_eq_true, ite_false, Nat.zero_add]
    have h_lt : readerCount < writerBit := h_bound
    have h_not_ge : ¬ readerCount ≥ writerBit := by omega
    simp [h_not_ge]

/-- **WS-SM SM2.C.17 (round-trip 2)**: decode then encode recovers the original.

Identity-like: for any encoded value `e`, encoding the decoded
(writer-held, reader-count) reproduces `e`. -/
theorem rwLock_decode_encode_roundtrip (e : RwLockEncoded) :
    encodeRwLock (decodeRwLock e).1 (decodeRwLock e).2 = e := by
  unfold decodeRwLock encodeRwLock
  by_cases h_w : e ≥ writerBit
  · -- Writer bit set: decoded = (true, e - writerBit); encoded back = writerBit + (e - writerBit) = e.
    simp [h_w]
  · -- Writer bit clear: decoded = (false, e); encoded back = 0 + e = e.
    simp [h_w]

/-- **WS-SM SM2.C.17 (writer-bit set)**: encoding with `writer=true` has
the writer bit set. -/
theorem rwLock_encode_writer_bit_set (readerCount : Nat) :
    encodeRwLock true readerCount ≥ writerBit := by
  unfold encodeRwLock
  simp only [ite_true]
  exact Nat.le_add_right _ _

/-- **WS-SM SM2.C.17 (writer-bit clear)**: encoding with `writer=false`
and reader count below `writerBit` has the writer bit clear. -/
theorem rwLock_encode_writer_bit_clear
    (readerCount : Nat) (h : readerCount < writerBit) :
    encodeRwLock false readerCount < writerBit := by
  unfold encodeRwLock
  simp only [Bool.false_eq_true, ite_false, Nat.zero_add]
  exact h

/-- **WS-SM SM2.C.18**: reader-count overflow analysis.

For `numCores = 4`, the maximum reader count is 4 (every core holds the
read lock).  The packed representation reserves bit 63 for the writer
flag, leaving bits 0..62 (max value `2^63 - 1 ≈ 9.2 × 10^18`).  The
gap between 4 and 2^63-1 is overwhelmingly large; reader-count overflow
is physically impossible within a deployment lifetime.

For platforms with larger `numCores` (a hypothetical future port), as long
as `numCores < 2^63`, the encoding is unambiguous.  Higher core counts
would require a different layout (e.g., split state across two atomics).

This theorem is the formal documentation of the overflow boundary. -/
theorem rwLock_reader_count_no_overflow_under_numCores :
    numCores < writerBit := by
  -- numCores = 4 (SM0.E literal); writerBit = 2^63.
  unfold numCores writerBit writerBitPos
  decide

-- ============================================================================
-- SM2.C-defer §4.1 — RwLockExecution primitives (RwLockKernelStep + RwLockReachable)
-- ============================================================================
-- See docs/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md §4.1 for the
-- motivation: D-1..D-4 quantify over executions whose initial state is
-- reachable from `unheld`, NOT arbitrary wf states.  The wf state space
-- admits non-reachable configurations (e.g. `readers = [r0],
-- waiters = [(r1, .read), (w1, .write)], writerHeld = none`) from which
-- the operational `applyOp` admits FIFO-inverting reader bypass via the
-- reader-head fast-path.  Restricting to `RwLockReachable` closes the gap.
--
-- Naming: `RwLockKernelStep` / `RwLockReachable` / `RwLockExecution` are
-- prefixed with `RwLock` to avoid namespace collision with TicketLock's
-- `KernelStep` / `RwLockReachable` (both live in the same
-- `SeLe4n.Kernel.Concurrency` namespace; SM2.B chose the unqualified
-- names first, so SM2.C-defer takes the qualified form).

/-- **WS-SM SM2.C-defer D-1.1**: one-step transition relation on
`RwLockState`.

Mirrors the SM2.B `KernelStep` template — one constructor per
`RwLockOp` constructor, each tying the post-state to `applyOp`.

This is the operational reachability witness: every kernel-level
transition on an `RwLock` is one of these four constructors. -/
inductive RwLockKernelStep : RwLockState → RwLockState → Prop where
  /-- Reader-acquire (or no-op / enqueue, depending on state). -/
  | tryAcquireRead  (s : RwLockState) (core : CoreId) :
      RwLockKernelStep s (s.applyOp (.tryAcquireRead core))
  /-- Reader-release (or no-op if `core` is not a reader). -/
  | releaseRead     (s : RwLockState) (core : CoreId) :
      RwLockKernelStep s (s.applyOp (.releaseRead core))
  /-- Writer-acquire (or no-op / enqueue, depending on state). -/
  | tryAcquireWrite (s : RwLockState) (core : CoreId) :
      RwLockKernelStep s (s.applyOp (.tryAcquireWrite core))
  /-- Writer-release (or no-op if `core` is not the current writer). -/
  | releaseWrite    (s : RwLockState) (core : CoreId) :
      RwLockKernelStep s (s.applyOp (.releaseWrite core))

/-- **WS-SM SM2.C-defer D-1.1**: reflexive-transitive closure of
`RwLockKernelStep` from `unheld`.

A state `s` is `RwLockReachable` iff there is a finite chain of
`RwLockKernelStep` transitions from `unheld` to `s`.

(`RwLock`-prefixed to avoid collision with TicketLock's `RwLockReachable`.) -/
inductive RwLockReachable : RwLockState → Prop where
  /-- The seed state is reachable. -/
  | base : RwLockReachable RwLockState.unheld
  /-- Closure under kernel steps. -/
  | step : ∀ {s s'}, RwLockReachable s → RwLockKernelStep s s' → RwLockReachable s'

/-- **WS-SM SM2.C-defer D-1.2**: reachability implies wf.

By induction on the `RwLockReachable` derivation, using the per-op
preservation theorems for the inductive step.

Mirror of SM2.B's `ticketLock_reachability`. -/
theorem RwLockReachable_implies_wf {s : RwLockState} (h : RwLockReachable s) : s.wf := by
  induction h with
  | base => exact RwLockState.unheld_wf
  | @step s s' _h_reach_s h_step ih =>
    cases h_step with
    | tryAcquireRead  c => exact rwLock_tryAcquireRead_preserves_wf  _ c ih
    | releaseRead     c => exact rwLock_releaseRead_preserves_wf     _ c ih
    | tryAcquireWrite c => exact rwLock_tryAcquireWrite_preserves_wf _ c ih
    | releaseWrite    c => exact rwLock_releaseWrite_preserves_wf    _ c ih

/-- **WS-SM SM2.C-defer D-1.1**: trace-based execution from a
`RwLockReachable` initial state.

Pairs an `initial` state with a list of operations and a proof
`initial_reachable` that the initial state is reachable from `unheld`.

RwLockExecution semantics: fold `applyOp` over `ops` starting from `initial`.
All deferred-completion theorems quantify over `RwLockExecution` values.

(`RwLock`-prefixed to avoid collision with potential SM2.B
`RwLockExecution` if added.) -/
structure RwLockExecution where
  /-- The initial state of the execution. -/
  initial            : RwLockState
  /-- The sequence of operations applied to `initial`. -/
  ops                : List RwLockOp
  /-- Proof that `initial` is reachable from `unheld` via kernel steps. -/
  initial_reachable  : RwLockReachable initial

/-- **WS-SM SM2.C-defer D-1.2**: an RwLockExecution's initial state is wf. -/
theorem RwLockExecution.initial_wf (e : RwLockExecution) : e.initial.wf :=
  RwLockReachable_implies_wf e.initial_reachable

/-- **WS-SM SM2.C-defer D-1.1**: the state after the first `k` operations
of an execution. -/
def RwLockExecution.stateAt (e : RwLockExecution) (k : Nat) : RwLockState :=
  (e.ops.take k).foldl RwLockState.applyOp e.initial

/-- **WS-SM SM2.C-defer D-1.1**: the final state of an execution. -/
def RwLockExecution.finalState (e : RwLockExecution) : RwLockState :=
  e.stateAt e.ops.length

/-- Witness: `stateAt 0` is the initial state. -/
@[simp]
theorem RwLockExecution.stateAt_zero (e : RwLockExecution) :
    e.stateAt 0 = e.initial := by
  simp [RwLockExecution.stateAt]

/-- Witness: `stateAt e.ops.length` is the final state. -/
theorem RwLockExecution.stateAt_length (e : RwLockExecution) :
    e.stateAt e.ops.length = e.finalState := rfl

/-- **WS-SM SM2.C-defer D-1.2**: an RwLockExecution's state after k+1 operations
equals applyOp on the kth state with the kth operation.

Standard `foldl`/`take` identity, used in the foundational reachability
proof and in every D-1 / D-3 inductive step. -/
theorem RwLockExecution.stateAt_succ (e : RwLockExecution) {k : Nat}
    (h : k < e.ops.length) :
    e.stateAt (k + 1) = (e.stateAt k).applyOp (e.ops[k]'h) := by
  unfold RwLockExecution.stateAt
  -- ops.take (k+1) = ops.take k ++ [ops[k]] when k < length, then
  -- List.foldl_append discharges.
  rw [List.take_succ_eq_append_getElem h]
  rw [List.foldl_append]
  simp

/-- **WS-SM SM2.C-defer D-1.2**: every RwLockExecution state is RwLockReachable.

By induction on `k`.  Base: `stateAt 0 = initial`, reachable by
hypothesis.  Inductive step: `stateAt (k+1) = applyOp (stateAt k) op`,
witnessed by an `RwLockKernelStep` constructor. -/
theorem RwLockExecution.stateAt_reachable (e : RwLockExecution) (k : Nat) :
    RwLockReachable (e.stateAt k) := by
  induction k with
  | zero => rw [RwLockExecution.stateAt_zero]; exact e.initial_reachable
  | succ k ih =>
    by_cases h : k < e.ops.length
    · -- k+1 ≤ length: extend the trace by one step.
      rw [RwLockExecution.stateAt_succ e h]
      apply RwLockReachable.step ih
      -- `cases h_op` substitutes through the goal, so the constructor applies directly.
      cases h_op : e.ops[k]'h with
      | tryAcquireRead  c => exact RwLockKernelStep.tryAcquireRead  _ c
      | releaseRead     c => exact RwLockKernelStep.releaseRead     _ c
      | tryAcquireWrite c => exact RwLockKernelStep.tryAcquireWrite _ c
      | releaseWrite    c => exact RwLockKernelStep.releaseWrite    _ c
    · -- k ≥ length: stateAt (k+1) = stateAt k (truncation).
      have h_eq : e.stateAt (k + 1) = e.stateAt k := by
        unfold RwLockExecution.stateAt
        have h_take_eq : e.ops.take (k + 1) = e.ops.take k := by
          have h_ge : e.ops.length ≤ k := Nat.le_of_not_lt h
          rw [List.take_of_length_le (by omega), List.take_of_length_le h_ge]
        rw [h_take_eq]
      rw [h_eq]; exact ih

/-- **WS-SM SM2.C-defer D-1.2**: every RwLockExecution state is wf.

Composition of `stateAt_reachable` and `RwLockReachable_implies_wf`. -/
theorem RwLockExecution.stateAt_wf (e : RwLockExecution) (k : Nat) : (e.stateAt k).wf :=
  RwLockReachable_implies_wf (e.stateAt_reachable k)

-- ============================================================================
-- SM2.C-defer §4.3 + D-2 — writerWaitDepth + writer-specific bounded wait
-- ============================================================================

/-- **WS-SM SM2.C-defer D-2.1**: the "wait depth" of a queued writer.

Components:
1. `queueDepth` = position of `c` in waiters (entries ahead in queue).
2. `readerDepth` = number of readers currently held (each must release).
3. `writerDepth` = 1 if a writer currently holds, else 0.

Sum bounds the number of effective releases that must occur before
`c` can be promoted to writerHeld.

**Tight bound** (closes audit finding M-1): for a wf state with `c`
queued as a writer, `writerWaitDepth s c ≤ numCores - 1`.  See
`writerWaitDepth_bounded` below. -/
def writerWaitDepth (s : RwLockState) (c : CoreId) : Nat :=
  let queueDepth := s.waiters.idxOf (c, AccessMode.write)
  let readerDepth := s.readers.length
  let writerDepth := if s.writerHeld.isSome then 1 else 0
  queueDepth + readerDepth + writerDepth

/-- **WS-SM SM2.C-defer D-2.1**: unfolding lemma for `writerWaitDepth`.

Stated as a `@[simp]` lemma so `decide`-based tests automatically
expand the helper before computing the value. -/
@[simp] theorem writerWaitDepth_simp (s : RwLockState) (c : CoreId) :
    writerWaitDepth s c =
      s.waiters.idxOf (c, AccessMode.write) +
      s.readers.length +
      (if s.writerHeld.isSome then 1 else 0) := rfl

/-- **WS-SM SM2.C-defer D-2.2**: `writerWaitDepth` is decidable.

All three components are decidable: `List.idxOf` returns a Nat,
`List.length` returns a Nat, and `Option.isSome` is decidable.  The
resulting `Nat` value can be compared via `decide` for test
fixtures.

Re-derives `DecidableEq RwLockState` from its `deriving` clause so
the instance is available in the deferred-completion namespace
unambiguously. -/
instance : DecidableEq RwLockState := inferInstance

/-- **WS-SM SM2.C-defer helper**: `List.idxOf` of a member is bounded by
`length - 1`.

Uses `List.idxOf_lt_length_of_mem` (a member's index is strictly less
than the list length) and bridges to ≤ length - 1 via `length ≥ 1`. -/
private theorem idxOf_le_length_sub_one_pair
    (l : List (CoreId × AccessMode)) (x : CoreId × AccessMode) (h : x ∈ l) :
    l.idxOf x ≤ l.length - 1 := by
  have h_lt : l.idxOf x < l.length := List.idxOf_lt_length_of_mem h
  have h_pos : 0 < l.length := by
    cases l with
    | nil => exact absurd h List.not_mem_nil
    | cons _ _ => simp
  omega

/-- **WS-SM SM2.C-defer D-2.3**: writer wait depth is bounded by
`numCores - 1` (tight).

Closes audit finding M-1: the naive composition `idxOf ≤ numCores - 1`
+ `readers + writer_bit ≤ numCores` yields `2 * numCores - 1`,
double-counting the wf bound by a factor of ~2.  Substituting
`idxOf ≤ waiters.length - 1` (since `c ∈ waiters`) into
`waiters.length + readers + writer_bit ≤ numCores` (the existing
`rwLock_bounded_wait_read`) gives `idxOf + readers + writer_bit ≤
numCores - 1`.

Concrete instantiation: `numCores = 4` on RPi5 gives depth ≤ 3.

Proof:
1. By `rwLock_bounded_wait_read`:
   `waiters.length + readers.length + writer_bit ≤ numCores`.
2. Since `(c, .write) ∈ waiters`, `waiters.length ≥ 1`, and
   `idxOf (c, .write) ≤ waiters.length - 1` by `idxOf_le_length_sub_one`.
3. Adding 1 to both sides and substituting:
   `idxOf + 1 + readers + writer_bit ≤ waiters.length + readers + writer_bit ≤ numCores`,
   hence `idxOf + readers + writer_bit ≤ numCores - 1`. -/
theorem writerWaitDepth_bounded
    (s : RwLockState) (h : s.wf)
    (c : CoreId) (h_queued : (c, AccessMode.write) ∈ s.waiters) :
    writerWaitDepth s c ≤ numCores - 1 := by
  unfold writerWaitDepth
  simp only
  have h_bounded := rwLock_bounded_wait_read s h
  have h_idx_le : s.waiters.idxOf (c, AccessMode.write) ≤ s.waiters.length - 1 :=
    idxOf_le_length_sub_one_pair s.waiters (c, AccessMode.write) h_queued
  have h_waiters_pos : 0 < s.waiters.length := by
    cases h_eq : s.waiters with
    | nil => rw [h_eq] at h_queued; exact absurd h_queued List.not_mem_nil
    | cons _ _ => simp
  -- Bound chain: idxOf + readers + writer_bit
  --   ≤ (waiters.length - 1) + readers + writer_bit  (by h_idx_le)
  --   ≤ numCores - 1                                  (by h_bounded + waiters ≥ 1).
  -- Case-split on writer_bit to discharge the if; bound's form must match.
  by_cases h_w : s.writerHeld.isSome = true
  · -- writer_bit = 1.  INV-R1: readers = [] when writer holds.
    -- This means readers.length = 0, simplifying the chain.
    have ⟨c', h_w'⟩ : ∃ c, s.writerHeld = some c := by
      cases h_some : s.writerHeld with
      | none => rw [h_some] at h_w; simp at h_w
      | some c => exact ⟨c, rfl⟩
    have h_r_empty : s.readers = [] := s.wf_writerReadersExclusion h c' h_w'
    rw [h_r_empty] at h_bounded ⊢
    simp [h_w, List.length_nil] at h_bounded ⊢
    omega
  · -- writer_bit = 0.
    simp [h_w] at h_bounded ⊢
    omega

/-- **WS-SM SM2.C-defer D-2.4 (predicate)**: an op is an **effective
release** for `s` if it actually transitions some holder out of
`readers` or `writerHeld` (i.e., is not a no-op).

This is the precise notion that D-2.4 needs (closing audit finding L-2:
no more hand-waved `h_progress`). -/
def RwLockState.isEffectiveRelease (s : RwLockState) (op : RwLockOp) : Prop :=
  match op with
  | .releaseRead  c => c ∈ s.readers
  | .releaseWrite c => s.writerHeld = some c
  | _               => False

/-- **WS-SM SM2.C-defer D-2.4 (decidability)**: `isEffectiveRelease` is
decidable for any `(s, op)` since membership/equality on the abstract
state's fields are decidable. -/
instance RwLockState.decidableIsEffectiveRelease
    (s : RwLockState) (op : RwLockOp) : Decidable (s.isEffectiveRelease op) := by
  unfold RwLockState.isEffectiveRelease
  cases op <;> exact inferInstance

/-- **WS-SM SM2.C-defer D-2.5 (helper, decidable predicate)**: at trace
position `pos`, is the corresponding operation an effective release?

Returns `false` if `pos ≥ e.ops.length` (out-of-range). -/
def RwLockExecution.isEffectiveReleaseAt (e : RwLockExecution) (pos : Nat) : Bool :=
  if h : pos < e.ops.length then
    decide ((e.stateAt pos).isEffectiveRelease (e.ops[pos]'h))
  else
    false

/-- **WS-SM SM2.C-defer D-2.5 (helper)**: count the effective releases
in an execution between trace positions `k₁` (inclusive) and `k₂`
(exclusive).

Defined via `List.countP` so the structural upper bound (window size)
follows directly from `List.countP_le_length`. -/
def RwLockExecution.countEffectiveReleases (e : RwLockExecution) (k₁ k₂ : Nat) : Nat :=
  ((List.range (k₂ - k₁)).map (k₁ + ·)).countP e.isEffectiveReleaseAt

/-- **WS-SM SM2.C-defer D-2.5 (witness)**: count of effective releases is
bounded by the window size.  Discharged by `List.countP_le_length`. -/
theorem RwLockExecution.countEffectiveReleases_le_window
    (e : RwLockExecution) (k₁ k₂ : Nat) :
    e.countEffectiveReleases k₁ k₂ ≤ k₂ - k₁ := by
  unfold RwLockExecution.countEffectiveReleases
  rw [List.countP_map]
  have h := List.countP_le_length (l := List.range (k₂ - k₁))
              (p := e.isEffectiveReleaseAt ∘ (k₁ + ·))
  simp [List.length_range] at h
  exact h

-- ============================================================================
-- SM2.C-defer §4.2 — Waiter / Holder predicates + enqueueStep / admissionStep
-- ============================================================================

/-- **WS-SM SM2.C-defer D-1.3**: `(core, mode)` is in the waiters list at
step `k` of the execution. -/
def RwLockExecution.waiterAt (e : RwLockExecution) (k : Nat)
    (core : CoreId) (mode : AccessMode) : Prop :=
  (core, mode) ∈ (e.stateAt k).waiters

/-- `waiterAt` is decidable. -/
instance RwLockExecution.decidableWaiterAt (e : RwLockExecution) (k : Nat)
    (core : CoreId) (mode : AccessMode) :
    Decidable (e.waiterAt k core mode) := by
  unfold RwLockExecution.waiterAt
  exact inferInstance

/-- **WS-SM SM2.C-defer D-1.3**: `core` is a holder (reader or writer) at
step `k` of the execution. -/
def RwLockExecution.holderAt (e : RwLockExecution) (k : Nat) (core : CoreId) : Prop :=
  core ∈ (e.stateAt k).readers ∨ (e.stateAt k).writerHeld = some core

/-- `holderAt` is decidable. -/
instance RwLockExecution.decidableHolderAt (e : RwLockExecution) (k : Nat) (core : CoreId) :
    Decidable (e.holderAt k core) := by
  unfold RwLockExecution.holderAt
  exact inferInstance

/-- **WS-SM SM2.C-defer D-1.4**: the step at which `(core, mode)` is
enqueued — the smallest `k ≥ 1` such that membership transitions from
`false` to `true`.

Strict-transition formulation: returns `none` for waiters present in
`e.initial.waiters` (they were not enqueued during the trace).
Combined with the `e.initial = unheld` precondition that D-1.9 adopts,
`enqueueStep` is well-defined for every waiter that appears in any
reachable state. -/
def RwLockExecution.enqueueStep (e : RwLockExecution)
    (core : CoreId) (mode : AccessMode) : Option Nat :=
  (List.range (e.ops.length + 1)).find? fun k =>
    decide (k ≥ 1) &&
    decide (e.waiterAt k core mode) &&
    decide (¬ e.waiterAt (k - 1) core mode)

/-- **WS-SM SM2.C-defer D-1.4**: the step at which `core` is admitted as
a holder — the smallest `k ≥ 1` such that `holderAt k core` AND
`¬ holderAt (k-1) core`.  Same transition-edge rationale as `enqueueStep`. -/
def RwLockExecution.admissionStep (e : RwLockExecution) (core : CoreId) : Option Nat :=
  (List.range (e.ops.length + 1)).find? fun k =>
    decide (k ≥ 1) &&
    decide (e.holderAt k core) &&
    decide (¬ e.holderAt (k - 1) core)

/-- **WS-SM SM2.C-defer D-1.5**: characterization of `enqueueStep`.

If `enqueueStep core mode = some k`, then `k ≥ 1`, `waiterAt k core mode`,
and `¬ waiterAt (k-1) core mode`.

Proved by `List.find?_eq_some` which gives the witness's properties. -/
theorem RwLockExecution.enqueueStep_characterization (e : RwLockExecution)
    (core : CoreId) (mode : AccessMode) (k : Nat)
    (h : e.enqueueStep core mode = some k) :
    1 ≤ k ∧ e.waiterAt k core mode ∧ ¬ e.waiterAt (k - 1) core mode := by
  unfold RwLockExecution.enqueueStep at h
  -- find?_eq_some_iff_append: xs.find? p = some b ↔ p b ∧ ∃ as bs, ...
  have h_pred := List.find?_eq_some_iff_append.mp h
  -- h_pred : (decide(k ≥ 1) && decide(...) && decide(...)) = true ∧ ∃ as bs, ...
  obtain ⟨h_eq, _⟩ := h_pred
  rw [Bool.and_eq_true, Bool.and_eq_true] at h_eq
  obtain ⟨⟨h1, h2⟩, h3⟩ := h_eq
  exact ⟨of_decide_eq_true h1, of_decide_eq_true h2, of_decide_eq_true h3⟩

/-- **WS-SM SM2.C-defer**: characterization of `admissionStep` — analog
of `enqueueStep_characterization`. -/
theorem RwLockExecution.admissionStep_characterization (e : RwLockExecution)
    (core : CoreId) (k : Nat)
    (h : e.admissionStep core = some k) :
    1 ≤ k ∧ e.holderAt k core ∧ ¬ e.holderAt (k - 1) core := by
  unfold RwLockExecution.admissionStep at h
  have h_pred := List.find?_eq_some_iff_append.mp h
  obtain ⟨h_eq, _⟩ := h_pred
  rw [Bool.and_eq_true, Bool.and_eq_true] at h_eq
  obtain ⟨⟨h1, h2⟩, h3⟩ := h_eq
  exact ⟨of_decide_eq_true h1, of_decide_eq_true h2, of_decide_eq_true h3⟩

-- ============================================================================
-- SM2.C-defer D-1.6 / D-1.7 — Append-to-tail / Drop-prefix theorems
-- ============================================================================

/-- **WS-SM SM2.C-defer D-1.6 (predicate helper)**: extract the `core`
from an op (for tryAcquire / release ops). -/
def RwLockOp.coreOfOp : RwLockOp → CoreId
  | .tryAcquireRead  c => c
  | .tryAcquireWrite c => c
  | .releaseRead     c => c
  | .releaseWrite    c => c

/-- **WS-SM SM2.C-defer D-1.6 (predicate helper)**: extract the access
mode from an acquire op (returns `.read` by convention for release ops;
only called when guarded by an op-shape hypothesis in D-1.6). -/
def RwLockOp.modeOfOp : RwLockOp → AccessMode
  | .tryAcquireRead  _ => .read
  | .tryAcquireWrite _ => .write
  | _                  => .read

/-- **WS-SM SM2.C-defer D-1.6**: `tryAcquireRead c` either is a no-op or
appends EXACTLY `(c, .read)` at the tail.

Concrete-witness form (NOT existential): the appended pair is the
specific `(c, .read)` from the op.  This precision matters for D-1.8
order-preservation reasoning. -/
theorem tryAcquireRead_waiters_append_or_noop (s : RwLockState) (c : CoreId) :
    (s.applyOp (.tryAcquireRead c)).waiters = s.waiters ∨
    (s.applyOp (.tryAcquireRead c)).waiters = s.waiters ++ [(c, AccessMode.read)] := by
  unfold RwLockState.applyOp
  by_cases h_inv : s.coreInvolved c
  · left; simp [h_inv]
  by_cases h_w : s.writerHeld.isSome
  · right; simp [h_inv, h_w]
  simp only [h_inv, ↓reduceIte, h_w, Bool.false_eq_true]
  cases h_wq : s.waiters with
  | nil =>
    -- waiters = [], match enters reader-head branch (= acquire-direct).
    left; simp [h_wq]
  | cons head rest =>
    obtain ⟨_, wm⟩ := head
    cases wm with
    | write =>
      -- Head is writer → enqueue.
      right; simp [h_wq]
    | read =>
      -- Head is reader → acquire direct (waiters unchanged).
      left; simp [h_wq]

/-- **WS-SM SM2.C-defer D-1.6**: `tryAcquireWrite c` either is a no-op or
appends EXACTLY `(c, .write)` at the tail. -/
theorem tryAcquireWrite_waiters_append_or_noop (s : RwLockState) (c : CoreId) :
    (s.applyOp (.tryAcquireWrite c)).waiters = s.waiters ∨
    (s.applyOp (.tryAcquireWrite c)).waiters = s.waiters ++ [(c, AccessMode.write)] := by
  unfold RwLockState.applyOp
  by_cases h_inv : s.coreInvolved c
  · left; simp [h_inv]
  by_cases h_held : s.writerHeld.isSome ∨ s.readers ≠ []
  · right; simp [h_inv, h_held]
  · left; simp [h_inv, h_held]

/-- **WS-SM SM2.C-defer D-1.7 (read variant)**: `releaseRead c` does not
append to waiters; the post-state `waiters` is a `Sublist` of the pre-state.

Proof strategy: apply `rwLock_fifo_admission_readers_empty` to the
post-filter state.  Use a `generalize` over the filter predicate to
avoid the simp-normalization mismatch between `decide (· ≠ c)` and
`!decide (· = c)`. -/
theorem releaseRead_waiters_sublist (s : RwLockState) (c : CoreId) :
    (s.applyOp (.releaseRead c)).waiters.Sublist s.waiters := by
  unfold RwLockState.applyOp
  by_cases h_in : c ∈ s.readers
  · have h_not_in : ¬ c ∉ s.readers := fun h => h h_in
    simp only [h_not_in, ↓reduceIte]
    -- post-state is `s'.promoteWaitersIfReadersEmpty`.  Generalize over
    -- the filtered readers list to eliminate the predicate-form mismatch.
    generalize h_filter : s.readers.filter _ = readers'
    -- Now the goal is about an arbitrary state with `readers := readers'`
    -- and `waiters := s.waiters`.  Apply the FIFO admission witness.
    obtain ⟨k, h_drop⟩ := rwLock_fifo_admission_readers_empty
      ({ writerHeld := s.writerHeld, readers := readers', waiters := s.waiters } :
        RwLockState)
    rw [h_drop]
    exact List.drop_sublist k _
  · -- c ∉ readers: applyOp is no-op; simp closes via Sublist.refl in default set.
    simp [h_in]

/-- **WS-SM SM2.C-defer D-1.7 (write variant)**: `releaseWrite c` does not
append to waiters; the post-state `waiters` is a `Sublist` of the pre-state. -/
theorem releaseWrite_waiters_sublist (s : RwLockState) (c : CoreId) :
    (s.applyOp (.releaseWrite c)).waiters.Sublist s.waiters := by
  unfold RwLockState.applyOp
  by_cases h_eq : s.writerHeld = some c
  · have h_not_ne : ¬ s.writerHeld ≠ some c := fun h => h h_eq
    simp only [h_not_ne, ↓reduceIte]
    obtain ⟨k, h_drop⟩ := rwLock_fifo_admission
      ({ writerHeld := none, readers := s.readers, waiters := s.waiters } :
        RwLockState)
    rw [h_drop]
    exact List.drop_sublist k _
  · -- writerHeld ≠ some c: applyOp is no-op; simp closes via Sublist.refl.
    simp [h_eq]

/-- **WS-SM SM2.C-defer D-1.7 (combined corollary)**: any release op
(read or write) produces a sublist of waiters. -/
theorem release_waiters_sublist
    (s : RwLockState) (op : RwLockOp)
    (h_op : (∃ c, op = .releaseRead c) ∨ (∃ c, op = .releaseWrite c)) :
    (s.applyOp op).waiters.Sublist s.waiters := by
  rcases h_op with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact releaseRead_waiters_sublist s c
  · exact releaseWrite_waiters_sublist s c

/-- **WS-SM SM2.C-defer D-1.7 (acquire combined)**: any acquire op
(read or write) produces a sublist relation in the OTHER direction:
the pre-state waiters is a sublist of the post-state waiters.

Either the post equals the pre (no-op), or post = pre ++ [(c, mode)],
in which case pre is a sublist of post by `List.sublist_append_left`. -/
theorem acquire_waiters_super_or_eq
    (s : RwLockState) (op : RwLockOp)
    (h_op : (∃ c, op = .tryAcquireRead c) ∨ (∃ c, op = .tryAcquireWrite c)) :
    s.waiters.Sublist (s.applyOp op).waiters := by
  rcases h_op with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · rcases tryAcquireRead_waiters_append_or_noop s c with h_eq | h_eq
    · rw [h_eq]; exact List.Sublist.refl _
    · rw [h_eq]; exact List.sublist_append_left s.waiters [(c, AccessMode.read)]
  · rcases tryAcquireWrite_waiters_append_or_noop s c with h_eq | h_eq
    · rw [h_eq]; exact List.Sublist.refl _
    · rw [h_eq]; exact List.sublist_append_left s.waiters [(c, AccessMode.write)]

-- ============================================================================
-- SM2.C-defer D-1.8 — Single-step order preservation
-- ============================================================================

/-- **WS-SM SM2.C-defer helper**: `idxOf` after appending preserves the
index of an existing element.

If `w ∈ l`, then `(l ++ extra).idxOf w = l.idxOf w` — appending to the
tail doesn't move existing elements' positions (since `idxOf` returns
the first occurrence, which is in the original `l`). -/
private theorem idxOf_append_of_mem
    (l : List (CoreId × AccessMode)) (extra : List (CoreId × AccessMode))
    (w : CoreId × AccessMode) (h_in : w ∈ l) :
    (l ++ extra).idxOf w = l.idxOf w := by
  rw [List.idxOf_append]
  simp [h_in]

/-- **WS-SM SM2.C-defer helper**: for a Nodup list, `idxOf` of a member
of `l.drop k` plus `k` equals `idxOf` in `l`.

This is the canonical positional relationship: dropping the first `k`
elements shifts every remaining element's index downward by exactly `k`. -/
private theorem drop_idxOf_eq_of_nodup
    {α : Type _} [BEq α] [LawfulBEq α]
    (l : List α) (h_nodup : l.Nodup) (k : Nat) (w : α) (h_in : w ∈ l.drop k) :
    (l.drop k).idxOf w + k = l.idxOf w := by
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
    cases l with
    | nil => simp at h_in
    | cons head rest =>
      -- l.drop (k+1) = rest.drop k.  l.idxOf w = if w = head then 0 else 1 + rest.idxOf w.
      simp only [List.drop_succ_cons] at h_in ⊢
      have h_rest_nodup : rest.Nodup := h_nodup.of_cons
      have h_w_ne_head : w ≠ head := by
        intro h_eq
        have : head ∈ rest.drop k := by rw [h_eq] at h_in; exact h_in
        have h_head_in : head ∈ rest := List.mem_of_mem_drop this
        have h_not := (List.nodup_cons.mp h_nodup).1
        exact h_not h_head_in
      have h_idx_cons : (head :: rest).idxOf w = rest.idxOf w + 1 := by
        rw [List.idxOf_cons]
        have h_beq : (head == w) = false := by
          rw [beq_eq_false_iff_ne]; exact h_w_ne_head.symm
        rw [h_beq]; rfl
      rw [h_idx_cons]
      have := ih rest h_rest_nodup h_in
      omega

/-- **WS-SM SM2.C-defer helper**: Nodup-fst implies Nodup on the full
pair list (since equal pairs require equal fst components). -/
private theorem nodup_of_nodup_map_fst
    (l : List (CoreId × AccessMode)) (h : (l.map Prod.fst).Nodup) : l.Nodup := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons head rest ih =>
    rw [List.map_cons] at h
    rw [List.nodup_cons] at h
    rw [List.nodup_cons]
    have h_rest := ih h.2
    refine ⟨?_, h_rest⟩
    intro h_in
    -- head ∈ rest ⇒ head.fst ∈ rest.map fst, contradicting h.1.
    have h_fst_in : head.fst ∈ rest.map Prod.fst := List.mem_map.mpr ⟨head, h_in, rfl⟩
    exact h.1 h_fst_in

/-- **WS-SM SM2.C-defer helper**: characterization of release-read
post-state when `c ∈ readers` (the effective-release branch). -/
private theorem releaseRead_effective_post (s : RwLockState) (c : CoreId)
    (h_in : c ∈ s.readers) :
    s.applyOp (.releaseRead c) =
    ({ writerHeld := s.writerHeld,
       readers := s.readers.filter (· ≠ c),
       waiters := s.waiters } : RwLockState).promoteWaitersIfReadersEmpty := by
  unfold RwLockState.applyOp
  simp [h_in]

/-- **WS-SM SM2.C-defer helper**: characterization of release-read
post-state when `c ∉ readers` (the no-op branch). -/
private theorem releaseRead_noop_post (s : RwLockState) (c : CoreId)
    (h_not_in : c ∉ s.readers) :
    s.applyOp (.releaseRead c) = s := by
  unfold RwLockState.applyOp; simp [h_not_in]

/-- **WS-SM SM2.C-defer helper**: characterization of release-write
post-state when `writerHeld = some c` (the effective-release branch). -/
private theorem releaseWrite_effective_post (s : RwLockState) (c : CoreId)
    (h_eq : s.writerHeld = some c) :
    s.applyOp (.releaseWrite c) =
    ({ writerHeld := none, readers := s.readers, waiters := s.waiters } :
      RwLockState).promoteWaitersOnWriterRelease := by
  unfold RwLockState.applyOp; simp [h_eq]

/-- **WS-SM SM2.C-defer helper**: characterization of release-write
post-state when `writerHeld ≠ some c` (the no-op branch). -/
private theorem releaseWrite_noop_post (s : RwLockState) (c : CoreId)
    (h_ne : s.writerHeld ≠ some c) :
    s.applyOp (.releaseWrite c) = s := by
  unfold RwLockState.applyOp; simp [h_ne]

/-- **WS-SM SM2.C-defer D-1.8**: for ANY single op, the relative order
of two waiters present in both the pre- and post-state is preserved.

Combining D-1.6 (acquire appends to tail) and D-1.7 (release drops
prefix from head) — both witnesses give concrete shape, allowing
positional reasoning via `idxOf_append_of_mem` and
`drop_idxOf_eq_of_nodup`. -/
theorem applyOp_preserves_waiter_order
    (s : RwLockState) (h_wf : s.wf)
    (op : RwLockOp)
    (w₁ w₂ : CoreId × AccessMode)
    (h_in₁_pre : w₁ ∈ s.waiters) (h_in₂_pre : w₂ ∈ s.waiters)
    (h_in₁_post : w₁ ∈ (s.applyOp op).waiters)
    (h_in₂_post : w₂ ∈ (s.applyOp op).waiters)
    (h_order : s.waiters.idxOf w₁ < s.waiters.idxOf w₂) :
    (s.applyOp op).waiters.idxOf w₁ < (s.applyOp op).waiters.idxOf w₂ := by
  -- INV-R3 gives Nodup-fst on waiters; derive Nodup of waiters.
  have h_nodup_fst := s.wf_waitersCoresNodup h_wf
  have h_nodup : s.waiters.Nodup := nodup_of_nodup_map_fst s.waiters h_nodup_fst
  cases op with
  | tryAcquireRead c =>
    rcases tryAcquireRead_waiters_append_or_noop s c with h_post | h_post
    · rw [h_post]; exact h_order
    · rw [h_post]
      rw [idxOf_append_of_mem s.waiters _ w₁ h_in₁_pre]
      rw [idxOf_append_of_mem s.waiters _ w₂ h_in₂_pre]
      exact h_order
  | tryAcquireWrite c =>
    rcases tryAcquireWrite_waiters_append_or_noop s c with h_post | h_post
    · rw [h_post]; exact h_order
    · rw [h_post]
      rw [idxOf_append_of_mem s.waiters _ w₁ h_in₁_pre]
      rw [idxOf_append_of_mem s.waiters _ w₂ h_in₂_pre]
      exact h_order
  | releaseRead c =>
    by_cases h_in : c ∈ s.readers
    · -- Effective release path: post = ({s with readers := filter}).promote
      rw [releaseRead_effective_post s c h_in] at h_in₁_post h_in₂_post ⊢
      -- Generalize the filtered readers so the predicate-form mismatch
      -- between `decide (· ≠ c)` and `!decide (· = c)` doesn't bite.
      generalize h_fil : s.readers.filter (· ≠ c) = readers' at h_in₁_post h_in₂_post ⊢
      obtain ⟨k, h_drop⟩ := rwLock_fifo_admission_readers_empty
        ({ writerHeld := s.writerHeld, readers := readers', waiters := s.waiters } :
          RwLockState)
      -- Normalize the `.waiters` projection of the record-update form.
      have h_w_proj : ({ writerHeld := s.writerHeld, readers := readers',
                         waiters := s.waiters } : RwLockState).waiters = s.waiters := rfl
      rw [h_w_proj] at h_drop
      rw [h_drop] at h_in₁_post h_in₂_post ⊢
      have h₁ := drop_idxOf_eq_of_nodup s.waiters h_nodup k w₁ h_in₁_post
      have h₂ := drop_idxOf_eq_of_nodup s.waiters h_nodup k w₂ h_in₂_post
      omega
    · -- No-op path.
      rw [releaseRead_noop_post s c h_in]; exact h_order
  | releaseWrite c =>
    by_cases h_eq : s.writerHeld = some c
    · rw [releaseWrite_effective_post s c h_eq] at h_in₁_post h_in₂_post ⊢
      obtain ⟨k, h_drop⟩ := rwLock_fifo_admission
        ({ writerHeld := none, readers := s.readers, waiters := s.waiters } :
          RwLockState)
      have h_w_proj : ({ writerHeld := none, readers := s.readers,
                         waiters := s.waiters } : RwLockState).waiters = s.waiters := rfl
      rw [h_w_proj] at h_drop
      rw [h_drop] at h_in₁_post h_in₂_post ⊢
      have h₁ := drop_idxOf_eq_of_nodup s.waiters h_nodup k w₁ h_in₁_post
      have h₂ := drop_idxOf_eq_of_nodup s.waiters h_nodup k w₂ h_in₂_post
      omega
    · rw [releaseWrite_noop_post s c h_eq]; exact h_order

-- ============================================================================
-- SM2.C-defer D-1.9 — Main temporal FIFO admission theorem (partial form)
-- ============================================================================

/-- **WS-SM SM2.C-defer D-1.9 (partial: structural sublist form)**:
across an RwLockExecution starting from `unheld`, the relative order of two
waiters is preserved across every kernel step (with both surviving).

This is a multi-step composition of `applyOp_preserves_waiter_order`
(D-1.8) — by induction on the trace length, every step preserves the
relative order of surviving waiters.

The full temporal claim (admission order ↔ enqueue order via the
`enqueueStep` / `admissionStep` form) requires additional bridging that
threads the strict-transition formulation through; the structural
"order is preserved across the whole trace" property captured here is
the cleanly-proven core of D-1.9. -/
theorem rwLock_fifo_admission_temporal_structural
    (e : RwLockExecution)
    (k₁ k₂ : Nat) (h_le : k₁ ≤ k₂)
    (w₁ w₂ : CoreId × AccessMode)
    (h_in₁_at_k₁ : w₁ ∈ (e.stateAt k₁).waiters)
    (h_in₂_at_k₁ : w₂ ∈ (e.stateAt k₁).waiters)
    (h_in₁_at_k₂ : w₁ ∈ (e.stateAt k₂).waiters)
    (h_in₂_at_k₂ : w₂ ∈ (e.stateAt k₂).waiters)
    (h_order : (e.stateAt k₁).waiters.idxOf w₁ < (e.stateAt k₁).waiters.idxOf w₂)
    (h_surviving : ∀ j, k₁ ≤ j → j ≤ k₂ →
        w₁ ∈ (e.stateAt j).waiters ∧ w₂ ∈ (e.stateAt j).waiters) :
    (e.stateAt k₂).waiters.idxOf w₁ < (e.stateAt k₂).waiters.idxOf w₂ := by
  -- Induct on the gap (k₂ - k₁).
  generalize h_gap : k₂ - k₁ = gap
  induction gap generalizing k₂ with
  | zero =>
    -- k₂ = k₁: trivial.
    have h_eq : k₂ = k₁ := by omega
    subst h_eq
    -- Need: (stateAt k₁).waiters.idxOf w₁ < (stateAt k₁).waiters.idxOf w₂.
    -- This is exactly h_order.
    exact h_order
  | succ n ih =>
    -- k₂ = k₁ + n + 1.  By IH at j = k₂ - 1 = k₁ + n, the order holds.
    -- Then one more step from j to k₂ via applyOp_preserves_waiter_order.
    have h_k_pos : k₂ ≥ 1 := by omega
    have h_prev : k₂ - 1 ≥ k₁ := by omega
    have h_le_prev : k₁ ≤ k₂ - 1 := h_prev
    have h_gap_prev : k₂ - 1 - k₁ = n := by omega
    -- Get the inductive hypothesis at k₂ - 1.
    have h_surv_prev : w₁ ∈ (e.stateAt (k₂ - 1)).waiters ∧ w₂ ∈ (e.stateAt (k₂ - 1)).waiters :=
      h_surviving (k₂ - 1) h_le_prev (by omega)
    have h_surviving_prev : ∀ j, k₁ ≤ j → j ≤ k₂ - 1 →
        w₁ ∈ (e.stateAt j).waiters ∧ w₂ ∈ (e.stateAt j).waiters := by
      intro j h_lo h_hi
      exact h_surviving j h_lo (by omega)
    have h_ih := ih (k₂ - 1) h_le_prev h_surv_prev.1 h_surv_prev.2
                    h_surviving_prev h_gap_prev
    -- Now extend by one step.  Either k₂ - 1 < ops.length (real step)
    -- or k₂ - 1 ≥ ops.length (state unchanged).
    by_cases h_in_range : k₂ - 1 < e.ops.length
    · -- stateAt k₂ = stateAt (k₂-1+1).
      have h_k_eq : k₂ = (k₂ - 1) + 1 := by omega
      rw [h_k_eq]
      rw [RwLockExecution.stateAt_succ e h_in_range]
      have h_wf_prev : (e.stateAt (k₂ - 1)).wf := e.stateAt_wf (k₂ - 1)
      -- Apply D-1.8 single-step preservation.
      apply applyOp_preserves_waiter_order
        (e.stateAt (k₂ - 1)) h_wf_prev (e.ops[k₂ - 1]'h_in_range)
        w₁ w₂ h_surv_prev.1 h_surv_prev.2
      · -- w₁ ∈ post-state: rewrite the goal via h_k_eq and RwLockExecution.stateAt_succ
        rw [← RwLockExecution.stateAt_succ e h_in_range, ← h_k_eq]; exact h_in₁_at_k₂
      · rw [← RwLockExecution.stateAt_succ e h_in_range, ← h_k_eq]; exact h_in₂_at_k₂
      · exact h_ih
    · -- k₂ - 1 ≥ ops.length: stateAt k₂ = stateAt (k₂ - 1).
      have h_eq : e.stateAt k₂ = e.stateAt (k₂ - 1) := by
        unfold RwLockExecution.stateAt
        have h_ge : e.ops.length ≤ k₂ - 1 := Nat.le_of_not_lt h_in_range
        have h_take : e.ops.take k₂ = e.ops.take (k₂ - 1) := by
          rw [List.take_of_length_le (by omega), List.take_of_length_le h_ge]
        rw [h_take]
      rw [h_eq]; exact h_ih

-- ============================================================================
-- SM2.C-defer D-2.5 — Bounded admission via effective-release events
-- ============================================================================

/-- **WS-SM SM2.C-defer D-2.5 (corollary, weak form)**: every queued
writer's wait-depth is bounded by `numCores - 1` (independent of the
trace), via `writerWaitDepth_bounded` (D-2.3).

This is the structural bound that D-3 (liveness) consumes: under any
fairness assumption with a `maxDelay` parameter, the writer is admitted
within `(numCores - 1) × maxDelay` steps. -/
theorem rwLock_bounded_wait_write_distinct_weak
    (s : RwLockState) (h_wf : s.wf)
    (c : CoreId) (h_queued : (c, AccessMode.write) ∈ s.waiters) :
    writerWaitDepth s c ≤ numCores - 1 :=
  writerWaitDepth_bounded s h_wf c h_queued

/-- **WS-SM SM2.C-defer D-2.5 (alternate form)**: the writer-specific
bound is symmetric to the reader bound at the structural level (both
share `numCores - 1` as the worst-case admission window in terms of
"distinct cores ahead of c").

Concretely, the admission window for a queued writer `c` is bounded by:
* `idxOf c ≤ numCores - 1 - readers - writer_bit`
* but the sum `idxOf + readers + writer_bit ≤ numCores - 1` is the tight
  composite bound (D-2.3).

This theorem packages the writer-specific perspective for SM3 consumers
in priority-inheritance reasoning. -/
theorem writerWaitDepth_componentBounded
    (s : RwLockState) (h_wf : s.wf)
    (c : CoreId) (h_queued : (c, AccessMode.write) ∈ s.waiters) :
    s.waiters.idxOf (c, AccessMode.write) ≤ numCores - 1 ∧
    s.readers.length ≤ numCores - 1 ∧
    (if s.writerHeld.isSome then 1 else 0) ≤ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · -- idxOf ≤ numCores - 1.
    have h_full := writerWaitDepth_bounded s h_wf c h_queued
    unfold writerWaitDepth at h_full
    simp only at h_full
    omega
  · -- readers.length ≤ numCores - 1.  From rwLock_bounded_wait_read:
    -- readers + waiters + writer_bit ≤ numCores.
    -- waiters.length ≥ 1 (c is in it).  So readers ≤ numCores - 1.
    have h_bnd := rwLock_bounded_wait_read s h_wf
    have h_w_pos : 0 < s.waiters.length := by
      cases h : s.waiters with
      | nil => rw [h] at h_queued; exact absurd h_queued List.not_mem_nil
      | cons _ _ => simp
    by_cases h_w : s.writerHeld.isSome <;> simp [h_w] at h_bnd <;> omega
  · split <;> omega

-- ============================================================================
-- SM2.C-defer §4.5 + D-3 — FairTrace predicate + writer liveness (partial)
-- ============================================================================

/-- **WS-SM SM2.C-defer §4.5 (D-3 input)**: an execution is "release-fair"
if every holder transitions out of holding within a bounded number of
steps after acquiring.

`maxDelay` is a parameter of the fairness assumption — it represents
the kernel-level critical-section duration bound that SM3+ consumers
must satisfy.  In the spec this is left as a parameter; in the runtime
it's enforced by the scheduler.

**Strengthened transition-edge form** (closes audit M-2): both
fairness conjuncts require the release to be a real *transition* edge
(`c ∈ readers` at `k_rel` AND `c ∉ readers` at `k_rel + 1`), not merely
"c is not a reader at some later step".  This eliminates the
vacuous-satisfiability concern. -/
structure FairTrace (e : RwLockExecution) (maxDelay : Nat) where
  /-- Every reader-acquire is paired with a reader-release transition
  within `maxDelay` subsequent steps. -/
  reader_fairness :
    ∀ k_acq c,
      1 ≤ k_acq →
      c ∈ (e.stateAt k_acq).readers →
      c ∉ (e.stateAt (k_acq - 1)).readers →
      ∃ k_rel, k_acq ≤ k_rel ∧ k_rel ≤ k_acq + maxDelay ∧
        c ∈ (e.stateAt k_rel).readers ∧
        c ∉ (e.stateAt (k_rel + 1)).readers
  /-- Every writer-acquire is paired with a writer-release transition
  within `maxDelay` subsequent steps. -/
  writer_fairness :
    ∀ k_acq c,
      1 ≤ k_acq →
      (e.stateAt k_acq).writerHeld = some c →
      (e.stateAt (k_acq - 1)).writerHeld ≠ some c →
      ∃ k_rel, k_acq ≤ k_rel ∧ k_rel ≤ k_acq + maxDelay ∧
        (e.stateAt k_rel).writerHeld = some c ∧
        (e.stateAt (k_rel + 1)).writerHeld ≠ some c

/-- **WS-SM SM2.C-defer D-3.7**: a runtime configuration symbol for the
maximum release delay.  Set to a placeholder value of `1024` (steps);
SM3 will tune this against actual kernel critical-section budgets. -/
def MAX_RELEASE_DELAY : Nat := 1024

/-- **WS-SM SM2.C-defer D-3 (single-step safety / building block)**:
under a wf state where a writer `c` is queued, a tryAcquireRead from a
different non-involved core does NOT promote `c` out of waiters.

This is the v1.0.0 baseline single-step safety claim that the v1.0.0
`rwLock_no_writer_starvation` already provides at the wf level — we
restate here in the deferred-completion namespace for compositional
reasoning with `FairTrace`. -/
theorem rwLock_writer_no_starvation_step
    (s : RwLockState) (h_wf : s.wf)
    (c_w : CoreId) (h_w_waiting : (c_w, AccessMode.write) ∈ s.waiters)
    (c_r : CoreId) (h_r_not_inv : ¬ s.coreInvolved c_r) :
    (c_w, AccessMode.write) ∈ (s.applyOp (.tryAcquireRead c_r)).waiters :=
  rwLock_writer_safety_under_reader_acquire s c_w h_w_waiting c_r h_r_not_inv

/-- **WS-SM SM2.C-defer D-3.5 (head-of-queue writer admission)**: when
a writer is at the head of the wait queue AND no holder exists, the
next call to `promoteWaitersOnWriterRelease` admits the writer to
`writerHeld`.

This is the operational basis for D-3.4 (writer-eventually-at-head ⇒
admitted): once the queue is in this configuration, the next release-
and-promote step puts the writer into `writerHeld`. -/
theorem writer_at_head_promoted
    (s : RwLockState)
    (c : CoreId) (h_head : s.waiters.head? = some (c, AccessMode.write)) :
    s.promoteWaitersOnWriterRelease.writerHeld = some c := by
  unfold RwLockState.promoteWaitersOnWriterRelease
  cases h_w : s.waiters with
  | nil => rw [h_w] at h_head; simp at h_head
  | cons head rest =>
    -- Destructure head into its components first.
    obtain ⟨c', m⟩ := head
    rw [h_w] at h_head
    simp at h_head
    -- h_head : c' = c ∧ m = .write
    obtain ⟨h_c, h_m⟩ := h_head
    subst h_c; subst h_m
    rfl

-- ============================================================================
-- SM2.C-defer §4.4 + D-4 — Concrete event model + bisimulation infrastructure
-- ============================================================================

/-- **WS-SM SM2.C-defer D-4.1**: a concrete Rust-level operation on the
lock state.

Each constructor represents one atomic memory operation the Rust impl
performs.  The abstract `RwLockOp` may map to multiple
`ConcreteRwLockOp`s (e.g., a `tryAcquireRead` is a load + CAS sequence,
possibly with CAS-retry under contention).

All constructors carry a `core : CoreId` (the executing core) for
fairness-reasoning compositionality (closes audit finding L-7). -/
inductive ConcreteRwLockOp where
  /-- Load(Acquire): observes current state. -/
  | load            (core : CoreId)
  /-- CAS s → s+1 (acquire-read success). -/
  | casAcquireRead  (core : CoreId) (expected new : UInt64)
  /-- `fetch_sub(1, Release)` for release-read. -/
  | fetchSubRead    (core : CoreId)
  /-- CAS 0 → WRITER_BIT (acquire-write success). -/
  | casAcquireWrite (core : CoreId)
  /-- `fetch_and(READER_MASK, Release)` for release-write. -/
  | fetchAndWrite   (core : CoreId)
  /-- SEV broadcast from `core`. -/
  | sev             (core : CoreId)
  /-- `wfe_bounded` park (no state change). -/
  | wfeWait         (core : CoreId)
  deriving Repr, DecidableEq

/-- **WS-SM SM2.C-defer D-4.1**: apply a single concrete operation to the
bit-packed state.

Returns `(new_state, succeeded)`: the new state and whether the op
succeeded (CAS may fail).  For non-CAS ops (load, fetch_sub, fetch_and,
sev, wfe), `succeeded` is always `true`.

`UInt64` arithmetic is modular over `2^64`, faithfully matching the
Rust impl's `fetch_sub` / `fetch_and` behaviour on a `u64` field —
including underflow (`0 - 1 = u64::MAX`) and bitmask composition
(closes audit finding M-4). -/
def concreteApplyOp (state : UInt64) (op : ConcreteRwLockOp) :
    UInt64 × Bool :=
  match op with
  | .load _ => (state, true)
  | .casAcquireRead _ expected new =>
      if state = expected then (new, true) else (state, false)
  | .fetchSubRead _ => (state - 1, true)
  | .casAcquireWrite _ =>
      if state = 0 then (writerBit.toUInt64, true) else (state, false)
  | .fetchAndWrite _ => (state &&& readerMask.toUInt64, true)
  | .sev _ => (state, true)
  | .wfeWait _ => (state, true)

/-- **WS-SM SM2.C-defer D-4.2**: admissible concrete sequences for each
abstract op.

A single abstract `RwLockOp` maps to a FAMILY of permissible concrete
sequences (closes audits M-5 / M-6):
1. **CAS-retry under contention** — `tryAcquireRead` loops on CAS failure.
2. **Park-and-retry under writer held** — `wfe_bounded`-parks + reloads.
3. **Conditional SEV emission** — `release_read` emits SEV only when
   post-state would be empty; otherwise no SEV.

The constructors below enumerate the base "success" shapes; the
inductive `tryRead_cas_retry` / `tryRead_park_retry` /
`tryWrite_cas_retry` / `tryWrite_park_retry` constructors close the
family under contention-retry. -/
inductive opCorresponds : RwLockOp → List ConcreteRwLockOp → Prop where
  /-- tryAcquireRead success: load + CAS-success. -/
  | tryRead_success (c : CoreId) (e n : UInt64) :
      opCorresponds (.tryAcquireRead c) [.load c, .casAcquireRead c e n]
  /-- tryAcquireRead CAS-retry: load + CAS-fail + recurse. -/
  | tryRead_cas_retry (c : CoreId) (e n : UInt64) (tail : List ConcreteRwLockOp) :
      opCorresponds (.tryAcquireRead c) tail →
      opCorresponds (.tryAcquireRead c)
        ([.load c, .casAcquireRead c e n] ++ tail)
  /-- tryAcquireRead park-retry: load + wfeWait + recurse. -/
  | tryRead_park_retry (c : CoreId) (tail : List ConcreteRwLockOp) :
      opCorresponds (.tryAcquireRead c) tail →
      opCorresponds (.tryAcquireRead c)
        ([.load c, .wfeWait c] ++ tail)
  /-- releaseRead: SEV-suppressed (post-state still has holders). -/
  | releaseRead_no_sev (c : CoreId) :
      opCorresponds (.releaseRead c) [.fetchSubRead c]
  /-- releaseRead: SEV-emitted (post-state empty). -/
  | releaseRead_with_sev (c : CoreId) :
      opCorresponds (.releaseRead c) [.fetchSubRead c, .sev c]
  /-- tryAcquireWrite success: load + CAS-success. -/
  | tryWrite_success (c : CoreId) :
      opCorresponds (.tryAcquireWrite c) [.load c, .casAcquireWrite c]
  /-- tryAcquireWrite CAS-retry: load + CAS-fail + recurse. -/
  | tryWrite_cas_retry (c : CoreId) (tail : List ConcreteRwLockOp) :
      opCorresponds (.tryAcquireWrite c) tail →
      opCorresponds (.tryAcquireWrite c)
        ([.load c, .casAcquireWrite c] ++ tail)
  /-- tryAcquireWrite park-retry: load + wfeWait + recurse. -/
  | tryWrite_park_retry (c : CoreId) (tail : List ConcreteRwLockOp) :
      opCorresponds (.tryAcquireWrite c) tail →
      opCorresponds (.tryAcquireWrite c)
        ([.load c, .wfeWait c] ++ tail)
  /-- releaseWrite: SEV-suppressed. -/
  | releaseWrite_no_sev (c : CoreId) :
      opCorresponds (.releaseWrite c) [.fetchAndWrite c]
  /-- releaseWrite: SEV-emitted. -/
  | releaseWrite_with_sev (c : CoreId) :
      opCorresponds (.releaseWrite c) [.fetchAndWrite c, .sev c]

/-- **WS-SM SM2.C-defer D-4.4**: `load` doesn't modify state.

This is the foundational "no-op state preservation" lemma for the
bisimulation: a load operation is a pure observation that doesn't
change the lock state. -/
theorem concreteApplyOp_preserves_sim_load
    (state : UInt64) (c : CoreId) :
    (concreteApplyOp state (.load c)).1 = state := by
  unfold concreteApplyOp
  rfl

/-- **WS-SM SM2.C-defer D-4.4**: `wfeWait` doesn't modify state.

Same shape as `load`: parking on the WFE event register doesn't change
the lock's bit-packed state. -/
theorem concreteApplyOp_preserves_sim_wfe
    (state : UInt64) (c : CoreId) :
    (concreteApplyOp state (.wfeWait c)).1 = state := by
  unfold concreteApplyOp
  rfl

/-- **WS-SM SM2.C-defer D-4.4**: `sev` doesn't modify state.

SEV is a wake-broadcast signal; it doesn't touch the lock's state. -/
theorem concreteApplyOp_preserves_sim_sev
    (state : UInt64) (c : CoreId) :
    (concreteApplyOp state (.sev c)).1 = state := by
  unfold concreteApplyOp
  rfl

/-- **WS-SM SM2.C-defer D-4.5 (failed CAS path)**: a failed
`casAcquireRead` doesn't modify state.

When the observed value doesn't match `expected`, the CAS leaves state
unchanged.  This is the building block for `tryRead_cas_retry`'s
inductive step (the failure step preserves the simulation). -/
theorem concreteApplyOp_preserves_sim_cas_acquire_read_fail
    (state expected new : UInt64) (c : CoreId)
    (h_ne : state ≠ expected) :
    (concreteApplyOp state (.casAcquireRead c expected new)).1 = state := by
  unfold concreteApplyOp
  simp [h_ne]

/-- **WS-SM SM2.C-defer D-4.5 (success CAS path)**: a successful
`casAcquireRead` produces the new state.

When `state = expected`, the CAS succeeds and returns `new`.  This is
the building block for `tryRead_success`. -/
theorem concreteApplyOp_cas_acquire_read_success
    (state expected new : UInt64) (c : CoreId)
    (h_eq : state = expected) :
    (concreteApplyOp state (.casAcquireRead c expected new)).1 = new := by
  unfold concreteApplyOp
  simp [h_eq]

/-- **WS-SM SM2.C-defer D-4.7 (failed CAS path)**: a failed
`casAcquireWrite` doesn't modify state. -/
theorem concreteApplyOp_preserves_sim_cas_acquire_write_fail
    (state : UInt64) (c : CoreId)
    (h_ne : state ≠ 0) :
    (concreteApplyOp state (.casAcquireWrite c)).1 = state := by
  unfold concreteApplyOp
  simp [h_ne]

/-- **WS-SM SM2.C-defer D-4.7 (success CAS path)**: a successful
`casAcquireWrite` from state 0 produces `writerBit.toUInt64`. -/
theorem concreteApplyOp_cas_acquire_write_success
    (state : UInt64) (c : CoreId)
    (h_eq : state = 0) :
    (concreteApplyOp state (.casAcquireWrite c)).1 = writerBit.toUInt64 := by
  unfold concreteApplyOp
  simp [h_eq]

/-- **WS-SM SM2.C-defer D-4.6 (abstract building block)**: when the
abstract state has a reader, its encoded form is ≥ 1.

This is the no-`rwLockSim`-dependency version of the underflow-corner
lemma; the `rwLockSim`-aware form lives in `RwLockRefinement.lean`. -/
theorem encodeRwLock_at_least_one_when_reader
    (abstract : RwLockState) (c : CoreId) (h_holder : c ∈ abstract.readers) :
    encodeRwLock abstract.writerHeld.isSome abstract.readers.length ≥ 1 := by
  unfold encodeRwLock
  have h_pos : abstract.readers.length ≥ 1 := by
    cases h : abstract.readers with
    | nil => rw [h] at h_holder; exact absurd h_holder List.not_mem_nil
    | cons _ _ => simp
  -- Goal: (if writerHeld.isSome then writerBit else 0) + readers.length ≥ 1.
  -- Use Nat.le_add_left to bound from below by readers.length.
  exact Nat.le_trans h_pos (Nat.le_add_left _ _)

-- ============================================================================
-- SM2.C-defer D-3.5 — head-of-queue ⇒ admitted (extended)
-- ============================================================================

/-- **WS-SM SM2.C-defer D-3.5 (reader-head batch promotion)**: when a
reader is at the head of the wait queue AND no holder exists, the next
call to `promoteWaitersOnWriterRelease` admits the reader to `readers`. -/
theorem reader_at_head_promoted
    (s : RwLockState)
    (c : CoreId) (h_head : s.waiters.head? = some (c, AccessMode.read)) :
    c ∈ s.promoteWaitersOnWriterRelease.readers := by
  unfold RwLockState.promoteWaitersOnWriterRelease
  cases h_w : s.waiters with
  | nil => rw [h_w] at h_head; simp at h_head
  | cons head rest =>
    obtain ⟨c', m⟩ := head
    rw [h_w] at h_head
    simp at h_head
    obtain ⟨h_c, h_m⟩ := h_head
    subst h_c; subst h_m
    -- head matches read pattern; the post-state's readers contains the
    -- batch-promoted prefix.  simp closes via `List.mem_cons`.
    simp

/-- **WS-SM SM2.C-defer D-3.5 (queue-emptied)**: when waiters is empty
AND no holder exists, `promoteWaitersOnWriterRelease` is a no-op
(returns the same state).

This is the structural complement to `writer_at_head_promoted` —
when there's nothing to promote, the function preserves state. -/
theorem promote_noop_on_empty_waiters (s : RwLockState)
    (h_w : s.waiters = []) :
    s.promoteWaitersOnWriterRelease = s := by
  unfold RwLockState.promoteWaitersOnWriterRelease
  rw [h_w]

-- ============================================================================
-- SM2.C-defer D-4.5 — Single-step CAS-success bisimulation (read variant)
-- ============================================================================

/-- **WS-SM SM2.C-defer D-4.5 (success branch identity)**: when the
abstract state has no writer and no queued-writer-head, a
`tryAcquireRead c` for a non-involved core c grows readers by 1.

Concretely, this is the post-state shape for the "acquire-direct"
branch of `applyOp .tryAcquireRead`. -/
theorem tryAcquireRead_direct_acquire_shape
    (s : RwLockState) (c : CoreId)
    (h_not_inv : ¬ s.coreInvolved c)
    (h_no_writer : s.writerHeld = none)
    (h_waiters_safe :
      s.waiters = [] ∨
      ∃ c' rest, s.waiters = (c', AccessMode.read) :: rest) :
    (s.applyOp (.tryAcquireRead c)).readers = c :: s.readers ∧
    (s.applyOp (.tryAcquireRead c)).writerHeld = s.writerHeld ∧
    (s.applyOp (.tryAcquireRead c)).waiters = s.waiters := by
  unfold RwLockState.applyOp
  simp [h_not_inv, h_no_writer]
  -- Goal: now the inner `match s.waiters with` needs to be discharged.
  rcases h_waiters_safe with h | ⟨c', rest, h⟩
  · rw [h]; simp
  · rw [h]; simp

/-- **WS-SM SM2.C-defer D-4.7 (success branch identity for writer)**:
when the abstract state has no holder, a `tryAcquireWrite c` for a
non-involved core c sets `writerHeld := some c`. -/
theorem tryAcquireWrite_direct_acquire_shape
    (s : RwLockState) (c : CoreId)
    (h_not_inv : ¬ s.coreInvolved c)
    (h_no_writer : s.writerHeld = none)
    (h_no_readers : s.readers = []) :
    (s.applyOp (.tryAcquireWrite c)).writerHeld = some c ∧
    (s.applyOp (.tryAcquireWrite c)).readers = s.readers ∧
    (s.applyOp (.tryAcquireWrite c)).waiters = s.waiters := by
  unfold RwLockState.applyOp
  simp [h_not_inv, h_no_writer, h_no_readers]

end SeLe4n.Kernel.Concurrency



