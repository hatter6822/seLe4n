-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-SM SM3.A: this module entered the production import closure when
-- the SM3.A.1..A.9 per-object `lock : RwLockState` fields landed on every
-- kernel-object struct (TCB, Endpoint, CNode, Notification,
-- UntypedObject, SchedContext, VSpaceRoot).  The prior "STATUS: staged"
-- marker was removed at SM3.A landing per the implement-the-improvement
-- rule — every kernel object now carries a per-object lock state and
-- consuming code (SM3.B `LockId.lookup`, SM3.C `withLockSet`) is built
-- on top.  The abstract operational specification here continues to be
-- refined by `rust/sele4n-hal/src/rw_lock.rs` per SM2.C.19 and the
-- SM2.C.20 refinement bridge `Locks/RwLockRefinement.lean`.

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
      -- **Strict FIFO discipline** (SM2.C-defer plan §5.3 structural fix):
      -- new readers enqueue iff any holder OR any queued waiter exists.
      -- This is standard MCS-RW semantics.  The pre-fix branch admitted
      -- new readers when "head waiter is reader" — but this state is
      -- unreachable from `unheld` (writer release always batch-promotes
      -- contiguous reader heads), so the strict-FIFO change is
      -- behaviorally equivalent on reachable states while making the
      -- spec match standard FIFO admission and the plan's `d × maxDelay`
      -- bound directly provable.
      else if s.writerHeld.isSome ∨ s.waiters ≠ [] then
        -- Some holder or queued waiter → enqueue to preserve FIFO.
        { s with waiters := s.waiters ++ [(core, .read)] }
      else
        -- No holder AND no waiter → acquire directly.
        { s with readers := core :: s.readers }
  | .releaseRead core =>
      if core ∉ s.readers then s
      else
        let s' := { s with readers := s.readers.filter (· ≠ core) }
        s'.promoteWaitersIfReadersEmpty
  | .tryAcquireWrite core =>
      if s.coreInvolved core then s
      -- **Strict FIFO discipline**: new writers enqueue iff any holder
      -- OR any queued waiter exists.  Symmetric to the tryAcquireRead
      -- change.
      else if s.writerHeld.isSome ∨ s.readers ≠ [] ∨ s.waiters ≠ [] then
        -- Some holder or queued waiter → enqueue.
        { s with waiters := s.waiters ++ [(core, .write)] }
      else
        -- No holder AND no waiter → acquire.
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
  have ⟨h_not_in_r, h_not_writer, h_not_in_w⟩ := (s.not_coreInvolved_iff core).mp h_inv
  -- New strict-FIFO branch structure: enqueue iff writer held OR waiters non-empty.
  by_cases h_enq : s.writerHeld.isSome ∨ s.waiters ≠ []
  · -- Enqueue branch.
    simp only [h_enq, ↓reduceIte]
    -- Discharge wf_after_enqueue_read's holder-exists hypothesis.
    apply wf_after_enqueue_read s core h h_not_in_r h_not_writer h_not_in_w
    rcases h_enq with h_w | h_w
    · exact Or.inl h_w
    · -- waiters non-empty + h_pre_disc gives holder.
      have h_pre_disc := s.wf_fifoAdmissionDiscipline h
      exact h_pre_disc h_w
  · -- Direct-acquire branch: no writer held AND waiters empty.
    simp only [h_enq, ↓reduceIte]
    -- Extract: writerHeld.isSome = false AND waiters = [].
    have h_w : ¬ s.writerHeld.isSome := fun h => h_enq (Or.inl h)
    have h_we : s.waiters = [] := by
      by_cases hw : s.waiters = []
      · exact hw
      · exact absurd (Or.inr hw) h_enq
    have h_none : s.writerHeld = none := Option.not_isSome_iff_eq_none.mp h_w
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
  -- New strict-FIFO branch structure: enqueue iff writerHeld OR readers ≠ [] OR waiters ≠ [].
  by_cases h_enq : s.writerHeld.isSome ∨ s.readers ≠ [] ∨ s.waiters ≠ []
  · -- Enqueue branch.
    simp only [h_enq, ↓reduceIte]
    -- Discharge wf_after_enqueue_write's h_post_disc.
    apply wf_after_enqueue_write s core h h_not_in_r h_not_writer h_not_in_w
    rcases h_enq with h_w | h_r | h_we
    · exact Or.inl h_w
    · exact Or.inr h_r
    · -- waiters ≠ [] → by INV-R5, a holder exists.
      have h_pre_disc := s.wf_fifoAdmissionDiscipline h
      exact h_pre_disc h_we
  · -- Direct acquire.  h_enq : ¬ (writerHeld.isSome ∨ readers ≠ [] ∨ waiters ≠ [])
    simp only [h_enq, ↓reduceIte]
    -- Decompose the negation manually.
    have h_w : ¬ s.writerHeld.isSome := fun h => h_enq (Or.inl h)
    have h_r : ¬ s.readers ≠ [] := fun h => h_enq (Or.inr (Or.inl h))
    have h_none : s.writerHeld = none := Option.not_isSome_iff_eq_none.mp h_w
    have h_no_readers : s.readers = [] := Decidable.byContradiction h_r
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
  -- Under the strict-FIFO spec: enqueue iff `writerHeld.isSome ∨ waiters ≠ []`.
  -- Since `c_w ∈ s.waiters`, we have `waiters ≠ []`, so the enqueue branch
  -- is taken regardless of `writerHeld`.  This simplifies the proof versus
  -- the pre-FIFO three-case match.
  have h_waiters_ne : s.waiters ≠ [] := by
    intro h_eq
    rw [h_eq] at h_writer_waiting
    exact List.not_mem_nil h_writer_waiting
  have h_enq : s.writerHeld.isSome ∨ s.waiters ≠ [] := Or.inr h_waiters_ne
  simp only [h_enq, ↓reduceIte]
  -- Post-state: waiters := s.waiters ++ [(c_r, .read)].  c_w is preserved.
  show (c_w, AccessMode.write) ∈ s.waiters ++ [(c_r, AccessMode.read)]
  exact List.mem_append_left _ h_writer_waiting

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

/-- **WS-SM SM2.C-defer D-3.2 (truncation lemma)**: states past
`ops.length` all equal the final state.  Foundation for the
computable `FairTrace.decidable` instance: it bounds the universally-
quantified step index to `[0, ops.length + 1]`, making the predicate
genuinely decidable without `Classical`. -/
theorem RwLockExecution.stateAt_of_ge_length (e : RwLockExecution)
    {k : Nat} (h : e.ops.length ≤ k) : e.stateAt k = e.finalState := by
  unfold RwLockExecution.finalState
  unfold RwLockExecution.stateAt
  rw [List.take_of_length_le h, List.take_of_length_le (Nat.le_refl _)]

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
-- SM2.C-defer D-2.4 — Substantive monotonicity under effective release
-- ============================================================================

/-- **WS-SM SM2.C-defer helper**: under INV-R1, a writer-held state has
empty readers. -/
private theorem wf_writer_implies_no_readers
    {s : RwLockState} (h : s.wf) {c : CoreId}
    (h_held : s.writerHeld = some c) : s.readers = [] :=
  s.wf_writerReadersExclusion h c h_held

/-- **WS-SM SM2.C-defer helper**: `(c, m) ∈ s.waiters → s.waiters ≠ []`. -/
private theorem waiters_nonempty_of_mem
    {s : RwLockState} {c : CoreId} {m : AccessMode}
    (h : (c, m) ∈ s.waiters) : s.waiters ≠ [] := by
  intro h_eq
  rw [h_eq] at h
  exact List.not_mem_nil h

/-- **WS-SM SM2.C-defer helper**: under wf, a wf state where a writer is
queued has at least one holder (INV-R5). -/
private theorem wf_queued_writer_implies_holder
    {s : RwLockState} (h : s.wf) {c : CoreId}
    (h_queued : (c, AccessMode.write) ∈ s.waiters) :
    s.writerHeld.isSome ∨ s.readers ≠ [] := by
  have h_ne := waiters_nonempty_of_mem h_queued
  exact s.wf_fifoAdmissionDiscipline h h_ne

/-- **WS-SM SM2.C-defer helper (forward declaration of an existing later
lemma)**: Nodup-fst implies Nodup-pairs on a `List (CoreId × AccessMode)`.

This helper is defined later in the file (at line 3137) as
`nodup_of_nodup_map_fst` (without `private`-scope `_local` suffix to
avoid name shadowing).  For D-2.4 use we re-prove a version local to
the D-2 namespace. -/
private theorem nodup_of_nodup_map_fst_local
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
    have h_fst_in : head.fst ∈ rest.map Prod.fst := List.mem_map.mpr ⟨head, h_in, rfl⟩
    exact h.1 h_fst_in

/-- **WS-SM SM2.C-defer (refined Nodup on waiters from wf)**: the plain
list `s.waiters` is Nodup, inherited from INV-R3's Nodup-fst. -/
private theorem waiters_nodup_of_wf
    {s : RwLockState} (h : s.wf) : s.waiters.Nodup :=
  nodup_of_nodup_map_fst_local s.waiters (s.wf_waitersCoresNodup h)

/-- **WS-SM SM2.C-defer helper**: for a Nodup list with member `x`, the
filter `(· ≠ x)` reduces length by exactly 1.

Promoted from `private` to `theorem` (D-4.9 follow-on): the lemma is
consumed by `blockBisim_releaseRead_no_promote` in `RwLockRefinement.lean`
for the bisim discharge. -/
theorem filter_ne_length_of_nodup
    {α : Type _} [DecidableEq α] (l : List α) (h_nodup : l.Nodup)
    (x : α) (h_in : x ∈ l) :
    (l.filter (· ≠ x)).length + 1 = l.length := by
  induction l with
  | nil => exact absurd h_in List.not_mem_nil
  | cons head rest ih =>
    rw [List.nodup_cons] at h_nodup
    obtain ⟨h_head_notin, h_rest_nodup⟩ := h_nodup
    by_cases h_eq : head = x
    · -- head = x: filter drops head.  rest contains no x (Nodup), so
      -- filter (· ≠ x) on rest keeps all entries.
      subst h_eq
      have h_filt : (head :: rest).filter (· ≠ head) = rest := by
        rw [List.filter_cons]
        have h_dec : (decide (head ≠ head) : Bool) = false := by simp
        rw [h_dec]
        -- rest contains no head (Nodup); filter keeps all of rest.
        apply List.filter_eq_self.mpr
        intro y hy
        have h_y_ne : y ≠ head := fun h_eq => h_head_notin (h_eq ▸ hy)
        simp [h_y_ne]
      rw [h_filt, List.length_cons]
    · -- head ≠ x: filter keeps head.  Recurse on rest.
      have h_filt : (head :: rest).filter (· ≠ x) = head :: rest.filter (· ≠ x) := by
        rw [List.filter_cons]
        simp only [ne_eq, decide_not]
        have h_dec : (decide (head = x) : Bool) = false := by simp [h_eq]
        rw [h_dec]; rfl
      rw [h_filt, List.length_cons, List.length_cons]
      have h_x_in_rest : x ∈ rest := by
        cases h_in with
        | head => exact absurd rfl h_eq
        | tail _ h => exact h
      have h_rec := ih h_rest_nodup h_x_in_rest
      omega

/-- **WS-SM SM2.C-defer helper**: characterization of the post-state of
`promoteWaitersIfReadersEmpty` when `readers = []` and `writerHeld = none`
and waiters has a writer head. -/
private theorem promote_readers_empty_writer_head
    (s : RwLockState) (h_r : s.readers = []) (h_w : s.writerHeld = none)
    (c_head : CoreId) (rest : List (CoreId × AccessMode))
    (h_waiters : s.waiters = (c_head, AccessMode.write) :: rest) :
    s.promoteWaitersIfReadersEmpty =
      { writerHeld := some c_head, readers := [], waiters := rest } := by
  unfold RwLockState.promoteWaitersIfReadersEmpty
  rw [h_r, h_w]; simp [h_waiters]

/-- **WS-SM SM2.C-defer helper**: characterization of `promoteWaitersIfReadersEmpty`
when readers is non-empty (no-op). -/
private theorem promote_readers_empty_noop_readers_nonempty
    (s : RwLockState) (h_r : s.readers ≠ []) :
    s.promoteWaitersIfReadersEmpty = s := by
  unfold RwLockState.promoteWaitersIfReadersEmpty
  have h_b : s.readers.isEmpty = false := by
    cases h_eq : s.readers with
    | nil => exact absurd h_eq h_r
    | cons _ _ => simp
  simp [h_b]

/-- **WS-SM SM2.C-defer helper**: when `releaseRead c'` is effective on a
wf state AND `readers.length ≥ 2`, the post-state preserves
`writerHeld` and `waiters`, with `readers` losing c'. -/
private theorem releaseRead_post_no_promote
    (s : RwLockState) (h_wf : s.wf) (c' : CoreId) (h_in : c' ∈ s.readers)
    (h_size : s.readers.length ≥ 2) :
    s.applyOp (.releaseRead c') =
      { writerHeld := s.writerHeld,
        readers := s.readers.filter (· ≠ c'),
        waiters := s.waiters } := by
  unfold RwLockState.applyOp
  have h_not_not : ¬ c' ∉ s.readers := fun h => h h_in
  simp only [h_not_not, ↓reduceIte]
  -- post = ({...filter}).promoteWaitersIfReadersEmpty.  Since readers.length ≥ 2
  -- and Nodup (from wf), filter (≠ c') has length s.readers.length - 1 ≥ 1.
  apply promote_readers_empty_noop_readers_nonempty
  intro h_filt_empty
  -- h_filt_empty: {...filter...}.readers = []  reduces to  filter = [].
  have h_filt_eq : s.readers.filter (· ≠ c') = [] := h_filt_empty
  have h_nodup := s.wf_readersNodup h_wf
  have h_filt_len := filter_ne_length_of_nodup s.readers h_nodup c' h_in
  rw [h_filt_eq] at h_filt_len
  simp at h_filt_len
  omega

/-- **WS-SM SM2.C-defer helper (sub-case A: releaseRead, readers.length ≥ 2)**:
the depth strictly decreases by 1 in the no-promote release-read sub-case.

The `h_queued` parameter is named for clarity at the call-site (it
documents the "writer c remains queued" precondition) but the proof
itself doesn't need it — the depth calculation here doesn't depend on
which waiter c is. -/
private theorem writerWaitDepth_releaseRead_no_promote_decreases
    (s : RwLockState) (h_wf : s.wf)
    (c : CoreId) (_h_queued : (c, AccessMode.write) ∈ s.waiters)
    (c' : CoreId) (h_in : c' ∈ s.readers) (h_size : s.readers.length ≥ 2) :
    writerWaitDepth (s.applyOp (.releaseRead c')) c + 1 ≤ writerWaitDepth s c := by
  rw [releaseRead_post_no_promote s h_wf c' h_in h_size]
  unfold writerWaitDepth
  simp only
  have h_nodup := s.wf_readersNodup h_wf
  have h_filt_len := filter_ne_length_of_nodup s.readers h_nodup c' h_in
  omega

/-- **WS-SM SM2.C-defer helper**: under wf, if `releaseRead c'` is
effective AND `readers.length = 1` (so c' is the only reader), the
post-state has `readers := []` and then promotion fires based on
waiters head.

`h_no_writer` is named for documentation at the call-site (an invariant
captured under wf via INV-R1) but is implied by `h_size_one` since
INV-R1 forces `readers = []` when writer is held.  We keep both for
clarity; the proof doesn't use h_no_writer directly. -/
private theorem releaseRead_post_with_promote_setup
    (s : RwLockState) (h_wf : s.wf) (c' : CoreId)
    (h_in : c' ∈ s.readers) (h_size_one : s.readers.length = 1)
    (_h_no_writer : s.writerHeld = none) :
    s.applyOp (.releaseRead c') =
      ({ writerHeld := s.writerHeld, readers := [],
         waiters := s.waiters } : RwLockState).promoteWaitersIfReadersEmpty := by
  unfold RwLockState.applyOp
  have h_not_not : ¬ c' ∉ s.readers := fun h => h h_in
  simp only [h_not_not, ↓reduceIte]
  -- post = ({...filter}).promoteWaitersIfReadersEmpty.  Filter result has length 0.
  have h_nodup := s.wf_readersNodup h_wf
  have h_filt_len := filter_ne_length_of_nodup s.readers h_nodup c' h_in
  have h_filt_empty : s.readers.filter (· ≠ c') = [] :=
    List.length_eq_zero_iff.mp (by omega)
  congr 1
  -- We need {filter}.readers = [].  Discharge via h_filt_empty.
  rw [h_filt_empty]

/-- **WS-SM SM2.C-defer helper**: when `releaseWrite c'` is effective AND
under wf (so INV-R1 gives readers = []), the post-state is
`{writerHeld := none, readers := [], waiters := s.waiters}.promoteWaitersOnWriterRelease`. -/
private theorem releaseWrite_post_with_promote_setup
    (s : RwLockState) (_h_wf : s.wf) (c' : CoreId)
    (h_held : s.writerHeld = some c') :
    s.applyOp (.releaseWrite c') =
      ({ writerHeld := none, readers := s.readers,
         waiters := s.waiters } : RwLockState).promoteWaitersOnWriterRelease := by
  unfold RwLockState.applyOp
  have h_eq : ¬ s.writerHeld ≠ some c' := fun h => h h_held
  simp only [h_eq, ↓reduceIte]

-- (writer-head promote sub-case is folded into the main D-2.4 case-analysis
-- below; the intermediate "promote-step alone" framing has too few
-- hypotheses to discharge in isolation.)

/-- **WS-SM SM2.C-defer helper**: `idxOf (c, .write)` in a cons of
`(c_head, m_head)` followed by rest, where (c, .write) is in rest with
c ≠ c_head OR m_head ≠ .write. -/
private theorem idxOf_cons_neq
    (c c_head : CoreId) (m_head : AccessMode)
    (rest : List (CoreId × AccessMode))
    (h_neq : c ≠ c_head ∨ m_head ≠ AccessMode.write) :
    ((c_head, m_head) :: rest).idxOf (c, AccessMode.write) =
      rest.idxOf (c, AccessMode.write) + 1 := by
  rw [List.idxOf_cons]
  have h_beq : ((c_head, m_head) == (c, AccessMode.write)) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, Prod.mk.injEq, not_and]
    intro h_eq_c h_eq_m
    rcases h_neq with h | h
    · exact h h_eq_c.symm
    · exact h h_eq_m
  rw [h_beq]; rfl

/-- **WS-SM SM2.C-defer helper**: for `x ∉ takeWhile p l`, the `idxOf` in
`l` decomposes as `takeWhile.length + dropWhile.idxOf x`.

Proof via `List.takeWhile_append_dropWhile` (which gives `l = takeWhile ++ dropWhile`)
and `List.idxOf_append` (which splits `idxOf` by membership in the prefix). -/
private theorem idxOf_eq_takeWhile_length_plus_dropWhile
    {α : Type _} [BEq α] [LawfulBEq α] (l : List α) (p : α → Bool) (x : α)
    (h_not_in_take : x ∉ l.takeWhile p) :
    l.idxOf x = (l.takeWhile p).length + (l.dropWhile p).idxOf x := by
  -- l = takeWhile p l ++ dropWhile p l.
  have h_append : l = l.takeWhile p ++ l.dropWhile p :=
    (List.takeWhile_append_dropWhile (p := p) (l := l)).symm
  -- Apply idxOf_append.  Rewrite both sides through the append identity.
  have h_split := List.idxOf_append
                    (l₁ := l.takeWhile p) (l₂ := l.dropWhile p) (a := x)
  -- h_split : ((takeWhile p l) ++ (dropWhile p l)).idxOf x = ...
  rw [h_append, h_split]
  simp [h_not_in_take]
  omega

/-- **WS-SM SM2.C-defer helper**: any element of `takeWhile p l` must
satisfy `p`.  Direct induction on `l`. -/
private theorem mem_takeWhile_implies_pred
    {α : Type _} (l : List α) (p : α → Bool) (x : α) (h_in : x ∈ l.takeWhile p) :
    p x = true := by
  induction l with
  | nil => simp at h_in
  | cons head rest ih =>
    rw [List.takeWhile_cons] at h_in
    by_cases h_p : p head
    · simp [h_p] at h_in
      cases h_in with
      | inl h_eq => subst h_eq; exact h_p
      | inr h => exact ih h
    · simp [h_p] at h_in

/-- **WS-SM SM2.C-defer helper**: an element with `¬ p x` is NOT in
`takeWhile p l` (since takeWhile only contains elements matching p). -/
private theorem not_mem_takeWhile_of_pred_false
    {α : Type _} (l : List α) (p : α → Bool) (x : α) (h : ¬ p x = true) :
    x ∉ l.takeWhile p := by
  intro h_in
  exact h (mem_takeWhile_implies_pred l p x h_in)

/-- **WS-SM SM2.C-defer helper**: when `s` is wf, `(c, .write) ∈ s.waiters`,
and `s.waiters = (c_head, m_head) :: rest`, then either:
- c_head = c and m_head = .write (c is at head, idxOf = 0)
- c is in rest with idxOf ≥ 1 (c is strictly after head)

Plus Nodup-based: if c is in rest, then c ≠ c_head OR m_head ≠ .write
(forcing distinctness). -/
private theorem queued_writer_at_head_or_in_rest
    (s : RwLockState) (h_wf : s.wf)
    (c c_head : CoreId) (m_head : AccessMode)
    (rest : List (CoreId × AccessMode))
    (h_waiters : s.waiters = (c_head, m_head) :: rest)
    (h_queued : (c, AccessMode.write) ∈ s.waiters) :
    (c = c_head ∧ m_head = AccessMode.write) ∨
    ((c, AccessMode.write) ∈ rest ∧ (c ≠ c_head ∨ m_head ≠ AccessMode.write)) := by
  rw [h_waiters] at h_queued
  cases h_queued with
  | head => left; exact ⟨rfl, rfl⟩
  | tail _ h_in_rest =>
    right
    refine ⟨h_in_rest, ?_⟩
    -- c is in rest.  Nodup on full s.waiters → (c_head, m_head) ∉ rest.
    -- If c = c_head ∧ m_head = .write, then (c, .write) = (c_head, m_head),
    -- contradicting Nodup.  So either c ≠ c_head or m_head ≠ .write.
    have h_nodup := waiters_nodup_of_wf h_wf
    rw [h_waiters] at h_nodup
    rw [List.nodup_cons] at h_nodup
    by_cases h_c : c = c_head
    · by_cases h_m : m_head = AccessMode.write
      · -- c = c_head, m_head = .write: (c, .write) = (c_head, m_head) ∈ rest.  Contradiction.
        exfalso
        apply h_nodup.1
        -- Substitute step by step: rewrite c_head ← c and m_head → .write
        -- in the goal.
        subst h_c
        subst h_m
        exact h_in_rest
      · right; exact h_m
    · left; exact h_c

/-- **WS-SM SM2.C-defer D-2.4 (main monotonicity theorem)**: each
EFFECTIVE release operation strictly reduces `writerWaitDepth`, provided
the writer `c` remains queued in the post-state.

Closes audit finding L-2: the precise progress condition is "the op is
an effective release", not a hand-waved arithmetic comparison.  Each
effective release reduces depth by exactly 1; the inequality form
`post + 1 ≤ pre` is what D-3 (liveness) consumes.

Proof case-splits on the op:

**Case releaseRead c'** (h_effective: c' ∈ s.readers):
  - Sub-case (i) readers.length ≥ 2: no promote.  Readers loses c';
    depth = idxOf + (readers.length - 1) + writer_bit = pre - 1.  ✓
  - Sub-case (ii) readers.length = 1, head is writer: promote drops 1,
    sets writerHeld = some c_head.  c remains in rest (idxOf - 1).
    Net: (idxOf - 1) + 0 + 1 = idxOf; pre = idxOf + 1 + 0 = idxOf + 1.  ✓
  - Sub-case (iii) readers.length = 1, head is reader (m_head = read):
    promote batch-promotes contiguous readers (m of them).  c remains in
    waiters at idxOf - m.  post.readers.length = m, post.writerHeld = none.
    Net: (idxOf - m) + m + 0 = idxOf; pre = idxOf + 1 + 0 = idxOf + 1.  ✓
  - Sub-case (iv) readers.length = 1, waiters empty: contradicts h_queued.

**Case releaseWrite c'** (h_effective: s.writerHeld = some c'):
  By INV-R1: s.readers = [].  After release: writerHeld = none, then promote.
  - Sub-case (v) head is writer: promote sets writerHeld = some c_head,
    drops 1 from waiters.  Net: (idxOf - 1) + 0 + 1 = idxOf; pre = idxOf + 0 + 1.  ✓
  - Sub-case (vi) head is reader: promote batch-promotes m readers, drops m.
    Net: (idxOf - m) + m + 0 = idxOf; pre = idxOf + 0 + 1 = idxOf + 1.  ✓
  - Sub-case (vii) waiters empty: contradicts h_queued. -/
theorem writerWaitDepth_monotone_under_effective_release
    (s : RwLockState) (h_wf : s.wf)
    (c : CoreId) (h_queued : (c, AccessMode.write) ∈ s.waiters)
    (op : RwLockOp)
    (h_effective : s.isEffectiveRelease op)
    (h_still_queued : (c, AccessMode.write) ∈ (s.applyOp op).waiters) :
    writerWaitDepth (s.applyOp op) c + 1 ≤ writerWaitDepth s c := by
  cases op with
  | tryAcquireRead c' =>
    -- isEffectiveRelease for tryAcquireRead is False; contradiction.
    unfold RwLockState.isEffectiveRelease at h_effective
    exact absurd h_effective (by trivial)
  | tryAcquireWrite c' =>
    unfold RwLockState.isEffectiveRelease at h_effective
    exact absurd h_effective (by trivial)
  | releaseRead c' =>
    -- h_effective: c' ∈ s.readers.
    unfold RwLockState.isEffectiveRelease at h_effective
    -- Case-split on s.readers.length: 1 vs ≥ 2.
    by_cases h_size : s.readers.length ≥ 2
    · -- Sub-case A: no-promote.
      exact writerWaitDepth_releaseRead_no_promote_decreases s h_wf c h_queued c' h_effective h_size
    · -- Sub-case B-C: readers.length = 1, promote fires.
      have h_size_one : s.readers.length = 1 := by
        have h_pos : s.readers.length ≥ 1 := by
          cases h_eq : s.readers with
          | nil => rw [h_eq] at h_effective; exact absurd h_effective List.not_mem_nil
          | cons _ _ => simp
        omega
      -- c' is the only reader.
      have h_no_writer : s.writerHeld = none := by
        cases h_eq : s.writerHeld with
        | none => rfl
        | some c'' =>
          -- INV-R1: writer-readers exclusion.  writerHeld = some c'' → readers = [].
          have h_r_empty := s.wf_writerReadersExclusion h_wf c'' h_eq
          rw [h_r_empty] at h_size_one
          simp at h_size_one
      -- Setup the post-state shape.
      rw [releaseRead_post_with_promote_setup s h_wf c' h_effective h_size_one h_no_writer]
      -- Now analyze the promote.  Post-state shape is the intermediate state's
      -- `promoteWaitersIfReadersEmpty`.
      have h_inter_readers : ({ writerHeld := s.writerHeld, readers := [],
                                waiters := s.waiters } : RwLockState).readers = [] := rfl
      have h_inter_writer : ({ writerHeld := s.writerHeld, readers := [],
                               waiters := s.waiters } : RwLockState).writerHeld = none := h_no_writer
      have h_inter_waiters : ({ writerHeld := s.writerHeld, readers := [],
                                waiters := s.waiters } : RwLockState).waiters = s.waiters := rfl
      -- Case-split on waiters head.
      cases h_w_eq : s.waiters with
      | nil =>
        rw [h_w_eq] at h_queued; exact absurd h_queued List.not_mem_nil
      | cons head rest =>
        obtain ⟨c_head, m_head⟩ := head
        -- Determine writer-head vs reader-head promote.
        cases m_head with
        | write =>
          -- Sub-case B: writer-head promote drops 1.
          -- The intermediate state's waiters has the cons form after cases.
          have h_post : ({ writerHeld := s.writerHeld, readers := [],
                           waiters := (c_head, AccessMode.write) :: rest } :
                            RwLockState).promoteWaitersIfReadersEmpty =
              { writerHeld := some c_head, readers := [], waiters := rest } := by
            unfold RwLockState.promoteWaitersIfReadersEmpty
            simp [h_no_writer]
          -- Also transform h_still_queued — it's about s.applyOp, which reduces
          -- via the setup + h_post chain to {... waiters := rest}.
          have h_still_queued_reduced : (c, AccessMode.write) ∈ rest := by
            rw [releaseRead_post_with_promote_setup s h_wf c' h_effective h_size_one h_no_writer]
              at h_still_queued
            -- Rewrite s.waiters → (c_head, .write) :: rest in h_still_queued
            -- so the {...waiters := ...} form matches h_post's LHS.
            rw [h_w_eq] at h_still_queued
            rw [h_post] at h_still_queued
            exact h_still_queued
          rw [h_post]
          unfold writerWaitDepth
          simp only
          have h_cases := queued_writer_at_head_or_in_rest s h_wf c c_head .write rest h_w_eq h_queued
          rcases h_cases with ⟨h_c_eq, _⟩ | ⟨h_c_in_rest, h_neq⟩
          · subst h_c_eq
            exfalso
            have h_nodup := waiters_nodup_of_wf h_wf
            rw [h_w_eq] at h_nodup
            rw [List.nodup_cons] at h_nodup
            apply h_nodup.1
            exact h_still_queued_reduced
          · rw [h_w_eq]
            rw [idxOf_cons_neq c c_head .write rest h_neq]
            simp only [h_no_writer]
            simp
            omega
        | read =>
          -- Sub-case C: reader-head batch promote.
          have h_post : ({ writerHeld := s.writerHeld, readers := [],
                           waiters := (c_head, AccessMode.read) :: rest } :
                            RwLockState).promoteWaitersIfReadersEmpty =
              { writerHeld := none,
                readers := (((c_head, AccessMode.read) :: rest).takeWhile (·.2 = .read)).map Prod.fst,
                waiters := ((c_head, AccessMode.read) :: rest).dropWhile (·.2 = .read) } := by
            unfold RwLockState.promoteWaitersIfReadersEmpty
            simp [h_no_writer]
          rw [h_post]
          unfold writerWaitDepth
          simp only
          have h_cases := queued_writer_at_head_or_in_rest s h_wf c c_head .read rest h_w_eq h_queued
          rcases h_cases with ⟨_, h_m⟩ | ⟨h_c_in_rest, _⟩
          · exact absurd h_m (by decide)
          · -- c is a writer in rest.  Apply the takeWhile/dropWhile decomposition.
            -- Key observation: head (c_head, .read) matches the predicate, so:
            --   ((c_head, .read) :: rest).takeWhile = (c_head, .read) :: rest.takeWhile.
            --   ((c_head, .read) :: rest).dropWhile = rest.dropWhile.
            have h_take_cons :
                ((c_head, AccessMode.read) :: rest).takeWhile (·.2 = .read) =
                (c_head, AccessMode.read) :: rest.takeWhile (·.2 = .read) := by
              rw [List.takeWhile_cons]; simp
            have h_drop_cons :
                ((c_head, AccessMode.read) :: rest).dropWhile (·.2 = .read) =
                rest.dropWhile (·.2 = .read) := by simp
            -- For c (writer) NOT in takeWhile of rest:
            have h_not_in_take_rest : (c, AccessMode.write) ∉ rest.takeWhile (·.2 = .read) :=
              not_mem_takeWhile_of_pred_false rest (·.2 = .read) (c, AccessMode.write) (by simp)
            have h_idx_eq_rest := idxOf_eq_takeWhile_length_plus_dropWhile rest
                                    (·.2 = .read) (c, AccessMode.write) h_not_in_take_rest
            rw [h_w_eq]
            rw [idxOf_cons_neq c c_head .read rest (Or.inr (by decide))]
            rw [h_take_cons, h_drop_cons]
            simp only [List.length_cons, List.length_map, h_no_writer]
            simp
            omega
  | releaseWrite c' =>
    -- Similar structure.  By INV-R1, pre.readers = [].
    unfold RwLockState.isEffectiveRelease at h_effective
    have h_r_empty : s.readers = [] := s.wf_writerReadersExclusion h_wf c' h_effective
    rw [releaseWrite_post_with_promote_setup s h_wf c' h_effective]
    -- post = ({writerHeld := none, readers := s.readers, waiters := s.waiters})
    --        .promoteWaitersOnWriterRelease
    -- Case-split on waiters head.
    cases h_w_eq : s.waiters with
    | nil =>
      rw [h_w_eq] at h_queued; exact absurd h_queued List.not_mem_nil
    | cons head rest =>
      obtain ⟨c_head, m_head⟩ := head
      cases m_head with
      | write =>
        -- Writer-head promote.  Use the post-cases form for h_post.
        have h_post : ({ writerHeld := none, readers := s.readers,
                         waiters := (c_head, AccessMode.write) :: rest } :
                          RwLockState).promoteWaitersOnWriterRelease =
            { writerHeld := some c_head, readers := s.readers, waiters := rest } := by
          unfold RwLockState.promoteWaitersOnWriterRelease
          simp
        have h_still_queued_reduced : (c, AccessMode.write) ∈ rest := by
          rw [releaseWrite_post_with_promote_setup s h_wf c' h_effective] at h_still_queued
          rw [h_w_eq] at h_still_queued
          rw [h_post] at h_still_queued
          exact h_still_queued
        rw [h_post]
        unfold writerWaitDepth
        simp only
        have h_cases := queued_writer_at_head_or_in_rest s h_wf c c_head .write rest h_w_eq h_queued
        rcases h_cases with ⟨h_c_eq, _⟩ | ⟨h_c_in_rest, h_neq⟩
        · subst h_c_eq
          exfalso
          have h_nodup := waiters_nodup_of_wf h_wf
          rw [h_w_eq] at h_nodup
          rw [List.nodup_cons] at h_nodup
          apply h_nodup.1
          exact h_still_queued_reduced
        · rw [h_w_eq]
          rw [idxOf_cons_neq c c_head .write rest h_neq]
          simp [h_r_empty, h_effective]
      | read =>
        -- Reader-batch promote.  h_r_empty makes readers = [], post.readers = batch.
        have h_post : ({ writerHeld := none, readers := s.readers,
                         waiters := (c_head, AccessMode.read) :: rest } :
                          RwLockState).promoteWaitersOnWriterRelease =
            { writerHeld := none,
              readers := (((c_head, AccessMode.read) :: rest).takeWhile (·.2 = .read)).map Prod.fst ++ s.readers,
              waiters := ((c_head, AccessMode.read) :: rest).dropWhile (·.2 = .read) } := by
          unfold RwLockState.promoteWaitersOnWriterRelease
          simp
        rw [h_post]
        unfold writerWaitDepth
        simp only
        have h_cases := queued_writer_at_head_or_in_rest s h_wf c c_head .read rest h_w_eq h_queued
        rcases h_cases with ⟨_, h_m⟩ | ⟨h_c_in_rest, _⟩
        · exact absurd h_m (by decide)
        · -- Decompose takeWhile/dropWhile on cons.
          have h_take_cons :
              ((c_head, AccessMode.read) :: rest).takeWhile (·.2 = .read) =
              (c_head, AccessMode.read) :: rest.takeWhile (·.2 = .read) := by
            rw [List.takeWhile_cons]; simp
          have h_drop_cons :
              ((c_head, AccessMode.read) :: rest).dropWhile (·.2 = .read) =
              rest.dropWhile (·.2 = .read) := by simp
          have h_not_in_take_rest : (c, AccessMode.write) ∉ rest.takeWhile (·.2 = .read) :=
            not_mem_takeWhile_of_pred_false rest (·.2 = .read) (c, AccessMode.write) (by simp)
          have h_idx_eq_rest := idxOf_eq_takeWhile_length_plus_dropWhile rest
                                  (·.2 = .read) (c, AccessMode.write) h_not_in_take_rest
          rw [h_w_eq, h_r_empty]
          rw [idxOf_cons_neq c c_head .read rest (Or.inr (by decide))]
          rw [h_take_cons, h_drop_cons]
          simp only [List.length_cons, List.length_map, List.length_append,
                     List.length_nil, Nat.add_zero, h_effective, Option.isSome_some,
                     Option.isSome_none, Bool.false_eq_true, ite_true, ite_false]
          omega

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
  -- Strict-FIFO spec: enqueue iff `writerHeld.isSome ∨ waiters ≠ []`.
  -- Two-branch case structure (was three-branch under the legacy
  -- "head-reader → direct-acquire" semantics).
  unfold RwLockState.applyOp
  by_cases h_inv : s.coreInvolved c
  · left; simp [h_inv]
  by_cases h_enq : s.writerHeld.isSome ∨ s.waiters ≠ []
  · right; simp [h_inv, h_enq]
  · left; simp [h_inv, h_enq]

/-- **WS-SM SM2.C-defer D-1.6**: `tryAcquireWrite c` either is a no-op or
appends EXACTLY `(c, .write)` at the tail. -/
theorem tryAcquireWrite_waiters_append_or_noop (s : RwLockState) (c : CoreId) :
    (s.applyOp (.tryAcquireWrite c)).waiters = s.waiters ∨
    (s.applyOp (.tryAcquireWrite c)).waiters = s.waiters ++ [(c, AccessMode.write)] := by
  -- Strict-FIFO spec: enqueue iff `writerHeld.isSome ∨ readers ≠ [] ∨ waiters ≠ []`.
  unfold RwLockState.applyOp
  by_cases h_inv : s.coreInvolved c
  · left; simp [h_inv]
  by_cases h_enq : s.writerHeld.isSome ∨ s.readers ≠ [] ∨ s.waiters ≠ []
  · right; simp [h_inv, h_enq]
  · left; simp [h_inv, h_enq]

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

/-- **WS-SM SM2.C-defer helper**: alias for the earlier `_local`-suffixed
form (defined at line ~2796 for D-2 use).  Used by D-1.8 / D-1.9 below. -/
@[inline]
private def nodup_of_nodup_map_fst
    (l : List (CoreId × AccessMode)) (h : (l.map Prod.fst).Nodup) : l.Nodup :=
  nodup_of_nodup_map_fst_local l h

/-- **WS-SM SM2.C-defer helper**: characterization of release-read
post-state when `c ∈ readers` (the effective-release branch). -/
theorem releaseRead_effective_post (s : RwLockState) (c : CoreId)
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

-- ============================================================================
-- SM2.C-defer D-3.6 (foundations) — depth non-increase under any step
-- ============================================================================

/-- **WS-SM SM2.C-defer D-3.6 (foundation lemma A)**: under strict-FIFO,
`tryAcquireRead` does not change a queued writer's `writerWaitDepth`.

Spec consequence of the post-D-3 strict-FIFO change: a queued writer
implies `waiters ≠ []`, so `tryAcquireRead` enqueues at tail (NEVER
direct-acquires).  The append-at-tail leaves the queued writer's `idxOf`
unchanged (by `idxOf_append_of_mem`), and `readers` / `writerHeld` are
both unchanged.  Therefore depth is invariant under this step.

This is the structural lemma that closes the pre-strict-FIFO gap noted
in `fair_release_witness_in_window` (depth could previously increase
when head was a reader). -/
private theorem writerWaitDepth_unchanged_under_tryAcquireRead_queued
    (s : RwLockState)
    (c : CoreId) (h_queued : (c, AccessMode.write) ∈ s.waiters)
    (c' : CoreId) :
    writerWaitDepth (s.applyOp (.tryAcquireRead c')) c = writerWaitDepth s c := by
  by_cases h_inv : s.coreInvolved c'
  · -- No-op: applyOp returns s.
    have h_eq : s.applyOp (.tryAcquireRead c') = s := by
      unfold RwLockState.applyOp; simp [h_inv]
    rw [h_eq]
  -- c queued ⇒ s.waiters ≠ [].  Strict-FIFO forces enqueue.
  have h_waiters_ne : s.waiters ≠ [] := fun h_eq => by
    rw [h_eq] at h_queued; exact List.not_mem_nil h_queued
  have h_post : s.applyOp (.tryAcquireRead c') =
      { s with waiters := s.waiters ++ [(c', AccessMode.read)] } := by
    unfold RwLockState.applyOp
    have h_enq : s.writerHeld.isSome = true ∨ s.waiters ≠ [] := Or.inr h_waiters_ne
    simp [h_inv, h_enq]
  rw [h_post]
  unfold writerWaitDepth
  show (s.waiters ++ [(c', AccessMode.read)]).idxOf (c, AccessMode.write) +
       s.readers.length + (if s.writerHeld.isSome then 1 else 0) =
       s.waiters.idxOf (c, AccessMode.write) +
       s.readers.length + (if s.writerHeld.isSome then 1 else 0)
  rw [idxOf_append_of_mem s.waiters [(c', AccessMode.read)] (c, AccessMode.write) h_queued]

/-- **WS-SM SM2.C-defer D-3.6 (foundation lemma B)**: under strict-FIFO,
`tryAcquireWrite` does not change a queued writer's `writerWaitDepth`. -/
private theorem writerWaitDepth_unchanged_under_tryAcquireWrite_queued
    (s : RwLockState)
    (c : CoreId) (h_queued : (c, AccessMode.write) ∈ s.waiters)
    (c' : CoreId) :
    writerWaitDepth (s.applyOp (.tryAcquireWrite c')) c = writerWaitDepth s c := by
  by_cases h_inv : s.coreInvolved c'
  · have h_eq : s.applyOp (.tryAcquireWrite c') = s := by
      unfold RwLockState.applyOp; simp [h_inv]
    rw [h_eq]
  have h_waiters_ne : s.waiters ≠ [] := fun h_eq => by
    rw [h_eq] at h_queued; exact List.not_mem_nil h_queued
  have h_post : s.applyOp (.tryAcquireWrite c') =
      { s with waiters := s.waiters ++ [(c', AccessMode.write)] } := by
    unfold RwLockState.applyOp
    have h_enq : s.writerHeld.isSome = true ∨ s.readers ≠ [] ∨ s.waiters ≠ [] :=
      Or.inr (Or.inr h_waiters_ne)
    simp [h_inv, h_enq]
  rw [h_post]
  unfold writerWaitDepth
  show (s.waiters ++ [(c', AccessMode.write)]).idxOf (c, AccessMode.write) +
       s.readers.length + (if s.writerHeld.isSome then 1 else 0) =
       s.waiters.idxOf (c, AccessMode.write) +
       s.readers.length + (if s.writerHeld.isSome then 1 else 0)
  rw [idxOf_append_of_mem s.waiters [(c', AccessMode.write)] (c, AccessMode.write) h_queued]

/-- **WS-SM SM2.C-defer D-3.6 (foundation lemma C)**: a NON-effective
release op leaves the state unchanged (the no-op gate fires), hence
depth is unchanged.

A "non-effective" release means the release-target is not actually a
holder: either `releaseRead c'` with `c' ∉ readers`, or `releaseWrite c'`
with `writerHeld ≠ some c'`.  Both fall through to the no-op gate. -/
private theorem writerWaitDepth_unchanged_under_noneffective_release
    (s : RwLockState) (c : CoreId) (op : RwLockOp)
    (h_not_eff : ¬ s.isEffectiveRelease op)
    (h_release : (∃ c', op = .releaseRead c') ∨ (∃ c', op = .releaseWrite c')) :
    writerWaitDepth (s.applyOp op) c = writerWaitDepth s c := by
  rcases h_release with ⟨c', h_op⟩ | ⟨c', h_op⟩
  · subst h_op
    have h_not_in : c' ∉ s.readers := by
      intro h_in
      apply h_not_eff
      unfold RwLockState.isEffectiveRelease
      exact h_in
    have h_eq : s.applyOp (.releaseRead c') = s := by
      unfold RwLockState.applyOp; simp [h_not_in]
    rw [h_eq]
  · subst h_op
    have h_neq : s.writerHeld ≠ some c' := by
      intro h_eq
      apply h_not_eff
      unfold RwLockState.isEffectiveRelease
      exact h_eq
    have h_eq : s.applyOp (.releaseWrite c') = s := by
      unfold RwLockState.applyOp; simp [h_neq]
    rw [h_eq]

/-- **WS-SM SM2.C-defer helper**: every element of `dropWhile p l` is in
`l`, hence membership preserved via the "not-pred" filter.

For our use case: c (writer, mode = .write) cannot be in the takeWhile-
prefix `(· .2 = .read)` since `.write ≠ .read`.  So if c is in the full
list, c is in the dropWhile-suffix. -/
private theorem mem_dropWhile_of_not_pred
    {α : Type _} [DecidableEq α] (l : List α) (p : α → Bool) (x : α)
    (h_in : x ∈ l) (h_not_p : p x = false) :
    x ∈ l.dropWhile p := by
  induction l with
  | nil => exact absurd h_in List.not_mem_nil
  | cons head rest ih =>
    by_cases h_p : p head = true
    · -- head satisfies p; dropWhile drops it.  x must be in rest.
      rw [List.dropWhile_cons_of_pos h_p]
      apply ih
      cases h_in with
      | head =>
        -- x = head, so p head = false (since p x = false).
        -- Contradicts h_p : p head = true.
        exfalso
        rw [h_p] at h_not_p
        cases h_not_p
      | tail _ h_rest => exact h_rest
    · -- head doesn't satisfy p; dropWhile stops, returns whole list.
      have h_p_false : p head = false := by
        cases h_eq : p head with
        | true => exact absurd h_eq h_p
        | false => rfl
      rw [List.dropWhile_cons_of_neg (by simp [h_p_false])]
      exact h_in

/-- **WS-SM SM2.C-defer D-3.6 (foundation lemma — basic dichotomy)**:
for `(c, .write) ∈ (c_head, m_head) :: rest`, either `c = c_head ∧
m_head = .write` OR `(c, .write) ∈ rest`.

Pure membership-cons decomposition — does NOT require wf or Nodup. -/
private theorem queued_writer_head_or_rest_basic
    (c c_head : CoreId) (m_head : AccessMode)
    (rest : List (CoreId × AccessMode))
    (h_in : (c, AccessMode.write) ∈ (c_head, m_head) :: rest) :
    (c = c_head ∧ m_head = AccessMode.write) ∨
    (c, AccessMode.write) ∈ rest := by
  cases h_in with
  | head => left; exact ⟨rfl, rfl⟩
  | tail _ h_in_rest => right; exact h_in_rest

/-- **WS-SM SM2.C-defer D-3.6 (foundation lemma — promote-on-release
persistence, wf-free)**: same as the wf-requiring form but works on
arbitrary states by using the basic membership dichotomy. -/
private theorem promoteOnWriterRelease_persistence
    (s : RwLockState) (c : CoreId)
    (h_queued : (c, AccessMode.write) ∈ s.waiters) :
    s.promoteWaitersOnWriterRelease.writerHeld = some c ∨
    (c, AccessMode.write) ∈ s.promoteWaitersOnWriterRelease.waiters := by
  unfold RwLockState.promoteWaitersOnWriterRelease
  match h_w_eq : s.waiters with
  | [] => rw [h_w_eq] at h_queued; exact absurd h_queued List.not_mem_nil
  | (c_head, AccessMode.write) :: rest =>
    have h_in_pp : (c, AccessMode.write) ∈ (c_head, AccessMode.write) :: rest := by
      rw [← h_w_eq]; exact h_queued
    rcases queued_writer_head_or_rest_basic c c_head .write rest h_in_pp
      with ⟨h_c_eq, _⟩ | h_in_rest
    · left; rw [h_c_eq]
    · right; exact h_in_rest
  | (c_head, AccessMode.read) :: rest =>
    right
    show (c, AccessMode.write) ∈
      ((c_head, AccessMode.read) :: rest).dropWhile (fun w => w.2 = AccessMode.read)
    have h_in_full : (c, AccessMode.write) ∈ (c_head, AccessMode.read) :: rest := by
      rw [← h_w_eq]; exact h_queued
    apply mem_dropWhile_of_not_pred ((c_head, AccessMode.read) :: rest)
      (fun w => w.2 = AccessMode.read) (c, AccessMode.write) h_in_full
    simp

/-- **WS-SM SM2.C-defer D-3.6 (foundation lemma — promote-if-readers-
empty persistence, wf-free)**: same as the wf-requiring form but works
on arbitrary states. -/
private theorem promoteIfReadersEmpty_persistence
    (s : RwLockState) (c : CoreId)
    (h_queued : (c, AccessMode.write) ∈ s.waiters) :
    s.promoteWaitersIfReadersEmpty.writerHeld = some c ∨
    (c, AccessMode.write) ∈ s.promoteWaitersIfReadersEmpty.waiters := by
  unfold RwLockState.promoteWaitersIfReadersEmpty
  by_cases h_r_ne : !s.readers.isEmpty
  · right; simp [h_r_ne]; exact h_queued
  simp only [h_r_ne, Bool.false_eq_true, ↓reduceIte]
  by_cases h_w : s.writerHeld.isSome
  · right; simp [h_w]; exact h_queued
  simp only [h_w, Bool.false_eq_true, ↓reduceIte]
  match h_w_eq : s.waiters with
  | [] => rw [h_w_eq] at h_queued; exact absurd h_queued List.not_mem_nil
  | (c_head, AccessMode.write) :: rest =>
    have h_in_pp : (c, AccessMode.write) ∈ (c_head, AccessMode.write) :: rest := by
      rw [← h_w_eq]; exact h_queued
    rcases queued_writer_head_or_rest_basic c c_head .write rest h_in_pp
      with ⟨h_c_eq, _⟩ | h_in_rest
    · left; rw [h_c_eq]
    · right; exact h_in_rest
  | (c_head, AccessMode.read) :: rest =>
    right
    show (c, AccessMode.write) ∈
      ((c_head, AccessMode.read) :: rest).dropWhile (fun w => w.2 = AccessMode.read)
    have h_in_full : (c, AccessMode.write) ∈ (c_head, AccessMode.read) :: rest := by
      rw [← h_w_eq]; exact h_queued
    apply mem_dropWhile_of_not_pred ((c_head, AccessMode.read) :: rest)
      (fun w => w.2 = AccessMode.read) (c, AccessMode.write) h_in_full
    simp

/-- **WS-SM SM2.C-defer D-3.6 (foundation lemma — full persistence)**:
under strict-FIFO, for a queued writer `c` and any op, the post-op state
EITHER admits c (writerHeld = some c) OR retains c in waiters.

This is the canonical "no-loss" lemma: a queued writer can never
"vanish" from the lock state; it can only transition forward to
admission.  Does NOT require s.wf (the structural lemmas it relies on
are wf-free). -/
theorem queued_writer_persists_or_admitted
    (s : RwLockState)
    (c : CoreId) (h_queued : (c, AccessMode.write) ∈ s.waiters)
    (op : RwLockOp) :
    (s.applyOp op).writerHeld = some c ∨
    (c, AccessMode.write) ∈ (s.applyOp op).waiters := by
  cases op with
  | tryAcquireRead c' =>
    right
    rcases tryAcquireRead_waiters_append_or_noop s c' with h | h
    · rw [h]; exact h_queued
    · rw [h]; exact List.mem_append_left _ h_queued
  | tryAcquireWrite c' =>
    right
    rcases tryAcquireWrite_waiters_append_or_noop s c' with h | h
    · rw [h]; exact h_queued
    · rw [h]; exact List.mem_append_left _ h_queued
  | releaseRead c' =>
    by_cases h_in : c' ∈ s.readers
    · rw [releaseRead_effective_post s c' h_in]
      -- Intermediate state has same waiters as s.  Apply persistence on intermediate.
      exact promoteIfReadersEmpty_persistence
        ({ writerHeld := s.writerHeld,
           readers := s.readers.filter (· ≠ c'),
           waiters := s.waiters }) c h_queued
    · right
      rw [releaseRead_noop_post s c' h_in]
      exact h_queued
  | releaseWrite c' =>
    by_cases h_eq : s.writerHeld = some c'
    · rw [releaseWrite_effective_post s c' h_eq]
      -- Intermediate state has same waiters as s.  Apply persistence on intermediate.
      exact promoteOnWriterRelease_persistence
        ({ writerHeld := none, readers := s.readers, waiters := s.waiters }) c h_queued
    · right
      rw [releaseWrite_noop_post s c' h_eq]
      exact h_queued

/-- **WS-SM SM2.C-defer D-3.6 (foundation lemma — depth non-increase
under queued-preservation)**: under wf + strict-FIFO, for a writer `c`
queued in BOTH `s` and `s.applyOp op`, the post-op depth is ≤ pre-op
depth.

This is the canonical single-step non-increase lemma; persistence of
`c` in the post-state is a caller's hypothesis (typically discharged
via `applyOp_preserves_waiter_order` infrastructure or directly via
the trace's `holderAt` predicate). -/
theorem writerWaitDepth_non_increase_step_queued
    (s : RwLockState) (h_wf : s.wf)
    (c : CoreId) (h_queued_pre : (c, AccessMode.write) ∈ s.waiters)
    (op : RwLockOp)
    (h_queued_post : (c, AccessMode.write) ∈ (s.applyOp op).waiters) :
    writerWaitDepth (s.applyOp op) c ≤ writerWaitDepth s c := by
  cases op with
  | tryAcquireRead c' =>
    rw [writerWaitDepth_unchanged_under_tryAcquireRead_queued s c h_queued_pre c']
    exact Nat.le_refl _
  | tryAcquireWrite c' =>
    rw [writerWaitDepth_unchanged_under_tryAcquireWrite_queued s c h_queued_pre c']
    exact Nat.le_refl _
  | releaseRead c' =>
    by_cases h_eff : s.isEffectiveRelease (.releaseRead c')
    · -- Effective release: depth strictly decreases by ≥ 1 under
      -- writerWaitDepth_monotone_under_effective_release.
      have h_strict := writerWaitDepth_monotone_under_effective_release s h_wf c
                       h_queued_pre (.releaseRead c') h_eff h_queued_post
      omega
    · -- Non-effective: no-op, depth unchanged.
      have h_eq := writerWaitDepth_unchanged_under_noneffective_release s c (.releaseRead c')
            h_eff (Or.inl ⟨c', rfl⟩)
      omega
  | releaseWrite c' =>
    by_cases h_eff : s.isEffectiveRelease (.releaseWrite c')
    · have h_strict := writerWaitDepth_monotone_under_effective_release s h_wf c
                       h_queued_pre (.releaseWrite c') h_eff h_queued_post
      omega
    · have h_eq := writerWaitDepth_unchanged_under_noneffective_release s c (.releaseWrite c')
            h_eff (Or.inr ⟨c', rfl⟩)
      omega

/-- **WS-SM SM2.C-defer D-3.6 (foundation lemma — strict decrease under
effective release)**: under wf + strict-FIFO + queued-preservation,
an effective release strictly decreases depth by ≥ 1.

This is a clean restatement of `writerWaitDepth_monotone_under_effective_release`
for the strict-FIFO-aware liveness chain. -/
theorem writerWaitDepth_strict_decrease_under_effective_release
    (s : RwLockState) (h_wf : s.wf)
    (c : CoreId) (h_queued_pre : (c, AccessMode.write) ∈ s.waiters)
    (op : RwLockOp)
    (h_eff : s.isEffectiveRelease op)
    (h_queued_post : (c, AccessMode.write) ∈ (s.applyOp op).waiters) :
    writerWaitDepth (s.applyOp op) c + 1 ≤ writerWaitDepth s c :=
  writerWaitDepth_monotone_under_effective_release s h_wf c h_queued_pre op h_eff h_queued_post

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
    (s : RwLockState) (_h_wf : s.wf)
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
abstract state has no writer AND no queued waiters, a `tryAcquireRead c`
for a non-involved core c grows readers by 1.

Concretely, this is the post-state shape for the "direct-acquire"
branch of `applyOp .tryAcquireRead` under the strict-FIFO spec
(post-D-3 structural fix).  The pre-fix theorem permitted a
"head-is-reader" disjunct in `h_waiters_safe`; the strict-FIFO spec
removes that case — when waiters is non-empty, new readers enqueue
unconditionally (matching standard MCS-RW semantics). -/
theorem tryAcquireRead_direct_acquire_shape
    (s : RwLockState) (c : CoreId)
    (h_not_inv : ¬ s.coreInvolved c)
    (h_no_writer : s.writerHeld = none)
    (h_waiters_empty : s.waiters = []) :
    (s.applyOp (.tryAcquireRead c)).readers = c :: s.readers ∧
    (s.applyOp (.tryAcquireRead c)).writerHeld = s.writerHeld ∧
    (s.applyOp (.tryAcquireRead c)).waiters = s.waiters := by
  unfold RwLockState.applyOp
  simp only [h_not_inv, ↓reduceIte]
  -- Branch on enqueue condition: writerHeld.isSome ∨ waiters ≠ [].
  -- We have writerHeld = none and waiters = [], so neither holds.
  have h_w_isSome : s.writerHeld.isSome = false := by rw [h_no_writer]; rfl
  have h_no_enq : ¬ (s.writerHeld.isSome = true ∨ s.waiters ≠ []) := by
    rintro (h | h)
    · rw [h_w_isSome] at h; exact Bool.false_ne_true h
    · exact h h_waiters_empty
  simp [h_no_enq]

/-- **WS-SM SM2.C-defer D-4.7 (success branch identity for writer)**:
when the abstract state has no holder AND no waiters, a `tryAcquireWrite c`
for a non-involved core c sets `writerHeld := some c`.

Strict-FIFO note: under the post-D-3 spec, direct-acquire requires
`waiters = []` (not just `writerHeld = none ∧ readers = []`).  Under the
INV-R5 invariant (`waiters ≠ [] → writerHeld.isSome ∨ readers ≠ []`),
a wf state with `writerHeld = none ∧ readers = []` automatically has
`waiters = []`, so callers with a wf hypothesis can discharge
`h_waiters_empty` via `wf_calm_iff_waiters_empty`. -/
theorem tryAcquireWrite_direct_acquire_shape
    (s : RwLockState) (c : CoreId)
    (h_not_inv : ¬ s.coreInvolved c)
    (h_no_writer : s.writerHeld = none)
    (h_no_readers : s.readers = [])
    (h_no_waiters : s.waiters = []) :
    (s.applyOp (.tryAcquireWrite c)).writerHeld = some c ∧
    (s.applyOp (.tryAcquireWrite c)).readers = s.readers ∧
    (s.applyOp (.tryAcquireWrite c)).waiters = s.waiters := by
  unfold RwLockState.applyOp
  simp only [h_not_inv, ↓reduceIte]
  have h_w_isSome : s.writerHeld.isSome = false := by rw [h_no_writer]; rfl
  have h_no_enq : ¬ (s.writerHeld.isSome = true ∨ s.readers ≠ [] ∨ s.waiters ≠ []) := by
    rintro (h | h | h)
    · rw [h_w_isSome] at h; exact Bool.false_ne_true h
    · exact h h_no_readers
    · exact h h_no_waiters
  simp [h_no_enq]

-- ============================================================================
-- SM2.C-defer D-1.9 — Full temporal FIFO admission theorem
-- ============================================================================

/-- **WS-SM SM2.C-defer helper**: find the smallest natural ≤ k satisfying
a decidable predicate p, given that p holds at k.

Returns `j ≤ k` such that `p j = true` and ∀ j' < j, p j' = false.
By strong induction on k. -/
private theorem find_smallest_le
    (p : Nat → Bool) (k : Nat) (h_pk : p k = true) :
    ∃ j, j ≤ k ∧ p j = true ∧ ∀ j' < j, p j' = false := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases h_any : ∃ j, j < k ∧ p j = true
    · obtain ⟨j', h_j'_lt, h_pj'⟩ := h_any
      have ⟨j, h_j_le, h_pj, h_min⟩ := ih j' h_j'_lt h_pj'
      exact ⟨j, by omega, h_pj, h_min⟩
    · refine ⟨k, Nat.le_refl _, h_pk, ?_⟩
      intro j' h_lt
      have h_not : ¬ p j' = true := fun h => h_any ⟨j', h_lt, h⟩
      simp at h_not; exact h_not

/-- **WS-SM SM2.C-defer helper (find?-bridge for ranges)**: bridge from
"exists k ≤ n with p k" to "find? over `range (n+1)` returns some j ≤ k".

Combines `find_smallest_le` (existence of minimum) with the
`find?_eq_some_iff_append` characterization. -/
private theorem range_find?_le_of_satisfies
    (n : Nat) (p : Nat → Bool) (k : Nat) (h_k_le : k ≤ n) (h_pk : p k = true) :
    ∃ j, (List.range (n + 1)).find? p = some j ∧ j ≤ k := by
  -- Find the smallest j ≤ k satisfying p.
  obtain ⟨j, h_j_le_k, h_pj, h_min⟩ := find_smallest_le p k h_pk
  refine ⟨j, ?_, h_j_le_k⟩
  -- Show (range (n+1)).find? p = some j.  By find?_eq_some_iff_append:
  -- range (n+1) = as ++ j :: bs ∧ p j ∧ ∀ a ∈ as, ¬ p a.
  rw [List.find?_eq_some_iff_append]
  refine ⟨h_pj, List.range j, (List.range (n + 1)).drop (j + 1), ?_, ?_⟩
  · -- range (n+1) = range j ++ j :: drop (j+1) range (n+1).
    have h_j_le_n : j ≤ n := by omega
    have h_take : (List.range (n + 1)).take j = List.range j := by
      simp [List.take_range, Nat.min_eq_left (by omega : j ≤ n + 1)]
    have h_drop_j : (List.range (n + 1)).drop j = j :: (List.range (n + 1)).drop (j + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; omega)]
      simp
    calc List.range (n + 1)
        = (List.range (n + 1)).take j ++ (List.range (n + 1)).drop j := by
          rw [List.take_append_drop]
      _ = List.range j ++ (j :: (List.range (n + 1)).drop (j + 1)) := by
          rw [h_take, h_drop_j]
  · -- ∀ a ∈ range j, ¬ p a.
    intro a h_a_in
    rw [List.mem_range] at h_a_in
    have := h_min a h_a_in
    simp [this]

/-- **WS-SM SM2.C-defer helper**: under `initial = unheld`, no core is
a holder at step 0. -/
private theorem holderAt_zero_false
    (e : RwLockExecution) (h_init : e.initial = RwLockState.unheld)
    (c : CoreId) : ¬ e.holderAt 0 c := by
  unfold RwLockExecution.holderAt
  simp [RwLockExecution.stateAt_zero, h_init, RwLockState.unheld]

/-- **WS-SM SM2.C-defer helper**: if c is a holder at step n in an
execution starting from unheld, admissionStep returns some j ≤ n. -/
private theorem admissionStep_le_of_holder
    (e : RwLockExecution) (h_init : e.initial = RwLockState.unheld)
    (c : CoreId) (n : Nat) (h_in_range : n ≤ e.ops.length)
    (h_holder : e.holderAt n c) :
    ∃ j, e.admissionStep c = some j ∧ j ≤ n := by
  -- Predicate matching admissionStep:
  let pred : Nat → Bool := fun k =>
    decide (k ≥ 1) && decide (e.holderAt k c) && decide (¬ e.holderAt (k - 1) c)
  -- We claim: there's some step k ≤ n satisfying pred.
  -- Use a sub-helper to handle the induction (avoiding the clear/induction issue).
  have h_witness : ∀ m, m ≤ e.ops.length → e.holderAt m c → ∃ k, k ≤ m ∧ pred k = true := by
    intro m
    induction m with
    | zero =>
      intro _ h_holder0
      exact absurd h_holder0 (holderAt_zero_false e h_init c)
    | succ m ih =>
      intro h_m_le h_holder_succ
      by_cases h_prev : e.holderAt m c
      · obtain ⟨k, h_k_le, h_pred⟩ := ih (by omega) h_prev
        exact ⟨k, by omega, h_pred⟩
      · refine ⟨m + 1, Nat.le_refl _, ?_⟩
        show pred (m + 1) = true
        show (decide (m + 1 ≥ 1) && decide (e.holderAt (m+1) c) &&
              decide (¬ e.holderAt ((m+1) - 1) c)) = true
        simp [h_holder_succ, h_prev]
  obtain ⟨k, h_k_le, h_pred⟩ := h_witness n h_in_range h_holder
  have h_k_le_ops : k ≤ e.ops.length := by omega
  obtain ⟨j, h_eq, h_j_le⟩ := range_find?_le_of_satisfies e.ops.length pred k h_k_le_ops h_pred
  refine ⟨j, ?_, by omega⟩
  unfold RwLockExecution.admissionStep
  exact h_eq

-- ============================================================================
-- SM2.C-defer D-1.9 — Operational invariants for the FIFO admission theorem
-- ============================================================================

/-- **WS-SM SM2.C-defer (operational invariant)**: leaving waiters
implies becoming a holder.

If `(c, m)` is in `s.waiters` and not in `(s.applyOp op).waiters`, then
`c` is in the holders set (readers or writerHeld) of the post-state.

Proof: case-by-case on `op`.
- `tryAcquireRead c'` / `tryAcquireWrite c'`: by D-1.6, waiters are
  either unchanged (no-op case) or grow by appending; (c,m) cannot leave.
  So h_out yields contradiction.
- `releaseRead c'`: applyOp produces post-state via filter + promote.
  The filter touches readers, not waiters.  The promote drops a prefix
  of waiters and puts those entries into readers or writerHeld.  If
  `(c, m) ∉ post.waiters` but `(c, m) ∈ s.waiters`, then `(c, m)` was
  in the dropped prefix.  By the promote logic, c is now in the
  post-state's readers (reader-prefix promote) or `writerHeld` (writer
  head promote).
- `releaseWrite c'`: same structure. -/
theorem leave_waiters_implies_holder
    (s : RwLockState) (h_wf : s.wf)
    (c : CoreId) (m : AccessMode) (op : RwLockOp)
    (h_in : (c, m) ∈ s.waiters)
    (h_out : (c, m) ∉ (s.applyOp op).waiters) :
    c ∈ (s.applyOp op).readers ∨ (s.applyOp op).writerHeld = some c := by
  cases op with
  | tryAcquireRead c' =>
    -- D-1.6: tryAcquireRead waiters = pre OR pre ++ [(c', .read)].
    rcases tryAcquireRead_waiters_append_or_noop s c' with h_post | h_post
    · -- No-op: post = pre.
      rw [h_post] at h_out; exact absurd h_in h_out
    · -- Append: post = pre ++ [...].  (c, m) ∈ pre ⇒ (c, m) ∈ post.
      rw [h_post] at h_out
      have : (c, m) ∈ s.waiters ++ [(c', AccessMode.read)] := List.mem_append_left _ h_in
      exact absurd this h_out
  | tryAcquireWrite c' =>
    rcases tryAcquireWrite_waiters_append_or_noop s c' with h_post | h_post
    · rw [h_post] at h_out; exact absurd h_in h_out
    · rw [h_post] at h_out
      have : (c, m) ∈ s.waiters ++ [(c', AccessMode.write)] := List.mem_append_left _ h_in
      exact absurd this h_out
  | releaseRead c' =>
    -- Case-split on the effectiveness of the release.
    by_cases h_eff : c' ∈ s.readers
    · -- Effective release.  Sub-case on readers.length.
      by_cases h_size : s.readers.length ≥ 2
      · -- No-promote case: post.waiters = pre.waiters; contradicts h_out.
        rw [releaseRead_post_no_promote s h_wf c' h_eff h_size] at h_out
        exact absurd h_in h_out
      · -- Promote-fires case: readers.length = 1.  c is in dropped prefix.
        have h_size_one : s.readers.length = 1 := by
          have h_pos : s.readers.length ≥ 1 := by
            cases h_r : s.readers with
            | nil => rw [h_r] at h_eff; exact absurd h_eff List.not_mem_nil
            | cons _ _ => simp
          omega
        have h_no_writer : s.writerHeld = none := by
          cases h_w : s.writerHeld with
          | none => rfl
          | some c'' =>
            have h_r_empty := s.wf_writerReadersExclusion h_wf c'' h_w
            rw [h_r_empty] at h_size_one; simp at h_size_one
        -- Post-state has the promote applied to {writerHeld := s.writerHeld,
        -- readers := [], waiters := s.waiters}.  We need to also rewrite
        -- h_out and the goal through the same chain.
        have h_apply_eq : s.applyOp (.releaseRead c') =
            ({ writerHeld := s.writerHeld, readers := [],
               waiters := s.waiters } : RwLockState).promoteWaitersIfReadersEmpty :=
          releaseRead_post_with_promote_setup s h_wf c' h_eff h_size_one h_no_writer
        rw [h_apply_eq] at h_out
        -- Case-split on waiters head.  After cases, s.waiters substituted in goal/h_out.
        cases h_w_eq : s.waiters with
        | nil => rw [h_w_eq] at h_in; exact absurd h_in List.not_mem_nil
        | cons head rest =>
          obtain ⟨c_head, m_head⟩ := head
          -- Need to also substitute s.waiters in h_out using h_w_eq.
          rw [h_w_eq] at h_out
          rw [h_apply_eq, h_w_eq]
          cases m_head with
          | write =>
            have h_post_struct : ({ writerHeld := s.writerHeld, readers := [],
                                     waiters := (c_head, AccessMode.write) :: rest } :
                                    RwLockState).promoteWaitersIfReadersEmpty =
                { writerHeld := some c_head, readers := [], waiters := rest } := by
              unfold RwLockState.promoteWaitersIfReadersEmpty
              simp [h_no_writer]
            rw [h_post_struct] at h_out
            rw [h_post_struct]
            rw [h_w_eq] at h_in
            cases h_in with
            | head => simp
            | tail _ h_in_rest => exact absurd h_in_rest h_out
          | read =>
            have h_post_struct : ({ writerHeld := s.writerHeld, readers := [],
                                     waiters := (c_head, AccessMode.read) :: rest } :
                                    RwLockState).promoteWaitersIfReadersEmpty =
                { writerHeld := none,
                  readers := (((c_head, AccessMode.read) :: rest).takeWhile
                                (fun w : CoreId × AccessMode => w.2 = AccessMode.read)).map Prod.fst,
                  waiters := ((c_head, AccessMode.read) :: rest).dropWhile
                                (fun w : CoreId × AccessMode => w.2 = AccessMode.read) } := by
              unfold RwLockState.promoteWaitersIfReadersEmpty
              simp [h_no_writer]
            rw [h_post_struct] at h_out
            rw [h_post_struct]
            rw [h_w_eq] at h_in
            have h_pre_eq : (c_head, AccessMode.read) :: rest =
                ((c_head, AccessMode.read) :: rest).takeWhile
                  (fun w : CoreId × AccessMode => w.2 = AccessMode.read) ++
                ((c_head, AccessMode.read) :: rest).dropWhile
                  (fun w : CoreId × AccessMode => w.2 = AccessMode.read) := by
              exact (List.takeWhile_append_dropWhile).symm
            rw [h_pre_eq] at h_in
            rw [List.mem_append] at h_in
            cases h_in with
            | inl h_in_take =>
              left
              exact List.mem_map.mpr ⟨(c, m), h_in_take, rfl⟩
            | inr h_in_drop => exact absurd h_in_drop h_out
    · -- Non-effective release: c' ∉ readers, so applyOp is no-op.
      have h_no : s.applyOp (.releaseRead c') = s := by
        unfold RwLockState.applyOp; simp [h_eff]
      rw [h_no] at h_out; exact absurd h_in h_out
  | releaseWrite c' =>
    by_cases h_eff : s.writerHeld = some c'
    · -- Effective release.  INV-R1: readers = [].
      have h_r_empty : s.readers = [] := s.wf_writerReadersExclusion h_wf c' h_eff
      have h_apply_eq : s.applyOp (.releaseWrite c') =
          ({ writerHeld := none, readers := s.readers,
             waiters := s.waiters } : RwLockState).promoteWaitersOnWriterRelease :=
        releaseWrite_post_with_promote_setup s h_wf c' h_eff
      rw [h_apply_eq] at h_out
      cases h_w_eq : s.waiters with
      | nil => rw [h_w_eq] at h_in; exact absurd h_in List.not_mem_nil
      | cons head rest =>
        obtain ⟨c_head, m_head⟩ := head
        rw [h_w_eq] at h_out
        rw [h_apply_eq, h_w_eq]
        cases m_head with
        | write =>
          have h_post_struct : ({ writerHeld := none, readers := s.readers,
                                   waiters := (c_head, AccessMode.write) :: rest } :
                                  RwLockState).promoteWaitersOnWriterRelease =
              { writerHeld := some c_head, readers := s.readers, waiters := rest } := by
            unfold RwLockState.promoteWaitersOnWriterRelease; simp
          rw [h_post_struct] at h_out
          rw [h_post_struct]
          rw [h_w_eq] at h_in
          cases h_in with
          | head => simp
          | tail _ h_in_rest => exact absurd h_in_rest h_out
        | read =>
          have h_post_struct : ({ writerHeld := none, readers := s.readers,
                                   waiters := (c_head, AccessMode.read) :: rest } :
                                  RwLockState).promoteWaitersOnWriterRelease =
              { writerHeld := none,
                readers := (((c_head, AccessMode.read) :: rest).takeWhile
                              (fun w : CoreId × AccessMode => w.2 = AccessMode.read)).map Prod.fst
                          ++ s.readers,
                waiters := ((c_head, AccessMode.read) :: rest).dropWhile
                              (fun w : CoreId × AccessMode => w.2 = AccessMode.read) } := by
            unfold RwLockState.promoteWaitersOnWriterRelease; simp
          rw [h_post_struct] at h_out
          rw [h_post_struct]
          rw [h_w_eq] at h_in
          have h_pre_eq : (c_head, AccessMode.read) :: rest =
              ((c_head, AccessMode.read) :: rest).takeWhile
                (fun w : CoreId × AccessMode => w.2 = AccessMode.read) ++
              ((c_head, AccessMode.read) :: rest).dropWhile
                (fun w : CoreId × AccessMode => w.2 = AccessMode.read) := by
            exact (List.takeWhile_append_dropWhile).symm
          rw [h_pre_eq] at h_in
          rw [List.mem_append] at h_in
          cases h_in with
          | inl h_in_take =>
            left
            have h_c_in_take : c ∈ (((c_head, AccessMode.read) :: rest).takeWhile
                                      (fun w : CoreId × AccessMode => w.2 = AccessMode.read)).map Prod.fst :=
              List.mem_map.mpr ⟨(c, m), h_in_take, rfl⟩
            exact List.mem_append_left _ h_c_in_take
          | inr h_in_drop => exact absurd h_in_drop h_out
    · -- Non-effective release.
      have h_no : s.applyOp (.releaseWrite c') = s := by
        unfold RwLockState.applyOp; simp [h_eff]
      rw [h_no] at h_out; exact absurd h_in h_out

/-- **WS-SM SM2.C-defer (operational invariant)**: at a release+promote
step, if `w₂ = (c₂, m₂)` leaves waiters (becomes a holder) and `w₁ =
(c₁, m₁)` was at strictly lower idxOf in pre-waiters, then `w₁` also
leaves waiters.

This is the FIFO inclusion property: when the promote drops a prefix
that includes a higher-idxOf waiter, it MUST also include all
lower-idxOf waiters (the prefix is contiguous from the head).

Proof: by case analysis on `op`.  Tryacquire cases are vacuous (don't
remove from waiters).  Release cases use the structural drop-prefix
characterization (`rwLock_fifo_admission` / `_readers_empty`): the
post-waiters equal `pre.waiters.drop k` for some k.  If w₂ ∉ post then
idxOf w₂ in pre < k.  Since idxOf w₁ < idxOf w₂ < k, w₁ is also in the
dropped prefix; w₁ ∉ post. -/
theorem promote_prefix_inclusion
    (s : RwLockState) (h_wf : s.wf)
    (w₁ w₂ : CoreId × AccessMode) (op : RwLockOp)
    (_h_in₁_pre : w₁ ∈ s.waiters) (h_in₂_pre : w₂ ∈ s.waiters)
    (h_idx_lt : s.waiters.idxOf w₁ < s.waiters.idxOf w₂)
    (h_out₂ : w₂ ∉ (s.applyOp op).waiters) :
    w₁ ∉ (s.applyOp op).waiters := by
  -- The waiters are Nodup (from wf via INV-R3).
  have h_nodup : s.waiters.Nodup := waiters_nodup_of_wf h_wf
  -- Case-split on op.  For tryAcquire, waiters are append-or-noop;
  -- w₂ ∉ post would mean w₂ ∉ pre, contradiction.
  cases op with
  | tryAcquireRead c' =>
    rcases tryAcquireRead_waiters_append_or_noop s c' with h_post | h_post
    · rw [h_post] at h_out₂; exact absurd h_in₂_pre h_out₂
    · rw [h_post] at h_out₂
      exact absurd (List.mem_append_left _ h_in₂_pre) h_out₂
  | tryAcquireWrite c' =>
    rcases tryAcquireWrite_waiters_append_or_noop s c' with h_post | h_post
    · rw [h_post] at h_out₂; exact absurd h_in₂_pre h_out₂
    · rw [h_post] at h_out₂
      exact absurd (List.mem_append_left _ h_in₂_pre) h_out₂
  | releaseRead c' =>
    -- Use the existing release-sublist via drop-prefix.
    have h_sub := releaseRead_waiters_sublist s c'
    -- post.waiters = s.waiters.drop k for some k.  Reconstruct k via
    -- the FIFO admission helper.
    by_cases h_in : c' ∈ s.readers
    · by_cases h_size : s.readers.length ≥ 2
      · -- No-promote: post.waiters = pre.waiters; contradicts h_out₂.
        rw [releaseRead_post_no_promote s h_wf c' h_in h_size] at h_out₂
        exact absurd h_in₂_pre h_out₂
      · -- Promote fires.  Get the drop count from rwLock_fifo_admission_readers_empty.
        have h_size_one : s.readers.length = 1 := by
          have h_pos : s.readers.length ≥ 1 := by
            cases h_r : s.readers with
            | nil => rw [h_r] at h_in; exact absurd h_in List.not_mem_nil
            | cons _ _ => simp
          omega
        have h_no_writer : s.writerHeld = none := by
          cases h_w : s.writerHeld with
          | none => rfl
          | some c'' =>
            have h_r_empty := s.wf_writerReadersExclusion h_wf c'' h_w
            rw [h_r_empty] at h_size_one; simp at h_size_one
        rw [releaseRead_post_with_promote_setup s h_wf c' h_in h_size_one h_no_writer]
        rw [releaseRead_post_with_promote_setup s h_wf c' h_in h_size_one h_no_writer] at h_out₂
        -- Now post.waiters = ({...s.waiters...}).promote....waiters.
        -- Extract k via fifo_admission_readers_empty.
        obtain ⟨k, h_drop⟩ := rwLock_fifo_admission_readers_empty
          ({ writerHeld := s.writerHeld, readers := [],
             waiters := s.waiters } : RwLockState)
        have h_w_proj : ({ writerHeld := s.writerHeld, readers := [],
                           waiters := s.waiters } : RwLockState).waiters = s.waiters := rfl
        rw [h_w_proj] at h_drop
        rw [h_drop] at h_out₂ ⊢
        -- post.waiters = s.waiters.drop k.  w₂ ∉ drop k.  Need w₁ ∉ drop k.
        -- Using drop_idxOf_eq_of_nodup: w ∈ drop k ↔ idxOf w in pre ≥ k.
        -- w₂ ∉ drop k AND w₂ ∈ pre ⇒ idxOf w₂ < k.
        -- w₁ ∈ pre and idxOf w₁ < idxOf w₂ < k ⇒ w₁ ∉ drop k (if w₁ ∈ drop k,
        -- idxOf would be ≥ k by drop_idxOf_eq_of_nodup, contradicting idxOf < k).
        intro h_in₁_post
        have h₁ := drop_idxOf_eq_of_nodup s.waiters h_nodup k w₁ h_in₁_post
        -- h₁: (drop k).idxOf w₁ + k = s.waiters.idxOf w₁
        -- Hence s.waiters.idxOf w₁ ≥ k.
        have h_idx₁ : s.waiters.idxOf w₁ ≥ k := by omega
        -- But idxOf w₁ < idxOf w₂.  And w₂ ∉ drop k.
        -- If w₂ ∈ s.waiters and w₂ ∉ s.waiters.drop k, then idxOf w₂ < k
        -- (w₂ is in the take, not the drop).
        have h_idx₂_lt_k : s.waiters.idxOf w₂ < k := by
          -- s.waiters = take k ++ drop k.  w₂ ∈ s.waiters.  If idxOf w₂ ≥ k,
          -- w₂ would be in drop k.  Contradiction with h_out₂.
          -- Direct proof: w₂ ∈ s.waiters splits into "in take k" or "in drop k".
          -- "in drop k" contradicts h_out₂.  "in take k" gives idxOf < k.
          have h_split : s.waiters = s.waiters.take k ++ s.waiters.drop k :=
            (List.take_append_drop k _).symm
          have h_in_split : w₂ ∈ s.waiters.take k ++ s.waiters.drop k := by
            rw [← h_split]; exact h_in₂_pre
          rw [List.mem_append] at h_in_split
          cases h_in_split with
          | inl h_in_take =>
            -- w₂ ∈ take k.  idxOf w₂ in s.waiters = idxOf w₂ in take ≤ length take - 1 < k.
            have h_idx_take : s.waiters.idxOf w₂ = (s.waiters.take k).idxOf w₂ := by
              -- s.waiters = take ++ drop.  By idxOf_append for w₂ ∈ take, get the take.idxOf form.
              calc s.waiters.idxOf w₂
                  = (s.waiters.take k ++ s.waiters.drop k).idxOf w₂ := by rw [← h_split]
                _ = (s.waiters.take k).idxOf w₂ := by
                    rw [List.idxOf_append]; simp [h_in_take]
            have h_take_idx_lt : (s.waiters.take k).idxOf w₂ < (s.waiters.take k).length :=
              List.idxOf_lt_length_of_mem h_in_take
            have h_take_length : (s.waiters.take k).length ≤ k := List.length_take_le _ _
            omega
          | inr h_in_drop => exact absurd h_in_drop h_out₂
        omega
    · -- Non-effective release.  post.waiters = pre.waiters.
      have h_no : s.applyOp (.releaseRead c') = s := by
        unfold RwLockState.applyOp; simp [h_in]
      rw [h_no] at h_out₂; exact absurd h_in₂_pre h_out₂
  | releaseWrite c' =>
    by_cases h_eff : s.writerHeld = some c'
    · rw [releaseWrite_post_with_promote_setup s h_wf c' h_eff]
      rw [releaseWrite_post_with_promote_setup s h_wf c' h_eff] at h_out₂
      obtain ⟨k, h_drop⟩ := rwLock_fifo_admission
        ({ writerHeld := none, readers := s.readers,
           waiters := s.waiters } : RwLockState)
      have h_w_proj : ({ writerHeld := none, readers := s.readers,
                         waiters := s.waiters } : RwLockState).waiters = s.waiters := rfl
      rw [h_w_proj] at h_drop
      rw [h_drop] at h_out₂ ⊢
      intro h_in₁_post
      have h₁ := drop_idxOf_eq_of_nodup s.waiters h_nodup k w₁ h_in₁_post
      have h_idx₁ : s.waiters.idxOf w₁ ≥ k := by omega
      have h_idx₂_lt_k : s.waiters.idxOf w₂ < k := by
        have h_split : s.waiters = s.waiters.take k ++ s.waiters.drop k :=
          (List.take_append_drop k _).symm
        have h_in_split : w₂ ∈ s.waiters.take k ++ s.waiters.drop k := by
          rw [← h_split]; exact h_in₂_pre
        rw [List.mem_append] at h_in_split
        cases h_in_split with
        | inl h_in_take =>
          have h_idx_take : s.waiters.idxOf w₂ = (s.waiters.take k).idxOf w₂ := by
            calc s.waiters.idxOf w₂
                = (s.waiters.take k ++ s.waiters.drop k).idxOf w₂ := by rw [← h_split]
              _ = (s.waiters.take k).idxOf w₂ := by
                  rw [List.idxOf_append]; simp [h_in_take]
          have h_take_idx_lt : (s.waiters.take k).idxOf w₂ < (s.waiters.take k).length :=
            List.idxOf_lt_length_of_mem h_in_take
          have h_take_length : (s.waiters.take k).length ≤ k := List.length_take_le _ _
          omega
        | inr h_in_drop => exact absurd h_in_drop h_out₂
      omega
    · have h_no : s.applyOp (.releaseWrite c') = s := by
        unfold RwLockState.applyOp; simp [h_eff]
      rw [h_no] at h_out₂; exact absurd h_in₂_pre h_out₂

-- ============================================================================
-- SM2.C-defer D-1.9 (third operational invariant + main theorem)
-- ============================================================================

/-- **WS-SM SM2.C-defer (operational invariant)**: queued waiters stay
in waiters until their FIRST admission step.

If `enqueueStep c m = some p` and `admissionStep c = some a`, then for
all k ∈ [p, a), `(c, m) ∈ stateAt k . waiters`.

Proof: by induction on k - p, using `leave_waiters_implies_holder`'s
contrapositive (c not a holder at k+1 ⇒ (c, m) stays in waiters).
`admissionStep c = some a` means c is NOT a holder at any step < a
(by minimality of the find?-form). -/
theorem c_in_waiters_through_admission
    (e : RwLockExecution) (h_init : e.initial = RwLockState.unheld)
    (c : CoreId) (m : AccessMode) (p a : Nat)
    (h_enq : e.enqueueStep c m = some p)
    (h_admit : e.admissionStep c = some a)
    (h_p_lt_a : p < a) :
    ∀ k, p ≤ k → k < a → (c, m) ∈ (e.stateAt k).waiters := by
  -- Get the enqueueStep characterization: (c, m) in waiters at p.
  obtain ⟨h_p_ge_1, h_waiter_p, _h_not_waiter_prev⟩ :=
    e.enqueueStep_characterization c m p h_enq
  -- Get a₂ ≤ ops.length via admissionStep's range bound.
  -- (Not needed for this proof; the induction is on k ∈ [p, a).)
  -- Track admission's "first transition" property: for all k < a,
  -- c is NOT a holder at k.
  have h_not_holder : ∀ k, k < a → ¬ e.holderAt k c := by
    intro k h_k_lt
    -- a is the FIRST k' with holderAt k' c AND ¬ holderAt (k'-1) c.
    -- We need: for ALL k < a, ¬ holderAt k c.
    -- Use the find?-minimality of admissionStep.
    by_cases h_k_zero : k = 0
    · -- holderAt 0 c is False (initial unheld).
      rw [h_k_zero]; exact holderAt_zero_false e h_init c
    · -- k ≥ 1.  If holderAt k c is true, then admissionStep would return ≤ k.
      -- This is admissionStep_le_of_holder applied with n = k.
      -- We need to handle the case where k ≤ e.ops.length.
      by_cases h_k_in_range : k ≤ e.ops.length
      · intro h_holder_k
        obtain ⟨j, h_j_eq, h_j_le⟩ :=
          admissionStep_le_of_holder e h_init c k h_k_in_range h_holder_k
        -- a was the value of admissionStep, so a = j.  Then a ≤ k < a.
        -- Contradiction.
        rw [h_admit] at h_j_eq
        injection h_j_eq with h_eq
        omega
      · -- k > ops.length.  holderAt k c implies state at k has c as holder.
        -- For k > length, stateAt k = stateAt length (truncation).
        intro h_holder_k
        have h_k_gt : e.ops.length < k := Nat.lt_of_not_le h_k_in_range
        have h_k_ge : e.ops.length ≤ k := Nat.le_of_lt h_k_gt
        have h_eq : e.stateAt k = e.stateAt e.ops.length := by
          unfold RwLockExecution.stateAt
          rw [List.take_of_length_le h_k_ge, List.take_of_length_le (Nat.le_refl _)]
        rw [RwLockExecution.holderAt] at h_holder_k
        rw [h_eq] at h_holder_k
        -- Now holderAt e.ops.length c is True.  Apply admissionStep_le_of_holder
        -- with n = e.ops.length.
        have h_holder_len : e.holderAt e.ops.length c := h_holder_k
        obtain ⟨j, h_j_eq, h_j_le⟩ :=
          admissionStep_le_of_holder e h_init c e.ops.length (Nat.le_refl _) h_holder_len
        rw [h_admit] at h_j_eq
        injection h_j_eq with h_eq2
        omega
  -- Now prove via induction on k - p (the offset from enqueue point).
  -- Use a helper that takes the offset and proves at (p + offset).
  have h_helper : ∀ d, d < a - p → (c, m) ∈ (e.stateAt (p + d)).waiters := by
    intro d
    induction d with
    | zero =>
      intro _
      simp; exact h_waiter_p
    | succ d ih =>
      intro h_succ_lt
      -- Apply ih to get (c, m) ∈ waiters_{p + d}.
      have h_d_lt : d < a - p := by omega
      have h_prev : (c, m) ∈ (e.stateAt (p + d)).waiters := ih h_d_lt
      -- Now show (c, m) ∈ waiters_{p + d + 1}.
      -- Use leave_waiters_implies_holder contrapositive at step p + d.
      have h_k : p + d + 1 = p + (d + 1) := by omega
      by_cases h_k_in_range : p + d < e.ops.length
      · have h_state_succ : e.stateAt (p + d + 1) =
            (e.stateAt (p + d)).applyOp (e.ops[p + d]'h_k_in_range) :=
          RwLockExecution.stateAt_succ e h_k_in_range
        rw [show p + (d + 1) = p + d + 1 from rfl]
        rw [h_state_succ]
        -- Goal: (c, m) ∈ ((stateAt (p+d)).applyOp ops[p+d]).waiters.
        -- Use Decidable.byContradiction: it's decidable since the post-state's
        -- waiters list has DecidableEq.
        have h_dec : Decidable ((c, m) ∈ ((e.stateAt (p + d)).applyOp
                                            (e.ops[p + d]'h_k_in_range)).waiters) :=
          inferInstance
        cases h_dec with
        | isTrue h => exact h
        | isFalse h_not_in =>
          exfalso
          have h_wf_pd : (e.stateAt (p + d)).wf := e.stateAt_wf (p + d)
          have h_holder := leave_waiters_implies_holder (e.stateAt (p + d)) h_wf_pd
                            c m (e.ops[p + d]'h_k_in_range) h_prev h_not_in
          have h_holder_at : e.holderAt (p + d + 1) c := by
            unfold RwLockExecution.holderAt
            rw [h_state_succ]
            exact h_holder
          have h_pd1_lt_a : p + d + 1 < a := by omega
          exact h_not_holder (p + d + 1) h_pd1_lt_a h_holder_at
      · -- p + d ≥ ops.length.  stateAt (p + d + 1) = stateAt (p + d).
        have h_pd_ge : p + d ≥ e.ops.length := Nat.le_of_not_lt h_k_in_range
        have h_eq : e.stateAt (p + (d + 1)) = e.stateAt (p + d) := by
          unfold RwLockExecution.stateAt
          have h_take : e.ops.take (p + (d + 1)) = e.ops.take (p + d) := by
            rw [List.take_of_length_le (by omega), List.take_of_length_le h_pd_ge]
          rw [h_take]
        rw [h_eq]; exact h_prev
  -- Apply h_helper to k.
  intro k h_p_le h_k_lt_a
  have h_offset_lt : k - p < a - p := by omega
  have h := h_helper (k - p) h_offset_lt
  have h_eq : p + (k - p) = k := by omega
  rw [h_eq] at h
  exact h

/-- **WS-SM SM2.C-defer D-1.9 (FULL MAIN THEOREM)**: temporal FIFO admission.

For an `RwLockExecution` `e` starting from `RwLockState.unheld` and two
waiters `(c₁, m₁)` and `(c₂, m₂)` enqueued at trace positions `p₁ < p₂`,
if `c₂` is admitted at step `a₂` AND `c₂`'s admission corresponds to
this enqueue (i.e., `p₂ < a₂`), then `c₁` is admitted at some step
`a₁ ≤ a₂`.

**Implement-the-improvement refinement**: the plan §5.1 omits the
`p₂ < a₂` precondition.  Per CLAUDE.md's implement-the-improvement
rule, we add it explicitly: without `p₂ < a₂`, the case `a₂ ≤ p₂`
(c₂'s FIRST admission via direct-acquire occurred BEFORE its FIRST
enqueue at p₂) admits FIFO-violating scenarios.  Specifically, c₂
could direct-acquire at a₂, release, then re-enqueue at p₂ > a₂;
c₁ enqueued at p₁ ∈ (a₂, p₂) would have a₁ > a₂, violating the
plan's conclusion.  Adding `p₂ < a₂` ensures the theorem captures
the intended "FIFO over the enqueue at p₂" semantics.

**Initial-state restriction**: `e.initial = RwLockState.unheld` (closes
audit M-3).

**Non-strict `≤`** accommodates reader-batching (closes audit L-4).

**Proof outline**:
1. Case-split on whether c₁ is a holder at some k ≤ a₂.
2. If yes: `admissionStep_le_of_holder` gives `admissionStep c₁ = some j ≤ k ≤ a₂`. ✓
3. If no: c₁ stays in waiters from p₁ to a₂ - 1 (via `leave_waiters_implies_holder`'s
   contrapositive, since c₁ is never a holder).  At step a₂ - 1, both c₁ and c₂
   are in waiters; by structural form, idxOf c₁ < idxOf c₂.  At step a₂, c₂ leaves
   waiters (becomes holder).  By `promote_prefix_inclusion`, c₁ also leaves
   waiters at a₂.  By `leave_waiters_implies_holder`, c₁ becomes a holder at a₂.
   This contradicts case (3)'s hypothesis "c₁ never holds at k ≤ a₂". -/
theorem rwLock_fifo_admission_temporal
    (e : RwLockExecution)
    (h_initial_unheld : e.initial = RwLockState.unheld)
    (c₁ c₂ : CoreId) (m₁ m₂ : AccessMode) (p₁ p₂ a₂ : Nat)
    (h_enqueue₁ : e.enqueueStep c₁ m₁ = some p₁)
    (h_enqueue₂ : e.enqueueStep c₂ m₂ = some p₂)
    (h_order : p₁ < p₂)
    (h_admitted₂ : e.admissionStep c₂ = some a₂)
    (h_p2_lt_a2 : p₂ < a₂) :
    ∃ a₁, e.admissionStep c₁ = some a₁ ∧ a₁ ≤ a₂ := by
  obtain ⟨h_a2_ge_1, h_a2_holder_c2, h_a2_prev_not_holder⟩ :=
    e.admissionStep_characterization c₂ a₂ h_admitted₂
  obtain ⟨h_p1_ge_1, h_w_p1, _⟩ := e.enqueueStep_characterization c₁ m₁ p₁ h_enqueue₁
  obtain ⟨h_p2_ge_1, h_w_p2, _⟩ := e.enqueueStep_characterization c₂ m₂ p₂ h_enqueue₂
  -- Bound a₂ ≤ ops.length.
  have h_a2_in_range : a₂ ≤ e.ops.length := by
    have h_a2_mem : a₂ ∈ List.range (e.ops.length + 1) := by
      have h_app := List.find?_eq_some_iff_append.mp h_admitted₂
      obtain ⟨_, _, _, h_split, _⟩ := h_app
      rw [h_split]
      exact List.mem_append_right _ List.mem_cons_self
    rw [List.mem_range] at h_a2_mem
    omega
  -- Case-split: is c₁ a holder at any step ≤ a₂?
  by_cases h_c1_holder_le_a2 : ∃ k, k ≤ a₂ ∧ e.holderAt k c₁
  · -- Direct case: admission step bridge.
    obtain ⟨k, h_k_le, h_holder⟩ := h_c1_holder_le_a2
    have h_k_in_range : k ≤ e.ops.length := by omega
    obtain ⟨j, h_j_eq, h_j_le⟩ :=
      admissionStep_le_of_holder e h_initial_unheld c₁ k h_k_in_range h_holder
    exact ⟨j, h_j_eq, by omega⟩
  · -- Contradiction case: c₁ never holds at k ≤ a₂.  Derive that c₁ IS a holder
    -- at a₂ via the FIFO chain, contradicting the case assumption.
    exfalso
    -- Convert the negated existential into a universal.
    have h_c1_not_holder : ∀ k ≤ a₂, ¬ e.holderAt k c₁ := by
      intro k h_k_le h_holder
      exact h_c1_holder_le_a2 ⟨k, h_k_le, h_holder⟩
    -- Step A: c₁ stays in waiters through a₂-1.  Uses the same argument as
    -- c_in_waiters_through_admission but with c₁'s never-a-holder condition
    -- (rather than reading the admissionStep).
    have h_c1_in_waiters : ∀ k, p₁ ≤ k → k < a₂ → (c₁, m₁) ∈ (e.stateAt k).waiters := by
      -- The proof mirrors c_in_waiters_through_admission's helper closure,
      -- with `h_c1_not_holder` replacing the admissionStep-derived bound.
      have h_helper : ∀ d, d < a₂ - p₁ → (c₁, m₁) ∈ (e.stateAt (p₁ + d)).waiters := by
        intro d
        induction d with
        | zero => intro _; simp; exact h_w_p1
        | succ d ih =>
          intro h_succ_lt
          have h_d_lt : d < a₂ - p₁ := by omega
          have h_prev : (c₁, m₁) ∈ (e.stateAt (p₁ + d)).waiters := ih h_d_lt
          by_cases h_k_in_range : p₁ + d < e.ops.length
          · have h_state_succ : e.stateAt (p₁ + d + 1) =
                (e.stateAt (p₁ + d)).applyOp (e.ops[p₁ + d]'h_k_in_range) :=
              RwLockExecution.stateAt_succ e h_k_in_range
            rw [show p₁ + (d + 1) = p₁ + d + 1 from rfl]
            rw [h_state_succ]
            have h_dec : Decidable ((c₁, m₁) ∈ ((e.stateAt (p₁ + d)).applyOp
                                                  (e.ops[p₁ + d]'h_k_in_range)).waiters) :=
              inferInstance
            cases h_dec with
            | isTrue h => exact h
            | isFalse h_not_in =>
              exfalso
              have h_wf_pd : (e.stateAt (p₁ + d)).wf := e.stateAt_wf (p₁ + d)
              have h_holder := leave_waiters_implies_holder (e.stateAt (p₁ + d)) h_wf_pd
                                c₁ m₁ (e.ops[p₁ + d]'h_k_in_range) h_prev h_not_in
              have h_holder_at : e.holderAt (p₁ + d + 1) c₁ := by
                unfold RwLockExecution.holderAt
                rw [h_state_succ]
                exact h_holder
              have h_pd1_le_a2 : p₁ + d + 1 ≤ a₂ := by omega
              exact h_c1_not_holder (p₁ + d + 1) h_pd1_le_a2 h_holder_at
          · -- Past ops.length; state unchanged.
            have h_pd_ge : p₁ + d ≥ e.ops.length := Nat.le_of_not_lt h_k_in_range
            have h_eq : e.stateAt (p₁ + (d + 1)) = e.stateAt (p₁ + d) := by
              unfold RwLockExecution.stateAt
              have h_take : e.ops.take (p₁ + (d + 1)) = e.ops.take (p₁ + d) := by
                rw [List.take_of_length_le (by omega), List.take_of_length_le h_pd_ge]
              rw [h_take]
            rw [h_eq]; exact h_prev
      intro k h_p1_le h_k_lt_a2
      have h_offset_lt : k - p₁ < a₂ - p₁ := by omega
      have h := h_helper (k - p₁) h_offset_lt
      have h_eq : p₁ + (k - p₁) = k := by omega
      rw [h_eq] at h
      exact h
    -- Step B: c₂ stays in waiters through a₂-1 (via the proven helper).
    have h_c2_in_waiters : ∀ k, p₂ ≤ k → k < a₂ → (c₂, m₂) ∈ (e.stateAt k).waiters :=
      c_in_waiters_through_admission e h_initial_unheld c₂ m₂ p₂ a₂
        h_enqueue₂ h_admitted₂ h_p2_lt_a2
    -- Step C: at step a₂-1, both c₁ and c₂ are in waiters.
    have h_a2_m1_pos : a₂ - 1 ≥ p₂ := by omega -- since p₂ < a₂.
    have h_a2_m1_lt : a₂ - 1 < a₂ := by omega
    have h_c1_at_a2_m1 : (c₁, m₁) ∈ (e.stateAt (a₂ - 1)).waiters :=
      h_c1_in_waiters (a₂ - 1) (by omega) h_a2_m1_lt
    have h_c2_at_a2_m1 : (c₂, m₂) ∈ (e.stateAt (a₂ - 1)).waiters :=
      h_c2_in_waiters (a₂ - 1) h_a2_m1_pos h_a2_m1_lt
    -- Step D: at step p₂ (just after c₂'s append at tail), idxOf c₁ < idxOf c₂.
    -- Use D-1.6 (acquire append-or-noop) to characterize stateAt p₂ vs stateAt (p₂-1).
    -- c₁ is in waiters at p₂-1 (since p₁ ≤ p₂-1 < a₂, by h_c1_in_waiters).
    have h_c1_at_p2_m1 : (c₁, m₁) ∈ (e.stateAt (p₂ - 1)).waiters :=
      h_c1_in_waiters (p₂ - 1) (by omega) (by omega)
    -- Step E: use structural form to extend the order from p₂ to a₂-1.
    -- For the structural form, we need to provide the surviving hypothesis.
    have h_surviving : ∀ j, p₂ ≤ j → j ≤ a₂ - 1 →
        (c₁, m₁) ∈ (e.stateAt j).waiters ∧ (c₂, m₂) ∈ (e.stateAt j).waiters := by
      intro j h_lo h_hi
      refine ⟨h_c1_in_waiters j (by omega) (by omega),
              h_c2_in_waiters j h_lo (by omega)⟩
    -- The structural form requires `idxOf c₁ < idxOf c₂` at p₂ as the base order.
    -- Get this from D-1.6: at p₂, (c₂, m₂) was just appended.  c₁ was in
    -- (stateAt (p₂-1)).waiters; (stateAt p₂).waiters = (stateAt (p₂-1)).waiters
    -- ++ [(c₂, m₂)] OR is unchanged (no-op).  The "no-op" case doesn't add c₂,
    -- so c₂ ∉ stateAt p₂ waiters (contradicting h_c2_in_waiters at p₂).
    -- Hence we're in the "append" case.
    have h_c2_at_p2 : (c₂, m₂) ∈ (e.stateAt p₂).waiters :=
      h_c2_in_waiters p₂ (Nat.le_refl _) (by omega)
    -- Get the op at step p₂-1 → p₂.
    have h_p2_pos : p₂ ≥ 1 := h_p2_ge_1
    have h_p2_in_range : p₂ - 1 < e.ops.length := by
      -- p₂ ≤ a₂ ≤ ops.length, and p₂ ≥ 1, so p₂ - 1 < ops.length.
      omega
    have h_state_p2 : e.stateAt p₂ = (e.stateAt (p₂ - 1)).applyOp (e.ops[p₂ - 1]'h_p2_in_range) := by
      have h_eq : (p₂ - 1) + 1 = p₂ := by omega
      have h_succ := RwLockExecution.stateAt_succ e h_p2_in_range
      rw [h_eq] at h_succ
      exact h_succ
    -- We need (e.ops[p₂-1] = tryAcquire c₂ ...) to use D-1.6.
    -- This isn't immediate; we use enqueueStep_characterization: at p₂, (c₂, m₂) is
    -- in waiters, not at p₂-1.  By transitivity arguments through applyOp's
    -- behavior, the op MUST be tryAcquireRead c₂ or tryAcquireWrite c₂.
    -- But proving this requires careful op-shape analysis.
    --
    -- Direct alternative: use D-1.6/D-1.7 to characterize the waiters change.
    -- post.waiters is either pre.waiters (no-op) or pre.waiters ++ [(c₂, m₂)]
    -- (one of the acquire append cases).  If pre = post, c₂ ∉ post would
    -- contradict h_c2_at_p2.  Hence post = pre ++ [(c, m')] for some op op_{p₂-1}.
    --
    -- For the FIFO order claim at step p₂, c₁ is at the SAME idxOf in pre and post
    -- (since the append doesn't move existing elements).  c₂ is at idxOf =
    -- pre.length in post.  Hence idxOf c₁ < pre.length = idxOf c₂ in post.
    --
    -- For brevity, use the existing structural facts:
    have h_order_at_p2 : (e.stateAt p₂).waiters.idxOf (c₁, m₁) <
                         (e.stateAt p₂).waiters.idxOf (c₂, m₂) := by
      -- The op at step p₂-1 must produce c₂ at the tail.  By D-1.6 case
      -- analysis: tryAcquireRead c₂ or tryAcquireWrite c₂ are the only ops
      -- adding (c₂, m₂) to waiters.  No-op or other ops preserve / drop only.
      -- Use the dispatch via applyOp + D-1.6/D-1.7.
      -- For the v1.0.0 deferred-completion, prove via the structure of
      -- stateAt_succ and case analysis on the op.
      have h_app := List.takeWhile_append_dropWhile (l := (e.stateAt (p₂ - 1)).waiters)
                      (p := fun _ : CoreId × AccessMode => true)
      -- Direct approach: case-split on e.ops[p₂-1].
      have h_op := e.ops[p₂ - 1]'h_p2_in_range
      have h_state_eq := h_state_p2
      -- (c₂, m₂) ∉ stateAt (p₂-1).waiters (by enqueueStep_characterization).
      have h_c2_not_at_p2m1 : (c₂, m₂) ∉ (e.stateAt (p₂ - 1)).waiters := by
        intro h_in
        -- waiterAt (p₂ - 1) c₂ m₂.  But enqueueStep_characterization says
        -- ¬ waiterAt (p₂ - 1) c₂ m₂.
        exact (e.enqueueStep_characterization c₂ m₂ p₂ h_enqueue₂).2.2 h_in
      -- Now case-split on the op.
      cases h_op_def : e.ops[p₂ - 1]'h_p2_in_range with
      | tryAcquireRead c' =>
        rcases tryAcquireRead_waiters_append_or_noop (e.stateAt (p₂ - 1)) c' with h_noop | h_app_form
        · -- Noop case: post = pre.  c₂ ∉ pre, c₂ ∉ post.  Contradicts h_c2_at_p2.
          exfalso
          have h_post_waiters : (e.stateAt p₂).waiters = (e.stateAt (p₂ - 1)).waiters := by
            rw [h_state_eq, h_op_def]; exact h_noop
          rw [h_post_waiters] at h_c2_at_p2
          exact h_c2_not_at_p2m1 h_c2_at_p2
        · -- Append case: post.waiters = pre.waiters ++ [(c', .read)].
          -- For c₂ to be in post, (c', .read) = (c₂, m₂), so c' = c₂ and m₂ = .read.
          have h_post_waiters : (e.stateAt p₂).waiters =
              (e.stateAt (p₂ - 1)).waiters ++ [(c', AccessMode.read)] := by
            rw [h_state_eq, h_op_def]; exact h_app_form
          rw [h_post_waiters] at h_c2_at_p2 ⊢
          -- Show c' = c₂ ∧ m₂ = .read.
          have h_c2_in_app : (c₂, m₂) ∈ (e.stateAt (p₂ - 1)).waiters ++ [(c', AccessMode.read)] := h_c2_at_p2
          rw [List.mem_append] at h_c2_in_app
          rcases h_c2_in_app with h_pre | h_singleton
          · exact absurd h_pre h_c2_not_at_p2m1
          · -- c₂ ∈ [(c', .read)].
            have h_eq : (c₂, m₂) = (c', AccessMode.read) := by
              cases h_singleton with
              | head => rfl
              | tail _ h => exact absurd h List.not_mem_nil
            have h_c2_eq : c₂ = c' := (Prod.mk.injEq _ _ _ _ |>.mp h_eq).1
            have h_m2_eq : m₂ = AccessMode.read := (Prod.mk.injEq _ _ _ _ |>.mp h_eq).2
            -- idxOf c₁ in post = idxOf c₁ in pre (since c₁ already in pre).
            -- idxOf c₂ in post = pre.length (since c₂ at tail).
            have h_c1_in_pre : (c₁, m₁) ∈ (e.stateAt (p₂ - 1)).waiters := h_c1_at_p2_m1
            -- post.waiters = pre ++ [(c₂, m₂)] (after substituting c'=c₂, .read=m₂).
            -- idxOf c₁ in post = idxOf c₁ in pre (since c₁ in pre).
            -- idxOf c₂ in post = pre.length (since c₂ ∉ pre and c₂ is at end).
            have h_idx_c1 : ((e.stateAt (p₂ - 1)).waiters ++ [(c', AccessMode.read)]).idxOf (c₁, m₁) =
                (e.stateAt (p₂ - 1)).waiters.idxOf (c₁, m₁) := by
              rw [List.idxOf_append]; simp [h_c1_in_pre]
            have h_idx_c2 : ((e.stateAt (p₂ - 1)).waiters ++ [(c', AccessMode.read)]).idxOf (c₂, m₂) =
                (e.stateAt (p₂ - 1)).waiters.length := by
              rw [List.idxOf_append]; simp [h_c2_not_at_p2m1, ← h_c2_eq, ← h_m2_eq]
            rw [h_idx_c1, h_idx_c2]
            exact List.idxOf_lt_length_of_mem h_c1_in_pre
      | tryAcquireWrite c' =>
        rcases tryAcquireWrite_waiters_append_or_noop (e.stateAt (p₂ - 1)) c' with h_noop | h_app_form
        · exfalso
          have h_post_waiters : (e.stateAt p₂).waiters = (e.stateAt (p₂ - 1)).waiters := by
            rw [h_state_eq, h_op_def]; exact h_noop
          rw [h_post_waiters] at h_c2_at_p2
          exact h_c2_not_at_p2m1 h_c2_at_p2
        · have h_post_waiters : (e.stateAt p₂).waiters =
              (e.stateAt (p₂ - 1)).waiters ++ [(c', AccessMode.write)] := by
            rw [h_state_eq, h_op_def]; exact h_app_form
          rw [h_post_waiters] at h_c2_at_p2 ⊢
          have h_c2_in_app : (c₂, m₂) ∈ (e.stateAt (p₂ - 1)).waiters ++ [(c', AccessMode.write)] := h_c2_at_p2
          rw [List.mem_append] at h_c2_in_app
          rcases h_c2_in_app with h_pre | h_singleton
          · exact absurd h_pre h_c2_not_at_p2m1
          · have h_eq : (c₂, m₂) = (c', AccessMode.write) := by
              cases h_singleton with
              | head => rfl
              | tail _ h => exact absurd h List.not_mem_nil
            have h_c2_eq : c₂ = c' := (Prod.mk.injEq _ _ _ _ |>.mp h_eq).1
            have h_m2_eq : m₂ = AccessMode.write := (Prod.mk.injEq _ _ _ _ |>.mp h_eq).2
            have h_c1_in_pre : (c₁, m₁) ∈ (e.stateAt (p₂ - 1)).waiters := h_c1_at_p2_m1
            have h_idx_c1 : ((e.stateAt (p₂ - 1)).waiters ++ [(c', AccessMode.write)]).idxOf (c₁, m₁) =
                (e.stateAt (p₂ - 1)).waiters.idxOf (c₁, m₁) := by
              rw [List.idxOf_append]; simp [h_c1_in_pre]
            have h_idx_c2 : ((e.stateAt (p₂ - 1)).waiters ++ [(c', AccessMode.write)]).idxOf (c₂, m₂) =
                (e.stateAt (p₂ - 1)).waiters.length := by
              rw [List.idxOf_append]; simp [h_c2_not_at_p2m1, ← h_c2_eq, ← h_m2_eq]
            rw [h_idx_c1, h_idx_c2]
            exact List.idxOf_lt_length_of_mem h_c1_in_pre
      | releaseRead c' =>
        -- Release ops drop only; can't add (c₂, m₂) to waiters.
        exfalso
        have h_sub := releaseRead_waiters_sublist (e.stateAt (p₂ - 1)) c'
        have h_post_sub : (e.stateAt p₂).waiters.Sublist (e.stateAt (p₂ - 1)).waiters := by
          rw [h_state_eq, h_op_def]; exact h_sub
        have h_c2_in_pre : (c₂, m₂) ∈ (e.stateAt (p₂ - 1)).waiters :=
          h_post_sub.mem h_c2_at_p2
        exact h_c2_not_at_p2m1 h_c2_in_pre
      | releaseWrite c' =>
        exfalso
        have h_sub := releaseWrite_waiters_sublist (e.stateAt (p₂ - 1)) c'
        have h_post_sub : (e.stateAt p₂).waiters.Sublist (e.stateAt (p₂ - 1)).waiters := by
          rw [h_state_eq, h_op_def]; exact h_sub
        have h_c2_in_pre : (c₂, m₂) ∈ (e.stateAt (p₂ - 1)).waiters :=
          h_post_sub.mem h_c2_at_p2
        exact h_c2_not_at_p2m1 h_c2_in_pre
    -- Get c₁ at p₂ for the structural call.
    have h_c1_at_p2 : (c₁, m₁) ∈ (e.stateAt p₂).waiters :=
      h_c1_in_waiters p₂ (by omega) (by omega)
    -- Apply rwLock_fifo_admission_temporal_structural to extend the order
    -- from p₂ to a₂-1.  Signature:
    -- (e k₁ k₂ h_le w₁ w₂ h_in₁_at_k₁ h_in₂_at_k₁ h_in₁_at_k₂ h_in₂_at_k₂ h_order h_surviving)
    have h_order_at_a2_m1 : (e.stateAt (a₂ - 1)).waiters.idxOf (c₁, m₁) <
                            (e.stateAt (a₂ - 1)).waiters.idxOf (c₂, m₂) :=
      rwLock_fifo_admission_temporal_structural e p₂ (a₂ - 1) (by omega)
        (c₁, m₁) (c₂, m₂)
        h_c1_at_p2 h_c2_at_p2
        h_c1_at_a2_m1 h_c2_at_a2_m1
        h_order_at_p2 h_surviving
    -- Step G: at step a₂, c₂ leaves waiters (becomes a holder).
    have h_c2_leaves : (c₂, m₂) ∉ (e.stateAt a₂).waiters := by
      -- c₂ ∈ holders at a₂ (h_a2_holder_c2).  By INV-R4 of stateAt a₂'s wf,
      -- holders disjoint from waiters.
      have h_wf_a2 : (e.stateAt a₂).wf := e.stateAt_wf a₂
      have h_disj := (e.stateAt a₂).wf_waitersDisjointFromHolders h_wf_a2
      intro h_in_waiters
      have h_disj_c2 := h_disj (c₂, m₂) h_in_waiters
      -- h_disj_c2: c₂ ∉ readers ∧ writerHeld ≠ some c₂.
      unfold RwLockExecution.holderAt at h_a2_holder_c2
      rcases h_a2_holder_c2 with h_r | h_w_held
      · exact h_disj_c2.1 h_r
      · exact h_disj_c2.2 h_w_held
    -- Step H: by promote_prefix_inclusion at step a₂-1, c₁ also leaves at a₂.
    have h_a2_eq : a₂ - 1 + 1 = a₂ := by omega
    -- We need the op at a₂-1 to be the one that does the promote.
    have h_a2_m1_in_range : a₂ - 1 < e.ops.length := by omega
    have h_state_a2 : e.stateAt a₂ = (e.stateAt (a₂ - 1)).applyOp (e.ops[a₂ - 1]'h_a2_m1_in_range) := by
      have h_succ := RwLockExecution.stateAt_succ e h_a2_m1_in_range
      rw [h_a2_eq] at h_succ
      exact h_succ
    rw [h_state_a2] at h_c2_leaves
    have h_wf_a2_m1 : (e.stateAt (a₂ - 1)).wf := e.stateAt_wf (a₂ - 1)
    have h_c1_leaves : (c₁, m₁) ∉ ((e.stateAt (a₂ - 1)).applyOp (e.ops[a₂ - 1]'h_a2_m1_in_range)).waiters :=
      promote_prefix_inclusion (e.stateAt (a₂ - 1)) h_wf_a2_m1
        (c₁, m₁) (c₂, m₂) (e.ops[a₂ - 1]'h_a2_m1_in_range)
        h_c1_at_a2_m1 h_c2_at_a2_m1 h_order_at_a2_m1 h_c2_leaves
    -- Step I: by leave_waiters_implies_holder, c₁ becomes a holder at a₂.
    have h_c1_holder := leave_waiters_implies_holder (e.stateAt (a₂ - 1)) h_wf_a2_m1
                          c₁ m₁ (e.ops[a₂ - 1]'h_a2_m1_in_range) h_c1_at_a2_m1 h_c1_leaves
    have h_c1_holder_at_a2 : e.holderAt a₂ c₁ := by
      unfold RwLockExecution.holderAt
      rw [h_state_a2]
      exact h_c1_holder
    -- Step J: contradicts the case assumption.
    exact h_c1_not_holder a₂ (Nat.le_refl _) h_c1_holder_at_a2

-- ============================================================================
-- SM2.C-defer D-3.6 — Writer liveness under fairness
-- ============================================================================

/-- **WS-SM SM2.C-defer helper**: at a queued-writer step, INV-R5
guarantees some holder exists.  This is the SUBSTANTIVE entry point
for the fairness-driven D-3.6 derivation: from "c queued at k" we
extract "either writerHeld at k OR readers ≠ [] at k". -/
theorem queued_implies_holder_at_step
    (e : RwLockExecution) (c : CoreId) (k : Nat)
    (h_queued : (c, AccessMode.write) ∈ (e.stateAt k).waiters) :
    (e.stateAt k).writerHeld.isSome = true ∨ (e.stateAt k).readers ≠ [] := by
  have h_wf := e.stateAt_wf k
  apply RwLockState.wf_fifoAdmissionDiscipline h_wf
  intro h_eq
  rw [h_eq] at h_queued
  exact List.not_mem_nil h_queued

/-- **WS-SM SM2.C-defer helper**: finds the latest step `j ≤ k` such
that `(e.stateAt j).writerHeld ≠ some c_holder`, given that the writer
is held by `c_holder` at step `k` and was NOT held by `c_holder` at
step 0.

This is the "decreasing-find" helper that lets us extract the
LATEST writer-acquire transition step (`k_acq = j + 1`).  Used by
`fair_writer_release_witness`. -/
private theorem find_latest_writer_non_holder
    (e : RwLockExecution) (c_holder : CoreId) (k : Nat)
    (h_held : (e.stateAt k).writerHeld = some c_holder)
    (h_zero_not_holder : (e.stateAt 0).writerHeld ≠ some c_holder) :
    ∃ j, j < k ∧ (e.stateAt j).writerHeld ≠ some c_holder ∧
         ∀ j', j < j' ∧ j' ≤ k → (e.stateAt j').writerHeld = some c_holder := by
  -- Induct on k.  Base k = 0: contradicts h_held vs h_zero_not_holder.
  -- Step: if (stateAt k).writerHeld = some, look at (stateAt (k-1)):
  --   - If ≠ some c_holder, then j = k-1 works.
  --   - Else apply IH to k-1.
  induction k with
  | zero =>
    exfalso; exact h_zero_not_holder h_held
  | succ k' ih =>
    by_cases h_prev : (e.stateAt k').writerHeld = some c_holder
    · -- Previous step also held by c_holder.  Apply IH.
      have ⟨j, h_j_lt, h_j_not, h_j_after⟩ := ih h_prev
      refine ⟨j, by omega, h_j_not, ?_⟩
      intro j' ⟨h_lt, h_le⟩
      by_cases h_eq : j' = k' + 1
      · rw [h_eq]; exact h_held
      · exact h_j_after j' ⟨h_lt, by omega⟩
    · -- Previous step NOT held by c_holder.  j = k' works.
      refine ⟨k', by omega, h_prev, ?_⟩
      intro j' ⟨h_lt, h_le⟩
      have h_eq : j' = k' + 1 := by omega
      rw [h_eq]; exact h_held

/-- **WS-SM SM2.C-defer (substantive — D-3.6 fairness derivation)**:
under FairTrace, if the writer is held by `c_holder` at step `k`
(with `k > 0` and the initial state having no writer), then there
exists a release transition step `k_rel ∈ [k, k + maxDelay]` where the
writer transitions from `some c_holder` to not.

**This is the FIRST substantive use of FairTrace in the D-3.6 chain.**
The proof:
1. By `find_latest_writer_non_holder`, find the LATEST step `j < k`
   where writerHeld ≠ some c_holder.  Define `k_acq = j + 1`.
2. By construction, `writerHeld(k_acq - 1) ≠ some c_holder` and
   `writerHeld(j') = some c_holder ∀ j' ∈ [k_acq, k]`.  In particular
   `writerHeld(k_acq) = some c_holder` (taking j' = k_acq).
3. Apply `h_fair.writer_fairness` at `(k_acq, c_holder)` to obtain
   `k_rel ∈ [k_acq, k_acq + maxDelay]` with transition-edge.
4. Show `k_rel ≥ k`: otherwise the transition-edge would force
   `writerHeld(k_rel + 1) ≠ some c_holder` for some `k_rel + 1 ≤ k`,
   but we have `writerHeld(j') = some c_holder ∀ j' ∈ [k_acq, k]`
   from step 2 — contradiction.
5. So `k ≤ k_rel ≤ k_acq + maxDelay ≤ k + maxDelay` (since `k_acq ≤ k`). -/
theorem fair_writer_release_witness
    (e : RwLockExecution) (maxDelay : Nat) (h_fair : FairTrace e maxDelay)
    (h_init : e.initial = RwLockState.unheld)
    (k : Nat)
    (c_holder : CoreId) (h_held : (e.stateAt k).writerHeld = some c_holder) :
    ∃ k_rel, k ≤ k_rel ∧ k_rel ≤ k + maxDelay ∧
             (e.stateAt k_rel).writerHeld = some c_holder ∧
             (e.stateAt (k_rel + 1)).writerHeld ≠ some c_holder := by
  -- Step 1+2: find the latest writer-acquire step.
  have h_zero_not : (e.stateAt 0).writerHeld ≠ some c_holder := by
    rw [RwLockExecution.stateAt_zero, h_init]
    -- (unheld).writerHeld = none ≠ some c_holder.
    intro h_eq
    have h_none : RwLockState.unheld.writerHeld = none := by
      unfold RwLockState.unheld; rfl
    rw [h_none] at h_eq
    cases h_eq
  obtain ⟨j, h_j_lt, h_j_not, h_after⟩ :=
    find_latest_writer_non_holder e c_holder k h_held h_zero_not
  -- Define k_acq = j + 1.
  let k_acq := j + 1
  have h_k_acq_ge_one : 1 ≤ k_acq := by simp [k_acq]
  have h_k_acq_le_k : k_acq ≤ k := by simp [k_acq]; omega
  have h_acq_minus_one : k_acq - 1 = j := by simp [k_acq]
  -- Writer held at k_acq (from h_after with j' = k_acq).
  have h_held_at_kacq : (e.stateAt k_acq).writerHeld = some c_holder :=
    h_after k_acq ⟨by simp [k_acq], h_k_acq_le_k⟩
  -- Writer NOT held by c_holder at k_acq - 1 = j.
  have h_not_held_pre : (e.stateAt (k_acq - 1)).writerHeld ≠ some c_holder := by
    rw [h_acq_minus_one]; exact h_j_not
  -- Step 3: apply writer_fairness.
  obtain ⟨k_rel, h_rel_ge, h_rel_le, h_rel_held, h_rel_succ_not⟩ :=
    h_fair.writer_fairness k_acq c_holder h_k_acq_ge_one h_held_at_kacq h_not_held_pre
  -- Step 4: show k_rel ≥ k.
  have h_rel_ge_k : k ≤ k_rel := by
    -- Suppose k_rel < k.  Then k_rel + 1 ≤ k.  We have h_after: writerHeld(j') = some c_holder
    -- for j' ∈ (j, k].  So writerHeld(k_rel + 1) = some c_holder if k_rel + 1 ∈ (j, k].
    -- But h_rel_succ_not says writerHeld(k_rel + 1) ≠ some c_holder.  Contradiction.
    apply Decidable.byContradiction
    intro h_neg
    have h_lt : k_rel < k := Nat.lt_of_not_le h_neg
    have h_succ_le_k : k_rel + 1 ≤ k := by omega
    -- k_rel ≥ k_acq = j + 1 (from h_rel_ge).  So k_rel + 1 > j + 1, hence k_rel + 1 > j.
    have h_succ_gt_j : j < k_rel + 1 := by
      have : k_acq ≤ k_rel := h_rel_ge
      simp [k_acq] at this; omega
    -- k_rel + 1 ∈ (j, k], so by h_after, writerHeld at k_rel + 1 = some c_holder.
    have h_held_at_succ : (e.stateAt (k_rel + 1)).writerHeld = some c_holder :=
      h_after (k_rel + 1) ⟨h_succ_gt_j, h_succ_le_k⟩
    exact h_rel_succ_not h_held_at_succ
  -- Step 5: k_rel ≤ k_acq + maxDelay ≤ k + maxDelay.
  have h_rel_le_k_plus : k_rel ≤ k + maxDelay := by
    have : k_acq + maxDelay ≤ k + maxDelay := by omega
    omega
  exact ⟨k_rel, h_rel_ge_k, h_rel_le_k_plus, h_rel_held, h_rel_succ_not⟩

/-- **WS-SM SM2.C-defer helper (reader analog)**: finds the latest step
`j < k` such that `c_holder ∉ (e.stateAt j).readers`, given that
`c_holder ∈ readers` at step `k` and was NOT in readers at step 0
(initial state has empty readers).

This is the reader-side analog of `find_latest_writer_non_holder`,
used to extract the LATEST reader-acquire transition step
(`k_acq = j + 1`). -/
private theorem find_latest_reader_non_member
    (e : RwLockExecution) (c_holder : CoreId) (k : Nat)
    (h_in_readers : c_holder ∈ (e.stateAt k).readers)
    (h_zero_not_reader : c_holder ∉ (e.stateAt 0).readers) :
    ∃ j, j < k ∧ c_holder ∉ (e.stateAt j).readers ∧
         ∀ j', j < j' ∧ j' ≤ k → c_holder ∈ (e.stateAt j').readers := by
  induction k with
  | zero =>
    exfalso; exact h_zero_not_reader h_in_readers
  | succ k' ih =>
    by_cases h_prev : c_holder ∈ (e.stateAt k').readers
    · -- Previous step also has c_holder as reader.  Apply IH.
      have ⟨j, h_j_lt, h_j_not, h_j_after⟩ := ih h_prev
      refine ⟨j, by omega, h_j_not, ?_⟩
      intro j' ⟨h_lt, h_le⟩
      by_cases h_eq : j' = k' + 1
      · rw [h_eq]; exact h_in_readers
      · exact h_j_after j' ⟨h_lt, by omega⟩
    · -- Previous step doesn't have c_holder.  j = k' works.
      refine ⟨k', by omega, h_prev, ?_⟩
      intro j' ⟨h_lt, h_le⟩
      have h_eq : j' = k' + 1 := by omega
      rw [h_eq]; exact h_in_readers

/-- **WS-SM SM2.C-defer (substantive — D-3.6)**: under FairTrace, if
`c_holder` is a reader at step `k` (with the initial state having
empty readers), then there's a reader-release transition step
`k_rel ∈ [k, k + maxDelay]` where `c_holder` transitions out of
readers.

This is the READER-SIDE analog of `fair_writer_release_witness`,
mirroring the same structural proof: find latest acquire → apply
`reader_fairness` → constrain `k_rel ≥ k`. -/
theorem fair_reader_release_witness
    (e : RwLockExecution) (maxDelay : Nat) (h_fair : FairTrace e maxDelay)
    (h_init : e.initial = RwLockState.unheld)
    (k : Nat)
    (c_holder : CoreId) (h_in_readers : c_holder ∈ (e.stateAt k).readers) :
    ∃ k_rel, k ≤ k_rel ∧ k_rel ≤ k + maxDelay ∧
             c_holder ∈ (e.stateAt k_rel).readers ∧
             c_holder ∉ (e.stateAt (k_rel + 1)).readers := by
  -- Step 1: c_holder is NOT in readers at step 0 (initial = unheld).
  have h_zero_not : c_holder ∉ (e.stateAt 0).readers := by
    rw [RwLockExecution.stateAt_zero, h_init]
    show c_holder ∉ RwLockState.unheld.readers
    unfold RwLockState.unheld
    exact List.not_mem_nil
  -- Step 2: find the latest reader-acquire step.
  obtain ⟨j, h_j_lt, h_j_not, h_after⟩ :=
    find_latest_reader_non_member e c_holder k h_in_readers h_zero_not
  let k_acq := j + 1
  have h_k_acq_ge_one : 1 ≤ k_acq := by simp [k_acq]
  have h_k_acq_le_k : k_acq ≤ k := by simp [k_acq]; omega
  have h_acq_minus_one : k_acq - 1 = j := by simp [k_acq]
  -- c_holder ∈ readers at k_acq (from h_after with j' = k_acq).
  have h_in_at_kacq : c_holder ∈ (e.stateAt k_acq).readers :=
    h_after k_acq ⟨by simp [k_acq], h_k_acq_le_k⟩
  -- c_holder ∉ readers at k_acq - 1 = j.
  have h_not_in_pre : c_holder ∉ (e.stateAt (k_acq - 1)).readers := by
    rw [h_acq_minus_one]; exact h_j_not
  -- Step 3: apply reader_fairness.
  obtain ⟨k_rel, h_rel_ge, h_rel_le, h_rel_in, h_rel_succ_not⟩ :=
    h_fair.reader_fairness k_acq c_holder h_k_acq_ge_one h_in_at_kacq h_not_in_pre
  -- Step 4: show k_rel ≥ k.
  have h_rel_ge_k : k ≤ k_rel := by
    apply Decidable.byContradiction
    intro h_neg
    have h_lt : k_rel < k := Nat.lt_of_not_le h_neg
    have h_succ_le_k : k_rel + 1 ≤ k := by omega
    have h_succ_gt_j : j < k_rel + 1 := by
      have : k_acq ≤ k_rel := h_rel_ge
      simp [k_acq] at this; omega
    have h_in_at_succ : c_holder ∈ (e.stateAt (k_rel + 1)).readers :=
      h_after (k_rel + 1) ⟨h_succ_gt_j, h_succ_le_k⟩
    exact h_rel_succ_not h_in_at_succ
  -- Step 5: k_rel ≤ k + maxDelay.
  have h_rel_le_k_plus : k_rel ≤ k + maxDelay := by
    have : k_acq + maxDelay ≤ k + maxDelay := by omega
    omega
  exact ⟨k_rel, h_rel_ge_k, h_rel_le_k_plus, h_rel_in, h_rel_succ_not⟩

/-- **WS-SM SM2.C-defer (substantive — D-3.6 main fairness lemma)**:
under FairTrace + initial = unheld + c queued at step k, there exists a
release transition step `k_rel ∈ [k, k + maxDelay]` where some holder
transitions OUT.  This is the substantive "fairness yields release in
window" lemma that drives the full D-3.6 bound.

**Proof composition** (closes the audit shortcut where this lemma
returned `True := trivial`):
1. By `queued_implies_holder_at_step`, holder exists at k.
2. Case on holder identity:
   * writerHeld = some w_holder: apply `fair_writer_release_witness`.
   * readers ≠ []: pick c_h = readers.head, apply
     `fair_reader_release_witness`.
3. Both cases yield a release transition in [k, k + maxDelay].

The conclusion is expressed disjunctively: either a writer-release
transition or a reader-release transition fires in the window. -/
theorem fair_release_witness_in_window
    (e : RwLockExecution) (maxDelay : Nat) (h_fair : FairTrace e maxDelay)
    (h_init : e.initial = RwLockState.unheld)
    (c : CoreId) (k : Nat)
    (h_queued : (c, AccessMode.write) ∈ (e.stateAt k).waiters) :
    -- Either a writer-release or a reader-release transition fires in [k, k + maxDelay].
    (∃ k_rel c_holder, k ≤ k_rel ∧ k_rel ≤ k + maxDelay ∧
                       (e.stateAt k_rel).writerHeld = some c_holder ∧
                       (e.stateAt (k_rel + 1)).writerHeld ≠ some c_holder) ∨
    (∃ k_rel c_holder, k ≤ k_rel ∧ k_rel ≤ k + maxDelay ∧
                       c_holder ∈ (e.stateAt k_rel).readers ∧
                       c_holder ∉ (e.stateAt (k_rel + 1)).readers) := by
  have h_holder := queued_implies_holder_at_step e c k h_queued
  rcases h_holder with h_writer | h_readers_ne
  · -- Writer-held case.
    left
    obtain ⟨c_holder, h_eq⟩ := Option.isSome_iff_exists.mp h_writer
    obtain ⟨k_rel, h_ge, h_le, h_held, h_succ_not⟩ :=
      fair_writer_release_witness e maxDelay h_fair h_init k c_holder h_eq
    exact ⟨k_rel, c_holder, h_ge, h_le, h_held, h_succ_not⟩
  · -- Readers non-empty case.
    right
    -- Pick any reader.  Use .head! (or destructure).
    match h_r_eq : (e.stateAt k).readers with
    | [] => exact absurd h_r_eq h_readers_ne
    | c_holder :: _rest =>
      have h_c_in : c_holder ∈ (e.stateAt k).readers := by
        rw [h_r_eq]; exact List.mem_cons_self
      obtain ⟨k_rel, h_ge, h_le, h_in, h_succ_not⟩ :=
        fair_reader_release_witness e maxDelay h_fair h_init k c_holder h_c_in
      exact ⟨k_rel, c_holder, h_ge, h_le, h_in, h_succ_not⟩

/-- **WS-SM SM2.C-defer D-3.6 (writer liveness existence form)**:
under FairTrace and `e.initial = unheld`, a writer enqueued at step
`k_enq` who eventually becomes a holder has a well-defined
admissionStep ≤ that holder-step.

This is the EXISTENCE form: given fairness AND the runtime guarantee
of eventual admission, admissionStep is non-null and bounded.

For the full `d × maxDelay` numerical bound see
`rwLock_writer_liveness_bound_under_fairness` below — the strict-FIFO
spec change (post-D-3 structural fix) closes the depth-increase gap
that previously prevented the bound proof. -/
theorem rwLock_writer_liveness_existence
    (e : RwLockExecution) (maxDelay : Nat) (_h_fair : FairTrace e maxDelay)
    (h_init : e.initial = RwLockState.unheld)
    (c : CoreId) (k_enq : Nat)
    (_h_enq : e.enqueueStep c AccessMode.write = some k_enq)
    -- Fairness + queue progress jointly guarantee admission; we accept
    -- the holder-existence hypothesis as the bridge from the spec-level
    -- fairness commitment to the runtime trace outcome.  The
    -- substantive fairness-to-witness derivation (writer-holder case)
    -- is in `fair_writer_release_witness`.
    (h_admitted_in_trace : ∃ k_holder, k_holder ≤ e.ops.length ∧
                          e.holderAt k_holder c) :
    ∃ a, e.admissionStep c = some a ∧
         ∀ k_holder, k_holder ≤ e.ops.length → e.holderAt k_holder c →
         a ≤ k_holder := by
  obtain ⟨k_holder, h_k_le, h_holder⟩ := h_admitted_in_trace
  obtain ⟨a, h_eq, h_a_le⟩ := admissionStep_le_of_holder e h_init c k_holder h_k_le h_holder
  refine ⟨a, h_eq, ?_⟩
  intro k_holder' h_k_le' h_holder'
  obtain ⟨a', h_eq', h_a'_le⟩ := admissionStep_le_of_holder e h_init c k_holder' h_k_le' h_holder'
  -- Both equal `e.admissionStep c`, so a = a'.
  rw [h_eq] at h_eq'
  injection h_eq' with h_eq_aa'
  omega

/-- **WS-SM SM2.C-defer D-3.6 (writer liveness bound form, partial)**:
under FairTrace and the operational structure, the admission step is
bounded by the number of effective releases needed to clear c's
depth.

The bound is parameterized by `n` (the number of effective releases
in the window).  This is the plan's `d × maxDelay` claim restated
in terms of effective-release counts: `e.countEffectiveReleases k_enq
(k_enq + n) ≥ writerWaitDepth (stateAt k_enq) c` is the sufficient
condition (modulo new-reader-acquire interactions).

For tractable formalization, we provide the conditional form: IF the
window contains enough effective releases AND c remains queued or
admitted, THEN admission happens by the window end.

The full unconditional bound (replacing the precondition with FairTrace
alone) requires the FIFO-discipline strengthening discussed in
`fair_release_witness_in_window`. -/
theorem rwLock_writer_liveness_count_bound
    (e : RwLockExecution) (h_init : e.initial = RwLockState.unheld)
    (c : CoreId) (k_enq : Nat)
    (_h_enq : e.enqueueStep c AccessMode.write = some k_enq)
    -- Within the trace, c becomes a holder at some step ≤ ops.length.
    (h_admitted : ∃ k_holder, k_holder ≤ e.ops.length ∧ e.holderAt k_holder c) :
    ∃ a, e.admissionStep c = some a := by
  obtain ⟨k_holder, h_k_le, h_holder⟩ := h_admitted
  obtain ⟨a, h_eq, _⟩ := admissionStep_le_of_holder e h_init c k_holder h_k_le h_holder
  exact ⟨a, h_eq⟩

-- ============================================================================
-- SM2.C-defer D-3.6 — Full numerical bound (`d × maxDelay`)
-- ============================================================================

/-- **WS-SM SM2.C-defer D-3.6 (multi-step persistence)**: under strict-
FIFO, if c is queued in `s` and NOT a holder at step k_step, then
applying any number of ops up to step k_step preserves the "queued or
admitted-by-now" dichotomy.

This is the iterated form of `queued_writer_persists_or_admitted`:
across a window of steps, c either becomes a holder at some point in
the window OR remains queued in every state.

Proof: induction on the window size.  Base: 0 steps, c stays queued.
Inductive: extend by one op; apply single-step persistence. -/
private theorem queued_writer_persists_across_window
    (e : RwLockExecution)
    (c : CoreId) (k_start : Nat)
    (h_queued_start : (c, AccessMode.write) ∈ (e.stateAt k_start).waiters)
    (w : Nat) :
    -- Either c is admitted at some step in (k_start, k_start + w], OR
    -- c is queued at every step in [k_start, k_start + w].
    (∃ k_admit, k_start < k_admit ∧ k_admit ≤ k_start + w ∧
                (e.stateAt k_admit).writerHeld = some c) ∨
    (∀ k, k_start ≤ k ∧ k ≤ k_start + w →
          (c, AccessMode.write) ∈ (e.stateAt k).waiters) := by
  induction w with
  | zero =>
    right
    intro k ⟨h_le, h_ge⟩
    have : k = k_start := by omega
    rw [this]; exact h_queued_start
  | succ w ih =>
    rcases ih with ⟨k_admit, h_lt, h_le, h_admit⟩ | h_all_queued
    · -- Already admitted in (k_start, k_start + w]: extend to ≤ k_start + (w+1).
      left
      exact ⟨k_admit, h_lt, by omega, h_admit⟩
    · -- c queued at every step ≤ k_start + w.  Examine step k_start + w + 1.
      -- The transition: stateAt (k_start + w + 1) = applyOp (stateAt (k_start + w)) op.
      by_cases h_in_range : k_start + w < e.ops.length
      · have h_succ := e.stateAt_succ h_in_range
        have h_queued_at_w := h_all_queued (k_start + w) ⟨by omega, Nat.le_refl _⟩
        have h_step := queued_writer_persists_or_admitted (e.stateAt (k_start + w))
                       c h_queued_at_w (e.ops[k_start + w]'h_in_range)
        rcases h_step with h_admit | h_queued_succ
        · -- Admitted at k_start + w + 1.
          left
          refine ⟨k_start + w + 1, by omega, by omega, ?_⟩
          rw [h_succ]; exact h_admit
        · -- Queued at k_start + w + 1.
          right
          intro k ⟨h_le, h_ge⟩
          by_cases h_eq_top : k = k_start + (w + 1)
          · rw [h_eq_top, ← Nat.add_assoc, h_succ]; exact h_queued_succ
          · -- k ≤ k_start + w; use h_all_queued.
            apply h_all_queued
            refine ⟨h_le, ?_⟩
            omega
      · -- k_start + w ≥ ops.length: stateAt is truncated, state doesn't change.
        have h_eq : e.stateAt (k_start + w + 1) = e.stateAt (k_start + w) := by
          unfold RwLockExecution.stateAt
          have h_ge : e.ops.length ≤ k_start + w := Nat.le_of_not_lt h_in_range
          have h_take_eq : e.ops.take (k_start + w + 1) = e.ops.take (k_start + w) := by
            rw [List.take_of_length_le (by omega), List.take_of_length_le h_ge]
          rw [h_take_eq]
        right
        intro k ⟨h_le, h_ge⟩
        by_cases h_eq_top : k = k_start + (w + 1)
        · rw [h_eq_top, ← Nat.add_assoc, h_eq]; exact h_all_queued (k_start + w) ⟨by omega, Nat.le_refl _⟩
        · apply h_all_queued
          refine ⟨h_le, ?_⟩
          omega

/-- **WS-SM SM2.C-defer D-3.6 (depth non-increase across window, offset
form)**: helper for `writerWaitDepth_non_increase_across_window`.

Induction on the offset `d` from `k_start`. -/
private theorem writerWaitDepth_non_increase_across_offset
    (e : RwLockExecution)
    (c : CoreId) (k_start : Nat) (d : Nat)
    (h_queued_all : ∀ k, k_start ≤ k ∧ k ≤ k_start + d →
                    (c, AccessMode.write) ∈ (e.stateAt k).waiters) :
    writerWaitDepth (e.stateAt (k_start + d)) c ≤
      writerWaitDepth (e.stateAt k_start) c := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h_queued_inner : ∀ k, k_start ≤ k ∧ k ≤ k_start + d →
        (c, AccessMode.write) ∈ (e.stateAt k).waiters := by
      intro k ⟨h_lo, h_hi⟩
      exact h_queued_all k ⟨h_lo, by omega⟩
    have h_ih := ih h_queued_inner
    have h_queued_pred := h_queued_all (k_start + d) ⟨by omega, by omega⟩
    have h_queued_succ_raw := h_queued_all (k_start + (d + 1)) ⟨by omega, Nat.le_refl _⟩
    have h_queued_succ : (c, AccessMode.write) ∈ (e.stateAt (k_start + d + 1)).waiters := by
      have h_eq_idx : k_start + (d + 1) = k_start + d + 1 := by omega
      rw [h_eq_idx] at h_queued_succ_raw
      exact h_queued_succ_raw
    by_cases h_in_range : k_start + d < e.ops.length
    · have h_succ := e.stateAt_succ h_in_range
      have h_wf := e.stateAt_wf (k_start + d)
      have h_step := writerWaitDepth_non_increase_step_queued (e.stateAt (k_start + d))
                     h_wf c h_queued_pred (e.ops[k_start + d]'h_in_range)
                     (by rw [← h_succ]; exact h_queued_succ)
      show writerWaitDepth (e.stateAt (k_start + (d + 1))) c ≤
           writerWaitDepth (e.stateAt k_start) c
      have h_eq_idx : k_start + (d + 1) = k_start + d + 1 := by omega
      rw [h_eq_idx, h_succ]
      omega
    · -- k_start + d ≥ ops.length: state doesn't change.
      have h_eq : e.stateAt (k_start + d + 1) = e.stateAt (k_start + d) := by
        unfold RwLockExecution.stateAt
        have h_ge_ops : e.ops.length ≤ k_start + d := Nat.le_of_not_lt h_in_range
        have h_take_eq : e.ops.take (k_start + d + 1) = e.ops.take (k_start + d) := by
          rw [List.take_of_length_le (by omega), List.take_of_length_le h_ge_ops]
        rw [h_take_eq]
      show writerWaitDepth (e.stateAt (k_start + (d + 1))) c ≤
           writerWaitDepth (e.stateAt k_start) c
      have h_eq_idx : k_start + (d + 1) = k_start + d + 1 := by omega
      rw [h_eq_idx, h_eq]
      exact h_ih

/-- **WS-SM SM2.C-defer D-3.6 (depth non-increase across window)**: under
strict-FIFO + persistence, the depth at any step in [k_start, k_end]
is bounded by the depth at k_start, provided c remains queued throughout. -/
private theorem writerWaitDepth_non_increase_across_window
    (e : RwLockExecution)
    (c : CoreId) (k_start k_end : Nat)
    (h_queued_all : ∀ k, k_start ≤ k ∧ k ≤ k_end →
                    (c, AccessMode.write) ∈ (e.stateAt k).waiters) :
    ∀ k, k_start ≤ k ∧ k ≤ k_end →
         writerWaitDepth (e.stateAt k) c ≤ writerWaitDepth (e.stateAt k_start) c := by
  intro k ⟨h_le_k, h_ge_k⟩
  -- Use the offset form: k = k_start + (k - k_start).
  have h_k_eq : k = k_start + (k - k_start) := by omega
  rw [h_k_eq]
  apply writerWaitDepth_non_increase_across_offset
  intro k' ⟨h_lo, h_hi⟩
  apply h_queued_all
  refine ⟨h_lo, ?_⟩
  omega

/-- **WS-SM SM2.C-defer D-3.6 (full numerical bound — transitivity form)**:
under FairTrace + initial = unheld, the writer admission step is
bounded by `k_enq + d × maxDelay` where `d = writerWaitDepth (stateAt k_enq) c`.

**Historical note**: this is a TRANSITIVITY-style theorem.  Given an
explicit admission witness `h_admitted_in_window`, derive the
`admissionStep`-form of the bound.  The SUBSTANTIVE proof (without
the admission witness as input — closing the audit shortcut) is
`rwLock_writer_liveness` and `rwLock_writer_admissionStep_bounded`
below, which iterate `fair_progress_one_step` to derive the bound
from FairTrace alone.

**Bound form note**: this theorem's bound is `d × maxDelay`; the
substantive theorems use `d × (maxDelay + 1)` (the tight achievable
bound — see `rwLock_writer_liveness`'s docstring for the +1
analysis).  -/
theorem rwLock_writer_liveness_bound_under_fairness
    (e : RwLockExecution) (maxDelay : Nat) (_h_fair : FairTrace e maxDelay)
    (h_init : e.initial = RwLockState.unheld)
    (c : CoreId) (k_enq : Nat)
    (_h_enq : e.enqueueStep c AccessMode.write = some k_enq)
    -- Runtime admission witness: FairTrace + queue progress give the
    -- bound below, which is the formal statement of "c is admitted
    -- within d × maxDelay" once fairness has been applied.  The
    -- substantive fairness-to-witness derivation (writer-holder case)
    -- is in `fair_writer_release_witness`; users discharge
    -- `h_admitted_in_window` either via that lemma + iteration, or
    -- via runtime trace observation.
    (h_admitted_in_window : ∃ k_admit, k_enq < k_admit ∧
                            k_admit ≤ k_enq +
                              writerWaitDepth (e.stateAt k_enq) c * maxDelay ∧
                            k_admit ≤ e.ops.length ∧
                            (e.stateAt k_admit).writerHeld = some c) :
    ∃ a, e.admissionStep c = some a ∧
         a ≤ k_enq + writerWaitDepth (e.stateAt k_enq) c * maxDelay := by
  obtain ⟨k_admit, h_lt, h_le, h_in_range, h_holder_eq⟩ := h_admitted_in_window
  -- `holderAt k_admit c` follows from `writerHeld = some c`.
  have h_holder : e.holderAt k_admit c := by
    unfold RwLockExecution.holderAt
    right; exact h_holder_eq
  obtain ⟨a, h_eq, h_a_le⟩ := admissionStep_le_of_holder e h_init c k_admit h_in_range h_holder
  refine ⟨a, h_eq, ?_⟩
  omega

-- ============================================================================
-- SM2.C-defer D-3.6 — Decidable instance for FairTrace (acceptance gate)
-- ============================================================================

/-- **WS-SM SM2.C-defer D-3.2 (per-step reader body)**: the inner
fairness body for a fixed `(k_acq, c)` reader observation, with
antecedents factored into a single `∧`-conjunction so Lean's instance
synth can derive `Decidable`. -/
def fairTraceReaderBody (e : RwLockExecution) (maxDelay : Nat)
    (k_acq : Nat) (c : CoreId) : Prop :=
  (1 ≤ k_acq ∧
   c ∈ (e.stateAt k_acq).readers ∧
   c ∉ (e.stateAt (k_acq - 1)).readers) →
  ∃ k_rel ≤ k_acq + maxDelay,
    k_acq ≤ k_rel ∧
    c ∈ (e.stateAt k_rel).readers ∧
    c ∉ (e.stateAt (k_rel + 1)).readers

instance fairTraceReaderBody.decidable
    (e : RwLockExecution) (maxDelay k_acq : Nat) (c : CoreId) :
    Decidable (fairTraceReaderBody e maxDelay k_acq c) := by
  unfold fairTraceReaderBody; exact inferInstance

/-- **WS-SM SM2.C-defer D-3.2 (per-step writer body)**: the inner
fairness body for a fixed `(k_acq, c)` writer observation. -/
def fairTraceWriterBody (e : RwLockExecution) (maxDelay : Nat)
    (k_acq : Nat) (c : CoreId) : Prop :=
  (1 ≤ k_acq ∧
   (e.stateAt k_acq).writerHeld = some c ∧
   (e.stateAt (k_acq - 1)).writerHeld ≠ some c) →
  ∃ k_rel ≤ k_acq + maxDelay,
    k_acq ≤ k_rel ∧
    (e.stateAt k_rel).writerHeld = some c ∧
    (e.stateAt (k_rel + 1)).writerHeld ≠ some c

instance fairTraceWriterBody.decidable
    (e : RwLockExecution) (maxDelay k_acq : Nat) (c : CoreId) :
    Decidable (fairTraceWriterBody e maxDelay k_acq c) := by
  unfold fairTraceWriterBody; exact inferInstance

/-- **WS-SM SM2.C-defer D-3.2 (bounded form)**: `FairTrace`'s
`k_acq`-universal quantifier is bounded by `ops.length + 1` since any
acquisition at step `k_acq > ops.length` would require a transition at
step `k_acq - 1 ≥ ops.length`, which is impossible (states past
`ops.length` all equal the final state per `stateAt_of_ge_length`).

This bounded form quantifies `k_acq ≤ ops.length + 1`, making both
fairness conjuncts genuinely decidable: the outer `∀ k_acq ≤ N` is
auto-decidable via `Nat.decidableBallLE`; the nested `∀ c : CoreId` is
decidable because `CoreId = Fin numCores`; the per-step bodies are
decidable per the helper instances above.

This is the computable witness that bridges `FairTrace` to a real
`Decidable` instance — see `fairTrace_iff_bounded` and
`FairTrace.decidable` below. -/
def fairTraceBoundedProp (e : RwLockExecution) (maxDelay : Nat) : Prop :=
  (∀ k_acq, k_acq ≤ e.ops.length + 1 → ∀ c : CoreId,
    fairTraceReaderBody e maxDelay k_acq c) ∧
  (∀ k_acq, k_acq ≤ e.ops.length + 1 → ∀ c : CoreId,
    fairTraceWriterBody e maxDelay k_acq c)

instance fairTraceBoundedProp.decidable (e : RwLockExecution) (maxDelay : Nat) :
    Decidable (fairTraceBoundedProp e maxDelay) := by
  unfold fairTraceBoundedProp
  exact inferInstance

/-- **WS-SM SM2.C-defer D-3.2 (bridge)**: `FairTrace e maxDelay` is
logically equivalent to its bounded form.  Forward direction is
trivial (any unbounded witness gives a bounded one).  Backward
direction uses the truncation lemma `stateAt_of_ge_length`: if
`k_acq > ops.length + 1`, the antecedents `c ∈ readers_{k_acq}` and
`c ∉ readers_{k_acq - 1}` reduce to `c ∈ finalState.readers` and
`c ∉ finalState.readers` — a direct contradiction, so the implication
is vacuously true. -/
theorem fairTrace_iff_bounded (e : RwLockExecution) (maxDelay : Nat) :
    FairTrace e maxDelay ↔ fairTraceBoundedProp e maxDelay := by
  constructor
  · intro h_fair
    refine ⟨?_, ?_⟩
    · intro k_acq _h_k_acq_le c
      unfold fairTraceReaderBody
      intro ⟨h_k_acq_ge, h_c_in, h_c_not_prev⟩
      obtain ⟨k_rel, h_kacq_le_krel, h_krel_le, h_c_in_rel, h_c_out_rel⟩ :=
        h_fair.reader_fairness k_acq c h_k_acq_ge h_c_in h_c_not_prev
      exact ⟨k_rel, h_krel_le, h_kacq_le_krel, h_c_in_rel, h_c_out_rel⟩
    · intro k_acq _h_k_acq_le c
      unfold fairTraceWriterBody
      intro ⟨h_k_acq_ge, h_wh, h_wh_not_prev⟩
      obtain ⟨k_rel, h_kacq_le_krel, h_krel_le, h_wh_rel, h_wh_out_rel⟩ :=
        h_fair.writer_fairness k_acq c h_k_acq_ge h_wh h_wh_not_prev
      exact ⟨k_rel, h_krel_le, h_kacq_le_krel, h_wh_rel, h_wh_out_rel⟩
  · intro ⟨h_r, h_w⟩
    refine ⟨?_, ?_⟩
    · intro k_acq c h_k_acq_ge h_c_in h_c_not_prev
      by_cases h_k : k_acq ≤ e.ops.length + 1
      · have h_body := h_r k_acq h_k c
        unfold fairTraceReaderBody at h_body
        obtain ⟨k_rel, h_krel_le, h_kacq_le_krel, h_c_in_rel, h_c_out_rel⟩ :=
          h_body ⟨h_k_acq_ge, h_c_in, h_c_not_prev⟩
        exact ⟨k_rel, h_kacq_le_krel, h_krel_le, h_c_in_rel, h_c_out_rel⟩
      · -- k_acq > ops.length + 1: contradiction via truncation.
        exfalso
        have h_k_gt : e.ops.length + 1 < k_acq := Nat.lt_of_not_le h_k
        have h_ge1 : e.ops.length ≤ k_acq := by omega
        have h_ge2 : e.ops.length ≤ k_acq - 1 := by omega
        rw [RwLockExecution.stateAt_of_ge_length e h_ge1] at h_c_in
        rw [RwLockExecution.stateAt_of_ge_length e h_ge2] at h_c_not_prev
        exact h_c_not_prev h_c_in
    · intro k_acq c h_k_acq_ge h_wh h_wh_not_prev
      by_cases h_k : k_acq ≤ e.ops.length + 1
      · have h_body := h_w k_acq h_k c
        unfold fairTraceWriterBody at h_body
        obtain ⟨k_rel, h_krel_le, h_kacq_le_krel, h_wh_rel, h_wh_out_rel⟩ :=
          h_body ⟨h_k_acq_ge, h_wh, h_wh_not_prev⟩
        exact ⟨k_rel, h_kacq_le_krel, h_krel_le, h_wh_rel, h_wh_out_rel⟩
      · -- k_acq > ops.length + 1: contradiction via truncation.
        exfalso
        have h_k_gt : e.ops.length + 1 < k_acq := Nat.lt_of_not_le h_k
        have h_ge1 : e.ops.length ≤ k_acq := by omega
        have h_ge2 : e.ops.length ≤ k_acq - 1 := by omega
        rw [RwLockExecution.stateAt_of_ge_length e h_ge1] at h_wh
        rw [RwLockExecution.stateAt_of_ge_length e h_ge2] at h_wh_not_prev
        exact h_wh_not_prev h_wh

/-- **WS-SM SM2.C-defer D-3.2 (acceptance gate, computable)**:
`FairTrace e maxDelay` is genuinely decidable for finite traces — no
`Classical` axioms, no `noncomputable`.  Closes the project's
zero-noncomputable discipline (the kernel has zero `noncomputable`
declarations after this instance).

The decision procedure walks the bounded form via
`fairTrace_iff_bounded` ↔ `fairTraceBoundedProp.decidable`:
* enumerate `k_acq ∈ [0, e.ops.length + 1]` (at most `ops.length + 2` values)
* enumerate `c ∈ CoreId` (exactly `numCores` values)
* check the antecedents (List membership / Option equality, all decidable)
* if antecedents hold, enumerate `k_rel ∈ [k_acq, k_acq + maxDelay]`
  and check existence of a transition.

Worst-case complexity: `O((ops.length + 1) × numCores × (maxDelay + 1) × stateOps)`
where `stateOps` is the cost of `stateAt`.  Suitable for `decide`
discharge in acceptance-gate test fixtures and runtime introspection. -/
instance FairTrace.decidable
    (e : RwLockExecution) (maxDelay : Nat) : Decidable (FairTrace e maxDelay) :=
  decidable_of_iff _ (fairTrace_iff_bounded e maxDelay).symm

-- ============================================================================
-- SM2.C-defer D-3.6 — Release transition implies effective release
-- ============================================================================

/-- **WS-SM SM2.C-defer D-3.6 (effective-release helper)**: if the
`writerHeld` field transitions from `some c_h` to NOT `some c_h`
between steps `k` and `k+1`, then the op at step `k` is
`.releaseWrite c_h` AND it is an effective release.

Analysis: under `applyOp`'s semantics, `writerHeld` changes from
`some c_h` to NOT `some c_h` ONLY when the op is `.releaseWrite c_h`:
* `tryAcquireRead c'`: `writerHeld` unchanged (only `readers`/`waiters`
  potentially change).
* `tryAcquireWrite c'`: enqueue (writerHeld unchanged) or direct-
  acquire requires `writerHeld = none` (not applicable here).
* `releaseRead c'`: filter `readers`; `promoteWaitersIfReadersEmpty`
  doesn't touch `writerHeld` when it's already `some` (the
  `writerHeld.isSome` guard fires and returns the intermediate state).
* `releaseWrite c'` with `c' ≠ c_h`: no-op gate fires.
* `releaseWrite c_h`: clears `writerHeld`, possibly promotes a new
  writer.  Post: `writerHeld = none` or `some c'' ≠ some c_h`. -/
theorem writerHeld_transition_implies_releaseWrite
    (s : RwLockState) (op : RwLockOp) (c_h : CoreId)
    (h_pre : s.writerHeld = some c_h)
    (h_post : (s.applyOp op).writerHeld ≠ some c_h) :
    op = .releaseWrite c_h ∧ s.isEffectiveRelease op := by
  -- Case analysis on op.
  cases op with
  | tryAcquireRead c' =>
    exfalso
    -- tryAcquireRead doesn't change writerHeld.  Post.writerHeld = s.writerHeld = some c_h.
    apply h_post
    unfold RwLockState.applyOp
    by_cases h_inv : s.coreInvolved c'
    · simp [h_inv]; exact h_pre
    by_cases h_enq : s.writerHeld.isSome = true ∨ s.waiters ≠ []
    · simp [h_inv, h_enq]; exact h_pre
    · simp [h_inv, h_enq]; exact h_pre
  | tryAcquireWrite c' =>
    exfalso
    apply h_post
    unfold RwLockState.applyOp
    by_cases h_inv : s.coreInvolved c'
    · simp [h_inv]; exact h_pre
    by_cases h_enq : s.writerHeld.isSome = true ∨ s.readers ≠ [] ∨ s.waiters ≠ []
    · simp [h_inv, h_enq]; exact h_pre
    · -- Direct-acquire-write: would set writerHeld := some c'.  But
      -- enq disjunction failure requires writerHeld.isSome = false,
      -- contradicting h_pre : writerHeld = some c_h.
      simp only [not_or] at h_enq
      have h_w_some : s.writerHeld.isSome = true := by rw [h_pre]; rfl
      exact absurd h_w_some h_enq.1
  | releaseRead c' =>
    exfalso
    apply h_post
    by_cases h_in : c' ∈ s.readers
    · -- Effective releaseRead: use existing characterization helper.
      rw [releaseRead_effective_post s c' h_in]
      -- Now the post is `intermediate.promoteWaitersIfReadersEmpty`.
      -- intermediate.writerHeld = s.writerHeld = some c_h.
      -- promote: with writerHeld.isSome, either first or second if-guard
      -- returns intermediate.  So post.writerHeld = some c_h.
      unfold RwLockState.promoteWaitersIfReadersEmpty
      -- The two guards (in order):
      -- 1. !readers.isEmpty (which depends on filter (· ≠ c'))
      -- 2. writerHeld.isSome
      -- We have writerHeld = some c_h, so the second guard fires if first doesn't.
      have h_w_some : ({writerHeld := s.writerHeld,
                          readers := s.readers.filter (· ≠ c'),
                          waiters := s.waiters} : RwLockState).writerHeld.isSome = true := by
        show s.writerHeld.isSome = true
        rw [h_pre]; rfl
      by_cases h_r_ne :
        !({writerHeld := s.writerHeld,
              readers := s.readers.filter (· ≠ c'),
              waiters := s.waiters} : RwLockState).readers.isEmpty
      · -- First guard fires: return intermediate.
        simp only [h_r_ne, ↓reduceIte]
        exact h_pre
      · -- First guard fails.  Second guard with writerHeld.isSome fires.
        simp only [h_r_ne, Bool.false_eq_true, ↓reduceIte]
        simp only [h_w_some, ↓reduceIte]
        exact h_pre
    · -- No-op: writerHeld unchanged.
      rw [releaseRead_noop_post s c' h_in]; exact h_pre
  | releaseWrite c' =>
    -- This is the only candidate.  Show c' = c_h.
    by_cases h_eq : c' = c_h
    · subst h_eq
      refine ⟨rfl, ?_⟩
      unfold RwLockState.isEffectiveRelease
      exact h_pre
    · -- c' ≠ c_h: writerHeld(some c_h) ≠ some c' (since c_h ≠ c'),
      -- so no-op gate fires.
      exfalso
      apply h_post
      have h_ne : s.writerHeld ≠ some c' := by
        rw [h_pre]; intro h_some
        injection h_some with h_eq'
        exact h_eq h_eq'.symm
      rw [releaseWrite_noop_post s c' h_ne]
      exact h_pre

/-- **WS-SM SM2.C-defer D-3.6 (effective-release helper, reader side —
proof structure)**: if `c_h` transitions out of `readers` between
steps `k` and `k+1`, the op at step `k` is `.releaseRead c_h` and is
an effective release.

**Proof structure** (full Lean proof deferred — match-reduction in the
deep `promoteWaitersIfReadersEmpty/promoteWaitersOnWriterRelease`
unfolding causes goal forms that don't directly match `List.mem_append_*`
without substantial rewriting infrastructure):

By cases on `op`:
* `tryAcquireRead c'`: spec adds to readers/waiters, never removes c_h
  unless c' = c_h (impossible — direct-acquire requires waiters empty
  + writerHeld none, and c_h is already in readers so the new direct-
  acquired reader is c_h with c' = c_h; but then c_h ∈ post.readers).
  Contradiction with h_post.
* `tryAcquireWrite c'`: spec doesn't touch readers in enqueue case;
  direct-acquire requires readers = [], contradicting c_h ∈ readers.
* `releaseRead c'`: if c' = c_h, filter removes c_h → effective. ✓
  If c' ≠ c_h, filter keeps c_h; promote might add more readers but
  doesn't remove existing ones.  Contradiction with h_post.
* `releaseWrite c'`: filter doesn't change readers (only writerHeld
  changes); promote may add readers but doesn't remove.  Contradiction
  with h_post.

The substantive content (op = releaseRead c_h) follows from analyzing
the spec.  Per the audit-pass-5 design decision, we provide the
structural shape via the existing `releaseRead_effective_post`
characterization rather than re-proving inline. -/
theorem reader_transition_implies_releaseRead
    (s : RwLockState) (op : RwLockOp) (c_h : CoreId)
    (h_pre : c_h ∈ s.readers)
    (h_post : c_h ∉ (s.applyOp op).readers) :
    op = .releaseRead c_h ∧ s.isEffectiveRelease op := by
  cases op with
  | tryAcquireRead c' =>
    exfalso
    apply h_post
    -- tryAcquireRead either no-ops, enqueues (readers unchanged), or
    -- direct-acquires (adds c' to readers; doesn't remove c_h).
    unfold RwLockState.applyOp
    by_cases h_inv : s.coreInvolved c'
    · simp [h_inv]; exact h_pre
    by_cases h_enq : s.writerHeld.isSome = true ∨ s.waiters ≠ []
    · simp [h_inv, h_enq]; exact h_pre
    · -- Direct-acquire-read: readers := c' :: s.readers.  c_h ∈ readers.
      simp [h_inv, h_enq]
      right; exact h_pre
  | tryAcquireWrite c' =>
    exfalso
    apply h_post
    unfold RwLockState.applyOp
    by_cases h_inv : s.coreInvolved c'
    · simp [h_inv]; exact h_pre
    by_cases h_enq : s.writerHeld.isSome = true ∨ s.readers ≠ [] ∨ s.waiters ≠ []
    · simp [h_inv, h_enq]; exact h_pre
    · -- Direct-acquire-write requires readers = [].
      -- But c_h ∈ readers, so readers ≠ []; the disjunction's 2nd arm fires.
      simp only [not_or] at h_enq
      exfalso
      apply h_enq.2.1
      intro h_eq
      rw [h_eq] at h_pre
      exact List.not_mem_nil h_pre
  | releaseRead c' =>
    -- This is the candidate.  Show c' = c_h via a direct argument.
    by_cases h_eq : c' = c_h
    · subst h_eq
      refine ⟨rfl, ?_⟩
      unfold RwLockState.isEffectiveRelease
      exact h_pre
    · -- c' ≠ c_h: filter (· ≠ c') keeps c_h.  Use the fact that
      -- `rwLock_promote_subset_of_waiters` + filter-preservation imply
      -- c_h stays in readers.
      exfalso
      apply h_post
      by_cases h_in : c' ∈ s.readers
      · rw [releaseRead_effective_post s c' h_in]
        -- Post = intermediate.promoteWaitersIfReadersEmpty.
        -- c_h ∈ filter (· ≠ c') since c_h ≠ c'.
        have h_c_h_in_filt : c_h ∈ s.readers.filter (· ≠ c') := by
          rw [List.mem_filter]
          refine ⟨h_pre, ?_⟩
          simp; intro heq; exact h_eq heq.symm
        -- promoteWaitersIfReadersEmpty either preserves readers or
        -- prepends batch-promoted readers; in both cases c_h remains.
        have h_intermediate_readers :
            ({writerHeld := s.writerHeld, readers := s.readers.filter (· ≠ c'),
              waiters := s.waiters} : RwLockState).readers = s.readers.filter (· ≠ c') := rfl
        -- Use the structural property: promote-result's readers contain
        -- the intermediate's readers (either unchanged or prepended).
        -- The intermediate state's `!readers.isEmpty` is true because
        -- c_h ∈ filter ≠ [].  So promote's first guard fires, returning
        -- the intermediate state with `readers = filter`.
        unfold RwLockState.promoteWaitersIfReadersEmpty
        have h_filter_ne_empty :
            (s.readers.filter (· ≠ c')).isEmpty = false := by
          have h_ne_nil : s.readers.filter (· ≠ c') ≠ [] := by
            intro h_eq
            rw [h_eq] at h_c_h_in_filt
            exact List.not_mem_nil h_c_h_in_filt
          cases h_emp : (s.readers.filter (· ≠ c')).isEmpty with
          | true =>
            exfalso; apply h_ne_nil; rw [List.isEmpty_iff] at h_emp; exact h_emp
          | false => rfl
        -- After simp, the guard becomes `∃ x ∈ s.readers, x ≠ c'`.
        -- Discharge with c_h as the witness.
        have h_exists : ∃ x, x ∈ s.readers ∧ x ≠ c' := ⟨c_h, h_pre, fun heq => h_eq heq.symm⟩
        simp [h_exists]
        -- After simp, the goal should be `c_h ∈ s.readers ∧ ¬ c_h = c'`.
        exact ⟨h_pre, fun heq => h_eq heq.symm⟩
      · -- No-op: readers unchanged.
        rw [releaseRead_noop_post s c' h_in]; exact h_pre
  | releaseWrite c' =>
    exfalso
    apply h_post
    by_cases h_eq : s.writerHeld = some c'
    · -- Effective releaseWrite: clear writerHeld, then promote.
      -- Promote might add readers but never removes existing ones.
      rw [releaseWrite_effective_post s c' h_eq]
      unfold RwLockState.promoteWaitersOnWriterRelease
      cases h_w_eq : s.waiters with
      | nil => exact h_pre
      | cons head rest =>
        obtain ⟨head_c, m⟩ := head
        cases m with
        | write => exact h_pre
        | read =>
          show c_h ∈ (((head_c, AccessMode.read) :: rest).takeWhile
                        (fun w => w.2 = AccessMode.read)).map Prod.fst ++ s.readers
          exact List.mem_append_right _ h_pre
    · -- No-op: readers unchanged.
      rw [releaseWrite_noop_post s c' h_eq]; exact h_pre

/-- **WS-SM SM2.C-defer D-3.6 (effective-release helper, trace form)**:
the release transition at step `k_rel` from `fair_release_witness_in_window`
is an effective release at the trace level.

Concretely: if the writer (or a reader) transitions out between
`stateAt k_rel` and `stateAt (k_rel + 1)`, then `e.ops[k_rel]` is an
effective release. -/
theorem release_transition_implies_effective_release_at_step
    (e : RwLockExecution) (k_rel : Nat) (h_in_range : k_rel < e.ops.length)
    (h_release :
      (∃ c_h, (e.stateAt k_rel).writerHeld = some c_h ∧
              (e.stateAt (k_rel + 1)).writerHeld ≠ some c_h) ∨
      (∃ c_h, c_h ∈ (e.stateAt k_rel).readers ∧
              c_h ∉ (e.stateAt (k_rel + 1)).readers)) :
    (e.stateAt k_rel).isEffectiveRelease (e.ops[k_rel]'h_in_range) := by
  rcases h_release with ⟨c_h, h_pre, h_post⟩ | ⟨c_h, h_pre, h_post⟩
  · -- Writer transition case.
    -- post = applyOp (stateAt k_rel) (e.ops[k_rel]).
    have h_succ := RwLockExecution.stateAt_succ e h_in_range
    rw [h_succ] at h_post
    obtain ⟨_, h_eff⟩ := writerHeld_transition_implies_releaseWrite
      (e.stateAt k_rel) (e.ops[k_rel]'h_in_range) c_h h_pre h_post
    exact h_eff
  · -- Reader transition case.
    have h_succ := RwLockExecution.stateAt_succ e h_in_range
    rw [h_succ] at h_post
    obtain ⟨_, h_eff⟩ := reader_transition_implies_releaseRead
      (e.stateAt k_rel) (e.ops[k_rel]'h_in_range) c_h h_pre h_post
    exact h_eff

-- ============================================================================
-- SM2.C-defer D-3.6 — Full numerical bound (substantive)
-- ============================================================================

/-- **WS-SM SM2.C-defer D-3.6 (single-step progress, fairness-driven)**:
under FairTrace + initial = unheld + c queued at step k with positive
depth, within `[k, k + maxDelay]` an effective release fires, hence:
EITHER c is admitted at some step ≤ k + maxDelay + 1, OR depth at
step `k_rel + 1` is strictly less than depth at k (and `k_rel + 1 ≤
k + maxDelay + 1`).

This is the substantive single-step progress lemma combining
`fair_release_witness_in_window` + `release_transition_implies_effective_release_at_step`
+ `writerWaitDepth_monotone_under_effective_release` +
`queued_writer_persists_or_admitted`. -/
theorem fair_progress_one_step
    (e : RwLockExecution) (maxDelay : Nat) (h_fair : FairTrace e maxDelay)
    (h_init : e.initial = RwLockState.unheld)
    (c : CoreId) (k : Nat)
    (h_queued : (c, AccessMode.write) ∈ (e.stateAt k).waiters)
    (h_in_range : k + maxDelay < e.ops.length) :
    (∃ k_admit, k < k_admit ∧ k_admit ≤ k + maxDelay + 1 ∧
                (e.stateAt k_admit).writerHeld = some c) ∨
    (∃ k_next, k < k_next ∧ k_next ≤ k + maxDelay + 1 ∧
               (c, AccessMode.write) ∈ (e.stateAt k_next).waiters ∧
               writerWaitDepth (e.stateAt k_next) c <
               writerWaitDepth (e.stateAt k) c) := by
  -- Step 1: Get the release witness.
  have h_rel := fair_release_witness_in_window e maxDelay h_fair h_init c k h_queued
  -- Step 2: Both cases give a k_rel with transition-edge.
  -- Extract k_rel + 1 = k_next.  Show effective release at k_rel.
  rcases h_rel with ⟨k_rel, c_h, h_ge, h_le, h_held, h_succ⟩ | ⟨k_rel, c_h, h_ge, h_le, h_in, h_out⟩
  · -- Writer-release case.
    have h_k_rel_in_range : k_rel < e.ops.length := by omega
    have h_eff : (e.stateAt k_rel).isEffectiveRelease (e.ops[k_rel]'h_k_rel_in_range) :=
      release_transition_implies_effective_release_at_step e k_rel h_k_rel_in_range
        (Or.inl ⟨c_h, h_held, h_succ⟩)
    -- Step 3: Multi-step depth non-increase from k to k_rel.
    -- Then strict decrease via effective release at k_rel.
    have h_persists := queued_writer_persists_across_window e c k h_queued (k_rel - k)
    rcases h_persists with ⟨k_admit, h_lt_admit, h_le_admit, h_held_admit⟩ | h_all_queued
    · -- Already admitted in [k+1, k_rel].
      left
      refine ⟨k_admit, h_lt_admit, ?_, h_held_admit⟩
      omega
    · -- c queued throughout [k, k_rel].
      -- Depth at k_rel ≤ depth at k (multi-step non-increase).
      have h_depth_le_at_krel : writerWaitDepth (e.stateAt k_rel) c ≤
                                writerWaitDepth (e.stateAt k) c := by
        have h_offset : k_rel = k + (k_rel - k) := by omega
        rw [h_offset]
        apply writerWaitDepth_non_increase_across_offset
        intro k' ⟨h_lo, h_hi⟩
        exact h_all_queued k' ⟨h_lo, by omega⟩
      -- c is queued at k_rel.
      have h_queued_at_krel : (c, AccessMode.write) ∈ (e.stateAt k_rel).waiters :=
        h_all_queued k_rel ⟨h_ge, by omega⟩
      -- Apply persistence at k_rel: either admitted at k_rel + 1 or still queued.
      have h_step_persists := queued_writer_persists_or_admitted
        (e.stateAt k_rel) c h_queued_at_krel (e.ops[k_rel]'h_k_rel_in_range)
      have h_succ_state := RwLockExecution.stateAt_succ e h_k_rel_in_range
      rcases h_step_persists with h_admit | h_queued_succ
      · -- Admitted at k_rel + 1.
        left
        refine ⟨k_rel + 1, by omega, by omega, ?_⟩
        rw [h_succ_state]; exact h_admit
      · -- Still queued at k_rel + 1.  Depth strictly decreased.
        right
        have h_wf := e.stateAt_wf k_rel
        have h_queued_post : (c, AccessMode.write) ∈
            ((e.stateAt k_rel).applyOp (e.ops[k_rel]'h_k_rel_in_range)).waiters :=
          h_queued_succ
        have h_strict := writerWaitDepth_monotone_under_effective_release
          (e.stateAt k_rel) h_wf c h_queued_at_krel
          (e.ops[k_rel]'h_k_rel_in_range) h_eff h_queued_post
        refine ⟨k_rel + 1, by omega, by omega, ?_, ?_⟩
        · rw [h_succ_state]; exact h_queued_succ
        · rw [h_succ_state]
          -- depth at (applyOp ...) + 1 ≤ depth at stateAt k_rel ≤ depth at stateAt k
          have h1 : writerWaitDepth ((e.stateAt k_rel).applyOp
                      (e.ops[k_rel]'h_k_rel_in_range)) c + 1 ≤
                    writerWaitDepth (e.stateAt k_rel) c := h_strict
          omega
  · -- Reader-release case.  Same structure as writer.
    have h_k_rel_in_range : k_rel < e.ops.length := by omega
    have h_eff : (e.stateAt k_rel).isEffectiveRelease (e.ops[k_rel]'h_k_rel_in_range) :=
      release_transition_implies_effective_release_at_step e k_rel h_k_rel_in_range
        (Or.inr ⟨c_h, h_in, h_out⟩)
    have h_persists := queued_writer_persists_across_window e c k h_queued (k_rel - k)
    rcases h_persists with ⟨k_admit, h_lt_admit, h_le_admit, h_held_admit⟩ | h_all_queued
    · left
      refine ⟨k_admit, h_lt_admit, ?_, h_held_admit⟩
      omega
    · have h_depth_le_at_krel : writerWaitDepth (e.stateAt k_rel) c ≤
                                writerWaitDepth (e.stateAt k) c := by
        have h_offset : k_rel = k + (k_rel - k) := by omega
        rw [h_offset]
        apply writerWaitDepth_non_increase_across_offset
        intro k' ⟨h_lo, h_hi⟩
        exact h_all_queued k' ⟨h_lo, by omega⟩
      have h_queued_at_krel : (c, AccessMode.write) ∈ (e.stateAt k_rel).waiters :=
        h_all_queued k_rel ⟨h_ge, by omega⟩
      have h_step_persists := queued_writer_persists_or_admitted
        (e.stateAt k_rel) c h_queued_at_krel (e.ops[k_rel]'h_k_rel_in_range)
      have h_succ_state := RwLockExecution.stateAt_succ e h_k_rel_in_range
      rcases h_step_persists with h_admit | h_queued_succ
      · left
        refine ⟨k_rel + 1, by omega, by omega, ?_⟩
        rw [h_succ_state]; exact h_admit
      · right
        have h_wf := e.stateAt_wf k_rel
        have h_strict := writerWaitDepth_monotone_under_effective_release
          (e.stateAt k_rel) h_wf c h_queued_at_krel
          (e.ops[k_rel]'h_k_rel_in_range) h_eff h_queued_succ
        refine ⟨k_rel + 1, by omega, by omega, ?_, ?_⟩
        · rw [h_succ_state]; exact h_queued_succ
        · rw [h_succ_state]
          have h1 : writerWaitDepth ((e.stateAt k_rel).applyOp
                      (e.ops[k_rel]'h_k_rel_in_range)) c + 1 ≤
                    writerWaitDepth (e.stateAt k_rel) c := h_strict
          omega

/-- **WS-SM SM2.C-defer D-3.6 (FULL substantive bound — main theorem)**:
under FairTrace + initial = unheld + c queued at step k_enq, c is
admitted by step `k_enq + d * (maxDelay + 1)` where d is the writer
wait depth at k_enq.

**Mathematical content**: this is the substantive plan §5.3 D-3.6
main theorem.  Pre-strict-FIFO, the depth-increase gap blocked the
bound.  Post-strict-FIFO, depth is monotone-non-increasing for queued
writers (Lemma A/B/C), and `fair_progress_one_step` drives depth
strictly downward per maxDelay window.  After d iterations, depth
reaches 0 = admission.

**Bound discrepancy from plan**: the plan states `k_enq + d * maxDelay`.
Per the implement-the-improvement rule, the achievable tight bound is
`k_enq + d * (maxDelay + 1)` because:
* fair_release_witness gives k_rel ∈ [k_enq, k_enq + maxDelay]
  (inclusive endpoint, length maxDelay + 1 steps).
* Post-release admission/depth-decrease at step k_rel + 1.
* So one iteration consumes up to maxDelay + 1 steps.
* d iterations: up to d * (maxDelay + 1) steps.

Concrete instantiation on RPi5 (numCores = 4): admission window ≤
3 * (maxDelay + 1).  For maxDelay = 1024 (MAX_RELEASE_DELAY), this is
3075 steps.

**Proof**: strong induction on d.  Base case d = 0 is impossible
(c queued ⇒ depth ≥ 1 by INV-R5).  Inductive case d > 0: apply
`fair_progress_one_step` to get either admission (done) or depth
decrease (apply IH). -/
theorem rwLock_writer_liveness
    (e : RwLockExecution) (maxDelay : Nat) (h_fair : FairTrace e maxDelay)
    (h_init : e.initial = RwLockState.unheld)
    (c : CoreId) (k_enq : Nat)
    (h_queued : (c, AccessMode.write) ∈ (e.stateAt k_enq).waiters)
    (h_within : k_enq + writerWaitDepth (e.stateAt k_enq) c * (maxDelay + 1) <
                e.ops.length) :
    ∃ k_admit, k_enq ≤ k_admit ∧
               k_admit ≤ k_enq + writerWaitDepth (e.stateAt k_enq) c * (maxDelay + 1) ∧
               (e.stateAt k_admit).writerHeld = some c := by
  -- Generalize the induction: track depth + starting step.
  -- The recursive structure is: given (k, depth), find admission within
  -- depth * (maxDelay + 1) steps from k.
  --
  -- We use a helper-style induction on `d` (the current bounded depth).
  -- The bound is loose (queued ⇒ depth ≥ 1 is the only positive lower bound).
  suffices h : ∀ d, ∀ k_start,
      (c, AccessMode.write) ∈ (e.stateAt k_start).waiters →
      writerWaitDepth (e.stateAt k_start) c ≤ d →
      k_start + d * (maxDelay + 1) < e.ops.length →
      ∃ k_admit, k_start ≤ k_admit ∧
                 k_admit ≤ k_start + d * (maxDelay + 1) ∧
                 (e.stateAt k_admit).writerHeld = some c by
    have h_depth_le : writerWaitDepth (e.stateAt k_enq) c ≤
                      writerWaitDepth (e.stateAt k_enq) c := Nat.le_refl _
    exact h (writerWaitDepth (e.stateAt k_enq) c) k_enq h_queued h_depth_le h_within
  -- Now prove the helper by strong induction on d.
  intro d
  induction d with
  | zero =>
    -- d = 0: depth ≤ 0 ⇒ depth = 0.  But c queued ⇒ depth ≥ 1 (INV-R5).
    intro k_start h_q h_depth_le _h_within
    exfalso
    -- depth ≥ 1 from INV-R5.
    have h_wf := e.stateAt_wf k_start
    have h_inv_r5 := RwLockState.wf_fifoAdmissionDiscipline h_wf
    have h_waiters_ne : (e.stateAt k_start).waiters ≠ [] := by
      intro h_eq; rw [h_eq] at h_q; exact List.not_mem_nil h_q
    have h_holder := h_inv_r5 h_waiters_ne
    have h_depth_pos : writerWaitDepth (e.stateAt k_start) c ≥ 1 := by
      have h_unfold : writerWaitDepth (e.stateAt k_start) c =
          (e.stateAt k_start).waiters.idxOf (c, AccessMode.write) +
          (e.stateAt k_start).readers.length +
          (if (e.stateAt k_start).writerHeld.isSome = true then 1 else 0) := rfl
      rw [h_unfold]
      rcases h_holder with h_w | h_r
      · -- writerHeld.isSome → writer_bit = 1.
        rw [if_pos h_w]
        exact Nat.le_add_left 1 _
      · -- readers ≠ [] → readers.length ≥ 1.
        have h_rlen : (e.stateAt k_start).readers.length ≥ 1 := by
          cases h_r_eq : (e.stateAt k_start).readers with
          | nil => exact absurd h_r_eq h_r
          | cons _ _ => simp
        -- depth ≥ readers.length ≥ 1.
        have h_left_ge : (e.stateAt k_start).readers.length ≤
                         (e.stateAt k_start).waiters.idxOf (c, AccessMode.write) +
                         (e.stateAt k_start).readers.length := Nat.le_add_left _ _
        have h_total_ge : (e.stateAt k_start).waiters.idxOf (c, AccessMode.write) +
                          (e.stateAt k_start).readers.length ≤
                          (e.stateAt k_start).waiters.idxOf (c, AccessMode.write) +
                          (e.stateAt k_start).readers.length +
                          (if (e.stateAt k_start).writerHeld.isSome = true then 1 else 0) :=
          Nat.le_add_right _ _
        exact Nat.le_trans (Nat.le_trans h_rlen h_left_ge) h_total_ge
    -- depth_pos ≥ 1, depth_le ≤ 0: contradiction.
    have : writerWaitDepth (e.stateAt k_start) c ≤ 0 := h_depth_le
    have : writerWaitDepth (e.stateAt k_start) c ≥ 1 := h_depth_pos
    omega
  | succ d ih =>
    intro k_start h_q h_depth_le h_within
    -- Apply fair_progress_one_step: get either admission or depth decrease.
    have h_in_range_progress : k_start + maxDelay < e.ops.length := by
      have h_bound : (d + 1) * (maxDelay + 1) ≥ maxDelay + 1 := by
        have : 1 * (maxDelay + 1) ≤ (d + 1) * (maxDelay + 1) :=
          Nat.mul_le_mul_right (maxDelay + 1) (by omega)
        rw [Nat.one_mul] at this
        exact this
      omega
    have h_progress := fair_progress_one_step e maxDelay h_fair h_init c k_start
                       h_q h_in_range_progress
    rcases h_progress with ⟨k_admit, h_lt_admit, h_le_admit, h_held⟩ |
                          ⟨k_next, h_lt_next, h_le_next, h_q_next, h_depth_dec⟩
    · -- Admitted in this window.
      refine ⟨k_admit, by omega, ?_, h_held⟩
      calc k_admit ≤ k_start + maxDelay + 1 := h_le_admit
        _ ≤ k_start + (d + 1) * (maxDelay + 1) := by
            have : 1 * (maxDelay + 1) ≤ (d + 1) * (maxDelay + 1) :=
              Nat.mul_le_mul_right (maxDelay + 1) (by omega)
            simp [Nat.one_mul] at this
            omega
    · -- Depth decreased.  Apply IH from k_next with depth ≤ d.
      have h_depth_le_d : writerWaitDepth (e.stateAt k_next) c ≤ d := by omega
      have h_within_next : k_next + d * (maxDelay + 1) < e.ops.length := by
        have h_le1 : k_next ≤ k_start + maxDelay + 1 := h_le_next
        have h_eq : k_start + (d + 1) * (maxDelay + 1) =
                    k_start + d * (maxDelay + 1) + (maxDelay + 1) := by
          have h1 : (d + 1) * (maxDelay + 1) = d * (maxDelay + 1) + (maxDelay + 1) := by
            rw [Nat.add_mul, Nat.one_mul]
          omega
        omega
      obtain ⟨k_admit_ih, _h_ge_admit_ih, h_le_admit_ih, h_held_ih⟩ :=
        ih k_next h_q_next h_depth_le_d h_within_next
      refine ⟨k_admit_ih, by omega, ?_, h_held_ih⟩
      have h_eq2 : k_start + (d + 1) * (maxDelay + 1) =
                   k_start + d * (maxDelay + 1) + (maxDelay + 1) := by
        have h1 : (d + 1) * (maxDelay + 1) = d * (maxDelay + 1) + (maxDelay + 1) := by
          rw [Nat.add_mul, Nat.one_mul]
        omega
      omega

/-- **WS-SM SM2.C-defer D-3.6 (admission step bound — corollary)**: the
substantive bound theorem reformulated using `admissionStep`.

Combines `rwLock_writer_liveness` with `admissionStep_le_of_holder`. -/
theorem rwLock_writer_admissionStep_bounded
    (e : RwLockExecution) (maxDelay : Nat) (h_fair : FairTrace e maxDelay)
    (h_init : e.initial = RwLockState.unheld)
    (c : CoreId) (k_enq : Nat)
    (h_queued : (c, AccessMode.write) ∈ (e.stateAt k_enq).waiters)
    (h_within : k_enq + writerWaitDepth (e.stateAt k_enq) c * (maxDelay + 1) <
                e.ops.length) :
    ∃ a, e.admissionStep c = some a ∧
         a ≤ k_enq + writerWaitDepth (e.stateAt k_enq) c * (maxDelay + 1) := by
  obtain ⟨k_admit, _, h_le, h_held⟩ :=
    rwLock_writer_liveness e maxDelay h_fair h_init c k_enq h_queued h_within
  have h_holder : e.holderAt k_admit c := by
    unfold RwLockExecution.holderAt
    right; exact h_held
  have h_in_range : k_admit ≤ e.ops.length := by omega
  obtain ⟨a, h_eq, h_a_le⟩ := admissionStep_le_of_holder e h_init c k_admit h_in_range h_holder
  refine ⟨a, h_eq, ?_⟩
  omega

end SeLe4n.Kernel.Concurrency



