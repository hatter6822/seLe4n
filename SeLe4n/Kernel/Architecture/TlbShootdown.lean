-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Concurrency.Types
import SeLe4n.Kernel.Architecture.TlbInvalidation

/-!
# WS-SM SM7.A — TLB shootdown descriptor + per-core pending/ack state

This module lands the SM7.A slice of the TLB/cache shootdown phase
(`docs/planning/SMP_TLB_SHOOTDOWN_PLAN.md` §5): the typed shootdown
descriptor, the per-core pending-shootdown queues, the per-core
acknowledgment flags, the `enqueueShootdown` / `drainShootdowns`
state operations, and the pending-queue capacity bound — together
with the store/load algebra and preservation theorems the SM7.B
protocol proofs (`tlbShootdownBroadcast_invalidatesAllCores`,
Theorem 3.3.1) compose over.

## Protocol context (plan §3.2)

A TLB shootdown for an `(asid, vaddr)` operand initiated by core
`c₀` proceeds as:

  1. `beginShootdownRound c₀` — every ack flag is reset to `false`
     except the initiator's own (the initiator performs its own
     invalidation locally, so it is born-acknowledged).
  2. For each target core `c ≠ c₀`: `enqueueShootdown c desc`
     (under the pending-shootdown lock), then a `.tlbShootdownReq`
     SGI (`SgiKind.tlbShootdownReq`, INTID 1) to `c`.
  3. The initiator executes its local broadcast-variant TLBI via
     `tlbiForSharing` and waits for `allAcked`.
  4. Each target's SGI handler: `drainShootdowns c` (returning the
     complete FIFO queue), one local TLBI per drained descriptor,
     then `acknowledgeShootdown c` (a release-store in the Rust
     runtime; see below).

Steps 2–4 are the SM7.B transitions (`TlbShootdownProtocol.lean`:
`tlbShootdownBroadcast` / `handleTlbShootdownReqOnCore`, LIVE behind
the `completeShootdownRounds` dispatch seam); this module supplies
the state layer they are built from, factored so the handler's TLBI
executions sit *between* the drain and the acknowledgment — the
pure ops deliberately do not fuse drain-and-ack, because the Rust
runtime must not publish the ack before the drained invalidations
have retired (`dsb`-completed) on the target core.

## Runtime correspondence

`TlbShootdownState` is the pure model of runtime state that lives
on the Rust side of the FFI seam:

* `pendingShootdowns` models the per-core descriptor queues the
  kernel maintains under the pending-shootdown lock discipline
  (SM7.B.7 declares the lock-set).
* `shootdownAck` models `rust/sele4n-hal/src/shootdown.rs`'s
  `SHOOTDOWN_ACK` — one cache-line-aligned `AtomicBool` per core.
  The Bool vector here captures the *values*; the release-store /
  acquire-load pairing that makes cross-core propagation sound is
  realised by the Rust atomics and proven against the SM2.A memory
  model at SM7.B.4 (`shootdownAck_release_acquire`).

The quiescent state (no shootdown round in flight) has every queue
empty and every ack flag `true` — "nobody is being waited on".
`TlbShootdownState.initial` (the boot state) is quiescent, matching
the Rust `SHOOTDOWN_ACK` boot value of all-`true`.

## Round serialisation contract (SM7.A audit; SM7.B.7 obligation)

The ack vector here carries **no round identity**, so *as modelled* it
is a single-round resource: at most one shootdown round may be in
flight system-wide.  The plan §3.2 precondition (the initiator holds
the VSpaceRoot write lock) is **not** sufficient to guarantee this —
two initiators shooting down *different* VSpaces hold different
VSpaceRoot locks and would interleave rounds, with two concrete
failures: (a) initiator B's `beginShootdownRound` marks B's own flag
`true` while A still waits on that core's invalidation for A's round,
so A's `allAcked` poll can exit before A's descriptors are drained — a
stale TLB entry stays live on the target, the exact SMP-C4 hazard; and
(b) B's reset clears A's born-`true` flag, which nothing re-sets if A
polls with IRQs masked — a mutual hang.  SM7.B.7 therefore serialises
rounds under the single global `ShootdownRoundLockId` (below), acquired
before any per-core `ShootdownQueueLockId`.

**What the runtime refines (SM7.F.3).**  The Rust acknowledgment
channel is *not* a Boolean reset — each slot holds a monotone
`acked_gen` advanced by a release `fetch_max`, the initiator waits for
`acked_gen[c] ≥ gen`, and there is no reset at all
(`rust/sele4n-hal/src/shootdown.rs`).  The extra strength is needed
because the runtime has a delivery mechanism this model does not
represent: a `.tlbShootdownReq` SGI can stay *pending* across the
cooperative round-lock acquire (which self-services without consuming
the interrupt) and be taken inside a later round, where a Boolean
handler would acknowledge work it never did.  Here a handler
application is an explicit function call, so that shape is
unrepresentable and the Boolean stays a faithful abstraction under the
serialisation contract above.  Round identity *is* modelled where it
is observable — on the descriptors (`TlbShootdownDescriptor.generation`
and the `roundGeneration` counter below), which is what makes the
window drain (`drainShootdownsInWindow`) exact.

## Capacity bound (SM7.A.6)

Every pending queue is bounded by `maxPendingPerCore = 16` (plan §4.1)
and the bound is deliberately conservative — it is an envelope over
what a target can accumulate *between drains*, which is one descriptor
per round posted against it.  That is **not** one round: a single
commit can open several rounds (the retype wrappers open one per
flushed ASID — `retypeShootdownAsids`), and posting happens in the
pure transition while the catch-up drain happens in the dispatch
entry, so a concurrently committed round can post into the same queue
in between.  The bound is therefore maintained by construction rather
than by a counting argument: `enqueueShootdown` is fail-closed — at
capacity it returns `none` rather than silently dropping or unboundedly
growing — its coalescing sibling `enqueueShootdownOrCoalesce` collapses
a full queue to a single covering `.vmalle1` (a superset, never an
under-invalidation), and `pendingBounded` is preserved by every
operation in this module.

## Production reachability

**Production** (SM7.A completion cut): `Model/State.lean` mounts this
state as `SystemState.tlbShootdown`, realising the plan §4.1
"`pendingShootdowns … in ConcurrencyState`" placement in the
codebase's actual state architecture (`SystemState` *is* the kernel's
runtime state; the SM3.A `objStoreLock` field landed the same way).
The module therefore imports only pure layers (`Concurrency.Types` +
the SM7.A-extracted `TlbInvalidation`), NOT the (now production)
`TlbiForSharing` FFI dispatcher — `Platform.FFI` sits above
`Kernel.API` in the import graph and would cycle through
`Model/State.lean`.  The SM7.B protocol transitions
(`TlbShootdownProtocol.lean`) are the sole mutators of the mounted
field; every other kernel transition frames it (no such transition
mentions the field, so `{ st with … }` updates preserve it
definitionally — the `…_tlbShootdown_eq` frame families in
`VSpace.lean` / `CleanupPreservation.lean` pin this per operation).

## Deliberately deferred (recorded design decisions)

* **ASID-generation tagging**: `TlbEntry.asidGeneration` (AK7-J)
  detects stale entries after ASID reuse.  Descriptors deliberately do
  NOT carry a generation: the shootdown *removes* entries (over-
  invalidation is always safe), so a stale-generation descriptor can
  only invalidate more than strictly needed — never less.  If SM7.C's
  per-core TLB effect semantics or SM7.B.10's ASID-retire path need
  generation-selective invalidation, the field is added there,
  alongside the effect semantics that would consume it.
* **Global invariant-bundle integration — LANDED at SM7.B**:
  `pendingBounded st.tlbShootdown` is the 12th conjunct of
  `proofLayerInvariantBundle` (`Architecture/Invariant.lean`).  The
  boot witness is `default_tlbShootdown_pendingBounded`; the adapter
  preservation proofs transport it definitionally (non-shootdown
  transitions frame the field); the live shootdown paths carry it via
  the `…_preserves_pendingBounded` family
  (`TlbShootdownProtocol.lean` §bundle-carriage +
  `completeShootdownOnCore_preserves_pendingBounded` below).
  `shootdownQuiescent` deliberately stays out of the bundle: it is a
  *between-rounds* property, false mid-round by design (the round
  capstones `shootdownRound_restores_quiescent` /
  `shootdownRoundFor_restores_quiescent` prove its restoration
  instead).
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- SM7.A.1 — Shootdown descriptor
-- ============================================================================

/-- **WS-SM SM7.A.1**: one pending TLB-invalidation request queued for a
remote core.

* `op` — the typed invalidation operand (`TlbInvalidation`, SM1.E.4).
  Carrying the full inductive rather than a bare `(asid, vaddr)` pair
  lets the same descriptor drive every SM7.B shootdown flavour: page
  unmap (`.vae1` / `.vale1`), ASID retirement (`.aside1`, SM7.B.10),
  and full-space flush (`.vmalle1`, retype-with-page-free, SM7.B.11)
  — without a second descriptor type.
* `initiator` — the core that started the shootdown round.  The
  primary ack channel is the shared `shootdownAck` flag vector (the
  target sets its *own* flag; the initiator polls), so the handler
  does not need this field for correctness; it identifies the round
  owner for the optional direct-ack SGI (`SgiKind.tlbShootdownAck`,
  plan §3.2 step 4d) and for post-mortem trace attribution.
* `generation` (SM7.F.3) — the round that posted this descriptor,
  allocated by `beginShootdownRound{,For}` from the monotone
  `TlbShootdownState.roundGeneration` counter.  It is what lets a
  round's deferred catch-up drain **only its own** descriptors: the
  model posting and the model catch-up are two separate atomic steps
  (`syscallDispatchCrossCoreEntry`'s commit, then
  `completeShootdownRounds`'s commit), neither under the hardware
  round lock, so without a round identity one round's catch-up fold
  would drain a *concurrently posted* round's freshly-queued
  descriptors and claim quiescence before that round's SGIs had
  fired.  See `drainShootdownsInWindow` for the selective drain and
  `shootdownCatchUpPerCoreInWindow` (`PerCoreTlbModel.lean`) for the
  live seam that uses it. -/
structure TlbShootdownDescriptor where
  op : TlbInvalidation
  initiator : CoreId
  generation : Nat
  deriving DecidableEq, Repr, Inhabited

-- ============================================================================
-- SM7.A.6 — Pending-queue capacity bound
-- ============================================================================

/-- **WS-SM SM7.A.6**: upper bound on each core's pending-shootdown
queue length (plan §4.1).  Every SM7.B caller enqueues one descriptor
per target per round, so this is a conservative envelope over the
rounds a target can accumulate between drains — several per commit for
the multi-ASID retype wrappers, plus any concurrently committed round
that posts before this commit's catch-up (see the module header's
capacity-bound section).  `enqueueShootdown` fails closed at this
bound; `enqueueShootdownOrCoalesce` collapses to a covering
`.vmalle1`. -/
def maxPendingPerCore : Nat := 16

/-- **WS-SM SM7.A.6**: the capacity bound admits at least one pending
descriptor — `drainShootdowns` followed by `enqueueShootdown` on the
same core therefore always succeeds
(`enqueueShootdown_isSome_after_drain`). -/
theorem maxPendingPerCore_pos : 0 < maxPendingPerCore := by decide

-- ============================================================================
-- SM7.A.2 + SM7.A.3 — Per-core shootdown state
-- ============================================================================

/-- **WS-SM SM7.A.2 + SM7.A.3**: the per-core TLB-shootdown state.

* `pendingShootdowns` (SM7.A.2) — core `c`'s slot holds the FIFO
  queue of invalidation requests other cores have posted for `c`.
  Writers append under the pending-shootdown lock discipline
  (SM7.B.7); core `c`'s `.tlbShootdownReq` SGI handler drains the
  whole queue (`drainShootdowns`).
* `shootdownAck` (SM7.A.3) — core `c`'s slot is `true` once `c` has
  completed (and locally retired) every invalidation of the current
  round; the initiator's wait loop polls for `allAcked`.  Models the
  Rust `SHOOTDOWN_ACK` per-core `AtomicBool` array (release-store on
  set, acquire-load on poll; formalised at SM7.B.4).

* `roundGeneration` (SM7.F.3) — the number of shootdown rounds opened
  so far; `beginShootdownRound{,For}` increments it and stamps the
  round's descriptors with the resulting value, so generations are
  allocated `1, 2, 3, …` in **commit** order (`0` is the boot value,
  which no descriptor ever carries).  Monotone by construction: no
  operation in this module decreases it.

  **This is NOT the generation the runtime rounds run under** (PR #854
  review P1).  The two counters answer different questions and are
  deliberately independent:

  - *this* one orders **commits**, and keys the SM7.F.3 window drain —
    "which descriptors belong to this commit?" — so it must be
    allocated by the pure transition, inside the atomic state commit;
  - the runtime's `SHOOTDOWN_ROUND_SEQ` orders **hardware rounds**, and
    keys the acknowledgment channel — "which round is this, relative to
    the rounds whose acknowledgments could satisfy its wait?" — so it is
    allocated by `completeShootdownRounds` while holding the round lock,
    which is what makes allocation order equal execution order.

  Conflating them is the ordering bug the review found: nothing relates
  a commit's position to its position in the round-lock queue, so under
  concurrency a round committed earlier can execute later and have its
  monotone `acked_gen >= gen` wait satisfied by a newer round's
  acknowledgments — returning from a round no target serviced, with the
  operands still live in every remote TLB.  What
  `rust/sele4n-hal/src/shootdown.rs` publishes into
  `ShootdownOpMailbox::generation`, and what each target's handler
  acknowledges (`ack_round`), is therefore the **runtime** generation,
  never this field.

All three fields default to the quiescent boot values: empty queues,
every core's acknowledged generation `0`, and round generation `0` —
so `roundGeneration ≤ ackedGenOnCore c` holds for every core at boot
("no round in flight, nobody waited on"), matching
`initial_shootdownQuiescent` and the Rust boot state. -/
structure TlbShootdownState where
  pendingShootdowns : Vector (List TlbShootdownDescriptor) numCores :=
    Vector.replicate numCores []
  /-- **WS-SM SM7.F.3 (PR #854 review)**: the **highest round generation**
  each core has acknowledged — the model mirror of the Rust
  `ShootdownAckSlot.acked_gen`, which the same review's P1 fix made the
  sole runtime acknowledgment channel.

  This was a `Vector Bool` until v0.32.113.  A flag cannot say *which*
  round it discharged, so a catch-up that deliberately drained only its
  own generation window still wrote `true` and thereby claimed every
  concurrently-posted round as acknowledged — `allAcked` could read true
  with a foreign round's descriptors still pending.  A generation says
  what it discharged, so a window drain can only ever claim its own
  window. -/
  shootdownAck : Vector Nat numCores :=
    Vector.replicate numCores 0
  roundGeneration : Nat := 0
  deriving Repr, DecidableEq

namespace TlbShootdownState

/-- **WS-SM SM7.A.2**: the quiescent boot state — every pending queue
empty, every ack flag `true`.  Witnessed quiescent by
`initial_shootdownQuiescent` and bounded by `initial_pendingBounded`. -/
def initial : TlbShootdownState := {}

instance : Inhabited TlbShootdownState := ⟨initial⟩

/-! ### Per-core accessors (path-a)

Per the SM4.B path-a discipline (`docs/planning/SMP_PER_CORE_STATE_PLAN.md`
§3.1), every per-core field is read through an explicit
`…OnCore (c : CoreId)` accessor and written through a matching
`set…OnCore` setter, so every callsite names the core it reasons
about and the store/load algebra below controls proof normalisation.
The accessors are intentionally **not** `@[simp]`. -/

/-- Per-core pending-shootdown queue of `st` on core `c`. -/
def pendingOnCore (st : TlbShootdownState) (c : CoreId) :
    List TlbShootdownDescriptor :=
  st.pendingShootdowns.get c

/-- **WS-SM SM7.F.3 (PR #854 review)**: the highest round generation core
`c` has acknowledged — the raw slot, mirroring the Rust
`ShootdownAckSlot.acked_gen`. -/
def ackedGenOnCore (st : TlbShootdownState) (c : CoreId) : Nat :=
  st.shootdownAck.get c

/-- Per-core shootdown-acknowledgment flag of `st` on core `c`: has `c`
acknowledged the round currently open?

Derived from `ackedGenOnCore` since v0.32.113 rather than stored, by the
same *shape* of comparison the Rust initiator uses — but against the
model's `roundGeneration`, which is a different counter answering a
different question, so the two are not interchangeable.  The runtime's
`acked_gen >= gen` compares against the lock-allocated
`SHOOTDOWN_ROUND_SEQ` generation, where allocation order is execution
order and the comparison therefore *does* mean "every round up to `gen`
was serviced".  Here it does not — see `allAcked`, which records the
consequence and the reachable counterexample.

Keeping this a `Bool` keeps the SM7.A/B acknowledgment theorems stated in
terms of a core being acknowledged or not; what changed underneath is
that "acknowledged" names a round instead of asserting a bare flag. -/
def ackOnCore (st : TlbShootdownState) (c : CoreId) : Bool :=
  st.roundGeneration ≤ st.ackedGenOnCore c

/-- Write core `c`'s pending-shootdown queue slot. -/
def setPendingOnCore (st : TlbShootdownState) (c : CoreId)
    (q : List TlbShootdownDescriptor) : TlbShootdownState :=
  { st with pendingShootdowns := st.pendingShootdowns.set c.val q c.isLt }

/-- Write core `c`'s acknowledged-generation slot. -/
def setAckedGenOnCore (st : TlbShootdownState) (c : CoreId) (g : Nat) :
    TlbShootdownState :=
  { st with shootdownAck := st.shootdownAck.set c.val g c.isLt }

/-! ### Store/load reduction algebra

The per-core setter/accessor algebra, mirroring the SM4.B phase-2
`SchedulerState` discipline: reading core `c`'s slot after writing
core `c` returns the written value (`_self`); reading another core's
slot of the same field (`_ne`), or any slot of the *other* field, is
unaffected.  All `@[simp]` so post-write reads reduce automatically. -/

@[simp] theorem setPendingOnCore_pendingOnCore_self (st : TlbShootdownState)
    (c : CoreId) (q : List TlbShootdownDescriptor) :
    (st.setPendingOnCore c q).pendingOnCore c = q := by
  simp [setPendingOnCore, pendingOnCore]

@[simp] theorem setPendingOnCore_pendingOnCore_ne (st : TlbShootdownState)
    (c c' : CoreId) (q : List TlbShootdownDescriptor) (h : c ≠ c') :
    (st.setPendingOnCore c q).pendingOnCore c' = st.pendingOnCore c' := by
  simp only [setPendingOnCore, pendingOnCore]
  exact SeLe4n.PerCoreVector.get_set_ne st.pendingShootdowns c c' q h

@[simp] theorem setPendingOnCore_ackOnCore (st : TlbShootdownState)
    (c c' : CoreId) (q : List TlbShootdownDescriptor) :
    (st.setPendingOnCore c q).ackOnCore c' = st.ackOnCore c' := by
  simp [setPendingOnCore, ackOnCore, ackedGenOnCore]

@[simp] theorem setAckedGenOnCore_ackedGenOnCore_self (st : TlbShootdownState)
    (c : CoreId) (g : Nat) :
    (st.setAckedGenOnCore c g).ackedGenOnCore c = g := by
  simp [setAckedGenOnCore, ackedGenOnCore]

@[simp] theorem setAckedGenOnCore_ackedGenOnCore_ne (st : TlbShootdownState)
    (c c' : CoreId) (g : Nat) (h : c ≠ c') :
    (st.setAckedGenOnCore c g).ackedGenOnCore c' = st.ackedGenOnCore c' := by
  simp only [setAckedGenOnCore, ackedGenOnCore]
  exact SeLe4n.PerCoreVector.get_set_ne st.shootdownAck c c' g h

/-- **WS-SM SM7.F.3**: writing core `c`'s generation leaves every *other*
core's acknowledgment verdict untouched. -/
@[simp] theorem setAckedGenOnCore_ackOnCore_ne (st : TlbShootdownState)
    (c c' : CoreId) (g : Nat) (h : c ≠ c') :
    (st.setAckedGenOnCore c g).ackOnCore c' = st.ackOnCore c' := by
  simp only [TlbShootdownState.ackOnCore, setAckedGenOnCore_ackedGenOnCore_ne _ _ _ _ h]
  rfl

@[simp] theorem setAckedGenOnCore_pendingOnCore (st : TlbShootdownState)
    (c c' : CoreId) (g : Nat) :
    (st.setAckedGenOnCore c g).pendingOnCore c' = st.pendingOnCore c' := by
  simp [setAckedGenOnCore, pendingOnCore]

/-- **WS-SM SM7.F.3**: writing a pending queue never allocates a round —
the generation counter is advanced only by `beginShootdownRound{,For}`. -/
@[simp] theorem setPendingOnCore_roundGeneration (st : TlbShootdownState)
    (c : CoreId) (q : List TlbShootdownDescriptor) :
    (st.setPendingOnCore c q).roundGeneration = st.roundGeneration := rfl

/-- **WS-SM SM7.F.3**: acknowledging never allocates a round. -/
@[simp] theorem setAckedGenOnCore_roundGeneration (st : TlbShootdownState)
    (c : CoreId) (g : Nat) :
    (st.setAckedGenOnCore c g).roundGeneration = st.roundGeneration := rfl

/-- **WS-SM SM7.F.3**: writing core `c`'s generation to a value at or
above the current round makes exactly `c` acknowledged. -/
@[simp] theorem setAckedGenOnCore_ackOnCore_self (st : TlbShootdownState)
    (c : CoreId) (g : Nat) :
    (st.setAckedGenOnCore c g).ackOnCore c = (st.roundGeneration ≤ g) := by
  simp [ackOnCore]

/-- **WS-SM SM7.A.2**: per-core extensionality.  Two shootdown states
are equal once their pending queues and ack flags agree at *every*
`CoreId` and their round-generation counters agree.  Named
`ext_perCore` to avoid clashing with the structure's auto-generated
`TlbShootdownState.ext`; each per-core hypothesis lifts to `Vector`
equality via `SeLe4n.PerCoreVector.ext`. -/
theorem ext_perCore {s₁ s₂ : TlbShootdownState}
    (hPend : ∀ c : CoreId, s₁.pendingOnCore c = s₂.pendingOnCore c)
    (hAck : ∀ c : CoreId, s₁.ackedGenOnCore c = s₂.ackedGenOnCore c)
    (hGen : s₁.roundGeneration = s₂.roundGeneration) :
    s₁ = s₂ := by
  have h1 : s₁.pendingShootdowns = s₂.pendingShootdowns :=
    SeLe4n.PerCoreVector.ext fun c => hPend c
  have h2 : s₁.shootdownAck = s₂.shootdownAck :=
    SeLe4n.PerCoreVector.ext fun c => hAck c
  obtain ⟨p₁, a₁, g₁⟩ := s₁
  obtain ⟨p₂, a₂, g₂⟩ := s₂
  simp_all

/-- **WS-SM SM7.A.2**: the boot state has an empty pending queue on
every core (`Vector.replicate` reduction). -/
@[simp] theorem initial_pendingOnCore (c : CoreId) :
    initial.pendingOnCore c = [] := by
  simp [initial, pendingOnCore]

/-- **WS-SM SM7.A.3**: the boot state has every ack flag `true` —
quiescent, matching the Rust `SHOOTDOWN_ACK` boot value. -/
@[simp] theorem initial_ackOnCore (c : CoreId) :
    initial.ackOnCore c = true := by
  simp [initial, ackOnCore]

/-- **WS-SM SM7.F.3**: no round has been opened at boot, so the
generation counter starts at `0` — a value no descriptor ever carries
(`beginShootdownRound{,For}` stamps `roundGeneration + 1`). -/
@[simp] theorem initial_roundGeneration : initial.roundGeneration = 0 := rfl

end TlbShootdownState

-- ============================================================================
-- SM7.F.3 — The descriptor a round posts
-- ============================================================================

/-- **WS-SM SM7.F.3**: the descriptor a round opened from `sd` posts to
each of its targets.

Factored out so the round's *generation* is written once: a round open
(`beginShootdownRound{,For}`) advances `sd.roundGeneration` by one, so
the descriptors the posting fold appends must carry
`sd.roundGeneration + 1` — the generation of the round *being opened*,
not of the pre-state.  `roundDescriptor_generation_eq_opened` pins that
agreement, and it is what makes every posted descriptor land inside its
own commit's window (`inRoundWindow`). -/
def roundDescriptor (sd : TlbShootdownState) (initiator : CoreId)
    (op : TlbInvalidation) : TlbShootdownDescriptor :=
  { op := op, initiator := initiator, generation := sd.roundGeneration + 1 }

/-- **WS-SM SM7.F.3**: the round descriptor carries the round's operand. -/
@[simp] theorem roundDescriptor_op (sd : TlbShootdownState)
    (initiator : CoreId) (op : TlbInvalidation) :
    (roundDescriptor sd initiator op).op = op := rfl

/-- **WS-SM SM7.F.3**: the round descriptor is attributed to the round's
initiator. -/
@[simp] theorem roundDescriptor_initiator (sd : TlbShootdownState)
    (initiator : CoreId) (op : TlbInvalidation) :
    (roundDescriptor sd initiator op).initiator = initiator := rfl

/-- **WS-SM SM7.F.3**: the round descriptor carries the generation the
round open allocates. -/
@[simp] theorem roundDescriptor_generation (sd : TlbShootdownState)
    (initiator : CoreId) (op : TlbInvalidation) :
    (roundDescriptor sd initiator op).generation = sd.roundGeneration + 1 :=
  rfl

-- ============================================================================
-- SM7.A.6 — State invariants
-- ============================================================================

/-- **WS-SM SM7.A.6**: the pending-queue capacity invariant — every
core's queue length is within `maxPendingPerCore`.  Established at
boot (`initial_pendingBounded`) and preserved by every shootdown
operation (`enqueueShootdown` / `drainShootdowns` /
`acknowledgeShootdown` / `beginShootdownRound` — the four
`…_preserves_pendingBounded` theorems); `enqueueShootdown` enforces it
fail-closed.  The raw `setPendingOnCore` setter can write an arbitrary
queue and is not an invariant boundary — SM7.B transitions must go
through the operations, never the raw setter. -/
def pendingBounded (st : TlbShootdownState) : Prop :=
  ∀ c : CoreId, (st.pendingOnCore c).length ≤ maxPendingPerCore

instance (st : TlbShootdownState) : Decidable (pendingBounded st) :=
  inferInstanceAs (Decidable (∀ c : CoreId,
    (st.pendingOnCore c).length ≤ maxPendingPerCore))

/-- **WS-SM SM7.F.3 (PR #854 review)**: well-formedness — no core has
acknowledged a round that has not been opened.

Boot satisfies it (`0 ≤ 0`) and every transition preserves it: a round
open raises `roundGeneration` and writes exactly the new generation to
the cores born-acknowledged, an acknowledgment writes a generation the
opener already minted, and the drains/enqueues do not touch the vector.

It is what makes "a target starts a round unacknowledged" true —
`beginShootdownRound_ackOnCore_target` and the two `_ackOnCore_iff`
characterisations take it as a hypothesis, because without it a slot
carrying a fabricated future generation would read as already
acknowledging the round about to open. -/
def ackBounded (st : TlbShootdownState) : Prop :=
  ∀ c : CoreId, st.ackedGenOnCore c ≤ st.roundGeneration

instance (st : TlbShootdownState) : Decidable (ackBounded st) :=
  inferInstanceAs (Decidable (∀ c : CoreId, st.ackedGenOnCore c ≤ _))

/-- **WS-SM SM7.A.3**: every core has acknowledged at or beyond the round
currently open — the initiator wait-loop's exit condition (plan §3.2
step 5).  Decidable so the SM7.B wait loop and the test suite can
evaluate it directly.

**Not a completion predicate on its own** (PR #854 review).  It is a
high-water mark, so reading it as "every round up to `roundGeneration`
has been serviced" is a *prefix* claim, and since v0.32.112 that claim
does not hold of the model: commit generations are allocated by the pure
transition and hardware rounds execute in round-lock order, and the two
orders are deliberately independent.  Concretely — round A commits
generation 1 and stalls before the lock while round B commits generation
2 and runs first; B's catch-up records `hi = 2` on every target, so
every core reads acknowledged, while A's generation-1 descriptors are
still queued and A's round has never run.  `SmpTlbShootdownSuite` §8.5
computes exactly that state, so this limitation is machine-checked
rather than asserted.

The model's source of truth for outstanding work is the **pending
queues**, so the sound completion predicate is `shootdownQuiescent`,
which conjoins them and is correctly false in that scenario.  Every
round capstone concludes `shootdownQuiescent`, and
`shootdownRound_allAcked` derives this from a *quiescent* pre-state —
where no earlier round is outstanding and the prefix reading is
therefore recovered — so no landed theorem depends on the unsound
reading.

The ack vector's role here is to mirror the Rust `acked_gen`, where the
prefix reading **is** valid: runtime generations are allocated under the
round lock, so allocation order is execution order and a target
acknowledging generation `g` has necessarily serviced every round it was
sent up to `g`.  Representing the model's discharged generations as a
**set** rather than a high-water mark — which would make the model
independently sound rather than sound-relative-to-quiescence — is
registered as tracked debt in `docs/planning/SMP_TLB_SHOOTDOWN_PLAN.md`
§SM7.F.3. -/
def allAcked (st : TlbShootdownState) : Prop :=
  ∀ c : CoreId, st.ackOnCore c = true

instance (st : TlbShootdownState) : Decidable (allAcked st) :=
  inferInstanceAs (Decidable (∀ c : CoreId, st.ackOnCore c = true))

/-- **WS-SM SM7.A**: no shootdown round in flight — every queue empty
and every flag acknowledged.  This is the state between rounds; the
boot state satisfies it (`initial_shootdownQuiescent`). -/
def shootdownQuiescent (st : TlbShootdownState) : Prop :=
  (∀ c : CoreId, st.pendingOnCore c = []) ∧ allAcked st

instance (st : TlbShootdownState) : Decidable (shootdownQuiescent st) :=
  inferInstanceAs (Decidable ((∀ c : CoreId, st.pendingOnCore c = []) ∧
    allAcked st))

/-- **WS-SM SM7.A.6**: the boot state satisfies the capacity bound. -/
theorem initial_pendingBounded : pendingBounded TlbShootdownState.initial := by
  intro c
  rw [TlbShootdownState.initial_pendingOnCore]
  exact Nat.zero_le _

/-- **WS-SM SM7.F.3 (PR #854 review)**: the boot state is ack-bounded —
every slot and the round counter are `0`.

The base case of the 15th `proofLayerInvariantBundle` conjunct. -/
theorem initial_ackBounded : ackBounded TlbShootdownState.initial := by
  intro c
  simp [TlbShootdownState.ackedGenOnCore, TlbShootdownState.initial,
    SeLe4n.PerCoreVector.replicate_get]

/-- **WS-SM SM7.A.3**: the boot state is fully acknowledged. -/
theorem initial_allAcked : allAcked TlbShootdownState.initial := fun c =>
  TlbShootdownState.initial_ackOnCore c

/-- **WS-SM SM7.A**: the boot state is quiescent. -/
theorem initial_shootdownQuiescent :
    shootdownQuiescent TlbShootdownState.initial :=
  ⟨fun c => TlbShootdownState.initial_pendingOnCore c, initial_allAcked⟩

/-- **WS-SM SM7.A.6**: a quiescent state trivially satisfies the
capacity bound (empty queues have length `0`). -/
theorem pendingBounded_of_shootdownQuiescent {st : TlbShootdownState}
    (h : shootdownQuiescent st) : pendingBounded st := by
  intro c
  rw [h.1 c]
  exact Nat.zero_le _

-- ============================================================================
-- SM7.A.4 — enqueueShootdown
-- ============================================================================

/-- **WS-SM SM7.A.4**: post one invalidation request onto a target
core's pending queue.

Appends at the tail so `drainShootdowns` observes requests in FIFO
order.  Fail-closed at the capacity bound: when the target's queue
already holds `maxPendingPerCore` descriptors the operation returns
`none` and the state is unchanged — it never drops a descriptor
silently (a dropped invalidation would leave a stale TLB entry on the
target, the exact SMP-C4 hazard SM7 exists to close) and never grows
the queue past the bound.

The SM7.B initiator calls this once per target core under the
pending-shootdown lock discipline (SM7.B.7) before firing the
`.tlbShootdownReq` SGI; an unexpected `none` is a protocol invariant
violation the caller must treat as fatal (the queues are sized so a
serialised initiator can never legitimately hit the bound). -/
def enqueueShootdown (st : TlbShootdownState) (target : CoreId)
    (d : TlbShootdownDescriptor) : Option TlbShootdownState :=
  if (st.pendingOnCore target).length < maxPendingPerCore then
    some (st.setPendingOnCore target (st.pendingOnCore target ++ [d]))
  else
    none

/-- **WS-SM SM7.A.4**: `enqueueShootdown` succeeds exactly when the
target queue is strictly below capacity. -/
theorem enqueueShootdown_isSome_iff (st : TlbShootdownState)
    (target : CoreId) (d : TlbShootdownDescriptor) :
    (enqueueShootdown st target d).isSome ↔
      (st.pendingOnCore target).length < maxPendingPerCore := by
  unfold enqueueShootdown
  split <;> simp_all

/-- **WS-SM SM7.A.6**: `enqueueShootdown` fails exactly when the target
queue is at (or, unreachably, beyond) capacity — the fail-closed dual
of `enqueueShootdown_isSome_iff`. -/
theorem enqueueShootdown_eq_none_iff (st : TlbShootdownState)
    (target : CoreId) (d : TlbShootdownDescriptor) :
    enqueueShootdown st target d = none ↔
      maxPendingPerCore ≤ (st.pendingOnCore target).length := by
  unfold enqueueShootdown
  split <;> simp_all <;> omega

/-- **WS-SM SM7.A.6**: at capacity the enqueue is rejected outright. -/
theorem enqueueShootdown_eq_none_of_full {st : TlbShootdownState}
    {target : CoreId} (d : TlbShootdownDescriptor)
    (h : maxPendingPerCore ≤ (st.pendingOnCore target).length) :
    enqueueShootdown st target d = none :=
  (enqueueShootdown_eq_none_iff st target d).mpr h

/-- **WS-SM SM7.A.4**: a successful enqueue appends the descriptor at
the tail of the target's queue — the FIFO-order witness
`drainShootdowns` relies on. -/
theorem enqueueShootdown_pending_target {st st' : TlbShootdownState}
    {target : CoreId} {d : TlbShootdownDescriptor}
    (h : enqueueShootdown st target d = some st') :
    st'.pendingOnCore target = st.pendingOnCore target ++ [d] := by
  unfold enqueueShootdown at h
  split at h
  · injection h with h
    subst h
    simp
  · simp at h

/-- **WS-SM SM7.A.4**: the enqueued descriptor is pending on the target
— no request is lost between posting and the SGI handler's drain. -/
theorem enqueueShootdown_mem {st st' : TlbShootdownState}
    {target : CoreId} {d : TlbShootdownDescriptor}
    (h : enqueueShootdown st target d = some st') :
    d ∈ st'.pendingOnCore target := by
  rw [enqueueShootdown_pending_target h]
  simp

/-- **WS-SM SM7.A.4**: a successful enqueue grows the target queue by
exactly one descriptor. -/
theorem enqueueShootdown_length {st st' : TlbShootdownState}
    {target : CoreId} {d : TlbShootdownDescriptor}
    (h : enqueueShootdown st target d = some st') :
    (st'.pendingOnCore target).length =
      (st.pendingOnCore target).length + 1 := by
  rw [enqueueShootdown_pending_target h]
  simp

/-- **WS-SM SM7.A.4**: enqueueing onto `target` leaves every *other*
core's pending queue untouched — the cross-core frame that makes
per-target posting independent. -/
theorem enqueueShootdown_frame_pending {st st' : TlbShootdownState}
    {target : CoreId} {d : TlbShootdownDescriptor}
    (h : enqueueShootdown st target d = some st')
    {c : CoreId} (hc : c ≠ target) :
    st'.pendingOnCore c = st.pendingOnCore c := by
  unfold enqueueShootdown at h
  split at h
  · injection h with h
    subst h
    exact TlbShootdownState.setPendingOnCore_pendingOnCore_ne
      st target c _ hc.symm
  · simp at h

/-- **WS-SM SM7.A.4**: enqueueing never touches any core's ack flag —
posting a request and acknowledging completion are disjoint effects. -/
theorem enqueueShootdown_frame_ack {st st' : TlbShootdownState}
    {target : CoreId} {d : TlbShootdownDescriptor}
    (h : enqueueShootdown st target d = some st') (c : CoreId) :
    st'.ackOnCore c = st.ackOnCore c := by
  unfold enqueueShootdown at h
  split at h
  · injection h with h
    subst h
    simp
  · simp at h

/-- **WS-SM SM7.F.3 (PR #854 review)**: the raw-generation form of the
posting frame. -/
theorem enqueueShootdown_frame_ackedGen {st st' : TlbShootdownState}
    {target : CoreId} {d : TlbShootdownDescriptor}
    (h : enqueueShootdown st target d = some st') (c : CoreId) :
    st'.ackedGenOnCore c = st.ackedGenOnCore c := by
  unfold enqueueShootdown at h
  split at h
  · injection h with h
    subst h
    simp [TlbShootdownState.ackedGenOnCore, TlbShootdownState.setPendingOnCore]
  · simp at h

/-- **WS-SM SM7.F.3**: posting a descriptor never allocates a round —
the generation is allocated once, by the round open, and every
descriptor of the round carries that same value. -/
theorem enqueueShootdown_frame_roundGeneration {st st' : TlbShootdownState}
    {target : CoreId} {d : TlbShootdownDescriptor}
    (h : enqueueShootdown st target d = some st') :
    st'.roundGeneration = st.roundGeneration := by
  unfold enqueueShootdown at h
  split at h
  · injection h with h
    subst h
    rfl
  · simp at h

/-- **WS-SM SM7.A.6**: a successful enqueue preserves the capacity
invariant — the target's post-length is `pre + 1 ≤ maxPendingPerCore`
(success required `pre < maxPendingPerCore`), and every other queue is
framed. -/
theorem enqueueShootdown_preserves_pendingBounded {st st' : TlbShootdownState}
    {target : CoreId} {d : TlbShootdownDescriptor}
    (hB : pendingBounded st) (h : enqueueShootdown st target d = some st') :
    pendingBounded st' := by
  intro c
  by_cases hc : c = target
  · subst hc
    have hlt : (st.pendingOnCore c).length < maxPendingPerCore :=
      (enqueueShootdown_isSome_iff st c d).mp (by rw [h]; rfl)
    rw [enqueueShootdown_length h]
    omega
  · rw [enqueueShootdown_frame_pending h hc]
    exact hB c

/-! ### SM7.A.6 — Capacity sufficiency for a serialised round

The plan §4.1 sizes `maxPendingPerCore` against the protocol's posting
pattern: the global round lock (the module-header round-serialisation
contract) serialises rounds, each round posts **one** descriptor per
target, and each target's queue was drained by the end of the previous
round.  The theorems below discharge that
argument formally rather than by prose: posting onto an empty queue
always succeeds, and a whole round's posting fold succeeds whenever the
targets are distinct and start empty — which
`shootdownRound_restores_quiescent` (below) shows is exactly the state
every completed round leaves behind. -/

/-- **WS-SM SM7.A.6**: posting onto an empty queue always succeeds
(`0 < maxPendingPerCore`). -/
theorem enqueueShootdown_isSome_of_empty {st : TlbShootdownState}
    {target : CoreId} (h : st.pendingOnCore target = [])
    (d : TlbShootdownDescriptor) :
    (enqueueShootdown st target d).isSome := by
  rw [enqueueShootdown_isSome_iff, h]
  exact maxPendingPerCore_pos

/-- **WS-SM SM7.A.6**: a round's posting fold — one descriptor per
target — succeeds whenever the targets are distinct and their queues
start empty.  This is the formal §4.1 capacity-sufficiency argument:
under round serialisation an initiator can never legitimately hit the
bound. -/
theorem foldlM_enqueueShootdown_isSome (targets : List CoreId) :
    ∀ (st : TlbShootdownState), targets.Nodup →
      (∀ c ∈ targets, st.pendingOnCore c = []) →
      ∀ d : TlbShootdownDescriptor,
        (targets.foldlM (fun s c => enqueueShootdown s c d) st).isSome := by
  induction targets with
  | nil => intro st _ _ d; rfl
  | cons t ts ih =>
    intro st hnd hempty d
    rw [List.foldlM_cons]
    obtain ⟨st', hst'⟩ := Option.isSome_iff_exists.mp
      (enqueueShootdown_isSome_of_empty (hempty t (List.mem_cons_self ..)) d)
    rw [hst']
    -- `some st' >>= k` reduces to `k st'` definitionally in `Option`.
    exact ih st' (List.nodup_cons.mp hnd).2
      (fun c hc => by
        have hct : c ≠ t := fun he => (List.nodup_cons.mp hnd).1 (he ▸ hc)
        rw [enqueueShootdown_frame_pending hst' hct]
        exact hempty c (List.mem_cons_of_mem _ hc)) d

/-- **WS-SM SM7.A.4**: the posting fold never touches any ack flag —
the fold-level form of `enqueueShootdown_frame_ack`. -/
theorem foldlM_enqueueShootdown_frame_ack {targets : List CoreId} :
    ∀ {st posted : TlbShootdownState} {d : TlbShootdownDescriptor},
      targets.foldlM (fun s c => enqueueShootdown s c d) st = some posted →
      ∀ c : CoreId, posted.ackOnCore c = st.ackOnCore c := by
  induction targets with
  | nil =>
    intro st posted d h c
    injection h with h
    subst h
    rfl
  | cons t ts ih =>
    intro st posted d h c
    rw [List.foldlM_cons] at h
    cases heq : enqueueShootdown st t d with
    | none => rw [heq] at h; simp at h
    | some st' =>
      rw [heq] at h
      -- `some st' >>= k` reduces to `k st'` definitionally in `Option`.
      rw [ih h c, enqueueShootdown_frame_ack heq c]

/-- **WS-SM SM7.A.4**: the posting fold leaves every non-target core's
queue untouched — the fold-level form of
`enqueueShootdown_frame_pending`. -/
theorem foldlM_enqueueShootdown_frame_pending {targets : List CoreId} :
    ∀ {st posted : TlbShootdownState} {d : TlbShootdownDescriptor},
      targets.foldlM (fun s c => enqueueShootdown s c d) st = some posted →
      ∀ {c : CoreId}, c ∉ targets →
        posted.pendingOnCore c = st.pendingOnCore c := by
  induction targets with
  | nil =>
    intro st posted d h c _
    injection h with h
    subst h
    rfl
  | cons t ts ih =>
    intro st posted d h c hnc
    rw [List.foldlM_cons] at h
    cases heq : enqueueShootdown st t d with
    | none => rw [heq] at h; simp at h
    | some st' =>
      rw [heq] at h
      -- `some st' >>= k` reduces to `k st'` definitionally in `Option`.
      have hct : c ≠ t := fun he => hnc (he ▸ List.mem_cons_self ..)
      rw [ih h (fun hm => hnc (List.mem_cons_of_mem _ hm)),
          enqueueShootdown_frame_pending heq hct]

-- ============================================================================
-- SM7.A.6 — Overflow-coalescing enqueue (the bounded-queue escape hatch)
-- ============================================================================

/-- **WS-SM SM7.A.6**: total enqueue with full-flush coalescing.

Behaves exactly like `enqueueShootdown` below the capacity bound.  At
the bound — unreachable under the serialised one-descriptor-per-target
round discipline (`foldlM_enqueueShootdown_isSome`), but reachable if a
future SM7.B caller batches many pages into one round — the target's
queue is **collapsed to a single full-flush descriptor**
(`.vmalle1`, carrying the requesting round's initiator).

This is the standard bounded-batching escape hatch (over-invalidation
is always safe; under-invalidation never is): a full flush supersedes
every queued invalidation and the new request alike, so no invalidation
is ever lost — the *new* request is pending or superseded
(`enqueueShootdownOrCoalesce_request_covered`), every *previously
queued* descriptor is pending or superseded
(`enqueueShootdownOrCoalesce_pending_covered`), and the queue stays
within `maxPendingPerCore` **unconditionally**
(`enqueueShootdownOrCoalesce_preserves_pendingBounded`).  The formal
"supersedes" statement — draining the collapsed queue invalidates at
least everything the dropped descriptors would have — lands with the
SM7.C per-core TLB effect semantics (`tlbInvalidateOnCore`), which is
where "what an op removes" is first defined; until then the two
coverage theorems pin the syntactic half (a `.vmalle1` descriptor is
present whenever anything was dropped).

**Generation attribution (SM7.F.3).**  The collapsed descriptor
carries the *incoming* request's generation, exactly as it carries the
incoming request's initiator: it is the requesting round that owes the
work, so it is that round's catch-up which must retire it.  This is
sound in both directions — the collapse only ever *widens* an operand
to `.vmalle1`, which covers every dropped descriptor whatever its
generation, so an older round whose descriptor was absorbed has its
obligation discharged early (safe over-application) rather than
dropped, and its own catch-up then correctly finds nothing left to
do. -/
def enqueueShootdownOrCoalesce (st : TlbShootdownState) (target : CoreId)
    (d : TlbShootdownDescriptor) : TlbShootdownState :=
  match enqueueShootdown st target d with
  | some st' => st'
  | none =>
    st.setPendingOnCore target [{ op := .vmalle1, initiator := d.initiator, generation := d.generation }]

/-- **WS-SM SM7.A.6**: below capacity, the coalescing enqueue is
exactly `enqueueShootdown`. -/
theorem enqueueShootdownOrCoalesce_eq_enqueue {st st' : TlbShootdownState}
    {target : CoreId} {d : TlbShootdownDescriptor}
    (h : enqueueShootdown st target d = some st') :
    enqueueShootdownOrCoalesce st target d = st' := by
  simp only [enqueueShootdownOrCoalesce, h]

/-- **WS-SM SM7.A.6**: at capacity, the target's queue collapses to a
single full-flush descriptor attributed to the requesting round's
initiator. -/
theorem enqueueShootdownOrCoalesce_of_full {st : TlbShootdownState}
    {target : CoreId} (d : TlbShootdownDescriptor)
    (h : maxPendingPerCore ≤ (st.pendingOnCore target).length) :
    (enqueueShootdownOrCoalesce st target d).pendingOnCore target =
      [{ op := .vmalle1, initiator := d.initiator, generation := d.generation }] := by
  simp only [enqueueShootdownOrCoalesce, enqueueShootdown_eq_none_of_full d h]
  simp

/-- **WS-SM SM7.A.6**: the coalescing enqueue never loses a request —
the descriptor is pending, or a full-flush descriptor (which supersedes
it) is. -/
theorem enqueueShootdownOrCoalesce_request_covered (st : TlbShootdownState)
    (target : CoreId) (d : TlbShootdownDescriptor) :
    d ∈ (enqueueShootdownOrCoalesce st target d).pendingOnCore target ∨
      ∃ d' ∈ (enqueueShootdownOrCoalesce st target d).pendingOnCore target,
        d'.op = TlbInvalidation.vmalle1 := by
  unfold enqueueShootdownOrCoalesce
  split
  next st' heq => exact Or.inl (enqueueShootdown_mem heq)
  next heq =>
    exact Or.inr ⟨{ op := .vmalle1, initiator := d.initiator, generation := d.generation }, by simp, rfl⟩

/-- **WS-SM SM7.A.6 (audit)**: the coalescing enqueue never loses a
*previously queued* request either — every descriptor that was pending
on the target before the call is still pending afterwards, or a
full-flush descriptor (which supersedes it) is.  Together with
`enqueueShootdownOrCoalesce_request_covered` (the same claim for the
*new* descriptor) this pins the syntactic no-invalidation-lost
property over the entire queue, not just the incoming request. -/
theorem enqueueShootdownOrCoalesce_pending_covered (st : TlbShootdownState)
    (target : CoreId) (d : TlbShootdownDescriptor) :
    ∀ dOld ∈ st.pendingOnCore target,
      dOld ∈ (enqueueShootdownOrCoalesce st target d).pendingOnCore target ∨
        ∃ d' ∈ (enqueueShootdownOrCoalesce st target d).pendingOnCore target,
          d'.op = TlbInvalidation.vmalle1 := by
  intro dOld hOld
  unfold enqueueShootdownOrCoalesce
  split
  next st' heq =>
    left
    rw [enqueueShootdown_pending_target heq]
    exact List.mem_append_left _ hOld
  next heq =>
    right
    exact ⟨{ op := .vmalle1, initiator := d.initiator, generation := d.generation }, by simp, rfl⟩

/-- **WS-SM SM7.A.6**: the coalescing enqueue preserves the capacity
invariant **unconditionally** — no success hypothesis needed (the
collapse arm leaves a one-element queue). -/
theorem enqueueShootdownOrCoalesce_preserves_pendingBounded
    {st : TlbShootdownState} (hB : pendingBounded st) (target : CoreId)
    (d : TlbShootdownDescriptor) :
    pendingBounded (enqueueShootdownOrCoalesce st target d) := by
  unfold enqueueShootdownOrCoalesce
  split
  next st' heq => exact enqueueShootdown_preserves_pendingBounded hB heq
  next heq =>
    intro c
    by_cases hc : c = target
    · subst hc
      rw [TlbShootdownState.setPendingOnCore_pendingOnCore_self]
      exact maxPendingPerCore_pos
    · rw [TlbShootdownState.setPendingOnCore_pendingOnCore_ne st target c _
        (fun he => hc he.symm)]
      exact hB c

/-- **WS-SM SM7.A.6**: the coalescing enqueue frames every other core's
queue. -/
theorem enqueueShootdownOrCoalesce_frame_pending (st : TlbShootdownState)
    {target c : CoreId} (hc : c ≠ target) (d : TlbShootdownDescriptor) :
    (enqueueShootdownOrCoalesce st target d).pendingOnCore c =
      st.pendingOnCore c := by
  unfold enqueueShootdownOrCoalesce
  split
  next st' heq => exact enqueueShootdown_frame_pending heq hc
  next heq =>
    exact TlbShootdownState.setPendingOnCore_pendingOnCore_ne st target c _
      hc.symm

/-- **WS-SM SM7.A.6**: the coalescing enqueue never touches any ack
flag. -/
theorem enqueueShootdownOrCoalesce_frame_ack (st : TlbShootdownState)
    (target c : CoreId) (d : TlbShootdownDescriptor) :
    (enqueueShootdownOrCoalesce st target d).ackOnCore c = st.ackOnCore c := by
  unfold enqueueShootdownOrCoalesce
  split
  next st' heq => exact enqueueShootdown_frame_ack heq c
  next heq => simp

/-- **WS-SM SM7.F.3 (PR #854 review)**: the coalescing enqueue preserves
well-formedness — it frames both the ack vector and the counter. -/
theorem enqueueShootdownOrCoalesce_preserves_ackBounded
    {st : TlbShootdownState} (hW : ackBounded st) (target : CoreId)
    (d : TlbShootdownDescriptor) :
    ackBounded (enqueueShootdownOrCoalesce st target d) := by
  intro c
  unfold enqueueShootdownOrCoalesce
  split
  next st' heq =>
    rw [enqueueShootdown_frame_ackedGen heq c,
      enqueueShootdown_frame_roundGeneration heq]
    exact hW c
  next heq =>
    show _ ≤ st.roundGeneration
    simpa [TlbShootdownState.ackedGenOnCore, TlbShootdownState.setPendingOnCore]
      using hW c

-- ============================================================================
-- SM7.A.5 — drainShootdowns
-- ============================================================================

/-- **WS-SM SM7.A.5**: drain a core's pending-shootdown queue.

Called from the `.tlbShootdownReq` SGI handler (SM7.B.3) on the
*target* core: returns the complete FIFO queue (for the handler to
execute one local TLBI per descriptor) and the state with that core's
queue emptied.

Deliberately does **not** set the ack flag: the handler must retire
the drained invalidations (`tlbiForSharing` + `dsb`) *before*
acknowledging, so the ack is a separate `acknowledgeShootdown` step —
fusing them here would let the pure model claim an acknowledgment the
runtime had not yet earned, breaking the SM7.B.4 release-acquire
correspondence. -/
def drainShootdowns (st : TlbShootdownState) (c : CoreId) :
    List TlbShootdownDescriptor × TlbShootdownState :=
  (st.pendingOnCore c, st.setPendingOnCore c [])

/-- **WS-SM SM7.A.5**: the drain returns the *entire* pending queue in
FIFO order — the completeness half of Theorem 3.3.1's remote-core case
(every posted invalidation reaches the handler). -/
theorem drainShootdowns_fst (st : TlbShootdownState) (c : CoreId) :
    (drainShootdowns st c).1 = st.pendingOnCore c := rfl

/-- **WS-SM SM7.A.5**: a descriptor is drained iff it was pending —
membership form of `drainShootdowns_fst`. -/
theorem mem_drainShootdowns_fst_iff (st : TlbShootdownState) (c : CoreId)
    (d : TlbShootdownDescriptor) :
    d ∈ (drainShootdowns st c).1 ↔ d ∈ st.pendingOnCore c := Iff.rfl

/-- **WS-SM SM7.A.5**: after the drain the core's queue is empty. -/
@[simp] theorem drainShootdowns_pending_self (st : TlbShootdownState)
    (c : CoreId) :
    (drainShootdowns st c).2.pendingOnCore c = [] := by
  simp [drainShootdowns]

/-- **WS-SM SM7.A.5**: draining core `c` leaves every other core's
queue untouched. -/
theorem drainShootdowns_frame_pending (st : TlbShootdownState)
    {c c' : CoreId} (h : c' ≠ c) :
    (drainShootdowns st c).2.pendingOnCore c' = st.pendingOnCore c' := by
  simp only [drainShootdowns]
  exact TlbShootdownState.setPendingOnCore_pendingOnCore_ne st c c' [] h.symm

/-- **WS-SM SM7.A.5**: draining never touches any ack flag (the ack is
the separate, post-TLBI `acknowledgeShootdown` step). -/
theorem drainShootdowns_frame_ack (st : TlbShootdownState) (c c' : CoreId) :
    (drainShootdowns st c).2.ackOnCore c' = st.ackOnCore c' := by
  simp [drainShootdowns, TlbShootdownState.ackOnCore,
    TlbShootdownState.ackedGenOnCore, TlbShootdownState.setPendingOnCore]

/-- **WS-SM SM7.F.3**: the raw-generation form of the frame above. -/
theorem drainShootdowns_frame_ackedGen (st : TlbShootdownState)
    (c c' : CoreId) :
    (drainShootdowns st c).2.ackedGenOnCore c' = st.ackedGenOnCore c' := by
  simp [drainShootdowns, TlbShootdownState.ackedGenOnCore,
    TlbShootdownState.setPendingOnCore]

/-- **WS-SM SM7.F.3 (PR #854 review)**: draining preserves
well-formedness — it touches neither the ack vector nor the counter. -/
theorem drainShootdowns_preserves_ackBounded {st : TlbShootdownState}
    (hW : ackBounded st) (c : CoreId) :
    ackBounded (drainShootdowns st c).2 := by
  intro c'
  rw [drainShootdowns_frame_ackedGen]
  show _ ≤ st.roundGeneration
  exact hW c'

/-- **WS-SM SM7.A.6**: draining preserves the capacity invariant (the
drained queue drops to length `0`; the rest are framed). -/
theorem drainShootdowns_preserves_pendingBounded {st : TlbShootdownState}
    (hB : pendingBounded st) (c : CoreId) :
    pendingBounded (drainShootdowns st c).2 := by
  intro c'
  by_cases hc : c' = c
  · subst hc
    simp
  · rw [drainShootdowns_frame_pending st hc]
    exact hB c'

/-- **WS-SM SM7.A.5**: a second drain of the same core returns nothing
— draining is exhaustive, so a spurious duplicate `.tlbShootdownReq`
SGI is harmless (the handler TLBIs nothing and re-acknowledges). -/
theorem drainShootdowns_drain_twice (st : TlbShootdownState) (c : CoreId) :
    (drainShootdowns (drainShootdowns st c).2 c).1 = [] := by
  rw [drainShootdowns_fst]
  simp

/-- **WS-SM SM7.A.6**: draining restores capacity — an enqueue onto a
just-drained core always succeeds (`0 < maxPendingPerCore`). -/
theorem enqueueShootdown_isSome_after_drain (st : TlbShootdownState)
    (c : CoreId) (d : TlbShootdownDescriptor) :
    (enqueueShootdown (drainShootdowns st c).2 c d).isSome := by
  rw [enqueueShootdown_isSome_iff, drainShootdowns_pending_self]
  exact maxPendingPerCore_pos

/-- **WS-SM SM7.F.3**: draining never allocates a round. -/
theorem drainShootdowns_frame_roundGeneration (st : TlbShootdownState)
    (c : CoreId) :
    (drainShootdowns st c).2.roundGeneration = st.roundGeneration := rfl

/-- **WS-SM SM7.A.4 + SM7.A.5**: enqueue/drain round trip — the target's
handler drains exactly the pre-existing queue with the new descriptor
appended, in FIFO order. -/
theorem drainShootdowns_after_enqueue {st st' : TlbShootdownState}
    {target : CoreId} {d : TlbShootdownDescriptor}
    (h : enqueueShootdown st target d = some st') :
    (drainShootdowns st' target).1 = st.pendingOnCore target ++ [d] := by
  rw [drainShootdowns_fst, enqueueShootdown_pending_target h]

-- ============================================================================
-- SM7.F.3 — Round-generation-selective drain (a commit drains its own rounds)
-- ============================================================================
--
-- `drainShootdowns` empties a core's queue wholesale.  That is the right
-- model of a *target's own* `.tlbShootdownReq` handler under the round-
-- serialisation contract (its queue then holds exactly the in-flight
-- round's descriptors), but it is the wrong model of the **initiator's
-- deferred catch-up**, which is a second atomic step taken *after* the
-- hardware round and NOT under the round lock.  Between a commit's
-- posting step and its catch-up step another core's commit can post its
-- own round; a wholesale drain would swallow those freshly-queued
-- descriptors and declare the model quiescent before that round's SGIs
-- had fired.  The window drain below is keyed on the descriptor's round
-- generation, so a catch-up retires exactly the rounds its own commit
-- opened and leaves every concurrent round's work pending.

/-- **WS-SM SM7.F.3**: does generation `g` belong to the round window a
single syscall commit opened?

A commit allocates a *contiguous* block of generations: `lo` is the
`roundGeneration` the commit observed on entry and `hi` the one it left
behind, so the rounds it opened are exactly `lo < g ≤ hi`.  A commit
that opened no round has `lo = hi`, and the window is empty
(`inRoundWindow_empty`).  Most maintenance-bearing syscalls open one
round; the retype-with-shootdown wrappers open up to two (the destroyed
and the installed ASID — `retypeShootdownAsidList`), which is why the
diff recovery is a window rather than a single generation. -/
def inRoundWindow (lo hi g : Nat) : Bool := decide (lo < g ∧ g ≤ hi)

/-- **WS-SM SM7.F.3**: membership in the window, as a proposition. -/
theorem inRoundWindow_iff (lo hi g : Nat) :
    inRoundWindow lo hi g = true ↔ (lo < g ∧ g ≤ hi) := by
  simp [inRoundWindow]

/-- **WS-SM SM7.F.3**: a commit that opened no round has an empty
window — its catch-up drains nothing, which is exactly the inertness the
non-shootdown syscalls need. -/
theorem inRoundWindow_empty (lo g : Nat) : inRoundWindow lo lo g = false := by
  simp only [inRoundWindow, decide_eq_false_iff_not, not_and, Nat.not_le]
  omega

/-- **WS-SM SM7.F.3**: the generation a round-open allocates is always in
that commit's own window — the well-formedness fact every posting site
discharges (`lo` is the pre-commit counter, the round's generation is
`lo + 1`, and `hi` is at least that). -/
theorem inRoundWindow_succ_self {lo hi : Nat} (h : lo + 1 ≤ hi) :
    inRoundWindow lo hi (lo + 1) = true := by
  rw [inRoundWindow_iff]
  omega

/-- **WS-SM SM7.F.3**: drain exactly the descriptors this commit's own
rounds posted onto core `c`, leaving every *other* round's queued work
pending.

Returns the drained descriptors in FIFO order (`List.filter` is
order-preserving, so the SM7.A.5 FIFO contract carries) together with
the state whose queue retains the complement.  This is the operation the
live catch-up seam runs (`shootdownCatchUpPerCoreInWindow`); under the
round-serialisation regime — where a core's queue holds only the
in-flight round's descriptors — it coincides with the wholesale
`drainShootdowns` (`drainShootdownsInWindow_eq_drainShootdowns`), which
is how every SM7.A/B round theorem carries over unchanged. -/
def drainShootdownsInWindow (st : TlbShootdownState) (c : CoreId)
    (lo hi : Nat) : List TlbShootdownDescriptor × TlbShootdownState :=
  ((st.pendingOnCore c).filter (fun d => inRoundWindow lo hi d.generation),
   st.setPendingOnCore c
     ((st.pendingOnCore c).filter
       (fun d => !inRoundWindow lo hi d.generation)))

/-- **WS-SM SM7.F.3**: the window drain returns the in-window prefix-
preserving sublist of the pending queue. -/
theorem drainShootdownsInWindow_fst (st : TlbShootdownState) (c : CoreId)
    (lo hi : Nat) :
    (drainShootdownsInWindow st c lo hi).1 =
      (st.pendingOnCore c).filter (fun d => inRoundWindow lo hi d.generation) :=
  rfl

/-- **WS-SM SM7.F.3**: a descriptor is drained iff it was pending *and*
belongs to this commit's rounds. -/
theorem mem_drainShootdownsInWindow_fst_iff (st : TlbShootdownState)
    (c : CoreId) (lo hi : Nat) (d : TlbShootdownDescriptor) :
    d ∈ (drainShootdownsInWindow st c lo hi).1 ↔
      (d ∈ st.pendingOnCore c ∧ inRoundWindow lo hi d.generation = true) := by
  rw [drainShootdownsInWindow_fst, List.mem_filter]

/-- **WS-SM SM7.F.3**: every drained descriptor was pending — the window
drain never invents work. -/
theorem mem_pending_of_mem_drainShootdownsInWindow_fst {st : TlbShootdownState}
    {c : CoreId} {lo hi : Nat} {d : TlbShootdownDescriptor}
    (h : d ∈ (drainShootdownsInWindow st c lo hi).1) :
    d ∈ st.pendingOnCore c :=
  ((mem_drainShootdownsInWindow_fst_iff st c lo hi d).mp h).1

/-- **WS-SM SM7.F.3**: after the window drain, core `c`'s queue is
exactly the out-of-window complement. -/
@[simp] theorem drainShootdownsInWindow_pending_self (st : TlbShootdownState)
    (c : CoreId) (lo hi : Nat) :
    (drainShootdownsInWindow st c lo hi).2.pendingOnCore c =
      (st.pendingOnCore c).filter
        (fun d => !inRoundWindow lo hi d.generation) := by
  simp [drainShootdownsInWindow]

/-- **WS-SM SM7.F.3 (the race-freedom lemma)**: a descriptor posted by a
round *outside* this commit's window is still pending after the drain.

This is the model-fidelity property the whole generation mechanism
exists for: a concurrently-posted round's descriptors survive another
round's catch-up, so the model can never claim a core clean of an
invalidation whose SGI has not yet fired. -/
theorem drainShootdownsInWindow_preserves_foreign {st : TlbShootdownState}
    {c : CoreId} {lo hi : Nat} {d : TlbShootdownDescriptor}
    (hmem : d ∈ st.pendingOnCore c)
    (hout : inRoundWindow lo hi d.generation = false) :
    d ∈ (drainShootdownsInWindow st c lo hi).2.pendingOnCore c := by
  rw [drainShootdownsInWindow_pending_self, List.mem_filter]
  exact ⟨hmem, by simp [hout]⟩

/-- **WS-SM SM7.F.3**: the dual — a descriptor this commit's own rounds
posted is gone from the queue afterwards (the catch-up genuinely
completes its own work). -/
theorem drainShootdownsInWindow_drains_own {st : TlbShootdownState}
    {c : CoreId} {lo hi : Nat} {d : TlbShootdownDescriptor}
    (hin : inRoundWindow lo hi d.generation = true) :
    d ∉ (drainShootdownsInWindow st c lo hi).2.pendingOnCore c := by
  rw [drainShootdownsInWindow_pending_self, List.mem_filter]
  simp [hin]

/-- **WS-SM SM7.F.3**: the window drain touches only core `c`'s queue. -/
theorem drainShootdownsInWindow_frame_pending (st : TlbShootdownState)
    {c c' : CoreId} (h : c' ≠ c) (lo hi : Nat) :
    (drainShootdownsInWindow st c lo hi).2.pendingOnCore c' =
      st.pendingOnCore c' := by
  simp only [drainShootdownsInWindow]
  exact TlbShootdownState.setPendingOnCore_pendingOnCore_ne st c c' _ h.symm

/-- **WS-SM SM7.F.3**: the window drain never touches an ack flag (the
acknowledgment is the separate, post-TLBI step). -/
theorem drainShootdownsInWindow_frame_ack (st : TlbShootdownState)
    (c c' : CoreId) (lo hi : Nat) :
    (drainShootdownsInWindow st c lo hi).2.ackOnCore c' = st.ackOnCore c' := by
  simp [drainShootdownsInWindow, TlbShootdownState.ackOnCore,
    TlbShootdownState.ackedGenOnCore, TlbShootdownState.setPendingOnCore]

/-- **WS-SM SM7.F.3**: the raw-generation form of the frame above. -/
theorem drainShootdownsInWindow_frame_ackedGen (st : TlbShootdownState)
    (c c' : CoreId) (lo hi : Nat) :
    (drainShootdownsInWindow st c lo hi).2.ackedGenOnCore c' =
      st.ackedGenOnCore c' := by
  simp [drainShootdownsInWindow, TlbShootdownState.ackedGenOnCore,
    TlbShootdownState.setPendingOnCore]

/-- **WS-SM SM7.F.3**: the window drain never allocates a round. -/
theorem drainShootdownsInWindow_frame_roundGeneration (st : TlbShootdownState)
    (c : CoreId) (lo hi : Nat) :
    (drainShootdownsInWindow st c lo hi).2.roundGeneration =
      st.roundGeneration := rfl

/-- **WS-SM SM7.F.3 (PR #854 review)**: the window drain preserves
well-formedness — it touches neither the ack vector nor the counter. -/
theorem drainShootdownsInWindow_preserves_ackBounded {st : TlbShootdownState}
    (hW : ackBounded st) (c : CoreId) (lo hi : Nat) :
    ackBounded (drainShootdownsInWindow st c lo hi).2 := by
  intro c'
  rw [drainShootdownsInWindow_frame_ackedGen]
  show _ ≤ st.roundGeneration
  exact hW c'

/-- **WS-SM SM7.F.3**: the window drain preserves the capacity invariant
— a filtered queue is never longer than the original. -/
theorem drainShootdownsInWindow_preserves_pendingBounded
    {st : TlbShootdownState} (hB : pendingBounded st) (c : CoreId)
    (lo hi : Nat) :
    pendingBounded (drainShootdownsInWindow st c lo hi).2 := by
  intro c'
  by_cases hc : c' = c
  · subst hc
    rw [drainShootdownsInWindow_pending_self]
    exact Nat.le_trans (List.length_filter_le _ _) (hB c')
  · rw [drainShootdownsInWindow_frame_pending st hc]
    exact hB c'

/-- **WS-SM SM7.F.3 (the bridge)**: when every descriptor pending on
core `c` belongs to this commit's window — the round-serialisation
regime, where a core's queue holds only the in-flight round's work — the
selective drain **is** the wholesale `drainShootdowns`.

Every SM7.A/B round theorem is stated against `drainShootdowns`; this is
what carries them to the live, generation-selective seam. -/
theorem drainShootdownsInWindow_eq_drainShootdowns {st : TlbShootdownState}
    {c : CoreId} {lo hi : Nat}
    (hall : ∀ d ∈ st.pendingOnCore c, inRoundWindow lo hi d.generation = true) :
    drainShootdownsInWindow st c lo hi = drainShootdowns st c := by
  have hself : (st.pendingOnCore c).filter
      (fun d => inRoundWindow lo hi d.generation) = st.pendingOnCore c :=
    List.filter_eq_self.mpr hall
  have hcomp : (st.pendingOnCore c).filter
      (fun d => !inRoundWindow lo hi d.generation) = [] := by
    refine List.filter_eq_nil_iff.mpr fun d hd => ?_
    simp [hall d hd]
  simp only [drainShootdownsInWindow, drainShootdowns, hself, hcomp]

/-- **WS-SM SM7.F.3**: from a state whose queues hold only this commit's
own rounds, the window drain is the wholesale drain on *every* core —
the fold-level form of the bridge. -/
theorem drainShootdownsInWindow_eq_drainShootdowns_of_all {st : TlbShootdownState}
    {lo hi : Nat}
    (hall : ∀ (c : CoreId), ∀ d ∈ st.pendingOnCore c,
      inRoundWindow lo hi d.generation = true) (c : CoreId) :
    drainShootdownsInWindow st c lo hi = drainShootdowns st c :=
  drainShootdownsInWindow_eq_drainShootdowns (hall c)

-- ============================================================================
-- SM7.A.3 — Acknowledgment operations
-- ============================================================================

/-- **WS-SM SM7.A.3 + SM7.F.3 (PR #854 review)**: record that core `c`
has serviced every round up to and including generation `g`.

The target's SGI handler calls this *after* its drained invalidations
have retired locally (plan §3.2 step 4c).  In the Rust runtime this is
`acked_gen.fetch_max(g, Release)` — the release edge of the SM7.B.4
release-acquire pairing that lets the initiator's acquire-poll conclude
the target's TLBIs happened-before the generation it observes.

`max` rather than a plain store, mirroring `fetch_max`: an
acknowledgment may only ever move a core's generation forward, so a
late-delivered handler run for an *older* round can re-affirm that
older generation without retracting a newer one.  The generation
argument is what makes the acknowledgment name the round it
discharged — a window drain passes its own window's upper bound and
therefore cannot claim a concurrently-posted round it did not
drain. -/
def acknowledgeShootdown (st : TlbShootdownState) (c : CoreId) (g : Nat) :
    TlbShootdownState :=
  st.setAckedGenOnCore c (max (st.ackedGenOnCore c) g)

/-- **WS-SM SM7.F.3**: acknowledging never allocates a round. -/
@[simp] theorem acknowledgeShootdown_roundGeneration (st : TlbShootdownState)
    (c : CoreId) (g : Nat) :
    (acknowledgeShootdown st c g).roundGeneration = st.roundGeneration := rfl

/-- **WS-SM SM7.F.3**: acknowledging generation `g` leaves the caller's
slot at least `g`. -/
@[simp] theorem acknowledgeShootdown_ackedGenOnCore_self
    (st : TlbShootdownState) (c : CoreId) (g : Nat) :
    (acknowledgeShootdown st c g).ackedGenOnCore c =
      max (st.ackedGenOnCore c) g := by
  simp [acknowledgeShootdown]

/-- **WS-SM SM7.A.3**: acknowledging the round currently open marks the
caller acknowledged — the generation form of the original flag set. -/
@[simp] theorem acknowledgeShootdown_ackOnCore_self (st : TlbShootdownState)
    (c : CoreId) {g : Nat} (h : st.roundGeneration ≤ g) :
    (acknowledgeShootdown st c g).ackOnCore c = true := by
  simp only [TlbShootdownState.ackOnCore, acknowledgeShootdown_ackedGenOnCore_self,
    acknowledgeShootdown_roundGeneration, decide_eq_true_eq]
  exact Nat.le_trans h (Nat.le_max_right _ _)

/-- **WS-SM SM7.A.3**: acknowledging leaves every *other* core's slot
untouched — each target answers only for itself. -/
theorem acknowledgeShootdown_ackOnCore_ne (st : TlbShootdownState)
    {c c' : CoreId} (g : Nat) (h : c' ≠ c) :
    (acknowledgeShootdown st c g).ackOnCore c' = st.ackOnCore c' := by
  simp only [acknowledgeShootdown]
  exact TlbShootdownState.setAckedGenOnCore_ackOnCore_ne st c c' _ h.symm

/-- **WS-SM SM7.F.3**: the raw-generation form of the frame above. -/
theorem acknowledgeShootdown_ackedGenOnCore_ne (st : TlbShootdownState)
    {c c' : CoreId} (g : Nat) (h : c' ≠ c) :
    (acknowledgeShootdown st c g).ackedGenOnCore c' = st.ackedGenOnCore c' := by
  simp only [acknowledgeShootdown]
  exact TlbShootdownState.setAckedGenOnCore_ackedGenOnCore_ne st c c' _ h.symm

/-- **WS-SM SM7.A.3**: acknowledging never touches any pending queue. -/
theorem acknowledgeShootdown_frame_pending (st : TlbShootdownState)
    (c c' : CoreId) (g : Nat) :
    (acknowledgeShootdown st c g).pendingOnCore c' = st.pendingOnCore c' := by
  simp [acknowledgeShootdown]

/-- **WS-SM SM7.A.6**: acknowledging preserves the capacity invariant. -/
theorem acknowledgeShootdown_preserves_pendingBounded {st : TlbShootdownState}
    (hB : pendingBounded st) (c : CoreId) (g : Nat) :
    pendingBounded (acknowledgeShootdown st c g) := by
  intro c'
  rw [acknowledgeShootdown_frame_pending]
  exact hB c'

/-- **WS-SM SM7.F.3**: acknowledging a generation the opener has already
minted preserves well-formedness. -/
theorem acknowledgeShootdown_preserves_ackBounded {st : TlbShootdownState}
    (hW : ackBounded st) (c : CoreId) {g : Nat} (h : g ≤ st.roundGeneration) :
    ackBounded (acknowledgeShootdown st c g) := by
  intro c'
  rw [acknowledgeShootdown_roundGeneration]
  by_cases hc : c' = c
  · subst hc
    rw [acknowledgeShootdown_ackedGenOnCore_self]
    exact Nat.max_le.mpr ⟨hW c', h⟩
  · rw [acknowledgeShootdown_ackedGenOnCore_ne _ _ hc]
    exact hW c'

/-- **WS-SM SM7.A.3**: acknowledgments only accumulate — an acknowledged
core stays acknowledged under further acknowledgments.  Monotonicity is
what makes the initiator's wait loop's exit condition stable
(`allAcked` cannot regress mid-round; only `beginShootdownRound`
advances the generation, and the global round lock — the module-header
round-serialisation contract — serialises rounds). -/
theorem acknowledgeShootdown_monotone (st : TlbShootdownState)
    (c c' : CoreId) (g : Nat) (h : st.ackOnCore c' = true) :
    (acknowledgeShootdown st c g).ackOnCore c' = true := by
  by_cases hc : c' = c
  · subst hc
    simp only [TlbShootdownState.ackOnCore, acknowledgeShootdown_ackedGenOnCore_self,
      acknowledgeShootdown_roundGeneration, decide_eq_true_eq]
    simp only [TlbShootdownState.ackOnCore, decide_eq_true_eq] at h
    exact Nat.le_trans h (Nat.le_max_left _ _)
  · rw [acknowledgeShootdown_ackOnCore_ne st g hc]
    exact h

/-- **WS-SM SM7.A.3**: an already-acknowledged core survives any fold
of further acknowledgments — the inductive engine behind
`allCores_foldl_acknowledgeShootdown_allAcked`. -/
theorem foldl_acknowledgeShootdown_monotone {l : List CoreId} {g : Nat}
    {st : TlbShootdownState} {c : CoreId} (h : st.ackOnCore c = true) :
    (l.foldl (fun s x => acknowledgeShootdown s x g) st).ackOnCore c = true := by
  induction l generalizing st with
  | nil => simpa using h
  | cons x xs ih =>
    rw [List.foldl_cons]
    exact ih (acknowledgeShootdown_monotone st x c g h)

/-- **WS-SM SM7.A.3**: folding acknowledgments of the round currently
open over a list marks every core in the list acknowledged. -/
theorem foldl_acknowledgeShootdown_sets {l : List CoreId} {g : Nat}
    {st : TlbShootdownState} {c : CoreId} (hc : c ∈ l)
    (hg : st.roundGeneration ≤ g) :
    (l.foldl (fun s x => acknowledgeShootdown s x g) st).ackOnCore c = true := by
  induction l generalizing st with
  | nil => cases hc
  | cons x xs ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hc with hEq | hMem
    · subst hEq
      exact foldl_acknowledgeShootdown_monotone
        (acknowledgeShootdown_ackOnCore_self st _ hg)
    · exact ih hMem (hg)

/-- **WS-SM SM7.A.3**: once every core has acknowledged the round
currently open, `allAcked` holds — the state-level termination anchor
for the SM7.B.5 initiator wait loop
(`shootdown_wait_loop_terminates`): the loop's exit condition is
*reachable* because acknowledging each core in `allCores` (every
`CoreId`, by `allCores` completeness) yields a fully-acknowledged
state, and monotonicity keeps it stable. -/
theorem allCores_foldl_acknowledgeShootdown_allAcked
    (st : TlbShootdownState) {g : Nat} (hg : st.roundGeneration ≤ g) :
    allAcked (allCores.foldl (fun s x => acknowledgeShootdown s x g) st) := by
  intro c
  have hmem : c ∈ allCores := by
    simp [SeLe4n.Kernel.Concurrency.allCores]
  exact foldl_acknowledgeShootdown_sets hmem hg

-- ============================================================================
-- SM7.A.3 — Round initialization (plan §3.2 step 1)
-- ============================================================================

/-- **WS-SM SM7.A.3**: open a new shootdown round.

Resets every ack flag to `false` except the initiator's own, which is
born-`true`: the initiator performs its own invalidation locally
(plan §3.2 steps 1 + 3) and is never waited on.  The SM7.B
`tlbShootdownBroadcast` transition calls this exactly once per round,
*before* enqueueing descriptors and firing `.tlbShootdownReq` SGIs;
the single global round lock (`ShootdownRoundLockId` — the
module-header round-serialisation contract; the per-VSpace VSpaceRoot
lock alone is NOT sufficient) serialises rounds, so a reset can never
race a straggling acknowledgment from a previous round (the previous
initiator only released the round lock after observing `allAcked`,
which happens-after every previous ack-set).

**Generation allocation (SM7.F.3)**: the round open is also where the
round's identity is minted — `roundGeneration` is incremented, and the
posting fold stamps every descriptor of the round with the resulting
value.  The counter is monotone (nothing in this module decreases it),
so generations are allocated `1, 2, 3, …` in commit order and a
descriptor's generation totally orders it against every other round. -/
def beginShootdownRound (st : TlbShootdownState) (initiator : CoreId) :
    TlbShootdownState :=
  { st with roundGeneration := st.roundGeneration + 1 }.setAckedGenOnCore
    initiator (st.roundGeneration + 1)

/-- **WS-SM SM7.A.3**: the initiator is born-acknowledged — it performs
its own invalidation locally and is never waited on. -/
@[simp] theorem beginShootdownRound_ackOnCore_initiator
    (st : TlbShootdownState) (initiator : CoreId) :
    (beginShootdownRound st initiator).ackOnCore initiator = true := by
  simp [beginShootdownRound, TlbShootdownState.ackOnCore,
    TlbShootdownState.ackedGenOnCore, TlbShootdownState.setAckedGenOnCore]

/-- **WS-SM SM7.A.3**: every non-initiator core starts the round
unacknowledged — the initiator genuinely waits on each target.

Needs `ackBounded` since v0.32.113: with generations there is no reset
to make a target unacknowledged, so what makes it so is that its slot
cannot already name the round about to be opened. -/
theorem beginShootdownRound_ackOnCore_target (st : TlbShootdownState)
    (hW : ackBounded st) {initiator c : CoreId} (h : c ≠ initiator) :
    (beginShootdownRound st initiator).ackOnCore c = false := by
  simp only [beginShootdownRound, TlbShootdownState.ackOnCore,
    decide_eq_false_iff_not, Nat.not_le]
  rw [show ({ st with roundGeneration := st.roundGeneration + 1
              : TlbShootdownState }.setAckedGenOnCore initiator
            (st.roundGeneration + 1)).ackedGenOnCore c
        = st.ackedGenOnCore c from
      TlbShootdownState.setAckedGenOnCore_ackedGenOnCore_ne _ _ _ _
        (fun hEq => h hEq.symm)]
  exact Nat.lt_succ_of_le (hW c)

/-- **WS-SM SM7.A.3**: at round start, a core is acknowledged iff it is
the initiator — the exact plan §3.2 step-1 postcondition. -/
theorem beginShootdownRound_ackOnCore_iff (st : TlbShootdownState)
    (hW : ackBounded st) (initiator c : CoreId) :
    (beginShootdownRound st initiator).ackOnCore c = true ↔ c = initiator := by
  by_cases h : c = initiator
  · subst h
    simp
  · simp [beginShootdownRound_ackOnCore_target st hW h, h]

/-- **WS-SM SM7.F.3**: opening a round preserves well-formedness — the
initiator is written exactly the generation just minted and every other
slot was already bounded by the smaller previous generation. -/
theorem beginShootdownRound_preserves_ackBounded {st : TlbShootdownState}
    (hW : ackBounded st) (initiator : CoreId) :
    ackBounded (beginShootdownRound st initiator) := by
  intro c
  show _ ≤ st.roundGeneration + 1
  by_cases h : c = initiator
  · subst h
    simp only [beginShootdownRound,
      TlbShootdownState.setAckedGenOnCore_ackedGenOnCore_self]
    exact Nat.le_refl _
  · simp only [beginShootdownRound]
    rw [TlbShootdownState.setAckedGenOnCore_ackedGenOnCore_ne _ _ _ _
      (fun hEq => h hEq.symm)]
    exact Nat.le_succ_of_le (hW c)

/-- **WS-SM SM7.A.3**: opening a round never touches any pending queue
(descriptors are posted by the subsequent per-target enqueues). -/
theorem beginShootdownRound_frame_pending (st : TlbShootdownState)
    (initiator c : CoreId) :
    (beginShootdownRound st initiator).pendingOnCore c =
      st.pendingOnCore c := by
  simp [beginShootdownRound, TlbShootdownState.pendingOnCore,
    TlbShootdownState.setAckedGenOnCore]

/-- **WS-SM SM7.A.6**: opening a round preserves the capacity
invariant. -/
theorem beginShootdownRound_preserves_pendingBounded
    {st : TlbShootdownState} (hB : pendingBounded st) (initiator : CoreId) :
    pendingBounded (beginShootdownRound st initiator) := by
  intro c
  rw [beginShootdownRound_frame_pending]
  exact hB c

/-- **WS-SM SM7.F.3**: opening a round allocates the next generation. -/
@[simp] theorem beginShootdownRound_roundGeneration (st : TlbShootdownState)
    (initiator : CoreId) :
    (beginShootdownRound st initiator).roundGeneration =
      st.roundGeneration + 1 := rfl

-- ============================================================================
-- SM7.A — Target-masked round initialization (PR #838 review P1)
-- ============================================================================

/-- **WS-SM SM7.F.3 (PR #854 review)**: closed form for a fold of
per-core generation writes — a core's slot is `g` exactly when the fold
visited it, and untouched otherwise.

Replaces the pre-v0.32.113 `foldl_setAckedGen_ackedGenOnCore`.  A masked
round used to *clear* the targets' flags; with generations there is no
clear at all — the round open raises `roundGeneration` and writes the
new generation to the cores that are born-acknowledged, which leaves
every target behind automatically.  That is the same change the Rust
side made when SM7.F.3 deleted `reset_for_round`. -/
theorem foldl_setAckedGen_ackedGenOnCore (l : List CoreId) (g : Nat) :
    ∀ (st : TlbShootdownState) (c : CoreId),
      (l.foldl (fun (s : TlbShootdownState) x => s.setAckedGenOnCore x g)
          st).ackedGenOnCore c =
        if c ∈ l then g else st.ackedGenOnCore c := by
  induction l with
  | nil => intro st c; simp
  | cons x xs ih =>
    intro st c
    rw [List.foldl_cons, ih]
    by_cases hcx : c ∈ xs
    · simp [hcx, List.mem_cons]
    · by_cases hce : c = x
      · subst hce
        simp [hcx]
      · rw [if_neg hcx, if_neg (by simp [List.mem_cons, hce, hcx])]
        exact TlbShootdownState.setAckedGenOnCore_ackedGenOnCore_ne st x c g
          (fun h => hce h.symm)

/-- **WS-SM SM7.F.3**: a fold of generation writes never touches any
pending queue. -/
theorem foldl_setAckedGen_pendingOnCore (l : List CoreId) (g : Nat) :
    ∀ (st : TlbShootdownState) (c : CoreId),
      (l.foldl (fun (s : TlbShootdownState) x => s.setAckedGenOnCore x g)
          st).pendingOnCore c =
        st.pendingOnCore c := by
  induction l with
  | nil => intro st c; rfl
  | cons x xs ih =>
    intro st c
    rw [List.foldl_cons, ih]
    simp

/-- **WS-SM SM7.F.3**: a fold of generation writes never allocates a
round. -/
theorem foldl_setAckedGen_roundGeneration (l : List CoreId) (g : Nat) :
    ∀ st : TlbShootdownState,
      (l.foldl (fun (s : TlbShootdownState) x => s.setAckedGenOnCore x g)
          st).roundGeneration = st.roundGeneration := by
  induction l with
  | nil => intro st; rfl
  | cons x xs ih =>
    intro st
    rw [List.foldl_cons, ih]
    rfl

/-- **WS-SM SM7.F.3**: the cores a masked round opens
born-acknowledged — every core that is not a target. -/
def bornAcknowledged (targets : List CoreId) : List CoreId :=
  allCores.filter (fun c => decide (c ∉ targets))

/-- **WS-SM SM7.F.3**: membership in the born-acknowledged set is
exactly non-membership in the target set (every `CoreId` is in
`allCores`). -/
@[simp] theorem mem_bornAcknowledged (targets : List CoreId) (c : CoreId) :
    c ∈ bornAcknowledged targets ↔ c ∉ targets := by
  simp [bornAcknowledged, SeLe4n.Kernel.Concurrency.allCores]

/-- **WS-SM SM7.A (PR #838 review P1)**: open a shootdown round against
an explicit **target set** — only the targets start unacknowledged;
every non-target (and the initiator) is born-`true`.

This is the model of the runtime's online-masked round (SM7.F.3
removed the ack reset, so the mask now lives on the *wait* —
`all_acked_for_round_in_slice`, `shootdown.rs`, driven by the
`smp::CORE_IRQ_READY` IRQ-serviceable snapshot — PR #839 review P1):
a core that is offline (a partial-core boot — `smp_enabled=false`, the
v1.0.0 default — an `smp_max_cores` cap, or a PSCI CPU_ON rejection),
still mid-bring-up before `enable_irq`, or wedged in the timer-init-
failure halt loop can never take the `.tlbShootdownReq` SGI and
acknowledge, so clearing its flag would make `allAcked` permanently
unreachable and hang the initiator's wait loop.  Leaving it
born-acknowledged is safe: such a core holds no invalidatable TLB
entry — every secondary bring-up runs `tlbi vmalle1` before enabling
its MMU (`rust/sele4n-hal/src/mmu.rs::init_mmu_secondary`), and a core
between MMU-enable and `enable_irq` (or a halted one) executes only
fixed boot / halt-loop mappings that are never unmapped.  SM7.B's
target-set computation must pass exactly the IRQ-serviceable
non-initiator cores, and rounds must not race core bring-up (bring-up
completes during boot, before any user mapping exists to shoot down).

`beginShootdownRoundFor · allCores` is exactly `beginShootdownRound`
(`beginShootdownRoundFor_allCores_eq`) — the fully-online
configuration. -/
def beginShootdownRoundFor (st : TlbShootdownState) (initiator : CoreId)
    (targets : List CoreId) : TlbShootdownState :=
  ((bornAcknowledged targets).foldl
      (fun (s : TlbShootdownState) c =>
        s.setAckedGenOnCore c (st.roundGeneration + 1))
      { st with
          roundGeneration := st.roundGeneration + 1 }).setAckedGenOnCore
    initiator (st.roundGeneration + 1)

/-- **WS-SM SM7.F.3**: the generation a masked round leaves in each
core's slot — the new generation for the initiator and every
non-target, and the core's previous value for a target.

The single closed form the masked-round characterisations below are
read off, so they cannot drift from the definition or each other. -/
theorem beginShootdownRoundFor_ackedGenOnCore (st : TlbShootdownState)
    (initiator : CoreId) (targets : List CoreId) (c : CoreId) :
    (beginShootdownRoundFor st initiator targets).ackedGenOnCore c =
      if c = initiator ∨ c ∉ targets then st.roundGeneration + 1
      else st.ackedGenOnCore c := by
  unfold beginShootdownRoundFor
  by_cases hci : c = initiator
  · subst hci
    rw [TlbShootdownState.setAckedGenOnCore_ackedGenOnCore_self,
      if_pos (Or.inl rfl)]
  · rw [TlbShootdownState.setAckedGenOnCore_ackedGenOnCore_ne _ _ _ _
      (fun h => hci h.symm), foldl_setAckedGen_ackedGenOnCore]
    by_cases hct : c ∈ targets
    · rw [if_neg (by simpa using hct), if_neg (by simp [hci, hct])]
      rfl
    · rw [if_pos (by simpa using hct), if_pos (Or.inr hct)]

/-- **WS-SM SM7.F.3**: opening a masked round advances the generation. -/
theorem beginShootdownRoundFor_gen (st : TlbShootdownState)
    (initiator : CoreId) (targets : List CoreId) :
    (beginShootdownRoundFor st initiator targets).roundGeneration =
      st.roundGeneration + 1 := by
  unfold beginShootdownRoundFor
  rw [TlbShootdownState.setAckedGenOnCore_roundGeneration,
    foldl_setAckedGen_roundGeneration]

/-- **WS-SM SM7.A (PR #838 review P1)**: the initiator and every
non-target are born-acknowledged at a masked round's start.

The direction the liveness capstones use, and it needs no
well-formedness hypothesis: these cores are *written* the round's own
generation, so they are acknowledged outright rather than by an argument
about what their slot cannot already hold. -/
theorem beginShootdownRoundFor_ackOnCore_of_born (st : TlbShootdownState)
    (initiator : CoreId) (targets : List CoreId) {c : CoreId}
    (h : c = initiator ∨ c ∉ targets) :
    (beginShootdownRoundFor st initiator targets).ackOnCore c = true := by
  simp only [TlbShootdownState.ackOnCore, beginShootdownRoundFor_gen,
    beginShootdownRoundFor_ackedGenOnCore, decide_eq_true_eq, if_pos h]
  exact Nat.le_refl _

/-- **WS-SM SM7.A (PR #838 review P1)**: at a masked round's start, a
core is acknowledged iff it is the initiator or not a target — the
non-target ("offline") cores are never waited on.

Needs `ackBounded` since v0.32.113: with generations a target is
unacknowledged because its slot still names an *earlier* round, so the
characterisation depends on no slot naming a round that has not been
opened. -/
theorem beginShootdownRoundFor_ackOnCore_iff (st : TlbShootdownState)
    (hW : ackBounded st) (initiator : CoreId) (targets : List CoreId)
    (c : CoreId) :
    (beginShootdownRoundFor st initiator targets).ackOnCore c = true ↔
      (c = initiator ∨ c ∉ targets) := by
  simp only [TlbShootdownState.ackOnCore, beginShootdownRoundFor_gen,
    beginShootdownRoundFor_ackedGenOnCore, decide_eq_true_eq]
  by_cases h : c = initiator ∨ c ∉ targets
  · rw [if_pos h]
    exact iff_of_true (Nat.le_refl _) h
  · rw [if_neg h]
    exact iff_of_false (Nat.not_le.mpr (Nat.lt_succ_of_le (hW c))) h

/-- **WS-SM SM7.A (PR #838 review P1)**: opening a masked round never
touches any pending queue. -/
theorem beginShootdownRoundFor_frame_pending (st : TlbShootdownState)
    (initiator : CoreId) (targets : List CoreId) (c : CoreId) :
    (beginShootdownRoundFor st initiator targets).pendingOnCore c =
      st.pendingOnCore c := by
  unfold beginShootdownRoundFor
  rw [TlbShootdownState.setAckedGenOnCore_pendingOnCore,
      foldl_setAckedGen_pendingOnCore]
  rfl

/-- **WS-SM SM7.F.3**: opening a masked round preserves
well-formedness. -/
theorem beginShootdownRoundFor_preserves_ackBounded {st : TlbShootdownState}
    (hW : ackBounded st) (initiator : CoreId) (targets : List CoreId) :
    ackBounded (beginShootdownRoundFor st initiator targets) := by
  intro c
  rw [beginShootdownRoundFor_gen, beginShootdownRoundFor_ackedGenOnCore]
  by_cases h : c = initiator ∨ c ∉ targets
  · rw [if_pos h]
    exact Nat.le_refl _
  · rw [if_neg h]
    exact Nat.le_succ_of_le (hW c)


/-- **WS-SM SM7.A (PR #838 review P1)**: opening a masked round
preserves the capacity invariant. -/
theorem beginShootdownRoundFor_preserves_pendingBounded
    {st : TlbShootdownState} (hB : pendingBounded st) (initiator : CoreId)
    (targets : List CoreId) :
    pendingBounded (beginShootdownRoundFor st initiator targets) := by
  intro c
  rw [beginShootdownRoundFor_frame_pending]
  exact hB c

/-- **WS-SM SM7.F.3**: opening a masked round allocates the next
generation, exactly as the unmasked form does — the mask decides who is
waited on, not which round this is. -/
@[simp] theorem beginShootdownRoundFor_roundGeneration (st : TlbShootdownState)
    (initiator : CoreId) (targets : List CoreId) :
    (beginShootdownRoundFor st initiator targets).roundGeneration =
      st.roundGeneration + 1 := by
  unfold beginShootdownRoundFor
  rw [TlbShootdownState.setAckedGenOnCore_roundGeneration,
      foldl_setAckedGen_roundGeneration]

/-- **WS-SM SM7.F.3**: the generation a masked round mints is strictly
above every generation the pre-state could hold — the freshness fact
that makes a round's descriptors distinguishable from every earlier
round's. -/
theorem beginShootdownRoundFor_roundGeneration_gt (st : TlbShootdownState)
    (initiator : CoreId) (targets : List CoreId) :
    st.roundGeneration <
      (beginShootdownRoundFor st initiator targets).roundGeneration := by
  rw [beginShootdownRoundFor_roundGeneration]
  omega

/-- **WS-SM SM7.F.3**: the descriptor the posting fold appends carries
exactly the generation the round open allocated — the agreement that
makes `roundDescriptor` well-formed against `beginShootdownRoundFor`.
Stated as an equation rather than baked into `roundDescriptor`'s
definition so a refactor that changes the round open's allocation
strategy breaks here rather than silently mis-stamping descriptors. -/
theorem roundDescriptor_generation_eq_opened (sd : TlbShootdownState)
    (initiator : CoreId) (targets : List CoreId) (op : TlbInvalidation) :
    (roundDescriptor sd initiator op).generation =
      (beginShootdownRoundFor sd initiator targets).roundGeneration := by
  rw [roundDescriptor_generation, beginShootdownRoundFor_roundGeneration]

/-- **WS-SM SM7.F.3**: a round's own descriptor lands inside the window
`(sd.roundGeneration, (opened state).roundGeneration]` — the window a
commit that opened exactly this one round recovers from its `(pre, post)`
diff.  This is the well-formedness fact the live catch-up needs: what a
commit posts, its own catch-up drains. -/
theorem roundDescriptor_inRoundWindow (sd : TlbShootdownState)
    (initiator : CoreId) (targets : List CoreId) (op : TlbInvalidation) :
    inRoundWindow sd.roundGeneration
        (beginShootdownRoundFor sd initiator targets).roundGeneration
        (roundDescriptor sd initiator op).generation = true := by
  rw [roundDescriptor_generation, beginShootdownRoundFor_roundGeneration,
      inRoundWindow_iff]
  omega

/-- **WS-SM SM7.A (PR #838 review P1)**: with every core targeted, the
masked round-open is exactly `beginShootdownRound` — the fully-online
configuration collapses to the unmasked form (mechanically mirrored on
the Rust side by `sm7f3_wait_matches_conjunction_exhaustively`, whose
all-online rows are the unmasked wait). -/
theorem beginShootdownRoundFor_allCores_eq (st : TlbShootdownState)
    (initiator : CoreId) :
    beginShootdownRoundFor st initiator allCores =
      beginShootdownRound st initiator := by
  refine TlbShootdownState.ext_perCore ?_ ?_ ?_
  case _ =>
    intro c
    rw [beginShootdownRoundFor_frame_pending, beginShootdownRound_frame_pending]
  case _ =>
    intro c
    have hmem : c ∈ allCores := by
      simp [SeLe4n.Kernel.Concurrency.allCores]
    rw [beginShootdownRoundFor_ackedGenOnCore]
    by_cases hci : c = initiator
    · subst hci
      rw [if_pos (Or.inl rfl)]
      simp only [beginShootdownRound,
        TlbShootdownState.setAckedGenOnCore_ackedGenOnCore_self]
    · rw [if_neg (by simp [hci, hmem])]
      simp only [beginShootdownRound]
      rw [TlbShootdownState.setAckedGenOnCore_ackedGenOnCore_ne _ _ _ _
        (fun h => hci h.symm)]
      rfl
  case _ =>
    rw [beginShootdownRoundFor_roundGeneration,
        beginShootdownRound_roundGeneration]

-- ============================================================================
-- SM7.A — Round-level composition (the SM7.B protocol's state skeleton)
-- ============================================================================

/-- **WS-SM SM7.A**: the state-level effect of core `c` completing its
shootdown work — queue drained, flag acknowledged.

This is the *state projection* of the `.tlbShootdownReq` handler
(plan §3.2 step 4), **not** an operation the runtime performs
atomically: the handler executes `drainShootdowns`, then retires one
local TLBI per drained descriptor (`dsb`-completed — an effect on the
SM7.C per-core TLB model, disjoint from this state type), and only
then `acknowledgeShootdown`.  The composition exists so round-level
theorems (`shootdownRound_restores_quiescent`) can fold one step per
target; `completeShootdownOnCore_eq` pins it to the two-step form the
runtime actually takes. -/
def completeShootdownOnCore (st : TlbShootdownState) (c : CoreId) :
    TlbShootdownState :=
  acknowledgeShootdown (drainShootdowns st c).2 c st.roundGeneration

/-- **WS-SM SM7.A**: the round step is definitionally the drain
followed by the acknowledgment — the handler's two state writes, in
the protocol's order.

The acknowledged generation is the round currently open: a whole-queue
drain retires every descriptor posted so far, so it genuinely discharges
every round up to the current one. -/
theorem completeShootdownOnCore_eq (st : TlbShootdownState) (c : CoreId) :
    completeShootdownOnCore st c =
      acknowledgeShootdown (drainShootdowns st c).2 c st.roundGeneration := rfl

/-- **WS-SM SM7.B**: the handler's round step preserves the capacity
invariant — draining empties the handled core's queue and the
acknowledgment touches no queue at all.  Composes the drain and ack
preservation theorems for the `.tlbShootdownReq` handler's
`pendingBounded` bundle carriage. -/
theorem completeShootdownOnCore_preserves_pendingBounded
    {st : TlbShootdownState} (hB : pendingBounded st) (c : CoreId) :
    pendingBounded (completeShootdownOnCore st c) :=
  acknowledgeShootdown_preserves_pendingBounded
    (drainShootdowns_preserves_pendingBounded hB c) c _

/-- **WS-SM SM7.F.3 (PR #854 review)**: the whole-queue round step
preserves well-formedness — it acknowledges the round currently open,
which is by definition not ahead of the counter. -/
theorem completeShootdownOnCore_preserves_ackBounded {st : TlbShootdownState}
    (hW : ackBounded st) (c : CoreId) :
    ackBounded (completeShootdownOnCore st c) := by
  rw [completeShootdownOnCore_eq]
  exact acknowledgeShootdown_preserves_ackBounded
    (drainShootdowns_preserves_ackBounded hW c) c
    (Nat.le_of_eq (drainShootdowns_frame_roundGeneration st c).symm)

/-- **WS-SM SM7.A**: a completed core's queue is empty. -/
@[simp] theorem completeShootdownOnCore_pendingOnCore_self
    (st : TlbShootdownState) (c : CoreId) :
    (completeShootdownOnCore st c).pendingOnCore c = [] := by
  unfold completeShootdownOnCore
  rw [acknowledgeShootdown_frame_pending]
  simp

/-- **WS-SM SM7.A**: a completed core's flag is acknowledged. -/
@[simp] theorem completeShootdownOnCore_ackOnCore_self
    (st : TlbShootdownState) (c : CoreId) :
    (completeShootdownOnCore st c).ackOnCore c = true := by
  unfold completeShootdownOnCore
  exact acknowledgeShootdown_ackOnCore_self _ _
    (Nat.le_of_eq (drainShootdowns_frame_roundGeneration st c).symm)

/-- **WS-SM SM7.A**: completing core `c` frames every other core's
queue. -/
theorem completeShootdownOnCore_frame_pending (st : TlbShootdownState)
    {c c' : CoreId} (h : c' ≠ c) :
    (completeShootdownOnCore st c).pendingOnCore c' = st.pendingOnCore c' := by
  unfold completeShootdownOnCore
  rw [acknowledgeShootdown_frame_pending, drainShootdowns_frame_pending st h]

/-- **WS-SM SM7.F.3**: the whole-queue round step never allocates a
round. -/
@[simp] theorem completeShootdownOnCore_roundGeneration
    (st : TlbShootdownState) (c : CoreId) :
    (completeShootdownOnCore st c).roundGeneration = st.roundGeneration := rfl

/-- **WS-SM SM7.F.3**: a whole-queue round step records the round
currently open. -/
@[simp] theorem completeShootdownOnCore_ackedGenOnCore_self
    (st : TlbShootdownState) (c : CoreId) :
    (completeShootdownOnCore st c).ackedGenOnCore c =
      max (st.ackedGenOnCore c) st.roundGeneration := by
  rw [completeShootdownOnCore_eq, acknowledgeShootdown_ackedGenOnCore_self,
    drainShootdowns_frame_ackedGen]

/-- **WS-SM SM7.F.3**: completing core `c` frames every other core's
acknowledged generation. -/
theorem completeShootdownOnCore_frame_ackedGen (st : TlbShootdownState)
    {c c' : CoreId} (h : c' ≠ c) :
    (completeShootdownOnCore st c).ackedGenOnCore c' = st.ackedGenOnCore c' := by
  rw [completeShootdownOnCore_eq, acknowledgeShootdown_ackedGenOnCore_ne _ _ h,
    drainShootdowns_frame_ackedGen]

/-- **WS-SM SM7.A**: completing core `c` frames every other core's
flag. -/
theorem completeShootdownOnCore_frame_ack (st : TlbShootdownState)
    {c c' : CoreId} (h : c' ≠ c) :
    (completeShootdownOnCore st c).ackOnCore c' = st.ackOnCore c' := by
  unfold completeShootdownOnCore
  rw [acknowledgeShootdown_ackOnCore_ne _ _ h, drainShootdowns_frame_ack]

/-- **WS-SM SM7.F.3**: the generation-selective round step — the state
projection of the initiator's deferred catch-up for core `c`.

Identical to `completeShootdownOnCore` except that the drain is keyed on
this commit's round window, so a concurrently-posted round's descriptors
survive (`completeShootdownOnCoreInWindow_preserves_foreign`).

**PR #854 review**: the acknowledgment names `hi` — this commit's own
round — rather than being unconditional.  Until v0.32.113 it set a bare
flag, so a catch-up that deliberately drained only its own window still
claimed *every* round as acknowledged, and `allAcked` could read true
with a concurrently-posted round's descriptors still pending: the
queues were generation-selective but the acknowledgment was not.
Acknowledging `hi` says exactly what was discharged, which is what the
runtime's `acked_gen` has said since the same review's P1 fix. -/
def completeShootdownOnCoreInWindow (st : TlbShootdownState) (c : CoreId)
    (lo hi : Nat) : TlbShootdownState :=
  acknowledgeShootdown (drainShootdownsInWindow st c lo hi).2 c hi

/-- **WS-SM SM7.F.3**: the window round step is definitionally the
window drain followed by the acknowledgment of the window's own round. -/
theorem completeShootdownOnCoreInWindow_eq (st : TlbShootdownState)
    (c : CoreId) (lo hi : Nat) :
    completeShootdownOnCoreInWindow st c lo hi =
      acknowledgeShootdown (drainShootdownsInWindow st c lo hi).2 c hi := rfl

/-- **WS-SM SM7.F.3 (the race-freedom lemma, round-step form)**: a
descriptor posted by a round outside this commit's window survives the
catch-up step. -/
theorem completeShootdownOnCoreInWindow_preserves_foreign
    {st : TlbShootdownState} {c : CoreId} {lo hi : Nat}
    {d : TlbShootdownDescriptor} (hmem : d ∈ st.pendingOnCore c)
    (hout : inRoundWindow lo hi d.generation = false) :
    d ∈ (completeShootdownOnCoreInWindow st c lo hi).pendingOnCore c := by
  rw [completeShootdownOnCoreInWindow_eq, acknowledgeShootdown_frame_pending]
  exact drainShootdownsInWindow_preserves_foreign hmem hout

/-- **WS-SM SM7.F.3**: the window round step acknowledges its core — for
a window that reaches the round currently open.

The hypothesis is the honest one: a catch-up whose window stops short of
the current generation (because a *later* round has been committed since)
discharges only its own rounds, and must not read as acknowledging the
newer one.  That is exactly the PR #854 review finding. -/
@[simp] theorem completeShootdownOnCoreInWindow_ackOnCore_self
    (st : TlbShootdownState) (c : CoreId) (lo hi : Nat)
    (hhi : st.roundGeneration ≤ hi) :
    (completeShootdownOnCoreInWindow st c lo hi).ackOnCore c = true := by
  rw [completeShootdownOnCoreInWindow_eq]
  exact acknowledgeShootdown_ackOnCore_self _ _
    (Nat.le_trans (Nat.le_of_eq (drainShootdownsInWindow_frame_roundGeneration st c lo hi)) hhi)

/-- **WS-SM SM7.F.3 (PR #854 review)**: the window round step records
exactly the round it drained — a core's acknowledged generation after a
catch-up is its previous value joined with the window's upper bound, and
never more. -/
@[simp] theorem completeShootdownOnCoreInWindow_ackedGenOnCore_self
    (st : TlbShootdownState) (c : CoreId) (lo hi : Nat) :
    (completeShootdownOnCoreInWindow st c lo hi).ackedGenOnCore c =
      max (st.ackedGenOnCore c) hi := by
  rw [completeShootdownOnCoreInWindow_eq,
    acknowledgeShootdown_ackedGenOnCore_self,
    drainShootdownsInWindow_frame_ackedGen _ c c lo hi]

/-- **WS-SM SM7.F.3 (PR #854 review, the headline)**: a catch-up whose
window stops below a foreign round's generation does **not** acknowledge
that round.

The acknowledgment dual of `completeShootdownOnCoreInWindow_preserves_foreign`:
that lemma says the foreign *descriptors* survive the drain, this one
says the foreign *round* is still owed.  Together they are what makes a
concurrently-committed round's work genuinely outstanding in the model
rather than merely present-but-declared-done. -/
theorem completeShootdownOnCoreInWindow_not_acks_foreign
    {st : TlbShootdownState} {c : CoreId} {lo hi g : Nat}
    (hW : st.ackedGenOnCore c < g) (hout : hi < g) :
    (completeShootdownOnCoreInWindow st c lo hi).ackedGenOnCore c < g := by
  rw [completeShootdownOnCoreInWindow_ackedGenOnCore_self]
  exact Nat.max_lt.mpr ⟨hW, hout⟩

/-- **WS-SM SM7.F.3 (PR #854 review)**: the window round step preserves
well-formedness, for a window that does not reach past the round counter.

The hypothesis is the honest one and the live seam supplies it: the
catch-up's window upper bound is the *post*-commit generation, and the
catch-up runs on that post-state, so `hi ≤ roundGeneration` holds
there.  A window claiming to discharge a round that has not been opened
is exactly the state this invariant exists to exclude. -/
theorem completeShootdownOnCoreInWindow_preserves_ackBounded
    {st : TlbShootdownState} (hW : ackBounded st) (c : CoreId) {lo hi : Nat}
    (hhi : hi ≤ st.roundGeneration) :
    ackBounded (completeShootdownOnCoreInWindow st c lo hi) := by
  rw [completeShootdownOnCoreInWindow_eq]
  exact acknowledgeShootdown_preserves_ackBounded
    (drainShootdownsInWindow_preserves_ackBounded hW c lo hi) c
    (Nat.le_trans hhi
      (Nat.le_of_eq (drainShootdownsInWindow_frame_roundGeneration st c lo hi).symm))

/-- **WS-SM SM7.F.3**: the window round step frames every other core's
queue. -/
theorem completeShootdownOnCoreInWindow_frame_pending (st : TlbShootdownState)
    {c c' : CoreId} (h : c' ≠ c) (lo hi : Nat) :
    (completeShootdownOnCoreInWindow st c lo hi).pendingOnCore c' =
      st.pendingOnCore c' := by
  rw [completeShootdownOnCoreInWindow_eq, acknowledgeShootdown_frame_pending,
      drainShootdownsInWindow_frame_pending st h]

/-- **WS-SM SM7.F.3**: the window round step frames every other core's
flag. -/
theorem completeShootdownOnCoreInWindow_frame_ack (st : TlbShootdownState)
    {c c' : CoreId} (h : c' ≠ c) (lo hi : Nat) :
    (completeShootdownOnCoreInWindow st c lo hi).ackOnCore c' =
      st.ackOnCore c' := by
  rw [completeShootdownOnCoreInWindow_eq, acknowledgeShootdown_ackOnCore_ne _ _ h,
      drainShootdownsInWindow_frame_ack]

/-- **WS-SM SM7.F.3**: the window round step never allocates a round. -/
theorem completeShootdownOnCoreInWindow_frame_roundGeneration
    (st : TlbShootdownState) (c : CoreId) (lo hi : Nat) :
    (completeShootdownOnCoreInWindow st c lo hi).roundGeneration =
      st.roundGeneration := rfl

/-- **WS-SM SM7.F.3**: the window round step preserves the capacity
invariant. -/
theorem completeShootdownOnCoreInWindow_preserves_pendingBounded
    {st : TlbShootdownState} (hB : pendingBounded st) (c : CoreId)
    (lo hi : Nat) :
    pendingBounded (completeShootdownOnCoreInWindow st c lo hi) :=
  acknowledgeShootdown_preserves_pendingBounded
    (drainShootdownsInWindow_preserves_pendingBounded hB c lo hi) c _

/-- **WS-SM SM7.F.3 (the bridge, round-step form)**: under the
round-serialisation regime — every descriptor pending on `c` belongs to
this commit's window, whose upper bound is the round currently open —
the generation-selective round step **is** the wholesale
`completeShootdownOnCore`.

The `hhi` hypothesis is new in v0.32.113 and is what the regime supplies:
serialised rounds mean the commit's own window reaches the current
generation, so acknowledging `hi` and acknowledging `roundGeneration`
coincide.  Without serialisation they do not — that difference is the
whole point of the PR #854 review fix, and dropping the hypothesis would
re-assert the identity the fix exists to deny. -/
theorem completeShootdownOnCoreInWindow_eq_complete {st : TlbShootdownState}
    {c : CoreId} {lo hi : Nat}
    (hall : ∀ d ∈ st.pendingOnCore c, inRoundWindow lo hi d.generation = true)
    (hhi : hi = st.roundGeneration) :
    completeShootdownOnCoreInWindow st c lo hi = completeShootdownOnCore st c := by
  rw [completeShootdownOnCoreInWindow_eq, completeShootdownOnCore_eq,
      drainShootdownsInWindow_eq_drainShootdowns hall, hhi]

/-- **WS-SM SM7.B**: round steps at *distinct* cores commute — each
step writes only its own core's queue and flag.  This is the
shootdown-state half of the handler-fold order-independence
(`handleTlbShootdownReqOnCore_comm` in `TlbShootdownProtocol.lean`):
the runtime's catch-up fold may visit targets in any order. -/
theorem completeShootdownOnCore_comm {c₁ c₂ : CoreId} (h : c₁ ≠ c₂)
    (st : TlbShootdownState) :
    completeShootdownOnCore (completeShootdownOnCore st c₁) c₂ =
      completeShootdownOnCore (completeShootdownOnCore st c₂) c₁ := by
  refine TlbShootdownState.ext_perCore ?_ ?_ rfl
  · intro c
    by_cases h1 : c = c₁
    · subst h1
      rw [completeShootdownOnCore_frame_pending _ h,
          completeShootdownOnCore_pendingOnCore_self,
          completeShootdownOnCore_pendingOnCore_self]
    · by_cases h2 : c = c₂
      · subst h2
        rw [completeShootdownOnCore_pendingOnCore_self,
            completeShootdownOnCore_frame_pending _ (Ne.symm h),
            completeShootdownOnCore_pendingOnCore_self]
      · rw [completeShootdownOnCore_frame_pending _ h2,
            completeShootdownOnCore_frame_pending _ h1,
            completeShootdownOnCore_frame_pending _ h1,
            completeShootdownOnCore_frame_pending _ h2]
  · intro c
    by_cases h1 : c = c₁
    · subst h1
      simp [completeShootdownOnCore_frame_ackedGen _ h]
    · by_cases h2 : c = c₂
      · subst h2
        simp [completeShootdownOnCore_frame_ackedGen _ (Ne.symm h)]
      · simp [completeShootdownOnCore_frame_ackedGen _ h1,
              completeShootdownOnCore_frame_ackedGen _ h2]

/-- **WS-SM SM7.A**: closed form for a fold of round steps — a core's
queue is empty exactly when the fold visited it, and untouched
otherwise. -/
theorem foldl_completeShootdownOnCore_pendingOnCore (l : List CoreId) :
    ∀ (st : TlbShootdownState) (c : CoreId),
      (l.foldl completeShootdownOnCore st).pendingOnCore c =
        if c ∈ l then [] else st.pendingOnCore c := by
  induction l with
  | nil => intro st c; simp
  | cons x xs ih =>
    intro st c
    rw [List.foldl_cons, ih]
    by_cases hcx : c ∈ xs
    · simp [hcx, List.mem_cons]
    · by_cases hce : c = x
      · subst hce
        simp [hcx]
      · rw [if_neg hcx, if_neg (by simp [List.mem_cons, hce, hcx]),
            completeShootdownOnCore_frame_pending st hce]

/-- **WS-SM SM7.A**: closed form for a fold of round steps — a core's
flag is acknowledged exactly when the fold visited it, and untouched
otherwise. -/
theorem foldl_completeShootdownOnCore_ackOnCore (l : List CoreId) :
    ∀ (st : TlbShootdownState) (c : CoreId),
      (l.foldl completeShootdownOnCore st).ackOnCore c =
        if c ∈ l then true else st.ackOnCore c := by
  induction l with
  | nil => intro st c; simp
  | cons x xs ih =>
    intro st c
    rw [List.foldl_cons, ih]
    by_cases hcx : c ∈ xs
    · simp [hcx, List.mem_cons]
    · by_cases hce : c = x
      · subst hce
        simp [hcx]
      · rw [if_neg hcx, if_neg (by simp [List.mem_cons, hce, hcx]),
            completeShootdownOnCore_frame_ack st hce]

/-- **WS-SM SM7.A.6**: from a quiescent state, opening a round and
posting one descriptor to each of a duplicate-free target list always
succeeds — the round-level capacity-sufficiency witness the plan §4.1
prose appeals to. -/
theorem beginRound_foldlM_enqueueShootdown_isSome
    {st : TlbShootdownState} (hq : shootdownQuiescent st)
    (initiator : CoreId) {targets : List CoreId} (hnd : targets.Nodup)
    (d : TlbShootdownDescriptor) :
    (targets.foldlM (fun s c => enqueueShootdown s c d)
      (beginShootdownRound st initiator)).isSome := by
  refine foldlM_enqueueShootdown_isSome targets _ hnd (fun c _ => ?_) d
  rw [beginShootdownRound_frame_pending]
  exact hq.1 c

/-- **WS-SM SM7.A capstone**: a complete shootdown round restores
quiescence.

From any quiescent state: open a round (`beginShootdownRound`), post
one descriptor per target (the `foldlM` posting fold — success is a
hypothesis here and is guaranteed from quiescence by
`beginRound_foldlM_enqueueShootdown_isSome`), then let every target
complete (`completeShootdownOnCore` per target).  Provided the targets
cover every non-initiator core (plan §3.2 step 2 — `allCores \ {c₀}`),
the final state is quiescent again: every queue empty, every flag
acknowledged — so the *next* round's posting fold succeeds too, closing
the induction that keeps `maxPendingPerCore` sufficient forever.

Generalises the concrete 4-core walk in
`tests/SmpTlbShootdownSuite.lean` §3.7 to arbitrary initiators, target
lists, and descriptors; no `Nodup` hypothesis is needed (a duplicated
target is drained twice — the second drain returns nothing,
`drainShootdowns_drain_twice`). -/
theorem shootdownRound_restores_quiescent
    {st : TlbShootdownState} (hq : shootdownQuiescent st)
    (initiator : CoreId) {targets : List CoreId}
    (hcov : ∀ c : CoreId, c ≠ initiator → c ∈ targets)
    {d : TlbShootdownDescriptor} {posted : TlbShootdownState}
    (hpost : targets.foldlM (fun s c => enqueueShootdown s c d)
      (beginShootdownRound st initiator) = some posted) :
    shootdownQuiescent (targets.foldl completeShootdownOnCore posted) := by
  constructor
  · intro c
    rw [foldl_completeShootdownOnCore_pendingOnCore]
    by_cases hc : c ∈ targets
    · rw [if_pos hc]
    · rw [if_neg hc, foldlM_enqueueShootdown_frame_pending hpost hc,
          beginShootdownRound_frame_pending]
      exact hq.1 c
  · intro c
    rw [foldl_completeShootdownOnCore_ackOnCore]
    by_cases hc : c ∈ targets
    · rw [if_pos hc]
    · rw [if_neg hc]
      have hci : c = initiator :=
        Decidable.byContradiction fun hne => hc (hcov c hne)
      subst hci
      rw [foldlM_enqueueShootdown_frame_ack hpost c,
          beginShootdownRound_ackOnCore_initiator]

/-- **WS-SM SM7.A (PR #838 review P1)**: a masked round's posting fold
from a quiescent state always succeeds — the partial-online analogue of
`beginRound_foldlM_enqueueShootdown_isSome`. -/
theorem beginRoundFor_foldlM_enqueueShootdown_isSome
    {st : TlbShootdownState} (hq : shootdownQuiescent st)
    (initiator : CoreId) {targets : List CoreId} (hnd : targets.Nodup)
    (d : TlbShootdownDescriptor) :
    (targets.foldlM (fun s c => enqueueShootdown s c d)
      (beginShootdownRoundFor st initiator targets)).isSome := by
  refine foldlM_enqueueShootdown_isSome targets _ hnd (fun c _ => ?_) d
  rw [beginShootdownRoundFor_frame_pending]
  exact hq.1 c

/-- **WS-SM SM7.A capstone, masked form (PR #838 review P1)**: a
complete round against an arbitrary target set restores quiescence —
no coverage hypothesis needed, because non-targets ("offline" cores)
are born-acknowledged rather than waited on.  This is the round
SM7.B actually runs on a partial-core boot: targets = the online
non-initiator cores; the liveness half of the review-P1 fix, stated
generally. -/
theorem shootdownRoundFor_restores_quiescent
    {st : TlbShootdownState} (hq : shootdownQuiescent st)
    (initiator : CoreId) {targets : List CoreId}
    {d : TlbShootdownDescriptor} {posted : TlbShootdownState}
    (hpost : targets.foldlM (fun s c => enqueueShootdown s c d)
      (beginShootdownRoundFor st initiator targets) = some posted) :
    shootdownQuiescent (targets.foldl completeShootdownOnCore posted) := by
  constructor
  · intro c
    rw [foldl_completeShootdownOnCore_pendingOnCore]
    by_cases hc : c ∈ targets
    · rw [if_pos hc]
    · rw [if_neg hc, foldlM_enqueueShootdown_frame_pending hpost hc,
          beginShootdownRoundFor_frame_pending]
      exact hq.1 c
  · intro c
    rw [foldl_completeShootdownOnCore_ackOnCore]
    by_cases hc : c ∈ targets
    · rw [if_pos hc]
    · rw [if_neg hc, foldlM_enqueueShootdown_frame_ack hpost c]
      exact beginShootdownRoundFor_ackOnCore_of_born st initiator targets
        (Or.inr hc)

-- ============================================================================
-- SM7.A — Round + per-core pending-queue lock identifiers (the SM7.B.7 seam)
-- ============================================================================

/-- **WS-SM SM7.A audit**: identifier for THE single global
shootdown-round lock — the serialiser the module-header
round-serialisation contract requires.

The ack vector carries no round identity, so rounds must not overlap
system-wide; the per-VSpace VSpaceRoot lock cannot guarantee that
across distinct VSpaces (see the module header for the concrete
stale-TLB and mutual-hang interleavings).  SM7.B.7's
`lockSet_tlbShootdown_correct` acquires this lock first — before the
VSpaceRoot object lock's TLBI section completes and before any
per-core `ShootdownQueueLockId` — and releases it only after the
initiator observes `allAcked`.

The type is deliberately fieldless: there is exactly one round lock
(`ShootdownRoundLockId.singleton` — every two values are equal), which
structurally encodes "at most one round *holding the lock*".  Note
that this bounds the hardware round (publish → SGI → wait), not the
model's pending queues: posting precedes the lock and the catch-up
drain follows it, so a queue can hold several rounds' descriptors —
which is why the drain is window-restricted (SM7.F.3). -/
structure ShootdownRoundLockId where
  deriving DecidableEq, Repr, Inhabited

/-- **WS-SM SM7.A audit**: the round lock is unique — the type has one
value, so a lock-set can never name two distinct round locks. -/
theorem ShootdownRoundLockId.singleton (a b : ShootdownRoundLockId) :
    a = b := rfl

/-- **WS-SM SM7.A**: identifier for core `c`'s pending-shootdown-queue
lock — the "PendingShootdown lock" of plan §3.2 step 2, at per-core
granularity per the WS-SM per-object-fine-locks decision.

Like the scheduler's `RunQueueLockId`, the guarded state is keyed by
`CoreId` rather than `ObjId`, so this is **not** a `LockKind`/`LockId`
(the SM0.I object-lock hierarchy is deliberately closed at ten kinds);
SM7.B.7 (`lockSet_tlbShootdown_correct`) integrates it into the
protocol's cross-domain lock-set the same way `SchedLockId` wraps the
run-queue locks.

**Acquisition order**: strictly ascending `core` (the total order
below), always after the global `ShootdownRoundLockId`.  Under the
module-header round-serialisation contract at most one initiator holds
queue locks at a time, so the total order is defense-in-depth rather
than load-bearing today: it (a) declares the 2PL write footprint of
the round's multi-queue posting under the SM3 discipline, and (b)
future-proofs any post-1.0 relaxation of round serialisation (e.g.
round-identity-tagged acks), where two concurrent initiators posting
to each other's cores WOULD deadlock without it (A holding queue 1
wanting queue 2 against B holding queue 2 wanting queue 1). -/
structure ShootdownQueueLockId where
  core : CoreId
  deriving DecidableEq, Repr

namespace ShootdownQueueLockId

instance : LE ShootdownQueueLockId := ⟨fun a b => a.core.val ≤ b.core.val⟩
instance : LT ShootdownQueueLockId := ⟨fun a b => a.core.val < b.core.val⟩

instance (a b : ShootdownQueueLockId) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.core.val ≤ b.core.val))
instance (a b : ShootdownQueueLockId) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.core.val < b.core.val))

/-- **WS-SM SM7.A**: the queue-lock order is reflexive. -/
theorem le_refl (a : ShootdownQueueLockId) : a ≤ a := Nat.le_refl _

/-- **WS-SM SM7.A**: the queue-lock order is transitive. -/
theorem le_trans {a b c : ShootdownQueueLockId}
    (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := Nat.le_trans h₁ h₂

/-- **WS-SM SM7.A**: the queue-lock order is antisymmetric — distinct
cores' queue locks are strictly ordered, so an ascending acquisition
sequence visits each at most once. -/
theorem le_antisymm {a b : ShootdownQueueLockId}
    (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  cases a with | mk ca =>
  cases b with | mk cb =>
  have hval : ca.val = cb.val := Nat.le_antisymm h₁ h₂
  rw [Fin.ext hval]

/-- **WS-SM SM7.A**: the queue-lock order is total — any two queue
locks are comparable, so the SM7.B.7 multi-target acquisition sequence
can always be sorted ascending. -/
theorem le_total (a b : ShootdownQueueLockId) : a ≤ b ∨ b ≤ a :=
  Nat.le_total a.core.val b.core.val

/-- **WS-SM SM7.A**: distinct queue locks are strictly comparable —
the deadlock-freedom precondition for concurrent initiators (see the
structure docstring). -/
theorem lt_or_gt_of_ne {a b : ShootdownQueueLockId} (h : a ≠ b) :
    a < b ∨ b < a := by
  cases Nat.lt_or_ge a.core.val b.core.val with
  | inl hlt => exact Or.inl hlt
  | inr hge =>
    cases Nat.eq_or_lt_of_le hge with
    | inl heq =>
      exact absurd (le_antisymm (Nat.le_of_eq heq.symm) (Nat.le_of_eq heq)) h
    | inr hlt => exact Or.inr hlt

end ShootdownQueueLockId

end SeLe4n.Kernel.Architecture
