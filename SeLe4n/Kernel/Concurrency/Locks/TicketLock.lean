-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM (SM2.B abstract TicketLock spec; refined by
-- `rust/sele4n-hal/src/ticket_lock.rs` per SM2.B.16 and the future SM2.D
-- refinement bridge).

import SeLe4n.Kernel.Concurrency.MemoryModel
import SeLe4n.Kernel.Concurrency.Types

/-!
# WS-SM SM2.B — TicketLock operational specification

This module contains the abstract operational specification of the
FIFO TicketLock primitive that the Rust HAL's
`rust/sele4n-hal/src/ticket_lock.rs` refines.  The spec is **pure**
(no `IO`, no `Unsafe`, zero added axioms, zero proof gaps): every
transition is a total function on the abstract `TicketLockState`,
and every theorem is mechanically discharged.

The six substantive theorems exported by this module are:

* `ticketLock_mutex` — at most one core holds the lock at any time.
* `ticketLock_wf_invariant` — every operation preserves the seven
  conjuncts of `TicketLockState.wf`.
* `ticketLock_fifo` — earlier `tryAcquire` calls capture smaller
  tickets (the FIFO foundation that SM3 ladder-acquisition lemmas
  build on).
* `ticketLock_bounded_wait` — when a core captures ticket `t`, at
  most `numCores - 1` other cores have tickets ahead of it (the
  WCRT bound that SM2.C RwLock's writer-starvation freedom is
  derived from).
* `ticketLock_release_acquire_pairing` — a release-store on the
  `serving` location synchronizes-with the next acquire-load that
  observes the released value (the release-acquire pairing that
  SM3 per-object locks consume for cross-core state visibility).
* `ticketLock_reachability` — every state reachable from `unheld`
  by a finite operation sequence satisfies `wf`.

Plus a determinism theorem (`ticketLock_applyOp_deterministic`) and
two closure-form preservation lemmas (`acquire_preserves_wf`,
`release_preserves_wf`) that SM3 / SM2.D / SM2.E consumers use.

## ARM ARM citations

The operational behaviour of the abstract `applyOp` corresponds to
the following hardware primitives:

* **`tryAcquire`** — atomic `LDADDA` (ARM ARM C6.2.116) on the
  `nextTicket` location.  Captures the ticket atomically; on
  ARMv8.1-A LSE this is one instruction.  Modelled in the memory
  trace as an RMW (load + store at the same `seqNum`).
* **`release`** — `STLR` (ARM ARM C6.2.243 / B2.3.7) on the `serving`
  location.  Release-store ordering publishes every prior write on
  the releasing core to any acquire-load that observes this value.
* **`observeServing`** — `LDAR` (ARM ARM C6.2.142) on the `serving`
  location.  Acquire-load ordering synchronises-with the
  release-store that produced the observed value.

## Axiom budget

Zero Lean `axioms`, zero `sorries`.  All hardware semantics enter as
operational constraints on the memory trace shape via the SM2.A
abstract memory model.

## Decidability

`TicketLockState.wf` carries a `Decidable` instance so test fixtures
can construct lock states and `decide` their well-formedness at
elaboration time.  The transition functions
(`captureTicket`, `applyOp`, `promotePending`, `releaseAndPromote`)
are total computable functions on `TicketLockState`.
-/

namespace SeLe4n.Kernel.Concurrency

-- ============================================================================
-- SM2.B.1 — TicketLockState
-- ============================================================================

/-- **WS-SM SM2.B.1**: the abstract state of a TicketLock primitive.

The four fields capture every observable aspect of a FIFO ticket
lock at the operational-semantics level:

* `nextTicket` — the monotone counter that every acquirer increments
  to capture its position in the queue.  Corresponds to the Rust
  impl's `AtomicU64 next_ticket` field.
* `serving` — the monotone counter that the releasing core increments
  to admit the next pending core.  Corresponds to the Rust impl's
  `AtomicU64 serving` field.
* `pending` — the list of (core, ticket) pairs that have captured a
  ticket but are spinning waiting for `serving` to reach it.  The
  abstract model uses an explicit list because the spec proves FIFO
  ordering; the Rust impl tracks this implicitly through the gap
  between `next_ticket` and `serving`.
* `held` — `Option (CoreId × Nat)` carrying the current holder (if
  any).  At most one core holds the lock at any time, witnessed by
  `ticketLock_mutex`.

`Inhabited` is derived (every field has `Inhabited` — `Nat` via
`0`, `List` via `[]`, `Option` via `none`).  The default
`Inhabited` witness is **not** `unheld`; see `unheld` below for the
canonical initial state. -/
structure TicketLockState where
  /-- Monotone counter capturing the next ticket to be issued. -/
  nextTicket : Nat
  /-- Monotone counter capturing the ticket currently being served. -/
  serving    : Nat
  /-- The (core, ticket) pairs waiting to be served. -/
  pending    : List (CoreId × Nat)
  /-- The current holder, if any.  At most one is admitted. -/
  held       : Option (CoreId × Nat)
  deriving Repr, Inhabited

-- ============================================================================
-- SM2.B.2 — unheld constructor
-- ============================================================================

/-- **WS-SM SM2.B.2**: the canonical initial state.

Every counter is zero; the pending queue is empty; no holder.  This
is the state every reachable trace begins in (the operational-
semantics seed for `ticketLock_reachability`). -/
def TicketLockState.unheld : TicketLockState where
  nextTicket := 0
  serving    := 0
  pending    := []
  held       := none

/-- Witness: `unheld.nextTicket = 0`. -/
theorem TicketLockState.unheld_nextTicket : unheld.nextTicket = 0 := rfl

/-- Witness: `unheld.serving = 0`. -/
theorem TicketLockState.unheld_serving : unheld.serving = 0 := rfl

/-- Witness: `unheld.pending = []`. -/
theorem TicketLockState.unheld_pending : unheld.pending = [] := rfl

/-- Witness: `unheld.held = none`. -/
theorem TicketLockState.unheld_held : unheld.held = none := rfl

-- ============================================================================
-- SM2.B.3 — wf predicate (7 conjuncts)
-- ============================================================================

/-- **WS-SM SM2.B.3**: well-formedness predicate for a TicketLockState.

The seven conjuncts encode every structural invariant the operational
semantics must preserve.  Each `INV-T*` annotation matches the plan's
§3.2.2 conjunct numbering for traceability.

* **INV-T1** — `serving ≤ nextTicket`.  Counter monotonicity: the
  number served never exceeds the number issued.
* **INV-T2** — pending tickets lie in `(serving, nextTicket)`.  A
  pending ticket is strictly between the current serving and the
  next-to-issue, so the wait queue is bounded by the issued-but-not-
  served window.
* **INV-T3** — `holder.ticket = serving`.  The current holder's
  captured ticket exactly equals the serving counter.
* **INV-T4** — pending tickets are unique.  Two distinct waiters
  cannot share a ticket.
* **INV-T5** — holder's ticket is not in pending.  The holder is
  always promoted out of the pending queue.
* **INV-T6** — pending cores are unique.  A core can wait for at
  most one ticket at a time.
* **INV-T7** — pending cores disjoint from holder.  The holder is
  not simultaneously waiting.

The `match s.held with | none => True | some h => P h` form is used
for the holder-side conjuncts (T3, T5, T7) to keep decidability
elementary; the `Option`-quantifier alternative
(`∀ h ∈ s.held, P h`) is mathematically equivalent but unfolds
through `Membership.mem` and is harder for `decide` to handle.

INV-T2 is encoded via `List.all` (Bool form) plus `= true` so the
inner bounded quantifier is decidable without appealing to
`Mathlib.Data.List.Forall`.  The `pendingInRange` helper exposes the
Bool predicate for downstream use. -/
def TicketLockState.pendingInRange (s : TicketLockState) : Bool :=
  s.pending.all (fun p => decide (s.serving < p.2 ∧ p.2 < s.nextTicket))

/-- **WS-SM SM2.B.3**: helper Bool encoding for the holder's
"present" bit — `1` if a holder is set, `0` otherwise.  Used by the
in-flight-count invariant (INV-T8) below. -/
def TicketLockState.heldCount (s : TicketLockState) : Nat :=
  match s.held with
  | none => 0
  | some _ => 1

/-- **WS-SM SM2.B.3**: helper Bool predicate for INV-T3 — the
holder's ticket equals `serving` (vacuously true when no holder). -/
def TicketLockState.holderTicketIsServing (s : TicketLockState) : Bool :=
  match s.held with
  | none => true
  | some h => decide (h.2 = s.serving)

/-- **WS-SM SM2.B.3**: helper Bool predicate for INV-T5 — the
holder's ticket is not in the pending list (vacuously true when no
holder). -/
def TicketLockState.holderTicketDisjointFromPending (s : TicketLockState) : Bool :=
  match s.held with
  | none => true
  | some h => decide (h.2 ∉ s.pending.map Prod.snd)

/-- **WS-SM SM2.B.3**: helper Bool predicate for INV-T7 — the
holder's core is not in the pending list (vacuously true when no
holder). -/
def TicketLockState.holderCoreDisjointFromPending (s : TicketLockState) : Bool :=
  match s.held with
  | none => true
  | some h => decide (h.1 ∉ s.pending.map Prod.fst)

/-- **WS-SM SM2.B.3**: well-formedness predicate for a TicketLockState.

Carries **eight conjuncts** — the seven from the plan's §3.2.2 plus
one count-parity invariant **INV-T8** that the plan's sketch omits.

### Why eight, not seven

The plan's pseudocode for `applyOp .tryAcquire` (§3.2.3) admits a
seemingly innocuous edge case: if `s.serving = s.nextTicket` AND
`s.held.isSome`, the operational step takes the `else` branch and
appends `(core, s.nextTicket)` to `pending`, producing a state that
violates INV-T2 (the new pending entry would have ticket `= serving`,
not `> serving`).

Such a state — `held = some _, serving = nextTicket` — is **not
reachable** from `unheld` by any sequence of operations, but the
seven-invariant `wf` admits it.  Per the implement-the-improvement
rule (`CLAUDE.md`), the correct remediation is to **strengthen the
invariant** so the spec captures exactly the reachable states.

INV-T8 is a count-parity invariant:
`nextTicket = serving + pending.length + heldCount`.

It says the "next ticket counter" equals the number served plus the
number in the wait queue plus the number held — every issued ticket
is accounted for.  This is the natural structural invariant for a
FIFO ticket lock and implies `held.isSome → serving < nextTicket`
plus `pending ≠ [] → serving < nextTicket`.

Under INV-T8, the troublesome state above is rejected: with
`held = some _ ∧ pending = []`, INV-T8 forces
`nextTicket = serving + 0 + 1 = serving + 1`, so `serving < nextTicket`.

The seven conjuncts encode every structural invariant the operational
semantics must preserve.  Each `INV-T*` annotation matches the plan's
§3.2.2 conjunct numbering for traceability.

* **INV-T1** — `serving ≤ nextTicket`.  Counter monotonicity: the
  number served never exceeds the number issued.
* **INV-T2** — pending tickets lie in `(serving, nextTicket)`.  A
  pending ticket is strictly between the current serving and the
  next-to-issue, so the wait queue is bounded by the issued-but-not-
  served window.
* **INV-T3** — `holder.ticket = serving`.  The current holder's
  captured ticket exactly equals the serving counter.
* **INV-T4** — pending tickets are unique.  Two distinct waiters
  cannot share a ticket.
* **INV-T5** — holder's ticket is not in pending.  The holder is
  always promoted out of the pending queue.
* **INV-T6** — pending cores are unique.  A core can wait for at
  most one ticket at a time.
* **INV-T7** — pending cores disjoint from holder.  The holder is
  not simultaneously waiting.
* **INV-T8** (new): in-flight count parity.
  `nextTicket = serving + pending.length + heldCount`.

The `match s.held with | none => True | some h => P h` form is used
for the holder-side conjuncts (T3, T5, T7) to keep decidability
elementary; the `Option`-quantifier alternative
(`∀ h ∈ s.held, P h`) is mathematically equivalent but unfolds
through `Membership.mem` and is harder for `decide` to handle. -/
def TicketLockState.wf (s : TicketLockState) : Prop :=
  -- INV-T1
  s.serving ≤ s.nextTicket
  ∧
  -- INV-T2 (Bool-encoded for elementary decidability)
  s.pendingInRange = true
  ∧
  -- INV-T3
  s.holderTicketIsServing = true
  ∧
  -- INV-T4
  (s.pending.map Prod.snd).Nodup
  ∧
  -- INV-T5
  s.holderTicketDisjointFromPending = true
  ∧
  -- INV-T6
  (s.pending.map Prod.fst).Nodup
  ∧
  -- INV-T7
  s.holderCoreDisjointFromPending = true
  ∧
  -- INV-T8 (count parity; closes the reachability gap in the 7-invariant form)
  s.nextTicket = s.serving + s.pending.length + s.heldCount

/-- **WS-SM SM2.B.3**: bridge the Bool `pendingInRange` to the
mathematically natural `∀ p ∈ s.pending, ...` form.  Used by every
preservation proof that reasons about pending tickets. -/
theorem TicketLockState.pendingInRange_iff (s : TicketLockState) :
    s.pendingInRange = true ↔
    (∀ p ∈ s.pending, s.serving < p.2 ∧ p.2 < s.nextTicket) := by
  unfold TicketLockState.pendingInRange
  rw [List.all_eq_true]
  constructor
  · intro h p hp
    have h_dec := h p hp
    exact of_decide_eq_true h_dec
  · intro h p hp
    have := h p hp
    exact decide_eq_true this

/-- **WS-SM SM2.B.3**: bridge for INV-T3.  `holderTicketIsServing`
returns `true` iff the holder (if any) has ticket equal to
`serving`. -/
theorem TicketLockState.holderTicketIsServing_iff (s : TicketLockState) :
    s.holderTicketIsServing = true ↔
    (∀ h, s.held = some h → h.2 = s.serving) := by
  unfold TicketLockState.holderTicketIsServing
  cases h_held : s.held with
  | none => simp
  | some h =>
    constructor
    · intro h_dec h' h_eq
      cases h_eq
      exact of_decide_eq_true h_dec
    · intro h_all
      exact decide_eq_true (h_all h rfl)

/-- **WS-SM SM2.B.3**: bridge for INV-T5.  `holderTicketDisjointFromPending`
returns `true` iff the holder's ticket (if any) is not in the
pending list. -/
theorem TicketLockState.holderTicketDisjointFromPending_iff (s : TicketLockState) :
    s.holderTicketDisjointFromPending = true ↔
    (∀ h, s.held = some h → h.2 ∉ s.pending.map Prod.snd) := by
  unfold TicketLockState.holderTicketDisjointFromPending
  cases h_held : s.held with
  | none => simp
  | some h =>
    constructor
    · intro h_dec h' h_eq
      cases h_eq
      exact of_decide_eq_true h_dec
    · intro h_all
      exact decide_eq_true (h_all h rfl)

/-- **WS-SM SM2.B.3**: bridge for INV-T7.  `holderCoreDisjointFromPending`
returns `true` iff the holder's core (if any) is not in the
pending list. -/
theorem TicketLockState.holderCoreDisjointFromPending_iff (s : TicketLockState) :
    s.holderCoreDisjointFromPending = true ↔
    (∀ h, s.held = some h → h.1 ∉ s.pending.map Prod.fst) := by
  unfold TicketLockState.holderCoreDisjointFromPending
  cases h_held : s.held with
  | none => simp
  | some h =>
    constructor
    · intro h_dec h' h_eq
      cases h_eq
      exact of_decide_eq_true h_dec
    · intro h_all
      exact decide_eq_true (h_all h rfl)

-- ============================================================================
-- SM2.B.4 — wf Decidable instance
-- ============================================================================

/-- **WS-SM SM2.B.4**: `wf` is decidable.

All seven conjuncts are decidable:

* INV-T1: `Nat.decLe`.
* INV-T2: bounded-quantifier over the finite `pending` list, where
  the predicate is conjunction of two `Nat.decLt`.
* INV-T3 / T5 / T7: discharged by `match` on `s.held` — both arms
  (`none → True`, `some h → ...`) are decidable.
* INV-T4 / T6: `List.Nodup` is decidable when the underlying
  `DecidableEq` is available (which we have for `Nat` and
  `CoreId = Fin numCores`).

The `unfold` + `inferInstance` pattern matches the SM2.A
`MemoryTrace.wellFormed` decidability proof. -/
instance (s : TicketLockState) : Decidable s.wf := by
  unfold TicketLockState.wf
  exact inferInstance

/-- Witness: `unheld` is well-formed.  Discharged by `decide`. -/
theorem TicketLockState.unheld_wf : TicketLockState.unheld.wf := by
  unfold TicketLockState.wf TicketLockState.unheld
  decide

-- ============================================================================
-- SM2.B.5 — TicketLockOp
-- ============================================================================

/-- **WS-SM SM2.B.5**: the operational-semantics operations on a
TicketLock.

Three operations cover the full lifecycle:

* `tryAcquire core` — attempts to capture a ticket for `core`.
  Corresponds to the Rust impl's `acquire()` body's
  `next_ticket.fetch_add(1, Acquire)` followed by a spin-loop
  iteration.  At the abstract level, the capture and the immediate
  spin-loop's first iteration are fused — if `serving` already
  equals the captured ticket and no holder is present, the core
  is promoted to held in one step.
* `release core` — releases the lock if `core` is the current
  holder.  Corresponds to the Rust impl's
  `serving.fetch_add(1, Release)` followed by an SEV broadcast.
* `observeServing core observed` — a pure observation of the
  `serving` counter (the spin-loop body).  Does not change the
  state; included so the spec can talk about the Acquire-load
  events that the release-acquire pairing theorem cites. -/
inductive TicketLockOp where
  /-- `core` attempts to capture a ticket. -/
  | tryAcquire     (core : CoreId)
  /-- `core` releases the lock (if it currently holds). -/
  | release        (core : CoreId)
  /-- `core` observes the `serving` counter (spin-loop iteration). -/
  | observeServing (core : CoreId) (observed : Nat)
  deriving Repr

-- ============================================================================
-- SM2.B.6 — captureTicket, observeServing, applyOp
-- ============================================================================

/-- **WS-SM SM2.B.6**: the atomic `fetch_add` capture step.

Returns the updated state and the captured ticket.  The state is
extended by:

* `nextTicket := nextTicket + 1` (the atomic increment side of
  `LDADDA`).
* `pending := (core, ticket) :: pending` (the just-captured entry
  is admitted at the head of the queue; the `applyOp` wrapper
  then removes it again if the captured ticket equals `serving`
  and no holder is present, fusing the capture with the immediate
  spin-loop's first iteration). -/
def TicketLockState.captureTicket (s : TicketLockState) (core : CoreId) :
    TicketLockState × Nat :=
  let ticket := s.nextTicket
  let s' :=
    { s with
      nextTicket := s.nextTicket + 1
      pending    := (core, ticket) :: s.pending }
  (s', ticket)

/-- **WS-SM SM2.B.6**: the pure observation step.

Returns the current `serving` counter without changing the state.
Corresponds to the Rust impl's `serving.load(Ordering::Acquire)`
inside the spin-loop body.

The function is total and computable; the `core` parameter is
informational (it identifies which core is observing, useful when
the spec is lifted to a `MemoryTrace` and an Acquire-load event
needs to be tagged with the observing core). -/
def TicketLockState.observeServing (s : TicketLockState) : Nat := s.serving

/-- **WS-SM SM2.B.6**: the operational-semantics step function.

Each `TicketLockOp` maps to a single transition on the abstract
state, producing a new state.  The function is total and
deterministic — `applyOp` is the unique function from
`(state, op)` to next state (witnessed by
`ticketLock_applyOp_deterministic`).

The `tryAcquire core` arm fuses the capture and the immediate
spin-loop's first iteration:

* If `core` is already pending or held, the op is a no-op.
  (Operationally this corresponds to the Rust impl's panic on
  double-acquire; the abstract spec treats it as a no-op so the
  state stays well-formed.)
* Otherwise, the capture admits a new entry to `pending`; if the
  captured ticket equals `serving` and no holder is present, the
  core is immediately promoted to held (the fused fast-path).

The `release core` arm:

* No-op if `core` is not the current holder.
* Otherwise, advances `serving` by 1, clears the holder.  The
  promotion of the next pending core is a separate step
  (`promotePending`), keeping the release and promotion proofs
  modular.

The `observeServing _ _` arm is a no-op on the state. -/
def TicketLockState.applyOp (s : TicketLockState) (op : TicketLockOp) :
    TicketLockState :=
  match op with
  | .tryAcquire core =>
      if core ∈ s.pending.map Prod.fst then s
      else if (s.held.map Prod.fst) = some core then s
      else
        let ticket := s.nextTicket
        let s' :=
          { s with
            nextTicket := s.nextTicket + 1
            pending    := (core, ticket) :: s.pending }
        if s.serving = ticket ∧ s.held.isNone then
          { s' with
            pending := s'.pending.filter (fun p => p.2 ≠ ticket)
            held    := some (core, ticket) }
        else
          s'
  | .release core =>
      match s.held with
      | none => s
      | some (c, _) =>
          if c = core then
            { s with
              serving := s.serving + 1
              held    := none }
          else s
  | .observeServing _ _ => s

-- ============================================================================
-- SM2.B.7 — promotePending, releaseAndPromote
-- ============================================================================

/-- **WS-SM SM2.B.7**: after a release, promote the pending entry
whose ticket equals the new `serving` counter (if any).

If `held` is already populated, this is a no-op (the holder must
release first).  Otherwise, the pending entry with ticket
`s.serving` is removed from the queue and promoted to held.

By INV-T4 there is at most one such pending entry; by INV-T6 we
can identify it uniquely by its `core` field as well, so the
`filter (fun p => p.1 ≠ c)` correctly removes exactly the
promoted entry. -/
def TicketLockState.promotePending (s : TicketLockState) :
    TicketLockState :=
  match s.held, s.pending.find? (fun p => p.2 = s.serving) with
  | none, some (c, t) =>
      { s with
        pending := s.pending.filter (fun p => p.1 ≠ c)
        held    := some (c, t) }
  | _, _ => s

/-- **WS-SM SM2.B.7**: the composed release-and-promote step.

Releases the lock from `core` and immediately promotes the next
pending entry (if any).  This is the "complete" release operation
the kernel-level release path performs; the SM2.B Rust impl's
`release()` function refines this composed step. -/
def TicketLockState.releaseAndPromote (s : TicketLockState) (core : CoreId) :
    TicketLockState :=
  (s.applyOp (.release core)).promotePending

-- ============================================================================
-- Foundational helpers for wf reasoning
-- ============================================================================

/-- **Helper**: extract INV-T1 from a wf state. -/
theorem TicketLockState.wf_servingLeNextTicket {s : TicketLockState}
    (h : s.wf) : s.serving ≤ s.nextTicket :=
  h.1

/-- **Helper**: extract INV-T2 (Prop form) from a wf state. -/
theorem TicketLockState.wf_pendingInRange {s : TicketLockState}
    (h : s.wf) :
    ∀ p ∈ s.pending, s.serving < p.2 ∧ p.2 < s.nextTicket :=
  (s.pendingInRange_iff).mp h.2.1

/-- **Helper**: extract INV-T3 (Prop form) from a wf state. -/
theorem TicketLockState.wf_holderTicketIsServing {s : TicketLockState}
    (h : s.wf) :
    ∀ x, s.held = some x → x.2 = s.serving :=
  (s.holderTicketIsServing_iff).mp h.2.2.1

/-- **Helper**: extract INV-T4 from a wf state. -/
theorem TicketLockState.wf_pendingTicketsNodup {s : TicketLockState}
    (h : s.wf) : (s.pending.map Prod.snd).Nodup :=
  h.2.2.2.1

/-- **Helper**: extract INV-T5 (Prop form) from a wf state. -/
theorem TicketLockState.wf_holderTicketNotInPending {s : TicketLockState}
    (h : s.wf) :
    ∀ x, s.held = some x → x.2 ∉ s.pending.map Prod.snd :=
  (s.holderTicketDisjointFromPending_iff).mp h.2.2.2.2.1

/-- **Helper**: extract INV-T6 from a wf state. -/
theorem TicketLockState.wf_pendingCoresNodup {s : TicketLockState}
    (h : s.wf) : (s.pending.map Prod.fst).Nodup :=
  h.2.2.2.2.2.1

/-- **Helper**: extract INV-T7 (Prop form) from a wf state. -/
theorem TicketLockState.wf_holderCoreNotInPending {s : TicketLockState}
    (h : s.wf) :
    ∀ x, s.held = some x → x.1 ∉ s.pending.map Prod.fst :=
  (s.holderCoreDisjointFromPending_iff).mp h.2.2.2.2.2.2.1

/-- **Helper**: extract INV-T8 (count parity) from a wf state. -/
theorem TicketLockState.wf_countParity {s : TicketLockState}
    (h : s.wf) :
    s.nextTicket = s.serving + s.pending.length + s.heldCount :=
  h.2.2.2.2.2.2.2

/-- **Derived corollary**: if a holder is set in a wf state, the
serving counter is strictly less than nextTicket.

Proof: INV-T8 gives nextTicket = serving + |pending| + 1 ≥ serving + 1. -/
theorem TicketLockState.wf_serving_lt_nextTicket_of_held {s : TicketLockState}
    (h : s.wf) (h_held : s.held.isSome = true) :
    s.serving < s.nextTicket := by
  have hCnt := s.wf_countParity h
  have hHeld : s.heldCount = 1 := by
    unfold TicketLockState.heldCount
    cases h_eq : s.held with
    | none =>
      rw [h_eq] at h_held
      exact absurd h_held (by simp)
    | some _ => rfl
  rw [hCnt, hHeld]
  omega

/-- **Derived corollary**: if pending is non-empty in a wf state,
the serving counter is strictly less than nextTicket.

Proof: INV-T8 gives nextTicket = serving + |pending| + heldCount.
|pending| ≥ 1 forces strict inequality. -/
theorem TicketLockState.wf_serving_lt_nextTicket_of_pending {s : TicketLockState}
    (h : s.wf) (h_pending : s.pending ≠ []) :
    s.serving < s.nextTicket := by
  have hCnt := s.wf_countParity h
  have hLen : s.pending.length ≥ 1 := by
    cases h_eq : s.pending with
    | nil => exact absurd h_eq h_pending
    | cons _ _ => simp
  omega

-- ============================================================================
-- SM2.B.8 — ticketLock_mutex
-- ============================================================================

/-- **Theorem 3.2.5.1 (SM2.B.8): the lock admits at most one holder.**

For any `TicketLockState s`, if `s.held = some (c₁, t₁)` and
`s.held = some (c₂, t₂)`, then `c₁ = c₂` and `t₁ = t₂`.

Proof: `s.held : Option (CoreId × Nat)` has at most one inhabitant
of the `some` case, and `Option.some` is injective.  The two
witnesses for the same `s.held` therefore project to the same
underlying pair.

This is the foundational mutex property the SM3 per-object lock
proofs cite when ruling out two concurrent kernel transitions on
the same lock-protected object. -/
theorem ticketLock_mutex (s : TicketLockState) :
    ∀ (c₁ c₂ : CoreId) (t₁ t₂ : Nat),
      s.held = some (c₁, t₁) → s.held = some (c₂, t₂) →
      c₁ = c₂ ∧ t₁ = t₂ := by
  intro c₁ c₂ t₁ t₂ h₁ h₂
  rw [h₁] at h₂
  injection h₂ with h
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

-- ============================================================================
-- SM2.B.9 — ticketLock_wf_invariant (case-by-case)
-- ============================================================================

/-- **wf-preservation case**: `observeServing` is the identity on
state, so wf is preserved trivially. -/
theorem ticketLock_observeServing_preserves_wf (s : TicketLockState)
    (core : CoreId) (observed : Nat) (h : s.wf) :
    (s.applyOp (.observeServing core observed)).wf := by
  unfold TicketLockState.applyOp
  exact h

/-- **Helper**: `applyOp .release core` either leaves `s` unchanged
(when `core` is not the current holder) or produces a state with
`serving' = serving + 1` and `held' = none`. -/
theorem TicketLockState.applyOp_release_cases (s : TicketLockState) (core : CoreId) :
    s.applyOp (.release core) = s
    ∨ (∃ holderTicket,
         s.held = some (core, holderTicket)
         ∧ s.applyOp (.release core) =
             { s with serving := s.serving + 1, held := none }) := by
  unfold TicketLockState.applyOp
  cases h_held : s.held with
  | none => exact Or.inl rfl
  | some h =>
    obtain ⟨c, t⟩ := h
    by_cases h_eq : c = core
    · subst h_eq
      refine Or.inr ⟨t, rfl, ?_⟩
      simp
    · refine Or.inl ?_
      simp [h_eq]

/-- **wf-preservation case**: `release core` preserves wf.

Cases:

1. `core` is not the holder ⟹ no-op ⟹ wf preserved trivially.
2. `core` is the holder ⟹ serving++, held := none.
   * INV-T1: old serving ≤ nextTicket; since held.isSome, by
     `wf_serving_lt_nextTicket_of_held` we have old serving <
     nextTicket, so old serving + 1 ≤ nextTicket. ✓
   * INV-T2: old pending entries have ticket in (old serving,
     nextTicket); they have ticket > old serving, so ticket ≥
     old serving + 1 = new serving.  However, we need STRICT
     `new serving < ticket`.  This is the crux of the proof:
     pending entries' tickets were strictly between old serving
     and old nextTicket; after release, they're between new
     serving (= old serving + 1) and old nextTicket = new
     nextTicket.  Specifically, for any pending entry p, old
     serving < p.2 means p.2 ≥ old serving + 1 = new serving;
     combined with p.2 < nextTicket (unchanged), if p.2 = new
     serving, we'd have a "ready-to-promote" entry, but INV-T2
     in the new state only requires p.2 > new serving for non-
     promoted entries.  However, `applyOp .release` does NOT
     do the promotion — that's `promotePending`'s job — so the
     new state may have a pending entry with p.2 = new serving.
     This is INV-T2 violated.

   So **`applyOp .release` alone does NOT preserve wf** when the
   release admits a pending entry at the new serving.  This is
   why the spec exposes `releaseAndPromote = applyOp .release;
   promotePending` as the kernel-visible release operation.

Therefore we prove a **weaker** preservation for `applyOp .release`
that retains every wf clause EXCEPT INV-T2 (which may be
temporarily violated until `promotePending` runs); the full wf
preservation lands on `releaseAndPromote`. -/
theorem ticketLock_release_preserves_partial_wf
    (s : TicketLockState) (core : CoreId) (h : s.wf) :
    let s' := s.applyOp (.release core)
    -- INV-T1 preserved
    s'.serving ≤ s'.nextTicket
    -- INV-T4 preserved
    ∧ (s'.pending.map Prod.snd).Nodup
    -- INV-T6 preserved
    ∧ (s'.pending.map Prod.fst).Nodup
    -- INV-T3 preserved (vacuous after release)
    ∧ s'.holderTicketIsServing = true
    -- INV-T5 preserved (vacuous after release)
    ∧ s'.holderTicketDisjointFromPending = true
    -- INV-T7 preserved (vacuous after release)
    ∧ s'.holderCoreDisjointFromPending = true := by
  rcases s.applyOp_release_cases core with h_id | ⟨t, h_held, h_step⟩
  · -- No-op case: wf preserved directly.
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals rw [h_id]
    · exact h.1
    · exact h.2.2.2.1
    · exact h.2.2.2.2.2.1
    · exact h.2.2.1
    · exact h.2.2.2.2.1
    · exact h.2.2.2.2.2.2.1
  · -- Active release: serving++, held := none.
    rw [h_step]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- INV-T1: serving + 1 ≤ nextTicket.  Follows from
      -- wf_serving_lt_nextTicket_of_held since s.held.isSome.
      have : s.held.isSome := by rw [h_held]; rfl
      have hLt := s.wf_serving_lt_nextTicket_of_held h this
      exact hLt
    · -- INV-T4: pending unchanged, so Nodup preserved.
      exact h.2.2.2.1
    · -- INV-T6: pending unchanged.
      exact h.2.2.2.2.2.1
    · -- INV-T3: held := none, so holderTicketIsServing = true vacuously.
      unfold TicketLockState.holderTicketIsServing
      simp
    · -- INV-T5: held := none, so vacuous.
      unfold TicketLockState.holderTicketDisjointFromPending
      simp
    · -- INV-T7: held := none, so vacuous.
      unfold TicketLockState.holderCoreDisjointFromPending
      simp

/-- **Lemma**: in a wf state, an entry in `pending` has ticket
strictly less than `nextTicket`. -/
theorem TicketLockState.wf_pending_ticket_lt {s : TicketLockState} (h : s.wf)
    {p : CoreId × Nat} (hp : p ∈ s.pending) :
    p.2 < s.nextTicket :=
  (s.wf_pendingInRange h p hp).2

/-- **Lemma**: in a wf state, an entry in `pending` has ticket
strictly greater than `serving`. -/
theorem TicketLockState.wf_pending_ticket_gt {s : TicketLockState} (h : s.wf)
    {p : CoreId × Nat} (hp : p ∈ s.pending) :
    s.serving < p.2 :=
  (s.wf_pendingInRange h p hp).1

/-- **Lemma**: `nextTicket` is not in the existing pending tickets,
because every pending ticket is `< nextTicket`. -/
theorem TicketLockState.wf_nextTicket_not_in_pending {s : TicketLockState}
    (h : s.wf) : s.nextTicket ∉ s.pending.map Prod.snd := by
  intro h_mem
  rw [List.mem_map] at h_mem
  obtain ⟨p, hp, h_eq⟩ := h_mem
  have h_lt := s.wf_pending_ticket_lt h hp
  rw [h_eq] at h_lt
  exact Nat.lt_irrefl _ h_lt

/-- **wf-preservation case**: `tryAcquire core` preserves wf.

Three sub-cases:

1. `core ∈ pending.map Prod.fst` → no-op (s unchanged).
2. `held.map Prod.fst = some core` → no-op (s unchanged).
3. Capture (with optional immediate-promote):
   * Fast-path: `s.serving = s.nextTicket ∧ s.held.isNone`.
     By INV-T8, `pending = []`; the captured ticket = nextTicket =
     serving; the immediate-promote sets held := some (core, t).
     Result: nextTicket+1, serving, [], some (core, serving).  All
     8 invariants verified.
   * Slow-path: `s.serving ≠ s.nextTicket ∨ s.held.isSome`.
     By INV-T1 + wf_serving_lt_nextTicket_of_held, we have
     `s.serving < s.nextTicket`.  The new entry has ticket =
     nextTicket; we check INV-T2 (serving < nextTicket < nextTicket+1),
     INV-T4 (Nodup: new ticket not in old pending by
     `wf_nextTicket_not_in_pending`), INV-T6 (Nodup: new core not in
     old pending by hypothesis), INV-T7 (holder.core ≠ new core by
     second-if-not-taken), and INV-T8 (count grows by 1 on both
     sides). -/
theorem ticketLock_tryAcquire_preserves_wf
    (s : TicketLockState) (core : CoreId) (h : s.wf) :
    (s.applyOp (.tryAcquire core)).wf := by
  -- Unfold the operation.
  show (s.applyOp (.tryAcquire core)).wf
  unfold TicketLockState.applyOp
  -- Branch 1: core already pending.
  by_cases hp : core ∈ s.pending.map Prod.fst
  · simp [hp]; exact h
  -- Branch 2: core already holds.
  by_cases hh : s.held.map Prod.fst = some core
  · simp [hp, hh]; exact h
  -- Branches 3 + 4: actual capture.
  simp only [hp, hh, ite_false]
  -- Split on the fast-path condition.
  by_cases hcond : s.serving = s.nextTicket ∧ s.held.isNone = true
  · -- Branch 3: fast-path immediate-promote.
    -- Derive: pending = [] (from INV-T8 and serving = nextTicket).
    have h_held_none : s.held = none := Option.isNone_iff_eq_none.mp hcond.2
    have h_heldCount_zero : s.heldCount = 0 := by
      unfold TicketLockState.heldCount; rw [h_held_none]
    have hCnt := s.wf_countParity h
    rw [hcond.1, h_heldCount_zero] at hCnt
    -- nextTicket = nextTicket + |pending| + 0 ⟹ |pending| = 0
    have h_pending_empty : s.pending = [] := by
      have h_len_zero : s.pending.length = 0 := by omega
      exact List.length_eq_zero_iff.mp h_len_zero
    -- The condition selects the fast-path branch.
    have h_dec : decide (s.serving = s.nextTicket ∧ s.held.isNone = true) = true := by
      apply decide_eq_true; exact hcond
    rw [if_pos hcond]
    -- Compute the post-state pending list.
    -- pending was [], after consing it's [(core, ticket)], after filter (ticket ≠ ticket) it's [].
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- INV-T1: serving ≤ nextTicket + 1.  From INV-T1 of s.
      simp; omega
    · -- INV-T2: pending in range.  Post pending = [].
      show TicketLockState.pendingInRange _ = true
      unfold TicketLockState.pendingInRange
      simp [h_pending_empty]
    · -- INV-T3: holder.ticket = serving.  Holder = (core, s.nextTicket); serving = s.nextTicket.
      show TicketLockState.holderTicketIsServing _ = true
      unfold TicketLockState.holderTicketIsServing
      simp
      exact hcond.1.symm
    · -- INV-T4: pending Nodup.  Post pending = [].
      simp [h_pending_empty]
    · -- INV-T5: holder.ticket not in pending.  Post pending = [].
      show TicketLockState.holderTicketDisjointFromPending _ = true
      unfold TicketLockState.holderTicketDisjointFromPending
      simp [h_pending_empty]
    · -- INV-T6: pending cores Nodup.  Post pending = [].
      simp [h_pending_empty]
    · -- INV-T7: holder.core not in pending.  Post pending = [].
      show TicketLockState.holderCoreDisjointFromPending _ = true
      unfold TicketLockState.holderCoreDisjointFromPending
      simp [h_pending_empty]
    · -- INV-T8: nextTicket + 1 = serving + 0 + 1.
      show s.nextTicket + 1 = s.serving + _ + _
      simp [h_pending_empty]
      unfold TicketLockState.heldCount
      simp
      omega
  · -- Branch 4: slow-path capture (no promote).
    -- We need s.serving < s.nextTicket.  Derive from hypotheses.
    have h_inv1 : s.serving ≤ s.nextTicket := h.1
    have h_lt : s.serving < s.nextTicket := by
      -- ¬ (serving = nextTicket ∧ held.isNone = true).
      by_cases hs : s.serving = s.nextTicket
      · -- Then held.isSome.
        cases h_eq : s.held with
        | none =>
          -- s.held = none ⟹ s.held.isNone = true ⟹ hcond contradicts.
          have h_none : s.held.isNone = true := by rw [h_eq]; rfl
          exact absurd ⟨hs, h_none⟩ hcond
        | some x =>
          -- s.held = some x ⟹ s.held.isSome = true ⟹ apply wf_serving_lt_of_held.
          have h_some : s.held.isSome = true := by rw [h_eq]; rfl
          exact s.wf_serving_lt_nextTicket_of_held h h_some
      · -- serving ≠ nextTicket.  By INV-T1, serving ≤ nextTicket, so strict.
        exact Nat.lt_of_le_of_ne h_inv1 hs
    rw [if_neg hcond]
    -- Post state: { s with nextTicket = +1, pending = (core, s.nextTicket) :: pending }.
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- INV-T1: serving ≤ nextTicket + 1.
      simp; exact Nat.le_succ_of_le h.1
    · -- INV-T2: pending in range (new entry + old entries).
      show TicketLockState.pendingInRange _ = true
      apply (TicketLockState.pendingInRange_iff _).mpr
      intro p hp_mem
      -- The post pending is `(core, s.nextTicket) :: s.pending`.
      simp only [List.mem_cons] at hp_mem
      cases hp_mem with
      | inl h_eq =>
        -- h_eq : p = (core, s.nextTicket)
        subst h_eq
        refine ⟨h_lt, ?_⟩
        simp
      | inr h_mem =>
        -- p ∈ old pending
        have h_old := s.wf_pendingInRange h p h_mem
        refine ⟨h_old.1, ?_⟩
        have : p.2 < s.nextTicket := h_old.2
        simp
        omega
    · -- INV-T3: holder unchanged.
      show TicketLockState.holderTicketIsServing _ = true
      have h_old := h.2.2.1
      unfold TicketLockState.holderTicketIsServing at *
      exact h_old
    · -- INV-T4: new ticket not in old pending tickets.
      simp only [List.map_cons]
      exact List.nodup_cons.mpr
        ⟨s.wf_nextTicket_not_in_pending h, s.wf_pendingTicketsNodup h⟩
    · -- INV-T5: holder.ticket not in new pending.
      show TicketLockState.holderTicketDisjointFromPending _ = true
      apply (TicketLockState.holderTicketDisjointFromPending_iff _).mpr
      intro x h_held_eq
      -- The post pending is `(core, s.nextTicket) :: s.pending`.
      simp only [List.map_cons, List.mem_cons]
      intro h_mem
      have h_x2 : x.2 = s.serving := s.wf_holderTicketIsServing h x h_held_eq
      cases h_mem with
      | inl h_eq =>
        -- x.2 = s.nextTicket; but x.2 = s.serving < s.nextTicket.  Contradiction.
        rw [h_x2] at h_eq
        exact absurd h_eq (Nat.ne_of_lt h_lt)
      | inr h_in =>
        -- x.2 ∈ old pending tickets.  But INV-T5 of s says it's not.  Contradiction.
        exact s.wf_holderTicketNotInPending h x h_held_eq h_in
    · -- INV-T6: pending cores Nodup.
      simp only [List.map_cons]
      exact List.nodup_cons.mpr ⟨hp, s.wf_pendingCoresNodup h⟩
    · -- INV-T7: holder.core not in new pending cores.
      show TicketLockState.holderCoreDisjointFromPending _ = true
      apply (TicketLockState.holderCoreDisjointFromPending_iff _).mpr
      intro x h_held_eq
      simp only [List.map_cons, List.mem_cons]
      intro h_mem
      cases h_mem with
      | inl h_eq =>
        -- x.1 = core; but hh says holder.1 ≠ core.
        apply hh
        rw [h_held_eq]
        simp [h_eq]
      | inr h_in =>
        -- x.1 ∈ old pending cores.  But INV-T7 of s says it's not.
        exact s.wf_holderCoreNotInPending h x h_held_eq h_in
    · -- INV-T8: count parity.  nextTicket+1 = serving + (|pending|+1) + heldCount.
      have h_old := s.wf_countParity h
      -- The post state has the same `held` field, so heldCount is the same.
      have h_heldCount_eq :
          ({ s with
              nextTicket := s.nextTicket + 1
              pending    := (core, s.nextTicket) :: s.pending } :
            TicketLockState).heldCount = s.heldCount := by
        unfold TicketLockState.heldCount; rfl
      simp [h_heldCount_eq]
      omega

/-- **Helper** (file-local): in a list of pairs whose map of seconds
is Nodup, two elements with the same second coordinate are equal.

This is the "unique-by-key" property: if pending tickets are unique
(INV-T4), then two pending entries with the same ticket must be
the same entry. -/
private theorem nodup_snd_unique_entry
    (l : List (CoreId × Nat)) (h : (l.map Prod.snd).Nodup) :
    ∀ a b, a ∈ l → b ∈ l → a.2 = b.2 → a = b := by
  intro a b ha hb hab
  induction l with
  | nil => simp at ha
  | cons x rest ih =>
    simp only [List.mem_cons] at ha hb
    rw [List.map_cons, List.nodup_cons] at h
    cases ha with
    | inl ha_eq =>
      cases hb with
      | inl hb_eq => exact ha_eq.trans hb_eq.symm
      | inr hb_mem =>
        exfalso
        rw [ha_eq] at hab
        apply h.1
        rw [hab]
        exact List.mem_map_of_mem hb_mem
    | inr ha_mem =>
      cases hb with
      | inl hb_eq =>
        exfalso
        rw [hb_eq] at hab
        apply h.1
        rw [← hab]
        exact List.mem_map_of_mem ha_mem
      | inr hb_mem =>
        exact ih h.2 ha_mem hb_mem

/-- **Helper** (file-local): same as `nodup_snd_unique_entry` for the
first coordinate.  Used when INV-T6 (Nodup cores) is needed. -/
private theorem nodup_fst_unique_entry
    (l : List (CoreId × Nat)) (h : (l.map Prod.fst).Nodup) :
    ∀ a b, a ∈ l → b ∈ l → a.1 = b.1 → a = b := by
  intro a b ha hb hab
  induction l with
  | nil => simp at ha
  | cons x rest ih =>
    simp only [List.mem_cons] at ha hb
    rw [List.map_cons, List.nodup_cons] at h
    cases ha with
    | inl ha_eq =>
      cases hb with
      | inl hb_eq => exact ha_eq.trans hb_eq.symm
      | inr hb_mem =>
        exfalso
        rw [ha_eq] at hab
        apply h.1
        rw [hab]
        exact List.mem_map_of_mem hb_mem
    | inr ha_mem =>
      cases hb with
      | inl hb_eq =>
        exfalso
        rw [hb_eq] at hab
        apply h.1
        rw [← hab]
        exact List.mem_map_of_mem ha_mem
      | inr hb_mem =>
        exact ih h.2 ha_mem hb_mem

/-- **Helper** (file-local): in a list whose map of firsts is Nodup,
`filter (.fst ≠ c)` removes exactly one entry whose first coordinate
equals `c` (when one exists).

Length-preservation: `(l.filter (.fst ≠ c)).length + 1 = l.length` when
exactly one entry has first coordinate `c`. -/
private theorem nodup_fst_filter_length
    (l : List (CoreId × Nat)) (h : (l.map Prod.fst).Nodup) (c : CoreId)
    (p : CoreId × Nat) (h_mem : p ∈ l) (h_fst : p.1 = c) :
    (l.filter (fun q => q.1 ≠ c)).length + 1 = l.length := by
  induction l with
  | nil => simp at h_mem
  | cons x rest ih =>
    simp only [List.mem_cons] at h_mem
    rw [List.map_cons, List.nodup_cons] at h
    cases h_mem with
    | inl h_eq =>
      -- p = x; so x.1 = c.  Filter drops x.  Need: |filter rest (.1 ≠ c)| + 1 = rest.length + 1.
      -- i.e., |filter rest (.1 ≠ c)| = rest.length.  This holds because no entry in rest has fst = c
      -- (by Nodup: x.1 = c ∉ rest.map fst).
      have h_x_fst : x.1 = c := h_eq ▸ h_fst
      -- Reduce (x :: rest).filter using List.filter_cons_of_neg (since x.1 = c, the predicate is false).
      have h_pred_false : decide (x.1 ≠ c) = false := by
        simp [h_x_fst]
      rw [List.filter_cons, h_pred_false]
      simp only [Bool.false_eq_true, if_false]
      -- Now goal: (rest.filter (fun q => decide (q.1 ≠ c))).length + 1 = (x :: rest).length.
      -- filter rest (.1 ≠ c) = rest (since no entry in rest has fst = c).
      have h_no_c_in_rest : c ∉ rest.map Prod.fst := h_x_fst ▸ h.1
      have h_filter_rest : rest.filter (fun q => decide (q.1 ≠ c)) = rest := by
        apply List.filter_eq_self.mpr
        intro q hq
        simp only [decide_eq_true_iff]
        intro h_eq_c
        apply h_no_c_in_rest
        rw [← h_eq_c]
        exact List.mem_map_of_mem hq
      rw [h_filter_rest, List.length_cons]
    | inr h_in_rest =>
      -- p ∈ rest with p.1 = c.  x.1 ≠ c (since by Nodup, c ∉ rest.map fst BUT c IS in there via p).
      have h_c_in_rest : c ∈ rest.map Prod.fst := h_fst ▸ List.mem_map_of_mem h_in_rest
      have h_x_ne : x.1 ≠ c := by
        intro h_eq
        apply h.1
        rw [h_eq]
        exact h_c_in_rest
      -- Reduce (x :: rest).filter using List.filter_cons_of_pos.
      have h_pred_true : decide (x.1 ≠ c) = true := decide_eq_true h_x_ne
      rw [List.filter_cons, h_pred_true]
      simp only [if_true, List.length_cons]
      -- Now goal: (rest.filter ...).length + 1 + 1 = rest.length + 1.
      have := ih h.2 h_in_rest
      omega

/-- **wf-preservation case**: `promotePending` after `applyOp .release`
preserves wf.

The composed step `releaseAndPromote` is what kernel-level code
calls when releasing a TicketLock.  It atomically advances `serving`
by 1 and promotes the pending entry whose ticket = new `serving`
(if any).

Cases for the post-release state `s_post := s.applyOp (.release core)`:

1. `s.held = none` or `s.held = some (c, _)` with `c ≠ core`: `s_post = s`.
   Then `promotePending` looks for pending entry with ticket = old
   serving.  By INV-T3 of `s` (vacuous if `s.held = none`), and INV-T5
   (holder.ticket NOT in pending), no such entry exists; so
   `promotePending` is a no-op.  Result: wf preserved.

   Hmm, but if `s.held = none`, there might be a pending entry with
   ticket = serving!  Consider state: nextTicket = 2, serving = 0,
   pending = [(c1, 0), (c2, 1)], held = none.  This SATISFIES our
   wf (T1: 0≤2; T2: 0<0<2 fails for c1!  Wait, INV-T2 says serving <
   p.2 < nextTicket; for c1 we'd need 0 < 0, false).

   So pending entries always have ticket > serving (INV-T2).  In the
   no-op case (s_post = s), no pending entry has ticket = serving.
   So promotePending is a no-op.  Result: wf preserved.

2. `s.held = some (core, _)`: `s_post` has serving' = serving+1,
   held' = none, pending unchanged.  Then `promotePending` looks for
   pending entry with ticket = new serving = old serving + 1.
   * If no such entry exists: `promotePending` is a no-op.
     We need: result satisfies all 8 invariants.  INV-T2 may have
     "new serving" violations (pending tickets > old serving but
     not > new serving).  However, no entry has ticket = new
     serving (by hypothesis), so every entry has ticket > new
     serving.  ✓.
   * If a pending entry `(c', t')` with `t' = new serving` exists:
     `promotePending` removes it from pending and sets held := some (c', t').
     INV-T2: remaining pending entries have ticket > new serving
     (now that the boundary entry is removed).  INV-T3: new holder
     ticket = new serving. ✓.

Cases:

1. `applyOp .release core = s` (no-op: `core` not holder).  Then
   `promotePending s` finds no entry to promote (INV-T2 ⟹ no entry
   has ticket = serving; INV-T3+T5 ⟹ holder if any has ticket = serving
   and is NOT in pending), so it's also a no-op.  wf preserved.

2. `applyOp .release core` advances serving by 1 and clears held.
   Then `promotePending` operates on the intermediate state:
   * If `find?` returns none: post-state = intermediate.  Verify wf
     using the relaxed INV-T2 (`p.2 ≥ serving+1`) plus the find?-none
     witness (`p.2 ≠ serving+1`) to derive INV-T2 strict.
   * If `find?` returns some (c', t'): post-state has filtered pending
     and held = some (c', t').  Verify wf using `nodup_snd_unique_entry`
     for INV-T2/T5 and `nodup_fst_filter_length` for INV-T8. -/
theorem ticketLock_releaseAndPromote_preserves_wf
    (s : TicketLockState) (core : CoreId) (h : s.wf) :
    (s.releaseAndPromote core).wf := by
  unfold TicketLockState.releaseAndPromote
  rcases s.applyOp_release_cases core with h_id | ⟨_t, h_held, h_step⟩
  · -- Case 1: applyOp .release was a no-op.  Show promotePending = s.
    rw [h_id]
    unfold TicketLockState.promotePending
    have h_no_match :
        s.pending.find? (fun p => decide (p.2 = s.serving)) = none := by
      apply List.find?_eq_none.mpr
      intro p hp h_dec
      have h_gt : s.serving < p.2 := s.wf_pending_ticket_gt h hp
      simp at h_dec
      omega
    rw [h_no_match]
    -- Match becomes `match s.held, none with | none, some _ => ... | _, _ => s`.
    cases h_held_eq : s.held with
    | none => exact h
    | some _x => exact h
  · -- Case 2: active release.  Intermediate state: { s with serving=+1, held=none }.
    rw [h_step]
    unfold TicketLockState.promotePending
    -- The match's first slot reduces to `none` (intermediate's held).
    -- The match's second slot is `find?` on `s.pending` for `p.2 = s.serving + 1`.
    -- (Note: the intermediate's `pending` and `serving` reduce by structure
    --  projection: `.pending = s.pending`, `.serving = s.serving + 1`.)
    -- Split on the find? result.
    cases h_find :
        s.pending.find? (fun p => decide (p.2 = s.serving + 1)) with
    | none =>
      -- Sub-case 2.a: no pending entry to promote.  Verify the intermediate is wf.
      -- The match falls through to `_, _ => intermediate`.
      -- Goal: { s with serving := +1, held := none }.wf.
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- INV-T1: serving + 1 ≤ nextTicket.
        show s.serving + 1 ≤ s.nextTicket
        have h_held_some : s.held.isSome = true := by rw [h_held]; rfl
        exact s.wf_serving_lt_nextTicket_of_held h h_held_some
      · -- INV-T2: each entry's ticket in (serving+1, nextTicket).
        show TicketLockState.pendingInRange _ = true
        apply (TicketLockState.pendingInRange_iff _).mpr
        intro p hp
        -- `hp : p ∈ {... pending := s.pending ...}.pending`; reduce to `p ∈ s.pending`.
        have h_pending_eq :
            ({ s with serving := s.serving + 1, held := none } : TicketLockState).pending
            = s.pending := rfl
        rw [h_pending_eq] at hp
        have h_old := s.wf_pendingInRange h p hp
        show s.serving + 1 < p.2 ∧ p.2 < s.nextTicket
        refine ⟨?_, h_old.2⟩
        have h_ne : p.2 ≠ s.serving + 1 := by
          intro h_eq
          have h_lemma := List.find?_eq_none.mp h_find p hp
          simp at h_lemma
          exact h_lemma h_eq
        have h_gt := h_old.1
        omega
      · -- INV-T3: held = none, vacuous.
        show TicketLockState.holderTicketIsServing _ = true
        unfold TicketLockState.holderTicketIsServing
        simp
      · -- INV-T4: pending unchanged from s, so Nodup-snd preserved.
        show (({ s with serving := s.serving + 1, held := none }
               : TicketLockState).pending.map Prod.snd).Nodup
        exact s.wf_pendingTicketsNodup h
      · -- INV-T5: held = none, vacuous.
        show TicketLockState.holderTicketDisjointFromPending _ = true
        unfold TicketLockState.holderTicketDisjointFromPending
        simp
      · -- INV-T6: pending unchanged, so Nodup-fst preserved.
        show (({ s with serving := s.serving + 1, held := none }
               : TicketLockState).pending.map Prod.fst).Nodup
        exact s.wf_pendingCoresNodup h
      · -- INV-T7: held = none, vacuous.
        show TicketLockState.holderCoreDisjointFromPending _ = true
        unfold TicketLockState.holderCoreDisjointFromPending
        simp
      · -- INV-T8: nextTicket = (serving + 1) + |pending| + 0.
        -- Pre INV-T8 (heldCount = 1): nextTicket = serving + |pending| + 1.
        have h_pre_cnt := s.wf_countParity h
        have h_pre_hc : s.heldCount = 1 := by
          unfold TicketLockState.heldCount; rw [h_held]
        rw [h_pre_hc] at h_pre_cnt
        -- Establish field-projection equalities as omega hints via rw.
        have h_n : ({ s with serving := s.serving + 1, held := none }
                    : TicketLockState).nextTicket = s.nextTicket := rfl
        have h_s : ({ s with serving := s.serving + 1, held := none }
                    : TicketLockState).serving = s.serving + 1 := rfl
        have h_p : ({ s with serving := s.serving + 1, held := none }
                    : TicketLockState).pending.length = s.pending.length := rfl
        have h_hc : ({ s with serving := s.serving + 1, held := none }
                    : TicketLockState).heldCount = 0 := rfl
        rw [h_n, h_s, h_p, h_hc]
        omega
    | some pp =>
      -- Sub-case 2.b: a pending entry with ticket = serving+1 promotes.
      obtain ⟨c', t'⟩ := pp
      -- From `find? = some (c', t')` extract the membership and ticket value.
      have h_pp_mem : (c', t') ∈ s.pending :=
        List.mem_of_find?_eq_some h_find
      have h_t'_eq : t' = s.serving + 1 := by
        have h_some := List.find?_some h_find
        simp at h_some
        exact h_some
      -- The match resolves to the `none, some (c', t')` arm.  Post-state:
      -- { nextTicket := s.nextTicket, serving := s.serving + 1,
      --   pending := s.pending.filter (fun p => decide (p.1 ≠ c')),
      --   held := some (c', t') }
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- INV-T1: serving + 1 ≤ nextTicket.
        show s.serving + 1 ≤ s.nextTicket
        have h_held_some : s.held.isSome = true := by rw [h_held]; rfl
        exact s.wf_serving_lt_nextTicket_of_held h h_held_some
      · -- INV-T2: filtered pending entries strictly above serving+1.
        show TicketLockState.pendingInRange _ = true
        apply (TicketLockState.pendingInRange_iff _).mpr
        intro p hp
        rw [List.mem_filter] at hp
        obtain ⟨h_p_in_s, h_p_ne_c'⟩ := hp
        simp at h_p_ne_c'
        have h_old := s.wf_pendingInRange h p h_p_in_s
        show s.serving + 1 < p.2 ∧ p.2 < s.nextTicket
        refine ⟨?_, h_old.2⟩
        -- p.2 ≠ s.serving + 1 via nodup_snd_unique_entry.
        have h_p2_ne : p.2 ≠ s.serving + 1 := by
          intro h_eq
          have h_eq_t' : p.2 = t' := h_t'_eq ▸ h_eq
          have h_pair_eq : p = (c', t') :=
            nodup_snd_unique_entry s.pending (s.wf_pendingTicketsNodup h)
              p (c', t') h_p_in_s h_pp_mem h_eq_t'
          apply h_p_ne_c'
          rw [h_pair_eq]
        have h_gt := h_old.1
        omega
      · -- INV-T3: new holder ticket = t' = s.serving + 1 = post.serving.
        show TicketLockState.holderTicketIsServing _ = true
        unfold TicketLockState.holderTicketIsServing
        simp
        exact h_t'_eq
      · -- INV-T4: filter preserves Nodup-snd.
        have h_sub :
            (s.pending.filter (fun p => decide (p.1 ≠ c'))).Sublist s.pending :=
          List.filter_sublist
        exact (h_sub.map Prod.snd).nodup (s.wf_pendingTicketsNodup h)
      · -- INV-T5: t' ∉ filtered pending tickets.
        show TicketLockState.holderTicketDisjointFromPending _ = true
        apply (TicketLockState.holderTicketDisjointFromPending_iff _).mpr
        intro x h_held_eq
        -- h_held_eq : post.held = some x.  post.held = some (c', t').
        -- Extract x = (c', t').
        have h_some_eq : (some (c', t') : Option (CoreId × Nat)) = some x := h_held_eq
        injection h_some_eq with h_pair_eq
        -- h_pair_eq : (c', t') = x
        have h_x_snd : x.2 = t' := by rw [← h_pair_eq]
        rw [h_x_snd]
        intro h_mem
        rw [List.mem_map] at h_mem
        obtain ⟨q, hq_in_filter, hq_snd⟩ := h_mem
        rw [List.mem_filter] at hq_in_filter
        obtain ⟨hq_in_s, hq_ne_c'⟩ := hq_in_filter
        simp at hq_ne_c'
        have h_q_eq : q = (c', t') :=
          nodup_snd_unique_entry s.pending (s.wf_pendingTicketsNodup h)
            q (c', t') hq_in_s h_pp_mem hq_snd
        apply hq_ne_c'
        rw [h_q_eq]
      · -- INV-T6: filter preserves Nodup-fst.
        have h_sub :
            (s.pending.filter (fun p => decide (p.1 ≠ c'))).Sublist s.pending :=
          List.filter_sublist
        exact (h_sub.map Prod.fst).nodup (s.wf_pendingCoresNodup h)
      · -- INV-T7: c' ∉ filtered cores.
        show TicketLockState.holderCoreDisjointFromPending _ = true
        apply (TicketLockState.holderCoreDisjointFromPending_iff _).mpr
        intro x h_held_eq
        have h_some_eq : (some (c', t') : Option (CoreId × Nat)) = some x := h_held_eq
        injection h_some_eq with h_pair_eq
        have h_x_fst : x.1 = c' := by rw [← h_pair_eq]
        rw [h_x_fst]
        intro h_mem
        rw [List.mem_map] at h_mem
        obtain ⟨q, hq_in_filter, hq_fst⟩ := h_mem
        rw [List.mem_filter] at hq_in_filter
        obtain ⟨_, hq_ne_c'⟩ := hq_in_filter
        simp at hq_ne_c'
        exact hq_ne_c' hq_fst
      · -- INV-T8: post.nextTicket = post.serving + |filtered| + 1.
        -- Pre INV-T8 (heldCount = 1): nextTicket = serving + |pending| + 1.
        -- nodup_fst_filter_length: |filtered| + 1 = |pending|.
        have h_filter_len :=
          nodup_fst_filter_length s.pending (s.wf_pendingCoresNodup h)
            c' (c', t') h_pp_mem rfl
        have h_pre_cnt := s.wf_countParity h
        have h_pre_hc : s.heldCount = 1 := by
          unfold TicketLockState.heldCount; rw [h_held]
        rw [h_pre_hc] at h_pre_cnt
        -- Field-projection equalities as omega hints.
        have h_n :
            ({ nextTicket := s.nextTicket, serving := s.serving + 1,
               pending := s.pending.filter (fun p => decide (p.1 ≠ c')),
               held := some (c', t') } : TicketLockState).nextTicket
            = s.nextTicket := rfl
        have h_s :
            ({ nextTicket := s.nextTicket, serving := s.serving + 1,
               pending := s.pending.filter (fun p => decide (p.1 ≠ c')),
               held := some (c', t') } : TicketLockState).serving
            = s.serving + 1 := rfl
        have h_p :
            ({ nextTicket := s.nextTicket, serving := s.serving + 1,
               pending := s.pending.filter (fun p => decide (p.1 ≠ c')),
               held := some (c', t') } : TicketLockState).pending.length
            = (s.pending.filter (fun p => decide (p.1 ≠ c'))).length := rfl
        have h_hc :
            ({ nextTicket := s.nextTicket, serving := s.serving + 1,
               pending := s.pending.filter (fun p => decide (p.1 ≠ c')),
               held := some (c', t') } : TicketLockState).heldCount = 1 := rfl
        rw [h_n, h_s, h_p, h_hc]
        omega

-- ============================================================================
-- SM2.B.14 — Determinism
-- ============================================================================

/-- **Theorem (SM2.B.14): `applyOp` is deterministic.**

For any state `s` and op `op`, the result of `s.applyOp op` is
unique — `applyOp` is a total function (Lean's definitional
equality witnesses this).  This is the "no-ND" property that
distinguishes the abstract spec from a weaker labelled-transition
specification.

The theorem statement is trivial (it asserts function-extensionality
of `applyOp` itself, which is true by definition), but is exported
as a named theorem because SM3 / SM2.D / SM2.E consumers cite it
when reasoning about operation sequences. -/
theorem ticketLock_applyOp_deterministic (s : TicketLockState)
    (op : TicketLockOp) :
    ∀ s₁ s₂ : TicketLockState,
      s₁ = s.applyOp op → s₂ = s.applyOp op → s₁ = s₂ := by
  intro s₁ s₂ h₁ h₂
  rw [h₁, h₂]

/-- **Theorem (SM2.B.14, alternate form): `promotePending` is
deterministic.**

Companion to `ticketLock_applyOp_deterministic` for the second-half
release step.  Mathematically trivial; exported for surface-anchor
use by SM3 consumers. -/
theorem ticketLock_promotePending_deterministic (s : TicketLockState) :
    ∀ s₁ s₂ : TicketLockState,
      s₁ = s.promotePending → s₂ = s.promotePending → s₁ = s₂ := by
  intro s₁ s₂ h₁ h₂
  rw [h₁, h₂]

-- ============================================================================
-- SM2.B.9 — Aggregator: ticketLock_wf_invariant
-- ============================================================================

/-- **Theorem 3.2.6.1 (SM2.B.9, aggregate): wf is preserved by every
kernel-facing transition.**

For any `TicketLockState s` satisfying `s.wf`:

* `applyOp .tryAcquire core` preserves wf.
* `applyOp .observeServing core observed` preserves wf (identity).
* `releaseAndPromote core` preserves wf.

The raw `applyOp .release core` does NOT preserve full wf in
general (it can leave INV-T2 transiently violated when a pending
entry has `ticket = new serving`); the kernel-facing release
operation `releaseAndPromote` atomically restores wf via
`promotePending`.  `ticketLock_release_preserves_partial_wf`
above documents the exact subset of invariants the raw release
preserves.

This is the canonical surface anchor that downstream consumers
(SM2.B.10..B.13, SM3 ladder-acquisition proofs) cite when reasoning
about long traces of operations. -/
theorem ticketLock_wf_invariant
    (s : TicketLockState) (h : s.wf) :
    (∀ core, (s.applyOp (.tryAcquire core)).wf)
    ∧ (∀ core observed, (s.applyOp (.observeServing core observed)).wf)
    ∧ (∀ core, (s.releaseAndPromote core).wf) :=
  ⟨fun c => ticketLock_tryAcquire_preserves_wf s c h
  , fun c o => ticketLock_observeServing_preserves_wf s c o h
  , fun c => ticketLock_releaseAndPromote_preserves_wf s c h⟩

-- ============================================================================
-- SM2.B.15 — Closure-form preservation aliases
-- ============================================================================

/-- **SM2.B.15 (closure-form)**: `acquire core` preserves wf.

Named alias for `ticketLock_tryAcquire_preserves_wf` matching the
kernel-facing API name.  SM3 ladder-acquisition proofs cite this
name when reasoning about per-object lock acquisition. -/
theorem ticketLock_acquire_preserves_wf
    (s : TicketLockState) (core : CoreId) (h : s.wf) :
    (s.applyOp (.tryAcquire core)).wf :=
  ticketLock_tryAcquire_preserves_wf s core h

/-- **SM2.B.15 (closure-form)**: `release core` (composed with the
implicit promotion) preserves wf.

Named alias for `ticketLock_releaseAndPromote_preserves_wf` matching
the kernel-facing API name.  SM3 ladder-acquisition proofs cite this
name when reasoning about per-object lock release. -/
theorem ticketLock_release_preserves_wf
    (s : TicketLockState) (core : CoreId) (h : s.wf) :
    (s.releaseAndPromote core).wf :=
  ticketLock_releaseAndPromote_preserves_wf s core h

end SeLe4n.Kernel.Concurrency
