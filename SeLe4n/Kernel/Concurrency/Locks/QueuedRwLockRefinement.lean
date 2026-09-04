-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-RR RR6 (QueuedRwLock refinement bridge; the
-- deployed FIFO lock's correspondence to the Lean spec).

import SeLe4n.Kernel.Concurrency.Locks.RwLock

/-!
# WS-RR RR6.4 … RR6.9 — QueuedRwLock refinement bridge

The refinement between the Lean abstract `RwLockState` (in
`Locks/RwLock.lean`) and the **ticket** lock the kernel deploys
(`rust/sele4n-hal/src/queued_rw_lock.rs`).

## Why this module exists, and why it is not `RwLockRefinement.lean`

`RwLockRefinement.lean` models `rust/sele4n-hal/src/rw_lock.rs`: a
CAS-retry lock over a **single** `AtomicU64`, whose `ConcreteRwLockOp`
alphabet has no way to express a ticket.  `QueuedRwLock` holds **four**
atomic words — `state`, `next_ticket`, `now_serving`, `last_enqueued` —
and its whole correctness argument is about the first three.  So the
concrete model, the protocol invariant, the simulation relation, the
per-entry-point block lemmas and their composition are separate objects
from the CAS-retry ones, and they live here.

The two locks also fail to satisfy the spec for *different* reasons,
which is the substantive point.  The CAS-retry lock does not enforce
FIFO admission at all: `rwLockSim` relates the writer bit and the reader
count and says in as many words that the abstract `waiters` field is
**not represented**.  For a lock the spec constrains chiefly through
`waiters`, that relation carries almost nothing.  The ticket lock does
represent the queue — as the half-open interval `[now_serving,
next_ticket)` — so `queuedSim` below relates `waiters` to it, in order,
and the FIFO admission property becomes a theorem rather than a
documented divergence.

## The four words, and the one ghost field

`QueuedRwLockConcrete` carries an abstraction of each machine word:

| Rust field | Here | Abstraction |
|------------|------|-------------|
| `state: AtomicU64` | `state : UInt64` | verbatim, bit 63 writer / bits 0..62 reader count |
| `next_ticket: AtomicU64` | `nextTicket : UInt64` | verbatim |
| `now_serving: AtomicU64` | `nowServing : UInt64` | verbatim |
| `last_enqueued: AtomicU8` | `lastEnqueued : Option CoreId` | `none` is the `u8::MAX` sentinel |

plus one field that is **not** a machine word:

* `ledger : List (Nat × CoreId)` — which core holds each issued,
  unretired ticket, oldest first.

The ledger is ghost (history) state.  The hardware does not record it,
and no operation's *effect* reads it; it exists so that "each issued
ticket is held by at most one core" and "the waiters are the ticket
interval, in order" are statements one can make at all.  It cannot be
used to smuggle information past the physical words, because
`QueuedTicketWf.ledgerTickets` pins it to them: the ledger's tickets
**are** `[now_serving, next_ticket)`, so any step that moves the ledger
without moving the counters correspondingly breaks the invariant.

The access **mode** of a queued waiter is deliberately absent from the
ledger.  In the implementation a waiter's mode is core-local — it lives
in the waiting core's own control flow, in no shared word — so a model
that recorded it would be claiming the lock knows something it does not.
`queuedSim` therefore relates the *cores* and their *order*, which is
exactly what the FIFO property is about.

## Section map

* §1 (RR6.4) — the concrete state, the operation alphabet, `applyOp`,
  and `opEnabled` (the protocol preconditions the implementation's
  control flow establishes).
* §2 (RR6.5) — the ticket protocol's own well-formedness, stated over
  the concrete model alone: `now_serving ≤ next_ticket`, one core per
  issued ticket, and `now_serving` advancing exactly once per issue.
  Plus the two consequences the rest of the phase rests on — the
  entitlement is a singleton (mutual exclusion) and both spin loops
  terminate.
* §3 (RR6.6) — `queuedSim`, and the unheld / writer-held / readers-held
  characterizations the block lemmas consume.
* §4 (RR6.7) — the block shapes, one per entry point, each admitting an
  arbitrary `await_turn` stutter prefix; and the per-block lemmas.
* §5 (RR6.8) — trace-level composition, taking no per-block obligation
  as a hypothesis.
* §6 (RR6.9) — the end-to-end corollary from the initial state.
-/

namespace SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1 (RR6.4) — Concrete state and operation alphabet
-- ============================================================================

/-- **WS-RR RR6.4**: the concrete state of a deployed `QueuedRwLock`.

Four machine words plus the ghost ledger; see the module docstring for
what each abstracts and why the ledger is sound. -/
structure QueuedRwLockConcrete where
  /-- Bit-packed lock word: bit 63 writer-held, bits 0..62 reader count.
  Same layout as the CAS-retry lock's, so `encodeRwLock` reads it. -/
  state : UInt64
  /-- The next ticket to hand out.  Monotone; `fetch_add` is the single
  issue point, which is what makes admission order total. -/
  nextTicket : UInt64
  /-- The ticket currently entitled to enter.  Monotone, advanced
  exactly once per issued ticket. -/
  nowServing : UInt64
  /-- The core that most recently took a ticket, or `none` for the
  `u8::MAX` sentinel.  Observability only — `peek_tail` reads it and no
  protocol decision does. -/
  lastEnqueued : Option CoreId
  /-- **Ghost**: the issued, unretired tickets with their holders,
  oldest first.  Pinned to the counters by `QueuedTicketWf`. -/
  ledger : List (Nat × CoreId)
  deriving Repr, DecidableEq

/-- **WS-RR RR6.4**: the initial concrete state — `QueuedRwLock::new`.

All three counters at zero, no core has enqueued, nothing outstanding. -/
def QueuedRwLockConcrete.unheld : QueuedRwLockConcrete where
  state := 0
  nextTicket := 0
  nowServing := 0
  lastEnqueued := none
  ledger := []

/-- **WS-RR RR6.4**: one atomic access the implementation performs.

The alphabet is derived from `queued_rw_lock.rs`, not enumerated by
theme: every `AtomicU64` / `AtomicU8` method call in that file appears
here exactly once.  `take_ticket` is two ops (the `fetch_add` and the
observability `store`), `await_turn` is a `load` and a bounded `wfe`,
`pass_turn` is a `fetch_add` and a `sev`; the `peek_*` accessors
contribute the remaining loads.

Three ops carry the **ticket** their executing core holds.  That is a
ghost annotation, exactly like the ledger: it does not change what the
instruction does (`opEnabled` is where it bites), and it is what lets
"a reader may only enter while being served" be stated.  The
implementation establishes it structurally — `await_turn` precedes
every one of these three call sites. -/
inductive QueuedRwLockOp where
  /-- `state.load(Acquire)` — the `debug_assert` read and `peek_state`. -/
  | stateLoad (core : CoreId)
  /-- `now_serving.load(Acquire)` — `await_turn`'s spin read. -/
  | nowServingLoad (core : CoreId)
  /-- `next_ticket.load(Acquire)` — `peek_tail` / `peek_tickets`. -/
  | nextTicketLoad (core : CoreId)
  /-- `last_enqueued.load(Acquire)` — `peek_tail`. -/
  | lastEnqueuedLoad (core : CoreId)
  /-- `cpu::sev()` — wake every PE parked on `wfe`. -/
  | sev (core : CoreId)
  /-- `cpu::wfe_bounded(..)` — park; no state change. -/
  | wfeWait (core : CoreId)
  /-- `next_ticket.fetch_add(1, AcqRel)` — issue a ticket to `core`. -/
  | nextTicketFetchAdd (core : CoreId)
  /-- `last_enqueued.store(core_id, Release)`. -/
  | lastEnqueuedStore (core : CoreId)
  /-- `now_serving.fetch_add(1, AcqRel)` — `pass_turn`, retiring the
  served ticket the executing core holds. -/
  | nowServingFetchAdd (core : CoreId) (ticket : Nat)
  /-- `state.fetch_add(1, AcqRel)` — a served reader joins the count. -/
  | stateFetchAddReader (core : CoreId) (ticket : Nat)
  /-- `state.fetch_sub(1, AcqRel)` — a reader leaves the count. -/
  | stateFetchSubReader (core : CoreId)
  /-- `state.compare_exchange(0, WRITER_BIT, ..)` — a served writer's
  admission.  May fail. -/
  | stateCasAcquireWrite (core : CoreId) (ticket : Nat)
  /-- `state.fetch_and(READER_MASK, AcqRel)` — the writer's release. -/
  | stateFetchAndReaderMask (core : CoreId)
  deriving Repr, DecidableEq

/-- **WS-RR RR6.4**: apply one atomic access to the concrete state.

Returns `(post, succeeded)`; only the CAS can report `false`.  The
arithmetic is `UInt64`, so `fetch_sub` on a zero reader count wraps to
`u64::MAX` exactly as the hardware does — the misuse is modelled, not
assumed away.  The ticket annotations do not gate the *effect*: an
instruction executes whatever the executing core believes about its
ticket, and it is `opEnabled` that says the implementation only reaches
these sites while served. -/
def QueuedRwLockConcrete.applyOp (s : QueuedRwLockConcrete)
    (op : QueuedRwLockOp) : QueuedRwLockConcrete × Bool :=
  match op with
  | .stateLoad _ | .nowServingLoad _ | .nextTicketLoad _
  | .lastEnqueuedLoad _ | .sev _ | .wfeWait _ => (s, true)
  | .nextTicketFetchAdd c =>
      ({ s with
          nextTicket := s.nextTicket + 1
          ledger := s.ledger ++ [(s.nextTicket.toNat, c)] }, true)
  | .lastEnqueuedStore c => ({ s with lastEnqueued := some c }, true)
  | .nowServingFetchAdd _ _ =>
      ({ s with nowServing := s.nowServing + 1, ledger := s.ledger.tail }, true)
  | .stateFetchAddReader _ _ => ({ s with state := s.state + 1 }, true)
  | .stateFetchSubReader _ => ({ s with state := s.state - 1 }, true)
  | .stateCasAcquireWrite _ _ =>
      if s.state = 0 then ({ s with state := writerBit.toUInt64 }, true)
      else (s, false)
  | .stateFetchAndReaderMask _ =>
      ({ s with state := s.state &&& readerMask.toUInt64 }, true)

/-- **WS-RR RR6.4**: an op is *observation-only* when it changes no
word.  These are exactly the six loads and hints; every other op is a
read-modify-write on one of the three counters. -/
def QueuedRwLockOp.isObservation : QueuedRwLockOp → Bool
  | .stateLoad _ | .nowServingLoad _ | .nextTicketLoad _
  | .lastEnqueuedLoad _ | .sev _ | .wfeWait _ => true
  | _ => false

/-- **WS-RR RR6.4**: an observation-only op leaves the concrete state
untouched — the property the `await_turn` stutter prefix rests on. -/
theorem QueuedRwLockConcrete.applyOp_observation
    (s : QueuedRwLockConcrete) (op : QueuedRwLockOp)
    (h : op.isObservation = true) : (s.applyOp op).1 = s := by
  cases op <;> simp_all [QueuedRwLockConcrete.applyOp, QueuedRwLockOp.isObservation]

/-- **WS-RR RR6.4**: the protocol preconditions the implementation's
control flow establishes at each call site.

This is not a claim that the hardware refuses a disabled access — it is
the statement of what `queued_rw_lock.rs` guarantees before performing
it.  The ticket-carrying ops require the executing core to hold the
ticket `now_serving` names, which `await_turn` is what enforces; the
issue requires ticket headroom; the reader ops require the writer bit
clear and the count in range, which is `acquire_read`'s overflow gate
and `release_read`'s `debug_assert`. -/
def QueuedRwLockConcrete.opEnabled (s : QueuedRwLockConcrete) :
    QueuedRwLockOp → Prop
  | .nextTicketFetchAdd _ => s.nextTicket.toNat + 1 < UInt64.size
  | .nowServingFetchAdd c t =>
      s.ledger.head? = some (t, c) ∧ t = s.nowServing.toNat
  | .stateFetchAddReader c t =>
      s.ledger.head? = some (t, c) ∧ t = s.nowServing.toNat ∧
        s.state.toNat + 1 < writerBit
  | .stateCasAcquireWrite c t =>
      s.ledger.head? = some (t, c) ∧ t = s.nowServing.toNat
  | .stateFetchSubReader _ => 1 ≤ s.state.toNat ∧ s.state.toNat < writerBit
  | .stateFetchAndReaderMask _ => writerBit ≤ s.state.toNat
  | _ => True

/-- `opEnabled` is decidable, so a fixture can `decide` it. -/
instance QueuedRwLockConcrete.decidableOpEnabled
    (s : QueuedRwLockConcrete) (op : QueuedRwLockOp) :
    Decidable (s.opEnabled op) := by
  cases op <;> unfold QueuedRwLockConcrete.opEnabled <;> exact inferInstance

/-- **WS-RR RR6.4**: fold a block of concrete ops, the canonical
"execute this stretch of the implementation" semantics. -/
def queuedFoldBlock (conc : QueuedRwLockConcrete)
    (blk : List QueuedRwLockOp) : QueuedRwLockConcrete :=
  blk.foldl (fun s op => (s.applyOp op).1) conc

@[simp] theorem queuedFoldBlock_nil (conc : QueuedRwLockConcrete) :
    queuedFoldBlock conc [] = conc := rfl

@[simp] theorem queuedFoldBlock_cons (conc : QueuedRwLockConcrete)
    (op : QueuedRwLockOp) (rest : List QueuedRwLockOp) :
    queuedFoldBlock conc (op :: rest)
      = queuedFoldBlock (conc.applyOp op).1 rest := rfl

theorem queuedFoldBlock_append (conc : QueuedRwLockConcrete)
    (a b : List QueuedRwLockOp) :
    queuedFoldBlock conc (a ++ b)
      = queuedFoldBlock (queuedFoldBlock conc a) b := by
  unfold queuedFoldBlock; rw [List.foldl_append]

/-- **WS-RR RR6.4**: a stutter prefix — a list of observation-only ops.
`await_turn`'s spin is an unbounded run of these, so every block shape
admits one and none of them is a step. -/
def QueuedStutter (ops : List QueuedRwLockOp) : Prop :=
  ∀ op ∈ ops, op.isObservation = true

/-- **WS-RR RR6.4**: a stutter prefix leaves the concrete state
untouched, however long it is.  This is what makes the unbounded
`await_turn` spin appear as stuttering rather than as steps. -/
theorem queuedFoldBlock_stutter (conc : QueuedRwLockConcrete)
    (ops : List QueuedRwLockOp) (h : QueuedStutter ops) :
    queuedFoldBlock conc ops = conc := by
  induction ops generalizing conc with
  | nil => rfl
  | cons op rest ih =>
    rw [queuedFoldBlock_cons,
      QueuedRwLockConcrete.applyOp_observation conc op (h op List.mem_cons_self)]
    exact ih _ (fun o ho => h o (List.mem_cons_of_mem _ ho))

-- ============================================================================
-- §2 (RR6.5) — The ticket protocol's own well-formedness
-- ============================================================================
--
-- Everything in this section is stated over `QueuedRwLockConcrete` alone.
-- It mentions no abstract state and consumes nothing from `RwLock.lean`'s
-- spec, because it is the argument that the *implementation* is correct as
-- a mutual-exclusion protocol — which is what the simulation in §3 then
-- gets to assume rather than re-derive, and what makes both spin loops in
-- `queued_rw_lock.rs` terminate.

/-- **WS-RR RR6.5**: the half-open interval of ticket numbers
`[start, start + count)`, oldest first.

Defined here rather than reached for in the standard library so the four
lemmas the invariant needs are self-contained and their shapes are the
ones the ledger updates take: a `cons` at the head (retirement) and an
append at the tail (issue). -/
def ticketRange (start : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => start :: ticketRange (start + 1) n

@[simp] theorem ticketRange_zero (start : Nat) : ticketRange start 0 = [] := rfl

@[simp] theorem ticketRange_succ (start n : Nat) :
    ticketRange start (n + 1) = start :: ticketRange (start + 1) n := rfl

@[simp] theorem ticketRange_length (start n : Nat) :
    (ticketRange start n).length = n := by
  induction n generalizing start with
  | zero => rfl
  | succ k ih => simp [ticketRange, ih]

/-- Issue: one more ticket appears at the **end** of the interval. -/
theorem ticketRange_concat (start n : Nat) :
    ticketRange start (n + 1) = ticketRange start n ++ [start + n] := by
  induction n generalizing start with
  | zero => simp [ticketRange]
  | succ k ih =>
    rw [ticketRange_succ start (k + 1), ih (start + 1), ticketRange_succ start k]
    simp [List.cons_append, Nat.add_comm, Nat.add_left_comm]

/-- Retirement: the oldest ticket leaves the **head** of the interval. -/
theorem ticketRange_tail (start n : Nat) :
    (ticketRange start (n + 1)).tail = ticketRange (start + 1) n := rfl

theorem ticketRange_head? (start n : Nat) (h : 0 < n) :
    (ticketRange start n).head? = some start := by
  cases n with
  | zero => omega
  | succ _ => rfl

theorem mem_ticketRange {start n t : Nat} :
    t ∈ ticketRange start n ↔ start ≤ t ∧ t < start + n := by
  induction n generalizing start with
  | zero => simp
  | succ k ih =>
    rw [ticketRange_succ, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨h1, h2⟩) <;> omega
    · intro ⟨h1, h2⟩
      by_cases hEq : t = start
      · exact Or.inl hEq
      · exact Or.inr ⟨by omega, by omega⟩

theorem ticketRange_nodup (start n : Nat) : (ticketRange start n).Nodup := by
  induction n generalizing start with
  | zero => simp
  | succ k ih =>
    rw [ticketRange_succ, List.nodup_cons]
    refine ⟨?_, ih (start + 1)⟩
    intro hMem
    have := mem_ticketRange.mp hMem
    omega

/-- **WS-RR RR6.5**: the ticket protocol's well-formedness.

Two conjuncts, and between them they say everything the protocol claims
about itself:

* `servingLeNext` — `now_serving` never passes `next_ticket`.  Because
  both are read at `Nat` width, this is also the statement that neither
  counter has wrapped: with `u64` wraparound `next_ticket` could fall
  *below* `now_serving`, and the interval below would be meaningless.
* `ledgerTickets` — the issued, unretired tickets are exactly the
  half-open interval `[now_serving, next_ticket)`, **in order**.

`ledgerTickets` is what makes the ghost ledger honest.  It pins the ghost
to the two machine words in both directions: the ledger cannot gain an
entry without `next_ticket` moving, cannot lose one without `now_serving`
moving, and cannot reorder at all.  Every claim below — one holder per
ticket, exactly-once advance, singleton entitlement, both spin bounds —
is a consequence of these two lines. -/
structure QueuedTicketWf (s : QueuedRwLockConcrete) : Prop where
  /-- `now_serving ≤ next_ticket`: no ticket is served before it is
  issued, and neither counter has wrapped. -/
  servingLeNext : s.nowServing.toNat ≤ s.nextTicket.toNat
  /-- The ledger's tickets are the interval `[now_serving, next_ticket)`
  in order. -/
  ledgerTickets : s.ledger.map Prod.fst
      = ticketRange s.nowServing.toNat (s.nextTicket.toNat - s.nowServing.toNat)

/-- The initial state satisfies the invariant. -/
theorem QueuedTicketWf.unheld : QueuedTicketWf QueuedRwLockConcrete.unheld := by
  constructor <;> simp [QueuedRwLockConcrete.unheld]

/-- **WS-RR RR6.5**: the number of outstanding tickets is the width of
the interval. -/
theorem QueuedTicketWf.ledger_length {s : QueuedRwLockConcrete}
    (h : QueuedTicketWf s) :
    s.ledger.length = s.nextTicket.toNat - s.nowServing.toNat := by
  have := congrArg List.length h.ledgerTickets
  simpa using this

/-- **WS-RR RR6.5**: the ledger is empty exactly when nothing is
outstanding. -/
theorem QueuedTicketWf.ledger_nil_iff {s : QueuedRwLockConcrete}
    (h : QueuedTicketWf s) :
    s.ledger = [] ↔ s.nowServing.toNat = s.nextTicket.toNat := by
  have hLen := h.ledger_length
  have hLe := h.servingLeNext
  constructor
  · intro hNil; rw [hNil] at hLen; simp at hLen; omega
  · intro hEq
    have : s.ledger.length = 0 := by omega
    exact List.eq_nil_of_length_eq_zero this

/-- **WS-RR RR6.5 (each issued ticket is held by at most one core)**:
the outstanding tickets are pairwise distinct, so a ticket names one
ledger entry and therefore one core. -/
theorem QueuedTicketWf.ledger_tickets_nodup {s : QueuedRwLockConcrete}
    (h : QueuedTicketWf s) : (s.ledger.map Prod.fst).Nodup := by
  rw [h.ledgerTickets]; exact ticketRange_nodup _ _

/-- **WS-RR RR6.5 (one holder per ticket)**: two ledger entries carrying
the same ticket name the same core. -/
private theorem snd_unique_of_map_fst_nodup
    {α β : Type} (l : List (α × β)) (h : (l.map Prod.fst).Nodup)
    {a : α} {b₁ b₂ : β} (h₁ : (a, b₁) ∈ l) (h₂ : (a, b₂) ∈ l) : b₁ = b₂ := by
  induction l with
  | nil => exact absurd h₁ List.not_mem_nil
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp h₁ with hEq₁ | hm₁
    · subst hEq₁
      rcases List.mem_cons.mp h₂ with hEq₂ | hm₂
      · exact (congrArg Prod.snd hEq₂).symm
      · exact absurd (List.mem_map.mpr ⟨(a, b₂), hm₂, rfl⟩) h.1
    · rcases List.mem_cons.mp h₂ with hEq₂ | hm₂
      · subst hEq₂
        exact absurd (List.mem_map.mpr ⟨(a, b₁), hm₁, rfl⟩) h.1
      · exact ih h.2 hm₁ hm₂

theorem QueuedTicketWf.ticket_holder_unique {s : QueuedRwLockConcrete}
    (h : QueuedTicketWf s) {t : Nat} {c₁ c₂ : CoreId}
    (h₁ : (t, c₁) ∈ s.ledger) (h₂ : (t, c₂) ∈ s.ledger) : c₁ = c₂ :=
  snd_unique_of_map_fst_nodup s.ledger h.ledger_tickets_nodup h₁ h₂

/-- **WS-RR RR6.5**: a ticket in the ledger lies in the interval, so the
number of pass-turns ahead of it is `t - now_serving`.

This is `await_turn`'s bound: the spin at `queued_rw_lock.rs`'s
`await_turn` waits for exactly that many advances of `now_serving`, and
that many is strictly less than the number of outstanding tickets. -/
theorem QueuedTicketWf.await_turn_depth {s : QueuedRwLockConcrete}
    (h : QueuedTicketWf s) {t : Nat} {c : CoreId} (hMem : (t, c) ∈ s.ledger) :
    s.nowServing.toNat ≤ t ∧ t < s.nextTicket.toNat ∧
      t - s.nowServing.toNat < s.ledger.length := by
  have hMemT : t ∈ s.ledger.map Prod.fst := List.mem_map.mpr ⟨(t, c), hMem, rfl⟩
  rw [h.ledgerTickets] at hMemT
  have hRange := mem_ticketRange.mp hMemT
  have hLen := h.ledger_length
  have hLe := h.servingLeNext
  exact ⟨hRange.1, by omega, by omega⟩


/-- **Helper**: `UInt64` increment is `Nat` increment below the wrap
boundary.  Every use below discharges the side condition from the
protocol invariant rather than assuming it. -/
private theorem uInt64_add_one_toNat (x : UInt64) (h : x.toNat + 1 < UInt64.size) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [UInt64.toNat_add]
  have hOne : (1 : UInt64).toNat = 1 := by decide
  rw [hOne, Nat.mod_eq_of_lt h]

/-- **Helper**: `UInt64` decrement is `Nat` decrement above zero. -/
private theorem uInt64_sub_one_toNat' (x : UInt64) (h : 1 ≤ x.toNat) :
    (x - 1).toNat = x.toNat - 1 := by
  have hLe : (1 : UInt64) ≤ x := by
    rw [UInt64.le_iff_toNat_le]
    show (1 : UInt64).toNat ≤ x.toNat
    have hOne : (1 : UInt64).toNat = 1 := by decide
    omega
  rw [UInt64.toNat_sub_of_le _ _ hLe]
  show x.toNat - (1 : UInt64).toNat = x.toNat - 1
  have hOne : (1 : UInt64).toNat = 1 := by decide
  rw [hOne]

/-- **Helper**: a ledger whose head is `(t, c)` *is* `(t, c) :: tl`.

Used wherever `opEnabled` gives the served entry and the proof needs the
list shape (the retirement is `List.tail`, which only reduces on a
`cons`). -/
private theorem ledger_head?_cons {l : List (Nat × CoreId)} {t : Nat} {c : CoreId}
    (h : l.head? = some (t, c)) : ∃ tl, l = (t, c) :: tl := by
  cases l with
  | nil => simp at h
  | cons hd tl => simp at h; exact ⟨tl, by rw [h]⟩

/-- **WS-RR RR6.5**: `now_serving` moves **only** through `pass_turn`.

Together with `nowServing_pass_turn_step` below this is the
"advances exactly once per issued ticket" claim: nothing else touches
the counter, and the one thing that does adds exactly one and consumes
exactly one ledger entry.  The implementation's comment on `pass_turn`
gives the reason `fetch_add` is used rather than a store of
`ticket + 1` — a store could regress `now_serving` if the
single-advancer assumption were ever broken, and a regressing
`now_serving` admits two cores at once. -/
theorem QueuedRwLockConcrete.nowServing_only_moves_by_pass_turn
    (s : QueuedRwLockConcrete) (op : QueuedRwLockOp)
    (h : ∀ c t, op ≠ .nowServingFetchAdd c t) :
    (s.applyOp op).1.nowServing = s.nowServing := by
  cases op with
  | nowServingFetchAdd c t => exact absurd rfl (h c t)
  | stateCasAcquireWrite c t =>
    by_cases hZ : s.state = 0 <;> simp [QueuedRwLockConcrete.applyOp, hZ]
  | _ => rfl

/-- **WS-RR RR6.5**: `next_ticket` moves **only** through `take_ticket`. -/
theorem QueuedRwLockConcrete.nextTicket_only_moves_by_take_ticket
    (s : QueuedRwLockConcrete) (op : QueuedRwLockOp)
    (h : ∀ c, op ≠ .nextTicketFetchAdd c) :
    (s.applyOp op).1.nextTicket = s.nextTicket := by
  cases op with
  | nextTicketFetchAdd c => exact absurd rfl (h c)
  | stateCasAcquireWrite c t =>
    by_cases hZ : s.state = 0 <;> simp [QueuedRwLockConcrete.applyOp, hZ]
  | _ => rfl

/-- **WS-RR RR6.5**: the ledger moves **only** through the two ticket
counters' own operations. -/
theorem QueuedRwLockConcrete.ledger_only_moves_with_tickets
    (s : QueuedRwLockConcrete) (op : QueuedRwLockOp)
    (hIssue : ∀ c, op ≠ .nextTicketFetchAdd c)
    (hRetire : ∀ c t, op ≠ .nowServingFetchAdd c t) :
    (s.applyOp op).1.ledger = s.ledger := by
  cases op with
  | nextTicketFetchAdd c => exact absurd rfl (hIssue c)
  | nowServingFetchAdd c t => exact absurd rfl (hRetire c t)
  | stateCasAcquireWrite c t =>
    by_cases hZ : s.state = 0 <;> simp [QueuedRwLockConcrete.applyOp, hZ]
  | _ => rfl

/-- **WS-RR RR6.5**: one `pass_turn` advances `now_serving` by exactly
one and retires exactly the head of the ledger. -/
theorem QueuedRwLockConcrete.nowServing_pass_turn_step
    {s : QueuedRwLockConcrete} (hWf : QueuedTicketWf s) {c : CoreId} {t : Nat}
    (hEn : s.opEnabled (.nowServingFetchAdd c t)) :
    (s.applyOp (.nowServingFetchAdd c t)).1.nowServing.toNat = s.nowServing.toNat + 1 ∧
    (s.applyOp (.nowServingFetchAdd c t)).1.ledger = s.ledger.tail ∧
    s.ledger.head? = some (t, c) := by
  obtain ⟨hHead, hT⟩ := hEn
  obtain ⟨tl, hCons⟩ := ledger_head?_cons hHead
  have hLen : 0 < s.ledger.length := by rw [hCons]; simp
  have hLenEq := hWf.ledger_length
  have hLt : s.nowServing.toNat < s.nextTicket.toNat := by omega
  have hSize : s.nextTicket.toNat < UInt64.size := s.nextTicket.toNat_lt_size
  have hNoWrap : s.nowServing.toNat + 1 < UInt64.size := by omega
  refine ⟨?_, rfl, hHead⟩
  show (s.nowServing + 1).toNat = s.nowServing.toNat + 1
  exact uInt64_add_one_toNat _ hNoWrap

/-- **WS-RR RR6.5**: the protocol invariant is preserved by every
**enabled** operation.

The two ticket operations are the only interesting cases, and each is
the interval identity its ledger update matches: an issue appends at the
top (`ticketRange_concat`), a retirement drops the head
(`ticketRange_tail`).  Every other operation touches only `state` or
`last_enqueued` and so preserves both conjuncts syntactically. -/
theorem QueuedTicketWf.preserved {s : QueuedRwLockConcrete}
    (hWf : QueuedTicketWf s) (op : QueuedRwLockOp) (hEn : s.opEnabled op) :
    QueuedTicketWf (s.applyOp op).1 := by
  cases op with
  | nextTicketFetchAdd c =>
    have hNoWrap : s.nextTicket.toNat + 1 < UInt64.size := hEn
    have hNext : (s.nextTicket + 1).toNat = s.nextTicket.toNat + 1 :=
      uInt64_add_one_toNat _ hNoWrap
    constructor
    · show s.nowServing.toNat ≤ (s.nextTicket + 1).toNat
      rw [hNext]; have := hWf.servingLeNext; omega
    · show (s.ledger ++ [(s.nextTicket.toNat, c)]).map Prod.fst
          = ticketRange s.nowServing.toNat ((s.nextTicket + 1).toNat - s.nowServing.toNat)
      rw [hNext, List.map_append, hWf.ledgerTickets]
      have hLe := hWf.servingLeNext
      have hStep : s.nextTicket.toNat + 1 - s.nowServing.toNat
          = (s.nextTicket.toNat - s.nowServing.toNat) + 1 := by omega
      rw [hStep, ticketRange_concat]
      have hSum : s.nowServing.toNat + (s.nextTicket.toNat - s.nowServing.toNat)
          = s.nextTicket.toNat := by omega
      rw [hSum]
      rfl
  | nowServingFetchAdd c t =>
    obtain ⟨hHead, _hT⟩ := hEn
    obtain ⟨tlLedger, hCons⟩ := ledger_head?_cons hHead
    have hLen : 0 < s.ledger.length := by rw [hCons]; simp
    have hLenEq := hWf.ledger_length
    have hLt : s.nowServing.toNat < s.nextTicket.toNat := by omega
    have hSize : s.nextTicket.toNat < UInt64.size := s.nextTicket.toNat_lt_size
    have hServing : (s.nowServing + 1).toNat = s.nowServing.toNat + 1 :=
      uInt64_add_one_toNat _ (by omega)
    constructor
    · show (s.nowServing + 1).toNat ≤ s.nextTicket.toNat
      rw [hServing]; omega
    · show s.ledger.tail.map Prod.fst
          = ticketRange (s.nowServing + 1).toNat
              (s.nextTicket.toNat - (s.nowServing + 1).toNat)
      rw [hServing]
      have hWidth : s.nextTicket.toNat - s.nowServing.toNat
          = (s.nextTicket.toNat - (s.nowServing.toNat + 1)) + 1 := by omega
      have hTickets := hWf.ledgerTickets
      rw [hWidth] at hTickets
      rw [hCons, List.map_cons, ticketRange_succ] at hTickets
      rw [hCons]
      show List.map Prod.fst tlLedger
          = ticketRange (s.nowServing.toNat + 1)
              (s.nextTicket.toNat - (s.nowServing.toNat + 1))
      exact (List.cons.inj hTickets).2
  | stateLoad _ | nowServingLoad _ | nextTicketLoad _ | lastEnqueuedLoad _
  | sev _ | wfeWait _ | lastEnqueuedStore _ | stateFetchAddReader _ _
  | stateFetchSubReader _ | stateFetchAndReaderMask _ =>
    exact ⟨hWf.servingLeNext, hWf.ledgerTickets⟩
  | stateCasAcquireWrite _ _ =>
    by_cases hZero : s.state = 0 <;>
      simp only [QueuedRwLockConcrete.applyOp, hZero, if_true, if_false] <;>
      exact ⟨hWf.servingLeNext, hWf.ledgerTickets⟩

/-- **WS-RR RR6.5**: a trace is *enabled* from `s` when every operation
in it satisfies the protocol precondition at the state it executes in. -/
def queuedTraceEnabled : QueuedRwLockConcrete → List QueuedRwLockOp → Prop
  | _, [] => True
  | s, op :: rest => s.opEnabled op ∧ queuedTraceEnabled (s.applyOp op).1 rest

/-- **WS-RR RR6.5**: the protocol invariant survives a whole enabled
trace, not merely one step. -/
theorem QueuedTicketWf.preserved_along {s : QueuedRwLockConcrete}
    (hWf : QueuedTicketWf s) (ops : List QueuedRwLockOp)
    (hEn : queuedTraceEnabled s ops) :
    QueuedTicketWf (queuedFoldBlock s ops) := by
  induction ops generalizing s with
  | nil => exact hWf
  | cons op rest ih =>
    obtain ⟨hHead, hTail⟩ := hEn
    exact ih (hWf.preserved op hHead) hTail

/-- **WS-RR RR6.5 (mutual exclusion, the entitlement half)**: at most
one core is entitled to enter at a time, and in at most one mode.

Both entry operations — a reader joining the count and a writer's CAS —
require their executing core to be at the **head** of the ledger, which
is one entry.  So there is no state at which two different cores, or one
core in two modes, may enter.  This is the whole of the ticket
protocol's mutual-exclusion argument: everything else about `state`
follows from it plus the fact that the writer's admission is a CAS from
exactly `0`. -/
theorem queued_entry_is_exclusive {s : QueuedRwLockConcrete}
    {cR cW : CoreId} {tR tW : Nat}
    (hR : s.opEnabled (.stateFetchAddReader cR tR))
    (hW : s.opEnabled (.stateCasAcquireWrite cW tW)) :
    cR = cW ∧ tR = tW := by
  obtain ⟨hHeadR, _, _⟩ := hR
  obtain ⟨hHeadW, _⟩ := hW
  rw [hHeadR] at hHeadW
  injection Option.some.inj hHeadW with hT hC
  exact ⟨hC, hT⟩

/-- **WS-RR RR6.5 (mutual exclusion, the reader half)**: while a core
holds the served ticket, **no other core** can join the reader count.

This is what makes `acquire_write`'s `compare_exchange(0, WRITER_BIT)`
loop terminate.  A writer that has been served holds the ledger head, so
the readers admitted ahead of it can only leave: the count is
monotonically decreasing and the CAS succeeds within that many
releases.  The implementation's comment at that loop states exactly this
("no NEW reader can enter — entering requires the ticket we hold"); this
is the statement. -/
theorem queued_no_reader_entry_while_served {s : QueuedRwLockConcrete}
    {w c : CoreId} {tw t : Nat}
    (hHead : s.ledger.head? = some (tw, w))
    (hR : s.opEnabled (.stateFetchAddReader c t)) : c = w ∧ t = tw := by
  obtain ⟨hHeadR, _, _⟩ := hR
  rw [hHeadR] at hHead
  injection Option.some.inj hHead with hT hC
  exact ⟨hC, hT⟩

/-- **WS-RR RR6.5 (writer admission is exclusive of readers)**: a
writer's CAS succeeds only from `state = 0`, so no reader holds at the
instant the writer bit is set.

The CAS — rather than a `fetch_or` after a load — is what makes this a
property of the *operation* instead of a property of a preceding
observation. -/
theorem queued_writer_admission_requires_empty_state
    (s : QueuedRwLockConcrete) (c : CoreId) (t : Nat)
    (h : (s.applyOp (.stateCasAcquireWrite c t)).2 = true) : s.state = 0 := by
  by_cases hZ : s.state = 0
  · exact hZ
  · simp [QueuedRwLockConcrete.applyOp, hZ] at h

/-- **WS-RR RR6.5 (the reader count strictly decreases on release)**:
one `release_read` lowers the reader count by exactly one.

Together with `queued_no_reader_entry_while_served` this is the
termination measure for `acquire_write`'s CAS loop: the count cannot
rise while the writer is served, and each release lowers it by one, so
the loop runs at most `state` times. -/
theorem queued_release_read_strictly_decreases
    {s : QueuedRwLockConcrete} {c : CoreId}
    (h : s.opEnabled (.stateFetchSubReader c)) :
    (s.applyOp (.stateFetchSubReader c)).1.state.toNat + 1 = s.state.toNat := by
  obtain ⟨hPos, _⟩ := h
  show (s.state - 1).toNat + 1 = s.state.toNat
  rw [uInt64_sub_one_toNat' _ hPos]
  omega

/-- **WS-RR RR6.5 (`await_turn` terminates)**: a core holding ticket `t`
waits for exactly `t - now_serving` advances, and that number is
strictly below the count of outstanding tickets.

`now_serving` advances once per issued ticket and only ever forward
(`nowServing_pass_turn_step`, `nowServing_only_moves_by_pass_turn`), so
the wait is finite and bounded by the queue's own length. -/
theorem queued_await_turn_terminates {s : QueuedRwLockConcrete}
    (hWf : QueuedTicketWf s) {t : Nat} {c : CoreId} (hMem : (t, c) ∈ s.ledger) :
    t - s.nowServing.toNat < s.ledger.length :=
  (hWf.await_turn_depth hMem).2.2


-- ============================================================================
-- §3 (RR6.6) — The simulation relation
-- ============================================================================
--
-- `rwLockSim` (in `RwLockRefinement.lean`) relates the writer bit and the
-- reader count, and states that the abstract `waiters` field is not
-- represented.  For the CAS-retry lock that is honest — it has no queue —
-- but it is also almost the whole of what the FIFO spec constrains, so the
-- relation carries very little.  The ticket lock *does* represent the
-- queue, as the half-open interval `[now_serving, next_ticket)`, and
-- `queuedSim` says so.

/-- **WS-RR RR6.6**: whether the abstract state's writer occupies a
ticket.  A writer holds its ticket from admission until `release_write`
retires it, so it is the ledger's head while it holds; a reader passes
its ticket on at entry and occupies none. -/
def queuedWriterOffset (abs : RwLockState) : Nat :=
  if abs.writerHeld.isSome then 1 else 0

/-- **WS-RR RR6.6**: the cores holding issued, unretired tickets, in
ticket order — the held writer, if any, then the waiters in queue order.

The access **mode** does not appear: in the implementation a waiter's
mode lives in its own control flow and in no shared word, so a model
that recorded it would credit the lock with knowledge it does not have.
What the FIFO property is about — which core, in what order — is exactly
what this list carries. -/
def queuedLedgerCores (abs : RwLockState) : List CoreId :=
  (match abs.writerHeld with | some w => [w] | none => []) ++ abs.waiters.map Prod.fst

@[simp] theorem queuedLedgerCores_length (abs : RwLockState) :
    (queuedLedgerCores abs).length = queuedWriterOffset abs + abs.waiters.length := by
  unfold queuedLedgerCores queuedWriterOffset
  cases abs.writerHeld <;> simp <;> omega

/-- **WS-RR RR6.6**: the simulation relation between the abstract
`RwLockState` and the deployed ticket lock.

Three conjuncts:

1. The packed word encodes the holder state, exactly as `rwLockSim`
   requires of the CAS-retry lock — the two locks share the `state`
   layout, so this half of the refinement is common.
2. The ticket protocol is well-formed (§2).  Carrying it inside the
   relation is what lets the block lemmas below use the interval
   without re-deriving it, and what forbids a "simulation" that moves
   the ghost ledger away from the machine words.
3. **The queue is represented**: the cores holding issued tickets, in
   ticket order, are the held writer followed by the abstract waiters
   in queue order.

Conjunct 3 with conjunct 2's `ledgerTickets` is the FIFO
correspondence: the `i`-th waiter holds ticket
`now_serving + writerOffset + i` (`queuedSim_waiter_ticket`), so
admission order — which is ticket order in the implementation — **is**
the spec's queue order. -/
def queuedSim (abs : RwLockState) (conc : QueuedRwLockConcrete) : Prop :=
  conc.state.toNat = encodeRwLock abs.writerHeld.isSome abs.readers.length ∧
  QueuedTicketWf conc ∧
  conc.ledger.map Prod.snd = queuedLedgerCores abs

/-- **Witness**: the initial states are related. -/
theorem queuedSim_unheld :
    queuedSim RwLockState.unheld QueuedRwLockConcrete.unheld := by
  refine ⟨?_, QueuedTicketWf.unheld, ?_⟩
  · simp [QueuedRwLockConcrete.unheld, encodeRwLock, RwLockState.unheld]
  · simp [QueuedRwLockConcrete.unheld, queuedLedgerCores, RwLockState.unheld]

/-- **WS-RR RR6.6**: the number of outstanding tickets is the held
writer plus the waiters — the interval's width read off the spec. -/
theorem queuedSim_outstanding {abs : RwLockState} {conc : QueuedRwLockConcrete}
    (h : queuedSim abs conc) :
    conc.nextTicket.toNat - conc.nowServing.toNat
      = queuedWriterOffset abs + abs.waiters.length := by
  obtain ⟨_, hWf, hCores⟩ := h
  have hLen := congrArg List.length hCores
  simp only [List.length_map, queuedLedgerCores_length] at hLen
  rw [← hWf.ledger_length, hLen]

/-- **WS-RR RR6.6 (unheld characterization)**: nothing is outstanding
exactly when the spec has no writer and no waiters. -/
theorem queuedSim_ledger_nil_iff {abs : RwLockState} {conc : QueuedRwLockConcrete}
    (h : queuedSim abs conc) :
    conc.ledger = [] ↔ (abs.writerHeld = none ∧ abs.waiters = []) := by
  obtain ⟨_, _hWf, hCores⟩ := h
  constructor
  · intro hNil
    rw [hNil] at hCores
    simp only [List.map_nil] at hCores
    unfold queuedLedgerCores at hCores
    cases hW : abs.writerHeld with
    | some w => rw [hW] at hCores; simp at hCores
    | none =>
      rw [hW] at hCores
      simp only [List.nil_append] at hCores
      exact ⟨rfl, by simpa using hCores.symm⟩
  · rintro ⟨hW, hQ⟩
    have : conc.ledger.map Prod.snd = [] := by
      rw [hCores]; unfold queuedLedgerCores; rw [hW, hQ]; simp
    simpa using this

/-- **WS-RR RR6.6 (writer-held characterization)**: while a writer
holds, the ledger's head is that writer at the served ticket, and the
packed word is exactly `WRITER_BIT`.

The second half needs the abstract INV-R1 (a writer excludes readers),
which is where `abs.wf` enters. -/
theorem queuedSim_writer_held {abs : RwLockState} {conc : QueuedRwLockConcrete}
    (h : queuedSim abs conc) (hWfAbs : abs.wf) {w : CoreId}
    (hW : abs.writerHeld = some w) :
    conc.ledger.head? = some (conc.nowServing.toNat, w) ∧
      conc.state = writerBit.toUInt64 := by
  obtain ⟨hState, hWf, hCores⟩ := h
  have hNoReaders : abs.readers = [] := RwLockState.wf_writerReadersExclusion hWfAbs w hW
  have hCoresHead : (conc.ledger.map Prod.snd).head? = some w := by
    rw [hCores]; unfold queuedLedgerCores; rw [hW]; rfl
  have hTicketHead : (conc.ledger.map Prod.fst).head? = some conc.nowServing.toNat := by
    rw [hWf.ledgerTickets]
    have hLenPos : 0 < conc.ledger.length := by
      cases hL : conc.ledger with
      | nil => rw [hL] at hCoresHead; simp at hCoresHead
      | cons _ _ => simp
    have := hWf.ledger_length
    exact ticketRange_head? _ _ (by omega)
  refine ⟨?_, ?_⟩
  · cases hL : conc.ledger with
    | nil => rw [hL] at hCoresHead; simp at hCoresHead
    | cons hd tl =>
      rw [hL, List.map_cons] at hCoresHead hTicketHead
      simp only [List.head?_cons, Option.some.injEq] at hCoresHead hTicketHead
      simp only [List.head?_cons, Option.some.injEq]
      exact Prod.ext hTicketHead hCoresHead
  · have : conc.state.toNat = writerBit := by
      rw [hState, hW, hNoReaders]; simp [encodeRwLock]
    apply UInt64.toNat_inj.mp
    rw [this]
    decide

/-- **WS-RR RR6.6 (readers-held characterization)**: with no writer, the
packed word is exactly the reader count, and the ledger's cores are the
waiters. -/
theorem queuedSim_no_writer {abs : RwLockState} {conc : QueuedRwLockConcrete}
    (h : queuedSim abs conc) (hW : abs.writerHeld = none) :
    conc.state.toNat = abs.readers.length ∧
      conc.ledger.map Prod.snd = abs.waiters.map Prod.fst := by
  obtain ⟨hState, _, hCores⟩ := h
  refine ⟨?_, ?_⟩
  · rw [hState, hW]; simp [encodeRwLock]
  · rw [hCores]; unfold queuedLedgerCores; rw [hW]; simp

/-- **WS-RR RR6.6 (head-waiter characterization)**: with no writer, the
head of the queue holds the served ticket — so the core the spec would
promote next is exactly the core the implementation admits next. -/
theorem queuedSim_head_waiter {abs : RwLockState} {conc : QueuedRwLockConcrete}
    (h : queuedSim abs conc) (hW : abs.writerHeld = none)
    {c : CoreId} {m : AccessMode} {rest : List (CoreId × AccessMode)}
    (hQ : abs.waiters = (c, m) :: rest) :
    conc.ledger.head? = some (conc.nowServing.toNat, c) := by
  obtain ⟨_, hWf, hCores⟩ := h
  have hCoresHead : (conc.ledger.map Prod.snd).head? = some c := by
    rw [hCores]; unfold queuedLedgerCores; rw [hW, hQ]; rfl
  have hLenPos : 0 < conc.ledger.length := by
    cases hL : conc.ledger with
    | nil => rw [hL] at hCoresHead; simp at hCoresHead
    | cons _ _ => simp
  have hTicketHead : (conc.ledger.map Prod.fst).head? = some conc.nowServing.toNat := by
    rw [hWf.ledgerTickets]
    have := hWf.ledger_length
    exact ticketRange_head? _ _ (by omega)
  cases hL : conc.ledger with
  | nil => rw [hL] at hCoresHead; simp at hCoresHead
  | cons hd tl =>
    rw [hL, List.map_cons] at hCoresHead hTicketHead
    simp only [List.head?_cons, Option.some.injEq] at hCoresHead hTicketHead
    simp only [List.head?_cons, Option.some.injEq]
    exact Prod.ext hTicketHead hCoresHead


/-- **Helper**: the interval's `i`-th ticket. -/
theorem ticketRange_getElem? (start n i : Nat) :
    (ticketRange start n)[i]? = if i < n then some (start + i) else none := by
  induction n generalizing start i with
  | zero => simp
  | succ k ih =>
    cases i with
    | zero => simp [ticketRange]
    | succ j =>
      rw [ticketRange_succ, List.getElem?_cons_succ, ih (start + 1) j]
      by_cases hLt : j < k
      · rw [if_pos hLt, if_pos (by omega)]
        congr 1
        omega
      · rw [if_neg hLt, if_neg (by omega)]

/-- **Helper**: the writer part of `queuedLedgerCores` has length
`queuedWriterOffset`. -/
private theorem queuedWriterPart_length (abs : RwLockState) :
    (match abs.writerHeld with | some w => [w] | none => ([] : List CoreId)).length
      = queuedWriterOffset abs := by
  unfold queuedWriterOffset; cases abs.writerHeld <;> simp

/-- **WS-RR RR6.6 (the FIFO correspondence)**: the `i`-th abstract
waiter holds ticket `now_serving + writerOffset + i`.

This is the payoff of §3 and the reason `queuedSim` is worth more than
`rwLockSim`.  Admission order in the implementation **is** ticket order
— `await_turn` admits `now_serving` and `pass_turn` advances it by one —
so this says the implementation admits waiters in exactly the spec's
queue order.  For the CAS-retry lock the corresponding statement is
false, which is the documented FIFO divergence at `rwLockSim`. -/
theorem queuedSim_waiter_ticket {abs : RwLockState} {conc : QueuedRwLockConcrete}
    (h : queuedSim abs conc) {i : Nat} {c : CoreId} {m : AccessMode}
    (hi : abs.waiters[i]? = some (c, m)) :
    conc.ledger[queuedWriterOffset abs + i]?
      = some (conc.nowServing.toNat + (queuedWriterOffset abs + i), c) := by
  obtain ⟨_, hWf, hCores⟩ := h
  have hILt : i < abs.waiters.length := by
    apply Decidable.byContradiction
    intro hc
    rw [List.getElem?_eq_none (by omega)] at hi
    exact absurd hi (by simp)
  have hOutstanding : conc.ledger.length
      = queuedWriterOffset abs + abs.waiters.length := by
    have hLen := congrArg List.length hCores
    simpa [queuedLedgerCores_length] using hLen
  have hCoreAt : (conc.ledger[queuedWriterOffset abs + i]?).map Prod.snd = some c := by
    rw [← List.getElem?_map, hCores]
    unfold queuedLedgerCores
    rw [List.getElem?_append_right (by rw [queuedWriterPart_length]; omega),
      queuedWriterPart_length]
    have hIdx : queuedWriterOffset abs + i - queuedWriterOffset abs = i := by omega
    rw [hIdx, List.getElem?_map, hi]
    rfl
  have hTicketAt : (conc.ledger[queuedWriterOffset abs + i]?).map Prod.fst
      = some (conc.nowServing.toNat + (queuedWriterOffset abs + i)) := by
    rw [← List.getElem?_map, hWf.ledgerTickets, ticketRange_getElem?]
    have hWidth : conc.nextTicket.toNat - conc.nowServing.toNat
        = queuedWriterOffset abs + abs.waiters.length := by
      rw [← hWf.ledger_length, hOutstanding]
    rw [hWidth, if_pos (by omega)]
  cases hAt : conc.ledger[queuedWriterOffset abs + i]? with
  | none => rw [hAt] at hCoreAt; simp at hCoreAt
  | some p =>
    rw [hAt] at hCoreAt hTicketAt
    simp only [Option.map_some, Option.some.injEq] at hCoreAt hTicketAt
    exact congrArg some (Prod.ext hTicketAt hCoreAt)


-- ============================================================================
-- §4 (RR6.7) — Per-entry-point block shapes and their step lemmas
-- ============================================================================
--
-- One abstract `RwLockOp` maps to one concrete block, mirroring the
-- `blockBisim_*` shape in `RwLockRefinement.lean`.  Two things differ from
-- that family, and both are forced by the protocol rather than chosen:
--
-- * Every acquire block admits an arbitrary **stutter prefix** — the
--   `await_turn` spin, which is unbounded in the implementation.  It must
--   appear as stuttering that leaves the state (and so `queuedSim`)
--   intact, not as a step, which is what `QueuedStutter` and
--   `queuedFoldBlock_stutter` deliver.
--
-- * A **release block carries the promoted waiters' entry**.  The abstract
--   `releaseWrite` batch-promotes through `promoteWaitersOnWriterRelease`,
--   and the concrete `fetch_and` + `pass_turn` alone leaves the promoted
--   cores outside the lock — so `queuedSim` is false in between and the
--   block has to reach the next quiescent point.  This is the same
--   block-contract extension the CAS-retry refinement needs (WS-RR RR6.16),
--   arrived at here for the same reason: the spec's release is a
--   promotion, and a concrete block that stops before the promotion has
--   not modelled it.

/-- **WS-RR RR6.7**: `take_ticket` — the issue plus the observability
store, in the order `queued_rw_lock.rs` performs them. -/
def takeTicketOps (c : CoreId) : List QueuedRwLockOp :=
  [.nextTicketFetchAdd c, .lastEnqueuedStore c]

/-- **WS-RR RR6.7**: the tail of `acquire_read` once the core is served:
the `debug_assert` read, the count increment, and `pass_turn`. -/
def readerEnterOps (c : CoreId) (t : Nat) : List QueuedRwLockOp :=
  [.nowServingLoad c, .stateLoad c, .stateFetchAddReader c t,
   .nowServingFetchAdd c t, .sev c]

/-- **WS-RR RR6.7**: the tail of `acquire_write` once the core is
served: the CAS from exactly `0`.  The writer keeps its ticket — it is
`release_write` that retires it. -/
def writerEnterOps (c : CoreId) (t : Nat) : List QueuedRwLockOp :=
  [.nowServingLoad c, .stateLoad c, .stateCasAcquireWrite c t]

/-- **WS-RR RR6.7**: a contiguous run of readers entering, each with its
own ticket, in ticket order. -/
def readerAdmitOps (t : Nat) : List CoreId → List QueuedRwLockOp
  | [] => []
  | c :: rest => readerEnterOps c t ++ readerAdmitOps (t + 1) rest

/-- **WS-RR RR6.7**: `release_write`'s own ops — clear the writer bit,
then hand the ticket on.  That order is required: a reader served by the
next ticket must not observe `WRITER_BIT` still set. -/
def releaseWriteOps (c : CoreId) (t : Nat) : List QueuedRwLockOp :=
  [.stateFetchAndReaderMask c, .nowServingFetchAdd c t, .sev c]

/-- **WS-RR RR6.7**: the concrete ops that carry out the abstract
promotion at served ticket `t`.

Mirrors `promoteWaitersOnWriterRelease`'s three cases exactly: nothing
queued, a writer at the head (admitted alone, keeping its ticket), or a
run of readers (admitted together, each passing its ticket on). -/
def promoteOps (t : Nat) (waiters : List (CoreId × AccessMode)) :
    List QueuedRwLockOp :=
  match waiters with
  | [] => []
  | (w, .write) :: _ => writerEnterOps w t
  | (_, .read) :: _ =>
      readerAdmitOps t ((waiters.takeWhile (fun x => x.2 = .read)).map Prod.fst)

-- ----------------------------------------------------------------------------
-- Folds
-- ----------------------------------------------------------------------------

theorem queuedFoldBlock_takeTicketOps (conc : QueuedRwLockConcrete) (c : CoreId) :
    queuedFoldBlock conc (takeTicketOps c)
      = { conc with
            nextTicket := conc.nextTicket + 1
            lastEnqueued := some c
            ledger := conc.ledger ++ [(conc.nextTicket.toNat, c)] } := rfl

theorem queuedFoldBlock_readerEnterOps (conc : QueuedRwLockConcrete)
    (c : CoreId) (t : Nat) :
    queuedFoldBlock conc (readerEnterOps c t)
      = { conc with
            state := conc.state + 1
            nowServing := conc.nowServing + 1
            ledger := conc.ledger.tail } := rfl

theorem queuedFoldBlock_writerEnterOps_of_zero (conc : QueuedRwLockConcrete)
    (c : CoreId) (t : Nat) (hZero : conc.state = 0) :
    queuedFoldBlock conc (writerEnterOps c t)
      = { conc with state := writerBit.toUInt64 } := by
  simp [queuedFoldBlock, writerEnterOps, QueuedRwLockConcrete.applyOp, hZero]

theorem queuedFoldBlock_releaseWriteOps (conc : QueuedRwLockConcrete)
    (c : CoreId) (t : Nat) :
    queuedFoldBlock conc (releaseWriteOps c t)
      = { conc with
            state := conc.state &&& readerMask.toUInt64
            nowServing := conc.nowServing + 1
            ledger := conc.ledger.tail } := rfl

/-- **WS-RR RR6.7**: the post-state of a reader batch, one entry per
core.  Written as a recursion rather than as `state + k` so the
`UInt64` no-wrap side conditions are discharged where they are needed
instead of assumed in the statement. -/
def readerAdmitPost (conc : QueuedRwLockConcrete) : List CoreId → QueuedRwLockConcrete
  | [] => conc
  | _ :: rest =>
      readerAdmitPost
        { conc with
            state := conc.state + 1
            nowServing := conc.nowServing + 1
            ledger := conc.ledger.tail } rest

theorem queuedFoldBlock_readerAdmitOps (conc : QueuedRwLockConcrete)
    (t : Nat) (cores : List CoreId) :
    queuedFoldBlock conc (readerAdmitOps t cores) = readerAdmitPost conc cores := by
  induction cores generalizing conc t with
  | nil => rfl
  | cons c rest ih =>
    rw [readerAdmitOps, queuedFoldBlock_append, queuedFoldBlock_readerEnterOps,
      readerAdmitPost, ih]

theorem readerAdmitPost_ledger (conc : QueuedRwLockConcrete) (cores : List CoreId) :
    (readerAdmitPost conc cores).ledger = conc.ledger.drop cores.length := by
  induction cores generalizing conc with
  | nil => rfl
  | cons c rest ih =>
    rw [readerAdmitPost, ih]
    show conc.ledger.tail.drop rest.length = conc.ledger.drop (rest.length + 1)
    cases conc.ledger <;> simp

theorem readerAdmitPost_nextTicket (conc : QueuedRwLockConcrete) (cores : List CoreId) :
    (readerAdmitPost conc cores).nextTicket = conc.nextTicket := by
  induction cores generalizing conc with
  | nil => rfl
  | cons c rest ih => rw [readerAdmitPost, ih]

theorem readerAdmitPost_state_toNat (conc : QueuedRwLockConcrete) (cores : List CoreId)
    (h : conc.state.toNat + cores.length < UInt64.size) :
    (readerAdmitPost conc cores).state.toNat = conc.state.toNat + cores.length := by
  induction cores generalizing conc with
  | nil => simp [readerAdmitPost]
  | cons c rest ih =>
    rw [readerAdmitPost]
    have hStep : (conc.state + 1).toNat = conc.state.toNat + 1 :=
      uInt64_add_one_toNat _ (by simp at h; omega)
    rw [ih _ (by simp only []; rw [hStep]; simp at h; omega)]
    simp only []
    rw [hStep]
    simp [List.length_cons]
    omega

theorem readerAdmitPost_nowServing_toNat (conc : QueuedRwLockConcrete)
    (cores : List CoreId)
    (h : conc.nowServing.toNat + cores.length < UInt64.size) :
    (readerAdmitPost conc cores).nowServing.toNat
      = conc.nowServing.toNat + cores.length := by
  induction cores generalizing conc with
  | nil => simp [readerAdmitPost]
  | cons c rest ih =>
    rw [readerAdmitPost]
    have hStep : (conc.nowServing + 1).toNat = conc.nowServing.toNat + 1 :=
      uInt64_add_one_toNat _ (by simp at h; omega)
    rw [ih _ (by simp only []; rw [hStep]; simp at h; omega)]
    simp only []
    rw [hStep]
    simp [List.length_cons]
    omega


/-- **Helper**: dropping the front of the interval. -/
theorem ticketRange_drop (start n k : Nat) :
    (ticketRange start n).drop k = ticketRange (start + k) (n - k) := by
  induction k generalizing start n with
  | zero => simp
  | succ j ih =>
    cases n with
    | zero => simp [ticketRange]
    | succ m =>
      rw [ticketRange_succ, List.drop_succ_cons, ih (start + 1) m]
      have h1 : start + 1 + j = start + (j + 1) := by omega
      have h2 : m - j = m + 1 - (j + 1) := by omega
      rw [h1, h2]

/-- **Helper**: `map` commutes with `drop`. -/
private theorem map_drop_comm {α β : Type} (f : α → β) (l : List α) (k : Nat) :
    (l.drop k).map f = (l.map f).drop k := by
  induction k generalizing l with
  | zero => simp
  | succ j ih => cases l with
    | nil => simp
    | cons hd tl => simp [ih tl]

/-- **WS-RR RR6.7 (the promotion block)**: from a quiescent
sim-related pair, the concrete promotion block reaches the state the
abstract promotion produces.

This is the release blocks' second half and the reason a release block
cannot stop at `fetch_and` + `pass_turn`: the spec's release **is** a
promotion, and between the two the concrete lock has admitted nobody
while the abstract has.  All three of the abstract helper's branches are
covered — nothing queued, a writer at the head (admitted alone, keeping
its ticket, so the ledger head stays), and a run of readers (admitted
together, each retiring its own ticket). -/
theorem promoteOps_preserves_queuedSim
    {abs : RwLockState} {conc : QueuedRwLockConcrete}
    (hSim : queuedSim abs conc) (hWaitersBound : abs.waiters.length ≤ numCores)
    (hW : abs.writerHeld = none) (hR : abs.readers = []) :
    queuedSim abs.promoteWaitersOnWriterRelease
      (queuedFoldBlock conc (promoteOps conc.nowServing.toNat abs.waiters)) := by
  obtain ⟨hState, hWf, hCores⟩ := hSim
  have hStateZero : conc.state = 0 := by
    apply UInt64.toNat_inj.mp
    rw [hState, hW, hR]
    simp [encodeRwLock]
  have hCoresQ : conc.ledger.map Prod.snd = abs.waiters.map Prod.fst := by
    rw [hCores]; unfold queuedLedgerCores; rw [hW]; simp
  have hLedgerLen : conc.ledger.length = abs.waiters.length := by
    have := congrArg List.length hCoresQ; simpa using this
  cases hQ : abs.waiters with
  | nil =>
    rw [promote_noop_on_empty_waiters abs hQ, ← hQ]
    have hOps : promoteOps conc.nowServing.toNat abs.waiters = [] := by
      rw [hQ]; rfl
    rw [hOps, queuedFoldBlock_nil]
    exact ⟨hState, hWf, hCores⟩
  | cons hd tl =>
    obtain ⟨c, m⟩ := hd
    cases m with
    | write =>
      -- A queued writer at the head is admitted alone and keeps its
      -- ticket, so the ledger's head does not move.
      rw [← hQ]
      have hPromote : abs.promoteWaitersOnWriterRelease
          = { abs with writerHeld := some c, waiters := tl } := by
        unfold RwLockState.promoteWaitersOnWriterRelease; rw [hQ]
      have hOps : promoteOps conc.nowServing.toNat abs.waiters
          = writerEnterOps c conc.nowServing.toNat := by
        rw [hQ]; rfl
      rw [hPromote, hOps, queuedFoldBlock_writerEnterOps_of_zero _ _ _ hStateZero]
      refine ⟨?_, ⟨hWf.servingLeNext, hWf.ledgerTickets⟩, ?_⟩
      · show (writerBit.toUInt64).toNat = encodeRwLock (some c).isSome abs.readers.length
        rw [hR]
        simp only [Option.isSome_some, encodeRwLock, if_true, List.length_nil, Nat.add_zero]
        decide
      · show conc.ledger.map Prod.snd = queuedLedgerCores _
        rw [hCoresQ, hQ]
        unfold queuedLedgerCores
        simp
    | read =>
      -- A run of readers is admitted together; each retires its own
      -- ticket at entry, so the interval shrinks from the bottom by the
      -- size of the run.
      rw [← hQ]
      have hPromote : abs.promoteWaitersOnWriterRelease
          = { abs with
                readers := (abs.waiters.takeWhile (fun w => w.2 = .read)).map Prod.fst
                  ++ abs.readers
                waiters := abs.waiters.dropWhile (fun w => w.2 = .read) } := by
        unfold RwLockState.promoteWaitersOnWriterRelease; rw [hQ]
      have hOps : promoteOps conc.nowServing.toNat abs.waiters
          = readerAdmitOps conc.nowServing.toNat
              ((abs.waiters.takeWhile (fun w => w.2 = .read)).map Prod.fst) := by
        rw [hQ]; rfl
      rw [hPromote, hOps, queuedFoldBlock_readerAdmitOps]
      have hSplit : (abs.waiters.takeWhile (fun w => w.2 = .read))
          ++ (abs.waiters.dropWhile (fun w => w.2 = .read)) = abs.waiters :=
        List.takeWhile_append_dropWhile
      have hBatchLen :
          ((abs.waiters.takeWhile (fun w => w.2 = .read)).map Prod.fst).length
            = (abs.waiters.takeWhile (fun w => w.2 = .read)).length := by simp
      have hKle : (abs.waiters.takeWhile (fun w => w.2 = .read)).length
          ≤ abs.waiters.length := by
        have := congrArg List.length hSplit
        simp only [List.length_append] at this
        omega
      have hSizeBound : (numCores : Nat) < UInt64.size := by decide
      have hStateNat : conc.state.toNat = 0 := by rw [hStateZero]; rfl
      have hLedgerWidth := hWf.ledger_length
      have hServingLe := hWf.servingLeNext
      have hNextBound : conc.nowServing.toNat
          + ((abs.waiters.takeWhile (fun w => w.2 = .read)).map Prod.fst).length
            ≤ conc.nextTicket.toNat := by
        rw [hBatchLen]; omega
      have hNextSize : conc.nextTicket.toNat < UInt64.size := conc.nextTicket.toNat_lt_size
      have hMapSplit :
          (abs.waiters.takeWhile (fun w => w.2 = .read)).map Prod.fst
            ++ (abs.waiters.dropWhile (fun w => w.2 = .read)).map Prod.fst
              = abs.waiters.map Prod.fst := by
        rw [← List.map_append, hSplit]
      refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
      · -- The packed word is the size of the admitted run.
        rw [readerAdmitPost_state_toNat _ _ (by rw [hStateNat, hBatchLen]; omega)]
        rw [hStateNat, hR]
        simp [encodeRwLock, hW]
      · -- `now_serving` has advanced by the run's size and still trails
        -- `next_ticket`.
        rw [readerAdmitPost_nowServing_toNat _ _ (by omega), readerAdmitPost_nextTicket]
        omega
      · -- The ledger is the interval, shortened at the bottom.
        rw [readerAdmitPost_ledger, readerAdmitPost_nowServing_toNat _ _ (by omega),
          readerAdmitPost_nextTicket, map_drop_comm, hWf.ledgerTickets, ticketRange_drop]
        congr 1 <;> omega
      · -- The remaining ledger cores are the waiters still queued.
        rw [readerAdmitPost_ledger, map_drop_comm, hCoresQ]
        unfold queuedLedgerCores
        simp only [hW, List.nil_append]
        rw [← hMapSplit, List.drop_left]


/-- **WS-RR RR6.7**: the concrete block shapes, one family per abstract
operation, indexed on **both** pre-states.

The concrete index is not decoration: the ticket an entry op carries
must be the one the lock would actually issue or serve at that state,
and indexing on `conc` pins it (`conc.nextTicket.toNat` for a freshly
issued ticket, `conc.nowServing.toNat` for the served one).  A block
predicate that left the ticket free would admit
`stateFetchAddReader c 999` — the shape of the defect WS-RR RR6.15
removes from the CAS-retry inductive, which parameterizes
`tryRead_success` by arbitrary CAS operands.  Building the constraint in
from the start is cheaper than removing it later.

`spin` is the `await_turn` stutter: an arbitrary run of observation-only
ops, which is how the implementation's unbounded spin appears without
being a step.

`hNoWrap` is the ticket-headroom side condition.  It is the ~584-year
wraparound bound the module docstring names, stated rather than assumed
away: at one acquisition per nanosecond a `u64` ticket counter takes
that long to reach it. -/
inductive queuedBlock :
    RwLockState → QueuedRwLockConcrete → RwLockOp → List QueuedRwLockOp → Prop where
  /-- A core already involved re-acquiring is a spec no-op; the
  implementation has no such path, so the block observes and returns. -/
  | acquireRead_noop (abs conc c spin) :
      abs.coreInvolved c → QueuedStutter spin →
      queuedBlock abs conc (.tryAcquireRead c) spin
  /-- `acquire_read` on a calm lock: take ticket, await turn (no-one
  ahead), join the count, pass the ticket on. -/
  | acquireRead_admit (abs conc c spin) :
      ¬ abs.coreInvolved c → abs.writerHeld = none → abs.waiters = [] →
      QueuedStutter spin → conc.nextTicket.toNat + 1 < UInt64.size →
      queuedBlock abs conc (.tryAcquireRead c)
        (takeTicketOps c ++ spin ++ readerEnterOps c conc.nextTicket.toNat)
  /-- `acquire_read` behind a holder or a queued waiter: take a ticket
  and spin.  The block ends in `await_turn`, which is exactly what the
  spec's enqueue models. -/
  | acquireRead_enqueue (abs conc c spin) :
      ¬ abs.coreInvolved c → (abs.writerHeld.isSome ∨ abs.waiters ≠ []) →
      QueuedStutter spin → conc.nextTicket.toNat + 1 < UInt64.size →
      queuedBlock abs conc (.tryAcquireRead c) (takeTicketOps c ++ spin)
  /-- Spec no-op for a core already involved. -/
  | acquireWrite_noop (abs conc c spin) :
      abs.coreInvolved c → QueuedStutter spin →
      queuedBlock abs conc (.tryAcquireWrite c) spin
  /-- `acquire_write` on a calm lock: take ticket, await turn, CAS from
  exactly `0`.  The writer keeps its ticket until it releases. -/
  | acquireWrite_admit (abs conc c spin) :
      ¬ abs.coreInvolved c → abs.writerHeld = none → abs.readers = [] →
      abs.waiters = [] → QueuedStutter spin →
      conc.nextTicket.toNat + 1 < UInt64.size →
      queuedBlock abs conc (.tryAcquireWrite c)
        (takeTicketOps c ++ spin ++ writerEnterOps c conc.nextTicket.toNat)
  /-- `acquire_write` behind a holder or a queued waiter. -/
  | acquireWrite_enqueue (abs conc c spin) :
      ¬ abs.coreInvolved c →
      (abs.writerHeld.isSome ∨ abs.readers ≠ [] ∨ abs.waiters ≠ []) →
      QueuedStutter spin → conc.nextTicket.toNat + 1 < UInt64.size →
      queuedBlock abs conc (.tryAcquireWrite c) (takeTicketOps c ++ spin)
  /-- Releasing a lock one does not hold is a spec no-op; the
  implementation's `debug_assert` rejects it. -/
  | releaseRead_noop (abs conc c spin) :
      c ∉ abs.readers → QueuedStutter spin →
      queuedBlock abs conc (.releaseRead c) spin
  /-- `release_read` leaving other holders (or a writer) behind: the
  count drops and nobody is promoted. -/
  | releaseRead_noPromote (abs conc c) :
      c ∈ abs.readers →
      (abs.readers.filter (· ≠ c) ≠ [] ∨ abs.writerHeld.isSome) →
      queuedBlock abs conc (.releaseRead c) [.stateFetchSubReader c, .sev c]
  /-- `release_read` draining the lock: the count drops to zero and the
  block carries the promotion the spec performs. -/
  | releaseRead_promote (abs conc c) :
      c ∈ abs.readers → abs.readers.filter (· ≠ c) = [] → abs.writerHeld = none →
      queuedBlock abs conc (.releaseRead c)
        ([.stateFetchSubReader c, .sev c]
          ++ promoteOps conc.nowServing.toNat abs.waiters)
  /-- Releasing a write lock one does not hold is a spec no-op. -/
  | releaseWrite_noop (abs conc c spin) :
      abs.writerHeld ≠ some c → QueuedStutter spin →
      queuedBlock abs conc (.releaseWrite c) spin
  /-- `release_write`: clear the writer bit, hand the ticket on, and
  carry the promotion.  The order of the first two is the
  implementation's and is required — a reader served by the next ticket
  must not observe `WRITER_BIT` still set. -/
  | releaseWrite_effective (abs conc c) :
      abs.writerHeld = some c →
      queuedBlock abs conc (.releaseWrite c)
        (releaseWriteOps c conc.nowServing.toNat
          ++ promoteOps (conc.nowServing.toNat + 1) abs.waiters)

/-- **Helper**: `take_ticket` preserves the protocol invariant. -/
theorem QueuedTicketWf.takeTicket {conc : QueuedRwLockConcrete}
    (hWf : QueuedTicketWf conc) (c : CoreId)
    (hNoWrap : conc.nextTicket.toNat + 1 < UInt64.size) :
    QueuedTicketWf (queuedFoldBlock conc (takeTicketOps c)) := by
  rw [queuedFoldBlock_takeTicketOps]
  have hStep := hWf.preserved (.nextTicketFetchAdd c) hNoWrap
  exact ⟨hStep.servingLeNext, hStep.ledgerTickets⟩

-- ----------------------------------------------------------------------------
-- Per-block step lemmas, one per entry point
-- ----------------------------------------------------------------------------

/-- **WS-RR RR6.7 (`acquire_read`, admitted)**: on a calm lock the
`acquire_read` block issues a ticket that is served at once, joins the
reader count and passes the ticket on.

This case alone needs no ticket headroom: nothing is queued, so
`now_serving` and `next_ticket` advance together and the invariant holds
even at the wrap boundary.  The block contract carries the side
condition because the enqueue path does need it. -/
theorem queuedBlock_step_acquireRead_admit
    {abs : RwLockState} {conc : QueuedRwLockConcrete} {c : CoreId}
    {spin : List QueuedRwLockOp}
    (hSim : queuedSim abs conc) (hWfAbs : abs.wf)
    (hNotInv : ¬ abs.coreInvolved c) (hW : abs.writerHeld = none)
    (hQ : abs.waiters = []) (hSpin : QueuedStutter spin) :
    queuedSim (abs.applyOp (.tryAcquireRead c))
      (queuedFoldBlock conc
        (takeTicketOps c ++ spin ++ readerEnterOps c conc.nextTicket.toNat)) := by
  obtain ⟨hState, hWf, hCores⟩ := hSim
  have hLedgerNil : conc.ledger = [] :=
    (queuedSim_ledger_nil_iff ⟨hState, hWf, hCores⟩).mpr ⟨hW, hQ⟩
  have hServEq : conc.nowServing.toNat = conc.nextTicket.toNat :=
    hWf.ledger_nil_iff.mp hLedgerNil
  have hServEqU : conc.nowServing = conc.nextTicket := UInt64.toNat_inj.mp hServEq
  have hShape := tryAcquireRead_direct_acquire_shape abs c hNotInv hW hQ
  have hStateNat : conc.state.toNat = abs.readers.length := by
    rw [hState, hW]; simp [encodeRwLock]
  have hReadersBound : abs.readers.length ≤ numCores := by
    have := rwLock_bounded_wait_read abs hWfAbs; omega
  have hStateNoWrap : conc.state.toNat + 1 < UInt64.size := by
    have : (numCores : Nat) + 1 < UInt64.size := by decide
    omega
  rw [queuedFoldBlock_append, queuedFoldBlock_append,
    queuedFoldBlock_takeTicketOps, queuedFoldBlock_stutter _ _ hSpin,
    queuedFoldBlock_readerEnterOps]
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · show (conc.state + 1).toNat
        = encodeRwLock (abs.applyOp (.tryAcquireRead c)).writerHeld.isSome
            (abs.applyOp (.tryAcquireRead c)).readers.length
    rw [uInt64_add_one_toNat _ hStateNoWrap, hShape.1, hShape.2.1, hW, hStateNat]
    simp [encodeRwLock]
  · show (conc.nowServing + 1).toNat ≤ (conc.nextTicket + 1).toNat
    rw [hServEqU]
    exact Nat.le_refl _
  · show (conc.ledger ++ [(conc.nextTicket.toNat, c)]).tail.map Prod.fst
        = ticketRange (conc.nowServing + 1).toNat
            ((conc.nextTicket + 1).toNat - (conc.nowServing + 1).toNat)
    rw [hLedgerNil, hServEqU]
    simp
  · show ((conc.ledger ++ [(conc.nextTicket.toNat, c)]).tail).map Prod.snd
        = queuedLedgerCores (abs.applyOp (.tryAcquireRead c))
    rw [hLedgerNil]
    unfold queuedLedgerCores
    rw [hShape.2.1, hShape.2.2, hW, hQ]
    simp

/-- **WS-RR RR6.7 (`acquire_read`, enqueued)**: behind a holder or a
queued waiter the block takes a ticket and spins, which is exactly the
spec's append to `waiters`. -/
theorem queuedBlock_step_acquireRead_enqueue
    {abs : RwLockState} {conc : QueuedRwLockConcrete} {c : CoreId}
    {spin : List QueuedRwLockOp}
    (hSim : queuedSim abs conc)
    (hNotInv : ¬ abs.coreInvolved c)
    (hBusy : abs.writerHeld.isSome ∨ abs.waiters ≠ [])
    (hSpin : QueuedStutter spin)
    (hNoWrap : conc.nextTicket.toNat + 1 < UInt64.size) :
    queuedSim (abs.applyOp (.tryAcquireRead c))
      (queuedFoldBlock conc (takeTicketOps c ++ spin)) := by
  obtain ⟨hState, hWf, hCores⟩ := hSim
  have hPost : abs.applyOp (.tryAcquireRead c)
      = { abs with waiters := abs.waiters ++ [(c, AccessMode.read)] } := by
    unfold RwLockState.applyOp
    simp only [hNotInv, ↓reduceIte]
    have : (abs.writerHeld.isSome = true ∨ abs.waiters ≠ []) := hBusy
    simp [this]
  have hWfPost := hWf.takeTicket c hNoWrap
  rw [queuedFoldBlock_append, queuedFoldBlock_takeTicketOps,
    queuedFoldBlock_stutter _ _ hSpin]
  rw [queuedFoldBlock_takeTicketOps] at hWfPost
  refine ⟨?_, hWfPost, ?_⟩
  · rw [hPost]; exact hState
  · show (conc.ledger ++ [(conc.nextTicket.toNat, c)]).map Prod.snd
        = queuedLedgerCores (abs.applyOp (.tryAcquireRead c))
    rw [hPost, List.map_append, hCores]
    unfold queuedLedgerCores
    simp [List.append_assoc]


/-- **WS-RR RR6.7 (`acquire_write`, admitted)**: on a calm lock the
`acquire_write` block issues a served ticket and takes the lock by CAS
from exactly `0`, keeping its ticket. -/
theorem queuedBlock_step_acquireWrite_admit
    {abs : RwLockState} {conc : QueuedRwLockConcrete} {c : CoreId}
    {spin : List QueuedRwLockOp}
    (hSim : queuedSim abs conc)
    (hNotInv : ¬ abs.coreInvolved c) (hW : abs.writerHeld = none)
    (hR : abs.readers = []) (hQ : abs.waiters = []) (hSpin : QueuedStutter spin)
    (hNoWrap : conc.nextTicket.toNat + 1 < UInt64.size) :
    queuedSim (abs.applyOp (.tryAcquireWrite c))
      (queuedFoldBlock conc
        (takeTicketOps c ++ spin ++ writerEnterOps c conc.nextTicket.toNat)) := by
  obtain ⟨hState, hWf, hCores⟩ := hSim
  have hLedgerNil : conc.ledger = [] :=
    (queuedSim_ledger_nil_iff ⟨hState, hWf, hCores⟩).mpr ⟨hW, hQ⟩
  have hServEq : conc.nowServing.toNat = conc.nextTicket.toNat :=
    hWf.ledger_nil_iff.mp hLedgerNil
  have hStateZero : conc.state = 0 := by
    apply UInt64.toNat_inj.mp
    rw [hState, hW, hR]; simp [encodeRwLock]
  have hShape := tryAcquireWrite_direct_acquire_shape abs c hNotInv hW hR hQ
  have hNextStep : (conc.nextTicket + 1).toNat = conc.nextTicket.toNat + 1 :=
    uInt64_add_one_toNat _ hNoWrap
  have hFoldWriter :
      queuedFoldBlock (queuedFoldBlock conc (takeTicketOps c))
          (writerEnterOps c conc.nextTicket.toNat)
        = { queuedFoldBlock conc (takeTicketOps c) with state := writerBit.toUInt64 } :=
    queuedFoldBlock_writerEnterOps_of_zero _ _ _
      (by rw [queuedFoldBlock_takeTicketOps]; exact hStateZero)
  rw [queuedFoldBlock_append, queuedFoldBlock_append,
    queuedFoldBlock_stutter _ _ hSpin, hFoldWriter, queuedFoldBlock_takeTicketOps]
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · show (writerBit.toUInt64).toNat
        = encodeRwLock (abs.applyOp (.tryAcquireWrite c)).writerHeld.isSome
            (abs.applyOp (.tryAcquireWrite c)).readers.length
    rw [hShape.1, hShape.2.1, hR]
    simp only [Option.isSome_some, encodeRwLock, if_true, List.length_nil, Nat.add_zero]
    decide
  · show conc.nowServing.toNat ≤ (conc.nextTicket + 1).toNat
    rw [hNextStep]; omega
  · show (conc.ledger ++ [(conc.nextTicket.toNat, c)]).map Prod.fst
        = ticketRange conc.nowServing.toNat
            ((conc.nextTicket + 1).toNat - conc.nowServing.toNat)
    rw [hLedgerNil, hNextStep, hServEq]
    simp [ticketRange]
  · show (conc.ledger ++ [(conc.nextTicket.toNat, c)]).map Prod.snd
        = queuedLedgerCores (abs.applyOp (.tryAcquireWrite c))
    rw [hLedgerNil]
    unfold queuedLedgerCores
    rw [hShape.1, hShape.2.2, hQ]
    simp

/-- **WS-RR RR6.7 (`acquire_write`, enqueued)**. -/
theorem queuedBlock_step_acquireWrite_enqueue
    {abs : RwLockState} {conc : QueuedRwLockConcrete} {c : CoreId}
    {spin : List QueuedRwLockOp}
    (hSim : queuedSim abs conc)
    (hNotInv : ¬ abs.coreInvolved c)
    (hBusy : abs.writerHeld.isSome ∨ abs.readers ≠ [] ∨ abs.waiters ≠ [])
    (hSpin : QueuedStutter spin)
    (hNoWrap : conc.nextTicket.toNat + 1 < UInt64.size) :
    queuedSim (abs.applyOp (.tryAcquireWrite c))
      (queuedFoldBlock conc (takeTicketOps c ++ spin)) := by
  obtain ⟨hState, hWf, hCores⟩ := hSim
  have hPost : abs.applyOp (.tryAcquireWrite c)
      = { abs with waiters := abs.waiters ++ [(c, AccessMode.write)] } := by
    unfold RwLockState.applyOp
    simp only [hNotInv, ↓reduceIte]
    have : (abs.writerHeld.isSome = true ∨ abs.readers ≠ [] ∨ abs.waiters ≠ []) := hBusy
    simp [this]
  have hWfPost := hWf.takeTicket c hNoWrap
  rw [queuedFoldBlock_append, queuedFoldBlock_takeTicketOps,
    queuedFoldBlock_stutter _ _ hSpin]
  rw [queuedFoldBlock_takeTicketOps] at hWfPost
  refine ⟨?_, hWfPost, ?_⟩
  · rw [hPost]; exact hState
  · show (conc.ledger ++ [(conc.nextTicket.toNat, c)]).map Prod.snd
        = queuedLedgerCores (abs.applyOp (.tryAcquireWrite c))
    rw [hPost, List.map_append, hCores]
    unfold queuedLedgerCores
    simp [List.append_assoc]


/-- **WS-RR RR6.7 (`release_read`, no promotion)**: the count drops and
nobody is admitted. -/
theorem queuedBlock_step_releaseRead_noPromote
    {abs : RwLockState} {conc : QueuedRwLockConcrete} {c : CoreId}
    (hSim : queuedSim abs conc) (hWfAbs : abs.wf)
    (hHolder : c ∈ abs.readers)
    (hNoPromote : abs.readers.filter (· ≠ c) ≠ [] ∨ abs.writerHeld.isSome = true) :
    queuedSim (abs.applyOp (.releaseRead c))
      (queuedFoldBlock conc [.stateFetchSubReader c, .sev c]) := by
  obtain ⟨hState, hWf, hCores⟩ := hSim
  have hLenStep : (abs.readers.filter (· ≠ c)).length + 1 = abs.readers.length :=
    filter_ne_length_of_nodup abs.readers hWfAbs.2.1 c hHolder
  have hPost : abs.applyOp (.releaseRead c)
      = ({ writerHeld := abs.writerHeld, readers := abs.readers.filter (· ≠ c),
           waiters := abs.waiters } : RwLockState) := by
    rw [releaseRead_effective_post abs c hHolder]
    exact promoteWaitersIfReadersEmpty_noop _ hNoPromote
  have hGe : 1 ≤ conc.state.toNat := by
    rw [hState]; exact encodeRwLock_at_least_one_when_reader abs c hHolder
  have hFold : queuedFoldBlock conc [QueuedRwLockOp.stateFetchSubReader c, .sev c]
      = { conc with state := conc.state - 1 } := rfl
  rw [hFold, hPost]
  refine ⟨?_, ⟨hWf.servingLeNext, hWf.ledgerTickets⟩, hCores⟩
  show (conc.state - 1).toNat
      = encodeRwLock abs.writerHeld.isSome (abs.readers.filter (· ≠ c)).length
  have hFilterLen : (abs.readers.filter (· ≠ c)).length = abs.readers.length - 1 := by omega
  have hPos : 1 ≤ abs.readers.length := by omega
  rw [uInt64_sub_one_toNat' _ hGe, hState, hFilterLen]
  unfold encodeRwLock
  cases hW : abs.writerHeld.isSome with
  | true => simp only [if_true]; omega
  | false => simp only [Bool.false_eq_true, if_false]; omega

/-- **WS-RR RR6.7 (`release_read`, draining)**: the last reader leaves,
and the block carries the promotion the spec performs.

The block cannot stop at `fetch_sub`: at that point the abstract state
has already admitted the head of the queue and the concrete lock has
not, so `queuedSim` is false in between. -/
theorem queuedBlock_step_releaseRead_promote
    {abs : RwLockState} {conc : QueuedRwLockConcrete} {c : CoreId}
    (hSim : queuedSim abs conc) (hWfAbs : abs.wf)
    (hHolder : c ∈ abs.readers) (hFilterNil : abs.readers.filter (· ≠ c) = [])
    (hW : abs.writerHeld = none) :
    queuedSim (abs.applyOp (.releaseRead c))
      (queuedFoldBlock conc
        ([.stateFetchSubReader c, .sev c]
          ++ promoteOps conc.nowServing.toNat abs.waiters)) := by
  obtain ⟨hState, hWf, hCores⟩ := hSim
  have hLenStep : (abs.readers.filter (· ≠ c)).length + 1 = abs.readers.length :=
    filter_ne_length_of_nodup abs.readers hWfAbs.2.1 c hHolder
  have hOne : abs.readers.length = 1 := by rw [hFilterNil] at hLenStep; simpa using hLenStep.symm
  have hStateOne : conc.state.toNat = 1 := by rw [hState, hW, hOne]; simp [encodeRwLock]
  have hWaitersBound : abs.waiters.length ≤ numCores := by
    have := rwLock_bounded_wait_read abs hWfAbs; omega
  have hPost : abs.applyOp (.releaseRead c)
      = ({ writerHeld := abs.writerHeld, readers := [], waiters := abs.waiters }
          : RwLockState).promoteWaitersOnWriterRelease := by
    rw [releaseRead_effective_post abs c hHolder, hFilterNil]
    exact promoteIfReadersEmpty_eq_onWriterRelease _ rfl hW
  have hFold : queuedFoldBlock conc [QueuedRwLockOp.stateFetchSubReader c, .sev c]
      = { conc with state := conc.state - 1 } := rfl
  rw [hPost, queuedFoldBlock_append, hFold]
  refine promoteOps_preserves_queuedSim ⟨?_, ⟨hWf.servingLeNext, hWf.ledgerTickets⟩, hCores⟩
    hWaitersBound hW rfl
  show (conc.state - 1).toNat = encodeRwLock abs.writerHeld.isSome ([] : List CoreId).length
  rw [uInt64_sub_one_toNat' _ (by omega), hStateOne, hW]
  simp [encodeRwLock]


/-- **WS-RR RR6.7 (`release_write`)**: clear the writer bit, hand the
ticket on, and admit whoever the spec promotes.

The order of the first two ops is the implementation's and is required:
a reader served by the next ticket must not observe `WRITER_BIT` still
set.  The block then carries the promotion, for the same reason as the
draining `release_read`. -/
theorem queuedBlock_step_releaseWrite
    {abs : RwLockState} {conc : QueuedRwLockConcrete} {c : CoreId}
    (hSim : queuedSim abs conc) (hWfAbs : abs.wf) (hW : abs.writerHeld = some c) :
    queuedSim (abs.applyOp (.releaseWrite c))
      (queuedFoldBlock conc
        (releaseWriteOps c conc.nowServing.toNat
          ++ promoteOps (conc.nowServing.toNat + 1) abs.waiters)) := by
  obtain ⟨hHead, hStateW⟩ := queuedSim_writer_held hSim hWfAbs hW
  obtain ⟨hState, hWf, hCores⟩ := hSim
  have hNoReaders : abs.readers = [] := RwLockState.wf_writerReadersExclusion hWfAbs c hW
  have hWaitersBound : abs.waiters.length ≤ numCores := by
    have := rwLock_bounded_wait_read abs hWfAbs; omega
  obtain ⟨tlLedger, hLedgerCons⟩ := ledger_head?_cons hHead
  have hLedgerLen : 0 < conc.ledger.length := by rw [hLedgerCons]; simp
  have hNsLt : conc.nowServing.toNat < conc.nextTicket.toNat := by
    have := hWf.ledger_length; omega
  have hNsStep : (conc.nowServing + 1).toNat = conc.nowServing.toNat + 1 :=
    uInt64_add_one_toNat _ (by have := conc.nextTicket.toNat_lt_size; omega)
  have hPost : abs.applyOp (.releaseWrite c)
      = ({ writerHeld := none, readers := abs.readers, waiters := abs.waiters }
          : RwLockState).promoteWaitersOnWriterRelease := by
    unfold RwLockState.applyOp
    have hNe : ¬ (abs.writerHeld ≠ some c) := fun h => h hW
    simp only [hNe, ↓reduceIte]
  have hFold : queuedFoldBlock conc (releaseWriteOps c conc.nowServing.toNat)
      = { conc with
            state := 0
            nowServing := conc.nowServing + 1
            ledger := conc.ledger.tail } := by
    rw [queuedFoldBlock_releaseWriteOps, hStateW]
    have hMask : writerBit.toUInt64 &&& readerMask.toUInt64 = 0 := by decide
    rw [hMask]
  have hWfMid : QueuedTicketWf
      { conc with
          state := 0
          nowServing := conc.nowServing + 1
          ledger := conc.ledger.tail } := by
    have hStep := hWf.preserved (.nowServingFetchAdd c conc.nowServing.toNat) ⟨hHead, rfl⟩
    exact ⟨hStep.servingLeNext, hStep.ledgerTickets⟩
  have hCoresMid : conc.ledger.tail.map Prod.snd = abs.waiters.map Prod.fst := by
    rw [hLedgerCons] at hCores ⊢
    unfold queuedLedgerCores at hCores
    rw [hW] at hCores
    simp only [List.map_cons, List.cons_append, List.tail_cons] at hCores ⊢
    exact (List.cons.inj hCores).2
  rw [hPost, queuedFoldBlock_append, hFold, ← hNsStep]
  refine promoteOps_preserves_queuedSim ⟨?_, hWfMid, ?_⟩ hWaitersBound rfl hNoReaders
  · show (0 : UInt64).toNat = encodeRwLock (none : Option CoreId).isSome abs.readers.length
    rw [hNoReaders]; simp [encodeRwLock]
  · show conc.ledger.tail.map Prod.snd
        = queuedLedgerCores
            { writerHeld := none
              readers := abs.readers
              waiters := abs.waiters }
    rw [hCoresMid]
    unfold queuedLedgerCores
    simp


/-- **WS-RR RR6.7 (the per-block step theorem)**: every block shape
carries the simulation across its abstract operation.

The case analysis is over `queuedBlock`'s constructors, so a
constructor added later is a **missing case** rather than a silent gap
— the same derivation-not-enumeration discipline the CAS-retry
refinement's `opCorresponds` coverage needs (WS-RR RR6.17). -/
theorem queuedBlock_preserves_queuedSim
    {abs : RwLockState} {conc : QueuedRwLockConcrete} {op : RwLockOp}
    {blk : List QueuedRwLockOp}
    (hSim : queuedSim abs conc) (hWfAbs : abs.wf)
    (hBlk : queuedBlock abs conc op blk) :
    queuedSim (abs.applyOp op) (queuedFoldBlock conc blk) := by
  cases hBlk with
  | acquireRead_noop c spin hInv hSpin =>
    rw [RwLockState.applyOp_noop_acquireRead hInv, queuedFoldBlock_stutter _ _ hSpin]
    exact hSim
  | acquireRead_admit c spin hNotInv hW hQ hSpin _hNoWrap =>
    exact queuedBlock_step_acquireRead_admit hSim hWfAbs hNotInv hW hQ hSpin
  | acquireRead_enqueue c spin hNotInv hBusy hSpin hNoWrap =>
    exact queuedBlock_step_acquireRead_enqueue hSim hNotInv hBusy hSpin hNoWrap
  | acquireWrite_noop c spin hInv hSpin =>
    rw [RwLockState.applyOp_noop_acquireWrite hInv, queuedFoldBlock_stutter _ _ hSpin]
    exact hSim
  | acquireWrite_admit c spin hNotInv hW hR hQ hSpin hNoWrap =>
    exact queuedBlock_step_acquireWrite_admit hSim hNotInv hW hR hQ hSpin hNoWrap
  | acquireWrite_enqueue c spin hNotInv hBusy hSpin hNoWrap =>
    exact queuedBlock_step_acquireWrite_enqueue hSim hNotInv hBusy hSpin hNoWrap
  | releaseRead_noop c spin hNotHolder hSpin =>
    rw [RwLockState.applyOp_noop_releaseRead hNotHolder, queuedFoldBlock_stutter _ _ hSpin]
    exact hSim
  | releaseRead_noPromote c hHolder hNoPromote =>
    exact queuedBlock_step_releaseRead_noPromote hSim hWfAbs hHolder hNoPromote
  | releaseRead_promote c hHolder hFilterNil hW =>
    exact queuedBlock_step_releaseRead_promote hSim hWfAbs hHolder hFilterNil hW
  | releaseWrite_noop c spin hNotWriter hSpin =>
    rw [RwLockState.applyOp_noop_releaseWrite hNotWriter, queuedFoldBlock_stutter _ _ hSpin]
    exact hSim
  | releaseWrite_effective c hW =>
    exact queuedBlock_step_releaseWrite hSim hWfAbs hW

-- ============================================================================
-- §5 (RR6.8) — Trace-level composition
-- ============================================================================

/-- **WS-RR RR6.8**: an abstract op-list paired with its concrete
block-list, each block admissible at the state pair it executes in.

Note what this inductive does **not** carry: any per-block simulation
obligation.  The blocks are related to the states by *shape* alone
(`queuedBlock`), and the composition below discharges the simulation
from that shape via `queuedBlock_preserves_queuedSim`.  Taking the
per-block conclusion as a hypothesis — which is what
`ListBlockBisim` does in the CAS-retry refinement, and what WS-RR
RR6.19 exists to remove — would make the main theorem assume the thing
it is supposed to prove. -/
inductive ListQueuedBlocks :
    RwLockState → QueuedRwLockConcrete → List RwLockOp →
      List (List QueuedRwLockOp) → Prop where
  | nil (abs : RwLockState) (conc : QueuedRwLockConcrete) :
      ListQueuedBlocks abs conc [] []
  | cons (abs : RwLockState) (conc : QueuedRwLockConcrete)
      (a : RwLockOp) (b : List QueuedRwLockOp)
      (as : List RwLockOp) (bs : List (List QueuedRwLockOp)) :
      queuedBlock abs conc a b →
      ListQueuedBlocks (abs.applyOp a) (queuedFoldBlock conc b) as bs →
      ListQueuedBlocks abs conc (a :: as) (b :: bs)

/-- **WS-RR RR6.8 (trace composition)**: from any sim-related,
well-formed starting pair, an abstract op-list and its concrete block
list end sim-related.

The proof is an induction over the chain with the per-block step
theorem at each link.  **No per-block obligation is a hypothesis** —
see `ListQueuedBlocks`'s docstring. -/
theorem queuedTrace_preserves_queuedSim
    {abs : RwLockState} {conc : QueuedRwLockConcrete}
    {ops : List RwLockOp} {blocks : List (List QueuedRwLockOp)}
    (hSim : queuedSim abs conc) (hWfAbs : abs.wf)
    (hChain : ListQueuedBlocks abs conc ops blocks) :
    queuedSim (ops.foldl RwLockState.applyOp abs)
      (queuedFoldBlock conc blocks.flatten) := by
  induction hChain with
  | nil a c => simpa using hSim
  | cons a c op blk restOps restBlocks hBlk _hRest ih =>
    have hStep := queuedBlock_preserves_queuedSim hSim hWfAbs hBlk
    have hWfStep := RwLockState.applyOp_preserves_wf hWfAbs op
    have hFlatten : (blk :: restBlocks).flatten = blk ++ restBlocks.flatten := by
      simp
    rw [List.foldl_cons, hFlatten, queuedFoldBlock_append]
    exact ih hStep hWfStep

-- ============================================================================
-- §6 (RR6.9) — The end-to-end refinement corollary
-- ============================================================================

/-- **WS-RR RR6.9**: `QueuedRwLock` refines the Lean FIFO
specification, end to end.

From the constructors' initial states — `QueuedRwLock::new` and
`RwLockState.unheld` — any abstract op-list executed against the
implementation's block sequence ends in a state that `queuedSim`
relates to the spec's.  With `queuedSim`'s third conjunct that includes
the **queue**: the cores holding issued tickets are the spec's waiters,
in the spec's order.

This is the statement the deployed lock is claimed to satisfy, and it
is proved before the lock is deployed (WS-RR RR6.10) rather than after,
so no version ships a core concurrency primitive whose refinement to
its own specification is open. -/
theorem queuedRwLock_refines_rwLockSpec
    (ops : List RwLockOp) (blocks : List (List QueuedRwLockOp))
    (hChain : ListQueuedBlocks RwLockState.unheld QueuedRwLockConcrete.unheld
      ops blocks) :
    queuedSim (ops.foldl RwLockState.applyOp RwLockState.unheld)
      (queuedFoldBlock QueuedRwLockConcrete.unheld blocks.flatten) :=
  queuedTrace_preserves_queuedSim queuedSim_unheld RwLockState.unheld_wf hChain

/-- **WS-RR RR6.9 (the FIFO payoff)**: after any such trace, the `i`-th
waiter the spec has queued holds the `i`-th outstanding ticket.

Admission order in the implementation is ticket order, so this says the
deployed lock admits waiters in exactly the order the spec's
`rwLock_fifo_admission` prescribes.  It is the property the CAS-retry
lock does **not** have — `rwLockSim` cannot even state it, because that
relation represents no queue at all. -/
theorem queuedRwLock_admits_in_spec_order
    (ops : List RwLockOp) (blocks : List (List QueuedRwLockOp))
    (hChain : ListQueuedBlocks RwLockState.unheld QueuedRwLockConcrete.unheld
      ops blocks)
    {i : Nat} {c : CoreId} {m : AccessMode}
    (hWaiter : (ops.foldl RwLockState.applyOp RwLockState.unheld).waiters[i]?
      = some (c, m)) :
    (queuedFoldBlock QueuedRwLockConcrete.unheld blocks.flatten).ledger[
        queuedWriterOffset (ops.foldl RwLockState.applyOp RwLockState.unheld) + i]?
      = some ((queuedFoldBlock QueuedRwLockConcrete.unheld blocks.flatten).nowServing.toNat
          + (queuedWriterOffset (ops.foldl RwLockState.applyOp RwLockState.unheld) + i), c) :=
  queuedSim_waiter_ticket (queuedRwLock_refines_rwLockSpec ops blocks hChain) hWaiter

end SeLe4n.Kernel.Concurrency
