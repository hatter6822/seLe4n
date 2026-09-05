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

## The machine words, and the one ghost field

`QueuedRwLockConcrete` carries an abstraction of each machine word:

| Rust field | Here | Abstraction |
|------------|------|-------------|
| `state: AtomicU64` | `state : UInt64` | verbatim, bit 63 writer / bits 0..62 reader count |
| `next_ticket: AtomicU64` | `nextTicket : UInt64` | verbatim |
| `now_serving: AtomicU64` | `nowServing : UInt64` | verbatim |
| `last_enqueued: AtomicU8` | `lastEnqueued : Option CoreId` | `none` is the `u8::MAX` sentinel |
| `cancelled: [AtomicU64; MAX_WAITERS]` | `cancelled : List Nat` | the published, unclaimed withdrawals (WS-LC LC2) |
| `held: [AtomicU8; MAX_WAITERS]` | `heldRead` / `heldWrite : List CoreId` | the cores whose word reads `HELD_READ` / `HELD_WRITE` (PR #890 review round 2) |

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
  issued ticket, one issued ticket per core, and `now_serving` advancing
  exactly once per issue.
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

The machine words plus the ghost ledger; see the module docstring for
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
  /-- The tickets whose holder has **withdrawn** and whose withdrawal
  nobody has claimed yet — the non-zero slots of the implementation's
  `cancelled: [AtomicU64; MAX_WAITERS]` array.

  This is a machine word, not ghost state: the withdrawal has to reach
  the core that will skip the ticket, and an array is how it does.  The
  per-core *indexing* is abstracted away, and what the array shape
  imposes is stated instead: the published tickets are distinct
  (`cancelledNodup`), and a core can have at most one withdrawal to
  publish because it holds at most one outstanding ticket
  (`ledgerCoresNodup`, WS-LC closure audit).  The second is the one the
  first cut left out, and it is not decoration: `cancel` stores into the
  slot unconditionally, so a core allowed a second ticket while its
  first withdrawal was unclaimed could overwrite that publication and
  leave the lock stalled on a ticket nobody would ever retire.  The
  issue is therefore enabled only for a core holding no ticket
  (`opEnabled`), and `publish_slot_empty` is the theorem that the store
  never overwrites. -/
  cancelled : List Nat
  /-- **PR #890 review round 2**: the cores whose **held word** reads
  `HELD_READ` — the implementation's `held: [AtomicU8; MAX_WAITERS]`
  array, one word per core, abstracted to the two sets of cores it marks
  (this one and `heldWrite`).

  These are machine words, and they are what makes a release by a
  non-holder the spec's no-op rather than a contract: `release_read`
  and `release_write` consult the caller's word before they write the
  state word, and `acquire_read` / `acquire_write` consult it before they
  take a ticket.  Before the words existed the refinement's `_noop`
  blocks described a stutter no code path performed — the deployed
  `release_read` was an unconditional `fetch_sub` — while the
  two-phase-locking unwind releases every member of a footprint,
  holding or not, relying on exactly that identity.  `queuedHeldSim`
  relates the two sets to the spec's `readers` and `writerHeld`, so the
  no-op blocks are derived from the relation rather than assumed. -/
  heldRead : List CoreId
  /-- **PR #890 review round 2**: the cores whose held word reads
  `HELD_WRITE` — at most one, by `queuedHeldSim` and INV-R1. -/
  heldWrite : List CoreId
  deriving Repr, DecidableEq

/-- **WS-RR RR6.4**: the initial concrete state — `QueuedRwLock::new`.

All three counters at zero, no core has enqueued, nothing outstanding. -/
def QueuedRwLockConcrete.unheld : QueuedRwLockConcrete where
  state := 0
  nextTicket := 0
  nowServing := 0
  lastEnqueued := none
  ledger := []
  cancelled := []
  heldRead := []
  heldWrite := []

/-- **WS-LC LC2.1**: the ledger entries whose holder has **not**
withdrawn — the queue as the spec sees it.

`ledger` keeps every issued, unretired ticket, so `ledgerTickets` stays
the contiguous interval and every arithmetic consequence of it (the
outstanding count, `await_turn`'s spin bound) is unchanged by a
withdrawal.  What a withdrawal removes is the *request*, and that is
what `liveLedger` drops: `queuedSim` relates this list to the spec's
waiters, not the raw ledger. -/
def liveOf (cancelled : List Nat) (l : List (Nat × CoreId)) : List (Nat × CoreId) :=
  l.filter (fun e => decide (e.1 ∉ cancelled))

@[simp] theorem liveOf_nil (cancelled : List Nat) : liveOf cancelled [] = [] := rfl

theorem liveOf_cons (cancelled : List Nat) (e : Nat × CoreId)
    (rest : List (Nat × CoreId)) :
    liveOf cancelled (e :: rest)
      = if e.1 ∈ cancelled then liveOf cancelled rest
        else e :: liveOf cancelled rest := by
  by_cases h : e.1 ∈ cancelled <;> simp [liveOf, h]

@[simp] theorem liveOf_nil_cancelled (l : List (Nat × CoreId)) : liveOf [] l = l := by
  induction l with
  | nil => rfl
  | cons e rest ih => rw [liveOf_cons]; simp [ih]

/-- The live entries are a sublist of the ledger, so every fact about the
ledger's ticket column that survives sublisting survives here. -/
theorem liveOf_sublist (cancelled : List Nat) (l : List (Nat × CoreId)) :
    List.Sublist (liveOf cancelled l) l := List.filter_sublist

theorem mem_liveOf {cancelled : List Nat} {l : List (Nat × CoreId)}
    {e : Nat × CoreId} : e ∈ liveOf cancelled l ↔ e ∈ l ∧ e.1 ∉ cancelled := by
  simp [liveOf, List.mem_filter]

/-- **WS-LC LC2.1**: see `liveOf`. -/
def QueuedRwLockConcrete.liveLedger (s : QueuedRwLockConcrete) :
    List (Nat × CoreId) :=
  liveOf s.cancelled s.ledger

/-- **WS-LC closure audit**: core `c` holds an outstanding ticket at this
lock — it appears in the ledger, live or withdrawn.

This is the subject of the "one outstanding ticket per core per lock"
contract.  The implementation records a withdrawal in one word per core,
so a core with two outstanding tickets could not withdraw both; the issue
is enabled only when this is false (`opEnabled`). -/
def QueuedRwLockConcrete.holdsTicket (s : QueuedRwLockConcrete) (c : CoreId) : Prop :=
  c ∈ s.ledger.map Prod.snd

instance QueuedRwLockConcrete.decidableHoldsTicket (s : QueuedRwLockConcrete) (c : CoreId) :
    Decidable (s.holdsTicket c) :=
  inferInstanceAs (Decidable (c ∈ s.ledger.map Prod.snd))

/-- **WS-LC closure audit**: core `c` has published a withdrawal nobody
has claimed yet — the implementation's `cancelled[c] != NO_WITHDRAWAL`,
which is the condition `QueuedRwLock::enqueue` parks on before it issues
a ticket.

A published withdrawal names an outstanding ticket
(`QueuedTicketWf.cancelledOutstanding`), so this is `holdsTicket`
restricted to the withdrawn entries — the half of the issue's
precondition the implementation enforces by waiting; the live half is
the caller's contract. -/
def QueuedRwLockConcrete.withdrawalPending (s : QueuedRwLockConcrete) (c : CoreId) : Prop :=
  ∃ t ∈ s.cancelled, (t, c) ∈ s.ledger

instance QueuedRwLockConcrete.decidableWithdrawalPending
    (s : QueuedRwLockConcrete) (c : CoreId) : Decidable (s.withdrawalPending c) := by
  unfold QueuedRwLockConcrete.withdrawalPending
  exact inferInstance

/-- A pending withdrawal is an outstanding ticket. -/
theorem QueuedRwLockConcrete.holdsTicket_of_withdrawalPending {s : QueuedRwLockConcrete}
    {c : CoreId} (h : s.withdrawalPending c) : s.holdsTicket c := by
  obtain ⟨t, _, hMem⟩ := h
  exact List.mem_map.mpr ⟨(t, c), hMem, rfl⟩

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
  /-- `cancelled[core].load(Acquire)` — the skip loop's read of a slot. -/
  | cancelledLoad (core : CoreId)
  /-- `cancelled[core].store(ticket + 1, Release)` — `cancel` publishing
  `core`'s withdrawal of the ticket it holds.  Publish precedes the
  head check, which is what makes the protocol race-free: a concurrent
  `pass_turn` that reaches this ticket either sees the publication and
  skips it, or does not and leaves the canceller to pass its own turn. -/
  | cancelPublish (core : CoreId) (ticket : Nat)
  /-- `cancelled[core].compare_exchange(ticket + 1, 0, AcqRel)` — the
  **arbiter**.  Exactly one of {the canceller, the previous holder's
  skip loop} clears a given slot, and only the winner may advance
  `now_serving` past that ticket; the loser must not, or two cores would
  be admitted at once.  May fail. -/
  | cancelClaim (core : CoreId) (ticket : Nat)
  /-- `held[core].load(Acquire)` — the holder check at the head of every
  acquire and release entry (PR #890 review round 2).  Observation only:
  the branch it decides is the block's shape. -/
  | heldLoad (core : CoreId)
  /-- `held[core].store(v, Release)` — `core`'s own held word set to
  `HELD_READ` / `HELD_WRITE` at its admission, or to `HELD_NONE` at its
  release.  The word is written and read by its own core only. -/
  | heldStore (core : CoreId) (mode : Option AccessMode)
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
  | .cancelledLoad _ => (s, true)
  | .cancelPublish _ t => ({ s with cancelled := s.cancelled ++ [t] }, true)
  | .cancelClaim _ t =>
      if t ∈ s.cancelled then ({ s with cancelled := s.cancelled.erase t }, true)
      else (s, false)
  | .heldLoad _ => (s, true)
  -- One word per core: a store replaces whatever the core held before.
  -- The three arms are written out so each fold lemma is `rfl`.
  | .heldStore c (some .read) =>
      ({ s with heldRead := s.heldRead.filter (· ≠ c) ++ [c]
                heldWrite := s.heldWrite.filter (· ≠ c) }, true)
  | .heldStore c (some .write) =>
      ({ s with heldRead := s.heldRead.filter (· ≠ c)
                heldWrite := s.heldWrite.filter (· ≠ c) ++ [c] }, true)
  | .heldStore c none =>
      ({ s with heldRead := s.heldRead.filter (· ≠ c)
                heldWrite := s.heldWrite.filter (· ≠ c) }, true)

/-- **WS-RR RR6.4**: an op is *observation-only* when it changes no
word.  These are exactly the six loads and hints; every other op is a
read-modify-write on one of the three counters. -/
def QueuedRwLockOp.isObservation : QueuedRwLockOp → Bool
  | .stateLoad _ | .nowServingLoad _ | .nextTicketLoad _
  | .lastEnqueuedLoad _ | .sev _ | .wfeWait _ | .cancelledLoad _ | .heldLoad _ => true
  | _ => false

/-- **WS-RR RR6.4**: an observation-only op leaves the concrete state
untouched — the property the `await_turn` stutter prefix rests on. -/
theorem QueuedRwLockConcrete.applyOp_observation
    (s : QueuedRwLockConcrete) (op : QueuedRwLockOp)
    (h : op.isObservation = true) : (s.applyOp op).1 = s := by
  cases op with
  | heldStore c m => cases m with
    | none => simp_all [QueuedRwLockOp.isObservation]
    | some m => cases m <;> simp_all [QueuedRwLockOp.isObservation]
  | _ => simp_all [QueuedRwLockConcrete.applyOp, QueuedRwLockOp.isObservation]

/-- **WS-RR RR6.4**: the protocol preconditions the implementation's
control flow establishes at each call site.

This is not a claim that the hardware refuses a disabled access — it is
the statement of what `queued_rw_lock.rs` guarantees before performing
it.  The ticket-carrying ops require the executing core to hold the
ticket `now_serving` names, which `await_turn` is what enforces; the
issue requires ticket headroom and a core holding **no** outstanding
ticket — the withdrawn half of that is the slot wait in `enqueue`, the
live half the one-outstanding-ticket-per-core contract; the reader ops
require the writer bit clear and the count in range, which is
`acquire_read`'s overflow gate and `release_read`'s `debug_assert`. -/
def QueuedRwLockConcrete.opEnabled (s : QueuedRwLockConcrete) :
    QueuedRwLockOp → Prop
  -- **WS-LC closure audit**: `¬ s.holdsTicket c` is what keeps the
  -- implementation's one-word-per-core withdrawal slot sufficient.  A
  -- core issued a second ticket while its first withdrawal was unclaimed
  -- could withdraw the second over it, and the first ticket would then
  -- never be retired: the lock stalls on a ticket nobody holds.  The
  -- implementation parks the issue until the slot is empty
  -- (`await_withdrawal_retired`), which is this precondition's withdrawn
  -- half (`withdrawalPending`); the live half is the caller's contract.
  | .nextTicketFetchAdd c => s.nextTicket.toNat + 1 < UInt64.size ∧ ¬ s.holdsTicket c
  -- `t ∉ s.cancelled` is the protocol rule that makes the invariant hold:
  -- a turn may be passed for a ticket **nobody has withdrawn**, and a skip
  -- reaches that state by claiming the withdrawal first (which erases it).
  -- Without it a `pass_turn` could retire a ticket whose slot is still
  -- published, leaving a withdrawal naming a ticket the lock has served —
  -- and the next skip loop would then advance past a live head.
  | .nowServingFetchAdd c t =>
      s.ledger.head? = some (t, c) ∧ t = s.nowServing.toNat ∧
        t ∉ s.cancelled
  | .stateFetchAddReader c t =>
      s.ledger.head? = some (t, c) ∧ t = s.nowServing.toNat ∧
        s.state.toNat + 1 < writerBit
  | .stateCasAcquireWrite c t =>
      s.ledger.head? = some (t, c) ∧ t = s.nowServing.toNat
  | .stateFetchSubReader _ => 1 ≤ s.state.toNat ∧ s.state.toNat < writerBit
  | .stateFetchAndReaderMask _ => writerBit ≤ s.state.toNat
  -- A core may publish a withdrawal only of a ticket it actually holds,
  -- and only once.  The implementation's slot is per core and its store
  -- is unconditional, so a second publication would overwrite the first
  -- rather than add to it — and under `ledgerCoresNodup` this
  -- precondition is exactly what rules that out: the core's only
  -- outstanding ticket is `t`, and `t` is not yet published
  -- (`QueuedTicketWf.publish_slot_empty`).  **And only by a core holding
  -- nothing** (PR #890 review round 3): `cancel` returns on the held word
  -- before it publishes, because a writer still holds its ticket and a
  -- withdrawal of it would pass the turn under the set bit — the spec's
  -- cancel is the identity for a holder, and the implementation now
  -- establishes that before the store rather than in a `debug_assert`.
  | .cancelPublish c t =>
      (t, c) ∈ s.ledger ∧ t ∉ s.cancelled ∧ c ∉ s.heldRead ∧ c ∉ s.heldWrite
  -- The claim has **no** precondition on purpose: it is a
  -- compare-exchange, so failing is a legitimate outcome and the model
  -- reports it in the `Bool` rather than forbidding the attempt.  What
  -- the protocol requires is that only a *successful* claim be followed
  -- by an advance, and that is `QueuedSkip`'s obligation, not this one.
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
  /-- **WS-LC LC2.1**: every published withdrawal names an issued,
  unretired ticket.  A slot naming a ticket the lock has already retired
  would make the skip loop advance `now_serving` past a ticket somebody
  is being served on — the exact hazard `pass_turn` off the head is. -/
  cancelledOutstanding : ∀ t ∈ s.cancelled, t ∈ s.ledger.map Prod.fst
  /-- **WS-LC LC2.1**: the published withdrawals are distinct.  Two
  cores cannot publish the same ticket because a ticket has one holder
  (`ticket_holder_unique`), and one core cannot publish twice because
  it holds at most one outstanding ticket (`ledgerCoresNodup`, below). -/
  cancelledNodup : s.cancelled.Nodup
  /-- **WS-LC closure audit**: one outstanding ticket per core.  The
  issue is enabled only for a core holding none (`opEnabled`), so the
  ledger's core column stays distinct.  This is what makes the
  implementation's one-word-per-core withdrawal slot sufficient: a core
  has at most one withdrawal to record (`holder_ticket_unique`), and an
  enabled publication finds its slot empty (`publish_slot_empty`).  The
  first cut of this invariant did not carry it, and the model then
  admitted the sequence — enqueue, withdraw, enqueue, withdraw — on
  which the deployed lock lost a withdrawal and stalled. -/
  ledgerCoresNodup : (s.ledger.map Prod.snd).Nodup

/-- The initial state satisfies the invariant. -/
theorem QueuedTicketWf.unheld : QueuedTicketWf QueuedRwLockConcrete.unheld := by
  constructor <;> simp [QueuedRwLockConcrete.unheld]

/-- **WS-LC LC2.1**: the invariant transported to a state whose four
*pinned* fields agree.

Every operation that writes only `state` or `last_enqueued` is this
case, and there are ten of them.  Going through one lemma rather than
re-listing the conjuncts at each site is what keeps adding a conjunct to
`QueuedTicketWf` from meaning editing ten proofs — and, more to the
point, from meaning that one of the ten quietly keeps proving the old,
weaker invariant. -/
theorem QueuedTicketWf.copy {s t : QueuedRwLockConcrete} (h : QueuedTicketWf s)
    (hServ : t.nowServing = s.nowServing) (hNext : t.nextTicket = s.nextTicket)
    (hLedger : t.ledger = s.ledger) (hCancelled : t.cancelled = s.cancelled) :
    QueuedTicketWf t where
  servingLeNext := by rw [hServ, hNext]; exact h.servingLeNext
  ledgerTickets := by rw [hLedger, hServ, hNext]; exact h.ledgerTickets
  cancelledOutstanding := by rw [hCancelled, hLedger]; exact h.cancelledOutstanding
  cancelledNodup := by rw [hCancelled]; exact h.cancelledNodup
  ledgerCoresNodup := by rw [hLedger]; exact h.ledgerCoresNodup

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

/-- **Helper (WS-LC LC2.6)**: with distinct second components, an entry
is determined by that component. -/
private theorem eq_of_snd_eq_of_nodup {l : List (Nat × CoreId)}
    (hNodup : (l.map Prod.snd).Nodup) {e f : Nat × CoreId}
    (hE : e ∈ l) (hF : f ∈ l) (hEq : e.2 = f.2) : e = f := by
  induction l with
  | nil => exact absurd hE (by simp)
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hNodup
    rcases List.mem_cons.mp hE with h1 | h1 <;> rcases List.mem_cons.mp hF with h2 | h2
    · rw [h1, h2]
    · exact absurd (List.mem_map.mpr ⟨f, h2, by rw [← hEq, ← h1]⟩) hNodup.1
    · exact absurd (List.mem_map.mpr ⟨e, h1, by rw [hEq, ← h2]⟩) hNodup.1
    · exact ih hNodup.2 h1 h2

/-- **WS-LC closure audit (one ticket per holder)**: two ledger entries
carrying the same core name the same ticket — the dual of
`ticket_holder_unique`, and what the implementation's one-word-per-core
withdrawal slot needs: a core has at most one withdrawal to record. -/
theorem QueuedTicketWf.holder_ticket_unique {s : QueuedRwLockConcrete}
    (h : QueuedTicketWf s) {t₁ t₂ : Nat} {c : CoreId}
    (h₁ : (t₁, c) ∈ s.ledger) (h₂ : (t₂, c) ∈ s.ledger) : t₁ = t₂ :=
  congrArg Prod.fst (eq_of_snd_eq_of_nodup h.ledgerCoresNodup h₁ h₂ rfl)

/-- **WS-LC closure audit (the publish never overwrites)**: an enabled
withdrawal publication finds the publishing core's slot empty.

`QueuedRwLock::cancel` stores into the slot unconditionally, so this is
the statement that the store is a *publication* and not an overwrite —
the property whose failure stalled the lock.  It follows from the
invariant alone: the core's only outstanding ticket is the one it is
withdrawing (`holder_ticket_unique`), and that one is not yet published
(`opEnabled`'s second conjunct). -/
theorem QueuedTicketWf.publish_slot_empty {s : QueuedRwLockConcrete}
    (h : QueuedTicketWf s) {c : CoreId} {t : Nat}
    (hEn : s.opEnabled (.cancelPublish c t)) : ¬ s.withdrawalPending c := by
  obtain ⟨hHeld, hFresh, _, _⟩ := hEn
  rintro ⟨t', ht'Dead, ht'Mem⟩
  exact hFresh (h.holder_ticket_unique ht'Mem hHeld ▸ ht'Dead)

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
  | cancelClaim c t =>
    by_cases hC : t ∈ s.cancelled <;> simp [QueuedRwLockConcrete.applyOp, hC]
  | heldStore c m => rcases m with _ | (_ | _) <;> rfl
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
  | cancelClaim c t =>
    by_cases hC : t ∈ s.cancelled <;> simp [QueuedRwLockConcrete.applyOp, hC]
  | heldStore c m => rcases m with _ | (_ | _) <;> rfl
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
  | cancelClaim c t =>
    by_cases hC : t ∈ s.cancelled <;> simp [QueuedRwLockConcrete.applyOp, hC]
  | heldStore c m => rcases m with _ | (_ | _) <;> rfl
  | _ => rfl

/-- **WS-RR RR6.5**: one `pass_turn` advances `now_serving` by exactly
one and retires exactly the head of the ledger. -/
theorem QueuedRwLockConcrete.nowServing_pass_turn_step
    {s : QueuedRwLockConcrete} (hWf : QueuedTicketWf s) {c : CoreId} {t : Nat}
    (hEn : s.opEnabled (.nowServingFetchAdd c t)) :
    (s.applyOp (.nowServingFetchAdd c t)).1.nowServing.toNat = s.nowServing.toNat + 1 ∧
    (s.applyOp (.nowServingFetchAdd c t)).1.ledger = s.ledger.tail ∧
    s.ledger.head? = some (t, c) := by
  obtain ⟨hHead, hT, _hNotCancelled⟩ := hEn
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
    obtain ⟨hNoWrap, hFree⟩ := hEn
    have hNext : (s.nextTicket + 1).toNat = s.nextTicket.toNat + 1 :=
      uInt64_add_one_toNat _ hNoWrap
    refine ⟨?_, ?_, ?_, hWf.cancelledNodup, ?_⟩
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
    · -- An issue only *grows* the ledger, so an outstanding withdrawal
      -- stays outstanding.
      intro t' ht'
      have := hWf.cancelledOutstanding t' ht'
      show t' ∈ (s.ledger ++ [(s.nextTicket.toNat, c)]).map Prod.fst
      rw [List.map_append]
      exact List.mem_append_left _ this
    · -- The issued ticket goes to a core holding none, so the core
      -- column stays distinct — `opEnabled`'s second conjunct.
      show ((s.ledger ++ [(s.nextTicket.toNat, c)]).map Prod.snd).Nodup
      rw [List.map_append]
      simp only [List.nodup_append]
      refine ⟨hWf.ledgerCoresNodup, by simp, ?_⟩
      intro a ha b hb hEq
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      subst hb
      exact hFree (hEq ▸ ha)
  | nowServingFetchAdd c t =>
    obtain ⟨hHead, _hT, hNotCancelled⟩ := hEn
    obtain ⟨tlLedger, hCons⟩ := ledger_head?_cons hHead
    have hLen : 0 < s.ledger.length := by rw [hCons]; simp
    have hLenEq := hWf.ledger_length
    have hLt : s.nowServing.toNat < s.nextTicket.toNat := by omega
    have hSize : s.nextTicket.toNat < UInt64.size := s.nextTicket.toNat_lt_size
    have hServing : (s.nowServing + 1).toNat = s.nowServing.toNat + 1 :=
      uInt64_add_one_toNat _ (by omega)
    refine ⟨?_, ?_, ?_, hWf.cancelledNodup, ?_⟩
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
    · -- The retirement drops the head, and the head's ticket is **not**
      -- withdrawn — that is `opEnabled`'s third conjunct, and it is what
      -- keeps a published withdrawal from outliving its ticket.
      intro t' ht'
      have hMem := hWf.cancelledOutstanding t' ht'
      show t' ∈ s.ledger.tail.map Prod.fst
      rw [hCons] at hMem ⊢
      simp only [List.map_cons, List.mem_cons, List.tail_cons] at hMem ⊢
      rcases hMem with hEq | hRest
      · exact absurd (hEq ▸ ht') hNotCancelled
      · exact hRest
    · -- Dropping the head keeps the core column distinct.
      have hCores := hWf.ledgerCoresNodup
      rw [hCons, List.map_cons, List.nodup_cons] at hCores
      show (s.ledger.tail.map Prod.snd).Nodup
      rw [hCons]
      exact hCores.2
  | cancelPublish c t =>
    obtain ⟨hHeld, hFresh, _, _⟩ := hEn
    refine ⟨hWf.servingLeNext, hWf.ledgerTickets, ?_, ?_, hWf.ledgerCoresNodup⟩
    · -- The published ticket is one the publishing core holds.
      intro t' ht'
      show t' ∈ s.ledger.map Prod.fst
      rcases List.mem_append.mp ht' with hOld | hNew
      · exact hWf.cancelledOutstanding t' hOld
      · rw [List.mem_singleton.mp hNew]
        exact List.mem_map.mpr ⟨(t, c), hHeld, rfl⟩
    · show (s.cancelled ++ [t]).Nodup
      simp only [List.nodup_append]
      refine ⟨hWf.cancelledNodup, by simp, ?_⟩
      intro a ha b hb hEq
      have hbt : b = t := List.mem_singleton.mp hb
      exact hFresh (by rw [← hbt, ← hEq]; exact ha)
  | cancelClaim c t =>
    by_cases hC : t ∈ s.cancelled
    · simp only [QueuedRwLockConcrete.applyOp, hC, if_pos]
      refine ⟨hWf.servingLeNext, hWf.ledgerTickets, ?_, ?_, hWf.ledgerCoresNodup⟩
      · intro t' ht'
        exact hWf.cancelledOutstanding t' (List.mem_of_mem_erase ht')
      · exact List.Nodup.erase t hWf.cancelledNodup
    · simp only [QueuedRwLockConcrete.applyOp, hC, if_false]
      exact (hWf.copy rfl rfl rfl rfl)
  | stateLoad _ | nowServingLoad _ | nextTicketLoad _ | lastEnqueuedLoad _
  | sev _ | wfeWait _ | lastEnqueuedStore _ | stateFetchAddReader _ _
  | stateFetchSubReader _ | stateFetchAndReaderMask _ | cancelledLoad _
  | heldLoad _ =>
    exact (hWf.copy rfl rfl rfl rfl)
  | heldStore c m =>
    -- A held-word store moves none of the four pinned fields, whichever
    -- of its three arms applies.
    rcases m with _ | (_ | _) <;> exact (hWf.copy rfl rfl rfl rfl)
  | stateCasAcquireWrite _ _ =>
    by_cases hZero : s.state = 0 <;>
      simp only [QueuedRwLockConcrete.applyOp, hZero, if_true, if_false] <;>
      exact (hWf.copy rfl rfl rfl rfl)

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

/-- **WS-LC LC2.5**: the ticket being served has not been withdrawn.

A **block-boundary** property, which is why it lives in `queuedSim`
rather than in `QueuedTicketWf`: within a block it is transiently false —
a `pass_turn` uncovers a new head, which may be a tombstone — and the
skip loop that follows restores it before the block ends.

It is what the implementation's protocol delivers: a core that withdraws
while it is the head claims its own slot and passes its own turn, and a
core that passes a turn keeps skipping while the new head is withdrawn.
And it is what the spec-facing consequences need: with it, `liveLedger`
is empty exactly when the ledger is, so "the queue is empty" means the
same thing on both sides and the calm-lock block shapes are unchanged by
the existence of withdrawals. -/
def queuedHeadLive (conc : QueuedRwLockConcrete) : Prop :=
  ∀ t c, conc.ledger.head? = some (t, c) → t ∉ conc.cancelled

/-- **PR #890 review round 2**: the held words represent the spec's
holders.

`held[c]` reads `HELD_READ` exactly when the spec has `c` among its
readers, and `HELD_WRITE` exactly when the spec's writer is `c`.  This
is the conjunct that makes a release by a non-holder, and a re-acquire
by a holder, the spec's **no-op** in the implementation rather than a
caller contract: `release_read`, `release_write`, `acquire_read` and
`acquire_write` each branch on the caller's own word before they touch
anything else, and the branch they take is decided by exactly the
abstract fact this relation pins the word to.  The four `_noop` block
shapes are therefore *derived* from the relation (their step cases in
`queuedBlock_preserves_queuedSim`), where before this conjunct existed
they were asserted of a stutter no code path performed.

Stated over membership: the words are one value per core, so the two
lists carry no order the implementation could observe. -/
def queuedHeldSim (abs : RwLockState) (conc : QueuedRwLockConcrete) : Prop :=
  (∀ c, c ∈ conc.heldRead ↔ c ∈ abs.readers) ∧
  (∀ c, c ∈ conc.heldWrite ↔ abs.writerHeld = some c)

/-- The held relation transports across any step that moves neither
held word nor either abstract holder field — which is every step that
is not an admission or a release. -/
theorem queuedHeldSim.copy {abs abs' : RwLockState}
    {conc conc' : QueuedRwLockConcrete} (h : queuedHeldSim abs conc)
    (hRead : conc'.heldRead = conc.heldRead) (hWrite : conc'.heldWrite = conc.heldWrite)
    (hReaders : abs'.readers = abs.readers) (hWriter : abs'.writerHeld = abs.writerHeld) :
    queuedHeldSim abs' conc' := by
  unfold queuedHeldSim
  rw [hRead, hWrite, hReaders, hWriter]
  exact h

/-- With no abstract reader, no core's word reads `HELD_READ`. -/
theorem queuedHeldSim.not_heldRead {abs : RwLockState} {conc : QueuedRwLockConcrete}
    (h : queuedHeldSim abs conc) (hR : abs.readers = []) (x : CoreId) :
    x ∉ conc.heldRead := by
  intro hx
  have := (h.1 x).mp hx
  rw [hR] at this
  simp at this

/-- With no abstract writer, no core's word reads `HELD_WRITE`. -/
theorem queuedHeldSim.not_heldWrite {abs : RwLockState} {conc : QueuedRwLockConcrete}
    (h : queuedHeldSim abs conc) (hW : abs.writerHeld = none) (x : CoreId) :
    x ∉ conc.heldWrite := by
  intro hx
  have := (h.2 x).mp hx
  rw [hW] at this
  simp at this

/-- **WS-RR RR6.6**: the simulation relation between the abstract
`RwLockState` and the deployed ticket lock.

Five conjuncts:
1. The packed word encodes the holder state, exactly as `rwLockSim`
   requires of the CAS-retry lock — the two locks share the `state`
   layout, so this half of the refinement is common.
2. The ticket protocol is well-formed (§2).  Carrying it inside the
   relation is what lets the block lemmas below use the interval
   without re-deriving it, and what forbids a "simulation" that moves
   the ghost ledger away from the machine words.
3. **The queue is represented**: the cores holding **live** issued
   tickets, in ticket order, are the held writer followed by the
   abstract waiters in queue order.  Live, because a withdrawal removes
   the *request* while the ticket stays outstanding until somebody
   passes it — the ticket column keeps the interval (conjunct 2), and
   this conjunct keeps the queue (WS-LC LC2.5).
4. The served ticket has not been withdrawn (`queuedHeadLive`), so
   "no live request" and "no outstanding ticket" say the same thing.
5. **The holders are represented** (`queuedHeldSim`, PR #890 review
   round 2): a core's held word reads `HELD_READ` exactly when the spec
   has it as a reader and `HELD_WRITE` exactly when the spec's writer is
   that core.  It is what the implementation's own holder checks decide
   on, so the no-op blocks of a non-holder's release and a holder's
   re-acquire follow from the relation instead of being assumed.

Conjunct 3 with conjunct 2's `ledgerTickets` is the FIFO
correspondence: the `i`-th waiter holds the `i`-th **live** ticket at or
after `now_serving` (`queuedSim_waiter_ticket`), so admission order —
which is ticket order in the implementation — **is** the spec's queue
order. -/
def queuedSim (abs : RwLockState) (conc : QueuedRwLockConcrete) : Prop :=
  conc.state.toNat = encodeRwLock abs.writerHeld.isSome abs.readers.length ∧
  QueuedTicketWf conc ∧
  conc.liveLedger.map Prod.snd = queuedLedgerCores abs ∧
  queuedHeadLive conc ∧
  queuedHeldSim abs conc

/-- **WS-LC LC2.6**: publishing a withdrawal removes exactly the entries
whose ticket it names. -/
theorem liveOf_publish (cancelled : List Nat) (t : Nat) (l : List (Nat × CoreId)) :
    liveOf (cancelled ++ [t]) l = (liveOf cancelled l).filter (fun e => decide (e.1 ≠ t)) := by
  induction l with
  | nil => rfl
  | cons e rest ih =>
    by_cases hMem : e.1 ∈ cancelled
    · rw [liveOf_cons, liveOf_cons, if_pos (List.mem_append_left _ hMem), if_pos hMem, ih]
    · by_cases hEq : e.1 = t
      · rw [liveOf_cons, liveOf_cons, if_neg hMem,
          if_pos (List.mem_append_right _ (by simp [hEq])), ih,
          List.filter_cons, if_neg (by simp [hEq])]
      · have hNot : e.1 ∉ cancelled ++ [t] := by
          intro hc
          rcases List.mem_append.mp hc with h | h
          · exact hMem h
          · exact hEq (List.mem_singleton.mp h)
        rw [liveOf_cons, liveOf_cons, if_neg hMem, if_neg hNot, ih,
          List.filter_cons, if_pos (by simp [hEq])]

/-- **WS-LC LC2.5**: a freshly issued ticket carries no withdrawal — a
published one names an *outstanding* ticket, and this one was not
outstanding a moment ago. -/
theorem QueuedTicketWf.nextTicket_not_cancelled {s : QueuedRwLockConcrete}
    (hWf : QueuedTicketWf s) : s.nextTicket.toNat ∉ s.cancelled := by
  intro hc
  have hMem := hWf.cancelledOutstanding _ hc
  rw [hWf.ledgerTickets] at hMem
  have := mem_ticketRange.mp hMem
  omega

theorem liveOf_append (cancelled : List Nat) (a b : List (Nat × CoreId)) :
    liveOf cancelled (a ++ b) = liveOf cancelled a ++ liveOf cancelled b := by
  show List.filter _ (a ++ b) = _
  exact List.filter_append a b

/-- **WS-LC LC2.5**: with nothing outstanding, nothing can be withdrawn
either — a published withdrawal names an issued ticket. -/
theorem QueuedTicketWf.cancelled_nil_of_ledger_nil {s : QueuedRwLockConcrete}
    (hWf : QueuedTicketWf s) (hNil : s.ledger = []) : s.cancelled = [] := by
  cases hC : s.cancelled with
  | nil => rfl
  | cons t rest =>
    exfalso
    have hMem := hWf.cancelledOutstanding t (by rw [hC]; simp)
    rw [hNil] at hMem; simp at hMem

/-- **WS-LC LC2.5**: with no withdrawal published, the live ledger is
the ledger and the head is trivially live — so every statement about a
withdrawal-free state is the pre-WS-LC statement verbatim. -/
theorem liveLedger_of_cancelled_nil {s : QueuedRwLockConcrete}
    (h : s.cancelled = []) : s.liveLedger = s.ledger := by
  show liveOf s.cancelled s.ledger = _
  rw [h]; exact liveOf_nil_cancelled _

theorem queuedHeadLive_of_cancelled_nil {s : QueuedRwLockConcrete}
    (h : s.cancelled = []) : queuedHeadLive s := by
  intro t c _; rw [h]; simp

/-- **WS-LC LC2.5**: with a live head, "no live request" and "no
outstanding ticket" are the same statement.

The direction that carries content is `→`: a ledger every one of whose
entries is withdrawn would have a withdrawn *head*, which
`queuedHeadLive` forbids.  Without it a lock with three tombstones and
nothing else would look quiescent to the spec while `now_serving` still
had three advances to make. -/
theorem liveLedger_nil_iff_ledger_nil {conc : QueuedRwLockConcrete}
    (hHead : queuedHeadLive conc) : conc.liveLedger = [] ↔ conc.ledger = [] := by
  constructor
  · intro hNil
    cases hL : conc.ledger with
    | nil => rfl
    | cons e rest =>
      exfalso
      have hLive : e.1 ∉ conc.cancelled := by
        refine hHead e.1 e.2 ?_
        rw [hL]; simp
      have : conc.liveLedger = e :: liveOf conc.cancelled rest := by
        show liveOf conc.cancelled conc.ledger = _
        rw [hL, liveOf_cons, if_neg hLive]
      rw [this] at hNil
      exact absurd hNil (by simp)
  · intro hNil; show liveOf conc.cancelled conc.ledger = []; rw [hNil]; rfl

/-- **WS-LC LC2.5**: a live head is the head of the live list. -/
theorem liveLedger_head?_eq {conc : QueuedRwLockConcrete}
    (hHead : queuedHeadLive conc) : conc.liveLedger.head? = conc.ledger.head? := by
  cases hL : conc.ledger with
  | nil => show (liveOf conc.cancelled conc.ledger).head? = _; rw [hL]; rfl
  | cons e rest =>
    have hLive : e.1 ∉ conc.cancelled := by
      refine hHead e.1 e.2 ?_
      rw [hL]; simp
    show (liveOf conc.cancelled conc.ledger).head? = _
    rw [hL, liveOf_cons, if_neg hLive]
    simp

/-- **Witness**: the initial states are related. -/
theorem queuedSim_unheld :
    queuedSim RwLockState.unheld QueuedRwLockConcrete.unheld := by
  refine ⟨?_, QueuedTicketWf.unheld, ?_, ?_, ?_⟩
  · simp [QueuedRwLockConcrete.unheld, encodeRwLock, RwLockState.unheld]
  · simp [QueuedRwLockConcrete.liveLedger, QueuedRwLockConcrete.unheld, liveOf,
      queuedLedgerCores, RwLockState.unheld]
  · intro t c h; simp [QueuedRwLockConcrete.unheld] at h
  · exact ⟨fun c => by simp [QueuedRwLockConcrete.unheld, RwLockState.unheld],
      fun c => by simp [QueuedRwLockConcrete.unheld, RwLockState.unheld]⟩

/-- **WS-RR RR6.6 / WS-LC LC2.5**: the number of **live** requests is the
held writer plus the waiters.

Read off conjunct 3 directly.  The *interval* width — `next_ticket -
now_serving` — is no longer this number: it counts the withdrawn tickets
too, which are outstanding until somebody passes them.  Stating the
figure the spec is about, rather than the one the counters happen to
give, is the whole content of the change. -/
theorem queuedSim_outstanding {abs : RwLockState} {conc : QueuedRwLockConcrete}
    (h : queuedSim abs conc) :
    conc.liveLedger.length = queuedWriterOffset abs + abs.waiters.length := by
  obtain ⟨_, _, hCores, _, _⟩ := h
  have hLen := congrArg List.length hCores
  simpa [queuedLedgerCores_length] using hLen

/-- **WS-LC LC2.5**: and the interval is at least that wide — every live
request holds an outstanding ticket, so the counters can only run
*ahead* of the queue, never behind it. -/
theorem queuedSim_outstanding_le {abs : RwLockState} {conc : QueuedRwLockConcrete}
    (h : queuedSim abs conc) :
    queuedWriterOffset abs + abs.waiters.length
      ≤ conc.nextTicket.toNat - conc.nowServing.toNat := by
  have hOut := queuedSim_outstanding h
  obtain ⟨_, hWf, _, _, _⟩ := h
  have hLive : conc.liveLedger.length ≤ conc.ledger.length :=
    (liveOf_sublist _ _).length_le
  rw [← hOut, ← hWf.ledger_length]
  exact hLive

/-- **WS-RR RR6.6 (unheld characterization)**: nothing is outstanding
exactly when the spec has no writer and no waiters.

Both directions need `queuedHeadLive`: without it a ledger of nothing
but tombstones would satisfy the right-hand side while the lock still
had advances to make. -/
theorem queuedSim_ledger_nil_iff {abs : RwLockState} {conc : QueuedRwLockConcrete}
    (h : queuedSim abs conc) :
    conc.ledger = [] ↔ (abs.writerHeld = none ∧ abs.waiters = []) := by
  obtain ⟨_, _hWf, hCores, hHead, _⟩ := h
  rw [← liveLedger_nil_iff_ledger_nil hHead]
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
    have : conc.liveLedger.map Prod.snd = [] := by
      rw [hCores]; unfold queuedLedgerCores; rw [hW, hQ]; simp
    simpa using this

/-- **Helper (WS-LC LC2.5)**: the ledger's head, when it exists, carries
the served ticket. -/
private theorem ledger_head?_served {conc : QueuedRwLockConcrete}
    (hWf : QueuedTicketWf conc) (hNe : conc.ledger ≠ []) :
    (conc.ledger.map Prod.fst).head? = some conc.nowServing.toNat := by
  rw [hWf.ledgerTickets]
  have hLenPos : 0 < conc.ledger.length := List.length_pos_iff.mpr hNe
  have := hWf.ledger_length
  exact ticketRange_head? _ _ (by omega)

/-- **Helper (WS-LC LC2.5)**: a head whose core is `c` and whose ticket
is the served one **is** `(now_serving, c)`. -/
private theorem ledger_head?_eq_of_core {conc : QueuedRwLockConcrete}
    (hWf : QueuedTicketWf conc) {c : CoreId}
    (hCore : (conc.ledger.map Prod.snd).head? = some c) :
    conc.ledger.head? = some (conc.nowServing.toNat, c) := by
  have hNe : conc.ledger ≠ [] := by
    intro hNil; rw [hNil] at hCore; simp at hCore
  have hTicket := ledger_head?_served hWf hNe
  cases hL : conc.ledger with
  | nil => exact absurd hL hNe
  | cons hd tl =>
    rw [hL, List.map_cons] at hCore hTicket
    simp only [List.head?_cons, Option.some.injEq] at hCore hTicket
    simp only [List.head?_cons, Option.some.injEq]
    exact Prod.ext hTicket hCore

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
  obtain ⟨hState, hWf, hCores, hHead, _⟩ := h
  have hNoReaders : abs.readers = [] := RwLockState.wf_writerReadersExclusion hWfAbs w hW
  have hLiveHead : (conc.liveLedger.map Prod.snd).head? = some w := by
    rw [hCores]; unfold queuedLedgerCores; rw [hW]; rfl
  have hCoresHead : (conc.ledger.map Prod.snd).head? = some w := by
    rw [List.head?_map] at hLiveHead ⊢
    rw [← liveLedger_head?_eq hHead]; exact hLiveHead
  refine ⟨ledger_head?_eq_of_core hWf hCoresHead, ?_⟩
  have : conc.state.toNat = writerBit := by
    rw [hState, hW, hNoReaders]; simp [encodeRwLock]
  apply UInt64.toNat_inj.mp
  rw [this]
  decide

/-- **WS-RR RR6.6 (readers-held characterization)**: with no writer, the
packed word is exactly the reader count, and the **live** ledger's cores
are the waiters. -/
theorem queuedSim_no_writer {abs : RwLockState} {conc : QueuedRwLockConcrete}
    (h : queuedSim abs conc) (hW : abs.writerHeld = none) :
    conc.state.toNat = abs.readers.length ∧
      conc.liveLedger.map Prod.snd = abs.waiters.map Prod.fst := by
  obtain ⟨hState, _, hCores, _, _⟩ := h
  refine ⟨?_, ?_⟩
  · rw [hState, hW]; simp [encodeRwLock]
  · rw [hCores]; unfold queuedLedgerCores; rw [hW]; simp

/-- **WS-RR RR6.6 (head-waiter characterization)**: with no writer, the
head of the queue holds the served ticket — so the core the spec would
promote next is exactly the core the implementation admits next.

This survives the withdrawal unchanged, and `queuedHeadLive` is why: the
served ticket is never a tombstone, so the queue's head and the ledger's
head are the same entry. -/
theorem queuedSim_head_waiter {abs : RwLockState} {conc : QueuedRwLockConcrete}
    (h : queuedSim abs conc) (hW : abs.writerHeld = none)
    {c : CoreId} {m : AccessMode} {rest : List (CoreId × AccessMode)}
    (hQ : abs.waiters = (c, m) :: rest) :
    conc.ledger.head? = some (conc.nowServing.toNat, c) := by
  obtain ⟨_, hWf, hCores, hHead, _⟩ := h
  have hLiveHead : (conc.liveLedger.map Prod.snd).head? = some c := by
    rw [hCores]; unfold queuedLedgerCores; rw [hW, hQ]; rfl
  have hCoresHead : (conc.ledger.map Prod.snd).head? = some c := by
    rw [List.head?_map] at hLiveHead ⊢
    rw [← liveLedger_head?_eq hHead]; exact hLiveHead
  exact ledger_head?_eq_of_core hWf hCoresHead

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

/-- **WS-RR RR6.6 / WS-LC LC2.5 (the FIFO correspondence)**: the `i`-th
abstract waiter is the `i`-th **live** ledger entry after the writer,
and the ticket it holds is outstanding.

This is the payoff of §3 and the reason `queuedSim` is worth more than
`rwLockSim`.  Admission order in the implementation **is** ticket order
— `await_turn` admits `now_serving` and `pass_turn` advances it by one —
so this says the implementation admits waiters in exactly the spec's
queue order.  For the CAS-retry lock the corresponding statement is
false, which is the documented FIFO divergence at `rwLockSim`.

The ticket is no longer computable as `now_serving + writerOffset + i`:
a withdrawal ahead of the waiter leaves an outstanding ticket that
carries no request, so the `i`-th request sits at some ticket *at or
after* that figure.  What matters for FIFO is the **position**, and that
is exact. -/
theorem queuedSim_waiter_ticket {abs : RwLockState} {conc : QueuedRwLockConcrete}
    (h : queuedSim abs conc) {i : Nat} {c : CoreId} {m : AccessMode}
    (hi : abs.waiters[i]? = some (c, m)) :
    ∃ t, conc.liveLedger[queuedWriterOffset abs + i]? = some (t, c) ∧
      conc.nowServing.toNat ≤ t ∧ t < conc.nextTicket.toNat := by
  obtain ⟨_, hWf, hCores, _, _⟩ := h
  have hILt : i < abs.waiters.length := by
    apply Decidable.byContradiction
    intro hc
    rw [List.getElem?_eq_none (by omega)] at hi
    exact absurd hi (by simp)
  have hCoreAt : (conc.liveLedger[queuedWriterOffset abs + i]?).map Prod.snd = some c := by
    rw [← List.getElem?_map, hCores]
    unfold queuedLedgerCores
    rw [List.getElem?_append_right (by rw [queuedWriterPart_length]; omega),
      queuedWriterPart_length]
    have hIdx : queuedWriterOffset abs + i - queuedWriterOffset abs = i := by omega
    rw [hIdx, List.getElem?_map, hi]
    rfl
  cases hAt : conc.liveLedger[queuedWriterOffset abs + i]? with
  | none => rw [hAt] at hCoreAt; simp at hCoreAt
  | some p =>
    rw [hAt] at hCoreAt
    simp only [Option.map_some, Option.some.injEq] at hCoreAt
    refine ⟨p.1, congrArg some (Prod.ext rfl hCoreAt), ?_, ?_⟩ <;>
      · have hMemLive : p ∈ conc.liveLedger := List.mem_of_getElem? hAt
        have hMem : p ∈ conc.ledger := (liveOf_sublist _ _).mem hMemLive
        have := hWf.await_turn_depth (t := p.1) (c := p.2) (by simpa using hMem)
        omega

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
the `debug_assert` read, the count increment, the held word marked
`HELD_READ` (PR #890 review round 2), and `pass_turn`. -/
def readerEnterOps (c : CoreId) (t : Nat) : List QueuedRwLockOp :=
  [.nowServingLoad c, .stateLoad c, .stateFetchAddReader c t, .heldStore c (some .read),
   .nowServingFetchAdd c t, .sev c]

/-- **WS-RR RR6.7**: the tail of `acquire_write` once the core is
served: the CAS from exactly `0`, then the held word marked
`HELD_WRITE`.  The writer keeps its ticket — it is `release_write` that
retires it. -/
def writerEnterOps (c : CoreId) (t : Nat) : List QueuedRwLockOp :=
  [.nowServingLoad c, .stateLoad c, .stateCasAcquireWrite c t, .heldStore c (some .write)]

/-- **PR #890 review round 2**: `release_read`'s ops once the held word
has confirmed the caller holds as a reader — clear the word, leave the
count, wake a parked writer. -/
def releaseReadOps (c : CoreId) : List QueuedRwLockOp :=
  [.heldLoad c, .heldStore c none, .stateFetchSubReader c, .sev c]

-- ----------------------------------------------------------------------------
-- WS-LC LC2.3 — the skip loop
-- ----------------------------------------------------------------------------
--
-- `pass_turn` advances `now_serving` by one.  If the ticket it uncovers has
-- been **withdrawn**, nobody is waiting on it and nobody will pass it on, so
-- the passer keeps going: claim the slot, advance again, repeat.  That loop is
-- what makes a mid-queue withdrawal safe, and it is why the withdrawal cannot
-- simply be dropped from the ledger — the counter still owes an advance for
-- every ticket ever issued.
--
-- The claim is a compare-exchange and it is the **arbiter**: exactly one of
-- {the canceller's own head check, the previous holder's skip loop} clears a
-- given slot, and only that one advances past the ticket.  Modelling the claim
-- as a step that *removes* the ticket from `cancelled` is what makes that
-- exclusion structural here rather than argued.

/-- **WS-LC LC2.3**: the ops that retire the withdrawn tickets sitting at
the head of a ledger, stopping at the first live entry. -/
def skipDeadOps : List Nat → List (Nat × CoreId) → List QueuedRwLockOp
  | _, [] => []
  | cancelled, (t, c) :: rest =>
      if t ∈ cancelled then
        .cancelClaim c t :: .nowServingFetchAdd c t :: skipDeadOps (cancelled.erase t) rest
      else []

/-- **WS-LC LC2.3**: how many entries `skipDeadOps` retires. -/
def deadPrefix : List Nat → List (Nat × CoreId) → Nat
  | _, [] => 0
  | cancelled, (t, _) :: rest =>
      if t ∈ cancelled then deadPrefix (cancelled.erase t) rest + 1 else 0

@[simp] theorem skipDeadOps_nil (cancelled : List Nat) :
    skipDeadOps cancelled [] = [] := rfl

@[simp] theorem deadPrefix_nil (cancelled : List Nat) :
    deadPrefix cancelled [] = 0 := rfl

theorem skipDeadOps_live {cancelled : List Nat} {t : Nat} {c : CoreId}
    {rest : List (Nat × CoreId)} (h : t ∉ cancelled) :
    skipDeadOps cancelled ((t, c) :: rest) = [] := by
  rw [skipDeadOps, if_neg h]

theorem deadPrefix_live {cancelled : List Nat} {t : Nat} {c : CoreId}
    {rest : List (Nat × CoreId)} (h : t ∉ cancelled) :
    deadPrefix cancelled ((t, c) :: rest) = 0 := by
  rw [deadPrefix, if_neg h]

theorem skipDeadOps_dead {cancelled : List Nat} {t : Nat} {c : CoreId}
    {rest : List (Nat × CoreId)} (h : t ∈ cancelled) :
    skipDeadOps cancelled ((t, c) :: rest)
      = [.cancelClaim c t, .nowServingFetchAdd c t]
        ++ skipDeadOps (cancelled.erase t) rest := by
  rw [skipDeadOps, if_pos h]; rfl

theorem deadPrefix_dead {cancelled : List Nat} {t : Nat} {c : CoreId}
    {rest : List (Nat × CoreId)} (h : t ∈ cancelled) :
    deadPrefix cancelled ((t, c) :: rest)
      = deadPrefix (cancelled.erase t) rest + 1 := by
  rw [deadPrefix, if_pos h]

/-- **WS-LC LC2.3**: one retirement's post-state, computed. -/
theorem queuedFoldBlock_skipStep (s : QueuedRwLockConcrete) (t : Nat) (c : CoreId)
    (hDead : t ∈ s.cancelled) :
    queuedFoldBlock s [.cancelClaim c t, .nowServingFetchAdd c t]
      = { s with
            nowServing := s.nowServing + 1
            ledger := s.ledger.tail
            cancelled := s.cancelled.erase t } := by
  show ((s.applyOp (.cancelClaim c t)).1.applyOp (.nowServingFetchAdd c t)).1 = _
  simp only [QueuedRwLockConcrete.applyOp, hDead, if_pos]

/-- **WS-LC LC2.3**: erasing a retired ticket from the withdrawal set
does not resurrect any *other* entry, because a ticket names one ledger
entry (`ledgerTickets` is `Nodup`). -/
theorem liveOf_skipStep {cancelled : List Nat} {t : Nat} {c : CoreId}
    {rest : List (Nat × CoreId)}
    (hNodup : (((t, c) :: rest).map Prod.fst).Nodup) (hDead : t ∈ cancelled) :
    liveOf (cancelled.erase t) rest = liveOf cancelled ((t, c) :: rest) := by
  rw [liveOf_cons, if_pos hDead]
  have hNotIn : t ∉ rest.map Prod.fst := by
    rw [List.map_cons, List.nodup_cons] at hNodup
    exact hNodup.1
  clear hNodup
  induction rest with
  | nil => rfl
  | cons e tl ih =>
    have hNe : e.1 ≠ t := by
      intro hEq; exact hNotIn (by simp [hEq])
    have hTl : t ∉ tl.map Prod.fst := by
      intro hMem
      exact hNotIn (by simp only [List.map_cons, List.mem_cons]; exact Or.inr hMem)
    rw [liveOf_cons, liveOf_cons]
    by_cases hMem : e.1 ∈ cancelled
    · rw [if_pos hMem, if_pos ((List.mem_erase_of_ne hNe).mpr hMem)]
      exact ih hTl
    · rw [if_neg hMem, if_neg (fun hc => hMem (List.mem_of_mem_erase hc))]
      rw [ih hTl]

/-- **WS-LC LC2.3**: one retirement preserves the protocol invariant.

Stated over the claim-and-pass **pair** rather than composed from
`QueuedTicketWf.preserved`, because the pass's own precondition — the
ticket is not withdrawn — is established *by* the claim, and only for
the ticket the claim erased.  Proving the pair keeps that dependency
where it belongs. -/
theorem QueuedTicketWf.skipStep {s : QueuedRwLockConcrete} (hWf : QueuedTicketWf s)
    {t : Nat} {c : CoreId} {rest : List (Nat × CoreId)}
    (hL : s.ledger = (t, c) :: rest) (hDead : t ∈ s.cancelled) :
    QueuedTicketWf (queuedFoldBlock s [.cancelClaim c t, .nowServingFetchAdd c t]) := by
  have hLenEq := hWf.ledger_length
  have hLen : 0 < s.ledger.length := by rw [hL]; simp
  have hLt : s.nowServing.toNat < s.nextTicket.toNat := by omega
  have hSize : s.nextTicket.toNat < UInt64.size := s.nextTicket.toNat_lt_size
  have hServing : (s.nowServing + 1).toNat = s.nowServing.toNat + 1 :=
    uInt64_add_one_toNat _ (by omega)
  rw [queuedFoldBlock_skipStep s t c hDead]
  refine ⟨?_, ?_, ?_, List.Nodup.erase t hWf.cancelledNodup, ?_⟩
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
    rw [hL, List.map_cons, ticketRange_succ] at hTickets
    rw [hL]
    exact (List.cons.inj hTickets).2
  · intro t' ht'
    have hNe : t' ≠ t := fun hEq => hWf.cancelledNodup.not_mem_erase (hEq ▸ ht')
    have hMem := hWf.cancelledOutstanding t' (List.mem_of_mem_erase ht')
    show t' ∈ s.ledger.tail.map Prod.fst
    rw [hL] at hMem ⊢
    simp only [List.map_cons, List.mem_cons, List.tail_cons] at hMem ⊢
    exact hMem.resolve_left hNe
  · have hCores := hWf.ledgerCoresNodup
    rw [hL, List.map_cons, List.nodup_cons] at hCores
    show (s.ledger.tail.map Prod.snd).Nodup
    rw [hL]
    exact hCores.2

/-- **WS-LC LC2.3**: what the skip loop does, in one statement.

Eight facts, and the fifth is the load-bearing one: the **live** ledger is
untouched.  Retiring a tombstone moves `now_serving` and shortens the
ledger, but it removes no request, so `queuedSim`'s queue conjunct is
unaffected — which is exactly what lets a skip be interleaved anywhere a
`pass_turn` uncovers a dead head without disturbing the refinement.  The
seventh says the loop ran to completion: after it, the served ticket is
live again.  The last two say the held words are untouched: a skip is a
ledger operation and moves nobody's holder status (PR #890 review round
2). -/
theorem skipDeadOps_spec :
    ∀ (n : Nat) (s : QueuedRwLockConcrete), s.ledger.length ≤ n → QueuedTicketWf s →
      (queuedFoldBlock s (skipDeadOps s.cancelled s.ledger)).state = s.state ∧
      (queuedFoldBlock s (skipDeadOps s.cancelled s.ledger)).nextTicket = s.nextTicket ∧
      (queuedFoldBlock s (skipDeadOps s.cancelled s.ledger)).ledger
        = s.ledger.drop (deadPrefix s.cancelled s.ledger) ∧
      (queuedFoldBlock s (skipDeadOps s.cancelled s.ledger)).nowServing.toNat
        = s.nowServing.toNat + deadPrefix s.cancelled s.ledger ∧
      (queuedFoldBlock s (skipDeadOps s.cancelled s.ledger)).liveLedger = s.liveLedger ∧
      QueuedTicketWf (queuedFoldBlock s (skipDeadOps s.cancelled s.ledger)) ∧
      queuedHeadLive (queuedFoldBlock s (skipDeadOps s.cancelled s.ledger)) ∧
      (queuedFoldBlock s (skipDeadOps s.cancelled s.ledger)).heldRead = s.heldRead ∧
      (queuedFoldBlock s (skipDeadOps s.cancelled s.ledger)).heldWrite = s.heldWrite := by
  intro n
  induction n with
  | zero =>
    intro s hn hWf
    have hNil : s.ledger = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hOps : skipDeadOps s.cancelled s.ledger = [] := by rw [hNil]; rfl
    have hPre : deadPrefix s.cancelled s.ledger = 0 := by rw [hNil]; rfl
    rw [hOps, hPre, queuedFoldBlock_nil]
    refine ⟨rfl, rfl, by rw [hNil]; rfl, by omega, rfl, hWf, ?_, rfl, rfl⟩
    intro t c h; rw [hNil] at h; simp at h
  | succ m ih =>
    intro s hn hWf
    by_cases hHeadDead : ∃ t c rest, s.ledger = (t, c) :: rest ∧ t ∈ s.cancelled
    · obtain ⟨t, c, rest, hL, hDead⟩ := hHeadDead
      obtain ⟨s', hs'⟩ :
          ∃ x, x = queuedFoldBlock s [.cancelClaim c t, .nowServingFetchAdd c t] :=
        ⟨_, rfl⟩
      have hStep : s' = { s with
          nowServing := s.nowServing + 1
          ledger := s.ledger.tail
          cancelled := s.cancelled.erase t } := by
        rw [hs']; exact queuedFoldBlock_skipStep s t c hDead
      have hWf' : QueuedTicketWf s' := by rw [hs']; exact hWf.skipStep hL hDead
      have hLedger' : s'.ledger = rest := by rw [hStep]; simp [hL]
      have hCancelled' : s'.cancelled = s.cancelled.erase t := by rw [hStep]
      have hLen' : s'.ledger.length ≤ m := by
        rw [hLedger']
        have hEq : s.ledger.length = rest.length + 1 := by rw [hL]; simp
        omega
      obtain ⟨hS, hN, hLg, hNow, hLive, hWfPost, hHead, hHR, hHW⟩ := ih s' hLen' hWf'
      have hUnfold : skipDeadOps s.cancelled s.ledger
          = [.cancelClaim c t, .nowServingFetchAdd c t]
            ++ skipDeadOps s'.cancelled s'.ledger := by
        rw [hL, skipDeadOps_dead hDead, hLedger', hCancelled']
      have hFold : queuedFoldBlock s (skipDeadOps s.cancelled s.ledger)
          = queuedFoldBlock s' (skipDeadOps s'.cancelled s'.ledger) := by
        rw [hUnfold, queuedFoldBlock_append, hs']
      have hDeadPre : deadPrefix s.cancelled s.ledger
          = deadPrefix s'.cancelled s'.ledger + 1 := by
        rw [hL, deadPrefix_dead hDead, hLedger', hCancelled']
      have hNowStep : s'.nowServing.toNat = s.nowServing.toNat + 1 := by
        have hLenEq := hWf.ledger_length
        have hLenPos : 0 < s.ledger.length := by rw [hL]; simp
        have hSize : s.nextTicket.toNat < UInt64.size := s.nextTicket.toNat_lt_size
        rw [hStep]
        exact uInt64_add_one_toNat _ (by omega)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hFold, hS, hStep]
      · rw [hFold, hN, hStep]
      · rw [hFold, hLg, hDeadPre, hLedger', hL, List.drop_succ_cons]
      · rw [hFold, hNow, hNowStep, hDeadPre]; omega
      · rw [hFold, hLive]
        show liveOf s'.cancelled s'.ledger = liveOf s.cancelled s.ledger
        rw [hCancelled', hLedger']
        have hNodup : (s.ledger.map Prod.fst).Nodup := hWf.ledger_tickets_nodup
        rw [hL] at hNodup
        rw [hL]
        exact liveOf_skipStep hNodup hDead
      · rw [hFold]; exact hWfPost
      · rw [hFold]; exact hHead
      · rw [hFold, hHR, hStep]
      · rw [hFold, hHW, hStep]
    · -- Either the ledger is empty or its head is live: nothing to skip.
      have hOps : skipDeadOps s.cancelled s.ledger = [] := by
        cases hL : s.ledger with
        | nil => rfl
        | cons hd rest =>
          obtain ⟨t, c⟩ := hd
          have hLive : t ∉ s.cancelled := fun hc => hHeadDead ⟨t, c, rest, hL, hc⟩
          exact skipDeadOps_live hLive
      have hPre : deadPrefix s.cancelled s.ledger = 0 := by
        cases hL : s.ledger with
        | nil => rfl
        | cons hd rest =>
          obtain ⟨t, c⟩ := hd
          have hLive : t ∉ s.cancelled := fun hc => hHeadDead ⟨t, c, rest, hL, hc⟩
          exact deadPrefix_live hLive
      rw [hOps, hPre, queuedFoldBlock_nil]
      refine ⟨rfl, rfl, by simp, by omega, rfl, hWf, ?_, rfl, rfl⟩
      intro t' c' h hc
      refine hHeadDead ⟨t', c', s.ledger.tail, ?_, hc⟩
      cases hL : s.ledger with
      | nil => rw [hL] at h; simp at h
      | cons hd rest =>
        rw [hL] at h
        simp only [List.head?_cons, Option.some.injEq] at h
        rw [← h]
        simp

/-- **WS-RR RR6.7**: `release_write`'s own ops — clear the writer bit,
then hand the ticket on.  That order is required: a reader served by the
next ticket must not observe `WRITER_BIT` still set. -/
def releaseWriteOps (c : CoreId) (t : Nat) : List QueuedRwLockOp :=
  [.heldLoad c, .heldStore c none, .stateFetchAndReaderMask c, .nowServingFetchAdd c t, .sev c]

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
            heldRead := conc.heldRead.filter (· ≠ c) ++ [c]
            heldWrite := conc.heldWrite.filter (· ≠ c)
            nowServing := conc.nowServing + 1
            ledger := conc.ledger.tail } := rfl

theorem queuedFoldBlock_writerEnterOps_of_zero (conc : QueuedRwLockConcrete)
    (c : CoreId) (t : Nat) (hZero : conc.state = 0) :
    queuedFoldBlock conc (writerEnterOps c t)
      = { conc with
            state := writerBit.toUInt64
            heldRead := conc.heldRead.filter (· ≠ c)
            heldWrite := conc.heldWrite.filter (· ≠ c) ++ [c] } := by
  simp [queuedFoldBlock, writerEnterOps, QueuedRwLockConcrete.applyOp, hZero]

theorem queuedFoldBlock_releaseReadOps (conc : QueuedRwLockConcrete) (c : CoreId) :
    queuedFoldBlock conc (releaseReadOps c)
      = { conc with
            state := conc.state - 1
            heldRead := conc.heldRead.filter (· ≠ c)
            heldWrite := conc.heldWrite.filter (· ≠ c) } := rfl

theorem queuedFoldBlock_releaseWriteOps (conc : QueuedRwLockConcrete)
    (c : CoreId) (t : Nat) :
    queuedFoldBlock conc (releaseWriteOps c t)
      = { conc with
            state := conc.state &&& readerMask.toUInt64
            heldRead := conc.heldRead.filter (· ≠ c)
            heldWrite := conc.heldWrite.filter (· ≠ c)
            nowServing := conc.nowServing + 1
            ledger := conc.ledger.tail } := rfl

/-- Membership in a core's own removal from a held set. -/
theorem mem_filter_ne_core {l : List CoreId} {x c : CoreId} :
    x ∈ l.filter (· ≠ c) ↔ x ∈ l ∧ x ≠ c := by
  simp [List.mem_filter]

/-- A single held-word load is a stutter: the branch it decides is
carried by the block's shape, not by the op. -/
theorem heldLoad_stutter (c : CoreId) : QueuedStutter [.heldLoad c] := by
  simp [QueuedStutter, QueuedRwLockOp.isObservation]

/-- **WS-LC LC2.3**: a served reader's entry preserves the protocol
invariant.

The same shape as `QueuedTicketWf.skipStep` and for the same reason: the
pass's precondition — the ticket is not withdrawn — is available here
from the *head being live*, which is a fact about this state rather than
about the operation. -/
theorem QueuedTicketWf.readerEnterStep {s : QueuedRwLockConcrete}
    (hWf : QueuedTicketWf s) {t : Nat} {c : CoreId} {rest : List (Nat × CoreId)}
    (hL : s.ledger = (t, c) :: rest) (hLive : t ∉ s.cancelled) :
    QueuedTicketWf (queuedFoldBlock s (readerEnterOps c t)) := by
  have hLenEq := hWf.ledger_length
  have hLen : 0 < s.ledger.length := by rw [hL]; simp
  have hLt : s.nowServing.toNat < s.nextTicket.toNat := by omega
  have hSize : s.nextTicket.toNat < UInt64.size := s.nextTicket.toNat_lt_size
  have hServing : (s.nowServing + 1).toNat = s.nowServing.toNat + 1 :=
    uInt64_add_one_toNat _ (by omega)
  rw [queuedFoldBlock_readerEnterOps]
  refine ⟨?_, ?_, ?_, hWf.cancelledNodup, ?_⟩
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
    rw [hL, List.map_cons, ticketRange_succ] at hTickets
    rw [hL]
    exact (List.cons.inj hTickets).2
  · intro t' ht'
    have hNe : t' ≠ t := fun hEq => hLive (hEq ▸ ht')
    have hMem := hWf.cancelledOutstanding t' ht'
    show t' ∈ s.ledger.tail.map Prod.fst
    rw [hL] at hMem ⊢
    simp only [List.map_cons, List.mem_cons, List.tail_cons] at hMem ⊢
    exact hMem.resolve_left hNe
  · have hCores := hWf.ledgerCoresNodup
    rw [hL, List.map_cons, List.nodup_cons] at hCores
    show (s.ledger.tail.map Prod.snd).Nodup
    rw [hL]
    exact hCores.2

/-- **WS-LC LC2.3**: admit a run of served readers, retiring any
tombstone that comes up in front of one.

The state-threaded replacement for the old consecutive-ticket family,
which assigned the promoted readers tickets `t, t+1, …`.  That was right
while every outstanding ticket carried a request; a withdrawal in the
middle of the queue falsifies it, and the reader that would have taken
the withdrawn ticket is a different core from the one the spec promotes.
Reading the ticket and the core off the ledger instead makes the
correspondence hold by construction.

Each iteration begins with the skip, including the last: the skip
belongs to the *preceding* `pass_turn`'s loop, so a run of `n` readers
performs `n + 1` of them. -/
def readerAdmitFrom (conc : QueuedRwLockConcrete) : Nat → List QueuedRwLockOp
  | 0 => skipDeadOps conc.cancelled conc.ledger
  | n + 1 =>
      let skip := skipDeadOps conc.cancelled conc.ledger
      let mid := queuedFoldBlock conc skip
      match mid.ledger with
      | [] => skip
      | (t, c) :: _ =>
          skip ++ readerEnterOps c t
            ++ readerAdmitFrom (queuedFoldBlock mid (readerEnterOps c t)) n

/-- The unfolding equation, with the `let`s expanded so a proof can
rewrite the skip's post-state before matching on its ledger. -/
theorem readerAdmitFrom_succ (conc : QueuedRwLockConcrete) (k : Nat) :
    readerAdmitFrom conc (k + 1)
      = (match (queuedFoldBlock conc (skipDeadOps conc.cancelled conc.ledger)).ledger with
         | [] => skipDeadOps conc.cancelled conc.ledger
         | (t, c) :: _ =>
             skipDeadOps conc.cancelled conc.ledger ++ readerEnterOps c t
               ++ readerAdmitFrom
                    (queuedFoldBlock
                      (queuedFoldBlock conc (skipDeadOps conc.cancelled conc.ledger))
                      (readerEnterOps c t)) k) := rfl

/-- **Helper**: a list's `takeWhile` prefix is its `take` of that length. -/
private theorem take_length_takeWhile {α : Type} (p : α → Bool) (l : List α) :
    l.take (l.takeWhile p).length = l.takeWhile p := by
  have hSplit : l.takeWhile p ++ l.dropWhile p = l := List.takeWhile_append_dropWhile
  generalize l.takeWhile p = tw at hSplit ⊢
  generalize l.dropWhile p = dw at hSplit
  rw [← hSplit]
  exact List.take_left

/-- **WS-LC LC2.3**: what admitting a run of readers does.

The third conjunct is the one the refinement consumes: `n` **live**
entries leave the queue, whatever number of tombstones were retired
alongside them.  The last two (PR #890 review round 2) say what the held
words do: the `n` admitted cores — the first `n` live entries' — are
marked as readers, and nothing else moves. -/
theorem readerAdmitFrom_spec :
    ∀ (n : Nat) (conc : QueuedRwLockConcrete), QueuedTicketWf conc →
      n ≤ conc.liveLedger.length → conc.state.toNat + n < UInt64.size →
      (queuedFoldBlock conc (readerAdmitFrom conc n)).state.toNat
        = conc.state.toNat + n ∧
      (queuedFoldBlock conc (readerAdmitFrom conc n)).nextTicket = conc.nextTicket ∧
      (queuedFoldBlock conc (readerAdmitFrom conc n)).liveLedger
        = conc.liveLedger.drop n ∧
      QueuedTicketWf (queuedFoldBlock conc (readerAdmitFrom conc n)) ∧
      queuedHeadLive (queuedFoldBlock conc (readerAdmitFrom conc n)) ∧
      (∀ x, x ∈ (queuedFoldBlock conc (readerAdmitFrom conc n)).heldRead
        ↔ x ∈ conc.heldRead ∨ x ∈ (conc.liveLedger.take n).map Prod.snd) ∧
      (∀ x, x ∈ (queuedFoldBlock conc (readerAdmitFrom conc n)).heldWrite
        ↔ x ∈ conc.heldWrite ∧ x ∉ (conc.liveLedger.take n).map Prod.snd) := by
  intro n
  induction n with
  | zero =>
    intro conc hWf _ _
    obtain ⟨hS, hN, _, _, hLive, hWfP, hHead, hHR, hHW⟩ :=
      skipDeadOps_spec conc.ledger.length conc (Nat.le_refl _) hWf
    have hDef : readerAdmitFrom conc 0 = skipDeadOps conc.cancelled conc.ledger := rfl
    rw [hDef]
    exact ⟨by rw [hS]; omega, hN, by rw [hLive]; simp, hWfP, hHead,
      fun x => by rw [hHR]; simp, fun x => by rw [hHW]; simp⟩
  | succ k ih =>
    intro conc hWf hLen hSize
    obtain ⟨hS, hN, _, _, hLiveEq, hWfMid, hHeadMid, hHRMid, hHWMid⟩ :=
      skipDeadOps_spec conc.ledger.length conc (Nat.le_refl _) hWf
    obtain ⟨mid, hmid⟩ :
        ∃ x, x = queuedFoldBlock conc (skipDeadOps conc.cancelled conc.ledger) := ⟨_, rfl⟩
    rw [← hmid] at hS hN hLiveEq hWfMid hHeadMid hHRMid hHWMid
    have hMidNe : mid.ledger ≠ [] := by
      intro hNil
      have hEmpty : mid.liveLedger = [] := (liveLedger_nil_iff_ledger_nil hHeadMid).mpr hNil
      rw [hLiveEq] at hEmpty
      rw [hEmpty] at hLen
      simp at hLen
    cases hML : mid.ledger with
    | nil => exact absurd hML hMidNe
    | cons hd rest =>
      obtain ⟨t, c⟩ := hd
      have hTLive : t ∉ mid.cancelled := hHeadMid t c (by rw [hML]; simp)
      obtain ⟨conc₁, h₁⟩ :
          ∃ x, x = queuedFoldBlock mid (readerEnterOps c t) := ⟨_, rfl⟩
      have hStep₁ : conc₁ = { mid with
          state := mid.state + 1
          heldRead := mid.heldRead.filter (· ≠ c) ++ [c]
          heldWrite := mid.heldWrite.filter (· ≠ c)
          nowServing := mid.nowServing + 1
          ledger := mid.ledger.tail } := by
        rw [h₁]; exact queuedFoldBlock_readerEnterOps _ _ _
      have hWf₁ : QueuedTicketWf conc₁ := by
        rw [h₁]; exact hWfMid.readerEnterStep hML hTLive
      have hMidLive : mid.liveLedger = (t, c) :: conc₁.liveLedger := by
        show liveOf mid.cancelled mid.ledger = _
        rw [hML, liveOf_cons, if_neg hTLive]
        congr 1
        show liveOf mid.cancelled rest = liveOf conc₁.cancelled conc₁.ledger
        rw [hStep₁]; simp [hML]
      have hUnfold : readerAdmitFrom conc (k + 1)
          = skipDeadOps conc.cancelled conc.ledger
            ++ readerEnterOps c t ++ readerAdmitFrom conc₁ k := by
        rw [readerAdmitFrom_succ, ← hmid, hML]
        show skipDeadOps conc.cancelled conc.ledger ++ readerEnterOps c t
               ++ readerAdmitFrom (queuedFoldBlock mid (readerEnterOps c t)) k = _
        rw [← h₁]
      have hFold : queuedFoldBlock conc (readerAdmitFrom conc (k + 1))
          = queuedFoldBlock conc₁ (readerAdmitFrom conc₁ k) := by
        rw [hUnfold, queuedFoldBlock_append, queuedFoldBlock_append, ← hmid, ← h₁]
      have hState₁ : conc₁.state.toNat = conc.state.toNat + 1 := by
        rw [hStep₁]
        show (mid.state + 1).toNat = _
        rw [uInt64_add_one_toNat _ (by rw [hS]; omega), hS]
      have hLen₁ : k ≤ conc₁.liveLedger.length := by
        have hL1 : mid.liveLedger.length = conc₁.liveLedger.length + 1 := by
          rw [hMidLive]; simp
        rw [hLiveEq] at hL1; omega
      have hHeld₁R : conc₁.heldRead = conc.heldRead.filter (· ≠ c) ++ [c] := by
        rw [hStep₁, hHRMid]
      have hHeld₁W : conc₁.heldWrite = conc.heldWrite.filter (· ≠ c) := by
        rw [hStep₁, hHWMid]
      have hTake : conc.liveLedger.take (k + 1) = (t, c) :: conc₁.liveLedger.take k := by
        rw [← hLiveEq, hMidLive, List.take_succ_cons]
      obtain ⟨hSk, hNk, hLivek, hWfk, hHeadk, hHRk, hHWk⟩ := ih conc₁ hWf₁ hLen₁ (by omega)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hFold, hSk, hState₁]; omega
      · rw [hFold, hNk, hStep₁, hN]
      · rw [hFold, hLivek, ← hLiveEq, hMidLive]; simp
      · rw [hFold]; exact hWfk
      · rw [hFold]; exact hHeadk
      · intro x
        rw [hFold, hHRk x, hHeld₁R, hTake]
        by_cases hxc : x = c <;> simp [hxc]
      · intro x
        rw [hFold, hHWk x, hHeld₁W, hTake]
        by_cases hxc : x = c <;> simp [hxc]

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

/-- **WS-LC LC2.3**: the concrete ops that carry out the abstract
promotion, read off the **ledger** rather than computed from the served
ticket.

The state-threaded replacement for `promoteOps`.  Its three branches
mirror `promoteWaitersOnWriterRelease`'s exactly — nothing queued, a
writer at the head admitted alone, or a run of readers admitted together
— and each opens with the skip loop, which is empty at a block boundary
(`queuedHeadLive`) and does the work when a `pass_turn` inside the reader
run uncovers a tombstone. -/
def promoteFrom (conc : QueuedRwLockConcrete)
    (waiters : List (CoreId × AccessMode)) : List QueuedRwLockOp :=
  match waiters with
  | [] => skipDeadOps conc.cancelled conc.ledger
  | (w, .write) :: _ =>
      let skip := skipDeadOps conc.cancelled conc.ledger
      let mid := queuedFoldBlock conc skip
      match mid.ledger with
      | [] => skip
      | (t, _) :: _ => skip ++ writerEnterOps w t
  | (_, .read) :: _ =>
      readerAdmitFrom conc (waiters.takeWhile (fun x => x.2 = .read)).length

/-- **WS-RR RR6.7 / WS-LC LC2.4 (the promotion block)**: from a quiescent
sim-related pair, the concrete promotion block reaches the state the
abstract promotion produces.

This is the release blocks' second half and the reason a release block
cannot stop at `fetch_and` + `pass_turn`: the spec's release **is** a
promotion, and between the two the concrete lock has admitted nobody
while the abstract has.  All three of the abstract helper's branches are
covered — nothing queued, a writer at the head (admitted alone, keeping
its ticket, so the ledger head stays), and a run of readers (admitted
together, each retiring its own ticket, and retiring any tombstone
uncovered between two of them).

The two held-word hypotheses (PR #890 review round 2) are the
quiescence stated on the concrete side: nobody's word reads held, which
`queuedHeldSim` gives from `hW` and `hR` at both call sites.  They are
taken as hypotheses rather than derived here because the releasing core
has just cleared its own word, and it is the *post*-clear state that is
quiescent. -/
theorem promoteFrom_preserves_queuedSim
    {abs : RwLockState} {conc : QueuedRwLockConcrete}
    (hState : conc.state.toNat = encodeRwLock abs.writerHeld.isSome abs.readers.length)
    (hWf : QueuedTicketWf conc)
    (hCores : conc.liveLedger.map Prod.snd = queuedLedgerCores abs)
    (hWaitersBound : abs.waiters.length ≤ numCores)
    (hW : abs.writerHeld = none) (hR : abs.readers = [])
    (hHeldR : ∀ x, x ∉ conc.heldRead) (hHeldW : ∀ x, x ∉ conc.heldWrite) :
    queuedSim abs.promoteWaitersOnWriterRelease
      (queuedFoldBlock conc (promoteFrom conc abs.waiters)) := by
  -- **No `queuedHeadLive` on entry.**  A promotion is reached through a
  -- `pass_turn`, which uncovers a head that may be a tombstone — so the
  -- skip loop that opens every branch here is exactly what restores it,
  -- and demanding it as a hypothesis would make this lemma unusable at
  -- the one place it is used.
  obtain ⟨hSkS, hSkN, _, _, hSkLive, hSkWf, hSkHead, hSkHR, hSkHW⟩ :=
    skipDeadOps_spec conc.ledger.length conc (Nat.le_refl _) hWf
  obtain ⟨mid, hmid⟩ :
      ∃ x, x = queuedFoldBlock conc (skipDeadOps conc.cancelled conc.ledger) := ⟨_, rfl⟩
  rw [← hmid] at hSkS hSkN hSkLive hSkWf hSkHead hSkHR hSkHW
  have hMidCores : mid.liveLedger.map Prod.snd = queuedLedgerCores abs := by
    rw [hSkLive]; exact hCores
  have hStateZero : conc.state = 0 := by
    apply UInt64.toNat_inj.mp
    rw [hState, hW, hR]
    simp [encodeRwLock]
  have hMidStateZero : mid.state = 0 := by rw [hSkS]; exact hStateZero
  have hCoresQ : mid.liveLedger.map Prod.snd = abs.waiters.map Prod.fst := by
    rw [hMidCores]; unfold queuedLedgerCores; rw [hW]; simp
  have hLiveLen : mid.liveLedger.length = abs.waiters.length := by
    have := congrArg List.length hCoresQ; simpa using this
  cases hQ : abs.waiters with
  | nil =>
    rw [promote_noop_on_empty_waiters abs hQ, ← hQ]
    have hOps : promoteFrom conc abs.waiters
        = skipDeadOps conc.cancelled conc.ledger := by rw [promoteFrom.eq_def, hQ]
    rw [hOps, ← hmid]
    refine ⟨by rw [hSkS]; exact hState, hSkWf, hMidCores, hSkHead, ?_⟩
    -- Nothing is admitted, so nobody's word moves: both sides stay empty.
    refine ⟨fun x => ?_, fun x => ?_⟩
    · rw [hSkHR, hR]; simp [hHeldR x]
    · rw [hSkHW, hW]; simp [hHeldW x]
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
      have hLiveNe : mid.liveLedger ≠ [] := by
        intro hNil; rw [hNil, hQ] at hCoresQ; simp at hCoresQ
      have hLedgerNe : mid.ledger ≠ [] := fun hNil =>
        hLiveNe ((liveLedger_nil_iff_ledger_nil hSkHead).mpr hNil)
      have hLedgerHead : mid.ledger.head? = some (mid.nowServing.toNat, c) := by
        refine ledger_head?_eq_of_core hSkWf ?_
        rw [List.head?_map, ← liveLedger_head?_eq hSkHead, ← List.head?_map, hCoresQ, hQ]
        rfl
      have hOps : promoteFrom conc abs.waiters
          = skipDeadOps conc.cancelled conc.ledger
            ++ writerEnterOps c mid.nowServing.toNat := by
        rw [promoteFrom.eq_def, hQ]
        show (match (queuedFoldBlock conc (skipDeadOps conc.cancelled conc.ledger)).ledger with
              | [] => skipDeadOps conc.cancelled conc.ledger
              | (t, _) :: _ => skipDeadOps conc.cancelled conc.ledger
                  ++ writerEnterOps c t) = _
        rw [← hmid]
        cases hL : mid.ledger with
        | nil => exact absurd hL hLedgerNe
        | cons e rest =>
          rw [hL] at hLedgerHead
          simp only [List.head?_cons, Option.some.injEq] at hLedgerHead
          show skipDeadOps conc.cancelled conc.ledger ++ writerEnterOps c e.1 = _
          rw [congrArg Prod.fst hLedgerHead]
      rw [hPromote, hOps, queuedFoldBlock_append, ← hmid,
        queuedFoldBlock_writerEnterOps_of_zero _ _ _ hMidStateZero]
      refine ⟨?_, (hSkWf.copy rfl rfl rfl rfl), ?_, ?_, ?_⟩
      · show (writerBit.toUInt64).toNat = encodeRwLock (some c).isSome abs.readers.length
        rw [hR]
        simp only [Option.isSome_some, encodeRwLock, if_true, List.length_nil, Nat.add_zero]
        decide
      · show (liveOf mid.cancelled mid.ledger).map Prod.snd = queuedLedgerCores _
        rw [show liveOf mid.cancelled mid.ledger = mid.liveLedger from rfl, hCoresQ, hQ]
        unfold queuedLedgerCores
        simp
      · exact hSkHead
      · -- The admitted writer's word now reads `HELD_WRITE`, and nobody
        -- else's moved.
        refine ⟨fun x => ?_, fun x => ?_⟩
        · show x ∈ mid.heldRead.filter (· ≠ c) ↔ x ∈ abs.readers
          rw [hSkHR, hR]; simp [hHeldR x]
        · show x ∈ mid.heldWrite.filter (· ≠ c) ++ [c] ↔ some c = some x
          rw [hSkHW]
          simp only [List.mem_append, mem_filter_ne_core, List.mem_singleton,
            Option.some.injEq]
          constructor
          · rintro (⟨hx, _⟩ | hx)
            · exact absurd hx (hHeldW x)
            · exact hx.symm
          · intro hx; exact Or.inr hx.symm
    | read =>
      -- A run of readers is admitted together; each retires its own
      -- ticket at entry, and any tombstone uncovered in between is
      -- retired with it.
      rw [← hQ]
      have hPromote : abs.promoteWaitersOnWriterRelease
          = { abs with
                readers := (abs.waiters.takeWhile (fun w => w.2 = .read)).map Prod.fst
                  ++ abs.readers
                waiters := abs.waiters.dropWhile (fun w => w.2 = .read) } := by
        unfold RwLockState.promoteWaitersOnWriterRelease; rw [hQ]
      have hOps : promoteFrom conc abs.waiters
          = readerAdmitFrom conc (abs.waiters.takeWhile (fun w => w.2 = .read)).length := by
        rw [promoteFrom.eq_def, hQ]
      have hSplit : (abs.waiters.takeWhile (fun w => w.2 = .read))
          ++ (abs.waiters.dropWhile (fun w => w.2 = .read)) = abs.waiters :=
        List.takeWhile_append_dropWhile
      have hKle : (abs.waiters.takeWhile (fun w => w.2 = .read)).length
          ≤ abs.waiters.length := by
        have := congrArg List.length hSplit
        simp only [List.length_append] at this
        omega
      have hStateNat : conc.state.toNat = 0 := by rw [hStateZero]; rfl
      have hSizeBound : (numCores : Nat) < UInt64.size := by decide
      have hConcLiveLen : conc.liveLedger.length = abs.waiters.length := by
        rw [← hSkLive]; exact hLiveLen
      obtain ⟨hS, hN, hLive, hWfP, hHeadP, hHR, hHW⟩ :=
        readerAdmitFrom_spec (abs.waiters.takeWhile (fun w => w.2 = .read)).length conc hWf
          (by omega) (by omega)
      have hConcCoresQ : conc.liveLedger.map Prod.snd = abs.waiters.map Prod.fst := by
        rw [hSkLive] at hCoresQ; exact hCoresQ
      -- The admitted cores are the reader run: the first `n` live entries'
      -- cores are the first `n` waiters', and those are the `takeWhile`.
      have hPromoted :
          (conc.liveLedger.take (abs.waiters.takeWhile (fun w => w.2 = .read)).length).map
              Prod.snd
            = (abs.waiters.takeWhile (fun w => w.2 = .read)).map Prod.fst := by
        rw [List.map_take, hConcCoresQ, ← List.map_take, take_length_takeWhile]
      rw [hPromote, hOps]
      refine ⟨?_, hWfP, ?_, hHeadP, ?_⟩
      · rw [hS, hStateNat, hR]
        simp [encodeRwLock, hW]
      · rw [hLive, map_drop_comm]
        rw [hConcCoresQ]
        unfold queuedLedgerCores
        simp only [hW, List.nil_append]
        have hLenEq : (abs.waiters.takeWhile (fun w => w.2 = .read)).length
            = ((abs.waiters.takeWhile (fun w => w.2 = .read)).map Prod.fst).length := by simp
        rw [hLenEq, ← hSplit, List.map_append]
        simp
      · refine ⟨fun x => ?_, fun x => ?_⟩
        · rw [hHR x, hPromoted]
          show x ∈ conc.heldRead ∨ x ∈ _
              ↔ x ∈ (abs.waiters.takeWhile (fun w => w.2 = .read)).map Prod.fst
                  ++ abs.readers
          rw [hR]; simp [hHeldR x]
        · rw [hHW x, hPromoted]
          show x ∈ conc.heldWrite ∧ x ∉ _ ↔ abs.writerHeld = some x
          rw [hW]; simp [hHeldW x]

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

**Every acquire and release opens with the caller's held-word load**
(PR #890 review round 2), because that is what the implementation does
before anything else, and the branch it decides is the block's shape:
the four `_noop` shapes are that one load and nothing after it, so the
spec's no-op and the implementation's are the same execution rather
than a stutter asserted of a path that did not exist.  A core with a
**queued** request is involved on the spec side and not a holder, and
has no acquire block at all: it is inside its own acquisition, or holds
a split-API ticket it must terminate first, so the one-outstanding-
ticket contract (`ledgerCoresNodup`) is what rules the call out, not a
branch in the implementation.

`hNoWrap` is the ticket-headroom side condition.  It is the ~584-year
wraparound bound the module docstring names, stated rather than assumed
away: at one acquisition per nanosecond a `u64` ticket counter takes
that long to reach it. -/
inductive queuedBlock :
    RwLockState → QueuedRwLockConcrete → RwLockOp → List QueuedRwLockOp → Prop where
  /-- A holder re-acquiring: its word reads held, and `acquire_read`
  returns on that load — the spec's no-op for an involved core. -/
  | acquireRead_noop (abs conc c) :
      (c ∈ abs.readers ∨ abs.writerHeld = some c) →
      queuedBlock abs conc (.tryAcquireRead c) [.heldLoad c]
  /-- `acquire_read` on a calm lock: the word reads free; take ticket,
  await turn (no-one ahead), join the count, pass the ticket on. -/
  | acquireRead_admit (abs conc c spin) :
      ¬ abs.coreInvolved c → abs.writerHeld = none → abs.waiters = [] →
      QueuedStutter spin → conc.nextTicket.toNat + 1 < UInt64.size →
      queuedBlock abs conc (.tryAcquireRead c)
        (.heldLoad c :: (takeTicketOps c ++ spin ++ readerEnterOps c conc.nextTicket.toNat))
  /-- `acquire_read` behind a holder or a queued waiter: take a ticket
  and spin.  The block ends in `await_turn`, which is exactly what the
  spec's enqueue models.

  **The core's withdrawal slot must be empty** (WS-LC closure audit):
  `enqueue` parks until it is, so a block that issued a ticket over a
  pending withdrawal would describe an execution the implementation
  refuses — and the one on which, before the wait existed, it lost the
  withdrawal and stalled.  On a calm lock nothing is published, so the
  `_admit` shapes need no such hypothesis. -/
  | acquireRead_enqueue (abs conc c spin) :
      ¬ abs.coreInvolved c → (abs.writerHeld.isSome ∨ abs.waiters ≠ []) →
      QueuedStutter spin → conc.nextTicket.toNat + 1 < UInt64.size →
      ¬ conc.withdrawalPending c →
      queuedBlock abs conc (.tryAcquireRead c) (.heldLoad c :: (takeTicketOps c ++ spin))
  /-- A holder re-acquiring as a writer: the same one load. -/
  | acquireWrite_noop (abs conc c) :
      (c ∈ abs.readers ∨ abs.writerHeld = some c) →
      queuedBlock abs conc (.tryAcquireWrite c) [.heldLoad c]
  /-- `acquire_write` on a calm lock: take ticket, await turn, CAS from
  exactly `0`.  The writer keeps its ticket until it releases. -/
  | acquireWrite_admit (abs conc c spin) :
      ¬ abs.coreInvolved c → abs.writerHeld = none → abs.readers = [] →
      abs.waiters = [] → QueuedStutter spin →
      conc.nextTicket.toNat + 1 < UInt64.size →
      queuedBlock abs conc (.tryAcquireWrite c)
        (.heldLoad c :: (takeTicketOps c ++ spin ++ writerEnterOps c conc.nextTicket.toNat))
  /-- `acquire_write` behind a holder or a queued waiter. -/
  | acquireWrite_enqueue (abs conc c spin) :
      ¬ abs.coreInvolved c →
      (abs.writerHeld.isSome ∨ abs.readers ≠ [] ∨ abs.waiters ≠ []) →
      QueuedStutter spin → conc.nextTicket.toNat + 1 < UInt64.size →
      ¬ conc.withdrawalPending c →
      queuedBlock abs conc (.tryAcquireWrite c) (.heldLoad c :: (takeTicketOps c ++ spin))
  /-- **WS-LC LC2.6**: a core with no queued request withdrawing is a
  spec no-op, and the implementation publishes nothing. -/
  | cancel_noop (abs conc c spin) :
      (∀ m, (c, m) ∉ abs.waiters) → QueuedStutter spin →
      queuedBlock abs conc (.cancel c) spin
  /-- **WS-LC LC2.6**: `cancel` — publish the withdrawal, then run the
  skip loop.

  **One shape covers both cases the implementation branches on**, and
  publishing first is what makes it so.  If the withdrawing core was not
  the head, the served ticket is still live and the loop is empty:
  "publish and return", with somebody ahead skipping the ticket when they
  pass their turn.  If it *was* the head, its own ticket is now a
  tombstone and the loop retires it — and any that follow.  So the head
  check in `queued_rw_lock.rs` is the loop's first iteration rather than a
  separate path, which is also why the publish may not be moved after it.

  The ticket is required to be `c`'s **live** one: a core that has already
  withdrawn has nothing left to withdraw, and the concrete block would
  otherwise retire a ticket the spec no longer has a request for.

  The block opens with the two loads `cancel` performs before it
  publishes — the caller's held word, which for a holder ends the call
  (PR #890 review round 3), and the served counter, which for a retired
  ticket does — so a withdrawal that reaches the publish is one by a core
  holding nothing, which is what `opEnabled` requires of the publish. -/
  | cancel_queued (abs conc c t spin) :
      (∃ m, (c, m) ∈ abs.waiters) → (t, c) ∈ conc.liveLedger →
      QueuedStutter spin →
      queuedBlock abs conc (.cancel c)
        (.heldLoad c :: .nowServingLoad c :: .cancelPublish c t
          :: spin ++ skipDeadOps (conc.cancelled ++ [t]) conc.ledger)
  /-- Releasing a read lock one does not hold: the word does not read
  `HELD_READ`, and `release_read` returns on that load — the spec's
  no-op.  The two-phase-locking unwind (`unwindAll`) relies on exactly
  this identity at every footprint member the core did not hold. -/
  | releaseRead_noop (abs conc c) :
      c ∉ abs.readers → queuedBlock abs conc (.releaseRead c) [.heldLoad c]
  /-- `release_read` leaving other holders (or a writer) behind: the
  word is cleared, the count drops and nobody is promoted. -/
  | releaseRead_noPromote (abs conc c) :
      c ∈ abs.readers →
      (abs.readers.filter (· ≠ c) ≠ [] ∨ abs.writerHeld.isSome) →
      queuedBlock abs conc (.releaseRead c) (releaseReadOps c)
  /-- `release_read` draining the lock: the count drops to zero and the
  block carries the promotion the spec performs. -/
  | releaseRead_promote (abs conc c) :
      c ∈ abs.readers → abs.readers.filter (· ≠ c) = [] → abs.writerHeld = none →
      queuedBlock abs conc (.releaseRead c)
        (releaseReadOps c
          ++ promoteFrom (queuedFoldBlock conc (releaseReadOps c)) abs.waiters)
  /-- Releasing a write lock one does not hold: the word does not read
  `HELD_WRITE`, and `release_write` returns on that load. -/
  | releaseWrite_noop (abs conc c) :
      abs.writerHeld ≠ some c → queuedBlock abs conc (.releaseWrite c) [.heldLoad c]
  /-- `release_write`: clear the word, clear the writer bit, hand the
  ticket on, and carry the promotion.  The order of the bit clear and
  the pass is the implementation's and is required — a reader served by
  the next ticket must not observe `WRITER_BIT` still set. -/
  | releaseWrite_effective (abs conc c) :
      abs.writerHeld = some c →
      queuedBlock abs conc (.releaseWrite c)
        (releaseWriteOps c conc.nowServing.toNat
          ++ promoteFrom
              (queuedFoldBlock conc (releaseWriteOps c conc.nowServing.toNat))
              abs.waiters)

/-- **Helper**: `take_ticket` preserves the protocol invariant, for a
core holding no outstanding ticket. -/
theorem QueuedTicketWf.takeTicket {conc : QueuedRwLockConcrete}
    (hWf : QueuedTicketWf conc) (c : CoreId)
    (hNoWrap : conc.nextTicket.toNat + 1 < UInt64.size)
    (hFree : ¬ conc.holdsTicket c) :
    QueuedTicketWf (queuedFoldBlock conc (takeTicketOps c)) := by
  rw [queuedFoldBlock_takeTicketOps]
  have hStep := hWf.preserved (.nextTicketFetchAdd c) ⟨hNoWrap, hFree⟩
  exact (hStep.copy rfl rfl rfl rfl)

/-- **WS-LC closure audit**: a core the spec has neither holding nor
queued, with no withdrawal pending, holds no ticket at all — the issue's
precondition, assembled from one fact on each side of the relation.  A
ledger entry of `c` is either live, in which case `queuedSim`'s queue
conjunct puts `c` among the spec's holders and waiters, or withdrawn, in
which case it is a pending withdrawal. -/
theorem queuedSim_not_holdsTicket {abs : RwLockState} {conc : QueuedRwLockConcrete}
    {c : CoreId} (hSim : queuedSim abs conc) (hNotInv : ¬ abs.coreInvolved c)
    (hNoPending : ¬ conc.withdrawalPending c) : ¬ conc.holdsTicket c := by
  intro hHold
  obtain ⟨e, hE, hEc⟩ := List.mem_map.mp hHold
  by_cases hDead : e.1 ∈ conc.cancelled
  · exact hNoPending ⟨e.1, hDead, by rw [← hEc]; exact hE⟩
  · have hLive : e ∈ conc.liveLedger := mem_liveOf.mpr ⟨hE, hDead⟩
    have hCore : c ∈ conc.liveLedger.map Prod.snd := List.mem_map.mpr ⟨e, hLive, hEc⟩
    rw [hSim.2.2.1] at hCore
    unfold queuedLedgerCores at hCore
    apply hNotInv
    unfold RwLockState.coreInvolved
    rcases List.mem_append.mp hCore with hW | hQ
    · right; left
      cases hWH : abs.writerHeld with
      | none => rw [hWH] at hW; simp at hW
      | some w => rw [hWH] at hW; simp at hW; rw [hW]
    · right; right; exact hQ

-- ----------------------------------------------------------------------------
-- Per-block step lemmas, one per entry point
-- ----------------------------------------------------------------------------

/-- The holder check at the head of every acquire and release is a load:
the fold passes through it. -/
theorem queuedFoldBlock_heldLoad_cons (conc : QueuedRwLockConcrete) (c : CoreId)
    (rest : List QueuedRwLockOp) :
    queuedFoldBlock conc (.heldLoad c :: rest) = queuedFoldBlock conc rest := rfl

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
        (.heldLoad c :: (takeTicketOps c ++ spin ++ readerEnterOps c conc.nextTicket.toNat))) := by
  have hLedgerNil : conc.ledger = [] := (queuedSim_ledger_nil_iff hSim).mpr ⟨hW, hQ⟩
  obtain ⟨hState, hWf, hCores, hHeadLive, hHeld⟩ := hSim
  have hCancNil : conc.cancelled = [] := hWf.cancelled_nil_of_ledger_nil hLedgerNil
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
  rw [queuedFoldBlock_heldLoad_cons, queuedFoldBlock_append, queuedFoldBlock_append,
    queuedFoldBlock_takeTicketOps, queuedFoldBlock_stutter _ _ hSpin,
    queuedFoldBlock_readerEnterOps]
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
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
  · intro t' ht'; rw [hCancNil] at ht'; simp at ht'
  · rw [hCancNil]; simp
  · rw [hLedgerNil]; simp
  · show (liveOf conc.cancelled ((conc.ledger ++ [(conc.nextTicket.toNat, c)]).tail)).map
          Prod.snd = queuedLedgerCores (abs.applyOp (.tryAcquireRead c))
    rw [hCancNil, liveOf_nil_cancelled, hLedgerNil]
    unfold queuedLedgerCores
    rw [hShape.2.1, hShape.2.2, hW, hQ]
    simp
  · exact queuedHeadLive_of_cancelled_nil (by rw [hCancNil])
  · -- The admitted reader's word reads `HELD_READ`; the writer word is
    -- untouched and, with no abstract writer, reads nothing.
    refine ⟨fun x => ?_, fun x => ?_⟩
    · show x ∈ conc.heldRead.filter (· ≠ c) ++ [c] ↔ x ∈ (abs.applyOp (.tryAcquireRead c)).readers
      rw [hShape.1]
      by_cases hxc : x = c <;> simp [hxc, hHeld.1 x]
    · show x ∈ conc.heldWrite.filter (· ≠ c) ↔ (abs.applyOp (.tryAcquireRead c)).writerHeld = some x
      rw [hShape.2.1, hW]
      simp [hHeld.not_heldWrite hW x]

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
    (hNoWrap : conc.nextTicket.toNat + 1 < UInt64.size)
    (hNoPending : ¬ conc.withdrawalPending c) :
    queuedSim (abs.applyOp (.tryAcquireRead c))
      (queuedFoldBlock conc (.heldLoad c :: (takeTicketOps c ++ spin))) := by
  have hFree : ¬ conc.holdsTicket c := queuedSim_not_holdsTicket hSim hNotInv hNoPending
  obtain ⟨hState, hWf, hCores, hHeadLive, hHeld⟩ := hSim
  have hPost : abs.applyOp (.tryAcquireRead c)
      = { abs with waiters := abs.waiters ++ [(c, AccessMode.read)] } := by
    unfold RwLockState.applyOp
    simp only [hNotInv, ↓reduceIte]
    have : (abs.writerHeld.isSome = true ∨ abs.waiters ≠ []) := hBusy
    simp [this]
  have hWfPost := hWf.takeTicket c hNoWrap hFree
  rw [queuedFoldBlock_heldLoad_cons, queuedFoldBlock_append, queuedFoldBlock_takeTicketOps,
    queuedFoldBlock_stutter _ _ hSpin]
  rw [queuedFoldBlock_takeTicketOps] at hWfPost
  have hFresh : conc.nextTicket.toNat ∉ conc.cancelled := hWf.nextTicket_not_cancelled
  refine ⟨?_, hWfPost, ?_, ?_, ?_⟩
  · rw [hPost]; exact hState
  · -- The issued ticket is fresh, so it joins the **live** ledger.
    show (liveOf conc.cancelled (conc.ledger ++ [(conc.nextTicket.toNat, c)])).map Prod.snd
        = queuedLedgerCores (abs.applyOp (.tryAcquireRead c))
    rw [liveOf_append, List.map_append,
      show liveOf conc.cancelled conc.ledger = conc.liveLedger from rfl, hCores,
      liveOf_cons, if_neg hFresh]
    rw [hPost]
    unfold queuedLedgerCores
    simp [List.append_assoc]
  · -- Appending cannot make the head withdrawn: either it is unchanged,
    -- or the ledger was empty and the new head is the fresh ticket.
    intro t' c' hHd
    cases hL : conc.ledger with
    | nil =>
      rw [hL] at hHd
      simp only [List.nil_append, List.head?_cons, Option.some.injEq, Prod.mk.injEq] at hHd
      rw [← hHd.1]; exact hFresh
    | cons e rest =>
      refine hHeadLive t' c' ?_
      rw [hL] at hHd ⊢
      simpa using hHd
  · -- Taking a ticket moves no held word and no abstract holder.
    rw [hPost]
    exact hHeld.copy rfl rfl rfl rfl


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
        (.heldLoad c :: (takeTicketOps c ++ spin ++ writerEnterOps c conc.nextTicket.toNat))) := by
  have hLedgerNil : conc.ledger = [] := (queuedSim_ledger_nil_iff hSim).mpr ⟨hW, hQ⟩
  obtain ⟨hState, hWf, hCores, hHeadLive, hHeld⟩ := hSim
  have hCancNil : conc.cancelled = [] := hWf.cancelled_nil_of_ledger_nil hLedgerNil
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
        = { queuedFoldBlock conc (takeTicketOps c) with
              state := writerBit.toUInt64
              heldRead := conc.heldRead.filter (· ≠ c)
              heldWrite := conc.heldWrite.filter (· ≠ c) ++ [c] } :=
    queuedFoldBlock_writerEnterOps_of_zero _ _ _
      (by rw [queuedFoldBlock_takeTicketOps]; exact hStateZero)
  rw [queuedFoldBlock_heldLoad_cons, queuedFoldBlock_append, queuedFoldBlock_append,
    queuedFoldBlock_stutter _ _ hSpin, hFoldWriter, queuedFoldBlock_takeTicketOps]
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
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
  · intro t' ht'; rw [hCancNil] at ht'; simp at ht'
  · rw [hCancNil]; simp
  · rw [hLedgerNil]; simp
  · show (liveOf conc.cancelled (conc.ledger ++ [(conc.nextTicket.toNat, c)])).map Prod.snd
        = queuedLedgerCores (abs.applyOp (.tryAcquireWrite c))
    rw [hCancNil, liveOf_nil_cancelled, hLedgerNil]
    unfold queuedLedgerCores
    rw [hShape.1, hShape.2.2, hQ]
    simp
  · exact queuedHeadLive_of_cancelled_nil (by rw [hCancNil])
  · -- The admitted writer's word reads `HELD_WRITE`; with no abstract
    -- reader, no reader word was set to begin with.
    refine ⟨fun x => ?_, fun x => ?_⟩
    · show x ∈ conc.heldRead.filter (· ≠ c) ↔ x ∈ (abs.applyOp (.tryAcquireWrite c)).readers
      rw [hShape.2.1, hR]
      simp [hHeld.not_heldRead hR x]
    · show x ∈ conc.heldWrite.filter (· ≠ c) ++ [c]
          ↔ (abs.applyOp (.tryAcquireWrite c)).writerHeld = some x
      rw [hShape.1]
      simp only [List.mem_append, mem_filter_ne_core, List.mem_singleton, Option.some.injEq]
      constructor
      · rintro (⟨hx, _⟩ | hx)
        · exact absurd hx (hHeld.not_heldWrite hW x)
        · exact hx.symm
      · intro hx; exact Or.inr hx.symm

/-- **WS-RR RR6.7 (`acquire_write`, enqueued)**. -/
theorem queuedBlock_step_acquireWrite_enqueue
    {abs : RwLockState} {conc : QueuedRwLockConcrete} {c : CoreId}
    {spin : List QueuedRwLockOp}
    (hSim : queuedSim abs conc)
    (hNotInv : ¬ abs.coreInvolved c)
    (hBusy : abs.writerHeld.isSome ∨ abs.readers ≠ [] ∨ abs.waiters ≠ [])
    (hSpin : QueuedStutter spin)
    (hNoWrap : conc.nextTicket.toNat + 1 < UInt64.size)
    (hNoPending : ¬ conc.withdrawalPending c) :
    queuedSim (abs.applyOp (.tryAcquireWrite c))
      (queuedFoldBlock conc (.heldLoad c :: (takeTicketOps c ++ spin))) := by
  have hFree : ¬ conc.holdsTicket c := queuedSim_not_holdsTicket hSim hNotInv hNoPending
  obtain ⟨hState, hWf, hCores, hHeadLive, hHeld⟩ := hSim
  have hPost : abs.applyOp (.tryAcquireWrite c)
      = { abs with waiters := abs.waiters ++ [(c, AccessMode.write)] } := by
    unfold RwLockState.applyOp
    simp only [hNotInv, ↓reduceIte]
    have : (abs.writerHeld.isSome = true ∨ abs.readers ≠ [] ∨ abs.waiters ≠ []) := hBusy
    simp [this]
  have hWfPost := hWf.takeTicket c hNoWrap hFree
  rw [queuedFoldBlock_heldLoad_cons, queuedFoldBlock_append, queuedFoldBlock_takeTicketOps,
    queuedFoldBlock_stutter _ _ hSpin]
  rw [queuedFoldBlock_takeTicketOps] at hWfPost
  have hFresh : conc.nextTicket.toNat ∉ conc.cancelled := hWf.nextTicket_not_cancelled
  refine ⟨?_, hWfPost, ?_, ?_, ?_⟩
  · rw [hPost]; exact hState
  · -- The issued ticket is fresh, so it joins the **live** ledger.
    show (liveOf conc.cancelled (conc.ledger ++ [(conc.nextTicket.toNat, c)])).map Prod.snd
        = queuedLedgerCores (abs.applyOp (.tryAcquireWrite c))
    rw [liveOf_append, List.map_append,
      show liveOf conc.cancelled conc.ledger = conc.liveLedger from rfl, hCores,
      liveOf_cons, if_neg hFresh]
    rw [hPost]
    unfold queuedLedgerCores
    simp [List.append_assoc]
  · -- Appending cannot make the head withdrawn: either it is unchanged,
    -- or the ledger was empty and the new head is the fresh ticket.
    intro t' c' hHd
    cases hL : conc.ledger with
    | nil =>
      rw [hL] at hHd
      simp only [List.nil_append, List.head?_cons, Option.some.injEq, Prod.mk.injEq] at hHd
      rw [← hHd.1]; exact hFresh
    | cons e rest =>
      refine hHeadLive t' c' ?_
      rw [hL] at hHd ⊢
      simpa using hHd
  · rw [hPost]
    exact hHeld.copy rfl rfl rfl rfl


/-- **WS-RR RR6.7 (`release_read`, no promotion)**: the word is cleared,
the count drops and nobody is admitted. -/
theorem queuedBlock_step_releaseRead_noPromote
    {abs : RwLockState} {conc : QueuedRwLockConcrete} {c : CoreId}
    (hSim : queuedSim abs conc) (hWfAbs : abs.wf)
    (hHolder : c ∈ abs.readers)
    (hNoPromote : abs.readers.filter (· ≠ c) ≠ [] ∨ abs.writerHeld.isSome = true) :
    queuedSim (abs.applyOp (.releaseRead c))
      (queuedFoldBlock conc (releaseReadOps c)) := by
  obtain ⟨hState, hWf, hCores, hHeadLive, hHeld⟩ := hSim
  have hLenStep : (abs.readers.filter (· ≠ c)).length + 1 = abs.readers.length :=
    filter_ne_length_of_nodup abs.readers hWfAbs.2.1 c hHolder
  have hPost : abs.applyOp (.releaseRead c)
      = ({ writerHeld := abs.writerHeld, readers := abs.readers.filter (· ≠ c),
           waiters := abs.waiters } : RwLockState) := by
    rw [releaseRead_effective_post abs c hHolder]
    exact promoteWaitersIfReadersEmpty_noop _ hNoPromote
  have hGe : 1 ≤ conc.state.toNat := by
    rw [hState]; exact encodeRwLock_at_least_one_when_reader abs c hHolder
  -- A reader is never the writer (INV-R1), so clearing `c`'s word cannot
  -- touch a `HELD_WRITE` the relation would still have to account for.
  have hNotWriter : abs.writerHeld ≠ some c := by
    intro hWc
    have hEmpty := RwLockState.wf_writerReadersExclusion hWfAbs c hWc
    rw [hEmpty] at hHolder
    simp at hHolder
  rw [queuedFoldBlock_releaseReadOps, hPost]
  refine ⟨?_, (hWf.copy rfl rfl rfl rfl), hCores, hHeadLive, ?_⟩
  · show (conc.state - 1).toNat
        = encodeRwLock abs.writerHeld.isSome (abs.readers.filter (· ≠ c)).length
    have hFilterLen : (abs.readers.filter (· ≠ c)).length = abs.readers.length - 1 := by omega
    have hPos : 1 ≤ abs.readers.length := by omega
    rw [uInt64_sub_one_toNat' _ hGe, hState, hFilterLen]
    unfold encodeRwLock
    cases hW : abs.writerHeld.isSome with
    | true => simp only [if_true]; omega
    | false => simp only [Bool.false_eq_true, if_false]; omega
  · refine ⟨fun x => ?_, fun x => ?_⟩
    · show x ∈ conc.heldRead.filter (· ≠ c) ↔ x ∈ abs.readers.filter (· ≠ c)
      simp only [mem_filter_ne_core, hHeld.1 x]
    · show x ∈ conc.heldWrite.filter (· ≠ c) ↔ abs.writerHeld = some x
      rw [mem_filter_ne_core, hHeld.2 x]
      constructor
      · exact And.left
      · intro hx
        refine ⟨hx, ?_⟩
        intro hxc
        exact hNotWriter (hxc ▸ hx)

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
        (releaseReadOps c
          ++ promoteFrom (queuedFoldBlock conc (releaseReadOps c)) abs.waiters)) := by
  obtain ⟨hState, hWf, hCores, hHeadLive, hHeld⟩ := hSim
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
  rw [hPost, queuedFoldBlock_append, queuedFoldBlock_releaseReadOps]
  refine promoteFrom_preserves_queuedSim
    (abs := { writerHeld := abs.writerHeld, readers := [], waiters := abs.waiters })
    ?_ (hWf.copy rfl rfl rfl rfl) hCores hWaitersBound hW rfl ?_ ?_
  · show (conc.state - 1).toNat = encodeRwLock abs.writerHeld.isSome ([] : List CoreId).length
    rw [uInt64_sub_one_toNat' _ (by omega), hStateOne, hW]
    simp [encodeRwLock]
  · -- `c` was the only reader, and its word is now clear.
    intro x hx
    rw [mem_filter_ne_core, hHeld.1 x] at hx
    have hMem : x ∈ abs.readers.filter (· ≠ c) := mem_filter_ne_core.mpr hx
    rw [hFilterNil] at hMem
    simp at hMem
  · intro x hx
    exact hHeld.not_heldWrite hW x (mem_filter_ne_core.mp hx).1


/-- **WS-RR RR6.7 (`release_write`)**: clear the word and the writer bit,
hand the ticket on, and admit whoever the spec promotes.

The order of the bit clear and the pass is the implementation's and is
required: a reader served by the next ticket must not observe
`WRITER_BIT` still set.  The block then carries the promotion, for the
same reason as the draining `release_read`. -/
theorem queuedBlock_step_releaseWrite
    {abs : RwLockState} {conc : QueuedRwLockConcrete} {c : CoreId}
    (hSim : queuedSim abs conc) (hWfAbs : abs.wf) (hW : abs.writerHeld = some c) :
    queuedSim (abs.applyOp (.releaseWrite c))
      (queuedFoldBlock conc
        (releaseWriteOps c conc.nowServing.toNat
          ++ promoteFrom
              (queuedFoldBlock conc (releaseWriteOps c conc.nowServing.toNat))
              abs.waiters)) := by
  obtain ⟨hHead, hStateW⟩ := queuedSim_writer_held hSim hWfAbs hW
  obtain ⟨hState, hWf, hCores, hHeadLive, hHeld⟩ := hSim
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
            heldRead := conc.heldRead.filter (· ≠ c)
            heldWrite := conc.heldWrite.filter (· ≠ c)
            nowServing := conc.nowServing + 1
            ledger := conc.ledger.tail } := by
    rw [queuedFoldBlock_releaseWriteOps, hStateW]
    have hMask : writerBit.toUInt64 &&& readerMask.toUInt64 = 0 := by decide
    rw [hMask]
  have hWfMid : QueuedTicketWf
      { conc with
          state := 0
          heldRead := conc.heldRead.filter (· ≠ c)
          heldWrite := conc.heldWrite.filter (· ≠ c)
          nowServing := conc.nowServing + 1
          ledger := conc.ledger.tail } := by
    have hServedLive : conc.nowServing.toNat ∉ conc.cancelled := hHeadLive _ c hHead
    have hStep :=
      hWf.preserved (.nowServingFetchAdd c conc.nowServing.toNat) ⟨hHead, rfl, hServedLive⟩
    exact (hStep.copy rfl rfl rfl rfl)
  have hServedLive' : conc.nowServing.toNat ∉ conc.cancelled := hHeadLive _ c hHead
  have hCoresMidLive :
      (liveOf conc.cancelled conc.ledger.tail).map Prod.snd = abs.waiters.map Prod.fst := by
    have hLive : conc.liveLedger
        = (conc.nowServing.toNat, c) :: liveOf conc.cancelled conc.ledger.tail := by
      show liveOf conc.cancelled conc.ledger = _
      rw [hLedgerCons, liveOf_cons, if_neg hServedLive']
      simp
    rw [hLive] at hCores
    unfold queuedLedgerCores at hCores
    rw [hW] at hCores
    simp only [List.map_cons, List.cons_append] at hCores
    exact (List.cons.inj hCores).2
  rw [hPost, queuedFoldBlock_append, hFold]
  refine promoteFrom_preserves_queuedSim
    (abs := { writerHeld := none, readers := abs.readers, waiters := abs.waiters })
    ?_ hWfMid ?_ hWaitersBound rfl hNoReaders ?_ ?_
  · show (0 : UInt64).toNat = encodeRwLock (none : Option CoreId).isSome abs.readers.length
    rw [hNoReaders]; simp [encodeRwLock]
  · show (liveOf conc.cancelled conc.ledger.tail).map Prod.snd
        = queuedLedgerCores
            { writerHeld := none
              readers := abs.readers
              waiters := abs.waiters }
    rw [hCoresMidLive]
    unfold queuedLedgerCores
    simp
  · -- A writer excludes readers (INV-R1), so no reader word was set.
    intro x hx
    exact hHeld.not_heldRead hNoReaders x (mem_filter_ne_core.mp hx).1
  · -- The only `HELD_WRITE` word was `c`'s, and it is now clear.
    intro x hx
    rw [mem_filter_ne_core, hHeld.2 x, hW] at hx
    exact hx.2 (Option.some.inj hx.1).symm


/-- **Helper (WS-LC LC2.6)**: filtering on a component and then mapping
it out is mapping and then filtering. -/
private theorem filter_map_snd_comm (l : List (Nat × CoreId)) (c : CoreId) :
    (l.filter (fun e => decide (e.2 ≠ c))).map Prod.snd
      = (l.map Prod.snd).filter (fun x => decide (x ≠ c)) := by
  induction l with
  | nil => rfl
  | cons e rest ih =>
    rw [List.filter_cons, List.map_cons, List.filter_cons]
    by_cases h : e.2 = c
    · rw [if_neg (by simp [h]), if_neg (by simp [h])]
      exact ih
    · rw [if_pos (by simp [h]), if_pos (by simp [h]), List.map_cons, ih]

private theorem filter_map_fst_comm (l : List (CoreId × AccessMode)) (c : CoreId) :
    (l.filter (fun w => decide (w.1 ≠ c))).map Prod.fst
      = (l.map Prod.fst).filter (fun x => decide (x ≠ c)) := by
  induction l with
  | nil => rfl
  | cons e rest ih =>
    rw [List.filter_cons, List.map_cons, List.filter_cons]
    by_cases h : e.1 = c
    · rw [if_neg (by simp [h]), if_neg (by simp [h])]
      exact ih
    · rw [if_pos (by simp [h]), if_pos (by simp [h]), List.map_cons, ih]

/-- **WS-LC LC2.6 (`cancel`, not queued)**: withdrawing a request one
does not have changes nothing on either side. -/
theorem queuedBlock_step_cancel_noop
    {abs : RwLockState} {conc : QueuedRwLockConcrete} {c : CoreId}
    {spin : List QueuedRwLockOp}
    (hSim : queuedSim abs conc) (hNotQueued : ∀ m, (c, m) ∉ abs.waiters)
    (hSpin : QueuedStutter spin) :
    queuedSim (abs.applyOp (.cancel c)) (queuedFoldBlock conc spin) := by
  have hFilter : abs.waiters.filter (fun w => w.1 ≠ c) = abs.waiters := by
    refine List.filter_eq_self.mpr ?_
    intro w hw
    simp only [decide_eq_true_eq, ne_eq]
    intro hEq
    exact hNotQueued w.2 (by rw [← hEq]; simpa using hw)
  have hPost : abs.applyOp (.cancel c) = abs := by
    show { abs with waiters := abs.waiters.filter (fun w => w.1 ≠ c) } = abs
    rw [hFilter]
  rw [hPost, queuedFoldBlock_stutter _ _ hSpin]
  exact hSim

/-- **Helper (WS-LC LC2.6)**: inside the live ledger, "this is ticket `t`"
and "this is core `c`" name the same entry.

Both directions are needed and each rests on a different `Nodup`: tickets
are distinct because `ledgerTickets` is an interval, and *live* cores are
distinct because they are the spec's held writer followed by its waiters,
which INV-R3 and INV-R4 keep distinct. -/
private theorem liveLedger_ticket_iff_core {conc : QueuedRwLockConcrete}
    (hWf : QueuedTicketWf conc) (hCoresNodup : (conc.liveLedger.map Prod.snd).Nodup)
    {t : Nat} {c : CoreId} (hMem : (t, c) ∈ conc.liveLedger)
    {e : Nat × CoreId} (hE : e ∈ conc.liveLedger) : (e.1 = t) = (e.2 = c) := by
  have hLedgerMem : ∀ {x : Nat × CoreId}, x ∈ conc.liveLedger → x ∈ conc.ledger :=
    fun hx => (liveOf_sublist _ _).mem hx
  refine propext ⟨?_, ?_⟩
  · intro hEq
    exact hWf.ticket_holder_unique (t := t) (c₁ := e.2) (c₂ := c)
      (by rw [← hEq]; simpa using hLedgerMem hE) (hLedgerMem hMem)
  · intro hEq
    -- Two live entries carrying the same core are the same entry, because
    -- the live cores are `Nodup`.
    rw [eq_of_snd_eq_of_nodup hCoresNodup hE hMem (by simpa using hEq)]

/-- **WS-LC LC2.6 (`cancel`, queued)**: the publish removes exactly the
withdrawing core's request, and the skip loop that follows leaves the
served ticket live again. -/
theorem queuedBlock_step_cancel_queued
    {abs : RwLockState} {conc : QueuedRwLockConcrete} {c : CoreId} {t : Nat}
    {spin : List QueuedRwLockOp}
    (hSim : queuedSim abs conc) (hWfAbs : abs.wf)
    (hQueued : ∃ m, (c, m) ∈ abs.waiters) (hLive : (t, c) ∈ conc.liveLedger)
    (hSpin : QueuedStutter spin) :
    queuedSim (abs.applyOp (.cancel c))
      (queuedFoldBlock conc
        (.heldLoad c :: .nowServingLoad c :: .cancelPublish c t
          :: spin ++ skipDeadOps (conc.cancelled ++ [t]) conc.ledger)) := by
  obtain ⟨hState, hWf, hCores, _, hHeld⟩ := hSim
  obtain ⟨hMemLedger, hNotCancelled⟩ := mem_liveOf.mp hLive
  -- A queued core holds nothing (INV-R4), so its word reads clear on both
  -- sides of the relation — the publish's precondition.
  have hNotHolding : c ∉ conc.heldRead ∧ c ∉ conc.heldWrite := by
    obtain ⟨m, hmQ⟩ := hQueued
    have hR4 := RwLockState.wf_waitersDisjointFromHolders hWfAbs (c, m) hmQ
    exact ⟨fun hx => hR4.1 ((hHeld.1 c).mp hx), fun hx => hR4.2 ((hHeld.2 c).mp hx)⟩
  have hPub : (conc.applyOp (.cancelPublish c t)).1
      = { conc with cancelled := conc.cancelled ++ [t] } := rfl
  obtain ⟨p, hp⟩ : ∃ x, x = { conc with cancelled := conc.cancelled ++ [t] } := ⟨_, rfl⟩
  have hWfP : QueuedTicketWf p := by
    rw [hp, ← hPub]
    exact hWf.preserved (.cancelPublish c t)
      ⟨hMemLedger, hNotCancelled, hNotHolding.1, hNotHolding.2⟩
  have hPLive : p.liveLedger = conc.liveLedger.filter (fun e => decide (e.1 ≠ t)) := by
    rw [hp]; exact liveOf_publish _ _ _
  obtain ⟨hSkS, hSkN, _, _, hSkLive, hSkWf, hSkHead, hSkHR, hSkHW⟩ :=
    skipDeadOps_spec p.ledger.length p (Nat.le_refl _) hWfP
  have hFold : queuedFoldBlock conc
      (.heldLoad c :: .nowServingLoad c :: .cancelPublish c t
        :: spin ++ skipDeadOps (conc.cancelled ++ [t]) conc.ledger)
      = queuedFoldBlock p (skipDeadOps p.cancelled p.ledger) := by
    show queuedFoldBlock (conc.applyOp (.cancelPublish c t)).1
        (spin ++ skipDeadOps (conc.cancelled ++ [t]) conc.ledger) = _
    rw [hPub, queuedFoldBlock_append, queuedFoldBlock_stutter _ _ hSpin, ← hp]
    congr 1 <;> rw [hp]
  have hCoresNodup : (conc.liveLedger.map Prod.snd).Nodup := by
    rw [hCores]
    unfold queuedLedgerCores
    have hR3 := RwLockState.wf_waitersCoresNodup hWfAbs
    have hR4 := RwLockState.wf_waitersDisjointFromHolders hWfAbs
    cases hW : abs.writerHeld with
    | none => simpa using hR3
    | some w =>
      simp only [List.singleton_append, List.nodup_cons]
      refine ⟨?_, hR3⟩
      intro hMemW
      obtain ⟨e, heMem, heEq⟩ := List.mem_map.mp hMemW
      exact (hR4 e heMem).2 (by rw [hW, heEq])
  have hAbsPost : abs.applyOp (.cancel c)
      = { abs with waiters := abs.waiters.filter (fun w => w.1 ≠ c) } := rfl
  rw [hFold, hAbsPost]
  refine ⟨?_, hSkWf, ?_, hSkHead, ?_⟩
  · rw [hSkS, hp]; exact hState
  · rw [hSkLive, hPLive]
    have hCongr : conc.liveLedger.filter (fun e => decide (e.1 ≠ t))
        = conc.liveLedger.filter (fun e => decide (e.2 ≠ c)) := by
      refine List.filter_congr ?_
      intro e he
      have hIff := liveLedger_ticket_iff_core hWf hCoresNodup hLive he
      simp only [ne_eq, decide_not, hIff]
    rw [hCongr, filter_map_snd_comm, hCores]
    unfold queuedLedgerCores
    have hR4 := RwLockState.wf_waitersDisjointFromHolders hWfAbs
    cases hW : abs.writerHeld with
    | none =>
      simp only [List.nil_append]
      rw [← filter_map_fst_comm]
    | some w =>
      obtain ⟨m, hmQ⟩ := hQueued
      have hWne : w ≠ c := by
        intro hEq
        exact (hR4 (c, m) hmQ).2 (by rw [hW, hEq])
      simp only [List.singleton_append, List.filter_cons]
      rw [if_pos (by simpa using hWne)]
      simp only [List.cons.injEq, true_and]
      rw [← filter_map_fst_comm]
  · -- Neither the publish nor the skip loop moves a held word, and a
    -- withdrawal moves no abstract holder.
    exact hHeld.copy (by rw [hSkHR, hp]) (by rw [hSkHW, hp]) rfl rfl

/-- **WS-RR RR6.7 (the per-block step theorem)**: every block shape
carries the simulation across its abstract operation.

The case analysis is over `queuedBlock`'s constructors, so a
constructor added later is a **missing case** rather than a silent gap
— the same derivation-not-enumeration discipline the CAS-retry
refinement's `opCorresponds` coverage needs (WS-RR RR6.17).

The four `_noop` cases are where `queuedHeldSim` pays (PR #890 review
round 2): each block is the caller's held-word load and nothing else,
and the abstract side no-ops on exactly the fact the relation pins that
word to, so both sides stand still together — derived, not assumed. -/
theorem queuedBlock_preserves_queuedSim
    {abs : RwLockState} {conc : QueuedRwLockConcrete} {op : RwLockOp}
    {blk : List QueuedRwLockOp}
    (hSim : queuedSim abs conc) (hWfAbs : abs.wf)
    (hBlk : queuedBlock abs conc op blk) :
    queuedSim (abs.applyOp op) (queuedFoldBlock conc blk) := by
  cases hBlk with
  | acquireRead_noop c hHolder =>
    have hInv : abs.coreInvolved c := by
      unfold RwLockState.coreInvolved
      rcases hHolder with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    rw [RwLockState.applyOp_noop_acquireRead hInv,
      queuedFoldBlock_stutter _ _ (heldLoad_stutter c)]
    exact hSim
  | acquireRead_admit c spin hNotInv hW hQ hSpin _hNoWrap =>
    exact queuedBlock_step_acquireRead_admit hSim hWfAbs hNotInv hW hQ hSpin
  | acquireRead_enqueue c spin hNotInv hBusy hSpin hNoWrap hNoPending =>
    exact queuedBlock_step_acquireRead_enqueue hSim hNotInv hBusy hSpin hNoWrap hNoPending
  | acquireWrite_noop c hHolder =>
    have hInv : abs.coreInvolved c := by
      unfold RwLockState.coreInvolved
      rcases hHolder with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    rw [RwLockState.applyOp_noop_acquireWrite hInv,
      queuedFoldBlock_stutter _ _ (heldLoad_stutter c)]
    exact hSim
  | acquireWrite_admit c spin hNotInv hW hR hQ hSpin hNoWrap =>
    exact queuedBlock_step_acquireWrite_admit hSim hNotInv hW hR hQ hSpin hNoWrap
  | acquireWrite_enqueue c spin hNotInv hBusy hSpin hNoWrap hNoPending =>
    exact queuedBlock_step_acquireWrite_enqueue hSim hNotInv hBusy hSpin hNoWrap hNoPending
  | cancel_noop c spin hNotQueued hSpin =>
    exact queuedBlock_step_cancel_noop hSim hNotQueued hSpin
  | cancel_queued c t spin hQueued hLive hSpin =>
    exact queuedBlock_step_cancel_queued hSim hWfAbs hQueued hLive hSpin
  | releaseRead_noop c hNotHolder =>
    rw [RwLockState.applyOp_noop_releaseRead hNotHolder,
      queuedFoldBlock_stutter _ _ (heldLoad_stutter c)]
    exact hSim
  | releaseRead_noPromote c hHolder hNoPromote =>
    exact queuedBlock_step_releaseRead_noPromote hSim hWfAbs hHolder hNoPromote
  | releaseRead_promote c hHolder hFilterNil hW =>
    exact queuedBlock_step_releaseRead_promote hSim hWfAbs hHolder hFilterNil hW
  | releaseWrite_noop c hNotWriter =>
    rw [RwLockState.applyOp_noop_releaseWrite hNotWriter,
      queuedFoldBlock_stutter _ _ (heldLoad_stutter c)]
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

/-- **WS-RR RR6.9 / WS-LC LC2.7 (the FIFO payoff)**: after any such
trace, the `i`-th waiter the spec has queued holds the `i`-th **live**
outstanding ticket.

Admission order in the implementation is ticket order, so this says the
deployed lock admits waiters in exactly the order the spec's
`rwLock_fifo_admission` prescribes.  It is the property the CAS-retry
lock does **not** have — `rwLockSim` cannot even state it, because that
relation represents no queue at all.

**Live**, because the trace may contain withdrawals: `RwLockOp.cancel`
removes a *request* while its ticket stays outstanding until somebody
passes it, so the ticket a waiter holds is no longer
`now_serving + offset + i`.  Its **position** among the live entries
still is, and position is what FIFO is about — so this is a sharper
claim than the arithmetic one it replaces, not a weaker one. -/
theorem queuedRwLock_admits_in_spec_order
    (ops : List RwLockOp) (blocks : List (List QueuedRwLockOp))
    (hChain : ListQueuedBlocks RwLockState.unheld QueuedRwLockConcrete.unheld
      ops blocks)
    {i : Nat} {c : CoreId} {m : AccessMode}
    (hWaiter : (ops.foldl RwLockState.applyOp RwLockState.unheld).waiters[i]?
      = some (c, m)) :
    ∃ t, (queuedFoldBlock QueuedRwLockConcrete.unheld blocks.flatten).liveLedger[
        queuedWriterOffset (ops.foldl RwLockState.applyOp RwLockState.unheld) + i]?
          = some (t, c) ∧
      (queuedFoldBlock QueuedRwLockConcrete.unheld blocks.flatten).nowServing.toNat ≤ t ∧
      t < (queuedFoldBlock QueuedRwLockConcrete.unheld blocks.flatten).nextTicket.toNat :=
  queuedSim_waiter_ticket (queuedRwLock_refines_rwLockSpec ops blocks hChain) hWaiter

end SeLe4n.Kernel.Concurrency
