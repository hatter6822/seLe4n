-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM (SM2.D refinement bridge between the Lean
-- abstract TicketLockState and the Rust two-u64 concrete representation;
-- SM3+ per-object locks first consume the refinement when wiring
-- kernel-side critical sections through the FFI bridge).

import SeLe4n.Kernel.Concurrency.Locks.TicketLock

/-!
# WS-SM SM2.D — TicketLock refinement bridge (Lean ↔ Rust)

Mirrors `Locks/RwLockRefinement.lean` for the TicketLock primitive.
Defines the operational simulation φ between the Lean abstract
`TicketLockState` and the Rust two-u64 concrete representation
(`next_ticket: AtomicU64`, `serving: AtomicU64`).

## Concrete representation

The Rust impl at `rust/sele4n-hal/src/ticket_lock.rs` exposes the
state as a pair of `AtomicU64` counters.  The SM2.D.1 peek FFI helper
returns a snapshot of both via `peek_next_ticket` / `peek_serving`.
We model the concrete state as the pair `(UInt64, UInt64)`.

## Simulation relation φ

The abstract `TicketLockState` carries four fields:

* `nextTicket : Nat` ↔ Rust `next_ticket: AtomicU64`
* `serving    : Nat` ↔ Rust `serving:     AtomicU64`
* `pending    : List (CoreId × Nat)` — implicit on the concrete side
  (waiting threads are reflected in the gap between the two counters
  plus per-core register state, not in shared lock state).
* `held       : Option (CoreId × Nat)` — implicit on the concrete side
  (the holder is the thread whose captured ticket equals `serving`).

The simulation φ relates the two `Nat` counters to the two `UInt64`
counters via `.toNat`:

    φ abstract (concrete_next, concrete_serving) iff
      concrete_next.toNat = abstract.nextTicket ∧
      concrete_serving.toNat = abstract.serving

## FIFO refinement

Unlike the CAS-retry RwLock (`rw_lock.rs`, whose FIFO divergence is
documented at `RwLockRefinement.lean` — and which WS-RR RR6.10 retired
from the deployed pool for exactly that reason), the TicketLock Rust
impl DOES satisfy the abstract spec's FIFO property structurally:
`next_ticket.fetch_add(1, Acquire)` produces
strictly monotone tickets, and `serving.fetch_add(1, Release)`
advances exactly once per release.  The abstract `pending` queue is
implicit but the ORDER it would enforce is the natural arrival
order of captured tickets.

## The trace-level bridge (WS-RR RR6.12 … RR6.14)

Through v0.34.48 `rust_ticketLock_refines_lean` was a conjunction of
four *per-step counter identities* — and its fourth conjunct was
`∀ abs conc, ticketLockSim abs conc → ticketLockSim abs conc`, which is
`id`: a statement that cannot fail, contributing nothing but a
conjunct.  The other three said that if the abstract counter moves and
the concrete counter moves the same way then the relation is preserved,
which is arithmetic about two counters rather than a claim about the
implementation: nothing in the statement tied a concrete counter's
movement to the Rust operation that causes it.

§B below builds the missing structure, mirroring the RwLock
refinements' shape:

* `ConcreteTicketLockOp` — one constructor per atomic access
  `ticket_lock.rs` performs, and `TicketLockConcrete.applyOp`, its
  effect on the two counters (RR6.12).
* `ticketBlock` — which concrete block each abstract `TicketLockOp`
  maps to, with the spin loop appearing as an arbitrary stutter prefix
  of observation-only ops rather than as steps (RR6.13).
* `ticketTrace_preserves_ticketLockSim` — the composition, taking **no**
  per-block obligation as a hypothesis (RR6.13).

`rust_ticketLock_refines_lean` is then the initial-state correspondence
plus that composition (RR6.14).  Both conjuncts can fail:
`ticketLockSim_not_universal` exhibits an unrelated pair, and
`ticketBlock_release_moves_serving` exhibits a block that moves the
concrete counter, so neither half is vacuous.

Unlike the CAS-retry RwLock's `opCorresponds` — whose `tryRead_success`
constructor takes arbitrary CAS operands, and so admits a block whose
concrete CAS fails (the defect WS-RR RR6.15 removes) — no
`ConcreteTicketLockOp` carries an operand at all.  `fetch_add(1)` has
nothing to get wrong, so `ticketBlock` needs no concrete-state index to
pin one.

## Reachability

`Concurrency.Locks.TicketLockRefinement` is reachable in the
kernel's production import closure via
`SeLe4n/Platform/Staged.lean`.

## Section map

* §A — the simulation relation and its per-step witnesses (SM2.D).
* §B — the concrete operation alphabet, the block shapes, and the
  trace-level composition (WS-RR RR6.12 … RR6.14).
-/

namespace SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §A (SM2.D) — The simulation relation and its per-step witnesses
-- ============================================================================

/-- **WS-SM SM2.D**: concrete representation of a Rust TicketLock —
    a pair of `UInt64` atomics.

    Used in the simulation relation φ as the concrete state.  The
    actual Rust `TicketLock` carries `AtomicU64` (not bare `UInt64`),
    but at the abstraction level of the Lean spec we model the
    observable state — i.e., what an atomic `load(Acquire)` returns. -/
structure TicketLockConcrete where
  /-- The `next_ticket` counter's current value. -/
  nextTicket : UInt64
  /-- The `serving` counter's current value. -/
  serving    : UInt64
  deriving Repr, DecidableEq, Inhabited

/-- **WS-SM SM2.D**: the unheld concrete state — both counters at
    zero.  Matches `TicketLock::new` in Rust. -/
def TicketLockConcrete.unheld : TicketLockConcrete :=
  { nextTicket := 0, serving := 0 }

/-- **WS-SM SM2.D**: the simulation relation φ between the abstract
    `TicketLockState` and the concrete `TicketLockConcrete`.

    Two conjuncts:
    1. `concrete.nextTicket.toNat = abstract.nextTicket`.
    2. `concrete.serving.toNat = abstract.serving`.

    The abstract `pending` and `held` fields are NOT directly
    represented in the concrete state; they are reconstructed
    implicitly from the gap between `serving` and `nextTicket`
    plus per-core captured-ticket state.  Under the abstract `wf`
    invariant the relation between abstract and concrete is
    one-to-one on the directly-tracked counters. -/
def ticketLockSim (abstract : TicketLockState) (concrete : TicketLockConcrete) :
    Prop :=
  concrete.nextTicket.toNat = abstract.nextTicket ∧
  concrete.serving.toNat = abstract.serving

/-- **WS-SM SM2.D**: `ticketLockSim` is decidable.  Used by tests
    that need to check the simulation holds at a specific abstract
    + concrete state pair. -/
instance decidableTicketLockSim (abstract : TicketLockState)
    (concrete : TicketLockConcrete) : Decidable (ticketLockSim abstract concrete) := by
  unfold ticketLockSim
  exact inferInstance

/-- **WS-SM SM2.D**: the unheld abstract state corresponds to the
    unheld concrete state under φ.

    Initial-state correspondence: the Rust `TicketLock::new` (which
    produces `next_ticket = 0, serving = 0`) and the Lean
    `TicketLockState.unheld` (which sets `nextTicket = 0, serving =
    0, pending = [], held = none`) agree on the directly-tracked
    counters. -/
theorem ticketLockSim_unheld :
    ticketLockSim TicketLockState.unheld TicketLockConcrete.unheld := by
  unfold ticketLockSim TicketLockConcrete.unheld TicketLockState.unheld
  decide

/-- **WS-SM SM2.D**: if the abstract state advances `nextTicket` by 1
    (capturing a ticket) and the concrete state advances its
    `nextTicket` counter correspondingly, the simulation φ is
    preserved.

    Structural witness for the `tryAcquire` operation's
    refinement: each abstract `nextTicket + 1` corresponds to a
    concrete `fetch_add(1, Acquire)` on the `next_ticket` u64. -/
theorem ticketLockSim_preserved_by_tryAcquire
    (abs : TicketLockState) (conc : TicketLockConcrete)
    (h_sim : ticketLockSim abs conc)
    (h_bound : abs.nextTicket + 1 < UInt64.size) :
    ticketLockSim
      { abs with nextTicket := abs.nextTicket + 1 }
      { conc with nextTicket := conc.nextTicket + 1 } := by
  unfold ticketLockSim at h_sim ⊢
  obtain ⟨h_next, h_srv⟩ := h_sim
  refine ⟨?_, h_srv⟩
  -- (conc.nextTicket + 1).toNat = abs.nextTicket + 1
  -- Under the u64 bound, addition does not wrap.
  have h_concBound : conc.nextTicket.toNat + 1 < UInt64.size := by
    rw [h_next]; exact h_bound
  -- Use UInt64.add_toNat or similar.  Add via Nat then convert.
  have : (conc.nextTicket + 1).toNat = conc.nextTicket.toNat + 1 := by
    have := UInt64.toNat_add conc.nextTicket 1
    rw [this]
    have h_one : (1 : UInt64).toNat = 1 := by decide
    rw [h_one]
    -- After toNat_add: (a + b).toNat = (a.toNat + b.toNat) % UInt64.size
    rw [Nat.mod_eq_of_lt h_concBound]
  rw [this, h_next]

/-- **WS-SM SM2.D**: if the abstract state advances `serving` by 1
    (releasing) and the concrete state's `serving` counter
    advances correspondingly, φ is preserved.

    Structural witness for the `release` operation's refinement:
    each abstract `serving + 1` corresponds to a concrete
    `fetch_add(1, Release)` on the `serving` u64. -/
theorem ticketLockSim_preserved_by_release
    (abs : TicketLockState) (conc : TicketLockConcrete)
    (h_sim : ticketLockSim abs conc)
    (h_bound : abs.serving + 1 < UInt64.size) :
    ticketLockSim
      { abs with serving := abs.serving + 1 }
      { conc with serving := conc.serving + 1 } := by
  unfold ticketLockSim at h_sim ⊢
  obtain ⟨h_next, h_srv⟩ := h_sim
  refine ⟨h_next, ?_⟩
  have h_concBound : conc.serving.toNat + 1 < UInt64.size := by
    rw [h_srv]; exact h_bound
  have : (conc.serving + 1).toNat = conc.serving.toNat + 1 := by
    rw [UInt64.toNat_add]
    have h_one : (1 : UInt64).toNat = 1 := by decide
    rw [h_one]
    rw [Nat.mod_eq_of_lt h_concBound]
  rw [this, h_srv]

/-- **WS-SM SM2.D**: if the abstract state is unchanged by an
    `observeServing` operation, the simulation φ is trivially
    preserved.

    Structural witness for the spin-loop observation step: each
    concrete `serving.load(Acquire)` is a pure observation that
    does not change shared state. -/
theorem ticketLockSim_preserved_by_observeServing
    (abs : TicketLockState) (conc : TicketLockConcrete)
    (h_sim : ticketLockSim abs conc) :
    ticketLockSim abs conc := h_sim

-- ============================================================================
-- §B (RR6.12 … RR6.14) — Concrete alphabet, block shapes, trace composition
-- ============================================================================

/-- **WS-RR RR6.12**: one atomic access `ticket_lock.rs` performs.

Derived from that file rather than themed: `acquire` is a
`next_ticket.fetch_add(1, Acquire)` followed by a spin on
`serving.load(Acquire)` with a bounded `wfe` between iterations;
`release` is `serving.fetch_add(1, Release)`, a `next_ticket.load` for
its `debug_assert`, and a `sev`; `peek_next_ticket` / `peek_serving`
contribute the two remaining loads.

No constructor carries an operand.  `fetch_add(1)` on a dedicated
counter has no `expected` to mismatch and no `new` to compute, which is
why this alphabet cannot express the CAS-operand defect that WS-RR
RR6.15 removes from the CAS-retry RwLock's `opCorresponds`. -/
inductive ConcreteTicketLockOp where
  /-- `next_ticket.fetch_add(1, Acquire)` — capture a ticket. -/
  | nextTicketFetchAdd (core : CoreId)
  /-- `serving.fetch_add(1, Release)` — release and publish. -/
  | servingFetchAdd (core : CoreId)
  /-- `serving.load(Acquire)` — the spin-loop body and `peek_serving`. -/
  | servingLoad (core : CoreId)
  /-- `next_ticket.load(Acquire)` — `peek_next_ticket` and `release`'s
  `debug_assert` read. -/
  | nextTicketLoad (core : CoreId)
  /-- `cpu::sev()` — wake the PEs parked on `wfe`. -/
  | sev (core : CoreId)
  /-- `cpu::wfe_bounded(..)` — park between spin iterations. -/
  | wfeWait (core : CoreId)
  deriving Repr, DecidableEq

/-- **WS-RR RR6.12**: the effect of one atomic access on the two
counters.

`UInt64` arithmetic, so the wrap is modelled rather than assumed away;
the block shapes below carry the no-wrap side conditions where a step
needs them. -/
def TicketLockConcrete.applyOp (s : TicketLockConcrete)
    (op : ConcreteTicketLockOp) : TicketLockConcrete :=
  match op with
  | .nextTicketFetchAdd _ => { s with nextTicket := s.nextTicket + 1 }
  | .servingFetchAdd _ => { s with serving := s.serving + 1 }
  | .servingLoad _ | .nextTicketLoad _ | .sev _ | .wfeWait _ => s

/-- **WS-RR RR6.12**: an op is *observation-only* when it moves neither
counter — the two loads and the two hints. -/
def ConcreteTicketLockOp.isObservation : ConcreteTicketLockOp → Bool
  | .servingLoad _ | .nextTicketLoad _ | .sev _ | .wfeWait _ => true
  | _ => false

theorem TicketLockConcrete.applyOp_observation (s : TicketLockConcrete)
    (op : ConcreteTicketLockOp) (h : op.isObservation = true) : s.applyOp op = s := by
  cases op <;> simp_all [TicketLockConcrete.applyOp, ConcreteTicketLockOp.isObservation]

/-- **WS-RR RR6.13**: execute a block of concrete ops. -/
def ticketFoldBlock (conc : TicketLockConcrete)
    (blk : List ConcreteTicketLockOp) : TicketLockConcrete :=
  blk.foldl TicketLockConcrete.applyOp conc

@[simp] theorem ticketFoldBlock_nil (conc : TicketLockConcrete) :
    ticketFoldBlock conc [] = conc := rfl

theorem ticketFoldBlock_append (conc : TicketLockConcrete)
    (a b : List ConcreteTicketLockOp) :
    ticketFoldBlock conc (a ++ b) = ticketFoldBlock (ticketFoldBlock conc a) b := by
  unfold ticketFoldBlock; rw [List.foldl_append]

/-- **WS-RR RR6.13**: a stutter — a run of observation-only ops.  The
`acquire` spin loop is an unbounded run of these; it must appear as
stuttering rather than as steps. -/
def TicketStutter (ops : List ConcreteTicketLockOp) : Prop :=
  ∀ op ∈ ops, op.isObservation = true

theorem ticketFoldBlock_stutter (conc : TicketLockConcrete)
    (ops : List ConcreteTicketLockOp) (h : TicketStutter ops) :
    ticketFoldBlock conc ops = conc := by
  induction ops generalizing conc with
  | nil => rfl
  | cons op rest ih =>
    rw [ticketFoldBlock, List.foldl_cons,
      TicketLockConcrete.applyOp_observation conc op (h op List.mem_cons_self)]
    exact ih _ (fun o ho => h o (List.mem_cons_of_mem _ ho))

-- ----------------------------------------------------------------------------
-- Abstract step shapes
-- ----------------------------------------------------------------------------

/-- The counters after a capture that is not a no-op.  Both branches of
`applyOp`'s fused fast path move `nextTicket` by one and leave `serving`
alone — the promotion the fast path performs is entirely in `pending` /
`held`, which the concrete state does not represent. -/
theorem TicketLockState.tryAcquire_counters (s : TicketLockState) (c : CoreId)
    (hNotPending : c ∉ s.pending.map Prod.fst)
    (hNotHeld : s.held.map Prod.fst ≠ some c) :
    (s.applyOp (.tryAcquire c)).nextTicket = s.nextTicket + 1 ∧
      (s.applyOp (.tryAcquire c)).serving = s.serving := by
  unfold TicketLockState.applyOp
  simp only [hNotPending, hNotHeld, ↓reduceIte]
  split <;> exact ⟨rfl, rfl⟩

theorem TicketLockState.tryAcquire_noop_of_pending (s : TicketLockState) (c : CoreId)
    (h : c ∈ s.pending.map Prod.fst) : s.applyOp (.tryAcquire c) = s := by
  unfold TicketLockState.applyOp; simp [h]

theorem TicketLockState.tryAcquire_noop_of_held (s : TicketLockState) (c : CoreId)
    (h : s.held.map Prod.fst = some c) : s.applyOp (.tryAcquire c) = s := by
  unfold TicketLockState.applyOp
  by_cases hp : c ∈ s.pending.map Prod.fst
  · simp [hp]
  · simp [hp, h]

theorem TicketLockState.release_counters (s : TicketLockState) (c : CoreId) (t : Nat)
    (h : s.held = some (c, t)) :
    (s.applyOp (.release c)).serving = s.serving + 1 ∧
      (s.applyOp (.release c)).nextTicket = s.nextTicket := by
  unfold TicketLockState.applyOp
  rw [h]
  simp

theorem TicketLockState.release_noop (s : TicketLockState) (c : CoreId)
    (h : ∀ t, s.held ≠ some (c, t)) : s.applyOp (.release c) = s := by
  unfold TicketLockState.applyOp
  cases hHeld : s.held with
  | none => rfl
  | some p =>
    obtain ⟨c', t⟩ := p
    by_cases hEq : c' = c
    · subst hEq; exact absurd hHeld (h t)
    · simp [hEq]

@[simp] theorem TicketLockState.observeServing_noop (s : TicketLockState)
    (c : CoreId) (v : Nat) : s.applyOp (.observeServing c v) = s := rfl

-- ----------------------------------------------------------------------------
-- Block shapes and the per-block step theorem
-- ----------------------------------------------------------------------------

/-- **WS-RR RR6.13**: which concrete block each abstract operation maps
to.

Indexed on the abstract state alone: the shape depends on which branch
of `applyOp` the state takes, and — unlike the CAS-retry RwLock's
blocks — no concrete operand needs pinning, because no
`ConcreteTicketLockOp` has one.

`spin` is `acquire`'s wait: an arbitrary run of `serving.load` /
`wfe_bounded`, unbounded in the implementation and stuttering here. -/
inductive ticketBlock :
    TicketLockState → TicketLockOp → List ConcreteTicketLockOp → Prop where
  /-- A core already queued or holding re-acquiring is a spec no-op; the
  implementation has no such path, so the block only observes. -/
  | tryAcquire_noop (abs : TicketLockState) (c : CoreId)
      (spin : List ConcreteTicketLockOp) :
      (c ∈ abs.pending.map Prod.fst ∨ abs.held.map Prod.fst = some c) →
      TicketStutter spin →
      ticketBlock abs (.tryAcquire c) spin
  /-- `acquire`: capture the ticket, then spin on `serving` until it is
  served.  The abstract fast path may fuse the promotion into the same
  step; that moves `pending` / `held`, which the concrete state does not
  represent, so the block is the same either way. -/
  | tryAcquire_capture (abs : TicketLockState) (c : CoreId)
      (spin : List ConcreteTicketLockOp) :
      c ∉ abs.pending.map Prod.fst → abs.held.map Prod.fst ≠ some c →
      TicketStutter spin → abs.nextTicket + 1 < UInt64.size →
      ticketBlock abs (.tryAcquire c) (.nextTicketFetchAdd c :: spin)
  /-- Releasing a lock one does not hold is a spec no-op; the
  implementation's `debug_assert` rejects it. -/
  | release_noop (abs : TicketLockState) (c : CoreId)
      (spin : List ConcreteTicketLockOp) :
      (∀ t, abs.held ≠ some (c, t)) → TicketStutter spin →
      ticketBlock abs (.release c) spin
  /-- `release`: advance `serving`, read `next_ticket` for the
  `debug_assert`, and wake the waiters. -/
  | release_effective (abs : TicketLockState) (c : CoreId) (t : Nat) :
      abs.held = some (c, t) → abs.serving + 1 < UInt64.size →
      ticketBlock abs (.release c)
        [.servingFetchAdd c, .nextTicketLoad c, .sev c]
  /-- The spin-loop observation: a pure read on both sides. -/
  | observeServing (abs : TicketLockState) (c : CoreId) (v : Nat)
      (spin : List ConcreteTicketLockOp) :
      TicketStutter spin →
      ticketBlock abs (.observeServing c v) spin

/-- **WS-RR RR6.13 (the per-block step theorem)**: every block shape
carries the simulation across its abstract operation.

The case analysis is over `ticketBlock`'s constructors, so a shape added
later is a missing case rather than a silent gap. -/
theorem ticketBlock_preserves_ticketLockSim
    {abs : TicketLockState} {conc : TicketLockConcrete} {op : TicketLockOp}
    {blk : List ConcreteTicketLockOp}
    (hSim : ticketLockSim abs conc) (hBlk : ticketBlock abs op blk) :
    ticketLockSim (abs.applyOp op) (ticketFoldBlock conc blk) := by
  cases hBlk with
  | tryAcquire_noop c spin hInv hSpin =>
    rw [ticketFoldBlock_stutter _ _ hSpin]
    rcases hInv with hp | hh
    · rw [TicketLockState.tryAcquire_noop_of_pending _ _ hp]; exact hSim
    · rw [TicketLockState.tryAcquire_noop_of_held _ _ hh]; exact hSim
  | tryAcquire_capture c spin hNotPending hNotHeld hSpin hNoWrap =>
    obtain ⟨hNext, hServ⟩ := hSim
    obtain ⟨hPostNext, hPostServ⟩ :=
      TicketLockState.tryAcquire_counters _ c hNotPending hNotHeld
    have hFold : ticketFoldBlock conc (.nextTicketFetchAdd c :: spin)
        = { conc with nextTicket := conc.nextTicket + 1 } := by
      rw [ticketFoldBlock, List.foldl_cons]
      exact ticketFoldBlock_stutter _ _ hSpin
    rw [hFold]
    refine ⟨?_, ?_⟩
    · show (conc.nextTicket + 1).toNat = (abs.applyOp (.tryAcquire c)).nextTicket
      rw [hPostNext, UInt64.toNat_add]
      have hOne : (1 : UInt64).toNat = 1 := by decide
      rw [hOne, Nat.mod_eq_of_lt (by rw [hNext]; exact hNoWrap), hNext]
    · show conc.serving.toNat = (abs.applyOp (.tryAcquire c)).serving
      rw [hPostServ]; exact hServ
  | release_noop c spin hNotHolder hSpin =>
    rw [TicketLockState.release_noop _ _ hNotHolder, ticketFoldBlock_stutter _ _ hSpin]
    exact hSim
  | release_effective c t hHeld hNoWrap =>
    obtain ⟨hNext, hServ⟩ := hSim
    obtain ⟨hPostServ, hPostNext⟩ := TicketLockState.release_counters _ c t hHeld
    have hFold : ticketFoldBlock conc
        [ConcreteTicketLockOp.servingFetchAdd c, .nextTicketLoad c, .sev c]
        = { conc with serving := conc.serving + 1 } := rfl
    rw [hFold]
    refine ⟨?_, ?_⟩
    · show conc.nextTicket.toNat = (abs.applyOp (.release c)).nextTicket
      rw [hPostNext]; exact hNext
    · show (conc.serving + 1).toNat = (abs.applyOp (.release c)).serving
      rw [hPostServ, UInt64.toNat_add]
      have hOne : (1 : UInt64).toNat = 1 := by decide
      rw [hOne, Nat.mod_eq_of_lt (by rw [hServ]; exact hNoWrap), hServ]
  | observeServing c v spin hSpin =>
    rw [TicketLockState.observeServing_noop, ticketFoldBlock_stutter _ _ hSpin]
    exact hSim

/-- **WS-RR RR6.13**: an abstract op-list paired with its concrete
block list, each block admissible at the abstract state it executes in.

Carries **no** per-block simulation obligation — the blocks are related
by shape, and the composition discharges the simulation from that
shape.  Taking the per-block conclusion as a hypothesis is the defect
WS-RR RR6.19 removes from the CAS-retry RwLock's main theorem; there is
no reason to reproduce it here. -/
inductive ListTicketBlocks :
    TicketLockState → List TicketLockOp → List (List ConcreteTicketLockOp) → Prop where
  | nil (abs : TicketLockState) : ListTicketBlocks abs [] []
  | cons (abs : TicketLockState) (a : TicketLockOp) (b : List ConcreteTicketLockOp)
      (as : List TicketLockOp) (bs : List (List ConcreteTicketLockOp)) :
      ticketBlock abs a b →
      ListTicketBlocks (abs.applyOp a) as bs →
      ListTicketBlocks abs (a :: as) (b :: bs)

/-- **WS-RR RR6.13 (trace composition)**: from any sim-related starting
pair, an abstract op-list and its concrete block list end sim-related. -/
theorem ticketTrace_preserves_ticketLockSim
    {abs : TicketLockState} {conc : TicketLockConcrete}
    {ops : List TicketLockOp} {blocks : List (List ConcreteTicketLockOp)}
    (hSim : ticketLockSim abs conc) (hChain : ListTicketBlocks abs ops blocks) :
    ticketLockSim (ops.foldl TicketLockState.applyOp abs)
      (ticketFoldBlock conc blocks.flatten) := by
  induction hChain generalizing conc with
  | nil a => simpa using hSim
  | cons a op blk restOps restBlocks hBlk _hRest ih =>
    have hStep := ticketBlock_preserves_ticketLockSim hSim hBlk
    have hFlatten : (blk :: restBlocks).flatten = blk ++ restBlocks.flatten := by simp
    rw [List.foldl_cons, hFlatten, ticketFoldBlock_append]
    exact ih hStep

-- ----------------------------------------------------------------------------
-- RR6.14 — the refinement anchor, with no conjunct that cannot fail
-- ----------------------------------------------------------------------------

/-- **WS-RR RR6.14 (negative witness)**: `ticketLockSim` is not
universal.

The relation the theorem below asserts has to be one a wrong
implementation would violate.  Here is a concrete state that does not
simulate the initial abstract one: its `serving` counter has advanced
while the spec's has not, which is exactly what a release that
advanced the wrong counter would produce. -/
theorem ticketLockSim_not_universal :
    ¬ ticketLockSim TicketLockState.unheld { nextTicket := 0, serving := 1 } := by
  intro h
  have := h.2
  simp [TicketLockState.unheld] at this

/-- **WS-RR RR6.14 (positive witness)**: the release block does move the
concrete counter.

Together with the negative witness this pins the composition as a real
claim: a block that left `serving` alone would fail the simulation at
the very next state, and this shows the block does not leave it alone. -/
theorem ticketBlock_release_moves_serving (conc : TicketLockConcrete) (c : CoreId) :
    (ticketFoldBlock conc
      [ConcreteTicketLockOp.servingFetchAdd c, .nextTicketLoad c, .sev c]).serving
      = conc.serving + 1 := rfl

/-- **WS-SM SM2.D F-01 / WS-RR RR6.14** (refinement theorem anchor): the
Rust `TicketLock` implementation refines the Lean operational
specification, at the level of **traces**.

Two conjuncts, and both can fail:

1. **Initial-state correspondence** — `TicketLock::new` and
   `TicketLockState.unheld` are related.  `ticketLockSim_not_universal`
   exhibits a state that is not, so this is a claim about these two
   rather than about every pair.
2. **Trace correspondence** — for every abstract op-list and the
   concrete block list the implementation executes for it
   (`ListTicketBlocks`, whose constructors are the per-entry-point
   shapes in `ticketBlock`), folding `applyOp` over the spec and folding
   the atomic accesses over the two counters end in related states.

What changed at WS-RR RR6.14: the previous form was four conjuncts of
per-step counter arithmetic, the fourth of which was
`∀ abs conc, ticketLockSim abs conc → ticketLockSim abs conc` — `id`,
a conjunct no implementation could violate.  The three others were
arithmetic about two counters with nothing tying a counter's movement
to the Rust operation that causes it; `ticketBlock` is that tie, and
conjunct 2 quantifies over it.

The per-step witnesses (`ticketLockSim_unheld`,
`ticketLockSim_preserved_by_tryAcquire`,
`ticketLockSim_preserved_by_release`,
`ticketLockSim_preserved_by_observeServing`) remain as §A lemmas — they
are the arithmetic conjunct 2's proof consumes — but they are no longer
what the anchor asserts.

The SM2.D.7 `lockPrimitives` aggregator references this theorem as the
F-01 refinement anchor. -/
theorem rust_ticketLock_refines_lean :
    -- Initial-state correspondence.
    ticketLockSim TicketLockState.unheld TicketLockConcrete.unheld ∧
    -- Trace correspondence: the spec's fold and the implementation's
    -- atomic accesses agree, for every trace the implementation can run.
    (∀ (ops : List TicketLockOp) (blocks : List (List ConcreteTicketLockOp)),
      ListTicketBlocks TicketLockState.unheld ops blocks →
      ticketLockSim (ops.foldl TicketLockState.applyOp TicketLockState.unheld)
        (ticketFoldBlock TicketLockConcrete.unheld blocks.flatten)) :=
  ⟨ticketLockSim_unheld,
   fun _ops _blocks hChain =>
     ticketTrace_preserves_ticketLockSim ticketLockSim_unheld hChain⟩


end SeLe4n.Kernel.Concurrency
