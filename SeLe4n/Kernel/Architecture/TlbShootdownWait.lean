-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.TlbShootdownProtocol
import SeLe4n.Kernel.Concurrency.MemoryModel

/-!
# WS-SM SM7.B.4–B.6 — Shootdown synchronization, wait-loop termination, timeout

The initiator side of the shootdown round's step 5 (plan §3.2): why
observing `allAcked` is *sufficient* (SM7.B.4 — the release-acquire
pairing orders every target's TLBI retirement before the initiator's
observation), why the wait terminates (SM7.B.5 — acknowledgments are
monotone and every target's handler eventually runs), and what the
bounded wait's verdict means (SM7.B.6 — `some` is a genuine
`allAcked` observation; `none` is a genuine timeout, so the runtime's
fail-closed panic never fires on a completed round).

## Runtime correspondence

* SM7.B.4's trace events model `rust/sele4n-hal/src/shootdown.rs`:
  `ack_set` is the release-store (`Ordering::Release`), the
  initiator's `all_acked` poll is the acquire-load
  (`Ordering::Acquire`), and the target's pre-ack `dsb` (baked into
  every `tlb.rs` TLBI primitive) is the same-core event sequenced
  before the release-store.
* SM7.B.5/B.6's poll trace models
  `shootdown.rs::wait_all_acked_bounded`: one `states i` snapshot per
  poll iteration; the `deadline` function is each target's handler
  completion time (guaranteed by SGI delivery — the GIC forwards the
  `.tlbShootdownReq` SGI, and the handler is short, panic-free, and
  runs with the interrupt already retired).
* The Lean timeout budget `shootdownWaitTimeoutTicks` mirrors the
  Rust `cpu::WFE_DEFAULT_TIMEOUT_TICKS` (10 ms at the BCM2712 54 MHz
  generic timer) — conformance-pinned on both sides.
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- SM7.B.4 — The ack flag's atomic location + release-acquire pairing
-- ============================================================================

/-- **WS-SM SM7.B.4**: concrete location ID for core `c`'s shootdown
ack flag — the SM2.A model of `SHOOTDOWN_ACK[c]` (`shootdown.rs`; one
cache-line-aligned `AtomicBool` per core).  `base` is the array's
location base under the SM2.B-style refinement assignment; per-core
flags occupy consecutive location IDs. -/
def AtomicLocation.shootdownAckOf (base : Nat) (c : CoreId) :
    AtomicLocation :=
  ⟨base + c.val⟩

/-- **WS-SM SM7.B.4**: distinct cores' ack flags never alias — each
target answers on its own atomic location, so one target's release
cannot satisfy the initiator's acquire-poll of another target's
flag. -/
theorem AtomicLocation.shootdownAckOf_injective (base : Nat)
    {c c' : CoreId} (h : c ≠ c') :
    AtomicLocation.shootdownAckOf base c ≠
      AtomicLocation.shootdownAckOf base c' := by
  intro hEq
  have hid : base + c.val = base + c'.val :=
    congrArg AtomicLocation.id hEq
  exact h (Fin.ext (Nat.add_left_cancel hid))

/-- **WS-SM SM7.B.4** (`shootdownAck_release_acquire`): the
release-acquire publication chain of the shootdown protocol.

If, in a well-formed execution trace:

* the target's TLBI-retirement event (`e_tlbi` — the `dsb` completing
  its drained invalidations) is sequenced before its ack
  release-store `e_rel` (program order in the SGI handler: TLBI, then
  `dsb`, then `ack_set`);
* the release-store synchronizes-with the initiator's acquire-load
  `e_acq` (same ack location, the load observes the stored `true` —
  ARM ARM B2.3.7); and
* the acquire-load is sequenced before the initiator's subsequent
  access `e_obs` (the initiator only proceeds after its poll),

then the target's TLBI retirement **happens-before** everything the
initiator does after observing the ack.  This is the Theorem 3.3.1
remote-case ordering: an initiator that saw `allAcked` can never
observe a stale translation on the target, because the invalidation's
retirement is ordered before its continuation. -/
theorem shootdownAck_release_acquire (t : MemoryTrace)
    {e_tlbi e_rel e_acq e_obs : MemoryEvent}
    (h_target : sequencedBefore t e_tlbi e_rel)
    (h_sync : synchronizesWith t e_rel e_acq)
    (h_initiator : sequencedBefore t e_acq e_obs) :
    happensBefore t e_tlbi e_obs :=
  .trans (.trans (.seq h_target) (.sync h_sync)) (.seq h_initiator)

-- ============================================================================
-- SM7.B.4 — Canonical event shapes + a concrete (non-vacuous) witness
-- ============================================================================

/-- **WS-SM SM7.B.4**: the target's ack release-store event shape —
`SHOOTDOWN_ACK[target].store(true, Release)` in `shootdown.rs`. -/
def shootdownAckReleaseStore (base : Nat) (target : CoreId) (seq : Nat) :
    MemoryEvent :=
  { core := target
    loc := AtomicLocation.shootdownAckOf base target
    isWrite := true
    order := .release
    value := 1
    seqNum := seq }

/-- **WS-SM SM7.B.4**: the initiator's ack acquire-load event shape —
the `all_acked` poll's per-flag `load(Acquire)` observing `true`. -/
def shootdownAckAcquireLoad (base : Nat) (initiator target : CoreId)
    (seq : Nat) : MemoryEvent :=
  { core := initiator
    loc := AtomicLocation.shootdownAckOf base target
    isWrite := false
    order := .acquire
    value := 1
    seqNum := seq }

/-- The concrete witness execution: target core 1 retires its TLBI
(`e_tlbi`, the handler's `dsb`-completion marker), release-stores its
ack; initiator core 0 acquire-loads the `true`, then proceeds
(`e_obs`).  Kept concrete (base 0, cores 0/1) so every side condition
evaluates by `decide` — the SM7.B.4 pairing is witnessed on an actual
trace, not only schematically. -/
private def ackWitnessTlbi : MemoryEvent :=
  { core := ⟨1, by decide⟩, loc := ⟨100⟩, isWrite := true,
    order := .relaxed, value := 0, seqNum := 0 }

private def ackWitnessRelease : MemoryEvent :=
  shootdownAckReleaseStore 0 ⟨1, by decide⟩ 1

private def ackWitnessAcquire : MemoryEvent :=
  shootdownAckAcquireLoad 0 ⟨0, by decide⟩ ⟨1, by decide⟩ 5

private def ackWitnessObserve : MemoryEvent :=
  { core := ⟨0, by decide⟩, loc := ⟨101⟩, isWrite := false,
    order := .relaxed, value := 0, seqNum := 6 }

private def ackWitnessTrace : MemoryTrace :=
  { events := [ackWitnessTlbi, ackWitnessRelease, ackWitnessAcquire,
               ackWitnessObserve] }

/-- **WS-SM SM7.B.4** (non-vacuity): the witness trace is well-formed
and the full publication chain holds on it — the target's TLBI
retirement happens-before the initiator's post-observation access. -/
theorem shootdownAck_release_acquire_witness :
    ackWitnessTrace.wellFormed ∧
      happensBefore ackWitnessTrace ackWitnessTlbi ackWitnessObserve := by
  refine ⟨by decide, ?_⟩
  have h_target : sequencedBefore ackWitnessTrace ackWitnessTlbi
      ackWitnessRelease :=
    ⟨by decide, by decide, by decide, by decide⟩
  have h_sync : synchronizesWith ackWitnessTrace ackWitnessRelease
      ackWitnessAcquire :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide,
     by decide, by decide, by decide⟩
  have h_initiator : sequencedBefore ackWitnessTrace ackWitnessAcquire
      ackWitnessObserve :=
    ⟨by decide, by decide, by decide, by decide⟩
  exact shootdownAck_release_acquire ackWitnessTrace h_target h_sync
    h_initiator

-- ============================================================================
-- SM7.B.5 — Wait-loop termination
-- ============================================================================

/-- **WS-SM SM7.B.5**: acknowledgment monotonicity over a poll trace —
once a core's flag is observed set it stays set for the rest of the
round.  This is the SM7.A `acknowledgeShootdown_monotone` property at
the trace level: mid-round, flags are only ever *set* (by handlers);
only the next round's `beginShootdownRoundFor` clears them, and the
round lock orders that after the current round's exit. -/
def ackMonotone (states : Nat → TlbShootdownState) : Prop :=
  ∀ (n : Nat) (c : CoreId),
    (states n).ackOnCore c = true → (states (n + 1)).ackOnCore c = true

/-- **WS-SM SM7.B.5**: a monotone flag stays set at every later poll. -/
theorem ackMonotone_stable {states : Nat → TlbShootdownState}
    (hmono : ackMonotone states) {c : CoreId} :
    ∀ {n m : Nat}, n ≤ m → (states n).ackOnCore c = true →
      (states m).ackOnCore c = true := by
  intro n m hle h
  induction m with
  | zero =>
    have : n = 0 := Nat.le_zero.mp hle
    rw [← this]
    exact h
  | succ k ih =>
    cases Nat.eq_or_lt_of_le hle with
    | inl heq => rw [← heq]; exact h
    | inr hlt => exact hmono k c (ih (Nat.lt_succ_iff.mp hlt))

/-- Fold-max helper: the accumulator never decreases. -/
private theorem foldl_max_ge_init (f : CoreId → Nat) (l : List CoreId) :
    ∀ init : Nat, init ≤ l.foldl (fun m x => max m (f x)) init := by
  induction l with
  | nil => intro init; exact Nat.le_refl _
  | cons x xs ih =>
    intro init
    exact Nat.le_trans (Nat.le_max_left init (f x)) (ih _)

/-- Fold-max helper: every listed core's value is below the fold. -/
private theorem le_foldl_max (f : CoreId → Nat) (l : List CoreId) :
    ∀ init : Nat, ∀ a ∈ l, f a ≤ l.foldl (fun m x => max m (f x)) init := by
  induction l with
  | nil => intro _ a ha; cases ha
  | cons x xs ih =>
    intro init a ha
    rcases List.mem_cons.mp ha with hEq | hMem
    · subst hEq
      exact Nat.le_trans (Nat.le_max_right init (f a))
        (foldl_max_ge_init f xs _)
    · exact ih _ a hMem

/-- **WS-SM SM7.B.5** (`shootdown_wait_loop_terminates`): the
initiator's wait loop terminates.

Constructive form: given monotone acknowledgments and, for every
core, a *deadline* poll index by which that core's flag is set (each
target's handler completion — guaranteed because the `.tlbShootdownReq`
SGI is delivered and its handler is short, panic-free, and
unconditionally acknowledges; the initiator and every non-target core
are born-acknowledged at index 0 by `beginShootdownRoundFor`), there
is a poll index at which `allAcked` holds — and it holds at every
later index, so the exit condition is stable, not a race window
(plan §3.2 step 5).

The witness is the maximum deadline over `allCores` — no choice
principle, no classical reasoning. -/
theorem shootdown_wait_loop_terminates
    (states : Nat → TlbShootdownState) (hmono : ackMonotone states)
    (deadline : CoreId → Nat)
    (hprog : ∀ c : CoreId, (states (deadline c)).ackOnCore c = true) :
    ∃ n : Nat, allAcked (states n) ∧
      ∀ m : Nat, n ≤ m → allAcked (states m) := by
  refine ⟨allCores.foldl (fun m x => max m (deadline x)) 0, ?_, ?_⟩
  · intro c
    have hmem : c ∈ allCores := by
      simp [SeLe4n.Kernel.Concurrency.allCores]
    exact ackMonotone_stable hmono (le_foldl_max deadline allCores 0 c hmem)
      (hprog c)
  · intro m hle c
    have hmem : c ∈ allCores := by
      simp [SeLe4n.Kernel.Concurrency.allCores]
    exact ackMonotone_stable hmono
      (Nat.le_trans (le_foldl_max deadline allCores 0 c hmem) hle) (hprog c)

-- ============================================================================
-- SM7.B.6 — Bounded wait + timeout fallback
-- ============================================================================

/-- **WS-SM SM7.B.6**: the fuel-bounded acquire-poll, from poll index
`i` — returns the first index at which `allAcked` holds, or `none`
after `fuel` polls (the timeout verdict). -/
def waitAllAckedFrom (states : Nat → TlbShootdownState) :
    Nat → Nat → Option Nat
  | _, 0 => none
  | i, fuel + 1 =>
      if allAcked (states i) then some i
      else waitAllAckedFrom states (i + 1) fuel

/-- **WS-SM SM7.B.6**: the initiator's bounded wait loop — poll up to
`fuel` snapshots for `allAcked` (the model of
`shootdown.rs::wait_all_acked_bounded`'s spin; one snapshot per
iteration). -/
def waitAllAckedBounded (fuel : Nat)
    (states : Nat → TlbShootdownState) : Option Nat :=
  waitAllAckedFrom states 0 fuel

/-- **WS-SM SM7.B.6**: a `some` verdict is a genuine observation —
`allAcked` really held at the returned poll index, which lies within
the budget. -/
theorem waitAllAckedFrom_some_spec (states : Nat → TlbShootdownState) :
    ∀ (fuel i n : Nat), waitAllAckedFrom states i fuel = some n →
      allAcked (states n) ∧ i ≤ n ∧ n < i + fuel := by
  intro fuel
  induction fuel with
  | zero => intro i n h; cases h
  | succ k ih =>
    intro i n h
    unfold waitAllAckedFrom at h
    by_cases hAck : allAcked (states i)
    · rw [if_pos hAck] at h
      injection h with h
      subst h
      exact ⟨hAck, Nat.le_refl _, Nat.lt_add_of_pos_right (Nat.succ_pos k)⟩
    · rw [if_neg hAck] at h
      obtain ⟨hAcked, hge, hlt⟩ := ih (i + 1) n h
      exact ⟨hAcked, Nat.le_trans (Nat.le_succ i) hge, by omega⟩

/-- **WS-SM SM7.B.6**: a `none` verdict is a genuine timeout — no poll
within the budget observed `allAcked`.  This is the fail-closed
guarantee behind the runtime's timeout panic: the panic can only fire
when the round truly did not complete within the budget, never on a
completed round. -/
theorem waitAllAckedFrom_none_spec (states : Nat → TlbShootdownState) :
    ∀ (fuel i : Nat), waitAllAckedFrom states i fuel = none →
      ∀ j : Nat, i ≤ j → j < i + fuel → ¬ allAcked (states j) := by
  intro fuel
  induction fuel with
  | zero => intro i _ j hge hlt; omega
  | succ k ih =>
    intro i h j hge hlt
    unfold waitAllAckedFrom at h
    by_cases hAck : allAcked (states i)
    · rw [if_pos hAck] at h; cases h
    · rw [if_neg hAck] at h
      cases Nat.eq_or_lt_of_le hge with
      | inl heq => rw [← heq]; exact hAck
      | inr hgt => exact ih (i + 1) h j hgt (by omega)

/-- **WS-SM SM7.B.6** (`shootdown_timeout_handling`): the bounded
wait's verdict is exact in both directions — `some n` iff `allAcked`
was genuinely observed at poll `n` within the budget, and `none` iff
no poll within the budget observed it.  Combined with
`shootdown_wait_loop_terminates` (under SGI delivery every core acks
by its deadline) a sufficient budget always yields `some`; the
runtime's timeout panic — v1.0.0 keeps a hung round fatal rather than
resumable, per plan SM7.B.6 — therefore fires only on a genuinely
hung target. -/
theorem shootdown_timeout_handling (fuel : Nat)
    (states : Nat → TlbShootdownState) :
    (∀ n : Nat, waitAllAckedBounded fuel states = some n →
      allAcked (states n) ∧ n < fuel) ∧
    (waitAllAckedBounded fuel states = none →
      ∀ j : Nat, j < fuel → ¬ allAcked (states j)) := by
  constructor
  · intro n h
    obtain ⟨hAcked, _, hlt⟩ := waitAllAckedFrom_some_spec states fuel 0 n h
    exact ⟨hAcked, by omega⟩
  · intro h j hj
    exact waitAllAckedFrom_none_spec states fuel 0 h j (Nat.zero_le _)
      (by omega)

/-- **WS-SM SM7.B.5 + B.6**: a sufficient budget never times out — if
`allAcked` holds at some poll index inside the budget (which
`shootdown_wait_loop_terminates` provides under SGI delivery), the
bounded wait returns `some`. -/
theorem waitAllAckedBounded_isSome {states : Nat → TlbShootdownState}
    {n fuel : Nat} (hn : allAcked (states n)) (hfuel : n < fuel) :
    (waitAllAckedBounded fuel states).isSome := by
  cases h : waitAllAckedBounded fuel states with
  | some m => rfl
  | none =>
    exact absurd hn ((shootdown_timeout_handling fuel states).2 h n hfuel)

/-- **WS-SM SM7.B.6**: the initiator's wait budget, in generic-timer
ticks — 10 ms at the BCM2712 54 MHz generic timer.  Mirrors the Rust
`cpu::WFE_DEFAULT_TIMEOUT_TICKS` (the established bounded-wait budget
of the SM1/SM2 spin primitives); the conformance is pinned by
`shootdownWaitTimeoutTicks_value` here and the
`sm7b_wait_timeout_matches_wfe_default` HAL test on the Rust side.  A
round completes in < 1 µs on the 4-core BCM2712 (plan §3.4), so the
budget carries four orders of magnitude of slack — a timeout means a
genuinely hung or deaf target core, which v1.0.0 treats as fatal
(fail-closed panic) rather than resumable. -/
def shootdownWaitTimeoutTicks : UInt64 := 540000

/-- **WS-SM SM7.B.6**: the budget literal, pinned (10 ms × 54 MHz /
1000 = 540 000 ticks). -/
theorem shootdownWaitTimeoutTicks_value :
    shootdownWaitTimeoutTicks = 540000 := rfl

end SeLe4n.Kernel.Architecture
