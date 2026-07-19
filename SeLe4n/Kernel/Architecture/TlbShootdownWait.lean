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
-- SM7.B.4 — Full-round multi-pair witness (all three targets of a
-- 4-core round, one trace)
-- ============================================================================
-- The single-pair witness above certifies one target's chain.  A real
-- BCM2712 round has THREE independent release-acquire pairs (targets
-- 1, 2, 3 → initiator 0), all on one execution; this witness pins that
-- every pair's publication chain holds simultaneously on a single
-- well-formed trace — no pair's ordering interferes with another's
-- (distinct ack locations, `AtomicLocation.shootdownAckOf_injective`).

private def multiPairTlbi (core : Nat) (h : core < numCores) (seq : Nat) :
    MemoryEvent :=
  { core := ⟨core, h⟩, loc := ⟨110 + core⟩, isWrite := true,
    order := .relaxed, value := 0, seqNum := seq }

private def multiPairRelease (core : Nat) (h : core < numCores) (seq : Nat) :
    MemoryEvent :=
  shootdownAckReleaseStore 0 ⟨core, h⟩ seq

private def multiPairAcquire (core : Nat) (h : core < numCores) (seq : Nat) :
    MemoryEvent :=
  shootdownAckAcquireLoad 0 ⟨0, by decide⟩ ⟨core, h⟩ seq

private def multiPairObserve : MemoryEvent :=
  { core := ⟨0, by decide⟩, loc := ⟨120⟩, isWrite := false,
    order := .relaxed, value := 0, seqNum := 20 }

private def multiPairTrace : MemoryTrace :=
  { events :=
      [ multiPairTlbi 1 (by decide) 1, multiPairRelease 1 (by decide) 2,
        multiPairTlbi 2 (by decide) 3, multiPairRelease 2 (by decide) 4,
        multiPairTlbi 3 (by decide) 5, multiPairRelease 3 (by decide) 6,
        multiPairAcquire 1 (by decide) 10, multiPairAcquire 2 (by decide) 11,
        multiPairAcquire 3 (by decide) 12, multiPairObserve ] }

/-- **WS-SM SM7.B.4** (multi-pair non-vacuity): on one well-formed
4-core round trace, EVERY target's TLBI retirement happens-before the
initiator's post-`allAcked` access — the three publication chains hold
simultaneously, which is exactly what `allAcked` needs to mean "no
stale translation anywhere". -/
theorem shootdownAck_release_acquire_multi_pair_witness :
    multiPairTrace.wellFormed ∧
      (happensBefore multiPairTrace (multiPairTlbi 1 (by decide) 1)
        multiPairObserve ∧
       happensBefore multiPairTrace (multiPairTlbi 2 (by decide) 3)
        multiPairObserve ∧
       happensBefore multiPairTrace (multiPairTlbi 3 (by decide) 5)
        multiPairObserve) := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · exact shootdownAck_release_acquire multiPairTrace
      (e_tlbi := multiPairTlbi 1 (by decide) 1)
      (e_rel := multiPairRelease 1 (by decide) 2)
      (e_acq := multiPairAcquire 1 (by decide) 10)
      (e_obs := multiPairObserve)
      ⟨by decide, by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide, by decide, by decide, by decide,
       by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide, by decide⟩
  · exact shootdownAck_release_acquire multiPairTrace
      (e_tlbi := multiPairTlbi 2 (by decide) 3)
      (e_rel := multiPairRelease 2 (by decide) 4)
      (e_acq := multiPairAcquire 2 (by decide) 11)
      (e_obs := multiPairObserve)
      ⟨by decide, by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide, by decide, by decide, by decide,
       by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide, by decide⟩
  · exact shootdownAck_release_acquire multiPairTrace
      (e_tlbi := multiPairTlbi 3 (by decide) 5)
      (e_rel := multiPairRelease 3 (by decide) 6)
      (e_acq := multiPairAcquire 3 (by decide) 12)
      (e_obs := multiPairObserve)
      ⟨by decide, by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide, by decide, by decide, by decide,
       by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide, by decide⟩

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

/-- **WS-SM SM7.B.6** (first-index spec): the bounded wait returns the
*first* satisfying poll index — no earlier poll in its window observed
`allAcked`.  Together with `waitAllAckedFrom_some_spec` this pins the
wait's result completely: it is the least all-acked snapshot. -/
theorem waitAllAckedFrom_first (states : Nat → TlbShootdownState) :
    ∀ (fuel i n : Nat), waitAllAckedFrom states i fuel = some n →
      ∀ j : Nat, i ≤ j → j < n → ¬ allAcked (states j) := by
  intro fuel
  induction fuel with
  | zero => intro i n h; cases h
  | succ k ih =>
    intro i n h j hij hjn
    unfold waitAllAckedFrom at h
    by_cases hAck : allAcked (states i)
    · rw [if_pos hAck] at h
      injection h with h
      subst h
      omega
    · rw [if_neg hAck] at h
      cases Nat.eq_or_lt_of_le hij with
      | inl heq => rw [← heq]; exact hAck
      | inr hlt => exact ih (i + 1) n h j hlt hjn

/-- **WS-SM SM7.B.6**: a `some` verdict is the *least* all-acked poll
index. -/
theorem waitAllAckedBounded_least {states : Nat → TlbShootdownState}
    {fuel n : Nat} (h : waitAllAckedBounded fuel states = some n) :
    allAcked (states n) ∧ ∀ j : Nat, j < n → ¬ allAcked (states j) :=
  ⟨(waitAllAckedFrom_some_spec states fuel 0 n h).1,
   fun j hj => waitAllAckedFrom_first states fuel 0 n h j (Nat.zero_le _) hj⟩

/-- **WS-SM SM7.B.5** (least-witness form): under monotone
acknowledgments and per-core deadlines there is a *least* poll index
at which `allAcked` holds, and it holds at every later index.
Constructive with no choice principle: the least witness is extracted
by running the bounded wait itself (`waitAllAckedBounded`) with a
sufficient budget — the wait's first-index spec
(`waitAllAckedBounded_least`) does the minimisation. -/
theorem shootdown_wait_loop_terminates_least
    (states : Nat → TlbShootdownState) (hmono : ackMonotone states)
    (deadline : CoreId → Nat)
    (hprog : ∀ c : CoreId, (states (deadline c)).ackOnCore c = true) :
    ∃ n : Nat, allAcked (states n) ∧
      (∀ j : Nat, j < n → ¬ allAcked (states j)) ∧
      ∀ m : Nat, n ≤ m → allAcked (states m) := by
  obtain ⟨N, hN, _⟩ :=
    shootdown_wait_loop_terminates states hmono deadline hprog
  have hsome : (waitAllAckedBounded (N + 1) states).isSome :=
    waitAllAckedBounded_isSome hN (Nat.lt_succ_self N)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨hAck, hleast⟩ := waitAllAckedBounded_least hn
  refine ⟨n, hAck, hleast, ?_⟩
  intro m hm c
  exact ackMonotone_stable hmono hm (hAck c)

-- ============================================================================
-- SM7.B.7 — The global round lock: CAS model + release-acquire publication
-- ============================================================================
-- The SM7.A round-serialisation contract is realised at runtime by
-- `shootdown.rs::SHOOTDOWN_ROUND_LOCK` — a single `AtomicBool` acquired
-- with `compare_exchange(false, true, Acquire, Relaxed)` and released
-- with `store(false, Release)`.  Two obligations are discharged here:
-- the CAS's *mutual exclusion* (at most one holder between release
-- points) and the *cross-round publication* edge (the previous holder's
-- critical-section writes — its masked ack reset, its posted queues —
-- happen-before everything the next holder does after its successful
-- CAS), which is exactly what makes the ack vector's lack of round
-- identity safe under serialisation.

/-- **WS-SM SM7.B.7**: location ID of the global round lock — the
SM2.A model of `SHOOTDOWN_ROUND_LOCK` (`shootdown.rs`; a single
`AtomicBool`, not per-core). -/
def AtomicLocation.shootdownRoundLockAt (base : Nat) : AtomicLocation :=
  ⟨base⟩

/-- **WS-SM SM7.B.7**: the round lock never aliases any core's ack
flag — releasing the lock cannot satisfy an ack acquire-poll and vice
versa, provided the refinement assignment separates the two location
ranges (the ack flags occupy `[ackBase, ackBase + numCores)`). -/
theorem AtomicLocation.shootdownRoundLockAt_ne_shootdownAckOf
    {lockBase ackBase : Nat}
    (h : lockBase < ackBase ∨ ackBase + numCores ≤ lockBase) (c : CoreId) :
    AtomicLocation.shootdownRoundLockAt lockBase ≠
      AtomicLocation.shootdownAckOf ackBase c := by
  intro hEq
  have hid : lockBase = ackBase + c.val := congrArg AtomicLocation.id hEq
  have hc : c.val < numCores := c.isLt
  omega

/-- **WS-SM SM7.B.7**: the round-lock CAS, as a pure state machine —
the model of `compare_exchange(false, true)`: succeeds exactly on an
unheld lock, and the lock is held afterwards in either case (a failed
CAS leaves the *other* holder's `true` in place). -/
def roundLockTryAcquire (held : Bool) : Bool × Bool :=
  if held then (false, true) else (true, true)

/-- **WS-SM SM7.B.7**: the release — an unconditional `store(false)`;
only the holder calls it (the Lean dispatch seam releases only after
its own successful cooperative acquire). -/
def roundLockRelease (_held : Bool) : Bool := false

/-- **WS-SM SM7.B.7**: the CAS succeeds iff the lock was free. -/
@[simp] theorem roundLockTryAcquire_success_iff (held : Bool) :
    (roundLockTryAcquire held).1 = true ↔ held = false := by
  cases held <;> simp [roundLockTryAcquire]

/-- **WS-SM SM7.B.7**: after any CAS attempt the lock is held (by the
new holder on success, by the existing holder on failure). -/
@[simp] theorem roundLockTryAcquire_post_held (held : Bool) :
    (roundLockTryAcquire held).2 = true := by
  cases held <;> rfl

/-- **WS-SM SM7.B.7** (mutual exclusion): two CAS attempts with no
intervening release cannot both succeed — the second attempt always
finds the lock held.  This is the at-most-one-initiator property that
serialises rounds (the runtime stress witness is the Rust
`sm7b_round_lock_*` HAL tests). -/
theorem roundLockTryAcquire_mutex (held : Bool) :
    ¬((roundLockTryAcquire held).1 = true ∧
      (roundLockTryAcquire (roundLockTryAcquire held).2).1 = true) := by
  cases held <;> simp [roundLockTryAcquire]

/-- **WS-SM SM7.B.7** (liveness): a release always re-enables the next
CAS — the cooperative acquire loop in
`acquireShootdownRoundLockServicingSelf` cannot starve once the
current holder's round completes. -/
theorem roundLockTryAcquire_after_release (held : Bool) :
    (roundLockTryAcquire (roundLockRelease held)).1 = true := by
  simp [roundLockRelease, roundLockTryAcquire]

/-- **WS-SM SM7.B.7**: the previous holder's release-store event shape
— `SHOOTDOWN_ROUND_LOCK.store(false, Release)`. -/
def shootdownRoundLockReleaseStore (base : Nat) (holder : CoreId)
    (seq : Nat) : MemoryEvent :=
  { core := holder
    loc := AtomicLocation.shootdownRoundLockAt base
    isWrite := true
    order := .release
    value := 0
    seqNum := seq }

/-- **WS-SM SM7.B.7**: the next holder's successful-CAS load event
shape — the acquire half of `compare_exchange(false, true, Acquire,
Relaxed)` observing the released `false` (value `0`). -/
def shootdownRoundLockAcquireCas (base : Nat) (next : CoreId)
    (seq : Nat) : MemoryEvent :=
  { core := next
    loc := AtomicLocation.shootdownRoundLockAt base
    isWrite := false
    order := .acquire
    value := 0
    seqNum := seq }

/-- **WS-SM SM7.B.7** (`shootdownRoundLock_release_acquire`): the
cross-round publication chain.  If the previous holder's last
critical-section access (`e_crit` — its masked ack reset, its posted
queues, its catch-up commit) is sequenced before its lock release
`e_rel`, the release synchronizes-with the next holder's successful
CAS `e_acq`, and that CAS is sequenced before the next holder's first
critical-section access `e_next`, then `e_crit` happens-before
`e_next`.  This is what makes the ack vector safe *without* a round
identity: under the serialised lock, a new round's
`reset_for_round` can never race a previous round's ack traffic —
every prior-round access is ordered before the reset. -/
theorem shootdownRoundLock_release_acquire (t : MemoryTrace)
    {e_crit e_rel e_acq e_next : MemoryEvent}
    (h_holder : sequencedBefore t e_crit e_rel)
    (h_sync : synchronizesWith t e_rel e_acq)
    (h_next : sequencedBefore t e_acq e_next) :
    happensBefore t e_crit e_next :=
  .trans (.trans (.seq h_holder) (.sync h_sync)) (.seq h_next)

/-- The concrete witness execution for the round-lock publication:
holder core 0 writes its round state (`e_crit`), release-stores the
lock free; core 1's CAS acquire-load observes the `false`, then core 1
resets for its own round (`e_next`).  Concrete (base 50, cores 0/1) so
every side condition evaluates by `decide`. -/
private def roundLockWitnessCrit : MemoryEvent :=
  { core := ⟨0, by decide⟩, loc := ⟨102⟩, isWrite := true,
    order := .relaxed, value := 0, seqNum := 10 }

private def roundLockWitnessRelease : MemoryEvent :=
  shootdownRoundLockReleaseStore 50 ⟨0, by decide⟩ 11

private def roundLockWitnessAcquire : MemoryEvent :=
  shootdownRoundLockAcquireCas 50 ⟨1, by decide⟩ 15

private def roundLockWitnessNext : MemoryEvent :=
  { core := ⟨1, by decide⟩, loc := ⟨103⟩, isWrite := true,
    order := .relaxed, value := 0, seqNum := 16 }

private def roundLockWitnessTrace : MemoryTrace :=
  { events := [roundLockWitnessCrit, roundLockWitnessRelease,
               roundLockWitnessAcquire, roundLockWitnessNext] }

/-- **WS-SM SM7.B.7** (non-vacuity): the round-lock publication chain
holds on an actual well-formed trace. -/
theorem shootdownRoundLock_release_acquire_witness :
    roundLockWitnessTrace.wellFormed ∧
      happensBefore roundLockWitnessTrace roundLockWitnessCrit
        roundLockWitnessNext := by
  refine ⟨by decide, ?_⟩
  have h_holder : sequencedBefore roundLockWitnessTrace roundLockWitnessCrit
      roundLockWitnessRelease :=
    ⟨by decide, by decide, by decide, by decide⟩
  have h_sync : synchronizesWith roundLockWitnessTrace
      roundLockWitnessRelease roundLockWitnessAcquire :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide,
     by decide, by decide, by decide⟩
  have h_next : sequencedBefore roundLockWitnessTrace
      roundLockWitnessAcquire roundLockWitnessNext :=
    ⟨by decide, by decide, by decide, by decide⟩
  exact shootdownRoundLock_release_acquire roundLockWitnessTrace h_holder
    h_sync h_next

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
