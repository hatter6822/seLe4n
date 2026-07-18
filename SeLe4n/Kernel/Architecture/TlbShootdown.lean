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

The ack vector carries **no round identity**, so it is a
single-round resource: at most one shootdown round may be in flight
system-wide.  The plan §3.2 precondition (the initiator holds the
VSpaceRoot write lock) is **not** sufficient to guarantee this — two
initiators shooting down *different* VSpaces hold different VSpaceRoot
locks and would interleave rounds, with two concrete failures: (a)
initiator B's `beginShootdownRound` marks B's own flag `true` while A
still waits on that core's invalidation for A's round, so A's
`allAcked` poll can exit before A's descriptors are drained — a stale
TLB entry stays live on the target, the exact SMP-C4 hazard; and (b)
B's reset clears A's born-`true` flag, which nothing re-sets if A
polls with IRQs masked — a mutual hang.  SM7.B.7 therefore MUST
serialise rounds under the single global `ShootdownRoundLockId`
(below), acquired before any per-core `ShootdownQueueLockId`; every
serialisation statement in this module and in the Rust realisation
assumes exactly that contract.

## Capacity bound (SM7.A.6)

Every pending queue is bounded by `maxPendingPerCore = 16`
(plan §4.1): a typical kernel never queues more than a few
descriptors — the global round lock (see above) serialises rounds, so
at most one round's descriptors are in flight per target — and the
bound is deliberately conservative.  `enqueueShootdown` is
fail-closed: at capacity it returns `none` rather than silently
dropping or unboundedly growing, and `pendingBounded` is preserved
by every operation in this module.

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
  plan §3.2 step 4d) and for post-mortem trace attribution. -/
structure TlbShootdownDescriptor where
  op : TlbInvalidation
  initiator : CoreId
  deriving DecidableEq, Repr, Inhabited

-- ============================================================================
-- SM7.A.6 — Pending-queue capacity bound
-- ============================================================================

/-- **WS-SM SM7.A.6**: upper bound on each core's pending-shootdown
queue length (plan §4.1).  The global round lock (`ShootdownRoundLockId`
— the module-header round-serialisation contract) serialises shootdown
rounds, so a target's queue holds at most one round's descriptors at a
time; `16` is a conservative envelope over every SM7.B caller (the
worst wired unmap path enqueues one descriptor per target per round).
`enqueueShootdown` fails closed at this bound. -/
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

Both fields default to the quiescent boot values: empty queues and
all-acknowledged flags (`true` = "no round in flight, nobody waited
on"), matching `initial_shootdownQuiescent` and the Rust boot state. -/
structure TlbShootdownState where
  pendingShootdowns : Vector (List TlbShootdownDescriptor) numCores :=
    Vector.replicate numCores []
  shootdownAck : Vector Bool numCores :=
    Vector.replicate numCores true
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

/-- Per-core shootdown-acknowledgment flag of `st` on core `c`. -/
def ackOnCore (st : TlbShootdownState) (c : CoreId) : Bool :=
  st.shootdownAck.get c

/-- Write core `c`'s pending-shootdown queue slot. -/
def setPendingOnCore (st : TlbShootdownState) (c : CoreId)
    (q : List TlbShootdownDescriptor) : TlbShootdownState :=
  { st with pendingShootdowns := st.pendingShootdowns.set c.val q c.isLt }

/-- Write core `c`'s shootdown-acknowledgment flag slot. -/
def setAckOnCore (st : TlbShootdownState) (c : CoreId) (b : Bool) :
    TlbShootdownState :=
  { st with shootdownAck := st.shootdownAck.set c.val b c.isLt }

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
  simp [setPendingOnCore, ackOnCore]

@[simp] theorem setAckOnCore_ackOnCore_self (st : TlbShootdownState)
    (c : CoreId) (b : Bool) :
    (st.setAckOnCore c b).ackOnCore c = b := by
  simp [setAckOnCore, ackOnCore]

@[simp] theorem setAckOnCore_ackOnCore_ne (st : TlbShootdownState)
    (c c' : CoreId) (b : Bool) (h : c ≠ c') :
    (st.setAckOnCore c b).ackOnCore c' = st.ackOnCore c' := by
  simp only [setAckOnCore, ackOnCore]
  exact SeLe4n.PerCoreVector.get_set_ne st.shootdownAck c c' b h

@[simp] theorem setAckOnCore_pendingOnCore (st : TlbShootdownState)
    (c c' : CoreId) (b : Bool) :
    (st.setAckOnCore c b).pendingOnCore c' = st.pendingOnCore c' := by
  simp [setAckOnCore, pendingOnCore]

/-- **WS-SM SM7.A.2**: per-core extensionality.  Two shootdown states
are equal once their pending queues and ack flags agree at *every*
`CoreId`.  Named `ext_perCore` to avoid clashing with the structure's
auto-generated `TlbShootdownState.ext`; each per-core hypothesis lifts
to `Vector` equality via `SeLe4n.PerCoreVector.ext`. -/
theorem ext_perCore {s₁ s₂ : TlbShootdownState}
    (hPend : ∀ c : CoreId, s₁.pendingOnCore c = s₂.pendingOnCore c)
    (hAck : ∀ c : CoreId, s₁.ackOnCore c = s₂.ackOnCore c) :
    s₁ = s₂ := by
  have h1 : s₁.pendingShootdowns = s₂.pendingShootdowns :=
    SeLe4n.PerCoreVector.ext fun c => hPend c
  have h2 : s₁.shootdownAck = s₂.shootdownAck :=
    SeLe4n.PerCoreVector.ext fun c => hAck c
  obtain ⟨p₁, a₁⟩ := s₁
  obtain ⟨p₂, a₂⟩ := s₂
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

end TlbShootdownState

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

/-- **WS-SM SM7.A.3**: every core has acknowledged — the initiator
wait-loop's exit condition (plan §3.2 step 5).  Decidable so the
SM7.B wait loop and the test suite can evaluate it directly. -/
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
present whenever anything was dropped). -/
def enqueueShootdownOrCoalesce (st : TlbShootdownState) (target : CoreId)
    (d : TlbShootdownDescriptor) : TlbShootdownState :=
  match enqueueShootdown st target d with
  | some st' => st'
  | none =>
    st.setPendingOnCore target [{ op := .vmalle1, initiator := d.initiator }]

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
      [{ op := .vmalle1, initiator := d.initiator }] := by
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
    exact Or.inr ⟨{ op := .vmalle1, initiator := d.initiator }, by simp, rfl⟩

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
    exact ⟨{ op := .vmalle1, initiator := d.initiator }, by simp, rfl⟩

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
  simp [drainShootdowns]

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

/-- **WS-SM SM7.A.4 + SM7.A.5**: enqueue/drain round trip — the target's
handler drains exactly the pre-existing queue with the new descriptor
appended, in FIFO order. -/
theorem drainShootdowns_after_enqueue {st st' : TlbShootdownState}
    {target : CoreId} {d : TlbShootdownDescriptor}
    (h : enqueueShootdown st target d = some st') :
    (drainShootdowns st' target).1 = st.pendingOnCore target ++ [d] := by
  rw [drainShootdowns_fst, enqueueShootdown_pending_target h]

-- ============================================================================
-- SM7.A.3 — Acknowledgment operations
-- ============================================================================

/-- **WS-SM SM7.A.3**: mark core `c`'s round complete.

The target's SGI handler calls this *after* its drained invalidations
have retired locally (plan §3.2 step 4c).  In the Rust runtime this is
a release-store on `SHOOTDOWN_ACK[c]` — the release edge of the
SM7.B.4 release-acquire pairing that lets the initiator's acquire-poll
conclude the target's TLBIs happened-before the observed `true`. -/
def acknowledgeShootdown (st : TlbShootdownState) (c : CoreId) :
    TlbShootdownState :=
  st.setAckOnCore c true

/-- **WS-SM SM7.A.3**: acknowledging sets the caller's own flag. -/
@[simp] theorem acknowledgeShootdown_ackOnCore_self (st : TlbShootdownState)
    (c : CoreId) :
    (acknowledgeShootdown st c).ackOnCore c = true := by
  simp [acknowledgeShootdown]

/-- **WS-SM SM7.A.3**: acknowledging leaves every *other* core's flag
untouched — each target answers only for itself. -/
theorem acknowledgeShootdown_ackOnCore_ne (st : TlbShootdownState)
    {c c' : CoreId} (h : c' ≠ c) :
    (acknowledgeShootdown st c).ackOnCore c' = st.ackOnCore c' := by
  simp only [acknowledgeShootdown]
  exact TlbShootdownState.setAckOnCore_ackOnCore_ne st c c' true h.symm

/-- **WS-SM SM7.A.3**: acknowledging never touches any pending queue. -/
theorem acknowledgeShootdown_frame_pending (st : TlbShootdownState)
    (c c' : CoreId) :
    (acknowledgeShootdown st c).pendingOnCore c' = st.pendingOnCore c' := by
  simp [acknowledgeShootdown]

/-- **WS-SM SM7.A.6**: acknowledging preserves the capacity invariant. -/
theorem acknowledgeShootdown_preserves_pendingBounded {st : TlbShootdownState}
    (hB : pendingBounded st) (c : CoreId) :
    pendingBounded (acknowledgeShootdown st c) := by
  intro c'
  rw [acknowledgeShootdown_frame_pending]
  exact hB c'

/-- **WS-SM SM7.A.3**: acknowledgments only accumulate — a flag already
`true` stays `true` under further acknowledgments.  Monotonicity is
what makes the initiator's wait loop's exit condition stable
(`allAcked` cannot regress mid-round; only `beginShootdownRound`
resets flags, and the global round lock — the module-header
round-serialisation contract — serialises rounds). -/
theorem acknowledgeShootdown_monotone (st : TlbShootdownState)
    (c c' : CoreId) (h : st.ackOnCore c' = true) :
    (acknowledgeShootdown st c).ackOnCore c' = true := by
  by_cases hc : c' = c
  · subst hc
    simp
  · rw [acknowledgeShootdown_ackOnCore_ne st hc]
    exact h

/-- **WS-SM SM7.A.3**: an already-acknowledged flag survives any fold
of further acknowledgments — the inductive engine behind
`allCores_foldl_acknowledgeShootdown_allAcked`. -/
theorem foldl_acknowledgeShootdown_monotone {l : List CoreId}
    {st : TlbShootdownState} {c : CoreId} (h : st.ackOnCore c = true) :
    (l.foldl acknowledgeShootdown st).ackOnCore c = true := by
  induction l generalizing st with
  | nil => simpa using h
  | cons x xs ih =>
    rw [List.foldl_cons]
    exact ih (acknowledgeShootdown_monotone st x c h)

/-- **WS-SM SM7.A.3**: folding acknowledgments over a list sets the
flag of every core in the list. -/
theorem foldl_acknowledgeShootdown_sets {l : List CoreId}
    {st : TlbShootdownState} {c : CoreId} (hc : c ∈ l) :
    (l.foldl acknowledgeShootdown st).ackOnCore c = true := by
  induction l generalizing st with
  | nil => cases hc
  | cons x xs ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hc with hEq | hMem
    · subst hEq
      exact foldl_acknowledgeShootdown_monotone
        (acknowledgeShootdown_ackOnCore_self st _)
    · exact ih hMem

/-- **WS-SM SM7.A.3**: once every core has acknowledged, `allAcked`
holds — the state-level termination anchor for the SM7.B.5 initiator
wait loop (`shootdown_wait_loop_terminates`): the loop's exit
condition is *reachable* because acknowledging each core in
`allCores` (every `CoreId`, by `allCores` completeness) yields a
fully-acknowledged state, and monotonicity keeps it stable. -/
theorem allCores_foldl_acknowledgeShootdown_allAcked
    (st : TlbShootdownState) :
    allAcked (allCores.foldl acknowledgeShootdown st) := by
  intro c
  have hmem : c ∈ allCores := by
    simp [SeLe4n.Kernel.Concurrency.allCores]
  exact foldl_acknowledgeShootdown_sets hmem

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
which happens-after every previous ack-set). -/
def beginShootdownRound (st : TlbShootdownState) (initiator : CoreId) :
    TlbShootdownState :=
  { st with shootdownAck :=
      (Vector.replicate numCores false).set initiator.val true initiator.isLt }

/-- **WS-SM SM7.A.3**: the initiator is born-acknowledged. -/
@[simp] theorem beginShootdownRound_ackOnCore_initiator
    (st : TlbShootdownState) (initiator : CoreId) :
    (beginShootdownRound st initiator).ackOnCore initiator = true := by
  simp [beginShootdownRound, TlbShootdownState.ackOnCore]

/-- **WS-SM SM7.A.3**: every non-initiator core starts the round
unacknowledged — the initiator genuinely waits on each target. -/
theorem beginShootdownRound_ackOnCore_target (st : TlbShootdownState)
    {initiator c : CoreId} (h : c ≠ initiator) :
    (beginShootdownRound st initiator).ackOnCore c = false := by
  simp only [beginShootdownRound, TlbShootdownState.ackOnCore]
  rw [SeLe4n.PerCoreVector.get_set_ne _ initiator c true h.symm]
  exact SeLe4n.PerCoreVector.replicate_get numCores false c

/-- **WS-SM SM7.A.3**: at round start, a core is acknowledged iff it is
the initiator — the exact plan §3.2 step-1 postcondition. -/
theorem beginShootdownRound_ackOnCore_iff (st : TlbShootdownState)
    (initiator c : CoreId) :
    (beginShootdownRound st initiator).ackOnCore c = true ↔ c = initiator := by
  by_cases h : c = initiator
  · subst h
    simp
  · simp [beginShootdownRound_ackOnCore_target st h, h]

/-- **WS-SM SM7.A.3**: opening a round never touches any pending queue
(descriptors are posted by the subsequent per-target enqueues). -/
theorem beginShootdownRound_frame_pending (st : TlbShootdownState)
    (initiator c : CoreId) :
    (beginShootdownRound st initiator).pendingOnCore c =
      st.pendingOnCore c := by
  simp [beginShootdownRound, TlbShootdownState.pendingOnCore]

/-- **WS-SM SM7.A.6**: opening a round preserves the capacity
invariant. -/
theorem beginShootdownRound_preserves_pendingBounded
    {st : TlbShootdownState} (hB : pendingBounded st) (initiator : CoreId) :
    pendingBounded (beginShootdownRound st initiator) := by
  intro c
  rw [beginShootdownRound_frame_pending]
  exact hB c

-- ============================================================================
-- SM7.A — Target-masked round initialization (PR #838 review P1)
-- ============================================================================

/-- **WS-SM SM7.A (PR #838 review P1)**: closed form for a fold of
per-core ack clears — a core's flag is `false` exactly when the fold
visited it, and untouched otherwise. -/
theorem foldl_setAckFalse_ackOnCore (l : List CoreId) :
    ∀ (st : TlbShootdownState) (c : CoreId),
      (l.foldl (fun (s : TlbShootdownState) x => s.setAckOnCore x false)
          st).ackOnCore c =
        if c ∈ l then false else st.ackOnCore c := by
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
        exact TlbShootdownState.setAckOnCore_ackOnCore_ne st x c false
          (fun h => hce h.symm)

/-- **WS-SM SM7.A (PR #838 review P1)**: a fold of ack clears never
touches any pending queue. -/
theorem foldl_setAckFalse_pendingOnCore (l : List CoreId) :
    ∀ (st : TlbShootdownState) (c : CoreId),
      (l.foldl (fun (s : TlbShootdownState) x => s.setAckOnCore x false)
          st).pendingOnCore c =
        st.pendingOnCore c := by
  induction l with
  | nil => intro st c; rfl
  | cons x xs ih =>
    intro st c
    rw [List.foldl_cons, ih]
    simp

/-- **WS-SM SM7.A (PR #838 review P1)**: open a shootdown round against
an explicit **target set** — only the targets start unacknowledged;
every non-target (and the initiator) is born-`true`.

This is the model of the runtime's online-masked reset
(`reset_for_round_in_slice_masked`, `shootdown.rs`): in a partial-core
boot (`smp_enabled=false` — the v1.0.0 default — an `smp_max_cores`
cap, or a PSCI CPU_ON rejection), an offline core can never take the
`.tlbShootdownReq` SGI and acknowledge, so clearing its flag would
make `allAcked` permanently unreachable and hang the initiator's wait
loop.  Leaving it born-acknowledged is safe: every secondary bring-up
runs `tlbi vmalle1` before enabling its MMU
(`rust/sele4n-hal/src/mmu.rs::init_mmu_secondary`), so a core that was
offline during a round comes online with an empty TLB.  SM7.B's
target-set computation must pass exactly the online non-initiator
cores, and rounds must not race core bring-up (bring-up completes
during boot, before any user mapping exists to shoot down).

`beginShootdownRoundFor · allCores` is exactly `beginShootdownRound`
(`beginShootdownRoundFor_allCores_eq`) — the fully-online
configuration. -/
def beginShootdownRoundFor (st : TlbShootdownState) (initiator : CoreId)
    (targets : List CoreId) : TlbShootdownState :=
  (targets.foldl (fun (s : TlbShootdownState) c => s.setAckOnCore c false)
      { st with shootdownAck := Vector.replicate numCores true }).setAckOnCore
    initiator true

/-- **WS-SM SM7.A (PR #838 review P1)**: at a masked round's start, a
core is acknowledged iff it is the initiator or not a target — the
non-target ("offline") cores are never waited on. -/
theorem beginShootdownRoundFor_ackOnCore_iff (st : TlbShootdownState)
    (initiator : CoreId) (targets : List CoreId) (c : CoreId) :
    (beginShootdownRoundFor st initiator targets).ackOnCore c = true ↔
      (c = initiator ∨ c ∉ targets) := by
  unfold beginShootdownRoundFor
  by_cases hci : c = initiator
  · subst hci
    simp
  · rw [TlbShootdownState.setAckOnCore_ackOnCore_ne _ initiator c true
      (fun h => hci h.symm)]
    rw [foldl_setAckFalse_ackOnCore]
    by_cases hct : c ∈ targets
    · simp [hct, hci]
    · simp [hct, hci, TlbShootdownState.ackOnCore]

/-- **WS-SM SM7.A (PR #838 review P1)**: opening a masked round never
touches any pending queue. -/
theorem beginShootdownRoundFor_frame_pending (st : TlbShootdownState)
    (initiator : CoreId) (targets : List CoreId) (c : CoreId) :
    (beginShootdownRoundFor st initiator targets).pendingOnCore c =
      st.pendingOnCore c := by
  unfold beginShootdownRoundFor
  rw [TlbShootdownState.setAckOnCore_pendingOnCore,
      foldl_setAckFalse_pendingOnCore]
  rfl

/-- **WS-SM SM7.A (PR #838 review P1)**: opening a masked round
preserves the capacity invariant. -/
theorem beginShootdownRoundFor_preserves_pendingBounded
    {st : TlbShootdownState} (hB : pendingBounded st) (initiator : CoreId)
    (targets : List CoreId) :
    pendingBounded (beginShootdownRoundFor st initiator targets) := by
  intro c
  rw [beginShootdownRoundFor_frame_pending]
  exact hB c

/-- **WS-SM SM7.A (PR #838 review P1)**: with every core targeted, the
masked round-open is exactly `beginShootdownRound` — the fully-online
configuration collapses to the unmasked form (mechanically mirrored by
the Rust `sm7a3_masked_reset_all_online_equals_unmasked_reset` test). -/
theorem beginShootdownRoundFor_allCores_eq (st : TlbShootdownState)
    (initiator : CoreId) :
    beginShootdownRoundFor st initiator allCores =
      beginShootdownRound st initiator := by
  apply TlbShootdownState.ext_perCore
  · intro c
    rw [beginShootdownRoundFor_frame_pending, beginShootdownRound_frame_pending]
  · intro c
    by_cases hci : c = initiator
    · subst hci
      rw [(beginShootdownRoundFor_ackOnCore_iff st c allCores c).mpr
            (Or.inl rfl),
          beginShootdownRound_ackOnCore_initiator]
    · have hmem : c ∈ allCores := by
        simp [SeLe4n.Kernel.Concurrency.allCores]
      have h1 : (beginShootdownRoundFor st initiator allCores).ackOnCore c
          = false := by
        cases hval : (beginShootdownRoundFor st initiator allCores).ackOnCore c
        · rfl
        · exact absurd
            ((beginShootdownRoundFor_ackOnCore_iff st initiator allCores c).mp
              hval)
            (by simp [hci, hmem])
      rw [h1, beginShootdownRound_ackOnCore_target st hci]

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
  acknowledgeShootdown (drainShootdowns st c).2 c

/-- **WS-SM SM7.A**: the round step is definitionally the drain
followed by the acknowledgment — the handler's two state writes, in
the protocol's order. -/
theorem completeShootdownOnCore_eq (st : TlbShootdownState) (c : CoreId) :
    completeShootdownOnCore st c =
      acknowledgeShootdown (drainShootdowns st c).2 c := rfl

/-- **WS-SM SM7.B**: the handler's round step preserves the capacity
invariant — draining empties the handled core's queue and the
acknowledgment touches no queue at all.  Composes the drain and ack
preservation theorems for the `.tlbShootdownReq` handler's
`pendingBounded` bundle carriage. -/
theorem completeShootdownOnCore_preserves_pendingBounded
    {st : TlbShootdownState} (hB : pendingBounded st) (c : CoreId) :
    pendingBounded (completeShootdownOnCore st c) :=
  acknowledgeShootdown_preserves_pendingBounded
    (drainShootdowns_preserves_pendingBounded hB c) c

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
  simp

/-- **WS-SM SM7.A**: completing core `c` frames every other core's
queue. -/
theorem completeShootdownOnCore_frame_pending (st : TlbShootdownState)
    {c c' : CoreId} (h : c' ≠ c) :
    (completeShootdownOnCore st c).pendingOnCore c' = st.pendingOnCore c' := by
  unfold completeShootdownOnCore
  rw [acknowledgeShootdown_frame_pending, drainShootdowns_frame_pending st h]

/-- **WS-SM SM7.A**: completing core `c` frames every other core's
flag. -/
theorem completeShootdownOnCore_frame_ack (st : TlbShootdownState)
    {c c' : CoreId} (h : c' ≠ c) :
    (completeShootdownOnCore st c).ackOnCore c' = st.ackOnCore c' := by
  unfold completeShootdownOnCore
  rw [acknowledgeShootdown_ackOnCore_ne _ h, drainShootdowns_frame_ack]

/-- **WS-SM SM7.B**: round steps at *distinct* cores commute — each
step writes only its own core's queue and flag.  This is the
shootdown-state half of the handler-fold order-independence
(`handleTlbShootdownReqOnCore_comm` in `TlbShootdownProtocol.lean`):
the runtime's catch-up fold may visit targets in any order. -/
theorem completeShootdownOnCore_comm {c₁ c₂ : CoreId} (h : c₁ ≠ c₂)
    (st : TlbShootdownState) :
    completeShootdownOnCore (completeShootdownOnCore st c₁) c₂ =
      completeShootdownOnCore (completeShootdownOnCore st c₂) c₁ := by
  apply TlbShootdownState.ext_perCore
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
      rw [completeShootdownOnCore_frame_ack _ h,
          completeShootdownOnCore_ackOnCore_self,
          completeShootdownOnCore_ackOnCore_self]
    · by_cases h2 : c = c₂
      · subst h2
        rw [completeShootdownOnCore_ackOnCore_self,
            completeShootdownOnCore_frame_ack _ (Ne.symm h),
            completeShootdownOnCore_ackOnCore_self]
      · rw [completeShootdownOnCore_frame_ack _ h2,
            completeShootdownOnCore_frame_ack _ h1,
            completeShootdownOnCore_frame_ack _ h1,
            completeShootdownOnCore_frame_ack _ h2]

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
      exact (beginShootdownRoundFor_ackOnCore_iff st initiator targets c).mpr
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
structurally encodes "at most one round in flight". -/
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
