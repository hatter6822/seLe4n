-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM SM7.B (SM7.A shootdown descriptor + per-core
-- pending/ack state; consumed by the SM7.B shootdown protocol transitions
-- `tlbShootdownLocal` / `tlbShootdownBroadcast` and the `.tlbShootdownReq`
-- SGI handler when they land)
import SeLe4n.Kernel.Concurrency.Types
import SeLe4n.Kernel.Architecture.TlbiForSharing

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

Steps 2–4 are SM7.B transitions; this module supplies the state
layer they are built from, factored so the handler's TLBI
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

## Capacity bound (SM7.A.6)

Every pending queue is bounded by `maxPendingPerCore = 16`
(plan §4.1): a typical kernel never queues more than a few
descriptors — the VSpaceRoot write lock serialises initiators, so
at most one round's descriptors are in flight per target — and the
bound is deliberately conservative.  `enqueueShootdown` is
fail-closed: at capacity it returns `none` rather than silently
dropping or unboundedly growing, and `pendingBounded` is preserved
by every operation in this module.

## Production reachability

Staged: nothing in the production kernel constructs a
`TlbShootdownState` yet.  The SM7.B protocol transitions are the
first runtime exerciser; they mount this state and wire the
`.tlbShootdownReq` SGI handler.  Registered in
`SeLe4n/Platform/Staged.lean` + `scripts/staged_module_allowlist.txt`.
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
queue length (plan §4.1).  The VSpaceRoot write lock serialises
shootdown initiators, so a target's queue holds at most one round's
descriptors at a time; `16` is a conservative envelope over every
SM7.B caller (the worst wired unmap path enqueues one descriptor per
target per round).  `enqueueShootdown` fails closed at this bound. -/
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
  deriving Repr

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
resets flags, and the VSpaceRoot lock serialises rounds). -/
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
the VSpaceRoot write lock held by the initiator serialises rounds, so
a reset can never race a straggling acknowledgment from a previous
round (the previous initiator only released the lock after observing
`allAcked`, which happens-after every previous ack-set). -/
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

end SeLe4n.Kernel.Architecture
