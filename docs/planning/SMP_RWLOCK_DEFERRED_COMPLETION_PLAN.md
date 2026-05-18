# SM2.C Deferred Completion Plan — Verified RwLock (post-v1.0.0)

> **Phase**: SM2.C-defer (post-1.0 closure of WS-SM SM2.C)
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Origin plan**: [`SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md`](SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md) §5.3 (closed at audit-pass-3, HEAD `1109bda`)
> **Audited closure cut**: PR #784 (SM2.C closure with three audit passes)
> **Target releases**: v1.x.x post-v1.0.0 (calendar TBD; see §7 for sequencing)
> **Calendar estimate**: 12–20 weeks across 6 items
> **Sub-task count**: ~30 across 6 deferred items (D-1..D-6)

## 1. Phase goal

The WS-SM SM2.C workstream ("Verified RwLock spec + Rust impl + refinement
bridge") **closed at audit-pass-3** (commit `1109bda`, PR #784) with all
22 sub-tasks landed and 27 audit-pass refinements applied (8 HIGH + 11
MEDIUM + 8 LOW issues closed across three sequential deep audits).
However, **six items** in the original plan or in standard verification
best practice were delivered in **weakened form** or with documented
gaps:

| # | Deferred item | Plan reference | Current state | Target |
|---|--------------|----------------|---------------|--------|
| D-1 | Temporal FIFO admission | §3.3.7.1 (R-03) | Structural drop-prefix only | Trace-based temporal claim |
| D-2 | Writer-specific bounded wait | §3.3.8.2 (R-05) | Alias of `_read` | Distinct structural bound |
| D-3 | Full liveness theorem | §3.3.10.1 (R-10) | Single-step safety only | Multi-step liveness under fairness |
| D-4 | Full bisimulation refinement | §3.4.2 (F-02) | `rwLockSim` + witnesses + no-op | Trace-based refinement theorem |
| D-5 | Queued RwLock variant | §5.3 note | CAS-retry; no waiter queue | FIFO-preserving Rust impl |
| D-6 | Tier 5 cross-language tests | §6.3 | Not built | Lean↔Rust correspondence harness |

This plan describes the **optimal, complete implementation** of D-1 through
D-6. Each item is broken down into sub-tasks with formal signatures, proof
sketches, code skeletons, risk analysis, and calendar estimates.

**Closure**: SM2.C-defer fully closes at the end of D-1..D-6. After closure,
the SM2.C deliverables match the plan's strongest form: full FIFO admission
+ liveness + bisimulation + queued impl + cross-language tests.

## 2. Context: what SM2.C delivered vs. what is deferred

### 2.1 What SM2.C delivered (at HEAD `1109bda`)

* **Abstract spec** at `SeLe4n/Kernel/Concurrency/Locks/RwLock.lean` (~2440 LoC):
  - `AccessMode` + `RwLockState` + `RwLockOp` data types.
  - `applyOp` operational semantics with uniform `coreInvolved` no-op gate.
  - 5-conjunct `wf` invariant (INV-R1..R5; INV-R5 closes a reachability gap).
  - `promoteWaitersOnWriterRelease` + `promoteWaitersIfReadersEmpty` helpers.
  - **64 substantive theorems** in RwLock.lean + **6 in RwLockRefinement** (70
    total at HEAD `1109bda`; the original SM2.C.* enumeration of 32 grew to
    64 across the three audit passes that added preservation closures,
    bridging helpers, and structural-FIFO corollaries) covering
    writer-readers exclusion (`rwLock_writer_readers_exclusion` —
    NOT named `rwLock_mutex`; the latter is a colloquial label for this
    topic that does not appear in the codebase), reader multiplicity,
    structural FIFO claim, bounded wait, RA pairing, wf preservation,
    reader batching, single-step safety, no-op refinement preservation,
    and bit-packed encoding round-trips.

* **Refinement bridge** at `SeLe4n/Kernel/Concurrency/Locks/RwLockRefinement.lean`
  (~230 LoC): `rwLockSim` relation + 5 witness theorems + no-op preservation.

* **Rust impl** at `rust/sele4n-hal/src/rw_lock.rs` (~1020 LoC): bit-packed
  `AtomicU64` state with CAS-retry, audit-pass-fixed `fetch_sub` /
  `fetch_and` release semantics, defensive overflow check, RAII guards.
  28 unit tests including 4 cross-thread stress tests.

* **Lean test suite** at `tests/RwLockSuite.lean` (~640 LoC): 90+ surface
  anchors + 35+ decidable examples + 38 runtime assertions.

### 2.2 What is deferred (this plan)

The deferred items fall into three categories:

**Category A — Theorems delivered in weakened form** (D-1, D-2, D-3, D-4):
The plan specified stronger theorem statements; the v1.0.0 cut delivered
structural / single-step versions. The full forms require trace-based
reasoning, fairness assumptions, or impl modeling — substantial Lean
proof work but no new code paths.

**Category B — Alternative implementation deferred** (D-5):
The plan §5.3 explicitly deferred a "queued RwLock" variant that
preserves FIFO admission at the Rust impl level. The current CAS-retry
impl satisfies mutex+exclusion but not FIFO. A queued variant would
require lock-free linked-list management or a per-waiter event
mechanism.

**Category C — Test infrastructure not built** (D-6):
The plan §6.3 specified a "Tier 5" cross-language correspondence test
infrastructure. Neither SM2.A nor SM2.B built this; SM2.C inherited
the gap. Closing it requires a lake↔cargo test harness that doesn't
exist at v1.0.0.

### 2.3 What is NOT deferred (acknowledged but accepted as-is)

The `_deterministic` theorems (`rwLock_applyOp_deterministic` and
siblings) are trivial function-extensionality wrappers. The audit
pass-3 LOW-8 acknowledged these are decorative anchors; their
substantive content IS trivial (a total function's output is unique
by Lean's definitional equality). They remain in the spec as named
surface anchors for SM3 consumer convenience but are NOT addressed
in this plan — no improvement is possible without changing the
underlying mathematical property.

### 2.4 Why the D-1..D-6 theorems are NOT in the same "decorative" class

To pre-empt the audit concern that the deferred lemmas are themselves
`_deterministic`-style decoration, each deferred theorem has substantive
content beyond Lean's definitional equality:

* **D-1.6 / D-1.7 (append-or-noop / drop-or-noop)** — substantive: case
  analysis on the `coreInvolved` gate + FIFO head check, not a direct
  consequence of `rfl`. Compare: `rwLock_applyOp_deterministic`
  discharges by definitional equality of total functions; D-1.6/.7
  require unfolding `applyOp` and reasoning about the post-state
  `waiters` field structure.
* **D-1.8 (order preservation)** — substantive: combines D-1.6 + D-1.7
  with `List.idxOf` arithmetic to lift single-element membership to
  pairwise ordering.
* **D-1.9 (temporal FIFO)** — substantive: induction over execution
  length composing single-step claims; the inductive hypothesis is
  non-trivially indexed by `(c₁, c₂)` pairs.
* **D-2.3 (writerWaitDepth bounded)** — substantive: pigeonhole
  argument over the Nodup-CoreId combined list (the same shape as
  `rwLock_bounded_wait_read`'s proof, applied to a different sum).
* **D-2.4 (monotone under release)** — substantive: case analysis on
  release op + promote logic.
* **D-2.5 (bounded wait write)** — substantive: induction on the
  release-count budget.
* **D-3 (writer liveness)** — substantive: combines D-2.4 monotonicity
  with the fairness predicate over a trace; not derivable from any
  single-step claim.
* **D-4 (bisimulation)** — substantive: structural correspondence
  across a pair of independently-defined step semantics; not a
  function-extensionality property.
* **D-5 (queued impl)** — substantive: Rust code, not a Lean theorem.
* **D-6 (cross-language harness)** — substantive: test infrastructure,
  not a Lean theorem.

None of D-1..D-6 are "the post-state of a total function is determined
by the inputs" tautologies. They each require non-trivial proof or
implementation work.

## 3. Dependencies

### 3.1 Pre-existing infrastructure (already in tree)

- SM2.C closure at HEAD `1109bda` (the deferred items reference this baseline).
- Lean 4.28.0 toolchain.
- Std library: `List.Pairwise`, `List.Sublist`, `List.drop`, `List.takeWhile`,
  `List.dropWhile`, `Decidable.byContradiction`.
- SM2.A `MemoryModel.lean`: `MemoryTrace`, `MemoryEvent`, `MemoryOrder`,
  `synchronizesWith`, `happensBefore`.
- SM2.B `TicketLock.lean`: structural pattern reference (the `KernelStep` +
  `Reachable` inductive used here as the template for `Execution`).

### 3.2 New infrastructure required

- **For D-1**: `Execution` structure, **`RwLockKernelStep` + `Reachable`
  inductive** (mirroring SM2.B's `KernelStep` + `Reachable` template;
  see §4.1 for the rationale of requiring reachability instead of
  merely `wf`), trace-based reasoning primitives.
- **For D-2**: `writerWaitDepth` definition (independent; D-3 reuses).
- **For D-3**: `FairTrace` predicate (release-event-bracketed; see
  §4.5) + bounded-release primitives.
- **For D-4**: `ConcreteRwLockOp` event model + `concreteApplyOp`
  semantics over `UInt64` (NOT `Nat` — see §4.4 / §6.4 rationale) +
  reflexive-transitive closure for CAS-retry contention.
- **For D-5**: per-core fixed-slot waiter table (`[WaiterSlot;
  numCores]`) — the MCS-style design chosen over lock-free
  linked-list in §5.5 to eliminate ABA + dangling-pointer hazards.
- **For D-6**: in-process Rust-side cross-language harness driven
  via a `tier5_rwlock_shim` test-only Rust binary (NOT Lean linking
  against `libsele4n_hal.a`; see §5.6 for the fail-closed FFI
  discipline preservation).

### 3.3 External dependencies

No new external Lean libraries. No new Rust crate dependencies (the
queued impl uses only `core::sync::atomic` and `core::ptr`, already
present).

## 4. Mathematical foundations

This section introduces the formal primitives that D-1..D-4 depend on.
D-5 (Rust impl) and D-6 (test infra) build on these but don't require
new mathematical foundations beyond what's defined here.

### 4.1 Execution primitives

An **execution** is a finite sequence of operations applied to an
initial state. All deferred-completion theorems quantify over
executions whose initial state is `RwLockState.unheld` (or, more
generally, a state proven `Reachable` from `unheld` by the
operational-step closure).

**Why `Reachable`, not just `wf`** (closes audit finding M-3): the
operational `applyOp` at `RwLock.lean:613-626` admits a fast-path for
`tryAcquireRead` when the head waiter is itself a reader (the new
core acquires directly, bypassing the queue). Under arbitrary `wf`
initial states, the configuration `readers = [r0], waiters = [(r1,
.read), (w1, .write)], writerHeld = none` is `wf` but unreachable
from `unheld`. From it, `tryAcquireRead r3` admits `r3` before the
queued `r1`, violating any FIFO-order theorem.  We close this gap by
mirroring SM2.B's `KernelStep` + `Reachable` pattern (see
`TicketLock.lean:1834-1850`) and quantifying D-1..D-4 over
`Reachable`-witnessed executions only.

    namespace SeLe4n.Kernel.Concurrency

    /-- One-step transition relation on `RwLockState`.

    Mirrors the SM2.B `KernelStep` template — one constructor per
    `RwLockOp` constructor, each tying the post-state to `applyOp`. -/
    inductive RwLockKernelStep : RwLockState → RwLockState → Prop where
      | tryAcquireRead  (s : RwLockState) (core : CoreId) :
          RwLockKernelStep s (s.applyOp (.tryAcquireRead core))
      | releaseRead     (s : RwLockState) (core : CoreId) :
          RwLockKernelStep s (s.applyOp (.releaseRead core))
      | tryAcquireWrite (s : RwLockState) (core : CoreId) :
          RwLockKernelStep s (s.applyOp (.tryAcquireWrite core))
      | releaseWrite    (s : RwLockState) (core : CoreId) :
          RwLockKernelStep s (s.applyOp (.releaseWrite core))

    /-- Reflexive-transitive closure: `s` is `Reachable` iff there is
    a finite chain of `RwLockKernelStep`s from `unheld` to `s`. -/
    inductive Reachable : RwLockState → Prop where
      | base : Reachable RwLockState.unheld
      | step : ∀ {s s'}, Reachable s → RwLockKernelStep s s' → Reachable s'

    /-- A trace-based execution from a `Reachable` initial state.

    The structure pairs an `initial` state with a list of operations
    `ops` and a proof `initial_reachable` that the initial state is
    reachable from `unheld`.  Reachability implies `wf` (proved by
    `Reachable_implies_wf` below); we thus get `wf` "for free" without
    admitting wf-but-unreachable initial states (audit finding M-3).

    Execution semantics: fold `applyOp` over `ops` starting from
    `initial`.

    All deferred-completion theorems quantify over `Execution` values
    rather than ad-hoc trace lists, providing a uniform proof surface. -/
    structure Execution where
      initial            : RwLockState
      ops                : List RwLockOp
      initial_reachable  : Reachable initial
      deriving Repr

    /-- Reachability implies wf.  Proved by induction on `Reachable`
    using the existing `rwLock_wf_invariant` aggregator (audit-pass-3
    surface anchor). -/
    theorem Reachable_implies_wf {s : RwLockState} (h : Reachable s) : s.wf := by
      induction h with
      | base => exact RwLockState.unheld_wf
      | step h_prev h_step ih =>
          cases h_step <;> exact rwLock_wf_invariant _ _ ih

    /-- Convenience: an Execution's initial state is wf. -/
    theorem Execution.initial_wf (e : Execution) : e.initial.wf :=
      Reachable_implies_wf e.initial_reachable

    /-- The state after the first `k` operations of an execution. -/
    def Execution.stateAt (e : Execution) (k : Nat) : RwLockState :=
      (e.ops.take k).foldl RwLockState.applyOp e.initial

    /-- The final state of an execution. -/
    def Execution.finalState (e : Execution) : RwLockState :=
      e.stateAt e.ops.length

    /-- Witness: `stateAt 0` is the initial state. -/
    @[simp]
    theorem Execution.stateAt_zero (e : Execution) :
        e.stateAt 0 = e.initial := by simp [stateAt]

    /-- Witness: `stateAt e.ops.length` is the final state. -/
    theorem Execution.stateAt_length (e : Execution) :
        e.stateAt e.ops.length = e.finalState := rfl

    /-- The state after k+1 operations is `applyOp` applied to the state
    after k operations (provided k < length). -/
    theorem Execution.stateAt_succ (e : Execution) {k : Nat}
        (h : k < e.ops.length) :
        e.stateAt (k+1) = (e.stateAt k).applyOp (e.ops.get ⟨k, h⟩) := ...

    /-- **Foundational theorem**: every state in the execution is
    Reachable, hence wf.

    Proof: induction on k.  Base case: `stateAt 0 = initial`, reachable
    by hypothesis.  Inductive step: `stateAt (k+1) = (stateAt k).applyOp
    op = (RwLockKernelStep)`; apply `Reachable.step`. -/
    theorem Execution.stateAt_reachable (e : Execution) (k : Nat) :
        Reachable (e.stateAt k) := ...

    theorem Execution.stateAt_wf (e : Execution) (k : Nat) : (e.stateAt k).wf :=
      Reachable_implies_wf (e.stateAt_reachable k)

This gives us a uniform trace abstraction restricted to operationally
reachable states. All D-1..D-4 theorems are parameterized over
`Execution`, and consumers obtain both reachability AND wf at every
trace position for free.

### 4.2 Waiter membership and admission events

The temporal FIFO claim (D-1) and liveness theorem (D-3) need to
identify the trace position at which a waiter is enqueued and the
position at which it transitions to a holder.

    /-- True iff `(core, mode)` is in the waiters list at step `k`. -/
    def Execution.waiterAt (e : Execution) (k : Nat)
        (core : CoreId) (mode : AccessMode) : Prop :=
      (core, mode) ∈ (e.stateAt k).waiters

    /-- `waiterAt` is decidable (waiters is a `List`, mode/core are decidable). -/
    instance (e : Execution) (k : Nat) (core : CoreId) (mode : AccessMode) :
        Decidable (e.waiterAt k core mode) := by
      unfold Execution.waiterAt
      exact inferInstance

    /-- True iff `core` is a holder (reader or writer) at step `k`. -/
    def Execution.holderAt (e : Execution) (k : Nat) (core : CoreId) : Prop :=
      core ∈ (e.stateAt k).readers ∨ (e.stateAt k).writerHeld = some core

    instance : Decidable (Execution.holderAt e k core) := ...

    /-- The step at which `(core, mode)` is enqueued.

    Definition: the smallest `k ≥ 1` such that `(core, mode) ∈ waiters`
    at step `k` AND `(core, mode) ∉ waiters` at step `k - 1`.  In other
    words, `k` is the step at which membership TRANSITIONS from false to
    true.  Returns `none` if no such transition occurs.

    **Why the strict-transition formulation** (closes the second arm of
    audit finding M-3): a naive "first step at which `waiterAt k`" would
    return `k = 0` for any waiter present in `e.initial.waiters` (since
    initial state is at index 0), conflating all initial-state waiters
    into a single enqueue step and breaking FIFO order resolution between
    them.  The strict transition form returns `none` for initial waiters
    (they were not enqueued during the trace), which forces the FIFO
    theorem's `p₁ < p₂` hypothesis to be witnessed by genuine in-trace
    enqueue events.

    Combined with the `Execution.initial = RwLockState.unheld`
    precondition that D-1.9 will adopt (see §5.1), `enqueueStep` is
    well-defined for every waiter that appears in any reachable state. -/
    def Execution.enqueueStep (e : Execution)
        (core : CoreId) (mode : AccessMode) : Option Nat :=
      (List.range (e.ops.length + 1)).find? fun k =>
        decide (k ≥ 1) &&
        decide (e.waiterAt k core mode) &&
        decide (¬ e.waiterAt (k - 1) core mode)

    /-- The step at which `core` is admitted as a holder.

    Definition: the smallest `k ≥ 1` such that `holderAt k core` AND
    `¬ holderAt (k - 1) core`.  Same transition-edge rationale as
    `enqueueStep`. -/
    def Execution.admissionStep (e : Execution) (core : CoreId) : Option Nat :=
      (List.range (e.ops.length + 1)).find? fun k =>
        decide (k ≥ 1) &&
        decide (e.holderAt k core) &&
        decide (¬ e.holderAt (k - 1) core)

    /-- Witness: if `enqueueStep = some k`, then waiter membership flips
    on at step `k` and the previous step is non-membership. -/
    theorem Execution.enqueueStep_characterization (e : Execution)
        (core : CoreId) (mode : AccessMode) (k : Nat)
        (h : e.enqueueStep core mode = some k) :
        1 ≤ k ∧ e.waiterAt k core mode ∧ ¬ e.waiterAt (k - 1) core mode := ...

These are **computable** definitions (no `noncomputable`); the
implementation uses `List.find?` over a finite range. Decidability of
membership is automatic.

### 4.3 Writer wait depth

For D-2 (writer-specific bound) and D-3 (liveness), we need a measure
of how much "work" remains before a queued writer can be admitted.

    /-- The "wait depth" of a queued writer: the number of releases that
    must occur before the writer is at the head of waiters AND the
    holder set is empty.

    Components:
    1. Position of the writer in waiters (entries ahead in queue).
    2. Number of readers currently held (each must release).
    3. 1 if a writer currently holds (must release before promote).

    **Tight bound** (closes audit finding M-1): for a wf state with `c`
    queued as a writer, `writerWaitDepth s c ≤ numCores - 1`.  Derivation:
    `queueDepth = idxOf (c, .write) ≤ waiters.length - 1` (since `c` is
    in waiters).  From `rwLock_bounded_wait_read`:
    `waiters.length + readers.length + writerBit ≤ numCores`.  Therefore
    `idxOf + readers + writerBit ≤ (waiters.length + readers + writerBit)
    - 1 ≤ numCores - 1`.  The naive composition would yield
    `2 * numCores - 1` by independently bounding `idxOf ≤ numCores - 1`
    and `readers + writerBit ≤ numCores`; this double-counts the wf bound
    and is loose by a factor of ~2. -/
    def writerWaitDepth (s : RwLockState) (c : CoreId) : Nat :=
      let queueDepth := s.waiters.idxOf (c, AccessMode.write)
      let readerDepth := s.readers.length
      let writerDepth := if s.writerHeld.isSome then 1 else 0
      queueDepth + readerDepth + writerDepth

    /-- Decidable equality on `RwLockState` makes `writerWaitDepth` Decidable. -/
    @[simp] theorem writerWaitDepth_simp (s : RwLockState) (c : CoreId) :
        writerWaitDepth s c =
        s.waiters.idxOf (c, AccessMode.write) +
        s.readers.length +
        (if s.writerHeld.isSome then 1 else 0) := rfl

### 4.4 Concrete event model (for D-4 refinement)

The Rust impl operates on a single `AtomicU64` location. Each Rust
function performs one or more atomic operations. To bisimulate, we
model these operations as events in an SM2.A `MemoryTrace`.

**Concrete state type**: `UInt64`, not `Nat` (closes audit finding M-4).
Modelling `state - 1` as `Nat` subtraction truncates `0 - 1 = 0`,
whereas the Rust `fetch_sub(1)` on a `u64` of `0` wraps to
`u64::MAX`. The bisimulation must match the hardware's
modular-arithmetic semantics on every reachable input — including
the unreachable-but-mathematically-defined corners — or the proof of
D-4 cannot discharge by case analysis over `concreteApplyOp` without
an additional precondition that the SM3 consumer must restate at
every call site. Operating directly in `UInt64` makes the spec
hardware-faithful, and the conversion to the abstract `RwLockEncoded
:= Nat` happens at the `rwLockSim` bridge via `UInt64.toNat`.

**Why `.sev` carries a `core` argument** (closes audit finding L-7):
SEV is emitted by a specific core (the releaser), and the per-core
attribution matters for fairness reasoning (D-3): a fair-trace
predicate may need to relate "core c emitted SEV at step k" to "core
c'/= c parked on WFE at step k+1 was woken". A bare `.sev` constructor
without source would force fairness reasoning to thread the source
core through context, breaking compositionality.

    /-- A concrete Rust-level operation on the lock state.

    Each constructor represents one atomic memory operation the Rust
    impl performs.  The abstract `RwLockOp` may map to multiple
    `ConcreteRwLockOp`s (e.g., a `tryAcquireRead` is a load + CAS
    sequence, possibly with CAS-retry under contention).

    All constructors carry a `core : CoreId` (the executing core) for
    fairness-reasoning compositionality. -/
    inductive ConcreteRwLockOp where
      | load            (core : CoreId)                       -- load(Acquire)
      | casAcquireRead  (core : CoreId) (expected new : UInt64) -- CAS s → s+1
      | fetchSubRead    (core : CoreId)                       -- fetch_sub(1, Release)
      | casAcquireWrite (core : CoreId)                       -- CAS 0 → WRITER_BIT
      | fetchAndWrite   (core : CoreId)                       -- fetch_and(READER_MASK, Release)
      | sev             (core : CoreId)                       -- SEV broadcast from `core`
      | wfeWait         (core : CoreId)                       -- wfe_bounded park
      deriving Repr, DecidableEq

    /-- Apply a single concrete operation to the bit-packed state.

    Returns `(new_state, succeeded)`: the new state and whether the
    op succeeded (CAS may fail).  For non-CAS ops (load, fetch_sub,
    fetch_and, sev, wfe), `succeeded` is always `true`.

    `UInt64` arithmetic is modular over `2^64`, faithfully matching
    the Rust impl's `fetch_sub` / `fetch_and` behaviour on a `u64`
    field — including underflow (`0 - 1 = u64::MAX`) and bitmask
    composition. -/
    def concreteApplyOp (state : UInt64) (op : ConcreteRwLockOp) :
        UInt64 × Bool :=
      match op with
      | .load _ => (state, true)  -- load returns the value, doesn't modify state
      | .casAcquireRead _ expected new =>
          if state = expected then (new, true) else (state, false)
      | .fetchSubRead _ => (state - 1, true)  -- u64 wrap on underflow
      | .casAcquireWrite _ =>
          if state = 0 then (writerBit.toUInt64, true) else (state, false)
      | .fetchAndWrite _ => (state &&& readerMask.toUInt64, true)
      | .sev _ => (state, true)
      | .wfeWait _ => (state, true)

    /-- Abstract operation → permissible concrete operation sequences.

    Each `RwLockOp` corresponds to a non-empty FAMILY of concrete
    sequences, not a single deterministic sequence, because:

    1. **CAS-retry under contention** (closes audit finding M-5): the
       Rust `acquire_read` loops on CAS failure.  A single abstract
       `tryAcquireRead` may map to `[load; cas-success]` OR
       `[load; cas-fail; load; cas-success]` OR longer chains under
       arbitrary contention.

    2. **Park-and-retry under writer held**: when a writer holds, the
       Rust impl `wfe_bounded`-parks and reloads.  The concrete
       sequence is `[load; wfeWait; load; cas-success]` or longer.

    3. **Conditional SEV emission** (closes audit finding M-6): the
       Rust `release_read` emits SEV only when `(prev & WRITER_BIT) ==
       0 && (prev & READER_MASK) == 1`.  Otherwise the sequence is
       `[fetchSubRead]` without trailing SEV.  Symmetric for
       `release_write`.

    We capture this with a sum-of-products structure: per abstract op,
    a list of permissible CONCRETE sub-patterns, and we close under
    the contention-retry idiom.  The base shapes are formalised below;
    the closure under CAS-retry is captured by `opCorresponds_closure`
    (a coinductive admissibility predicate). -/
    inductive opCorresponds : RwLockOp → List ConcreteRwLockOp → Prop where
      -- tryAcquireRead: success-first-try shape.
      | tryRead_success (c : CoreId) :
          opCorresponds (.tryAcquireRead c)
            [.load c, .casAcquireRead c default default]
      -- tryAcquireRead: CAS-retry on contention.
      | tryRead_cas_retry (c : CoreId) (tail : List ConcreteRwLockOp) :
          opCorresponds (.tryAcquireRead c) tail →
          opCorresponds (.tryAcquireRead c)
            ([.load c, .casAcquireRead c default default] ++ tail)
      -- tryAcquireRead: writer-held park-and-retry on contention.
      | tryRead_park_retry (c : CoreId) (tail : List ConcreteRwLockOp) :
          opCorresponds (.tryAcquireRead c) tail →
          opCorresponds (.tryAcquireRead c)
            ([.load c, .wfeWait c] ++ tail)
      -- releaseRead: SEV-suppressed (post-state still has holders).
      | releaseRead_no_sev (c : CoreId) :
          opCorresponds (.releaseRead c) [.fetchSubRead c]
      -- releaseRead: SEV-emitted (post-state empty).
      | releaseRead_with_sev (c : CoreId) :
          opCorresponds (.releaseRead c) [.fetchSubRead c, .sev c]
      -- tryAcquireWrite: analogous to tryRead (success / cas-retry /
      -- park-retry).  Definitions elided here; same structural shape.
      | tryWrite_success (c : CoreId) : ...
      | tryWrite_cas_retry (c : CoreId) (tail : ...) : ...
      | tryWrite_park_retry (c : CoreId) (tail : ...) : ...
      -- releaseWrite: SEV-emitted iff writer-bit was actually cleared.
      | releaseWrite_no_sev (c : CoreId) :
          opCorresponds (.releaseWrite c) [.fetchAndWrite c]
      | releaseWrite_with_sev (c : CoreId) :
          opCorresponds (.releaseWrite c) [.fetchAndWrite c, .sev c]

The refinement theorem (D-4) proves: for any abstract op and ANY
admissible concrete sequence (by `opCorresponds`), the abstract
`applyOp` produces a state related to the concrete `concreteApplyOp`-
fold under `rwLockSim`. The proof case-splits on the `opCorresponds`
constructor, with CAS-failure / WFE-wait branches preserving
`rwLockSim` (no state change on either side), and successful
acquire / release branches advancing both sides in lock-step.

### 4.5 Fairness predicate (for D-3 liveness)

    /-- An execution is "release-fair" if every holder releases within
    a bounded number of steps after acquiring.

    `maxDelay` is a parameter of the fairness assumption — it
    represents the kernel-level critical-section duration bound that
    SM3+ consumers must satisfy.  In the spec this is left as a
    parameter; in the runtime it's enforced by the scheduler.

    **Predicate strength** (closes audit finding M-2): both `*_fairness`
    conjuncts require the release event to be a *transition* edge —
    `c ∈ readers` at step `k_release` AND `c ∉ readers` at step
    `k_release + 1`.  A naive `c ∉ readers at (k_release + 1)` alone
    is vacuously satisfiable by any trace where `c` is never a reader
    in the window (e.g., `c` momentarily acquired and then was never
    a reader again at any later step).  The transition-edge form
    forces the release event to actually exist within the bounded
    window. -/
    structure FairTrace (e : Execution) (maxDelay : Nat) where
      /-- Every reader-acquire is paired with a reader-release transition
      within `maxDelay` subsequent steps.

      "Reader-acquire at step k_acq" is witnessed by
      `c ∈ readers (k_acq) ∧ c ∉ readers (k_acq - 1)` (for k_acq ≥ 1),
      i.e., an in-trace transition from non-reader to reader.

      The conclusion asserts an in-trace transition from reader to
      non-reader within the window: `c ∈ readers (k_rel) ∧
      c ∉ readers (k_rel + 1)`. -/
      reader_fairness :
        ∀ k_acq c,
          1 ≤ k_acq →
          c ∈ (e.stateAt k_acq).readers →
          c ∉ (e.stateAt (k_acq - 1)).readers →
          ∃ k_rel, k_acq ≤ k_rel ∧ k_rel ≤ k_acq + maxDelay ∧
            c ∈ (e.stateAt k_rel).readers ∧
            c ∉ (e.stateAt (k_rel + 1)).readers
      /-- Same shape for writers: every writer-acquire is paired with a
      writer-release transition within `maxDelay` steps. -/
      writer_fairness :
        ∀ k_acq c,
          1 ≤ k_acq →
          (e.stateAt k_acq).writerHeld = some c →
          (e.stateAt (k_acq - 1)).writerHeld ≠ some c →
          ∃ k_rel, k_acq ≤ k_rel ∧ k_rel ≤ k_acq + maxDelay ∧
            (e.stateAt k_rel).writerHeld = some c ∧
            (e.stateAt (k_rel + 1)).writerHeld ≠ some c

This fairness predicate is the v1.0.0 substitute for full temporal
reasoning. In practice, kernel critical sections are bounded by the
scheduler's preemption window; encoding this as a Lean predicate over
traces is sufficient for the liveness theorem to be meaningful.

## 5. Detailed sub-task breakdown

### 5.1 D-1: Temporal FIFO admission (10 sub-tasks)

**Plan reference**: SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md §3.3.7.1, theorem R-03.

**Plan statement (target)**:

> If c₁ enqueues as a waiter at trace position p₁ < p₂ = c₂'s enqueue
> position, then c₁ becomes a holder before c₂ does.

**Current state (HEAD `1109bda`)**: structural drop-prefix claim
(`∃ k, post.waiters = s.waiters.drop k`) plus three corollaries
(`subset_of_waiters`, `is_sublist_of_waiters`, `pair_in_drop`).

**Gap**: the structural claim addresses single-step promotion; the
plan's claim is multi-step across a trace. SM3 consumers can derive
the temporal claim by composing the structural claim with the
"tryAcquire appends to tail" property, but this composition is not
itself proven.

**Optimal target**: the theorem statement above, proven for executions
whose initial state is `RwLockState.unheld`.  Quantifying over arbitrary
`wf` initial states fails (audit M-3 counter-example): the wf-but-
unreachable state `readers = [r0], waiters = [(r1, .read), (w1, .write)],
writerHeld = none` admits `tryAcquireRead r3` to bypass queued `r1`,
inverting FIFO.  Restricting to `initial = unheld` (which the `Execution`
type already provides via `Reachable_implies_wf`) eliminates this class
of states.

#### Sub-tasks

| Sub | Description | Theorem / artifact | Est |
|-----|-------------|--------------------|-----|
| D-1.1 | `RwLockKernelStep` + `Reachable` inductive + `Execution` (with `initial_reachable` field) | (definitions) | S |
| D-1.2 | `Reachable_implies_wf` + `Execution.stateAt_reachable` + `Execution.stateAt_wf` aggregates | Theorem | S |
| D-1.3 | `waiterAt` / `holderAt` decidable predicates | (definitions) | T |
| D-1.4 | `enqueueStep` / `admissionStep` (strict-transition form per §4.2) | (definitions) | T |
| D-1.5 | `enqueueStep_characterization` witness theorem | Theorem | S |
| D-1.6 | Append-to-tail property for `tryAcquire*` (concrete `(core, mode)` from op, not existential) | Theorem | M |
| D-1.7 | Drop-prefix property for `release*` (concrete `k` determined by promote, not existential) | Theorem | M |
| D-1.8 | Order-preservation across single op (using D-1.6 + D-1.7) | Theorem | L |
| D-1.9 | **`rwLock_fifo_admission_temporal`** main theorem (under `initial = unheld`) | Theorem | XL |
| D-1.10 | Tests + surface anchors | tests | M |

#### Theorem statements

```lean
/-- Definitional helper: the `(core, mode)` an enqueueing op appends. -/
def RwLockOp.coreOfOp : RwLockOp → CoreId
  | .tryAcquireRead  c => c
  | .tryAcquireWrite c => c
  | .releaseRead     c => c
  | .releaseWrite    c => c

def RwLockOp.modeOfOp : RwLockOp → AccessMode
  | .tryAcquireRead  _ => .read
  | .tryAcquireWrite _ => .write
  | _                  => .read  -- unreached when guarded by op-shape

/-- **Lemma (D-1.6)**: `tryAcquire*` either is a no-op or appends EXACTLY
the op's `(core, mode)` at the tail.

The post-state's `waiters` is either equal to the pre-state's `waiters`
(no-op case: `coreInvolved core` was true OR the op succeeded into
`readers`/`writerHeld`) or equals `pre.waiters ++ [(op.coreOfOp,
op.modeOfOp)]` where the appended pair is the SPECIFIC pair from the op
(NOT an arbitrary existential — closes audit finding L-1).  This
precision matters for D-1.8: order-preservation reasoning uses the
specific appended pair to identify which waiters were already in
`pre.waiters`. -/
theorem tryAcquire_waiters_append_or_noop
    (s : RwLockState) (op : RwLockOp)
    (h_op_is_tryAcquire : op matches .tryAcquireRead _ ∨ op matches .tryAcquireWrite _) :
    (s.applyOp op).waiters = s.waiters ∨
    (s.applyOp op).waiters = s.waiters ++ [(op.coreOfOp, op.modeOfOp)]

/-- The number of waiters consumed by a single release-and-promote step
on state `s`, determined by the existing promote logic:
- 0 if no promote applies (no holders to release, or readers still
  present after release).
- 1 if head waiter is a writer.
- `takeWhile (·.2 = .read) |>.length` if head waiter is a reader
  (batch-promoted reader prefix). -/
def RwLockState.promoteDropCount (s : RwLockState) : Nat :=
  if s.writerHeld.isSome ∨ s.readers ≠ [] then 0
  else
    match s.waiters with
    | []               => 0
    | (_, .write) :: _ => 1
    | (_, .read)  :: _ => s.waiters.takeWhile (fun w => w.2 = .read) |>.length

/-- **Lemma (D-1.7)**: `release*` either is a no-op or consumes EXACTLY
`promoteDropCount` entries from the head of `waiters`.

The post-state's `waiters` is either equal to the pre-state's `waiters`
(no-op: releaser not actually a holder) or equals
`pre.waiters.drop (postReleaseState.promoteDropCount)` where
`postReleaseState` is the intermediate state AFTER the releaser is
removed from holders but BEFORE the promote runs.  Stating the drop
count by definition (rather than as an existential `∃ k ≥ 1`) closes
audit finding L-1 and lets D-1.8 reason about exact survivors. -/
theorem release_waiters_drop_or_noop
    (s : RwLockState) (op : RwLockOp)
    (h_op_is_release : op matches .releaseRead _ ∨ op matches .releaseWrite _) :
    -- One of:
    -- (a) op is no-op: post = pre, waiters unchanged.
    (s.applyOp op).waiters = s.waiters ∨
    -- (b) op is effective: waiters dropped by promoteDropCount of the
    --     intermediate post-release-pre-promote state.
    (∃ s_inter, s_inter.writerHeld = none ∧
                s_inter.readers = s.readers.filter (· ≠ op.coreOfOp) ∧
                s_inter.waiters = s.waiters ∧
                (s.applyOp op).waiters = s_inter.waiters.drop s_inter.promoteDropCount)

/-- **Lemma (D-1.8)**: relative order of two waiters is preserved across a
single `applyOp` step, provided both waiters survive.

This is the "order-preserving" property the temporal claim cascades from. -/
theorem applyOp_preserves_waiter_order
    (s : RwLockState) (op : RwLockOp)
    (w₁ w₂ : CoreId × AccessMode)
    (h_in₁ : w₁ ∈ s.waiters) (h_in₂ : w₂ ∈ s.waiters)
    (h_order : s.waiters.idxOf w₁ < s.waiters.idxOf w₂)
    (h_post₁ : w₁ ∈ (s.applyOp op).waiters)
    (h_post₂ : w₂ ∈ (s.applyOp op).waiters) :
    (s.applyOp op).waiters.idxOf w₁ < (s.applyOp op).waiters.idxOf w₂

/-- **D-1.9 main theorem**: temporal FIFO admission.

For an execution `e` starting from `RwLockState.unheld` and two waiters
`(c₁, m₁)`, `(c₂, m₂)` enqueued at trace positions `p₁ < p₂` (under the
strict-transition form of `enqueueStep` from §4.2), if `c₂` is admitted
at step `a₂`, then `c₁` is admitted at step `a₁ ≤ a₂`.

The conclusion is **non-strict** `≤` (not `<`) because reader batching
admits multiple readers in one promote step: if `(c₁, .read)` is at
position 0 and `(c₂, .read)` is at position 1, they are batch-promoted
together — `a₁ = a₂`. Heterogeneous-mode pairs (writer + reader, in
either order) yield strict `<` by INV-R1; the non-strict bound is the
correct unifying claim (closes audit finding L-4).  The informal
"becomes a holder before" wording should be read as "no later than"
(the `≤` form), with strict-`<` following automatically when modes
differ.

**Initial-state restriction** (closes audit finding M-3):
`e.initial = RwLockState.unheld`.  Quantifying over arbitrary `wf`
initial states fails — the wf-but-unreachable state with mixed-mode
initial waiters admits FIFO-inverting reader bypass via the
`applyOp .tryAcquireRead` reader-head fast-path. -/
theorem rwLock_fifo_admission_temporal
    (e : Execution)
    (h_initial_unheld : e.initial = RwLockState.unheld)
    (c₁ c₂ : CoreId) (m₁ m₂ : AccessMode) (p₁ p₂ a₂ : Nat)
    (h_enqueue₁ : e.enqueueStep c₁ m₁ = some p₁)
    (h_enqueue₂ : e.enqueueStep c₂ m₂ = some p₂)
    (h_order : p₁ < p₂)
    (h_admitted₂ : e.admissionStep c₂ = some a₂) :
    ∃ a₁, e.admissionStep c₁ = some a₁ ∧ a₁ ≤ a₂
```

#### Proof sketch

By induction on the execution length, using two key invariants:

1. **Append-to-tail (D-1.6)**: `tryAcquire*` only adds to the tail of
   `waiters`; existing waiters' positions only increase (i.e., their
   absolute index in `waiters` is unchanged by appends since they're
   already in the list).

2. **Consume-from-head (D-1.7)**: `release*` (via `promote*`) only
   removes from the head; surviving waiters' positions decrease by
   exactly the drop count.

3. **Order preservation (D-1.8)**: combining (1) and (2), two waiters
   in the queue maintain their relative order across any single op.

4. **Temporal FIFO (D-1.9)**: by induction over the execution, the
   relative order is preserved across the whole trace. Therefore,
   admission (transition out of waiters into holders) of c₂ implies
   that any earlier-enqueued waiter (c₁ at position p₁ < p₂) must have
   been admitted at an earlier step.

#### Tests

```lean
-- Concrete trace starting from `unheld`: boot acquires writer; three
-- writers queue behind; boot releases; chain of admissions follows.
-- All quantification is over an `Execution` with `initial = unheld`,
-- satisfying D-1.9's precondition.
example :
    let e : Execution :=
      { initial := RwLockState.unheld,
        ops := [.tryAcquireWrite boot,    -- boot becomes writer
                .tryAcquireWrite c1,      -- c1 queued at position 0
                .tryAcquireWrite c2,      -- c2 queued at position 1
                .tryAcquireWrite c3,      -- c3 queued at position 2
                .releaseWrite boot,       -- promotes c1 to writerHeld
                .releaseWrite c1,         -- promotes c2
                .releaseWrite c2 ],       -- promotes c3
        initial_reachable := Reachable.base }
    -- The temporal theorem says: admission order matches enqueue order.
    -- For heterogeneous writers, the inequality is strict (`<`); the
    -- non-strict `≤` form generalises to the reader-batching case.
    (e.admissionStep c1).get! < (e.admissionStep c2).get! ∧
    (e.admissionStep c2).get! < (e.admissionStep c3).get! := by decide
```

**Estimated effort**: 3-4 weeks of Lean proof work.

**Risk**: HIGH. The proof requires careful position arithmetic across
trace-based `idxOf` reasoning; the existing `dropWhile_eq_drop_takeWhile_length`
helper handles the structural case but extending to multi-step requires
new positional invariants.

### 5.2 D-2: Writer-specific bounded wait (6 sub-tasks)

**Plan reference**: SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md §3.3.8.2, theorem R-05.

**Plan statement (target)**:

> `WCRT(tryAcquireWrite) ≤ (coreCount - 1) × T_cs`

**Current state**: literal alias of `rwLock_bounded_wait_read`.

**Gap**: a meaningfully writer-specific bound.

**Optimal target**: a structural bound on `writerWaitDepth` that
distinguishes writer waits from reader waits. The bound depends on the
in-flight count of readers plus queued waiters ahead, NOT the
symmetric "all involved cores" bound.

#### Sub-tasks

| Sub | Description | Theorem / artifact | Est |
|-----|-------------|--------------------|-----|
| D-2.1 | `writerWaitDepth` definition | (definition) | T |
| D-2.2 | Decidability of `writerWaitDepth` | instance | T |
| D-2.3 | `writerWaitDepth_bounded`: ≤ numCores - 1 (TIGHT bound) | Theorem | M |
| D-2.4 | `writerWaitDepth_monotone_under_effective_release`: reduces by ≥ 1 per effective release | Theorem | M |
| D-2.5 | `rwLock_bounded_wait_write_distinct`: bounded admission via release-event count | Theorem | M |
| D-2.6 | Tests + surface anchors | tests | S |

#### Theorem statements

```lean
/-- **D-2.3**: writer wait depth is bounded by `numCores - 1` (tight).

Closes audit finding M-1: the naive composition would yield
`2 * numCores - 1` by independently bounding `idxOf ≤ numCores - 1`
and `readers + writer_bit ≤ numCores`; this double-counts the wf
bound.  Substituting `idxOf ≤ waiters.length - 1` (since `c ∈ waiters`)
into `waiters.length + readers + writer_bit ≤ numCores` (the existing
`rwLock_bounded_wait_read`) gives `idxOf + readers + writer_bit ≤
numCores - 1`.  Per CLAUDE.md's `implement-the-improvement` rule, the
tight bound is the canonical statement.

Concrete instantiation: `numCores = 4` on RPi5 gives depth ≤ 3. -/
theorem writerWaitDepth_bounded
    (s : RwLockState) (h : s.wf)
    (c : CoreId) (h_queued : (c, .write) ∈ s.waiters) :
    writerWaitDepth s c ≤ numCores - 1

/-- An op is an **effective release** for `s` if it actually transitions
some holder out of `readers` or `writerHeld` (i.e., is not a no-op).
This is the precise notion that D-2.4 needs (closing audit finding L-2:
no more hand-waved `h_progress`). -/
def RwLockState.isEffectiveRelease (s : RwLockState) (op : RwLockOp) : Prop :=
  match op with
  | .releaseRead  c => c ∈ s.readers
  | .releaseWrite c => s.writerHeld = some c
  | _               => False

/-- **D-2.4**: each EFFECTIVE release operation strictly reduces
`writerWaitDepth`, provided `c` remains queued in the post-state.

Closes audit finding L-2: the precise progress condition is "the op is
an effective release", not a hand-waved arithmetic comparison. -/
theorem writerWaitDepth_monotone_under_effective_release
    (s : RwLockState) (h : s.wf)
    (c : CoreId) (h_queued : (c, .write) ∈ s.waiters)
    (op : RwLockOp)
    (h_op_release : op matches .releaseRead _ ∨ op matches .releaseWrite _)
    (h_effective : s.isEffectiveRelease op)
    (h_still_queued : (c, .write) ∈ (s.applyOp op).waiters) :
    writerWaitDepth (s.applyOp op) c + 1 ≤ writerWaitDepth s c

/-- **D-2.5**: writer-specific bounded wait, counted in effective-release
events along the execution.

For any execution `e` starting from `unheld` and a writer `c` queued at
some step `k` (witnessed by `e.enqueueStep c .write = some k`), `c` is
admitted within at most `writerWaitDepth (e.stateAt k) c` subsequent
effective-release events.

Closes audit finding M-9: the previous "depth=0 means admitted on next
release" formulation collided with the operational semantics —
`applyOp` does not proactively promote without an explicit release op,
so a "depth=0 with no holder" state is transient and only arises AS
PART of a release-and-promote step.  The corrected induction is on the
number of pending effective releases, not on the depth at a single
state. -/
theorem rwLock_bounded_wait_write_distinct
    (e : Execution)
    (h_initial_unheld : e.initial = RwLockState.unheld)
    (c : CoreId) (k : Nat)
    (h_enqueued_at : e.enqueueStep c .write = some k) :
    ∃ a, e.admissionStep c = some a ∧
         -- `a - k` ≤ depth × bounded constant.  In particular, the
         -- number of EFFECTIVE-RELEASE events between step k and a is
         -- at most `writerWaitDepth (e.stateAt k) c`.
         countEffectiveReleases e k a ≤ writerWaitDepth (e.stateAt k) c
```

#### Proof sketch

- D-2.3 (tight bound): pigeonhole on the Nodup CoreId set
  `waiters.map Prod.fst ++ readers ++ writerHeld.toList`.
  - `idxOf c ≤ waiters.length - 1` (since `c ∈ waiters`, so
    `waiters.length ≥ 1`).
  - From `rwLock_bounded_wait_read`:
    `waiters.length + readers.length + writer_bit ≤ numCores`.
  - Substituting:
    `idxOf c + readers.length + writer_bit
       ≤ (waiters.length - 1) + readers.length + writer_bit
       = (waiters.length + readers.length + writer_bit) - 1
       ≤ numCores - 1`.

- D-2.4: case analysis on `op` with `isEffectiveRelease` discharged.
  - `releaseRead c'`: `c' ∈ s.readers`, so `s.readers.length` decreases
    by exactly 1 in the post-state.  If `c` survives in waiters, the
    promote either didn't fire (queue head was a writer; or readers
    still non-empty) — in which case `idxOf c` is unchanged and the
    sum decreases by 1 — or the promote fired and consumed some prefix
    that did NOT include `c` (because `c` survived) — in which case
    `idxOf c` decreased by the prefix length, also yielding a strict
    decrease.
  - `releaseWrite c'`: `s.writerHeld = some c'`, so `writer_bit` drops
    from 1 to 0 in the post-state.  Same survival analysis on `idxOf`.

- D-2.5 (corrected induction on release-event count):
  - Base case: 0 effective releases between `k` and `a` means
    `writerWaitDepth (e.stateAt k) c = 0` — `c` is at queue head AND
    no holders.  By the operational `applyOp` semantics, the only step
    that can take `c` out of `waiters` is an effective release with
    promote.  If `writerWaitDepth (e.stateAt k) c = 0`, the state at
    step `k` is a transient "just released" state (the promote step
    that put `(c, .write)` at head also placed `c` into `writerHeld`
    atomically — they happen in the same `applyOp .releaseWrite` /
    `applyOp .releaseRead` invocation).  Strictly, the state where `c`
    is queued AND depth=0 AND no holders is only reachable as a
    transient intermediate; the next operational step puts `c` into
    `writerHeld` (or, if `c`'s mode were `.read`, into `readers` —
    but D-2.5 is for writers).
  - Inductive step: depth = n+1 ⇒ at least one barrier
    (reader / writer holder / queued predecessor) blocks `c`.  The
    next effective release in the trace (which exists by the fairness
    hypothesis pushed into the consumer; here we just count events
    without invoking fairness — that's D-3's job) decreases the
    depth by 1 via D-2.4.  Induction discharges.

  `countEffectiveReleases e k a` is a helper computing the number of
  `applyOp` steps between trace positions `k` and `a` that satisfy
  `(e.stateAt i).isEffectiveRelease (e.ops.get i)`.

**Estimated effort**: 1-2 weeks.

**Risk**: LOW. The proofs are pigeonhole + structural arithmetic +
event-count induction.

### 5.3 D-3: Full liveness theorem (8 sub-tasks)

**Plan reference**: SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md §3.3.10.1, theorem R-10.

**Plan statement (target)**:

> Under the FIFO admission discipline, a waiter for write access is
> always eventually admitted, provided the set of read holders turns
> over (i.e., readers release within bounded time).

**Current state**: single-step safety only (writer in waiters stays in
waiters after a fresh `tryAcquireRead`).

**Gap**: the multi-step liveness claim requires temporal reasoning
over infinite traces with fairness assumptions.

**Optimal target**: prove that under a `FairTrace` assumption (every
holder releases within bounded steps), every queued writer is eventually
admitted within a bounded number of steps.

#### Sub-tasks

| Sub | Description | Theorem / artifact | Est |
|-----|-------------|--------------------|-----|
| D-3.1 | `FairTrace` predicate definition | (definition) | M |
| D-3.2 | Decidability of `FairTrace` (Decidable for finite traces) | instance | S |
| D-3.3 | `fair_release_reduces_writerWaitDepth`: fairness + queue → progress | Theorem | L |
| D-3.4 | `writer_eventually_at_head`: under fairness, writer reaches queue head | Theorem | L |
| D-3.5 | `writer_at_head_eventually_admitted`: head writer is admitted | Theorem | M |
| D-3.6 | **`rwLock_writer_liveness`** main theorem | Theorem | XL |
| D-3.7 | `MAX_RELEASE_DELAY` parameterization for kernel-runtime config | (definition) | S |
| D-3.8 | Tests + surface anchors | tests | M |

#### Theorem statements

The `FairTrace` predicate is defined in §4.5 above with the
strengthened transition-edge formulation (closes audit finding M-2).
D-3 consumes it as a black-box hypothesis.

```lean
-- (FairTrace defined in §4.5; reproduced here only as a reminder of
-- the strengthened "transition-edge" form that closes audit M-2.)

/-- **D-3.3**: under fairness, each step where the writer is still
queued, an effective release occurs within `maxDelay` subsequent steps,
strictly reducing the writer's wait depth.

This is the "progress" theorem that drives the liveness proof.

Note: the `e.initial = unheld` precondition matches D-1.9 and D-2.5 —
arbitrary wf initial states are not admitted (audit finding M-3
propagates into D-3). -/
theorem fair_release_reduces_writerWaitDepth
    (e : Execution) (maxDelay : Nat) (h_fair : FairTrace e maxDelay)
    (h_initial_unheld : e.initial = RwLockState.unheld)
    (c : CoreId)
    (k : Nat) (h_queued : (c, .write) ∈ (e.stateAt k).waiters) :
    -- Either c is admitted within the window, OR the depth strictly
    -- decreases within the window via an effective release.
    (∃ j, k < j ∧ j ≤ k + maxDelay ∧ (e.stateAt j).writerHeld = some c) ∨
    (∃ j, k < j ∧ j ≤ k + maxDelay ∧
          (c, .write) ∈ (e.stateAt j).waiters ∧
          writerWaitDepth (e.stateAt j) c < writerWaitDepth (e.stateAt k) c)

/-- **D-3.6 main theorem**: writer liveness under fairness.

For any execution starting from `unheld`, satisfying `FairTrace e
maxDelay`, and containing a writer `c` enqueued at some step `k`
(witnessed by `e.enqueueStep c .write = some k`), the writer is
admitted within `writerWaitDepth (e.stateAt k) c × maxDelay` subsequent
steps.

The tight upper bound on `writerWaitDepth` is `numCores - 1` per
D-2.3, so the total admission window is bounded by
`(numCores - 1) × maxDelay`.  Concrete instantiation on RPi5
(numCores = 4): admission window ≤ `3 × maxDelay`. -/
theorem rwLock_writer_liveness
    (e : Execution) (maxDelay : Nat) (h_fair : FairTrace e maxDelay)
    (h_initial_unheld : e.initial = RwLockState.unheld)
    (c : CoreId) (k_enq : Nat)
    (h_enqueued_at : e.enqueueStep c .write = some k_enq) :
    ∃ a, e.admissionStep c = some a ∧
         a ≤ k_enq + writerWaitDepth (e.stateAt k_enq) c * maxDelay
```

#### Proof sketch

- D-3.3: `writerWaitDepth` is bounded by `numCores - 1` (D-2.3 tight
  bound).  Under `FairTrace` (strengthened §4.5 form), if `c` is queued
  at step `k`, there must be at least one holder by INV-R5; by
  `*_fairness`, that holder transitions out within `maxDelay` steps
  (transition-edge: the predicate forces a real release event, closing
  audit M-2).  Each effective release reduces `writerWaitDepth` by ≥ 1
  (D-2.4 with `isEffectiveRelease`).  Disjunction in the conclusion:
  either `c` is promoted to writerHeld within the window (the release
  was the LAST barrier), or `c` is still queued with strictly smaller
  depth.

- D-3.4: by induction on `writerWaitDepth`.  Base case: depth = 0 with
  `c` queued is operationally a transient state (see D-2.5 base-case
  discussion); the very same `applyOp` step that produces depth = 0
  also moves `c` into `writerHeld`.  So depth = 0 at any step ⇒ `c` is
  admitted at that step.

- D-3.5: when writer is at queue head and the next release fires, the
  promote logic admits `c` (or batch-promotes preceding readers,
  reducing depth — covered by D-3.3's strict-decrease disjunct).

- D-3.6: combine D-3.3 (window-bounded depth decrease) + D-3.4 (depth =
  0 ⇒ admitted).  The total number of steps is bounded by
  `writerWaitDepth × maxDelay` (each "unit of depth" cleared takes at
  most `maxDelay` steps).  Termination of the induction is by
  well-founded recursion on `writerWaitDepth`, which is bounded by
  `numCores - 1` so trivially terminates.

**Estimated effort**: 3-4 weeks.

**Risk**: HIGH. The fairness predicate is delicate; the induction
requires careful handling of the `k_acq → k_rel` tracking under the
strengthened transition-edge form.

### 5.4 D-4: Full bisimulation refinement (10 sub-tasks)

**Plan reference**: SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md §3.4.2, theorem F-02.

**Plan statement (target)**:

```
theorem rust_rwLock_refines_lean :
  ∀ (impl_trace : MemoryTrace) (lean_trace : List RwLockOp),
    impl_trace.wellFormed →
    rustImplementsRwLock impl_trace lean_trace →
    rwLockSim (lean_trace.foldl applyOp .unheld) impl_trace
```

**Current state**: `rwLockSim` relation + 5 witness theorems +
`_noop` preservation.

**Gap**: full bisimulation requires modeling the Rust impl's atomic
step function in Lean, plus a structural correspondence predicate
`rustImplementsRwLock`.

**Optimal target**: prove the full bisimulation using the
`ConcreteRwLockOp` event model from §4.4 and a Lean-side abstract of
the Rust impl's step semantics.

#### Sub-tasks

| Sub | Description | Theorem / artifact | Est |
|-----|-------------|--------------------|-----|
| D-4.1 | `ConcreteRwLockOp` inductive (with `.sev` carrying `CoreId`) + `concreteApplyOp` over `UInt64` | (definition) | M |
| D-4.2 | `opCorresponds` inductive (with CAS-retry / WFE-park / conditional-SEV constructors) | (definition) | M |
| D-4.3 | `rustImplementsRwLock`: full concrete-trace ↔ abstract-op-list correspondence (closes over D-4.2's permissible sequences) | (definition) | L |
| D-4.4 | `concreteApplyOp_preserves_sim_load`: load doesn't modify state | Theorem | S |
| D-4.5 | `concreteApplyOp_preserves_sim_cas_acquire_read`: CAS-success step (+ companion `cas_fail` preservation) | Theorem | L |
| D-4.6 | `concreteApplyOp_preserves_sim_fetch_sub`: release_read step (with the u64-wrap precondition `readers > 0` discharged) | Theorem | L |
| D-4.7 | `concreteApplyOp_preserves_sim_cas_acquire_write` | Theorem | L |
| D-4.8 | `concreteApplyOp_preserves_sim_fetch_and`: release_write step | Theorem | L |
| D-4.9 | **`rust_rwLock_refines_lean`** main theorem | Theorem | XL |
| D-4.10 | Tests + surface anchors | tests | M |

#### Theorem statements

```lean
/-- **D-4.1**: see §4.4 — `abbrev ConcreteState := UInt64` (audit M-4),
`ConcreteRwLockOp` inductive with `.sev (core : CoreId)` (audit L-7),
`concreteApplyOp : UInt64 → ConcreteRwLockOp → UInt64 × Bool` using
modular `UInt64` arithmetic. -/

/-- **D-4.2**: see §4.4 — `opCorresponds` inductive with explicit
constructors for success / CAS-retry / WFE-park / conditional-SEV
emission (audits M-5, M-6).  A SINGLE abstract op maps to a FAMILY of
permissible concrete sequences. -/

/-- **D-4.3**: a Rust trace implements a Lean op list iff the concrete
sequence can be split into per-abstract-op blocks, each admissible by
`opCorresponds`.

`splitByOps` non-deterministically partitions the concrete trace into
sub-lists; the predicate witnesses some splitting that satisfies
`opCorresponds` pointwise. -/
def rustImplementsRwLock
    (conc : List ConcreteRwLockOp) (abs : List RwLockOp) : Prop :=
  ∃ (blocks : List (List ConcreteRwLockOp)),
    blocks.length = abs.length ∧
    blocks.flatten = conc ∧
    List.zipWith opCorresponds abs blocks |>.all id

/-- **D-4.6 precondition discharge**: under any reachable abstract
state, if the next abstract op is `.releaseRead c` and `c ∈
abs.readers`, then `abs.readers.length ≥ 1`, so the concrete
`fetch_sub(1)` on a `UInt64` with `readers.length ≤ writerBit - 1`
operates above the underflow boundary.  The u64-wrap corner
(`state = 0 → state - 1 = u64::MAX`) is provably unreachable. -/
theorem concreteApplyOp_fetch_sub_no_underflow
    (abs : RwLockState) (conc : UInt64) (c : CoreId)
    (h_sim : rwLockSim abs conc)
    (h_holder : c ∈ abs.readers) :
    conc ≥ 1

/-- **D-4.9 main theorem**: bisimulation.

For any abstract operation list and corresponding concrete trace
(under the `opCorresponds`-closed correspondence relation), applying
the abstract `applyOp` fold and the concrete `concreteApplyOp` fold
produces related states. -/
theorem rust_rwLock_refines_lean
    (initial_abs : RwLockState) (initial_conc : UInt64)
    (h_sim_init : rwLockSim initial_abs initial_conc)
    (h_initial_reachable : Reachable initial_abs)
    (abs_ops : List RwLockOp)
    (conc_ops : List ConcreteRwLockOp)
    (h_corresponds : rustImplementsRwLock conc_ops abs_ops) :
    let final_abs := abs_ops.foldl RwLockState.applyOp initial_abs
    let final_conc := (conc_ops.foldl concreteApplyOp initial_conc).1
    rwLockSim final_abs final_conc
```

#### Proof sketch

By induction on `abs_ops`:

- Base case: `[]` — `rustImplementsRwLock` forces `conc_ops = []`;
  both states unchanged; `rwLockSim` preserved by hypothesis.

- Inductive step: take one abstract op + its corresponding block of
  concrete ops (witnessed by the `splitByOps` partition).  Case
  analysis on the `opCorresponds` constructor for this block:
  - **`tryRead_success`**: `[.load c, .casAcquireRead c ...]`.  The
    `.load` doesn't change concrete state (D-4.4).  The `.casAcquireRead`
    either:
    - Succeeds: concrete state `s → s + 1`.  The abstract op enters
      the "acquire-direct" branch of `applyOp` (no `coreInvolved`, no
      writer held, no queued-writer-head).  Abstract `readers` grows
      by 1.  `rwLockSim` preserved: new `conc = encodeRwLock false
      (readers.length + 1) = encodeRwLock false readers.length + 1
      = s + 1`.
    - Fails (state changed under our feet): this constructor isn't
      hit — the `tryRead_cas_retry` constructor would have been used
      instead.
  - **`tryRead_cas_retry`**: `[.load c, .casAcquireRead-fail c ..., tail]`
    where `tail` recursively corresponds to `.tryAcquireRead c`.  The
    failed CAS leaves concrete state unchanged.  Abstract: the
    `tryRead_cas_retry` constructor represents a SINGLE abstract op
    (`.tryAcquireRead c`); the inductive hypothesis on `tail` discharges.
  - **`tryRead_park_retry`**: same shape — `.wfeWait` doesn't modify
    state; recurse on `tail`.
  - **`releaseRead_no_sev`**: `[.fetchSubRead c]`.  Concrete `s → s - 1`
    (audit M-4: this is `UInt64` modular subtraction; the precondition
    `s ≥ 1` is discharged by D-4.6 helper, so no underflow occurs).
    Abstract: `readers` shrinks by 1 via filter.  `rwLockSim`
    preserved by the readers-length decrement.
  - **`releaseRead_with_sev`**: `[.fetchSubRead c, .sev c]`.  The
    `.sev` is a no-op on state.  Same analysis as `_no_sev` (audit
    M-6: the conditional SEV is now a separate `opCorresponds`
    constructor; the proof handles both shapes uniformly).
  - **`tryWrite_*` / `releaseWrite_*`**: analogous structural shape.

The key invariant: at each step, `rwLockSim abs conc` says
`conc.toNat = encodeRwLock abs.writerHeld.isSome abs.readers.length`.
We prove this is preserved by each `opCorresponds`-permitted
abstract/concrete step pair.

**Estimated effort**: 5-8 weeks. This is the largest sub-task in the
plan.

**Risk**: HIGH. The proof depth grows with the number of
`opCorresponds` constructors (success / cas-retry / park-retry /
sev-emitted / sev-suppressed for each of acquire-read / release-read /
acquire-write / release-write = ~16 cases).  Each case is mechanical
once the invariant is set up; the work is in scripting the case
analysis without exploding the proof term.

### 5.5 D-5: Queued RwLock variant (8 sub-tasks)

**Plan reference**: SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md §5.3 note,
"SM2.C.19.a may extend to a queued RwLock".

**Current state**: CAS-retry Rust impl with NO waiter queue. FIFO not
enforced at impl level.

**Gap**: a queued Rust impl that preserves the Lean spec's FIFO
admission property.

**Optimal target**: an **MCS-style queued RwLock** with per-core fixed
slots (NOT a lock-free linked-list).  The design rationale follows.

#### Design choice: per-core MCS slots, not lock-free linked-list

The original §5.5 sketch proposed a stack-allocated `WaiterNode` with
`AtomicPtr<WaiterNode>` linked-list management.  Three audit findings
ruled that design out:

* **H-1 (FIFO violation in fast-path)**: the `acquire_read` fast-path
  loaded `state` and `waiter_head` non-atomically; a concurrent
  `enqueue_waiter` between the two loads could be bypassed by the
  fast-path CAS — silently breaking the FIFO property the queued
  variant exists to preserve.
* **H-2 (lifetime safety not enforced by borrow checker)**: storing a
  `&mut WaiterNode` into an `AtomicPtr<WaiterNode>` deliberately
  bypasses the borrow checker.  Soundness requires a protocol the
  borrow checker cannot enforce (the waiter must never return until
  `parked == true`); the original sketch claimed "borrow-checker
  enforces" which is false.
* **M-7 (simpler designs avoid both)**: for the project's bounded
  `numCores = 4` (witnessed by SM0.E `numCores_pos` /
  `allCores_length`), a per-core fixed-slot queue avoids ABA, avoids
  dangling pointers, avoids heap allocation, and is straightforward
  to verify.  Per CLAUDE.md's "trusted computing base must stay small"
  principle, we adopt the simplest sound design.

**Adopted design**: an MCS-style FIFO queue where each core has ONE
preallocated slot in a per-lock `[WaiterSlot; numCores]` array
(`numCores = 4`).  Lock holds `(tail_slot_idx : AtomicU8)` indexing
into the array (or `NONE_SENTINEL = u8::MAX` if empty).  Each
`WaiterSlot` stores `next : AtomicU8` (successor slot idx) and
`parked : AtomicBool`.

**Heap-free, ABA-free, lifetime-safe**:

* No heap allocation (`alloc` is unavailable in `no_std` kernel
  build).  The slot array lives inside the lock structure.
* No ABA (slot indices are 8-bit; addresses are not used in CAS).
* No dangling pointers (slots are statically owned by the lock; their
  storage outlives any waiter).
* The "crossbeam-like" reference in the original §5.5 risk inventory
  is misleading (closes audit L-3): crossbeam requires `alloc`.  The
  reference patterns are the Linux kernel's `osq_lock` (optimistic
  spin-queue) and the classical MCS paper [Mellor-Crummey, Scott
  TOPLAS 1991], both heap-free.

**FIFO preservation in the fast-path** (closes audit H-1): the only
admission path is via the queue.  There is NO state-only fast-path —
every acquire enqueues first, observes its predecessor (or absence
thereof + immediate-admit predicate on state), and waits.  Heuristic
"is the lock free right now" loads are checks AFTER enqueue, not
before, eliminating the bypass race.

#### Sub-tasks

| Sub | Description | Artifact | Est |
|-----|-------------|----------|-----|
| D-5.1 | `WaiterSlot` + `MAX_WAITERS = numCores` slot array + `NONE_SENTINEL` | Rust | M |
| D-5.2 | `enqueue_self`: atomic swap on `tail_slot_idx` + back-link via predecessor's `next` | Rust | L |
| D-5.3 | `dequeue_head`: head-side promotion on release | Rust | L |
| D-5.4 | Per-slot `parked: AtomicBool` event mechanism (single-writer per slot) | Rust | M |
| D-5.5 | `QueuedRwLock::acquire_read/write` with enqueue-then-park (no fast-path bypass) | Rust | L |
| D-5.6 | `QueuedRwLock::release_read/write` with successor signal | Rust | L |
| D-5.7 | Refinement bridge update: FIFO no longer "deferred" | Lean | M |
| D-5.8 | Cross-thread stress tests + Miri runs + loom-style coverage | Rust | L |

#### Rust impl skeleton (revised — MCS-style)

```rust
// rust/sele4n-hal/src/queued_rw_lock.rs

#![allow(unsafe_code)]  // documented unsafe blocks at call sites

use core::sync::atomic::{AtomicBool, AtomicU8, AtomicU64, Ordering};

/// Sentinel meaning "no slot" — indexes outside the [0, numCores)
/// range cannot collide with a real slot index.
const NONE_SENTINEL: u8 = u8::MAX;

/// Number of waiter slots — one per core.  Pinned to
/// `PlatformBinding::coreCount` at compile time via the existing
/// `MAX_CORE_COUNT_SYM` constant from SM1.B.
const MAX_WAITERS: usize = crate::smp::MAX_CORE_COUNT;
const _: () = assert!(MAX_WAITERS <= 255,
    "WaiterSlot indices are u8; MAX_WAITERS must fit in u8.");

/// One waiter slot — exactly one per core.  The slot is OWNED by the
/// lock for the duration of the program; no heap or stack allocation
/// is involved.  This eliminates lifetime hazards (audit H-2).
#[repr(C, align(64))]  // cache-line aligned to avoid false sharing
struct WaiterSlot {
    /// Index of the next slot in the FIFO queue, or NONE_SENTINEL if
    /// this is the tail.  Single-writer (the OWNING core, while in
    /// queue); single-reader (the predecessor or the lock-holder).
    next: AtomicU8,
    /// True when the slot owner has been admitted.  Single-writer
    /// (the predecessor or the lock-holder); single-reader (the
    /// slot owner).
    parked: AtomicBool,
    /// Requested access mode at enqueue time.  Single-writer (the
    /// slot owner at enqueue); read-only thereafter.
    mode: AtomicU8,  // 0 = .read, 1 = .write
}

#[repr(C, align(64))]
pub struct QueuedRwLock {
    /// Bit-packed reader count + writer bit (same layout as RwLock).
    state: AtomicU64,
    /// Index of the tail slot, or NONE_SENTINEL if no waiters queued.
    /// Single CAS-mutation point for enqueue.
    tail: AtomicU8,
    /// Index of the head slot, or NONE_SENTINEL if no waiters queued.
    /// Mutated by the lock-holder under exclusion (only one thread
    /// holds the writer bit, and readers don't touch head).
    head: AtomicU8,
    /// Per-core waiter slots.  Slot `i` is owned by `CoreId i`.
    slots: [WaiterSlot; MAX_WAITERS],
}

impl QueuedRwLock {
    pub const fn new() -> Self {
        // const fn array init: every slot starts unused.
        Self {
            state: AtomicU64::new(0),
            tail: AtomicU8::new(NONE_SENTINEL),
            head: AtomicU8::new(NONE_SENTINEL),
            slots: [
                // const-fn-able WaiterSlot::INIT
                WaiterSlot::INIT, WaiterSlot::INIT,
                WaiterSlot::INIT, WaiterSlot::INIT,
            ],
        }
    }

    /// Acquire read access.  FIFO-preserving: every caller enqueues
    /// itself before checking immediate-admission predicates; there is
    /// NO state-only fast-path that could bypass a concurrently-
    /// enqueueing waiter (closes audit H-1).
    ///
    /// # Safety
    ///
    /// Each `CoreId` MUST call only with its own `core_id` value.
    /// Each core has exactly one slot; reentrance / cross-core use of
    /// a slot is UB.  The hardware bound `core_id < MAX_WAITERS` is
    /// asserted at the entry; under `panic = "abort"` an out-of-range
    /// call halts the kernel rather than aliasing a sibling's slot.
    pub fn acquire_read(&self, core_id: u8) {
        assert!((core_id as usize) < MAX_WAITERS, "core_id out of range");
        let slot = &self.slots[core_id as usize];

        // Step 1: prepare own slot.  Single-writer (this core).
        slot.next.store(NONE_SENTINEL, Ordering::Relaxed);
        slot.parked.store(false, Ordering::Relaxed);
        slot.mode.store(0 /* .read */, Ordering::Relaxed);

        // Step 2: enqueue at tail via atomic swap.  After this point
        // we are visible to release_* paths.
        let prev_tail = self.tail.swap(core_id, Ordering::AcqRel);

        if prev_tail == NONE_SENTINEL {
            // We are the head.  Try to admit immediately if state
            // allows.  This check happens AFTER enqueue, so a
            // concurrent acquire_write that increments writer-bit
            // BEFORE our swap is observed by us via the swap's
            // Acquire fence; we wait via the parked loop.
            self.head.store(core_id, Ordering::Release);
            if self.try_admit_self_as_reader() { return; }
        } else {
            // Link predecessor to us.  Predecessor will signal us
            // when it releases / is admitted.
            // SAFETY: prev_tail < MAX_WAITERS by AcqRel swap's
            // observation invariant; the slot is owned by core prev_tail.
            self.slots[prev_tail as usize].next.store(core_id, Ordering::Release);
        }

        // Step 3: wait until predecessor signals us.
        // SAFETY: `slot.parked` is single-writer (the predecessor or
        // the lock holder).  We never return until parked == true, so
        // the slot remains in-queue throughout (closes audit H-2 by
        // EXPLICIT PROTOCOL: this loop is the lifetime-safety
        // mechanism, and the loop is documented as the safety contract).
        while !slot.parked.load(Ordering::Acquire) {
            crate::cpu::wfe_bounded(crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS);
        }

        // We are admitted; head is owned by us until we transition out
        // (via promote chain on next release).
    }

    /// Try to atomically convert self-at-head into a reader if state
    /// permits.  Returns true on success; false if state is held by a
    /// writer and we must wait via parked loop.
    fn try_admit_self_as_reader(&self) -> bool { ... }

    pub fn release_read(&self, core_id: u8) { ... }
    pub fn acquire_write(&self, core_id: u8) { ... }
    pub fn release_write(&self, core_id: u8) { ... }
}
```

**Safety invariants of the per-slot protocol** (closes audit H-2):

1. **Slot ownership**: `slots[i]` is owned by `CoreId(i)`.  Cross-core
   writes to another core's slot are restricted to specific fields
   (`next` written by predecessor at enqueue; `parked` written by
   predecessor at admit) under the documented single-writer
   discipline.
2. **Slot lifetime**: `slots` lives for the lifetime of the lock,
   which is a static or arena-bound object.  No stack-allocated
   nodes, no dangling pointers, no AtomicPtr.
3. **Park loop is the safety mechanism**: each `acquire_*` MUST NOT
   return until `parked == true`.  The `loop`+`wfe_bounded` structure
   makes this explicit: timeouts retry the loop, not return.  Panics
   on `panic = "abort"` (mandatory for `no_std` per
   `rust/Cargo.toml:33`) terminate the kernel, so a partial-release
   panic between enqueue and admit is impossible.
4. **No ABA**: indices are bounded `[0, numCores)` integers; the same
   slot index returning to play is the SAME slot, not a freed-and-
   reused different slot.  ABA-free by construction.

#### Refinement update

After D-5 lands, the `RwLockRefinement.lean` FIFO divergence
documentation should be updated:

```lean
-- BEFORE (current):
-- "The Rust CAS-retry impl satisfies mutex + exclusion but NOT FIFO."

-- AFTER (post-D-5):
-- "The Rust QueuedRwLock impl preserves FIFO admission, matching the
-- Lean spec's rwLock_fifo_admission_temporal theorem.  The CAS-retry
-- RwLock impl is retained for backward compatibility; new SM3
-- consumers requiring FIFO should use QueuedRwLock."
```

#### Tests (D-5.8) — strengthened acceptance gate (closes audit M-10)

```rust
// 1. FIFO verification: NUM_WRITERS writers contend; admission order
//    matches enqueue order.  Repeated 10⁴ iterations to surface races.
#[test]
fn queued_rwlock_writer_fifo() { ... }

// 2. Mixed reader/writer stress.
#[test]
fn queued_rwlock_mixed_stress() { ... }

// 3. Self-test for slot ownership invariants (no cross-core slot
//    mutation outside the documented single-writer protocol).
#[test]
fn queued_rwlock_slot_ownership() { ... }

// 4-N. Additional stress configurations.
```

**Acceptance gate** (per §8):

* ≥10 cross-thread tests covering FIFO, mutex, mixed-stress,
  panic-safety, and slot-ownership invariants.
* Each FIFO test repeats ≥10⁴ iterations.
* All tests pass under `cargo +nightly miri test -p sele4n-hal --lib
  queued_rw_lock` with `-Zmiri-strict-provenance`.
* All tests pass under loom-style exhaustive interleaving on op
  sequences of length ≤ 4 (see `loom` crate; integrated via
  `cfg(loom)`).

**Estimated effort**: 4-5 weeks.

**Risk**: MEDIUM (was HIGH for the linked-list design; reduced by
adopting the per-core fixed-slot MCS-style approach).  No ABA, no
heap, no dangling pointers, no borrow-checker bypass — these classes
of bugs are eliminated by construction.  Remaining risk: getting the
release-path successor-signaling protocol right, which is a smaller
state space than the linked-list version.

### 5.6 D-6: Tier 5 cross-language correspondence tests (6 sub-tasks)

**Plan reference**: SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md §6.3.

**Plan statement (target)**:

> Tier 5 (NEW for SM2): cross-language correspondence tests exercising
> both Lean spec and Rust impl on small operation sequences; verifies
> the simulation φ holds.

**Current state**: not built. SM2.A and SM2.B both omitted Tier 5
infrastructure; SM2.C inherited the gap.

**Gap**: an integration harness that runs both Lean and Rust on the
same op sequence and compares states via `rwLockSim`.

**Optimal target**: a Tier 5 test infrastructure that:

1. Generates structured + random operation sequences (`List
   RwLockOp`).
2. Runs the Lean spec's `applyOp` fold and serialises the final
   `RwLockState` to a deterministic textual form (`lake exe
   rw_lock_oracle`).
3. Runs the equivalent Rust ops against an actual `RwLock` /
   `QueuedRwLock` and serialises the post-state to the same form
   (`cargo run -p sele4n-hal --bin rw_lock_oracle`).
4. A driver script diffs the two oracle outputs op-sequence by
   op-sequence; mismatches are surfaced as test failures.
5. Integrated into CI as a Tier 5 gate.

**Design choice: process-boundary harness, NOT Lean linking against
`libsele4n_hal.a`** (closes audit findings H-3 and M-8):

The original §5.6 sketch had two soundness problems.  First, it
proposed adding link-time FFI access from Lean test executables to
the HAL — directly violating the WS-RC R12.B fail-closed FFI
discipline documented in `SeLe4n/Platform/FFI.lean:67-72` ("any path
that reaches an `@[extern]` symbol without the Rust HAL linked would
surface as a missing-symbol link error at build time").  Second, the
harness passed lock state as a UInt64 argument (`ffiRwLockAcquireRead
: UInt64 → BaseIO UInt64`), which is incompatible with the actual
Rust impl's `&self` AtomicU64 (you cannot inject state externally).
The harness as written would test a STUB that simulates the lock,
not the real impl.

The revised design uses **two independent oracle binaries** that
communicate via deterministic text on stdin/stdout:

* `lake exe rw_lock_oracle` — a Lean program that reads a serialised
  op-sequence from stdin, folds `applyOp` over it, prints the post-
  state.  Pure Lean; no FFI; respects the fail-closed discipline.
* `cargo run -p sele4n-hal --bin rw_lock_oracle` — a Rust program
  that holds a real `RwLock` / `QueuedRwLock` in process memory,
  reads the same op-sequence format, executes each op against the
  real lock (driving multiple OS threads for concurrent op blocks),
  prints the post-state in the same textual form.
* A driver shell script feeds the same op-sequence to both, diffs
  the outputs, and reports.

No Lean-to-HAL linking; no link-discipline change; the existing
fail-closed FFI guarantee is preserved everywhere.

#### Sub-tasks

| Sub | Description | Artifact | Est |
|-----|-------------|----------|-----|
| D-6.1 | `tests/Tier5/RwLockOracle.lean` + `lake exe rw_lock_oracle` Lean oracle | Lean | M |
| D-6.2 | `rust/sele4n-hal/src/bin/rw_lock_oracle.rs` Rust oracle binary | Rust | M |
| D-6.3 | Op-sequence text wire format + serdes on both sides | Spec + Lean + Rust | S |
| D-6.4 | Property-based op-sequence generator (deterministic seeds, ≥1000 sequences per gate run) | Bash + Lean | M |
| D-6.5 | `scripts/test_tier5_cross_language.sh` driver: stream same input to both oracles + diff | Bash | M |
| D-6.6 | CI integration (added to `test_nightly.sh` under `NIGHTLY_ENABLE_EXPERIMENTAL=1`) | Config | S |

#### Test harness skeleton (revised — process-boundary)

```lean
-- tests/Tier5/RwLockOracle.lean

import SeLe4n.Kernel.Concurrency.Locks.RwLock

namespace SeLe4n.Tier5.RwLockOracle

/-- Wire format for one op: `R<core>`, `r<core>`, `W<core>`, `w<core>`
where uppercase = acquire, lowercase = release.  Cores are decimal.
A trailing `,` separates ops.  Example: "R0,R1,r0,W2,w2,". -/

def parseOp (s : String) : Option RwLockOp := ...
def parseTrace (s : String) : Option (List RwLockOp) := ...

/-- Serialise a final `RwLockState` to a canonical textual form. -/
def renderState (s : RwLockState) : String := ...

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  match parseTrace input with
  | none => IO.eprintln "parse error" *> IO.Process.exit 1
  | some ops =>
      let final := ops.foldl RwLockState.applyOp RwLockState.unheld
      IO.println (renderState final)
```

```rust
// rust/sele4n-hal/src/bin/rw_lock_oracle.rs

// Reads op-sequence on stdin; runs against a real RwLock; prints
// post-state on stdout.
use sele4n_hal::rw_lock::RwLock;
use std::io::Read;

fn main() {
    let mut input = String::new();
    std::io::stdin().read_to_string(&mut input).unwrap();
    let ops = parse_trace(&input).expect("parse error");

    // For sequences without inter-thread concurrency, the lock is
    // driven sequentially on the current thread.  For concurrent
    // blocks (annotated in the wire format as `||...||`), threads
    // are spawned and joined at the block boundary.
    let lock = RwLock::new();
    for op in ops {
        match op {
            Op::AcquireRead(c)  => lock.acquire_read(/* c */),
            Op::ReleaseRead(c)  => lock.release_read(/* c */),
            Op::AcquireWrite(c) => lock.acquire_write(/* c */),
            Op::ReleaseWrite(c) => lock.release_write(/* c */),
        }
    }
    // Inspect lock state via a test-only `peek_state` accessor that
    // returns the bit-packed u64 atomically.  Print in canonical
    // form matching Lean's `renderState`.
    let final_state = lock.peek_state();
    println!("{}", render_state(final_state));
}
```

```bash
# scripts/test_tier5_cross_language.sh

# For each generated op-sequence, feed to both oracles, diff outputs.
generate_sequences ≥1000 | while read -r seq; do
    lean_out=$(echo "$seq" | lake exe rw_lock_oracle)
    rust_out=$(echo "$seq" | cargo run --quiet --bin rw_lock_oracle)
    if [ "$lean_out" != "$rust_out" ]; then
        echo "MISMATCH on: $seq"
        echo "  lean: $lean_out"
        echo "  rust: $rust_out"
        exit 1
    fi
done
```

#### Infrastructure considerations (revised)

* **No FFI link-discipline change**.  Both oracles are independent
  binaries; the Lean oracle is pure Lean, the Rust oracle is pure
  Rust.  The existing `@[extern]` fail-closed contract is preserved.
* **State comparison via canonical text form**, not via in-process
  `rwLockSim` call.  This avoids the bisim-formality issue of the
  original sketch and lets the cross-language diff be done by a 3-line
  shell `diff` invocation.
* **Acceptance gate** (per §8, strengthened to close audit M-10): the
  Tier 5 generator emits ≥1000 op-sequences per gate run, deterministic
  under a fixed seed for reproducibility, with both random and
  pathological/edge sequences (mutex, batched-reader, exhaustive small
  models of length ≤ 5).
* **CI integration**: the existing `test_nightly.sh` runs Tier 4
  (`NIGHTLY_ENABLE_EXPERIMENTAL=1`); adding a Tier 5 invocation is a
  small change.

**Estimated effort**: 3-4 weeks (infrastructure-heavy).

**Risk**: MEDIUM. The wire format is the critical detail: both
oracles must agree on canonical state representation, including
ordering conventions for `readers` / `waiters` lists (e.g., sort by
CoreId for canonical form before serialisation).  Property-based
testing in Lean is well-supported (via `decide` + sequence
enumeration); on the Rust side, `proptest` or hand-rolled deterministic
generators suffice.

## 6. Architectural decisions

### 6.1 Computable vs. noncomputable definitions

All deferred-completion definitions in §4 are **computable**:
`Execution.stateAt` uses `List.foldl`; `enqueueStep` uses `List.find?`;
`writerWaitDepth` is straightforward arithmetic.

**Rationale**: matches the project's zero-`noncomputable` discipline.
Decidability of trace predicates enables `decide` discharge in test
fixtures and supports future runtime-introspection use cases (e.g.,
SM3 kernel-state diagnostics).

### 6.2 Parameterized fairness

The `FairTrace` predicate takes a `maxDelay : Nat` parameter rather
than hard-coding a constant.

**Rationale**: the kernel-level critical-section bound is platform-
configurable (different scheduler quanta on different SoCs). Hard-
coding would over-specify the spec.

### 6.3 Queued RwLock as a SEPARATE module

The queued variant (D-5) lands as `QueuedRwLock` in a new module,
NOT as a modification to `RwLock`.

**Rationale**: backward compatibility. Existing SM3 consumers that
don't require FIFO can continue using `RwLock` (CAS-retry). New
consumers that require FIFO opt into `QueuedRwLock` explicitly.

### 6.4 Concrete event model uses `UInt64`, not `Nat`

The `concreteApplyOp` function in §4.4 operates on `UInt64`, not `Nat`
(revised from the original sketch per audit finding M-4).

**Rationale**: the Rust `fetch_sub(1)` on a `u64` of `0` wraps to
`u64::MAX`, while Lean `Nat` subtraction truncates `0 - 1 = 0`.  The
bisimulation theorem D-4.9 must match the hardware's modular-arithmetic
semantics on every input — including the unreachable-but-mathematically-
defined corner cases — or the case analysis cannot discharge by
structural induction without lifting the underflow precondition to
every call site.  Operating directly in `UInt64` keeps the spec
hardware-faithful; the bridge to the abstract `RwLockEncoded := Nat`
form happens at `rwLockSim` via `UInt64.toNat`.

The unreachability of the underflow case at runtime (Rust never calls
`fetch_sub` unless `readers > 0`) is encoded as a separate helper
theorem `concreteApplyOp_fetch_sub_no_underflow` (D-4.6 in §5.4), so
downstream consumers get both the hardware-faithful semantics AND a
proof that the underflow corner cannot be observed under the protocol.

### 6.5 Tier 5 as opt-in nightly, two-oracle process-boundary harness

D-6 integrates Tier 5 into `test_nightly.sh` (opt-in via
`NIGHTLY_ENABLE_EXPERIMENTAL=1`), NOT into the default `test_smoke.sh`.

**Rationale**: the Tier 5 harness runs two oracle binaries
(`lake exe rw_lock_oracle` and `cargo run --bin rw_lock_oracle`)
per op-sequence, plus ≥1000 sequences per gate run.  This is slower
than the existing `lake exe` test executables that complete in
seconds.  Opt-in nightly keeps the smoke test fast and stable.

**Why two oracles and not Lean linking against `libsele4n_hal.a`**
(closes audit finding H-3): the project's `Platform/FFI.lean:67-72`
documents a uniform fail-closed FFI policy — `@[extern]` symbols
without HAL linking surface as build-time link errors.  Allowing a
"host-stub libsele4n_hal.a for tests only" exception establishes a
precedent that erodes this discipline.  The two-oracle pattern
respects the policy: both binaries are independent processes; no
cross-language linking is required.

## 7. Sequencing recommendation

The 6 deferred items have the following dependency structure:

```
D-1 (Temporal FIFO)
  ├─ D-2 (Writer bound) [independent]
  │   └─ D-3 (Liveness)  [needs D-2's writerWaitDepth]
  ├─ D-5 (Queued RwLock) [independent of Lean theorems]
  └─ (independent items below)

D-6 (Tier 5 infra)
  └─ D-4 (Full bisimulation) [needs D-6's harness for empirical validation]
```

Suggested sequencing across 6 PRs (one per item):

| PR | Item | Calendar | Cumulative |
|----|------|----------|------------|
| 1 | D-2 (writer bound) | 1-2 weeks | 1-2 weeks |
| 2 | D-1 (temporal FIFO) | 3-4 weeks | 4-6 weeks |
| 3 | D-3 (liveness) | 3-4 weeks | 7-10 weeks |
| 4 | D-6 (Tier 5 infra) | 3-4 weeks | 10-14 weeks |
| 5 | D-4 (full bisimulation) | 5-8 weeks | 15-22 weeks |
| 6 | D-5 (queued impl) | 4-5 weeks | 19-27 weeks |

**Total calendar**: 19-27 weeks if strictly sequential.

**Parallel-eligibility** (closes audit finding M-11): the original
sketch claimed "12-20 weeks if D-5 runs in parallel with D-2..D-4 (no
shared Lean state)".  This is false: D-5.7 explicitly updates
`RwLockRefinement.lean`'s FIFO-divergence documentation, and D-4 lands
its bisim theorem in `RwLockRefinement.lean`.  Two PRs editing the same
file violate CLAUDE.md's "Background agent file-change protection"
discipline if attempted concurrently.  **Recommendation**: keep the
sequencing strictly serial.  If concurrency is desired, D-5's
implementation work (Rust) can land BEFORE D-5.7 (Lean), with D-5.7
deferred to a follow-up PR that lands after D-4 — but this is a
multi-PR split, not "parallel" in the conflict-on-same-file sense.

**Recommended starting point**: D-2 (writer bound) — smallest sub-task,
introduces `writerWaitDepth` foundation that D-3 reuses, low risk.

## 8. Acceptance gates

Each deferred item closes when (strengthened from the original sketch
per audit finding M-10):

| Item | Gate |
|------|------|
| D-1 | `rwLock_fifo_admission_temporal` proven under `e.initial = unheld`; Tier 3 surface anchor added; ≥3 `decide`-checked test fixtures (success, reader-batching tie, writer-after-readers) |
| D-2 | `rwLock_bounded_wait_write_distinct` proven (no longer alias) with the **tight** `numCores - 1` bound; Tier 3 anchor added; ≥3 `decide`-checked test fixtures |
| D-3 | `rwLock_writer_liveness` proven under the strengthened §4.5 `FairTrace`; Tier 3 anchor added; `FairTrace` `Decidable` instance for finite traces |
| D-4 | `rust_rwLock_refines_lean` proven over the full `opCorresponds`-closed correspondence (CAS-retry + park-retry + conditional-SEV all covered); Tier 3 anchor added; the `concreteApplyOp_fetch_sub_no_underflow` helper landed |
| D-5 | `QueuedRwLock` impl (MCS-style per-core slots, NOT lock-free linked-list); refinement bridge updated; **≥10 cross-thread tests** covering FIFO + mutex + mixed-stress + panic-safety + slot-ownership; **`cargo +nightly miri test -p sele4n-hal --lib queued_rw_lock` passes with `-Zmiri-strict-provenance`**; **`cfg(loom)` exhaustive-interleaving runs pass on op-sequences of length ≤ 4**; FIFO test iteration count ≥ 10⁴ per run |
| D-6 | `scripts/test_tier5_cross_language.sh` integrated into `test_nightly.sh` under `NIGHTLY_ENABLE_EXPERIMENTAL=1`; two-oracle harness in place (no Lean-to-HAL linking); **≥1000 op-sequences per gate run** (mixed deterministic-edge + property-based-random under a fixed seed); zero mismatches |

**Phase closure** (SM2.C-defer fully complete): all 6 gates pass; the
plan's strongest-form claims are realized; the deferral inventory in
`docs/WORKSTREAM_HISTORY.md` is updated to mark SM2.C-defer as CLOSED.

**Axiom budget for the entire deferred-completion phase**: 0 Lean
`axioms`, 0 `sorries`. All theorems machine-discharged. (The `FairTrace`
predicate is a `structure`, not an axiom — kernel runtime discharges it
operationally.)

## 9. Risk inventory

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| D-1 temporal FIFO proof has subtle gap in position arithmetic | MED | MED | Strong existing structural foundation; helper lemmas D-1.6/.7/.8 (with concrete-witness statements per audit L-1) carry the bulk of complexity; `e.initial = unheld` precondition closes audit M-3 |
| D-3 fairness predicate is too restrictive (false positives) or too lax (false negatives) | MED | HIGH | Strengthened §4.5 transition-edge form closes audit M-2's vacuous-satisfiability concern; iterate against SM3 review of actual kernel CS bounds |
| D-4 concrete event model misses an ARMv8.1-A LSE corner case | LOW | HIGH | `UInt64` modular arithmetic (audit M-4) faithfully models hardware; `opCorresponds` inductive covers CAS-retry + park-retry + conditional-SEV (audits M-5, M-6); cross-validate against ARM ARM K11; reuse SM2.A's existing memory model abstractions |
| D-5 lock-free linked-list ABA bug | N/A | N/A | **Eliminated by design** (closes audit M-7): per-core fixed-slot MCS-style queue uses bounded integer indices, not pointers; no ABA possible |
| D-5 `WaiterNode` lifetime bug | N/A | N/A | **Eliminated by design** (closes audit H-2): slots are owned by the lock for the lock's lifetime; no stack-allocated nodes; no AtomicPtr; no borrow-checker bypass |
| D-5 fast-path FIFO violation | N/A | N/A | **Eliminated by design** (closes audit H-1): the MCS protocol enqueues unconditionally before checking state; no state-only fast-path that could bypass concurrent enqueuers |
| D-5 release-path successor-signaling race | MED | HIGH | The remaining principal risk; mitigated by `loom` exhaustive-interleaving tests on op-sequences of length ≤ 4 (audit M-10 acceptance gate) and `cargo +nightly miri test` runs |
| D-6 FFI link-time setup violates fail-closed discipline | N/A | N/A | **Eliminated by design** (closes audit H-3): two-oracle process-boundary harness; no Lean-to-HAL linking; `Platform/FFI.lean:67-72` discipline preserved |
| D-6 cross-language tests are flaky on heavy CI load | LOW | LOW | Deterministic generation under fixed seed (audit M-10 acceptance gate); no timing-dependent assertions; oracles communicate via stdin/stdout, no shared mutable state |
| Calendar slip on D-4 (estimated 5-8 weeks; could blow up) | MED | LOW | Acceptable — this is post-1.0 work; v1.0.0 is shipped with the v1.0.0-form claims |

## 10. Cross-references

### Plans

- **Master overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
- **Origin plan (closed)**: [`SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md`](SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md)
- **Next consumer**: [`SMP_PER_OBJECT_LOCKS_PLAN.md`](SMP_PER_OBJECT_LOCKS_PLAN.md) — SM3 consumes the post-deferred RwLock surface

### Source files (post-closure)

- `SeLe4n/Kernel/Concurrency/Locks/RwLock.lean` (SM2.C closed at audit-pass-3)
- `SeLe4n/Kernel/Concurrency/Locks/RwLockRefinement.lean` (SM2.C.20 refinement bridge)
- `rust/sele4n-hal/src/rw_lock.rs` (SM2.C.19 CAS-retry impl)
- New for D-5: `rust/sele4n-hal/src/queued_rw_lock.rs` (MCS-style queued variant)
- New for D-6: `tests/Tier5/RwLockOracle.lean` (Lean oracle binary)
  and `rust/sele4n-hal/src/bin/rw_lock_oracle.rs` (Rust oracle binary)
- Extended in D-1..D-4: `SeLe4n/Kernel/Concurrency/Locks/RwLock.lean`

### Test infrastructure

- Existing: `lake exe rw_lock_suite` (SM2.C.21)
- New for D-6: `lake exe rw_lock_oracle` + `cargo run --bin rw_lock_oracle`
  + `scripts/test_tier5_cross_language.sh` driver (two-oracle process
  boundary; NO Lean-to-HAL linking, per fail-closed FFI discipline)

### Audit history (informative)

- SM2.C closure: PR #784, three audit passes (pass-1/2/3 detailed in `CHANGELOG.md`)
- 27 audit findings closed at v1.0.0 cut: 8 HIGH + 11 MEDIUM + 8 LOW
- 7 items deferred to this plan: D-1..D-6 above + `_deterministic` decorative anchors (accepted as-is)

## Appendix A — Per-PR checklist (replication of project PR checklist for each deferred PR)

For each PR landing D-1..D-6:

- [ ] Workstream ID identified (WS-SM SM2.C-defer D-x)
- [ ] Scope is one coherent slice (one deferred item per PR)
- [ ] Transitions are explicit and deterministic
- [ ] Invariant/theorem updates paired with implementation
- [ ] Module build verified (pre-commit hook installed and not bypassed)
- [ ] `test_smoke.sh` passes; `test_full.sh` for theorem changes
- [ ] **Documentation synchronized** — the full canonical set (matches
      CLAUDE.md "Documentation rules"); update every entry that the
      change touches:
  - [ ] `README.md` (metrics from `docs/codebase_map.json` via the
        `readme_sync` key)
  - [ ] `docs/spec/SELE4N_SPEC.md`
  - [ ] `docs/DEVELOPMENT.md`
  - [ ] Affected GitBook chapter(s) under `docs/gitbook/` (mirror /
        link to canonical root docs)
  - [ ] `docs/CLAIM_EVIDENCE_INDEX.md` if claims change
  - [ ] `docs/WORKSTREAM_HISTORY.md` if workstream status changes
  - [ ] `CHANGELOG.md` entry
  - [ ] `docs/codebase_map.json` regenerated if Lean sources changed
- [ ] No website-linked paths renamed or removed
      (`scripts/website_link_manifest.txt`)
- [ ] No `claude.ai/code/session_*` URL in commit messages or PR
      title/body
- [ ] `Refs: docs/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md §x.x (D-x)` in commit

## Appendix B — Verification commands

```bash
source ~/.elan/env

# Per-module build:
lake build SeLe4n.Kernel.Concurrency.Locks.RwLock
lake build SeLe4n.Kernel.Concurrency.Locks.RwLockRefinement

# Test suites:
lake exe rw_lock_suite                  # Existing SM2.C tests

# Tier 5 (D-6) — two-oracle process-boundary harness.  Each oracle
# is invoked separately by the driver script; they DO NOT link
# against each other.  This preserves the fail-closed FFI discipline.
lake exe rw_lock_oracle                 # Lean oracle (reads sequence on stdin)
cargo run --bin rw_lock_oracle          # Rust oracle (reads sequence on stdin)
scripts/test_tier5_cross_language.sh    # Driver: feeds both, diffs

NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # Includes Tier 5

# Cargo (post-D-5):
cargo test -p sele4n-hal --lib rw_lock         # Existing CAS-retry impl tests
cargo test -p sele4n-hal --lib queued_rw_lock  # NEW (D-5) queued impl tests

# Miri (REQUIRED acceptance gate for D-5, per §8 audit-M-10 update):
cargo +nightly miri test -p sele4n-hal --lib queued_rw_lock \
    -- -Zmiri-strict-provenance

# Loom exhaustive interleavings (REQUIRED acceptance gate for D-5):
RUSTFLAGS="--cfg loom" cargo test -p sele4n-hal --lib queued_rw_lock \
    --release
```

---

*SM2.C-defer is the closure phase that brings the verified RwLock primitive
to its plan-strongest form.  The deferrals are not gaps in v1.0.0 (each was
accepted with an honest weakening and audit-traced justification); they are
the post-1.0 hardening path to "the lock primitives are first-class proven
artefacts" in the fullest sense of WS-SM SM2's verification-quality
elevation.*
