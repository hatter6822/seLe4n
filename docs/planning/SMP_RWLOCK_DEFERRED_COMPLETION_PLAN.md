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

* **Abstract spec** at `SeLe4n/Kernel/Concurrency/Locks/RwLock.lean` (~2400 LoC):
  - `AccessMode` + `RwLockState` + `RwLockOp` data types.
  - `applyOp` operational semantics with uniform `coreInvolved` no-op gate.
  - 5-conjunct `wf` invariant (INV-R1..R5; INV-R5 closes a reachability gap).
  - `promoteWaitersOnWriterRelease` + `promoteWaitersIfReadersEmpty` helpers.
  - 38 substantive theorems (32 in RwLock + 6 in RwLockRefinement) covering
    mutex, reader multiplicity, structural FIFO claim, bounded wait, RA
    pairing, wf preservation, reader batching, single-step safety, no-op
    refinement preservation, and bit-packed encoding round-trips.

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

- **For D-1**: `Execution` structure and trace-based reasoning primitives.
- **For D-2**: `writerWaitDepth` definition (independent; D-3 reuses).
- **For D-3**: `FairTrace` predicate + bounded-release primitives.
- **For D-4**: `ConcreteRwLockOp` event model + `concreteApplyOp` semantics.
- **For D-5**: Lock-free linked-list primitives in Rust (`WaiterNode` ABI).
- **For D-6**: Lake↔Cargo cross-build test harness; CI integration.

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
initial state. Most theorems quantify over executions of arbitrary
length starting from `RwLockState.unheld`.

    namespace SeLe4n.Kernel.Concurrency

    /-- A trace-based execution from an initial state.

    The structure pairs an `initial` state with a list of operations
    `ops` and a proof `initial_wf` that the initial state is wf.
    Execution semantics: fold `applyOp` over `ops` starting from
    `initial`.

    All deferred-completion theorems quantify over `Execution` values
    rather than ad-hoc trace lists, providing a uniform proof surface. -/
    structure Execution where
      initial    : RwLockState
      ops        : List RwLockOp
      initial_wf : initial.wf
      deriving Repr

    /-- The state after the first `k` operations of an execution. -/
    def Execution.stateAt (e : Execution) (k : Nat) : RwLockState :=
      (e.ops.take k).foldl RwLockState.applyOp e.initial

    /-- The final state of an execution. -/
    def Execution.finalState (e : Execution) : RwLockState :=
      e.stateAt e.ops.length

    /-- The number of operations in the execution. -/
    @[simp]
    theorem Execution.length_ops (e : Execution) : e.ops.length = e.ops.length := rfl

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

    /-- **Foundational theorem**: every reachable state is wf.

    Proof: induction on k.  Base case: `stateAt 0 = initial`, wf by
    hypothesis.  Inductive step: `stateAt (k+1) = (stateAt k).applyOp op`;
    apply `rwLock_wf_invariant` to lift `wf` across `applyOp`. -/
    theorem Execution.stateAt_wf (e : Execution) (k : Nat) : (e.stateAt k).wf := ...

This gives us a uniform trace abstraction. All D-1..D-4 theorems are
parameterized over `Execution`.

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

    /-- The first step at which `(core, mode)` becomes a waiter, if ever.

    A waiter is "enqueued" at step `k` iff it is NOT a waiter at step `k`
    but IS a waiter at step `k+1`.  We return the smallest such `k+1`
    (i.e., the first step at which membership becomes true), or `none`
    if the waiter never appears in the execution. -/
    def Execution.enqueueStep (e : Execution)
        (core : CoreId) (mode : AccessMode) : Option Nat :=
      (List.range (e.ops.length + 1)).find?
        (fun k => decide (e.waiterAt k core mode))

    /-- The first step at which `core` becomes a holder, if ever. -/
    def Execution.admissionStep (e : Execution) (core : CoreId) : Option Nat :=
      (List.range (e.ops.length + 1)).find?
        (fun k => decide (e.holderAt k core))

    /-- Witness: if `enqueueStep = some k`, then `waiterAt k` and
    not-`waiterAt (k-1)` (where k > 0). -/
    theorem Execution.enqueueStep_characterization (e : Execution)
        (core : CoreId) (mode : AccessMode) (k : Nat)
        (h : e.enqueueStep core mode = some k) :
        e.waiterAt k core mode ∧
        (∀ j < k, ¬ e.waiterAt j core mode) := ...

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

    Under wf: `writerWaitDepth s c ≤ 2 * numCores - 1` (a tight bound). -/
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

    /-- A concrete Rust-level operation on the lock state.

    Each constructor represents one atomic memory operation the Rust
    impl performs.  The abstract `RwLockOp` may map to multiple
    `ConcreteRwLockOp`s (e.g., a `tryAcquireRead` is a load + CAS
    sequence). -/
    inductive ConcreteRwLockOp where
      | load           (core : CoreId)             -- load(Acquire)
      | casAcquireRead (core : CoreId) (expected new : Nat) -- CAS s → s+1
      | fetchSubRead   (core : CoreId)             -- fetch_sub(1, Release)
      | casAcquireWrite (core : CoreId)            -- CAS 0 → WRITER_BIT
      | fetchAndWrite  (core : CoreId)             -- fetch_and(READER_MASK, Release)
      | sev                                         -- SEV broadcast
      | wfeWait         (core : CoreId)            -- wfe_bounded park
      deriving Repr, DecidableEq

    /-- Apply a single concrete operation to the bit-packed state.

    Returns `(new_state, succeeded)`: the new state and whether the
    op succeeded (CAS may fail).  For non-CAS ops (load, fetch_sub,
    fetch_and, sev, wfe), `succeeded` is always `true`. -/
    def concreteApplyOp (state : RwLockEncoded) (op : ConcreteRwLockOp) :
        RwLockEncoded × Bool :=
      match op with
      | .load _ => (state, true)  -- load returns the value, doesn't modify state
      | .casAcquireRead _ expected new =>
          if state = expected then (new, true) else (state, false)
      | .fetchSubRead _ => (state - 1, true)  -- wraps modulo 2^64
      | .casAcquireWrite _ =>
          if state = 0 then (writerBit, true) else (state, false)
      | .fetchAndWrite _ => (state &&& readerMask, true)
      | .sev => (state, true)
      | .wfeWait _ => (state, true)
      where
        readerMask : Nat := writerBit - 1
        -- Note: |||, &&& are bitwise ops; we abstract over Nat here.
        -- The actual encoding uses `Nat` for spec purposes; refinement
        -- to Rust `u64` is mechanical at the FFI boundary.

    /-- Abstract operation → expected concrete operation sequence.

    For each `RwLockOp`, we describe the canonical Rust impl sequence.
    This is the **refinement spec**: it ties abstract ops to concrete
    event traces. -/
    def opCorresponds (abs : RwLockOp) (conc : List ConcreteRwLockOp) : Prop := ...

The refinement theorem (D-4) proves: for any abstract op and its
corresponding concrete sequence, the abstract `applyOp` produces a
state related to the concrete `concreteApplyOp`-fold under `rwLockSim`.

### 4.5 Fairness predicate (for D-3 liveness)

    /-- An execution is "release-fair" if every holder releases within
    a bounded number of steps after acquiring.

    `MAX_RELEASE_DELAY` is a parameter of the fairness assumption — it
    represents the kernel-level critical-section duration bound that
    SM3+ consumers must satisfy.  In the spec this is left as a
    parameter; in the runtime it's enforced by the scheduler. -/
    structure FairTrace (e : Execution) (maxDelay : Nat) where
      /-- Every reader that acquires at step k releases by step
      k + maxDelay. -/
      reader_fairness :
        ∀ k c, c ∈ (e.stateAt k).readers →
          (∀ j < k, c ∉ (e.stateAt j).readers ∨ ...) →  -- "just acquired" predicate
          ∃ j, k < j ∧ j ≤ k + maxDelay ∧
            c ∉ (e.stateAt j).readers
      /-- Same for writers. -/
      writer_fairness : ...

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

**Optimal target**: the theorem statement above, proven for any
`Execution` (any starting state, any operation list).

#### Sub-tasks

| Sub | Description | Theorem / artifact | Est |
|-----|-------------|--------------------|-----|
| D-1.1 | `Execution` structure + `stateAt` / `finalState` definitions | (definitions) | S |
| D-1.2 | `Execution.stateAt_wf` aggregate (every state in trace is wf) | Theorem | S |
| D-1.3 | `waiterAt` / `holderAt` decidable predicates | (definitions) | T |
| D-1.4 | `enqueueStep` / `admissionStep` computable functions | (definitions) | T |
| D-1.5 | `enqueueStep_characterization` witness theorem | Theorem | S |
| D-1.6 | Append-to-tail property for `tryAcquire*` | Theorem | M |
| D-1.7 | Drop-prefix property for `release*` (compose existing structural claim) | Theorem | M |
| D-1.8 | Order-preservation across single op (using D-1.6 + D-1.7) | Theorem | L |
| D-1.9 | **`rwLock_fifo_admission_temporal`** main theorem | Theorem | XL |
| D-1.10 | Tests + surface anchors | tests | M |

#### Theorem statements

```lean
/-- **Lemma (D-1.6)**: `tryAcquire*` either is a no-op or appends to tail.

Specifically: for any `applyOp` step that is a `tryAcquireRead` or
`tryAcquireWrite`, the post-state's `waiters` is either equal to the
pre-state's `waiters` (no-op) or equals `pre.waiters ++ [(core, mode)]`
(enqueue at tail).  -/
theorem tryAcquire_waiters_append_or_noop
    (s : RwLockState) (op : RwLockOp)
    (h_op_is_tryAcquire : op matches .tryAcquireRead _ ∨ op matches .tryAcquireWrite _) :
    (s.applyOp op).waiters = s.waiters ∨
    ∃ core mode, (s.applyOp op).waiters = s.waiters ++ [(core, mode)]

/-- **Lemma (D-1.7)**: `release*` either is a no-op or consumes from head.

Specifically: for any `applyOp` step that is a `releaseRead` or
`releaseWrite`, the post-state's `waiters` is either equal to the
pre-state's `waiters` (no-op) or is `pre.waiters.drop k` for some
`k ≥ 1` (consume from head). -/
theorem release_waiters_drop_or_noop
    (s : RwLockState) (op : RwLockOp)
    (h_op_is_release : op matches .releaseRead _ ∨ op matches .releaseWrite _) :
    (s.applyOp op).waiters = s.waiters ∨
    ∃ k ≥ 1, (s.applyOp op).waiters = s.waiters.drop k

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

For an execution `e` and two waiters `c₁`, `c₂` enqueued at trace
positions p₁ < p₂, if c₂ is admitted at step a₂, then c₁ is admitted
at step a₁ ≤ a₂ (i.e., c₁ becomes a holder no later than c₂). -/
theorem rwLock_fifo_admission_temporal
    (e : Execution)
    (c₁ c₂ : CoreId) (m₁ m₂ : AccessMode)
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
-- Concrete trace: enqueue w₁, w₂, w₃; release writer; verify FIFO.
example :
    let e := { initial := unheld_with_writer_held boot,
               ops := [.tryAcquireWrite c1, .tryAcquireWrite c2, .tryAcquireWrite c3,
                       .releaseWrite boot],
               initial_wf := ... }
    -- All three queued writers were enqueued in order p₁ < p₂ < p₃.
    -- After boot's release, c1 is admitted (promoted to writerHeld).
    -- After c1's release, c2 is admitted.  Etc.
    -- The temporal theorem says: admission order matches enqueue order.
    e.admissionStep c1 < e.admissionStep c2 ∧
    e.admissionStep c2 < e.admissionStep c3 := by decide
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
| D-2.3 | `writerWaitDepth_bounded`: ≤ 2 × numCores - 1 | Theorem | M |
| D-2.4 | `writerWaitDepth_monotone_under_release`: reduces by ≥ 1 per release | Theorem | M |
| D-2.5 | `rwLock_bounded_wait_write_distinct`: replaces alias with substantive bound | Theorem | M |
| D-2.6 | Tests + surface anchors | tests | S |

#### Theorem statements

```lean
/-- **D-2.3**: writer wait depth is bounded by `2 × numCores - 1`.

The factor of 2 reflects: at most numCores - 1 entries ahead in the
queue (since the writer itself occupies one slot), at most numCores
holders (readers + writer), but the holders + queue overlap is bounded
by numCores total cores.  Refined: depth ≤ 2 × numCores - 1. -/
theorem writerWaitDepth_bounded
    (s : RwLockState) (h : s.wf)
    (c : CoreId) (h_queued : (c, .write) ∈ s.waiters) :
    writerWaitDepth s c ≤ 2 * numCores - 1

/-- **D-2.4**: each release operation reduces `writerWaitDepth` by at
least 1, provided c is still in waiters.

This is the structural progress property: every release transitions
the system one step closer to c's admission. -/
theorem writerWaitDepth_monotone_under_release
    (s : RwLockState) (h : s.wf)
    (c : CoreId) (h_queued : (c, .write) ∈ s.waiters)
    (releaser : CoreId)
    (op : RwLockOp)
    (h_op : op = .releaseRead releaser ∨ op = .releaseWrite releaser)
    (h_progress : (s.applyOp op).readers.length + ... <
                   s.readers.length + ...) :
    -- If c remains queued after the release:
    (c, .write) ∈ (s.applyOp op).waiters →
    writerWaitDepth (s.applyOp op) c ≤ writerWaitDepth s c - 1

/-- **D-2.5**: writer-specific bounded wait.

For any wf state `s` and queued writer `c`, after at most
`writerWaitDepth s c` release operations, `c` is admitted. -/
theorem rwLock_bounded_wait_write_distinct
    (e : Execution)
    (c : CoreId) (h_queued : (c, .write) ∈ e.initial.waiters) :
    -- The writer is admitted within `writerWaitDepth e.initial c` releases.
    e.admissionStep c ≤ writerWaitDepth e.initial c
```

#### Proof sketch

- D-2.3: pigeonhole. `writerWaitDepth = idxOf + readers + writer_bit`.
  Under wf:
  - `idxOf ≤ waiters.length - 1` (writer is in waiters).
  - `waiters.length + readers.length + writer_bit ≤ numCores` (existing
    `rwLock_bounded_wait_read`).
  - So `idxOf + readers + writer_bit ≤ numCores - 1 + numCores = 2×numCores - 1`.

- D-2.4: case analysis on `op`.
  - `releaseRead`: readers shrinks by 1. If the writer is still in
    waiters, `idxOf` either stays (no promote) or decreases (promote
    happened and pulled this writer up via consume-from-head). Either
    way, the sum decreases.
  - `releaseWrite`: writer_bit → 0; same analysis.

- D-2.5: induction on `writerWaitDepth`. Base case: depth = 0 means c
  is at queue head AND no holders, so the next op (which must be a
  release of nothing — contradiction) admits c. Inductive step:
  depth = n+1 means there's at least one "barrier" to clear; the
  next release clears one barrier; induction.

**Estimated effort**: 1-2 weeks.

**Risk**: LOW. The proofs are pigeonhole + structural arithmetic.

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

```lean
/-- **D-3.1**: a trace is `FairTrace` if every holder releases within
`maxDelay` steps after acquiring.

Formal definition uses an "acquire predicate" (the step at which a
core becomes a holder) and asserts that within `maxDelay` steps,
the core releases.  -/
structure FairTrace (e : Execution) (maxDelay : Nat) where
  reader_fairness :
    ∀ k_acquire c,
      c ∈ (e.stateAt (k_acquire + 1)).readers →
      c ∉ (e.stateAt k_acquire).readers →
      -- c acquired at step k_acquire + 1
      ∃ k_release > k_acquire, k_release ≤ k_acquire + maxDelay ∧
        c ∉ (e.stateAt (k_release + 1)).readers
  writer_fairness : ... -- analogous

/-- **D-3.3**: under fairness, each step where the writer is still
queued and at least one holder exists, the next release reduces the
writer's wait depth.

This is the "progress" theorem that drives the liveness proof. -/
theorem fair_release_reduces_writerWaitDepth
    (e : Execution) (h_fair : FairTrace e maxDelay)
    (c : CoreId) (h_queued : (c, .write) ∈ e.initial.waiters) :
    ∀ k, (c, .write) ∈ (e.stateAt k).waiters →
      ∃ j > k, j ≤ k + maxDelay ∧
        writerWaitDepth (e.stateAt j) c < writerWaitDepth (e.stateAt k) c

/-- **D-3.6 main theorem**: writer liveness under fairness.

For any execution that is `FairTrace e maxDelay` and contains a
queued writer `c` in its initial state, the writer is admitted
within `writerWaitDepth e.initial c × maxDelay` steps. -/
theorem rwLock_writer_liveness
    (e : Execution) (maxDelay : Nat) (h_fair : FairTrace e maxDelay)
    (c : CoreId) (h_queued : (c, .write) ∈ e.initial.waiters) :
    ∃ k ≤ writerWaitDepth e.initial c * maxDelay,
      (e.stateAt k).writerHeld = some c
```

#### Proof sketch

- D-3.3: `writerWaitDepth` is bounded by 2×numCores - 1 (D-2.3). Under
  `FairTrace`, every holder releases within `maxDelay` steps. Each
  release reduces `writerWaitDepth` by ≥ 1 (D-2.4). So within `maxDelay`
  steps, the depth strictly decreases.

- D-3.4: by induction on `writerWaitDepth`. Base case: depth = 0 means
  c is at queue head with no holders — promote fires on next release-
  equivalent step.

- D-3.5: when writer is at head with no holders, the next op (which
  must be a release that triggers promote) admits c.

- D-3.6: combine D-3.4 + D-3.5. The total number of steps is bounded
  by `writerWaitDepth × maxDelay` (each "unit of depth" cleared takes
  at most `maxDelay` steps).

**Estimated effort**: 3-4 weeks.

**Risk**: HIGH. The fairness predicate is delicate; the induction
requires careful handling of the "k_acquire" tracking.

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
| D-4.1 | `ConcreteRwLockOp` inductive + `concreteApplyOp` semantics | (definition) | M |
| D-4.2 | `opCorresponds` predicate (abs op → conc seq) | (definition) | M |
| D-4.3 | `rustImplementsRwLock`: trace ↔ op-list correspondence predicate | (definition) | L |
| D-4.4 | `concreteApplyOp_preserves_sim_load`: load doesn't modify state | Theorem | S |
| D-4.5 | `concreteApplyOp_preserves_sim_cas_acquire_read`: CAS-success step | Theorem | L |
| D-4.6 | `concreteApplyOp_preserves_sim_fetch_sub`: release_read step | Theorem | L |
| D-4.7 | `concreteApplyOp_preserves_sim_cas_acquire_write` | Theorem | L |
| D-4.8 | `concreteApplyOp_preserves_sim_fetch_and`: release_write step | Theorem | L |
| D-4.9 | **`rust_rwLock_refines_lean`** main theorem | Theorem | XL |
| D-4.10 | Tests + surface anchors | tests | M |

#### Theorem statements

```lean
/-- **D-4.1**: bit-packed concrete state + atomic operation semantics. -/
abbrev ConcreteState := Nat  -- represents AtomicU64 contents

inductive ConcreteRwLockOp where ... -- (as in §4.4)

def concreteApplyOp (state : ConcreteState) (op : ConcreteRwLockOp) :
    ConcreteState × Bool := ... -- (as in §4.4)

/-- **D-4.2**: correspondence relation.

For each `RwLockOp`, define the canonical Rust impl sequence. -/
def opCorresponds : RwLockOp → List ConcreteRwLockOp → Prop
  | .tryAcquireRead core, [.load _, .casAcquireRead _ _ _] => True  -- load + CAS
  | .releaseRead core, [.fetchSubRead _, .sev] => True
  | .tryAcquireWrite core, [.load _, .casAcquireWrite _] => True
  | .releaseWrite core, [.fetchAndWrite _, .sev] => True
  | _, _ => False

/-- **D-4.9 main theorem**: bisimulation.

For any abstract operation list and corresponding concrete trace,
applying the abstract `applyOp` fold and the concrete `concreteApplyOp`
fold produces related states. -/
theorem rust_rwLock_refines_lean
    (initial_abs : RwLockState) (initial_conc : ConcreteState)
    (h_sim_init : rwLockSim initial_abs initial_conc)
    (abs_ops : List RwLockOp)
    (conc_ops : List ConcreteRwLockOp)
    (h_corresponds : abs_ops.zip ... = conc_ops.split ... ∧ ...) :
    let final_abs := abs_ops.foldl applyOp initial_abs
    let final_conc := (conc_ops.foldl concreteApplyOp initial_conc).1
    rwLockSim final_abs final_conc
```

#### Proof sketch

By induction on `abs_ops`:

- Base case: `[]` — both states unchanged; `rwLockSim` preserved by
  hypothesis.

- Inductive step: take one abstract op + its corresponding concrete
  sequence. By case analysis on the op:
  - `tryAcquireRead`: load + CAS. The load doesn't modify state
    (D-4.4); the CAS either succeeds (state becomes s+1; abstract
    readers grows by 1; D-4.5) or fails (retry; both abstract
    no-op and concrete state unchanged).
  - `releaseRead`: fetch_sub + sev. fetch_sub decrements (D-4.6);
    abstract readers shrinks by 1.
  - Similar for write ops.

The key invariant: at each step, `rwLockSim abs conc` says
`conc = encodeRwLock abs.writerHeld.isSome abs.readers.length`. We
prove this is preserved by each abstract/concrete step pair.

**Estimated effort**: 5-8 weeks. This is the largest sub-task in the
plan.

**Risk**: HIGH. Modeling the Rust impl's CAS-retry behavior is subtle.
The proof must handle "CAS failure → retry" gracefully (retries
don't make abstract progress; the bisimulation is preserved across
retries because no state change occurs on either side).

### 5.5 D-5: Queued RwLock variant (8 sub-tasks)

**Plan reference**: SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md §5.3 note,
"SM2.C.19.a may extend to a queued RwLock".

**Current state**: CAS-retry Rust impl with NO waiter queue. FIFO not
enforced at impl level.

**Gap**: a queued Rust impl that preserves the Lean spec's FIFO
admission property.

**Optimal target**: implement a queued RwLock with an explicit waiter
linked-list and per-waiter event mechanism.

#### Sub-tasks

| Sub | Description | Artifact | Est |
|-----|-------------|----------|-----|
| D-5.1 | `WaiterNode` struct + linked-list ABI | Rust | M |
| D-5.2 | Lock-free `enqueue_waiter` (CAS on tail) | Rust | L |
| D-5.3 | Lock-free `dequeue_waiter` (head pop) | Rust | L |
| D-5.4 | Per-waiter `parked: AtomicBool` event mechanism | Rust | M |
| D-5.5 | `QueuedRwLock::acquire_read/write` with explicit park/wake | Rust | L |
| D-5.6 | `QueuedRwLock::release_read/write` with head signal | Rust | L |
| D-5.7 | Refinement bridge update: FIFO no longer "deferred" | Lean | M |
| D-5.8 | Cross-thread stress tests (FIFO verification) | Rust | L |

#### Rust impl skeleton

```rust
// rust/sele4n-hal/src/queued_rw_lock.rs

use core::sync::atomic::{AtomicU64, AtomicPtr, AtomicBool, Ordering};
use core::ptr::null_mut;

#[repr(C, align(64))]
pub struct QueuedRwLock {
    /// Bit-packed state (same as RwLock): bit 63 = writer, bits 0..62 = reader count.
    state: AtomicU64,
    /// Head of the FIFO waiter queue (or null if empty).
    waiter_head: AtomicPtr<WaiterNode>,
    /// Tail of the FIFO waiter queue (or null if empty).
    waiter_tail: AtomicPtr<WaiterNode>,
}

/// A node in the waiter linked-list.  Allocated on the waiter's stack
/// (the waiter owns its node for the duration of the wait).
pub struct WaiterNode {
    /// Pointer to the next node in the queue.
    next: AtomicPtr<WaiterNode>,
    /// Requested access mode.
    mode: AccessMode,
    /// Set to true when the waiter is admitted by `release_*`.
    parked: AtomicBool,
}

impl QueuedRwLock {
    pub const fn new() -> Self { ... }

    pub fn acquire_read(&self) {
        // Fast path: try CAS (s + 1) if state has no writer/no waiters.
        loop {
            let s = self.state.load(Ordering::Acquire);
            if s & WRITER_BIT == 0 && self.waiter_head.load(Ordering::Acquire).is_null() {
                let new = s + 1;
                if self.state.compare_exchange(s, new, Ordering::Acquire, Ordering::Relaxed).is_ok() {
                    return;
                }
                continue;  // CAS contention; retry fast path
            }
            break;  // Fall through to slow path
        }
        // Slow path: enqueue + park.
        let mut node = WaiterNode { next: AtomicPtr::new(null_mut()),
                                    mode: AccessMode::Read,
                                    parked: AtomicBool::new(false) };
        self.enqueue_waiter(&mut node);
        while !node.parked.load(Ordering::Acquire) {
            crate::cpu::wfe_bounded(crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS);
        }
    }

    // ... release_read, acquire_write, release_write similar.

    fn enqueue_waiter(&self, node: &mut WaiterNode) { ... }
    fn dequeue_head(&self) -> Option<*mut WaiterNode> { ... }
}
```

#### Refinement update

After D-5 lands, the `RwLockRefinement.lean` FIFO divergence
documentation should be updated:

```lean
-- BEFORE (current):
-- "The Rust CAS-retry impl satisfies mutex + exclusion but NOT FIFO."

-- AFTER (post-D-5):
-- "The Rust queued impl preserves FIFO admission, matching the Lean
-- spec's rwLock_fifo_admission_temporal theorem.  The CAS-retry impl
-- is retained as RwLock for backward compatibility; new SM3 consumers
-- requiring FIFO should use QueuedRwLock."
```

#### Tests (D-5.8)

```rust
// FIFO verification test: NUM_THREADS writers contend; verify
// admission order matches enqueue order.
#[test]
fn queued_rwlock_writer_fifo() {
    use std::sync::Barrier;
    let lock = Arc::new(QueuedRwLock::new());
    let barrier = Arc::new(Barrier::new(NUM_WRITERS));
    let admission_order = Arc::new(Mutex::new(vec![]));
    // ... spawn writers; each calls acquire_write then records its id;
    // verify the recorded order matches a known enqueue order.
}
```

**Estimated effort**: 4-5 weeks.

**Risk**: HIGH. Lock-free linked-list management is notoriously
error-prone. The ABA problem must be carefully handled. Stack-
allocated `WaiterNode`s require careful lifetime analysis.

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

1. Generates random/structured operation sequences (`List RwLockOp`).
2. Runs the Lean spec's `applyOp` fold (in `lake exe`).
3. Runs the equivalent Rust ops (via FFI).
4. Compares the final states via `rwLockSim`.
5. Integrated into CI as a Tier 5 gate.

#### Sub-tasks

| Sub | Description | Artifact | Est |
|-----|-------------|----------|-----|
| D-6.1 | `tests/Tier5/RwLockCrossLanguageSuite.lean` harness | Lean | L |
| D-6.2 | FFI bindings for `RwLockOp` → Rust calls | Lean + Rust | M |
| D-6.3 | Property-based op-sequence generator | Lean | M |
| D-6.4 | State comparison via `rwLockSim` | Lean | S |
| D-6.5 | `scripts/test_tier5_cross_language.sh` runner | Bash | S |
| D-6.6 | CI integration (added to `test_nightly.sh`) | Config | S |

#### Test harness skeleton

```lean
-- tests/Tier5/RwLockCrossLanguageSuite.lean

import SeLe4n.Kernel.Concurrency.Locks.RwLock
import SeLe4n.Platform.FFI

namespace SeLe4n.Tier5.RwLockCrossLanguage

/-- FFI binding: call the Rust `acquire_read` and return new state. -/
@[extern "ffi_rwlock_acquire_read"]
opaque ffiRwLockAcquireRead : UInt64 → BaseIO UInt64

/-- Run an `RwLockOp` against the Rust impl, returning the new state. -/
def runOpOnRust (state : UInt64) (op : RwLockOp) : BaseIO UInt64 :=
  match op with
  | .tryAcquireRead _ => ffiRwLockAcquireRead state
  | .releaseRead _ => ffiRwLockReleaseRead state
  | .tryAcquireWrite _ => ffiRwLockAcquireWrite state
  | .releaseWrite _ => ffiRwLockReleaseWrite state

/-- Property: for any short op sequence, the Lean fold and Rust fold
agree under `rwLockSim`. -/
def crossLanguageProperty (ops : List RwLockOp) : BaseIO Bool := do
  -- Run the Lean spec.
  let lean_final := ops.foldl RwLockState.applyOp RwLockState.unheld
  -- Run the Rust impl.
  let mut rust_state : UInt64 := 0
  for op in ops do
    rust_state ← runOpOnRust rust_state op
  -- Compare via rwLockSim.
  return decide (rwLockSim lean_final rust_state.toNat)

def runCrossLanguageChecks : IO Unit := do
  -- Generate small op sequences (e.g., 5-10 ops).
  let sequences := [
    [.tryAcquireRead bootCoreId, .releaseRead bootCoreId],
    [.tryAcquireWrite bootCoreId, .releaseWrite bootCoreId],
    -- ... more sequences, including pathological cases
  ]
  for seq in sequences do
    let result ← crossLanguageProperty seq
    if !result then
      throw (IO.userError s!"Cross-language mismatch on: {repr seq}")
```

#### Infrastructure considerations

The Tier 5 harness requires:

1. **FFI link-time access** to the Rust HAL. Currently, the project
   structure has `Platform/FFI.lean` with `@[extern]` bindings, but
   they're typically `panic!` stubs when not linked against the HAL.
   For Tier 5, the test executable must link against a host-stub
   version of `libsele4n_hal.a` that exposes the RwLock atomic ops.

2. **A stateful Rust harness** that exposes the RwLock as an
   `extern "C"` static + per-op entry points. This requires a small
   shim module in `rust/sele4n-hal/src/tier5_rwlock_shim.rs` that's
   only compiled under a `tier5_test` cfg.

3. **CI integration**: the existing `test_nightly.sh` runs Tier 4
   (`NIGHTLY_ENABLE_EXPERIMENTAL=1`); adding a Tier 5 invocation is
   a small change.

**Estimated effort**: 3-4 weeks (infrastructure-heavy).

**Risk**: MEDIUM. The link-time FFI setup is non-trivial but
mechanical. Property-based testing in Lean is well-supported (via
`decide` + sequence enumeration).

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

### 6.4 Concrete event model uses `Nat` instead of `UInt64`

The `ConcreteState` abbreviation is `Nat`, not `UInt64`.

**Rationale**: matches the existing `RwLockEncoded := Nat` abbreviation
in `RwLock.lean`. The Nat-vs-UInt64 question is a refinement-bridge
concern handled at the FFI boundary (UInt64.toNat, .ofNat). Bridging
to the Rust u64 is mechanical.

### 6.5 Tier 5 as opt-in nightly, not Tier 0-3 default

D-6 integrates Tier 5 into `test_nightly.sh` (opt-in via
`NIGHTLY_ENABLE_EXPERIMENTAL=1`), NOT into the default `test_smoke.sh`.

**Rationale**: Tier 5 requires linking against `libsele4n_hal.a` and
running multi-process tests. This is slower and more fragile than the
existing `lake exe` test executables. Opt-in nightly keeps the smoke
test fast and stable.

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
| 6 | D-5 (queued impl) | 4-5 weeks | 19-27 weeks (parallel-eligible) |

**Total calendar**: 19-27 weeks if strictly sequential; 12-20 weeks if
D-5 runs in parallel with D-2..D-4 (no shared Lean state).

**Recommended starting point**: D-2 (writer bound) — smallest sub-task,
introduces `writerWaitDepth` foundation that D-3 reuses, low risk.

## 8. Acceptance gates

Each deferred item closes when:

| Item | Gate |
|------|------|
| D-1 | `rwLock_fifo_admission_temporal` proven; Tier 3 surface anchor added |
| D-2 | `rwLock_bounded_wait_write_distinct` proven (no longer alias); Tier 3 anchor added |
| D-3 | `rwLock_writer_liveness` proven; Tier 3 anchor added; `FairTrace` decidable instance |
| D-4 | `rust_rwLock_refines_lean` proven; Tier 3 anchor added |
| D-5 | `QueuedRwLock` impl + ≥3 cross-thread FIFO tests; refinement bridge updated |
| D-6 | `scripts/test_tier5_cross_language.sh` integrated into `test_nightly.sh`; ≥10 op-sequence cases covered |

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
| D-1 temporal FIFO proof has subtle gap in position arithmetic | MED | MED | Strong existing structural foundation; helper lemmas D-1.6/.7/.8 carry the bulk of complexity |
| D-3 fairness predicate is too restrictive (false positives) or too lax (false negatives) | MED | HIGH | Iterate on `FairTrace` definition against SM3 review of actual kernel CS bounds |
| D-4 concrete event model misses an ARMv8.1-A LSE corner case | LOW | HIGH | Cross-validate against ARM ARM K11; reuse SM2.A's existing memory model abstractions |
| D-5 lock-free linked-list ABA bug | MED | CRIT | Use `cargo-miri` validation; reuse a published lock-free queue pattern (e.g., MPSC from `crossbeam`-style) |
| D-5 stack-allocated `WaiterNode` lifetime bug | LOW | CRIT | Borrow-checker enforces; supplemented by Miri runs |
| D-6 FFI link-time setup is platform-specific | MED | MED | Host-stub `libsele4n_hal.a` for Linux/macOS; Windows is out of scope per CLAUDE.md |
| D-6 cross-language tests are flaky on heavy CI load | MED | LOW | Use deterministic op sequences (not random); avoid timing-dependent assertions |
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
- New for D-5: `rust/sele4n-hal/src/queued_rw_lock.rs`
- New for D-6: `tests/Tier5/RwLockCrossLanguageSuite.lean` + harness shim
- Extended in D-1..D-4: `SeLe4n/Kernel/Concurrency/Locks/RwLock.lean`

### Test infrastructure

- Existing: `lake exe rw_lock_suite` (SM2.C.21)
- New for D-6: `lake exe rw_lock_tier5_suite` + `scripts/test_tier5_cross_language.sh`

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
- [ ] Documentation synchronized (`README.md`, `docs/spec/SELE4N_SPEC.md`,
      `docs/WORKSTREAM_HISTORY.md`, `CHANGELOG.md`, affected GitBook chapter)
- [ ] No website-linked paths renamed or removed
- [ ] No `claude.ai/code/session_*` URL in commit messages or PR title/body
- [ ] `Refs: docs/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md §x.x (D-x)` in commit

## Appendix B — Verification commands

```bash
source ~/.elan/env

# Per-module build:
lake build SeLe4n.Kernel.Concurrency.Locks.RwLock
lake build SeLe4n.Kernel.Concurrency.Locks.RwLockRefinement

# Test suites:
lake exe rw_lock_suite                  # Existing SM2.C tests
lake exe rw_lock_tier5_suite            # NEW (D-6) cross-language
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # Includes Tier 5

# Cargo (post-D-5):
cargo test -p sele4n-hal --lib rw_lock         # Existing CAS-retry impl tests
cargo test -p sele4n-hal --lib queued_rw_lock  # NEW (D-5) queued impl tests

# Miri (recommended for D-5 lock-free correctness):
cargo +nightly miri test -p sele4n-hal --lib queued_rw_lock
```

---

*SM2.C-defer is the closure phase that brings the verified RwLock primitive
to its plan-strongest form.  The deferrals are not gaps in v1.0.0 (each was
accepted with an honest weakening and audit-traced justification); they are
the post-1.0 hardening path to "the lock primitives are first-class proven
artefacts" in the fullest sense of WS-SM SM2's verification-quality
elevation.*
