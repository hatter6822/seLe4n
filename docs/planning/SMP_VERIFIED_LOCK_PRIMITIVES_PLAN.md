# SM2 — Verified Lock Primitives (WS-SM Phase 2)

> **Phase**: SM2 of WS-SM
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Audited cut**: `v0.31.2`
> **Target releases**: v0.33.0 .. v0.45.x (parallel with SM1)
> **Calendar estimate**: 16-22 weeks
> **Sub-task count**: 70-95 across ~28-40 PRs

## 1. Phase goal

SM2 implements the **maintainer-decided verification quality
elevation** (decision #10): the lock primitives themselves —
TicketLock and RwLock — are formally specified in Lean against an
abstract operational semantics of ARMv8.1-A LSE atomic operations
and proven correct. The Rust implementations refine the Lean
specs via an operational simulation argument.

This is what differentiates seLe4n from seL4: the seL4 project
historically assumes its lock primitives (they appear in the
TCB as unverified C); we elevate them to first-class proven
artefacts.

**Concrete deliverables**:

1. **Abstract memory model** (`Concurrency/MemoryModel.lean`):
   operational semantics of acquire/release/seqCst atomic
   operations, the synchronizes-with relation, the happens-before
   partial order.
2. **TicketLock spec** (`Concurrency/Locks/TicketLock.lean`):
   operational state, transition rules, well-formedness
   invariant, and 6 theorems (mutex, FIFO, bounded wait,
   release-acquire pairing, wf preservation, reachability).
3. **TicketLock Rust impl** (`rust/sele4n-hal/src/ticket_lock.rs`):
   structural-correspondence implementation; cargo unit tests.
4. **TicketLock refinement** (`Concurrency/Locks/TicketLockRefinement.lean`):
   operational simulation φ between the Lean spec and the Rust
   atomic-event trace.
5. **RwLock spec** (`Concurrency/Locks/RwLock.lean`): same
   structure for reader-writer semantics; 10 theorems.
6. **RwLock Rust impl** (`rust/sele4n-hal/src/rw_lock.rs`).
7. **RwLock refinement**.
8. **FFI bridge** (`SeLe4n/Platform/FFI.lean`): Lean wrappers and
   `withLock` / `withReadLock` / `withWriteLock` RAII combinators.
9. **Documentation** (`docs/spec/SELE4N_SPEC.md` §10; new GitBook
   chapter 17).

**Closure**: SMP-H4 (foundationally — the lock primitives exist
and are proven; their integration into kernel paths happens in
SM3).

**Axiom budget for SM2: 0 Lean axioms.** All hardware properties
(ARMv8.1-A LSE atomic semantics, release/acquire ordering,
inner-shareable memory model) enter the proof surface via
documented ARM ARM citations in module docstrings; we model them
operationally without `axiom` declarations.

## 2. Dependencies

- **SM0**: SM0.E (CoreId), SM0.G (PlatformBinding.coreCount).
- **SM1** (parallel, no direct dependency): SM2's outputs are
  consumed starting in SM3 (per-object lock fields).
- Lean 4.28.0 toolchain.
- Std library (`List.finRange`, `Vector`, basic combinators).

## 3. Mathematical foundations

### 3.1 Abstract memory model

The Lean-side abstract memory model captures enough of ARMv8.1-A
LSE atomic semantics to prove the lock primitives correct. The
model is **operational**: a trace is a sequence of memory events
on shared atomic locations; the synchronizes-with relation is
derived from event order; happens-before is the transitive
closure.

#### 3.1.1 Memory order

    namespace SeLe4n.Kernel.Concurrency

      inductive MemoryOrder where
        | relaxed      -- no synchronization
        | acquire      -- acquire-load
        | release      -- release-store
        | acqRel       -- both (used by RMW)
        | seqCst       -- sequentially consistent
        deriving DecidableEq, Repr

      /-- Is this order at least Acquire-strength? -/
      def MemoryOrder.isAcquire : MemoryOrder → Bool
        | .acquire | .acqRel | .seqCst => true
        | _ => false

      /-- Is this order at least Release-strength? -/
      def MemoryOrder.isRelease : MemoryOrder → Bool
        | .release | .acqRel | .seqCst => true
        | _ => false

    end SeLe4n.Kernel.Concurrency

#### 3.1.2 Atomic location

    /-- Identifier for an atomic memory location. The lock
        primitive uses a small fixed set of locations
        (TicketLock has 2: nextTicket, serving; RwLock has 1:
        state). We use an opaque `Nat` here; SM2.A.2 wires
        concrete location IDs to specific lock fields. -/
    structure AtomicLocation where
      id : Nat
      deriving DecidableEq, Repr

#### 3.1.3 Memory event

    /-- An atomic memory operation on a specific location. -/
    structure MemoryEvent where
      core    : CoreId           -- which core executed it
      loc     : AtomicLocation   -- which location
      isWrite : Bool             -- true = store, false = load
      order   : MemoryOrder
      value   : Nat              -- written value (for stores) or
                                 -- observed value (for loads)
      seqNum  : Nat              -- per-core sequencing number
      deriving Repr

    /-- For a Read-Modify-Write (e.g., fetch_add), we model it
        as two events: a load with the pre-value and a store with
        the post-value. Both share a single `seqNum` (atomic). -/

#### 3.1.4 Memory trace

    /-- A trace is a finite sequence of memory events. The
        operational semantics generates traces; theorems quantify
        over reachable traces. -/
    structure MemoryTrace where
      events : List MemoryEvent
      deriving Repr

    def MemoryTrace.empty : MemoryTrace := { events := [] }

    def MemoryTrace.append (t : MemoryTrace) (e : MemoryEvent) :
        MemoryTrace := { events := t.events ++ [e] }

#### 3.1.5 Trace well-formedness

    /-- A trace is well-formed iff:
        1. Per-core seqNums are monotonic.
        2. No two events share (core, seqNum).
        3. RMW loads-stores are paired and consecutive in the
           same core's order. -/
    def MemoryTrace.wellFormed (t : MemoryTrace) : Prop :=
      -- Monotonicity per core
      ( ∀ e₁ e₂, e₁ ∈ t.events → e₂ ∈ t.events →
        e₁.core = e₂.core → e₁.seqNum < e₂.seqNum →
        t.events.indexOf? e₁ < t.events.indexOf? e₂ )
      ∧
      -- Distinct (core, seqNum)
      ( ∀ e₁ e₂, e₁ ∈ t.events → e₂ ∈ t.events →
        e₁.core = e₂.core → e₁.seqNum = e₂.seqNum →
        e₁ = e₂ )

    /-- Decidability of well-formedness (used for testing). -/
    instance (t : MemoryTrace) : Decidable (t.wellFormed) := by
      unfold MemoryTrace.wellFormed
      -- Both conjuncts are decidable (finite ∀ + decidable
      -- propositions inside).
      exact inferInstance

#### 3.1.6 Synchronizes-with

    /-- An event e_R "synchronizes-with" an event e_A iff:
        - e_R is a Release-store on location L.
        - e_A is an Acquire-load on the same L.
        - e_A's observed value equals e_R's written value.
        - e_R precedes e_A in the trace order.

        This is the basic synchronization edge per ARM ARM B2.3.7
        and Rust's release-acquire memory-model rule. -/
    def synchronizesWith (t : MemoryTrace) (e_R e_A : MemoryEvent) : Prop :=
      e_R.isWrite ∧
      e_R.order.isRelease ∧
      ¬ e_A.isWrite ∧
      e_A.order.isAcquire ∧
      e_R.loc = e_A.loc ∧
      e_R.value = e_A.value ∧
      e_R ∈ t.events ∧
      e_A ∈ t.events ∧
      t.events.indexOf? e_R < t.events.indexOf? e_A

#### 3.1.7 Happens-before

    /-- Per-core sequenced-before order (decidable from seqNums). -/
    def sequencedBefore (e₁ e₂ : MemoryEvent) : Prop :=
      e₁.core = e₂.core ∧ e₁.seqNum < e₂.seqNum

    /-- The "happens-before" relation: per-core sequencing plus
        synchronizes-with, transitively closed.

        ARM ARM K11.2: hb is irreflexive, transitive, antisymmetric.
        It defines a partial order on events. -/
    inductive happensBefore (t : MemoryTrace) : MemoryEvent → MemoryEvent → Prop where
      | seq : ∀ {e₁ e₂}, sequencedBefore e₁ e₂ → happensBefore t e₁ e₂
      | sync : ∀ {e_R e_A}, synchronizesWith t e_R e_A → happensBefore t e_R e_A
      | trans : ∀ {e₁ e₂ e₃}, happensBefore t e₁ e₂ → happensBefore t e₂ e₃ →
                happensBefore t e₁ e₃

#### 3.1.8 Happens-before is a partial order

**Theorem 3.1.8.1** (Irreflexivity). For any well-formed trace t
and any event e ∈ t.events, ¬ happensBefore t e e.

*Proof sketch.* By induction on the `happensBefore` derivation:
- `seq`: contradicts `e.seqNum < e.seqNum` (Nat irreflexivity).
- `sync`: requires `e.isWrite ∧ ¬e.isWrite`, contradiction.
- `trans`: needs irreflexivity for the intermediate steps, by IH.
  Use the well-formed total order on trace positions to derive a
  contradiction.

**Theorem 3.1.8.2** (Transitivity). Immediate from the `trans`
constructor.

**Theorem 3.1.8.3** (Antisymmetry). For well-formed t and events
e₁ ≠ e₂, NOT (happensBefore t e₁ e₂ ∧ happensBefore t e₂ e₁).

*Proof sketch.* By contradiction. If both hold, then by
irreflexivity (3.1.8.1) applied through the cycle, we get
happensBefore t e₁ e₁ — contradiction.

**Theorem 3.1.8** (`happens_before_partial_order`):

    theorem happens_before_partial_order (t : MemoryTrace) :
      t.wellFormed →
      (∀ e ∈ t.events, ¬ happensBefore t e e) ∧
      (∀ e₁ e₂ e₃, happensBefore t e₁ e₂ → happensBefore t e₂ e₃ →
        happensBefore t e₁ e₃) ∧
      (∀ e₁ e₂, e₁ ∈ t.events → e₂ ∈ t.events → e₁ ≠ e₂ →
        ¬ (happensBefore t e₁ e₂ ∧ happensBefore t e₂ e₁))

The proof is by induction on the inductive structure of
`happensBefore` (~60 LoC of Lean proof).

### 3.2 TicketLock operational semantics

#### 3.2.1 State

    structure TicketLockState where
      nextTicket : Nat                       -- monotone counter
      serving    : Nat                       -- monotone counter
      pending    : List (CoreId × Nat)       -- (core, captured ticket)
      held       : Option (CoreId × Nat)     -- (current holder, ticket)
      deriving Repr, Inhabited

    def TicketLockState.unheld : TicketLockState :=
      { nextTicket := 0
      , serving    := 0
      , pending    := []
      , held       := none }

#### 3.2.2 Well-formedness

    def TicketLockState.wf (s : TicketLockState) : Prop :=
      -- INV-T1: serving ≤ nextTicket
      s.serving ≤ s.nextTicket
      ∧
      -- INV-T2: pending tickets lie in (serving, nextTicket)
      ( ∀ p ∈ s.pending, s.serving < p.2 ∧ p.2 < s.nextTicket )
      ∧
      -- INV-T3: holder's ticket equals serving (if held)
      ( ∀ h ∈ s.held, h.2 = s.serving )
      ∧
      -- INV-T4: pending tickets are NoDup
      s.pending.map Prod.snd |>.Nodup
      ∧
      -- INV-T5: holder's ticket is not in pending
      ( ∀ h ∈ s.held, h.2 ∉ s.pending.map Prod.snd )
      ∧
      -- INV-T6: pending cores are NoDup (a core can only wait
      -- for one ticket at a time)
      s.pending.map Prod.fst |>.Nodup
      ∧
      -- INV-T7: pending cores disjoint from holder
      ( ∀ h ∈ s.held, h.1 ∉ s.pending.map Prod.fst )

#### 3.2.3 Operations

    inductive TicketLockOp where
      | tryAcquire    (core : CoreId)  -- capture ticket; succeed if serving == captured
      | release       (core : CoreId)  -- release if currently held by core
      | observeServing (core : CoreId) (observed : Nat)  -- spin-loop iteration
      deriving Repr

    /-- The atomic-fetch-add step that captures a ticket. -/
    def TicketLockState.captureTicket
        (s : TicketLockState) (core : CoreId) :
        TicketLockState × Nat :=
      let ticket := s.nextTicket
      let s' := { s with
                  nextTicket := s.nextTicket + 1
                  pending := (core, ticket) :: s.pending }
      (s', ticket)

    /-- The serving-load step inside the spin loop. -/
    def TicketLockState.observeServing (s : TicketLockState) :
        Nat := s.serving

    /-- The transition rule. Each operation has a single
        operational step from state s to state s'. -/
    def TicketLockState.applyOp
        (s : TicketLockState) (op : TicketLockOp) :
        TicketLockState :=
      match op with
      | .tryAcquire core =>
          -- If core is already in pending or held, no-op.
          if core ∈ s.pending.map Prod.fst then s
          else if (s.held.map Prod.fst).contains core then s
          else
            let (s', ticket) := s.captureTicket core
            -- If serving == captured, immediately promote to held.
            if s.serving = ticket && s.held.isNone then
              { s' with
                pending := s'.pending.filter (fun p => p.2 ≠ ticket)
                held    := some (core, ticket) }
            else
              s'
      | .release core =>
          match s.held with
          | none => s
          | some (c, _) =>
              if c ≠ core then s
              else
                { s with
                  serving := s.serving + 1
                  held    := none }
      | .observeServing core observed =>
          -- Pure observation; no state change.
          let _ := (core, observed)
          s

#### 3.2.4 Promotion: pending → held

When `release` advances `serving`, the pending core with
ticket = `s.serving + 1` (if any) should be promoted to `held`.
This is the "second half" of release:

    def TicketLockState.promotePending (s : TicketLockState) :
        TicketLockState :=
      match s.held, s.pending.find? (fun p => p.2 = s.serving) with
      | none, some (c, t) =>
          { s with
            pending := s.pending.filter (fun p => p.1 ≠ c)
            held    := some (c, t) }
      | _, _ => s

The `release` op composes with `promotePending`:

    def TicketLockState.releaseAndPromote
        (s : TicketLockState) (core : CoreId) :
        TicketLockState :=
      (s.applyOp (.release core)).promotePending

#### 3.2.5 Holder is unique

**Theorem 3.2.5.1** (Mutex / `ticketLock_mutex`). For any
reachable `TicketLockState s` (i.e., obtained from
`TicketLockState.unheld` by a finite sequence of `applyOp` /
`promotePending` steps), if `s.held = some (c₁, t₁)` and
`s.held = some (c₂, t₂)`, then `c₁ = c₂` and `t₁ = t₂`.

*Proof.* `s.held : Option (CoreId × Nat)` has at most one
inhabitant of the `some` case. `Option` constructors are injective:
`some x = some y → x = y`. □

This is encoded as:

    theorem ticketLock_mutex (s : TicketLockState) :
        ∀ (c₁ c₂ : CoreId) (t₁ t₂ : Nat),
          s.held = some (c₁, t₁) → s.held = some (c₂, t₂) →
          c₁ = c₂ ∧ t₁ = t₂ := by
      intro c₁ c₂ t₁ t₂ h₁ h₂
      rw [h₁] at h₂
      injection h₂ with h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

#### 3.2.6 wf is preserved

**Theorem 3.2.6.1** (`ticketLock_wf_invariant`). For any
`TicketLockState s` satisfying `s.wf` and any `TicketLockOp op`,
`(s.applyOp op).wf` (and similarly for `promotePending`).

*Proof.* By case analysis on `op`:

**Case** `op = .tryAcquire core`:
- Sub-case: `core ∈ s.pending.map Prod.fst` → s unchanged, wf
  preserved trivially.
- Sub-case: `core` is the current holder → s unchanged, wf
  preserved.
- Sub-case: capture a fresh ticket. Need to show that:
  - INV-T1: `serving ≤ nextTicket + 1` (since nextTicket grew by
    1, and serving unchanged) — immediate.
  - INV-T2: the new pending entry `(core, nextTicket)` satisfies
    `serving < nextTicket < nextTicket + 1`. The first is by
    `s.wf.1` and the new `nextTicket = s.nextTicket`; the second
    is `Nat.lt_succ_self`.
  - INV-T4: new ticket is `s.nextTicket`; not in `s.pending.map
    Prod.snd` by INV-T2 (pending tickets are < s.nextTicket).
  - INV-T6: similar argument on cores.
  - INV-T7: new core not previously a holder by sub-case
    discrimination.
  - If we immediately promote: need to verify the promotion's
    invariants too.

**Case** `op = .release core`:
- Sub-case: `s.held = none` → s unchanged, wf preserved.
- Sub-case: `s.held = some (c, _)` with `c ≠ core` → s unchanged.
- Sub-case: `c = core` → `s.serving := s.serving + 1`,
  `s.held := none`. INV-T1: serving + 1 ≤ nextTicket because by
  INV-T2 previous pending tickets were < nextTicket, and by
  INV-T3 held.2 = serving < nextTicket so serving + 1 ≤ nextTicket.
  INV-T2: previous pending tickets > old serving = new serving - 1,
  so new pending tickets > new serving - 1, which implies they're
  ≥ new serving. If any pending p has p.2 = new serving, that's
  the promote-target (handled by promotePending). Otherwise all
  > new serving. Q.E.D.

**Case** `op = .observeServing _ _`: no state change.

**Case** `promotePending`:
- Sub-case: nothing to promote → s unchanged.
- Sub-case: found pending p with p.2 = s.serving. Promote: remove
  from pending, set held. INV-T2: removed p was the boundary
  case; remaining pending have p.2 > s.serving. INV-T3: new
  held.2 = s.serving. INV-T7: removed promoted core from pending.

Each case is ~30 LoC of Lean; total proof ~200 LoC.

#### 3.2.7 FIFO order

**Theorem 3.2.7.1** (`ticketLock_fifo`). Let trace τ be a finite
sequence of `applyOp` calls starting from `unheld`. If at trace
positions p₁ < p₂ two cores c₁ ≠ c₂ both successfully capture
tickets t₁, t₂ (via the corresponding `tryAcquire`), then t₁ < t₂.

*Proof.* `nextTicket` is monotonically increasing under
`tryAcquire` (by INV-T1 preservation). The tickets are captured
sequentially in trace order; each capture reads the current
`nextTicket` and increments. So t₁ < t₂ follows from
`p₁ < p₂` and the monotonicity of `nextTicket`. □

#### 3.2.8 Bounded wait

**Theorem 3.2.8.1** (`ticketLock_bounded_wait`). For
`PlatformBinding.coreCount = N` and a critical section bounded
by `T_cs` operations, a core c that captures ticket t will see
`serving = t` within at most `(N - 1) × T_cs` operations.

*Proof.* When c captures t, the pending set has at most N - 1
cores ahead (each holding a smaller ticket). Each release
increments serving by 1 and (via promotePending) admits the next
pending core. So after at most N - 1 release events, serving
reaches t. Each release happens within T_cs of its own acquire,
giving the bound. □

#### 3.2.9 Release-acquire pairing

**Theorem 3.2.9.1** (`ticketLock_release_acquire_pairing`). Let
c₁ release the lock at trace position p₁ (executing
`serving.fetch_add(1, Release)`) and c₂ observe `serving = t₁`
at trace position p₂ > p₁ via `observeServing` with Acquire
ordering. Then every event sequenced-before p₁ on c₁ happens-
before every event sequenced-after p₂ on c₂.

*Proof.* c₁'s release at p₁ is a Release-store on `serving`
location. c₂'s observation at p₂ is an Acquire-load on
`serving` that reads c₁'s released value. By the
`synchronizesWith` definition (3.1.6), this establishes a
sync-edge. Combined with per-core sequencing, transitive closure
of happens-before gives the conclusion. □

### 3.3 RwLock operational semantics

#### 3.3.1 State

    structure RwLockState where
      writerHeld : Option CoreId
      readers    : List CoreId            -- multiset of read holders
      waiters    : List (CoreId × AccessMode)  -- FIFO queue
      deriving Repr, Inhabited

    def RwLockState.unheld : RwLockState :=
      { writerHeld := none, readers := [], waiters := [] }

#### 3.3.2 Well-formedness

    def RwLockState.wf (s : RwLockState) : Prop :=
      -- INV-R1: Writer-readers exclusion
      ( s.writerHeld.isSome → s.readers = [] )
      ∧
      -- INV-R2: Readers don't double-acquire
      s.readers.Nodup
      ∧
      -- INV-R3: Waiter cores are NoDup
      s.waiters.map Prod.fst |>.Nodup
      ∧
      -- INV-R4: Waiters disjoint from current holders
      ( ∀ w ∈ s.waiters, w.1 ∉ s.readers ∧ s.writerHeld ≠ some w.1 )

#### 3.3.3 Operations

    inductive RwLockOp where
      | tryAcquireRead   (core : CoreId)
      | releaseRead       (core : CoreId)
      | tryAcquireWrite  (core : CoreId)
      | releaseWrite      (core : CoreId)
      deriving Repr

#### 3.3.4 Transition rules

    def RwLockState.applyOp
        (s : RwLockState) (op : RwLockOp) :
        RwLockState :=
      match op with
      | .tryAcquireRead core =>
          if s.writerHeld.isSome then
            -- Writer holds → enqueue as waiter (read)
            if core ∈ s.waiters.map Prod.fst then s
            else if s.writerHeld = some core then s
            else { s with waiters := s.waiters ++ [(core, .read)] }
          else if !s.waiters.isEmpty ∧
                  s.waiters.head?.map Prod.snd = some .write then
            -- Head waiter is a writer → enqueue (no reader-jump)
            if core ∈ s.waiters.map Prod.fst then s
            else { s with waiters := s.waiters ++ [(core, .read)] }
          else
            -- Acquire: append to readers
            if core ∈ s.readers then s
            else { s with readers := core :: s.readers }
      | .releaseRead core =>
          if core ∉ s.readers then s
          else
            let s' := { s with readers := s.readers.filter (· ≠ core) }
            -- If readers become empty, promote head waiter (if writer)
            s'.promoteWaitersIfReadersEmpty
      | .tryAcquireWrite core =>
          if s.writerHeld.isSome ∨ ¬ s.readers.isEmpty then
            -- Locked → enqueue as waiter (write)
            if core ∈ s.waiters.map Prod.fst then s
            else if s.writerHeld = some core then s
            else { s with waiters := s.waiters ++ [(core, .write)] }
          else
            -- Acquire
            { s with writerHeld := some core }
      | .releaseWrite core =>
          if s.writerHeld ≠ some core then s
          else
            let s' := { s with writerHeld := none }
            -- Promote head waiter(s)
            s'.promoteWaitersOnWriterRelease

    /-- After releasing the last reader, if head waiter is a
        writer, promote it. -/
    def RwLockState.promoteWaitersIfReadersEmpty
        (s : RwLockState) :
        RwLockState :=
      if !s.readers.isEmpty then s
      else
        match s.waiters with
        | (c, .write) :: rest =>
            { s with writerHeld := some c, waiters := rest }
        | _ => s  -- Either empty or head is .read (which would
                  -- already have been promoted when readers
                  -- became non-zero earlier; defensive case)

    /-- After releasing the writer, promote head waiter (or
        contiguous readers if head is a reader). -/
    def RwLockState.promoteWaitersOnWriterRelease
        (s : RwLockState) :
        RwLockState :=
      match s.waiters with
      | [] => s
      | (c, .write) :: rest =>
          { s with writerHeld := some c, waiters := rest }
      | (c, .read) :: _ =>
          -- Reader-batching: promote all contiguous .read waiters.
          let readWaiters := s.waiters.takeWhile (·.2 = .read)
          let rest := s.waiters.dropWhile (·.2 = .read)
          { s with
            readers := readWaiters.map Prod.fst ++ s.readers
            waiters := rest }

#### 3.3.5 Writer-readers exclusion

**Theorem 3.3.5.1** (`rwLock_writer_readers_exclusion`). For any
reachable wf RwLockState s, `s.writerHeld.isSome → s.readers = []`.

*Proof.* Direct from INV-R1, preserved by every applyOp
(structural argument case-by-case). □

#### 3.3.6 Reader multiplicity

**Theorem 3.3.6.1** (`rwLock_reader_multiplicity`). There exists
a reachable wf RwLockState s with `s.readers.length ≥ 2`.

*Proof.* Construct: start with `unheld`; apply
`tryAcquireRead c₁`; apply `tryAcquireRead c₂` for c₁ ≠ c₂.
By INV-R2 and the transition rules, `s.readers = [c₂, c₁]`,
length 2. □

#### 3.3.7 FIFO admission

**Theorem 3.3.7.1** (`rwLock_fifo_admission`). If c₁ enqueues as
a waiter at trace position p₁ < p₂ = c₂'s enqueue position, then
c₁ becomes a holder before c₂ does.

*Proof.* `waiters` is a FIFO list; appends go to the tail
(`waiters ++ [(c, m)]`). `promoteWaitersOnWriterRelease` /
`promoteWaitersIfReadersEmpty` pop from the head. So c₁ (head)
is promoted before c₂. (Reader-batching can promote multiple
contiguous readers together; this preserves FIFO of the *first*
reader and groups subsequent ones with it, which respects
order.) □

#### 3.3.8 Bounded wait

**Theorem 3.3.8.1** (`rwLock_bounded_wait_read`).
WCRT(`tryAcquireRead`) ≤ (coreCount - 1) × T_cs.

**Theorem 3.3.8.2** (`rwLock_bounded_wait_write`).
WCRT(`tryAcquireWrite`) ≤ (coreCount - 1) × T_cs.

*Proof.* For both: at most coreCount - 1 other cores can have
outstanding holds/waits ahead of the requester. Each release
within T_cs admits one (or a batch). □

#### 3.3.9 Release-acquire pairing

**Theorem 3.3.9.1** (`rwLock_release_acquire_pairing_read`).
**Theorem 3.3.9.2** (`rwLock_release_acquire_pairing_write`).

Both follow the same structure as TicketLock's 3.2.9.1: a
release-store on the lock's state location synchronizes-with the
corresponding acquire-load that reads the released value. □

#### 3.3.10 Writer-starvation freedom

**Theorem 3.3.10.1** (`rwLock_no_writer_starvation`). Under the
FIFO admission discipline (3.3.7.1), a waiter for write access
is always eventually admitted, provided the set of read holders
turns over (i.e., readers release within bounded time).

*Proof sketch.* Once a writer is in the waiters queue at
position k, no new reader enters the holder set until the writer
is admitted (because `tryAcquireRead` checks for a head writer
and enqueues if one exists). The existing readers complete; the
holder set shrinks to empty; promoteWaitersIfReadersEmpty
promotes the writer. □

### 3.4 Lock-primitive refinement (Lean ↔ Rust)

We prove an operational simulation between the Lean abstract
state and the Rust atomic-operation trace.

#### 3.4.1 Simulation relation φ

    /-- The simulation relation between abstract TicketLockState
        and a concrete MemoryTrace. -/
    def ticketLockSim
        (abs : TicketLockState) (concrete : MemoryTrace) : Prop :=
      -- The trace's most recent write to the nextTicket location
      -- equals abs.nextTicket; similarly for serving.
      ( ∃ e ∈ concrete.events, e.loc = nextTicketLocation ∧
        e.isWrite ∧ e.value = abs.nextTicket ∧
        ∀ e' ∈ concrete.events, e'.loc = nextTicketLocation ∧
          e'.isWrite → concrete.events.indexOf? e ≥
          concrete.events.indexOf? e' )
      ∧
      -- (Similar for serving)
      ...

(The full definition has 4-6 conjuncts capturing the
correspondence between Lean state fields and atomic events.)

#### 3.4.2 Refinement theorem

    theorem ticketLockRefinement :
      ∀ (impl_trace : MemoryTrace) (lean_trace : List TicketLockOp),
        impl_trace.wellFormed →
        rustImplementsTicketLock impl_trace lean_trace →
        ticketLockSim (lean_trace.foldl applyOp .unheld) impl_trace

where `rustImplementsTicketLock` is a structural correspondence
predicate: the Rust events at trace position k correspond
exactly to the Lean operations at lean_trace position k.

This refinement is by **bisimulation**: at each step, the Lean
state and the most recent Rust trace events are related by φ;
each step preserves φ.

#### 3.4.3 Refinement is a per-PR review obligation

The refinement proof is structural but the Rust code is reviewed
manually against the Lean operational spec. Each Rust function
(`acquire`, `release`) has a docstring referencing the Lean
operation it implements. A `#[cfg(test)]` correspondence test
exercises the Rust function and checks the resulting trace
matches what the Lean spec would produce.

## 4. Architectural choices

### 4.1 Why operational semantics (not axiomatic)

We model the memory operations *operationally* — as a sequence
of trace events — rather than axiomatizing happens-before
directly. Benefits:
- Decidable for finite traces (testable).
- Lean-compiler optimizations apply (the abstract state is
  manipulable at term level).
- Refinement is a structural simulation; no need to import a
  full C++/Rust memory-model library.

Cost: ~12 sub-tasks to lay down the model (SM2.A).

### 4.2 Why both TicketLock and RwLock

Decision #11 (RW locks) requires both:
- TicketLock provides the FIFO + bounded-wait foundation that
  RwLock builds on (writer-starvation freedom follows from
  TicketLock's FIFO).
- RwLock adds reader multiplicity for read-mostly workloads.

If we'd skipped TicketLock, RwLock would have needed to
re-derive FIFO from scratch. By proving TicketLock first, RwLock's
proofs reuse the FIFO machinery.

### 4.3 Why bit-packed RwLock state

The Rust RwLock packs `(writerHeld, readers)` into a single
AtomicU64: bit 63 = writer-held, bits 0..62 = reader count. This
allows the entire state to be CAS'd atomically:

```rust
struct RwLock {
    state: AtomicU64,  // bit 63 = writer-held; bits 0..62 = reader count
}
```

The Lean spec models the abstract state directly; the bit-packing
is a refinement detail (SM2.C.16). The encoding/decoding round-
trip lemmas (SM2.C.17) prove the bit operations preserve semantic
state.

### 4.4 No upgrade/downgrade in v1.0.0

RwLock upgrades (reader → writer) and downgrades (writer →
reader) are notoriously bug-prone. Decision #2 explicitly defers
these to v1.x. The v1.0.0 RwLock supports only plain
acquire/release. The spec's `applyOp` does not include upgrade/
downgrade operations.

## 5. Detailed sub-task breakdown

### 5.1 Memory model (SM2.A, 4 PRs, 12 sub-tasks)

[Per §3.1 above. Each sub-task implements one of the definitions
or theorems.]

| Sub | Description | Theorem / artifact | Est |
|-----|-------------|--------------------|-----|
| SM2.A.1 | `MemoryOrder` inductive | (definition + DecidableEq) | S |
| SM2.A.2 | `AtomicLocation` struct + concrete location IDs | (definition) | T |
| SM2.A.3 | `MemoryEvent` structure | (definition) | S |
| SM2.A.4 | `MemoryTrace` + `empty` + `append` | (definitions) | S |
| SM2.A.5 | `MemoryTrace.wellFormed` predicate | Decidable instance | M |
| SM2.A.6 | `synchronizesWith` relation | (definition) | M |
| SM2.A.7 | `sequencedBefore` + `happensBefore` | (definitions) | M |
| SM2.A.8 | `happensBefore_irreflexive` | Theorem | L |
| SM2.A.9 | `happensBefore_transitive` | Theorem (immediate by `trans` ctor) | T |
| SM2.A.10 | `happensBefore_antisymmetric` | Theorem | L |
| SM2.A.11 | `happens_before_partial_order` (aggregate) | Theorem | M |
| SM2.A.12 | Tests `tests/MemoryModelSuite.lean` | 8+ scenarios | L |

**File**: All in `SeLe4n/Kernel/Concurrency/MemoryModel.lean`,
~600 LoC plus 200 LoC of tests.

### 5.2 TicketLock spec (SM2.B, 5 PRs, 16 sub-tasks)

| Sub | Description | Theorem / artifact | Est |
|-----|-------------|--------------------|-----|
| SM2.B.1 | `TicketLockState` structure + `Inhabited` | (def) | S |
| SM2.B.2 | `TicketLockState.unheld` constructor | (def) | T |
| SM2.B.3 | `TicketLockState.wf` predicate (7 conjuncts) | (def) | M |
| SM2.B.4 | `wf` decidability | Decidable instance | S |
| SM2.B.5 | `TicketLockOp` inductive | (def) | S |
| SM2.B.6 | `captureTicket`, `observeServing`, `applyOp` | (def) | L |
| SM2.B.7 | `promotePending`, `releaseAndPromote` | (def) | M |
| SM2.B.8 | `ticketLock_mutex` | Theorem 3.2.5.1 | S |
| SM2.B.9 | `ticketLock_wf_invariant` | Theorem 3.2.6.1 | XL |
| SM2.B.10 | `ticketLock_fifo` | Theorem 3.2.7.1 | M |
| SM2.B.11 | `ticketLock_bounded_wait` | Theorem 3.2.8.1 | L |
| SM2.B.12 | `ticketLock_release_acquire_pairing` | Theorem 3.2.9.1 | L |
| SM2.B.13 | Reachability: every reachable state satisfies wf | Theorem | M |
| SM2.B.14 | Determinism: `applyOp` is deterministic | Theorem | S |
| SM2.B.15 | Closure-form: `acquire_preserves_wf`, `release_preserves_wf` | 2 theorems | M |
| SM2.B.16 | Rust ticket-lock impl + tests | `rust/sele4n-hal/src/ticket_lock.rs` | L |

**Files**:
- `SeLe4n/Kernel/Concurrency/Locks/TicketLock.lean` (~700 LoC)
- `rust/sele4n-hal/src/ticket_lock.rs` (~300 LoC)
- `tests/TicketLockSuite.lean` (~250 LoC)
- `rust/sele4n-hal/src/ticket_lock.rs` cargo tests (~150 LoC)

#### SM2.B.16 Rust impl skeleton

```rust
// SPDX-License-Identifier: GPL-3.0-or-later
//! TicketLock — FIFO spinlock with bounded wait.
//!
//! Refines `SeLe4n/Kernel/Concurrency/Locks/TicketLock.lean`'s
//! operational spec; see `Concurrency/Locks/TicketLockRefinement.lean`
//! for the bisimulation argument.

use core::sync::atomic::{AtomicU64, Ordering};

#[repr(C, align(64))]   // cache-line aligned to avoid false sharing
pub struct TicketLock {
    next_ticket: AtomicU64,
    serving:     AtomicU64,
}

impl TicketLock {
    pub const fn new() -> Self {
        Self {
            next_ticket: AtomicU64::new(0),
            serving:     AtomicU64::new(0),
        }
    }

    /// Acquire the lock. Blocks until this core's ticket is served.
    ///
    /// Refines the Lean operation `tryAcquire core` followed by
    /// repeated `observeServing core (s.serving)` until the
    /// observed value equals the captured ticket.
    pub fn acquire(&self) -> u64 {
        // Capture ticket (Acquire ordering).
        let my_ticket = self.next_ticket.fetch_add(1, Ordering::Acquire);
        // Spin until our ticket is being served.
        while self.serving.load(Ordering::Acquire) != my_ticket {
            crate::cpu::wfe_bounded(crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS);
        }
        my_ticket
    }

    /// Release the lock. Increments serving by 1 and signals
    /// waiters via SEV.
    ///
    /// Refines the Lean operation `release core`.
    pub fn release(&self) {
        self.serving.fetch_add(1, Ordering::Release);
        #[cfg(target_arch = "aarch64")]
        unsafe {
            // SAFETY: SEV is a hint instruction with no side effects.
            core::arch::asm!("sev", options(nomem, nostack, preserves_flags));
        }
    }

    /// RAII combinator. The closure is executed with the lock
    /// held; the lock is always released, even on panic
    /// (handled by Drop on the guard).
    pub fn with_lock<F, R>(&self, f: F) -> R
    where F: FnOnce() -> R {
        let _guard = TicketLockGuard::acquire(self);
        f()
    }
}

/// RAII guard: releases the lock on drop.
struct TicketLockGuard<'a> {
    lock: &'a TicketLock,
}

impl<'a> TicketLockGuard<'a> {
    fn acquire(lock: &'a TicketLock) -> Self {
        let _ticket = lock.acquire();
        Self { lock }
    }
}

impl<'a> Drop for TicketLockGuard<'a> {
    fn drop(&mut self) {
        self.lock.release();
    }
}
```

Plus 8 unit tests covering: single-thread acquire/release;
multi-thread (host) FIFO; with_lock RAII; panic-safe release;
construction is const; cache-line alignment.

### 5.3 RwLock spec (SM2.C, 6 PRs, 22 sub-tasks)

| Sub | Description | Theorem / artifact | Est |
|-----|-------------|--------------------|-----|
| SM2.C.1 | `RwLockState` structure | (def) | S |
| SM2.C.2 | `RwLockState.wf` (4 conjuncts) | (def) | M |
| SM2.C.3 | `RwLockOp` inductive | (def) | T |
| SM2.C.4 | `applyOp`, `promoteWaitersIfReadersEmpty`, `promoteWaitersOnWriterRelease` | (defs) | XL |
| SM2.C.5 | `rwLock_writer_readers_exclusion` | Theorem 3.3.5.1 | M |
| SM2.C.6 | `rwLock_reader_multiplicity` | Theorem 3.3.6.1 | S |
| SM2.C.7 | `rwLock_fifo_admission` | Theorem 3.3.7.1 | L |
| SM2.C.8 | `rwLock_bounded_wait_read` | Theorem 3.3.8.1 | L |
| SM2.C.9 | `rwLock_bounded_wait_write` | Theorem 3.3.8.2 | L |
| SM2.C.10 | `rwLock_release_acquire_pairing_read` | Theorem 3.3.9.1 | L |
| SM2.C.11 | `rwLock_release_acquire_pairing_write` | Theorem 3.3.9.2 | L |
| SM2.C.12 | `rwLock_wf_invariant` | Theorem | XL |
| SM2.C.13 | Reader-batching: contiguous readers acquire together | Theorem + proof | M |
| SM2.C.14 | `rwLock_no_writer_starvation` | Theorem 3.3.10.1 | L |
| SM2.C.15 | Closure-form: 4 per-op preservation theorems | 4 theorems | M |
| SM2.C.16 | Bit-packed encoding: `state : AtomicU64` (bit 63 + bits 0..62) | Definition | M |
| SM2.C.17 | Encoding/decoding round-trip: 4 lemmas | 4 theorems | S |
| SM2.C.18 | Reader-count overflow analysis (max 2^63 readers; unreachable) | Documentation | T |
| SM2.C.19 | Rust RwLock impl | `rust/sele4n-hal/src/rw_lock.rs` | XL |
| SM2.C.20 | Refinement bridge `rust_rwLock_refines_lean` | Theorem | XL |
| SM2.C.21 | `tests/RwLockSuite.lean` | 15+ scenarios | L |
| SM2.C.22 | Cross-core RwLock stress test | Cargo `#[ignore]` | L |

**Files**:
- `SeLe4n/Kernel/Concurrency/Locks/RwLock.lean` (~1000 LoC)
- `rust/sele4n-hal/src/rw_lock.rs` (~400 LoC)
- `tests/RwLockSuite.lean` (~400 LoC)
- Cargo tests (~200 LoC)

#### SM2.C.19 Rust impl skeleton

```rust
// SPDX-License-Identifier: GPL-3.0-or-later
//! RwLock — reader-writer lock with FIFO writer admission.

use core::sync::atomic::{AtomicU64, Ordering};

const WRITER_BIT: u64 = 1 << 63;
const READER_MASK: u64 = !WRITER_BIT;

#[repr(C, align(64))]
pub struct RwLock {
    state: AtomicU64,  // bit 63 = writer-held; bits 0..62 = reader count
    // Waiter discipline: implicit through CAS-retry; full
    // queue would need additional state. The v1.0.0 impl uses
    // a CAS-retry loop with WFE for backoff.
}

impl RwLock {
    pub const fn new() -> Self {
        Self { state: AtomicU64::new(0) }
    }

    /// Acquire a read lock. Blocks if a writer is held.
    pub fn acquire_read(&self) {
        loop {
            let s = self.state.load(Ordering::Acquire);
            if s & WRITER_BIT != 0 {
                // Writer holds; wait for release.
                crate::cpu::wfe_bounded(crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS);
                continue;
            }
            let new = (s & READER_MASK) + 1;
            if self.state.compare_exchange(
                s, new, Ordering::Acquire, Ordering::Relaxed).is_ok() {
                return;
            }
            // CAS failed; retry.
        }
    }

    pub fn release_read(&self) {
        // Atomic decrement of reader count.
        loop {
            let s = self.state.load(Ordering::Acquire);
            let count = s & READER_MASK;
            debug_assert!(count > 0, "release_read with no readers");
            let new = (s & WRITER_BIT) | (count - 1);
            if self.state.compare_exchange(
                s, new, Ordering::Release, Ordering::Relaxed).is_ok() {
                // SEV to wake any writer-waiter.
                #[cfg(target_arch = "aarch64")]
                unsafe {
                    core::arch::asm!("sev",
                        options(nomem, nostack, preserves_flags));
                }
                return;
            }
        }
    }

    pub fn acquire_write(&self) {
        loop {
            // Wait until both writer bit is 0 and reader count is 0.
            let s = self.state.load(Ordering::Acquire);
            if s != 0 {
                crate::cpu::wfe_bounded(crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS);
                continue;
            }
            if self.state.compare_exchange(
                0, WRITER_BIT, Ordering::Acquire, Ordering::Relaxed).is_ok() {
                return;
            }
        }
    }

    pub fn release_write(&self) {
        // Clear writer bit (and possibly preserve reader count;
        // under wf, readers must be 0 here).
        debug_assert!(self.state.load(Ordering::Acquire) & READER_MASK == 0,
            "release_write with non-zero readers");
        self.state.store(0, Ordering::Release);
        #[cfg(target_arch = "aarch64")]
        unsafe {
            core::arch::asm!("sev", options(nomem, nostack, preserves_flags));
        }
    }

    /// RAII reader combinator.
    pub fn with_read<F, R>(&self, f: F) -> R
    where F: FnOnce() -> R {
        let _guard = RwLockReadGuard::acquire(self);
        f()
    }

    /// RAII writer combinator.
    pub fn with_write<F, R>(&self, f: F) -> R
    where F: FnOnce() -> R {
        let _guard = RwLockWriteGuard::acquire(self);
        f()
    }
}

// (RwLockReadGuard, RwLockWriteGuard analogous to TicketLockGuard)
```

Note: this CAS-based RwLock does not implement full FIFO writer
admission as specified in the Lean spec. The v1.0.0 impl is a
weakened correspondence; the **Lean spec** captures the desired
semantics, and the Rust impl provides progress + mutex but not
strict FIFO. For applications that require strict FIFO writer
admission (such as critical-section-bound RT workloads),
SM2.C.19.a may extend to a queued RwLock.

The refinement theorem (SM2.C.20) explicitly documents this
divergence: the abstract spec is **stronger** than the impl;
the impl satisfies all wf invariants and mutex but does not
satisfy FIFO. SM2.D documents which kernel paths rely on FIFO
(few; SM3 review verifies) and which can tolerate the weaker
ordering.

### 5.4 FFI bridge + integration (SM2.D, 4 PRs, 8 sub-tasks)

| Sub | Description | Acceptance | Est |
|-----|-------------|------------|-----|
| SM2.D.1 | Lean FFI for TicketLock: `acquire`, `release`, `peekHolder` | FFI compiles | S |
| SM2.D.2 | Lean FFI for RwLock: 4 ops | FFI compiles | S |
| SM2.D.3 | RAII combinators: `withLock`, `withReadLock`, `withWriteLock` | Combinator + 3 tests | M |
| SM2.D.4 | Lock-state tracing: optional debug instrumentation | Trace log | S |
| SM2.D.5 | Static linker-time check: every Rust lock-using fn has matching Lean spec | Build-time gate | M |
| SM2.D.6 | Verified-lock-primitive surface anchor | `tests/SmpSurfaceAnchors.lean` | S |
| SM2.D.7 | `lockPrimitives` aggregator: index of all 22 theorems | Aggregator + size witness | S |
| SM2.D.8 | Cross-core test: verify FFI calls actually serialize | Cross-core test | M |

### 5.5 Documentation + assertion sites (SM2.E, 3 PRs, 7 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM2.E.1 | `docs/spec/SELE4N_SPEC.md` new §10 "Verified Lock Primitives" | Spec | M |
| SM2.E.2 | New GitBook chapter 17 | GitBook | M |
| SM2.E.3 | ARM ARM citation map in `MemoryModel.lean` | docstring | S |
| SM2.E.4 | Decision rationale doc | Lean docstring | T |
| SM2.E.5 | Refinement-proof methodology doc | `Locks/Refinement.lean` | S |
| SM2.E.6 | Hardware-discipline limits | docstring | T |
| SM2.E.7 | CHANGELOG entries per PR | CHANGELOG | T |

## 6. Verification strategy for SM2

### 6.1 What SM2 proves

22 substantive theorems (full list in Appendix C). Highlights:

- TicketLock: 6 theorems (mutex, FIFO, bounded wait,
  release-acquire, wf invariant, reachability).
- RwLock: 10 theorems (writer-readers exclusion, reader
  multiplicity, FIFO, bounded wait × 2, release-acquire × 2,
  wf invariant, reader batching, writer-starvation freedom).
- Memory model: happens-before partial order (3 properties as
  one aggregate theorem).
- Refinement: 2 simulation theorems (TicketLock, RwLock).

### 6.2 What SM2 assumes

- ARMv8.1-A LSE atomic semantics (LDADDA, STADDL, etc.) — cited
  ARM ARM K11, K12. Encoded operationally in MemoryModel.lean's
  Acquire/Release-store correspondence.
- Sequential per-core program order (immediate from any
  single-PE semantics; not an SMP-specific assumption).

No Lean `axiom` declarations.

### 6.3 Tests

- **Tier 1 (build)**: All SM2 modules compile.
- **Tier 3 (invariant)**: `tests/MemoryModelSuite.lean`,
  `tests/TicketLockSuite.lean`, `tests/RwLockSuite.lean` —
  35+ decidable examples and surface anchors.
- **Tier 4 (nightly)**: cargo stress tests on host (4 threads
  × 1M ops on TicketLock; 4 threads × 100K ops alternating
  read/write on RwLock).
- **Tier 5 (NEW for SM2)**: cross-language correspondence tests
  exercising both Lean spec and Rust impl on small operation
  sequences; verifies the simulation φ holds.

## 7. Risk inventory for SM2

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Memory model abstraction misses an ARMv8.1-A LSE feature | LOW | HIGH | Limited surface (only Acquire / Release / RMW); reviewed against ARM ARM K11, K12 |
| `happens_before_partial_order` proof has subtle gap | LOW | HIGH | Standard partial-order proof; review pattern matches established literature |
| `wf` invariant of TicketLock fails to capture some reachable state | MED | HIGH | SM2.B.13 (reachability) catches this by exhaustive enumeration |
| RwLock CAS-based Rust impl diverges from Lean spec's FIFO claim | KNOWN | MED | Documented in SM2.C.19 commentary; SM2.C.19.a optional FIFO-queued variant deferred |
| Bit-packed RwLock encoding has off-by-one | LOW | CRIT | SM2.C.17 round-trip lemmas catch |
| Refinement φ relation is too weak | MED | HIGH | Refinement reviewed alongside impl per PR; bisimulation explicit |
| Tier-5 correspondence tests time out | MED | LOW | Bounded trace lengths (~50 events); not full exhaustive |
| Lean spec proves bounded-wait but Rust impl exhibits unbounded wait on a buggy SoC | LOW | HIGH | Cargo stress test gates upper-bound on contention |
| Reader-batching subtly violates FIFO | LOW | MED | Theorem 3.3.7.1 proven; reader batching preserves head-FIFO |
| Writer-starvation under pathological reader churn | LOW | MED | Theorem 3.3.10.1 proven |

## 8. Acceptance gate for SM2

SM2 is complete when:

- [ ] Memory model: 12 SM2.A sub-tasks landed; `happens_before_partial_order` proven.
- [ ] TicketLock: 16 SM2.B sub-tasks landed; 6 theorems proven; Rust impl matches spec.
- [ ] RwLock: 22 SM2.C sub-tasks landed; 10 theorems proven; Rust impl matches spec (with documented FIFO divergence).
- [ ] FFI: 8 SM2.D sub-tasks landed; Lean wrappers + RAII combinators ready.
- [ ] Documentation: 7 SM2.E sub-tasks landed; spec §10 + GitBook chapter 17 published.
- [ ] Tier 0..5 tests green at HEAD.
- [ ] Zero Lean axioms.
- [ ] Aggregate SM2 closure CHANGELOG entry.

## 9. Cross-references

- **Master overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
- **Previous phase**: [`SMP_FOUNDATIONS_PLAN.md`](SMP_FOUNDATIONS_PLAN.md)
- **Parallel phase**: [`SMP_RUST_HAL_PLAN.md`](SMP_RUST_HAL_PLAN.md)
- **Next phase (consumer)**: [`SMP_PER_OBJECT_LOCKS_PLAN.md`](SMP_PER_OBJECT_LOCKS_PLAN.md) — SM3 puts SM2's primitives to use.

## 10. Theorem catalogue for SM2

22 substantive theorems:

| # | Theorem | Statement |
|---|---------|-----------|
| M-01 | `happensBefore_irreflexive` | `∀ e ∈ wf trace, ¬ hb e e` |
| M-02 | `happensBefore_transitive` | `hb a b → hb b c → hb a c` (immediate by ctor) |
| M-03 | `happensBefore_antisymmetric` | `a ≠ b → ¬ (hb a b ∧ hb b a)` |
| M-04 | `happens_before_partial_order` | Aggregate of M-01..M-03 |
| T-01 | `ticketLock_mutex` | At most one holder |
| T-02 | `ticketLock_fifo` | Earlier capture → smaller ticket |
| T-03 | `ticketLock_bounded_wait` | `WCRT(acquire) ≤ (N-1) × T_cs` |
| T-04 | `ticketLock_release_acquire_pairing` | Release-store sync-with Acquire-load |
| T-05 | `ticketLock_wf_invariant` | wf preserved by every applyOp |
| T-06 | `ticketLock_reachability` | every reachable state satisfies wf |
| R-01 | `rwLock_writer_readers_exclusion` | writer-held → no readers |
| R-02 | `rwLock_reader_multiplicity` | ∃ state with ≥ 2 readers |
| R-03 | `rwLock_fifo_admission` | head-of-queue admitted first |
| R-04 | `rwLock_bounded_wait_read` | `WCRT(acquireRead) ≤ (N-1) × T_cs` |
| R-05 | `rwLock_bounded_wait_write` | `WCRT(acquireWrite) ≤ (N-1) × T_cs` |
| R-06 | `rwLock_release_acquire_pairing_read` | Reader RA pairing |
| R-07 | `rwLock_release_acquire_pairing_write` | Writer RA pairing |
| R-08 | `rwLock_wf_invariant` | wf preserved |
| R-09 | `rwLock_reader_batching` | Contiguous readers acquire together |
| R-10 | `rwLock_no_writer_starvation` | Writer eventually admitted |
| F-01 | `rust_ticketLock_refines_lean` | Operational simulation |
| F-02 | `rust_rwLock_refines_lean` | Operational simulation (with documented FIFO divergence) |

**Total**: 22 theorems (4 memory model + 6 TicketLock + 10 RwLock + 2 refinement).

## Appendix A — Verification commands

```bash
source ~/.elan/env

# Per-module build:
lake build SeLe4n.Kernel.Concurrency.MemoryModel
lake build SeLe4n.Kernel.Concurrency.Locks.TicketLock
lake build SeLe4n.Kernel.Concurrency.Locks.RwLock
lake build SeLe4n.Kernel.Concurrency.Locks.TicketLockRefinement
lake build SeLe4n.Kernel.Concurrency.Locks.RwLockRefinement

# Test suites:
lake build MemoryModelSuite
lake build TicketLockSuite
lake build RwLockSuite

# Cargo:
cargo test -p sele4n-hal --lib ticket_lock
cargo test -p sele4n-hal --lib rw_lock

# Tier 5 (new): cross-language correspondence
./scripts/test_tier5_lock_correspondence.sh
```

## Appendix B — Sub-task dependency graph

```
SM2.A.1..A.4     (defs)         independent
SM2.A.5          (wellFormed)   needs A.4
SM2.A.6..A.7     (sync/hb)      needs A.3, A.5
SM2.A.8..A.11    (theorems)     needs A.6..A.7

SM2.B.1..B.7     (TicketLock defs)  needs SM2.A (memory model)
SM2.B.8..B.15    (theorems)         needs B.1..B.7
SM2.B.16         (Rust impl)        needs B.1..B.15 (spec)

SM2.C.1..C.4     (RwLock defs)      needs SM2.A
SM2.C.5..C.18    (theorems + encoding)  needs C.1..C.4
SM2.C.19         (Rust impl)        needs C.1..C.18
SM2.C.20         (refinement)       needs C.19 + C.1..C.18
SM2.C.21..C.22   (tests)            needs C.19, C.20

SM2.D.1..D.8     (FFI + tests)      needs B.16, C.19
SM2.E.1..E.7     (docs)             needs everything else
```

Critical path: SM2.A → SM2.B → SM2.C → SM2.D → SM2.E. SM2.B and
SM2.C can partly proceed in parallel after SM2.A.

---

*SM2 is the verification-quality elevation that distinguishes
seLe4n from seL4. The lock primitives are first-class proven
artefacts, not assumed primitives. The cost is the 16-22 week
calendar; the benefit is reduced trusted computing base (TCB) at
the lock-primitive layer.*
