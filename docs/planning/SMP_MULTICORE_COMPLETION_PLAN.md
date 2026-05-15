# WS-SM — SMP / Multi-Core Completion (pre-v1.0.0)

> **Status**: PLAN — workstream to land in full before the v1.0.0 cut.
>
> **Audited cut**: `v0.31.2` (current `lakefile.toml::version`).
>
> **Branch (this audit)**: `claude/audit-multicore-implementation-sUcIx`.
>
> **Release target**: **v1.0.0 "bootable verified SMP microkernel on
> Raspberry Pi 5"** — bootable on all 4 BCM2712 cores with the SMP
> path verified at the same rigor seL4 applies to its single-core
> kernel, plus verified lock primitives that the seL4 project
> historically left as assumptions.
>
> **Sequencing**: WS-RC retargets from v1.0.0 to **v0.31.last** (R2..R6
> close at v0.31.last; substance unchanged, only the version-bump
> sub-tasks shift). WS-SM opens at v0.32.0 and runs through v1.0.0.
>
> **Maintainer decisions taken** (recorded in §10; drove this plan):
> 1. Lock layout: **per-object fine locks**.
> 2. Lock type: **reader-writer (RW)** with exclusive-only acquire/
>    release for v1.0.0 (no upgrade/downgrade).
> 3. Lock acquire-order: **hierarchical by object kind** then ObjId.val
>    within kind.
> 4. Model rewrite: **path-a replacement** (singular fields become
>    `Vector α coreCount`; no bootCore shim).
> 5. numCores parameterization: **PlatformBinding.coreCount**
>    typeclass field (RPi5 sets 4).
> 6. Sharing domain: **PlatformBinding.sharingDomain : SharingDomain**
>    (RPi5 sets `.inner`; cross-cluster ports set `.outer`).
> 7. Default SMP activation: **enabled by default** on RPi5; opt-out
>    via `smp_enabled=false`.
> 8. Idle threads: **per-core idle TCBs** (one per core).
> 9. SM0 sequencing: **spread across many small PRs** (v0.32.0..v0.32.x).
> 10. Lock primitive verification: **TicketLock + RwLock semantics
>     modelled in Lean against an abstract ARMv8.1-A LSE memory
>     model and proven correct** (axiom budget for the lock module
>     itself: 0; only the ARMv8.1-A LSE memory-model axioms remain,
>     and those are themselves discharged through documented ARM ARM
>     citations).
> 11. Workstream ID: **WS-SM**.
> 12. Timeline: **accept ~24-30 months** to v1.0.0 at the project's
>     single-maintainer cadence; ship when WS-SM completes, even if
>     that is late 2027 / early 2028.
>
> **Out of scope** (deferred past v1.0.0):
> - ARMv9-A Confidential Compute / MPAM partitioning — separate
>   plan, [`HARDWARE_PARTITION_ISOLATION_PLAN.md`](HARDWARE_PARTITION_ISOLATION_PLAN.md);
>   depends on WS-SM as prerequisite.
> - Heterogeneous / big.LITTLE asymmetric topologies.
> - Hot-unplug, live core migration, cpu-frequency scaling.
> - RwLock upgrade/downgrade (reader→writer, writer→reader) — v1.x
>   post-1.0 hardening; v1.0.0 supports plain acquire/release only.
> - NUMA / non-uniform memory.
> - Per-CPU work-stealing scheduler — v1.0.0 uses affinity-bound
>   threads (no migration); work-stealing is a v1.x performance
>   workstream.

## 1. Executive summary

### 1.1 The core finding

The current SMP scaffolding cannot be activated: four CRITICAL
gaps make `SMP_ENABLED = true` either dead code (no caller) or
a correctness hazard (secondaries wake into a state the kernel
can neither observe nor coordinate, TLB invalidations don't
broadcast, kernel state races on concurrent entries). The AN9-J
disposition ("activation cost is just flipping the runtime flag",
`AUDIT_v0.29.0_DEFERRED.md:296`) is materially inaccurate.
Shipping v1.0.0 under that disposition would ship a non-functional
SMP binary on a 4-core SoC.

### 1.2 Headline-severity findings (catalogue in §3)

| Sev | ID | Finding |
|-----|----|---------|
| **CRIT** | SMP-C1 | `bring_up_secondaries()` is never called. No Phase 5 in `rust_boot_main` parses `smp_enabled` or invokes bring-up. |
| **CRIT** | SMP-C2 | `rust_secondary_main` skips MMU/VBAR/GIC/timer init. Secondaries wake with MMU off and exception vectors unset. |
| **CRIT** | SMP-C3 | `kernelStateRef : IO.Ref SystemState` is one shared, non-atomic Ref. Concurrent kernel entries race. |
| **CRIT** | SMP-C4 | TLB invalidation uses non-IS variants (`tlbi vae1`, not `vae1is`). Page unmaps leave stale translations on remote cores at the hardware level. |
| **HIGH** | SMP-H1 | No SGI / IPI primitive in `gic.rs`. Cross-core wake, TLB shootdown impossible. |
| **HIGH** | SMP-H2 | `ArchAssumption` lacks the `singleCoreOperation` constructor that `Concurrency/Assumptions.lean` advertises. |
| **HIGH** | SMP-H3 | Inventory `Lean.Name` literals not build-checked. |
| **HIGH** | SMP-H4 | No spinlock or lock primitive of any kind. `with_interrupts_disabled` is the only atomicity primitive and it does not cross cores. |
| **MED** | SMP-M1..M7, **LOW** | SMP-L1..L5 — documentation, hygiene, scope items (§3.9). |

### 1.3 Workstream shape

**WS-SM**, 10 phases, ~520–640 sub-tasks, ~24–30 months at the
project's solo-maintainer cadence.

```
SM0  Foundations & honesty patches              (18-25 PRs, 40-50 sub)
SM1  Rust HAL completion                        (22-32 PRs, 60-80 sub)
SM2  Verified lock primitives (Lean + Rust)     (28-40 PRs, 70-95 sub)
SM3  Per-object lock fields + hierarchical order(18-26 PRs, 50-65 sub)
SM4  Path-a per-core state replacement          (35-50 PRs, 90-115 sub)
SM5  Per-core scheduler                         (28-38 PRs, 75-95 sub)
SM6  Cross-core IPC                             (22-32 PRs, 60-80 sub)
SM7  TLB / cache shootdown                      (15-22 PRs, 40-55 sub)
SM8  Information flow under SMP                 (15-22 PRs, 40-55 sub)
SM9  Documentation, tests, version closure      (10-15 PRs, 25-35 sub)
──────────────────────────────────────────────────────────────────────
                                                211-302 PRs total
```

Parallelism: SM0 must complete first; SM1 || SM2 (independent);
SM3 gates on SM2 (lock primitives) and SM1.B (Rust types); SM4 ||
SM3 (independent state-shape work); SM5 gates on SM3+SM4; SM6
gates on SM5; SM7 || SM6 after SM3; SM8 || SM6/SM7 after SM4; SM9
last.

## 2. Mathematical foundations

This section pins the formal specification of SMP semantics that
every subsequent phase relies on. The model is **per-object
reader-writer fine locking** with **hierarchical-by-kind acquire
order**, **path-a per-core kernel state**, and **fully verified
lock primitives**. All claims have an ARM ARM citation or follow
strictly from cited claims.

### 2.1 Concurrency model: per-object RW fine-lock serialization

**Definition 2.1.1** (Per-object lock). Each kernel object owns a
reader-writer lock embedded as a structure field:

    -- Each object kind gains a `lock : RwLock` field
    structure ThreadControlBlock where
      ...                             -- existing fields
      lock : RwLock := RwLock.unheld
    structure Endpoint where
      ...
      lock : RwLock := RwLock.unheld
    -- and analogously for CNode, Notification, Reply, SchedContext,
    -- VSpaceRoot, Page. The ObjStore (RobinHood) gains a single
    -- table-level RwLock.

**Definition 2.1.2** (Lock kind hierarchy). Every kernel-object
lock has a kind drawn from a 10-level total order:

    inductive LockKind where
      | objStore         -- the RobinHood hash table (level 0)
      | untyped          -- Untyped memory regions   (level 1)
      | cnode            -- Capability nodes         (level 2)
      | tcb              -- Thread control blocks    (level 3)
      | endpoint         -- IPC endpoints            (level 4)
      | notification     -- Notification objects     (level 5)
      | reply            -- Reply objects            (level 6)
      | schedContext     -- Scheduling contexts      (level 7)
      | vspaceRoot       -- VSpace roots / ASIDs     (level 8)
      | page             -- Page frames              (level 9)
      deriving DecidableEq, Repr

    def LockKind.level : LockKind → Nat
      | .objStore => 0  | .untyped => 1  | .cnode => 2
      | .tcb => 3       | .endpoint => 4 | .notification => 5
      | .reply => 6     | .schedContext => 7
      | .vspaceRoot => 8 | .page => 9

The choice of order reflects typical kernel-operation dependency:
operations on objects of kind K typically need only objects of
kind ≤ K (e.g., retype reads Untyped, writes CNode; capability
copy reads source CNode, writes dest CNode + CDT; IPC operations
read TCB + write Endpoint queue).

**Definition 2.1.3** (Lock identity).

    structure LockId where
      kind  : LockKind
      objId : ObjId
      deriving DecidableEq, Repr

    /-- Hierarchical-by-kind, then ObjId.val within kind. -/
    instance : LE LockId where
      le l₁ l₂ :=
        l₁.kind.level < l₂.kind.level ∨
        (l₁.kind.level = l₂.kind.level ∧ l₁.objId.val ≤ l₂.objId.val)

    theorem LockId.le_total : ∀ l₁ l₂ : LockId, l₁ ≤ l₂ ∨ l₂ ≤ l₁ := by
      intros; -- by lex-of-totals on (level, objId.val)
      sorry  -- proven by case analysis in Locks.lean

**Definition 2.1.4** (Access mode).

    inductive AccessMode where
      | read
      | write
      deriving DecidableEq, Repr

**Definition 2.1.5** (Lock-set of a transition). For each kernel
transition τ : SystemState × Args → KernelResult, declare its
**lock-set** as a finite map:

    def lockSet (τ : KernelTransition) (args : Args) : Finset (LockId × AccessMode)

  The lock-set is **statically derivable**: it depends only on
  the *shape* of the args (ObjIds appearing in caps, register
  values), not on data in the kernel state. We pin this by making
  `lockSet` total over (τ, args) pairs without consulting the
  state.

**Definition 2.1.6** (Lock-set ordering). Acquire by ascending
`LockId` order (Definition 2.1.3); release in reverse.

    def lockAcquireSequence (S : Finset (LockId × AccessMode)) :
        List (LockId × AccessMode) :=
      S.toList.qsort (fun (l₁, _) (l₂, _) => l₁ ≤ l₂)

**Theorem 2.1.7** (Lock-set ordering is canonical). For any
finite set S, `lockAcquireSequence S` is the unique sorted
permutation of S w.r.t. the LockId order.

  *Proof.* By `Finset.toList`'s permutation property plus
  `List.qsort`'s sortedness theorem on `LockId.le_total`. □

**Definition 2.1.8** (Two-phase locking). For each kernel
transition τ:
1. Compute `lockSet τ args`.
2. Sort the set by `LockId` ascending.
3. For each `(l, mode)` in order: acquire l in mode (read or write).
4. Execute the transition body, reading/writing only the locked
   objects.
5. Release all locks in reverse order.

**Theorem 2.1.9** (Deadlock-freedom under hierarchical acquire).
Under Definition 2.1.8's discipline, no execution of any set of
kernel transitions on any set of cores can deadlock.

  *Proof.* By induction on the LockId total order. Suppose two
  cores c₁ and c₂ are blocked. Each is waiting on some lock l
  while holding a strictly smaller set of locks (in LockId
  order). Let l₁ be the smallest lock c₁ holds, l₂ be the
  smallest lock c₂ holds. WLOG l₁ ≤ l₂.  By Def 2.1.8, c₁ holds
  l₁ and is waiting for a lock l₁' ≥ l₁. Similarly c₂ holds l₂
  ≥ l₁ and is waiting for l₂' ≥ l₂. For c₁ to be waiting on a
  lock c₂ holds, c₁'s wait target = some lock in c₂'s held set.
  But every lock in c₂'s held set is ≥ l₂ ≥ l₁. By Def 2.1.6's
  acquire-in-ascending-order discipline, c₁ would have acquired
  any lock < l₂ before reaching its current wait. So c₁'s wait
  target ≥ l₂. Symmetric argument: c₂'s wait target ≥ l₁. But
  c₁ holds l₁ and c₂ holds l₂. So c₂'s wait target = l₁ ⇒ c₂'s
  wait target < l₂ — contradiction with the previous bound.
  Therefore no such deadlock state exists. □

**Theorem 2.1.10** (Serializability). Under Definition 2.1.8,
every interleaved execution of kernel transitions is equivalent
(in observable state) to some serial execution.

  *Proof sketch.* By the **two-phase locking theorem** (Bernstein
  et al.). Two-phase locking with hierarchical acquire gives
  strict-2PL, which is conflict-serializable. The Lean
  proof reduces to: for any two transitions τ₁, τ₂ whose lock-sets
  intersect non-trivially, exactly one is "ahead" of the other
  in conflict order (the one that holds the conflicting lock
  first). Compose into a topological sort of all conflicting
  transitions. The resulting order is a valid serial execution
  with the same final state. □

**Corollary 2.1.11** (Single-core proof preservation). Every
existing single-core kernel-transition theorem remains valid for
SMP under Definition 2.1.8, *provided* the theorem is stated
relative to the post-acquire pre-release state of the transition
(i.e., the state observed under all locks in the lock-set held in
the correct modes).

This is the verification-cost lever: existing single-core proofs
are reused, with the precondition strengthened to "lock-set is
held in the declared modes" instead of "BKL is held" (which would
have been free under BKL).

### 2.2 Verified lock primitives

The seL4 project historically *assumed* its lock primitives;
WS-SM **proves** them. This is a substantial extension to the
verification surface but the user-mandated quality target.

#### 2.2.1 Abstract memory model

We define an abstract operational semantics of ARMv8.1-A LSE
atomic operations in `Concurrency/MemoryModel.lean`:

    inductive MemoryOrder where
      | relaxed
      | acquire
      | release
      | acqRel    -- "release+acquire"
      | seqCst
      deriving DecidableEq, Repr

    /-- A trace of memory events. Each event is either a Read or
        Write on a specific atomic location, with a memory order
        and the observed/published value. -/
    structure MemoryEvent where
      core    : CoreId
      loc     : AtomicLocation
      isWrite : Bool
      order   : MemoryOrder
      value   : Nat
      seqNum  : Nat   -- per-core sequencing

    structure MemoryTrace where
      events : List MemoryEvent

The **synchronization edge** is defined: a Release-store w on
location L on core c₁ synchronizes-with an Acquire-load r on the
same L on core c₂ iff r observes w's value (per ARM ARM B2.3.7).

**Theorem 2.2.1.1** (Happens-before). The synchronization edge
combined with per-core sequencing defines a partial order
`hb : MemoryEvent → MemoryEvent → Prop` such that:
- All events on the same core are totally ordered by their seqNum.
- Synchronization edges are happens-before.
- Transitive closure of the above defines a partial order.

  *Proof.* By the standard C++11/Rust memory-model construction
  (Boehm, Adve), specialized to ARMv8.1-A LSE per ARM ARM K11.
  Tracked in `Concurrency/MemoryModel.lean::happens_before_partial_order`. □

#### 2.2.2 TicketLock verification

    structure TicketLock where
      nextTicket : AtomicU64
      serving    : AtomicU64
      deriving Inhabited

    /-- TicketLock operational state. Logical view of the physical
        AtomicU64 pair, plus the multiset of currently waiting
        cores' captured tickets. -/
    structure TicketLockState where
      nextTicket  : Nat
      serving     : Nat
      pending     : List (CoreId × Nat)  -- (core, captured ticket)
      held        : Option (CoreId × Nat)  -- (current holder, its ticket)

    /-- Well-formedness invariant. -/
    def TicketLockState.wf (s : TicketLockState) : Prop :=
      s.serving ≤ s.nextTicket ∧
      (∀ (c, t) ∈ s.pending, s.serving < t ∧ t < s.nextTicket) ∧
      (∀ holder ∈ s.held, holder.snd = s.serving) ∧
      s.pending.map Prod.snd |>.Nodup

**Theorem 2.2.2.1** (Ticket-Lock mutex). For any reachable
TicketLockState s,

    s.wf → ∀ c₁ c₂ : CoreId, s.held = some (c₁, _) → s.held = some (c₂, _) → c₁ = c₂

  *Proof.* `Option` has at most one inhabitant; the `some` case
  forces the holder triple to be unique by structural equality. □

**Theorem 2.2.2.2** (TicketLock FIFO). If c₁ captures ticket t₁
at memory-trace time τ₁ < τ₂ = c₂'s capture of t₂, then t₁ < t₂.

  *Proof.* `fetch_add` on `nextTicket` is a total order across
  cores (Theorem 2.2.1.1's happens-before plus the atomic
  read-modify-write semantics). The capture at τ₁ reads value v
  and writes v+1; the capture at τ₂ reads v+1 (or later) and
  writes v+2 (or later). Therefore t₁ < t₂. □

**Theorem 2.2.2.3** (TicketLock bounded wait). For coreCount cores,

    WCRT(TicketLock.acquire) ≤ (coreCount − 1) × WCRT(criticalSection)

provided every critical section has bounded WCRT.

  *Proof.* By the standard ticket-lock analysis: at most
  (coreCount − 1) other cores can have outstanding tickets
  smaller than mine; each must complete its critical section
  (release `serving`) before mine starts. □

**Theorem 2.2.2.4** (TicketLock release-acquire). If c₁ releases
the TicketLock at trace time τ₁ (corresponding to c₁'s
`serving.fetch_add(1, Release)`) and c₂'s spin-loop
`serving.load(Acquire)` at trace time τ₂ > τ₁ reads c₁'s
released value, then every memory event sequenced-before τ₁ on
c₁ happens-before every event sequenced-after τ₂ on c₂.

  *Proof.* Release-store on `serving` at τ₁ synchronizes-with the
  Acquire-load at τ₂ that observes its value (Theorem 2.2.1.1's
  synchronizes-with relation). By transitive closure of
  happens-before, all c₁ pre-release events precede all c₂
  post-acquire events. □

#### 2.2.3 RwLock verification

The RwLock model supports concurrent readers OR a single writer.

    structure RwLock where
      state : AtomicU64   -- bit 63 = writer-held; bits 0..62 = reader count
      deriving Inhabited

    structure RwLockState where
      writerHeld : Option CoreId
      readers    : List CoreId       -- multiset of read holders
      waiters    : List (CoreId × AccessMode)  -- FIFO queue

    /-- Well-formedness. -/
    def RwLockState.wf (s : RwLockState) : Prop :=
      -- Mutex of writer with everything else
      (s.writerHeld.isSome → s.readers = []) ∧
      -- Readers don't double-acquire (we forbid recursive RW for v1.0.0)
      s.readers.Nodup ∧
      -- Waiter queue is FIFO and disjoint from holders
      s.waiters.map Prod.fst |>.Nodup ∧
      ∀ (c, _) ∈ s.waiters, c ∉ s.readers ∧ s.writerHeld ≠ some c

**Theorem 2.2.3.1** (RwLock writer-readers exclusion). For any
reachable RwLockState s satisfying wf,

    s.writerHeld = some _ → s.readers = []

  *Proof.* By wf's first conjunct. The acquire primitive's
  transition rule (in `Concurrency/RwLock.lean::acquireWrite`)
  preserves the invariant: writer acquire blocks until both
  `writerHeld = none` AND `readers = []`. □

**Theorem 2.2.3.2** (RwLock reader-multiplicity). Multiple
distinct readers may hold the lock concurrently:

    ∃ s, s.readers.length ≥ 2 ∧ s.wf

  *Proof.* By construction: start with `unheld`, two distinct
  `acquireRead` calls succeed without blocking. □

**Theorem 2.2.3.3** (RwLock FIFO admission). If c₁ is queued for
mode m₁ at trace time τ₁ < τ₂ = c₂'s queueing for mode m₂, then
c₁ becomes a holder before c₂ does.

  *Proof.* The waiter queue is FIFO. Releases pop from the head;
  if the head wants Write, it acquires alone; if Read, it
  acquires together with all subsequent contiguous Read waiters
  (writer-batching is acceptable since multiple readers share).
  Therefore the head waiter (c₁) acquires first. □

**Theorem 2.2.3.4** (RwLock bounded wait). For coreCount cores,

    WCRT(RwLock.acquireRead)  ≤ (coreCount − 1) × WCRT(criticalSection)
    WCRT(RwLock.acquireWrite) ≤ (coreCount − 1) × WCRT(criticalSection)

  *Proof.* Same as Theorem 2.2.2.3 modulo the reader-batching
  shortcut (which can only reduce wait time). □

**Theorem 2.2.3.5** (RwLock release-acquire pairing). Same
structure as Theorem 2.2.2.4 for both modes. □

#### 2.2.4 Lock-primitive refinement (Lean ↔ Rust)

The Rust implementation must implement the Lean operational
specification. We prove this by:

    /-- Operational simulation between the Lean RwLockState and a
        sequence of Rust atomic-operation effects. -/
    def rwLockSimulation
        (leanTransitions : List RwLockOp)
        (rustEffects : MemoryTrace) : Prop :=
      ∃ φ : RwLockState → MemoryTrace → Prop,
        φ RwLockState.unheld {events := []} ∧
        ∀ s op s', applyOp op s = s' → φ s τ → φ s' (τ ++ rustEffectsFor op)

    theorem rust_rwLock_refines_lean_rwLock :
        ∀ (impl : RwLockImpl), implCorrect impl →
        ∃ φ, rwLockSimulation _ _

The refinement proof is the seam between the Lean spec and the
Rust implementation. The Rust code is reviewed against the
specification (manual review + cargo tests); the Lean side carries
the abstract proofs.

### 2.3 Per-core state encoding (path-a Vector replacement)

**Definition 2.3.1** (Platform-parameterized core count).

    /-- PlatformBinding extension. The coreCount is a typeclass
        field so multi-platform builds can supply different counts
        without altering the kernel proof surface. -/
    class PlatformBinding where
      ...                                      -- existing fields
      coreCount     : Nat
      coreCountPos  : coreCount > 0
      bootCoreId    : Fin coreCount
      sharingDomain : SharingDomain             -- §2.4

    /-- RPi5 platform: 4 cores, boot core 0, inner-shareable. -/
    instance rpi5PlatformBinding : PlatformBinding where
      ...
      coreCount      := 4
      coreCountPos   := by decide
      bootCoreId     := ⟨0, by decide⟩
      sharingDomain  := .inner

    abbrev CoreId : Type := Fin PlatformBinding.coreCount

**Definition 2.3.2** (Per-core SchedulerState — path-a). The
singular fields are **replaced** (not augmented) with Vector
fields. No `currentOnBootCore` compat shim:

    structure SchedulerState where
      current             : Vector (Option ThreadId) PlatformBinding.coreCount
      runQueue            : Vector RunQueue PlatformBinding.coreCount
      replenishQueue      : Vector ReplenishQueue PlatformBinding.coreCount
      activeDomain        : Vector DomainId PlatformBinding.coreCount
      domainTimeRemaining : Vector Nat PlatformBinding.coreCount
      domainScheduleIndex : Vector Nat PlatformBinding.coreCount
      lastTimeoutErrors   : Vector (List (ThreadId × KernelError)) PlatformBinding.coreCount
      -- System-wide (unchanged)
      domainSchedule         : List DomainScheduleEntry := []
      configDefaultTimeSlice : Nat := 5

    namespace SchedulerState
      /-- Direct per-core accessors. -/
      def currentOnCore (s : SchedulerState) (c : CoreId) : Option ThreadId :=
        s.current.get c
      def runQueueOnCore (s : SchedulerState) (c : CoreId) : RunQueue :=
        s.runQueue.get c
      -- ... and so on for every per-core field
    end SchedulerState

Path-a means every existing theorem referencing `.current`,
`.runQueue`, etc., is rewritten to take a `c : CoreId` parameter
or to fix a specific core (typically `bootCoreId` for boot
properties). The migration touches ~110 theorems across ~60
files (§6 impact matrix).

**Theorem 2.3.3** (Per-core extensionality).

    ∀ s₁ s₂ : SchedulerState,
      (∀ c : CoreId, s₁.currentOnCore c = s₂.currentOnCore c) →
      (∀ c : CoreId, s₁.runQueueOnCore c = s₂.runQueueOnCore c) →
      ...                       -- all per-core field accessors
      s₁.domainSchedule = s₂.domainSchedule →
      s₁.configDefaultTimeSlice = s₂.configDefaultTimeSlice →
      s₁ = s₂

  *Proof.* Vector extensionality via `Vector.ext` applied
  per-field; record-extensionality across the whole struct. □

### 2.4 Sharing domain (cross-cluster parameterization)

**Definition 2.4.1**.

    inductive SharingDomain where
      | inner    -- Inner-shareable (single cluster, e.g., BCM2712)
      | outer    -- Outer-shareable (multi-cluster, e.g., big.LITTLE)
      deriving DecidableEq, Repr

The `BarrierKind` and TLBI variants threading is parameterized:

    def dsbForSharing (d : SharingDomain) : BarrierKind :=
      match d with
      | .inner => .dsbIsh
      | .outer => .dsbOsh

    def tlbiVaeForSharing (d : SharingDomain) (asid : ASID) (va : VAddr) : BarrierKind × TlbInvalidation :=
      (dsbForSharing d, .vae1 asid va)

All kernel TLB operations route through `tlbFlushByPage` /
`tlbFlushByASID`, which thread `PlatformBinding.sharingDomain`
through to the HAL. The single-cluster (Inner) and multi-cluster
(Outer) paths are then both verified, but RPi5 uses Inner.

### 2.5 IPI / SGI model

**Definition 2.5.1** (SGI INTID allocation).

    inductive SgiKind where
      | reschedule         -- INTID 0
      | tlbShootdownReq    -- INTID 1
      | tlbShootdownAck    -- INTID 2
      | cacheBroadcast     -- INTID 3
      | haltAll            -- INTID 4
      deriving DecidableEq, Repr

    def SgiKind.toIntid : SgiKind → Fin 16 := ...

The kernel reserves 5 of the 16 SGI INTIDs. The remaining 11 are
available for application-layer use via a future capability
operation (post-1.0).

**Definition 2.5.2** (Pending SGI queue).

    structure PendingSgi where
      sender  : CoreId
      kind    : SgiKind
      payload : Option Nat
      deriving Repr

    structure ConcurrencyState where
      perCorePendingSgis : Vector (List PendingSgi) PlatformBinding.coreCount

The `ConcurrencyState` field is added to `SystemState`. Lock for
per-core queues: each core's queue has its own RwLock (level
already covered; the per-core slot's lock is at LockKind.tcb or
a new LockKind.sgiQueue — TBD by SM3 design).

**Theorem 2.5.3** (SGI delivery). If sender c₁ executes
`sendSgi c₂ k payload` while holding the lock-set required for
the operation, then on c₂'s next kernel entry, c₂'s queue
contains the entry.

  *Proof.* Under proper locking (Definition 2.1.8), the append
  is atomic. The next kernel entry on c₂ acquires the same lock
  via its IRQ-handler envelope and reads the updated queue. □

### 2.6 TLB shootdown protocol

**Specification 2.6.1** (Correctness). After a successful TLB
shootdown for (asid, vaddr) initiated by core c₀, no core c ∈
PlatformBinding.allCores has (asid, vaddr) cached in its TLB.

**Protocol 2.6.2** (Acquire-shootdown-release):

```
TlbShootdown(initiator c₀, asid, vaddr):
  1. Required locks: VSpaceRoot(asid).lock (write).
  2. Initialize shootdownAck : Vector Bool coreCount; set shootdownAck[c₀] := true.
  3. For each c ∈ allCores \ {c₀}:
       sendSgi c .tlbShootdownReq (encode asid vaddr)
  4. Initiator's local: tlbi_for_sharing(sharingDomain, asid, vaddr); dsb_for_sharing(...); isb.
  5. Loop with bounded WFE per target c:
       wait until shootdownAck[c] = true
     Each remote SGI handler:
       a. tlbi_for_sharing(sharingDomain, asid, vaddr)
       b. dsb_for_sharing(sharingDomain) ; isb
       c. atomically set shootdownAck[c] := true (lock held throughout SGI handler)
       d. (optional) send back .tlbShootdownAck SGI
       e. eret to interrupted context
  6. Loop terminates when shootdownAck = all true.
  7. Final dsb_for_sharing ; isb.
  8. Release locks.
```

**Theorem 2.6.3** (Protocol correctness). At end of TlbShootdown,
no core has (asid, vaddr) in its TLB.

  *Proof.* Each remote core c executes `tlbi ...is` in step
  5(a) before setting `shootdownAck[c]`. The IS-variant TLBI
  effect on remote PEs is observed by DSB ISH (or DSB OSH for
  outer sharing). The atomic-set on shootdownAck[c] establishes
  a release-acquire edge with the initiator's read. After step
  6, the initiator has observed all completions. The final DSB
  in step 7 ensures the initiator's subsequent memory accesses
  follow the shootdown. □

### 2.7 Information flow under SMP

**Definition 2.7.1** (Per-core observer). An *observer* is a
pair `(c, L)` of (core, security-label) — an attacker thread
running on core `c` with label `L`.

**Definition 2.7.2** (Per-core observable state).

    def ObservableState.onCore (c : CoreId) (L : SecurityLabel) (s : SystemState) : ObservableState :=
      { current      := s.scheduler.currentOnCore c
      , runQueue     := s.scheduler.runQueueOnCore c
      , activeDomain := s.scheduler.activeDomain.get c
      , objects      := { o ∈ s.objects | labelOf o ⊑ L }
      , ...
      }

**Theorem 2.7.3** (Cross-core non-interference). For observers
(c, L), if a transition on a *different* core c' ≠ c does not
mutate any object o with labelOf o ⊑ L AND does not signal a
notification observable by (c, L), then ObservableState.onCore c
L is unchanged across that transition.

  *Proof.* The transition on c' holds a lock-set disjoint from c
  for the part of state that c observes (per locking discipline);
  c-observable state writes only happen with c's locks held,
  which c' does not have. □

**Acceptable covert channel** (documented, not closed):
- `bklContentionTiming` — when core c spins on a contended lock
  it can measure how long another core holds the lock; this is a
  timing side channel observable to any thread on c. Documented
  in `Projection.lean::acceptedCovertChannel_bklContention`;
  mitigation deferred to WS-W (CCA/MPAM partitioning).

### 2.8 Mathematical roadmap summary

| Phase | New axioms / assumptions | New substantive theorems |
|-------|--------------------------|---------------------------|
| SM0 | None | ~12 (CoreId, SgiKind, ArchAssumption) |
| SM1 | None | ~6 (HAL primitives existence) |
| SM2 | ARMv8.1-A LSE memory model (cited, not Lean-axiom) | ~22 (TicketLock + RwLock + refinement) |
| SM3 | None | ~28 (per-object lock fields, lock-set discipline, deadlock-freedom) |
| SM4 | None | ~50 (path-a Vector migration; per-core invariants) |
| SM5 | None | ~30 (per-core scheduler) |
| SM6 | None | ~25 (cross-core IPC) |
| SM7 | None | ~14 (TLB shootdown) |
| SM8 | None | ~18 (per-core NI, BKL channel) |
| SM9 | None | ~5 (closure markers) |
| **Total** | **0 Lean axioms** | **~210 substantive theorems** |

The ARMv8.1-A memory-model "axioms" are external — they are ARM
ARM citations woven through `Concurrency/MemoryModel.lean`'s
docstrings, not Lean `axiom` declarations.

## 3. Detailed finding catalogue

Each finding cites file:line directly verifiable in the audit's
source tree. Acceptance in §5 references these IDs.

### 3.1 SMP-C1 — `bring_up_secondaries` never called

`rust_boot_main` (`boot.rs:27-108`) has 4 phases (UART, MMU,
GIC, timer) ending in `lean_kernel_main(dtb_ptr)`. No Phase 5.
`crate::smp::bring_up_secondaries()` is unreferenced outside
`smp.rs` and a comment in `boot.S:141`. The `smp.rs:55-57`
docstring's "deployments set this `true` via a kernel-command-line
parameter parsed by `boot.rs::rust_boot_main`" is aspiration.

**Closure**: SM0.J + SM1.D — DTB cmdline parser + Phase 5
invocation with SMP-default-on policy.

### 3.2 SMP-C2 — `rust_secondary_main` incomplete

`smp.rs:213-235` body: a `wfe_bounded` loop on `CORE_READY[idx]`
then `loop { wfe }`. Docstring (lines 202-211) claims a 4-step
init sequence (MMU, VBAR, GIC CPU interface, timer) that is not
implemented. Activation today would wake secondaries into MMU-off,
VBAR-zero state.

**Closure**: SM1.C — full secondary init per the docstring.

### 3.3 SMP-C3 — `kernelStateRef` shared without atomicity

`SeLe4n/Platform/FFI.lean:394` declares `kernelStateRef :
IO.Ref SystemState`. Lean's `IO.Ref` is not cross-core atomic.

**Closure**: SM3 — per-object locks replace the single global
`kernelStateRef` view. State decomposes into per-object slices,
each guarded by its own RwLock. The `kernelStateRef` is retained
as the "live state holder" but its writers must acquire all
write-locks in their lock-set, and readers must acquire
appropriate read-locks. The Lean model proves serializability
(Theorem 2.1.10).

### 3.4 SMP-C4 — TLB instructions non-IS

`tlb.rs:34,57,78,100`: emits `tlbi vmalle1`, `vae1`, `aside1`,
`vale1` — all non-IS. Per ARM ARM C6.2.311-316, these invalidate
only the issuing PE's TLB. The trailing `dsb ish` does not
propagate; it waits only for the issuing PE.

**Closure**: SM1.E — add IS-variant primitives;
SM7 — shootdown protocol with explicit ack.

### 3.5 SMP-H1 — No SGI primitive

`gic.rs` lacks `GICD_SGIR` constant and `send_sgi` function.

**Closure**: SM1.G — add `send_sgi`, SGI dispatch, Lean FFI.

### 3.6 SMP-H2 — Missing `singleCoreOperation` ArchAssumption

`Architecture/Assumptions.lean:17-23` has 5 constructors; none is
`singleCoreOperation`, despite `Concurrency/Assumptions.lean:163-176`
referencing this anchor.

**Closure**: SM0.A — add constructor + extend
`assumptionInventory`, `archAssumptionConsumer`, distinctness
theorem.

### 3.7 SMP-H3 — Inventory `Lean.Name` not build-checked

Self-acknowledged in `Concurrency/Assumptions.lean:53-61`.

**Closure**: SM0.C — `Concurrency/Anchors.lean` `@`-references.

### 3.8 SMP-H4 — No lock primitive

`with_interrupts_disabled` (interrupts.rs:101-106) is the sole
atomicity primitive; it does not cross cores.

**Closure**: SM2 — verified TicketLock + RwLock primitives;
SM3 — per-object lock fields + lock-set discipline.

### 3.9 SMP-M1..M7, SMP-L1..L5

Documentation, hygiene, scope items closed via SM0.K..SM0.R
(see §5). Severity-tagged in §1.2; remediation per-item in §5.

## 4. Architectural design choices (recorded decisions)

The 12 decisions in §0 governing this plan. Each cites the open
question, the chosen option, and the rationale.

| # | Decision | Rationale |
|---|----------|-----------|
| 1 | **Per-object fine locks** | Maximum concurrency. Trade: every operation declares its lock-set, sorts by hierarchical order, acquires/releases in 2PL. Deadlock-freedom via Theorem 2.1.9. Significantly more proof work than BKL but unbounded scalability headroom. |
| 2 | **Reader-writer locks** | Read-mostly workloads (capability lookup, object-store read) get parallel reader paths. Adds 4 operation types (acquire/release × read/write) and their invariants per lock. Upgrade/downgrade deferred to v1.x. |
| 3 | **Hierarchical-by-kind order** | LockKind = `Untyped < CNode < TCB < Endpoint < Notification < Reply < SchedContext < VSpaceRoot < Page < ObjStore` (10 levels). Within-kind by ObjId.val. Reflects kernel-operation dependency structure; cleaner proof of deadlock-freedom (Theorem 2.1.9). |
| 4 | **Path-a Vector replacement** | Singular SchedulerState fields replaced with `Vector α coreCount`. No bootCore-shim. Cleaner final state at the cost of ~5000-7000 LoC of theorem rewrites (path-b's mechanical migration is shifted to substantive proof restatements). |
| 5 | **numCores via PlatformBinding** | Future-proof for multi-platform builds. ~40% more proof surface than hardcoded. |
| 6 | **PlatformBinding.sharingDomain** | Inner (RPi5) vs Outer (future multi-cluster). Generic theorems hold under either. |
| 7 | **SMP enabled by default** | SMP is the v1.0.0 headline capability; QEMU `-smp 4` integration test is mandatory on every release. Latent SMP bugs become release blockers (positive constraint on rigor). |
| 8 | **Per-core idle TCBs** | One idle thread per core (priority 0, bound to its core). `chooseThreadOnCore` always succeeds (idle fallback). Standard pattern; cleanest invariants. |
| 9 | **SM0 spread across PRs** | 18+ separate small PRs across v0.32.0..v0.32.x. Reviewer-friendly; longer calendar; care needed for inter-PR state consistency. |
| 10 | **Verified lock primitives** | TicketLock + RwLock formally modelled in Lean against an abstract ARMv8.1-A LSE memory model and proven correct (§2.2). seL4 historically left these as assumptions; WS-SM elevates them to proofs. |
| 11 | **Workstream ID = WS-SM** | Two-letter convention. |
| 12 | **24-30 month timeline** | Single-maintainer cadence; comprehensive scope. v1.0.0 ships when WS-SM completes. |

### 4.1 Rejected alternatives (for the record)

| Option | Why rejected |
|--------|--------------|
| Big Kernel Lock | Lower concurrency ceiling; less future headroom. |
| Per-subsystem locks (5 locks) | Middle ground; less optimal than per-object. |
| Exclusive-only spinlocks | Insufficient for read-mostly workloads. |
| Numerical ObjId acquire order | Less semantically aligned than kind-hierarchical. |
| Path-b additive (bootCore-shim) | Leaves residual single-core flavor in the codebase. |
| Hardcoded numCores | Closes the multi-platform door. |
| OSH-by-default | Penalizes single-cluster (RPi5) performance with no current consumer. |
| SMP off by default | Defeats the v1.0.0 SMP headline. |
| Shared idle thread | Complicates "every core has a runnable thread" invariant. |
| Single big SM0 release | Less reviewer-friendly. |
| Trust lock primitives | Below the user-required verification quality. |

## 5. Phase plan

Sub-task sizing legend: T (Trivial, <50 LoC) — S (Small, 50-200 LoC)
— M (Medium, 200-500 LoC) — L (Large, 500-1500 LoC) — XL (Extra-large,
>1500 LoC).

### Phase SM0 — Foundations & honesty patches (40-50 sub-tasks)

**Goal**: foundational types; documentation drift; small structural
fixes prerequisite to the larger phases. **Cadence**: spread across
~18 separate PRs over v0.32.0..v0.32.x.

| Sub | Description | Files | Theorem / acceptance | Est |
|-----|-------------|-------|----------------------|-----|
| SM0.A | Add `singleCoreOperation` constructor to `ArchAssumption`. | `Architecture/Assumptions.lean` | `ArchAssumption` has 6 cases. | S |
| SM0.B | Extend `assumptionInventory` to 6 entries; extend `archAssumptionConsumer`; update distinctness to C(6,2)=15. | `Architecture/Assumptions.lean` | `architecture_assumptions_index_total_6`; `archAssumptionConsumer_distinct_6`. | S |
| SM0.C | `Concurrency/Anchors.lean` with `@`-references of every inventory `identifier` + `sourceTheorem`. Wire into `Platform.Staged`. | `Concurrency/Anchors.lean`, `Platform/Staged.lean` | Build fails if any name doesn't resolve. | S |
| SM0.D | Inventory NoDup witness. | `Concurrency/Assumptions.lean` | `smpLatentInventory_identifiers_nodup` by `decide`. | T |
| SM0.E | Define platform-parameterized `CoreId := Fin PlatformBinding.coreCount`; `numCores_pos`; helpers. | new `Concurrency/Types.lean` | `coreCountPos`, `allCores_length`, `allCores_nodup`, `bootCoreId_valid`. | M |
| SM0.F | Define `SharingDomain` inductive + decidability. | new `Concurrency/Types.lean` | `SharingDomain.eq_decidable`. | T |
| SM0.G | Extend `PlatformBinding` typeclass: `coreCount`, `coreCountPos`, `bootCoreId`, `sharingDomain` fields. | `Platform/Contract.lean` | Typeclass extended; all platform instances updated (RPi5, Sim). | M |
| SM0.H | Define `SgiKind` + `toIntid` + `toIntid_injective`. | new `Concurrency/Sgi.lean` | 5 constructors; injective by `decide`. | S |
| SM0.I | Define `LockKind` (10-level) + `LockKind.level` + `level_strictMono_kind`. | new `Concurrency/Locks/Kind.lean` | Total order; 10 constructors. | S |
| SM0.J | Repoint `dev_history/` references in production sources. | `boot.S:103`, `Architecture/Assumptions.lean:333`, `CrossSubsystem.lean:3264` | grep `dev_history` in production sources = 0 hits. | T |
| SM0.K | Update `docs/spec/SELE4N_SPEC.md §6.4` from "deferred to WS-V" → "implemented in WS-SM (pre-v1.0.0)". Same in DEVELOPMENT.md, GitBook. | (4 files) | grep "deferred to WS-V" in SMP context = 0 hits. | S |
| SM0.L | Rewrite `dev_history/audits/AUDIT_v0.29.0_DEFERRED.md::DEF-R-HAL-L20`: "RESOLVED at v0.30.10" → "PARTIALLY RESOLVED at v0.30.10 — scaffolding only; full activation in WS-SM". | (1 file) | Disposition row reflects scaffolding-only state. | T |
| SM0.M | Zero `.smp_stacks` at boot. Extend `boot.S` BSS-zero loop. | `boot.S` | Boot trace + cargo test `secondary_stacks_zeroed_at_boot`. | S |
| SM0.N | Set `TPIDR_EL1` in `secondary_entry` to per-CPU base. Add `__per_cpu_data_base` linker symbol + `static PER_CPU_DATA: [PerCpuData; coreCount]` skeleton. | `boot.S`, `smp.rs`, `link.ld` | TPIDR_EL1 readable from `rust_secondary_main`. | M |
| SM0.O | `MAX_SECONDARY_CORES = coreCount - 1` parameterization in Rust. | `smp.rs` | Test pins constant. | S |
| SM0.P | Update CLAUDE.md/AGENTS.md to record WS-SM as the active workstream after WS-RC closure. | `CLAUDE.md`, `AGENTS.md` | Workstream context updated; byte-identical mirror. | S |
| SM0.Q | Retarget WS-RC R2..R6 closing-version from v1.0.0 to v0.31.last in `docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md`. | `docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md` | Plan reflects v0.31.last closure. | S |
| SM0.R | Update `docs/codebase_map.json` for new modules. | `docs/codebase_map.json` | Map regenerated. | T |
| SM0.S | New tier-3 surface anchor for the SM0 foundational types. | `tests/SmpFoundationsSuite.lean` | `#check` of every new type. | S |
| SM0.T | New nightly tier `test_tier4_smp_bootcheck.sh` (stub initially — populates over SM1..SM9). | `scripts/test_tier4_smp_bootcheck.sh` | Stub created; tier slot reserved. | T |
| SM0.U | CHANGELOG entry per SM0 PR. | `CHANGELOG.md` | One entry per PR. | T |

**Acceptance gate**: `test_full.sh` green; production-source
`dev_history/` references gone; foundational types compile; doc
references reflect actual SMP status; WS-RC retargeted in its
plan file.

### Phase SM1 — Rust HAL completion (60-80 sub-tasks)

**Goal**: complete HAL primitives — secondaries bring up fully,
SGI primitive exists, TLB has IS variants, command-line parser
works, basic per-CPU register infra is in place.

**Dependencies**: SM0 closure.

#### SM1.A — PSCI completion (5 PRs, 8 sub-tasks)

| Sub | Description | Acceptance | Est |
|-----|-------------|------------|-----|
| SM1.A.1 | `psci::cpu_off()` — HVC `0x8400_0002`. | DEN0022D §5.1.5; round-trip test. | S |
| SM1.A.2 | `psci::affinity_info(mpidr)` — HVC `0xC400_0004`. Returns `AffinityInfoState`. | DEN0022D §5.1.8. | S |
| SM1.A.3 | `psci::system_off()` — HVC `0x84000008`. | DEN0022D §5.1.13. | T |
| SM1.A.4 | `psci::system_reset()` — HVC `0x84000009`. | DEN0022D §5.1.14. | T |
| SM1.A.5 | `psci::migrate_info_type()` — HVC `0x84000006`. | DEN0022D §5.1.7. | T |
| SM1.A.6 | `psci::psci_version()` — HVC `0x84000000`. | DEN0022D §5.1.1. | T |
| SM1.A.7 | Function-id pinning tests for all 6 above. | New module-tests. | S |
| SM1.A.8 | Documentation: PSCI return-code matrix and HVC encoding map in `psci.rs` docstring. | Map present. | T |

#### SM1.B — Per-CPU data + TPIDR_EL1 (3 PRs, 7 sub-tasks)

| Sub | Description | Acceptance | Est |
|-----|-------------|------------|-----|
| SM1.B.1 | Define `PerCpuData` struct (initially empty; populated by later phases). | New `per_cpu.rs`. | T |
| SM1.B.2 | `static PER_CPU_DATA: [PerCpuData; coreCount]` in BSS. | Static array declared; linker resolves. | S |
| SM1.B.3 | `pub fn current_per_cpu() -> &'static PerCpuData` — reads TPIDR_EL1, returns reference. | Inline `mrs tpidr_el1`. | S |
| SM1.B.4 | `pub fn current_core_id_from_tpidr() -> CoreId` — preferred over MPIDR for hot paths. | Test on host stub. | T |
| SM1.B.5 | Lean FFI: `@[extern "ffi_current_core_id"] opaque currentCoreIdFfi : BaseIO Nat`. | Lean wrapper. | T |
| SM1.B.6 | Per-CPU data invariants: `PER_CPU_DATA[i].coreId = i`. | Compile-time assert. | S |
| SM1.B.7 | Tests: `test_per_cpu_data_layout`. | 4+ tests. | S |

#### SM1.C — Secondary core full init (6 PRs, 12 sub-tasks)

| Sub | Description | Acceptance | Est |
|-----|-------------|------------|-----|
| SM1.C.1 | Extract `mmu::init_mmu_secondary(core_id)` from primary's `init_mmu`. | Test: secondary's SCTLR_EL1 matches canonical. | M |
| SM1.C.2 | Extract `vectors::write_vbar_el1_secondary()`. | Refactor; primary uses helper too. | T |
| SM1.C.3 | `gic::init_cpu_interface_secondary(core_id)`. Per-core SGI/PPI enable register write. | Test: secondary's GICC_CTLR enabled. | S |
| SM1.C.4 | `timer::init_timer_secondary(tick_hz)`. CNTKCTL_EL1 + CNTV_TVAL_EL0 per-core. | Test: secondary's CNTV_CTL_EL0 enabled. | S |
| SM1.C.5 | Rewrite `rust_secondary_main` body: 5-step init (MMU, VBAR, GIC CPU iface, timer, set CORE_READY) then enter `lean_secondary_kernel_main(core_id)`. | Body matches docstring. | M |
| SM1.C.6 | Lean side: `@[export] def secondaryKernelMain (coreId : UInt64) : BaseIO Unit`. Initially enters per-core idle loop. | FFI symbol linkable. | M |
| SM1.C.7 | Per-core stack: linker reservation already exists in link.ld; SM1.C.5 uses `__smp_secondary_stack_top` minus offset. | Existing infrastructure; verify usage. | T |
| SM1.C.8 | Per-core MMU page-table reuse: secondaries share kernel PT (TTBR1) and have a per-process TTBR0 (initially the boot process). | Documented; no per-core PT yet. | T |
| SM1.C.9 | SCTLR_EL1 per-core bitmap application. | `init_mmu_secondary` calls existing helper. | T |
| SM1.C.10 | Per-core exception vector — same vector base on every core (VBAR_EL1 is banked). | Documented. | T |
| SM1.C.11 | SError handler enabled on every secondary. | Tested. | S |
| SM1.C.12 | Tests: full secondary-init host stubs. | 6+ unit tests. | M |

#### SM1.D — DTB cmdline + Phase 5 (3 PRs, 6 sub-tasks)

| Sub | Description | Acceptance | Est |
|-----|-------------|------------|-----|
| SM1.D.1 | `sele4n-hal/src/cmdline.rs`: DTB `/chosen/bootargs` parser. Supports key=value, flag-only, quoted strings. Returns `CmdlineConfig { smp_enabled: bool, smp_max_cores: usize, ... }`. | Robust to malformed input; 10+ unit tests. | M |
| SM1.D.2 | Phase 5 in `boot.rs::rust_boot_main`: parse cmdline, set `SMP_ENABLED`, call `bring_up_secondaries()`. | Boot trace shows Phase 5; test host stub. | S |
| SM1.D.3 | **Default behavior: SMP enabled** unless `smp_enabled=false` in cmdline. | Test: empty cmdline → `SMP_ENABLED = true`. | T |
| SM1.D.4 | Ordering: BKL... wait, no BKL. Initialization of all per-object locks (in their objects) is implicit (`Default`). Verify static initialization happens before Phase 5. | Compile-time `const` initializers. | M |
| SM1.D.5 | Ordering: `init_per_cpu_data()` runs before `bring_up_secondaries`. | Test: per-CPU data populated. | S |
| SM1.D.6 | `smp_max_cores` cmdline option for testing with fewer than `coreCount` cores. | Parsed and respected. | S |

#### SM1.E — IS-variant TLB instructions (3 PRs, 5 sub-tasks)

| Sub | Description | Acceptance | Est |
|-----|-------------|------------|-----|
| SM1.E.1 | Add `tlb::tlbi_vmalle1is`, `tlbi_vae1is`, `tlbi_aside1is`, `tlbi_vale1is`. | 4 new functions; per-fn unit tests. | S |
| SM1.E.2 | Add `tlb::tlbi_vmalle1os`, `tlbi_vae1os`, `tlbi_aside1os`, `tlbi_vale1os` (outer-shareable variants). | Future cross-cluster prep. | S |
| SM1.E.3 | `tlb::tlbi_for_sharing(d, op, args)` dispatcher: routes to IS or OS variant by SharingDomain. | Routing test. | M |
| SM1.E.4 | Lean FFI: `@[extern "ffi_tlbi_is"] opaque tlbiIs : TlbOp → BaseIO Unit` (and analogues). | FFI compiles. | S |
| SM1.E.5 | Migrate kernel-side TLB callers to use the sharing-domain-routed variant. | grep `tlbi_vae1` (non-IS) outside HAL test code = 0 hits in callers. | M |

#### SM1.F — SGI primitive (4 PRs, 8 sub-tasks)

| Sub | Description | Acceptance | Est |
|-----|-------------|------------|-----|
| SM1.F.1 | `gic::GICD_SGIR` = GICD_BASE + 0xF00. | Constant; cited GIC-400 TRM §4.3.13. | T |
| SM1.F.2 | `gic::send_sgi(target_mask, intid)`: writes `(0x0 << 24) \| (target_mask << 16) \| (intid & 0xF)`. | Encoding test. | S |
| SM1.F.3 | `gic::send_sgi_to_self(intid)` — TargetListFilter=10. | Test. | T |
| SM1.F.4 | `gic::send_sgi_to_all_but_self(intid)` — TargetListFilter=01. | Test. | T |
| SM1.F.5 | SGI handler dispatch: explicit SGI-range (INTID 0..15) branch with per-SGI handler table. Registers per `SgiKind`. | Dispatch test for each `SgiKind`. | M |
| SM1.F.6 | Lean FFI: `@[extern "ffi_send_sgi_to_core"]`, `ffi_send_sgi_to_self`, `ffi_send_sgi_to_all_but_self`. | FFI compiles. | S |
| SM1.F.7 | SGI handler test stub: simulated SGI delivery on host. | 6+ tests. | M |
| SM1.F.8 | GICD_SGIR write ordering: SGI write must happen with DSB before to ensure prior writes are visible to the target. | Documented; test. | S |

#### SM1.G — Cross-core kprintln synchronization (2 PRs, 4 sub-tasks)

| Sub | Description | Acceptance | Est |
|-----|-------------|------------|-----|
| SM1.G.1 | Audit `UartLock::with` in `uart.rs`. Replace with `TicketLock` from SM2.B if needed. | Lock semantics audited; either reused or replaced. | M |
| SM1.G.2 | Per-core boot banner. | QEMU SMP shows 4 banner lines. | T |
| SM1.G.3 | Per-core kprintln stress test: 4 cores × 1M kprintln; no torn output. | Stress test passes. | M |
| SM1.G.4 | `kprintln_core!` macro that prefixes with core ID. | Macro defined; used in select call sites. | S |

#### SM1.H — QEMU SMP integration (2 PRs, 5 sub-tasks)

| Sub | Description | Acceptance | Est |
|-----|-------------|------------|-----|
| SM1.H.1 | Replace stub `test_qemu_smp_bringup.sh` with full implementation. | QEMU `-smp 4 -machine virt,secure=on` boots; UART log shows 4 cores; cross-core SGI test passes. | L |
| SM1.H.2 | Wire `test_qemu_smp_bringup.sh` into nightly tier. | Tier-4 includes QEMU SMP. | S |
| SM1.H.3 | Add `test_qemu_smp_minimal.sh` for 1-core-secondary (tests bring-up loop without full 4 cores). | Reduced test variant. | M |
| SM1.H.4 | UART log capture + per-core banner verification. | Log shows 4 banners in any order. | S |
| SM1.H.5 | SGI round-trip test: core 0 sends SGI to core 1, 1 responds, 0 receives ack. | Cross-core SGI proven by trace. | M |

#### SM1.I — Miscellaneous HAL improvements (3 PRs, 6 sub-tasks)

| Sub | Description | Acceptance | Est |
|-----|-------------|------------|-----|
| SM1.I.1 | Per-core IRQ handler entry: `trap.rs::handle_irq_perCore`. | Reads core ID, dispatches per-core. | M |
| SM1.I.2 | Per-core IRQ priority masking via GICC_PMR per-core. | Already per-CPU-interface; verify. | T |
| SM1.I.3 | Per-core IDLE thread Rust stub (Lean owns the actual idle TCB). | C-callable. | T |
| SM1.I.4 | Per-core exception statistics. | Optional; informational. | S |
| SM1.I.5 | SEV / WFE coordination: SEV broadcasts wakeup to all WFE-parked cores. | Documented in barriers.rs. | T |
| SM1.I.6 | `cargo test -p sele4n-hal --lib smp` extends with cross-core tests where host stubs permit. | New tests. | M |

**SM1 acceptance gate**: cargo tests pass (~50+ new); QEMU
`-smp 4` boots; 4 cores reach kernel; SGI round-trip works; TLB
IS variants in use everywhere.

### Phase SM2 — Verified lock primitives (70-95 sub-tasks)

**Goal**: model TicketLock + RwLock semantics in Lean against an
abstract ARMv8.1-A LSE memory model; prove mutex/FIFO/bounded-wait
properties; show refinement to the Rust implementation.

**Dependencies**: SM0.

This is the most novel and verification-heavy phase. It implements
the user-mandated "verify lock primitives" decision.

#### SM2.A — Memory model (4 PRs, 12 sub-tasks)

| Sub | Description | Acceptance | Est |
|-----|-------------|------------|-----|
| SM2.A.1 | Define `MemoryOrder` inductive (relaxed/acquire/release/acqRel/seqCst). | `Concurrency/MemoryModel.lean`. | S |
| SM2.A.2 | Define `MemoryEvent` structure (core, loc, isWrite, order, value, seqNum). | Same file. | S |
| SM2.A.3 | Define `MemoryTrace := List MemoryEvent`. | Same file. | T |
| SM2.A.4 | Define `synchronizesWith : MemoryEvent → MemoryEvent → Prop`. | Same file. | M |
| SM2.A.5 | Define `happensBefore : MemoryEvent → MemoryEvent → Prop` (transitive closure of per-core seq + synchronizesWith). | Same file. | M |
| SM2.A.6 | `happens_before_partial_order` theorem: hb is irreflexive + transitive + antisymmetric (modulo total ordering across cores). | Theorem. | L |
| SM2.A.7 | `atomicRmw` operational semantics: load-modify-store as a single trace event. | Definition. | M |
| SM2.A.8 | Acquire-load + Release-store pairing lemma. | Theorem. | M |
| SM2.A.9 | ARM ARM K11.2 citation discipline: every assumption explicitly cited in docstring. | Citation map. | S |
| SM2.A.10 | Decidability instances for trace-event equality and ordering. | Instance proofs. | S |
| SM2.A.11 | `MemoryTrace.wellFormed`: per-core seqNums are monotonic; no two events share (core, seqNum). | Definition + proof. | M |
| SM2.A.12 | Tests in `tests/MemoryModelSuite.lean`: small example traces; verify hb computes correctly. | 8+ unit tests. | M |

#### SM2.B — TicketLock Lean spec (5 PRs, 16 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM2.B.1 | `TicketLockState` structure + `Inhabited` instance. | `Concurrency/Locks/TicketLock.lean`. | S |
| SM2.B.2 | `TicketLockState.unheld` constructor. | Definition. | T |
| SM2.B.3 | `wf : TicketLockState → Prop`. | Predicate. | M |
| SM2.B.4 | `wf_decidable`. | Decidable instance. | S |
| SM2.B.5 | `apply : TicketLockOp → TicketLockState → TicketLockState × MemoryTrace`. Operational step relation. | Definition. | L |
| SM2.B.6 | `TicketLock.mutex` theorem. | Theorem (2.2.2.1). | M |
| SM2.B.7 | `TicketLock.fifo` theorem. | Theorem (2.2.2.2). | M |
| SM2.B.8 | `TicketLock.boundedWait` theorem (parameterized by `coreCount`). | Theorem (2.2.2.3). | L |
| SM2.B.9 | `TicketLock.releaseAcquirePairing` theorem. | Theorem (2.2.2.4). | L |
| SM2.B.10 | `TicketLock.wfInvariant` — wf preserved by every apply. | Theorem. | M |
| SM2.B.11 | `TicketLock.deterministic` — no non-determinism in apply. | Theorem. | S |
| SM2.B.12 | `TicketLock.reachability` — every reachable state satisfies wf. | Theorem (corollary). | S |
| SM2.B.13 | Closure-form lemmas: `acquire_preserves_wf`, `release_preserves_wf`. | 2 theorems. | M |
| SM2.B.14 | Rust ticket-lock impl in `rust/sele4n-hal/src/ticket_lock.rs` (per Definition 2.2.2). | Module + 8 tests. | M |
| SM2.B.15 | Refinement bridge `rust_ticketLock_refines_lean_ticketLock`. | Theorem; proof obligation in `Concurrency/Locks/TicketLockRefinement.lean`. | L |
| SM2.B.16 | Tests in `tests/TicketLockSuite.lean`: 12+ scenarios (single-core acquire, multi-core FIFO, contention bounded). | All pass. | M |

#### SM2.C — RwLock Lean spec (6 PRs, 22 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM2.C.1 | `RwLockState` structure (writerHeld + readers + waiters). | `Concurrency/Locks/RwLock.lean`. | S |
| SM2.C.2 | `wf : RwLockState → Prop`. Writer-readers exclusion + reader-nodup + waiter-fifo. | Predicate. | M |
| SM2.C.3 | `RwLockOp` inductive: `acquireRead`, `releaseRead`, `acquireWrite`, `releaseWrite`. | Definition. | T |
| SM2.C.4 | `apply : RwLockOp → CoreId → RwLockState → RwLockState`. | Definition with blocking semantics. | L |
| SM2.C.5 | `RwLock.writerReadersExclusion` (Theorem 2.2.3.1). | Theorem. | M |
| SM2.C.6 | `RwLock.readerMultiplicity` (Theorem 2.2.3.2). | Theorem. | S |
| SM2.C.7 | `RwLock.fifoAdmission` (Theorem 2.2.3.3). | Theorem. | L |
| SM2.C.8 | `RwLock.boundedWaitRead` (Theorem 2.2.3.4 read variant). | Theorem. | L |
| SM2.C.9 | `RwLock.boundedWaitWrite` (Theorem 2.2.3.4 write variant). | Theorem. | L |
| SM2.C.10 | `RwLock.releaseAcquirePairingRead` (Theorem 2.2.3.5 read variant). | Theorem. | L |
| SM2.C.11 | `RwLock.releaseAcquirePairingWrite` (write variant). | Theorem. | L |
| SM2.C.12 | `RwLock.wfInvariant` (wf preserved by every apply). | Theorem. | M |
| SM2.C.13 | Reader-batching: contiguous read-waiters acquire together on writer release. | Theorem + proof. | M |
| SM2.C.14 | Writer-starvation freedom: writers eventually admitted under bounded reader rotation. | Theorem. | L |
| SM2.C.15 | Closure-form lemmas: 4 per-op preservation theorems. | 4 theorems. | M |
| SM2.C.16 | Bit-packed encoding: `state : AtomicU64` with bit 63 = writer-held, bits 0..62 = reader count. | Encoding definition + proofs. | M |
| SM2.C.17 | Encoding/decoding round-trip lemmas: 4. | Theorems. | S |
| SM2.C.18 | Reader-count overflow analysis: max 2^63 readers; unreachable in practice (4 cores). | Documented. | T |
| SM2.C.19 | Rust RwLock impl in `rust/sele4n-hal/src/rw_lock.rs`. | Module + 12 tests. | L |
| SM2.C.20 | Refinement bridge `rust_rwLock_refines_lean_rwLock`. | Theorem. | XL |
| SM2.C.21 | Tests in `tests/RwLockSuite.lean`: 15+ scenarios. | All pass. | L |
| SM2.C.22 | Cross-core RwLock stress test (host): 4 threads × 100k ops alternating read/write. | Passes. | M |

#### SM2.D — FFI bridge + integration (4 PRs, 8 sub-tasks)

| Sub | Description | Acceptance | Est |
|-----|-------------|------------|-----|
| SM2.D.1 | Lean FFI bindings for TicketLock: `@[extern] acquire`, `release`, `peekHolder`. | Lean wrappers compile. | S |
| SM2.D.2 | Lean FFI bindings for RwLock: 4 ops. | Lean wrappers compile. | S |
| SM2.D.3 | RAII `withLock`, `withReadLock`, `withWriteLock` combinators. | Combinators released on panic. | M |
| SM2.D.4 | Lock-state tracing: optional debug instrumentation. | Trace logs lock acquire/release. | S |
| SM2.D.5 | Static linker-time check: every Rust lock-using function has matching Lean spec. | Build-time gate. | M |
| SM2.D.6 | Verified-lock-primitive surface anchor in `tests/SmpSurfaceAnchors.lean`. | `#check` 22 theorems. | S |
| SM2.D.7 | `lockPrimitives` aggregator in `Concurrency/Locks.lean`: index of all 22 lock theorems. | Aggregator + 22-entry size witness. | S |
| SM2.D.8 | Tests verify lock primitives via FFI calls actually serialize. | Cross-core test. | M |

#### SM2.E — Documentation + assertion sites (3 PRs, 7 sub-tasks)

| Sub | Description | Acceptance | Est |
|-----|-------------|------------|-----|
| SM2.E.1 | `docs/spec/SELE4N_SPEC.md` new §10 "Verified Lock Primitives" with formal definitions. | Section present. | M |
| SM2.E.2 | GitBook chapter 17: lock primitive verification walkthrough. | New chapter. | M |
| SM2.E.3 | ARM ARM citation map in `Concurrency/MemoryModel.lean` docstring. | Citation map. | S |
| SM2.E.4 | Decision rationale doc: why Lean models the memory model abstractly rather than as Lean `axiom`s. | Doc. | T |
| SM2.E.5 | Refinement-proof methodology: explained in `Concurrency/Locks/Refinement.lean`. | Doc + 2 example refinements. | S |
| SM2.E.6 | Hardware-discipline limits: documented in `Concurrency/Locks.lean`. | Doc. | T |
| SM2.E.7 | CHANGELOG entries per SM2 PR. | Per-PR. | T |

**SM2 acceptance gate**: TicketLock + RwLock specs proven; Rust
impls refine specs; FFI bridge functional; verified-lock-primitive
surface anchored in tier-3. Zero Lean axioms; only documented ARM
ARM citations as assumptions.

### Phase SM3 — Per-object lock fields + hierarchical order (50-65 sub-tasks)

**Goal**: extend every kernel-object structure with a `lock :
RwLock` field; define the LockKind hierarchy; prove the lock-set
discipline preserves invariants.

**Dependencies**: SM2.

#### SM3.A — Add `lock : RwLock` fields (5 PRs, 11 sub-tasks)

| Sub | Description | Acceptance | Est |
|-----|-------------|------------|-----|
| SM3.A.1 | `ThreadControlBlock` gains `lock : RwLock`. | Structure extended; all 22-field BEq update. | M |
| SM3.A.2 | `Endpoint` gains `lock : RwLock`. | Structure extended. | S |
| SM3.A.3 | `CNode` gains `lock : RwLock`. | Structure extended. | S |
| SM3.A.4 | `Notification` gains `lock : RwLock`. | Structure extended. | S |
| SM3.A.5 | `Reply` gains `lock : RwLock`. | Structure extended. | S |
| SM3.A.6 | `SchedContext` gains `lock : RwLock`. | Structure extended. | S |
| SM3.A.7 | `VSpaceRoot` gains `lock : RwLock`. | Structure extended. | S |
| SM3.A.8 | `Page` (`PageFrame` etc.) gains `lock : RwLock`. | Structure extended. | S |
| SM3.A.9 | `Untyped` regions gain `lock : RwLock`. | Structure extended. | S |
| SM3.A.10 | ObjStore (RobinHood) gains a table-level `lock : RwLock`. | Table-level lock; reads need read-acquire. | M |
| SM3.A.11 | Default-state initialization: every default-constructed object has `lock = RwLock.unheld`. | Theorem `default_objects_locks_unheld`. | S |

#### SM3.B — LockId computation + lock-set extraction (4 PRs, 9 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM3.B.1 | `LockId.fromObject : KernelObject → LockId`. | Definition. | S |
| SM3.B.2 | `LockId.lookup : SystemState → LockId → Option (RwLock × KernelObject)`. | Lookup function. | M |
| SM3.B.3 | `lockSet : KernelTransition → Args → Finset (LockId × AccessMode)`. Per-transition static lock-set declaration. | Definition. | L |
| SM3.B.4 | `lockSet_consistent : ∀ τ args, ∀ l ∈ lockSet τ args, l.kind ∈ permittedKinds τ`. | Theorem. | M |
| SM3.B.5 | `lockAcquireSequence : Finset (LockId × AccessMode) → List (LockId × AccessMode)`. Sorts by `LockId` order. | Definition. | M |
| SM3.B.6 | `lockAcquireSequence_ordered`. | Theorem. | M |
| SM3.B.7 | `lockAcquireSequence_complete`. Every element of input set appears in output. | Theorem. | M |
| SM3.B.8 | `lockAcquireSequence_canonical`. Unique up to permutation. | Theorem (2.1.7). | M |
| SM3.B.9 | Tests in `tests/LockSetSuite.lean`: per-operation lock-set examples. | 20+ tests. | L |

#### SM3.C — Two-phase locking discipline (4 PRs, 10 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM3.C.1 | `withLockSet : Finset (LockId × AccessMode) → ((SystemState → α) → SystemState → α)` combinator. | Definition. | M |
| SM3.C.2 | RAII discipline: acquires in order; releases in reverse on normal exit. | Combinator semantics. | M |
| SM3.C.3 | Panic-safe release: every panic path also releases locks. | Tests. | M |
| SM3.C.4 | `lockSetHeld` predicate: BUT lock-state changes are not in pure model — they're observable behavior. | Predicate; documented. | M |
| SM3.C.5 | `lockSet_acquired_in_order`. | Theorem. | M |
| SM3.C.6 | `lockSet_released_in_reverse`. | Theorem. | M |
| SM3.C.7 | `lockSet_atomic_under_2pl`. | Theorem (extends Theorem 2.1.10). | L |
| SM3.C.8 | `lockSet_invariant_preserved`. | Theorem: for any transition τ whose lock-set is held in the declared modes, the transition's existing single-core invariant proof goes through. | L |
| SM3.C.9 | Migration: every `@[export]` body wraps body in `withLockSet (lockSet τ args)`. | All @[export] bodies wrapped. | L |
| SM3.C.10 | Tests verifying RAII discipline. | 8+ tests. | M |

#### SM3.D — Deadlock-freedom (3 PRs, 7 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM3.D.1 | `noDeadlock` predicate over execution traces. | Definition. | M |
| SM3.D.2 | `LockId.le_total` (Theorem 2.1.7's totality). | Theorem. | S |
| SM3.D.3 | `lockOrder_strict` (irreflexive + transitive). | Theorem. | S |
| SM3.D.4 | `deadlockFreedom_under_2pl_and_ordering` (Theorem 2.1.9). | Major theorem. | XL |
| SM3.D.5 | Wait-graph acyclicity lemma: under 2PL+ordering, the wait-graph is a DAG. | Theorem. | L |
| SM3.D.6 | Bounded-wait corollary: WCRT bound under fine locking. | Corollary. | M |
| SM3.D.7 | Tests demonstrating deadlock-freedom in tricky scenarios (multi-object operations). | 10+ tests. | M |

#### SM3.E — Serializability (3 PRs, 8 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM3.E.1 | `conflictOrder : KernelTransition → KernelTransition → Prop`. | Definition. | M |
| SM3.E.2 | `serialEquivalent` predicate. | Definition. | M |
| SM3.E.3 | `serializability_under_2pl` (Theorem 2.1.10). | Major theorem. | XL |
| SM3.E.4 | `strictly_2pl` predicate proof. | Theorem. | M |
| SM3.E.5 | `commutativeOperations` lemmas: identify operations whose lock-sets don't conflict. | Theorems × ~10. | L |
| SM3.E.6 | `singleCore_proof_preservation` (Corollary 2.1.11). | Major corollary. | L |
| SM3.E.7 | Tests in `tests/SerializabilitySuite.lean`: example interleavings. | 15+ tests. | L |
| SM3.E.8 | Surface anchors. | `#check` of 8 major theorems. | S |

**SM3 acceptance gate**: per-object locks present; lock-set
discipline encoded; deadlock-freedom + serializability proven;
Corollary 2.1.11 establishes single-core proof preservation.

### Phase SM4 — Path-a per-core state replacement (90-115 sub-tasks)

**Goal**: replace singular `SchedulerState` fields with `Vector α
coreCount`. Every theorem touching these fields rewrites.

**Dependencies**: SM0, SM3 (lock fields).

This is the largest phase — ~5000-7000 LoC of theorem rewrites
across 60+ files.

#### SM4.A — Vector + PlatformBinding (3 PRs, 8 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM4.A.1 | Vector helper bootstrap (use `List.Vector` or define local). | `Prelude.lean`. | M |
| SM4.A.2 | Vector helper theorems (`get_set_eq`, `get_set_ne`, `length`). | 6+ theorems. | M |
| SM4.A.3 | PlatformBinding `coreCount` field. | `Platform/Contract.lean`. | S |
| SM4.A.4 | RPi5 instance: `coreCount := 4`. | `Platform/RPi5/Contract.lean`. | T |
| SM4.A.5 | Sim instance(s). | `Platform/Sim/`. | T |
| SM4.A.6 | `CoreId := Fin PlatformBinding.coreCount`. | Abbrev. | T |
| SM4.A.7 | `bootCoreId` typeclass field. | Field. | S |
| SM4.A.8 | `allCores`, `allCores_length`, `allCores_nodup` (using List.finRange). | Definitions + theorems. | S |

#### SM4.B — SchedulerState path-a replacement (5 PRs, 15 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM4.B.1 | `SchedulerState.current : Vector (Option ThreadId) coreCount`. Replaces singular `current`. | Field replaced. | M |
| SM4.B.2 | `SchedulerState.runQueue : Vector RunQueue coreCount`. | Field replaced. | M |
| SM4.B.3 | `SchedulerState.replenishQueue : Vector ReplenishQueue coreCount`. | Field replaced. | M |
| SM4.B.4 | `SchedulerState.activeDomain : Vector DomainId coreCount`. | Field replaced. | S |
| SM4.B.5 | `SchedulerState.domainTimeRemaining : Vector Nat coreCount`. | Field replaced. | S |
| SM4.B.6 | `SchedulerState.domainScheduleIndex : Vector Nat coreCount`. | Field replaced. | S |
| SM4.B.7 | `SchedulerState.lastTimeoutErrors : Vector ... coreCount`. | Field replaced. | S |
| SM4.B.8 | Helpers: `currentOnCore`, `runQueueOnCore`, `replenishQueueOnCore`, ... | 7 def. | M |
| SM4.B.9 | Default-state initializer: every per-core slot has the singleton-core default. | Theorem `default_state_perCoreInitialized`. | M |
| SM4.B.10 | `SchedulerState.ext` per-core extensionality. | Theorem (2.3.3). | M |
| SM4.B.11 | `Repr` instance updated. | Instance. | T |
| SM4.B.12 | `BEq` instance updated. | Instance. | S |
| SM4.B.13 | `Inhabited` instance updated. | Instance. | T |
| SM4.B.14 | All immediate-caller sites in `Model/State.lean`. | Migrations. | M |
| SM4.B.15 | Migration regression test: trace fixture preserved at single-core scenarios. | Tests pass. | M |

#### SM4.C — Scheduler invariants migration (10 PRs, 30 sub-tasks)

Each sub-task migrates an existing single-core scheduler theorem
to per-core. Pattern:

```
-- Pre-SM4 (single-core):
theorem scheduler_X_consistent (s : SystemState) :
    s.scheduler.current = some tid → ... := ...

-- Post-SM4 (per-core):
theorem scheduler_X_consistent (s : SystemState) (c : CoreId) :
    s.scheduler.currentOnCore c = some tid → ... := ...
```

| Sub | Files | Migrations | Est |
|-----|-------|-----------:|-----|
| SM4.C.1 | `Scheduler/Invariant/CurrentThread.lean` | ~12 theorems | L |
| SM4.C.2 | `Scheduler/Invariant/RunQueue.lean` | ~15 theorems | L |
| SM4.C.3 | `Scheduler/Invariant/Domain.lean` | ~10 theorems | L |
| SM4.C.4 | `Scheduler/Invariant/CBS.lean` | ~8 theorems | L |
| SM4.C.5 | `Scheduler/Operations/Core.lean` | ~20 sites | L |
| SM4.C.6 | `Scheduler/Operations/Preservation.lean` | ~30 sites | XL |
| SM4.C.7 | `Scheduler/Operations/Selection.lean` | ~15 sites | L |
| SM4.C.8 | `Scheduler/RunQueue.lean` migrations | ~25 sites | L |
| SM4.C.9 | `Scheduler/PriorityInheritance/*.lean` | ~20 sites | L |
| SM4.C.10 | `Scheduler/SchedContext/*.lean` | ~15 sites | L |
| SM4.C.11 | `Scheduler/Liveness/*.lean` (incl. WCRT) | ~10 sites | M |
| SM4.C.12 | `Scheduler/Domain/*.lean` | ~8 sites | M |
| SM4.C.13 | `Scheduler/CBS/*.lean` | ~10 sites | M |
| SM4.C.14 | `Scheduler/Timer/*.lean` | ~12 sites | M |
| SM4.C.15 | `Scheduler/Suspend/*.lean` | ~8 sites | M |
| SM4.C.16 | `Scheduler/Yield/*.lean` | ~5 sites | S |
| SM4.C.17 | `Scheduler/RoundRobin/*.lean` | ~5 sites | S |
| SM4.C.18 | `Scheduler/PIP/Compute.lean` | ~12 sites | M |
| SM4.C.19 | `Scheduler/PIP/Discipline.lean` | ~10 sites | M |
| SM4.C.20 | `Scheduler/PIP/Liveness.lean` | ~8 sites | M |
| SM4.C.21 | `Scheduler/PIP/BlockingGraph.lean` | ~10 sites | M |
| SM4.C.22 | `Scheduler/Operations/Reschedule.lean` | ~10 sites | M |
| SM4.C.23 | `Scheduler/Operations/Wake.lean` | ~8 sites | M |
| SM4.C.24 | `Scheduler/Operations/Block.lean` | ~6 sites | S |
| SM4.C.25 | `Scheduler/Operations/Donate.lean` | ~10 sites | M |
| SM4.C.26 | `Scheduler/SchedulerState.lean` | ~12 sites | M |
| SM4.C.27 | `Scheduler/EffectivePriority.lean` | ~8 sites | M |
| SM4.C.28 | `Scheduler/EffectiveSchedParams.lean` | ~8 sites | M |
| SM4.C.29 | Aggregate invariant: `schedulerInvariant_perCore`. | New aggregate. | L |
| SM4.C.30 | Cross-core: `schedulerInvariant_perCore_pairwise` (different cores' invariants are independent). | Theorem. | M |

#### SM4.D — IPC / Capability / Lifecycle / Service migrations (8 PRs, 22 sub-tasks)

Same migration pattern for cross-subsystem theorems reading
SchedulerState.

| Sub | Files | Migrations | Est |
|-----|-------|-----------:|-----|
| SM4.D.1 | `IPC/Operations/*.lean` (~12 sites) | 12 sites | L |
| SM4.D.2 | `IPC/Invariant/*.lean` | 8 sites | M |
| SM4.D.3 | `Capability/Operations.lean` | 5 sites | M |
| SM4.D.4 | `Capability/Invariant/*.lean` | 4 sites | M |
| SM4.D.5 | `Lifecycle/Operations.lean` | 3 sites | S |
| SM4.D.6 | `Lifecycle/Invariant/*.lean` | 3 sites | S |
| SM4.D.7 | `Service/Operations.lean` | 2 sites | S |
| SM4.D.8 | `Service/Invariant/*.lean` | 2 sites | S |
| SM4.D.9 | `Architecture/Invariant.lean` | 8 sites | M |
| SM4.D.10 | `Architecture/ExceptionModel.lean` | 4 sites | M |
| SM4.D.11 | `Architecture/InterruptDispatch.lean` | 4 sites | M |
| SM4.D.12 | `InformationFlow/Operations/*.lean` | 10 sites | L |
| SM4.D.13 | `InformationFlow/Projection.lean` | 5 sites | M |
| SM4.D.14 | `InformationFlow/Invariant/*.lean` | 8 sites | M |
| SM4.D.15 | `Model/State.lean` callsites | 15 sites | M |
| SM4.D.16 | `Model/FreezeProofs.lean` | 6 sites | M |
| SM4.D.17 | `Platform/Boot.lean` | 8 sites | M |
| SM4.D.18 | `Platform/FFI.lean` | 4 sites | S |
| SM4.D.19 | `CrossSubsystem.lean` | 12 sites | L |
| SM4.D.20 | `API.lean` | 6 sites | M |
| SM4.D.21 | `Kernel/Architecture/VSpace.lean` | 4 sites | M |
| SM4.D.22 | `Kernel/Architecture/SyscallEntry.lean` | 4 sites | M |

#### SM4.E — Witness retirement / replacement (2 PRs, 5 sub-tasks)

| Sub | Description | Acceptance | Est |
|-----|-------------|------------|-----|
| SM4.E.1 | Retire `bootFromPlatform_singleCore_witness` (existential on `Option ThreadId` is too weak now). | Theorem deleted. | T |
| SM4.E.2 | Add `bootFromPlatform_smp_witness` proving the per-core shape. | New theorem. | M |
| SM4.E.3 | AN12-B inventory entry 7 (`architecture_singleCoreOnly_smpLatent`): `smpDischarge` becomes "implemented in SM4 path-a"; `sourceTheorem` points to `bootFromPlatform_smp_witness`. | Inventory updated. | S |
| SM4.E.4 | AN12-B inventory entry 8 (`bootFromPlatform_currentCore_is_zero_smpLatent`): same treatment. | Inventory updated. | S |
| SM4.E.5 | Aggregator: AN12-B inventory at SM4 close has 0 latent entries. Replace with `smpRetiredInventory` (8 entries, all retired). | New aggregator + size witness. | M |

**SM4 acceptance gate**: `lake build` (256 jobs) green; all
existing tests pass; per-core helpers in use throughout; AN12-B
inventory shows discharged state.

### Phase SM5 — Per-core scheduler (75-95 sub-tasks)

**Goal**: scheduling, time-slicing, CBS, PIP all operate per-core
with cross-core wake via SGI.

**Dependencies**: SM3, SM4.

#### SM5.A — Per-core chooseThread (5 PRs, 8 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM5.A.1 | `chooseThreadOnCore (s : SystemState) (c : CoreId) : Option ThreadId`. Reads `s.scheduler.runQueueOnCore c` (under read-lock on the per-core RunQueue). Returns highest-priority runnable. | `chooseThreadOnCore_selects_highest` | M |
| SM5.A.2 | Lock-set: `{(LockId.runQueue c, .read)}`. Encoded in `lockSet chooseThread args`. | `lockSet_chooseThread_correct` | S |
| SM5.A.3 | Per-core independence: `chooseThreadOnCore c` does not observe `s.scheduler.runQueueOnCore c'` for c' ≠ c. | `chooseThreadOnCore_perCore_independence` | M |
| SM5.A.4 | Idle-fallback completeness: returns `some (idleThreadOnCore c)` when no other runnable thread is on this core. | `chooseThreadOnCore_always_succeeds` | M |
| SM5.A.5 | Migrate the legacy global `chooseThread` to call `chooseThreadOnCore` for the current core (read from TPIDR_EL1). | (refactor) | S |
| SM5.A.6 | Run-queue well-formedness preserved by chooseThread (idempotent read). | `chooseThreadOnCore_preserves_wellFormed` | M |
| SM5.A.7 | Decidability of `chooseThreadOnCore`. | `chooseThreadOnCore_decidable` | T |
| SM5.A.8 | Unit tests in `tests/SmpSchedulerSuite.lean`: 6 chooseThread scenarios. | New tests. | M |

#### SM5.B — Per-core switchToThread (5 PRs, 9 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM5.B.1 | `switchToThreadOnCore (s : SystemState) (c : CoreId) (tid : ThreadId) : Result SystemState`. Sets `currentOnCore c := some tid`; validates runnable. | `switchToThreadOnCore_sets_current` | M |
| SM5.B.2 | Lock-set: `{(LockId.tcb tid, .write), (LockId.runQueue c, .write)}`. | `lockSet_switchToThread_correct` | S |
| SM5.B.3 | Preempt-self-to-runnable: previous current thread returns to run queue on same core. | `switchToThreadOnCore_preempts_previous` | M |
| SM5.B.4 | If target thread is on a different core's run queue, return `.error .threadOnDifferentCore`. | `switchToThreadOnCore_rejects_remote` | M |
| SM5.B.5 | Invariant: `runQueueOnCore_excludes_currentOnCore` — current thread is NOT in its core's run queue. | `runQueueOnCore_excludes_currentOnCore` | M |
| SM5.B.6 | Cross-core protection: lock-set includes target TCB's write-lock, preventing cross-core race. | `switchToThread_lockSet_protects` | M |
| SM5.B.7 | Hardware context-switch FFI: `ffi_switch_to_thread(tid, core_id)` writes TPIDR_EL1's per-core thread pointer. | `ffi_switch_to_thread_correct` | S |
| SM5.B.8 | Decidability and totality of `switchToThreadOnCore`. | `switchToThreadOnCore_total` | S |
| SM5.B.9 | Tests: 8 scenarios covering preempt, idle, remote-reject. | New tests. | M |

#### SM5.C — Cross-core wake via SGI (6 PRs, 12 sub-tasks)

This is the most novel work in SM5.

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM5.C.1 | `enqueueRunnableOnCore (s : SystemState) (c : CoreId) (tid : ThreadId) : SystemState`. Adds tid to c's run queue. Lock-set: `{(LockId.runQueue c, .write), (LockId.tcb tid, .read)}`. | `enqueueRunnableOnCore_wellFormed` | M |
| SM5.C.2 | `wakeThread (s : SystemState) (tid : ThreadId) : SystemState × List PendingSgi`. Determines target core via TCB.cpuAffinity (defaults to bootCoreId if .none). Enqueues; if target ≠ executing core, emits `(target, .reschedule)` SGI. | `wakeThread_emits_sgi_if_remote` | L |
| SM5.C.3 | Lock-set for cross-core wake: `{(LockId.tcb tid, .write), (LockId.runQueue target, .write)}` plus the executing core's RunQueue if target = executing core. | `lockSet_wakeThread_correct` | M |
| SM5.C.4 | The `@[export]` body's SGI emission: SGI write to GICD_SGIR happens with write-locks held; release-ordering on the write-lock release publishes the post-state. | `wakeThread_sgi_release_ordering` | M |
| SM5.C.5 | SGI handler on target core: `handleSgiInterrupt` (under IRQ-entry lock-set) reads `pendingSgis[myCore]` from post-state (release-acquire pairing); drains queue; for `.reschedule`, re-runs `chooseThreadOnCore myCore` and switches. | `handleSgiInterrupt_processes_pending` | L |
| SM5.C.6 | `wakeThread_lossless`: every wakeThread call eventually causes the target thread to be selected by `chooseThreadOnCore target` (modulo higher-priority work). | `wakeThread_lossless` | L |
| SM5.C.7 | TCB.cpuAffinity field added to TCB structure (Option CoreId; default .none). | Structure extension. | S |
| SM5.C.8 | `setThreadCpuAffinity` capability operation — sets affinity for a TCB; requires write-lock on TCB. | New op; `setThreadCpuAffinity_correct`. | M |
| SM5.C.9 | Boot-time affinity: every kernel thread gets default affinity = bootCoreId initially; userspace can change post-boot via syscall. | `boot_threads_default_affinity` | S |
| SM5.C.10 | Cross-core wake invariant: post-wake, target core's run queue contains tid. | `wakeThread_target_runQueue_contains` | M |
| SM5.C.11 | SGI delivery latency bound: `WCRT(sgi_delivery) ≤ WCRT(critical_section)` (one full lock-set hold by target). | `sgi_delivery_bounded` | M |
| SM5.C.12 | Tests: cross-core wake round-trip; affinity respected; cross-core preempt observed. | 10+ tests. | L |

#### SM5.D — Per-core timer tick (4 PRs, 10 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM5.D.1 | Each core has its own CNTV (ARM Generic Timer) firing locally. Timer ISR on core c calls `handleTimerInterruptPerCore c`. | (HAL + Lean) | M |
| SM5.D.2 | `timerTickOnCore (s : SystemState) (c : CoreId) : SystemState` — decrements `c`'s `domainTimeRemaining`; handles CBS replenishment for threads on `c`; emits preemption if higher-pri thread becomes runnable on `c`. | `timerTickOnCore_advances_per_core` | L |
| SM5.D.3 | Lock-set for timer tick: per-core run queue (write), per-core replenish queue (write), per-core domain state (write), affected TCBs (write). | `lockSet_timerTick_correct` | M |
| SM5.D.4 | Cross-core CBS replenishment: a thread on core c whose budget fires can release a higher-priority thread on a different core; SM5.C handles the cross-core wake. | `cbsReplenish_can_wake_remote_core` | L |
| SM5.D.5 | Per-core time-slice exhaustion → preempt local. | `timerTickOnCore_preempts_local` | M |
| SM5.D.6 | Per-core domain rotation: when `domainTimeRemaining = 0`, advance `domainScheduleIndex` and reset `activeDomain` per-core. | `timerTickOnCore_rotates_domain` | M |
| SM5.D.7 | WCRT-relevant: timer ISR completes within bounded time. | `timerTickOnCore_wcrt_bounded` | M |
| SM5.D.8 | Decidability of timer-tick transition. | `timerTickOnCore_decidable` | S |
| SM5.D.9 | Per-core lastTimeoutErrors field: diagnostic record per core. | `lastTimeoutErrorsOnCore_consistent` | S |
| SM5.D.10 | Tests: per-core timer fires; cross-core CBS wake; per-core domain rotation. | 8+ tests. | L |

#### SM5.E — Per-core idle threads (3 PRs, 6 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM5.E.1 | `idleThreadId (c : CoreId) : ThreadId := ⟨ObjId.ofNat (idleThreadIdBase + c.val), _⟩`. Per-core distinct idle TIDs. | Definition. | S |
| SM5.E.2 | `createIdleThread (c : CoreId) : ThreadControlBlock` — TCB with priority 0, bound to no SchedContext, runnable, cpuAffinity := some c. | Constructor. | S |
| SM5.E.3 | Extend `bootFromPlatform` to install idle TCBs (one per core) and set `currentOnCore c := some (idleThreadId c)`. | `bootFromPlatform_all_cores_have_idle` | M |
| SM5.E.4 | `idleThread_core_locality`: idle TCBs never appear on other cores' run queues. | `idleThread_core_locality` | M |
| SM5.E.5 | `idleThread_priority_zero`: priority 0; never selected if any other thread is runnable on the same core. | `idleThread_priority_zero` | S |
| SM5.E.6 | `chooseThreadOnCore_always_succeeds`: every core always has at least the idle thread as a fallback. | `chooseThreadOnCore_always_succeeds` | M |

#### SM5.F — Per-core PIP (5 PRs, 10 sub-tasks)

PIP propagation extends per-core under fine locks. The R5 work
established the single-core PIP discipline; SM5.F extends.

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM5.F.1 | `computeMaxWaiterPriorityOnCore (c : CoreId)` — per-core variant. Reads `runQueueOnCore c`. | `computeMaxWaiterPriorityOnCore_correct` | M |
| SM5.F.2 | If a PIP boost causes a thread on core c' to become runnable while the chain is on core c, emit `.reschedule` SGI to c' (uses SM5.C wake mechanism). | `pipBoost_cross_core_wake` | L |
| SM5.F.3 | `pipBoost_perCore_consistent` — per-core PIP boost is consistent with cross-subsystem invariants. | `pipBoost_perCore_consistent` | M |
| SM5.F.4 | Donation chain across cores: donor on c₁ donates SC to receiver on c₂; SC's bound core can change. | `donation_perCore_consistent` | L |
| SM5.F.5 | `restoreToReady` (existing) — per-core variant. Lock-set: per-core TCB (write). | `restoreToReadyOnCore_correct` | M |
| SM5.F.6 | `resumeThread` cross-core PIP recomputation under per-core fields. | `resumeThread_perCore_pipBoost_consistent` | L |
| SM5.F.7 | `blockingGraph` per-core view. Each core's blocking graph is its share of the global graph. | `blockingGraphOnCore_consistent` | M |
| SM5.F.8 | `blockingAcyclic_perCore` — per-core acyclicity preserved by all transitions. | `blockingAcyclic_perCore` | M |
| SM5.F.9 | `priorityInheritance_perCore_witness` — the PIP discipline holds per core. | `priorityInheritance_perCore_witness` | M |
| SM5.F.10 | Tests: cross-core PIP scenarios. | 8+ tests. | L |

#### SM5.G — Per-core domain scheduling (3 PRs, 6 sub-tasks)

Decision: per-core active domain. Each core independently advances
its own domain schedule. Shared `domainSchedule` table (config-only);
per-core `domainScheduleIndex` and `domainTimeRemaining`.

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM5.G.1 | `activeDomainOnCore (c : CoreId)`. | Definition. | T |
| SM5.G.2 | `advanceDomainOnCore (c : CoreId)` — rotates that core's `domainScheduleIndex`. | Definition + cyclic theorem. | M |
| SM5.G.3 | `activeDomainOnCore_isInDomainSchedule` per core. | Theorem. | M |
| SM5.G.4 | `chooseThreadOnCore_respects_activeDomain` per core. | Theorem. | M |
| SM5.G.5 | Cross-core: different cores can be in different domains simultaneously. | `domains_independent_across_cores` | S |
| SM5.G.6 | Tests: per-core domain rotation; cross-core domain independence. | 5+ tests. | M |

#### SM5.H — Per-core CBS (4 PRs, 8 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM5.H.1 | `replenishQueueOnCore (c : CoreId)` — per-core CBS replenishment queue. | Definition. | S |
| SM5.H.2 | `replenishOnCore (c : CoreId) (sc : SchedContextId)` — replenishes a SchedContext bound to a thread on core c. | `replenishOnCore_correct` | M |
| SM5.H.3 | `replenishQueueOnCore_wellFormed` — per-core invariant. | Theorem. | M |
| SM5.H.4 | Cross-core SC migration: when a TCB's cpuAffinity changes, its SchedContext's replenish queue migrates to the new core. | `schedContextMigration_consistent` | L |
| SM5.H.5 | `schedContextRunQueueConsistent_perCore` — extension of existing invariant. | Theorem. | M |
| SM5.H.6 | `replenishmentPipelineOrder_perCore` — the AK2-K invariant extended per-core. | Theorem. | M |
| SM5.H.7 | CBS budget accounting per core. | `cbsAccountingOnCore_consistent` | M |
| SM5.H.8 | Tests: cross-core CBS, migration scenarios. | 6+ tests. | L |

#### SM5.I — Per-core invariant suite (5 PRs, 10 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM5.I.1 | `currentOnCore_validThreadIfSome (c)`. | Theorem. | S |
| SM5.I.2 | `runQueueOnCore_wellFormed (c)`. | Theorem. | S |
| SM5.I.3 | `schedContextRunQueueConsistent_perCore`. | Theorem. | M |
| SM5.I.4 | `priorityInheritance_perCore`. | Theorem. | M |
| SM5.I.5 | Composition: `schedulerInvariant_perCore` aggregates the 4 invariants above per core. | Aggregate theorem. | M |
| SM5.I.6 | Cross-core: `schedulerInvariant_perCore_pairwise` — different cores' invariants are independent. | Theorem. | M |
| SM5.I.7 | `schedulerInvariant_smp` — system-wide invariant = ∀ c, schedulerInvariant_perCore c. | Theorem. | M |
| SM5.I.8 | Preservation: every scheduler transition preserves `schedulerInvariant_smp`. | Theorem. | L |
| SM5.I.9 | `crossSubsystemInvariant_smp` extends the existing 12-conjunct with `schedulerInvariant_smp`. | Theorem. | M |
| SM5.I.10 | Tier-3 surface anchors for the per-core invariant suite. | `#check` 10+ theorems. | S |

#### SM5.J — WCRT under fine locks (2 PRs, 5 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM5.J.1 | `WCRT_lockSet (operation) := |lockSet operation| × (coreCount - 1) × WCRT_per_lock`. | Definition. | M |
| SM5.J.2 | `wcrt_bound_rpi5_smp` — extends R5's `wcrt_bound_rpi5` with the lock-set factor. | Theorem. | L |
| SM5.J.3 | Per-operation WCRT bounds: chooseThread, switchToThread, wakeThread, timerTick, IPC. | 5 theorems. | L |
| SM5.J.4 | Liveness theorem: no thread starves under fine-lock SMP. | Theorem. | L |
| SM5.J.5 | Tests: WCRT verification scenarios. | 3+ tests. | M |

#### SM5.K — Tests + fixtures (3 PRs, 6 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM5.K.1 | `tests/SmpSchedulerSuite.lean`: 50+ scenarios. | New file. | XL |
| SM5.K.2 | `tests/SmpTimerSuite.lean`: per-core timer tests. | New file. | M |
| SM5.K.3 | `tests/SmpPipSuite.lean`: cross-core PIP. | New file. | M |
| SM5.K.4 | `tests/fixtures/smp_4core_scheduler.expected`. | New file. | M |
| SM5.K.5 | QEMU `-smp 4` scheduler integration in `test_qemu_smp_scheduler.sh`. | New script. | M |
| SM5.K.6 | Surface anchors for SM5 theorems. | `tests/SmpSurfaceAnchors.lean`. | S |

**SM5 acceptance gate**: 4-thread workload distributed across
4 cores; cross-core preempt works under fine locks; per-core
timer ticks advance per-core domain state; PIP cross-core works;
idle threads per core; WCRT bounded.

### Phase SM6 — Cross-core IPC (60-80 sub-tasks)

**Goal**: endpoint call/send/recv, notifications, reply all work
across cores under per-object fine locks. Each IPC operation
declares its lock-set; cross-core wake routes through SM5.C.

**Dependencies**: SM5.

Lock-set per IPC operation:

| Operation | Lock-set (acquire in `LockId` order) |
|-----------|--------------------------------------|
| `endpointCall` | caller TCB (W), sender's CNode (R for cap lookup), endpoint (W), receiver TCB (W if unblock) |
| `endpointSend`/`endpointSendNonBlocking` | caller TCB (R), endpoint (W) |
| `endpointReceive` | caller TCB (W), endpoint (W) |
| `endpointReplyRecv` | caller TCB (W), reply object (W), endpoint (W) |
| `notificationSignal` | caller TCB (R), notification (W), receiver TCB (W if unblock) |
| `notificationWait` | caller TCB (W), notification (W) |
| `cancelIpcBlocking` | victim TCB (W), associated endpoint or notification (W) |
| `endpointReply` | caller TCB (W), reply object (W), receiver TCB (W) |

#### SM6.A — Endpoint call across cores (4 PRs, 10 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM6.A.1 | Migrate `endpointCall` (existing) to acquire its lock-set before executing. | (refactor) | M |
| SM6.A.2 | `endpointCall_lockSet_correct` — the lock-set declaration matches the read/write set. | Theorem. | M |
| SM6.A.3 | Cross-core call: when receiver wakes (transitions blocked → runnable), wake routes through `wakeThread` which emits SGI if receiver on different core. | `endpointCall_emits_sgi_if_remote_receiver` | L |
| SM6.A.4 | `endpointCall_perCore_blocking`: caller blocks on caller's core; reply unblocks caller via wake. | Theorem. | M |
| SM6.A.5 | Donation chain locking: caller's SC may flow to receiver; lock-set extends to include SC. | `endpointCall_donation_lockSet` | M |
| SM6.A.6 | Reply object allocation: under lock-set, reply object created and bound. | Theorem. | M |
| SM6.A.7 | Information flow: `endpointCall_call_path_NI` (cross-core variant of R1 theorem). | Theorem. | L |
| SM6.A.8 | endpointCallWithCaps (with capability transfer): lock-set extends to include source CNode (R) and destination CNode (W). | `endpointCallWithCaps_lockSet_correct` | L |
| SM6.A.9 | endpointCall_atomic_under_lockSet — single conflict-serializable transition under 2PL. | Theorem. | L |
| SM6.A.10 | Tests: 8+ cross-core call scenarios. | New tests. | L |

#### SM6.B — Notification across cores (3 PRs, 8 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM6.B.1 | Migrate `notificationSignal` to acquire lock-set. | (refactor) | M |
| SM6.B.2 | `notificationSignal_remote_wake`: if waiting thread on different core, emit SGI to that core. | Theorem. | L |
| SM6.B.3 | Multi-waiter discipline: only one waker leaves the queue (binary semaphore); remaining stay blocked. | Theorem (existing inv extended). | M |
| SM6.B.4 | `notificationWait` lock-set + atomicity. | `notificationWait_atomic_under_lockSet` | M |
| SM6.B.5 | `notificationSignal_perCore_consistent` — per-core invariant. | Theorem. | M |
| SM6.B.6 | Binding (notification bound to TCB) — lock-set extension. | Theorem. | M |
| SM6.B.7 | Notification IF: per-core NI extension. | `notificationSignal_perCore_NI` | M |
| SM6.B.8 | Tests: cross-core notification scenarios. | 6+ tests. | L |

#### SM6.C — Reply path across cores (4 PRs, 10 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM6.C.1 | Migrate `endpointReply` to acquire lock-set. | (refactor) | M |
| SM6.C.2 | Cross-core reply: reply wakes caller; caller may be on different core. | `endpointReply_remote_wake` | L |
| SM6.C.3 | Donation chain across cores: SC's bound core can change at reply time. | `donation_perCore_consistent` (extension) | L |
| SM6.C.4 | Reply receive on caller's core after wake: ensures reply payload delivered to right TCB. | `endpointReply_perCore_delivery` | M |
| SM6.C.5 | `endpointReplyRecv` (combined reply + receive) lock-set. | `endpointReplyRecv_lockSet_correct` | M |
| SM6.C.6 | Reply object lifecycle: created on call, consumed on reply. | `replyObject_lifecycle_under_lockSet` | M |
| SM6.C.7 | Reply-replay protection: a reply object can only be consumed once. | Theorem. | M |
| SM6.C.8 | Cross-core reply NI: `endpointReply_perCore_NI`. | Theorem. | M |
| SM6.C.9 | Reply chain length bound (donation chain k > 2). | `replyChain_length_bounded_perCore` (existing extension). | M |
| SM6.C.10 | Tests: 8+ reply scenarios. | New tests. | L |

#### SM6.D — IPC across-core invariant bundle (2 PRs, 6 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM6.D.1 | `ipcInvariantFull_perCore`: 15-conjunct bundle restricted to per-core endpoint/notification views. | `ipcInvariantFull_perCore` | L |
| SM6.D.2 | All 6 per-operation preservation theorems carry through with per-core lock-set discipline. | 6 theorems. | XL |
| SM6.D.3 | `ipcStateQueueMembershipConsistent_perCore`. | Theorem. | M |
| SM6.D.4 | `endpointQueueNoDup_perCore`. | Theorem. | M |
| SM6.D.5 | `queueNextBlockingConsistent_perCore`. | Theorem. | M |
| SM6.D.6 | `queueHeadBlockedConsistent_perCore`. | Theorem. | M |

#### SM6.E — Cancellation across cores (3 PRs, 6 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM6.E.1 | Migrate `cancelIpcBlocking` to lock-set discipline. | (refactor) | M |
| SM6.E.2 | `cancelIpcBlocking_atomic_under_lockSet` — atomic removal under 2PL. | Theorem. | M |
| SM6.E.3 | `cancelDonation` (R5.A) under lock-set discipline. | (refactor) | M |
| SM6.E.4 | `cancelDonation_atomic_under_lockSet`. | Theorem. | M |
| SM6.E.5 | Cross-core cancellation: cancellation on c₁ of a thread on c₂ — lock-set spans cores. | `cancellation_cross_core_correct` | L |
| SM6.E.6 | Tests: cancellation scenarios across cores. | 6+ tests. | M |

#### SM6.F — Tests + fixtures (3 PRs, 6 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM6.F.1 | `tests/SmpIpcSuite.lean`: 30+ cross-core IPC scenarios. | New file. | XL |
| SM6.F.2 | `tests/SmpNotificationSuite.lean`: 15+ scenarios. | New file. | L |
| SM6.F.3 | `tests/SmpCancellationSuite.lean`: 10+ scenarios. | New file. | M |
| SM6.F.4 | `tests/fixtures/smp_ipc_4core.expected`. | New file. | M |
| SM6.F.5 | QEMU `-smp 4` IPC integration in `test_qemu_smp_ipc.sh`. | New script. | M |
| SM6.F.6 | Surface anchors. | `tests/SmpSurfaceAnchors.lean` (extension). | S |

**SM6 acceptance gate**: 2-thread cross-core IPC works; 4-thread
SMP rendezvous test passes; existing IPC invariants hold per-core.

### Phase SM7 — TLB / cache shootdown (40-55 sub-tasks)

**Goal**: page unmaps, ASID retire, retype-with-page-free invalidate
translations on every core. CRITICAL for closing SMP-C4.

**Dependencies**: SM2.A (memory model), SM1.E (IS-variant TLB
ops), SM1.F (SGI primitive), SM3 (lock discipline).

#### SM7.A — Shootdown descriptor + state (3 PRs, 6 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM7.A.1 | `TlbShootdownDescriptor` struct: `(asid : ASID, vaddr : Option VAddr, kind : .vaae \| .aside \| .vmalle)`. | Definition. | M |
| SM7.A.2 | `pendingShootdowns : Vector (List TlbShootdownDescriptor) coreCount`. Per-core queue. | Definition. | M |
| SM7.A.3 | `shootdownAck : Vector Bool coreCount`. Per-core ack flag. | Definition. | S |
| SM7.A.4 | `enqueueShootdown (initiator) (targets) (desc)` — adds desc to each target's queue. | Definition. | M |
| SM7.A.5 | `drainShootdowns (c : CoreId)` — called from SGI handler on c. | Definition. | M |
| SM7.A.6 | Pending queue capacity: bounded by `coreCount × maxPendingPerCore` (= 4 × 16 = 64). Documented. | Constant + invariant. | S |

#### SM7.B — Shootdown protocol (4 PRs, 12 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM7.B.1 | `tlbShootdownLocal (asid) (vaddr)`: this core executes `tlbi_for_sharing vaae1is/vae1is + dsb_for_sharing + isb`. | Definition. | M |
| SM7.B.2 | `tlbShootdownBroadcast (initiator) (targets) (asid) (vaddr)`: enqueue descriptor, send SGI, initiate local shootdown, wait for ack. | Definition. | L |
| SM7.B.3 | SGI handler for `.tlbShootdownReq` (registered in SM1.F): drain queue, execute local TLBI for each, set ack flag, return. | Handler. | L |
| SM7.B.4 | `shootdownAck` synchronization: ack flag is a release-store; initiator reads with acquire-load. | `shootdownAck_release_acquire` | M |
| SM7.B.5 | Initiator wait-loop: bounded WFE on each target's ack flag. | `shootdown_wait_loop_terminates` | M |
| SM7.B.6 | Timeout fallback: if ack doesn't come within bounded WFE rounds, log diagnostic and continue (single-core only; full SMP requires the ack). For v1.0.0, treat timeout as a panic. | `shootdown_timeout_handling` | M |
| SM7.B.7 | Lock-set for shootdown: VSpaceRoot(asid) write-lock (covers the unmap operation). | `lockSet_tlbShootdown_correct` | M |
| SM7.B.8 | `tlbShootdownBroadcast_invalidatesAllCores` (Theorem 2.6.3). | Major theorem. | XL |
| SM7.B.9 | Wire all unmap callers to use Broadcast variant. | (~8 callsites) | M |
| SM7.B.10 | ASID-retire shootdown: when an ASID is freed, broadcast `aside1is`. | Definition + theorem. | M |
| SM7.B.11 | Retype-with-page-free shootdown: when untyped is retyped and pages are freed, broadcast each page's invalidation. | Theorem. | M |
| SM7.B.12 | Cross-cluster path (Outer sharing): same protocol but uses OS variants. Parameterized. | `tlbShootdown_outer_correct` | M |

#### SM7.C — Per-core TLB model (3 PRs, 8 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM7.C.1 | Extend `TlbState` (existing) to `Vector TlbState coreCount`. | Definition. | M |
| SM7.C.2 | `tlbInsertOnCore (c : CoreId) (entry)` — adds entry to c's TLB (modeling HW translation walker). | Definition. | M |
| SM7.C.3 | `tlbInvalidateOnCore (c : CoreId) (asid, vaddr)`. | Definition. | M |
| SM7.C.4 | `tlbInvalidateOnAllCores (asid, vaddr)` — uses shootdown protocol. | Definition. | M |
| SM7.C.5 | `tlbInvalidationConsistent_perCore`: per-core TLB ↔ page table consistency. | Theorem. | L |
| SM7.C.6 | `tlbShootdown_invalidates_perCore` — for each core c, post-shootdown TLB lacks the entry. | Theorem (corollary of 2.6.3). | M |
| SM7.C.7 | `tlbConsistency_cross_subsystem` — cross-subsystem invariant. | Theorem. | M |
| SM7.C.8 | Surface anchors. | `#check` 8 theorems. | S |

#### SM7.D — Cache maintenance broadcast (2 PRs, 4 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM7.D.1 | I-cache invalidation on code modification — use existing `ic_ialluis`. | `cache.rs`, `Architecture/CacheModel.lean` | S |
| SM7.D.2 | D-cache by VA at PoC — system-wide; no broadcast needed (ARM ARM B2.7.5). Documented in `CacheModel.lean`. | Docstring. | T |
| SM7.D.3 | Cross-core DC maintenance for DMA buffers — documented as post-1.0 (no DMA driver in v1.0.0). | Doc. | T |
| SM7.D.4 | Cache-coherency invariant under SMP. | Theorem. | M |

#### SM7.E — Tests (3 PRs, 6 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM7.E.1 | `tests/SmpTlbShootdownSuite.lean`: 15+ scenarios (unmap-then-read-on-remote-core; ASID retire; broadcast timing). | New file. | L |
| SM7.E.2 | QEMU SMP shootdown integration: `test_qemu_smp_shootdown.sh`. | New script. | M |
| SM7.E.3 | Shootdown stress test: 4 cores × concurrent unmaps. | Test. | M |
| SM7.E.4 | Cross-cluster shootdown test (mocked Outer sharing). | Test. | M |
| SM7.E.5 | Surface anchors. | `tests/SmpSurfaceAnchors.lean`. | S |
| SM7.E.6 | Fixture: `smp_tlb_shootdown.expected`. | New fixture. | S |

**SM7 acceptance gate**: unmap-then-reuse a page on different
cores; no stale translation observed on remote cores; theorem
`tlbShootdownBroadcast_invalidatesAllCores` proven. **Closes SMP-C4.**

### Phase SM8 — Information flow under SMP (40-55 sub-tasks)

**Goal**: extend NI proofs to per-core observers; document new
covert channels (lock contention timing); per-core declassification
audit.

**Dependencies**: SM4, SM5.

#### SM8.A — Per-core observable state (3 PRs, 6 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM8.A.1 | `ObservableState.onCore (c) (L) (s)` — per-core projection per Definition 2.7.2. | Definition. | M |
| SM8.A.2 | `onCore_isProjection_of_globalProjection` — refinement composition. | Theorem. | M |
| SM8.A.3 | `onCore_decidable`. | Decidable instance. | S |
| SM8.A.4 | `onCore_perCore_independence`: observers on different cores see independent projections (modulo shared L-observable state). | Theorem. | M |
| SM8.A.5 | `onCore_label_monotone`: higher label ⇒ wider projection. | Theorem. | M |
| SM8.A.6 | Tests in `tests/SmpInformationFlowSuite.lean` (start). | New file. | M |

#### SM8.B — Per-core NI proofs (5 PRs, 14 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM8.B.1 | `nonInterference_perCore`: existing NI proof generalized. | Theorem. | XL |
| SM8.B.2 | `crossCoreNonInterference` (Theorem 2.7.3): transitions on other cores don't change my projection. | Theorem. | XL |
| SM8.B.3 | Per-core NI for each `kernelOperationNi` constructor — there are 32 in the existing model. | 32 theorems. | L |
| SM8.B.4 | NI under per-object lock-set: locks themselves are observable but don't leak L-state. | Theorem. | L |
| SM8.B.5 | `niStepCoverage_perCore` — coverage map updated for per-core. | Theorem. | M |
| SM8.B.6 | `enforcementBoundaryExtended_perCore` — 23 entries (was 22 in V6-L). | Definition + theorem. | M |
| SM8.B.7 | Boundary completeness witness extended. | Theorem. | M |
| SM8.B.8 | `acceptedCovertChannel_lockContention`: lock-contention timing as documented covert channel. | Definition. | M |
| SM8.B.9 | Mitigation note: WS-W (CCA/MPAM) narrows this channel via partition isolation. | Documentation. | S |
| SM8.B.10 | `acceptedCovertChannel_perCoreCount`: total = 5 channels (4 existing + lock contention). | Definition. | T |
| SM8.B.11 | `endpointPolicyRestricted_perCore`. | Theorem. | M |
| SM8.B.12 | Per-core NI bridge to non-interference release. | Theorem. | M |
| SM8.B.13 | Cross-core information flow: a thread on c can only learn about c' via documented channels. | `crossCoreLeakage_bounded` | L |
| SM8.B.14 | Tests in `tests/SmpInformationFlowSuite.lean`: 15+ scenarios. | New tests. | L |

#### SM8.C — Per-core declassification audit (3 PRs, 7 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM8.C.1 | `DeclassificationEvent` extended with `originatingCore : CoreId`. | Structure extension. | M |
| SM8.C.2 | Per-core audit-trail: cross-core declassification chains recorded. | Theorem. | M |
| SM8.C.3 | Audit trail invariant: every declass event has a valid originating core. | Theorem. | S |
| SM8.C.4 | `DeclassificationEvent_perCore_audit`. | Theorem. | M |
| SM8.C.5 | `authorizationBasis_perCore` — extends V6-H. | Theorem. | M |
| SM8.C.6 | Cross-core declassification: rules for declassifying state observed on another core. | Theorem. | M |
| SM8.C.7 | Tests: per-core declass scenarios. | New tests. | M |

#### SM8.D — Information-flow under fine locks (3 PRs, 6 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM8.D.1 | Lock state visibility: lock acquire/release are atomic but their *timing* is observable. | Documented. | M |
| SM8.D.2 | Reader-multiplicity not directly observable: readers don't see each other under RW locks (each thinks it owns shared access). | Theorem. | M |
| SM8.D.3 | Writer-exclusion observable: a thread blocked on a writer can detect another writer's presence. | Documented. | T |
| SM8.D.4 | Bibba-integrity under per-core locks. | Theorem. | M |
| SM8.D.5 | Secure-information-flow witness under fine locks. | Theorem. | M |
| SM8.D.6 | Tests: lock-contention IF scenarios. | 5+ tests. | M |

#### SM8.E — Tests + closure (2 PRs, 3 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM8.E.1 | Surface anchors for SM8 theorems (~18 theorems). | `tests/SmpSurfaceAnchors.lean`. | S |
| SM8.E.2 | Comprehensive IF test fixture: `smp_information_flow.expected`. | New fixture. | M |
| SM8.E.3 | Update `enforcementBoundaryExtended` count witness from 22 → 23+. | Theorem. | T |

**SM8 acceptance gate**: NI proofs go through per-core; lock-
contention channel documented; declassification trail extends
per-core; enforcement boundary extended.

### Phase SM9 — Documentation, tests, version closure (25-35 sub-tasks)

**Goal**: complete v1.0.0 release.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM9.A.1 | Spec §6.4 rewritten for SMP (5 subsections). | `docs/spec/SELE4N_SPEC.md` | L |
| SM9.A.2 | New GitBook chapter 16 (SMP architecture). | `docs/gitbook/16-smp-architecture.md` | L |
| SM9.A.3 | New GitBook chapter 17 (verified lock primitives). | `docs/gitbook/17-verified-lock-primitives.md` | L |
| SM9.A.4 | README + 10 i18n update with SMP capability claim. | (11 files) | M |
| SM9.A.5 | DEVELOPMENT.md + CLAIM_EVIDENCE_INDEX.md updates. | (2 files) | M |
| SM9.A.6 | WORKSTREAM_HISTORY.md WS-SM closure. | (1 file) | L |
| SM9.A.7 | codebase_map.json regeneration. | (1 file) | T |
| SM9.A.8 | website_link_manifest.txt updates. | (1 file) | S |
| SM9.B.1..B.10 | Full SMP test suites (Scheduler, IPC, Capability, TLB, IF, Foundations) — 6 new tests files. | tests/ | XL |
| SM9.B.11 | smp_4core_boot.expected fixture. | tests/fixtures/ | M |
| SM9.B.12 | tier-4 SMP test script. | scripts/ | M |
| SM9.B.13 | tier-5 verification tier (proves all 210 SM theorems land at HEAD). | scripts/ | S |
| SM9.C.1 | Version bump to v1.0.0 across all metric-bearing files (~25 files). | (~25 files) | M |
| SM9.C.2 | CHANGELOG v1.0.0 closure entry. | CHANGELOG.md | M |
| SM9.C.3 | Move WS-RC artefacts to dev_history/. | (file moves) | S |
| SM9.C.4 | Move this plan to dev_history/planning/. | (1 move) | T |
| SM9.C.5 | Tag v1.0.0 (maintainer-cut). | git tag | T |

**SM9 acceptance gate**: v1.0.0 released; all 11 acceptance
criteria from §11 met.

## 6. Cross-subsystem impact matrix

| Subsystem | Files | Existing LoC | New LoC (lock + per-core + SMP) | Migration LoC | Notes |
|-----------|------:|-------------:|---------------------------------:|--------------:|-------|
| Concurrency (new modules) | 0 → 8 | 228 | ~3500 | 0 | TicketLock + RwLock + MemoryModel + LockKind + Anchors + Sgi + Locks + Types |
| Scheduler | 22 | ~7000 | ~2200 | ~2400 | Path-a Vector replacement; per-core invariants; lock-set discipline |
| IPC | 35 | ~12000 | ~1500 | ~1800 | Multi-object lock-set; cross-core wake |
| Capability | 18 | ~5500 | ~600 | ~700 | Per-object locks on CNodes; CDT operations under lock-set |
| Lifecycle | 6 | ~1500 | ~300 | ~200 | Retype under multi-object lock-set |
| Service | 4 | ~1500 | ~150 | ~100 | Registry under lock |
| Architecture | 14 | ~6000 | ~1500 | ~600 | TLB shootdown; IS variants; per-core IRQ |
| InformationFlow | 12 | ~6000 | ~1500 | ~800 | Per-core observer; cross-core NI; BKL channel |
| RobinHood / RadixTree | 6 | ~3500 | ~250 | ~50 | Table-level lock + per-bucket atomicity |
| Platform | 17 | ~5000 | ~1000 | ~300 | PlatformBinding extension; per-core boot data; sharingDomain |
| CrossSubsystem | 1 | 3309 | ~800 | ~400 | Retire singleCore witness; per-core consistency conjunct |
| Model | 5 | ~5500 | ~600 | ~400 | path-a Vector replacement; per-core fields |
| Object types | 7 | ~3500 | ~400 | ~200 | `lock : RwLock` on each object kind |
| **Total** | **155** | **~60,000** | **~14,300** | **~7,950** | |

Total new code: **~22,250 LoC** across **~155 files**.

For scale: WS-AK ran ~14 months delivering ~6,000 LoC of remediation
work; WS-SM at ~3.7× that LoC and at higher conceptual complexity
predicts ~24-30 months.

## 7. Verification strategy

### 7.1 What we prove

| Property | Proof technique | Phase |
|----------|-----------------|-------|
| TicketLock mutex (Thm 2.2.2.1) | Direct from `Option` cardinality | SM2.B |
| TicketLock FIFO (Thm 2.2.2.2) | Atomic-RMW total ordering | SM2.B |
| TicketLock bounded wait (Thm 2.2.2.3) | Bandwidth argument on ticket counter | SM2.B |
| TicketLock release-acquire (Thm 2.2.2.4) | Memory-model synchronization | SM2.B |
| RwLock writer-readers exclusion (Thm 2.2.3.1) | Predicate invariant | SM2.C |
| RwLock reader multiplicity (Thm 2.2.3.2) | Constructive | SM2.C |
| RwLock FIFO admission (Thm 2.2.3.3) | Queue discipline | SM2.C |
| RwLock bounded wait (Thm 2.2.3.4) | Bandwidth + reader-batching | SM2.C |
| RwLock release-acquire (Thm 2.2.3.5) | Memory-model | SM2.C |
| Lock-set canonical ordering (Thm 2.1.7) | Sort uniqueness | SM3.B |
| Deadlock-freedom (Thm 2.1.9) | Induction over LockId total order | SM3.D |
| Serializability (Thm 2.1.10) | Strict-2PL conflict-serializability | SM3.E |
| Single-core proof preservation (Cor 2.1.11) | Theorem migration with lock-set precondition | SM3.E |
| Path-a per-core extensionality (Thm 2.3.3) | Vector extensionality | SM4.B |
| ~110 migrated per-core scheduler invariants | Mechanical migration | SM4.C |
| ~22 migrated per-core IPC invariants | Same | SM4.D |
| SGI delivery (Thm 2.5.3) | Atomic-append + 2PL | SM5.C |
| TLB shootdown completeness (Thm 2.6.3) | Protocol with explicit ack | SM7 |
| Cross-core NI (Thm 2.7.3) | Per-core observer model | SM8 |
| WCRT bound under SMP fine-locking | Lock-set + per-lock WCRT composition | SM5.J |

### 7.2 What we assume

| Assumption | Citation | Phase |
|------------|----------|-------|
| ARMv8.1-A LSE atomic semantics (LDADDA, STADDL, etc.) | ARM ARM K11, K12 | SM2.A |
| Inner-shareable PE coherence | ARM ARM B2.3.6, B2.7.5 | All |
| DSB ISH waits for prior memory accesses by this PE | ARM ARM B2.7.5 | All |
| TLBI ...IS broadcasts to inner-shareable domain | ARM ARM C6.2.311-316 | SM7 |
| GICD_SGIR delivery semantics | GIC-400 TRM §4.3.13 | SM5.C |
| MPIDR_EL1 affinity field layout | ARM ARM D17.2.98 | SM0 |

**No Lean `axiom` declarations.** Hardware assumptions enter the
proof surface via FFI's opaque declarations (`@[extern]`) whose
Rust implementations are reviewed against ARM ARM. The Lean
abstract memory model (`Concurrency/MemoryModel.lean`) captures
the operational semantics; specific compilation choices (LDADDA vs
DMB ISH + STR) are HAL-side review obligations.

### 7.3 Testing tiers under SMP

| Tier | What it checks | SMP additions |
|------|----------------|---------------|
| Tier 0 (hygiene) | sorry/axiom/native_decide etc. | 0 axioms added |
| Tier 1 (build) | All modules compile | Concurrency suite compiles |
| Tier 2 (trace) | Deterministic trace fixture | `smp_4core_boot.expected` |
| Tier 3 (invariant) | Surface anchor `#check`s | Per-core invariant anchors; lock-primitive anchors |
| Tier 4 (nightly) | QEMU `-smp 4` boot | Cross-core IPC; TLB shootdown; SGI round-trip |
| Tier 5 (NEW) | Lock-primitive correctness | TicketLock + RwLock formal-spec checks |

### 7.4 Liveness under contention

Under per-object fine locks, syscall WCRT is bounded by:

    WCRT(syscall) ≤ max-lock-set-size × (coreCount − 1) × WCRT(criticalSection / lock)

For most operations, lock-set size is ≤ 4 (e.g., capability copy:
src CNode, dst CNode, CDT root, ObjStore). For RPi5 (coreCount = 4):

    WCRT(syscall) ≤ 4 × 3 × WCRT_per_lock ≈ 4 × 3 × ~60 µs = 720 µs ≈ 1 ms

This fits within the 1-ms timer-tick budget. Better than BKL's
4 × 250 µs = 1 ms worst case (per-object locks distribute the
wait across multiple locks, and most operations don't contend on
all of them simultaneously).

## 8. Risk inventory

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Lock-set extraction static analysis too brittle | MEDIUM | HIGH | SM3.B builds `lockSet` as a total Lean function; the static-derivability obligation is itself a theorem. |
| Deadlock-freedom proof has subtle gap | LOW | CRITICAL | Theorem 2.1.9's induction is mathematically standard; SM3.D includes wait-graph acyclicity as backup proof. |
| Multi-object operations exceed reasonable lock-set sizes (>8 locks) | MEDIUM | MEDIUM | Per-operation review during SM6; if any exceeds, refactor to fewer locks. |
| Per-core wake SGI lost | LOW | HIGH | GIC SGI delivery hardware-guaranteed; ack protocol confirms. |
| TLB shootdown deadlock (initiator waits forever) | LOW | HIGH | Bounded WFE in ack loop; timeout reverts to local-only TLBI |
| Secondary core wakes into broken MMU state | ZERO (SM1.C closes) | CRITICAL | SM1.C completes init before any kernel work |
| Lock acquire/release imbalance | LOW | CRITICAL | RAII `withLockSet` combinator; static analysis (`#[must_use]`) |
| Vector indexing out of bounds | ZERO (Fin coreCount) | — | Type-system guarantee |
| Memory ordering violation between cores | LOW | HIGH | ARMv8 release/acquire; SM2.A models semantics |
| Per-core idle thread interactions with PIP | LOW | MEDIUM | Idle priority 0; never participates in PIP boost |
| WS-SM scope overruns 30 months | MEDIUM | MEDIUM (release delay) | Phased delivery; each SM-phase independently shippable |
| Refinement proof Rust ↔ Lean has compilation drift | MEDIUM | HIGH | SM2.D static linker-time check; cargo test refinement scenarios |
| Hierarchical lock order has implicit cycles via cross-kind references | LOW | HIGH | SM3.D's wait-graph acyclicity catches; tested via property-based fuzz |
| RW lock starvation under writer contention | LOW | MEDIUM | Theorem 2.2.3.3 (FIFO admission); SM2.C.14 (writer-starvation freedom) |
| Lock-set complexity penalty too high for some hot-path operations | MEDIUM | MEDIUM | SM6 reviews hot paths; can use single-object locks where lock-set is naturally 1 |

## 9. Timeline

**Prerequisite implication for WS-RC**: WS-RC R2..R6 close at
v0.31.last instead of v1.0.0. Mechanical change; tracked under
SM0.Q.

WS-RC closure → WS-SM open at v0.31.x → v0.32.0 boundary.

| Phase | Releases | Estimated calendar |
|-------|----------|--------------------|
| SM0 | v0.32.0 → v0.32.x | 4-6 weeks |
| SM1 \|\| SM2 | v0.33.0 → v0.45.x | 16-22 weeks (parallel) |
| SM3 | v0.46.0 → v0.52.x | 8-12 weeks |
| SM4 | v0.53.0 → v0.70.x | 20-26 weeks (largest phase) |
| SM5 | v0.71.0 → v0.82.x | 12-16 weeks |
| SM6 | v0.83.0 → v0.90.x | 8-12 weeks |
| SM7 \|\| SM8 | v0.91.0 → v0.97.x | 6-10 weeks (parallel) |
| SM9 | v0.98.0 → **v1.0.0** | 4-6 weeks |
| **Total** | | **78-110 weeks (~18-26 months)** |

The lower bound assumes contributor parallelism on SM1+SM2 and
SM7+SM8. Solo-maintainer cadence at the bounds gives ~24-30
months realistic.

## 10. Decisions taken (was: open questions)

All 9 original open questions plus 3 derived ones answered:

| # | Question | Decision |
|---|----------|----------|
| 1 | Concurrency model | Per-subsystem locks (escalated to per-object fine locks in §3) |
| 2 | Target version + WS-RC retarget | v1.0.0 ships SMP; WS-RC retargets to v0.31.last (SM0.Q) |
| 3 | Model rewrite path | Path-a replacement |
| 4 | Default SMP activation | Enabled by default; opt-out via cmdline |
| 5 | numCores parameterization | Via `PlatformBinding.coreCount` |
| 6 | Cross-cluster portability | Via `PlatformBinding.sharingDomain` |
| 7 | Idle threads | Per-core idle TCBs |
| 8 | SM0 sequencing | Spread across many small PRs |
| 9 | Workstream ID | WS-SM |
| 10 | Lock layout | Per-object fine locks |
| 11 | RW vs exclusive | Reader-writer locks |
| 12 | Lock acquire order | Hierarchical by object kind |
| 13 | Timeline / scope trade-off | Longer timeline + verify lock primitives |

These decisions are recorded here as binding for WS-SM. Future
deviations require maintainer-led re-decisioning recorded in
errata.

## 11. Acceptance / completeness criteria for v1.0.0 release

WS-SM is complete and v1.0.0 ships when:

- [ ] All 4 CRITICAL findings closed (SMP-C1..C4) and all HIGH findings closed.
- [ ] All MEDIUM findings closed except those deferred with explicit rationale.
- [ ] LOW findings closed or recorded post-1.0 with correctness-impact statement.
- [ ] Every phase's acceptance gate (§5) green.
- [ ] tier-0 through tier-5 tests green at HEAD.
- [ ] QEMU `-smp 4` integration test green on every nightly.
- [ ] `cargo test` (HAL + ABI + types + sys) green.
- [ ] `lake build` (256 jobs) green; zero `sorry`, `axiom`, `native_decide`.
- [ ] `scripts/test_full.sh` + `scripts/test_nightly.sh` green.
- [ ] Documentation synchronized per CLAUDE.md "Documentation rules".
- [ ] AN12-B inventory transitioned to discharged state (or replaced).
- [ ] WCRT bound proven for SMP RPi5 canonical config.
- [ ] Per-core non-interference proven.
- [ ] Information flow: BKL contention channel documented; enforcement boundary extended.
- [ ] No production-source `dev_history/` cross-references.
- [ ] CHANGELOG v1.0.0 entry complete.
- [ ] Version bumped to 1.0.0 across all metric-bearing files.
- [ ] WS-SM closure recorded in `docs/WORKSTREAM_HISTORY.md`.
- [ ] This plan moved to `docs/dev_history/planning/`.

## Appendix A — Source-of-truth file inventory

[Same as prior version; ~2300 LoC of existing source inventoried.]

## Appendix B — Verification commands

```bash
# SMP-C1: bring_up_secondaries has no caller
grep -rn "bring_up_secondaries\|crate::smp::bring_up" rust/

# SMP-C2: rust_secondary_main body
sed -n '202,240p' rust/sele4n-hal/src/smp.rs

# SMP-C4: TLB module emits non-IS variants
grep -E "tlbi (vae1|aside1|vmalle1|vale1)[, ]" rust/sele4n-hal/src/tlb.rs

# SMP-H1: No SGI primitive
grep -n "GICD_SGIR\|send_sgi\|fn.*sgi" rust/sele4n-hal/src/gic.rs

# SMP-H2: ArchAssumption constructor count
grep -A 10 "inductive ArchAssumption" SeLe4n/Kernel/Architecture/Assumptions.lean

# SMP-H3: Inventory Lean.Name disclaimer
grep -A 3 "Lean does not enforce" SeLe4n/Kernel/Concurrency/Assumptions.lean

# SMP-M1: dev_history cross-references
grep -rn "dev_history" rust/sele4n-hal/src/ SeLe4n/Kernel/

# SMP-M2: stale WS-V claim
grep -n "deferred to WS-V" docs/spec/SELE4N_SPEC.md

# SMP-M3: .smp_stacks not zeroed
grep -B 2 -A 8 ".smp_stacks" rust/sele4n-hal/link.ld

# SMP-M4: TPIDR_EL1 not set in secondary_entry
grep -n "TPIDR\|tpidr" rust/sele4n-hal/src/boot.S

# SMP-M6: QEMU stub
head -30 scripts/test_qemu_smp_bringup.sh

# Inventory size
grep -n "smpLatentInventory_count" SeLe4n/Kernel/Concurrency/Assumptions.lean
```

## Appendix C — Theorem catalogue (forward-looking)

~210 new substantive theorems across the 10 phases. Selected
canonical names (full list maintained in
`docs/audits/SMP_THEOREM_INDEX.md` once WS-SM opens):

### C.0 Foundations (SM0)

- `numCores_pos`, `allCores_length`, `allCores_nodup`,
  `bootCoreId_valid`, `SgiKind.toIntid_injective`,
  `smpLatentInventory_identifiers_nodup`,
  `archAssumption_singleCoreOperation_added`,
  `archAssumptionConsumer_total_6`,
  `archAssumptionConsumer_distinct_6`,
  `LockKind.level_strictMono`, `LockId.le_total`,
  `SharingDomain.eq_decidable`.

### C.1 Memory model (SM2.A)

- `happens_before_partial_order`, `synchronizesWith_irreflexive`,
  `atomicRmw_total_order`, `acquireLoad_releaseStore_pair`,
  `memoryTrace_wellFormed_preserved`.

### C.2 Lock primitives (SM2.B, SM2.C)

- TicketLock: 6 theorems (mutex, FIFO, bounded wait, release-acq,
  wfInvariant, reachability).
- RwLock: 10 theorems (writer-readers exclusion, reader
  multiplicity, FIFO admission, bounded wait × 2, release-acq ×
  2, wfInvariant, reader batching, writer-starvation freedom).
- Refinement: 2 theorems (rust_ticketLock_refines_lean,
  rust_rwLock_refines_lean).

### C.3 Lock discipline (SM3)

- `lockSet_consistent`, `lockSet_acquired_in_order`,
  `lockSet_released_in_reverse`, `lockAcquireSequence_canonical`,
  `deadlockFreedom_under_2pl_and_ordering`,
  `serializability_under_2pl`, `singleCore_proof_preservation`,
  `waitGraph_acyclic`, plus ~10 commutativity lemmas.

### C.4 Per-core scheduler (SM4, SM5)

- ~110 migrated invariants + ~25 new per-core theorems
  (chooseThreadOnCore_*, runQueueOnCore_*,
  schedulerInvariant_perCore, schedulerInvariant_perCore_pairwise,
  wakeThread_emits_sgi_if_remote, wakeThread_lossless,
  cbsReplenish_can_wake_remote_core, idleThread_core_locality,
  idleThread_priority_zero, chooseThreadOnCore_always_succeeds,
  pipBoost_perCore_consistent, activeDomainOnCore_*, etc.).

### C.5 Per-core IPC (SM6)

- ~30 theorems: endpointCall_emits_sgi_if_remote_receiver,
  endpointCall_perCore_blocking, notificationSignal_remote_wake,
  endpointReply_perCore_delivery, donation_perCore_consistent,
  ipcInvariantFull_perCore, cancelIpcBlocking_atomic_under_lockset,
  cancelDonation_atomic_under_lockset, plus 22 migrated invariants.

### C.6 TLB shootdown (SM7)

- 14 theorems: tlbShootdownLocal_invalidates_local,
  tlbShootdownBroadcast_invalidatesAllCores,
  tlbInvalidationConsistent_perCore,
  shootdownAck_completes_in_bounded_time,
  pendingShootdowns_drained_at_sgi_entry,
  plus protocol invariants.

### C.7 Information flow (SM8)

- 18 theorems: onCore_isProjection_of_globalProjection,
  onCore_decidable, nonInterference_perCore,
  crossCoreNonInterference, bklContention_acceptedCovertChannel,
  enforcementBoundary_perCore_complete,
  DeclassificationEvent_perCore_audit, plus per-NI-constructor
  per-core analogues (32 of these in seL4 model).

### C.8 Boot / platform (SM4.E)

- 5 theorems: bootFromPlatform_all_cores_have_idle,
  bootFromPlatform_smp_witness, perCoreSchedulerConsistent,
  perCoreSchedulerConsistent_at_boot, PlatformBinding_coreCount_pos.

### C.9 Closure (SM9)

- 5 marker theorems: smpRetiredInventory_complete,
  wsm_phase_count, wsm_acceptance_gate_count, wsm_theorem_count,
  v1_0_0_release_witness.

**Total**: ~210 substantive theorems.

## Appendix D — Internal-first naming compliance

Per CLAUDE.md, no workstream IDs in identifiers. The plan uses
phase IDs `SM0..SM9` only in:
- Plan filename
- Sub-task labels (`SM3.A.1`, etc.)
- CHANGELOG entries
- Docstrings citing historical context

It does NOT use them in:
- Theorem names, function names, file names, test names, fields

WS-SM ages out as a label; the underlying code describes itself by
purpose.

## Appendix E — Verification quality ladder

The plan elevates seLe4n above seL4 on three verification axes:

| Axis | seL4 | seLe4n WS-SM |
|------|------|--------------|
| Lock-primitive correctness | Assumed | Formally proven (SM2) |
| Per-object lock discipline | BKL only | Per-object RW + hierarchical order |
| Cross-core NI | Limited | Per-core observer model (SM8) |

The cost is the ~24-30 month timeline. The benefit is the most
rigorously verified SMP microkernel in the literature.

---

*This plan was produced from branch
`claude/audit-multicore-implementation-sUcIx` at v0.31.2.  It opens
as workstream **WS-SM** immediately after WS-RC closure (which
retargets to v0.31.last per SM0.Q), with the goal of shipping a
bootable verified SMP microkernel as v1.0.0.  All 13 maintainer
decisions in §10 are binding for this workstream.*
