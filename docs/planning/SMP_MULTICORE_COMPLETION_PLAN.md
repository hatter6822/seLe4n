# WS-SM — SMP / Multi-Core Completion (pre-v1.0.0)

> **Status**: PLAN — workstream to land in full before the v1.0.0 cut.
>
> **Audited cut**: `v0.31.2` (current `lakefile.toml::version`).
>
> **Branch (this audit)**: `claude/audit-multicore-implementation-sUcIx`.
>
> **Release target**: **v1.0.0 "bootable verified SMP microkernel on
> Raspberry Pi 5"**. The v1.0.0 release notes claim a *bootable
> verified microkernel*; on a 4-core BCM2712 target that claim is
> only honest if all 4 cores are exercised. This workstream delivers
> that honesty by hardening the existing AN9-J scaffolding into a
> fully functional, machine-checked SMP kernel.
>
> **Sequencing**: WS-RC continues to closure as planned; **WS-SM
> opens at the v0.31.x → v0.32.0 boundary** (the same boundary that
> would have promoted v0.31.x to v1.0.0 under the prior plan). WS-SM
> closes at v1.0.0. The intermediate cuts (v0.32.x..v0.99.x) are
> WS-SM staging releases.
>
> **Scope discipline**: this plan is large (9 phases, ~340–420
> sub-tasks). It is decomposed so that *every* sub-task is
> independently verifiable, has a precise file:line target, a
> mathematical specification, and an acceptance criterion. Each
> sub-task is sized so that a single PR can land it without
> compound-state risk to surrounding work.
>
> **Out of scope** (deferred past v1.0.0):
> - ARMv9-A Confidential Compute / MPAM partitioning — separate
>   plan, [`HARDWARE_PARTITION_ISOLATION_PLAN.md`](HARDWARE_PARTITION_ISOLATION_PLAN.md);
>   depends on WS-SM as prerequisite.
> - Heterogeneous / big.LITTLE asymmetric topologies.
> - Hot-unplug, live core migration, cpu-frequency scaling.
> - Per-subsystem fine-grained locks (BKL is the v1.0.0 atomicity
>   primitive; finer locks are a v1.x performance workstream).
> - NUMA / non-uniform memory.

## 1. Executive summary

### 1.1 The core finding

The current SMP scaffolding **cannot be activated**: three CRITICAL
gaps make `SMP_ENABLED = true` either dead code (no caller) or a
correctness hazard (secondaries wake into a state the kernel can
neither observe nor coordinate). The AN9-J disposition
("activation cost is just flipping the runtime flag",
`AUDIT_v0.29.0_DEFERRED.md:296`) is materially inaccurate. Shipping
v1.0.0 under that disposition would ship a non-functional SMP
binary on a 4-core SoC.

### 1.2 Headline-severity findings (full catalogue in §3)

| Sev | ID | Finding |
|-----|----|---------|
| **CRIT** | SMP-C1 | `bring_up_secondaries()` has no caller. `rust_boot_main` has 4 phases (UART, MMU, GIC, timer) and no Phase 5 to parse `smp_enabled` or invoke bring-up. |
| **CRIT** | SMP-C2 | `rust_secondary_main` does **not** perform per-core MMU enable, VBAR install, GIC CPU-interface init, or timer arming despite its docstring claiming it does. Secondaries would wake with MMU off and exception vectors unset. |
| **CRIT** | SMP-C3 | `kernelStateRef : IO.Ref SystemState` (`FFI.lean:394`) is one shared `IO.Ref`. Lean's `IO.Ref` is not cross-core atomic; concurrent kernel entries are a race. |
| **CRIT** | SMP-C4 | TLB invalidation primitives (`tlb::tlbi_vae1`, `tlbi_aside1`, `tlbi_vmalle1`, `tlbi_vale1`) emit the **non-IS** variants. These instructions invalidate only the issuing PE's TLB (ARM ARM C6.2.311–316). Page unmaps leave stale translations on remote cores at the **hardware level** — a confidentiality and integrity hazard, not merely a coordination gap. |
| **HIGH** | SMP-H1 | No SGI / IPI primitive in `gic.rs`. No `send_sgi(target_cpu_mask, intid)`, no SGI handler dispatch. Cross-core reschedule, TLB shootdown, and wake notifications all require this. |
| **HIGH** | SMP-H2 | `ArchAssumption` inductive lacks the `singleCoreOperation` constructor that `Concurrency/Assumptions.lean:163-176` advertises as its anchor. The inventory entry's `singleCoreWitness` description is unimplemented per the **implement-the-improvement rule**. |
| **HIGH** | SMP-H3 | Inventory `Lean.Name` references are not build-checked. Renaming a referenced theorem silently drifts the inventory. |
| **HIGH** | SMP-H4 | `with_interrupts_disabled` is the kernel's only atomicity primitive. It does not serialise cross-core kernel entries. No spinlock / BKL exists. |
| **MED** | SMP-M1 | `dev_history/` cross-references in production sources (`boot.S:103`, `Architecture/Assumptions.lean:333`, `CrossSubsystem.lean:3264`). |
| **MED** | SMP-M2 | Stale "deferred to WS-V" SMP claim across spec, DEVELOPMENT.md, GitBook. WS-V is closed and never owned SMP. |
| **MED** | SMP-M3 | `.smp_stacks` linker section not zeroed at boot — stale RAM exposure on activation. |
| **MED** | SMP-M4 | `TPIDR_EL1` not set in `secondary_entry` despite docstring claim. |
| **MED** | SMP-M5 | PSCI wrapper only implements `cpu_on`. Missing `cpu_off`, `affinity_info`, `system_off`, `system_reset`. |
| **MED** | SMP-M6 | `scripts/test_qemu_smp_bringup.sh` is a SKIP stub. |
| **MED** | SMP-M7 | `PlatformBinding` has no `numCores` / `bootCoreId` field; `PlatformConfig` has no per-core boot data. |
| **LOW** | SMP-L1 | No NoDup witness on `smpLatentInventory.identifier` list. |
| **LOW** | SMP-L2 | `MAX_SECONDARY_CORES = 3` hard-coded for BCM2712. |
| **LOW** | SMP-L3 | No `setThreadCpuAffinity` capability operation; no `coreId` field on TCB. |
| **LOW** | SMP-L4 | Lean `Concurrency/` namespace has only `Assumptions.lean`; no `Locks.lean`, `Memory.lean`, `Ipi.lean`. |
| **LOW** | SMP-L5 | No Lean test exercises any multicore code path. |

### 1.3 Workstream shape

**WS-SM**, 9 phases, ~340–420 sub-tasks, ~14–22 staging releases.

```
SM0  Foundations & honesty patches            (12-18 PRs, 30-40 sub)
SM1  Rust HAL completion                      (18-26 PRs, 50-70 sub)
SM2  Per-core kernel state model              (15-22 PRs, 40-55 sub)
SM3  BKL Lean integration                     (20-28 PRs, 50-65 sub)
SM4  Per-core scheduler                       (22-30 PRs, 60-80 sub)
SM5  Cross-core IPC                           (15-22 PRs, 40-55 sub)
SM6  TLB / cache shootdown                    (12-18 PRs, 30-45 sub)
SM7  Information flow under SMP               (12-18 PRs, 30-40 sub)
SM8  Documentation, tests, version closure    (8-12 PRs, 20-30 sub)
─────────────────────────────────────────────────────────────────
                                              134-194 PRs total
```

Parallelism: SM0 must complete first; SM1 || SM2 (independent); SM3
gates on SM1+SM2; SM4 || SM6 || SM7 after SM3; SM5 after SM4; SM8
last.

## 2. Mathematical foundations

This section pins the **formal specification** of SMP semantics
that every subsequent phase relies on. Definitions are written in
mathematical/Lean notation; proof sketches use standard inference
rules. All claims have an ARM ARM citation or are derived
strictly from cited claims.

### 2.1 Concurrency model: Big Kernel Lock serialization

**Definition 2.1.1** (Kernel transition). A *kernel transition* is
an atomic state-update function τ : SystemState × Args → KernelResult.
At v0.31.2 every `@[export]` body composes pure transitions.

**Definition 2.1.2** (BKL property). For a SystemState s with field
`s.concurrency.bkl : BklState`,

    BklProperty(s) ≡ s.concurrency.bkl = .unheld
                   ∨ ∃! c : CoreId, s.concurrency.bkl = .held c

**Theorem 2.1.3** (BKL serialization). Under BklProperty,
concurrent kernel entries from distinct cores execute *sequentially*
with respect to SystemState observation. Specifically, if at clock
time t₁ < t₂ cores c₁ ≠ c₂ both call `@[export]` body f, then
either (a) c₁'s f completes (BKL released) strictly before c₂'s f
acquires BKL, or (b) symmetrically.

**Proof sketch.** Ticket-lock FIFO discipline (Theorem 2.2.6 below)
plus the atomicity of `fetch_add` on `next_ticket` partition the
ticket space; the lock holder is exactly the core whose captured
ticket equals `serving`; releases increment `serving` by exactly 1;
therefore exactly one core observes `serving == my_ticket` at any
moment. □

**Corollary 2.1.4** (single-core proof reuse). Every existing
single-core kernel-transition theorem in
`SeLe4n/Kernel/*/Invariant/*.lean` remains valid for SMP under BKL,
*provided* the precondition that BKL is held by the executing core
is added (or, equivalently, the conclusion is stated relative to
"the current-core view" of the state).

This is the architectural lever that makes SMP tractable for
v1.0.0: the BKL preserves the proof surface. Finer-grained locking
would force a re-prove of every transition; BKL imposes a global
serialization order that the existing proofs already satisfy.

### 2.2 Lock correctness: ticket lock

**Definition 2.2.1** (Ticket lock state).

    structure TicketLock where
      nextTicket : AtomicU64   // monotone, write-only via fetch_add
      serving    : AtomicU64   // monotone, write-only via fetch_add

with invariant TL-INV: `serving ≤ nextTicket` (interpreted as
`UInt64` partial order modulo wrap-around; wrap is unreachable for
our deployment — see Note 2.2.7).

**Definition 2.2.2** (Acquire). In pseudocode:

    fn acquire(self: &TicketLock) -> u64 {
      let my = self.nextTicket.fetch_add(1, Acquire);
      while self.serving.load(Acquire) != my {
        wfe_bounded(WFE_DEFAULT_TIMEOUT_TICKS);
      }
      my
    }

**Definition 2.2.3** (Release).

    fn release(self: &TicketLock) {
      self.serving.fetch_add(1, Release);
      sev();  // wake any waiters parked in wfe
    }

**Definition 2.2.4** (Holder).

    holder(t : TicketLock) ≡
      { c : CoreId | c has captured my == t.serving and not yet released }

**Theorem 2.2.5** (Mutex). For any TicketLock t, |holder(t)| ≤ 1.

**Proof.** A core c is in holder(t) iff (1) c captured a `my` via
`fetch_add` on `nextTicket`, and (2) c observed `serving == my` and
(3) c has not yet released. By the atomicity of `fetch_add`, every
captured `my` is distinct (the captured value is the
pre-increment). `serving` is a single `AtomicU64`; at any moment it
equals exactly one captured `my`. Therefore at most one c satisfies
(2) at any moment. □

**Theorem 2.2.6** (FIFO progress). If c₁ acquires `my = m₁` at time
t₁ and c₂ acquires `my = m₂` at time t₂ > t₁ (real-time order of
the two `fetch_add`s), then m₁ < m₂, and c₁'s critical section
completes (release advances `serving` past m₁) before c₂ exits the
spin loop.

**Proof.** The first claim is immediate from `fetch_add`'s
monotonic-pre-increment semantics. The second: c₂'s spin loop
exits iff `serving == m₂`. `serving` only advances via release
calls. Since `serving` starts ≤ m₁ < m₂, it must pass through m₁
before reaching m₂. When `serving == m₁`, c₁ is in its critical
section; c₁'s eventual release sets `serving := m₁ + 1`; further
releases (from cores with `my = m₁+1, m₁+2, ..., m₂-1`) eventually
set `serving = m₂`. □

**Note 2.2.7** (Wrap-around). The ticket counters are `UInt64`.
Even at 10 billion acquires per second, wrap takes ~58 years —
unreachable in any real deployment. The model treats wrap as
unreachable. If a theoretically rigorous wrap handling is desired,
the standard technique is to compute differences modulo 2^64 and
require `(nextTicket - serving) < numCores` invariantly; this is
always satisfied because at most `numCores` cores can hold or be
waiting at any moment. We document this in
`Concurrency/Locks.lean::wrapUnreachable`.

**Theorem 2.2.8** (Bounded wait). For numCores cores, the WCRT of
`acquire` is

    WCRT(acquire) ≤ (numCores − 1) × WCRT(criticalSection)

provided every critical section has a bounded WCRT.

**Proof.** Bandwidth argument: between c's `fetch_add` capturing
`my` and c observing `serving == my`, at most `my - serving_at_capture`
holders must release. By Theorem 2.2.6, that count is at most
numCores − 1 (the other cores). Each release happens within
WCRT(criticalSection). □

**Corollary 2.2.9** (Liveness). Under SMP BKL, every syscall
returns within `numCores × WCRT(criticalSection)`. For seLe4n on
RPi5 (`numCores = 4`), this is 4× the existing single-core WCRT
bound established by R5's `wcrt_bound_rpi5`. We extend that bound
in SM4.

### 2.3 Memory model

**Assumption 2.3.1** (ARMv8-A inner-shareable PE coherence). All
ARMv8-A PEs in the inner-shareable domain observe a coherent view
of memory under the following discipline (ARM ARM B2.3.6, B2.7.5,
K11):

1. Atomic operations with Acquire/Release ordering establish a
   happens-before relation across PEs.
2. `DSB ISH` on a PE waits for all prior memory accesses *by that
   PE* to complete with respect to the inner-shareable domain.
3. `DSB ISH; ISB` ensures all prior translations and instruction
   fetches are observed before any subsequent fetch.
4. `TLBI ...IS` broadcasts the invalidation to all PEs in the
   inner-shareable domain; non-IS variants do NOT broadcast (this
   is SMP-C4).

BCM2712 is a single Cortex-A76 cluster with 4 cores; all four are
in one inner-shareable domain. No cross-cluster (outer-shareable)
considerations apply unless a future port targets a multi-cluster
SoC, at which point `BarrierKind::DsbOsh` (AN9-I) and OSH-variant
TLB instructions are required.

**Theorem 2.3.2** (BKL release-acquire pairing). Let c₁ release
the BKL at time t₁ (corresponding to c₁'s `serving.fetch_add(1,
Release)` retiring) and c₂ acquire the BKL at time t₂ > t₁
(corresponding to c₂'s spin-loop `serving.load(Acquire)` reading
the value c₁ wrote). Then all writes performed by c₁ before t₁
are visible to c₂ at and after t₂.

**Proof.** c₁'s release stores the new `serving` value with
Release ordering — on ARMv8.1-A this compiles to `STADDL`, or on
earlier cores to `DMB ISH ; STR`. The Release semantics (ARM ARM
K11.2) guarantee that all writes c₁ performed before this store
(including writes to the shared `SystemState` carried inside
`kernelStateRef`) are sequenced-before the store with respect to
the inner-shareable domain.

c₂'s spin-loop terminating load is `serving.load(Acquire)`,
compiled to `LDAR` or `LDR ; DMB ISH`. The Acquire semantics
guarantee that all reads c₂ performs after this load see values
that were published by any release-ordered store the load
synchronizes with.

When c₂'s `serving.load(Acquire)` observes the value c₁ wrote
with `serving.fetch_add(1, Release)`, a release-acquire
synchronization edge is established (ARM ARM B2.3.7, C++/Rust
memory-model rule "release sequence headed by a release operation
synchronizes-with an acquire operation that reads from it"). All
writes by c₁ sequenced-before its release are therefore observed
by c₂ at and after the synchronizing load — and consequently at
and after t₂. □

**Note 2.3.2.a** (the role of `nextTicket`). The Acquire ordering
on `nextTicket.fetch_add(1, Acquire)` provides a *total order on
ticket assignments* across cores (each fetch_add observes the
previous fetch_add's increment), but it does NOT itself
synchronize c₂ with c₁'s prior critical section. The
state-visibility synchronization is purely on `serving`. We pin
this in `Concurrency/Locks.lean` docstring to prevent future
maintainers from "optimizing away" the spin-loop Acquire load.

**Corollary 2.3.3** (kernelStateRef safety under BKL). The shared
`IO.Ref SystemState` is safe to read and write under BKL because:

1. All reads (`getKernelState`) happen with BKL held → no
   concurrent writer (Theorem 2.2.5).
2. All writes (`updateKernelState`) happen with BKL held → no
   concurrent reader.
3. The previous holder's writes are visible (Theorem 2.3.2).

Therefore the sequence "acquire BKL → read pre-state → compute
post-state → write post-state → release BKL" is sequentially
consistent with respect to other BKL holders' sequences. □

### 2.4 Per-core state encoding

**Definition 2.4.1** (Core identifier).

    namespace SeLe4n.Kernel.Concurrency

      /-- Number of cores on the kernel's target SoC. Fixed at
          numCores = 4 for the RPi5 BCM2712 target. Future platform
          parameterization is a post-1.0 hardening item. -/
      def numCores : Nat := 4

      /-- Typed core identifier. `Fin numCores` makes every CoreId
          valid by construction; index out-of-bounds is a Lean type
          error, not a runtime check. -/
      abbrev CoreId : Type := Fin numCores

      def bootCoreId : CoreId := ⟨0, by decide⟩

      /-- All core ids enumerated. Useful for fold-over-cores
          operations like cross-core invariant composition.
          Uses the Lean 4 Std helper `List.finRange : (n : Nat) →
          List (Fin n)` which returns `[⟨0, _⟩, ⟨1, _⟩, …, ⟨n-1, _⟩]`
          with built-in length theorem. -/
      def allCores : List CoreId := List.finRange numCores

      theorem allCores_length : allCores.length = numCores :=
        List.length_finRange numCores

      /-- Cores are pairwise distinct by construction (Fin equality is
          decidable and `finRange` produces a distinct enumeration). -/
      theorem allCores_nodup : allCores.Nodup :=
        List.nodup_finRange numCores

    end SeLe4n.Kernel.Concurrency

**Definition 2.4.2** (Per-core scheduler state). The single-core
`SchedulerState` becomes:

    structure SchedulerState where
      -- Per-core fields (Vector indexed by CoreId)
      current             : Vector (Option ThreadId) numCores
      runQueue            : Vector RunQueue numCores
      replenishQueue      : Vector ReplenishQueue numCores
      activeDomain        : Vector DomainId numCores
      domainTimeRemaining : Vector Nat numCores
      domainScheduleIndex : Vector Nat numCores
      lastTimeoutErrors   : Vector (List (ThreadId × KernelError)) numCores
      -- System-wide fields (unchanged from single-core)
      domainSchedule      : List DomainScheduleEntry := []
      configDefaultTimeSlice : Nat := 5

with helpers:

    namespace SchedulerState
      def currentOnCore (s : SchedulerState) (c : CoreId) : Option ThreadId :=
        s.current.get c

      def runQueueOnCore (s : SchedulerState) (c : CoreId) : RunQueue :=
        s.runQueue.get c

      -- ... and so on for every per-core field.

      /-- Boot-core compatibility shim. Every theorem that read
          `s.current` in the single-core era now reads
          `s.currentOnCore bootCoreId` (or `currentOnBootCore`). -/
      def currentOnBootCore (s : SchedulerState) : Option ThreadId :=
        s.currentOnCore bootCoreId
    end SchedulerState

**Rationale**: choosing `Vector α numCores` (not `Array`, not
`List`, not `coreId → α`) is mathematically forced:

- `Array α` lacks compile-time length proofs; out-of-bounds access
  returns a default value silently.
- `List α` lacks O(1) random access.
- `CoreId → α` is total but extensional equality is undecidable.
- `Vector α numCores` (with `Vector := { l : List α // l.length = numCores }`)
  gives O(1) get (via `List.get` + length proof), decidable
  extensionality, and compile-time index safety. Lean 4's `Vector`
  is in `Mathlib` or `Std`; if not available we define it locally.

### 2.5 BKL Lean encoding

**Definition 2.5.1** (BKL state model).

    namespace SeLe4n.Kernel.Concurrency

      /-- Big Kernel Lock state. The Lean model exposes only the
          atomic transitions (acquire / release); the underlying
          ticket-lock mechanics are HAL-side and not modeled
          per-step in Lean (they are reasoned about externally
          via §2.2's theorems). -/
      inductive BklState where
        | unheld
        | held (owner : CoreId)
        deriving DecidableEq, Repr, Inhabited

      def bklHeldBy (b : BklState) (c : CoreId) : Prop :=
        b = .held c

      instance (b : BklState) (c : CoreId) : Decidable (bklHeldBy b c) := by
        unfold bklHeldBy; exact inferInstance

      structure ConcurrencyState where
        bkl : BklState := .unheld
        deriving Repr, Inhabited

    end SeLe4n.Kernel.Concurrency

The `SystemState` gains a `concurrency : ConcurrencyState` field.

**Definition 2.5.2** (BKL pre/post predicates). For a kernel
transition τ : SystemState × Args → KernelResult on core c,

    bklPreAcquired(c, s) ≡ s.concurrency.bkl = .unheld
    bklPostAcquired(c, s) ≡ s.concurrency.bkl = .held c
    bklPostReleased(s) ≡ s.concurrency.bkl = .unheld

**Definition 2.5.3** (BKL discipline for `@[export]` bodies). Every
`@[export]` FFI body conforms to:

1. **Pre**: BKL is unheld OR the body acquires BKL as its first
   action.
2. **Mid**: BKL is held by the executing core for the full duration
   of state-touching work.
3. **Post**: BKL is released as the last action; post-state has
   `bkl = .unheld`.

**Theorem 2.5.4** (BKL atomicity of state transitions).

    ∀ (τ : SystemState → SystemState),
    ∀ (c : CoreId) (s s' : SystemState),
      bklPreAcquired(c, s) →
      τ s = s' →
      bklPostReleased(s') →
      ∃ (sMid : SystemState),
        bklPostAcquired(c, sMid) ∧
        τ' sMid = s' ∧                 -- intermediate transition
        bklPostReleased(s')

This is the *kernel-transition envelope theorem*. It encodes that
every state mutation is bracketed by BKL acquire/release; the
inner kernel logic operates on the "during" state where BKL is
held.

The model is **non-destructive**: existing single-core transitions
become "during-BKL" transitions; the acquire/release brackets are
new envelope code in `@[export]` bodies. Single-core proofs prove
properties of the *during* transition; the BKL discipline gives
us the *envelope* property.

### 2.6 IPI (SGI) model

**Definition 2.6.1** (SGI INTID allocation).

    namespace SeLe4n.Kernel.Concurrency
      /-- SGI INTIDs used by the kernel. ARM GIC-400 SGI range is
          INTIDs 0..15 (TRM §3.1). seLe4n reserves these 5; the
          remaining 11 are available for application-layer use via
          a future capability operation (post-1.0). -/
      inductive SgiKind where
        | reschedule        -- INTID 0: target core re-enters scheduler
        | tlbShootdownReq   -- INTID 1: invalidate-and-ack
        | tlbShootdownAck   -- INTID 2: invalidation completed
        | cacheBroadcast    -- INTID 3: cross-core cache maintenance
        | haltAll           -- INTID 4: panic/halt synchronization
        deriving DecidableEq, Repr

      def SgiKind.toIntid : SgiKind → Nat
        | .reschedule      => 0
        | .tlbShootdownReq => 1
        | .tlbShootdownAck => 2
        | .cacheBroadcast  => 3
        | .haltAll         => 4

      /-- Pairwise distinctness: the 5 SGI INTIDs are different.
          C(5,2) = 10 inequalities, all by `decide`. -/
      theorem SgiKind.toIntid_injective :
        ∀ k₁ k₂ : SgiKind, k₁ ≠ k₂ → k₁.toIntid ≠ k₂.toIntid := by
        intros k₁ k₂ h; cases k₁ <;> cases k₂ <;> simp_all <;> decide
    end SeLe4n.Kernel.Concurrency

**Definition 2.6.2** (SGI send semantics). An SGI is modeled as a
pending-event entry on the target core's pending queue:

    structure PendingSgi where
      sender : CoreId
      kind   : SgiKind
      payload : Option Nat  -- e.g., TLB shootdown carries asid/vaddr

    structure ConcurrencyState where
      bkl : BklState := .unheld
      pendingSgis : Vector (List PendingSgi) numCores :=
        Vector.replicate numCores []

The `sendSgi` operation under BKL appends to the target's pending
queue; the target's SGI handler (run on next kernel entry on that
core) drains the queue.

**Theorem 2.6.3** (SGI delivery). For sender c₁ and target c₂ with
SGI kind k, if c₁ executes `sendSgi c₂ k payload` while holding
BKL, then on c₂'s next kernel entry, c₂'s pending queue contains
the entry.

**Proof.** Under BKL, the append is atomic with respect to c₂'s
read (Corollary 2.3.3). The next kernel entry on c₂ acquires BKL
and reads the (updated) pending queue. □

**Note 2.6.4** (Hardware delivery). The Lean model abstracts SGI
delivery as "appears in pending queue". The Rust HAL implements
the actual GICD_SGIR write and the SGI handler dispatch. The
Lean-side `@[extern "ffi_send_sgi"]` is the seam: Lean appends to
the queue, calls the FFI primitive which writes GICD_SGIR; the
target core's GIC raises an IRQ; the IRQ handler executes the
queued work.

### 2.7 TLB shootdown protocol

**Specification 2.7.1** (Correctness). After a successful TLB
shootdown for (asid, vaddr) initiated by core c₀, no core c ∈
allCores has (asid, vaddr) cached in its TLB.

**Protocol 2.7.2** (Acquire-shootdown-release):

```
TlbShootdown(initiator c₀, asid, vaddr):
  1. Hold BKL (precondition: every kernel entry holds BKL).
  2. Initialize shootdownAck : Vector Bool numCores :=
       Vector.replicate numCores false; set shootdownAck[c₀] := true
       (initiator does its own invalidation locally).
  3. For each c ∈ allCores \ {c₀}:
       sendSgi c .tlbShootdownReq (encode asid vaddr)
  4. Locally: tlbi vaae1is, vaddr ; dsb ish ; isb.
     (IS variant suffices for inner-shareable but we go a step
     further with explicit ack for protocol-level certainty and
     cross-cluster portability.)
  5. Loop: for each c with shootdownAck[c] = false, wfe_bounded(...);
     each remote core's SGI handler:
       a. tlbi vaae1is, vaddr (matches initiator's local TLBI)
       b. dsb ish ; isb
       c. atomically set shootdownAck[c] := true
       d. send back .tlbShootdownAck SGI
       e. eret to interrupted context.
  6. Loop terminates when shootdownAck = all true.
  7. Issue final dsb ish ; isb.
  8. Release BKL (envelope).
```

**Theorem 2.7.3** (Protocol correctness). At end of TlbShootdown,
no core has (asid, vaddr) in its TLB.

**Proof.** Each remote core c executes `tlbi vaae1is` in step 5(a)
before setting `shootdownAck[c]`. The IS-variant TLBI's effect on
remote PEs is observed-by-DSB-ISH (Assumption 2.3.1), and the
local DSB ISH in 5(b) waits for c's own invalidation to complete.
The initiator waits until all flags are true (step 6), then issues
DSB ISH (step 7). At this point every remote core has completed
its TLBI, and the initiator has observed those completions
through the acquire-ordered atomic-set of `shootdownAck` and the
final DSB. □

**Note 2.7.4** (Optimization: IS-variant alone). On a single-cluster
inner-shareable BCM2712, `tlbi vaae1is` alone is sufficient at the
hardware level — the IS variant broadcasts to all PEs in the
inner-shareable domain. We adopt the explicit-ack protocol for
two reasons:
1. **Cross-cluster portability**: future multi-cluster ports need
   explicit synchronization (the inner-shareable domain becomes
   per-cluster).
2. **Formal anchor**: explicit ack gives the Lean proof a concrete
   per-core invalidation event to reason about, rather than relying
   on a single global "DSB ISH suffices" assumption.

### 2.8 Information flow under SMP

**Definition 2.8.1** (Per-core observer). Under SMP, an *observer*
is a pair (c, L) of (core, security-label) — an attacker running
on core c with label L.

**Definition 2.8.2** (Per-core projection).

    ObservableState.onCore (c : CoreId) (L : SecurityLabel) (s : SystemState) :=
      { current      := s.scheduler.currentOnCore c
      , runQueue     := s.scheduler.runQueueOnCore c
      , activeDomain := s.scheduler.activeDomain.get c
      , objects      := { o ∈ s.objects | labelOf o ⊑ L }
      , -- ... other label-filtered fields
      }

**Theorem 2.8.3** (Cross-core noninterference). For observers
(c, L), if a transition on a *different* core c' ≠ c does not
mutate any object o with labelOf o ⊑ L AND does not signal a
notification observable by (c, L), then ObservableState.onCore c L
is unchanged.

This is the SMP analogue of the existing NI proof; the per-core
projection isolates each core's view, and the BKL serialization
ensures cross-core transitions are observable only via their
label-respecting effects.

### 2.9 Mathematical roadmap summary

| Phase | New axioms / assumptions | New theorems |
|-------|--------------------------|--------------|
| SM2 | None (model rewrite) | `numCores = 4`, `bootCoreId = ⟨0, _⟩`, `allCores_length`, ~12 helper-equality lemmas |
| SM3 | Acq/Rel ordering on `AtomicU64` (ARM ARM cited) | `bklMutex` (Thm 2.2.5), `bklFifo` (2.2.6), `bklRelAcq` (2.3.2), `kernelStateRefSafe` (2.3.3) |
| SM4 | None | Per-core analogues of every Scheduler invariant: `runQueueOnCore_wellFormed`, `currentOnCore_consistent`, `pipBoost_perCore`, `wcrtBound_smp` (extends `wcrt_bound_rpi5`) |
| SM5 | None | Per-core IPC: `crossCoreCall_wakesReceiver`, `crossCoreNotify_observedByReceiver` |
| SM6 | None | `tlbShootdown_invalidatesAllCores` (Thm 2.7.3) |
| SM7 | None | `crossCoreNonInterference` (Thm 2.8.3) |

Total: 0 new axioms; ~80–110 new substantive theorems; ~10–15
helper-equality lemmas. The `axiom budget` for WS-SM is **0**.

## 3. Detailed finding catalogue

(Each finding cites file:line directly verifiable in the
audit's source tree. Acceptance criteria in §5 reference these IDs.)

### 3.1 SMP-C1 — `bring_up_secondaries` is never called

**Locus**: `rust/sele4n-hal/src/boot.rs:27-108` (`rust_boot_main`).

`rust_boot_main` executes 4 phases (UART → MMU → GIC → timer) and
calls `lean_kernel_main(dtb_ptr)` on Phase 4. There is no Phase 5.
`grep -rn "bring_up_secondaries\|crate::smp::bring_up" rust/` returns
only references inside `smp.rs` itself and a comment in `boot.S:141`.

The `smp.rs:55-57` docstring claims "deployments that opt in to SMP
set this `true` via a kernel-command-line parameter parsed by
`boot.rs::rust_boot_main` before invoking `bring_up_secondaries`."
**No such parsing or invocation exists.**

**Closure**: SM0.5 documents honestly; SM1.E adds the DTB parser;
SM1.F adds the Phase 5 invocation under `BKL initialized`
precondition (see SM3).

### 3.2 SMP-C2 — `rust_secondary_main` is incomplete

**Locus**: `rust/sele4n-hal/src/smp.rs:213-235`.

Docstring (lines 202-211) promises: "Each secondary core runs
through the AK5-D-ordered MMU-enable sequence, applies the AK5-C
SCTLR_EL1 bitmap, initialises its GIC CPU interface, then spins on
its `core_ready` flag." Body actually contains only a
`wfe_bounded` loop on `CORE_READY[core_idx]` and a final
`loop { wfe }`. No `mmu::init_mmu`, no `write_vbar_el1`, no
`gic::init_cpu_interface`, no `timer::init_timer` call.

**Consequence at runtime** (if SMP-C1 were closed first):

1. Secondary jumps from `secondary_entry` (with MMU off — PSCI hands
   off in the same MMU state the firmware left, typically off) into
   `rust_secondary_main`.
2. First load via virtual address would fault — but `wfe_bounded`
   uses `mrs cntpct_el0` and direct memory access to `CORE_READY`
   (a static), both of which can succeed without MMU (the kernel
   image is identity-mapped at the load address).
3. The `CORE_READY` flag is in BSS (`.bss`), which lives at a
   physical address that happens to be loadable without MMU
   (because U-Boot loaded the image at a known physical address).
   So the spin loop *would work*.
4. Once the primary signals ready, secondary enters
   `loop { wfe }` — parks idle forever.
5. **Any IRQ delivered to this core** would jump to PC = VBAR_EL1
   = 0 (uninitialized) — UNDEFINED behavior, likely a synchronous
   exception loop or hard reset.

The current state is *latently safe* (no IRQ ever fires because
GIC isn't routed to this core's CPU interface), but a single
mis-configured GIC distributor write would expose this.

**Closure**: SM1.C, SM1.D — full secondary init sequence.

### 3.3 SMP-C3 — `kernelStateRef` is shared across cores

**Locus**: `SeLe4n/Platform/FFI.lean:394`.

```lean
initialize kernelStateRef : IO.Ref SystemState ← IO.mkRef (default : SystemState)
```

`IO.Ref` is a mutable reference cell with non-atomic read/modify/write
semantics. Two cores executing `updateKernelState f` concurrently
would race; the second `set` clobbers the first.

The hazard is unrealized today because secondary cores never reach
any FFI body (SMP-C1, SMP-C2 prevent it). Activation requires
serialization.

**Closure**: SM3 — BKL discipline wraps every `@[export]` body;
Corollary 2.3.3 establishes `kernelStateRef` safety under BKL.

### 3.4 SMP-C4 — TLB instructions are non-IS (single-PE only)

**Locus**: `rust/sele4n-hal/src/tlb.rs`:

- Line 34: `asm!("tlbi vmalle1", ...)` — invalidates this PE only.
- Line 57: `asm!("tlbi vae1, {0}", ...)` — invalidates this PE only.
- Line 78: `asm!("tlbi aside1, {0}", ...)` — invalidates this PE only.
- Line 100: `asm!("tlbi vale1, {0}", ...)` — invalidates this PE only.

Per ARM ARM C6.2.311-316, the `IS` (inner-shareable) variants
(`vmalle1is`, `vae1is`, `aside1is`, `vale1is`) broadcast to all PEs
in the inner-shareable domain. The current non-IS variants do not
broadcast at all. Even the trailing `dsb ish` (lines 38, 60, 81,
103) does NOT propagate the invalidation — DSB ISH only waits for
**this PE's** memory operations.

**Concrete failure scenario** (under SMP activation):

1. Core 0 unmaps page V (calls `tlbi_vae1(asid, V)`); kernel-side
   it considers V unmapped.
2. Core 0 reallocates V's physical backing for a different ASID/process.
3. Core 1 still has the old translation V → P_old in its TLB.
4. Core 1 dereferences V — reads P_old's contents (which now
   belongs to a different process).

This is a **confidentiality + integrity vulnerability** on any
SMP activation that uses page unmaps (every retype, every
revocation). Severity: CRITICAL.

**Closure**: SM1.F (HAL-side IS variants) + SM6 (shootdown
protocol with explicit ack).

### 3.5 SMP-H1 — No SGI / IPI primitive

**Locus**: `rust/sele4n-hal/src/gic.rs` — no `GICD_SGIR` register
constant, no `send_sgi` function. Grep `GICD_SGIR\|send_sgi` returns
zero hits.

ARM GIC-400 TRM §4.3.13: GICD_SGIR at offset 0xF00 from GICD base.
Format:

```
[31:26] reserved
[25:24] TargetListFilter (00=use list, 01=all but self, 10=self only)
[23:16] CPUTargetList (bit i = CPU i)
[15]    NSATT (non-secure access flag)
[14:4]  reserved
[3:0]   SGIINTID (0..15)
```

**Closure**: SM1.G — `gic::send_sgi` + Lean `@[extern]` + SGI
dispatch.

### 3.6 SMP-H2 — Missing `singleCoreOperation` ArchAssumption

**Locus**: `SeLe4n/Kernel/Architecture/Assumptions.lean:17-23`.

`ArchAssumption` has 5 constructors:

```
inductive ArchAssumption where
  | deterministicTimerProgress
  | deterministicRegisterContext
  | memoryAccessSafety
  | bootObjectTyping
  | irqRoutingTotality
```

But `SeLe4n/Kernel/Concurrency/Assumptions.lean:163-176` entry 7
references this inductive as the anchor for the single-core
assumption, claiming:

> "recorded in `Architecture/Assumptions.lean` via the
> `ArchAssumption` inductive + `assumptionInventory` aggregator."

The constructor does not exist. The inventory entry's description
is documentation-as-aspiration, not documentation-as-truth.

Per CLAUDE.md's **implement-the-improvement rule**: the inventory
description is the better state; **implement the constructor** so
the description becomes true.

**Closure**: SM0.A — add `singleCoreOperation` constructor; extend
`assumptionInventory` to 6 entries; extend `archAssumptionConsumer`
to map it to `bootFromPlatform_singleCore_witness`; extend the
distinctness theorem to C(6,2) = 15 inequalities.

### 3.7 SMP-H3 — Inventory Lean.Name not build-checked

**Locus**: `Concurrency/Assumptions.lean:53-61`.

```lean
The `identifier` and `sourceTheorem` fields hold `Lean.Name`
literals. Lean does not enforce that a `Lean.Name` literal resolves
to a defined symbol — the name is just a structural reference.
```

A `@` reference per name would catch the rename-without-update
case. Pattern already exists in `Architecture/Invariant.lean` for
`archAssumptionConsumer`.

**Closure**: SM0.C — `Concurrency/Anchors.lean` with `@`-references
of every inventory `identifier` and `sourceTheorem`.

### 3.8 SMP-H4 — `with_interrupts_disabled` insufficient for SMP

**Locus**: `rust/sele4n-hal/src/interrupts.rs:101-106`.

`with_interrupts_disabled` masks IRQ on the calling core. On SMP it
does NOT prevent other cores from running concurrent kernel
transitions. The AN12-B inventory's `smpDischarge` fields for
entries 1, 2, 3, 4, 5, 7, 8 all rely on "the FFI bracket prevents
interleaved capability operations" — this is FALSE for cross-core
interleaving.

**Closure**: SM1.B (Rust ticket lock), SM1.J (Lean BKL FFI binding),
SM3 (BKL discipline) — every `@[export]` body acquires BKL before
the IRQ-disable bracket.

### 3.9 SMP-M1..M7, SMP-L1..L5 (documentation, hygiene, scope)

Detailed remediation in §5 (SM0.D through SM0.K, SM1.A, SM2.M,
SM7.K). These items are individually smaller but collectively
significant for project honesty and future maintainer onboarding.

## 4. Architectural design choices (and the rejected alternatives)

### 4.1 Why Big Kernel Lock (not finer locks)

**Choice**: a single global ticket lock serializes every kernel
entry.

**Alternatives considered**:

| Option | Pros | Cons | Decision |
|--------|------|------|----------|
| Big Kernel Lock | Preserves single-core proof surface; one lock to verify; well-understood (Linux 2.0..2.6, seL4 initial SMP) | Worst-case 4× syscall latency under contention | **Selected** for v1.0.0 |
| Per-subsystem locks (scheduler, IPC, capability, object store) | Better contention behaviour | 4× the lock proofs; deadlock risk requires lock-ordering proofs | Deferred to v1.x |
| Lock-free RCU-style state | Best contention | Requires lock-free verified data structures; orders of magnitude more proof work | Deferred indefinitely |
| Per-CPU kernel state with cross-core IPI-only sharing | Best scalability | Total model rewrite; cross-core consistency proofs explode | Deferred to v2.x |

The BKL is a **proof-quality-preserving** choice. For a verified
microkernel, correctness dominates micro-optimization. The 4×
worst-case latency is acceptable for v1.0.0 RPi5 deployments;
optimization paths remain open for v1.x.

### 4.2 Why ticket lock (not MCS, not test-and-set)

**Choice**: ticket lock as defined in §2.2.

| Option | Pros | Cons | Decision |
|--------|------|------|----------|
| Test-and-set spinlock | Trivial implementation | No fairness; starvation possible | Rejected (liveness hazard) |
| Ticket lock | FIFO fairness; bounded wait; simple state | Cache-line contention on `serving` | **Selected**; cache contention bounded by `numCores = 4` |
| MCS lock | Cache-locality optimal | Per-acquire allocation; complex proof | Deferred to v1.x performance work |
| CLH lock | Like MCS but simpler | Per-acquire allocation | Deferred |

Ticket lock + WFE+SEV gives FIFO fairness with zero allocation.
The `serving` cache line bounces between cores under contention but
on a 4-core single-cluster L2-shared topology the cost is bounded.

### 4.3 Why hardcoded `numCores := 4`

**Choice**: at v1.0.0, `numCores = 4` is a compile-time constant
matching BCM2712.

**Alternative**: parameterize by `PlatformBinding.coreCount`.

**Rationale**:

- `Vector α numCores` requires the index to be a Nat literal or
  fixed at the type level. Parameterizing by a typeclass field
  requires generalization across `numCores : Nat` everywhere it
  appears — every theorem, every helper, every test.
- v1.0.0 targets RPi5 only. Multi-platform ports are post-1.0
  scope.
- The constant is changeable in one line of source; the
  multi-platform abstraction can be added in a single
  parameterization PR later (post-1.0).

We accept the rigidity for v1.0.0 in exchange for ~40% less proof
surface compared to a parameterized version.

### 4.4 Why explicit-ack TLB shootdown (when IS-variant alone would do)

See Note 2.7.4. Briefly: cross-cluster portability + formal anchor
+ defensive design. The explicit-ack adds ~5 SGI round-trips per
unmap, but on a 1 GHz Cortex-A76 with 4 cores, each round-trip is
< 100 ns, so total overhead is < 500 ns per shootdown — dwarfed by
the existing kernel-entry overhead.

### 4.5 Why "Vector" not "Array" for per-core fields

See discussion in §2.4 after Definition 2.4.2. The choice of
`Vector α numCores` is forced by the simultaneous requirements of
(a) compile-time index safety, (b) O(1) random access, and (c)
decidable extensional equality.

## 5. Phase plan

Each phase below lists sub-tasks with file:line targets, theorem
names, mathematical specifications, acceptance criteria, and
dependencies. Sub-task estimates: Trivial (T) < 50 LoC; Small (S)
50-200 LoC; Medium (M) 200-500 LoC; Large (L) 500-1500 LoC.

### Phase SM0 — Foundations & honesty patches (12-18 PRs)

**Goal**: land foundational types, fix documentation drift, prepare
the codebase for the larger phases by closing the smallest
correctness/honesty gaps. No runtime behavior change yet.

**Dependencies**: WS-RC closure (so we don't tangle with R0..R14).

**Mathematical specification**: no new theorems substantively; new
types (`CoreId`, `BklState`, `ConcurrencyState`, `SgiKind`) +
existence proofs (`numCores > 0`, `bootCoreId.val < numCores`,
constructor distinctness).

| Sub | Description | Files | Theorem / acceptance | Est |
|-----|-------------|-------|----------------------|-----|
| SM0.A | Add `singleCoreOperation` constructor to `ArchAssumption`. | `Architecture/Assumptions.lean` | `ArchAssumption` has 6 cases; `singleCoreOperation` is the 6th. | S |
| SM0.B | Extend `assumptionInventory` and `archAssumptionConsumer` to 6 entries. Update distinctness to C(6,2) = 15 inequalities. | `Architecture/Assumptions.lean` | `architecture_assumptions_index` total over 6 cases. `archAssumptionConsumer_distinct_6` pairwise distinctness. | S |
| SM0.C | New `SeLe4n/Kernel/Concurrency/Anchors.lean`: `@`-references of every inventory `identifier` + `sourceTheorem`. Wire into `Platform.Staged`. | `Concurrency/Anchors.lean`, `Platform/Staged.lean` | Build fails if any name doesn't resolve. | S |
| SM0.D | Inventory NoDup witness. | `Concurrency/Assumptions.lean` | `smpLatentInventory_identifiers_nodup : (smpLatentInventory.map (·.identifier)).Nodup := by decide`. | T |
| SM0.E | Define `CoreId := Fin numCores`, `numCores := 4`, `bootCoreId`, `allCores`, `allCores_length`, `allCores_nodup`. Uses `List.finRange` from Lean Std for built-in length + Nodup theorems. | new `Concurrency/Types.lean` | `numCores = 4`, `allCores_length : allCores.length = 4`, `allCores_nodup : allCores.Nodup`, `bootCoreId.val = 0`. | S |
| SM0.F | Define `BklState`, `bklHeldBy`, `Decidable bklHeldBy`. | new `Concurrency/Locks.lean` | `BklState`'s `held` constructor uniqueness; `bklHeldBy_decidable_consistent`. | S |
| SM0.G | Define `SgiKind`, `SgiKind.toIntid`, `SgiKind.toIntid_injective`. | `Concurrency/Locks.lean` | `SgiKind` has 5 constructors; `toIntid_injective` by `decide`. | S |
| SM0.H | Define `ConcurrencyState`; add `concurrency : ConcurrencyState := default` field to `SystemState`. | `Concurrency/Locks.lean`, `Model/State.lean` | `default_concurrency_bkl_unheld`. | M |
| SM0.I | Add `singleCoreOperation` `archAssumptionConsumer` mapping to `bootFromPlatform_singleCore_witness`. Verify mapping completeness. | `Architecture/Assumptions.lean` | New `archAssumptionConsumer .singleCoreOperation = `bootFromPlatform_singleCore_witness`. | T |
| SM0.J | Repoint `dev_history/` references in production sources. | `boot.S:103`, `Architecture/Assumptions.lean:333`, `CrossSubsystem.lean:3264` | grep `dev_history` in production sources returns zero hits. | T |
| SM0.K | Update `docs/spec/SELE4N_SPEC.md §6.4` from "deferred to WS-V" → "implemented in WS-SM (pre-v1.0.0)". Same in `docs/DEVELOPMENT.md:68`, `docs/gitbook/01-project-overview.md:94`. | (4 files) | grep "deferred to WS-V" in SMP context returns 0. | T |
| SM0.L | Rewrite `dev_history/audits/AUDIT_v0.29.0_DEFERRED.md::DEF-R-HAL-L20` from "RESOLVED at v0.30.10" to "PARTIALLY RESOLVED at v0.30.10 — scaffolding only; full activation tracked under WS-SM". | (1 file) | Disposition row reflects scaffolding-only state. | T |
| SM0.M | Zero `.smp_stacks` section at boot. Extend `boot.S` BSS-zero loop to cover `__smp_secondary_stacks_bottom..__smp_secondary_stack_top`. | `boot.S` | Boot trace confirms zeroed region; cargo test `secondary_stacks_zeroed_at_boot`. | S |
| SM0.N | Set `TPIDR_EL1` in `secondary_entry` to per-CPU base pointer. Add `__per_cpu_data_base` linker symbol + `static PER_CPU_DATA: [PerCpuData; 4]` (initially empty struct). | `boot.S`, `smp.rs`, `link.ld` | TPIDR_EL1 readable from `rust_secondary_main`. | M |
| SM0.O | Add `numCores` regression test ensuring `MAX_SECONDARY_CORES + 1 = numCores`. | `tests/SmpFoundationsSuite.lean`, `rust/sele4n-hal/src/smp.rs` test module | Cross-language constant pinning. | T |
| SM0.P | Update `docs/codebase_map.json` for new `Concurrency/Types.lean`, `Locks.lean`, `Anchors.lean`. | `docs/codebase_map.json` | Map regenerated; module presence verified. | T |
| SM0.Q | Update `CLAUDE.md` to record WS-SM as the active workstream after WS-RC closure. | `CLAUDE.md`, `AGENTS.md` | Workstream context section updated; byte-identical mirror. | T |
| SM0.R | CHANGELOG entry `SM0` summarizing foundations + honesty patches. | `CHANGELOG.md` | Single entry per honesty-patch landing PR. | T |

**Acceptance gate**: `test_full.sh` green; all `dev_history`
production-source references gone; foundational types compile and
have basic theorems; documentation reflects actual SMP status.

**Estimated effort**: 30–40 individually small sub-tasks across
~12–18 PRs over 3-5 weeks.

### Phase SM1 — Rust HAL completion (18-26 PRs)

**Goal**: complete the Rust HAL so that secondary cores can be
brought up, initialized fully, communicate via SGI, and the BKL
primitive exists.

**Dependencies**: SM0 closure (uses `CoreId`, `SgiKind`).

**Mathematical specification**: every new Rust function has a
docstring stating its pre/post invariants in terms of §2's
mathematical model. Unit tests verify the invariants on host stubs.

#### SM1.A — PSCI completion (3-5 PRs)

| Sub | Description | Files | Acceptance | Est |
|-----|-------------|-------|------------|-----|
| SM1.A.1 | `psci::cpu_off()` — issues `hvc #0` with `PSCI_FN_CPU_OFF`. Returns `PsciResult`. | `psci.rs` | ARM DEN0022D §5.1.5 encoding verified by test. | S |
| SM1.A.2 | `psci::affinity_info(target_mpidr)` — function id `0xC4000004`. Returns `AffinityInfoState` (ON/OFF/ON_PENDING). | `psci.rs` | DEN0022D §5.1.8 encoding. | S |
| SM1.A.3 | `psci::system_off()` — function id `0x84000008`. Power off, no return. | `psci.rs` | DEN0022D §5.1.13. | T |
| SM1.A.4 | `psci::system_reset()` — function id `0x84000009`. Reset, no return. | `psci.rs` | DEN0022D §5.1.14. | T |
| SM1.A.5 | Unit tests covering host stubs returning Success; function-id pinning; cross-function distinctness. | `psci.rs` test module | 5+ new tests pass. | S |

#### SM1.B — Ticket lock primitive (3-4 PRs)

| Sub | Description | Files | Acceptance | Est |
|-----|-------------|-------|------------|-----|
| SM1.B.1 | New `sele4n-hal/src/spinlock.rs`: `pub struct TicketLock` with `next_ticket`/`serving` fields. `new() -> Self`. Both atomics initialized to 0. | `spinlock.rs` | Construction is `const fn` for static initialization. | S |
| SM1.B.2 | `TicketLock::acquire() -> u64` per Definition 2.2.2. Returns captured ticket. | `spinlock.rs` | Theorem 2.2.5 documented in docstring; test `acquire_returns_monotonic_tickets`. | S |
| SM1.B.3 | `TicketLock::release()` per Definition 2.2.3. Issues SEV. | `spinlock.rs` | Theorem 2.2.6 documented; test `release_advances_serving_by_one`. | S |
| SM1.B.4 | `TicketLock::with_lock<F, R>(&self, f: F) -> R` RAII combinator. | `spinlock.rs` | Test `with_lock_releases_on_normal_exit`; test `with_lock_releases_on_panic` (panic-handler discipline). | M |
| SM1.B.5 | Cross-core stress test: spawn 4 host threads, each acquires + holds for fixed time + releases. Verify FIFO and mutex via shared counter. | `spinlock.rs` test module | 1M-iteration stress test passes. | M |
| SM1.B.6 | Documentation: ARM ARM citation map. LDADD/STADD/CASA semantics referenced. | `spinlock.rs` docstring | Citations to ARM ARM K11.2, K12 (LSE atomics). | T |

#### SM1.C — Secondary core full init (4-6 PRs)

| Sub | Description | Files | Acceptance | Est |
|-----|-------------|-------|------------|-----|
| SM1.C.1 | Extract `mmu::init_mmu_secondary(core_id)` from existing `mmu::init_mmu` — re-uses primary's TTBR0/TTBR1 (which are CPU-banked but point to the same kernel page tables) and re-applies SCTLR_EL1 bitmap per-core. | `mmu.rs` | Test: post-init, secondary's SCTLR_EL1 reads the canonical bitmap. | M |
| SM1.C.2 | Extract `vectors::write_vbar_el1_secondary()` — sets VBAR_EL1 to `__exception_vectors`. Identical to primary's `set_vbar`. | `boot.rs` (refactor) | Helper extracted; primary's `set_vbar` calls it. | T |
| SM1.C.3 | `gic::init_cpu_interface_secondary(core_id)` — re-uses `init_cpu_interface(GICC_BASE)` (the GIC-400 CPU interface MMIO is the same physical address for all cores, banked per-core by the GIC). | `gic.rs` | Test: post-init, secondary's GICC_CTLR shows enabled. | S |
| SM1.C.4 | `timer::init_timer_secondary(tick_hz)` — secondary's CNTKCTL_EL1 is per-core; CNTV_TVAL_EL0 arms its own timer. | `timer.rs` | Test: secondary's CNTV_CTL_EL0 shows enabled. | S |
| SM1.C.5 | Rewrite `rust_secondary_main` body: (1) `init_mmu_secondary`, (2) `write_vbar_el1_secondary`, (3) `init_cpu_interface_secondary`, (4) `init_timer_secondary`, (5) spin on `CORE_READY[core_idx]`, (6) call `lean_secondary_kernel_main(core_id)`. | `smp.rs` | Body matches docstring claim. | M |
| SM1.C.6 | Lean side: `@[export] def secondaryKernelMain (coreId : UInt64) : BaseIO Unit := ...` enters per-core idle loop (initially calls existing scheduler with `coreId`-aware entry; full work-stealing deferred to SM4). | `Platform/FFI.lean`, `Kernel/SecondaryEntry.lean` (new) | Lean `@[export]` symbol linkable. | M |

#### SM1.D — DTB cmdline + boot Phase 5 (2-3 PRs)

| Sub | Description | Files | Acceptance | Est |
|-----|-------------|-------|------------|-----|
| SM1.D.1 | New `sele4n-hal/src/cmdline.rs`: parser for DTB `/chosen/bootargs` string. Supports `key=value` and `flag`-only tokens. Returns `CmdlineConfig { smp_enabled: bool, ... }`. | `cmdline.rs` | Test: `parse_cmdline("smp_enabled=true smp_enabled=false")` returns last-wins `false`. Robust to malformed input. | M |
| SM1.D.2 | Extend `boot.rs::rust_boot_main` with Phase 5: parse DTB cmdline via `crate::cmdline::parse(dtb_ptr)`; if `smp_enabled`, set `SMP_ENABLED.store(true, Release)` and call `bring_up_secondaries()`. | `boot.rs` | Test (host-side stub): `smp_enabled=true` triggers bring-up call; `false` skips. | S |
| SM1.D.3 | Pre-Phase-5 ordering audit: BKL must be initialized BEFORE secondaries are released. Ensure `BkL::new()` static initializer executes during Phase 0 (BSS-zero already covers it; explicit `BKL.serving.store(0, Release)` before bring-up). | `boot.rs` | Test: `bkl_initialized_before_smp` ordering check. | S |

#### SM1.E — IS-variant TLB instructions (2-3 PRs)

| Sub | Description | Files | Acceptance | Est |
|-----|-------------|-------|------------|-----|
| SM1.E.1 | Add `tlb::tlbi_vmalle1is`, `tlbi_vae1is`, `tlbi_aside1is`, `tlbi_vale1is`. Same operand encoding as non-IS variants. | `tlb.rs` | 4 new functions; per-function unit tests. | S |
| SM1.E.2 | Migrate existing `tlbi_vmalle1`, `tlbi_vae1`, etc., to call IS variants on SMP builds (compile-time `cfg(feature = "smp")` or runtime check on `SMP_ENABLED`). | `tlb.rs` | All TLB ops broadcast under SMP; single-core code path unchanged (regression test). | M |
| SM1.E.3 | Lean-side FFI: extend `Platform/FFI.lean` with `@[extern "ffi_tlbi_all_is"]`, `ffi_tlbi_by_asid_is`, `ffi_tlbi_by_vaddr_is`. Add Lean wrappers in `Architecture/VSpace.lean` (`tlbFlushByASIDBroadcast`, `tlbFlushByPageBroadcast`). | `Platform/FFI.lean`, `Architecture/VSpace.lean` | Test: existing single-core TLB ops continue to pass; new IS ops compile. | M |
| SM1.E.4 | Wire all kernel `tlbFlushByASID` / `tlbFlushByPage` callers to use Broadcast variants on SMP. | (~12 callsites) | Search-and-replace; tier-3 surface anchor tests broadcast variant in use. | S |

#### SM1.F — SGI primitive (3-4 PRs)

| Sub | Description | Files | Acceptance | Est |
|-----|-------------|-------|------------|-----|
| SM1.F.1 | `gic::GICD_SGIR` constant = `GICD_BASE + 0xF00`. Documented per GIC-400 TRM §4.3.13. | `gic.rs` | Constant present; ARM TRM cited. | T |
| SM1.F.2 | `gic::send_sgi(target_mask: u8, intid: u8)` — writes GICD_SGIR with format `(0x0 << 24) | (target_mask << 16) | (intid as u32 & 0xF)`. | `gic.rs` | Test: `send_sgi(0b1110, 1)` writes `0x000E_0001` to GICD_SGIR (verified via host MMIO stub). | S |
| SM1.F.3 | `gic::send_sgi_to_self(intid)` — TargetListFilter = 10. | `gic.rs` | Test: writes `0x0200_000X`. | T |
| SM1.F.4 | `gic::send_sgi_to_all_but_self(intid)` — TargetListFilter = 01. | `gic.rs` | Test: writes `0x0100_000X`. | T |
| SM1.F.5 | SGI handler dispatch: `gic::dispatch_irq` already handles all INTIDs uniformly. Add explicit SGI-range (INTID 0..15) branch with per-SGI handler table. | `gic.rs` | SGI handlers registered via `register_sgi_handler(sgi_kind, handler)`. | M |
| SM1.F.6 | Lean FFI: `@[extern "ffi_send_sgi_to_core"]` / `ffi_send_sgi_to_all_but_self`. Lean-side dispatch routes pending-SGI queue drains through these. | `Platform/FFI.lean` | FFI symbols resolve at link time. | S |
| SM1.F.7 | Unit tests: SGI target-list filter encoding; INTID range guard; per-handler dispatch. | `gic.rs` test module | 8+ tests; cover all 4 SGI dispatch paths. | M |

#### SM1.G — Cross-core kprintln synchronization (1-2 PRs)

| Sub | Description | Files | Acceptance | Est |
|-----|-------------|-------|------------|-----|
| SM1.G.1 | Audit `UartLock::with` in `uart.rs`. Confirm CAS loop is correct under multi-core contention; replace with `TicketLock` from SM1.B if needed. | `uart.rs` | Cross-core stress test (4 cores × 1M kprintln) interleaves cleanly; no torn output. | M |
| SM1.G.2 | Per-core boot banner: each secondary's first action after init is `kprintln!("[smp] core {} ready", core_id)`. | `smp.rs` | QEMU SMP boot trace shows 4 banner lines in order. | T |

#### SM1.H — QEMU SMP test wired (1-2 PRs)

| Sub | Description | Files | Acceptance | Est |
|-----|-------------|-------|------------|-----|
| SM1.H.1 | Replace stub `test_qemu_smp_bringup.sh` with full implementation per the existing 5-step description. | `scripts/test_qemu_smp_bringup.sh` | Boots QEMU `-smp 4 -machine virt,secure=on`; UART log shows 4 cores ready; cross-core SGI test passes. | L |
| SM1.H.2 | Wire into nightly tier `test_nightly.sh`. | `scripts/test_nightly.sh` | Tier-4 includes QEMU SMP. | S |

#### SM1.J — Lean BKL FFI binding (1-2 PRs)

| Sub | Description | Files | Acceptance | Est |
|-----|-------------|-------|------------|-----|
| SM1.J.1 | `sele4n-hal::bkl::BKL: TicketLock = TicketLock::new()` static. `bkl::acquire()`, `bkl::release()` wrappers around the static. | `bkl.rs` (new) | Static initializer executes at link time (atomic zero-init). | S |
| SM1.J.2 | `#[no_mangle] pub extern "C" fn ffi_acquire_bkl(core_id: u64)`, `ffi_release_bkl(core_id: u64)`. Each calls `bkl::acquire`/`release`; the `core_id` argument is documentation (logical owner). | `bkl.rs` | Symbols `ffi_acquire_bkl` / `ffi_release_bkl` exported. | T |
| SM1.J.3 | Lean-side `@[extern "ffi_acquire_bkl"] opaque acquireBkl (coreId : UInt64) : BaseIO Unit`. Same for `releaseBkl`. | `Platform/FFI.lean` | FFI binding compiles; type checks. | T |

**SM1 acceptance gate**: cargo tests pass (~30+ new tests); QEMU
`-smp 4` boots; all 4 cores reach kernel; SGI round-trip
demonstrates inter-core communication; BKL acquire/release exposed
to Lean.

**SM1 LoC estimate**: ~2500 new Rust LoC + ~150 new Lean LoC.

### Phase SM2 — Per-core kernel state model (15-22 PRs)

**Goal**: rewrite `SchedulerState` (and related) to be per-core,
preserving the single-core proof surface via the bootCore-shim
helpers.

**Dependencies**: SM0 closure (uses `CoreId`).

**Mathematical specification**: §2.4 (per-core state encoding).
Each existing single-core theorem is migrated to be parameterized
by `c : CoreId`; default callers use `c = bootCoreId`.

#### SM2.A — Vector primitive bootstrap (1-2 PRs)

| Sub | Description | Files | Acceptance | Est |
|-----|-------------|-------|------------|-----|
| SM2.A.1 | Define `Vector α n` (if not already available from Std). | `Prelude.lean` (or use Std) | `Vector.get`, `Vector.set`, `Vector.replicate`, decidable extensionality. | M |
| SM2.A.2 | Vector helper theorems: `Vector.get_set_eq`, `Vector.get_set_ne`, `Vector.length_eq_n`. | `Prelude.lean` | 6+ helpers. | S |
| SM2.A.3 | Verify Vector compiles efficiently to runtime arrays (Lean compiler emits Array for List with length proof — confirm). | (audit) | `lake exe sele4n` runtime traces show acceptable per-core access. | T |

#### SM2.B — SchedulerState shape migration (3-5 PRs)

| Sub | Description | Files | Acceptance | Est |
|-----|-------------|-------|------------|-----|
| SM2.B.1 | Add per-core fields to `SchedulerState`: `current : Vector (Option ThreadId) numCores`, `runQueue : Vector RunQueue numCores`, `replenishQueue : Vector ReplenishQueue numCores`, `activeDomain : Vector DomainId numCores`, `domainTimeRemaining : Vector Nat numCores`, `domainScheduleIndex : Vector Nat numCores`, `lastTimeoutErrors : Vector (List (ThreadId × KernelError)) numCores`. | `Model/State.lean` | Structure compiles; all defaults initialize to single-core-equivalent values at `bootCoreId`. | L |
| SM2.B.2 | Remove the singular `current`, `runQueue`, etc., fields. | `Model/State.lean` | No single `current : Option ThreadId` remains. | S |
| SM2.B.3 | Add `currentOnCore`, `runQueueOnCore`, etc., helpers. | `Model/State.lean` | Helper defs + 7 single-field helpers. | S |
| SM2.B.4 | Add `currentOnBootCore := currentOnCore bootCoreId` and analogues for every per-core field — these are the *single-core compatibility shims*. | `Model/State.lean` | Shim defs; tests `currentOnBootCore_eq_current_old_semantics` (passing the single-core scenario). | M |
| SM2.B.5 | Document the shim discipline: every existing theorem that read `s.current` is migrated to `s.currentOnBootCore` in the same PR; new SMP theorems use `s.currentOnCore c`. | `CONTRIBUTING.md`, `Model/State.lean` docstring | Migration guide present. | T |

#### SM2.C — Proof migration: scheduler invariants (5-8 PRs)

Migration of all theorems in `Kernel/Scheduler/Invariant/*.lean`
(estimated ~50 sites) from `s.current` → `s.currentOnBootCore`,
`s.runQueue` → `s.runQueueOnBootCore`, etc. **No semantic change**;
the bootCore-shim makes this a mechanical rename that the build
verifies.

| Sub | Description | Files | Acceptance | Est |
|-----|-------------|-------|------------|-----|
| SM2.C.1 | `Scheduler/Invariant/CurrentThread.lean`: migrate ~12 theorems. | (1 file) | Build green; all theorems prove. | M |
| SM2.C.2 | `Scheduler/Invariant/RunQueue.lean`: migrate ~15 theorems. | (1 file) | Build green. | M |
| SM2.C.3 | `Scheduler/Invariant/Domain.lean`: migrate ~10 theorems. | (1 file) | Build green. | M |
| SM2.C.4 | `Scheduler/Invariant/CBS.lean`: migrate ~8 theorems on replenishment queue. | (1 file) | Build green. | M |
| SM2.C.5 | `Scheduler/Invariant/Preservation.lean`: migrate ~25 preservation lemmas (this is the heavy file). | (1 file, 3779 LoC) | Build green. | L |

Pattern for each migration:

```
-- Pre-SM2:
theorem scheduler_current_consistent (s : SystemState) :
    s.scheduler.current = some tid → ... := ...
-- Post-SM2:
theorem scheduler_current_consistent (s : SystemState) :
    s.scheduler.currentOnBootCore = some tid → ... := ...
```

#### SM2.D — Proof migration: IPC / capability / lifecycle (4-6 PRs)

Same mechanical migration for cross-subsystem theorems that read
scheduler fields.

| Sub | Files | LoC | Est |
|-----|-------|----:|-----|
| SM2.D.1 | `IPC/Operations/*.lean` (~12 callsites) | 1200 | M |
| SM2.D.2 | `Capability/Operations.lean` (~5 callsites) | 1868 | M |
| SM2.D.3 | `Lifecycle/Operations.lean` (~3 callsites) | 400 | S |
| SM2.D.4 | `Service/Operations.lean` (~2 callsites) | 300 | S |

#### SM2.E — Per-core RunQueue extensions (2-3 PRs)

| Sub | Description | Files | Acceptance | Est |
|-----|-------------|-------|------------|-----|
| SM2.E.1 | `RunQueue.empty` already exists. Confirm `Vector.replicate numCores RunQueue.empty` is decidably-equal to `Vector.mk [empty, empty, empty, empty]`. | `Scheduler/RunQueue.lean` | `decide`-proven theorem. | T |
| SM2.E.2 | Add `enqueueOnCore (s : SchedulerState) (c : CoreId) (tid : ThreadId) : SchedulerState`. | `Scheduler/Operations/Core.lean` | Per-core operation. | S |
| SM2.E.3 | Add `dequeueOnCore (s : SchedulerState) (c : CoreId) : (Option ThreadId × SchedulerState)`. | `Scheduler/Operations/Core.lean` | Per-core operation. | S |
| SM2.E.4 | Per-core wellFormed: `∀ c, (s.runQueueOnCore c).wellFormed`. | `Scheduler/Invariant/RunQueue.lean` | Witness theorem `runQueue_wellFormed_perCore`. | S |

#### SM2.F — Platform contract extension (2-3 PRs)

| Sub | Description | Files | Acceptance | Est |
|-----|-------------|-------|------------|-----|
| SM2.F.1 | Extend `PlatformBinding` typeclass with `coreCount : Nat`, `bootCoreId : Fin coreCount`, `validateCoreCount : coreCount > 0`. | `Platform/Contract.lean` | Typeclass extended; default `coreCount := numCores`. | S |
| SM2.F.2 | Update RPi5 `PlatformBinding` instance: `coreCount := 4`, `bootCoreId := ⟨0, _⟩`. | `Platform/RPi5/Contract.lean` | Decidable proofs by `decide`. | T |
| SM2.F.3 | Update Sim `PlatformBinding` instance(s). | `Platform/Sim/*.lean` | Sim instances respect contract. | T |
| SM2.F.4 | `PlatformConfig` gains `perCoreBootData : Vector PerCoreBootData coreCount` (initially empty struct; SM4 populates with idle TCBs). | `Platform/Boot.lean` | Field added; default `Vector.replicate _ default`. | S |

#### SM2.G — Boot bridge for per-core idle threads (3-5 PRs)

Each core needs an idle thread (priority 0, runnable only by the
scheduler when no other thread is available). The boot pipeline
creates `numCores` idle threads and assigns each to its core's
`currentOnCore`.

| Sub | Description | Files | Acceptance | Est |
|-----|-------------|-------|------------|-----|
| SM2.G.1 | Define `idleThreadId : CoreId → ThreadId := fun c => ⟨ObjId.ofNat (kernelObjectIdBase + c.val), _⟩`. | `Kernel/IdleThread.lean` (new) | Per-core distinct idle TIDs. | S |
| SM2.G.2 | `createIdleThread (c : CoreId) : ThreadControlBlock` — TCB with priority 0, bound to no SchedContext, runnable. | `Kernel/IdleThread.lean` | Constructor function. | S |
| SM2.G.3 | Extend `bootFromPlatform` to populate `s.scheduler.currentOnCore c := some (idleThreadId c)` for each core; insert idle TCBs into object store. | `Platform/Boot.lean` | Post-boot every core has a current thread (the idle). | M |
| SM2.G.4 | Witness theorem `bootFromPlatform_all_cores_have_idle` replacing single-core `bootFromPlatform_singleCore_witness`. The old theorem becomes a corollary: `currentOnBootCore = some (idleThreadId bootCoreId)`. | `CrossSubsystem.lean` | New theorem proven. | M |
| SM2.G.5 | Retire `bootFromPlatform_singleCore_witness` (the existential form is too weak now). Replace with `bootFromPlatform_smp_witness` proving the per-core shape. | `CrossSubsystem.lean` | Theorem retired; replacement proven. | M |
| SM2.G.6 | Update AN12-B inventory entry 7 (`architecture_singleCoreOnly_smpLatent`) and entry 8 (`bootFromPlatform_currentCore_is_zero_smpLatent`): mark `smpDischarge` as "SMP-implemented in WS-SM"; update `sourceTheorem` to point to `bootFromPlatform_smp_witness`. | `Concurrency/Assumptions.lean` | Inventory reflects SMP state. | S |

#### SM2.H — Cross-subsystem invariant update (2-3 PRs)

| Sub | Description | Files | Acceptance | Est |
|-----|-------------|-------|------------|-----|
| SM2.H.1 | Update `crossSubsystemInvariant` to add `perCoreSchedulerConsistent`: `∀ c, isValidThreadOrIdle (s.scheduler.currentOnCore c)`. | `CrossSubsystem.lean` | New conjunct; existing 12 conjuncts unchanged. | M |
| SM2.H.2 | Prove `perCoreSchedulerConsistent_holds_at_boot`. | `CrossSubsystem.lean` | Bridge theorem. | S |
| SM2.H.3 | Prove every operation preserves `perCoreSchedulerConsistent` (most are immediate since the operation only mutates `currentOnBootCore`). | (multiple files) | Closure-form preservation per op. | M |

**SM2 acceptance gate**: `lake build` (256 jobs) green; all
existing tests pass without semantic change; `test_full.sh` green;
new per-core helpers compile and have basic theorems; old
`bootFromPlatform_singleCore_witness` retired with audit trail.

**SM2 LoC estimate**: ~3000 LoC of new Lean theorems + ~1000 LoC
of mechanical migrations.

### Phase SM3 — BKL Lean integration (20-28 PRs)

**Goal**: thread the BKL acquire/release discipline through every
`@[export]` body so concurrent kernel entries are serialized.

**Dependencies**: SM1.J (Lean FFI for BKL), SM2 (per-core state).

**Mathematical specification**: §2.5 (BKL Lean encoding). Every
`@[export]` body's invariants:

```
Pre:  s.concurrency.bkl = .unheld
Mid:  s.concurrency.bkl = .held myCore
Post: s.concurrency.bkl = .unheld
```

#### SM3.A — BKL Lean state model (2-3 PRs)

| Sub | Description | Files | Acceptance | Est |
|-----|-------------|-------|------------|-----|
| SM3.A.1 | Add `currentCoreId : BaseIO CoreId` Lean shim that reads MPIDR via `@[extern "ffi_current_core_id"]`. Adds matching Rust `pub extern "C" fn ffi_current_core_id() -> u64 { current_core_id() & MPIDR_CORE_ID_MASK }` (already exists; just expose). | `Platform/FFI.lean`, `ffi.rs` | Lean reads core ID at FFI boundary. | S |
| SM3.A.2 | `acquireBkl : CoreId → BaseIO Unit` — calls `ffi_acquire_bkl coreId.val.toUInt64`; updates `kernelStateRef`'s concurrency.bkl to `.held coreId` after the FFI call returns (logical state update reflecting hardware state). | `Platform/FFI.lean` | Lean wrapper. | S |
| SM3.A.3 | `releaseBkl : CoreId → BaseIO Unit` — updates `kernelStateRef`'s concurrency.bkl to `.unheld`; calls `ffi_release_bkl coreId.val.toUInt64`. | `Platform/FFI.lean` | Lean wrapper; release-after-state-update ordering. | S |
| SM3.A.4 | `withBkl (action : CoreId → BaseIO α) : BaseIO α` combinator: gets core ID, acquires, runs action, releases (with `try-finally`-style error handling so panics still release). | `Platform/FFI.lean` | Combinator + 3 tests: normal exit, exception in action, nested-acquire-not-allowed. | M |

#### SM3.B — `@[export]` body BKL discipline (8-12 PRs, ~25 sub-tasks)

Every `@[export]` body in `FFI.lean` gains BKL bracketing. The
current count is 2 (`suspend_thread_inner`,
`syscall_dispatch_inner`); SM5 + SM4 may add more. For each:

```
@[export sele4n_suspend_thread]
def suspendThreadInner_smp (tid : UInt64) : BaseIO UInt32 := do
  withBkl fun myCore => do
    -- existing R2.A.2 logic, with currentCoreId threaded through
    let st ← getKernelState
    let result := suspendThread (ThreadId.ofUInt64 tid) st
    match result with
    | .ok s' =>
        updateKernelState (fun _ => s')
        return 0
    | .error e =>
        return KernelError.toUInt32 e
```

| Sub | Description | Files | Acceptance | Est |
|-----|-------------|-------|------------|-----|
| SM3.B.1 | Wrap `suspend_thread_inner` body in `withBkl`. | `Platform/FFI.lean` | Existing R2 tests pass; new test `suspend_thread_acquires_bkl`. | S |
| SM3.B.2 | Wrap `syscall_dispatch_inner` body in `withBkl`. | `Platform/FFI.lean` | Existing R2 tests pass; new test `syscall_dispatch_acquires_bkl`. | S |
| SM3.B.3 | New `@[export] def panicEntry`: emergency BKL release for panic paths. | `Platform/FFI.lean`, `rust panic_handler` | Panic handler calls Lean panic-entry which forcibly releases BKL. | M |
| SM3.B.4 | Audit: every existing `@[extern]` call site (Lean→Rust) that reads/writes kernel state must happen with BKL held. The `@[export]` bracketing handles this for syscalls; check timer-tick handler, IRQ handler, etc. | (multiple files) | Audit report; all kernel-state-mutating paths bracketed. | M |
| SM3.B.5 | `@[export] def handleTimerInterrupt`: timer tick on any core acquires BKL, runs `timerTickWithBudget` on that core's perCoreState, releases. | `Platform/FFI.lean` | Per-core timer ISR. | M |
| SM3.B.6 | `@[export] def handleSgiInterrupt`: SGI handler acquires BKL, drains pending-SGI queue for this core, releases. | `Platform/FFI.lean` | Per-core SGI dispatch. | M |
| SM3.B.7 | `@[export] def handleIrqInterrupt`: generic IRQ entry, acquires BKL, dispatches via existing `handleInterrupt`, releases. | `Platform/FFI.lean` | Per-core IRQ entry. | M |

#### SM3.C — BKL invariants and preservation (4-6 PRs)

| Sub | Description | Theorem name | Est |
|-----|-------------|--------------|-----|
| SM3.C.1 | `bkl_unheld_at_kernel_entry`: at the start of every `@[export]` body, BKL is unheld. | `bkl_unheld_at_kernel_entry` | S |
| SM3.C.2 | `bkl_unheld_at_kernel_exit`: at the end of every `@[export]` body, BKL is unheld. | `bkl_unheld_at_kernel_exit` | S |
| SM3.C.3 | `bkl_held_during_kernel_transition`: every transition observes BKL held by the current core. | `bkl_held_during_kernel_transition` | M |
| SM3.C.4 | `bkl_acquire_release_paired`: every acquire is followed by exactly one release on the same execution path. | `bkl_acquire_release_paired` | M |
| SM3.C.5 | `bkl_mutex_property`: `BklProperty` (Definition 2.1.2) is preserved by every kernel transition. | `bkl_mutex_property` | M |
| SM3.C.6 | `kernelStateRef_safe_under_bkl`: `kernelStateRef` reads and writes happen with BKL held. (Encoded as a structural property of every `@[export]` body.) | `kernelStateRef_safe_under_bkl` | L |

#### SM3.D — IRQ / exception entry BKL discipline (3-5 PRs)

The kernel takes interrupts on any core. Each interrupt is a kernel
entry and must acquire BKL.

| Sub | Description | Files | Acceptance | Est |
|-----|-------------|-------|------------|-----|
| SM3.D.1 | `trap.rs::handle_irq` — wrap the Lean kernel call (`ffi_handle_irq_dispatch(intid, core_id)`) so BKL acquire happens at the FFI boundary. | `trap.rs` | IRQ handler acquires BKL before kernel work. | M |
| SM3.D.2 | `trap.rs::handle_synchronous_exception` — same. | `trap.rs` | Synchronous exception handler acquires BKL. | M |
| SM3.D.3 | SError handler `trap.rs::handle_serror` — same. | `trap.rs` | SError acquires BKL. | S |
| SM3.D.4 | Nested-IRQ defense: if an IRQ arrives while BKL is held by the same core, the IRQ is masked (we run interrupts-disabled inside kernel by AG5-G). Document the explicit ordering: BKL acquire → interrupts disable → kernel work → interrupts restore → BKL release. | `interrupts.rs`, `Platform/FFI.lean` | Ordering documented; nested-IRQ test. | M |

#### SM3.E — Panic discipline (2-3 PRs)

| Sub | Description | Files | Acceptance | Est |
|-----|-------------|-------|------------|-----|
| SM3.E.1 | Rust `panic_handler` calls `bkl::force_release()` before halting. This unblocks waiters; remaining cores can then take their own panic path. | `panic.rs` | Panic test: core A panics with BKL held, core B can still acquire (and panic too if it tries to use broken state). | M |
| SM3.E.2 | Halt-all SGI: when one core panics, it sends `SgiKind.haltAll` to all others; they enter parking loops without entering the kernel further. | `gic.rs`, `panic.rs` | Multi-core panic test: all 4 cores reach the halt loop. | M |

**SM3 acceptance gate**: every kernel entry path goes through BKL;
no race-able `kernelStateRef` access; cargo + Lean tests verify
discipline.

### Phase SM4 — Per-core scheduler (22-30 PRs)

**Goal**: scheduling decisions, run-queue management, time-slicing,
and CBS replenishment all operate per-core, with cross-core
notifications via SGI.

**Dependencies**: SM2, SM3, SM1.F.

**Mathematical specification**:

For each existing scheduler theorem `T(s)` referencing `s.runQueue`
or `s.current`, the SMP analogue is `∀ c : CoreId, T(s, c)` with
`s.runQueueOnCore c` substituted.

The cross-core scheduling decision rule (default policy at v1.0.0):

```
enqueueRunnable(s, tid):
  -- Determine target core by affinity, else by load balancing
  let c := match tcb.cpuAffinity with
           | some core => core
           | none      => leastLoadedCore(s)
  s.scheduler.runQueueOnCore c .insert tid
```

#### SM4.A — chooseThread per-core (3-5 PRs)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM4.A.1 | `chooseThreadOnCore (s : SystemState) (c : CoreId) : Option ThreadId` — selects highest-priority runnable thread from `s.scheduler.runQueueOnCore c`. | `chooseThreadOnCore_selects_highest` | M |
| SM4.A.2 | Each core's `chooseThreadOnCore` ignores other cores' run queues. | `chooseThreadOnCore_perCore_independence` | S |
| SM4.A.3 | Migrate the global `chooseThread` to call `chooseThreadOnCore bootCoreId` (boot-core compat). | (refactor) | Existing tests pass. | T |
| SM4.A.4 | `chooseThreadOnCore_preserves_wellFormed`. | `chooseThreadOnCore_preserves_wellFormed` | M |

#### SM4.B — switchToThread per-core (4-6 PRs)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM4.B.1 | `switchToThreadOnCore (s : SystemState) (c : CoreId) (tid : ThreadId) : Result SystemState` — set `currentOnCore c := some tid`, validate runnable. | `switchToThreadOnCore_sets_current` | M |
| SM4.B.2 | Cross-subsystem: `runQueueOnCore_excludes_currentOnCore` — current thread is NOT in its own core's run queue (existing invariant generalized). | `runQueueOnCore_excludes_currentOnCore` | M |
| SM4.B.3 | Preempt-self-to-runnable: when `switchToThreadOnCore` evicts the previous current thread, it goes back to the same core's run queue. | `switchToThreadOnCore_preempts_previous` | M |
| SM4.B.4 | If the target thread is on a different core's run queue (migration scenario), `switchToThreadOnCore` returns `.error .threadOnDifferentCore`. (Migration is post-1.0 capability operation.) | `switchToThreadOnCore_rejects_remote` | M |

#### SM4.C — Cross-core wake via SGI (5-8 PRs)

This is the most novel work in SM4.

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM4.C.1 | `enqueueRunnableOnCore (s : SystemState) (c : CoreId) (tid : ThreadId) : SystemState` — add tid to `c`'s run queue. | `enqueueRunnableOnCore_wellFormed` | M |
| SM4.C.2 | `wakeThread (s : SystemState) (tid : ThreadId) : SystemState × List PendingSgi` — determines target core via TCB.cpuAffinity (or bootCoreId default); enqueues; if target ≠ executing core, returns a `(target, .reschedule)` SGI to send. | `wakeThread_emits_sgi_if_remote` | L |
| SM4.C.3 | The `@[export]` body sending the SGI: after BKL state mutation completes, call `ffi_send_sgi_to_core(target_core, sgi_intid)` BEFORE releasing BKL. (The SGI is sent under BKL so the post-state is consistent before the target reacts.) | (multiple) | Ordering: state update → SGI send → BKL release. | M |
| SM4.C.4 | SGI handler on target core: `handleSgiInterrupt` (called under BKL via the IRQ-entry envelope of SM3.B.7) reads `pendingSgis[myCore]` from the post-state (BKL release-acquire pairing guarantees post-state visibility — Theorem 2.3.2), drains the queue, processes each entry; for `.reschedule`, re-runs `chooseThreadOnCore myCore` and switches. | `Platform/FFI.lean` | Cross-core wake round-trip works. | L |
| SM4.C.5 | `wakeThread_lossless`: every wakeThread call eventually causes the target thread to run on target core (modulo higher-priority work). | `wakeThread_lossless` | L |

#### SM4.D — Per-core timer tick (3-5 PRs)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM4.D.1 | Each core has its own ARM Generic Timer (CNTV_TVAL_EL0) firing locally. The timer ISR on core c calls `timerTickOnCore c`. | (HAL + Lean) | Timer fires per-core. | M |
| SM4.D.2 | `timerTickOnCore (s : SystemState) (c : CoreId) : SystemState` — decrements `c`'s `domainTimeRemaining`; handles CBS replenishment for threads on `c`; emits preemption if higher-pri thread becomes runnable on `c`. | `timerTickOnCore_advances_per_core` | L |
| SM4.D.3 | Cross-core CBS replenishment: a thread on core c whose budget fires can release a higher-priority thread on a different core; SM4.C handles the cross-core wake. | (proof) | `cbsReplenish_can_wake_remote_core` | L |
| SM4.D.4 | WCRT bound update: `wcrt_bound_rpi5_smp` extending R5.wcrt_bound_rpi5 with the 4× BKL factor (Corollary 2.2.9). | `wcrt_bound_rpi5_smp` | L |

#### SM4.E — Per-core idle threads (2-3 PRs)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM4.E.1 | The `bootFromPlatform` extension from SM2.G installs idle TCBs per core. SM4.E makes the scheduler aware that idle threads never leave their core. | `idleThread_core_locality` | M |
| SM4.E.2 | `idleThread_priority_zero`: idle has priority 0 (lowest). Never selected if any other thread is runnable on the same core. | `idleThread_priority_zero` | S |
| SM4.E.3 | `chooseThreadOnCore_always_succeeds`: every core always has at least the idle thread as a fallback. | `chooseThreadOnCore_always_succeeds` | M |

#### SM4.F — Priority Inheritance per-core (4-6 PRs)

PIP propagation is per-core under BKL (existing model already
discrete; just needs cross-core wake).

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM4.F.1 | `computeMaxWaiterPriority` already takes a state; under SMP it reads per-core fields where applicable. | (refactor) | Existing R5 theorems pass. | M |
| SM4.F.2 | If a PIP boost causes a thread on core c' to become runnable while the chain is on core c, emit `.reschedule` SGI to c'. | (`Scheduler/PriorityInheritance/*.lean`) | Cross-core PIP works. | L |
| SM4.F.3 | `pipBoost_perCore_consistent`. | `pipBoost_perCore_consistent` | M |

#### SM4.G — Domain scheduling per-core (3-5 PRs)

Domains were system-wide in the single-core model. Per-core, the
choice is: (a) system-wide active domain (all cores in the same
domain at once), or (b) per-core active domain.

| Sub | Description | Choice | Est |
|-----|-------------|--------|-----|
| SM4.G.1 | Decision: per-core active domain. Each core independently advances its own domain schedule. The same `domainSchedule` table is shared (config-only); the per-core `domainScheduleIndex` and `domainTimeRemaining` track each core's position. | (design) | Documented decision; rationale: maximises parallelism while still bounding per-domain CPU share. | M |
| SM4.G.2 | `activeDomainOnCore (c : CoreId)` returns the core's current domain. | (def + theorem) | `activeDomainOnCore_isInDomainSchedule` | M |
| SM4.G.3 | `advanceDomainOnCore (c : CoreId)` rotates that core's `domainScheduleIndex`. | (def) | `advanceDomainOnCore_cyclic` | M |
| SM4.G.4 | `chooseThreadOnCore` respects per-core active domain. | (proof) | `chooseThreadOnCore_inActiveDomain` | M |

#### SM4.H — Per-core invariant suite (3-5 PRs)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM4.H.1 | `currentOnCore_validThreadIfSome (c : CoreId)`. | `currentOnCore_validThreadIfSome` | S |
| SM4.H.2 | `runQueueOnCore_wellFormed (c : CoreId)`. | `runQueueOnCore_wellFormed` | S |
| SM4.H.3 | `schedContextRunQueueConsistent_perCore`. | `schedContextRunQueueConsistent_perCore` | M |
| SM4.H.4 | Composition: `schedulerInvariant_perCore` aggregates the 3 per-core invariants in H.1..H.3. | `schedulerInvariant_perCore` | M |
| SM4.H.5 | Cross-core: `schedulerInvariant_perCore_pairwise` — different cores' invariants are independent (no cross-core run-queue overlap). | `schedulerInvariant_perCore_pairwise` | M |

**SM4 acceptance gate**: 4-thread workload running on 4 cores;
cross-core preempt works; per-core timer ticks advance per-core
domain state; PIP cross-core works; idle threads per core.

### Phase SM5 — Cross-core IPC (15-22 PRs)

**Goal**: endpoint call/send/recv, notifications, and reply across
cores work correctly under BKL with SGI wake.

**Dependencies**: SM3, SM4.

**Mathematical specification**: existing IPC invariants
(`ipcInvariantFull`, 15 conjuncts post-R4) remain valid under BKL
because every IPC transition is atomic (BKL-bracketed). Cross-core
WAKE requires emitting `.reschedule` SGI when receiver is on a
different core.

#### SM5.A — Endpoint call across cores (3-5 PRs)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM5.A.1 | `endpointCall` (existing) — under BKL, the operation is atomic. The sender's core may be different from the receiver's. When the receiver wakes (transitions from blocked → runnable), the wake routes through `wakeThread` which emits SGI if the receiver is on a different core. | (refactor) | Existing R1 tests pass; `endpointCall_emits_sgi_if_remote_receiver`. | M |
| SM5.A.2 | `endpointCall_perCore_blocking`: caller blocks on caller's core; reply unblocks caller via wake (same SGI mechanism). | `endpointCall_perCore_blocking` | M |
| SM5.A.3 | `endpointCall_call_path_NI`: cross-core call doesn't leak info beyond what single-core call leaks. | (extends R1) | M |

#### SM5.B — Notification across cores (3-4 PRs)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM5.B.1 | `notificationSignal` (existing) — under BKL, signals at most one waiting thread; wake the thread on its core. | (refactor) | Existing tests pass. | M |
| SM5.B.2 | `notificationSignal_remote_wake`: if the waiting thread is on core c' ≠ executing core, emit SGI to c'. | `notificationSignal_remote_wake` | M |
| SM5.B.3 | Multi-waiter case (binary semaphore): only one waker leaves the queue; remaining waiters stay blocked. | (existing inv) | S |

#### SM5.C — Reply path across cores (3-5 PRs)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM5.C.1 | `endpointReply` (existing) — reply wakes caller; caller may be on different core. | (refactor) | M |
| SM5.C.2 | Donation chain across cores: donor on c₁ donates SC to receiver on c₂; the SC's bound core can change. SchedContext-bound-thread-domain invariant (R5.G) extends per-core. | `donation_perCore_consistent` | L |
| SM5.C.3 | Reply receive on caller's core after wake: ensure the reply payload is delivered to the right TCB. | `endpointReply_perCore_delivery` | M |

#### SM5.D — IPC across-core invariant bundle (2-3 PRs)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM5.D.1 | `ipcInvariantFull_perCore`: 15-conjunct bundle restricted to per-core endpoint/notification views; identical semantics under BKL serialization. | `ipcInvariantFull_perCore` | M |
| SM5.D.2 | All 6 per-operation preservation theorems (`endpointSendDual`, `endpointReceiveDual`, `endpointCall`, `endpointReplyRecv`, `notificationSignal`, `notificationWait`) carry through. | (multiple) | L |

#### SM5.E — Cancellation across cores (2-3 PRs)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM5.E.1 | `cancelIpcBlocking` (existing): under BKL, atomically removes the thread from its endpoint queue. The cancellation happens on the cancelling core; the cancelled thread's TCB may be associated with a different core. | (refactor) | M |
| SM5.E.2 | `cancelDonation` (existing R5.A): same atomic semantics under BKL. | (refactor) | M |

#### SM5.F — Tests + fixtures (2-3 PRs)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM5.F.1 | New `tests/SmpIpcSuite.lean`: 8-12 SMP-specific IPC scenarios (sender on c₀, receiver on c₁; notification across cores; reply across cores; cancellation across cores). | `tests/SmpIpcSuite.lean` | L |
| SM5.F.2 | New fixture `tests/fixtures/smp_ipc_4core.expected`. | (1 file) | S |

**SM5 acceptance gate**: 2-thread cross-core IPC works; 4-thread
SMP rendezvous test passes; existing IPC invariants hold per-core.

### Phase SM6 — TLB / cache shootdown (12-18 PRs)

**Goal**: page unmaps, ASID retire, retype-with-page-free operations
all invalidate translations on every core. CRITICAL for closing
SMP-C4.

**Dependencies**: SM1.E (IS-variant TLB ops), SM1.F (SGI primitive),
SM3 (BKL).

**Mathematical specification**: §2.7 (shootdown protocol).

#### SM6.A — Lean-side shootdown descriptor (2-3 PRs)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM6.A.1 | `TlbShootdownDescriptor` struct: `(asid : ASID, vaddr : Option VAddr)` (vaddr=none means all-asid flush). | `Architecture/TlbShootdown.lean` (new) | M |
| SM6.A.2 | `pendingShootdowns : Vector (List TlbShootdownDescriptor) numCores` — per-core queue, similar to pending SGI but specialized. | `Architecture/TlbShootdown.lean` | M |
| SM6.A.3 | `enqueueShootdown (initiator : CoreId) (targets : List CoreId) (desc : TlbShootdownDescriptor)`. | `Architecture/TlbShootdown.lean` | M |
| SM6.A.4 | `drainShootdowns (c : CoreId) : List TlbShootdownDescriptor` — called from SGI handler on c. | `Architecture/TlbShootdown.lean` | M |

#### SM6.B — Shootdown protocol implementation (3-5 PRs)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM6.B.1 | `tlbShootdownLocal (asid, vaddr)`: this core executes `tlbi vaae1is, vaddr ; dsb ish ; isb`. | `Architecture/TlbShootdown.lean`, `Architecture/VSpace.lean` | M |
| SM6.B.2 | `tlbShootdownBroadcast (initiator, targets, asid, vaddr)`: enqueue descriptor on each target, send `.tlbShootdownReq` SGI, initiate local shootdown, wait for ack via `shootdownAck` Vector. | `Architecture/TlbShootdown.lean` | L |
| SM6.B.3 | SGI handler for `.tlbShootdownReq`: drain queue, execute local TLBI for each, set ack flag, return. | `Platform/FFI.lean` SGI dispatch | L |
| SM6.B.4 | `tlbShootdownBroadcast_invalidatesAllCores` theorem. | (proof) | L |
| SM6.B.5 | Wire all unmap callers (`vspaceMapPageCheckedWithFlush`, `vspaceUnmapPage`, `retypeFromUntyped` with page free) to use Broadcast variant. | (~8 callsites) | M |

#### SM6.C — Cache maintenance broadcast (2-3 PRs)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM6.C.1 | I-cache invalidation on code modification (rare; almost no code paths modify code at runtime in seLe4n) — use `ic_ialluis` (already exists in HAL). | `cache.rs`, `Architecture/CacheModel.lean` | S |
| SM6.C.2 | D-cache by VA already operates at PoC (Point of Coherency, system-wide) — no broadcast needed (ARM ARM B2.7.5). Document this in `CacheModel.lean`. | `Architecture/CacheModel.lean` docstring | T |
| SM6.C.3 | Cross-core DC maintenance: only needed for DMA-coherent buffers. Out of scope (DMA driver subsystem is post-1.0). | (documentation) | T |

#### SM6.D — Per-core TLB model (3-5 PRs)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM6.D.1 | Extend `TlbState` (existing in `Architecture/TlbModel.lean`) to `Vector TlbState numCores`. | (model) | M |
| SM6.D.2 | `tlbShootdown_invalidatesAllCores`: post-broadcast, every core's TLB has the entry removed. | `tlbShootdown_invalidatesAllCores` | L |
| SM6.D.3 | `tlbInvalidationConsistent_perCore`: per-core invariant relating page-table state to TLB state. | `tlbInvalidationConsistent_perCore` | L |

#### SM6.E — Tests (2-3 PRs)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM6.E.1 | `tests/SmpTlbShootdownSuite.lean`: unmap-then-read-on-remote-core scenario; verify protocol completes. | `tests/SmpTlbShootdownSuite.lean` | L |
| SM6.E.2 | QEMU integration: shootdown test under `-smp 4`. | `scripts/test_qemu_smp_shootdown.sh` | M |

**SM6 acceptance gate**: unmap-then-reuse a page on different
cores; verify no stale translation observed on remote cores;
theorem `tlbShootdown_invalidatesAllCores` proven; closes SMP-C4.

### Phase SM7 — Information flow under SMP (12-18 PRs)

**Goal**: extend the NI proofs to per-core observers; document new
covert channels (BKL contention timing) honestly.

**Dependencies**: SM2, SM4.

**Mathematical specification**: §2.8 (per-core observer model).

#### SM7.A — Per-core observable state (3-4 PRs)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM7.A.1 | `ObservableState.onCore (c : CoreId) (L : SecurityLabel) (s : SystemState) : ObservableState` — per-core projection. | `InformationFlow/Projection.lean` | M |
| SM7.A.2 | `onCore_isProjection_of_globalProjection`: composition property — per-core projection is a refinement of the global projection. | (theorem) | M |
| SM7.A.3 | Per-core observable state is decidable. | (instance) | S |

#### SM7.B — Per-core NI proofs (4-6 PRs)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM7.B.1 | `nonInterference_perCore`: existing NI proof generalized to per-core observers. | `nonInterference_perCore` | L |
| SM7.B.2 | `crossCoreNonInterference`: transitions on core c' don't change ObservableState.onCore c L unless they modify shared, L-observable state. | `crossCoreNonInterference` | L |
| SM7.B.3 | Per-core NI for each of the 32 `kernelOperationNi` constructors. | (multiple) | L |

#### SM7.C — BKL contention covert channel (2-3 PRs)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM7.C.1 | Document `acceptedCovertChannel_bklContention` in `InformationFlow/Projection.lean`: when core c spins on BKL acquire, it can measure how long another core holds the lock; this is a timing side channel observable to any thread on c. | `InformationFlow/Projection.lean` | M |
| SM7.C.2 | Mitigation note: under WS-W (CCA/MPAM partitioning), BKL contention can be partitioned by partition assignment. v1.0.0 documents the channel; v1.x narrows it. | (documentation) | S |
| SM7.C.3 | Update `enforcementBoundaryExtended` to 23+ entries (V6-L was 22). | `InformationFlow/Policy.lean` | S |

#### SM7.D — Per-core declassification audit (2-3 PRs)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM7.D.1 | `DeclassificationEvent` extended with `originatingCore : CoreId`. | (record extension) | M |
| SM7.D.2 | Audit trail records cross-core declassification chains: a thread on c₁ may declassify state observed on c₂. | (theorem) | M |

#### SM7.E — Tests (1-2 PRs)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM7.E.1 | `tests/SmpInformationFlowSuite.lean`: per-core NI scenarios; BKL contention timing test (positive — channel exists). | `tests/SmpInformationFlowSuite.lean` | L |

**SM7 acceptance gate**: NI proofs go through per-core; BKL channel
documented; declassification trail extends per-core.

### Phase SM8 — Documentation, tests, version closure (8-12 PRs)

**Goal**: complete documentation sync for v1.0.0 SMP release.

#### SM8.A — Documentation sync (3-4 PRs)

Per CLAUDE.md "Documentation rules", when behavior or theorems
change, update in same PR:

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM8.A.1 | `docs/spec/SELE4N_SPEC.md §6.4` rewritten for SMP. New subsections 6.4.1 SMP architecture, 6.4.2 boot sequence, 6.4.3 per-core invariants, 6.4.4 cross-core IPC, 6.4.5 TLB shootdown protocol, 6.4.6 BKL discipline. | (1 file, ~500 LoC added) | L |
| SM8.A.2 | New `docs/gitbook/16-smp-architecture.md`. | (1 file, ~300 LoC) | M |
| SM8.A.3 | Update `docs/gitbook/01-project-overview.md` and `docs/gitbook/15-rust-syscall-wrappers.md` for SMP. | (2 files) | S |
| SM8.A.4 | Update `README.md` metrics + SMP capability claim. Sync 10 i18n READMEs. | (11 files) | M |
| SM8.A.5 | Update `docs/DEVELOPMENT.md` with WS-SM closure. | (1 file) | S |
| SM8.A.6 | Update `docs/CLAIM_EVIDENCE_INDEX.md` with WS-SM phase entries. | (1 file) | M |
| SM8.A.7 | Update `docs/WORKSTREAM_HISTORY.md` with WS-SM portfolio summary. | (1 file) | L |
| SM8.A.8 | Regenerate `docs/codebase_map.json`. | (1 file) | T |
| SM8.A.9 | Update `scripts/website_link_manifest.txt` for new SMP-related paths. | (1 file) | S |

#### SM8.B — Test suite completion (2-4 PRs)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM8.B.1 | `tests/SmpSchedulerSuite.lean` (~600 LoC). | (1 file) | L |
| SM8.B.2 | `tests/SmpIpcSuite.lean` (~500 LoC). | (1 file) | L |
| SM8.B.3 | `tests/SmpCapabilitySuite.lean` (~400 LoC). | (1 file) | M |
| SM8.B.4 | `tests/SmpTlbShootdownSuite.lean` (~400 LoC). | (1 file) | M |
| SM8.B.5 | `tests/SmpInformationFlowSuite.lean` (~400 LoC). | (1 file) | M |
| SM8.B.6 | `tests/fixtures/smp_4core_boot.expected` (deterministic boot trace). | (1 file) | M |
| SM8.B.7 | New tier `scripts/test_tier4_smp.sh` covering all SMP suites. | (1 file) | M |
| SM8.B.8 | Wire QEMU `-smp 4` integration into nightly. | `scripts/test_nightly.sh` | S |

#### SM8.C — Version bump to v1.0.0 (1 PR)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM8.C.1 | Bump `lakefile.toml::version` from current → `1.0.0`. Sync `README.md`, `CHANGELOG.md`, `CLAUDE.md`, `docs/spec/SELE4N_SPEC.md`, `rust/Cargo.toml`, `rust/sele4n-hal/src/boot.rs::KERNEL_VERSION`, 10 i18n READMEs, `docs/codebase_map.json`. | (~20 files) | M |

#### SM8.D — AN12-B inventory retire / rewrite (1 PR)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM8.D.1 | Each `smpLatentInventory` entry's `smpDischarge` is now "SMP-implemented in WS-SM"; each `sourceTheorem` points to the SMP analogue. The inventory transitions from "latent" to "discharged". Optionally rename to `smpDischargedInventory` for honesty. | `Concurrency/Assumptions.lean` | M |
| SM8.D.2 | The 8-entry size witness is retained; the inventory is now historical-doc + ongoing-anchor for the discharged-property witnesses. | `Concurrency/Assumptions.lean` | T |

#### SM8.E — CHANGELOG closure (1 PR)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM8.E.1 | `CHANGELOG.md` v1.0.0 entry: full WS-SM portfolio summary; closes 5 CRITICAL + 4 HIGH + 7 MEDIUM + 5 LOW findings from this audit. | `CHANGELOG.md` | M |

#### SM8.F — Archive WS-RC audit artefacts (1 PR)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM8.F.1 | Per `docs/audits/README.md` lifecycle: archive WS-RC `AUDIT_v0.30.11_*` files to `docs/dev_history/audits/` once v1.0.0 cuts. | (file moves) | S |
| SM8.F.2 | Move this SMP audit (`docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md`) to `docs/dev_history/planning/` once WS-SM closes. | (1 file move) | T |
| SM8.F.3 | Update `scripts/website_link_manifest.txt` for archived locations. | (1 file) | T |

**SM8 acceptance gate**: v1.0.0 release ships with: bootable
verified SMP microkernel on RPi5; full documentation; all tests
green at all tiers; CHANGELOG complete; archive policy honored.

## 6. Cross-subsystem impact matrix

Approximate proof rewrite cost under WS-SM (assuming BKL +
bootCore-shim discipline preserves single-core proofs):

| Subsystem | Files | Existing LoC | New LoC | Migration LoC | Notes |
|-----------|------:|-------------:|--------:|--------------:|-------|
| Concurrency | 1 (now 4-5) | 228 | ~600 | 0 | New phase-foundation modules |
| Scheduler | 22 | ~7000 | ~1500 | ~800 | Per-core fields rewrite; per-core invariants; cross-core wake |
| IPC | 35 | ~12000 | ~600 | ~400 | BKL bracketing; cross-core wake on signal/call |
| Capability | 18 | ~5500 | ~150 | ~200 | Mostly BKL-bracketed; no structural change |
| Lifecycle | 6 | ~1500 | ~100 | ~100 | Cleanup paths BKL-bracketed |
| Service | 4 | ~1500 | ~50 | ~50 | Registry under BKL |
| Architecture | 14 | ~6000 | ~800 | ~300 | TLB shootdown; per-core IRQ; SGI dispatch |
| InformationFlow | 12 | ~6000 | ~700 | ~400 | Per-core observer; cross-core NI |
| RobinHood / RadixTree | 6 | ~3500 | 0 | 0 | Pure functional; BKL-protected |
| Platform | 17 | ~5000 | ~500 | ~150 | PlatformBinding extension; per-core boot data |
| CrossSubsystem | 1 | 3309 | ~500 | ~200 | Retire singleCore witness; add perCore consistency conjunct |
| **Totals** | **136** | **~51500** | **~5500** | **~2600** | New theorems + migration |

Total new proof + code: ~8100 LoC across ~136 files.

For scale: WS-RC R4 closeout added ~1900 LoC; WS-RC R5 deferred
completion added ~616 LoC. WS-SM is roughly 4× R4+R5 size — a
substantial but tractable workstream.

## 7. Verification strategy

### 7.1 What we prove

| Property | Proof technique | Phase |
|----------|-----------------|-------|
| BKL mutex (Thm 2.2.5) | Structural — uses `AtomicU64::fetch_add` semantics from rust documentation; treated as axiom of the hardware (cited ARM ARM K11) | SM3.C |
| BKL FIFO (Thm 2.2.6) | Same | SM3.C |
| BKL release-acquire (Thm 2.3.2) | Same | SM3.C |
| Per-core invariant preservation | Migration of existing closure-form proofs | SM2.C, SM2.D |
| Cross-core IPC delivery (Thm 2.6.3) | Atomic-append + BKL serialization | SM5.A.1 |
| TLB shootdown completeness (Thm 2.7.3) | Protocol-level — explicit ack invariant | SM6.B.4 |
| Per-core NI (Thm 2.8.3) | Generalized projection composition | SM7.B |
| WCRT under BKL (Cor 2.2.9) | Worst-case analysis on ticket counter advance | SM4.D.4 |

### 7.2 What we assume (axioms)

The WS-SM **axiom budget is 0**. Hardware primitives (atomic
operations, IS-variant TLBIs, MMU coherence) are *assumptions* —
not axioms in the Lean sense — but each is documented with an ARM
ARM citation in the corresponding module's docstring. We do NOT
add `axiom` declarations to Lean source; instead, hardware
properties enter the proof surface via FFI's opaque declarations
(`@[extern]`) whose Rust implementations are reviewed for
correctness against ARM ARM.

This matches seL4's approach: hardware primitives are trusted at
the assumption level (cited in the spec), not axiomatized in the
proof assistant.

### 7.3 Testing tiers under SMP

| Tier | What it checks | SMP additions |
|------|----------------|---------------|
| Tier 0 (hygiene) | sorry/axiom/native_decide, etc. | Confirm 0 axioms added |
| Tier 1 (build) | All modules compile | New SMP modules compile |
| Tier 2 (trace) | Deterministic trace fixture | `smp_4core_boot.expected` |
| Tier 3 (invariant) | Surface anchor #checks | Per-core invariant anchors |
| Tier 4 (nightly) | QEMU `-smp 4` boot, multi-core scenarios | All SMP suites; cross-core IPC; TLB shootdown |

### 7.4 Liveness under contention

Define `T_cs` as the WCRT of a single kernel transition (the time
from BKL acquire to BKL release on one core) and `T_acq` as the
WCRT of BKL acquisition (the spin time before serving equals the
captured ticket).

**Theorem 7.4.1** (Syscall WCRT under BKL). For a kernel running
under BKL on `numCores` cores,

    WCRT(syscall) = T_acq + T_cs ≤ numCores × T_cs

**Proof.** By Theorem 2.2.8, `T_acq ≤ (numCores − 1) × T_cs`. The
syscall is a BKL-acquire followed by the kernel transition (T_cs)
followed by BKL-release (constant time absorbed into T_cs's
upper bound). Sum: `T_acq + T_cs ≤ numCores × T_cs`. □

**Concrete bound for RPi5**. R5's `wcrt_bound_rpi5` establishes
`T_cs ≤ B_cs` for some concrete bound `B_cs` derived from the
canonical config's largest kernel transition (typically the
deepest CDT revoke or the longest IPC capability-transfer loop).
The SMP analogue:

    wcrt_bound_rpi5_smp : ∀ syscall, WCRT(syscall) ≤ 4 × B_cs

For the canonical config's `B_cs ≈ 250 µs` (an order-of-magnitude
estimate; the precise constant is dictated by the CDT depth bound
`maxCdtDepth = 65536` and the per-step CDT operation cost), the
SMP bound is `≈ 1 ms` worst case. This comfortably fits within
the 1-ms timer tick budget.

**Note**: WCRT is an *upper* bound. Average-case syscall latency
is single-core T_cs when contention is low (likely true for most
workloads). We do not prove average-case bounds; the bounded-wait
property suffices for hard real-time guarantees.

## 8. Risk inventory

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| BKL contention dominates scheduler latency | MEDIUM | MEDIUM (real-time deadlines slip) | WCRT proven bounded; v1.x performance work introduces finer locks |
| Cross-core wake SGI lost | LOW | HIGH (thread starvation) | GIC SGI delivery is hardware-guaranteed; ack protocol confirms |
| TLB shootdown deadlock (initiator waits forever) | LOW | HIGH (kernel hang) | Bounded WFE in ack loop; timeout reverts to local-only TLBI |
| Secondary core wakes into broken MMU state | ZERO (SM1.C fully initializes) | CRITICAL | SM1.C completes init before any kernel work |
| BKL acquire / release imbalance (lock leak) | LOW | CRITICAL | RAII `with_bkl` combinator; static analysis (`#[must_use]` on acquire result) |
| Vector indexing out of bounds | ZERO (Fin numCores) | — | Type-system guarantee; no runtime check needed |
| Memory ordering violation between cores | LOW | HIGH | ARMv8 release/acquire semantics; explicit `dsb ish` at protocol boundaries |
| Per-core idle thread interactions with PIP | LOW | MEDIUM | Idle threads have priority 0; never participate in PIP boost |
| Test coverage gap for cross-core scenarios | MEDIUM | MEDIUM (latent bugs ship) | SM8.B requires explicit cross-core suites; QEMU `-smp 4` mandatory |
| WS-SM doesn't fit in pre-1.0 timeline | MEDIUM | HIGH (delay v1.0.0) | Phased delivery — each SM-phase is independently shippable; if needed, freeze at any phase and ship as v1.0.0-rcN |

## 9. Timeline

**Prerequisite implication for WS-RC**: the current `CLAUDE.md`
release path has WS-RC closing at v1.0.0 (R2..R6 portion). To
accommodate WS-SM landing pre-v1.0.0, **WS-RC must close at some
v0.31.x version (not v1.0.0)**. The mechanical change is small —
WS-RC's R2..R6 phases retarget their "version bump" sub-tasks
from v1.0.0 to v0.31.last. The substance of WS-RC is unchanged;
only the closing version is moved. WS-SM then takes over the
v1.0.0 release-cut role. This is the single CLAUDE.md edit
required before SM0 opens — recorded as Open Question #2.

WS-RC closure → WS-SM open at the v0.31.x → v0.32.0 boundary.

| Phase | Releases | Estimated calendar |
|-------|----------|--------------------|
| SM0 | v0.32.0 → v0.32.x | 3-5 weeks |
| SM1 || SM2 | v0.33.0 → v0.40.x | 8-12 weeks (parallel) |
| SM3 | v0.41.0 → v0.45.x | 6-10 weeks |
| SM4 | v0.46.0 → v0.55.x | 10-14 weeks |
| SM5 | v0.56.0 → v0.62.x | 5-8 weeks |
| SM6 | v0.63.0 → v0.70.x | 5-8 weeks (parallel with SM5 partially) |
| SM7 | v0.71.0 → v0.78.x | 5-8 weeks (parallel with SM6) |
| SM8 | v0.79.0 → **v1.0.0** | 3-5 weeks |
| **Total** | | **45–70 weeks** (~11–16 months) |

This is a *substantial* workstream. The estimate is consistent
with seLe4n's historical workstream cadence (WS-AK ran 14 months
end-to-end; WS-AN ran 8 months). The estimate is calibrated to
the project's solo-maintainer rhythm; faster delivery requires
contributor parallelism (multiple phases progressing concurrently
where dependencies permit).

**Critical-path note**: SM0 → SM1+SM2 → SM3 → SM4 → SM5 → SM8 is
the critical path. SM6 and SM7 can run parallel to SM4/SM5 once
SM3 lands.

## 10. Open questions for the maintainer

Before SM0 opens, the following decisions are needed:

1. **Workstream ID** — `WS-SM` (SMP / Multi-core) per the
   two-letter convention. Confirm or rename.
2. **Target version + WS-RC retarget** — v1.0.0 ships SMP. This
   requires retargeting WS-RC's R2..R6 closing version from v1.0.0
   to v0.31.last (substance unchanged; only the release-bump
   sub-tasks shift). Confirm both the v1.0.0-ships-SMP goal AND the
   WS-RC retarget.
3. **BKL discipline** — accept Big Kernel Lock for v1.0.0;
   per-subsystem locks deferred to v1.x performance workstream?
4. **Concurrency strategy** — confirm path-b (additive per-core
   fields with bootCore-shim) over path-a (replace existing fields)
   per §2.4.
5. **Default SMP activation** — should v1.0.0 default to
   `smp_enabled=true` on RPi5? seL4 ships SMP off; we recommend
   same: ON only when explicitly requested. The PRIMARY core path
   remains the same single-core kernel; SMP activation brings up
   secondaries.
6. **Cross-cluster portability** — defer to post-1.0 (BCM2712 is
   single cluster; OSH variants exist but unused)? Confirm.
7. **`numCores` parameterization** — hardcoded to 4 for v1.0.0
   per §4.3? Or generalize across PlatformBinding now?
8. **Idle threads** — per-core idle threads (recommended in
   §SM2.G) or shared idle thread with affinity?
9. **Honesty patches sequencing** — SM0 batched into one
   v0.32.0 release, or spread across the WS-SM lifetime?

## 11. Acceptance / completeness criteria for v1.0.0 release

WS-SM is complete and v1.0.0 ships when:

- [ ] All 5 CRITICAL findings closed (SMP-C1..C4 + the SMP-H4 BKL gap).
- [ ] All HIGH findings closed.
- [ ] All MEDIUM findings closed except those deferred with explicit
      rationale.
- [ ] LOW findings either closed or recorded post-1.0 with
      correctness-impact statement.
- [ ] Every phase's acceptance gate (§5 per-phase) green.
- [ ] tier-0 through tier-4 tests green at HEAD.
- [ ] QEMU `-smp 4` integration test green.
- [ ] Cargo `cargo test -p sele4n-hal --lib smp` (after extensions) green.
- [ ] `lake build` (256 jobs) green; zero `sorry`, `axiom`, `native_decide`.
- [ ] `scripts/test_full.sh` green; `scripts/test_nightly.sh` green.
- [ ] Documentation synchronized per CLAUDE.md "Documentation rules".
- [ ] AN12-B inventory transitioned from "latent" to "discharged"
      OR replaced with a post-1.0 "SMP-runtime-invariant" inventory.
- [ ] WCRT bound proven for the SMP RPi5 canonical config.
- [ ] Per-core noninterference proven.
- [ ] Information flow: BKL contention channel documented;
      enforcement boundary extended.
- [ ] No production-source `dev_history/` cross-references.
- [ ] CHANGELOG v1.0.0 entry complete.
- [ ] Version bumped to 1.0.0 across all metric-bearing files.

## Appendix A — Source-of-truth file inventory

The full source surface audited for this plan (~2300 lines of
existing source):

| Path | Lines | Purpose |
|------|------:|---------|
| `SeLe4n/Kernel/Concurrency/Assumptions.lean` | 228 | AN12-B SMP-latent inventory |
| `rust/sele4n-hal/src/smp.rs` | 345 | SMP bring-up scaffolding |
| `rust/sele4n-hal/src/psci.rs` | 189 | PSCI CPU_ON wrapper |
| `rust/sele4n-hal/src/boot.S` | 170 | Boot assembly |
| `rust/sele4n-hal/src/boot.rs` | 170 | Rust boot main (4 phases) |
| `rust/sele4n-hal/src/cpu.rs` | 351 | MPIDR mask, wfe_bounded |
| `rust/sele4n-hal/src/gic.rs` | 848 | GIC-400 (no SGI primitive) |
| `rust/sele4n-hal/src/interrupts.rs` | 156 | with_interrupts_disabled |
| `rust/sele4n-hal/src/tlb.rs` | 155 | TLB ops (non-IS only — SMP-C4) |
| `rust/sele4n-hal/src/barriers.rs` | 540 | barrier ops; dsb_osh exists |
| `rust/sele4n-hal/src/cache.rs` | 270 | cache ops; ic_ialluis exists |
| `rust/sele4n-hal/link.ld` | 102 | .smp_stacks reserved |
| `SeLe4n/Kernel/Architecture/Assumptions.lean` | 346 | ArchAssumption inductive |
| `SeLe4n/Kernel/CrossSubsystem.lean:3239-3273` | 35 | singleCore witness |
| `SeLe4n/Model/State.lean:120-170` | 50 | SchedulerState (single-core) |
| `SeLe4n/Platform/FFI.lean:380-460` | 80 | kernelStateRef shared |
| `SeLe4n/Platform/Contract.lean` | 133 | PlatformBinding |
| `scripts/test_qemu_smp_bringup.sh` | 42 | Stub (SKIP) |
| `docs/spec/SELE4N_SPEC.md §6.4, §6.8, §11.2.3` | ~200 | SMP-deferred claims |
| `docs/audits/AUDIT_v0.30.11_DEEP_VERIFICATION.md:1054,1294` | ~30 | Prior audit's SMP notes |
| `docs/dev_history/audits/AUDIT_v0.29.0_DEFERRED.md:290-340` | 50 | DEF-R-HAL-L20 |
| **Total existing** | **~4500** | |

## Appendix B — Verification commands

The following commands independently verify the findings in §3:

```bash
# SMP-C1: bring_up_secondaries has no caller outside smp.rs
grep -rn "bring_up_secondaries\|crate::smp::bring_up" rust/

# SMP-C2: rust_secondary_main body — confirm no init calls
sed -n '202,240p' rust/sele4n-hal/src/smp.rs

# SMP-C4: TLB module emits non-IS variants
grep -E "tlbi (vae1|aside1|vmalle1|vale1)[, ]" rust/sele4n-hal/src/tlb.rs

# SMP-H1: No SGI primitive
grep -n "GICD_SGIR\|send_sgi\|fn.*sgi" rust/sele4n-hal/src/gic.rs

# SMP-H2: ArchAssumption constructor count
grep -A 10 "inductive ArchAssumption" SeLe4n/Kernel/Architecture/Assumptions.lean

# SMP-H3: Inventory Lean.Name disclaimer
grep -A 3 "Lean does not enforce" SeLe4n/Kernel/Concurrency/Assumptions.lean

# SMP-M1: dev_history cross-references in production
grep -rn "dev_history" rust/sele4n-hal/src/ SeLe4n/Kernel/

# SMP-M2: stale WS-V claim
grep -n "deferred to WS-V" docs/spec/SELE4N_SPEC.md

# SMP-M3: .smp_stacks not in BSS-zero loop
grep -B 2 -A 8 ".smp_stacks" rust/sele4n-hal/link.ld

# SMP-M4: TPIDR_EL1 not set in secondary_entry
grep -n "TPIDR\|tpidr" rust/sele4n-hal/src/boot.S

# SMP-M6: QEMU stub
head -30 scripts/test_qemu_smp_bringup.sh

# Inventory size witness
grep -n "smpLatentInventory_count" SeLe4n/Kernel/Concurrency/Assumptions.lean
```

## Appendix C — Theorem catalogue (forward-looking)

The complete list of new substantive theorems WS-SM introduces.
Each will land in the phase indicated; the catalogue is the
canonical reference for verification audits during WS-SM.

### C.1 Foundations (SM0)

| Theorem | Statement | File |
|---------|-----------|------|
| `numCores_pos` | `numCores > 0` | `Concurrency/Types.lean` |
| `allCores_length` | `allCores.length = numCores` | `Concurrency/Types.lean` |
| `allCores_nodup` | `allCores.Nodup` | `Concurrency/Types.lean` |
| `bootCoreId_valid` | `bootCoreId.val < numCores` | `Concurrency/Types.lean` |
| `SgiKind.toIntid_injective` | Pairwise distinct INTIDs | `Concurrency/Locks.lean` |
| `smpLatentInventory_identifiers_nodup` | NoDup identifiers | `Concurrency/Assumptions.lean` |
| `archAssumption_singleCoreOperation_added` | 6th constructor exists | `Architecture/Assumptions.lean` |
| `archAssumptionConsumer_total_6` | total over 6 cases | `Architecture/Assumptions.lean` |
| `archAssumptionConsumer_distinct_6` | C(6,2)=15 distinct | `Architecture/Assumptions.lean` |

### C.2 Lock model (SM3)

| Theorem | Statement | File |
|---------|-----------|------|
| `bklMutex` | At most one core holds BKL | `Concurrency/Locks.lean` |
| `bklFifo` | Tickets serve in order | `Concurrency/Locks.lean` |
| `bklRelAcq` | Release → acquire happens-before | `Concurrency/Locks.lean` |
| `bklBoundedWait` | WCRT(acquire) ≤ (n-1)×WCRT(cs) | `Concurrency/Locks.lean` |
| `bkl_unheld_at_kernel_entry` | Pre-condition on @[export] bodies | `Platform/FFI.lean` |
| `bkl_unheld_at_kernel_exit` | Post-condition on @[export] bodies | `Platform/FFI.lean` |
| `bkl_held_during_kernel_transition` | Mid-state of @[export] bodies | `Platform/FFI.lean` |
| `bkl_acquire_release_paired` | RAII discipline | `Platform/FFI.lean` |
| `bkl_mutex_property_preserved` | BklProperty invariant | `Platform/FFI.lean` |
| `kernelStateRef_safe_under_bkl` | IO.Ref safety | `Platform/FFI.lean` |

### C.3 Per-core scheduler (SM4)

| Theorem | Statement |
|---------|-----------|
| `chooseThreadOnCore_selects_highest` | Highest-priority runnable selected |
| `chooseThreadOnCore_perCore_independence` | Per-core independence |
| `chooseThreadOnCore_preserves_wellFormed` | Run queue invariant |
| `chooseThreadOnCore_always_succeeds` | Idle fallback |
| `switchToThreadOnCore_sets_current` | currentOnCore mutation |
| `switchToThreadOnCore_preempts_previous` | Eviction discipline |
| `switchToThreadOnCore_rejects_remote` | Migration not implicit |
| `runQueueOnCore_excludes_currentOnCore` | Per-core inv generalized |
| `runQueueOnCore_wellFormed` | Per-core run queue inv |
| `currentOnCore_validThreadIfSome` | Per-core current validity |
| `schedContextRunQueueConsistent_perCore` | Per-core CBS inv |
| `schedulerInvariant_perCore` | Aggregate per-core inv |
| `schedulerInvariant_perCore_pairwise` | Cross-core independence |
| `enqueueRunnableOnCore_wellFormed` | Per-core enqueue preserves inv |
| `wakeThread_emits_sgi_if_remote` | Cross-core wake protocol |
| `wakeThread_lossless` | Eventually delivered |
| `timerTickOnCore_advances_per_core` | Per-core tick |
| `cbsReplenish_can_wake_remote_core` | Cross-core replenish |
| `idleThread_core_locality` | Idle stays on its core |
| `idleThread_priority_zero` | Idle is lowest priority |
| `pipBoost_perCore_consistent` | PIP per-core |
| `activeDomainOnCore_isInDomainSchedule` | Domain validity per-core |
| `advanceDomainOnCore_cyclic` | Domain rotation |
| `chooseThreadOnCore_inActiveDomain` | Per-core domain respect |
| `wcrt_bound_rpi5_smp` | SMP WCRT bound |

### C.4 Per-core IPC (SM5)

| Theorem | Statement |
|---------|-----------|
| `endpointCall_emits_sgi_if_remote_receiver` | Cross-core call wake |
| `endpointCall_perCore_blocking` | Caller blocks on own core |
| `notificationSignal_remote_wake` | Cross-core notification |
| `endpointReply_perCore_delivery` | Reply to correct TCB |
| `donation_perCore_consistent` | Donation across cores |
| `ipcInvariantFull_perCore` | 15-conjunct per-core |
| `cancelIpcBlocking_atomic_under_bkl` | Cancel atomicity |
| `cancelDonation_atomic_under_bkl` | Donation cancel atomicity |

### C.5 TLB / cache (SM6)

| Theorem | Statement |
|---------|-----------|
| `tlbShootdownLocal_invalidates_local` | Initiator's TLB cleared |
| `tlbShootdownBroadcast_invalidatesAllCores` | All TLBs cleared |
| `tlbInvalidationConsistent_perCore` | Per-core TLB ↔ page table |
| `shootdownAck_completes_in_bounded_time` | Ack protocol bounded |
| `pendingShootdowns_drained_at_sgi_entry` | Pending queue drained |

### C.6 Information flow (SM7)

| Theorem | Statement |
|---------|-----------|
| `onCore_isProjection_of_globalProjection` | Refinement |
| `onCore_decidable` | Decidable projection |
| `nonInterference_perCore` | Per-core NI |
| `crossCoreNonInterference` | Cross-core NI |
| `bklContention_acceptedCovertChannel` | Channel documented |
| `enforcementBoundary_perCore_complete` | Extended boundary |
| `DeclassificationEvent_perCore_audit` | Per-core audit trail |

### C.7 Boot / platform (SM2)

| Theorem | Statement |
|---------|-----------|
| `bootFromPlatform_all_cores_have_idle` | Every core's currentOnCore = some idle |
| `bootFromPlatform_smp_witness` | Per-core boot shape |
| `perCoreSchedulerConsistent` | New crossSubsystemInvariant conjunct |
| `perCoreSchedulerConsistent_at_boot` | Holds at boot |
| `PlatformBinding_coreCount_pos` | Contract precondition |

### C.8 Closure (SM8)

| Theorem | Statement |
|---------|-----------|
| `smpLatentInventory_dischargedInSm8` | All 8 entries have SMP discharge |
| `wsm_phase_count` | 9 phases (SM0..SM8) |
| `wsm_acceptance_gate_count` | All gates green |

**Total new substantive theorems**: ~95.

## Appendix D — Internal-first naming compliance

Per CLAUDE.md, no workstream IDs in identifiers. The plan uses
phase IDs `SM0..SM8` only in:
- Plan filename (`SMP_MULTICORE_COMPLETION_PLAN.md`)
- Sub-task labels (`SM3.A.1`, etc.) for cross-reference
- CHANGELOG entries
- Docstrings explaining the historical context

It does NOT use them in:
- Theorem names (e.g., `wcrt_bound_rpi5_smp`, not `sm4_d_4_theorem`)
- Function names (e.g., `chooseThreadOnCore`, not `sm4_choose`)
- File names (e.g., `Architecture/TlbShootdown.lean`, not
  `Architecture/Sm6Shootdown.lean`)
- Test names (e.g., `cross_core_call_wakes_receiver`, not
  `test_sm5_a_3`)
- Field names

Workstream-ID neutrality keeps the codebase clean of churn-driven
debt; SM0..SM8 ages out as labels but the underlying code describes
itself by purpose.

---

*This plan was produced from branch
`claude/audit-multicore-implementation-sUcIx` at v0.31.2. It is a
forward-looking planning artefact; no runtime behavior, proof
obligations, or source identifiers change with this document. The
plan is intended to open as workstream **WS-SM** immediately after
WS-RC closure, with the goal of shipping a bootable verified SMP
microkernel as v1.0.0.*
