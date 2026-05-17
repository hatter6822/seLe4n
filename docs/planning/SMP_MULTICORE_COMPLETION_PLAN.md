# WS-SM — SMP / Multi-Core Completion (pre-v1.0.0) — Overview

> **Status**: PLAN (overview) — unified workstream closing at
> v1.0.0. WS-RC and WS-SM are merged.
>
> **Audited cut**: `v0.31.2` (current `lakefile.toml::version`).
>
> **Branch (this audit)**: `claude/audit-multicore-implementation-sUcIx`.
>
> **Release target**: **v1.0.0 "bootable verified SMP microkernel
> on Raspberry Pi 5"** — bootable on all 4 BCM2712 cores with the
> SMP path verified at the same rigor seL4 applies to its
> single-core kernel, plus verified lock primitives that the seL4
> project historically left as assumptions.
>
> **Sequencing**: WS-RC and WS-SM merge into a single unified
> workstream. WS-RC's already-landed phases (R0..R5 at v0.31.2)
> stand; remaining R6..R14 phases are recategorized into
> SM-phases per SM0.Q. The merged plan opens immediately at the
> v0.31.2 boundary; SM0 honesty patches land first; SM1..SM9
> follow. There is no intermediate v0.31.last release; the next
> milestone after v0.31.2 is v1.0.0 itself, reached via SM
> staging releases (v0.32.x..v0.99.x).
>
> **Estimated timeline**: 24-30 months at the project's
> single-maintainer cadence.

This document is the **overview/index** for the WS-SM workstream.
Each phase has its own dedicated planning document that contains
the deep mathematical specifications, code skeletons, proof
obligations, test plans, and atomic sub-task breakdowns. This
overview ties them together.

## Table of contents

| Section | Topic |
|---------|-------|
| §1 | Executive summary |
| §2 | Mathematical foundations (high level) |
| §3 | Findings catalogue (gaps to close) |
| §4 | Architectural design choices |
| §5 | Phase plan index (links to per-phase plans) |
| §6 | Cross-subsystem impact matrix |
| §7 | Verification strategy |
| §8 | Risk inventory |
| §9 | Timeline |
| §10 | Decisions taken |
| §11 | Acceptance criteria for v1.0.0 |
| App A | Phase-plan directory |
| App B | Verification commands |
| App C | Theorem-catalogue index |

## 1. Executive summary

### 1.1 The core finding

The current SMP scaffolding cannot be activated: four CRITICAL
gaps make `SMP_ENABLED = true` either dead code (no caller) or a
correctness hazard. The AN9-J disposition
("activation cost is just flipping the runtime flag",
`AUDIT_v0.29.0_DEFERRED.md:296`) is materially inaccurate.
Shipping v1.0.0 under that disposition would ship a non-functional
SMP binary on a 4-core SoC.

### 1.2 Headline findings

| Sev | ID | Finding |
|-----|----|---------|
| **CRIT** | SMP-C1 | `bring_up_secondaries()` is never called. |
| **CRIT** | SMP-C2 | `rust_secondary_main` skips MMU/VBAR/GIC/timer init. |
| **CRIT** | SMP-C3 | `kernelStateRef : IO.Ref SystemState` not cross-core atomic. |
| **CRIT** | SMP-C4 | TLB uses non-IS variants — page unmaps don't broadcast. |
| **HIGH** | SMP-H1 | No SGI / IPI primitive. |
| **HIGH** | SMP-H2 | `ArchAssumption` lacks `singleCoreOperation` constructor. |
| **HIGH** | SMP-H3 | Inventory `Lean.Name` not build-checked. |
| **HIGH** | SMP-H4 | No spinlock or lock primitive of any kind. |
| **MED+LOW** | SMP-M1..M7 + SMP-L1..L5 | Documentation, hygiene, scope items (see §3.9). |

### 1.3 Workstream shape

**WS-SM**, 10 phases, ~550-725 sub-tasks, ~24-30 months. Each
phase has its own detailed plan (Appendix A directory).

```
SM0  Foundations & honesty patches              SMP_FOUNDATIONS_PLAN.md
SM1  Rust HAL completion                        SMP_RUST_HAL_PLAN.md
SM2  Verified lock primitives                   SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md
SM3  Per-object lock fields + hierarchical      SMP_PER_OBJECT_LOCKS_PLAN.md
SM4  Path-a per-core state replacement          SMP_PER_CORE_STATE_PLAN.md
SM5  Per-core scheduler                         SMP_PER_CORE_SCHEDULER_PLAN.md
SM6  Cross-core IPC                             SMP_CROSS_CORE_IPC_PLAN.md
SM7  TLB / cache shootdown                      SMP_TLB_SHOOTDOWN_PLAN.md
SM8  Information flow under SMP                 SMP_INFORMATION_FLOW_PLAN.md
SM9  Documentation, tests, version closure      SMP_RELEASE_CLOSURE_PLAN.md
```

**Parallelism**: SM0 first; SM1 ‖ SM2 (independent); SM3 gates on
SM2 + SM1.B (Rust types); SM4 ‖ SM3 (independent state-shape
work); SM5 gates on SM3 + SM4; SM6 gates on SM5; SM7 ‖ SM6 after
SM3; SM8 ‖ SM6/SM7 after SM4; SM9 last.

## 2. Mathematical foundations (high level)

This section gives the formal-spec backbone. Each phase plan
elaborates the subset relevant to it.

### 2.1 Concurrency model: per-object RW fine-lock serialization

The kernel runs under **per-object reader-writer fine locking**
with **hierarchical-by-kind acquire order** and **two-phase
locking (2PL)**. Each kernel-object struct (`TCB`, `Endpoint`,
`CNode`, `Notification`, `Reply`, `SchedContext`, `VSpaceRoot`,
`Page`, `Untyped`, plus the `ObjStore` itself) carries a `lock :
RwLock` field.

A `LockKind` enumeration imposes a 10-level total order:

```
ObjStore < Untyped < CNode < TCB < Endpoint < Notification <
Reply < SchedContext < VSpaceRoot < Page
```

with within-kind ordering by `ObjId.val`. The `LockId.le` lex
order is total (`LockId.le_total`).

Each kernel transition τ declares its **lock-set** statically
(derived from the argument shape, not from runtime state):

    def lockSet (τ : KernelTransition) (args : Args) :
      Finset (LockId × AccessMode)

Locks are acquired in ascending `LockId` order; released in
reverse (strict-2PL).

**Theorem 2.1.9** (Deadlock-freedom). Under strict-2PL plus
hierarchical acquire-in-ascending-order, no execution can
deadlock. *Proof sketch*: induction over `LockId` total order
plus pigeonhole on the wait graph; details in
[`SMP_PER_OBJECT_LOCKS_PLAN.md`](SMP_PER_OBJECT_LOCKS_PLAN.md)
§4.

**Theorem 2.1.10** (Serializability). Strict-2PL is
conflict-serializable: every interleaved execution has a serial
equivalent producing the same final state. *Proof*: classical
Bernstein result reused. Details in
[`SMP_PER_OBJECT_LOCKS_PLAN.md`](SMP_PER_OBJECT_LOCKS_PLAN.md)
§5.

**Corollary 2.1.11** (Single-core proof preservation). Every
existing single-core kernel-transition theorem remains valid
under SMP, *provided* the theorem's precondition is strengthened
to "the transition's lock-set is held in the declared modes".
This is the lever that keeps the verification cost tractable.

### 2.2 Verified lock primitives

WS-SM verifies the **lock primitives themselves** — TicketLock
and RwLock — in Lean against an abstract operational semantics
of ARMv8.1-A LSE atomic operations. seL4 historically assumed
these primitives; we elevate them to proofs.

Key theorems (full statements in
[`SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md`](SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md)):

- TicketLock: `mutex` (2.2.2.1), `fifo` (2.2.2.2),
  `boundedWait` (2.2.2.3), `releaseAcquirePairing` (2.2.2.4).
- RwLock: `writerReadersExclusion` (2.2.3.1),
  `readerMultiplicity` (2.2.3.2), `fifoAdmission` (2.2.3.3),
  `boundedWait` × 2 (2.2.3.4), `releaseAcquirePairing` × 2
  (2.2.3.5).
- Refinement: `rust_ticketLock_refines_lean`,
  `rust_rwLock_refines_lean`.

**Axiom budget for WS-SM: 0 Lean axioms.** Hardware properties
(ARMv8.1-A LSE semantics) enter via documented ARM ARM citations
in module docstrings; no `axiom` declarations.

### 2.3 Per-core state encoding (path-a)

The `SchedulerState` (and analogues) get **path-a Vector
replacement**: singular `current : Option ThreadId` becomes
`current : Vector (Option ThreadId) PlatformBinding.coreCount`,
with `CoreId := Fin PlatformBinding.coreCount`. Every
single-core theorem rewrites to take a `c : CoreId` parameter.
Details in
[`SMP_PER_CORE_STATE_PLAN.md`](SMP_PER_CORE_STATE_PLAN.md).

### 2.4 Sharing domain parameterization

`PlatformBinding.sharingDomain : SharingDomain` (Inner ↔ Outer).
RPi5 = Inner. Cross-cluster targets = Outer. All barrier/TLBI
emission routes through `dsbForSharing` / `tlbiForSharing`.

### 2.5 IPI / SGI model

5 reserved SGI INTIDs:

| INTID | Purpose |
|-------|---------|
| 0 | reschedule |
| 1 | tlbShootdownReq |
| 2 | tlbShootdownAck |
| 3 | cacheBroadcast |
| 4 | haltAll |

Pending-SGI queue is per-core (`pendingSgis : Vector (List
PendingSgi) coreCount`). Drained at SGI handler entry under
appropriate lock-set. Details in
[`SMP_RUST_HAL_PLAN.md`](SMP_RUST_HAL_PLAN.md) §SM1.F and
[`SMP_PER_CORE_SCHEDULER_PLAN.md`](SMP_PER_CORE_SCHEDULER_PLAN.md)
§SM5.C.

### 2.6 TLB shootdown protocol

Explicit-ack protocol with per-core acknowledgement flags. Local
core issues `tlbi vaae1is`; remote cores receive
`tlbShootdownReq` SGI, execute local TLBI, set ack flag, return.
Initiator waits until all flags set. Details in
[`SMP_TLB_SHOOTDOWN_PLAN.md`](SMP_TLB_SHOOTDOWN_PLAN.md).

### 2.7 Information flow under SMP

Per-core observer `(c, L)` projection. `crossCoreNonInterference`
theorem proves transitions on c' ≠ c don't change c's L-view
unless they mutate L-observable shared state. Lock-contention
timing is a documented accepted covert channel. Details in
[`SMP_INFORMATION_FLOW_PLAN.md`](SMP_INFORMATION_FLOW_PLAN.md).

## 3. Detailed finding catalogue

Each finding cites file:line directly verifiable in the audit's
source tree. The full per-finding writeup with reproduction
steps and closure tracking lives in
[`SMP_FOUNDATIONS_PLAN.md`](SMP_FOUNDATIONS_PLAN.md) §1. Here we
summarize.

### 3.1..3.4 CRITICAL findings

| ID | Location | Closure |
|----|----------|---------|
| SMP-C1 (no bring-up caller) | `rust/sele4n-hal/src/boot.rs:27-108` | SM1.D Phase 5 wiring |
| SMP-C2 (incomplete secondary init) | `rust/sele4n-hal/src/smp.rs:213-235` | SM1.C full init |
| SMP-C3 (shared kernelStateRef) | `SeLe4n/Platform/FFI.lean:394` | SM3 per-object lock-set discipline |
| SMP-C4 (TLB non-IS) | `rust/sele4n-hal/src/tlb.rs:34..100` | SM1.E IS variants + SM7 shootdown protocol |

### 3.5..3.8 HIGH findings

| ID | Location | Closure |
|----|----------|---------|
| SMP-H1 (no SGI primitive) | `rust/sele4n-hal/src/gic.rs` | SM1.F SGI primitive |
| SMP-H2 (missing ArchAssumption ctor) | `SeLe4n/Kernel/Architecture/Assumptions.lean:17-23` | SM0.A constructor |
| SMP-H3 (inventory names not checked) | `Concurrency/Assumptions.lean:53-61` | SM0.C `@`-references |
| SMP-H4 (no lock primitive) | `interrupts.rs:101-106` | SM2 verified primitives |

### 3.9 MED + LOW findings

`SMP-M1`..`SMP-M7`, `SMP-L1`..`SMP-L5` — documentation, hygiene,
scope items. All closed in SM0 honesty patches per
[`SMP_FOUNDATIONS_PLAN.md`](SMP_FOUNDATIONS_PLAN.md).

## 4. Architectural design choices

The 13 binding maintainer decisions:

| # | Decision | Rationale |
|---|----------|-----------|
| 1 | **Per-object fine locks** | Maximum concurrency; 2PL preserves proof surface (Cor 2.1.11). |
| 2 | **Reader-writer locks** | Read-mostly workloads (lookup, ObjStore) gain parallel reader paths. Upgrade/downgrade deferred to v1.x. |
| 3 | **Hierarchical-by-kind order** | 10-level LockKind hierarchy; cleaner proof of deadlock-freedom. |
| 4 | **Path-a Vector replacement** | Cleaner final state. Cost: ~5000-7000 LoC of theorem rewrites. |
| 5 | **numCores via PlatformBinding** | Multi-platform future-proof. |
| 6 | **sharingDomain via PlatformBinding** | Cross-cluster support pre-positioned. |
| 7 | **SMP enabled by default** | v1.0.0 headline capability; rigor enforced by QEMU `-smp 4` test mandate. |
| 8 | **Per-core idle TCBs** | One per core; clean invariants. |
| 9 | **SM0 spread across PRs** | Review-friendly small PRs. |
| 10 | **Verified lock primitives** | TicketLock + RwLock proven in Lean; refinement to Rust impl proven. seL4 historically left these as assumptions. |
| 11 | **WS-SM** | Workstream ID. |
| 12 | **WS-RC + WS-SM merge** | Single unified workstream; no intermediate v0.31.last. |
| 13 | **24-30 month timeline** | Solo-maintainer cadence; comprehensive scope. |

Rejected alternatives are recorded per-phase. The decision-by-
decision detail with rejected alternatives lives in
[`SMP_FOUNDATIONS_PLAN.md`](SMP_FOUNDATIONS_PLAN.md) §3.

## 5. Phase plan index

Each phase has its own dedicated planning document. The index:

### SM0 — Foundations & honesty patches

Document: [`SMP_FOUNDATIONS_PLAN.md`](SMP_FOUNDATIONS_PLAN.md).

21 sub-tasks landed in a single coherent cut at v0.31.3 (compressed from the originally-planned ~18-PR v0.32.x spread per maintainer redirection).
Foundational types (`CoreId`, `LockKind`, `BklState`, `SgiKind`,
`SharingDomain`); documentation drift; small structural fixes;
WS-RC absorption. **Prerequisite**: WS-RC R0..R5 LANDED (true at
v0.31.2).

### SM1 — Rust HAL completion

Document: [`SMP_RUST_HAL_PLAN.md`](SMP_RUST_HAL_PLAN.md).

60-80 sub-tasks across ~22-32 PRs. PSCI completion; per-CPU
data + TPIDR_EL1; full secondary-core init (MMU/VBAR/GIC/timer);
DTB cmdline parser + Phase 5; IS-variant TLB instructions; SGI
primitive; cross-core kprintln synchronization; QEMU SMP
integration. **Closes**: SMP-C1, SMP-C2, SMP-C4 (HAL part),
SMP-H1, SMP-M3, SMP-M4, SMP-M5, SMP-M6.

### SM2 — Verified lock primitives

Document: [`SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md`](SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md).

70-95 sub-tasks across ~28-40 PRs. The most novel and
verification-heavy phase. Abstract memory model
(`MemoryModel.lean`); TicketLock Lean spec + Rust impl +
refinement; RwLock Lean spec + Rust impl + refinement; FFI
bridge; documentation. **Closes**: SMP-H4 (foundationally).

### SM3 — Per-object lock fields + hierarchical order

Document: [`SMP_PER_OBJECT_LOCKS_PLAN.md`](SMP_PER_OBJECT_LOCKS_PLAN.md).

50-65 sub-tasks across ~18-26 PRs. Add `lock : RwLock` field to
every kernel-object struct; define `LockKind` 10-level
hierarchy; lock-set extraction; two-phase locking discipline;
prove `deadlockFreedom_under_2pl_and_ordering` (Thm 2.1.9) and
`serializability_under_2pl` (Thm 2.1.10) and
`singleCore_proof_preservation` (Cor 2.1.11). **Closes**:
SMP-C3 (formal foundation).

### SM4 — Path-a per-core state replacement

Document: [`SMP_PER_CORE_STATE_PLAN.md`](SMP_PER_CORE_STATE_PLAN.md).

90-115 sub-tasks across ~35-50 PRs. The largest phase. Replace
singular `SchedulerState` fields with `Vector α coreCount`;
migrate every theorem touching them (~5000-7000 LoC of theorem
rewrites). Retire `bootFromPlatform_singleCore_witness`.
**Closes**: SMP-H2 retired (no longer applicable).

### SM5 — Per-core scheduler

Document: [`SMP_PER_CORE_SCHEDULER_PLAN.md`](SMP_PER_CORE_SCHEDULER_PLAN.md).

75-95 sub-tasks across ~28-38 PRs. Per-core `chooseThread`,
`switchToThread`; cross-core wake via SGI; per-core timer tick;
per-core idle threads; per-core PIP; per-core domain
scheduling; per-core CBS; WCRT under fine locks.

### SM6 — Cross-core IPC

Document: [`SMP_CROSS_CORE_IPC_PLAN.md`](SMP_CROSS_CORE_IPC_PLAN.md).

60-80 sub-tasks across ~22-32 PRs. Endpoint call/send/recv,
notifications, reply all under per-object fine locks with
cross-core wake. IPC invariant bundle per-core.

### SM7 — TLB / cache shootdown

Document: [`SMP_TLB_SHOOTDOWN_PLAN.md`](SMP_TLB_SHOOTDOWN_PLAN.md).

40-55 sub-tasks across ~15-22 PRs. Shootdown descriptor; explicit-
ack protocol; per-core TLB model; cache maintenance broadcast.
**Closes**: SMP-C4 (formal proof part).

### SM8 — Information flow under SMP

Document: [`SMP_INFORMATION_FLOW_PLAN.md`](SMP_INFORMATION_FLOW_PLAN.md).

40-55 sub-tasks across ~15-22 PRs. Per-core observable state;
per-core NI proofs; lock-contention covert channel
documentation; per-core declassification audit.

### SM9 — Documentation, tests, version closure

Document: [`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md).

25-35 sub-tasks across ~10-15 PRs. Spec rewrite; new GitBook
chapters; README + 10 i18n; CLAIM_EVIDENCE_INDEX;
WORKSTREAM_HISTORY; full SMP test suites; tier-4/tier-5 scripts;
version bump to 1.0.0; WS-SM closure record.

## 6. Cross-subsystem impact matrix

| Subsystem | Files | Existing LoC | New LoC | Migration LoC | Phase footprint |
|-----------|------:|-------------:|--------:|--------------:|-----------------|
| Concurrency (new) | 0 → 8 | 228 | ~3500 | 0 | SM0, SM2, SM3 |
| Scheduler | 22 | ~7000 | ~2200 | ~2400 | SM4, SM5 |
| IPC | 35 | ~12000 | ~1500 | ~1800 | SM4, SM6 |
| Capability | 18 | ~5500 | ~600 | ~700 | SM3, SM4 |
| Lifecycle | 6 | ~1500 | ~300 | ~200 | SM3, SM4 |
| Service | 4 | ~1500 | ~150 | ~100 | SM4 |
| Architecture | 14 | ~6000 | ~1500 | ~600 | SM1, SM7 |
| InformationFlow | 12 | ~6000 | ~1500 | ~800 | SM8 |
| RobinHood / RadixTree | 6 | ~3500 | ~250 | ~50 | SM3 |
| Platform | 17 | ~5000 | ~1000 | ~300 | SM0, SM1, SM4 |
| CrossSubsystem | 1 | 3309 | ~800 | ~400 | SM4 |
| Model | 5 | ~5500 | ~600 | ~400 | SM4 |
| Object types | 7 | ~3500 | ~400 | ~200 | SM3 |
| **Total** | **155** | **~60,000** | **~14,300** | **~7,950** | |

Total new+migration: **~22,250 LoC** across **~155 files**.

For scale: WS-AK delivered ~6,000 LoC across 14 months; WS-SM at
~3.7× that LoC and at higher conceptual complexity predicts
~24-30 months.

## 7. Verification strategy

**Axiom budget**: 0 Lean axioms. Hardware assumptions enter via
`@[extern]` opaque declarations whose Rust implementations are
reviewed against ARM ARM citations.

| Property | Phase | Proof technique |
|----------|-------|-----------------|
| TicketLock mutex/FIFO/bounded-wait/release-acquire | SM2 | Direct (atomic-RMW semantics; bandwidth argument) |
| RwLock writer-readers exclusion/multiplicity/FIFO/bounded-wait/release-acquire (×2 each) | SM2 | Predicate invariant; queue discipline |
| Refinement Rust ↔ Lean | SM2 | Operational simulation; per-op spec match |
| Deadlock-freedom under 2PL+order (Thm 2.1.9) | SM3 | Induction over LockId total order |
| Serializability under strict-2PL (Thm 2.1.10) | SM3 | Bernstein conflict-serializability |
| Single-core proof preservation (Cor 2.1.11) | SM3 | Theorem migration |
| ~110 migrated per-core scheduler invariants | SM4 | Mechanical migration |
| ~22 migrated per-core IPC invariants | SM4 | Same |
| Cross-core wake (SGI delivery) | SM5 | Atomic-append + 2PL |
| TLB shootdown completeness (Thm 2.6.3) | SM7 | Protocol + explicit ack |
| Cross-core NI (Thm 2.7.3) | SM8 | Per-core observer model |
| WCRT bound under SMP fine-locking | SM5 | Lock-set + per-lock WCRT composition |

### 7.1 Testing tiers

| Tier | Coverage | SMP additions |
|------|----------|---------------|
| Tier 0 (hygiene) | sorry/axiom/native_decide | 0 axioms |
| Tier 1 (build) | All modules compile | Concurrency suite compiles |
| Tier 2 (trace) | Deterministic trace fixture | `smp_4core_boot.expected` |
| Tier 3 (invariant) | Surface anchor `#check`s | Per-core + lock-primitive anchors |
| Tier 4 (nightly) | QEMU `-smp 4` boot | Cross-core IPC; TLB shootdown; SGI |
| Tier 5 (NEW) | Lock-primitive correctness | TicketLock + RwLock spec checks |

### 7.2 Liveness under contention

Worst-case syscall response time under per-object fine locks:

    WCRT(syscall) ≤ max-lock-set-size × (coreCount - 1) × WCRT_per_lock

For RPi5 (coreCount = 4, typical lock-set size ≤ 4):

    WCRT(syscall) ≤ 4 × 3 × ~60 µs ≈ 720 µs

Comfortably fits within the 1-ms timer tick budget. Better than
BKL's 4 × 250 µs = 1 ms because fine locks distribute the wait.

## 8. Risk inventory

(Per-phase risks live in each phase plan; here we record
workstream-level risks.)

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Lock-set extraction static analysis brittle | MED | HIGH | SM3.B builds `lockSet` as a total Lean function; static-derivability is itself a theorem |
| Deadlock-freedom proof has subtle gap | LOW | CRIT | Theorem 2.1.9's induction is mathematically standard; wait-graph acyclicity as backup |
| Refinement Rust ↔ Lean drift over time | MED | HIGH | SM2.D static linker-time check; cargo test refinement scenarios |
| Multi-object operations exceed reasonable lock-set sizes (>8) | MED | MED | Per-op review during SM6; refactor if exceeded |
| WS-SM scope overruns 30 months | MED | MED (release delay) | Phased delivery; each SM-phase independently shippable |
| Hierarchical lock order has implicit cycles via cross-kind refs | LOW | HIGH | SM3.D wait-graph acyclicity catches; property-based fuzz |
| RW lock starvation under writer contention | LOW | MED | Theorem 2.2.3.3 (FIFO admission); writer-starvation freedom proof (SM2.C.14) |

## 9. Timeline

WS-RC and WS-SM are merged. Opens immediately at v0.31.2 boundary.

| Phase | Releases | Estimated calendar |
|-------|----------|--------------------|
| SM0 | v0.31.3 (LANDED) | single cut (compressed from the original v0.32.0..v0.32.x ~18-PR spread per maintainer redirection) |
| SM1 | v0.31.3 → v0.31.8 (LANDED) | 9 sub-phases (SM1.A–SM1.I), all landed in compressed cadence; SM2 still pending |
| SM1 ‖ SM2 | v0.33.0 → v0.45.x | 16-22 weeks (parallel) |
| SM3 | v0.46.0 → v0.52.x | 8-12 weeks |
| SM4 | v0.53.0 → v0.70.x | 20-26 weeks (largest phase) |
| SM5 | v0.71.0 → v0.82.x | 12-16 weeks |
| SM6 | v0.83.0 → v0.90.x | 8-12 weeks |
| SM7 ‖ SM8 | v0.91.0 → v0.97.x | 6-10 weeks (parallel) |
| SM9 | v0.98.0 → **v1.0.0** | 4-6 weeks |
| **Total** | | **78-110 weeks (~18-26 months)** |

Solo-maintainer cadence at upper bounds gives ~24-30 months
realistic.

## 10. Decisions taken

All 13 maintainer decisions are binding for WS-SM:

| # | Question | Decision |
|---|----------|----------|
| 1 | Concurrency model | Per-object fine locks |
| 2 | Target version + WS-RC merge | v1.0.0 ships SMP; WS-RC merges into WS-SM (single unified workstream; SM0.Q absorbs R6..R14 into SM-phases) |
| 3 | Model rewrite path | Path-a replacement |
| 4 | Default SMP activation | Enabled by default; opt-out via cmdline |
| 5 | numCores parameterization | Via `PlatformBinding.coreCount` |
| 6 | Cross-cluster portability | Via `PlatformBinding.sharingDomain` (Inner/Outer) |
| 7 | Idle threads | Per-core idle TCBs |
| 8 | SM0 sequencing | Spread across many small PRs |
| 9 | Workstream ID | WS-SM |
| 10 | Lock layout | Per-object fine locks |
| 11 | RW vs exclusive | Reader-writer locks |
| 12 | Lock acquire order | Hierarchical by object kind |
| 13 | Timeline / scope trade-off | Longer timeline + verify lock primitives |

Future deviations require maintainer-led re-decisioning recorded
in errata.

## 11. Acceptance criteria for v1.0.0 release

WS-SM is complete and v1.0.0 ships when:

- [ ] All 4 CRITICAL findings closed (SMP-C1..C4).
- [ ] All HIGH findings closed (SMP-H1..H4).
- [ ] All MEDIUM findings closed except those deferred with rationale.
- [ ] LOW findings closed or recorded post-1.0 with correctness-impact statement.
- [ ] Every phase's acceptance gate (per-phase docs) green.
- [ ] tier-0..tier-5 tests green at HEAD.
- [ ] QEMU `-smp 4` integration test green on every nightly.
- [ ] cargo test (HAL + ABI + types + sys) green.
- [ ] `lake build` (256 jobs) green; zero `sorry`, `axiom`, `native_decide`.
- [ ] `scripts/test_full.sh` + `scripts/test_nightly.sh` green.
- [ ] Documentation synchronized per CLAUDE.md "Documentation rules".
- [ ] AN12-B inventory transitioned to discharged state.
- [ ] WCRT bound proven for SMP RPi5 canonical config.
- [ ] Per-core non-interference proven.
- [ ] Information flow: lock-contention channel documented; enforcement boundary extended.
- [ ] No production-source `dev_history/` cross-references.
- [ ] CHANGELOG v1.0.0 entry complete.
- [ ] Version bumped to 1.0.0 across all metric-bearing files.
- [ ] WS-SM closure recorded in `docs/WORKSTREAM_HISTORY.md`.
- [ ] This plan (and all 10 phase plans) moved to `docs/dev_history/planning/`.

## Appendix A — Phase-plan directory

| Phase | Document | Sub-tasks | LoC est. |
|-------|----------|----------:|---------:|
| SM0 | [`SMP_FOUNDATIONS_PLAN.md`](SMP_FOUNDATIONS_PLAN.md) | 40-50 | ~3,000 |
| SM1 | [`SMP_RUST_HAL_PLAN.md`](SMP_RUST_HAL_PLAN.md) | 60-80 | ~2,500 |
| SM2 | [`SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md`](SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md) | 70-95 | ~3,500 |
| SM3 | [`SMP_PER_OBJECT_LOCKS_PLAN.md`](SMP_PER_OBJECT_LOCKS_PLAN.md) | 50-65 | ~1,500 |
| SM4 | [`SMP_PER_CORE_STATE_PLAN.md`](SMP_PER_CORE_STATE_PLAN.md) | 90-115 | ~7,000 |
| SM5 | [`SMP_PER_CORE_SCHEDULER_PLAN.md`](SMP_PER_CORE_SCHEDULER_PLAN.md) | 75-95 | ~2,500 |
| SM6 | [`SMP_CROSS_CORE_IPC_PLAN.md`](SMP_CROSS_CORE_IPC_PLAN.md) | 60-80 | ~1,800 |
| SM7 | [`SMP_TLB_SHOOTDOWN_PLAN.md`](SMP_TLB_SHOOTDOWN_PLAN.md) | 40-55 | ~1,200 |
| SM8 | [`SMP_INFORMATION_FLOW_PLAN.md`](SMP_INFORMATION_FLOW_PLAN.md) | 40-55 | ~1,500 |
| SM9 | [`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md) | 25-35 | ~500 |
| **Total** | | **550-725** | **~25,000 LoC of new code** |

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

## Appendix C — Theorem-catalogue index

WS-SM introduces ~210 new substantive theorems. Per-phase
breakdown:

| Phase | Theorems | Document section |
|-------|---------:|------------------|
| SM0 Foundations | ~12 | [SMP_FOUNDATIONS_PLAN §10](SMP_FOUNDATIONS_PLAN.md) |
| SM1 Rust HAL | ~6 | [SMP_RUST_HAL_PLAN §10](SMP_RUST_HAL_PLAN.md) |
| SM2 Verified locks | ~22 | [SMP_VERIFIED_LOCK_PRIMITIVES_PLAN §10](SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md) |
| SM3 Per-object locks | ~28 | [SMP_PER_OBJECT_LOCKS_PLAN §10](SMP_PER_OBJECT_LOCKS_PLAN.md) |
| SM4 Per-core state | ~50 | [SMP_PER_CORE_STATE_PLAN §10](SMP_PER_CORE_STATE_PLAN.md) |
| SM5 Per-core scheduler | ~30 | [SMP_PER_CORE_SCHEDULER_PLAN §10](SMP_PER_CORE_SCHEDULER_PLAN.md) |
| SM6 Cross-core IPC | ~25 | [SMP_CROSS_CORE_IPC_PLAN §10](SMP_CROSS_CORE_IPC_PLAN.md) |
| SM7 TLB shootdown | ~14 | [SMP_TLB_SHOOTDOWN_PLAN §10](SMP_TLB_SHOOTDOWN_PLAN.md) |
| SM8 Information flow | ~18 | [SMP_INFORMATION_FLOW_PLAN §10](SMP_INFORMATION_FLOW_PLAN.md) |
| SM9 Closure | ~5 | [SMP_RELEASE_CLOSURE_PLAN §10](SMP_RELEASE_CLOSURE_PLAN.md) |
| **Total** | **~210** | |

The canonical authoritative list will be maintained in
`docs/audits/SMP_THEOREM_INDEX.md` once WS-SM opens (created in
SM0).

## Appendix D — Verification quality ladder

WS-SM elevates seLe4n above seL4 on three verification axes:

| Axis | seL4 | seLe4n WS-SM |
|------|------|--------------|
| Lock-primitive correctness | Assumed | Formally proven (SM2) |
| Per-object lock discipline | BKL only | Per-object RW + hierarchical order (SM3) |
| Cross-core NI | Limited | Per-core observer model (SM8) |

The cost is the ~24-30 month timeline. The benefit is the most
rigorously verified SMP microkernel in the literature.

---

*This overview was produced from branch
`claude/audit-multicore-implementation-sUcIx` at v0.31.2. WS-RC
and WS-SM are merged into a single unified workstream that opens
immediately at the v0.31.2 boundary; WS-RC R0..R5 (already
LANDED) stand, R6..R14 absorb into SM-phases per SM0.Q. The
workstream closes at v1.0.0 with a bootable verified SMP
microkernel. All 13 maintainer decisions in §10 are binding for
this workstream.*

*This overview document is intentionally compact (~800 lines).
Deep per-phase detail — mathematical specifications, code
skeletons, proof structures, test plans, sub-task atomic
breakdowns — lives in the 10 phase planning documents listed in
Appendix A.*
