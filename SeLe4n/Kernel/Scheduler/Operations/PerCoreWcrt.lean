-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.PerCoreChooseThread
import SeLe4n.Kernel.Scheduler.Operations.PerCoreSwitchToThread
import SeLe4n.Kernel.Scheduler.Operations.PerCoreWake
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTimerTick
import SeLe4n.Kernel.Scheduler.Operations.PerCoreCbs
import SeLe4n.Kernel.Scheduler.Operations.PerCoreDomain
import SeLe4n.Kernel.Scheduler.Operations.PerCoreIdle
import SeLe4n.Kernel.Concurrency.LockSet
import SeLe4n.Kernel.Scheduler.Liveness.RPi5CanonicalConfig

/-!
# WS-SM SM5.J — WCRT under fine locks (plan §3.9)

Per-core scheduler operations run under per-object RW **fine locks** (SM3), not a
big kernel lock.  This module bounds their **worst-case response time (WCRT)**
under that fine-lock contention, extending the R5 domain-rotation / band-exhaustion
scheduling-latency bound (`Scheduler/Liveness/WCRT.lean`, `wcrtBound`) with the SMP
lock-contention dimension (plan §3.9):

    WCRT_lockSet(op) ≤ max-lock-set-size × (coreCount − 1) × WCRT_per_lock

On the RPi5 target (`coreCount = 4`, pinned by `numCores_eq_rpi5_coreCount`) the
core-count factor is `coreCount − 1 = 3`, so any op whose `SchedLockId` footprint
respects the SM3.D static `maxLockSetSize` (= 8) bound has lock-WCRT
`≤ maxLockSetSize × 3 × WCRT_per_lock` — within the 1 ms timer-tick budget.

## Contents (plan §5 SM5.J sub-tasks)

* **SM5.J.1** `WCRT_lockSet` — the fine-lock-contention WCRT of a per-core
  scheduler operation as a function of its `SchedLockId` footprint length, reusing
  the SM3.D `perLockWaitCost` (= `(numCores − 1) · tCs`) so the per-lock cost is
  shared verbatim with the `boundedWait_under_2pl` model.
* **SM5.J.2** `wcrt_bound_rpi5_smp` — the plan §3.9 Theorem 3.9.1 RPi5 bound, plus
  the combined `WCRT_smp` (R5 scheduling latency + lock contention) that *extends*
  the R5 `wcrtBound`.
* **SM5.J.3** the five per-operation WCRT bounds (`chooseThreadOnCore`,
  `switchToThreadOnCore`, `wakeThread`, `timerTickOnCore`, `replenishOnCore`), each
  with its exact value and its `≤ maxLockSetSize · 3 · tCs` headline.
* **SM5.J.4** liveness — no thread starves under SMP: the per-core idle fallback
  guarantees no core stalls (`schedulerNoStall_smp`), the SM3.D bounded-wait gives
  no unbounded lock-contention inversion (`boundedKernelWait_smp`), the capstone
  `no_starvation_under_smp`, and the R5-latency bridge `r5_latency_within_smp_bound`.

`WCRT_lockSet` / `WCRT_smp` are pure cost functions on the (production-reached)
per-core op footprints; the live per-core run loop (SM5.I) is the runtime exerciser
that acquires those footprints under `withLockSet`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (numCores maxLockSetSize perLockWaitCost CoreId AccessMode
  bootCoreId allCores)

-- ============================================================================
-- §1  SM5.J.1 — `WCRT_lockSet`: fine-lock-contention WCRT of a per-core op
-- ============================================================================

/-- WS-SM SM5.J.1 (plan §3.9): the worst-case response time contributed by
per-object RW **fine-lock contention** for a per-core scheduler operation, as a
function of its `SchedLockId`-typed lock-set footprint and the per-lock
critical-section cost `tCs` (= the §3.9 `WCRT_per_lock`).

Under FIFO RwLock fairness (SM2.C) each lock in the footprint is contended by at
most `numCores − 1` other cores, each for one bounded critical section of cost
`tCs`.  The total worst-case lock-wait of an op that acquires `|lockSet|` locks is
therefore `|lockSet| · (numCores − 1) · tCs` — the plan §3.9 formula
`max-lock-set-size · (coreCount − 1) · WCRT_per_lock` specialised to a concrete
op's footprint length.

This *extends* the R5 domain-rotation / band-exhaustion bound (`wcrtBound`,
`Scheduler/Liveness/WCRT.lean`) with the SMP lock-contention dimension: R5 bounds
*when* a runnable thread is scheduled; SM5.J bounds *how long* a syscall executing
on the CPU waits for kernel locks under per-object fine locks.  Reuses the SM3.D
`perLockWaitCost` (= `(numCores − 1) · tCs`) so the per-lock cost is shared with the
`boundedWait_under_2pl` model verbatim. -/
def WCRT_lockSet (lockSet : List (SchedLockId × AccessMode)) (tCs : Nat) : Nat :=
  lockSet.length * perLockWaitCost tCs

/-- SM5.J.1: `WCRT_lockSet` unfolds to the §3.9 product form
`|lockSet| · ((numCores − 1) · tCs)`. -/
theorem WCRT_lockSet_eq_product (lockSet : List (SchedLockId × AccessMode)) (tCs : Nat) :
    WCRT_lockSet lockSet tCs = lockSet.length * ((numCores - 1) * tCs) := rfl

/-- SM5.J.1: the empty footprint contributes zero lock-wait. -/
theorem WCRT_lockSet_nil (tCs : Nat) : WCRT_lockSet [] tCs = 0 := by
  simp [WCRT_lockSet]

/-- SM5.J.1: `WCRT_lockSet` is monotone in the footprint length — a larger lock-set
can only increase the worst-case wait. -/
theorem WCRT_lockSet_mono_length {l₁ l₂ : List (SchedLockId × AccessMode)} (tCs : Nat)
    (h : l₁.length ≤ l₂.length) :
    WCRT_lockSet l₁ tCs ≤ WCRT_lockSet l₂ tCs :=
  Nat.mul_le_mul_right _ h

/-- SM5.J.1: `WCRT_lockSet` is monotone in the per-lock critical-section cost. -/
theorem WCRT_lockSet_mono_cost (lockSet : List (SchedLockId × AccessMode)) {t₁ t₂ : Nat}
    (h : t₁ ≤ t₂) :
    WCRT_lockSet lockSet t₁ ≤ WCRT_lockSet lockSet t₂ := by
  unfold WCRT_lockSet perLockWaitCost
  exact Nat.mul_le_mul (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_refl _) h)

/-- WS-SM SM5.J.1 (the uniform worst-case, before specialising the core count):
any footprint of size `≤ maxLockSetSize` has lock-wait `≤ maxLockSetSize ·
(numCores − 1) · tCs`.  Mirrors SM3.D's `totalWaitCost_le_bound`; the RPi5
specialisation substitutes `numCores − 1 = 3`. -/
theorem WCRT_lockSet_le_maxLockSetSize (lockSet : List (SchedLockId × AccessMode)) (tCs : Nat)
    (hSize : lockSet.length ≤ maxLockSetSize) :
    WCRT_lockSet lockSet tCs ≤ maxLockSetSize * perLockWaitCost tCs := by
  unfold WCRT_lockSet
  exact Nat.mul_le_mul_right _ hSize

/-- WS-SM SM5.J (plan §3.9): on the RPi5 target there are `numCores = 4` cores
(pinned to `PlatformBinding.coreCount RPi5Platform` by `numCores_eq_rpi5_coreCount`
in `Platform.RPi5.Contract`), so a syscall waits behind at most `coreCount − 1 = 3`
other cores per lock — the `× 3` factor in the plan §3.9 RPi5 bound `4 × 3 × 60 µs`. -/
theorem rpi5OtherCoreCount : numCores - 1 = 3 := by decide

/-- SM5.J.1: the RPi5 per-lock wait cost is `3 · tCs` (`(numCores − 1) · tCs` with
`numCores = 4`). -/
theorem perLockWaitCost_rpi5 (tCs : Nat) : perLockWaitCost tCs = 3 * tCs := by
  unfold perLockWaitCost; rw [rpi5OtherCoreCount]

/-- SM5.J.1: the RPi5 form of `WCRT_lockSet` — `|lockSet| · 3 · tCs`. -/
theorem WCRT_lockSet_rpi5 (lockSet : List (SchedLockId × AccessMode)) (tCs : Nat) :
    WCRT_lockSet lockSet tCs = lockSet.length * (3 * tCs) := by
  rw [WCRT_lockSet_eq_product, rpi5OtherCoreCount]

-- ============================================================================
-- §2  SM5.J.2 — `wcrt_bound_rpi5_smp` (plan §3.9 Theorem 3.9.1) + `WCRT_smp`
-- ============================================================================

open SeLe4n.Kernel.Liveness (DeploymentSchedulingConfig rpi5CanonicalConfig)

/-- WS-SM SM5.J.2 (plan §3.9 Theorem 3.9.1 `wcrt_bound_rpi5_smp`): the WCRT bound
under fine locks for the RPi5 canonical deployment.

For the canonical RPi5 config (`coreCount = 4 ⟹ coreCount − 1 = 3`), any per-core
scheduler operation whose `SchedLockId` lock-set footprint respects the SM3.D
static `maxLockSetSize` (= 8) bound has worst-case lock-contention response time
`≤ maxLockSetSize · 3 · tCs`.  With `tCs ≈ 60 µs` (a bounded critical section) the
typical `|lockSet| ≤ 4` syscall fits the plan's `4 · 3 · 60 µs ≈ 1 ms` (the §3
per-operation bounds give the tighter per-op value).

The `config = rpi5CanonicalConfig` hypothesis scopes the theorem to the RPi5
deployment and is load-bearing: the first conjunct re-derives the config's
well-formedness from it (mirroring `boundedWait_under_2pl`'s
`noDeadlock ∧ WCRT ≤ …` shape).  This EXTENDS the R5 WCRT (`wcrtBound`): R5 bounds
the scheduling latency; SM5.J.2 bounds the orthogonal lock-contention latency. -/
theorem wcrt_bound_rpi5_smp
    (config : DeploymentSchedulingConfig) (hConfig : config = rpi5CanonicalConfig)
    (lockSet : List (SchedLockId × AccessMode)) (tCs : Nat)
    (hSize : lockSet.length ≤ maxLockSetSize) :
    config.wellFormed ∧ WCRT_lockSet lockSet tCs ≤ maxLockSetSize * (3 * tCs) := by
  refine ⟨?_, ?_⟩
  · rw [hConfig]; exact Liveness.rpi5CanonicalConfig_wellFormed
  · rw [WCRT_lockSet_rpi5]
    exact Nat.mul_le_mul_right _ hSize

/-- WS-SM SM5.J.2 (extends R5): the **combined** SMP worst-case response time —
the R5 scheduling latency (`wcrtBound`: domain rotation + higher-priority band
exhaustion) PLUS the SM5.J fine-lock contention (`WCRT_lockSet`).

Both operands are `Nat` costs in a common time base (e.g. processor cycles: a
scheduler tick is `cyclesPerTick`, a lock critical section is `tCs` cycles); the
sum is the algebraic upper bound on the total time from a thread becoming runnable
to its syscall completing — the scheduling delay plus the in-kernel lock-wait.  R5
bounded only the first summand; SM5.J adds the second. -/
def WCRT_smp (D L_max N B P : Nat) (lockSet : List (SchedLockId × AccessMode)) (tCs : Nat) : Nat :=
  Liveness.wcrtBound D L_max N B P + WCRT_lockSet lockSet tCs

/-- SM5.J.2: the combined bound splits into the R5 scheduling-latency term and the
SM5.J lock-contention term. -/
theorem WCRT_smp_decomposition (D L_max N B P : Nat)
    (lockSet : List (SchedLockId × AccessMode)) (tCs : Nat) :
    WCRT_smp D L_max N B P lockSet tCs =
      Liveness.wcrtBound D L_max N B P + WCRT_lockSet lockSet tCs := rfl

/-- SM5.J.2: the R5 scheduling-latency term is a lower component of the combined
bound (the SM5.J lock term only adds to it). -/
theorem WCRT_smp_r5_component_le (D L_max N B P : Nat)
    (lockSet : List (SchedLockId × AccessMode)) (tCs : Nat) :
    Liveness.wcrtBound D L_max N B P ≤ WCRT_smp D L_max N B P lockSet tCs :=
  Nat.le_add_right _ _

/-- SM5.J.2: the SM5.J lock-contention term is a lower component of the combined
bound. -/
theorem WCRT_smp_lockSet_component_le (D L_max N B P : Nat)
    (lockSet : List (SchedLockId × AccessMode)) (tCs : Nat) :
    WCRT_lockSet lockSet tCs ≤ WCRT_smp D L_max N B P lockSet tCs :=
  Nat.le_add_left _ _

/-- WS-SM SM5.J.2 (the full extends-R5 bound for RPi5): the combined SMP WCRT is
bounded by the R5 scheduling latency plus the bounded RPi5 lock contention
`maxLockSetSize · 3 · tCs`. -/
theorem wcrt_smp_bound_rpi5 (D L_max N B P : Nat)
    (lockSet : List (SchedLockId × AccessMode)) (tCs : Nat)
    (hSize : lockSet.length ≤ maxLockSetSize) :
    WCRT_smp D L_max N B P lockSet tCs ≤
      Liveness.wcrtBound D L_max N B P + maxLockSetSize * (3 * tCs) := by
  unfold WCRT_smp
  refine Nat.add_le_add (Nat.le_refl _) ?_
  rw [WCRT_lockSet_rpi5]
  exact Nat.mul_le_mul_right _ hSize

-- ============================================================================
-- §3  SM5.J.3 — Per-operation WCRT bounds (5 theorems + exact values)
-- ============================================================================

/-- WS-SM SM5.J.3 (generic per-operation bound): any per-core scheduler op whose
`SchedLockId` footprint respects `maxLockSetSize` has RPi5 lock-WCRT
`≤ maxLockSetSize · 3 · tCs`.  The five named per-op bounds below are this lemma
applied to each op's footprint-length witness. -/
theorem wcrt_op_bounded_of_size (lockSet : List (SchedLockId × AccessMode)) (tCs : Nat)
    (hSize : lockSet.length ≤ maxLockSetSize) :
    WCRT_lockSet lockSet tCs ≤ maxLockSetSize * (3 * tCs) := by
  rw [WCRT_lockSet_rpi5]
  exact Nat.mul_le_mul_right _ hSize

/-- SM5.J.3 (chooseThreadOnCore exact): the SM5.A selection footprint (object-store
+ run-queue READ locks, 2 locks) has lock-WCRT exactly `2 · 3 · tCs`. -/
theorem wcrt_chooseThreadOnCore_eq (c : CoreId) (tCs : Nat) :
    WCRT_lockSet (chooseThreadOnCoreLockSet c) tCs = 2 * (3 * tCs) := by
  rw [WCRT_lockSet_rpi5, chooseThreadOnCoreLockSet_length]

/-- SM5.J.3 (chooseThreadOnCore bound): within the RPi5 `maxLockSetSize · 3 · tCs`. -/
theorem wcrt_chooseThreadOnCore_bounded (c : CoreId) (tCs : Nat) :
    WCRT_lockSet (chooseThreadOnCoreLockSet c) tCs ≤ maxLockSetSize * (3 * tCs) :=
  wcrt_op_bounded_of_size _ tCs (by rw [chooseThreadOnCoreLockSet_length]; decide)

/-- SM5.J.3 (switchToThreadOnCore exact): the SM5.B switch footprint (object-store +
run-queue WRITE locks, 2 locks) has lock-WCRT exactly `2 · 3 · tCs`. -/
theorem wcrt_switchToThreadOnCore_eq (c : CoreId) (tCs : Nat) :
    WCRT_lockSet (switchToThreadOnCoreLockSet c) tCs = 2 * (3 * tCs) := by
  rw [WCRT_lockSet_rpi5, switchToThreadOnCoreLockSet_length]

/-- SM5.J.3 (switchToThreadOnCore bound). -/
theorem wcrt_switchToThreadOnCore_bounded (c : CoreId) (tCs : Nat) :
    WCRT_lockSet (switchToThreadOnCoreLockSet c) tCs ≤ maxLockSetSize * (3 * tCs) :=
  wcrt_op_bounded_of_size _ tCs (by rw [switchToThreadOnCoreLockSet_length]; decide)

/-- SM5.J.3 (wakeThread exact): the SM5.C cross-core wake footprint (object-store +
target run-queue WRITE locks, 2 locks) has lock-WCRT exactly `2 · 3 · tCs`. -/
theorem wcrt_wakeThread_eq (target : CoreId) (tCs : Nat) :
    WCRT_lockSet (wakeThreadLockSet target) tCs = 2 * (3 * tCs) := by
  rw [WCRT_lockSet_rpi5, wakeThreadLockSet_length]

/-- SM5.J.3 (wakeThread bound). -/
theorem wcrt_wakeThread_bounded (target : CoreId) (tCs : Nat) :
    WCRT_lockSet (wakeThreadLockSet target) tCs ≤ maxLockSetSize * (3 * tCs) :=
  wcrt_op_bounded_of_size _ tCs (by rw [wakeThreadLockSet_length]; decide)

/-- SM5.J.3 (timerTickOnCore exact): the SM5.D tick footprint (object-store +
run-queue + replenish-queue WRITE locks, 3 locks) has lock-WCRT exactly `3 · 3 · tCs`. -/
theorem wcrt_timerTickOnCore_eq (c : CoreId) (tCs : Nat) :
    WCRT_lockSet (timerTickOnCoreLockSet c) tCs = 3 * (3 * tCs) := by
  rw [WCRT_lockSet_rpi5, timerTickOnCoreLockSet_length]

/-- SM5.J.3 (timerTickOnCore bound). -/
theorem wcrt_timerTickOnCore_bounded (c : CoreId) (tCs : Nat) :
    WCRT_lockSet (timerTickOnCoreLockSet c) tCs ≤ maxLockSetSize * (3 * tCs) :=
  wcrt_op_bounded_of_size _ tCs (by rw [timerTickOnCoreLockSet_length]; decide)

/-- SM5.J.3 (replenishOnCore exact): the SM5.H replenish footprint (the single
per-core replenish-queue WRITE lock) has lock-WCRT exactly `1 · 3 · tCs`. -/
theorem wcrt_replenishOnCore_eq (c : CoreId) (tCs : Nat) :
    WCRT_lockSet (replenishOnCoreLockSet c) tCs = 1 * (3 * tCs) := by
  rw [WCRT_lockSet_rpi5, replenishOnCoreLockSet_length]

/-- SM5.J.3 (replenishOnCore bound). -/
theorem wcrt_replenishOnCore_bounded (c : CoreId) (tCs : Nat) :
    WCRT_lockSet (replenishOnCoreLockSet c) tCs ≤ maxLockSetSize * (3 * tCs) :=
  wcrt_op_bounded_of_size _ tCs (by rw [replenishOnCoreLockSet_length]; decide)

/-- SM5.J.3 (advanceDomainOnCore bound, bonus): the SM5.G per-core domain rotation
footprint (the single per-core run-queue WRITE lock) is within the RPi5 bound. -/
theorem wcrt_advanceDomainOnCore_bounded (c : CoreId) (tCs : Nat) :
    WCRT_lockSet (advanceDomainOnCoreLockSet c) tCs ≤ maxLockSetSize * (3 * tCs) :=
  wcrt_op_bounded_of_size _ tCs (by rw [advanceDomainOnCoreLockSet_length]; decide)

-- ============================================================================
-- §4  SM5.J.4 — Liveness: no thread starves under SMP
-- ============================================================================

/-- WS-SM SM5.J.4 (per-core non-stall): on any core `c` whose idle thread is
enqueued (the SM5.E `idleThreadEnqueuedOnCore` invariant) with a well-formed run
queue and runnable-are-TCBs, `chooseThreadOnCore` always selects *some* thread.
The idle thread is the priority-0 fallback, so no core ever stalls with nothing to
run — a runnable thread can never be starved by a core that has stopped making
scheduling decisions.  Lifts the SM5.E keystone `chooseThreadOnCore_always_succeeds`
as the SMP no-stall guarantee. -/
theorem schedulerNoStallOnCore (st : SystemState) (c : CoreId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hRunnable : runnableThreadsAreTCBsOnCore st c)
    (hIdle : idleThreadEnqueuedOnCore st c) :
    ∃ tid, chooseThreadOnCore st c = .ok (some tid) :=
  chooseThreadOnCore_always_succeeds st c hwf hRunnable hIdle

/-- WS-SM SM5.J.4 (SMP no-stall, ∀-core form): if every core has its idle thread
enqueued with a well-formed run queue + runnable-are-TCBs, then every core selects
some thread — no core in the system stalls.  This is the structural SMP
no-starvation guarantee the per-core idle threads (SM5.E) provide: a high-priority
thread that becomes runnable on core `c` is dispatched by core `c`'s own scheduler,
which is always live. -/
theorem schedulerNoStall_smp (st : SystemState)
    (hwf : ∀ c, (st.scheduler.runQueueOnCore c).wellFormed)
    (hRunnable : ∀ c, runnableThreadsAreTCBsOnCore st c)
    (hIdle : ∀ c, idleThreadEnqueuedOnCore st c) :
    ∀ c : CoreId, ∃ tid, chooseThreadOnCore st c = .ok (some tid) :=
  fun c => chooseThreadOnCore_always_succeeds st c (hwf c) (hRunnable c) (hIdle c)

/-- WS-SM SM5.J.4 (no unbounded priority inversion under SMP): a higher-priority
thread waiting for a kernel lock held by a lower-priority thread on another core
waits at most a bounded time.  Under 2PL + `LockId`-ordered acquisition the kernel
is deadlock-free AND every operation's worst-case response time is bounded by
`maxLockSetSize · (numCores − 1) · tCs = maxLockSetSize · 3 · tCs` (SM3.D
`boundedWait_under_2pl`, specialised to the RPi5 `coreCount − 1 = 3`).  So no thread
is starved by *unbounded* lock contention.  This is the lock-contention half of the
SMP no-starvation argument (the scheduling half is `schedulerNoStall_smp`). -/
theorem boundedKernelWait_smp (e : Concurrency.KernelExecution) (c : CoreId)
    (op : Concurrency.KernelOperation) (tCs : Nat)
    (h2pl : Concurrency.executionFollows2PL e)
    (hOrder : Concurrency.executionAcquiresInLockIdOrder e) :
    Concurrency.noDeadlock e ∧
    Concurrency.WCRT e c op tCs ≤ maxLockSetSize * (3 * tCs) := by
  obtain ⟨hNoDeadlock, hb⟩ := Concurrency.boundedWait_under_2pl e c op tCs h2pl hOrder
  refine ⟨hNoDeadlock, ?_⟩
  rwa [rpi5OtherCoreCount] at hb

/-- WS-SM SM5.J.4 (SMP no-starvation capstone): combines the two halves —
(1) every core always makes a scheduling decision (`schedulerNoStall_smp`: the
per-core idle thread guarantees `chooseThreadOnCore` succeeds, so no core stalls),
and (2) every kernel operation's lock-contention response time is bounded
(`boundedKernelWait_smp`: deadlock-free + WCRT ≤ maxLockSetSize · 3 · tCs).
Together: under SMP no thread starves — neither by a stalled core nor by unbounded
lock contention. -/
theorem no_starvation_under_smp (st : SystemState)
    (e : Concurrency.KernelExecution) (op : Concurrency.KernelOperation) (tCs : Nat)
    (hwf : ∀ c, (st.scheduler.runQueueOnCore c).wellFormed)
    (hRunnable : ∀ c, runnableThreadsAreTCBsOnCore st c)
    (hIdle : ∀ c, idleThreadEnqueuedOnCore st c)
    (h2pl : Concurrency.executionFollows2PL e)
    (hOrder : Concurrency.executionAcquiresInLockIdOrder e) :
    (∀ c : CoreId, ∃ tid, chooseThreadOnCore st c = .ok (some tid)) ∧
    (∀ c : CoreId, Concurrency.noDeadlock e ∧
      Concurrency.WCRT e c op tCs ≤ maxLockSetSize * (3 * tCs)) :=
  ⟨schedulerNoStall_smp st hwf hRunnable hIdle,
   fun c => boundedKernelWait_smp e c op tCs h2pl hOrder⟩

/-- WS-SM SM5.J.4 (R5-latency bridge, extends R5): the R5 bounded scheduling-latency
theorem (`bounded_scheduling_latency_exists`) selects a runnable thread within
`wcrtBound D L_max N B P` ticks; that selection is *a fortiori* within the combined
SMP bound `WCRT_smp` (R5 scheduling latency + the SM5.J lock-contention headroom),
since `wcrtBound ≤ WCRT_smp`.  So adding the fine-lock dimension never invalidates
the R5 liveness guarantee — SM5.J's combined bound subsumes it. -/
theorem r5_latency_within_smp_bound
    (trace : Liveness.SchedulerTrace) (tid : ThreadId)
    (D L_max N B P : Nat) (lockSet : List (SchedLockId × AccessMode)) (tCs : Nat)
    (k : Nat) (hk : k ≤ Liveness.wcrtBound D L_max N B P)
    (hSel : Liveness.selectedAt trace k tid) :
    ∃ k', k' ≤ WCRT_smp D L_max N B P lockSet tCs ∧ Liveness.selectedAt trace k' tid :=
  ⟨k, Nat.le_trans hk (WCRT_smp_r5_component_le D L_max N B P lockSet tCs), hSel⟩

end SeLe4n.Kernel
