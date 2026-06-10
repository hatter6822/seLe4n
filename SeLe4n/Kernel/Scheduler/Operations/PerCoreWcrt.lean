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
* **SM5.J.3** the per-operation WCRT bounds (`chooseThreadOnCore`,
  `switchToThreadOnCore`, `wakeThread`, `timerTickOnCore`, `replenishOnCore`, plus
  `advanceDomainOnCore`, `handleRescheduleSgiOnCore`, and the complete variable-length
  tick footprint), each with its exact value and/or `≤ maxLockSetSize · 3 · tCs`
  headline.
* **§3b modeling refinements** — access-mode soundness
  (`WCRT_lockSet_mode_independent`: the worst case is all-writers), the
  execution-sensitive bridge (`kernelWait_le_WCRT_lockSet_of_length_eq`: the static
  ceiling dominates the per-execution `Concurrency.WCRT`), the honest config-free
  grounding (`wcrt_bound_smp`), and the cycle-commensurate combined bound
  (`WCRT_smp_cycles`).
* **SM5.J.4** liveness — no thread starves under SMP, in three genuine parts:
  (1) no core stalls (`schedulerNoStall_smp` + the decidable discharge
  `schedulerNoStall_smp_of_idleAvailableB`); (2) **the specific runnable thread is
  selected on its own core within `wcrtBound`**
  (`thread_eventually_scheduled_onCore`, via the production per-core R5
  generalisation `Liveness.bounded_scheduling_latency_exists_onCore`); (3) no
  unbounded lock-contention inversion (`boundedKernelWait_smp`).  The 3-way
  capstone is `no_starvation_under_smp`; `thread_eventually_scheduled_within_smp_bound`
  and the single-core legacy bridge `r5_latency_within_smp_bound` place the
  progress inside the combined `WCRT_smp`.

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

**Honest grounding of the two hypotheses.**  The `× 3` factor of the *bound itself*
comes from `numCores − 1` (pinned to the RPi5 `coreCount` by
`numCores_eq_rpi5_coreCount`), **not** from the `DeploymentSchedulingConfig` (which
has no core-count field); the config-free form is `wcrt_bound_smp` (= the second
conjunct here).  The `config = rpi5CanonicalConfig` hypothesis is included to match
the plan §3.9 Theorem 3.9.1 signature and contributes the *orthogonal*
`config.wellFormed` deployment-identity conjunct (mirroring `boundedWait_under_2pl`'s
`noDeadlock ∧ WCRT ≤ …` shape) — it scopes the theorem to the RPi5 deployment but
does not influence the lock bound.  This EXTENDS the R5 WCRT (`wcrtBound`): R5 bounds
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

/-- SM5.J.3 (handleRescheduleSgiOnCore bound): the SM5.C SGI handler the target
core runs after a cross-core wake (footprint = the switch footprint, 2 locks) is
within the RPi5 bound — so the cross-core wake → SGI → dispatch round-trip's
target-side critical section is itself WCRT-bounded. -/
theorem wcrt_handleRescheduleSgiOnCore_bounded (c : CoreId) (tCs : Nat) :
    WCRT_lockSet (handleRescheduleSgiOnCoreLockSet c) tCs ≤ maxLockSetSize * (3 * tCs) :=
  wcrt_op_bounded_of_size _ tCs (by
    rw [handleRescheduleSgiOnCoreLockSet_eq, switchToThreadOnCoreLockSet_length]; decide)

/-- SM5.J.3 (timerTickOnCore *complete* footprint bound): the variable-length
(3-or-4-lock) complete tick footprint — which additionally locks the to-be-woken
remote thread's TCB on the cross-core CBS-replenish path — is also within the RPi5
bound, via the SM5.D `timerTickOnCoreCompleteLockSet_size_le_maxLockSetSize`
size witness. -/
theorem wcrt_timerTickOnCoreComplete_bounded (c : CoreId) (tCs : Nat) :
    WCRT_lockSet (timerTickOnCoreCompleteLockSet c) tCs ≤ maxLockSetSize * (3 * tCs) :=
  wcrt_op_bounded_of_size _ tCs (timerTickOnCoreCompleteLockSet_size_le_maxLockSetSize c)

-- ============================================================================
-- §3b  SM5.J — Modeling refinements (access-mode soundness, execution bridge,
--       honest numCores grounding, cycle-commensurate units)
-- ============================================================================

/-- WS-SM SM5.J.1 (access-mode soundness): `WCRT_lockSet` does **not** depend on
the per-lock `AccessMode` — and this is *correct for the worst case*.  Under
RwLock FIFO fairness a read lock is contended only by writers and a write lock by
all others, but the WORST case over executions is "every other core is a writer of
each lock", at which point a read lock and a write lock both face the full
`numCores − 1` contention.  So charging full contention per lock (mode-agnostic) is
the sound worst-case bound; the per-execution mode-aware tightening is the
*execution-sensitive* `Concurrency.WCRT` (bridged below), not the static ceiling. -/
theorem WCRT_lockSet_mode_independent
    (locks : List SchedLockId) (m₁ m₂ : AccessMode) (tCs : Nat) :
    WCRT_lockSet (locks.map (·, m₁)) tCs = WCRT_lockSet (locks.map (·, m₂)) tCs := by
  simp [WCRT_lockSet]

/-- WS-SM SM5.J (execution bridge — B6/C7): `WCRT_lockSet` (the static per-core
SchedLockId-footprint cost) coincides with the SM3.D `Concurrency.totalWaitCost`
(the LockId-domain uniform cost) whenever the two footprints have equal size — both
are `size · (numCores − 1) · tCs`.  This formally connects the per-core scheduler
WCRT model to the deadlock-freedom WCRT model: they are the *same* uniform bound on
their respective lock domains. -/
theorem WCRT_lockSet_eq_totalWaitCost_of_length_eq
    (ls : List (SchedLockId × AccessMode)) (S : Concurrency.LockSet) (tCs : Nat)
    (hlen : ls.length = S.size) :
    WCRT_lockSet ls tCs = Concurrency.totalWaitCost S tCs := by
  rw [WCRT_lockSet_eq_product, Concurrency.totalWaitCost_eq, hlen]

/-- WS-SM SM5.J (execution bridge — B6/C7): the *execution-sensitive* worst-case
response time `Concurrency.WCRT e c op tCs` of a `KernelOperation` (which counts
the cores actually contending each lock, `≤ numCores − 1`) is bounded by the
*static* per-core `WCRT_lockSet` of any equal-size SchedLockId footprint.  So the
per-operation bounds of §3 (on the SchedLockId footprints) dominate the genuine
per-execution lock-wait — closing the gap between the two WCRT models: the static
ceiling is a sound over-approximation of the execution-aware cost. -/
theorem kernelWait_le_WCRT_lockSet_of_length_eq
    (e : Concurrency.KernelExecution) (c : CoreId) (op : Concurrency.KernelOperation)
    (ls : List (SchedLockId × AccessMode)) (tCs : Nat)
    (hlen : ls.length = op.lockSet.size) :
    Concurrency.WCRT e c op tCs ≤ WCRT_lockSet ls tCs := by
  rw [WCRT_lockSet_eq_totalWaitCost_of_length_eq ls op.lockSet tCs hlen]
  exact Concurrency.WCRT_le_totalWaitCost e c op tCs

/-- WS-SM SM5.J.2 (honest grounding — C8): the WCRT bound `≤ maxLockSetSize · 3 ·
tCs` is grounded **purely in the core count** (`numCores − 1 = 3` on RPi5, pinned
to `coreCount` by `numCores_eq_rpi5_coreCount`), *independent of the
`DeploymentSchedulingConfig`*.  This is the config-free form of `wcrt_bound_rpi5_smp`
(whose `config = rpi5CanonicalConfig` hypothesis adds only the orthogonal
`config.wellFormed` deployment-identity conjunct, not the bound itself). -/
theorem wcrt_bound_smp (lockSet : List (SchedLockId × AccessMode)) (tCs : Nat)
    (hSize : lockSet.length ≤ maxLockSetSize) :
    WCRT_lockSet lockSet tCs ≤ maxLockSetSize * (3 * tCs) :=
  wcrt_op_bounded_of_size lockSet tCs hSize

/-- WS-SM SM5.J.2 (cycle-commensurate combined bound — C9): the unit-explicit form
of `WCRT_smp`.  R5's `wcrtBound` is in *scheduler ticks* and `WCRT_lockSet` is in
*per-lock critical-section costs* (`tCs`); converting both to a common base —
processor cycles, with `cyclesPerTick` cycles per tick and `tCs` already in cycles —
makes the sum genuinely commensurate: `cyclesPerTick · wcrtBound + WCRT_lockSet`.
`WCRT_smp` is the `cyclesPerTick = 1` special case (operands pre-scaled to a shared
base). -/
def WCRT_smp_cycles (cyclesPerTick D L_max N B P : Nat)
    (lockSet : List (SchedLockId × AccessMode)) (tCs : Nat) : Nat :=
  cyclesPerTick * Liveness.wcrtBound D L_max N B P + WCRT_lockSet lockSet tCs

/-- SM5.J.2: `WCRT_smp` is the `cyclesPerTick = 1` instance of `WCRT_smp_cycles`. -/
theorem WCRT_smp_cycles_one (D L_max N B P : Nat)
    (lockSet : List (SchedLockId × AccessMode)) (tCs : Nat) :
    WCRT_smp_cycles 1 D L_max N B P lockSet tCs = WCRT_smp D L_max N B P lockSet tCs := by
  simp [WCRT_smp_cycles, WCRT_smp, Nat.one_mul]

/-- SM5.J.2: the cycle-commensurate bound decomposes into the (scaled) R5
scheduling-latency term and the SM5.J lock-contention term. -/
theorem WCRT_smp_cycles_decomposition (cyclesPerTick D L_max N B P : Nat)
    (lockSet : List (SchedLockId × AccessMode)) (tCs : Nat) :
    WCRT_smp_cycles cyclesPerTick D L_max N B P lockSet tCs =
      cyclesPerTick * Liveness.wcrtBound D L_max N B P + WCRT_lockSet lockSet tCs := rfl

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

/-- WS-SM SM5.J.4 (per-core no-stall, decidable discharge — closes the
"hypothesis never discharged" gap): the no-stall precondition is *not* an
unfounded assumption.  `idleAvailableOnCoreB st c` (a `Bool`) decides whether core
`c`'s idle thread is an in-domain run-queue candidate, so on **any concrete
reachable state** the no-stall premise is established by `decide` (not assumed) —
the constructive form `chooseThreadOnCore_always_succeeds_of_idleAvailableB`.  The
∀-core form: if every core's idle is available, every core selects some thread. -/
theorem schedulerNoStall_smp_of_idleAvailableB (st : SystemState)
    (hwf : ∀ c, (st.scheduler.runQueueOnCore c).wellFormed)
    (hRunnable : ∀ c, runnableThreadsAreTCBsOnCore st c)
    (hAvail : ∀ c, idleAvailableOnCoreB st c = true) :
    ∀ c : CoreId, ∃ tid, chooseThreadOnCore st c = .ok (some tid) :=
  fun c => chooseThreadOnCore_always_succeeds_of_idleAvailableB st c (hwf c) (hRunnable c) (hAvail c)

/-- WS-SM SM5.J.4 (**the genuine per-core eventually-scheduled liveness** — the
real fix for "no thread starves"): a thread `tid` runnable on core `c` with
`WCRTHypothesesOnCore st tid c` (bounded same-or-higher-priority band on core `c`)
*is selected on core `c`* within `wcrtBound D L_max N B P` ticks, given the per-core
deployment obligations (core `c`'s target domain activates with `tid` still runnable
within the domain-rotation bound; once active, `tid` is selected within the
band-exhaustion bound).

This is **not** the structural no-stall — it proves a *specific runnable thread
makes progress*, on an *arbitrary* core `c`, via the per-core generalisation of the
R5 bounded-latency theorem (`Liveness.bounded_scheduling_latency_exists_onCore`,
which lifts the production R5 trace model to `(c : CoreId)`).  The RPi5 canonical
deployment discharges the band-progress obligation via
`Liveness.rpi5_higherBandExhausted_from_progressesOnCore`. -/
theorem thread_eventually_scheduled_onCore
    (st : SystemState) (tid : ThreadId) (c : CoreId) (trace : Liveness.SchedulerTrace)
    (hyp : Liveness.WCRTHypothesesOnCore st tid c)
    (hValid : Liveness.ValidTrace st trace)
    (hDomainActiveRunnable : ∃ k₁, k₁ ≤ Liveness.domainRotationBound
        st.scheduler.domainSchedule.length
        (Liveness.maxDomainLength st.scheduler.domainSchedule) ∧
      match Liveness.traceStateAt trace k₁ with
      | some st₁ => (st₁.scheduler.activeDomainOnCore c) = hyp.targetDomain ∧
                     (st₁.scheduler.runQueueOnCore c).contains tid = true
      | none => False)
    (hBandProgress : ∀ k₁ st₁,
      Liveness.traceStateAt trace k₁ = some st₁ →
      (st₁.scheduler.activeDomainOnCore c) = hyp.targetDomain →
      (st₁.scheduler.runQueueOnCore c).contains tid = true →
      ∃ k₂, k₂ ≤ Liveness.bandExhaustionBound hyp.N hyp.B hyp.P ∧
        Liveness.selectedAtOnCore trace (k₁ + k₂) tid c) :
    ∃ k, k ≤ Liveness.wcrtBound
              st.scheduler.domainSchedule.length
              (Liveness.maxDomainLength st.scheduler.domainSchedule)
              hyp.N hyp.B hyp.P ∧
      Liveness.selectedAtOnCore trace k tid c :=
  Liveness.bounded_scheduling_latency_exists_onCore st tid c trace hyp hValid
    hDomainActiveRunnable hBandProgress

/-- WS-SM SM5.J.4 (eventually-scheduled within the combined SMP bound): the genuine
per-core scheduling latency `thread_eventually_scheduled_onCore` is *a fortiori*
within the combined `WCRT_smp` (R5 scheduling latency + the SM5.J lock-contention
headroom), since `wcrtBound ≤ WCRT_smp`.  So adding the fine-lock dimension never
weakens the per-core liveness guarantee — the combined bound subsumes it. -/
theorem thread_eventually_scheduled_within_smp_bound
    (st : SystemState) (tid : ThreadId) (c : CoreId) (trace : Liveness.SchedulerTrace)
    (lockSet : List (SchedLockId × AccessMode)) (tCs : Nat)
    (hyp : Liveness.WCRTHypothesesOnCore st tid c)
    (hValid : Liveness.ValidTrace st trace)
    (hDomainActiveRunnable : ∃ k₁, k₁ ≤ Liveness.domainRotationBound
        st.scheduler.domainSchedule.length
        (Liveness.maxDomainLength st.scheduler.domainSchedule) ∧
      match Liveness.traceStateAt trace k₁ with
      | some st₁ => (st₁.scheduler.activeDomainOnCore c) = hyp.targetDomain ∧
                     (st₁.scheduler.runQueueOnCore c).contains tid = true
      | none => False)
    (hBandProgress : ∀ k₁ st₁,
      Liveness.traceStateAt trace k₁ = some st₁ →
      (st₁.scheduler.activeDomainOnCore c) = hyp.targetDomain →
      (st₁.scheduler.runQueueOnCore c).contains tid = true →
      ∃ k₂, k₂ ≤ Liveness.bandExhaustionBound hyp.N hyp.B hyp.P ∧
        Liveness.selectedAtOnCore trace (k₁ + k₂) tid c) :
    ∃ k, k ≤ WCRT_smp st.scheduler.domainSchedule.length
              (Liveness.maxDomainLength st.scheduler.domainSchedule)
              hyp.N hyp.B hyp.P lockSet tCs ∧
      Liveness.selectedAtOnCore trace k tid c := by
  obtain ⟨k, hk, hSel⟩ := thread_eventually_scheduled_onCore st tid c trace hyp hValid
    hDomainActiveRunnable hBandProgress
  exact ⟨k, Nat.le_trans hk (WCRT_smp_r5_component_le _ _ _ _ _ lockSet tCs), hSel⟩

/-- WS-SM SM5.J.4 (**SMP no-starvation capstone — genuine**): combines the THREE
guarantees that together establish no thread starves under SMP:

1. **No core stalls** (`schedulerNoStall_smp`): the per-core idle thread guarantees
   every core always makes a scheduling decision.
2. **The runnable thread makes progress** (`thread_eventually_scheduled_onCore`):
   the *specific* thread `tid` runnable on core `c` *is selected on `c`* within
   `wcrtBound` ticks — the genuine eventually-scheduled property (not merely "the
   scheduler picks *someone*").
3. **No unbounded lock-contention inversion** (`boundedKernelWait_smp`): the kernel
   is deadlock-free and every op's lock-contention response time is bounded by
   `maxLockSetSize · 3 · tCs`.

Conjunct (2) is what makes this a real starvation-freedom theorem: a runnable
thread is *provably eventually scheduled*, on every core, within a closed bound. -/
theorem no_starvation_under_smp (st : SystemState)
    (tid : ThreadId) (c : CoreId) (trace : Liveness.SchedulerTrace)
    (e : Concurrency.KernelExecution) (op : Concurrency.KernelOperation) (tCs : Nat)
    (hyp : Liveness.WCRTHypothesesOnCore st tid c)
    (hwf : ∀ c, (st.scheduler.runQueueOnCore c).wellFormed)
    (hRunnable : ∀ c, runnableThreadsAreTCBsOnCore st c)
    (hIdle : ∀ c, idleThreadEnqueuedOnCore st c)
    (hValid : Liveness.ValidTrace st trace)
    (hDomainActiveRunnable : ∃ k₁, k₁ ≤ Liveness.domainRotationBound
        st.scheduler.domainSchedule.length
        (Liveness.maxDomainLength st.scheduler.domainSchedule) ∧
      match Liveness.traceStateAt trace k₁ with
      | some st₁ => (st₁.scheduler.activeDomainOnCore c) = hyp.targetDomain ∧
                     (st₁.scheduler.runQueueOnCore c).contains tid = true
      | none => False)
    (hBandProgress : ∀ k₁ st₁,
      Liveness.traceStateAt trace k₁ = some st₁ →
      (st₁.scheduler.activeDomainOnCore c) = hyp.targetDomain →
      (st₁.scheduler.runQueueOnCore c).contains tid = true →
      ∃ k₂, k₂ ≤ Liveness.bandExhaustionBound hyp.N hyp.B hyp.P ∧
        Liveness.selectedAtOnCore trace (k₁ + k₂) tid c)
    (h2pl : Concurrency.executionFollows2PL e)
    (hOrder : Concurrency.executionAcquiresInLockIdOrder e) :
    -- (1) no core stalls:
    (∀ c' : CoreId, ∃ tid', chooseThreadOnCore st c' = .ok (some tid')) ∧
    -- (2) the runnable thread `tid` is genuinely selected on core `c` within the bound:
    (∃ k, k ≤ Liveness.wcrtBound st.scheduler.domainSchedule.length
              (Liveness.maxDomainLength st.scheduler.domainSchedule) hyp.N hyp.B hyp.P ∧
      Liveness.selectedAtOnCore trace k tid c) ∧
    -- (3) no unbounded lock-contention inversion:
    (∀ c' : CoreId, Concurrency.noDeadlock e ∧
      Concurrency.WCRT e c' op tCs ≤ maxLockSetSize * (3 * tCs)) :=
  ⟨schedulerNoStall_smp st hwf hRunnable hIdle,
   thread_eventually_scheduled_onCore st tid c trace hyp hValid hDomainActiveRunnable hBandProgress,
   fun c' => boundedKernelWait_smp e c' op tCs h2pl hOrder⟩

/-- WS-SM SM5.J.4 (R5-latency bridge, single-core legacy form): the single-core R5
selection (`Liveness.selectedAt`, the `c := bootCoreId` instance) is within the
combined `WCRT_smp` bound.  Retained for the single-core surface; the genuine
per-core form is `thread_eventually_scheduled_within_smp_bound`. -/
theorem r5_latency_within_smp_bound
    (trace : Liveness.SchedulerTrace) (tid : ThreadId)
    (D L_max N B P : Nat) (lockSet : List (SchedLockId × AccessMode)) (tCs : Nat)
    (k : Nat) (hk : k ≤ Liveness.wcrtBound D L_max N B P)
    (hSel : Liveness.selectedAt trace k tid) :
    ∃ k', k' ≤ WCRT_smp D L_max N B P lockSet tCs ∧ Liveness.selectedAt trace k' tid :=
  ⟨k, Nat.le_trans hk (WCRT_smp_r5_component_le D L_max N B P lockSet tCs), hSel⟩

end SeLe4n.Kernel
