# SM5 — Per-Core Scheduler (WS-SM Phase 5)

> **Phase**: SM5 of WS-SM
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Audited cut**: `v0.31.2`
> **Target releases**: v0.71.0 .. v0.82.x
> **Calendar estimate**: 12-16 weeks
> **Sub-task count**: 75-95 across ~28-38 PRs

## 1. Phase goal

SM5 implements **per-core scheduling**: each core runs its own
scheduler, picking threads from its own run queue, with cross-
core notifications via SGI for events that change another core's
runnability state.

**Concrete deliverables**:

1. **Per-core chooseThread / switchToThread** (SM5.A, SM5.B):
   per-core selection of the highest-priority runnable thread;
   per-core context switch.
2. **Cross-core wake via SGI** (SM5.C): when a thread on core c'
   becomes runnable and its priority exceeds c''s current
   running thread, the originating core sends a `.reschedule`
   SGI to c'.
3. **Per-core timer tick** (SM5.D): each core's ARM Generic
   Timer fires independently; `timerTickOnCore` advances that
   core's domain state, processes CBS, emits preemption if a
   higher-priority thread becomes runnable.
4. **Per-core idle threads** (SM5.E): one idle TCB per core,
   bound to its core, never migrates.
5. **Per-core PIP** (SM5.F): priority inheritance protocol per
   core; cross-core PIP boost via SGI.
6. **Per-core domain scheduling** (SM5.G): each core has its own
   domain rotation.
7. **Per-core CBS** (SM5.H): per-core replenishment queue;
   cross-core migration on `cpuAffinity` change.
8. **Per-core invariant suite** (SM5.I): aggregate per-core
   invariants.
9. **WCRT bound under fine locks** (SM5.J).
10. **Tests** (SM5.K).

## 2. Dependencies

- **SM3**: per-object lock-set discipline + serializability.
- **SM4**: per-core SchedulerState fields.
- **SM1.F**: SGI primitive in HAL.
- **SM1.B**: per-CPU data + TPIDR_EL1.

## 3. Mathematical foundations

### 3.1 Per-core scheduling decision

For a core c with its run queue and current thread, the
scheduling decision is:

    chooseThreadOnCore (s : SystemState) (c : CoreId) : Option ThreadId :=
      let rq := s.scheduler.runQueueOnCore c
      let activeDom := s.scheduler.activeDomainOnCore c
      -- Highest-priority runnable thread in activeDom.
      rq.selectHighestInDomain activeDom

**Theorem 3.1.1** (`chooseThreadOnCore_selects_highest`).

```lean
theorem chooseThreadOnCore_selects_highest (s : SystemState) (c : CoreId) :
    let chosen := chooseThreadOnCore s c
    ∀ tid ∈ chosen,
      ∀ otherTid ∈ s.scheduler.runQueueOnCore c |>.toList,
        otherTid ∈ activeDomain (s.scheduler.activeDomainOnCore c) →
        priority (lookupTcb s otherTid) ≤ priority (lookupTcb s tid)
```

*Proof.* By `RunQueue.selectHighest` correctness (existing R5
theorem, extended per-core). □

**Theorem 3.1.2** (`chooseThreadOnCore_perCore_independence`).

```lean
theorem chooseThreadOnCore_perCore_independence
    (s : SystemState) (c₁ c₂ : CoreId) (h : c₁ ≠ c₂) :
    chooseThreadOnCore s c₁ does NOT depend on s.scheduler.runQueueOnCore c₂
```

Formal statement: `chooseThreadOnCore` reads only
`s.scheduler.runQueueOnCore c` and `s.scheduler.activeDomainOnCore c`
for its single c argument. By `Vector.get_set_ne` and structural
inspection of the definition.

### 3.2 Per-core switch

    switchToThreadOnCore
        (s : SystemState) (c : CoreId) (tid : ThreadId) :
        Result SystemState

Lock-set: `{(LockId.tcb tid, .write), (LockId.runQueue c, .write)}`.

**Theorem 3.2.1** (`switchToThreadOnCore_sets_current`).

```lean
theorem switchToThreadOnCore_sets_current
    (s : SystemState) (c : CoreId) (tid : ThreadId) :
    switchToThreadOnCore s c tid = .ok s' →
    s'.scheduler.currentOnCore c = some tid
```

**Theorem 3.2.2** (`switchToThreadOnCore_preempts_previous`).

When `switchToThreadOnCore` evicts the previous current thread,
that thread goes back to the same core's run queue (preempted
state).

**Theorem 3.2.3** (`switchToThreadOnCore_rejects_remote`).

If the target thread's `cpuAffinity` is bound to a different
core c' ≠ c, returns `.error .threadOnDifferentCore`. Migration
is a separate operation, not implicit in switch.

### 3.3 Cross-core wake protocol

When a thread `tid` becomes runnable (from blocked/waiting state),
its target core is determined by `tid`'s `cpuAffinity`:

    wakeThread (s : SystemState) (tid : ThreadId) :
        SystemState × Option (CoreId × SgiKind) :=
      let target := determineTargetCore s tid
      let s' := enqueueRunnableOnCore s target tid
      let executingCore := currentCoreId s
      let sgi := if target ≠ executingCore then
                   some (target, .reschedule)
                 else none
      (s', sgi)

The lock-set for `wakeThread`:
- `(LockId.tcb tid, .write)` — modify thread state to runnable.
- `(LockId.runQueue target, .write)` — append to run queue.
- (No lock on the executing core's run queue is needed; the wake
  operation reads but doesn't mutate it.)

**Theorem 3.3.1** (`wakeThread_emits_sgi_if_remote`).

```lean
theorem wakeThread_emits_sgi_if_remote
    (s : SystemState) (tid : ThreadId)
    (executingCore : CoreId) :
    let (s', sgi) := wakeThread s tid
    let target := determineTargetCore s tid
    target ≠ executingCore →
    sgi = some (target, SgiKind.reschedule)
```

**Theorem 3.3.2** (`wakeThread_lossless`).

```lean
theorem wakeThread_lossless
    (s : SystemState) (tid : ThreadId) :
    let (s', sgi) := wakeThread s tid
    let target := determineTargetCore s tid
    ∃ (futureState : SystemState),
      reachableFrom s' futureState ∧
      futureState.scheduler.currentOnCore target = some tid ∨
      tid ∈ futureState.scheduler.runQueueOnCore target |>.toList
```

(Assuming no higher-priority work preempts.)

### 3.4 Per-core timer tick

Each core has its own ARM Generic Timer (CNTP) firing locally.
On each tick, the per-core handler advances `domainTimeRemaining`,
processes CBS replenishment for SchedContexts bound to this core,
and emits preemption if a higher-priority thread becomes runnable.

    timerTickOnCore (s : SystemState) (c : CoreId) : SystemState :=
      let s := decrementDomainTimeOnCore s c
      let s := processCbsReplenishmentOnCore s c
      let s := emitPreemptionIfHigher s c
      s

Lock-set per timer tick:
- `(LockId.runQueue c, .write)`.
- `(LockId.replenishQueue c, .write)`.
- All TCB locks for threads whose SchedContext is bound to c
  (computed dynamically; lock-set may grow with the bound thread
  count).

### 3.5 Per-core idle threads

Per decision #8, one idle TCB per core:

    def idleThreadId (c : CoreId) : ThreadId :=
      ⟨ObjId.ofNat (idleThreadIdBase + c.val), proof⟩

    def createIdleThread (c : CoreId) : ThreadControlBlock :=
      { tid := idleThreadId c
      , priority := ⟨0, by decide⟩
      , state := .runnable
      , cpuAffinity := some c
      , -- other fields ...
      , lock := RwLock.unheld
      }

**Theorem 3.5.1** (`idleThread_core_locality`).

```lean
theorem idleThread_core_locality (s : SystemState) :
    ∀ c : CoreId,
      let idleTid := idleThreadId c
      idleTid ∉ s.scheduler.runQueueOnCore c.complement |>.toList
```

(The idle thread for core c never appears on another core's
run queue.)

**Theorem 3.5.2** (`chooseThreadOnCore_always_succeeds`).

```lean
theorem chooseThreadOnCore_always_succeeds (s : SystemState) (c : CoreId) :
    schedulerInvariant_perCore s c →
    chooseThreadOnCore s c = some _
```

Since `idleThreadId c` is always in c's run queue at priority 0
(by `bootFromPlatform_all_cores_have_idle`), and the run queue
is non-empty, `chooseThreadOnCore` returns some thread.

### 3.6 Per-core PIP

Priority inheritance under SMP: when a thread t on core c is
blocked on a resource held by a thread t' on core c', and t's
priority exceeds t''s, t' inherits t's priority (PIP boost). If
c' ≠ c, the boost emits a `.reschedule` SGI to c'.

    computeMaxWaiterPriorityOnCore
        (s : SystemState) (c : CoreId)
        (waitingThread : ThreadId) :
        Priority

Reads `s.scheduler.runQueueOnCore c` and the blocking graph for
threads on c.

**Theorem 3.6.1** (`pipBoost_perCore_consistent`).

```lean
theorem pipBoost_perCore_consistent (s : SystemState) :
    ∀ c : CoreId,
      ∀ tid : ThreadId, isHolderInBlockingGraph s tid →
        (computeMaxWaiterPriorityOnCore s c tid).val
        ≤ effectivePriority (lookupTcb s tid)
```

### 3.7 Per-core domain scheduling

Each core independently rotates its own domain schedule:

    activeDomainOnCore (s : SystemState) (c : CoreId) : DomainId :=
      s.scheduler.activeDomainOnCore c

    advanceDomainOnCore (s : SystemState) (c : CoreId) : SystemState :=
      let idx := s.scheduler.domainScheduleIndexOnCore c
      let nextIdx := (idx + 1) % s.scheduler.domainSchedule.length
      let nextDom := s.scheduler.domainSchedule.get? nextIdx |>.map (·.domain)
      { s with scheduler :=
          { s.scheduler with
            activeDomain := s.scheduler.activeDomain.set c (nextDom.getD ⟨0⟩)
            domainScheduleIndex := s.scheduler.domainScheduleIndex.set c nextIdx
            domainTimeRemaining := s.scheduler.domainTimeRemaining.set c
              (s.scheduler.domainSchedule.get? nextIdx |>.map (·.length) |>.getD 5) }}

**Theorem 3.7.1** (`activeDomainOnCore_isInDomainSchedule`).

```lean
theorem activeDomainOnCore_isInDomainSchedule (s : SystemState) :
    schedulerInvariant_perCore_smp s →
    ∀ c : CoreId,
      s.scheduler.activeDomainOnCore c ∈ s.scheduler.domainSchedule.map (·.domain)
```

### 3.8 Per-core CBS

The `replenishQueueOnCore c` holds the budget-refill schedule
for SchedContexts whose bound thread is on core c. Migration on
`cpuAffinity` change moves the SC's replenishment to the new
core's queue.

**Theorem 3.8.1** (`schedContextRunQueueConsistent_perCore`).

```lean
theorem schedContextRunQueueConsistent_perCore (s : SystemState) (c : CoreId) :
    ∀ sc ∈ s.scheduler.replenishQueueOnCore c |>.toList,
      let scObj := lookupSchedContext s sc.scid
      ∀ boundTcb ∈ scObj.boundTcb,
        (lookupTcb s boundTcb).cpuAffinity = some c
```

### 3.9 WCRT under fine locks

The WCRT bound under per-object RW fine locks:

    WCRT(syscall) ≤ max-lock-set-size × (coreCount - 1) × WCRT_per_lock

For RPi5 (coreCount = 4):
- Most syscalls have lock-set size ≤ 4.
- coreCount - 1 = 3.
- WCRT_per_lock ≈ 60 µs (bounded critical section).

So: `WCRT(syscall) ≤ 4 × 3 × 60 µs = 720 µs ≈ 1 ms`.

This fits within the 1 ms timer tick budget.

**Theorem 3.9.1** (`wcrt_bound_rpi5_smp`).

```lean
theorem wcrt_bound_rpi5_smp :
    ∀ (config : DeploymentSchedulingConfig),
      config = rpi5CanonicalConfig →
      ∀ (syscall : KernelTransition) (args : Args),
        WCRT syscall args ≤ maxLockSetSize × 3 × T_per_lock
```

## 4. Architectural choices

### 4.1 Why per-core run queues (not work-stealing)

Per-core run queues with affinity-bound threads simplify the
reasoning. Work-stealing would let a core "steal" runnable
threads from a busier core's queue, but:
- Stealing requires cross-core lock acquisition (more lock-set
  complexity).
- Migration changes the thread's `cpuAffinity` implicitly,
  complicating invariants.
- The performance benefit on a 4-core kernel is modest.

Decision: affinity-bound + cross-core wake (not steal). Future
v1.x performance work may add work-stealing.

### 4.2 Why per-core domain rotation

Decision: each core independently advances its domain schedule
(maintainer decision #7 implicit; matches per-core local
operation). Different cores can be in different domains
simultaneously, maximising parallelism while still bounding
per-domain CPU share.

Alternative considered: system-wide domain rotation (all cores
synchronously advance). Rejected: requires a system-wide tick
coordinator (more SGI traffic) and constrains parallelism.

### 4.3 Why per-core idle threads (not hardware idle)

Decision #8: per-core idle TCBs. Each core has a dedicated TCB
for its idle thread. The `chooseThreadOnCore_always_succeeds`
theorem then has a clean proof: idle is always a fallback.

Alternative: hardware idle (no TCB; scheduler returns `none`
and the HAL's `idle_loop` runs WFE). Rejected: requires the
scheduler proof to handle a `none` case specially.

### 4.4 Cross-core wake under BKL-free SMP

Wake is the trickiest cross-core operation. The wake routine:
1. Acquires write-lock on the waker's TCB.
2. Acquires write-lock on the target core's run queue.
3. Appends the waker to the run queue.
4. Emits `.reschedule` SGI to target core (if target ≠ executing).
5. Releases locks in reverse order.

The SGI handler on the target core:
1. Acquires its own run queue's write-lock.
2. Re-runs `chooseThreadOnCore` to pick the highest-priority
   thread.
3. Switches to it (lock-set extends to the chosen TCB).
4. Releases locks.

Deadlock cannot occur because of hierarchical lock order
(Theorem 2.1.9): TCB locks (kind level 3) are always acquired
before any run queue locks (handled via the LockId per object
ID).

## 5. Detailed sub-task breakdown

(Compact tables; full per-sub-task detail is structurally
similar to SM0/SM1 patterns.)

### SM5.A — Per-core chooseThread (5 PRs, 8 sub-tasks)

| Sub | Description | Est |
|-----|-------------|-----|
| SM5.A.1 | `chooseThreadOnCore (s, c) : Option ThreadId` | M |
| SM5.A.2 | Lock-set: `{(LockId.runQueue c, .read)}` | S |
| SM5.A.3 | `chooseThreadOnCore_perCore_independence` | M |
| SM5.A.4 | Idle-fallback completeness theorem | M |
| SM5.A.5 | Migrate legacy `chooseThread` to call per-core | S |
| SM5.A.6 | `chooseThreadOnCore_preserves_wellFormed` | M |
| SM5.A.7 | Decidability instance | T |
| SM5.A.8 | Unit tests (6 scenarios) | M |

### SM5.B — Per-core switchToThread (5 PRs, 9 sub-tasks)

| Sub | Description | Est |
|-----|-------------|-----|
| SM5.B.1 | `switchToThreadOnCore (s, c, tid)` | M |
| SM5.B.2 | Lock-set | S |
| SM5.B.3 | Preempt-previous discipline | M |
| SM5.B.4 | Reject-remote thread | M |
| SM5.B.5 | `runQueueOnCore_excludes_currentOnCore` | M |
| SM5.B.6 | Cross-core lock-set protection | M |
| SM5.B.7 | FFI: `ffi_switch_to_thread(tid, core_id)` | S |
| SM5.B.8 | Totality + decidability | S |
| SM5.B.9 | 8 unit-test scenarios | M |

### SM5.C — Cross-core wake via SGI (6 PRs, 12 sub-tasks)

| Sub | Description | Est |
|-----|-------------|-----|
| SM5.C.1 | `enqueueRunnableOnCore` | M |
| SM5.C.2 | `wakeThread (s, tid)` returning state + optional SGI | L |
| SM5.C.3 | Lock-set per wake | M |
| SM5.C.4 | SGI emission under BKL discipline | M |
| SM5.C.5 | SGI handler in target core (drains pending; re-chooses) | L |
| SM5.C.6 | `wakeThread_lossless` theorem | L |
| SM5.C.7 | `TCB.cpuAffinity : Option CoreId` field | S |
| SM5.C.8 | `setThreadCpuAffinity` capability op | M |
| SM5.C.9 | Boot-time default affinity = bootCoreId | S |
| SM5.C.10 | `wakeThread_target_runQueue_contains` | M |
| SM5.C.11 | SGI delivery latency bound | M |
| SM5.C.12 | Cross-core wake round-trip tests | L |

### SM5.D — Per-core timer tick (4 PRs, 10 sub-tasks)

| Sub | Description | Est |
|-----|-------------|-----|
| SM5.D.1 | Per-core CNTP timer ISR | M |
| SM5.D.2 | `timerTickOnCore (s, c)` body | L |
| SM5.D.3 | Lock-set per tick | M |
| SM5.D.4 | Cross-core CBS replenish wakes remote | L |
| SM5.D.5 | Per-core preempt on time-slice exhaust | M |
| SM5.D.6 | Per-core domain rotation | M |
| SM5.D.7 | WCRT-bounded tick | M |
| SM5.D.8 | Tick decidability | S |
| SM5.D.9 | Per-core lastTimeoutErrors clearing | S |
| SM5.D.10 | 8 tick scenarios | L |

> **WS-SM SM5.D LANDED at v0.31.41** (all 10 sub-tasks).  Production
> transitions (`timerTickOnCore`, `decrementDomainTimeOnCore`,
> `processReplenishmentsDueOnCore`, `timerTickBudgetOnCore`,
> `scheduleEffectiveOnCore`, `switchDomainOnCore`/`scheduleDomainOnCore`) in
> `Scheduler/Operations/Core.lean`; the SM5.D.3 lock-set (`ReplenishQueueLockId`
> + `SchedLockId.replenishQueue`, plan §4.4 object<runQueue<replenishQueue) in
> `PerCoreChooseThread.lean`; the staged theorem surface — SM5.D.3/.7 lock-set +
> WCRT, SM5.D.6 domain rotation, SM5.D.4 `cbsReplenish_can_wake_remote_core` +
> preservation, SM5.D.5 budget tick + the full IPC-timeout objects-`invExt`
> preservation chain, the SM5.D.2 headlines (`timerTickOnCore_advances_per_core`
> / `_preempts_local` / `_rotates_domain` / `_clears_lastTimeoutErrors`) +
> objects-`invExt` preservation, SM5.D.8 decidability — in
> `PerCoreTimerTick.lean` (all axiom-clean).  SM5.D.1: `timer::per_core_timer_tick_isr`
> + `handle_irq_per_core` wiring + the `lean_per_core_timer_tick` export seam
> (`PerCoreTimerEntry.lean`).  Tests: `tests/SmpTimerSuite.lean`; +4 Rust HAL
> tests.  The runtime per-core scheduler-tick driver (reading live per-core
> kernel state, committing under the `timerTickOnCoreLockSet` `withLockSet`
> bracket, emitting the cross-core SGIs) is SM5.I work — the pure transition +
> its full theorem surface land here.
>
> **WS-SM SM5.D audit-pass-1 LANDED at v0.31.42** (deep self-audit; closes the
> verification-completeness gaps the initial cut deferred).  Per the maintainer-
> approved **"parameterize + track"** decision: clean paths proved
> unconditionally; the bound-budget-exhausted timeout branch (re-enqueuing
> through the bootCoreId-pinned `ensureRunnable` / `revertPriorityInheritance`) is
> parameterized by a single clean hypothesis and recorded as explicit **SM5.F**
> (per-core PIP migration) tracked debt.  (1) **§4b** full per-core domain
> re-dispatch — `switchDomainOnCore` no-op / `_preserves_objects_invExt` /
> `_sets_currentOnCore_none` / `_rotates` + `scheduleDomainOnCore_decrements` /
> `_preserves_objects_invExt`.  (2) **§7** per-core invariant preservation
> (B1/B2/B3): `timerTickOnCore_preserves_currentThreadValidOnCore` UNCONDITIONAL
> (preempted re-establishment absorbs the timeout's object-store effect);
> `_preserves_runQueueOnCoreWellFormed` (B2) + `_preserves_queueCurrentConsistentOnCore`
> parameterized (clean-path discharge unconditional, bound-exhausted = SM5.F);
> full helper layer for `decrementDomainTimeOnCore` / `saveOutgoingContextOnCore` /
> `scheduleEffectiveOnCore` / `timerTickBudgetOnCore_notPreempted_*`.  (3) **D3**
> `Sm5DInventory.lean` (99-entry typed inventory, 7 categories, `s5dt!` macro).
> (4) **D4** `scripts/test_qemu_smp_timer.sh` tier-4 SKIP-stub.  C1 (full-path
> `machine.timer`) folds into the same SM5.F gap.  All axiom-clean; Tier 0–3
> green; partition gate 48 staged-only; trace byte-identical.
>
> **WS-SM SM5.D audit-pass-2 LANDED at v0.31.43** (deep code-first audit; PR #809).
> **CRITICAL FIX**: the pre-fix `timerTickOnCore` folded an in-tick domain *rotation*
> (`decrementDomainTimeOnCore`) into the tick **without** the coupled re-dispatch,
> breaking `currentThreadInActiveDomain` on multi-domain configs (the running thread's
> domain ≠ the rotated `activeDomainOnCore`).  This diverged from the single-core model
> (`timerTick` / `timerTickWithBudget` never touch domain time; rotation is the
> *atomic* `scheduleDomain` = `switchDomain` + `schedule`).  Fix: `timerTickOnCore` is
> now a **pure budget tick**; the §3.4 pseudocode above (which showed
> `decrementDomainTimeOnCore` in the tick) is superseded — per-core rotation is the
> separate atomic `scheduleDomainOnCore`.  `decrementDomainTimeOnCore` is the pure
> non-boundary decrement, wired into `scheduleDomainOnCore`'s `else`-branch.  Capstone:
> `timerTickOnCore_preserves_currentThreadInActiveDomainOnCore` *proves* the fix.
> Rust LOW findings fixed: the per-core timer is **CNTP** (EL1 physical, PPI 30) not
> "CNTV"; `per_core_timer_tick_isr` hw-only `debug_assert_eq!` on `core_id`;
> `reprogram_timer` `wrapping_add`.  Axiom-clean; `Sm5DInventory` 100 entries; Tier
> 0+1+2 green (722 Rust HAL tests, zero clippy); trace byte-identical.

### SM5.E — Per-core idle threads (3 PRs, 6 sub-tasks)

| Sub | Description | Est |
|-----|-------------|-----|
| SM5.E.1 | `idleThreadId (c)` def | S |
| SM5.E.2 | `createIdleThread (c)` ctor | S |
| SM5.E.3 | `bootFromPlatform` extension installing idle TCBs | M |
| SM5.E.4 | `idleThread_core_locality` theorem | M |
| SM5.E.5 | `idleThread_priority_zero` theorem | S |
| SM5.E.6 | `chooseThreadOnCore_always_succeeds` | M |

> **WS-SM SM5.E LANDED at v0.31.45; completion at v0.31.46; audit-pass-1 (dispatcher soundness parity — `scheduleOrIdleOnCore` brought to exact 6-property parity with `scheduleEffectiveOnCore`) at v0.31.47** (all 6 sub-tasks).
> First cut (v0.31.45): `createIdleThread` `cpuAffinity := some c` (SM5.E.2);
> `idleThread_priority_zero` (SM5.E.5) + field lemmas; the run-queue primitive
> `enqueueIdleThreadOnCore` (SM5.E.3); `chooseThreadOnCore_always_succeeds`
> (SM5.E.6, discharging the conditional SM5.A `chooseThreadOnCore_some_of_eligible`
> with the idle candidate, via the `idleThreadEnqueuedOnCore` predicate);
> `idleThread_core_locality` (SM5.E.4, affinity-based).  Staged
> `Scheduler/Operations/PerCoreIdle.lean` + `PerCoreIdleInventory.lean`; tests
> `tests/SmpIdleSuite.lean`.
>
> **Completion (v0.31.46)** — per maintainer directive, the **SM5.I per-core
> idle-aware dispatcher is pulled forward** so idle threads are *live in the
> running kernel*: `scheduleOrIdleOnCore` (production `Scheduler/Operations/Core.lean`,
> the SM5.I seed) runs core `c`'s idle thread when `scheduleEffectiveOnCore` finds
> nothing runnable, instead of `current = none` (conditional-fallback
> idle-if-installed-else-`none`, sound + backward-compatible, *layered on*
> `scheduleEffectiveOnCore` so the SM5.D / `timerTickOnCore` proof base is
> untouched).  Headline `scheduleOrIdleOnCore_runs_idle` + the soundness surface
> (objects-`invExt` / `currentThreadValid` / `queueCurrentConsistent` /
> `runQueueWellFormed`) in staged `Scheduler/Operations/PerCoreDispatch.lean`; a
> `MainTraceHarness` `[IDLE-…]` demo shows idle dispatched live (+6 additive trace
> lines).  Plus the `enqueueIdleThreadOnCore` invariant-preservation surface (incl.
> the soundness-critical conditional `queueCurrentConsistent` under the documented
> `current ≠ idle` precondition), the `enqueueIdleThreadOnCoreLockSet` footprint,
> `idleThread_no_starvation`, the decidable `idleAvailableOnCoreB`, and the
> `idleThread_core_locality_forall` `∀c` aggregate; `idleThreadId` moved to
> `Scheduler/IdleThread.lean`; inventory 26 → 58 entries; partition gate 51
> staged-only modules; axiom-clean; trace additive-only.  **Tracked debt (SM5.I /
> SM5.H / post-1.0)**: folding the idle dispatch *into* `scheduleEffectiveOnCore` in
> place; the unconditional invariant-backed `chooseThreadOnCore_always_succeeds`
> (needs idle-always-enqueued maintained across every transition); per-(core,domain)
> idle for multi-domain configs; wiring `scheduleOrIdleOnCore` into the legacy
> single-core `schedule`.  Items deferred past v1.0.0 with correctness impact: NONE.

### SM5.F — Per-core PIP (5 PRs, 10 sub-tasks)

| Sub | Description | Est |
|-----|-------------|-----|
| SM5.F.1 | `computeMaxWaiterPriorityOnCore` | M |
| SM5.F.2 | Cross-core PIP wake | L |
| SM5.F.3 | `pipBoost_perCore_consistent` | M |
| SM5.F.4 | Donation chain across cores | L |
| SM5.F.5 | `restoreToReady` per-core variant | M |
| SM5.F.6 | `resumeThread` per-core PIP recomp | L |
| SM5.F.7 | `blockingGraphOnCore_consistent` | M |
| SM5.F.8 | `blockingAcyclic_perCore` | M |
| SM5.F.9 | `priorityInheritance_perCore_witness` | M |
| SM5.F.10 | Cross-core PIP scenarios (tests) | L |

### SM5.G — Per-core domain scheduling (3 PRs, 6 sub-tasks)

| Sub | Description | Est |
|-----|-------------|-----|
| SM5.G.1 | `activeDomainOnCore` | T |
| SM5.G.2 | `advanceDomainOnCore` + cyclic theorem | M |
| SM5.G.3 | `activeDomainOnCore_isInDomainSchedule` | M |
| SM5.G.4 | `chooseThreadOnCore_respects_activeDomain` | M |
| SM5.G.5 | Cross-core domain independence | S |
| SM5.G.6 | 5 domain-rotation tests | M |

### SM5.H — Per-core CBS (4 PRs, 8 sub-tasks)

| Sub | Description | Est |
|-----|-------------|-----|
| SM5.H.1 | `replenishQueueOnCore` | S |
| SM5.H.2 | `replenishOnCore (s, c, sc)` | M |
| SM5.H.3 | `replenishQueueOnCore_wellFormed` | M |
| SM5.H.4 | SC migration on affinity change | L |
| SM5.H.5 | `schedContextRunQueueConsistent_perCore` | M |
| SM5.H.6 | `replenishmentPipelineOrder_perCore` | M |
| SM5.H.7 | CBS budget accounting per core | M |
| SM5.H.8 | 6 cross-core CBS tests | L |

### SM5.I — Per-core invariant suite (5 PRs, 10 sub-tasks)

| Sub | Description | Est |
|-----|-------------|-----|
| SM5.I.1 | `currentOnCore_validThreadIfSome` | S |
| SM5.I.2 | `runQueueOnCore_wellFormed` | S |
| SM5.I.3 | `schedContextRunQueueConsistent_perCore` | M |
| SM5.I.4 | `priorityInheritance_perCore` | M |
| SM5.I.5 | `schedulerInvariant_perCore` aggregate | M |
| SM5.I.6 | `schedulerInvariant_perCore_pairwise` | M |
| SM5.I.7 | `schedulerInvariant_smp` system-wide | M |
| SM5.I.8 | Preservation by every transition | L |
| SM5.I.9 | `crossSubsystemInvariant_smp` extension | M |
| SM5.I.10 | Tier-3 surface anchors | S |

### SM5.J — WCRT under fine locks (2 PRs, 5 sub-tasks)

| Sub | Description | Est |
|-----|-------------|-----|
| SM5.J.1 | `WCRT_lockSet` definition | M |
| SM5.J.2 | `wcrt_bound_rpi5_smp` extending R5 | L |
| SM5.J.3 | Per-operation WCRT bounds (5 theorems) | L |
| SM5.J.4 | Liveness: no thread starves under SMP | L |
| SM5.J.5 | WCRT scenarios (3 tests) | M |

### SM5.K — Tests + fixtures (3 PRs, 6 sub-tasks)

| Sub | Description | Est |
|-----|-------------|-----|
| SM5.K.1 | `tests/SmpSchedulerSuite.lean` (50+ scenarios) | XL |
| SM5.K.2 | `tests/SmpTimerSuite.lean` | M |
| SM5.K.3 | `tests/SmpPipSuite.lean` (cross-core PIP) | M |
| SM5.K.4 | `tests/fixtures/smp_4core_scheduler.expected` | M |
| SM5.K.5 | `scripts/test_qemu_smp_scheduler.sh` | M |
| SM5.K.6 | Surface anchors | S |

## 6. Verification strategy for SM5

### 6.1 What SM5 proves

~30 substantive theorems:
- Selection: `chooseThreadOnCore_selects_highest`,
  `chooseThreadOnCore_perCore_independence`,
  `chooseThreadOnCore_always_succeeds`,
  `chooseThreadOnCore_preserves_wellFormed`.
- Switch: `switchToThreadOnCore_sets_current`,
  `switchToThreadOnCore_preempts_previous`,
  `switchToThreadOnCore_rejects_remote`.
- Wake: `wakeThread_emits_sgi_if_remote`,
  `wakeThread_lossless`, `wakeThread_target_runQueue_contains`,
  `enqueueRunnableOnCore_wellFormed`.
- Timer: `timerTickOnCore_advances_per_core`,
  `cbsReplenish_can_wake_remote_core`,
  `timerTickOnCore_preempts_local`,
  `timerTickOnCore_rotates_domain`.
- Idle: `idleThread_core_locality`,
  `idleThread_priority_zero`, `chooseThreadOnCore_always_succeeds`.
- PIP: `pipBoost_perCore_consistent`,
  `donation_perCore_consistent`,
  `blockingAcyclic_perCore`,
  `priorityInheritance_perCore_witness`.
- Domain: `activeDomainOnCore_isInDomainSchedule`,
  `advanceDomainOnCore_cyclic`,
  `chooseThreadOnCore_inActiveDomain`.
- CBS: `replenishQueueOnCore_wellFormed`,
  `schedContextRunQueueConsistent_perCore`,
  `schedContextMigration_consistent`.
- Aggregate: `schedulerInvariant_perCore`,
  `schedulerInvariant_perCore_pairwise`,
  `schedulerInvariant_smp`.
- WCRT: `wcrt_bound_rpi5_smp`, `WCRT_lockSet`.

### 6.2 What SM5 assumes

- SM3's lock-set discipline and Cor 2.1.11.
- SM4's per-core SchedulerState fields.
- SM1.F's SGI primitive.

## 7. Risk inventory

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Cross-core wake SGI lost | LOW | HIGH | GIC SGI delivery hardware-guaranteed |
| `wakeThread_lossless` proof has subtle case | MED | HIGH | Eventually-runnable property is structural |
| Per-core PIP introduces cycles | LOW | CRIT | `blockingAcyclic_perCore` preserved |
| SchedContext migration races | LOW | HIGH | Migration happens under lock-set; serializable |
| Per-core timer skew | LOW | MED | Each core has its own CNTP; firmware sync |
| Idle thread starvation | LOW | LOW | Idle priority 0; never starves higher-pri |
| WCRT bound too tight in practice | MED | LOW | Empirical measurement on RPi5 |

## 8. Acceptance gate

- [ ] All 11 sub-task groups (A..K) complete.
- [ ] 30+ per-core scheduler theorems proven.
- [ ] 4-thread workload distributed across 4 cores.
- [ ] Cross-core preempt works via SGI.
- [ ] Per-core timer ticks advance per-core domain state.
- [ ] PIP cross-core works.
- [x] Idle threads per core (SM5.E, v0.31.45 → v0.31.46; the production idle-aware
  dispatcher `scheduleOrIdleOnCore` runs the idle thread live).
- [ ] WCRT bound proven for RPi5 canonical config.
- [ ] Tier 0..4 green.
- [ ] Aggregate SM5 closure CHANGELOG.

## 9. Cross-references

- **Previous**: [`SMP_PER_CORE_STATE_PLAN.md`](SMP_PER_CORE_STATE_PLAN.md), [`SMP_PER_OBJECT_LOCKS_PLAN.md`](SMP_PER_OBJECT_LOCKS_PLAN.md)
- **Next**: [`SMP_CROSS_CORE_IPC_PLAN.md`](SMP_CROSS_CORE_IPC_PLAN.md)

## 10. Theorem catalogue for SM5

~30 substantive theorems (full list §6.1).

## Appendix A — Verification commands

```bash
source ~/.elan/env
lake build SeLe4n.Kernel.Scheduler  # full subsystem
lake build SmpSchedulerSuite
./scripts/test_qemu_smp_scheduler.sh
```

---

*SM5 brings the kernel from "single-scheduler under lock" to
"per-core scheduler with cross-core wake". The work composes
cleanly atop SM3 (lock discipline) and SM4 (per-core state).*
