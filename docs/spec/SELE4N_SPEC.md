# seLe4n Project Specification

This document defines the normative scope, milestone structure, active workstream
portfolio, and acceptance criteria for **seLe4n** — a production-oriented microkernel
written in Lean 4 with machine-checked proofs, improving on seL4 architecture.

For the reference specification of the original seL4 microkernel that seLe4n builds on,
see [`docs/spec/SEL4_SPEC.md`](./SEL4_SPEC.md).

---

## Table of Contents

1. [Project Identity](#1-project-identity)
2. [Current State Snapshot](#2-current-state-snapshot)
3. [Milestone History](#3-milestone-history)
4. [Architectural Improvements over seL4](#4-architectural-improvements-over-sel4)
5. [Completed Workstream Portfolio (WS-G) and Next Steps](#5-completed-workstream-portfolio-ws-g-and-next-steps)
6. [Hardware Target: Raspberry Pi 5](#6-hardware-target-raspberry-pi-5)
7. [Acceptance Expectations](#7-acceptance-expectations)
8. [Model Fidelity & Type Safety (WS-S Phase S4)](#8-model-fidelity--type-safety-ws-s-phase-s4)
9. [Non-Negotiable Baseline Contracts](#9-non-negotiable-baseline-contracts)
10. [Audit Baselines](#10-audit-baselines)
11. [Security and Threat Model](#11-security-and-threat-model)

---

## 1. Project Identity

**seLe4n** is a novel microkernel built from the ground up in Lean 4. Every kernel
transition is an executable pure function. Every invariant is machine-checked — zero
`sorry`, zero `axiom` across the entire production proof surface.

The project keeps four concerns in one engineering loop:

1. deterministic transition semantics (executable pure functions),
2. machine-checked invariant preservation (3,045 theorem/lemma declarations),
3. architectural improvements over seL4 where the proof framework enables them,
4. milestone-oriented delivery toward production on **Raspberry Pi 5** (ARM64).

The project began as a formalization of seL4 semantics and is now a production-oriented
kernel that preserves seL4's capability-based security model while introducing novel
improvements in service orchestration, capability management, IPC queuing, information-flow
enforcement, and scheduling.

---

## 2. Current State Snapshot

| Attribute | Value |
|-----------|-------|
| **Package version** | `0.31.155` (`lakefile.toml`) |
| **Lean toolchain** | `v4.28.0` (`lean-toolchain`) |
| **Production LoC** | 186,302 across 251 Lean files |
| **Test LoC** | 39,822 across 61 Lean test suites |
| **Proved declarations** | 6,151 theorem/lemma declarations (zero sorry/axiom) |
| **Target hardware** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Latest audit** | [`AUDIT_v0.27.6_COMPREHENSIVE`](../dev_history/audits/AUDIT_v0.27.6_COMPREHENSIVE.md) — full-kernel Lean + Rust audit (5 HIGH, 27 MED, 28 LOW). All actionable findings remediated via WS-AI (7 phases, 37 sub-tasks). |
| **Active workstream** | **WS-SM (SMP multi-core completion) IN FLIGHT** — closes at v1.0.0 with a bootable verified SMP microkernel on Raspberry Pi 5. Current sub-phase: **SM6.B notification across cores LANDED (v0.31.68)** — the cross-core IPC phase (SM6) continues with the notification syscalls lifted to SMP: `notificationSignalOnCore` (`SeLe4n/Kernel/IPC/CrossCore/NotificationSignal.lean`) routes the head waiter's wake through the SM5.C cross-core `wakeThread` (a `.reschedule` SGI to a remote waiter's home core — `notificationSignalOnCore_remote_wake`) while the signaller does **not** block, and `notificationWaitOnCore` blocks the caller on its *own* core via the per-core `removeRunnableOnCore`; the SM6.B theorems land axiom-clean (multi-waiter discipline `notificationSignalOnCore_wakes_head` / `_remaining_waiters` — one wake per signal, the woken head removed from the duplicate-free remainder, read back through the object-invisible wake; 2PL atomicity `notificationWaitOnCore_atomic_under_lockSet`; per-core wake locality `notificationSignalOnCore_perCore_consistent`; the notification ↔ TCB binding lock-set membership `lockSet_notificationSignal_{notification,waiter_tcb}_write_mem` — both ends write-locked via the unconditional `self_write_mem_insertOrMerge`; and boot-core + per-core/∀-core (`lowEquivalent_smp`) non-interference `notificationSignalOnCore_signal_path_NI{,_smp}`); tests `tests/SmpCrossCoreNotificationSuite.lean` (24 runtime assertions + theorem witnesses); staged (partition 54 → 56), the live cross-core notification dispatch wiring is the SM5.I FFI-seam follow-on.  **Prior sub-phase: SM6.A endpoint call across cores LANDED (v0.31.65)** — the cross-core IPC phase (SM6) opens with the endpoint `Call` rendezvous lifted to SMP: `endpointCallOnCore` (`SeLe4n/Kernel/IPC/CrossCore/EndpointCall.lean`) routes the receiver wake through the SM5.C cross-core `wakeThread` (a `.reschedule` SGI to a remote receiver's `determineTargetCore` home core — plan **Theorem 3.2.1** `endpointCallOnCore_emits_sgi_if_remote_receiver`) and blocks the caller on its *own* core via the new per-core `removeRunnableOnCore` (`… bootCoreId = removeRunnable …` by `rfl`); all ten SM6.A sub-tasks land axiom-clean (lock-set correctness `endpointCallOnCore_lockSet_correct`, donation-chain extension `lockSet_endpointCall_donation_extension`, 2PL atomicity `endpointCallOnCore_atomic_under_lockSet`, per-core blocking `endpointCallOnCore_perCore_blocking`, reply-state allocation `endpointCallOnCore_reply_linkage_under_lockSet` — this kernel has no separate Reply object — the WithCaps footprint `endpointCallWithCaps_lockSet_correct`, and cross-core non-interference `endpointCallOnCore_call_path_NI` from the new per-core scheduler-step projection lemmas); tests `tests/SmpCrossCoreCallSuite.lean` (20 runtime assertions + theorem witnesses). **v0.31.66**: the live `API.dispatchWithCap{,Checked}` `.call` arm now routes through `endpointCallCrossCoreDispatch{,Checked}` on the production checked chain (`syscall_dispatch_inner` → `syscallEntryChecked` → `dispatchWithCapChecked`), waking the receiver on its home core and descheduling the caller on its own core (`determineExecutingCore`); the 14 SMP dispatch modules are promoted to production (staged-only 71 → 57). **v0.31.67 — cross-core completion** (PR #820 review #1/#3/#5): the **SGI-firing** seam `SyscallDispatchEntry` (`@[export lean_syscall_dispatch_cross_core]`) + its closure (`PriorityInheritance.PerCore`, `Concurrency.Runtime`) are promoted to production (staged-only 57 → **54**) and the Rust `svc_dispatch` extern is flipped to it (fires the diff-recovered cross-core `.reschedule` SGIs, single-core-inert); `syscallDispatchFromAbi` / `syscallEntryChecked` take an explicit `executingCore` and read `currentOnCore executingCore` (per-core caller identification — `syscallDispatchCrossCoreEntry` threads `currentCoreId`, `syscallDispatchInner` stays boot-pinned; the five `syscallDispatchFromAbi_*` bridges generalise to an arbitrary core); and the `.call` arm's donation propagation switches to the cross-core chain walk `propagatePipChainCrossCore` (migrates each boosted server's bucket on its home core).  Prior sub-phase: **SM5.J WCRT under fine locks + SM5.K acceptance tests COMPLETE (v0.31.63; completion audit-pass v0.31.64)** — the **v0.31.64 completion** makes "no thread starves under SMP" a *genuine* eventually-scheduled liveness theorem by generalising the bootCoreId-pinned R5 trace model to an arbitrary `(c : CoreId)` **in production** (`selectedAtOnCore` / `WCRTHypothesesOnCore` / `bounded_scheduling_latency_exists_onCore` + the RPi5 closure, each the single-core form's `rfl`-bridged `c := bootCoreId` instance), so `thread_eventually_scheduled_onCore` and the strengthened 3-way `no_starvation_under_smp` prove a *specific runnable thread is selected on an arbitrary core within `wcrtBound`*; it also adds the decidable no-stall discharge, the execution-sensitive bridge to `Concurrency.WCRT`, cycle-commensurate units (`WCRT_smp_cycles`), access-mode soundness, the SGI-handler / complete-timer per-op bounds, and a multi-step dynamic 4-core simulation + cross-core round-trip in `SmpSchedulerSuite` (inventory 32 → 44; AK7 floor re-anchored for the structural-minimum raw increase).  SM5.J bounds the per-core scheduler operations' worst-case response time under per-object RW **fine locks** (plan §3.9), *extending* the R5 domain-rotation / band-exhaustion scheduling-latency bound (`wcrtBound`) with the SMP lock-contention dimension: `WCRT_lockSet (lockSet) (tCs) := |lockSet| · perLockWaitCost tCs` (reusing the SM3.D `perLockWaitCost = (numCores − 1) · tCs` verbatim — the §3.9 `max-lock-set-size · (coreCount − 1) · WCRT_per_lock` formula), the plan §3.9 **Theorem 3.9.1** `wcrt_bound_rpi5_smp` (`config = rpi5CanonicalConfig ⟹ config.wellFormed ∧ WCRT_lockSet ≤ maxLockSetSize · 3 · tCs`, the RPi5 `coreCount − 1 = 3` pinned by `numCores_eq_rpi5_coreCount`), the combined `WCRT_smp` (R5 latency + lock contention), the five per-operation bounds (chooseThread / switch / wake / timerTick / replenish), and **no thread starves under SMP** (`schedulerNoStall_smp` per-core non-stall via the SM5.E idle fallback + `boundedKernelWait_smp` no-unbounded-inversion via the SM3.D `boundedWait_under_2pl` + the `no_starvation_under_smp` capstone + the `r5_latency_within_smp_bound` R5 bridge); `wcrt_bound_rpi5_smp` is axiom-free.  SM5.K lands the acceptance-gate test surface: `tests/SmpSchedulerSuite.lean` (the **4-thread workload distributed across 4 cores** — 51 runtime scenarios on a deterministic per-core-bound fixture covering selection / independence / affinity / cross-core wake SGI / switch / WCRT / idle no-stall), the golden `tests/fixtures/smp_4core_scheduler.expected` trace (each line computed from the live `chooseThreadOnCore` / `determineTargetCore` / `wakeThread` / `switchToThreadOnCore` decisions, verified byte-for-byte), `tests/SmpWcrtSuite.lean`, and the `scripts/test_qemu_smp_scheduler.sh` Tier-4 stub.  Staged `Scheduler/Operations/PerCoreWcrt.lean` + `PerCoreWcrtInventory.lean` (32-entry `pcwt!` inventory); partition gate **64 staged-only modules**; both new suites wired into Tier 2; axiom-clean; default build green; trace byte-identical.  Prior sub-phase: **SM5.I per-core invariant suite + SM4.B register-bank payoff COMPLETE (v0.31.61)** — the SM4.B per-core register banks (`MachineState.coreRegs : Vector RegisterFile numCores`, accessor `regsOnCore c` / `setRegsOnCore c`, with `MachineState.regs = regsOnCore bootCoreId` as a back-compat def-accessor) make `contextMatchesCurrentOnCore` (which now reads core `c`'s *own* bank) a genuine ∀-core invariant: the register-bank-extended `schedulerInvariantStructuralReg_smp` (the structural safety core + `contextMatchesCurrentOnCore`) and the Nodup-extended `schedulerInvariantStructuralRegNodup_smp` (+ `runQueueUniqueOnCore`, via the new public `RunQueue.{insert,remove}_preserves_toList_nodup`) are proved preserved system-wide by every one of the ten SM5 per-core transitions (the two dispatch transitions *establish* `contextMatchesCurrentOnCore` on the operated core; the sibling frame is discharged by the `RegisterFile` partial-equivalence `beq_symm` / `beq_trans` idempotent-save argument — no cross-core current-disjointness invariant needed).  79-entry inventory (new `.registerBank` category, 39 entries); `tests/SmpInvariantSuite.lean` adds a genuinely multi-core fixture witnessing `contextMatchesCurrentOnCore` on two cores simultaneously + cross-core register-bank isolation; axiom-clean (`propext` / `Quot.sound` / `Classical.choice`); default build green (324 jobs); partition gate 62 staged-only modules; trace byte-identical; AK7 floor re-anchored by the structural minimum (the new `restoreIncomingContextOnCore` mirrors the single-core `restoreIncomingContext`'s raw match for the `rfl` bridge).  Prior sub-phase: **SM5.H per-core CBS (Constant Bandwidth Server) COMPLETE (v0.31.54)** — each core owns its **own** CBS replenishment queue (`replenishQueueOnCore c`, the SM4.B per-core field), holding the budget-refill schedule for the SchedContexts whose bound thread is homed on that core; when a thread's `cpuAffinity` changes, its bound SchedContext's pending replenishments **migrate** to the new core's queue (plan §3.8).  Staged `Scheduler/Operations/PerCoreCbs.lean` adds `replenishOnCore` (the per-core CBS replenishment-scheduling primitive — insert into `replenishQueueOnCore c`) + the full frame surface and its `replenishQueueValidOnCore` (sorted + size-consistent) / `replenishmentPipelineOrderOnCore` (future-eligible) / affinity-consistency preservation; `migrateSchedContextReplenishment` (move a SchedContext's pending replenishments between cores — `remove` from source, fold-of-`insert`s into destination) + the structural moves-the-entries facts + validity / pipeline SMP-preservation; the composite `setThreadCpuAffinityWithMigration` (the SM5.C.8 affinity write + the migration) and the headline restoration `schedContextMigration_consistent` (binding a thread to a new core **and** migrating its SchedContext's replenishments *restores* `replenishQueueAffinityConsistent_smp` on every core, under the 1:1 binding + pre-state consistency); the plan §3.8 Theorem 3.8.1 invariant `replenishQueueAffinityConsistentOnCore` (every queued SchedContext is homed on its core — named to avoid the §3.8 caption's collision with the unrelated SM4.C `schedContextRunQueueConsistent_perCore`; the literal `cpuAffinity = some c` realised as `determineTargetCore = c` so SchedContext-bound-but-affinity-unbound threads are correctly admitted); and the aggregate `perCoreCbsInvariant` + CBS budget-bound accounting (`consumeBudget` / `applyRefill` keep `budgetRemaining ≤ budget`).  54-entry `pccbst!` inventory (`PerCoreCbsInventory.lean`, 7 categories); tests `tests/SmpCbsSuite.lean` (`smp_cbs_suite`, 60 anchors / 8 examples / 36 runtime assertions — the cross-core migration genuinely moves entries between cores); partition gate 57 staged-only modules; axiom-clean; default build green (324 jobs); trace byte-identical.  Built on **SM5.G per-core domain scheduling COMPLETE (v0.31.51; audit-pass completion v0.31.52; deep-audit pass v0.31.53)** — each core independently rotates its **own** domain schedule (plan §3.7), so different cores can be in different scheduling domains simultaneously (plan §4.2).  The staged `Scheduler/Operations/PerCoreDomain.lean` adds `advanceDomainOnCore` (the *pure* per-core domain rotation — advancing **only** core `c`'s domain triple; an empty schedule no-ops via the out-of-bounds `Option` lookup) + the full frame surface + the `advanceDomainOnCoreN` iteration and the **cyclic theorem** `advanceDomainOnCore_cyclic` (iterating `domainSchedule.length` times returns the schedule index to its start); the bridge `switchDomainOnCore_activeDomain_eq_advanceDomainOnCore` (the operational SM5.D.6 switch's *domain effect* IS this rotation); `advanceDomainOnCore_establishes_activeDomainOnCore_isInDomainSchedule` + the plan §3.7 **Theorem 3.7.1** membership form `activeDomainOnCore_isInDomainSchedule_mem`; `chooseThreadOnCore_respects_activeDomain` (a selected thread is in core `c`'s active domain — the domain barrier / temporal isolation, via the new `chooseBestRunnableBy_result_eligible` fold lemma); and cross-core domain independence (`advanceDomainOnCore_independent_of_other_core` + the `advanceDomainOnCoreLockSet` core-local footprint).  39-entry `pcdt!` inventory (`PerCoreDomainInventory.lean`); tests `tests/SmpDomainSuite.lean` (`smp_domain_suite`, 43 anchors / 7 examples / 27 runtime assertions); partition gate 55 staged-only modules; axiom-clean; default build green (324 jobs); trace byte-identical.  **Audit-pass completion (v0.31.52)** closes every optimality gap from the SM5.G self-audit (inventory **39 → 67** entries, 9 categories): the bridge to `switchDomainOnCore` is upgraded to the **full domain triple** (`switchDomainOnCore_domainTriple_eq_advanceDomainOnCore`; a code-merge of the two rotation paths is deliberately not done — it would regress the fail-closed `.error` on an out-of-bounds lookup); the cyclic theorem's `idx < length` precondition is discharged from a maintained invariant (`domainScheduleIndexInBoundsOnCore` + `advanceDomainOnCore_cyclic_of_inBounds`); the cyclic property is extended from the index to the **active domain** (`domainConsistentOnCore` + `advanceDomainOnCore_cyclic_activeDomain`); invariant preservation is lifted to the **live** transitions (`switchDomainOnCore` / `scheduleDomainOnCore_preserves_activeDomainOnCore_isInDomainSchedule`, via the new `scheduleEffectiveOnCore` domain frames); the literal §3.7 `SystemState.activeDomainOnCore` accessor is built + made load-bearing (`activeDomainOnCore_systemState_mem`); the lock-set gains an acquisition-order + write-containment witness; the tier-4 stub `scripts/test_qemu_smp_domain.sh` reserves the nightly slot; and the budget-aware respects-domain theorem drops its asymmetric `wellFormed` hypothesis.  Tests grow to 43 runtime assertions (+16 completion scenarios).  **Deep-audit pass (v0.31.53)** — a code-first audit (reading the implementation, not docstrings) confirmed the v0.31.52 cut sound, secure, and dependent only on the foundational `propext` / `Quot.sound` / `Classical.choice`, with no shortcut that made the codebase less secure; it closed **one substantive completeness asymmetry**: v0.31.52 introduced the two per-core domain invariants `domainScheduleIndexInBoundsOnCore` (index `< domainSchedule.length`) and `domainConsistentOnCore` (active domain = the schedule entry at the index) and proved only the *abstract* rotation establishes them and that `scheduleDomainOnCore` preserves the SM4.C *membership* predicate — it did **not** prove the **live** `scheduleDomainOnCore` / `switchDomainOnCore` transitions maintain these two new invariants (so SM5.I could not assume them across a domain tick), now closed by §11's 8 live-transition preservation theorems (`domainScheduleIndexInBoundsOnCore_frame` / `domainConsistentOnCore_frame` per-other-core frames; the three schedule-index re-dispatch frames `idleFallbackOnCore` / `scheduleEffectiveOnCore` / `decrementDomainTimeOnCore` `_domainScheduleIndexOnCore`; `scheduleDomainOnCore_preserves_domainScheduleIndexInBoundsOnCore`, `switchDomainOnCore_preserves_domainConsistentOnCore`, `scheduleDomainOnCore_preserves_domainConsistentOnCore`) + a stale def-docstring fix (`advanceDomainOnCore` now cites the full-triple bridge `switchDomainOnCore_domainTriple_eq_advanceDomainOnCore`, not the superseded active-domain-only one).  Inventory **67 → 75** (`livePreservation` 7 → 15); tests grow to **45** runtime assertions; AK7 floor unchanged.  Built on **SM5.F per-core priority inheritance protocol COMPLETE (v0.31.50)** — under SMP a thread on core `c` blocked on a resource held by a thread on core `c'` boosts that holder to its priority; if `c' ≠ c` the boost emits a `.reschedule` SGI to `c'`.  Correctness keystone: the boost VALUE is the GLOBAL `computeMaxWaiterPriority` (the max over *every* waiter, cross-core — taking only a per-core slice would under-boost and re-introduce priority inversion); the per-core aspect is purely (1) which core's run queue the boosted holder's bucket migrates on and (2) whether a remote core must be poked.  Production transitions (additive; the raw single-core PIP is preserved verbatim via the `rfl` bridge `updatePipBoost = updatePipBoostOnCore bootCoreId`): SM5.F.1 `computeMaxWaiterPriorityOnCore` (per-core slice) + `computeMaxWaiterPriorityOnCore_le_global` (the per-core ≤ global decomposition) (`Compute.lean`); SM5.F.2 `updatePipBoostOnCore` (per-core bucket migration) + `pipBoostWithWake` (cross-core PIP wake — emits `.reschedule` iff remote + material) + SM5.F.4 `propagatePipChainCrossCore` (donation chain across cores) (`Propagate.lean`); SM5.F.5/.6 `restoreToReadyOnCore` / `restoreToReadyWithWake` (per-core resume PIP recompute from the GLOBAL graph + cross-core resume wake) (`Lifecycle/Suspend.lean`).  Staged theorem surface (`Scheduler/PriorityInheritance/PerCore.lean`): SM5.F.3 `pipBoost_perCore_consistent` (Thm 3.6.1 — a PIP-consistent holder's per-core slice ≤ its effective priority), SM5.F.7 `blockingServerOnCore` + `blockingGraphOnCore_consistent` (the global blocking graph is the union of the per-core slices), SM5.F.8 `blockingAcyclic_perCore` (the per-core slice is a sub-walk of the acyclic global chain — no new PIP cycle), SM5.F.9 `priorityInheritance_perCore_witness` (aggregate soundness).  **Completion pass (same v0.31.50 cut)** brings SM5.F to complete + optimal: the exact per-core decomposition `computeMaxWaiterPriority_eq_sup_perCore` (global boost = sup over per-core slices — completeness), post-boost dominance, chain-SGI completeness + the single-core behaviour-identical bridge to `propagatePriorityInheritance`, the C9 runnability gate on `pipBoostWithWake` (a blocked holder's boost fires no spurious cross-core IPI), the memory-model `pipBoostOrdering_happensBefore`, the complete per-core resume `resumeThreadOnCore` (Inactive→Ready), and the **cross-core wake dispatch** `computeCrossCoreSgis` + `Concurrency.fireCrossCoreSgis` (proven inert on single-core, demonstrated to fire `[(core1,.reschedule)]` for a cross-core boost diff).  **PR #811 review closure (same v0.31.50 cut)**: P2-2 gates the cross-core `.reschedule` SGI on the *effective* run-queue-bucket priority changing (`resolveEffectivePrioDeadline`), not the raw `pipBoost` — exactly `updatePipBoostOnCore`'s bucket-migration condition, so a boost that does not raise the effective priority (the holder's base already dominates) fires no spurious cross-core IPI (in both `pipBoostWithWake` and the diff-based `crossCoreSgiBody`); P2-5 makes a LOCAL `resumeThreadOnCore` (home = executing core) process the reschedule **inline** via `handleRescheduleSgiOnCore` — the exact handler the remote core runs on the SGI, so the local and remote paths mirror each other (preemption-gated, switch-based re-enqueue: the faithful + improved analogue of single-core `resumeThread`'s H5).  A post-review deep audit of that single-core analogue then surfaced and fixed a *pre-existing* liveness defect in the production single-core `resumeThread` (`seL4_TCB_Resume`): its H5 reschedule called `schedule` **without re-enqueuing the current (calling) thread** (the only `schedule` caller that skipped this; `handleYield` / `timerTick` / `switchDomain` all re-enqueue), so a *lower*-priority thread that resumed a *higher*-priority thread silently **orphaned itself** — lost from scheduling; the defect was invisible to the proof surface because the violated invariant (`threadStateConsistent`) is a testing-only check, not part of `crossSubsystemInvariant`.  Fixed by re-enqueuing the current thread (via the proven `ensureRunnable`) before `schedule`, with the `tests/SuspendResumeSuite.lean` SR-030 regression guard (verified to fail without the fix); follow-on hardening (tracked): promote `threadStateConsistent` into the proven invariant bundle.  99-entry `ppit!` inventory (`PerCoreInventory.lean`, 10 categories; +4 P2-5 inline-reschedule frame lemmas — `preemptCurrentOnCore_getTcb?_ne_current` / `switchToThreadOnCore_getTcb?_ne_current` / `handleRescheduleSgiOnCore_getTcb?_ne_current` / `resumeReadyMidState_scheduler_eq`); tests `tests/SmpPipSuite.lean` (`smp_pip_suite`, 99 anchors / 16 examples / 64 runtime assertions incl. the P2-2 immaterial-boost non-vacuity §3.11, the P2-5 inline-local-reschedule §3.12, and the deep-audit §3.13 cross-core SGI coalescing coverage — `dedupCrossCoreSgis` + the new `dedupCrossCoreSgis_nodup_cores` completeness witness, deduped target cores pairwise distinct so a boost chain naming one home core twice fires one IPI; no dead-weight); partition gate 53 staged-only modules; axiom-clean (`propext` / `Quot.sound` / `Classical.choice`); trace byte-identical; AK7 baseline re-anchored (`raw_match_total` 122 → 125, `raw_lookup_tid` 810 → 814 — the per-core PIP transitions mirror the raw-based D4-era single-core PIP, plus `crossCoreSgiBody`'s single object-store iteration; the raw floor rises by the structural minimum; the P2-2/P2-5 proofs use the `.get?` method form so the floor is unchanged).  Tracked debt (SM5.I): the cross-core dispatch *mechanism* is built + verified; the production call-site substitution (routing the `@[export]` IPC donation / timeout / resume bodies through the per-core boost + `fireCrossCoreSgis`) is gated on the SM5.I per-core FFI seam, and also closes the SM5.D timeout-path latency gap.  Built on **SM5.E per-core idle threads COMPLETE (v0.31.45)** — each core has a dedicated idle TCB (the lowest-priority thread it runs when nothing else is runnable) pinned to its own core via `createIdleThread`'s `cpuAffinity := some c` (SM5.E.2, the field added at SM5.B.4) and never migrating.  SM5.E theorems (staged `Scheduler/Operations/PerCoreIdle.lean`, building on the SM4.G idle-thread bootstrap `idleThreadId` / `createIdleThread` / `bootFromPlatformWithIdleThreads` in `Platform/Boot.lean` + the SM5.A `chooseThreadOnCore` selection): SM5.E.5 `idleThread_priority_zero` (idle is priority `⟨0⟩`, so a runnable user thread always outranks it — idle never starves a higher-priority thread) + the companion field lemmas; the SM5.E.3 `enqueueIdleThreadOnCore` run-queue primitive (the boot installer makes idle *current*; `chooseThreadOnCore` reads the run queue, so idle must be a *member* to be a fallback — full frame / membership / resolution / `invExt` + run-queue-wellFormed + runnable-are-TCBs preservation surface, mirroring SM5.C's `enqueueRunnableOnCore`); the SM5.E.6 keystone `chooseThreadOnCore_always_succeeds` (selection returns `some` when the idle thread is enqueued + in its active domain — the `idleThreadEnqueuedOnCore` discharge predicate — discharging the conditional SM5.A `chooseThreadOnCore_some_of_eligible` with the always-present idle candidate; `enqueueIdleThreadOnCore_establishes_idleThreadEnqueuedOnCore` + `enqueueIdleThreadOnCore_chooseThreadOnCore_succeeds` are the constructive non-vacuity witnesses); and the SM5.E.4 `idleThread_core_locality` (core `c`'s idle thread never appears on another core `c' ≠ c`'s run queue — *substantive* via the affinity binding `affinityAdmitsCore (createIdleThread c) c' = (c == c')`, plus the operational `idleThread_core_locality_of_enqueue` frame companion).  The 26-entry `PerCoreIdleInventory.lean` (4 categories field/enqueue/alwaysSucceeds/locality, `pcit!` compile-time identifier-validation macro) pins the surface; tests `tests/SmpIdleSuite.lean` (`smp_idle_suite`, 27 anchors / 9 examples / 24 runtime assertions); both modules staged via `Platform/Staged.lean`; partition gate 50 staged-only modules; axiom-clean (only the foundational `propext` / `Quot.sound` / `Classical.choice`); trace byte-identical.  **Completion cut (v0.31.46)**: the SM5.I per-core *idle-aware dispatcher* is pulled forward — `scheduleOrIdleOnCore` (`Scheduler/Operations/Core.lean`, production) **runs core `c`'s idle thread** when the budget-aware `scheduleEffectiveOnCore` finds nothing runnable, instead of leaving the core at `current = none` (conditional-fallback idle-if-installed-else-`none`, sound + backward-compatible, *layered on* `scheduleEffectiveOnCore` so the SM5.D / `timerTickOnCore` proof base is untouched); the headline `scheduleOrIdleOnCore_runs_idle` + the soundness surface (`_preserves_objects_invExt` / `_establishes_currentThreadValidOnCore` / `_establishes_queueCurrentConsistentOnCore` / `_preserves_runQueueOnCoreWellFormed`) are in the staged `Scheduler/Operations/PerCoreDispatch.lean`; a `MainTraceHarness` `[IDLE-…]` demo shows idle dispatched live (legacy single-core `schedule` → `current = none` vs. idle-aware → `current = some 65536`; the trace fixture grows by 6 additive lines).  The completion also adds the per-core invariant-preservation surface for `enqueueIdleThreadOnCore` (incl. the soundness-critical conditional `queueCurrentConsistent` under the documented `current ≠ idle` precondition), the `enqueueIdleThreadOnCoreLockSet` cross-domain footprint (SM5.A–D parity), `idleThread_no_starvation`, the decidable `idleAvailableOnCoreB` companion, and the `idleThread_core_locality_forall` `∀c` aggregate; `idleThreadId` moved to `Scheduler/IdleThread.lean` so the dispatcher can reference it; inventory 26 → 62 entries; partition gate 51 staged-only modules.  **Audit-pass-1 (v0.31.47)** — a deep code-first audit (reading the implementation, not docstrings) confirmed no security shortcut and no reachable-state defect, and closed one completeness gap: `scheduleOrIdleOnCore` established a strictly *smaller* invariant surface than the `scheduleEffectiveOnCore` it layers on, so `_establishes_currentThreadInActiveDomainOnCore` + `_preserves_runnableThreadsAreTCBsOnCore` were added, bringing the wrapper to *exact parity* (6 properties) with the wrapped selector (the other 5 base conjuncts are uniformly SM5.I work, unestablished by `scheduleEffectiveOnCore` either; for the reachable `createIdleThread` — timeSlice 5, unbound, domain 0 — all 11 conjuncts genuinely hold).  **Audit-pass-2 (v0.31.48, PR #810 review closure)** — fixed the CI shellcheck SC2016 (backticks in a tier-3 heredoc comment) + three Codex P2 findings: review #3 added an `affinityAdmitsCore` conjunct to `idleDispatchableOnCore` (a reserved-slot TCB bound to another core is no longer dispatchable as core `c`'s idle — mirrors `switchToThreadOnCore`); review #1 made `enqueueIdleThreadOnCore` `remove`-then-`insert` so a re-enqueue refreshes idle's priority bucket (a bare `insert` is an identity for existing members, leaving a stale bucket); review #2 added the *strong* production-dispatcher no-starvation `scheduleOrIdleOnCore_idle_starves_no_eligible_thread` (idle is dispatched **only when no in-domain budget-eligible thread is runnable at all** — never preempting a runnable user thread of any priority incl. 0, stronger than `idleThread_no_starvation`'s higher-priority-only scope); review #4 (wire the dispatcher into the live tick path) is the **fold cut below**.  **Review #4 closure — fold into `scheduleEffectiveOnCore` (v0.31.49)**: per the maintainer's choice, idle dispatch is folded **into** `scheduleEffectiveOnCore`'s `none` branch (new `idleFallbackOnCore` helper: run idle if `idleDispatchableOnCore`, else legacy `current = none`), so the live per-core tick / domain paths (`timerTickOnCore` / `scheduleDomainOnCore`, which already call `scheduleEffectiveOnCore`) now reach the idle thread on the running kernel; `dispatchIdleOnCore` + frame lemmas move into `Core`; `scheduleOrIdleOnCore` is now *definitionally* `scheduleEffectiveOnCore`.  The idle/`none` case split is discharged once in four `idleFallbackOnCore_*` lemmas, so the six `scheduleEffectiveOnCore_*` establishment theorems (PerCoreTimerTick §7) cover the folded dispatch and every `timerTickOnCore` / `scheduleDomainOnCore` preservation proof consuming them is unchanged.  New `scheduleDomainOnCore_runs_idle` proves the live domain-tick path dispatches idle (single-domain boundary + nothing eligible + idle dispatchable ⇒ `current = some (idleThreadId c)`); headline / strong-no-starvation restated on the idle-dispatch precondition (`chooseThreadEffectiveOnCore = .ok none`); states without an installed idle thread are byte-identical to pre-fold (trace unchanged).  Inventory 62 → 64 (dispatch +`idleFallbackOnCore` +`scheduleDomainOnCore_runs_idle`); `smp_idle_suite` 40/40; partition gate 51 staged-only modules; axiom-clean.  Tracked debt (SM5.I / SM5.H / post-1.0): the unconditional invariant-backed `chooseThreadOnCore_always_succeeds`, per-(core,domain) idle for multi-domain configs, and wiring `scheduleOrIdleOnCore` into the legacy single-core `schedule`.  Built on **SM5.D per-core timer tick COMPLETE (v0.31.41; audit-pass-2 v0.31.43; audit-pass-3 v0.31.44, PR #809 review closure)** — `timerTickOnCore (st) (c : CoreId) : Except KernelError (SystemState × List (CoreId × SgiKind))` (`Scheduler/Operations/Core.lean`, production) advances core `c`'s domain accounting, processes its due CBS replenishments (cross-core-waking refilled threads onto their target core via SM5.C's `wakeThread`, emitting `.reschedule` SGIs for remote targets), and preempts the running thread on budget / time-slice exhaust — reading but **never advancing** the global `machine.timer` (each core's CNTP is local; the global monotonic count is primary-owned, mirroring the Rust HAL's `TICK_COUNT`).  SM5.D theorems (staged `Scheduler/Operations/PerCoreTimerTick.lean`): the SM5.D.3 cross-domain `timerTickOnCoreLockSet` (object-store + run-queue + replenish-queue WRITE locks over the `SchedLockId` extended with the new `ReplenishQueueLockId` domain, plan §4.4 object < runQueue < replenishQueue) + the SM5.D.7 WCRT size bound, SM5.D.6 domain rotation (the separate atomic `scheduleDomainOnCore` / `switchDomainOnCore_rotates` — audit-pass-2: the budget-only tick itself does NOT rotate, preserving `currentThreadInActiveDomain`), the SM5.D.4 cross-core wake `cbsReplenish_can_wake_remote_core` + the replenishment preservation lemmas, the SM5.D.5 budget tick (`timerTickBudgetOnCore` preemption witnesses) + the reusable, previously-missing IPC-timeout objects-`invExt` preservation chain (`revertPriorityInheritance` / `timeoutThread` / `timeoutBlockedThreads_preserves_objects_invExt`), and the SM5.D.2 headlines `timerTickOnCore_advances_per_core` / `_preempts_local` / `_clears_lastTimeoutErrors` / `_preserves_currentThreadInActiveDomainOnCore` + `_preserves_objects_invExt` (SM5.B/C object-store-invariant parity) + SM5.D.8 decidability.  SM5.D.1: the Rust `timer::per_core_timer_tick_isr` + `handle_irq_per_core` wiring (build.rs Check 5) + the `lean_per_core_timer_tick` export seam (`Kernel.perCoreTimerTickEntry`, `PerCoreTimerEntry.lean`); +4 Rust HAL tests (722 total, zero clippy warnings).  Tests `tests/SmpTimerSuite.lean` (`smp_timer_suite`); partition gate 48 staged-only modules; axiom-clean (`propext` / `Quot.sound` / `Classical.choice`); trace byte-identical.  **Audit-pass-3 (PR #809 review closure)** fixed a P2 cross-core double-placement in the CBS-replenishment wake — `processOneReplenishmentOnCore`'s "already placed" guard now checks the new `runningOnSomeCore` predicate (current across all cores; a running thread is dequeued from every run queue, so the prior `runnableOnSomeCore` guard missed it and could wake it onto a second core); renamed the five phase-coded theorem-inventory modules to semantic names (`PerCoreTimerInventory` / `CrossCoreWakeInventory` / `WithLockSetInventory` / `DeadlockInventory` / `SerializabilityInventory`, `perCoreTimerTheorems` now 101 entries); and documented the timeout-path missing-cross-core-SGI latency gap as tracked debt deferred to SM5.F (per-core PIP).  Built on **SM5.C cross-core wake via SGI COMPLETE (v0.31.40)** — `wakeThread (st) (tid) (executingCore) : SystemState × Option (CoreId × SgiKind)` (`Scheduler/Operations/Selection.lean`, production) enqueues a newly-runnable thread on its affinity-determined target core (`enqueueRunnableOnCore`, which sets `ipcState := .ready` + inserts at effective priority) and emits a `.reschedule` SGI iff the target is remote from the executing core; `handleRescheduleSgiOnCore` is the target core's re-choose-and-switch handler; `setThreadCpuAffinity` is the affinity-control op; `determineTargetCore` routes an unbound thread to `bootCoreId` (SM5.C.9).  SM5.C theorems (staged `Scheduler/Operations/PerCoreWake.lean`): the cross-domain `wakeThreadLockSet` / `handleRescheduleSgiOnCoreLockSet` (object-store + run-queue WRITE locks, plan §4.4 order; SM5.C.3), `wakeThread_emits_sgi_if_remote` (Thm 3.3.1; SM5.C.4), `wakeThread_target_runQueue_contains` (SM5.C.10), `wakeThread_lossless` (Thm 3.3.2 via the `SchedStep`/`SchedReachable` RT-closure; SM5.C.6), the `enqueueRunnableOnCore` / `handleRescheduleSgiOnCore` / `setThreadCpuAffinity` preservation + frame lemmas, and the SGI delivery latency bound (`wakeThread_emits_at_most_one_sgi` + `rescheduleSgi_lowest_intid` + `sgiDeliveryLatencyBound = 0`; SM5.C.11).  Typed FFI SGI-emission wrappers (`coreIdTargetMask` / `sendRescheduleSgi` / `emitWakeSgi`) in `Concurrency/Runtime.lean`; `Concurrency.Sgi` promoted production-reached (production `Selection` imports it for `SgiKind`).  **Audit-pass-1** closed seven optimality gaps: §10 invariant preservation (`wakeThread_preserves_ipcSchedulerContract` — the full SM4.D IPC↔scheduler-coherence bundle preserved *because* the wake sets `ipcState := .ready`, so a wake can never produce a runnable-but-blocked thread; plus `currentThreadValidOnCore` / `queueCurrentConsistentOnCore` under the don't-wake-current precondition — the SM5.B-parity coverage); the ghost-wake SGI guard (`wakeThread_no_sgi_if_no_tcb`); §6b multi-step liveness (`wakeThread_roundtrip_reachable_current` — wake→handler dispatches to current via the `SchedReachable` `.tail`/`.switch` closure); §11 memory-model happens-before (`wakeOrdering_happensBefore` — the BKL release→acquire ordering as a theorem in SM2.A's model); honest latency-bound scoping; the (now 83-entry, audit-pass-3 Codex PR #806 closure) `CrossCoreWakeInventory.lean`; and the `test_qemu_smp_wake.sh` tier-4 SKIP-stub.  **Audit-pass-2** (independent code-not-docstring re-audit) found+fixed a duplicate-identifier bug `native_decide` had masked (Nodup proofs switched to kernel-sound `decide` under an elevated `maxRecDepth`, now axiom-clean), and added the no-liveness-stranding security theorems `determineTargetCore_admits_thread` / `wakeThread_target_admits_thread` + the field-frame `enqueueRunnableOnCore_preserves_woken_thread_fields`; `smp_wake_suite` 59/59 PASS.  **Audit-pass-3 Codex PR #806 closure** then fixed three real cross-core scheduling-correctness gaps the prior self-audits missed: a budget-aware + preempt-gated `handleRescheduleSgiOnCore` (`chooseThreadEffectiveOnCore` + the `candidateOutranksCurrentOnCore` gate — a lower-priority cross-core wake no longer preempts a higher-priority running thread, and a reschedule no longer dispatches a budget-exhausted thread) and the global single-placement reject `runnableOnSomeCore` in `enqueueRunnableOnCore` (the same thread can no longer be runnable on two cores); inventory 83 entries, `smp_wake_suite` 64/64 PASS, all axiom-clean.  **Audit-pass-3** (deepest code-first re-audit against the plan §3.3/§4.4 spec, not docstrings) found **no bugs / no security shortcuts** across all 12 sub-tasks: `enqueueRunnableOnCore` faithfully mirrors the trusted `IPC.ensureRunnable` (both gate on `ipcState` not `threadState`, so no suspended-thread-wake shortcut), is idempotent (a double-wake cannot duplicate a run-queue entry — now pinned by two runtime assertions, suite 59 → 61), and honors PIP boost (`effectiveRunQueuePriority` ≡ `ipcEffectiveRunQueuePriority`); the two plan-deviations (object-store table lock, explicit `executingCore`) are both safer; and `setThreadCpuAffinity`'s docstring now records that the scheduler-control capability gate belongs at the syscall-dispatch layer (the op is unwired → no live gap).  `smp_wake_suite` 61/61 PASS.  Axiom-clean; default build green (322 jobs); trace fixture byte-identical; partition gate 45 staged-only modules (audit-pass-1 +`CrossCoreWakeInventory`).  Built on **SM5.B per-core `switchToThread` COMPLETE (v0.31.39)** — `switchToThreadOnCore (st) (c : CoreId) (tid : ThreadId) : Except KernelError SystemState` per-core context switch (`Scheduler/Operations/Selection.lean`, production): preempt core `c`'s current thread (`preemptCurrentOnCore`: save register context + re-enqueue at effective priority), dequeue `tid` (dequeue-on-dispatch), restore `tid`'s context, set current = `tid`; fail-closed reject-remote (`.threadOnDifferentCore`) when `tid`'s new `TCB.cpuAffinity` (`Option CoreId`, pulled forward from the plan's SM5.C.7 slot since reject-remote needs a per-thread core binding) binds it to another core.  SM5.B theorems (staged `Scheduler/Operations/PerCoreSwitchToThread.lean`): the cross-domain `switchToThreadOnCoreLockSet` (object-store + run-queue WRITE locks, plan §4.4 object-before-run-queue order; SM5.B.2), `switchToThreadOnCore_sets_current` (Thm 3.2.1), `_preempts_previous` (Thm 3.2.2), `_rejects_remote` / `_ok_of_admits` (Thm 3.2.3), `_runQueueOnCore_excludes_current` (SM5.B.5), `_independent_of_other_core` (SM5.B.6), totality + decidable `switchToThreadOnCoreSucceeds` / `_RejectsRemote` (SM5.B.8); the SM5.B.7 FFI seam (Rust `ffi_switch_to_thread` / `ffi_per_core_current_thread` + Lean `@[extern]` + `Concurrency.switchToThreadHw` / `perCoreCurrentThreadHw` typed wrappers).  `KernelError.threadOnDifferentCore` (discriminant 53) added across the Lean enum + Rust `sele4n-types`/`sele4n-abi` (54 variants).  Axiom-clean; partition gate 44 staged-only modules; trace fixture byte-identical; full Rust HAL suite 718 tests green.  Built on **SM5.A per-core `chooseThread` COMPLETE (v0.31.38)** — `chooseThreadOnCore (st) (c : CoreId) : Except KernelError (Option ThreadId)` per-core thread selection (`Scheduler/Operations/Selection.lean`, production), reading only core `c`'s run-queue + active-domain slots; the legacy single-core `chooseThread` migrates to delegate to it (`chooseThread_eq_chooseThreadOnCore_bootCore`, `rfl`) with **zero behavioural change**.  The SM5.A theorems (staged `Scheduler/Operations/PerCoreChooseThread.lean`): SM5.A.2 `RunQueueLockId` (+ a `CoreId`-keyed total order and §4.4 `runQueueLockLevel`) + the cross-domain `SchedLockId` (object-lock ⊕ run-queue, plan §4.4 total order — object locks before run-queue locks) + the complete two-domain `chooseThreadOnCoreLockSet` (object-store read lock guarding the `st.objects` resolutions + the per-core run-queue read lock); SM5.A.3 per-core-independence frame + corollaries (Theorem 3.1.2) **and selection optimality `chooseThreadOnCore_selects_highest` (Theorem 3.1.1 — best in the maximum-priority bucket; the honest optimality, since `chooseBestInBucket` buckets by *effective* priority so a global base-priority-max claim would be false)**; SM5.A.4 idle-fallback completeness (`_ok_of_runnableTCBs` / `_none_no_eligible` / `_some_of_eligible`); SM5.A.6 selection soundness (`_some_mem_runQueueOnCore` + the literal `_preserves_wellFormed` anchor); SM5.A.7 decidable selection predicates; **§6 the CBS-budget-aware companion `chooseThreadEffectiveOnCore`** (production def + legacy `chooseThreadEffective` migration; mirrored independence / completeness / soundness + the `_selected_has_budget` guarantee — a dispatched thread genuinely has budget; it carries the same complete footprint via `chooseThreadEffectiveOnCoreLockSet` = `chooseThreadOnCoreLockSet`, since the object-store table read lock also guards its `hasSufficientBudget` SchedContext reads).  The cross-domain `SchedLockId` order unifies the object-lock and run-queue domains now (post-audit, closing the run-queue-only footprint's under-locking gap); the runtime `withLockSet` acquisition wiring over `SchedLockId` is SM5.B.  Axiom-clean (`propext` / `Quot.sound`); partition gate 43 staged-only modules; trace fixture byte-identical.  Built on **SM4.G per-core idle-thread bootstrap (v0.31.36→v0.31.37)**, **SM4.E single-core-witness retirement + `bootFromPlatform_smp_witness` (v0.31.35)**, and **SM4.D cross-subsystem per-core invariant migration (v0.31.30) + audit-passes 1–2 (lowEquivalentOnCore NI substrate, passiveServerIdle natural-SMP form, full per-operation SMP-preservation layer in CrossSubsystemPerCorePreservation.lean, typed-accessor migration, RetypeTargetSmp consumer)** — every cross-subsystem invariant reading scheduler state lifted to additive, soundness-preserving per-core `(c : CoreId)` forms + `∀ c` SMP aggregates across 5 new staged modules: IPC↔scheduler coherence (12 predicates, `IPC/Invariant/PerCore.lean`), capability no-stale-scheduler-ref retype precondition (`Capability/Invariant/PerCore.lean`), architecture register-decode consistency (`Architecture/InvariantPerCore.lean`), the 6 IF-M1 projections + `projectStateOnCore` (`InformationFlow/ProjectionPerCore.lean`), and the `crossSubsystemInvariant_perCore` / `crossSubsystemSchedulerContract_perCore` capstones (`CrossSubsystemPerCore.lean`); axiom-clean; partition gate 40 staged-only modules; trace fixture byte-identical (purely additive).  Built on **SM4.C per-core scheduler invariant migration (v0.31.13 → v0.31.29)** — the per-core scheduler invariant layer: 16 per-core predicate forms (all typed-accessor); 16 boot-core bridges; 3 aggregates (base `schedulerInvariant_perCore` mirroring `…BundleFull`'s per-core slice + extended mirroring `…BundleExtended` + cross-subsystem mirroring plan §5.6 with `schedContextRunQueueConsistent_perCore` / `priorityInheritance_perCore` / `activeDomainOnCore_isInDomainSchedule`) with SMP forms and bundle bridges; 20 per-conjunct frame lemmas; 7 setter independence corollaries + cross-core pairwise theorem (SM4.C.30); 6 per-op aggregate per-core preservation theorems (for `schedule` / `handleYield` / `timerTick` / `switchDomain` / `scheduleDomain` + `chooseThread` base bridge) + 25 named per-conjunct per-op SMP preservation theorems (plan §3.4 Pattern 1 lifts: 5 conjuncts × 5 ops); `_smp_of_bootCore_preservation` composition skeleton; `_holds_if_idle` sufficient theorem.  Across 2 modules (`SeLe4n/Kernel/Scheduler/Invariant/PerCore.lean` ~1660 LoC + `…/PerCorePreservation.lean` ~700 LoC); axiom-clean (only `propext` / `Quot.sound` / `Classical.choice`); AK7 baseline restored to the v0.31.2 floor (`RAW_MATCH_TOTAL` 122) with `GETTCB_ADOPTION` net +56 / `GETSCHEDCTX_ADOPTION` net +27; trace fixture byte-identical; partition gate green (35 staged-only modules). Landed earlier in WS-SM: SM0 (foundations, v0.31.3), SM1 (Rust HAL, v0.31.8), SM2 (verified lock primitives), SM3 (per-object locks → 2PL → deadlock-freedom → serializability), SM4.A (per-core `Vector` bootstrap, v0.31.11), SM4.B (`SchedulerState` path-a `Vector` replacement, v0.31.12), SM4.C (per-core scheduler invariant migration, v0.31.13 → v0.31.29), SM4.D (cross-subsystem per-core invariant migration, v0.31.30 → v0.31.34), SM4.E (single-core-witness retirement + `bootFromPlatform_smp_witness`, v0.31.35), SM4.G (per-core idle-thread bootstrap, v0.31.36 → v0.31.37), SM5.A (per-core `chooseThread` + selection optimality + budget-aware selector + cross-domain `SchedLockId` lock-order unification, v0.31.38), SM5.B (per-core `switchToThread` + `TCB.cpuAffinity` reject-remote + the cross-domain `switchToThreadOnCoreLockSet`, v0.31.39), SM5.C (cross-core wake via SGI: `wakeThread` + `enqueueRunnableOnCore` + `handleRescheduleSgiOnCore` + `setThreadCpuAffinity` + `wakeThread_lossless`, v0.31.40), SM5.D (per-core timer tick: `timerTickOnCore` + CBS replenishment cross-core wake + domain rotation + budget-tick preemption + the `ReplenishQueueLockId` lock domain, v0.31.41), SM5.E (per-core idle threads: `createIdleThread` `cpuAffinity := some c` + `enqueueIdleThreadOnCore` + `chooseThreadOnCore_always_succeeds` + `idleThread_core_locality` + the production idle-aware dispatcher `scheduleOrIdleOnCore` folded into `scheduleEffectiveOnCore` so the live tick path reaches idle, v0.31.45 → v0.31.49), SM5.F (per-core priority inheritance: `computeMaxWaiterPriorityOnCore` per-core slice + per-core ≤ global decomposition, `updatePipBoostOnCore` per-core bucket migration, `pipBoostWithWake` cross-core PIP wake, `propagatePipChainCrossCore` donation chain across cores, `restoreToReadyOnCore` / `restoreToReadyWithWake` per-core resume, `pipBoost_perCore_consistent` / `blockingAcyclic_perCore` / `priorityInheritance_perCore_witness`, v0.31.50), SM5.G (per-core domain scheduling: `advanceDomainOnCore` pure rotation + the cyclic theorem `advanceDomainOnCore_cyclic` + the full-triple bridge to the operational `switchDomainOnCore` + `activeDomainOnCore_isInDomainSchedule` / Thm 3.7.1 + `chooseThreadOnCore_respects_activeDomain` + cross-core domain independence + the `domainScheduleIndexInBoundsOnCore` / `domainConsistentOnCore` invariants maintained by the live transitions, v0.31.51 → v0.31.53), SM5.H (per-core CBS: `replenishOnCore` per-core replenishment-scheduling primitive + validity / pipeline-order / affinity preservation, `migrateSchedContextReplenishment` + the composite `setThreadCpuAffinityWithMigration` + the headline `schedContextMigration_consistent`, the §3.8 `replenishQueueAffinityConsistentOnCore` invariant, and the aggregate `perCoreCbsInvariant` + CBS budget bounds, v0.31.54), SM5.I (per-core invariant suite + the SM4.B per-core register-bank payoff — `schedulerInvariantStructuralReg_smp` / `…RegNodup_smp` preserved system-wide by every per-core transition, v0.31.60 → v0.31.61), SM5.J (WCRT under fine locks: `WCRT_lockSet` + the §3.9 `wcrt_bound_rpi5_smp` + the combined `WCRT_smp` extending the R5 `wcrtBound` + the five per-operation bounds + `no_starvation_under_smp`, v0.31.63), SM5.K (the 4-thread/4-core acceptance suite `SmpSchedulerSuite` + `SmpWcrtSuite` + the golden `smp_4core_scheduler.expected` trace fixture + the `test_qemu_smp_scheduler.sh` Tier-4 stub, v0.31.63). Follow-on: SM6.A (endpoint call across cores: `endpointCallOnCore` + the cross-core wake SGI / per-core blocking / reply-state / lock-set / cross-core-NI theorems, v0.31.65), SM6.B (notification across cores: `notificationSignalOnCore` / `notificationWaitOnCore` + the cross-core wake SGI / multi-waiter discipline / per-core wake locality / 2PL atomicity / notification-↔-TCB-binding lock-set / cross-core-NI theorems, v0.31.68), then SM6.C..SM9 (cross-core reply / cancellation, the per-core IPC invariant bundle, and — wiring the runtime `withLockSet` acquisition over `SchedLockId`, the per-core scheduler-tick driver, and the cross-core PIP / resume wake into the live IPC donation / timeout / resume paths — TLB shootdown, info-flow, release closure). Plans: master [`SMP_MULTICORE_COMPLETION_PLAN.md`](../planning/SMP_MULTICORE_COMPLETION_PLAN.md); per-core state [`SMP_PER_CORE_STATE_PLAN.md`](../planning/SMP_PER_CORE_STATE_PLAN.md) §5.3. Canonical per-phase record: [`docs/WORKSTREAM_HISTORY.md`](../WORKSTREAM_HISTORY.md). Prior closed portfolios: WS-RC pre-1.0 audit remediation (v0.30.11→v0.31.2), WS-AN (v0.30.11), WS-AK (v0.30.6), WS-AM–WS-B. |
| **Workstream history** | [`docs/WORKSTREAM_HISTORY.md`](../WORKSTREAM_HISTORY.md) |
| **Metrics source of truth** | [`docs/codebase_map.json`](../../docs/codebase_map.json) (`readme_sync` key) |
| **Codebase map** | `docs/codebase_map.json` (generated via `./scripts/generate_codebase_map.py --pretty`; validated with `--check`; auto-refreshed on `main` by `.github/workflows/codebase_map_sync.yml`) |

---

## 3. Milestone History

seLe4n has been developed through incremental milestone slices, each building on the
semantic and proof foundations of the previous one.

### 3.1 Completed Milestone Slices

| Milestone | Scope | Status |
|-----------|-------|--------|
| **Bootstrap** | Typed identifiers, monad foundations, machine state | Complete |
| **M1** | Scheduler semantics and preservation theorems | Complete |
| **M2** | Capability/CSpace operations + authority invariants | Complete |
| **M3** | IPC seed semantics | Complete |
| **M3.5** | Waiting handshake + scheduler coherence | Complete |
| **M4-A** | Lifecycle/retype foundations | Complete |
| **M4-B** | Lifecycle-capability composition hardening | Complete |
| **M5** | Service-graph and policy-surface completion | Complete |
| **M6** | Architecture-boundary assumptions/adapters/invariant hooks | Complete |
| **M7** | Audit remediation WS-A1..WS-A8 | Complete |

### 3.2 Completed Audit Portfolios

| Portfolio | Scope | Workstreams |
|-----------|-------|-------------|
| **WS-S** (v0.19.0–v0.19.6) | Pre-Benchmark Strengthening: 7 phases (S1–S7), 83 sub-tasks addressing 115+ findings from dual v0.18.7 audits. Security boundary hardening, Rust type safety, test hardening, proof surface closure (CDT maps consistency, RunQueue well-formedness, SecurityLabel lattice), model fidelity (capacity enforcement, typed IPC registers, alignment predicates), API cleanup (removed deprecated wrappers, SimRestrictive platform), hardware preparation (WithFlush VSpace, memory scrubbing, DeviceTree abstraction), documentation & polish. 5 High, 29 Medium, 19 Low findings resolved. Zero sorry/axiom | WS-S completed |
| **WS-R8** (v0.18.7) | Infrastructure & CI hardening: elan binary pinning with SHA-256, PR-based codebase map workflow, Rust test skip annotation, compiled test suite execution, Rust newtype encapsulation | WS-R8 completed |
| **WS-R7** (v0.18.6) | Architecture & hardware preparation: `TlbState` integrated into `SystemState`, `tlbConsistent` added to `proofLayerInvariantBundle` (M-17); TLB-flushing VSpace wrappers with preservation proofs; `RegName.isValid` ARM64 GPR bounds (L-02); `isWord64` predicate + `machineWordBounded` invariant for 64-bit value bounds (L-03); TCB `faultHandler`/`boundNotification` for seL4 fidelity (L-06); `KernelObjectType` enum replacing raw `Nat` in `LifecycleRetypeArgs` with typed decode boundary (L-10) | WS-R7 completed |
| **WS-R6** (v0.18.5) | Model & frozen state correctness: `apiInvariantBundle_frozenDirect` freeze-time equivalence, badge deprecation, `RegisterFile` BEq, scheduler bundle extension with `schedulerPriorityMatch`, all preservation proofs sorry-free | WS-R6 completed |
| **WS-R5** (v0.18.4) | Information flow completion: internalized IPC NI, service NI, content-aware memory projection | WS-R5 completed |
| **WS-R1–R4** (v0.18.0–v0.18.3) | Pre-release blockers, capability & CDT hardening, IPC invariant completion, lifecycle & service coherence | WS-R1–R4 completed |
| **WS-M2** (v0.16.15) | Capability subsystem performance optimization: fused revoke path eliminating redundant CDT traversal (M-P01), CDT `parentMap` reverse index for O(1) parent lookup (M-P02/M-P03), reply-capability lemma extraction into dedicated module (M-P05) | WS-M2 completed |
| **WS-M1** (v0.16.14) | Capability subsystem audit & remediation Phase 1: initial audit findings triage, critical invariant gap closure, baseline proof surface hardening | WS-M1 completed |
| **WS-F6** | Invariant quality: `capabilityInvariantBundle` reduced from 8-tuple to 6-tuple (tautological predicates removed); `blockedOnNotificationNotRunnable` added to `ipcSchedulerContractPredicates` (6-tuple); `runnableThreadsAreTCBs` in `schedulerInvariantBundleFull` (6-tuple) with sorry-free preservation for all scheduler ops; `vspaceCrossAsidIsolation` in `vspaceInvariantBundle` (6-tuple); `default_serviceCountBounded` and `default_serviceGraphInvariant` proved; zero sorry/axiom | WS-F6 completed |
| **WS-H13** (v0.14.4) | CSpace, lifecycle & service model enrichment: `cspaceDepthConsistent` invariant in `capabilityInvariantBundle` (8-tuple → 6-tuple after WS-F6), `resolveCapAddress` theorems (`_deterministic`, `_zero_bits`, `_result_valid_cnode`), `serviceGraphInvariant` preservation proofs (`serviceRegisterDependency`), `cspaceMove` error-path atomicity theorem (A-21); CNode field migration (`depth`/`guardWidth`/`guardValue`/`radixWidth`); addresses H-01, A-21, A-29, A-30, M-17/A-31. *(WS-Q1: `serviceStart`/`serviceStop` lifecycle ops and backing-object verification removed; registry-only model.)* | WS-H13 completed |
| **WS-H12f** (v0.14.3) | Test harness update & documentation sync: `runDequeueOnDispatchTrace`, `runInlineContextSwitchTrace`, `runBoundedMessageExtendedTrace` trace scenarios; legacy `endpointInvariant` comment cleanup; fixture updated (108 lines); 9 new Tier 3 anchors; documentation synchronized. Completes WS-H12 composite workstream | WS-H12f completed |
| **WS-H12b** (v0.13.9) | Dequeue-on-dispatch scheduler semantics: `queueCurrentConsistent` inverted to `current ∉ runnable` matching seL4's `switchToThread`/`tcbSchedDequeue`; `schedule`/`handleYield`/`timerTick`/`switchDomain` updated; `currentTimeSlicePositive` and `schedulerPriorityMatch` predicates; IPC predicates (`currentThreadIpcReady`, `currentNotEndpointQueueHead`, `currentNotOnNotificationWaitList`, `currentThreadDequeueCoherent`); ~1800 lines of proofs re-proved; closes H-04 (HIGH) | WS-H12b completed |
| **WS-H11** (v0.13.7) | VSpace & architecture enrichment: `PagePermissions` struct with `wxCompliant` and W^X enforcement at insertion, `vspaceMapPageChecked` with ARM64 52-bit physical address bounds, `vspaceInvariantBundle` 5-conjunct preservation proofs, TLB/cache maintenance model (`TlbState`, `adapterFlushTlb`, `adapterFlushTlbByAsid`, `tlbConsistent`), `VSpaceBackend` typeclass abstraction; 10 new theorems | WS-H11 completed |
| **WS-H8** (v0.13.2) | Enforcement-NI bridge & missing wrappers: enforcement soundness meta-theorems, 4 new enforcement wrappers (`notificationSignalChecked`, `cspaceCopyChecked`, `cspaceMoveChecked`, `endpointReceiveDualChecked`), NI bridge theorems, projection hardening (domain timing metadata), `enforcementBoundaryExtended` (8 policy-gated ops); 26 new theorems | WS-H8 completed |
| **WS-H6** (v0.13.1) | Scheduler proof-surface completion: RunQueue reverse bridge (`flat_wf_rev`, `membership_implies_flat`, `mem_toList_iff_mem`) and scheduler candidate-selection lemmas (`isBetterCandidate_transitive`, `bucketFirst_fullScan_equivalence`); schedule membership validation now uses O(1) runQueue membership checks | WS-H6 completed |
| **WS-H5** (v0.12.19) | IPC dual-queue structural invariant: `intrusiveQueueWellFormed`, `dualQueueSystemInvariant`, `tcbQueueLinkIntegrity`; 13 preservation theorems for all dual-queue operations; closes C-04/A-22 (CRITICAL), A-23 (HIGH), A-24 (HIGH) | WS-H5 completed |
| **WS-H4** (v0.12.18) | Capability invariant redesign: `capabilityInvariantBundle` extended from 4-tuple to 7-tuple with `cspaceSlotCountBounded`, `cdtCompleteness`, `cdtAcyclicity`; all 25+ preservation theorems re-proved against non-trivial predicates | WS-H4 completed |
| **WS-H3** (v0.12.17) | Build/CI infrastructure fixes: `run_check` return value fix (H-12), `test_docs_sync.sh` CI integration (M-19), Tier 3 `rg` availability guard with `grep -P` fallback (M-20) | WS-H3 completed |
| **WS-H2** (v0.12.16) | Lifecycle safety guards: childId collision/self-overwrite guards, TCB scheduler cleanup on retype, CNode CDT detach, atomic retype | WS-H2 completed |
| **WS-H1** (v0.12.16) | IPC call-path semantic fix: `blockedOnCall` state, reply-target scoping, 5-conjunct `ipcSchedulerContractPredicates` | WS-H1 completed |
| **WS-G** (v0.12.6–v0.12.15) | Kernel performance optimization: all hot paths migrated to O(1) hash-based structures, 14 audit findings resolved | WS-G1..G9 + refinement completed |
| **WS-F1..F4** (v0.12.2–v0.12.5) | Critical audit remediation: IPC message transfer, untyped memory, info-flow completeness, proof gap closure | WS-F1..F4 completed |
| **WS-E** (v0.11.6) | Test/CI, proof quality, kernel hardening, capability/IPC, info-flow, completeness | WS-E1..E6 completed |
| **WS-D** (v0.11.0) | Test validity, info-flow enforcement, proof gaps, kernel design | WS-D1..D4 completed; D5/D6 absorbed into WS-E |
| **WS-C** (v0.9.32) | Model structure, documentation, maintainability | WS-C1..C8 completed |
| **WS-B** (v0.9.0) | Comprehensive audit 2026-02 | WS-B1..B11 completed |

### 3.3 Security Hardening (implemented)

- IPC thread-state updates fail with `objectNotFound` for missing/reserved TCBs, preventing ghost queue entries.
- Sentinel ID `0` rejected at IPC boundaries (`lookupTcb`/`storeTcbIpcState`).
- Intrusive dual-queue endpoints with `sendQ`/`receiveQ` and per-thread links for O(1) removal. Formal structural invariant (`dualQueueSystemInvariant`) with doubly-linked integrity proofs (WS-H5).
- IPC message transfer via `TCB.pendingMessage`: messages (registers, caps, badge) flow through sender→receiver rendezvous with combined state+message helpers (`storeTcbIpcStateAndMessage`).
- **WS-H12d/A-09:** IPC message payloads bounded by `maxMessageRegisters` (120) and `maxExtraCaps` (3), matching seL4's `seL4_MsgMaxLength`/`seL4_MsgMaxExtraCaps`. Bounds enforced at all IPC send boundaries with `ipcMessageTooLarge`/`ipcMessageTooManyCaps` errors. `IpcMessage.bounded` predicate with proven send-produces-bounded theorems.
- Node-stable CDT with bidirectional slot↔node maps and strict revocation error reporting.
- Policy-checked wrappers (`endpointSendDualChecked`, `cspaceMintChecked`, `registerServiceChecked`) exercised by default in trace and probe harnesses. `enforcementBoundary` classifies 33 operations (11 policy-gated, 18 capability-only, 4 read-only). Includes SchedContext ops (WS-Z8), thread lifecycle (D1), priority management (D2), IPC buffer (D3), VSpace/service ops (AC4-D). (WS-Q1: `serviceRestartChecked` removed, `registerServiceChecked` added — service lifecycle simplified to registry-only model.)
- **WS-G1/WS-J1:** All 16 typed identifiers and the composite `SlotRef` key have `Hashable` instances with `@[inline]` for zero overhead. `Std.Data.HashMap` and `Std.Data.HashSet` imported in `Prelude.lean`, enabling O(1) hash-based data structures for kernel performance optimization (WS-G2..G9). WS-J1-A added `RegName`/`RegValue` (v0.15.4); WS-J1-F added `CdtNodeId` (v0.15.10).

---

## 4. Architectural Improvements over seL4

seLe4n is not a 1:1 formalization of seL4. It preserves seL4's capability-based
security model while introducing improvements that the Lean 4 proof framework enables:

| Area | seL4 | seLe4n Improvement |
|------|------|-------------------|
| **Service registry** *(seLe4n extension)* | No kernel-level service concept | Service registry with dependency graphs, acyclic policy enforcement, isolation edges (novel seLe4n extension — not present in seL4). WS-Q1 simplified to stateless registry model: no `ServiceStatus`/`ServiceConfig`/lifecycle ops. R4: cross-subsystem invariants — endpoint cleanup on TCB retype, service registration authority check (Write right + endpoint type verification), dependency graph cleanup on revocation, `crossSubsystemInvariant` bundle (12 predicates: Z9 5→8, AE5-C +registryInterfaceValid, AF1-B3 +blockingAcyclic, AM4 +lifecycleObjectTypeLockstep, AK8-A +untypedRegionsDisjoint) in `proofLayerInvariantBundle` |
| **CDT representation** | Mutable doubly-linked list | Node-stable CDT with O(1) slot transfer via pointer/backpointer fixup |
| **IPC queuing** | Intrusive linked list | Dual-queue model (`sendQ`/`receiveQ`) with O(1) arbitrary removal; `blockedOnCall` state for call/reply semantics; reply-target scoping for confused-deputy prevention; formal `dualQueueSystemInvariant` with doubly-linked integrity (WS-H5) |
| **Information flow** | Binary high/low partition | Parameterized N-domain labels with per-endpoint flow policies |
| **Scheduling** | Priority-based round-robin | Priority + EDF scheduling with dequeue-on-dispatch semantics, per-TCB register context with inline context switch, and domain-aware partitioning |
| **Revocation** | Silent error swallowing | Strict variant (`cspaceRevokeCdtStrict`) reporting first failure with context; CDT node preserved on slot deletion failure (AH3-A) |
| **Syscall boundary** *(WS-J1-A/B/C/D completed; WS-V V2 complete)* | C code extracts args from registers | Typed register wrappers (J1-A) + total decode layer with `RegisterDecode.lean`, complete round-trip proof surface for all 3 decode components (`decodeCapPtr_roundtrip`, `decodeSyscallId_roundtrip`, `decodeMsgInfo_roundtrip` with bitwise `Nat.testBit` extensionality, plus composite `decode_components_roundtrip`), determinism proof, and error exclusivity (J1-B) + `syscallEntry` register-sourced entry point with capability-gated dispatch to all 17 kernel operations (13 original + `notificationSignal`/`notificationWait`/`replyRecv` added in V2), soundness theorems (J1-C) + invariant preservation and NI coverage for decode/dispatch path with `registerDecodeConsistent` predicate and 2 new `NonInterferenceStep` constructors (J1-D); `MessageInfo` label field bounded to 20 bits (seL4 convention, V2-E/V2-H); cap transfer slot base configurable via `capRecvSlot` (V2-F/V2-G) |

These are not abstract research extensions — they are design decisions that will be
carried forward into the production kernel.

---

## 5. Completed Workstream Portfolio (WS-G) and Next Steps

The WS-G portfolio addressed kernel performance optimization findings from the
[v0.12.5 performance audit](../dev_history/audits/KERNEL_PERFORMANCE_AUDIT_v0.12.5.md).
All 9 workstreams completed (v0.12.6–v0.12.15), closing all 14 findings.

Authoritative detail:
[`docs/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md`](../dev_history/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md).

### 5.1 Completed — Data Structure Optimization

- **WS-G1:** ~~Typed identifier Hashable instances~~ **COMPLETED** — `Hashable` + `LawfulHashable` for all 16 typed identifiers (13 original + `RegName`/`RegValue` via WS-J1-A + `CdtNodeId` via WS-J1-F); `Std.HashMap`/`Std.HashSet` imports; zero-overhead foundation for O(1) lookups (v0.12.6, extended v0.15.4/v0.15.10)
- **WS-G2:** ~~Object store & ObjectIndex HashMap~~ **COMPLETED** — `objects : Std.HashMap ObjId KernelObject` replacing closure-chain accumulation; `objectIndexSet : Std.HashSet ObjId` shadow set for O(1) membership; `objectTypes : Std.HashMap ObjId KernelObjectType` lifecycle metadata; 9 bridge lemmas; full proof migration (599 theorems verified); closes F-P01, F-P10, F-P13 (v0.12.7)
- **WS-G3:** ~~ASID Resolution Table~~ **COMPLETED** — `asidTable : Std.HashMap ASID ObjId` in `SystemState`; `resolveAsidRoot` rewritten from O(n) `objectIndex.findSome?` to O(1) HashMap lookup with object-store validation; bidirectional `asidTableConsistent` invariant (soundness + completeness); `vspaceInvariantBundle` extended to 3-conjunct; erase-before-insert maintenance in `storeObject`; 3 bridge lemmas; round-trip theorems simplified; closes F-P06 (v0.12.8)

### 5.2 Completed — Scheduler Optimization

- **WS-G4:** ~~Run queue restructure~~ **COMPLETED** — `RunQueue` structure with `Std.HashMap Priority (List ThreadId)` + `Std.HashSet ThreadId` + bidirectional structural invariants (`flat_wf`, `flat_wf_rev`); `SchedulerState.runQueue` replaces flat `runnable : List ThreadId`; O(1) `insert`/`remove`/`contains`/`rotateHead`/`rotateToBack`; `chooseBestInBucket` bucket-first scheduling reduces best-candidate selection from O(t) to O(k); `withRunnableQueue`/`runnableHead`/`runnableTail` eliminated; 13 bridge lemmas; 30+ IPC invariant proofs migrated; info-flow projection re-proved; closes F-P02, F-P07, F-P12 (v0.12.9)

### 5.3 Completed — CNode Optimization

- **WS-G5:** ~~CNode slot HashMap~~ **COMPLETED** — `CNode.slots : Std.HashMap Slot Capability` replacing `List (Slot × Capability)`; `lookup`/`insert`/`remove` all O(1) amortized; `slotsUnique` trivially true (HashMap key uniqueness); 2 bridge lemmas (`HashMap_filter_preserves_key`, `HashMap_filter_filter_getElem?`); `projectKernelObject_idempotent` reformulated to slot-level lookup equality; `cspaceRevoke` `revokedRefs` via `HashMap.fold` (single O(m) pass); manual `BEq CNode`/`BEq KernelObject` instances; 10 files modified; closes F-P03 (v0.12.10)

### 5.4 Completed — VSpace Optimization

- **WS-G6:** ~~VSpace mapping HashMap~~ **COMPLETED** — `VSpaceRoot.mappings : Std.HashMap VAddr PAddr` replacing `List (VAddr × PAddr)` (enriched to `Std.HashMap VAddr (PAddr × PagePermissions)` by WS-H11); `lookup`/`mapPage`/`unmapPage` all O(1) amortized; universal `noVirtualOverlap_trivial` theorem proves the property for all VSpaceRoots (HashMap key uniqueness); round-trip theorems re-proved with HashMap bridge lemmas; manual `BEq VSpaceRoot` instance; `boundedAddressTranslation` reformulated for HashMap; `hashMapVSpaceBackend` replaces `listVSpaceBackend`; 7 files modified; closes F-P05 (v0.12.11)

### 5.5 Completed — IPC Queue & Notification Optimization

- **WS-G7:** ~~IPC Queue Completion & Notification~~ **COMPLETED** — Legacy `endpointSend`/`endpointReceive`/`endpointAwaitReceive` deprecated (removed in WS-H12a); trace harness and sequence probe migrated to O(1) dual-queue (`endpointSendDual`/`endpointReceiveDual`). `notificationWait` O(n) duplicate check replaced with O(1) TCB `ipcState` check; O(n) append replaced with O(1) prepend. New `notificationWaiterConsistent` invariant bridges TCB state to queue membership. `endpointSendDualChecked` enforcement wrapper added. All invariant proofs re-proved; 9 files modified; closes F-P04 and F-P11 (v0.12.12)

### 5.6 WS-G8: Graph Traversal Optimization (completed, v0.12.13)

- **WS-G8:** ~~Graph Traversal Optimization~~ **COMPLETED** — `serviceHasPathTo` rewritten from O(n²) BFS with `List ServiceId` to O(n+e) DFS with `Std.HashSet ServiceId`. `CapDerivationTree` extended with `childMap : Std.HashMap CdtNodeId (List CdtNodeId)` parent-indexed edge index; `childrenOf` O(1) HashMap lookup; `descendantsOf` O(N+E) total. `childMapConsistent` invariant with `empty`/`addEdge` preservation proofs. Full invariant proof migration; closes F-P08, F-P14 (v0.12.13)

### 5.7 WS-G9: Information-Flow Projection Optimization (completed, v0.12.14)

- **WS-G9:** ~~Information-Flow Projection Optimization~~ **COMPLETED** — `computeObservableSet` precomputes `Std.HashSet ObjId` via single `foldl` pass; `projectObjectsFast`, `projectIrqHandlersFast`, `projectObjectIndexFast` use O(1) `contains` lookups instead of redundant `objectObservable` re-evaluation. `projectStateFast_eq` proves equivalence with original `projectState` (`@[csimp]`-ready). Zero downstream proof breakage — all NI theorems, enforcement wrappers, and invariant proofs unchanged. 3 HashSet foldl bridge lemmas in `Prelude.lean`; closes F-P09 (v0.12.14)

### 5.8 WS-G Refinement Pass (v0.12.15)

Post-completion refinement addressing residual code quality, validation gaps, and test coverage across the WS-G portfolio:

- **RunQueue.remove optimization:** Eliminated redundant bucket computation — filtered bucket now computed once and reused for both `byPriority` and `maxPriority` updates.
- **WS-H6 scheduler proof completion:** Added reverse RunQueue bridge `membership_implies_flat`, bidirectional membership/list equivalence `mem_toList_iff_mem`, candidate-order transitivity `isBetterCandidate_transitive`, and bucket/full-scan equivalence theorem `bucketFirst_fullScan_equivalence`.
- **WS-H6 scheduler runtime optimization:** `schedule` now validates selection using O(1) `tid ∈ st.scheduler.runQueue` while preserving list-level reasoning via bridge lemmas.
- **MachineConfig validation hardening:** `wellFormed` now validates `pageSize` as a positive power of two via `isPowerOfTwo` (bitwise check), strengthening platform configuration safety.
- **Dead code removal:** Removed unused `filterByDomain` from `Scheduler/Operations.lean` (superseded by WS-G4 bucket-first scheduling).
- **Phantom object cleanup:** Removed object ID 200 from `bootstrapInvariantObjectIds` (no corresponding bootstrap object).
- **Runtime invariant checks:** Added `runQueueThreadPriorityConsistentB` (RunQueue membership ↔ threadPriority consistency) and `cdtChildMapConsistentCheck` (CDT childMap ↔ edges bidirectional consistency).
- **StateBuilder priority fix:** `BootstrapBuilder.build` uses actual TCB priorities for RunQueue bucketing instead of defaulting to priority 0.
- **Test coverage expansion:** `NegativeStateSuite` extended with `endpointReplyRecv` (2 negative + 1 positive via endpointCall chain) and `cspaceMutate` (2 negative + 2 positive including badge override) audit coverage checks.

### 5.9 WS-H1: IPC Call-Path Semantic Fix (completed, v0.12.16)

WS-H1 addresses the IPC call-path semantic gap identified in the v0.12.15 audit.
The `endpointCall` operation now transitions the caller to a distinct `blockedOnCall`
state (rather than reusing `blockedOnReply`), and reply operations validate the
authorized replier via reply-target scoping.

- **Part A (C-01 CRITICAL):** Added `blockedOnCall endpointId` variant to `ThreadIpcState`; `endpointCall` transitions caller to `blockedOnCall` instead of `blockedOnReply`; `endpointReceiveDual` detects call-origin senders via `senderWasCall` match and transitions them to `blockedOnReply endpointId (some caller)` with reply-target scoping.
- **Part B (M-02 MEDIUM):** `endpointReply`/`endpointReplyRecv` validate `expectedReplier` field — only the designated receiver can complete the reply, preventing confused-deputy attacks.
- **Part C (Invariant maintenance):** `ipcSchedulerContractPredicates` expanded from 3 to 6 conjuncts (added `blockedOnCallNotRunnable`, `blockedOnReplyNotRunnable`, `blockedOnNotificationNotRunnable` via WS-F6/D2); all 62+ IPC invariant preservation theorems re-proved with zero sorry/axiom; 5 H1-series trace anchors added.

### 5.10 WS-H11: VSpace & Architecture Enrichment (completed, v0.13.7)

WS-H11 enriches the VSpace subsystem with per-page permissions, W^X enforcement,
bounded address translation checks, and an abstract TLB maintenance model.

- **Part A (H-02/A-32):** `PagePermissions` structure with `read`/`write`/`execute`/`user`/`cacheable` fields; `VSpaceRoot.mappings` enriched from `HashMap VAddr PAddr` to `HashMap VAddr (PAddr × PagePermissions)`; `vspaceMapPage` enforces W^X at insertion (returns `policyDenied` on violation); `vspaceLookupFull` returns `(PAddr × PagePermissions)`; `VSpaceBackend` typeclass enriched with permissions; all round-trip and preservation theorems re-proved.
- **Part B (A-05/M-12/M-14):** `MemoryRegion.wellFormed` validates `endAddr ≤ 2^physicalAddressWidth`; `MachineConfig.wellFormed` extended with per-region overflow check; `boundedAddressTranslation` integrated into `vspaceInvariantBundle`.
- **Part C (A-12):** Global ASID uniqueness via `vspaceAsidRootsUnique` and `asidTableConsistent` (already in bundle since WS-G3); preservation proven for all VSpace operations.
- **Part D (H-10):** Abstract TLB model — `TlbEntry`/`TlbState` structures; `adapterFlushTlb` (full flush) and `adapterFlushTlbByAsid` (per-ASID flush); `tlbConsistent` invariant; flush-restoration and composition theorems.

`vspaceInvariantBundle` now contains 6 conjuncts: `vspaceAsidRootsUnique`, `vspaceRootNonOverlap`, `asidTableConsistent`, `wxExclusiveInvariant`, `boundedAddressTranslation`, `vspaceCrossAsidIsolation` (WS-F6/D6).

### 5.11 Prior Portfolio: WS-F (completed, v0.12.2)

The WS-F portfolio addressed findings from two independent v0.12.2 codebase audits.
Combined: 6 CRITICAL, 6 HIGH, 12 MEDIUM, 9 LOW findings.

- **WS-F1:** ~~IPC message transfer and dual-queue verification~~ **COMPLETED**
- **WS-F2:** ~~Untyped memory model~~ **COMPLETED**
- **WS-F3:** ~~Information-flow completeness~~ **COMPLETED**
- **WS-F4:** ~~Proof gap closure~~ **COMPLETED**
- **WS-F5–F8:** Medium/Low priority — immediate next steps (see below)

### 5.12 Next Steps: Remaining WS-F Workstreams (F5–F8)

The remaining WS-F workstreams address medium/low-priority findings:

| ID | Focus | Priority | Status |
|----|-------|----------|--------|
| **WS-F5** | Model fidelity (word-bounded badge, order-independent rights, deferred ops) | Medium | **Completed** (v0.14.9) |
| **WS-F6** | Invariant quality (tautology reclassification, adapter proof hooks) | Medium | **Completed** (v0.14.9) |
| **WS-F7** | Testing expansion (oracle, probe, fixtures) | Low | **Completed** (v0.14.9) |
| **WS-F8** | Cleanup (dead code, legacy/dual-queue resolution) | Low | **Completed** (v0.14.9) |
| **WS-I1** | Critical testing infrastructure (inter-transition assertions, mandatory determinism, scenario ID traceability) | High | **Completed** (v0.15.0) |
| **WS-I3** | Test coverage expansion — operations (multi-operation chains, scheduler stress, declassification checks) | Medium | **Completed** (v0.15.2) |
| **WS-I4** | Test coverage expansion — subsystems (VSpace multi-ASID sharing, IPC interleaving, lifecycle cascading chains) | Low | **Completed** (v0.15.3) |

After WS-F/WS-I1: Raspberry Pi 5 hardware binding (H3).

### 5.13 WS-I1: Critical Testing Infrastructure (completed, v0.15.0)

WS-I1 is the first workstream of the WS-I improvement portfolio, addressing three
critical testing infrastructure recommendations from the v0.14.9 audit.

- **Part A (R-01 — Inter-transition assertions):** 17 `checkInvariants` calls inserted across all 13 trace functions in `MainTraceHarness.lean`. Each call invokes `assertStateInvariantsFor` (17 invariant check families covering scheduler, CSpace, IPC, lifecycle, service, VSpace, CDT, ASID, untyped, notification, blocked-thread, and domain invariants) with `IO.Ref Nat` counter tracking. Summary `[ITR-001]` line confirms all 17 checks passed. Zero sorry/axiom.
- **Part B (R-02 — Mandatory determinism):** `scripts/test_tier2_determinism.sh` runs the trace harness twice and diffs output, failing on any divergence. Integrated into `test_smoke.sh` Tier 2 gate (between trace and negative checks), making determinism a mandatory CI property rather than an optional Tier 4 extension.
- **Part C (R-03 — Scenario ID traceability):** All 121 trace output lines tagged with unique scenario IDs (15 prefix families: ENT, CAT, SST, LEP, CIC, IMT, IMB, DDT, ICS, BME, STD, UMT, SGT, RCF, ITR, PTY). Fixture format upgraded to pipe-delimited (`SCENARIO_ID | SUBSYSTEM | expected_trace_fragment`). `tests/fixtures/scenario_registry.yaml` maps all 121 IDs to source functions and subsystems. `scripts/scenario_catalog.py validate-registry` checks bidirectional fixture↔registry consistency. Tier 0 hygiene validates registry on every PR.
- **WS-I2 (v0.15.1):** proof/validation depth completed: Tier 0 now runs semantic L-08 theorem-body analysis (`scripts/check_proof_depth.py` with regex fallback), Tier 3 now runs Lean `#check` correctness anchors across scheduler/capability/IPC/lifecycle/service/VSpace/IF preservation theorems, and IF projection now supports optional memory-domain ownership (`memoryOwnership`) with backward-compatible default (`none`).
- **WS-I3 (v0.15.2):** operations coverage expansion completed: new `tests/OperationChainSuite.lean` adds six multi-operation chain tests and scheduler stress coverage (16-thread repeated schedule/yield, same-priority determinism, multi-domain domain-switch isolation); Tier 2 now executes this suite via `scripts/test_tier2_negative.sh`; `tests/InformationFlowSuite.lean` adds declassification runtime checks for authorized downgrade, normal-flow rejection, policy-denied rejection, and three-domain lattice behavior. The declassification policy-denied branch is represented explicitly as `KernelError.declassificationDenied` for clearer failure-mode discrimination.
- **WS-I4 (v0.15.3):** subsystem coverage expansion completed in `tests/OperationChainSuite.lean` with three new chain families: (R-09) VSpace multi-ASID shared-page coherency and per-ASID permission independence checks (including post-unmap isolation), (R-10) endpoint IPC interleaved three-sender FIFO plus alternating send/receive ordering checks, and (R-11) lifecycle authority-degradation and CDT cascading-revoke chains (root→child→grandchild) validating descendant cleanup and non-amplification of rights.

### 5.14 Deferred Operations (WS-F5/D3)

The following seL4 operations are intentionally deferred from the current model.
Each has a documented rationale and prerequisite milestone:

| Operation | seL4 Equivalent | Rationale | Prerequisite | Status |
|-----------|----------------|-----------|--------------|--------|
| `setPriority` | `seL4_TCB_SetPriority` | MCP authority validation, SchedContext-aware priority update, run queue migration | MCS scheduling (Z1–Z5) | **Implemented (D2, v0.24.1)** |
| `setMCPriority` | `seL4_TCB_SetMCPriority` | MCP ceiling update with retroactive priority capping | MCS scheduling (Z1–Z5) | **Implemented (D2, v0.24.1)** |
| `suspend` | `seL4_TCB_Suspend` | Requires thread lifecycle state machine | WS-F6 (lifecycle invariants) | **Implemented (D1, v0.24.0)** |
| `resume` | `seL4_TCB_Resume` | Inverse of suspend; same prerequisite | WS-F6 (lifecycle invariants) | **Implemented (D1, v0.24.0)** |
| `setIPCBuffer` | `seL4_TCB_SetIPCBuffer` | VSpace-validated IPC buffer address update | H3 (VSpace integration) | **Implemented (D3, v0.24.2–v0.24.3)** |

**D1 (v0.24.0):** Thread suspension and resumption are now fully implemented.
`suspendThread` performs the complete cleanup pipeline (IPC blocking cancellation,
SchedContext donation cleanup, run queue removal, pending state clearing, state
transition to Inactive). `resumeThread` transitions from Inactive to Ready with
conditional preemption. Both operations are wired into the API dispatch layer
(`SyscallId.tcbSuspend`, `.tcbResume`) as capability-only arms and have frozen-phase
equivalents. Transport lemmas prove scheduler, serviceRegistry, and lifecycle
preservation through all suspension sub-operations.

These operations are tracked in `SeLe4n/Kernel/API.lean` (stability table) and
`docs/CLAIM_EVIDENCE_INDEX.md` (evidence tracking).

**D2 (v0.24.1):** Priority management is now fully implemented. `setPriorityOp`
validates MCP authority, updates priority on SchedContext (if bound) or TCB
(if unbound), migrates run queue buckets, and triggers conditional reschedule.
`setMCPriorityOp` updates the MCP ceiling and retroactively caps the thread's
current priority if it exceeds the new MCP. Both operations are wired into
`dispatchWithCap` (`SyscallId.tcbSetPriority`, `.tcbSetMCPriority`) as
capability-only arms with frozen-phase equivalents. Preservation theorems
prove authority non-escalation (`setPriority_authority_bounded`,
`setMCPriority_authority_bounded`) and transport lemmas guarantee scheduler,
serviceRegistry, and lifecycle field preservation.

**D3 (v0.24.2):** IPC buffer configuration is now fully implemented.
`setIPCBufferOp` validates the buffer address through a 7-step pipeline
(alignment to 512 bytes, canonical address check, VSpace root validity,
mapping existence via VSpaceRoot.lookup, write permission, physical address
bounds check against `2^physicalAddressWidth` — AJ4-C) before updating
the TCB's `ipcBuffer` field. The operation is wired into `dispatchWithCap`
(`SyscallId.tcbSetIPCBuffer`) as a capability-only arm with a frozen-phase
equivalent (`frozenSetIPCBuffer`). Validation correctness theorems prove that
successful validation implies alignment and mapped-writable guarantees.
Frame preservation is trivial since `ipcBuffer` is not referenced by any
scheduler, IPC, cross-subsystem, or capability invariant predicate. As of
AH3-B (v0.27.4), the TCB update delegates to `storeObject` — ensuring
consistency with the canonical object storage path and eliminating manual
struct-with replication.

**D4 (v0.25.0):** Priority Inheritance Protocol is now fully implemented.
A deterministic PIP temporarily elevates a server thread's effective scheduling
priority when it holds a pending Reply on behalf of a higher-priority client,
resolving transitive priority inversion (SV-2). Key components:

- **`pipBoost` TCB field**: `Option Priority := none`. When `some p`, the
  thread's effective priority is `max(SchedContext.priority, p)`.
- **Blocking graph**: `blockedOnThread` predicate, `waitersOf` (direct
  dependents), `blockingChain` (fuel-bounded transitive walk). Acyclicity
  and depth bound proven (`blockingChain_length_le_fuel`).
- **Propagation/Reversion**: `propagatePriorityInheritance` walks the
  blocking chain upward from a server, applying `updatePipBoost` at each
  step. `revertPriorityInheritance` recomputes after client unblock. Both
  are structurally identical (`revert_eq_propagate`).
- **Integration**: Call path propagates PIP after blocking
  (`endpointCallWithDonation`), Reply/ReplyRecv paths revert PIP after
  unblock, Suspend path reverts PIP before cleanup, Timeout path reverts
  PIP for server when timed-out client was in `blockedOnReply`.
- **Composition with SchedContext donation (Z7)**: PIP provides an
  additional boost beyond the donated SchedContext priority via the
  `max(scPrio, pipBoost)` computation in `effectiveSchedParams` (the
  total successor to the retired `effectivePriority`; see WS-RC R5.C.1).
- **Bounded inversion**: `pip_bounded_inversion` proves priority inversion
  bounded by `objectIndex.length * WCRT`.
- **16 frame preservation theorems**, determinism proofs, 22 test cases.

**D5 (v0.25.0):** Bounded Latency Theorem is now proven — the first
machine-checked WCRT for a microkernel with MCS scheduling contexts. Zero
kernel code changes (proof-only phase). Key results:

- **Trace model**: `SchedulerStep` (9 constructors), `SchedulerTrace`,
  `validTrace` predicate, query predicates (`selectedAt`, `runnableAt`,
  `budgetAvailableAt`), counting functions.
- **Per-mechanism bounds**: `timerTickBudget_bound_succeeds` (budget
  decrement characterization), `replenishment_within_period` (CBS
  replenishment timing), `fifo_progress_in_band` (FIFO progress within
  priority band), `domainRotationTotal_le_bound` (domain rotation).
- **WCRT hypotheses**: `WCRTHypotheses` structure with 14 fields
  (threadRunnable, threadHasBudget, targetPrio, targetDomain, threadInDomain,
  N, higherPriorityBound, B, maxBudgetBound, P, maxPeriodBound,
  domainScheduleAdequate, domainEntriesPositive, domainScheduleNonEmpty).
- **Main theorem**: `wcrtBound_unfold` / `bounded_scheduling_latency_exists` proves WCRT =
  D * L_max + N * (B + P), where D = domain schedule entries,
  L_max = maximum domain time, N = higher-priority thread count,
  B = max budget, P = max period.
- **PIP enhancement**: `pip_enhanced_wcrt_le_base` shows PIP-boosted
  threads have tighter WCRT (fewer higher-priority competitors).
- 58 surface anchor tests in `LivenessSuite.lean`.

**D6 (v0.25.2):** API Surface Integration & Closure. Rust ABI synchronized
with 5 new `SyscallId` variants (20→25) and `AlignmentError` (43). All 25
SyscallId variants, 33 enforcement boundary entries, 20 frozen operations,
and 25 dispatch arms verified. Documentation fully synchronized.

---

## 6. Hardware Target: Raspberry Pi 5

The first production hardware target is **Raspberry Pi 5** (ARM64, BCM2712).

### 6.1 Why Raspberry Pi 5

1. Practical ARM64 platform for repeated experiments and bring-up
2. Realistic interrupt/memory/boot profile for architecture-bound modeling
3. Broad tooling availability and community support
4. Good tradeoff between accessibility and systems realism

### 6.2 Path to Hardware

| Stage | Description | Status |
|-------|-------------|--------|
| **H0** | Architecture-neutral semantics and proofs | Complete (M1–M7, WS-B..E) |
| **H1** | Architecture-boundary interfaces and adapters | Complete (M6) |
| **H2** | Audit-driven proof deepening (close critical gaps) | Complete (WS-F and WS-H portfolios) |
| **H3** | Platform binding — map interfaces to Raspberry Pi 5 hardware | **COMPLETE** (AG1–AG10, v0.26.0–v0.27.1) |
| **H4** | Evidence convergence — connect proofs to platform assumptions | Planned |

**H3 preparation (structural):** The `Platform/` directory now provides the
organizational foundation for hardware binding:

- `PlatformBinding` typeclass (`SeLe4n/Platform/Contract.lean`)
- `MachineConfig` and `MemoryRegion` types (`SeLe4n/Machine.lean`);
  `defaultMachineConfig` constant with ARM64 defaults (AH2-E)
- `PlatformConfig.machineConfig` field — `bootFromPlatform` now calls
  `applyMachineConfig` as its final step, ensuring machine state fields
  (register width, address widths, page size, ASID limit, memory map) are
  always set from platform configuration (AH2-F, M-03/L-16 fix)
- `VSpaceBackend` abstraction with permissions-enriched `hashMapVSpaceBackend` instance (WS-G6/WS-H11)
- `ExtendedBootBoundaryContract` with platform boot fields
- Simulation platform (`Platform/Sim/`) for testing
- RPi5 platform (`Platform/RPi5/`) with BCM2712 memory map, GIC-400 constants,
  ARM64 machine config, and platform-specific runtime contract
- GIC-400 interrupt controller driver (`sele4n-hal/src/gic.rs`) with
  distributor/CPU interface init, acknowledge/dispatch/EOI sequence
- ARM Generic Timer driver (`sele4n-hal/src/timer.rs`) at 54 MHz with
  configurable tick rate and counter-relative reprogramming
- Interrupt-disabled region primitives (`sele4n-hal/src/interrupts.rs`) via
  DAIF register for critical section enforcement
- Lean interrupt model: `MachineState.interruptsEnabled`, exception-entry
  atomicity proofs, timer interrupt → `timerTick` binding, `handleInterrupt`
  NI step (35th `KernelOperation`)

**H3 binding progress**: AG1 (Lean code fixes) → AG2 (Rust ABI fixes) → AG3
(platform model) → AG4 (HAL crate + boot) → AG5 (interrupts + timer) → AG6
(ARMv8 memory management) → AG7 (FFI bridge + proof hooks) → AG8 (integration
+ model closure) → AG9 (testing + validation) → AG10 (documentation + closure).
**All 10 phases COMPLETE** (v0.26.0–v0.27.1).

### 6.2.1 DTB peripheral-discovery depth (AN7-D.5 / PLT-M06, v0.30.8)

`extractPeripherals` in `SeLe4n/Platform/DeviceTree.lean` performs a
**fuel-bounded recursive depth-first walk** of the FDT tree, replacing
the previous hardcoded 2-level traversal (top-level + direct children
only).  The new walk supports arbitrary nesting depth, which is required
for ARM SoC platforms with nested bus hierarchies (`simple-bus`, `i2c`,
`spi`, `usb` controllers exposing child devices).

**Fuel contract**:
- Default fuel `1024` comfortably exceeds the BCM2712 node count (~200).
- Termination is guaranteed structurally by the decreasing `fuel`
  parameter.
- `extractPeripherals_zero_fuel` and `extractPeripherals_empty` witness
  the two base cases of the recursion at the invariant surface.
- `extractPeripherals_fuel_sufficient_for_BCM2712 : 1024 ≥ 200` anchors
  the sufficiency bound.

**Boundary guarantees**:
- On fuel exhaustion, the walk returns the entries collected so far
  (graceful degradation).
- Consumers that need exhaustion detection should invoke `parseFdtNodes`
  first; that function propagates `DeviceTreeParseError.fuelExhausted`
  explicitly (AJ3-A).

**Regression coverage**: `tests/Ak9PlatformSuite.lean` includes 8
runtime tests (`an7d5_01..04`) exercising:

- Depth-3 peripheral discovery (`level1-bus` → `level2-controller` →
  `level3-device` nested tree, all three extracted).
- Zero-fuel collapse (empty-list return regardless of tree depth).
- Incomplete-node skip (nodes lacking `reg` or `compatible` are
  correctly filtered out).
- Reserved-name exclusion (`memory@*` / `cpus` / `chosen` are excluded
  even when they carry proper `reg` + `compatible` properties).

The tests are constructed programmatically via `FdtNode` values with
explicit big-endian `reg` property encoding; no synthesized DTB-blob
infrastructure is required.

### 6.3 Cache Coherency & Memory Ordering Assumptions (T6-G/M-NEW-8)

The seLe4n model makes the following cache coherency and memory ordering
assumptions for the initial single-core RPi5 target:

1. **Single-core assumption**: The RPi5 target uses one Cortex-A76 core.
   Single-core execution eliminates most cache coherency concerns — all loads
   and stores from the same core observe a consistent memory view without
   explicit cache maintenance.

2. **MMIO requires barriers**: Device register accesses (MMIO) are *not*
   subject to normal memory ordering guarantees. All MMIO operations must use
   explicit ARM64 memory barriers:
   - **Reads**: `DMB` (Data Memory Barrier) after read to ensure the value
     is visible before subsequent dependent accesses.
   - **Writes**: `DSB` (Data Synchronization Barrier) before write to ensure
     prior writes complete before the device register update.
   - **Configuration writes**: `ISB` (Instruction Synchronization Barrier)
     after writes to system configuration registers (e.g., MMU, GIC) to
     flush the instruction pipeline.

   The MMIO adapter (`Platform/RPi5/MmioAdapter.lean`) models these barriers
   as fields on `MmioOp`. The `MemoryBarrier` inductive (DMB, DSB, ISB)
   captures the three ARM64 barrier types.

3. **DMA coherency is out of scope**: Direct Memory Access (DMA) coherency
   requires explicit cache clean/invalidate operations and is not modeled.
   DMA is relevant only for device drivers (USB, SD, network), which are
   outside the kernel's formal boundary. DMA coherency will be addressed in
   WS-U if multicore or DMA-capable device drivers are targeted.

4. **TLB coherency**: TLB invalidation after page table modifications is
   modeled via `adapterFlushTlb` (full flush), `adapterFlushTlbByAsid`
   (per-ASID flush), and `adapterFlushTlbByVAddr` (per-page flush). The
   production dispatch path uses `vspaceMapPageCheckedWithFlush` which
   includes a full flush. Targeted flushes (`tlbFlushByASID`, `tlbFlushByPage`)
   are defined for future optimization but not yet wired into production paths.

### 6.4 Hardware Limitations (AG10-A / FINDING-05)

The H3 hardware binding targets **single-core operation** on Raspberry Pi 5:

1. **Single-core execution**: H3 uses Cortex-A76 core 0 only. The remaining
   3 cores are held in a WFE (Wait For Event) loop by the AG4-E boot sequence
   (`sele4n-hal/src/boot.S`). All kernel state is core-local — no spinlocks,
   no inter-processor interrupts (IPI), no cross-core scheduling.

2. **SMP implications**: Symmetric multiprocessing is implemented in WS-SM
   (pre-v1.0.0), tracked in
   [`docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md`](../planning/SMP_MULTICORE_COMPLETION_PLAN.md).
   The phased plan delivers each capability in its own sub-plan:
   - Per-core run queues with work-stealing or affinity-based scheduling →
     [`SMP_PER_CORE_SCHEDULER_PLAN.md`](../planning/SMP_PER_CORE_SCHEDULER_PLAN.md)
   - IPI for cross-core preemption notification (SGI INTID 0–4 reserved at
     SM0.H) and TLB shootdown →
     [`SMP_TLB_SHOOTDOWN_PLAN.md`](../planning/SMP_TLB_SHOOTDOWN_PLAN.md)
   - Verified ticket lock + RW lock primitives for shared kernel state →
     [`SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md`](../planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md)
   - Per-object lock acquisition discipline (LockId total order from SM0.I) →
     [`SMP_PER_OBJECT_LOCKS_PLAN.md`](../planning/SMP_PER_OBJECT_LOCKS_PLAN.md)
   - Cache coherency model (MOESI on Cortex-A76, managed by hardware; software
     ensures proper barrier usage via `BarrierKind` selection from SM0.F) — no
     dedicated sub-plan; lives inside per-object lock primitives
   - Per-core TLB flush coordination (currently single-core TLBI suffices) →
     [`SMP_TLB_SHOOTDOWN_PLAN.md`](../planning/SMP_TLB_SHOOTDOWN_PLAN.md)
   - Per-core exception vector tables and interrupt routing →
     [`SMP_RUST_HAL_PLAN.md`](../planning/SMP_RUST_HAL_PLAN.md)
   - Per-core kernel state (run queue head, current thread, idle TCB) →
     [`SMP_PER_CORE_STATE_PLAN.md`](../planning/SMP_PER_CORE_STATE_PLAN.md)
   - Cross-core IPC fast-path →
     [`SMP_CROSS_CORE_IPC_PLAN.md`](../planning/SMP_CROSS_CORE_IPC_PLAN.md)
   - Information-flow projection under SMP →
     [`SMP_INFORMATION_FLOW_PLAN.md`](../planning/SMP_INFORMATION_FLOW_PLAN.md)
   WS-SM Phase SM0 (foundations & honesty patches) closes the type-level
   scaffolding (CoreId, LockKind, LockId, SgiKind, SharingDomain,
   BklState) at v0.31.3; SM1..SM9 wire those types into runtime state.

   WS-SM Phase SM1.A (PSCI completion) extends the Rust HAL's PSCI
   surface to the full ARM DEN0022D §5 subset (`cpu_off`,
   `affinity_info`, `system_off`, `system_reset`, `psci_version`,
   `migrate_info_type`).  WS-SM Phase SM1.B (closes SMP-M4) populates
   the per-CPU data block (`PerCpuData` in
   `rust/sele4n-hal/src/per_cpu.rs`) and exposes
   `current_core_id_from_tpidr()` via the new
   `ffi_current_core_id` FFI export; the Lean side wraps it as
   `Concurrency.currentCoreId : BaseIO CoreId` in
   `SeLe4n/Kernel/Concurrency/Runtime.lean`, where the typed `CoreId
   = Fin numCores` return value is range-checked against `numCores`.
   `TPIDR_EL1` is written on every core's first kernel-mode entry
   (`boot.rs::rust_boot_main` Phase 4 for the boot core,
   `boot.S::secondary_entry` for secondaries), so an
   `mrs xN, tpidr_el1` instruction is a single-cycle per-core lookup
   on Cortex-A76.

   WS-SM Phase SM1.C (closes SMP-C2) rewrites
   `rust_secondary_main` as the full per-core boot pipeline:
   (1) wait on `CORE_READY[i]` with bounded WFE for the primary's
   PSCI authorization signal; (2) `mmu::init_mmu_secondary(core_id)`
   re-applying the AK5-C SCTLR_EL1 bitmap via the shared
   `init_mmu_per_core` helper (TTBRs point at the primary's
   shared boot L1 table); (3)
   `boot::install_exception_vectors()` for VBAR_EL1
   (shared call with the primary's `rust_boot_main` Phase 2);
   (4) `gic::init_cpu_interface_secondary(core_id)` for the
   banked-per-core GIC CPU interface; (5)
   `timer::init_timer_secondary(tick_hz)` arming this core's
   `CNTP_CVAL_EL0` without resetting the primary's monotonic
   `TICK_COUNT`; (6) `enable_irq()` to unmask PSTATE.I; (7)
   jump into the Lean kernel via
   `lean_secondary_kernel_main(context_id)`, which resolves to
   `SeLe4n.Kernel.secondaryKernelMain` (defined in
   `SeLe4n/Kernel/SecondaryEntry.lean` with
   `@[export lean_secondary_kernel_main]`).  At SM1.C the Lean side
   is a placeholder `pure ()`; SM5 replaces it with the per-core
   scheduler entry.  Three `build.rs` regression scanners pin the
   primary/secondary call-site symmetry and the SM1.C.5 init-helper
   call chain at build time.

   WS-SM Phase SM1.D (v0.31.6) wires `rust_boot_main` Phase 5 to
   parse the DTB-supplied `/chosen/bootargs` cmdline via the new
   `cmdline.rs` module — a self-contained FDT walker (fuel-bounded,
   depth-bounded) extracts the bootargs, the `parse_cmdline`
   token parser produces a typed `CmdlineConfig`, and
   `apply_cmdline_and_start_smp` writes `smp::SMP_ENABLED` then
   dispatches `bring_up_secondaries_with_limit` (SM1.D.6 limit-aware
   variant).  Default at v0.31.6+ is `smp_enabled=true
   smp_max_cores=4` per maintainer decision #7 — operators opt out
   via the kernel command line.  A new `scan_boot_rs_phase5_uses_cmdline`
   build-script scanner pins the Phase-5 call sites textually so a
   refactor cannot silently disable the cmdline parse.

   WS-SM Phases SM1.E/F/G/H (v0.31.7) complete the SM1 Rust HAL
   surface required for SM5+ per-core kernel state to land on a
   fully-functional cross-core HAL.  SM1.E adds 8 broadcast TLBI
   wrappers (4 IS-variants `tlbi_*is` for inner-shareable
   broadcast + 4 OS-variants `tlbi_*os` for outer-shareable) plus
   the `tlbi_for_sharing(domain, op)` dispatcher with typed
   `SharingDomain` and `TlbInvalidation` enums; the dispatcher is
   surfaced to Lean via the typed wrapper
   `SeLe4n.Kernel.Architecture.tlbiForSharing` (in
   `TlbiForSharing.lean`) backed by `ffiTlbiForSharing` FFI export.
   SM1.F adds the GICD_SGIR-based SGI primitive surface
   (`gic::send_sgi`, `send_sgi_to_self`, `send_sgi_to_all_but_self`)
   plus the `register_sgi_handler` / `dispatch_sgi` handler-table
   infrastructure; each send-SGI variant emits `dsb ish` BEFORE
   the GICD_SGIR write per ARM ARM B2.7.5, pinned by the
   `scan_gic_rs_send_sgi_emits_dsb_ish` build scanner.  SM1.G
   audits the `UartLock` for SMP correctness (Acquire/Release
   semantics + per-acquire DAIF mask) and adds the
   `kprintln_core!` macro for per-core attributed boot tracing.
   SM1.H wires three QEMU SMP integration tests
   (`test_qemu_smp_bringup.sh` for `-smp 4`,
   `test_qemu_smp_minimal.sh` for `-smp 2`,
   `test_qemu_smp_sgi_roundtrip.sh` for cross-core SGI) into the
   tier-4 nightly slot, replacing the SM0.T SKIP-only stub.

   **WS-SM Phase SM1.I (v0.31.8) closes SM1**.  Six sub-tasks
   complete the miscellaneous HAL improvements that act as
   SM5 landing seams: `trap.rs::handle_irq_per_core` per-core
   IRQ handler entry (reads TPIDR_EL1, records per-core stats,
   dispatches via `gic::dispatch_irq` with per-core attribution
   in the unhandled-INTID log line; SM5 will swap the assembly
   entry vector to this function); per-core IRQ priority masking
   documentation (GICC_PMR per-core banking + DAIF.I per-PE
   scoping); per-core idle-wait primitives at three layers
   (`cpu::idle_wait` / `ffi_idle_wait` / `Concurrency.idleWait`);
   new `per_cpu_stats.rs` module with cache-line aligned
   `PerCpuStats` cohabiting six AtomicU64 counters
   (`irq_count`, `timer_tick_count`, `sgi_count`,
   `syscall_count`, `vmfault_count`, `user_exception_count`)
   wired to the synchronous-exception handler per EC branch;
   SEV / WFE coordination documentation; 8 cross-core test
   scenarios in `smp::tests::sm1i6_*`.  New build-script
   scanner `scan_trap_rs_handle_irq_per_core_intact` pins the
   SM1.I.1 contract.  593 HAL tests at v0.31.8 (510 at SM1.E/F/G/H close + 83 SM1.I including audit-pass refinements at
   v0.31.7).  WS-SM SM1 acceptance gate (per
   `docs/planning/SMP_RUST_HAL_PLAN.md` §8) all items checked.

   **WS-SM Phase SM2.A (v0.31.9) opens SM2** — the **verification-
   quality elevation** that distinguishes seLe4n from seL4: the
   lock primitives themselves are formally specified in Lean
   against an abstract operational semantics of ARMv8.1-A LSE
   atomic operations.  SM2.A is the abstract memory model
   foundation that SM2.B (TicketLock) and SM2.C (RwLock)
   release-acquire pairing proofs consume.  Twelve sub-tasks
   landed in one cut in `SeLe4n/Kernel/Concurrency/MemoryModel.lean`
   (~700 LoC):

   - `MemoryOrder` inductive with 5 constructors mapping to ARM
     ARM B2.3.7 release/acquire semantics (`.relaxed`, `.acquire`,
     `.release`, `.acqRel`, `.seqCst`) and `isAcquire` /
     `isRelease` Bool selectors.
   - `AtomicLocation` struct (single `id : Nat` field) with three
     concrete encoding helpers (`nextTicketOf`, `servingOf`,
     `rwLockStateOf`) reserving slot offsets per lock instance.
   - `MemoryEvent` structure (6 fields capturing the per-event
     observation: which core, which location, isWrite, memory-
     order tag, value, per-core seqNum).
   - `MemoryTrace` structure (event sequence) plus `.empty` seed,
     `.append e` extension, and three structural witnesses.
   - `MemoryTrace.wellFormed` predicate (events Nodup +
     per-core Pairwise seqNum monotonicity) with auto-derived
     `Decidable` instance; `eventPos` (canonical position via
     `List.idxOf`) plus four bridging properties for
     positional reasoning.
   - `synchronizesWith` (9-conjunct relation per ARM ARM B2.3.7
     — both endpoints in trace, release-store + acquire-load,
     same location, observed=released value, positional
     ordering) with two relaxed-rejection witnesses.
   - `sequencedBefore` (4-conjunct relation — both endpoints in
     trace, same core, smaller seqNum); `happensBefore`
     inductive (3 constructors: `.seq`, `.sync`, `.trans`); the
     `happensBefore_in_trace` and
     `happensBefore_strict_positional` foundational lemmas.
   - The four canonical partial-order theorems
     (`happensBefore_irreflexive`, `happensBefore_transitive`,
     `happensBefore_antisymmetric`, aggregate
     `happens_before_partial_order`) plus
     `happens_before_strict_partial_order` (kernel-convenient
     form) and `happensBefore_no_cycle` (smoke-test form).

   **`tests/MemoryModelSuite.lean`** (NEW, ~675 LoC): 64
   surface anchors + 39 decidable examples + 50 runtime
   assertions via `lake exe memory_model_suite`, wired into
   Tier 2 (negative) and Tier 3 (invariant surface).  Module
   reachability: staged via `SeLe4n/Platform/Staged.lean`
   (allowlist entry per WS-RC R12.B partition gate); SM2.B
   (TicketLock) is the first runtime exerciser.

   **Audit-pass refinements** (included in v0.31.9):

   - Non-strict `≤` per-core seqNum monotonicity in `wellFormed`
     (not strict `<` as in the plan pseudocode) to support
     ARMv8.1-A LSE atomic RMW operations.  The plan §3.1.3
     commentary explicitly says RMW ops are modelled as two
     events sharing one `seqNum`; strict `<` would reject all
     RMW traces (including `TicketLock.acquire`'s `next_ticket
     .fetch_add(1, Acquire)`).  Strict ordering for
     `happensBefore.seq` is preserved by the strict `<` in
     `sequencedBefore`, so the partial-order theorems are
     unchanged.
   - Eight helper-theorem lifters added for SM2.B/SM2.C
     consumers: `sequencedBefore_implies_happensBefore`,
     `synchronizesWith_implies_happensBefore`,
     `MemoryTrace.wellFormed.nodup`,
     `MemoryTrace.wellFormed.pairwise`,
     `happensBefore_eventPos_lt`,
     `happensBefore_endpoints_in_trace_with_pos`,
     `MemoryTrace.singleton_wellFormed` (operational-semantics
     base case), `MemoryTrace.wellFormed_append` (inductive
     step that lets SM2.B/C build long well-formed traces from
     per-operation steps via structural fold).

   **Axiom budget for SM2.A**: 0 Lean axioms, 0 sorries.  All
   ARMv8.1-A LSE semantics enter operationally as constraints
   on the trace shape.

2.5. **WS-SM Phase SM2.B (post-v0.31.9) completes SM2.B** — the
   verified TicketLock primitive.  Closes the second sub-phase
   of SM2 ("Verified Lock Primitives") with all 16 sub-tasks
   landed.  See `docs/planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md`
   §5.2 for the full plan.

   **Abstract spec** (`SeLe4n.Kernel.Concurrency.Locks.TicketLock`):
   `TicketLockState` 4-field structure (`nextTicket`, `serving`,
   `pending`, `held`) with `Repr`, `Inhabited`, `DecidableEq`
   derived.  `unheld` canonical seed.  `TicketLockOp`
   3-constructor inductive (`tryAcquire`, `release`,
   `observeServing`).  Operational semantics: `captureTicket`,
   `observeServing`, `applyOp` (with fast-path immediate-promote),
   `promotePending`, `releaseAndPromote`.

   **8-conjunct well-formedness** (improvement over plan's 7):
   INV-T1 (counter monotonicity), INV-T2 (pending tickets in
   `(serving, nextTicket)`), INV-T3 (holder ticket = serving),
   INV-T4 (pending tickets Nodup), INV-T5 (holder ticket not in
   pending), INV-T6 (pending cores Nodup), INV-T7 (holder core
   not in pending), and the new **INV-T8 (count parity)**:
   `nextTicket = serving + |pending| + heldCount`.  The
   7-invariant form admits a non-reachable state
   `(held = some _, serving = nextTicket)` that
   `applyOp .tryAcquire` cannot exit via a wf-preserving step;
   INV-T8 (the natural structural invariant — every issued
   ticket is accounted for by being served, pending, or held)
   closes the gap exactly.  Decidable via `unfold` plus
   `inferInstance`, with Bool-encoded helpers
   (`pendingInRange`, `heldCount`, `holderTicketIsServing`,
   `holderTicketDisjointFromPending`,
   `holderCoreDisjointFromPending`) plus 4 `*_iff` bridge
   theorems for Prop-form use in proofs.

   **6 substantive theorems** (plan §10 catalogue T-01..T-06):
   * `ticketLock_mutex` — at most one holder per state.
     `Option.some` injectivity argument.
   * `ticketLock_wf_invariant` — wf preserved by every kernel-
     facing transition (`tryAcquire`, `releaseAndPromote`,
     `observeServing`).  Aggregates three per-op preservation
     theorems with 4-branch case analyses and 8-invariant
     verification per branch (~530 LoC total proof).
   * `ticketLock_fifo` — `applyOp` is monotone on `nextTicket`.
     `ticketLock_fifo_trace` folds over operation lists.
   * `ticketLock_bounded_wait` — `nextTicket ≤ serving + numCores`
     for any wf state.  Pigeonhole-style: pending cores plus
     optional holder form a Nodup CoreId list ≤ numCores; INV-T8
     gives the structural bound.
   * `ticketLock_release_acquire_pairing` — bridges to SM2.A
     `MemoryModel`.  Given matching events on the `serving`
     location with matching value + positional ordering, the
     events `synchronizesWith` per the abstract memory model.
     Companion `_happensBefore` lifts to happens-before.
   * `ticketLock_reachability` — every state reachable from
     `unheld` via kernel transitions is wf.  Uses a
     `KernelStep` inductive (3 constructors: `acquire` /
     `release` / `observe`; raw `applyOp .release` excluded
     because it doesn't preserve full wf) and `Reachable` (RT
     closure).  Proof by induction citing per-op preservation.

   Plus determinism witnesses (`ticketLock_applyOp_deterministic`,
   `ticketLock_promotePending_deterministic`) and closure-form
   aliases (`ticketLock_acquire_preserves_wf`,
   `ticketLock_release_preserves_wf`) matching kernel-facing
   API names.

   **Rust impl** (`rust/sele4n-hal/src/ticket_lock.rs`):
   structural refinement of the Lean spec.  `TicketLock`
   `#[repr(C, align(64))]` (cache-line aligned), two
   `AtomicU64` fields, three public methods (`acquire`,
   `release`, `with_lock`), RAII `TicketLockGuard<'a>`.
   `next_ticket.fetch_add(1, Acquire)` captures the ticket;
   spin-loop on `serving.load(Acquire)` with `wfe_bounded`
   parks waiters in low-power state.  `release` does
   `serving.fetch_add(1, Release)` followed by `sev` broadcast.
   21 unit tests including panic-safety
   (`with_lock_releases_on_panic`), cross-thread mutex stress
   (4 threads × 1000 ops, no lost updates), cross-thread FIFO
   observation, cache-line alignment, signature pinning,
   100-cycle monotone counter.  Zero clippy warnings.

   **Axiom budget for SM2.B**: 0 Lean axioms, 0 sorries.
   `TicketLock.lean` ~1830 LoC of which ~640 LoC are
   substantive proofs (wf-preservation across all transitions
   plus helper lemmas).

2.6. **WS-SM Phase SM2.C (post-v0.31.9) completes SM2.C** — the
   verified RwLock primitive (reader-writer lock with bit-packed
   atomic state).  Closes the third sub-phase of SM2 with all 22
   sub-tasks landed.  See
   `docs/planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md` §5.3 for
   the full plan.

   **Abstract spec** (`SeLe4n.Kernel.Concurrency.Locks.RwLock`):
   `AccessMode` inductive (`.read` / `.write`).  `RwLockState`
   3-field structure (`writerHeld : Option CoreId`, `readers :
   List CoreId`, `waiters : List (CoreId × AccessMode)`).
   `unheld` canonical seed.  `RwLockOp` 4-constructor inductive
   (`tryAcquireRead`, `releaseRead`, `tryAcquireWrite`,
   `releaseWrite`).  Operational semantics: `applyOp` with a
   uniform `coreInvolved` top-level no-op gate (audit-fixed —
   the plan's pseudocode had three separate "is core already
   involved" checks that missed sub-cases, allowing INV-R4
   violations; the consolidated check covers reader-set / writer-
   held / waiter-list membership in one decidable predicate).
   Promotion helpers: `promoteWaitersOnWriterRelease` (consumes
   contiguous reader prefix via `takeWhile (·.2 = .read)`, or
   the single writer head); `promoteWaitersIfReadersEmpty`
   (same shape, called from `releaseRead` after the reader-
   count drops to zero).

   **5-conjunct well-formedness** (improvement over plan's 4):
   INV-R1 (writer-readers exclusion: writerHeld.isSome → readers
   = []), INV-R2 (readers Nodup), INV-R3 (waiters cores Nodup),
   INV-R4 (waiters disjoint from current holders), and the new
   **INV-R5 (FIFO admission discipline)**: `waiters ≠ [] →
   writerHeld.isSome ∨ readers ≠ []`.  The 4-invariant form
   admits unreachable-but-locally-wf states with non-empty
   waiters and no holders, from which `tryAcquireWrite` could
   produce an INV-R4 violation by acquiring for a core already
   sitting in the waiters queue.  INV-R5 is the RwLock analog
   of SM2.B's INV-T8 — both close reachability gaps.
   Decidable via `unfold` + `inferInstance`, with Bool-encoded
   helpers (`writerReadersExclusion`, `waitersDisjointFromHolders`,
   `fifoAdmissionDiscipline`) plus 3 `*_iff` bridge theorems.

   **10 substantive theorems** (plan §10 catalogue R-01..R-10):
   * `rwLock_writer_readers_exclusion` — INV-R1 in extracted form.
   * `rwLock_reader_multiplicity` — constructive existence
     witness: ∃ s, s.wf ∧ s.readers.length ≥ 2 (built by two
     sequential `tryAcquireRead` ops from `unheld`).
   * `rwLock_fifo_admission` — **substantive structural drop-
     prefix claim** (audit-fixed; the plan's pseudocode would
     have been a trivial tautology).  The theorem states:
     ∃ k, `s.promoteWaitersOnWriterRelease.waiters = s.waiters.drop k`.
     Three cases (empty / writer head / reader head with
     batch-promote) yield k = 0 / 1 / takeWhile-length
     respectively.  Companion `rwLock_fifo_admission_readers_empty`
     for the `releaseRead` promote path.  Corollaries
     `rwLock_promote_subset_of_waiters` and
     `rwLock_promote_preserves_order` derive order preservation.
   * `rwLock_bounded_wait_read` / `rwLock_bounded_wait_write` —
     `readers.length + waiters.length + (writerHeld ? 1 : 0) ≤
     numCores` for any wf state.  Pigeonhole-style: all involved
     cores are distinct (by INV-R2, INV-R3, INV-R4 + Nodup-fst
     witness), so the combined Nodup CoreId list has length ≤
     numCores.  `_write` is currently an alias of `_read` (the
     structural bound is symmetric; a meaningful writer-specific
     bound would require runtime critical-section duration
     hypotheses outside the spec's scope).
   * `rwLock_release_acquire_pairing_read` /
     `rwLock_release_acquire_pairing_write` — bridge to SM2.A
     `MemoryModel`.  Given matching events on the
     `rwLockStateOf base` location with matching value +
     positional ordering, the events `synchronizesWith` per the
     abstract memory model.  Companion `_happensBefore_read`
     lifts to happens-before.
   * `rwLock_wf_invariant` — wf preserved by every kernel-facing
     transition (`tryAcquireRead`, `releaseRead`,
     `tryAcquireWrite`, `releaseWrite`).  Aggregates four
     per-op preservation theorems.  The release-side
     preservation uses a partial-wf intermediate
     (`wfPartial` = 4 invariants without INV-R5) because
     `releaseRead` / `releaseWrite` transiently violate INV-R5
     (readers dropped to zero with non-empty waiters; writerHeld
     cleared with non-empty waiters); the immediately-following
     promote step restores INV-R5.  Helpers
     `rwLock_promoteWaitersIfReadersEmpty_preserves_wf_partial`
     and `rwLock_promoteWaitersOnWriterRelease_preserves_wf_partial`
     take `wfPartial` to full `wf`.
   * `rwLock_reader_batching` + strengthened bounds
     `rwLock_reader_batching_admits_at_least_one`
     (`post.readers.length ≥ s.readers.length + 1`) and
     `rwLock_reader_batching_exact_count`
     (`post.readers.length = takeWhile-length + s.readers.length`)
     — audit-fixed.  The base structural theorem unfolds the
     definition; the strengthened bounds formalise the
     docstring's "many readers admitted at once" claim.
   * `rwLock_writer_safety_under_reader_acquire` — single-step
     safety form (audit-renamed from `no_writer_starvation` for
     honesty; the backwards-compat alias is retained).  Proves
     that a writer in the waiters queue is not displaced by a
     fresh reader's `tryAcquireRead`.  The full liveness claim
     ("writer eventually progresses under bounded reader / writer
     release time") is deferred to post-1.0 temporal reasoning;
     the bounded-wait theorem gives a structural bound on the
     queue size that combined with bounded-critical-section
     assumptions in the runtime is the v1.0.0 substitute.

   Plus determinism witnesses for all three transition functions
   (`rwLock_applyOp_deterministic`,
   `rwLock_promoteWaitersOnWriterRelease_deterministic`,
   `rwLock_promoteWaitersIfReadersEmpty_deterministic`),
   4 closure-form preservation aliases
   (`rwLock_tryAcquireRead_preserves_wf_alias`, etc.) matching
   kernel-facing API names, and bit-packed encoding
   (`encodeRwLock`, `decodeRwLock`, `writerBit = 2^63`,
   `readerMask = writerBit - 1`) with 5 round-trip / writer-bit /
   overflow-bound lemmas
   (`rwLock_encode_decode_roundtrip`,
   `rwLock_decode_encode_roundtrip`,
   `rwLock_encode_writer_bit_set`,
   `rwLock_encode_writer_bit_clear`,
   `rwLock_reader_count_no_overflow_under_numCores`).

   **Refinement bridge** (`SeLe4n.Kernel.Concurrency.Locks.RwLockRefinement`):
   `rwLockSim` relation between abstract `RwLockState` and the
   bit-packed `AtomicU64` `RwLockEncoded`; 5 witness theorems
   (`rwLockSim_unheld`, `rwLockSim_writer_only`,
   `rwLockSim_readers_only`, `rwLockSim_writer_bit_iff`,
   `rwLockSim_reader_count_iff`).  Documents the **FIFO
   divergence**: the Rust CAS-retry impl satisfies the mutex +
   exclusion invariants but not the spec's FIFO admission (no
   explicit waiters queue in the Rust state).  SM3 review
   verifies which kernel paths require strict FIFO.

   **Rust impl** (`rust/sele4n-hal/src/rw_lock.rs`): bit-packed
   `RwLock` `#[repr(C, align(64))]` with one `AtomicU64` `state`
   field.  Public API: `acquire_read` / `release_read` /
   `acquire_write` / `release_write`; RAII guards
   `RwLockReadGuard<'a>` / `RwLockWriteGuard<'a>`;
   `with_read` / `with_write` combinators.  Audit-pass
   release-build hardening: `release_read` uses
   `fetch_sub(1, Release)` (audit fix H-3: prior CAS-retry with
   `count - 1` arithmetic could wrap to u64::MAX in release
   builds, silently corrupting state); `release_write` uses
   `fetch_and(READER_MASK, Release)` (audit fix H-4: prior
   `store(0)` would wipe reader bits on misuse); SEV broadcast
   gated on `prev count = 1` for reader-release (M-3: avoids
   spurious wakeups under heavy reader contention); single-load
   debug asserts (M-7: avoids torn observations).  28 unit
   tests including panic-safety (`with_read/with_write_releases_on_panic`),
   debug-assert misuse detection, cache-line alignment,
   const-fn pinning, and 4 cross-thread stress tests (4-reader
   stress, mixed reader/writer with counter, deterministic
   reader-multiplicity via two-phase Barrier, deterministic
   writer-readers exclusion verifying `rwLock_writer_readers_exclusion`
   at runtime).  Zero clippy warnings.

   **Axiom budget for SM2.C**: 0 Lean axioms, 0 sorries.
   `RwLock.lean` ~2300 LoC; `RwLockRefinement.lean` ~230 LoC.

2.7. **WS-SM Phase SM2.D (post-v0.31.9) completes SM2.D** — the
   FFI bridge and integration layer.  Closes the fourth sub-phase
   of SM2 with all 8 sub-tasks landed.  See
   `docs/planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md` §5.4 for
   the full plan.

   **Lean FFI layer** (`SeLe4n/Platform/FFI.lean` + new
   `SeLe4n/Kernel/Concurrency/LockBridge.lean`):
   - 16 `@[extern]` declarations expose the lock operations
     (`ffiTicketLockStaticHandle`, `ffiTicketLockAcquire`,
     `ffiTicketLockRelease`, `ffiTicketLockPeekHolder`,
     `ffiTicketLockAcquireCount`, `ffiTicketLockReleaseCount`;
     `ffiRwLockStaticHandle`, `ffiRwLockAcquireRead`,
     `ffiRwLockReleaseRead`, `ffiRwLockAcquireWrite`,
     `ffiRwLockReleaseWrite`, `ffiRwLockSnapshot`, plus four
     per-counter trace accessors).
   - Typed handles (`TicketLockHandle`, `RwLockHandle`) carrying
     structural bound proofs (`raw.toNat < staticTicketLockPoolSize`)
     so well-formed callers cannot trip the FFI's fail-closed
     panic.
   - Smart constructors (`mkTicketLockHandle` /
     `mkRwLockHandle`) take a typed `Fin staticTicketLockPoolSize`
     argument; round-trip witness theorems prove `raw.toNat`
     equals the input `Fin.val`.
   - Typed FFI wrappers (`acquireTicketLock`, `releaseTicketLock`,
     `peekTicketLockHolder`, `acquireReadLock`, etc.) wrap the
     raw FFI declarations.
   - RAII combinators (`withTicketLock`, `withReadLock`,
     `withWriteLock`) bracket a `BaseIO α` action with
     acquire/release; three `*_unfold` marker theorems pin the
     definitional unfolding for Tier-3 surface anchoring.
   - 14 `*_eq_ffi` marker theorems prove each typed wrapper is a
     direct FFI pass-through (`rfl`).

   **Rust FFI bridge** (`rust/sele4n-hal/src/lock_bridge.rs`
   ~1170 LoC + 16 exports in `ffi.rs`):
   - Two static lock pools (`STATIC_TICKET_LOCK_POOL: [TicketLock;
     4]`, `STATIC_RW_LOCK_POOL: [RwLock; 4]`) sized to match
     `PlatformBinding.coreCount = 4` so cross-core tests can
     exercise one lock per core.
   - Always-on Relaxed atomic trace counters (6 arrays × 4
     entries) recording acquire/release call counts per slot;
     wait-free, off the correctness path.
   - Fail-closed handle decoders (`decode_ticket_lock_handle` /
     `decode_rw_lock_handle`) — `Option`-returning `const fn`s
     that perform the bound check in `u64` space BEFORE the `as
     usize` cast (audit-pass-1 defense-in-depth narrowing).
   - 16 `#[no_mangle] pub extern "C"` FFI exports forwarding to
     the helpers; panic on malformed handle under
     `panic = "abort"` (fails-closed via clean kernel abort).
   - Public `TicketLock::peek_next_ticket` and `peek_serving`
     methods (audit-pass-1 fix) replace the pre-audit
     raw-pointer cast against `repr(C)` layout.

   **TicketLock refinement bridge** (NEW MODULE
   `SeLe4n/Kernel/Concurrency/Locks/TicketLockRefinement.lean`):
   defines `TicketLockConcrete` struct (two `UInt64` counters)
   mirroring the Rust impl, `ticketLockSim` simulation relation
   (φ : abstract `TicketLockState` ↔ concrete
   `TicketLockConcrete` via `.toNat` on both counters), and four
   per-operation preservation witnesses
   (`ticketLockSim_unheld` initial-state correspondence;
   `ticketLockSim_preserved_by_tryAcquire` /
   `_release` / `_observeServing`).  The F-01 aggregator theorem
   `rust_ticketLock_refines_lean` packages all four witnesses.
   Mirrors the `Locks/RwLockRefinement.lean` structure.

   **SM2.D.7 lockPrimitives aggregator** (NEW MODULE
   `SeLe4n/Kernel/Concurrency/LockPrimitives.lean` ~250 LoC):
   typed `LockPrimitiveTheorem` list aggregating all 22 SM2
   theorems (4 memory-model + 6 TicketLock + 10 RwLock + 2
   refinement) with size + per-category count + NoDup witnesses.
   Cross-language symmetry: the Rust-side
   `SM2_THEOREM_COUNT = 22` constant in `lock_bridge.rs` is
   enforced equal via `scripts/check_lock_ffi_symmetry.sh`
   (wired into Tier 0 hygiene).

   **SM2.D.5 cross-language symmetry**:
   `scripts/check_lock_ffi_symmetry.sh` verifies:
   1. Every expected FFI symbol is declared on the Lean side
      (`@[extern "ffi_*"]`).
   2. Every expected FFI symbol is exported on the Rust side
      (`#[no_mangle] pub extern "C"`).
   3. Every expected FFI symbol has a corresponding helper in
      `lock_bridge.rs`.
   4. The Lean `lockPrimitives_count` value matches the Rust
      `SM2_THEOREM_COUNT` constant.
   5/6. Bidirectional orphan detection (no Rust export without
      a matching Lean declaration; no Lean declaration without
      a matching Rust export).
   Plus two `build.rs` scanners
   (`scan_lock_bridge_rs_intact`,
   `scan_ffi_rs_exposes_lock_ffi_exports`) catch the
   single-file case at elaboration time.

   **Test coverage**: 36 SM2.D Rust tests (24 handle/layout
   decoder + 9 FFI export pass-through + 3 cross-thread
   serialization tests on slot 3); 80+ Lean surface anchors
   in `tests/SmpSurfaceAnchors.lean`; 25+ decidable examples
   plus ~35 runtime structural assertions across
   `tests/LockBridgeSuite.lean` and `tests/SmpSurfaceAnchors.lean`.
   Zero clippy warnings.  Stress-tested 10/10 runs of
   `cargo test sm2d8` without flakiness; 10/10 runs of
   `cargo test sm2d` (full SM2.D set) without flakiness.

   **Audit-pass-1 refinements** (HIGH/MEDIUM/LOW):
   - **HIGH (encapsulation)**: replaced raw-pointer `repr(C)`
     cast with public `TicketLock::peek_*` accessors.
   - **MEDIUM (32-bit truncation defense)**: bound checks in
     `u64` space before `as usize` cast.
   - **MEDIUM (test concurrency)**: unified
     `SM2D_TRACE_TEST_MUTEX` across `lock_bridge::runtime_tests`
     and `crate::ffi::tests` (was: distinct mutex instances
     racing on shared pool slots).
   - **HIGH (refinement-theorem aliasing)**: implemented
     the missing F-01 `rust_ticketLock_refines_lean` theorem
     in NEW MODULE `Locks/TicketLockRefinement.lean` (per
     the implement-the-improvement rule); removed the
     LockPrimitives alias.
   - **LOW (cross-language symmetry)**: bidirectional orphan
     checks added to `check_lock_ffi_symmetry.sh`.

   **Audit-pass-2 refinements**: added 6 missing
   `*Count_eq_ffi` marker theorems for SM2.D.4 trace-counter
   accessors (symmetry with SM2.D.1/2 pass-through markers).

   **Axiom budget for SM2.D**: 0 Lean axioms, 0 sorries.
   `LockBridge.lean` ~552 LoC; `LockPrimitives.lean` ~252 LoC;
   `TicketLockRefinement.lean` ~257 LoC.

   **Items deferred past v1.0.0 with correctness impact**: NONE.

2.8. **WS-SM Phase SM3.A (post-v0.31.9) per-object lock fields** —
   wires SM2.C's abstract `RwLockState` into every kernel-object
   struct that seLe4n models, plus a table-level lock on the
   SystemState's object store, plus the per-variant `objectLockOf`
   projection function and the SM3.A.11 default-state theorems.
   Closes §5.1 of
   `docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md` (11 sub-tasks; 9
   LANDED + 2 documented as N/A for seLe4n's object model).

   **Per-object lock fields**:
   - **SM3.A.1 — TCB.lock**: `lock : RwLockState := RwLockState.unheld`
     in `SeLe4n/Model/Object/Types.lean`.  Manual `BEq TCB` extended
     to compare 23 fields total; `TCB.ext` extensionality lemma
     extended with `hLock` hypothesis.
   - **SM3.A.2 — Endpoint.lock**: per-Endpoint lock with default
     unheld.  Retains derived `DecidableEq`.
   - **SM3.A.3 — CNode.lock**: per-CNode lock with default unheld.
     Manual `BEq CNode` extended; `CNode.beq_sound` rewritten with
     `obtain` for robustness against future BEq additions.
   - **SM3.A.4 — Notification.lock**: per-Notification lock with
     default unheld.  Retains derived `DecidableEq`.
   - **SM3.A.6 — SchedContext.lock**: per-SchedContext lock with
     default unheld in `SeLe4n/Kernel/SchedContext/Types.lean`.
   - **SM3.A.7 — VSpaceRoot.lock**: per-VSpaceRoot lock with
     default unheld in `SeLe4n/Model/Object/Structures.lean`.
     Manual `BEq VSpaceRoot` extended; `VSpaceRoot.beq_sound` and
     `VSpaceRoot.beq_refl` updated for the new conjunct.
   - **SM3.A.9 — UntypedObject.lock**: per-UntypedObject lock with
     default unheld.  Positional `UntypedObject.mk` calls converted
     to named-field syntax for robustness.

   **Skipped sub-tasks (N/A for seLe4n's object model)**:
   - **SM3.A.5 (Reply)**: seLe4n encodes reply discipline through
     TCB state (`blockedOnReply`, `pipBoost`) rather than a
     first-class Reply kernel object.
   - **SM3.A.8 (Page)**: seLe4n stores page mappings inline in
     `VSpaceRoot.mappings`; per-PTE locking is rejected by §4.3
     of the SM3 plan (single per-VSpaceRoot lock suffices for
     serializability).

   **SM3.A.10 — ObjStore table-level lock + objectLockOf projection**:
   - `SystemState.objStoreLock : RwLockState := unheld` field on
     `SystemState` in `SeLe4n/Model/State.lean`.  Per §4.4 of the
     plan, the underlying RobinHood hash table is held under a
     single table-level lock at the top of the SM0.I hierarchy
     (`LockKind.objStore`, level 0).
   - `KernelObject.objectLockOf : KernelObject → RwLockState`
     projection in `SeLe4n/Model/Object/Structures.lean` with 7
     `@[simp]` per-variant unfold lemmas
     (`objectLockOf_tcb`/`endpoint`/`notification`/`cnode`/
     `vspaceRoot`/`untyped`/`schedContext`).  SM3.B `LockId.lookup`
     and SM3.C `lockSetHeld` will consume this projection.
   - Frozen-state mirror: `FrozenSystemState.objStoreLock`,
     `FrozenCNode.lock`, `FrozenVSpaceRoot.lock` fields added;
     `freeze`, `freezeCNode`, `freezeVSpaceRoot` forward the lock
     state unchanged so the per-object lock state is preserved
     across the freeze boundary.

   **SM3.A.11 — Default-state theorems**:
   - `default_objStoreLock_unheld : default.objStoreLock = unheld`
     — proven by `rfl`.
   - `default_objects_locks_unheld` — the canonical SM3.A.11
     closure theorem: for every `id ∈ default.objects`,
     `objectLockOf o = unheld`.  Vacuously discharged via
     `RHTable.getElem?_empty` (default's `objects` is the empty
     hash table).  Base case for the SM3.C `lockSetHeld`
     per-state induction.
   - `default_objects_toList_empty` — computable `decide`-discharged
     witness that the default state's `toList` snapshot is empty.
   - `default_objects_locks_unheld_via_toList` — the `toList`
     membership form, discharged via `List.not_mem_nil`.

   **Production/staged partition updates**:
   `Kernel.Concurrency.Locks.RwLock` and
   `Kernel.Concurrency.MemoryModel` moved from the staged
   allowlist into the production import closure (now reachable via
   `Model.Object.Types`'s new import of
   `Concurrency.Locks.RwLock`).  The `STATUS: staged` markers in
   those files are removed in the same cut per the
   implement-the-improvement rule.  `RwLockRefinement` remains
   staged-only (not yet wired to a runtime consumer).

   **Test coverage**: NEW FILE
   `tests/PerObjectLockSuite.lean` (~646 LoC post-audit-pass-4)
   with 36 surface anchors, 36 decidable examples, and 41
   runtime `assertBool` assertions covering every public SM3.A
   symbol: per-object `lock` fields, `KernelObject.objectLockOf`
   + 7 per-variant `@[simp]` unfolds, `FrozenKernelObject.objectLockOf`
   + 7 per-variant `@[simp]` unfolds (audit-pass-2 M-1, full
   variant runtime coverage at audit-pass-4), four
   `freeze_preserves_*` witness theorems (exercised on every
   variant at audit-pass-4), four SM3.A.11 default-state theorems
   (with 3 non-vacuous post-insert witnesses added at
   audit-pass-4 to give the universal quantifier a non-empty
   exerciser), and `RwLockState.unheld` auxiliary properties.
   Runnable as `lake exe per_object_lock_suite`.  Wired into Tier 2
   (negative) and Tier 3 (invariant-surface) pipelines.

   **Axiom budget for SM3.A**: 0 Lean axioms, 0 sorries.

   **Items deferred past v1.0.0 with correctness impact**: NONE.

2.9. **WS-SM Phase SM3.B (post-SM3.A) LockSet, LockId projection,
   per-transition lockSet declarations, canonical sort theorems** —
   builds the abstract lock-set type and the per-syscall lock-set
   declarations on top of SM3.A's per-object lock fields and SM0.I's
   `LockKind`/`LockId` total order.  Closes §5.2 of
   `docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md` (9 sub-tasks; all
   LANDED).

   **SM3.B.1 — `KernelObject.lockKind` + `LockId.fromObject`**:
   - `KernelObject.lockKind : KernelObject → LockKind` projects the
     SM0.I `LockKind` from a `KernelObject` variant
     (`SeLe4n/Kernel/Concurrency/Locks/LockIdProjection.lean`).  Total
     per-variant case dispatch; 7 `@[simp]` per-variant unfold lemmas
     plus a totality witness (`lockKind_exists`) and an agreement
     theorem with `objectType` (`lockKind_eq_of_objectType`).
   - `LockId.fromObject (oid : ObjId) (o : KernelObject) : LockId`
     pairs an external `ObjId` (the RHTable key) with the object's
     kind.  The plan's pseudocode signature `(o : KernelObject) →
     LockId` is adapted to seLe4n's data model: only `TCB` and
     `SchedContext` carry inner-struct IDs; the other variants are
     looked up by external ObjId in `SystemState.objects`.  Seven
     per-variant `@[simp]` convenience lemmas.

   **SM3.B.2 — `LockId.lookup`**:
   - `LockId.lookup (s : SystemState) (l : LockId) :
     Option (RwLockState × KernelObject)` resolves a LockId against
     a SystemState.  Returns `some (lockState, object)` iff the
     object exists at `l.objId` AND its variant matches `l.kind`;
     `none` otherwise.  The kind-mismatch arm prevents capability-
     confusion errors (e.g. resolving a `.tcb`-tagged LockId at an
     ObjId storing a non-TCB).
   - **AK7-cascade cleanliness**: the dispatcher routes through the
     typed `getX?` accessors (`getTcb?`, `getEndpoint?`, etc.) in
     `Model/State.lean` rather than performing a raw pattern-match
     on the object store directly — this consumes 7 AK7-typed
     accessors and adds zero raw `match ... objects[...]?` sites.
   - Six structural witness theorems: `lookup_some_of_kindMatch`,
     `lookup_fromObject_of_present`, `lookup_objStore`,
     `lookup_reply`, `lookup_page` (the three `@[simp]` fail-closed
     witnesses for the N/A `LockKind` variants), `lookup_kindMatch`,
     and `lookup_lockState_eq`.

   **SM3.B.5..B.8 — `LockSet` + `lockAcquireSequence` + theorems**:
   - `LockSet` structure
     (`SeLe4n/Kernel/Concurrency/Locks/LockSet.lean`) carries
     `pairs : List (LockId × AccessMode)` plus a Nodup-of-keys
     proof `hUniqueKeys`, enforcing plan §3.5's key-uniqueness
     invariant by construction.  Smart constructors `empty`,
     `singleton`, `insert?` (strict; rejects duplicate keys),
     `insertOrMerge` (merges via `AccessMode.lub`), `union`.
   - `AccessMode.lub` (write dominates read; idempotent,
     commutative, associative) and `AccessMode.conflicts`
     (symmetric; read/read is the only non-conflicting pair).
   - `lockAcquireSequence (S : LockSet) :
     List (LockId × AccessMode)` sorts `S.pairs` by `LockId`
     ascending via `List.mergeSort` with the `LockId ≤` comparator.
     Plus the three substantive theorems:
     * `lockAcquireSequence_ordered` (SM3.B.6) — the sort is
       `Pairwise (≤ on fst)` — discharged via
       `List.pairwise_mergeSort` + `LockId.le_trans` +
       `LockId.le_total`.
     * `lockAcquireSequence_complete` (SM3.B.7) — every input pair
       appears in the sorted output (and vice versa).
     * `lockAcquireSequence_canonical` (SM3.B.8, plan §3.5.1) —
       the sorted sequence is the *unique* `≤`-sorted permutation
       of `S.pairs` (uniqueness from key uniqueness +
       antisymmetry).
   - Helper theorem `LockSet.fst_inj_at_pairs` (key uniqueness
     forces pair uniqueness on shared `fst`) and the generic
     `list_fst_inj_of_nodup_keys`.

   **SM3.B.3 — Per-transition `lockSet_<τ>` declarations**:
   25 functions in
   `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean`, one
   per `SyscallId` variant (`lockSet_endpointSend`,
   `lockSet_endpointReceive`, `lockSet_endpointCall`,
   `lockSet_endpointReply`, `lockSet_replyRecv`,
   `lockSet_notificationSignal`, `lockSet_notificationWait`,
   `lockSet_cspaceMint`/`Copy`/`Move`/`Delete`,
   `lockSet_lifecycleRetype`, `lockSet_vspaceMap`/`Unmap`,
   `lockSet_serviceRegister`/`Revoke`/`Query`,
   `lockSet_schedContextConfigure`/`Bind`/`Unbind`,
   `lockSet_tcbSuspend`/`Resume`/`SetPriority`/`SetMCPriority`/
   `SetIPCBuffer`).  Each takes post-cap-resolution `ObjId`s plus
   the caller's `ThreadId` and (where applicable) `Option ObjId`
   arguments for path-dependent locks (e.g.,
   `endpointSend`'s receiver TCB, `tcbSuspend`'s blocked
   endpoint/notification).

   **SM3.B.4 — `permittedKinds` + per-transition consistency**:
   - `permittedKinds (sid : SyscallId) : List LockKind` —
     declarative upper-bound on which `LockKind`s a transition may
     declare.  Per-syscall pattern match with `Decidable` instance.
   - 25 per-transition `lockSet_consistent_<τ>` theorems witness
     that every declared `(l, _) ∈ lockSet_<τ> args` has
     `l.kind ∈ permittedKinds <τ>`.  Discharged through three
     generic builder lemmas (`lockSet_consistent_of_extended_base`,
     `lockSet_consistent_extendOpt`,
     `lockSet_consistent_base_plus_opt`,
     `lockSet_consistent_base_plus_two_opts`) plus per-transition
     `simp only [<lockBuilder>_kind] + decide` discharge of the
     finite kinds-list membership.

   **SM3.B inventory (90 entries after audit-pass-5)**:
   `Concurrency/Locks/LockSetInventory.lean` mirrors SM3.A's
   `PerObjectLockInventory.lean` pattern with a typed
   `LockSetTheorem` struct, a `lkst!` macro that compile-time
   elaborates identifiers, and a 90-entry list partitioned across
   six categories:
   - `.projection` (22 entries): `KernelObject.lockKind` + 7
     per-variant simp lemmas + `lockKind_eq_of_objectType` + 4
     `lockKind_*` co-domain theorems (audit-pass-2) +
     `LockId.fromObject` + `LockId.lookup` + 4 lookup structural
     theorems + 3 N/A-kind fail-closed witnesses (audit-pass-1).
   - `.lockSet` (25 entries): one per `lockSet_<τ>`.
   - `.consistency` (25 entries): one per `lockSet_consistent_<τ>`.
   - `.acquireSort` (6 entries): `lockAcquireSequence` + three
     theorems + length + perm.
   - `.algebra` (9 entries): `AccessMode.lub` properties +
     `LockSet.insertOrMerge_mem` + `lockSetOfList_mem_inv` +
     `LockSet.fst_inj_at_pairs` + `LockSet.union_mem_inv`
     (audit-pass-1) + `LockSet.containsKey_iff` (audit-pass-2).
   - `.chainStart` (3 entries, NEW at audit-pass-5):
     `pipChainStart_endpointCall`/`endpointReply`/`replyRecv` —
     structural signal to SM3.C that a transition invokes a
     dynamic PIP chain walk whose length is state-discovered.

   Plus per-category count witnesses, partition-sum theorem,
   Nodup-on-identifiers and Nodup-on-descriptions witnesses
   (discharged via `native_decide` due to list size), and a
   coverage theorem `lockSet_consistent_aggregate_covers_every_syscall`
   pinning `consistency category count = SyscallId.count`.

   **Production/staged partition**: all five SM3.B modules
   (`LockSet`, `LockIdProjection`, `LockSetTransitions`,
   `LockSetInventory`, and the `LockSet` re-export hub) staged via
   `Platform/Staged.lean`.  SM3.C's `withLockSet` 2PL combinator
   will promote them to production-reachable.

   **Test coverage** (audit-pass-1+2): NEW FILE
   `tests/LockSetSuite.lean` (~1000 LoC) with 110+ surface
   anchors for every public SM3.B symbol, decidable examples on
   small concrete LockSets exercising sort ordering and
   per-transition shape, and 83 runtime `assertBool` assertions
   across 15 sections (§1 empty/singleton, §2 acquire sort, §3
   AccessMode algebra, §4 permitted kinds, §5 lockKind helpers,
   §6 LockId projection, §7 per-transition shapes, §8 inventory
   aggregator, §9 lub-merging on duplicate keys, §10
   LockSet.union semantics, §11 runtime exercise of
   `lockSet_consistent_*` on concrete args, §12 canonical-sort
   determinism across insertion orders, §13 `LockId.lookup` on
   non-default fixture state including kind-mismatch fail-closed
   branches, §14 lockKind co-domain audit-pass-2 — verifies
   lockKind never returns `.objStore`/`.reply`/`.page`, §15
   `LockSet.fst_inj_at_pairs` structural witness).  Runnable as
   `lake exe lock_set_suite`.  Wired into Tier 2 (negative) and
   Tier 3 (invariant-surface) pipelines.

   **Axiom budget for SM3.B**: 0 Lean axioms, 0 sorries.

   **Items deferred past v1.0.0 with correctness impact**: NONE.

   **Audit-pass-1 refinements** (comprehensive deep audit;
   land in the same v0.31.9 release cut):

   * **Code-quality cleanup**: removed no-op `simp only at h` in
     `DecidableEq LockSet`, replaced `simp_all` workaround in
     `containsKey_iff`, dropped unused `_hSortedRef` parameter
     from `lockAcquireSequence_canonical_aux`.
   * **Proof-style refactor**: replaced 76 repeated `simp only
     [tcbLock_kind, ..., untypedLock_kind]; decide` across the
     25 `lockSet_consistent_*` theorems with clean `simp; decide`
     (the `*Lock_kind` lemmas are `@[simp]` globally); removed
     the `set_option linter.unusedSimpArgs false` workaround.
   * **Module-layering fix**: moved `LockSet.insertOrMerge_mem`
     from `LockSetTransitions.lean` to `LockSet.lean` (the
     defining module).
   * **Spec-gap closure**: added `LockSet.union_mem_inv` — the
     structural characterisation theorem for `LockSet.union`'s
     semantics that was missing from the initial landing.
   * **Inventory expansion**: 72 → 81 entries (+8 projection: 4
     lookup structural theorems + 3 N/A-kind fail-closed witnesses
     + `lockKind_eq_of_objectType`; +1 algebra: `union_mem_inv`).
   * **Test-coverage gap closures**: 5 new runtime check sections
     (§9..§13), +27 runtime assertions over the initial landing.

   **Audit-pass-2 refinements** (second deeper deep audit;
   land in the same v0.31.9 release cut):

   * **Code-quality cleanup**: removed duplicate theorem
     `fromObject_lockKind_eq` (literally identical to
     `fromObject_kind`); removed unused `[DecidableEq α]`
     constraint from `list_fst_inj_of_nodup_keys` (proof never
     invokes decidability of equality).
   * **Substantive co-domain theorems**: `KernelObject.lockKind_exists`
     is genuinely trivial; audit-pass-2 adds 4 useful co-domain
     theorems: `lockKind_in_modeledKinds`, `lockKind_ne_objStore`,
     `lockKind_ne_reply`, `lockKind_ne_page`.  These tell SM3.C
     consumers that a `KernelObject`-derived `LockId` will never
     refer to a SystemState-level or N/A kind.
   * **Donation-path scope** (initial audit-pass-2 form was
     documentation-only; **REPLACED by audit-pass-3 below** per
     CLAUDE.md's `Implement-the-improvement` rule).
   * **Inventory expansion** (audit-pass-2): 81 → 87 entries (+4
     projection: 4 `lockKind_*` co-domain theorems; +1
     acquireSort: `lockAcquireSequence_perm`; +1 algebra:
     `LockSet.containsKey_iff`).
   * **Test-coverage gap closures**: 2 new runtime check sections
     (§14 lockKind co-domain, §15 fst_inj structural witness),
     +11 runtime assertions (72 → 83).

   **Audit-pass-4 refinements** (deepest deep audit; closes one
   remaining defense-in-depth gap in audit-pass-3's donation fix
   and acknowledges PIP-chain dynamic locking; land in the same
   v0.31.9 release cut):

   * **`originalOwner` separated for defense-in-depth**:
     audit-pass-3's `lockSet_endpointReply` and
     `lockSet_replyRecv` assumed the well-formed invariant
     `originalOwner == replyTargetTid` and only declared a
     single Option for the donation SC.  Audit-pass-4 declares
     the originalOwner TCB lock as a SEPARATE
     `donatedOriginalOwnerTid : Option ThreadId` arg (per plan
     §4.1's "union over all paths" requirement).  Under the
     invariant, lub-merge collapses the duplicate entry — same
     behavior as before.  Under hypothetical invariant
     violation, both objects are correctly locked.  This makes
     the reply paths symmetric with `lockSet_tcbSuspend`.

   * **PIP-chain dynamic-locking acknowledged**: traced
     `endpointCallWithDonation` /
     `endpointReplyWithDonation` through
     `propagatePriorityInheritance` /
     `revertPriorityInheritance`.  These walk arbitrarily-long
     blocking-graph chains, touching TCB `pipBoost` fields.
     Chain length is state-discovered, not statically
     pre-resolvable.  Plan §4.1's "variable number of locks"
     provision applies — SM3.C will handle PIP locks via
     dynamic ladder extension preserving the SM0.I lock-id
     total order's deadlock-freedom.  This is the
     genuinely-dynamic case explicitly permitted by the plan.

   * **Test-coverage expansion**: 95 → 96 runtime assertions
     (+1 for the invariant-drift defense-in-depth assertion).

   **Audit-pass-5 refinements** (structural PIP-chain
   obligation encoded at the type level; implements the chain-
   start signal audit-pass-4 only acknowledged as a doc note,
   per CLAUDE.md's `Implement-the-improvement` rule; land in
   the same v0.31.9 release cut):

   * **3 new `pipChainStart_<τ>` declarations** for the 3
     PIP-invoking transitions:
     - `pipChainStart_endpointCall` — mirrors `receiverTid`
       (no waiting receiver ⇒ no chain).
     - `pipChainStart_endpointReply` — always emits revertPIP
       at `callerTid`.
     - `pipChainStart_replyRecv` — always emits revertPIP at
       `callerTid`.
     Each returns `Option ThreadId` exposing the chain start
     point as structural metadata about the transition (a
     "follow this dynamic obligation" signal), not a lockSet
     element.  Defense-in-depth: the chain-start TCB is
     contained in the static lockSet (verified by 2 runtime
     assertions).
   * **Structural separation from `lockSet_<τ>`**: Plan §4.1's
     `lockSet : args → Finset` signature is preserved unchanged.
     The chain-start hint is separate, surfacing the dynamic
     obligation explicitly at the type level — SM3.C cannot
     forget to handle the chain.
   * **New SM3.C.11 sub-task** in
     `docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md` §5.3
     covering the dynamic chain-walk locking design:
     `withDynamicChainExtension` combinator (optimistic walk +
     verify, `ObjId.val` ascending discipline, bounded
     retries), `dynamicChainHeld` predicate,
     `dynamic_chain_deadlock_free` theorem,
     `walkAndAcquire_terminates` theorem, per-transition
     wrappers, and 6 sub-sub-tasks (SM3.C.11.a..f).  SM3.C
     lifts from 4 PRs / 10 sub-tasks to 5 PRs / 11 sub-tasks.
   * **Inventory expansion**: 87 → 90 entries (+3 in the NEW
     `chainStart` category).  `lockSetTheorems_chainStart_count
     = 3` new witness; partition-sum updated to 6-way.
   * **Test-coverage expansion**: 96 → 106 runtime assertions
     (+10 = +9 §16 `runPipChainStartChecks` + 1 inventory
     chainStart check).  3 new surface anchors + 6 new
     decidable examples + 4 new tier-3 surface anchors.

   **Audit-pass-6 refinements** (external Codex code-review
   closure on PR #793; 4 P1 high-severity + 1 P2 medium-severity
   lock-set under-approximations resolved by re-tracing the
   actual kernel operations and extending the static lock-set
   declarations; land in the same v0.31.9 release cut):

   * **P1 — `lockSet_tcbSetPriority`**: gains
     `boundSchedContextId : Option SchedContextId` arg.
     `setPriorityOp` → `updatePrioritySource` writes the bound
     SC's `priority` field when the target's binding is
     `.bound`/`.donated`.
   * **P1 — `lockSet_tcbSetMCPriority`**: gains
     `boundSchedContextId : Option SchedContextId` arg.
     `setMCPriorityOp` calls `updatePrioritySource` in the
     priority-capping branch.
   * **P1 — `lockSet_tcbSetIPCBuffer`**: gains
     `targetVSpaceRootObjId : Option ObjId` arg.
     `setIPCBufferOp` → `validateIpcBufferAddress` reads the
     target's VSpaceRoot and traverses its mappings.
   * **P2 — `lockSet_serviceRegister`**: gains a mandatory
     `endpointObjId : ObjId` arg.  `registerService` reads
     `st.objects[epId]?` to verify endpoint kind.
   * **`permittedKinds` extensions**: `.tcbSetPriority` /
     `.tcbSetMCPriority` add `.schedContext`;
     `.tcbSetIPCBuffer` adds `.vspaceRoot`; `.serviceRegister`
     adds `.endpoint`.  `.serviceRevoke` / `.serviceQuery`
     split out unchanged.
   * **Consistency proofs**: `_tcbSetPriority` /
     `_tcbSetMCPriority` / `_tcbSetIPCBuffer` use
     `lockSet_consistent_base_plus_opt` (Option discharge
     pattern from audit-pass-3); `_serviceRegister` gains a
     3rd literal-list rcases branch.
   * **Test-coverage expansion**: 106 → 133 runtime assertions
     (+27).  NEW §17 `runAuditPass6FootprintChecks` (+10).
     Plus +6 §4, +7 §7, +4 §11.

   **Audit-pass-3 refinements** (donation-path FIX implementing
   the improvement audit-pass-2 only documented; land in the
   same v0.31.9 release cut):

   * **Donation-path lockSet extensions**: per plan §4.1's
     "union over all paths" requirement, 4 syscalls now have
     pre-resolved `Option` args covering the donation
     footprint:
     - `lockSet_endpointCall` gains `donatedScId : Option
       SchedContextId` for `applyCallDonation`'s SC update.
     - `lockSet_endpointReply` gains `donatedScId : Option
       SchedContextId` for `applyReplyDonation`'s SC return
       (original-owner TCB == `replyTargetTid` already in
       lockSet, so only the SC is new).
     - `lockSet_replyRecv` gains `donatedScId : Option
       SchedContextId` (same as reply).
     - `lockSet_tcbSuspend` gains TWO new Options: `bindingScId
       : Option SchedContextId` AND `donatedOriginalOwnerTid :
       Option ThreadId` for `cancelDonation`'s `.bound`/`.donated`
       arms.
   * **Source-level tracing**: each extension verified against
     the actual kernel code (`donateSchedContext`,
     `returnDonatedSchedContext`, `cancelDonation` dispatch
     arms) to ensure the lockSets declare exactly the set of
     objects the underlying transition writes.
   * **`permittedKinds` extensions**: `.call`, `.reply`,
     `.replyRecv`, `.tcbSuspend` all gain `.schedContext`.
   * **New consistency-proof builders**:
     `lockSet_consistent_base_plus_three_opts` (for `replyRecv`)
     and `lockSet_consistent_base_plus_four_opts` (for
     `tcbSuspend`).
   * **Test-coverage expansion**: 83 → 95 runtime assertions
     (+12 for new donation-shape, donation-consistency-runtime,
     extended permittedKinds, and donation-aware acquireSort
     checks).

2.10. **WS-SM Phase SM3.C (post-SM3.B) two-phase-locking discipline,
   `lockSetHeld` predicate, dynamic PIP chain-walk locking** — closes
   §5.3 of the per-object-locks plan (11 sub-tasks; 10 LANDED, SM3.C.9
   deferred to SM5+).  Wires SM3.B's per-transition `lockSet`
   declarations into the verified 2PL combinator that SM3.D
   (deadlock-freedom) and SM3.E (serializability) build on.

   **SM3.C.1 — `withLockSet` 2PL combinator**:
   `withLockSet (S : LockSet) (core : CoreId) (action : SystemState →
   SystemState × α) (s : SystemState) : SystemState × α` acquires
   every lock in `S.lockAcquireSequence` (LockId ascending), runs
   `action`, then releases in reverse order.  Pure-function form (not
   `BaseIO`) because the abstract model tracks lock state as a pure
   `RwLockState` field-update; the BaseIO/FFI overload is deferred to
   SM5+.  `acquireAll` / `releaseAll` are the fold helpers; the
   `withLockSet_empty` / `_unfold` / `_fst` / `_snd` lemmas expose the
   three-phase decomposition.

   **SM3.C.2 — `acquireLockOnObject` / `releaseLockOnObject`**:
   per-object lock primitives dispatching on `l.kind`.  The
   `.objStore` arm advances `SystemState.objStoreLock`; the modeled
   kinds route through `updateObjectAt` + `KernelObject.updateLock`
   (which advances the inner per-object `RwLockState` via
   `RwLockState.applyOp`); the `.reply`/`.page` arms are no-ops
   (SM3.A.5/A.8 N/A).  `updateLock` carries 7 `@[simp]` per-variant
   unfolds plus `updateLock_preserves_lockKind` /
   `updateLock_preserves_objectType` / `objectLockOf_updateLock`.

   **SM3.C.3 — RAII discipline**: the abstract `withLockSet` is a
   total pure function with no panic paths, so the release fold
   *always* runs after the action (it is the next step in the total
   fold, not conditional on a success flag).  The Rust-side
   `panic = "abort"` discipline (SM2.D) covers the hardware panic
   case.

   **SM3.C.4 — `lockSetHeld` predicate** (SMP-migration precondition
   for Corollary 2.1.11): `lockSetHeld (c : CoreId) (S : LockSet)
   (s : SystemState) : Prop` witnesses that core `c` holds every lock
   in `S` on `s`.  Dispatches per-lock via `lockHeld` (routing
   modeled kinds through `LockId.lookup`, the `.objStore` arm through
   `s.objStoreLock`, failing closed on `.reply`/`.page`).  Decidable;
   `lockSetHeld_default_iff_empty` witnesses that a freshly-booted
   system holds no locks.

   **SM3.C.5 / SM3.C.6 — ordering theorems**:
   `lockSet_acquired_in_order` (the acquire order is `LockId`
   ascending, lifting SM3.B.6's `lockAcquireSequence_ordered`) and
   `lockSet_released_in_reverse` (the release order is descending).

   **SM3.C.7 — `lockSet_atomic_under_2pl`** (Theorem 2.1.10
   operational form): the `withLockSet` result is the action's
   output on the post-acquire state, composed with the release fold —
   no external observer can interleave with the action phase.

   **SM3.C.8 — `lockSet_invariant_preserved`** (Corollary 2.1.11):
   the *substantive* metatheorem (not a tautology).  Proves by
   induction on the canonical acquisition sequence that the acquire
   fold preserves any lock-insensitive invariant.  The lock-
   insensitivity hypothesis is discharged structurally for the
   kind-discipline invariant class by the foundation lemmas
   `acquireLockOnObject_preserves_objStoreLock_of_modeled`,
   `releaseLockOnObject_preserves_objStoreLock_of_modeled`, and
   `updateObjectAt_preserves_objectType_at` (which threads the
   RHTable extension invariant through `getElem?_insert_self` /
   `getElem?_insert_ne` to show the kind tag at every key is
   preserved).  `withLockSet_invariant_preserved` composes the
   acquire-fold + action + release-fold preservation into the full
   closure that SM4..SM6 phase migrations consume.

   **SM3.C.9 — `@[export]` body migration**: DEFERRED to SM5+.  At
   SM3.C the kernel is modelled single-core, so wrapping each
   `@[export]` body in `withLockSet` would be a no-op on the current
   abstract model.  The migration lands with SM5's per-core scheduler
   integration, which is when the wrappers become semantically
   active.

   **SM3.C.11 — dynamic PIP chain-walk locking**: the 3 PIP-invoking
   transitions (`.call`/`.reply`/`.replyRecv`) walk a blocking chain
   whose length is state-discovered, so no static lockSet can contain
   the chain TCBs.  `withDynamicChainExtension` consumes the SM3.B
   `pipChainStart_<τ>` signal and walks the chain via `walkAndAcquire`
   (a fuel-bounded — `MAX_PIP_RETRIES = 64` — pure function returning a
   `WalkOutcome`).  The deadlock-freedom witness
   `walkAndAcquire_path_ascending_in_ObjId_if_terminated` proves that
   any terminating walk produces a path whose `ObjId.val`s are
   strictly ascending — the SM0.I total-order discipline that closes
   any potential wait-cycle (two cores walking different chains
   cannot deadlock because each only ever holds locks at strictly
   ascending `ObjId.val`).  `dynamicChainHeld` is the 4-conjunct
   chain-held predicate (write-locks held + ObjId-ascending +
   path-starts-at-start + path-follows-blockingServer).

   **SM3.C inventory (71 entries)**: `withLockSetTheorems` in
   `WithLockSetInventory.lean` aggregates the SM3.C theorems across 5
   categories (`.combinator` = 31, `.held` = 11, `.ordering` = 3,
   `.atomicity` = 9, `.dynamicChain` = 17) with a compile-time-checked
   `wlst!` macro, per-category count witnesses, partition-sum, and
   Nodup-on-identifiers / Nodup-on-descriptions.

   **Files**: `WithLockSet.lean` (~540 LoC), `LockSetHeld.lean`
   (~330 LoC), `LockSet2PL.lean` (~290 LoC),
   `DynamicChainExtension.lean` (~560 LoC), `WithLockSetInventory.lean`
   (~290 LoC), all under
   `SeLe4n/Kernel/Concurrency/Locks/`.  Staged via the LockSet
   re-export hub; SM5+ per-core scheduler integration is the first
   production runtime exerciser.

   **Test coverage**: `tests/WithLockSetSuite.lean` (~430 LoC) — 70+
   surface anchors, 12 decidable examples, 52 runtime `assertBool`
   assertions (runnable as `lake exe with_lock_set_suite`).  Tier-2
   (negative) + Tier-3 (invariant surface) wired.

   **AK7-cascade cleanliness**: the `withLockSet` / `lockSetHeld`
   definitions route through the `RHTable.get?` method form and the
   generic `default_objects_get?_none` helper rather than the bare
   `match s.objects[…]?` bracket idiom and the `.toObjId]?` boundary
   idiom; the cumulative `RAW_MATCH_TOTAL` floor stays at the v0.31.2
   baseline (122) and `RAW_LOOKUP_TID` drops from 759 to 757.

   **Axiom budget for SM3.C**: 0 Lean axioms, 0 sorries.  Every
   theorem depends only on the standard Lean foundational axioms
   (`propext`, `Quot.sound`, `Classical.choice`).

   **Group-B deferred-gap closure** (post-landing audit): the gaps
   provable within SM3.C's abstract scope (i.e. not gated on the SM5+
   per-core FFI seam) are closed.  SM3.C.7 gains the observational-
   atomicity theorems (`AcquireInsensitive` / `ReleaseInsensitive`
   observer predicates, `acquireAll_lockInsensitive` /
   `releaseAll_lockInsensitive`, `withLockSet_release_invisible`, and
   the `lockSet_observer_atomic` capstone) — a lock-insensitive observer
   sees exactly the action's effect, the 2PL machinery invisible.
   SM3.C.8 gains the *establishment* lemmas
   (`acquireLockOnObject_establishes_lockHeld_modeled`, the multi-lock
   `acquireAll_establishes_lockHeld_of_distinct_present_unheld`, and the
   `LockSet`-level `acquireAll_establishes_lockSetHeld` with automatic
   ObjId-distinctness from `Nodup` keys + state resolution) — the
   growing phase genuinely establishes the `lockSetHeld` precondition.
   SM3.C.11.c gains conjunct-1 establishment
   (`chainLockSeq_acquire_establishes_pathHeld`) + the `blockingServer`
   transport + the full-four-conjunct capstone
   `withDynamicChainExtension_establishes_dynamicChainHeld`.  SM3.C.11.d
   gains the two-core deadlock-freedom theorems
   (`dynamic_chain_deadlock_free` / `dynamic_chain_no_mutual_wait`).
   Tests gain RAII-release, populated-state establishment,
   observer-atomicity, and a real 3-TCB multi-step blocking chain
   (`5 → 7 → 10`).  Inventory grows 71 → 86; all new theorems
   axiom-clean.

   **Items deferred past v1.0.0 with correctness impact**: NONE
   (SM3.C.9, plus the C.1/C.2 FFI overloads and the SM3.C.11.b
   per-transition wrapper, are sequencing deferrals to the SM5 per-core
   FFI seam, not correctness gaps).

3. **Sequential memory model**: Under single-core operation, all memory
   operations are sequentially ordered. DMB/DSB/ISB barriers are emitted in the
   Rust HAL (`sele4n-hal/src/cpu.rs`) for hardware correctness but are
   semantically no-ops in the Lean model. The `BarrierKind` type and
   `barrierOrdered` theorems in `MmioAdapter.lean` (AG8-C) are trivially
   satisfied under the sequential model.

4. **No multi-core invariants**: The `crossSubsystemInvariant` (12 predicates)
   and `proofLayerInvariantBundle` (11 conjuncts) are formulated for single-core
   state. Multi-core extensions would require per-core state partitioning and
   cross-core invariant composition.

### 6.5 Hardware Binding Architecture (AG10-D)

The H3 hardware binding is structured as a layered architecture bridging the
abstract Lean kernel model to concrete ARM64 hardware:

```
┌──────────────────────────────────────────────────────────┐
│  Lean Kernel Model (pure functions, machine-checked)     │
│  - Transitions: SeLe4n/Kernel/API.lean (25 syscalls)     │
│  - Invariants: cross-subsystem, IPC, scheduler, etc.     │
├──────────────────────────────────────────────────────────┤
│  FFI Bridge (@[extern] declarations)                     │
│  - SeLe4n/Platform/FFI.lean (17 Rust HAL functions)      │
│  - C calling convention, Lean ↔ Rust type mapping        │
├──────────────────────────────────────────────────────────┤
│  Rust HAL (sele4n-hal crate)                             │
│  - ARM64 instructions (WFE/WFI/NOP/ERET, barriers)      │
│  - System registers (MRS/MSR for SCTLR, TCR, MAIR, etc.)│
│  - PL011 UART, GIC-400, ARM Generic Timer               │
│  - MMU, exception vectors, trap entry/exit               │
├──────────────────────────────────────────────────────────┤
│  Hardware (Raspberry Pi 5 / BCM2712 / Cortex-A76)        │
└──────────────────────────────────────────────────────────┘
```

#### 6.5.1 Exception Handling

The ARM64 exception model (`SeLe4n/Kernel/Architecture/ExceptionModel.lean`,
AG3-C) defines the hardware exception dispatch path:

- **Exception types**: Synchronous (SVC, data abort, instruction abort,
  alignment fault), IRQ, FIQ (unsupported), SError (hardware fault)
- **ESR_EL1 classification**: The Exception Syndrome Register EC field
  (bits [31:26]) routes synchronous exceptions to handlers
- **SVC dispatch**: SVC instructions from EL0 enter `dispatchException` which
  classifies the exception and routes to `syscallEntry`
- **Exception levels**: EL0 (user) ↔ EL1 (kernel) transitions are modeled
  with `exceptionEntry_setsEL1` and `exceptionReturn_restoresEL0` proofs
- **Atomicity**: 8 preservation theorems prove kernel state consistency across
  exception and interrupt boundaries (context save/restore, thread selection,
  dispatch, scheduling, timer tick, and interrupt handling)

The Rust HAL implements the exception vector table (`sele4n-hal/src/vectors.S`)
with 16 entries (4 types × 4 execution states) and a trap frame
(`sele4n-hal/src/trap.rs`) that saves/restores all 31 general-purpose registers
plus SP_EL0, ELR_EL1, SPSR_EL1, ESR_EL1, and FAR_EL1 (288-byte `TrapFrame`;
16-byte aligned).

**AK5-F (v0.29.8)**: The TrapFrame grew from 272 → 288 bytes to include
read-only snapshots of `ESR_EL1` (offset 272) and `FAR_EL1` (offset 280).
`handle_synchronous_exception` reads these from the frame, not the live
registers — nested exceptions (SError during data-abort handling, etc.)
would otherwise mutate the live registers before the outer handler
inspected them. Compile-time `offset_of!` asserts in `trap.rs` lock the
layout; the Lean-side `trapFrameLayout` in `ExceptionModel.lean`
(`TrapFrameLayout` structure) documents the binary contract.

**AI1-A/AI1-B (v0.27.7)**: The Rust exception handler error codes match the
Lean model exactly. Alignment faults (`PC_ALIGN`, `SP_ALIGN`) and unknown
exceptions return discriminant 45 (`UserException`), matching
`ExceptionModel.lean:175-177`. The SVC handler now substantively dispatches
to `Kernel.syscallEntryChecked` via the FFI bridge — see §6.5.5 below.
Named constants in `trap.rs`
(`error_code::VM_FAULT`, `USER_EXCEPTION`, `NOT_IMPLEMENTED`) replace bare
numeric literals for cross-reference clarity.

**WS-RC R2 (v0.30.11)**: the FFI bridge that the audit tracked under
`DEF-R-HAL-L14` in `AUDIT_v0.29.0_DEFERRED.md` is now substantively
wired.  `@[export syscall_dispatch_inner]` (`SeLe4n/Platform/FFI.lean`)
reads the live `SystemState` from `kernelStateRef`, spills the FFI
register values into the current TCB via `writeFfiRegistersToTcb`,
invokes the verified `Kernel.syscallEntryChecked`, encodes the result
into the bit-63 error-flag UInt64 contract, and writes the post-state
back to the IO.Ref.  `@[export suspend_thread_inner]` is the analogous
substantive bridge into `Kernel.Lifecycle.Suspend.suspendThread`.  The
`NotImplemented = 17` discriminant is no longer emitted by either
bridge on any non-error code path — every error now corresponds to a
substantive kernel rejection.

#### 6.5.0 Panic Discipline (AK5-A)

**Added in v0.29.8**: the `rust/Cargo.toml` workspace manifest sets
`panic = "abort"` for both `[profile.dev]` and `[profile.release]`.
The default `panic = "unwind"` is undefined behavior across `extern "C"`
boundaries and requires a landing-pad implementation the bare-metal HAL
does not provide. Under `panic = "abort"`:

- A panic in any Rust HAL function calls the platform abort handler
  (which the kernel implements as an infinite `wfe` loop via
  `cpu::wfe()`), stopping the kernel deterministically. This is the
  correct behavior for invariant violations — halting is safer than
  continuing with corrupted state.
- The `EoiGuard` introduced in AK5-B relies on this discipline to
  guarantee that the GIC end-of-interrupt fires even when a handler
  panics: the compiler inserts the `Drop` call on the unwinding /
  aborting scope exit before control reaches the abort handler.
- `ffi.rs` carries a `#[cfg(all(not(panic = "abort")), not(debug_assertions))]
  compile_error!` guard so a future maintainer cannot accidentally
  re-enable unwinding on a release build.

The `[profile.test]` panic setting is intentionally omitted: Rust's
stable test harness requires unwind semantics for `#[should_panic]` tests
(the MMIO alignment and UART baud=0 regression tests use this).
`cargo test` therefore compiles every crate with unwind, while
`cargo build` / `cargo build --release` uses abort.

#### 6.5.2 Interrupt Dispatch

The GIC-400 interrupt dispatch model
(`SeLe4n/Kernel/Architecture/InterruptDispatch.lean`, AG3-D) implements the
acknowledge → dispatch → EOI sequence:

- **Acknowledge**: Read GICC_IAR to get the INTID; spurious INTIDs (≥ 1020)
  are dropped
- **Dispatch**: Timer PPI (INTID 30) → `timerTick`; mapped SPIs → endpoint
  `notificationSignal`; unmapped → error
- **EOI**: Write GICC_EOIR to signal completion (no-op in abstract model)
- **INTID space**: SGIs (0–15), PPIs (16–31), SPIs (32–223) for BCM2712

The `handleInterrupt` operation is the 35th `KernelOperation` constructor
with a corresponding non-interference step in the information flow model.

The Rust GIC-400 driver (`sele4n-hal/src/gic.rs`) initializes the distributor
(GICD_CTLR, IGROUPR, IPRIORITYR, ITARGETSR, ICPENDR, ISENABLER) and CPU
interface (GICC_PMR, BPR, CTLR), with a generic `dispatch_irq<F>()` handler.

#### 6.5.3 Timer Binding

The hardware timer model (`SeLe4n/Kernel/Architecture/TimerModel.lean`, AG3-E)
bridges abstract timer ticks to the ARM Generic Timer:

- **Hardware registers**: CNTPCT_EL0 (54 MHz physical counter), CNTP_CVAL_EL0
  (comparator), CNTFRQ_EL0 (frequency)
- **Mapping**: One model `timerTick` = one timer interrupt event (counter ≥
  comparator). At 1000 Hz tick rate: 54,000 counter increments per tick
- **Monotonicity**: `hardwareTimerToModelTick_monotone` proves the hardware-to-
  model conversion is monotonically non-decreasing
- **`TimerInterruptBinding`**: Structure capturing the bidirectional relationship
  between hardware timer events and model timer ticks

The Rust timer driver (`sele4n-hal/src/timer.rs`) uses system register
accessors and counter-relative reprogramming for evenly-spaced interrupts.

**AI1-C (v0.27.7)**: The timer tick accounting path has been unified. The IRQ
handler (`trap.rs::handle_irq`) only re-arms the hardware timer via
`reprogram_timer()`. Tick counting is performed exclusively by
`ffi_timer_reprogram()` (`ffi.rs`), which the Lean kernel controls. This
eliminates the M-26 dual-path bug where both the IRQ handler and FFI bridge
incremented the tick count, causing double-counting on hardware.

#### 6.5.4 Memory Management (ARMv8)

The ARMv8 page table model (`SeLe4n/Kernel/Architecture/PageTable.lean`, AG6)
provides a formal model of the 4-level translation table structure:

- **Page table levels**: L0 (512 GB regions) → L1 (1 GB) → L2 (2 MB) → L3
  (4 KB pages). 48-bit VA space, 4 KB granule
- **Descriptor types**: Invalid, Block (L1/L2 huge pages), Table (next-level
  pointer), Page (L3 leaf entry)
- **Attributes**: `PageAttributes` captures access permissions (RW/RO/None,
  user/kernel), shareability (Non/Inner/Outer), and the access flag
- **W^X enforcement**: `hwDescriptor_wxCompliant_bridge` bridges hardware
  descriptor AP/UXN/PXN bits to the abstract VSpace W^X invariant
- **Walk**: `pageTableWalk` uses structural recursion (no fuel) with
  `pageTableWalk_fault_on_non_table_l0` (L0 fault condition) and
  `pageTableWalkPerms_wx_bridge` (W^X compliance transfer) proofs

The VSpace ARMv8 instance (`VSpaceARMv8.lean`, AG6-C/D) provides the
`VSpaceBackend` typeclass implementation using a shadow `VSpaceRoot` with
refinement proofs: `simulationRelation`, `lookupPage_refines`,
`vspaceProperty_transfer`.

The ASID manager (`AsidManager.lean`, AG6-H) implements a bump allocator with
generation tracking, free list reuse, and `asidPoolUnique` invariant.

#### 6.5.5 FFI Bridge (Lean ↔ Rust)

The FFI bridge (`SeLe4n/Platform/FFI.lean`, AG7 + WS-RC R2) crosses the
Lean ↔ Rust boundary in two directions:

**Lean → Rust** (`@[extern]` `opaque` declarations): the verified Lean
kernel calls into the Rust HAL.  After WS-RC R2 the surface remains
the same set of HAL primitives:

- **UART**: `ffi_uart_putchar`, `ffi_uart_getchar`
- **Timer**: `ffi_timer_get_count`, `ffi_timer_set_comparator`,
  `ffi_timer_get_frequency`
- **GIC**: `ffi_gic_acknowledge`, `ffi_gic_eoi`, `ffi_gic_enable_irq`
- **MMU**: `ffi_mmu_enable`, `ffi_mmu_set_ttbr0`, `ffi_mmu_invalidate_tlb`
- **CPU**: `ffi_cpu_wfe`, `ffi_cpu_dsb`, `ffi_cpu_isb`, `ffi_cpu_dmb`
- **Context switch**: `ffi_context_switch`
- **Interrupts**: `ffi_interrupts_disable`, `ffi_interrupts_restore`

**Rust → Lean** (`@[export]` declarations, WS-RC R2): the Rust HAL
calls back into the verified kernel after handling an exception
bracket.  Two such bridges exist:

- `@[export suspend_thread_inner]` (named `suspend_thread_inner` on
  the C side) — substantively routes into
  `Kernel.Lifecycle.Suspend.suspendThread` after sentinel rejection
  via `ThreadId.toValid?`.  Returns `0` on success or the
  `KernelError as u32` discriminant on failure.
- `@[export syscall_dispatch_inner]` (named `syscall_dispatch_inner`
  on the C side) — a thin BaseIO wrapper around the pure typed-ABI
  entry point `syscallDispatchFromAbi`, which spills the FFI
  register values into the current TCB and invokes
  `syscallEntryChecked` with the deployment's `LabelingContext` and
  `arm64DefaultLayout`.  Returns a UInt64 per the bit-63 error-flag
  contract: bit 63 = 1 with the low 32 bits encoding the
  `KernelError` discriminant on the error path; bit 63 = 0 with the
  low 63 bits carrying the success return value.

Hardware-mode kernel state lives in two `IO.Ref` cells:

- `kernelStateRef : IO.Ref SystemState` — the live kernel state.
  Initialised by `bootAndInitialiseFromPlatform` (which composes
  `bootFromPlatformChecked` with the IO.Ref seed) on hardware boot.
- `kernelLabelingContextRef : IO.Ref LabelingContext` — the
  deployment's information-flow labeling policy.  Defaults to
  `Kernel.testLabelingContext` (which passes the
  `isInsecureDefaultContext` runtime gate); production deployments
  override it with their domain-specific policy at boot.

The IO.Ref design was chosen over thread-local register-decoded
snapshots and pure functional reconstruction because (a) the Rust
HAL serialises every SVC entry through `with_interrupts_disabled`,
giving the IO.Ref the sequential semantics it needs without
atomicity overhead; (b) thread-local snapshots would multiply FFI
symbols per syscall; (c) pure reconstruction would force
serialise/deserialise of the full `SystemState` (object store,
scheduler, CDT, …) at every syscall, making cost unbounded in
object-store size.

Production `AdapterProofHooks` (`rpi5ProductionAdapterProofHooks` in
`Platform/RPi5/ProofHooks.lean`) provides substantive preservation proofs
for all 4 adapter paths. The `proofLayerInvariantBundle` (11 conjuncts)
and `ipcInvariantFull` (15 conjuncts after WS-RC R4.C.7 close-out)
are preserved through the FFI boundary.

**AI1-D (v0.27.7)**: The `BOOT_UART` global in `sele4n-hal/src/uart.rs` is now
synchronized via an `AtomicBool`-based `UartLock` spinlock, which disables
interrupts before acquiring the lock and restores them after release, preventing
IRQ-handler deadlock on single-core systems. This eliminates the M-27 unsafe
`static mut` that produced undefined behavior after interrupts were enabled. All
UART access (including `kprint!` macro and FFI `ffi_uart_putc`) flows through
the lock. The original `pub static mut BOOT_UART` has been replaced with
module-private `BOOT_UART_INNER` guarded by `UART_LOCK`.

#### 6.5.6 Architecture Gap: TPIDR_EL0 / TLS (L-13)

`RegisterFile` (Prelude.lean) models GPRs (x0-x30), PC, and SP only.
The ARM64 `TPIDR_EL0` register (thread-local storage pointer) is not
modeled. This register is required for user-space TLS support (e.g.,
`__thread` variables, Go runtime, Rust `thread_local!`).

**Integration timeline**: TPIDR_EL0 modeling is planned for a future
AG-phase when user-space binary loading and context switching of system
registers are implemented. The `TrapFrame` in `sele4n-hal` (272 bytes)
already has space for system register state; the Lean model needs a
corresponding `RegisterFile` extension.

### 6.6 Platform Testing Limitations (M-05)

The simulation platform contract (`Sim/Contract.lean`) uses a permissive
runtime contract (`True` for register context stability and memory access)
but substantive boot and interrupt contracts (AI5-A/B, v0.27.11).

**Boot contract** (`simBootContract`): Validates empty initial object store
and empty capability reference table — matching the RPi5 production pattern.

**Interrupt contract** (`simInterruptContract`): Restricts supported IRQs
to GIC-400 INTID range 0–223, with handler mapping required for supported
lines — matching the RPi5 production pattern.

**Remaining limitations**:
- The RPi5 `registerContextStable` check (6 conditions: stack alignment,
  PC kernel range, budget positivity, SP mapped, return address valid,
  TLS pointer valid) is NOT exercisable under simulation
- Cache coherency model proofs (`CacheModel.lean`) are trivially satisfied
- Interrupt disable/enable semantics are sequential-model approximations

**Recommendation**: Use the `Sim.Restrictive` contract for property
validation (it imposes some structural constraints). For production-
representative testing, use the RPi5 contract (`RPi5/Contract.lean`).

### 6.7 Insecure Default Labeling Context Guard (M-19)

The `defaultLabelingContext` assigns `publicLabel` to all entities, defeating
all information-flow enforcement. This is formally proven insecure by
`defaultLabelingContext_insecure` and `defaultLabelingContext_all_threads_observable`.

**Runtime guard** (AI5-C, v0.27.11): `syscallEntryChecked` rejects contexts
detected as insecure by `isInsecureDefaultContext`, returning `.error .policyDenied`.
The detector checks sentinel labels at ID 0 across all four entity classes
(threads, objects, endpoints, services) in O(1) time.

**Test helper**: `testLabelingContext` assigns `kernelTrusted` to ID 0 entities,
passing the guard while remaining structurally valid for test execution. Test
harnesses should use this context instead of `defaultLabelingContext` when
exercising `syscallEntryChecked`.

### 6.8 SMP-Latent Single-Core Assumptions (AN12-B / Theme 4.4)

WS-AN Phase AN9-J landed the secondary-core bring-up infrastructure
(`rust/sele4n-hal/src/psci.rs`, `rust/sele4n-hal/src/smp.rs`) merged
behind the runtime flag `SMP_ENABLED = false` so v1.0.0 ships single-core
by default. AN12-B records the per-site inventory of kernel transitions
that depended on a single-core ordering invariant before AN9-J and now
share the AN9-J runtime gating.

The canonical inventory lives in
`SeLe4n/Kernel/Concurrency/Assumptions.lean` as
`def smpLatentInventory : List SmpLatentAssumption` with 8 entries
(`smpLatentInventory_count : smpLatentInventory.length = 8` is the
machine-checked size witness). Each entry carries five fields
(`identifier`, `singleCoreWitness`, `smpDischarge`, `sourceTheorem`,
`auditReference`).

| # | Site | Audit reference |
|---|------|-----------------|
| 1 | `cspaceLookupMultiLevel` resolved-CNode validity | H-05 / AN4-D |
| 2 | `cspaceCopy/Move/Mutate` CDT post-state composition | AK7-F.cascade / AN10-B |
| 3 | `lifecyclePreRetypeCleanup` sequential cleanup ordering | C-M04 / AN9-D |
| 4 | `serviceHasPathTo` graph traversal | SVC-M01 / AN4-H |
| 5 | `timerTickWithBudget` replenishment pipeline | AK2-K / AN5-D |
| 6 | `typedIdDisjointness` invariant | H-10 / AN2-D |
| 7 | `Architecture/Assumptions.lean` single-core kernel model | AG-* baseline |
| 8 | `bootFromPlatform` boot-core / current-core | CX-M03 / AN6-F |

The inventory is wired into `SeLe4n.Platform.Staged` so `lake build
SeLe4n.Platform.Staged` (and therefore tier-1 CI) forces the module to
compile. Future SMP activation (flipping `SMP_ENABLED = true`) does not
require any new entries to land; instead each entry's `smpDischarge`
field documents the runtime invariant that AN9-J's bring-up code
preserves on a per-core basis.

#### WS-SM SM4.E — single-core witness retirement + retirement ledger

WS-SM **SM4.E** (plan `docs/planning/SMP_PER_CORE_STATE_PLAN.md` §5.5)
begins discharging the inventory as the SM4 path-a per-core migration
lands. SM4.B replaced the singular `SchedulerState` fields with per-core
`Vector α numCores`, so the boot-core-only single-core witness
`bootFromPlatform_singleCore_witness` (formerly in `CrossSubsystem.lean`)
became structurally too weak to characterise the per-core shape and was
**retired** (SM4.E.1). Its replacement is the per-core SMP-shape witness
`SeLe4n.Platform.Boot.bootFromPlatform_smp_witness` — `∀ c : CoreId`, the
booted scheduler's `currentOnCore c` is `none ∨ = some (idleThreadId c)` —
with the substantive companion `bootFromPlatform_smp_currentAllNone`
(`currentOnCore c = none` on **every** core at boot). Naming the per-core
idle thread makes the witness non-vacuous (it excludes `current = some t`
for non-idle `t`) yet forward-compatible. Inventory entries 7 and 8 are
repointed to these two theorems (SM4.E.3 / SM4.E.4) and their `smpDischarge`
reads "implemented in SM4 path-a".

**WS-SM SM4.G (v0.31.36)** then installed the per-core idle threads (plan
§3.7): `idleThreadId` / `createIdleThread` /
`bootFromPlatformWithIdleThreads` (a wrapper leaving the base
`bootFromPlatform` unchanged), with `bootFromPlatformWithIdleThreads_all_cores_have_idle`
(`∀ c`, `currentOnCore c = some (idleThreadId c)` + idle TCB present — the
live `some` branch of the witness),
`…_schedulerInvariantBundle` (the installed state is scheduler-valid), and
`…_valid` (the four structural boot invariants).  All axiom-clean.

**WS-SM SM4.G audit-pass-1 (v0.31.37)** strengthened the idle-state soundness
to the **full** 9-conjunct bundle and closed a phantom-symbol gap:
`bootFromPlatformWithIdleThreads_schedulerInvariantBundleFull` proves the
installed state satisfies `schedulerInvariantBundleFull` (not merely the base
triad) — and, unlike the plain `bootFromPlatform` Full bundle (which discharges
the current-thread conjuncts vacuously via `current = none`), the idle path
discharges `currentTimeSlicePositive` and `contextMatchesCurrent`
*substantively* against the live idle TCB; bonus
`…_currentThreadInActiveDomain` places the idle thread in the boot active
domain.  The `idleThreadIdBase` docstring's `idleSlotsFreshAt` freshness
hypothesis — previously a phantom reference — is now a real predicate, with
`bootFromPlatformWithIdleThreads_preserves_platform_objects` (under freshness
the install is purely additive — no config object clobbered) and
`idleSlotsFreshAt_of_initialObjects_below_base` (freshness discharged for any
config whose objects live below `idleThreadIdBase` — the canonical RPi5/Sim
case), making the 16-bit disjointness rationale a *proven* property rather than
a convention.  All axiom-clean.

`SeLe4n/Kernel/Concurrency/Assumptions.lean` also adds the **retirement
ledger** `def smpRetiredInventory : List SmpRetiredAssumption` (SM4.E.5):
an 8-entry list mirroring `smpLatentInventory` one-to-one by `identifier`
(`smpRetiredInventory_covers_latent`), tracking the retirement of each
latent assumption toward the v1.0.0 SMP release. Each entry carries a
`SmpRetirementStatus` — `.pathARetired` for the two assumptions SM4 path-a
genuinely retires (the scheduler-state shape and the boot-core current),
`.perCoreBracketGated` for the six whose single-core property is preserved
per-core by the FFI interrupt-disabled dispatch bracket (full cross-core
retirement gated on SM5+). The honest current disposition is pinned by the
full partition `smpRetiredInventory_pathARetired_count` (= 2 at SM4.E) /
`smpRetiredInventory_perCoreBracketGated_count` (= 6) and the size by
`smpRetiredInventory_count` (= 8); WS-SM SM9 (release closure) flips the
gated entries and proves `smpRetiredInventory_complete` once SM5..SM8 land.
The ledger's per-entry names are build-anchored in `Concurrency.Anchors`
alongside the latent inventory (closing SMP-H3).

2.11. **WS-SM Phase SM3.D (post-SM3.C) deadlock-freedom, wait-graph
   acyclicity, bounded-wait, and lock-discipline grounding** — closes
   §5.4 of `docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md` (3 PRs, 7
   sub-tasks, all LANDED) within the v0.31.9 release cut.  Proves the
   architectural keystone of SM3: **no execution of the verified
   microkernel can deadlock** when every kernel transition acquires
   its locks under SM3.C's two-phase-locking discipline in the SM0.I
   `LockId` total order.  New file
   `SeLe4n/Kernel/Concurrency/Locks/Deadlock.lean` (~584 LoC) +
   `DeadlockInventory.lean` (37-theorem inventory aggregator); three
   `LockId` strict-order helpers added to the SM0.I `Kind.lean`.

   **SM3.D.1 — `KernelExecution` model + `noDeadlock`**: the abstract
   per-core lock-state snapshot (`held : CoreId → List LockId`,
   `blocked : CoreId → Option LockId`) with `blockedAt` / `heldBy`
   predicates; `noDeadlock e` is the two-core mutual-block deadlock-
   freedom predicate.  `Decidable (noDeadlock e)` is derived via the
   finite reformulation `noDeadlockDec` + `noDeadlock_iff_dec`: the
   spec's `∃ l₁ l₂ : LockId` are pinned by the `blocked` fields, so
   the existential collapses to a decidable per-pair `mutualBlocked`
   test (no unbounded search over the infinite `LockId` type).

   **SM3.D.3 — `lockOrder_strict`**: the `LockId` strict order is
   irreflexive ∧ transitive, bundling the new `Kind.lean` helpers
   `LockId.lt_irrefl` / `LockId.lt_trans` / `LockId.lt_asymm`.
   (`Irreflexive` / `Transitive` are mathlib typeclasses unavailable
   in the core-only toolchain, so stated with explicit `∀`.)

   **SM3.D.4 — `deadlockFreedom_under_2pl_and_ordering` (Theorem
   2.1.9)**: no execution satisfying `executionFollows2PL` AND
   `executionAcquiresInLockIdOrder` reaches a two-core deadlock.  The
   proof factors through the **ladder invariant**
   `ladder_of_2pl_and_order`: every lock a blocked core holds is
   *strictly* below the lock it waits for.  This is the exact point
   where the two hypotheses combine — ordering gives `held ≤ wanted`;
   2PL (a core never blocks on a lock it already holds, `wanted ∉
   held`) upgrades it to the strict `held < wanted` that closes the
   cycle.  Both hypotheses carry genuine, non-redundant content.

   **SM3.D.5 — `waitGraph_acyclic_under_2pl`**: the dual, N-core form
   — the wait-for graph among blocked cores is a DAG.  Formalised with
   a mathlib-free transitive closure `ReachesPlus` and `Acyclic R := ∀
   c, ¬ ReachesPlus R c c`.  The wanted lock strictly increases along
   every wait edge (`blockedWaitsFor_wanted_lt`) and hence every path
   (`reachesPlus_wanted_lt`), so a cycle would force `w < w`.  The
   coherence corollary `noDeadlock_of_waitGraph_acyclic` derives the
   two-core SM3.D.4 from the N-core SM3.D.5 (a 2-cycle is a closed
   walk c₁ → c₂ → c₁).

   **SM3.D.6 — `boundedWait_under_2pl`** (full form): under the 2PL +
   ordering hypotheses, an execution is deadlock-free AND every kernel
   operation's worst-case response time is bounded —
   `noDeadlock e ∧ WCRT e c op tCs ≤ maxLockSetSize · (numCores − 1) ·
   T_cs`.  `WCRT` is contention-sensitive: for each lock in the
   operation's footprint, `contendersAhead e c` counts the cores
   actually holding it (`≤ numCores − 1`).  `KernelOperation` carries a
   `LockSet` footprint plus a `sizeWithinBound` proof, and
   `lockSetTransitions_within_bound` discharges that proof for all 25
   SM3.B `lockSet_<τ>` declarations (size `≤ 8`) — so the bound is
   never vacuous.

   **SM3.D.5b — mode-aware deadlock-freedom**: the plan-signature
   `noDeadlock` / `waitGraph_acyclic_under_2pl` use bare `LockId`,
   which over-approximates blocking.  `conflictWaitGraph_acyclic_under_2pl`
   refines this — an edge fires only on a genuine
   `AccessMode.conflicts` (two readers never block) — and is proved
   acyclic via `Acyclic_mono` (it is a subgraph of the plain wait
   graph).

   **SM3.D §7b — model↔kernel bridge**: `lockSetHeld_realizes_heldBy`
   connects the abstract `KernelExecution.heldBy` (via `executionOfHeld`)
   to SM3.C's concrete `lockSetHeld` / `lockHeld`, which read the actual
   per-object `RwLockState` of a `SystemState` — so a deadlock-relevant
   abstract "held" edge is realised by a genuine kernel lock holding.

   **SM3.D §7 — grounding**: `execution_satisfies_hypotheses_of_all_prefix`
   discharges both abstract hypotheses from the SM3.B
   `lockAcquireSequence` canonical sort.  A blocked core in
   `withLockSet`'s growing phase holds a `Nodup`-keyed ascending
   *prefix* (`CorePrefixOf`) of its transition's acquire order and
   waits on the next element, which forces 2PL
   (`coreFollows2PL_of_prefix`, via the `Nodup` split) and ordering
   (`coreAcquiresInOrder_of_prefix`, via `lockSet_acquired_in_order`).
   This realises plan §3.7's "By 2PL, H_c is the prefix of c's
   `lockAcquireSequence(S_c)`" step: the deadlock-freedom hypotheses
   are *consequences* of `withLockSet`, not assumptions.

   **Tests**: `tests/DeadlockFreedomSuite.lean` (~357 LoC) — surface
   anchors for every SM3.D symbol, decidable examples on concrete
   `KernelExecution` fixtures, compile-time theorem-inhabitation
   `example`s, and 30 runtime `assertBool` assertions.  Includes a
   non-vacuity witness: a genuine 2-core deadlock fixture that IS a
   mutual block AND necessarily violates the ordering hypothesis
   (every deadlock state falsifies a hypothesis).  Wired into Tier 2
   (negative) + Tier 3 (invariant surface).  **Axiom budget for
   SM3.D**: 0 Lean axioms, 0 sorries.

2.12. **WS-SM Phase SM3.E (post-SM3.D) serializability, conflict-graph
   acyclicity, single-core proof preservation — SM3 CLOSED** — the
   second architectural keystone of SM3 (after SM3.D's deadlock-freedom):
   **every interleaved execution of kernel transitions under strict
   two-phase locking is conflict-equivalent to a serial execution**
   (Bernstein et al. 1987, Theorem 2.1.10), the serial order being the
   commit-time order.  New module
   `SeLe4n/Kernel/Concurrency/Locks/Serializability.lean` (~1857 LoC) +
   `SerializabilityInventory.lean` (111-theorem inventory), staged via
   `Concurrency.LockSet`.

   - **SM3.E.1 — `conflictOrder`**: the `KernelTransitionInstance`
     schedule model `(lockSet, core, commitTime, acquireTime, action)`;
     two instances conflict-order on a shared `LockId` in conflicting
     modes when the first commits no later than the second acquires it.
     Decidable via the Bool `ktiConflictsB` (+ `ktiConflictsB_iff`).
   - **SM3.E.2 — `serialEquivalent`**: `applySequential` folds the
     schedule's actions; two schedules are serial-equivalent when they
     produce the same final state.  Under strict 2PL each transition
     commits atomically (SM3.C.7), so `applySequential` on the commit
     order computes the interleaved net effect.
   - **SM3.E.3 — `serializability_under_2pl` (Theorem 2.1.10)**: every
     strict-2PL execution is serial-equivalent to the commit-sorted
     serial order (a permutation, commit-ascending = topological sort).
     Reduces to `conflictGraph_acyclic` (the acyclic conflict graph,
     proved like SM3.D's wait-graph via strict-`<`-along-edges over
     commit times) plus the commuting-transposition reordering
     (`commitSort_commutingReorder` under the strict-2PL
     `outOfOrderCommute` hypothesis).
   - **SM3.E.4 — `strictly_2pl_preserved`**: every `withLockSet`-built
     transition holds all its locks until commit
     (`conflictOrder_commit_le` forces conflict resolution in commit
     order).
   - **SM3.E.5 — commutativity**: ≥8 lemmas at two honest fidelities —
     structural `actionsCommute` for read-only and disjoint-subsystem
     pairs; observational `objStoreEquiv` for write/write on distinct
     objects (the Robin-Hood store's slot layout is insertion-order-
     dependent, and conflict-serializability is an observational
     property, so this is faithful).
   - **SM3.E.6 — `singleCore_proof_preservation` (Corollary 2.1.11)**:
     the pre→post meta-theorem lifting single-core theorems to SMP under
     the `lockSetHeld` precondition (a *consequence* of `withLockSet`,
     via `withLockSet_growing_phase_establishes_lockSetHeld`), reusing
     SM3.C.8's `withLockSet_invariant_preserved`.
   - **SM3.E (audit-pass-3) — atomicity bridge + observational
     serializability + second Cor 2.1.11 instantiation**: closes the
     three gaps the initial landing documented as deferred but did not
     implement.  (a) `withLockSet_observation_eq_action` +
     `applySequentialWithLockSet_observation` connect the bare-action
     `applySequential` model back to SM3.C.7's `withLockSet` atomicity,
     so the headline theorem reasons about real 2PL-wrapped transitions.
     (b) `serializability_under_2pl_obs` proves serial-equivalence up to
     `objStoreEquiv` for write/write-to-distinct-object schedules (the
     structural headline reorders via `Eq`, which write/write pairs do
     not satisfy), threading `invExt` through the `commitSort` reorder;
     `objStoreWriteInstance` is the canonical covered instance.
     (c) `withLockSet_preserves_objectType_at` proves the 2PL machinery
     preserves a second real invariant (per-key kind-tag equality bundled
     with `invExt`), demonstrating the Cor 2.1.11 lever generalises
     beyond `objStoreLock.wf`.
   - **SM3.E (audit-pass-4) — atomicity-bridge non-vacuity (§9b)**: a
     comprehensive `#print axioms` sweep over all 106 inventory theorems
     confirmed they are axiom-clean.  The §9 bridge's `AcquireInsensitive`
     / `ReleaseInsensitive` hypotheses had no concrete witness (unlike
     §8b/§8c/§10), so §9b exhibits the `scheduler` projection as a genuine
     non-trivial observer discharging both unconditionally
     (`schedulerObserver_acquireInsensitive` / `_releaseInsensitive` via
     `acquireLockOnObject_preserves_scheduler` / `release…`) and applies the
     bridge non-vacuously (`withLockSet_observation_scheduler_witness`: a
     scheduler write through the full 2PL machinery is observed `= sch`).
     Inventory 106 → 111.
   - **SM3.E.7/E.8 — tests**: `tests/SerializabilitySuite.lean`
     (60+ surface anchors + 18 decidable examples + 6 theorem-application
     witnesses + 27 runtime assertions) + 8 major-theorem `#check`
     anchors in `tests/SmpSurfaceAnchors.lean`.  Tier 2 + Tier 3 wired.

   **Non-vacuity**: `serializability_of_readOnly_schedule` proves a
   hypothesis-free family (read-only schedules) is serial-equivalent to
   its commit sort.  **Axiom budget for SM3.E**: 0 Lean axioms, 0
   sorries.  **SM3 CLOSED** — all five sub-phases LANDED (SM3.A–SM3.E);
   the `@[export]`-body migration (SM3.C.9) remains deferred to SM5+.

2.13. **WS-SM Phase SM4.A (v0.31.11) per-core `Vector` bootstrap +
   PlatformBinding** — opens SM4, the path-a replacement of the singular
   `SchedulerState` fields with `Vector α coreCount` indexed by
   `CoreId`.  All eight sub-tasks landed in one cut; SM4.A.1 + SM4.A.2
   are the new Lean-side work, SM4.A.3..SM4.A.8 confirm/recap the SM0
   deliverables the per-core `Vector` machinery rests on.

   - **SM4.A.1 + SM4.A.2 — `SeLe4n.PerCoreVector` bootstrap** (`Prelude.lean`):
     per plan §4.2 the implementation uses Lean core's `Array`-backed
     `Vector α n` (not `List.Vector`) — the only choice giving
     compile-time length safety (`CoreId = Fin n` indexing in-bounds by
     construction), O(1) random access, decidable equality, AND an
     `Array`-backed runtime.  Lean core's vector lemmas are stated in
     `getElem` (`Nat`-indexed) form; the SM4 per-core accessors index
     with a `Fin n` value via `Vector.get`, so the block re-expresses
     them in `Vector.get` form on top of the definitional bridge
     `get_eq_getElem` (`v.get i = v[i.val]`, by `rfl`).  Six helpers
     (`namespace SeLe4n.PerCoreVector`): `get_set_eq` (read-after-write at the
     same core), `get_set_ne` (a per-core write frames every other
     core's slot), `toList_length` (`v.toList.length = n`), `replicate_get`
     (every slot of a replicate holds the value — the SM4.B.9 default-
     init workhorse), `ext` (per-core `Vector.get`-form extensionality;
     intentionally not `@[ext]`-tagged so the core `_root_.Vector.ext`
     keeps firing under the `ext` tactic), and `nodup_of_finRange`
     (`(List.finRange n).Nodup` for arbitrary `n` — Lean core has
     `nodup_range` but no `nodup_finRange`; proved by induction via
     `finRange_succ` + `Fin.succ_ne_zero` + `Fin.succ_inj`, generalising
     `Concurrency.allCores_nodup`'s literal-4 `decide` to a platform-
     parameterised `coreCount`).
   - **SM4.A.3 — runtime efficiency**: `Vector α n` is `Array`-backed
     (`structure Vector where toArray : Array α`) with `@[inline,
     expose]` `get`/`set`/`replicate`, so it compiles to O(1) `Array`
     operations.  Backed by two layers of evidence: the codegen
     (emitting the C shows `Vector.get` → `lean_array_fget`, `set` →
     `lean_array_fset`, `replicate` → `lean_mk_array`, no `lean_list_*`
     ops) and the persistent
     type-level witness `get_eq_toArray_getElem` (`v.get i =
     v.toArray[i.val]`, so `.get` indexes `toArray` directly — a future
     refactor breaking the array routing fails the build).  (The full
     `lake exe sele4n` per-core-access trace lands at SM4.B.15, once
     `SchedulerState` is itself `Vector`-shaped.)
   - **SM4.A.4 — RPi5 `coreCount = 4`**: confirmed, pinned to
     `Concurrency.numCores` via `numCores_eq_rpi5_coreCount` (`rfl`).
   - **SM4.A.5 — simulation bindings**: added the single-core sim
     `SimSingleCorePlatform` (`coreCount := 1`) alongside the 4-core SMP
     sims (`SimPlatform` / `SimRestrictivePlatform`, `coreCount := 4`),
     realising the single-core variant the SM0.G code comment
     anticipated — the minimal non-degenerate per-core topology and the
     SM4.B.15 byte-identical single-core trace target.  Exercised at
     runtime: a topology-parametric per-core read-fold drives the
     binding's `coreCount` through the `Vector` machinery end-to-end.
   - **SM4.A.6 / SM4.A.7 / SM4.A.8 — recaps** of `CoreId = Fin
     numCores`, `bootCoreId`, and `allCores` (`allCores_length`,
     `allCores_nodup`).  `allCores_nodup` is rewired to prove via the
     SM4.A.2 `nodup_of_finRange numCores` (replacing its literal-`4`
     `decide`), so the generalisation is load-bearing in production.

   **Test coverage**: `tests/PerCoreVectorSuite.lean`
   (`lake exe per_core_vector_suite`) — 22 surface anchors, 40 decidable
   examples, 34 runtime assertions across seven sections (incl. SM4.A.1
   instance anchors verifying `Vector (Option ThreadId) numCores` carries
   `DecidableEq`/`Repr`/`Inhabited`/`BEq`); Tier 2 + Tier 3 wired.
   **Axiom budget for SM4.A**: 0 Lean axioms, 0 sorries.

   **SM4.B — `SchedulerState` path-a `Vector` replacement (v0.31.12).**
   The seven singular per-core `SchedulerState` fields (`runQueue`,
   `current`, `replenishQueue`, `activeDomain`, `domainTimeRemaining`,
   `domainScheduleIndex`, `lastTimeoutErrors`) flip from scalars to
   `Vector α Concurrency.numCores` indexed by `CoreId`, with
   `Vector.replicate numCores <neutral>` defaults; `domainSchedule` and
   `configDefaultTimeSlice` stay system-wide. The seven `…OnCore`
   accessors are now `Vector.get`-backed and gain seven matching
   `set…OnCore` writers, governed by a 70-lemma `@[simp]` store/load
   algebra (7 read-after-write + 7 same-field cross-core independence
   `_ne` + 42 cross-field frame + 14 system-wide-field frame). Because
   `Vector.get (Vector.set …)` is not
   definitional, these proved lemmas — not `rfl`/iota — drive every
   post-write read reduction, which is how the whole production import
   closure (scheduler operations + preservation, SchedContext,
   lifecycle, IPC, priority inheritance, information-flow projection +
   NI, architecture invariants, cross-subsystem, boot, freeze) re-proves
   without behavioural change. `default_state_perCoreInitialized`
   (SM4.B.9) and `SchedulerState.ext_perCore` (SM4.B.10) anchor the
   per-core defaults and extensionality. The executable trace remains
   **byte-identical** to `main_trace_smoke.expected` (SM4.B.15) because
   the boot core behaves exactly as the former scalar. Axiom budget for
   SM4.B: 0 axioms, 0 sorries. Follow-on: SM4.C/SM4.D (theorem
   migrations), SM4.E (`bootFromPlatform_smp_witness` + witness
   retirement).

   **SM4.C — per-core scheduler invariant migration (v0.31.13).**  Lifts
   the scheduler invariant *predicates* from the single-core forms (pinned
   to `bootCoreId` after SM4.B) to per-core forms parameterised by an
   explicit `(c : CoreId)` (plan §5.3 / §5.6, migration pattern §3.4).
   The migration is **additive and soundness-preserving**: every per-core
   form at `bootCoreId` is *definitionally* the existing single-core
   predicate (proved as `Iff.rfl`), so the live `schedulerInvariantBundle*`
   / `crossSubsystemInvariant` surface stays green and SM4.C strictly
   adds the per-core layer SM5 consumes.  New module
   `SeLe4n/Kernel/Scheduler/Invariant/PerCore.lean` (~380 LoC, staged
   via `Platform/Staged.lean`):
   - **§1 (16 per-core predicate forms)** — the full per-core slice of
     `schedulerInvariantBundleExtended`'s genuinely-per-core conjuncts:
     `queueCurrentConsistentOnCore` / `runQueueUniqueOnCore` /
     `currentThreadValidOnCore` / `currentThreadInActiveDomainOnCore` /
     `timeSlicePositiveOnCore` / `currentTimeSlicePositiveOnCore` /
     `edfCurrentHasEarliestDeadlineOnCore` / `contextMatchesCurrentOnCore`
     / `runnableThreadsAreTCBsOnCore` / `schedulerPriorityMatchOnCore` /
     `domainTimeRemainingPositiveOnCore` / `currentBudgetPositiveOnCore`
     / `budgetPositiveOnCore` / `replenishmentPipelineOrderOnCore` /
     `replenishQueueValidOnCore` / `effectiveParamsMatchRunQueueOnCore`.
   - **§2 (16 boot-core bridges)** — each `…OnCore_bootCore_iff` is
     `Iff.rfl`, the non-orphan defeq grounding to the live single-core
     predicates.
   - **§3 (SM4.C.29 aggregate)** — `schedulerInvariant_perCore st c` is
     the 10-conjunct per-core analogue of `schedulerInvariantBundleFull`
     (minus the system-wide `domainScheduleEntriesPositive`);
     `schedulerInvariant_smp st := ∀ c, schedulerInvariant_perCore st c`;
     `schedulerInvariant_perCore_aggregateForall` bridges the two
     (plan §5.6); 10 per-conjunct projections mirror the
     `schedulerInvariantBundleFull_to_*` family.
   - **§4 (bundle bridges)** —
     `schedulerInvariantBundleFull_to_perCore_bootCore` (and the
     `Extended` lift) proves the existing single-core preservation work
     yields a per-core preservation at the boot core *for free*; the
     converse `…_bootCore_to_bundleFull` reassembles the full bundle
     from the per-core slice plus the system-wide
     `domainScheduleEntriesPositive`.
   - **§5 (default-state)** — `default_schedulerInvariant_perCore (c)`
     proves every core satisfies the per-core invariant on the freshly-
     booted system; `default_schedulerInvariant_smp` is the full SMP form.
   - **§6 (frame + SM4.C.30 pairwise independence)** — the substantive
     cross-core-independence content.  `schedulerInvariant_perCore_frame`
     is the general frame lemma (core `c`'s invariant depends only on
     core `c`'s `current`/`runQueue`/`domainTimeRemaining` plus `objects`
     and `machine.regs`); `…_frame_idle` is the regs-independent variant
     for idle cores (used when a boot operation re-writes `machine.regs`,
     e.g. `schedule`'s context restore — the idle cores' invariants stay
     preserved because their current-dependent conjuncts are vacuous);
     three cross-core independence corollaries
     (`_independent_of_setCurrentOnCore`, `…setRunQueueOnCore`,
     `…setDomainTimeRemainingOnCore`) instantiate the frame via the SM4.B
     `set…OnCore_…OnCore_ne` algebra; **`schedulerInvariant_perCore_pairwise`**
     (the SM4.C.30 deliverable) *strengthens* the plan's documentation-
     only `P ↔ P` form per the implement-the-improvement rule into a
     substantive theorem: for `c₁ ≠ c₂`, overwriting all three of core
     `c₂`'s invariant-read slots leaves core `c₁`'s invariant unchanged.
   - **§7 (SMP-preservation skeleton)** —
     `schedulerInvariant_smp_of_bootCore_and_idle_frame` is the SM5
     migration bridge: a per-core operation's preservation needs to be
     reproven only at the core it writes; every other core discharges
     by the idle frame lemma.

   **Test coverage**: `tests/SchedulerInvariantPerCoreSuite.lean`
   (`lake exe scheduler_invariant_per_core_suite`) — 60+ Tier-3 surface
   anchors, 12 elaboration-time `example`s applying every headline
   theorem to verified inputs, and 16 runtime `assertBool` assertions
   across four sections (default-state per-core foundations on every
   core in `allCores`; theorem-application checks; cross-core pairwise
   independence; boot-core bridge reflexivity).  Tier-2 + Tier-3 wired.
   **Axiom budget for SM4.C**: 0 Lean axioms, 0 sorries — every theorem
   depends only on `propext` / `Quot.sound` / `Classical.choice`
   (verified via `#print axioms` on the headline theorems).  Follow-on:
   SM4.D (cross-subsystem theorem migrations), SM4.E
   (`bootFromPlatform_smp_witness` + single-core witness retirement).

---

## 7. Acceptance Expectations

### 7.1 Per-Workstream Acceptance Gates

Each workstream has defined entry/exit criteria. Common acceptance patterns:

1. implementation compiles and passes tiered validation,
2. new/modified theorems are non-tautological and non-trivial,
3. executable trace evidence captures semantic breadcrumbs,
4. documentation is synchronized across all canonical surfaces,
5. no regressions in previously-completed workstream contracts.

### 7.2 Milestone-Moving PR Requirements

Every milestone-moving PR should include:

1. workstream ID(s) advanced,
2. objective and exit-criterion delta,
3. command evidence,
4. synchronized docs updates (README/spec/development/GitBook as needed),
5. explicit deferrals (if any) and destination workstream.

---

## 8. Model Fidelity & Type Safety (WS-S Phase S4)

### 8.1 Object Capacity Bounds

The abstract model uses unbounded `Nat` for object indices. For the RPi5
hardware target, the expected maximum object count is `maxObjects = 65536`.

- **objectIndex growth**: The `objectIndex` list consumes at most
  `65536 × 8 = 512 KB` at maximum capacity — well within RPi5's 8 GB RAM.
- **Advisory predicate**: `objectIndexBounded st` asserts
  `st.objectIndex.length ≤ maxObjects` (defined in `Model/State.lean`).
- **Capacity enforcement**: `storeObjectChecked` (AC3-E) returns
  `objectStoreCapacityExceeded` when inserting a new object at `maxObjects`
  capacity. In-place updates of existing objects are always permitted.
  `storeObject` (infallible) is used by internal operations where
  `objectIndexBounded` is an established invariant precondition.
  **Machine-checked (AF2-A)**: `storeObject_existing_preserves_objectIndex_length`
  proves in-place mutations preserve `objectIndex` length exactly;
  `retypeFromUntyped_capacity_gated` proves the allocation boundary gates
  on `maxObjects`.

### 8.2 Word-Boundedness Invariants

The Lean model bridges abstract `Nat` semantics to 64-bit hardware:

- **Register values**: `RegValue` wraps `Nat` with `isWord64` validity predicate.
- **Badges**: `Badge.ofNatMasked` masks to `2^64` at construction, proven valid.
- **Access rights**: `AccessRightSet.mk` constructor is `private` (AJ2-A/M-10);
  external construction via `ofNat` (masked to 5-bit), `ofList`, `singleton`,
  `empty`, or `mk_checked` (proof-carrying). Proven valid (`ofList_valid`, T2-A/H-1).
- **IPC messages**: `IpcMessage.registers` uses `Array RegValue` (typed values).
- **CPtr resolution**: `resolveSlot` masks input to 64 bits before guard extraction.
- **CNode guard bounds**: `CNode.guardBounded` predicate (`guardValue < 2^guardWidth`)
  integrated into `CNode.wellFormed`. `resolveSlot_guardMismatch_of_not_guardBounded`
  proves resolution always fails for out-of-bounds guards (T2-J/L-NEW-4).
- **CDT access control**: `CapDerivationTree` constructor is `private`; external
  construction requires `mk_checked` with `cdtMapsConsistent` witness (T2-B/C/H-2).
- **Frozen TLB**: `FrozenSystemState.tlb` field preserves TLB state across freeze;
  `freeze_preserves_tlb` correctness theorem (T2-D/E/F/M-NEW-1).
- **storeObject preservation**: Bundled `storeObject_preserves_allTablesInvExtK`
  theorem composing 16+ component proofs (T2-G/M-NEW-2). Uses `invExtK` kernel-level
  invariant bundle (V3-B) — eliminates separate `hSize`/`hCapGe4` threading.

### 8.3 Memory Alignment Model Gap

The abstract model uses `Memory := PAddr → UInt8` (byte-addressable). Real ARM64
hardware requires word-aligned access for register-width loads/stores:

- **Alignment predicates**: `alignedRead`/`alignedWrite` in `Machine.lean` document
  the word-alignment requirement.
- **Alignment faults**: Not modeled — the abstract `Memory` function accepts any
  address. Hardware binding (WS-T) must enforce alignment via the platform contract.
- This is a documented model gap, not a soundness issue: proofs about memory
  semantics hold for the abstract model; hardware binding adds the alignment
  constraint as an additional platform-level precondition.

### 8.4 Page-Alignment Requirement for VSpace-Bound Retype

`retypeFromUntyped` enforces page-aligned allocation bases (4 KiB) for object
types that require it. This applies to VSpace roots and CNodes, which must be
page-aligned for correct hardware page-table walks and CNode radix indexing.

- **`requiresPageAlignment`** -- predicate identifying `KernelObjectType` values
  that require page-aligned allocation (VSpace roots, CNodes).
- **`allocationBasePageAligned`** -- checks 4 KiB alignment of the allocation base
  (`base % 4096 == 0`).
- **`allocationMisaligned`** -- `KernelError` variant returned when the alignment
  check fails.
- **Lifecycle invariant preservation**: all existing lifecycle preservation proofs
  are updated to account for the new error branch. Error returns preserve the
  unchanged state trivially.

This enforcement closes the gap between the abstract model (which previously
accepted any allocation base) and hardware requirements for ARM64 page-table
structures. See `SeLe4n/Kernel/Lifecycle/Operations.lean` (S5-G/S5-H).

### 8.5 IPC Timeout Semantics (Z6)

seLe4n implements budget-driven timeout for IPC blocking operations (Z6),
extending seL4 MCS timeout semantics. When a thread's SchedContext budget
expires while blocked on send/receive/call/reply, the thread is unblocked
with the explicit `timedOut := true` TCB field set and re-enqueued in the
RunQueue.

- **`timeoutThread`** (`Timeout.lean`): Removes thread from endpoint queue
  via `endpointQueueRemove`, resets IPC state to `.ready`, sets
  `timedOut := true`, re-enqueues via `ensureRunnable`.
- **`timeoutBlockedThreads`** (`Core.lean`): Looks up the per-SchedContext
  thread index (`scThreadIndex`) for O(1) identification of threads bound
  to an exhausted SchedContext, then calls `timeoutThread` on each.
- **`timeoutAwareReceive`** (`Timeout.lean`): Wrapper that detects prior
  timeout via `tcb.timedOut` field; clears the flag on detection. Returns
  `.error .endpointQueueEmpty` if `pendingMessage = none` (AH2-G, v0.27.3),
  surfacing protocol violations instead of silently returning empty messages.
- **`blockedThreadTimeoutConsistent`** invariant: Threads with
  `timeoutBudget = some scId` must reference a valid SchedContext and be
  in a blocking IPC state.

**AG8-A migration note** (v0.26.9): Prior to AG8-A, timeout was signaled via
a sentinel value `0xFFFFFFFF` in GPR x0 combined with an `ipcState = .ready`
dual-condition check. This was fragile and could collide with legitimate IPC
data. AG8-A replaced the sentinel with an explicit `timedOut : Bool` TCB field,
eliminating the collision risk entirely.

The timeout lookup is triggered in `timerTickBudget` on budget exhaustion,
using the `scThreadIndex` (a Robin Hood hash table mapping `SchedContextId`
to `List ThreadId`) for O(1) identification of affected threads.

### 8.5.1 IPC Buffer Alignment (AG10-B / FINDING-07)

The IPC buffer has specific alignment requirements bridging the Lean model to
ARM64 hardware:

- **Lean model**: IPC buffer alignment is enforced at 512 bytes
  (`ipcBufferAlignment = 512` in `Architecture/IpcBufferValidation.lean`).
  `setIPCBufferOp` validates the address via a 5-step pipeline including
  alignment check, page membership, and VSpace lookup.
- **Rust ABI**: The `IpcBuffer` structure (`sele4n-abi/src/ipc_buffer.rs`) is
  960 bytes, `#[repr(C)]`, with 8-byte natural alignment. The 512-byte model
  alignment exceeds the ABI's 8-byte requirement.
- **Hardware justification**: 512-byte alignment provides 8 × 64-byte cache
  lines on Cortex-A76, ensuring the IPC buffer does not straddle cache line
  boundaries in a way that would cause false sharing or require additional
  cache maintenance. This is a **performance optimization**, not an
  architectural requirement — the hardware would function correctly with
  any 8-byte aligned buffer.
- **Page safety**: The `ipcBuffer_within_page` theorem (AE4-J) proves that
  a 512-byte-aligned IPC buffer of 960 bytes never crosses a 4 KiB page
  boundary (512 + 960 = 1472 < 4096). This guarantees a single TLB entry
  covers the entire buffer, avoiding mid-transfer page faults.

### 8.6 Memory Scrubbing on Delete (WS-S Phase S6)

When an object is deleted via `lifecycleRetypeWithCleanup`, the backing memory
region is zeroed using `scrubObjectMemory` before the memory is returned to the
untyped pool. This prevents information leakage between security domains when
memory is retyped for a different purpose.

- **`zeroMemoryRange`** (`Machine.lean`): Primitive that zeroes a contiguous
  range of physical memory addresses.
- **`memoryZeroed`** (`Machine.lean`): Postcondition predicate asserting all
  bytes in a range are zero after scrubbing.
- **`scrubObjectMemory`** (`Lifecycle/Operations/ScrubAndUntyped.lean` after the
  AN4-G.5 split; was `Lifecycle/Operations.lean`): Applies `zeroMemoryRange`
  to the object's backing region during cleanup.
- **Invariant preservation**: `scrubObjectMemory` preserves lifecycle invariants
  trivially (only modifies `machine.memory`, not kernel state structures).
- **NI preservation**: `scrubObjectMemory` preserves `lowEquivalent` for
  non-observable targets — scrubbing memory outside an observer's domain does
  not affect their projected state.

**AN4-G.3 (LIF-M03) — Lifecycle: model-vs-hardware scrub bridge.** The
model-layer `scrubObjectMemory` computes its target PAddr as
`objectId.toNat × objectTypeAllocSize` — a purely abstract convention. Real
hardware (the RPi5 AArch64 target) must route the same scrub through the
VSpace bridge so it hits the physical frame that actually backs the object's
allocation extent:

1. The untyped allocator in `retypeFromUntyped` records each child's
   allocation region as `(regionBase + offset, allocSize)` within the parent
   untyped object's physical range.
2. On cleanup, the hardware bridge must map the model-layer PAddr to the
   physical-frame extent assigned by the allocator and zero that extent
   using a cache-safe sequence (DSB ISHST + DC CVAC per 64-byte line +
   DSB ISH) before the memory is returned to the untyped pool.
3. The VSpace bridge is deferred to AN9 (hardware workstream); until then,
   the model-level scrub stands in as the abstract witness, and the
   `memoryZeroed` postcondition covers the model's view of the region.
4. AN12-B's SMP inventory tracks the additional obligation that the
   scrub must happen within the same critical section as the retype to
   prevent another core from observing the pre-scrub contents of the
   region during a race.

**AN4-G.6 (LIF-M06) — Lifecycle partial-failure semantics.** The
`lifecycleRevokeDeleteRetype` composition is **non-transactional**. An
early `.error` return from any of its four phases (revoke / delete /
post-delete-lookup / final retype) leaves the system state in a
partially-cleaned form, and the caller must handle this contractually.
The phase-by-phase side-effect catalogue is:

1. **`cspaceRevoke` failure**: no mutations committed; caller state preserved.
2. **`cspaceDeleteSlot` failure** (after successful revoke): the revoked
   CDT edges remain stripped even though the slot still holds its original
   capability. Caller sees `.error` with the partial revoke side-effect.
3. **Post-delete `cspaceLookupSlot` returns unexpectedly**: both revoke and
   delete have committed; retype is skipped; the slot was already scrubbed
   clean.
4. **`Internal.lifecycleRetypeObject` failure** (cleanup-bypass path —
   production callers use `lifecycleRetypeWithCleanup` instead): revoke +
   delete committed; target object retains its old variant.

Callers needing strict transactional "all-or-nothing" semantics should
invoke `cspaceRevokeCdtTransactional` (AK8-B) separately before the
retype pipeline, or use `lifecycleRetypeWithCleanup`, which wraps the
strict cleanup pipeline and propagates errors before any retype is
attempted. `.error` from `lifecycleRevokeDeleteRetype` is a best-effort
cleanup-partially-completed outcome, NOT a rollback.

### 8.7 TLB Flush Requirements for Production Paths (WS-S Phase S6)

All production VSpace operations must use TLB-flushing variants to ensure
hardware TLB consistency:

- **`vspaceMapPageCheckedWithFlush`**: Production path for mapping pages.
  Performs W^X checks, bounds validation, and targeted per-(ASID,VAddr) TLB
  flush after insertion (AJ4-B). Only the modified TLB entry is invalidated;
  other cached translations are preserved for performance.
- **`vspaceUnmapPageWithFlush`**: Production path for unmapping pages.
  Targeted per-(ASID,VAddr) TLB flush after removal (AJ4-B).
- **Internal helpers**: The unflushed `vspaceMapPage`/`vspaceUnmapPage` are
  internal proof decomposition helpers only. They carry explicit warnings
  against direct use in production paths.
- **API dispatch**: `dispatchWithCap` routes VSpace syscalls through the
  `WithFlush` variants exclusively.

### 8.8 Frozen IPC Queue Semantics (WS-T Phase T1)

Frozen kernel operations now support blocking IPC paths with proper queue
management:

- **`frozenQueuePushTail`**: Appends a thread to a frozen endpoint queue with
  dual-queue invariant precondition checks (head/tail link integrity).
  Integrated into `frozenEndpointSend`, `frozenEndpointReceive`, and
  `frozenEndpointCall`.
- **7 preservation theorems** prove that enqueue operations maintain all frozen
  state invariants via `frozenQueuePushTail_only_modifies_objects`.
- **Commutativity**: `FrozenMap` set/get? roundtrip proofs ensure lookup
  consistency after frozen state mutations.

### 8.9 Object Well-Formedness Validation (WS-T Phase T5)

Every kernel object has a decidable well-formedness predicate:

- **`KernelObject.wellFormed`**: Validates structural constraints (CNode guard
  bounds, VSpace permission compliance, TCB register consistency, endpoint queue
  integrity).
- **`lifecycleRetypeWithCleanup`**: Enforces well-formedness at object creation
  via the decidable validator.
- **Intrusive queue cleanup**: `spliceOutMidQueueNode` patches predecessor and
  successor links when removing mid-queue nodes, maintaining doubly-linked list
  integrity.

### 8.10 Checked Dispatch and MMIO Adapter (WS-T Phase T6)

- **Checked dispatch**: `dispatchWithCapChecked`, `dispatchSyscallChecked`, and
  `syscallEntryChecked` gate all 11 policy-relevant operations through
  `securityFlowsTo` wrappers at runtime (endpointSend/Receive/Call/Reply/ReplyRecv,
  cspaceMint/Copy/Move, notificationSignal/Wait, registerService).
  `checkedDispatch_flowDenied_preserves_state` proves state preservation on flow
  denial. AH1: Checked `.send` now delegates to `endpointSendDualWithCaps`
  (capability transfer) matching the unchecked path.
- **MMIO adapter**: `mmioRead`/`mmioWrite` in `Platform/RPi5/MmioAdapter.lean`
  validate device-region membership. `mmioWrite32`/`mmioWrite64`/`mmioWrite32W1C`
  validate the full byte range of the write (AF3-B: prevents boundary-spill into
  adjacent memory). `MemoryBarrier` inductive (DMB, DSB, ISB) models ARM64
  memory ordering. `mmioAccessAllowed` runtime contract predicate gates access.
- **TLB flush operations**: `tlbFlushByASID`, `tlbFlushByPage`, `tlbFlushAll`
  with state frame proofs for targeted invalidation.

### 8.10.1 Checked Send Capability Transfer (AH1 / H-01)

Prior to AH1, the checked `.send` path (`endpointSendDualChecked`) delegated to
`endpointSendDual` (without capability transfer), while the unchecked path
correctly used `endpointSendDualWithCaps`. This meant IPC messages sent through
the information-flow enforcement layer silently dropped capability transfer on
rendezvous.

**Fix**: `endpointSendDualChecked` now delegates to `endpointSendDualWithCaps`,
adding three parameters (`endpointRights`, `senderCspaceRoot`, `receiverSlotBase`)
and changing the return type to `Kernel CapTransferSummary`. Both checked and
unchecked `.send` paths now perform identical capability transfer semantics.

**Proof impact**: 8 theorems updated across Wrappers.lean, Soundness.lean, and
Operations.lean (NI). The enforcement-NI bridge (`enforcementBridge_to_NonInterferenceStep`)
carries the updated signature. All proofs mechanically verified.

### 8.10.2 Device Memory Execute Permission Validation (AH1 / M-01)

`validateVSpaceMapPermsForMemoryKind` (SyscallArgDecode.lean) was defined and
tested but not wired into the `.vspaceMap` dispatch arm. Device memory regions
could theoretically receive execute permission through the syscall path (undefined
behavior on ARM64).

**Fix**: The `.vspaceMap` dispatch in `dispatchCapabilityOnly` now calls
`validateVSpaceMapPermsForMemoryKind` after decode and before mapping. Device
regions with `perms.execute = true` return `.error .policyDenied`.

### 8.10.3 seL4 Divergence: CNode Intermediate Rights (M-06)

`resolveCapAddress` (Operations.lean:85-128) does NOT check `Read` rights
on intermediate CNode capabilities during multi-level CSpace traversal.
This diverges from seL4, which requires `Read` on each intermediate CNode.

**Impact**: A thread with only `Write` right on an intermediate CNode can
still resolve capabilities through it, broadening the access path. However,
no additional *operations* become accessible — rights are still checked at
the leaf capability by the individual operation handler.

**Rationale**: seLe4n uses a single-resolution-per-syscall model where each
syscall resolves exactly one capability path. The intermediate rights check
in seL4 guards against multi-hop traversals that could bypass CNode access
control; in seLe4n's flat model, this guard is redundant.

**Source annotation**: U-M25 (Operations.lean).

### 8.10.4 IPC Extra Capability Resolution — Silent-Drop Semantics (AI6 / M-02)

`resolveExtraCaps` (API.lean) resolves sender-specified capability addresses
to actual capabilities for IPC transfer. Capabilities that fail resolution
(invalid CPtr, missing slot, empty slot) are **silently dropped** — the
returned array contains only successfully resolved capabilities.

**seL4 equivalence**: This matches the seL4 C kernel's `lookupExtraCaps`
behavior, which silently discards unresolvable capabilities and returns
only valid ones in the IPC buffer. The receiver observes fewer extra caps
than the sender specified; the count is available via `MessageInfo.extraCaps`.

**Security**: No information leak — failed resolutions produce no observable
side effect. The receiver can detect drops by comparing the resolved count
against the sender's declared count.

**Source**: API.lean:409-416, inline comment AC3-D / API-01.

### 8.10.5 IPC Buffer Overflow Merge for Syscall Arguments (AK4 / R-ABI-C01)

The ARM64 default register layout (`SeLe4n.arm64DefaultLayout`) provides
four inline message-register positions — `x2`, `x3`, `x4`, `x5`. Syscalls
whose `MessageInfo.length > 4` encode the additional message registers into
the caller's IPC buffer (a per-thread virtual memory region whose base VA
is stored in `TCB.ipcBuffer`). The kernel decode step merges the overflow
into the `msgRegs` array before per-syscall argument decode runs.

**Two affected syscalls in the v0.29 ABI:**

| Syscall ID | Name | Arg count | Inline regs | Overflow regs |
|------------|------|-----------|-------------|---------------|
| 11 | `serviceRegister` | 5 | `x2..x5` | `MR[4]` |
| 17 | `schedContextConfigure` | 5 | `x2..x5` | `MR[4]` |

**Decode pipeline:**

1. Register-only decode (`decodeSyscallArgs`) populates `msgRegs` from
   the inline GPR positions (`x2..x5` = 4 entries on ARM64).
2. State-aware wrapper (`decodeSyscallArgsFromState`) inspects
   `msgInfo.length`:
   - If `length ≤ 4`, no overflow is consulted. `inlineCount = 4`,
     `overflowCount = 0`.
   - If `length > 4`, `length − 4` additional slots are read via
     `ipcBufferReadMr` from the caller's IPC buffer. The overflow results
     are appended to `msgRegs` and `overflowCount = length − 4`.

**IPC-buffer layout:** The thread's IPC buffer starts at
`tcb.ipcBuffer : VAddr`; overflow slot `i` (0-indexed) lives at byte
offset `i * 8`. This mirrors `rust/sele4n-abi/src/ipc_buffer.rs`
(`OVERFLOW_SLOTS = 116`, each slot is `u64`).

**Failure modes — all collapse to `KernelError.invalidMessageInfo`**
(matches seL4 behaviour: the caller sees a single error kind regardless of
classification):

| Internal `IpcBufferReadError` | User-visible error |
|-------------------------------|---------------------|
| `threadNotFound` | `.invalidMessageInfo` |
| `vspaceRootInvalid` | `.invalidMessageInfo` |
| `ipcBufferVAddrUnmapped` | `.invalidMessageInfo` |
| `overflowIndexOutOfRange` | `.invalidMessageInfo` |

**Read-only / NI:** `ipcBufferReadMr` and `decodeSyscallArgsFromState`
never modify `SystemState`. Every IPC-buffer read is parameterised by the
caller's `ThreadId`; no other thread's state is consulted. This guarantees
that a 5-arg syscall cannot leak cross-domain data through the overflow
channel.

**Source**:
- `SeLe4n/Kernel/Architecture/IpcBufferRead.lean` —
  `ipcBufferReadMr`, `IpcBufferReadError`.
- `SeLe4n/Kernel/Architecture/RegisterDecode.lean` —
  `decodeSyscallArgsFromState`.
- `SeLe4n/Kernel/API.lean` — `syscallEntry`, `syscallEntryChecked`.

### 8.10.6 IPC Capability-Transfer NI Symmetry (AK1-I + WS-RC R1 / DEEP-IPC-03)

The three IPC capability-transfer wrappers in
`SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean` —
`endpointSendDualWithCaps`, `endpointReceiveDualWithCaps`, and
`endpointCallWithCaps` — all read the dequeued peer's `cspaceRoot`
via `lookupCspaceRoot` after the rendezvous. When that lookup
returns `none` (the dequeued peer's TCB is missing or has been
corrupted to a non-TCB object — a structural fault excluded on the
normal IPC path by `intrusiveQueueWellFormed` + `tcbQueueLinkIntegrity`,
the dual-queue sub-clauses of `dualQueueSystemInvariant` /
`ipcInvariantFull`), the wrappers must fail closed identically;
otherwise an attacker observing kernel-result shapes from two
domains can use the disagreement as a covert channel via
`KernelError`.

AK1-I (I-M07) brought `endpointSendDualWithCaps` and
`endpointReceiveDualWithCaps` to fail closed with
`.error .invalidCapability` on this fault. WS-RC R1 (DEEP-IPC-03)
extends the same fail-closed shape to `endpointCallWithCaps`,
which previously returned `.ok ({ results := #[] }, st')` on the
same fault. After WS-RC R1, all three wrappers return
`.error .invalidCapability` on the missing-CSpace-root branch and
the per-domain covert channel via `KernelError` is closed.

The two adjacent `| none =>` arms in each wrapper (for
`ep.receiveQ.head = none` and `getEndpoint? = none`) intentionally
remain `.ok` because they encode an unrelated invariant ("no
receiver enqueued ≠ missing CSpace root"). All three wrappers
preserve this distinction symmetrically.

**Proof impact**: `endpointCallWithCaps_preserves_ipcInvariant`
(`SeLe4n/Kernel/IPC/Invariant/CallReplyRecv/ReplyRecv.lean`) was
updated so the `lookupCspaceRoot = none` arm becomes vacuous via
`simp [hLookup] at hStep`, matching the post-AK1-I send-path
tactic. The full-invariant theorem
`endpointCallWithCaps_preserves_ipcInvariantFull` in
`Structural/DualQueueMembership.lean` forwards through unchanged.

**Test coverage**: `tests/InformationFlowSuite.lean` AK1-I
regression extended for send/receive/call symmetry;
`tests/NegativeStateSuite.lean::runR1IpcCallPathSymmetryChecks`
provides three runtime-observable checks (healthy state, faulty
state must error, `lookupCspaceRoot` returns `none`).

### 8.10.7 Structural-Fix Discharge Index (WS-RC R4)

WS-RC R4 (Structural-invariant promotions —
[`docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md)
§8) lands four sub-tasks under the structural-fix policy (`§1.5` of
the WS-RC plan).  **All four sub-tasks are COMPLETE** with full
type-level structural promotion:

* **R4.A (DEEP-MODEL-01)** — `CNode.slots : RHTable Slot Capability`
  → `CNode.slots : SeLe4n.UniqueSlotMap Capability`.  The wrapper
  (`SeLe4n/Model/Object/UniqueSlotMap.lean`) carries
  `RHTable.invExtK` (no-duplicate-keys ∧ `size < capacity` ∧
  `4 ≤ capacity`) **structurally** at construction time via the
  smart constructors `empty`, `insert`, `erase`, `filter`, and
  `ofListWF`.  The state-level `cspaceSlotUnique` invariant is now
  **trivially derivable** via `SeLe4n.Model.CNode.slotsUnique_holds :
  ∀ (cn : CNode), cn.slotsUnique` (a one-liner projection of
  `cn.slots.hWF`).  The corresponding preservation theorems
  (`empty/insert/remove/revokeTargetLocal_slotsUnique`) likewise
  collapse to projections of the smart-constructor result's
  `hWF` field.  Structural witness theorem
  `SeLe4n.UniqueSlotMap.keys_unique`.
* **R4.B (DEEP-CAP-04)** — `RetypeTarget` non-bypassable
  construction.  The `cleanupHookDischarged` predicate requires an
  opaque `ScrubToken` whose only public introduction is
  `SeLe4n.Kernel.ScrubToken.fromCleanup`, gated on a successful
  `lifecyclePreRetypeCleanup` outcome.  No-bypass property codified
  by `SeLe4n.Kernel.retypeTarget_implies_scrub_token_held :
  ∀ st (rt : RetypeTarget st), SeLe4n.Kernel.ScrubToken st rt.id`.
  Defined in `SeLe4n/Kernel/Capability/Invariant/Defs.lean`.
* **R4.C (DEEP-IPC-05; subsumes DEEP-IPC-01)** —
  `Notification.waitingThreads : List ThreadId` →
  `Notification.waitingThreads : SeLe4n.NoDupList SeLe4n.ThreadId`.
  The wrapper (`SeLe4n/Model/Object/NoDupList.lean`) carries
  `List.Nodup` **structurally** at construction time.  `notificationSignal`
  pops via `NoDupList.tail?`; `notificationWait` cons site is
  gated by `NoDupList.consWithGuard?` (runtime membership check
  returning `Option`) so the duplicate rejection at line 723 is
  structural rather than upstream-convention.  The state-level
  `uniqueWaiters` invariant is now **trivially derivable** via
  `SeLe4n.Kernel.uniqueWaiters_holds`.  Structural witness theorems:
  `SeLe4n.NoDupList.nodup_witness`,
  `SeLe4n.Kernel.notification_waitingThreads_nodup_witness`, and
  `SeLe4n.Kernel.notificationWait_runtime_check_implied_by_nodup`.
* **R4.D (DEEP-CAP-02)** — `cspaceMutate` null-cap rejection.  Two
  witness theorems in
  `SeLe4n/Kernel/Capability/Invariant/Preservation/CopyMoveMutate.lean`:
  `cspaceMutate_rejects_null_cap` (every successful mutation
  witnesses a non-null pre-state capability) and
  `cspaceMutate_null_cap_rejected` (every null-cap input totalises
  to `.nullCapability`).  Regression tests in both
  `tests/ModelIntegritySuite.lean::cspaceMutate_from_null_rejected`
  and `tests/NegativeStateSuite.lean::NEG-MUTATE-NULL`.

The R4 closure-form discharge index is anchored by
`SeLe4n.Kernel.r4_structural_fix_discharge_index_documented` in
`SeLe4n/Kernel/CrossSubsystem.lean`, with cross-references to the
canonical
[`docs/audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md`](../audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md)
§3 (sections D/E/F).  Companion foundation-readiness markers:
`SeLe4n.Kernel.uniqueSlotMap_module_ready` and
`SeLe4n.Kernel.noDupList_module_ready`.

### 8.10.8 Scheduler / Lifecycle Behaviour Symmetry (WS-RC R5)

WS-RC R5 closes the seven scheduler/lifecycle audit findings whose
remediation is a behavioural symmetry or function-split. The phase
implements seven coherent slices (R5.A..R5.G) and lands them on the
v0.31.0 release path; see
[`docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md)
§9 for the canonical task breakdown and the closure record in
[`docs/WORKSTREAM_HISTORY.md`](../WORKSTREAM_HISTORY.md) `WS-RC R5`
for the per-sub-task narrative.

* **R5.A (DEEP-SUSP-02) — `cancelDonation` split**: the suspend G3
  step's `cancelDonation` is split into `cancelBoundDonation` (in-place
  unbind) and `cancelDonatedDonation` (return-to-original-owner via
  `cleanupDonatedSchedContext`); the original name survives as a thin
  dispatcher.  Source: `SeLe4n/Kernel/Lifecycle/Suspend.lean`.  Six
  new preservation theorems in
  `SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean`.
* **R5.B (DEEP-SUSP-01) — PIP recomputation on resume**: `resumeThread`
  re-derives `pipBoost` from the post-suspend blocking graph via
  `PriorityInheritance.computeMaxWaiterPriority`.  Three structural
  witnesses (`restoreToReady_objectIndex_eq`,
  `restoreToReady_objects_eq_at_tid`,
  `resumeThread_pipBoost_consistent_post_restore`) in
  `SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean`.
* **R5.C (DEEP-SCH-02) — `effectivePriority` API uniformity**: new
  total form `effectiveSchedParams` returning
  `Priority × Deadline × DomainId`; bridge witness
  `effectiveSchedParams_priority_deadline_eq_resolve` in
  `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`.  **R5.C.1 full
  deprecation (v0.31.2)**: the partial `effectivePriority` def + 3
  helper theorems + bridge `effectivePriority_some_eq_effectiveSchedParams`
  are RETIRED.  All callers (`TraceModel.lean`, `Preservation.lean`,
  `PriorityInheritanceSuite.lean`) migrated to `effectiveSchedParams`.
* **R5.D (DEEP-SCH-03) — shared `restoreToReady` helper**: the
  IPC-state-clearing transition shared between `cancelIpcBlocking`
  (suspend G2) and `resumeThread` (H3) extracted as `restoreToReady`
  (`SeLe4n/Kernel/Lifecycle/Suspend.lean`).  The private
  `clearTcbIpcFields` retained as a `@[inline]` back-compat shim with
  `clearTcbIpcFields_eq_restoreToReady` bridging the two names for
  proof discharge.
* **R5.E (DEEP-SCH-04) — surface `.missingSchedContext`**:
  `timerTickBudget` rejects with `KernelError.missingSchedContext`
  (new discriminant 52) when a bound-budget thread references an
  absent SchedContext, replacing the pre-R5 silent `(state, false)`
  no-preempt fallback.  The Rust `KernelError` enum mirror in
  `rust/sele4n-types/src/error.rs` grows in lock-step (range
  0..=52, sentinel range 53..=254).  Mirrored in
  `FrozenOps.frozenTimerTickBudget` for cross-phase consistency.
* **R5.F (DEEP-SCH-05) — explicit `rotateToBack` precondition**:
  two new assertion theorems
  (`rotateToBack_requires_membership`,
  `rotateToBack_priority_eq_threadPriority`) in
  `SeLe4n/Kernel/Scheduler/RunQueue.lean` discharge the
  membership precondition formally.  Function definition unchanged.
* **R5.G (DEEP-SCH-06) — domain propagation in
  `schedContextConfigure`**: domain-propagation block mirroring the
  existing priority-propagation block, closing the
  `boundThreadDomainConsistent` invariant-drift path.  Two witness
  theorems in `SeLe4n/Kernel/SchedContext/Invariant/Preservation.lean`
  (`schedContextConfigure_bound_tcb_domain_eq`,
  `schedContextConfigure_domain_noop_when_eq`).

R5 test coverage: 4 + 2 + 2 + 3 + 1 = 12 new Lean regression tests
(in `SuspendResumeSuite`, `PriorityManagementSuite`,
`NegativeStateSuite`), 1 new discriminant pin in
`SyscallDispatchSuite`, 23 surface anchors in `LivenessSuite`, and 2
new Rust tests (`decode_missing_sched_context_error` unit,
`missing_sched_context_decode` conformance).  AK7 cascade monotonicity
baseline retained at the v0.30.11 floor.

### 8.11 buildChecked Runtime Invariant Validation (WS-T Phase T7)

All test states use `BootstrapBuilder.buildChecked` instead of `build`:

- **Runtime structural validation**: No duplicate ObjIds, lifecycle type-tag
  matching, runnable threads reference existing TCBs, CNode capacity bounds,
  current thread in runnable list.
- **31 post-mutation invariant checks** in the trace harness covering all
  major transition families (IPC, VSpace, lifecycle, scheduler, capability).

### 8.12 Scheduling Context Objects (WS-Z)

A `SchedContext` is a first-class kernel object containing CPU budget, period,
priority, deadline, and domain parameters for CBS (Constant Bandwidth Server)
scheduling. Threads bind to SchedContexts via the `schedContextBinding` field
(unbound | bound | donated). The `threadSchedulingParams` accessor resolves
effective scheduling parameters from the bound SchedContext or falls back to
legacy TCB fields.

Key types: `Budget` (CPU time in ticks), `Period` (replenishment period),
`Bandwidth` (budget/period pair for admission control), `ReplenishmentEntry`
(CBS replenishment event), `SchedContextBinding` (thread ↔ SchedContext relationship).

#### 8.12.1 CBS Budget Engine (WS-Z Phase Z2)

The CBS budget engine (`Kernel/SchedContext/Budget.lean`) provides pure-function
budget management operations with machine-checked invariants:

- **Budget consumption**: `consumeBudget` decrements `budgetRemaining` with
  saturating arithmetic (cannot go negative). `isBudgetExhausted` detects
  zero remaining budget.
- **Replenishment scheduling**: `scheduleReplenishment` creates a
  `ReplenishmentEntry` eligible one period in the future and truncates the
  replenishment list to `maxReplenishments` (= 8).
- **Replenishment processing**: `processReplenishments` partitions the
  replenishment list by eligibility time, sums eligible amounts, and refills
  `budgetRemaining` capped at the configured `budget` ceiling via `applyRefill`.
  `applyRefill` also synchronizes `isActive` to reflect whether budget is positive.
- **CBS deadline rule**: `cbsUpdateDeadline` assigns `deadline := currentTime +
  period` when a SchedContext is replenished after budget exhaustion.
- **Combined entry point**: `cbsBudgetCheck` composes consume → exhaust check →
  replenishment scheduling → processing → deadline update into a single
  atomic step returning `(updatedSc, wasPreempted)`.
- **Admission control**: `admissionCheck` verifies that adding a new SchedContext
  does not exceed total utilization of 1000 per-mille (100% bandwidth).

Invariants (`Kernel/SchedContext/Invariant/Defs.lean`):
- `budgetWithinBounds`: `budgetRemaining ≤ budget ≤ period`
- `replenishmentListWellFormed`: bounded length, no zero-amount entries
- `replenishmentAmountsBounded`: each entry's amount ≤ configured budget
- `schedContextWellFormed`: 4-conjunct bundle (`wellFormed ∧ budgetWithinBounds ∧
  replenishmentListWellFormed ∧ replenishmentAmountsBounded`)

16 preservation theorems (4 operations × 4 sub-invariants) prove that all CBS
operations maintain the invariant bundle, composed into
`cbsBudgetCheck_preserves_schedContextWellFormed` (bundled) and
`cbsBudgetCheck_preserves_replenishmentAmountsBounded` (standalone).
Bandwidth isolation theorems (`cbs_single_period_bound`, `cbs_bandwidth_bounded`)
bound total consumption by `maxReplenishments × budget`.

#### 8.12.2 Replenishment Queue (WS-Z Phase Z3)

The system-wide `ReplenishQueue` (`Kernel/SchedContext/ReplenishQueue.lean`)
tracks when each SchedContext's budget becomes eligible for refill. The queue
is a sorted list of `(SchedContextId, eligibleAt)` pairs with a cached `size`
field, enabling O(1) `peek`/`hasDue` and O(k) `popDue` (prefix split).

Operations: `insert` (sorted O(n)), `popDue` (prefix split O(k)), `remove`
(filter O(n)). Invariants: `pairwiseSortedBy` (recursive adjacency predicate),
`replenishQueueSorted`, `replenishQueueSizeConsistent`, `replenishQueueConsistent`
(parameterized by object store lookup). 13 preservation/membership theorems
including `insert_preserves_sorted`, `popDue_preserves_sorted`,
`splitDue_length_additive`, `mem_insertSorted`.

#### 8.12.3 Scheduler Integration (WS-Z Phase Z4)

The CBS budget engine and replenishment queue are wired into the scheduler via
`effectiveSchedParams` (the total successor to the retired
`effectivePriority`; resolves scheduling params from SchedContext if bound, TCB
fields if unbound), `hasSufficientBudget` (budget eligibility predicate),
`chooseThreadEffective` (budget-filtered selection chain), and `timerTickBudget`
(3-branch: unbound legacy / bound decrement / bound exhaustion+preempt).

6 new invariants: `budgetPositive`, `currentBudgetPositive`,
`schedContextsWellFormed`, `replenishQueueValid`, `schedContextBindingConsistent`,
`effectiveParamsMatchRunQueue`, `boundThreadDomainConsistent` (AE3-A: enforces
`tcb.domain = sc.domain` for all bound thread-SchedContext pairs). Extended
bundle: `schedulerInvariantBundleExtended` (16-tuple: original 9 + 7 new).
Backward compatible: existing `chooseThread`/`schedule`/`timerTick`/`handleYield`
preserved unchanged.

#### 8.12.4 Capability-Controlled Thread Binding (WS-Z Phase Z5)

3 new `SyscallId` variants: `.schedContextConfigure` (17), `.schedContextBind`
(18), `.schedContextUnbind` (19). Capability-gated operations:
`validateSchedContextParams`, `schedContextConfigure` (validate + admit + store),
`schedContextBind` (bidirectional TCB↔SchedContext binding + RunQueue
re-insertion + domain consistency enforcement: `tcb.domain == sc.domain`
required), `schedContextUnbind` (unbind + preemption guard + RunQueue
removal), `schedContextYieldTo` (kernel-internal budget transfer). 7
preservation theorems including `schedContextBind_output_bidirectional` and
`schedContextConfigure_admission_excludes_eq`. API dispatch via
`dispatchCapabilityOnly` shared path.

#### 8.12.5 API Surface & Syscall Wiring (WS-Z Phase Z8)

3 error-exclusivity theorems (`decodeSchedContextConfigureArgs_error_iff`,
`decodeSchedContextBindArgs_error_iff`, `decodeSchedContextUnbindArgs_error_iff`).
4 frozen SchedContext operations (`frozenSchedContextConfigure`,
`frozenSchedContextBind`, `frozenSchedContextUnbind`, `frozenTimerTickBudget`).
`enforcementBoundary` expanded 22→25 entries (3 new `.capabilityOnly` SchedContext
operations). `frozenOpCoverage_count` increased 12→15.

#### 8.12.6 Invariant Composition & Cross-Subsystem (WS-Z Phase Z9)

3 new cross-subsystem predicates: `schedContextStoreConsistent` (every
SchedContext in the object store satisfies `schedContextWellFormed`),
`schedContextNotDualBound` (no SchedContext simultaneously bound to two threads),
`schedContextRunQueueConsistent` (RunQueue threads have bound SchedContext with
positive budget or are legacy-unbound). `crossSubsystemInvariant` extended from
5 to 8 predicates. `proofLayerInvariantBundle` extended from 9 to 10 conjuncts
(added `schedulerInvariantBundleExtended`). `bootSafeObject` extended with
SchedContext `schedContextWellFormed` requirement (6th conjunct). Field-
disjointness: 16 pairwise witnesses for 8 predicates, 3 new frame lemmas.

### 8.7 SchedContext Donation (Z7)

SchedContext donation enables **passive servers** — threads that consume zero
CPU when idle by borrowing the client's SchedContext during IPC Call/Reply.

**Protocol**: (1) Client calls server via `endpointCall`. If server is passive
(`.unbound`), client's SchedContext is donated via `donateSchedContext`. (2)
Server executes on client's budget. (3) Server replies via `endpointReply` —
`returnDonatedSchedContext` returns the SC to the original owner. (4) Server
becomes passive (`.unbound`, removed from RunQueue).

**Architecture**: Donation is implemented as post-processing in the API dispatch
layer (`API.lean`), preserving all existing IPC invariant proofs unchanged. Core
IPC functions (`endpointCall`, `endpointReply`, `endpointReplyRecv`) are not
modified. Key helpers: `donateSchedContext`, `returnDonatedSchedContext`,
`applyCallDonation`, `applyReplyDonation`, `cleanupPreReceiveDonation`.

**Error propagation** (AH2-A/B, v0.27.3): `applyCallDonation` and
`applyReplyDonation` return `Except KernelError SystemState` (not bare
`SystemState`). Errors from `donateSchedContext` are propagated to callers
instead of being silently swallowed. All 7 call sites in `API.lean` and
`Donation.lean` use match-based error handling. Preservation theorems
(`applyCallDonation_scheduler_eq`, `applyCallDonation_machine_eq`,
`applyReplyDonation_machine_eq`, `applyCallDonation_preserves_projection`)
carry an explicit `h : ... = .ok st'` success hypothesis.

**Invariants** (`ipcInvariantFull` 15 conjuncts after WS-RC R4.C.7 close-out
retired the `uniqueWaiters` state-level slot to a structural witness on
`Notification.waitingThreads : SeLe4n.NoDupList ThreadId`):
- `donationChainAcyclic`: no circular donation chains (A→B and B→A)
- `donationOwnerValid`: donated bindings reference valid objects with
  bidirectional consistency (`sc.boundThread = some server`,
  `owner.schedContextBinding = .bound scId`, `owner.ipcState = .blockedOnReply`)
- `passiveServerIdle`: unbound non-runnable threads are ready/receiving
- `donationBudgetTransfer`: at most one thread per SchedContext
- `uniqueWaiters` (RETIRED at WS-RC R4.C.7): no notification has duplicate
  thread IDs in `waitingThreads` (AG1-C, F-T02) — content now carried
  structurally by `NoDupList.hNodup` on every `Notification.waitingThreads`.
  The state-level predicate is retained as a `True` alias for backward
  compatibility with vestigial hypothesis parameters; discharge via
  `SeLe4n.Kernel.uniqueWaiters_trivial` or the per-Notification
  `SeLe4n.Kernel.notification_waiters_nodup` witness.

**Production receive cleanup** (AI4-A, v0.27.11): `cleanupPreReceiveDonation` is
wired into the `endpointReceiveDual` no-sender branch (Transport.lean). When a
server blocks on `.receive` without having replied to a prior `.call`, the stale
donated SchedContext is returned to the original owner before blocking. This
prevents SchedContext leaks on the abnormal receive-without-reply path. The
function is defined in Endpoint.lean (co-located with `returnDonatedSchedContext`)
and called before `endpointQueueEnqueue`. On the common path (no stale donation),
it returns `st` unchanged — zero overhead.

**Lifecycle**: `cleanupDonatedSchedContext` in `lifecyclePreRetypeCleanup`
returns donated SchedContexts before TCB destruction. AJ1-A (M-14): errors from
`returnDonatedSchedContext` are propagated (not silently swallowed), preventing
retype from proceeding with dangling SchedContext references.

**Defense-in-depth**: `donateSchedContext` validates `sc.boundThread = some
clientTid` before transferring ownership.

### 8.13 Priority Inheritance Protocol (WS-AB Phase D4)

Priority inversion via Call/Reply IPC is mitigated by a deterministic Priority
Inheritance Protocol (PIP). When a client blocks on a server via `Call`, the
server's effective scheduling priority is transiently elevated to match the
highest-priority client transitively waiting on it.

**TCB field**: `pipBoost : Option Priority := none`. When `some p`, the
thread's effective priority is `max(SchedContext.priority, p)`.

**Blocking graph**: `blockedOnThread` (direct blocking via `blockedOnReply`),
`waitersOf` (all direct waiters), `blockingChain` (transitive upward walk).
Acyclicity is a system-level invariant (`blockingAcyclic`); chain depth is
bounded by `objectIndex.length`.

**Operations**:
- `computeMaxWaiterPriority`: maximum effective priority among direct waiters
- `updatePipBoost`: single-thread pipBoost recompute + conditional run queue migration
- `propagatePriorityInheritance`: chain walk applying updatePipBoost at each step
- `revertPriorityInheritance`: structurally identical to propagation (same updatePipBoost)

**Integration points**:
- `endpointCallWithDonation`: propagates PIP after Call completes (D4-L)
- `endpointReplyWithDonation`: reverts PIP after Reply unblocks client (D4-M)
- `endpointReplyRecvWithDonation`: reverts PIP for ReplyRecv (D4-M)
- `suspendThread`: reverts PIP before cleanup pipeline (D4-N)
- `timeoutThread`: reverts PIP when timed-out client was in `blockedOnReply` (D4-N)
- API dispatch (Call/Reply/ReplyRecv): PIP propagation/reversion applied inline
  for both enforced (`dispatchWithCapChecked`) and non-enforced (`dispatchWithCap`)
  paths, ensuring consistent behavior regardless of information-flow enforcement

**Composition with SchedContext donation (Z7)**: `effectiveSchedParams`
(the total successor to the retired `effectivePriority`) computes
`max(scPrio, pipBoost)`, so PIP provides an additional boost when the transitive
client priority exceeds the donated SchedContext priority.

**Bounded inversion**: Priority inversion is bounded by
`objectIndex.length × WCRT(effectiveSchedParams)` ticks (parametric in WCRT).

### 8.14 Bounded Latency Theorem (WS-AB Phase D5)

The kernel's first machine-checked liveness property: a conditional worst-case
response time (WCRT) bound for the CBS-aware, PIP-enhanced scheduler. This is a
proof-only phase with zero kernel code changes.

**Trace model** (`Kernel/Scheduler/Liveness/TraceModel.lean`): `SchedulerStep`
inductive (9 constructors covering all scheduler transitions), `SchedulerTrace`
(list of step-state pairs), `validTrace` predicate (each step's precondition
holds and postcondition feeds into the next step). Query predicates:
`selectedAt`, `runnableAt`, `budgetAvailableAt`. Counting functions:
`countHigherOrEqualEffectivePriority`, `maxBudgetInBand`, `maxPeriodInBand`.

**Per-mechanism bounds**:
- Timer-tick budget: `timerTickBudget_bound_succeeds` / `timerTickBudget_donated_succeeds` characterize Z4-F2/F3 budget decrement and exhaustion-preemption branches
- Replenishment: `replenishment_within_period` bounds the dead time between budget exhaustion and replenishment by `sc.period`
- Yield/FIFO: `fifo_progress_in_band` proves a thread at position `k` in its priority bucket is selected within `k * max_preemption_interval` ticks
- Domain rotation: `domainRotationTotal_le_bound` proves every domain receives CPU within `D * L_max` ticks

**WCRT theorem** (`Kernel/Scheduler/Liveness/WCRT.lean`): `WCRTHypotheses`
structure encodes the preconditions (thread runnable with budget, domain
membership, higher-priority thread count N, budget bound B, period bound P).
The main theorem `wcrtBound_unfold` / `bounded_scheduling_latency_exists` proves:

> WCRT = D * L_max + N * (B + P)

where D is the domain schedule length, L_max is the maximum domain entry length,
N is the count of higher-or-equal effective priority threads, B is the maximum
budget, and P is the maximum period in the priority band.

**PIP enhancement**: `countHigherOrEqual_mono_threshold` proves that PIP-boosted
threads have fewer higher-priority competitors (monotonicity in threshold).
`pip_enhanced_wcrt_le_base` proves the PIP-enhanced WCRT bound is tighter than
the base bound. This closes the previously parametric WCRT in D4's bounded
inversion theorem.

**Evidence**: 58 surface anchor tests in `tests/LivenessSuite.lean`. Zero
sorry/axiom.

### 8.14.1 WCRT Externalized Hypotheses (AI6 / M-24, M-25)

The WCRT theorem `bounded_scheduling_latency_exists` requires two externalized
hypotheses that encode runtime properties not mechanically derivable from
kernel invariants:

1. **`hDomainActiveRunnable`** (M-25): The domain scheduler eventually
   activates the target domain with the thread still runnable. This depends on
   domain schedule configuration (all domains receiving non-zero time) and
   thread behavior (not entering a permanent block before domain activation).

2. **`hBandProgress`** (M-25): Once the domain is active and the thread is
   runnable, higher-priority thread preemption completes within the CBS budget
   bound `N × (B + P)`. This depends on CBS admission control and the
   `eventuallyExits` hypothesis (below).

**Sub-dependency — `eventuallyExits`** (M-24): `hBandProgress` internally
relies on `eventuallyExits`, which asserts that every higher-priority thread
eventually leaves the run queue. For CBS-bound threads, this should follow
from budget finiteness (`consumeBudget` monotonic decrease). For unbound
threads, this is NOT satisfiable without an external progress assumption
(e.g., all threads eventually block, yield, or complete). Deriving this
from CBS budget finiteness for bound threads is future work.

**Deployment obligation**: These hypotheses are deployment-time validation
requirements. Deployers must verify them for their specific workload and
domain schedule configuration. The kernel provides the mechanism; the
deployment provides the guarantee.

**Source**: WCRT.lean:167-187, BandExhaustion.lean:34-43.

### 8.14.1.1 RPi5 Canonical Deployment Specialisation (AN5-E / DEF-AK2-K.4 RESOLVED)

AN5-E discharges the `eventuallyExits` hypothesis substantively for the
canonical Raspberry Pi 5 deployment configuration. The closure is
formalised in `SeLe4n/Kernel/Scheduler/Liveness/RPi5CanonicalConfig.lean`.

**Two-tier WCRT semantics**:

1. **General theorem** (`bounded_scheduling_latency_exists` in
   `Liveness/WCRT.lean`): the WCRT bound `D × L_max + N × (B + P)` is
   proven modulo the externalised `hDomainActiveRunnable` and
   `hBandProgress` hypotheses described in §8.14.1. Applies to any
   deployment platform.

2. **RPi5-canonical specialisation** (`wcrt_bound_rpi5` in
   `Liveness/RPi5CanonicalConfig.lean`): for deployments matching
   `rpi5CanonicalConfig` (54 MHz timer, 10 000-tick CBS period, 256
   priority bands, 16 domains, 1000-tick default time-slice, 750 ‰
   admission utilisation), the `eventuallyExits` sub-hypothesis is
   discharged by `rpi5_canonicalConfig_eventuallyExits`. The theorem
   consumes a `CanonicalDeploymentProgress` witness — a deployment
   obligation that the trace contains an exit event for the thread — and
   composes `eventuallyExits_of_exit_index` to produce the substantive
   `eventuallyExits` conclusion.

**DeploymentSchedulingConfig schema** (`RPi5CanonicalConfig.lean`):

* `timerFrequencyHz : Nat` — hardware timer tick rate (must be positive).
* `cbsPeriodTicks : Nat` — CBS replenishment period in timer ticks (must
  be positive).
* `maxPriorityBands : Nat` — priority-band count (256 on RPi5 per seL4
  MCS).
* `maxDomains : Nat` — domain scheduler capacity (16 on RPi5 per
  `numDomainsVal`).
* `configDefaultTimeSlice : Nat` — default time-slice quantum (must be
  positive).
* `admissibleUtilisation : Nat` — aggregate CBS admission ceiling in
  per-mille. A well-formed config has `admissibleUtilisation ≤ 1000`;
  canonical deployments typically set ≤ 750 to leave headroom for
  kernel / interrupt overhead.

**Runtime canonical check**: `isRPi5CanonicalConfig c` is a decidable
predicate that deployments can invoke at boot time to classify the
deployment into (a) canonical-specialisation mode (uses
`wcrt_bound_rpi5` — the `eventuallyExits` discharge applies
automatically from a progress witness) or (b) general parameterised
mode (uses `bounded_scheduling_latency_exists` — deployer supplies both
externalised hypotheses as before).

**DEF-AK2-K.4 status**: RESOLVED in AN5-E. The general theorem retains
the parameterised `eventuallyExits` form for future non-RPi5 platforms.
The RPi5 canonical deployment (v1.0.0 release target) ships with the
hypothesis discharged via the `CanonicalDeploymentProgress` witness.

**CBS bandwidth witness** (AN5-D / SC-M01): alongside the WCRT closure,
`rpi5_cbs_window_replenishments_bounded` instantiates the
`cbs_bandwidth_bounded_tight` (AK6-I) conditional for any SchedContext
whose period matches `rpi5CanonicalConfig.cbsPeriodTicks = 10 000`. This
gives deployments a tight `budget × ⌈window / 10 000⌉` consumption bound
once they pass admission control, replacing the conservative 8× loose
bound in `cbs_bandwidth_bounded`.

**Source**: `Scheduler/Liveness/RPi5CanonicalConfig.lean`; 13 surface
anchors + 5 runtime witnesses in `tests/LivenessSuite.lean`.

### 8.14.2 Boot Invariant Bridge Scope (AI6 / M-07)

`bootToRuntime_invariantBridge_empty` (Boot.lean) proves that the full
10-component `proofLayerInvariantBundle` holds after booting with an empty
`PlatformConfig`. For non-empty configs (real hardware with IRQ tables,
pre-allocated objects), the full bundle is NOT proven to hold.

The checked boot path `bootFromPlatformChecked` validates per-object
well-formedness (uniqueness via `wellFormed`) AND structural boot safety
(via `bootSafeObjectCheck`, added in AJ3-C). The `bootSafeObjectCheck`
Bool-valued function verifies empty endpoint queues, idle notifications,
CNode bounds, clean TCB state, **boot-safe VSpaceRoot admission**
(WS-RC R3 / DEEP-BOOT-01), and SchedContext well-formedness. A
soundness bridge theorem `bootSafeObjectCheck_sound_structural` proves
the Bool check implies the structural conjuncts of `bootSafeObject`
(all except CNode badge validity). The full
`bootFromPlatform_proofLayerInvariantBundle_general` theorem composes
`bootSafe` with boot preservation to discharge the complete 10-component
invariant bundle (with the WS-RC R3 precondition that no VSpaceRoots are
present in `initialObjects` — the canonical boot VSpace is installed
via the dedicated `bootVSpaceRoot` field, not the standard fold).

**WS-RC R3 (DEEP-BOOT-01) — Boot VSpaceRoot threading.**  Pre-R3 the
`.vspaceRoot _ => false` arm of `bootSafeObjectCheck` rendered the
proven-W^X-compliant `rpi5BootVSpaceRoot` data structure inert at boot
time.  R3 (with post-landing audit fixes) closes the gap by:

1. Adding `bootSafeVSpaceRootCheck : VSpaceRoot → Bool` (in
   `Platform/RPi5/VSpaceBoot.lean`) and the equivalence theorem
   `bootSafeVSpaceRootCheck_iff` so the four `VSpaceRootWellFormed`
   conjuncts (asid bounded, every mapping W^X compliant, non-empty
   mappings, paddr bounded) are simultaneously available in Bool
   form (for the runtime check) and Prop form (for the structural
   invariant).
2. Rewriting the `.vspaceRoot` arm of `bootSafeObjectCheck` and
   `bootSafeObject` to admit roots passing the boot-safety
   predicate.
3. Adding the `installBootVSpaceRoot` builder operation to
   `Platform/Boot.lean` that composes `Builder.createObject` with an
   `asidTable` insertion so the boot VSpace is resolvable by ASID
   after boot, mirroring the runtime `storeObject` semantics.
4. Adding the `bootVSpaceRoot : Option BootVSpaceRootEntry := none`
   field to `PlatformConfig`, plus four runtime gates
   (`noVSpaceRootsInInitialObjects` — forbids VSpaceRoots in
   `initialObjects` since `Builder.createObject` doesn't update
   `asidTable`; `bootVSpaceRootObjIdDistinct` — forbids ObjId
   collision with `initialObjects`; `bootVSpaceRootObjIdNonSentinel` —
   forbids the `ObjId.sentinel` value (`⟨0⟩` per Prelude.lean
   H-06/WS-E3); `bootVSpaceRootSafe` — requires the boot root passes
   `bootSafeVSpaceRootCheck`) wired into `bootFromPlatformChecked`.
   When the `bootVSpaceRoot` field is `some entry`, the gated boot
   path installs the entry via `installBootVSpaceRoot` between the
   `initialObjects` fold and the interrupts-enable step.
5. Threading `bootVSpaceRoot := some rpi5BootVSpaceRootEntry` into
   the RPi5 `PlatformBinding` instance (and a parallel
   `simBootVSpaceRoot` into the Sim platform instances), so the
   platform binding now carries the canonical boot VSpace from the
   typeclass.

The correctness theorem
`bootFromPlatformChecked_eq_bootFromPlatform` retains its existing
shape with an additional `bootVSpaceRoot = none` precondition; the
sibling `bootFromPlatformChecked_admits_bootVSpace` covers the
`some entry` case.

**Source**: `Platform/Boot.lean`, `Platform/Contract.lean`,
`Platform/RPi5/VSpaceBoot.lean`, `Platform/RPi5/Contract.lean`,
`Platform/Sim/Contract.lean`.

### 8.14.3 MMIO Model Limitations (AI6 / M-10)

The `mmioRead` function (RPi5/MmioAdapter.lean) returns `st.machine.memory addr`
(RAM semantics) for device addresses. The sequential model does not capture
volatile register behavior:

- **Status registers**: May change between reads (interrupt pending bits, DMA
  completion flags).
- **FIFO registers**: Return different data on each read (UART RX data).
- **Write-one-to-clear registers**: Side effects not modeled in abstract store.

Proofs must use `MmioSafe` or restrict to non-device addresses to avoid
unsound reasoning. A future hardware-binding workstream (tracked per-ID in
[`docs/dev_history/audits/AUDIT_v0.29.0_DEFERRED.md`](../dev_history/audits/AUDIT_v0.29.0_DEFERRED.md))
must substitute actual MMIO reads via the FFI bridge to Rust HAL
(`mmio.rs`).

**Source**: RPi5/MmioAdapter.lean:336-356.

### 8.15 Hardware Integration Roadmap (AJ6-A / H-01, H-02, H-03)

The v0.28.0 comprehensive audit identified three HIGH findings concerning
orphaned architecture modules, inactive budget-aware scheduling, and an
unwired FFI bridge. All three are pre-hardware deployment requirements
deferred to **WS-V (AG10: Hardware Integration)**. This section documents
the activation plans.

#### 8.15.1 Architecture Module Integration (H-01)

Seven architecture modules are implemented and proven but not yet imported
into the main kernel execution path:

1. `ExceptionModel.lean` — ARM64 exception classification and dispatch
2. `InterruptDispatch.lean` — GIC-400 acknowledge→handle→EOI sequence
3. `TimerModel.lean` — Hardware timer binding (54 MHz RPi5)
4. `VSpaceARMv8.lean` — ARMv8 page table shadow with refinement proofs
5. `AsidManager.lean` — ASID pool allocator with uniqueness proof
6. `CacheModel.lean` — D-cache/I-cache coherency model
7. `PageTable.lean` — ARMv8 4-level page table walk with W^X bridge

**Activation steps:**
1. Create `Architecture/HardwareIntegration.lean` hub module importing all 7.
2. Wire `ExceptionModel.dispatchException` into the syscall entry path
   (requires resolving the ExceptionModel→API.lean→ExceptionModel import
   cycle via an interface abstraction or mutual import refactoring).
3. Connect `VSpaceARMv8` as RPi5-specific `VSpaceBackend` instance via
   conditional platform selection.
4. Import `AsidManager` into VSpace subsystem for ASID allocation.
5. Import `TimerModel` into scheduler timer tick path.
6. Import `CacheModel` into Architecture invariant bundle.
7. Add `ArchitectureHardwareSuite.lean` test suite for all 7 modules.

**Dependency:** Resolving the import cycle between ExceptionModel and
API.lean is the gating prerequisite before integration is possible.

#### 8.15.2 Budget-Aware Scheduler Activation (H-02)

The CBS budget engine (`SchedContext/Budget.lean`), replenishment queue
(`SchedContext/ReplenishQueue.lean`), and budget-aware scheduler operations
(`scheduleEffective`, `handleYieldWithBudget`, `timerTickWithBudget`) are
implemented with invariants but not yet wired into the checked API dispatch
path. The current checked wrappers call the non-budget-aware variants.

**Activation steps:**
1. Update `API.lean` checked wrappers: `scheduleChecked` calls
   `scheduleEffective`, `handleYieldChecked` calls `handleYieldWithBudget`,
   `timerTickChecked` calls `timerTickWithBudget`.
2. Add preservation theorems for all three budget-aware operations in
   `Scheduler/Operations/Preservation.lean`.
3. Update NI proofs for the new operation semantics.
4. Add `SchedulerBudgetSuite.lean` test suite exercising CBS enforcement,
   budget consumption, replenishment queue, and timeout-on-budget-expiry.

**Dependency:** Preservation proofs must be complete before activation.

#### 8.15.3 FFI Bridge Wiring (H-03)

`FFI.lean` declares 17 `@[extern]` Lean functions mapping to Rust HAL
(`sele4n-hal/src/ffi.rs`). These declarations exist but are not imported
by any module in the production build chain.

**Activation steps:**
1. Import `FFI.lean` from hardware-specific Architecture modules (or create
   `Platform/HardwareBindings.lean` that selectively imports FFI).
2. Create typeclass-based dispatch that selects FFI-backed implementations
   vs pure-function models based on platform configuration.
3. Verify all 17 FFI function signatures still match `sele4n-hal/src/ffi.rs`.

**Dependency:** Requires H-01 (orphaned modules integrated first).

---

## 9. Non-Negotiable Baseline Contracts

Unless a PR explicitly proposes spec-level change control, preserve:

1. deterministic transition semantics (explicit success/failure branches),
2. M3.5 IPC-scheduler handshake coherence semantics and trace anchors,
3. domain-aware scheduling semantics (`schedule` is active-domain-only; no cross-domain fallback),
4. local + composed invariant layering (including `currentThreadInActiveDomain` in the canonical scheduler bundle),
5. theorem discoverability through stable naming,
   - canonical IPC/lifecycle composition surfaces: `coreIpcInvariantBundle`, `ipcSchedulerCouplingInvariantBundle`, `lifecycleCompositionInvariantBundle`,
   - canonical trace helper surfaces: `runCapabilityIpcTrace`, `runSchedulerTimingDomainTrace`,
6. fixture-backed executable evidence (`Main.lean` + trace fixture),
7. tiered validation command behavior (`test_fast`/`smoke`/`full`/`nightly`),
8. top-level import hygiene: `SeLe4n/Kernel/API.lean` is the canonical aggregate API surface.
9. syscall capability-checking: `SyscallGate` + `syscallLookupCap` model the seL4 CSpace-lookup + rights-check pattern; production path `syscallEntry` -> `dispatchSyscall` -> `syscallInvoke` -> `dispatchWithCap` (S5-A: deprecated `api*` wrappers removed); 3 soundness theorems prove capability requirements; 17 `SyscallId` variants (V2: added `notificationSignal`=14, `notificationWait`=15, `replyRecv`=16); `MessageInfo` label bounded to 20 bits (seL4 convention).
10. HashMap-backed equality for `VSpaceRoot` and `CNode` is order-independent (size + fold containment), and the migrated state stores (`services`, `irqHandlers`, `capabilityRefs`, `cdtSlotNode`, `cdtNodeSlot`) are `Std.HashMap`-backed (no closure-chain metadata stores).

---

## 10. Audit Baselines

### 10.1 Active Baselines

| Artifact | Path |
|----------|------|
| Codebase audit v1 (v0.12.2) | [`docs/audits/AUDIT_CODEBASE_v0.12.2_v1.md`](../dev_history/audits/AUDIT_CODEBASE_v0.12.2_v1.md) |
| Codebase audit v2 (v0.12.2) | [`docs/audits/AUDIT_CODEBASE_v0.12.2_v2.md`](../dev_history/audits/AUDIT_CODEBASE_v0.12.2_v2.md) |
| Execution baseline (WS-F) | [`docs/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md) |

### 10.2 Prior Baselines (completed)

| Artifact | Path |
|----------|------|
| Findings baseline (v0.11.6) | [`docs/dev_history/audits/AUDIT_CODEBASE_v0.11.6.md`](../dev_history/audits/AUDIT_CODEBASE_v0.11.6.md) |
| Execution baseline (WS-E) | [`docs/dev_history/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.11.6_WORKSTREAM_PLAN.md) |
| Findings baseline (v0.11.0) | [`docs/dev_history/audits/AUDIT_v0.11.0.md`](../dev_history/audits/AUDIT_v0.11.0.md) |
| Execution baseline (WS-D) | [`docs/dev_history/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md) |

### 10.3 Historical Baselines

Prior audits and workstream plans are archived in [`docs/dev_history/audits/`](../dev_history/audits/).

---

## 11. Security and Threat Model

Security assumptions and trust boundaries are documented in
[`docs/THREAT_MODEL.md`](../THREAT_MODEL.md).

The hardware-boundary contract policy governing test-only fixture separation and
architecture-assumption interfaces is documented in
[`docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md`](../HARDWARE_BOUNDARY_CONTRACT_POLICY.md).

### 10.1 Trust Boundaries (WS-S/S1)

The following trust boundaries are documented as part of WS-S Phase S1:

**`ThreadId.toObjId` identity mapping** (`SeLe4n/Prelude.lean`): The conversion
from `ThreadId` to `ObjId` is an unchecked identity mapping. Callers must verify
the returned `ObjId` references a TCB by pattern-matching on `.tcb tcb` after
object store lookup. The checked variant `toObjIdChecked` additionally rejects
the sentinel value (ID 0). See `ThreadId.toObjId_injective` for the injectivity
proof.

**Badge forging via Mint** (`SeLe4n/Kernel/Capability/Operations.lean`): Any
holder of a capability with Mint authority on an endpoint can mint a derived
capability with an arbitrary badge value. This matches seL4 semantics — badge
values are opaque sender identifiers, not cryptographic authenticators.
Authentication relies on the CDT tracking which entity performed the mint.

**`MemoryRegion.wellFormed`** (`SeLe4n/Machine.lean`): Converted from a runtime
`Bool` check to a `Prop` proof obligation in WS-S/S1-B. Callers must provide
evidence that `size > 0 ∧ endAddr ≤ 2^physAddrWidth`. A `Decidable` instance
enables `decide`/`native_decide` and `if`-expressions.

**`AccessRightSet.valid`** (`SeLe4n/Model/Object/Types.lean`): Added in
WS-S/S1-G. The well-formedness predicate `bits < 2^5` ensures no spurious
upper bits exist. `AccessRightSet.ofNat` masks inputs to the valid 5-bit range.

### 11.2 Information Flow and Non-Interference Boundary (AD3-C/F-05)

The kernel's non-interference (NI) guarantees cover all kernel-primitive
transitions via 35 `NonInterferenceStep` constructors in
`SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean`. These include IPC
(with SchedContext donation and priority inheritance protocol propagation),
scheduling (including domain rotation via `ComposedNonInterferenceStep`),
capability operations, lifecycle, and decode/dispatch paths. The
`dispatchSyscallChecked_preserves_projection` theorem (`API.lean`) bridges
per-operation NI proofs to the full 25-arm syscall dispatch path.

**Service orchestration is explicitly outside the kernel NI boundary.** The
`serviceOrchestrationOutsideNiBoundary` theorem (`Projection.lean:551`)
formally proves that service orchestration internals (lifecycle policies,
restart state, heartbeat, dependency resolution order) are not captured by the
NI projection model. Only the service registry layer (presence and dependency
edges) is observable.

Deployers requiring service-layer information-flow isolation must analyze
service-layer flows independently of kernel NI guarantees. See
[`docs/DEPLOYMENT_GUIDE.md`](../DEPLOYMENT_GUIDE.md) Section 3 for deployment
implications.

#### 11.2.1 Service-presence covert channels (AN6-E.1 / IF-M01)

WS-AN Phase AN6-E.1 formalizes the scope of `serviceObservable`
(`Kernel/InformationFlow/Projection.lean:139`): the predicate covers
**boolean service presence only**, not internal state. Cross-service
covert channels — for example, one service observing another's restart
cadence via service-presence sampling — are **NOT** closed by the kernel
NI property. These are accepted covert channels at v1.0.0.

The formal justification for the acceptance is that service
orchestration operates above the kernel-primitive NI boundary: services
are trusted components that the kernel merely tracks presence for. A
deployment that requires NI at the service-orchestration layer must
either:

1. Model service state in the projection explicitly (a deployer-specific
   model-refinement effort — the kernel model does not ship with
   service-state-aware projection), or
2. Treat the service layer as a separate trusted component outside the
   NI analysis boundary.

The kernel model at v1.0.0 does not attempt to close this gap. Four
regression tests in `tests/InformationFlowSuite.lean` (`NI-L3/1..4`)
guard the four known observable scheduler channels (current thread,
active domain, time-remaining, schedule index) against silent closure
that would invalidate the NI-L3 acceptance documentation.

See `docs/dev_history/audits/AUDIT_v0.30.6_COMPREHENSIVE.md` §2.5 IF-M01 for the
audit-level classification.

#### 11.2.2 Architecture assumption consumer index (AN6-B / H-08)

WS-AN Phase AN6-B adds a machine-searchable index
(`archAssumptionConsumer` in `Kernel/Architecture/Assumptions.lean`)
mapping each of the 5 `ArchAssumption` enumeration values to the fully
qualified `Lean.Name` of its consuming theorem. The mapping is:

| `ArchAssumption` constructor      | Consuming theorem |
|-----------------------------------|-------------------|
| `.deterministicTimerProgress`     | `deterministicTimerProgress_consumed_by_advanceTimer` |
| `.deterministicRegisterContext`   | `deterministicRegisterContext_consumed_by_writeRegister` |
| `.memoryAccessSafety`             | `memoryAccessSafety_consumed_by_readMemory` |
| `.bootObjectTyping`               | `default_system_state_proofLayerInvariantBundle` |
| `.irqRoutingTotality`             | `SeLe4n.Platform.Boot.bootFromPlatformChecked_ok_implies_irqHandlersValid` |

Three complementary guards enforce the index cannot silently drift:

1. `architecture_assumptions_index : ∀ a, ∃ n, archAssumptionConsumer a = n`
   — totality witness (adding a constructor without a mapping entry
   fails elaboration via `cases a`).
2. `archAssumptionConsumer_distinct` — the 5 names are pairwise
   distinct (catches the "all map to the same name" shortcut).
3. 5 compile-time `example` blocks in
   `Kernel/Architecture/Invariant.lean` that resolve 4 of the 5
   consumer theorems by Lean-level identifier (not by `Name` literal),
   plus an `@` reference to the 5th in `tests/ModelIntegritySuite.lean`.
   If any consumer theorem is renamed or deleted, one of these
   references fails elaboration.

#### 11.2.3 Single-core kernel model witness (AN6-F / CX-M03)

WS-AN Phase AN6-F added `bootFromPlatform_singleCore_witness` in
`Kernel/CrossSubsystem.lean`. As anticipated below, the WS-SM SMP
bring-up workstream took **path (a)**: at **SM4.B** (v0.31.12) the
`SchedulerState.current` field flipped from a single `Option ThreadId`
to `Vector (Option ThreadId) Concurrency.numCores` indexed by `CoreId`
(the path-a per-core `Vector` replacement). **WS-SM SM4.E (v0.31.35)**
then **retired** the boot-core-only witness — once `current` was a
per-core `Vector`, the boot-core-only form was structurally too weak to
characterise the per-core map — and replaced it with the per-core
SMP-shape witness `SeLe4n.Platform.Boot.bootFromPlatform_smp_witness`
(`∀ c : CoreId, currentOnCore c = none ∨ = some (idleThreadId c)`), the
new structural anchor for the `singleCoreOperation` `ArchAssumption`
(see §6.8). **WS-SM SM4.G (v0.31.36)** then installed the per-core idle
threads, so the witness's `some` branch is live on the
`bootFromPlatformWithIdleThreads` boot path
(`bootFromPlatformWithIdleThreads_all_cores_have_idle`). The Rust HAL
still enforces the hardware-level boot assumption via
`MPIDR_CORE_ID_MASK = 0x00FFFFFF` and the core-0 wake gate in
`rust/sele4n-hal/src/boot.S` (secondary-core wake-up is staged in the
SM1 HAL but not yet driven from the verified kernel).

The original AN6-F note anticipated exactly this: "any future SMP
extension that adds per-core scheduler state will either (a) change the
`current` field's type (breaking this theorem statement) or (b)
introduce a separate per-core-map field." SM4.B took option (a); SM4.E
retired the now-too-weak witness and SM4.G replaced it with the
substantive per-core form — so the SMP assumption was carried
continuously across the migration (restated, not deleted, at SM4.B; then
retired-with-replacement at SM4.E/SM4.G), never silently dropped.

## 12. Licensing and Third-Party Attribution

seLe4n is distributed under the GNU General Public License v3.0 or later
(GPLv3+), as stated in [`LICENSE`](../../LICENSE). Every Lean source file,
Rust source file, and assembly file carries an SPDX-compatible copyright
header identifying the project license.

### 12.1 Runtime TCB composition

The final kernel binary contains **no third-party Rust crates**. Every
crate in the runtime dependency tree (`sele4n-types`, `sele4n-abi`,
`sele4n-sys`, `sele4n-hal`) is `#![no_std]` and authored entirely within
this repository. Hardware access in the HAL uses `core::ptr::read_volatile`
and `core::ptr::write_volatile` directly rather than any third-party MMIO
crate (e.g., the deprecated `mmio` crate or the newer `safe-mmio`). This
keeps the trusted computing base minimal and under unified GPLv3+
governance.

### 12.2 Build-time dependencies

A small number of external crates are required at **build time only** to
assemble the ARM64 boot assembly files (`boot.S`, `vectors.S`, `trap.S`)
via `rust/sele4n-hal/build.rs`:

| Crate             | Version | License              | Role                                                 |
|-------------------|---------|----------------------|------------------------------------------------------|
| `cc`              | 1.2.59  | `MIT OR Apache-2.0`  | Invokes the C toolchain to assemble `*.S` files.     |
| `find-msvc-tools` | 0.1.9   | `MIT OR Apache-2.0`  | Transitive dep of `cc`; inactive on non-Windows.     |
| `shlex`           | 1.3.0   | `MIT OR Apache-2.0`  | Transitive dep of `cc`; POSIX shell-word splitting.  |

Both MIT and Apache-2.0 are GPL-3.0-compatible per the Free Software
Foundation. seLe4n consumes each crate under the MIT option; the verbatim
upstream copyright and permission notices (plus contributor lists for
`shlex`) are reproduced in
[`THIRD_PARTY_LICENSES.md`](../../THIRD_PARTY_LICENSES.md) at the
repository root. Apache-2.0 § 4(d) requires propagation of any upstream
`NOTICE` file; as of the versions listed above, none of the three crates
ships a `NOTICE` file, so no additional text is required by that clause.

When upgrading any of these crates, the PR must re-check the upstream
`LICENSE-MIT` for authorship or copyright changes and re-check for a new
`NOTICE` file. The `scripts/website_link_manifest.txt` file tracks
`THIRD_PARTY_LICENSES.md` as a protected path so the file cannot be
renamed without website-repo coordination.
