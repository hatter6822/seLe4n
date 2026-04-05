# WS-V Workstream Plan — Kernel Starvation Prevention & Liveness Guarantees

**Created**: 2026-03-24
**Baseline version**: 0.20.7
**Prior portfolios**: WS-B through WS-T (all COMPLETE)
**Constraint**: Zero `sorry`/`axiom` in production proof surface
**Hardware target**: Raspberry Pi 5 (ARM64) — scheduling latency bounds inform real-time guarantees
**Relationship to WS-U**: Independent. WS-V addresses scheduling liveness; WS-U addresses hardware binding. Disjoint file sets allow parallel development. WS-V phases V1–V3 may run concurrently with WS-U; V4 depends on WS-U platform types for hardware timer integration.

---

## 1. Motivation

The seLe4n kernel has **best-in-class safety properties** for its scheduler,
IPC, and cross-subsystem invariants: deterministic thread selection, dequeue-on-
dispatch semantics, queue acyclicity, time-slice positivity, EDF ordering within
priority bands, and structural coherence between IPC blocking and scheduler
state. All transitions are pure functions with machine-checked preservation
proofs. Zero `sorry`, zero `axiom`.

However, the kernel currently proves **no liveness or fairness properties**.
Every proven invariant is a safety property ("nothing bad happens"), but no
theorem guarantees that a runnable thread will eventually execute, that a
blocked thread will eventually unblock, or that priority inversion is bounded.

This gap matters for three reasons:

1. **Correctness completeness**: A verified microkernel that cannot prove threads
   make progress has an incomplete correctness story. Safety without liveness
   means the kernel could be "correct" while every thread starves.

2. **Real-time schedulability**: The RPi5 target (WS-U) will host real-time
   workloads. Without formal worst-case response time (WCRT) bounds, system
   integrators cannot prove schedulability of their task sets.

3. **Priority inversion**: The Call/Reply IPC pattern allows high-priority
   clients to be transitively blocked by low-priority servers — the classic
   Mars Pathfinder scenario. No mitigation mechanism is formalized.

WS-V closes these gaps across four phases, each independently valuable:

| Phase | Deliverable | Key Guarantee |
|-------|------------|---------------|
| V1 | Bounded Latency Theorem | WCRT bound for runnable threads (zero code changes) |
| V2 | IPC Timeout Mechanism | Bounded blocking for all IPC operations |
| V3 | Priority Inheritance Protocol | Bounded priority inversion for Call/Reply |
| V4 | MCS Scheduling Contexts | CPU budgets, passive servers, timeout endpoints |

---

## 2. Starvation Analysis — Current State

### 2.1 Proven Properties (Safety)

| ID | Property | Predicate | File | Line |
|----|----------|-----------|------|------|
| S-1 | Deterministic selection | `isBetterCandidate` | `Scheduler/Operations/Selection.lean` | 38 |
| S-2 | Dequeue-on-dispatch | `queueCurrentConsistent` | `Scheduler/Invariant.lean` | 41 |
| S-3 | No duplicate threads | `runQueueUnique` | `Scheduler/Invariant.lean` | 53 |
| S-4 | Current thread valid | `currentThreadValid` | `Scheduler/Invariant.lean` | 58 |
| S-5 | Time-slice positive | `timeSlicePositive` | `Scheduler/Invariant.lean` | 116 |
| S-6 | Current time-slice positive | `currentTimeSlicePositive` | `Scheduler/Invariant.lean` | 128 |
| S-7 | EDF within priority band | `edfCurrentHasEarliestDeadline` | `Scheduler/Invariant.lean` | 149 |
| S-8 | Domain partitioning | `currentThreadInActiveDomain` | `Scheduler/Invariant.lean` | 66 |
| S-9 | Context consistency | `contextMatchesCurrent` | `Scheduler/Invariant.lean` | 176 |
| S-10 | Blocked ⇒ not runnable | `blockedOn*NotRunnable` (5 predicates) | `IPC/Invariant/Defs.lean` | 268–298 |
| S-11 | Runnable ⇒ IPC ready | `runnableThreadIpcReady` | `IPC/Invariant/Defs.lean` | 268 |
| S-12 | Queue chain acyclicity | `tcbQueueChainAcyclic` | `IPC/Invariant/Defs.lean` | 145 |
| S-13 | No stale queue refs | `noStaleEndpointQueueReferences` | `CrossSubsystem.lean` | 58 |
| S-14 | Priority-match consistency | `schedulerPriorityMatch` | `Scheduler/Invariant.lean` | 272 |
| S-15 | RunQueue well-formedness | `RunQueue.wellFormed` | `Scheduler/RunQueue.lean` | 666 |

### 2.2 Identified Starvation Vectors

| ID | Vector | Severity | Mechanism |
|----|--------|----------|-----------|
| SV-1 | Strict priority starvation | HIGH | Thread at priority P never runs while any thread at priority P+1 is runnable. No aging, no decay, no boost. `isBetterCandidate` (Selection.lean:38) enforces strict ordering. |
| SV-2 | Priority inversion via Call/Reply | HIGH | High-priority client enters `blockedOnReply` (Types.lean:295) waiting for low-priority server. Middle-priority threads preempt server indefinitely. No priority inheritance. |
| SV-3 | Unbounded IPC blocking | HIGH | Threads in `blockedOnSend`/`blockedOnReceive`/`blockedOnReply`/`blockedOnNotification` are removed from run queue (`removeRunnable`). No timeout mechanism. Unblocking is purely event-driven. |
| SV-4 | Notification LIFO ordering | MEDIUM | `notificationWait` prepends to `waitingThreads` (Endpoint.lean:227). `notificationSignal` wakes `List.head?`. Earlier waiters can be starved by continuous new-waiter arrival. |
| SV-5 | Domain schedule imbalance | MEDIUM | `scheduleDomain` (Core.lean:384) uses static `domainSchedule` table. No fairness guarantee if entries have unequal lengths. Within-domain priority starvation compounds. |
| SV-6 | Run queue cycling without bound | LOW | At equal priority and deadline, FIFO stability retains incumbent (`isBetterCandidate` returns `false` on equality). But no theorem bounds the number of rotations before a specific thread is selected. |

### 2.3 What Is NOT a Starvation Risk

| Property | Why It's Safe |
|----------|--------------|
| Deadlock from queue cycles | `tcbQueueChainAcyclic` (Defs.lean:145) prevents circular wait chains |
| Stale references blocking progress | `noStaleEndpointQueueReferences` (CrossSubsystem.lean:58) + lifecycle cleanup |
| Time-slice underflow | `timeSlicePositive` (Invariant.lean:116) prevents infinite execution without preemption |
| Phantom scheduling | `runnableThreadsAreTCBs` (Invariant.lean:240) ensures only valid TCBs are scheduled |

---

## 3. Phase Dependency Graph

```
V1 (Bounded Latency Theorem)           — proof-only, zero code changes
 │
 ├──→ V2 (IPC Timeout Mechanism)       — new kernel transitions + proofs
 │     │
 │     └──→ V3 (Priority Inheritance)  — TCB extension + scheduler changes + proofs
 │           │
 │           └──→ V4 (MCS Scheduling Contexts) — new kernel object type + full rework
 │
 └──→ V4 (depends on V1 trace model + V2 timeout infra + V3 effective priority)
```

**Critical path**: V1 → V2 → V3 → V4

**Parallelism opportunities**:
- V1 is entirely proof-only (new `.lean` files in `Scheduler/Liveness/`). No
  file overlap with WS-U hardware binding work.
- V2-A through V2-D (type extensions, timeout decrement) can begin immediately
  after V1 completes; V2-I through V2-N (preservation proofs) depend on V2-G/H.
- V3 depends on V2 for the timeout-aware IPC state type but can prototype the
  effective priority mechanism independently.
- V4 depends on all prior phases and WS-U platform types.

**File ownership by phase** (disjoint new directories; shared files use additive changes):
- **V1** owns: `SeLe4n/Kernel/Scheduler/Liveness/` (new directory, all files).
  No modifications to existing files.
- **V2** owns: `SeLe4n/Kernel/IPC/Operations/Timeout.lean` (new),
  `SeLe4n/Kernel/IPC/Invariant/TimeoutPreservation.lean` (new),
  `SeLe4n/Kernel/IPC/Liveness/` (new directory).
  Modifies: `Model/Object/Types.lean` (timeout field on IPC states),
  `IPC/Operations/Endpoint.lean`, `IPC/DualQueue/Core.lean`,
  `Scheduler/Operations/Core.lean` (timeout tick integration).
- **V3** owns: `SeLe4n/Kernel/Scheduler/PriorityInheritance/` (new directory).
  Modifies: `Model/Object/Types.lean` (effectivePriority field — additive, no
  conflict with V2's timeout field), `Scheduler/Operations/Selection.lean`,
  `Scheduler/RunQueue.lean`, `IPC/Operations/Endpoint.lean` (Call/Reply PIP hooks).
- **V4** owns: `SeLe4n/Kernel/SchedContext/` (new directory).
  Modifies: `Model/Object/Types.lean` (SchedContext type + TCB binding field),
  `Prelude.lean` (SchedContextId), `Kernel/API.lean`, `Architecture/SyscallArgDecode.lean`.

**Shared file coordination**: `Model/Object/Types.lean` receives additive changes
in V2 (timeout fields), V3 (effectivePriority), and V4 (SchedContext + TCB binding).
Each phase adds new fields or constructors — no conflicting modifications. The
sequential phase ordering (V2 → V3 → V4) ensures each phase builds on the
previous type definitions.

---

## 4. Phase V1 — Bounded Latency Theorem (v0.21.0)

**Scope**: Prove a conditional worst-case response time (WCRT) bound for the
existing scheduler — with zero kernel code changes. Establish the trace model
infrastructure that all subsequent liveness proofs will build on.

**Rationale**: The existing scheduler already guarantees round-robin within a
priority level via `timerTick` preemption (quantum = `defaultTimeSlice` = 5) and
`rotateToBack` on yield. The key insight is that these mechanisms *already*
bound latency — the bound just hasn't been stated or proven. V1 formalizes
this latency bound as a function of thread count and quantum size, providing
the first machine-checked WCRT for a microkernel scheduler in a modern
dependently-typed proof assistant.

**Dependencies**: None. Proof-only phase over existing kernel transitions.

**Gate**: `test_full.sh` passes. All new theorems compile without `sorry`/`axiom`.
New liveness module builds via `lake build SeLe4n.Kernel.Scheduler.Liveness.TraceModel`
(and all submodules). Zero sorry, zero axiom.

**Sub-tasks (15):**

| ID | Finding | Description | Files | Estimate |
|----|---------|-------------|-------|----------|
| V1-A | SV-6 | **Define trace model types.** Create `SeLe4n/Kernel/Scheduler/Liveness/TraceModel.lean`. Define `SchedulerStep` inductive covering `timerTick`, `schedule`, `handleYield`, `switchDomain`, `scheduleDomain`. Define `SchedulerTrace` as `List (SchedulerStep × SystemState)`. Define `validTrace` predicate: each step's precondition holds and postcondition state feeds into the next step's precondition. | `SeLe4n/Kernel/Scheduler/Liveness/TraceModel.lean` | Small |
| V1-B | SV-6 | **Define trace query predicates.** In the same file, define `selectedAt (trace : SchedulerTrace) (k : Nat) (tid : ThreadId) : Prop` — thread `tid` is the `current` thread at trace index `k`. Define `runnableAt (trace : SchedulerTrace) (k : Nat) (tid : ThreadId) : Prop` — thread `tid` is in `runQueue` at index `k`. Prove basic structural lemmas: `selectedAt_implies_not_runnableAt` (from `queueCurrentConsistent`). | `SeLe4n/Kernel/Scheduler/Liveness/TraceModel.lean` | Small |
| V1-C | SV-6 | **Define counting predicates.** In the same or adjacent file, define `countHigherOrEqualPriority (tid : ThreadId) (st : SystemState) : Nat` — number of threads in `runQueue` with priority ≥ `tid`'s priority in the same domain. Define `maxQuantumInBand (tid : ThreadId) (st : SystemState) : Nat` — maximum `timeSlice` among those threads. Define `bucketPosition (tid : ThreadId) (st : SystemState) : Option Nat` — 0-indexed position of `tid` in its priority bucket. These are pure read-only functions over existing state. | `SeLe4n/Kernel/Scheduler/Liveness/TraceModel.lean` | Small |
| V1-D | SV-6 | **Prove timer-tick monotonicity.** Create `SeLe4n/Kernel/Scheduler/Liveness/TimerTick.lean`. Prove `timerTick_decrements_timeSlice`: if `current = some tid` and `tcb.timeSlice > 1`, then after `timerTick`, `tcb'.timeSlice = tcb.timeSlice - 1`. This follows directly from the `timerTick` definition (Core.lean:313) by unfolding and case-splitting on the `timeSlice ≤ 1` branch. | `SeLe4n/Kernel/Scheduler/Liveness/TimerTick.lean` | Small |
| V1-E | SV-6 | **Prove timer-tick preemption.** In the same file, prove `timerTick_preempts_at_one`: if `current = some tid` and `tcb.timeSlice ≤ 1`, then after `timerTick`, `tid` is re-enqueued (in `runQueue`) and `schedule` is called. Combined with V1-D, this shows every thread is preempted within exactly `tcb.timeSlice` ticks. Prove `timerTick_preemption_bound`: after exactly `tcb.timeSlice` applications of `timerTick`, thread `tid` is preempted (direct corollary of V1-D + V1-E). | `SeLe4n/Kernel/Scheduler/Liveness/TimerTick.lean` | Small |
| V1-F | SV-6 | **Prove yield rotates to back.** Create `SeLe4n/Kernel/Scheduler/Liveness/Yield.lean`. Prove `handleYield_rotates_to_back`: after `handleYield`, the yielding thread is at the tail of its priority bucket in `runQueue.byPriority`. Use `RunQueue.rotateToBack` semantics (RunQueue.lean:335) and `mem_rotateToBack` bridge lemma (RunQueue.lean:457). | `SeLe4n/Kernel/Scheduler/Liveness/Yield.lean` | Small |
| V1-G | SV-6 | **Prove single-step FIFO advance.** In the same file, prove `fifo_single_step_advance`: if thread `tid` is at position `k > 0` in its priority bucket and the thread at position `k-1` is preempted (via `timerTick` expiry) or yields (via `handleYield`), then `tid`'s position becomes `k-1`. This is a single application of the `rotateToBack` effect on bucket ordering. Depends on V1-E (preemption) and V1-F (rotation semantics). | `SeLe4n/Kernel/Scheduler/Liveness/Yield.lean` | Small |
| V1-H | SV-6 | **Prove FIFO progress within priority band.** In the same file, prove `fifo_progress_in_band`: if thread `tid` is at position `k` (0-indexed) in its priority bucket, and no higher-priority threads exist in the active domain, then `tid` is selected within `k × defaultTimeSlice` ticks. Proof by induction on `k`: base case `k = 0` means `tid` is at head and is selected immediately; inductive step uses V1-G (`single_step_advance`) to show position decreases after each preemption cycle of `defaultTimeSlice` ticks. | `SeLe4n/Kernel/Scheduler/Liveness/Yield.lean` | Medium |
| V1-I | SV-1 | **Prove priority-band exhaustion.** Create `SeLe4n/Kernel/Scheduler/Liveness/BandExhaustion.lean`. Prove `higher_band_exhaustion`: if all threads at priority > P are eventually removed from the run queue (blocked, yielded to lower priority, or deleted), then a thread at priority P will be selected. This is a conditional liveness lemma — it does not prove that higher-priority threads *will* leave, only that *if* they do, progress occurs. Uses `isBetterCandidate` ordering (Selection.lean:38) and `chooseBestInBucket` semantics. | `SeLe4n/Kernel/Scheduler/Liveness/BandExhaustion.lean` | Medium |
| V1-J | SV-5 | **Prove domain rotation bound.** Create `SeLe4n/Kernel/Scheduler/Liveness/DomainRotation.lean`. Prove `domain_rotation_bound`: if `domainSchedule` has `D` entries with maximum length `L_max`, then every domain receives CPU time within `D × L_max` ticks. Uses `switchDomain` round-robin semantics (Core.lean:356) and modular index arithmetic on `domainScheduleIndex`. | `SeLe4n/Kernel/Scheduler/Liveness/DomainRotation.lean` | Medium |
| V1-K | SV-1, SV-6 | **State and prove WCRT hypotheses.** Create `SeLe4n/Kernel/Scheduler/Liveness/WCRT.lean`. Define the `WCRTHypotheses` structure bundling: (1) thread `tid` is in `runQueue`, (2) `tid` is in domain `d` which appears in `domainSchedule`, (3) `countHigherOrEqualPriority tid st ≤ N`, (4) all threads in band have `timeSlice ≤ Q`, (5) domain schedule entry for `d` has length ≥ `N × Q`. Prove `wcrt_hypotheses_stable_under_timerTick`: if hypotheses hold at state `st`, they hold at the state after `timerTick` (provided `tid` is not the current thread). | `SeLe4n/Kernel/Scheduler/Liveness/WCRT.lean` | Medium |
| V1-L | SV-1, SV-6 | **Prove the main WCRT theorem.** In the same file, prove `bounded_scheduling_latency`: given `WCRTHypotheses`, thread `tid` is selected within `N × Q` ticks from any valid trace. Structure: (1) apply `domain_rotation_bound` (V1-J) to show `tid`'s domain becomes active within `D × L_max` ticks; (2) apply `fifo_progress_in_band` (V1-H) to show `tid` is selected within `N × Q` ticks once its domain is active; (3) compose bounds. The proof uses `Nat.le_trans` to chain the two bounds. | `SeLe4n/Kernel/Scheduler/Liveness/WCRT.lean` | Medium |
| V1-M | — | **Create re-export hub.** Create `SeLe4n/Kernel/Scheduler/Liveness.lean` as a thin import-only file re-exporting `TraceModel`, `TimerTick`, `Yield`, `BandExhaustion`, `DomainRotation`, and `WCRT`. Follow the project's re-export hub convention. | `SeLe4n/Kernel/Scheduler/Liveness.lean` | Trivial |
| V1-N | — | **Add test surface anchors.** Add invariant surface anchor tests in `tests/` that verify the new liveness theorems are reachable from the test harness. Reference `bounded_scheduling_latency`, `domain_rotation_bound`, `fifo_progress_in_band`, and `timerTick_preemption_bound` as anchor points. Follow existing anchor test patterns from `test_full.sh` (Tier 3). | `tests/LivenessSuite.lean`, `lakefile.lean` | Small |
| V1-O | — | **Documentation sync.** Update `docs/spec/SELE4N_SPEC.md` with the WCRT bound statement and its hypotheses. Update `docs/CLAIM_EVIDENCE_INDEX.md` with new liveness claims. Update source layout in `CLAUDE.md` to include the new `Scheduler/Liveness/` directory. Regenerate `docs/codebase_map.json`. | `docs/spec/SELE4N_SPEC.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, `CLAUDE.md`, `docs/codebase_map.json` | Small |

**Intra-phase ordering constraints:**
- Trace model foundation: V1-A → V1-B → V1-C (types → queries → counting)
- Timer-tick chain: V1-D → V1-E (monotonicity → preemption bound)
- Yield/FIFO chain: V1-F → V1-G → V1-H (rotate → single-step → inductive FIFO)
- Band exhaustion: V1-I (independent of yield chain; depends on V1-C for counting)
- Domain rotation: V1-J (independent; depends on V1-A for trace model)
- WCRT: V1-H + V1-I + V1-J → V1-K → V1-L (hypotheses → composition)
- Infrastructure: V1-L → V1-M → V1-N → V1-O (sequential post-proof)
- V1-D/E and V1-F/G/H are independent chains (can run in parallel)
- V1-I and V1-J are independent of each other (can run in parallel)

---

## 5. Phase V2 — IPC Timeout Mechanism (v0.21.1)

**Scope**: Add an optional timeout parameter to all blocking IPC operations,
enabling bounded blocking. When a timeout expires, the blocked thread is
forcibly unblocked with an error result. Prove that forced unblocking preserves
all existing IPC and scheduler invariants.

**Rationale**: Unbounded IPC blocking (SV-3) is the single largest availability
risk. A thread that enters `blockedOnSend` or `blockedOnReceive` may never
unblock if the counterparty never arrives. This phase adds a deterministic,
kernel-level timeout that guarantees every blocked thread unblocks within a
bounded number of ticks. The timeout is optional (defaulting to `none` for
backward compatibility) and purely kernel-internal — no new syscall is required
in this phase.

**Dependencies**: V1 (trace model infrastructure for timeout-expiry liveness proof).

**Gate**: `test_full.sh` passes. All IPC preservation theorems updated for
timeout paths. Timeout expiry triggers correct error propagation. No `sorry`,
no `axiom`. Module builds verified for every modified `.lean` file.

**Sub-tasks (18):**

| ID | Finding | Description | Files | Estimate |
|----|---------|-------------|-------|----------|
| V2-A | SV-3 | **Extend ThreadIpcState with timeout.** Add optional `timeout : Option Nat` field to each blocking variant of `ThreadIpcState` (Types.lean:290–297): `blockedOnSend`, `blockedOnReceive`, `blockedOnCall`, `blockedOnReply`, `blockedOnNotification`. Default to `none` (no timeout). This is a backward-compatible extension — all existing pattern matches on `ThreadIpcState` continue to work because `timeout` is a field within each constructor, not a new constructor. | `SeLe4n/Model/Object/Types.lean` | Medium |
| V2-B | SV-3 | **Update IPC operations to accept timeout.** Modify `notificationWait` (Endpoint.lean:202), and the blocking paths of send/receive/call operations to accept an optional `timeout : Option Nat` parameter. Thread the timeout value into `storeTcbIpcState` calls. When `timeout = none`, behavior is identical to current (no timeout). When `timeout = some n`, the blocking state carries the countdown. | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | Medium |
| V2-C | SV-3 | **Update dual-queue enqueue for timeout.** Modify `endpointQueueEnqueue` (DualQueue/Core.lean:254) to store the timeout value in the enqueued thread's IPC state. Ensure the `alreadyWaiting` guard (line 264) still functions correctly with the new field. | `SeLe4n/Kernel/IPC/DualQueue/Core.lean` | Small |
| V2-D | SV-3 | **Implement timeout decrement logic.** Create `SeLe4n/Kernel/IPC/Operations/Timeout.lean`. Implement `decrementTimeout (st : SystemState) (tid : ThreadId) (tcb : TCB) : SystemState` — for a single thread with blocking IPC state and `timeout = some n` where `n > 1`, update `ipcState` to carry `timeout = some (n - 1)` via `storeTcbIpcState`. This is the non-expiry path. Implement `isTimeoutExpired (tcb : TCB) : Bool` — returns `true` when `tcb.ipcState` has `timeout = some n` with `n ≤ 1`. | `SeLe4n/Kernel/IPC/Operations/Timeout.lean` | Small |
| V2-E | SV-3 | **Implement single-thread forced unblock.** In the same file, implement `forceUnblockThread (st : SystemState) (tid : ThreadId) (tcb : TCB) : Except KernelError SystemState` — the expiry path for a single thread. Case-splits on `tcb.ipcState` to determine which queue/wait-list the thread is in: `blockedOnSend epId` / `blockedOnReceive epId` → call `forceRemoveFromEndpointQueue`; `blockedOnCall epId` → call `forceRemoveFromEndpointQueue`; `blockedOnReply epId _` → no queue removal needed (thread is not in an endpoint queue); `blockedOnNotification notifId` → call `forceRemoveFromNotificationWaitList`. Then set `ipcState := .ready`, `pendingMessage := some (.error .timeout)`, and call `ensureRunnable`. | `SeLe4n/Kernel/IPC/Operations/Timeout.lean` | Medium |
| V2-F | SV-3 | **Implement `ipcTimeoutTick` as fold over threads.** In the same file, implement `ipcTimeoutTick : Kernel Unit` — folds over `st.objects` visiting each TCB. For each TCB with a blocking IPC state carrying `timeout = some n`: if `isTimeoutExpired tcb`, call `forceUnblockThread`; otherwise, call `decrementTimeout`. The fold is deterministic (uses `objects.fold` in insertion order, matching lifecycle cleanup patterns). | `SeLe4n/Kernel/IPC/Operations/Timeout.lean` | Medium |
| V2-G | SV-3 | **Implement forced endpoint queue removal.** In the timeout file, implement `forceRemoveFromEndpointQueue (tid : ThreadId) (epId : ObjId) (isReceiveQ : Bool) : Kernel Unit`. Reuse the splice logic from `spliceOutMidQueueNode` (Lifecycle/Operations.lean:48) — reads removed TCB's queue links from original state, patches predecessor's `queueNext` and successor's `queuePrev`. Then update endpoint head/tail pointers via `removeThreadFromQueue` pattern. Clear removed thread's queue links. | `SeLe4n/Kernel/IPC/Operations/Timeout.lean` | Medium |
| V2-H | SV-3 | **Implement forced notification wait list removal.** In the timeout file, implement `forceRemoveFromNotificationWaitList (tid : ThreadId) (notifId : ObjId) : Kernel Unit`. Filter `tid` from `notification.waitingThreads` (same pattern as `removeFromAllNotificationWaitLists`, Lifecycle/Operations.lean:98). Update notification state from `.waiting` to `.idle` if wait list becomes empty. | `SeLe4n/Kernel/IPC/Operations/Timeout.lean` | Small |
| V2-I | SV-3 | **Prove forced removal transport lemmas.** Create `SeLe4n/Kernel/IPC/Invariant/TimeoutPreservation.lean`. Prove 4 transport lemmas for `forceRemoveFromEndpointQueue`: (1) `forceRemove_scheduler_eq` — scheduler unchanged; (2) `forceRemove_notification_backward` — notifications at other ObjIds preserved; (3) `forceRemove_tcb_forward` — TCBs at other ObjIds survive; (4) `forceRemove_endpoint_backward_ne` — non-target endpoints preserved. These follow the exact pattern of `endpointQueueRemoveDual` transport lemmas in Transport.lean. | `SeLe4n/Kernel/IPC/Invariant/TimeoutPreservation.lean` | Medium |
| V2-J | SV-3 | **Prove forced removal preserves `intrusiveQueueWellFormed`.** In the same file, prove `forceRemove_preserves_intrusiveQueueWellFormed`: after forced endpoint queue removal, both the target queue (with thread removed) and all non-target queues maintain well-formedness (Defs.lean:107). The proof follows the structural frame lemma pattern: `storeObject_tcb_preserves_intrusiveQueueWellFormed` (Structural.lean) for link-patching steps, plus endpoint head/tail pointer updates maintain P1–P5 properties. | `SeLe4n/Kernel/IPC/Invariant/TimeoutPreservation.lean` | Medium |
| V2-K | SV-3 | **Prove forced removal preserves `tcbQueueLinkIntegrity` and `tcbQueueChainAcyclic`.** In the same file, prove two theorems: (1) `forceRemove_preserves_tcbQueueLinkIntegrity` — forward/reverse link consistency maintained after splice-out; (2) `forceRemove_preserves_tcbQueueChainAcyclic` — removing a node from a chain cannot create a cycle. Together with V2-J, compose into `forceRemove_preserves_dualQueueSystemInvariant`. | `SeLe4n/Kernel/IPC/Invariant/TimeoutPreservation.lean` | Medium |
| V2-L | SV-3 | **Prove `ipcTimeoutTick` preserves `ipcInvariantFull`.** Show that forced unblocking maintains `notificationQueueWellFormed` (state transitions from `.waiting` to `.idle` when last waiter is removed via V2-H), `allPendingMessagesBounded` (timeout error message satisfies `msg.bounded`), and `badgeWellFormed` (no badge modification on timeout path). Uses backward notification transport from V2-I. | `SeLe4n/Kernel/IPC/Invariant/TimeoutPreservation.lean` | Medium |
| V2-M | SV-3 | **Prove `ipcTimeoutTick` preserves scheduler invariants.** Show that `ensureRunnable` on timeout-unblocked threads preserves `schedulerInvariantBundleFull`. Decompose into per-component lemmas following the standard pattern: (1) `ipcTimeoutTick_preserves_queueCurrentConsistent` — `ensureRunnable` adds to queue, current unchanged; (2) `ipcTimeoutTick_preserves_runQueueUnique` — use `ensureRunnable_nodup` (SchedulerLemmas.lean:103); (3) `ipcTimeoutTick_preserves_currentThreadValid` — objects unchanged at current tid; (4) bundle composition via `⟨comp1, comp2, comp3⟩`. | `SeLe4n/Kernel/IPC/Invariant/TimeoutPreservation.lean` | Medium |
| V2-N | SV-3 | **Prove `ipcTimeoutTick` preserves cross-subsystem invariants.** Show that `noStaleEndpointQueueReferences` (CrossSubsystem.lean:58) and `noStaleNotificationWaitReferences` (CrossSubsystem.lean:76) are maintained after forced removal. The thread is removed from queues but its TCB still exists — no stale reference is created. For interior queue members checked via `collectQueueMembers`, the removed thread no longer appears in the traversal chain. | `SeLe4n/Kernel/IPC/Invariant/TimeoutPreservation.lean` | Small |
| V2-O | SV-3 | **Prove timeout liveness.** In a new file `SeLe4n/Kernel/IPC/Liveness/TimeoutBound.lean`, prove `ipc_timeout_bound`: if a thread enters a blocking IPC state with `timeout = some n`, then within `n` applications of `ipcTimeoutTick`, the thread is either unblocked by the counterparty or forcibly unblocked by timeout. Proof by induction on `n`: base case `n ≤ 1` triggers immediate `forceUnblockThread`; inductive step uses `decrementTimeout` to reduce to `some (n-1)`. Uses the V1 trace model for trace-level statement. | `SeLe4n/Kernel/IPC/Liveness/TimeoutBound.lean` | Medium |
| V2-P | SV-3 | **Integrate `ipcTimeoutTick` into timer path.** Modify `timerTick` (Core.lean:313) or create a composite `systemTick` that sequences: (1) `ipcTimeoutTick` (timeout decrements and forced unblocks), (2) existing `timerTick` logic (time-slice decrement and preemption). Update `timerTick_preserves_schedulerInvariantBundle` and `timerTick_preserves_kernelInvariant` in Preservation.lean to compose timeout preservation (V2-K through V2-N) with existing scheduler preservation. | `SeLe4n/Kernel/Scheduler/Operations/Core.lean`, `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean` | Medium |
| V2-Q | — | **Add negative-state tests.** Add test cases to `tests/NegativeStateSuite.lean` verifying: (1) timeout of 1 causes immediate unblock on next tick, (2) timeout decrement from `some 5` to `some 4` is correct, (3) forced removal from mid-queue endpoint preserves queue structure, (4) timeout error message `(.error .timeout)` is propagated in `pendingMessage`, (5) thread with `timeout = none` is not affected by `ipcTimeoutTick`. | `tests/NegativeStateSuite.lean`, `tests/TimeoutSuite.lean` | Small |
| V2-R | — | **Documentation sync.** Update `docs/spec/SELE4N_SPEC.md` with timeout semantics (optional timeout field, decrement-per-tick, forced unblock). Update `docs/CLAIM_EVIDENCE_INDEX.md` with bounded-blocking claim referencing `ipc_timeout_bound`. Update `CLAUDE.md` source layout with `IPC/Operations/Timeout.lean` and `IPC/Liveness/`. Regenerate `docs/codebase_map.json`. | `docs/spec/SELE4N_SPEC.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, `CLAUDE.md`, `docs/codebase_map.json` | Small |

**Intra-phase ordering constraints:**
- Type extension chain: V2-A → V2-B → V2-C (each builds on the extended type)
- Forced removal: V2-A → V2-G → V2-H (endpoint removal → notification removal; parallel implementations)
- Timeout core: V2-D → V2-E → V2-F (decrement → forced unblock → fold composition)
- V2-E depends on V2-G + V2-H (forced unblock calls forced removal functions)
- Transport lemmas: V2-G + V2-H → V2-I (implementations → transport proofs)
- Queue preservation: V2-I → V2-J → V2-K (transport → wellFormed → link integrity + composition)
- Invariant proofs: V2-K → V2-L (dualQueue → ipcInvariantFull), V2-K → V2-M (→ scheduler), V2-K → V2-N (→ cross-subsystem). These three are independent.
- Liveness: V2-D + V2-E + V1 trace model → V2-O
- Integration: V2-L + V2-M + V2-N → V2-P (all preservation proofs → timer integration)
- Testing: V2-P → V2-Q → V2-R (integration → tests → docs)

---

## 6. Phase V3 — Priority Inheritance Protocol (v0.21.2)

**Scope**: Implement a deterministic priority inheritance protocol (PIP) that
temporarily elevates a server thread's effective priority when it holds a
logical lock (pending Reply) on behalf of a higher-priority client. Prove that
PIP preserves all existing scheduler invariants, bounds the duration of priority
inversion, and is deterministic.

**Rationale**: Priority inversion via Call/Reply IPC (SV-2) is the most
dangerous starvation vector for client-server patterns. When a high-priority
client calls a low-priority server, the server executes at its own base
priority. Any middle-priority thread can preempt the server indefinitely,
transitively blocking the high-priority client. PIP resolves this by elevating
the server's effective scheduling priority to the maximum of its own priority
and all clients waiting for its reply. This is fully deterministic — the
effective priority is a pure function of the blocking graph.

**Dependencies**: V2 (timeout-aware `ThreadIpcState` type).

**Gate**: `test_full.sh` passes. Priority inheritance activates on Call, deactivates
on Reply. `isBetterCandidate` uses effective priority. All scheduler preservation
theorems updated. Inversion bounded by blocking chain depth. No `sorry`, no
`axiom`. Module builds verified for every modified `.lean` file.

**Sub-tasks (21):**

| ID | Finding | Description | Files | Estimate |
|----|---------|-------------|-------|----------|
| V3-A | SV-2 | **Add `effectivePriority` field to TCB.** Add `effectivePriority : Priority` field to the `TCB` structure (Types.lean:308). Initialize to `tcb.priority` (base priority) via default value. This field is the scheduling-visible priority; `priority` remains the base/configured priority. Add helper `TCB.resetEffectivePriority (tcb : TCB) : TCB` that sets `effectivePriority := tcb.priority`. | `SeLe4n/Model/Object/Types.lean` | Small |
| V3-B | SV-2 | **Define the blocking graph.** Create `SeLe4n/Kernel/Scheduler/PriorityInheritance/BlockingGraph.lean`. Define `blockedOnThread (st : SystemState) (waiter server : ThreadId) : Prop` — `waiter` has `ipcState = .blockedOnReply epId (some server)`. Define `waitersOf (st : SystemState) (tid : ThreadId) : List ThreadId` — all threads directly blocked on `tid` via `blockedOnReply`. Define `blockingChain (st : SystemState) (tid : ThreadId) : List ThreadId` — the transitive chain following `blockedOnReply` → server → server's `blockedOnReply` → …, with fuel bounded by `st.objects.size`. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/BlockingGraph.lean` | Medium |
| V3-C | SV-2 | **Prove blocking graph acyclicity.** In the same file, prove `blockingChain_acyclic`: `∀ tid, tid ∉ blockingChain st tid`. Proof strategy: each step in the chain follows `blockedOnReply` which requires the waiter to be in a blocking IPC state, while the server is either running or also blocked — the chain visits distinct threads. Use well-founded induction on the set of unvisited threads (finite, decreasing at each step). | `SeLe4n/Kernel/Scheduler/PriorityInheritance/BlockingGraph.lean` | Medium |
| V3-D | SV-2 | **Define `computeEffectivePriority`.** Create `SeLe4n/Kernel/Scheduler/PriorityInheritance/Compute.lean`. Define `computeEffectivePriority (st : SystemState) (tid : ThreadId) : Priority` — the maximum of `tid.priority` and all `waiter.priority` for `waiter ∈ waitersOf st tid` (direct waiters only — transitive propagation is handled by the chain walk, not recomputation). Prove `computeEffectivePriority_ge_base`: effective priority ≥ base priority (immediate from `Nat.le_max_left`). | `SeLe4n/Kernel/Scheduler/PriorityInheritance/Compute.lean` | Small |
| V3-E | SV-2 | **Implement `updateEffectivePriority` (single-thread).** Create `SeLe4n/Kernel/Scheduler/PriorityInheritance/Propagate.lean`. Implement `updateEffectivePriority (st : SystemState) (tid : ThreadId) : SystemState` — computes `computeEffectivePriority st tid`, updates the TCB's `effectivePriority` field, and if the thread is in `runQueue`, performs remove-then-insert to migrate it to the correct priority bucket. This is the atomic building block for propagation. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/Propagate.lean` | Medium |
| V3-F | SV-2 | **Implement `propagatePriorityInheritance` (chain walk).** In the same file, implement `propagatePriorityInheritance (st : SystemState) (tid : ThreadId) : SystemState`. Walks the blocking chain upward from `tid`: if `tid` has `ipcState = .blockedOnReply _ (some server)`, apply `updateEffectivePriority` to `server`, then recurse on `server`. The walk terminates because `blockingChain` is acyclic (V3-C) and bounded by thread count. Use `Nat.lt_wfRel` on remaining chain length for well-founded recursion. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/Propagate.lean` | Medium |
| V3-G | SV-2 | **Prove `propagatePriorityInheritance` termination and correctness.** In the same file, prove: (1) `propagate_terminates`: the chain walk terminates (follows from acyclicity + finite thread set); (2) `propagate_correct`: after propagation, every thread on the chain has `effectivePriority = computeEffectivePriority`. Proof by induction on chain length, using `updateEffectivePriority` correctness at each step. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/Propagate.lean` | Medium |
| V3-H | SV-2 | **Implement `revertPriorityInheritance`.** In the same file, implement `revertPriorityInheritance (st : SystemState) (tid : ThreadId) : SystemState` — called when `tid` completes a Reply. Walks the same chain as propagation but in the opposite direction: recomputes `computeEffectivePriority` for `tid` and all threads that were transitively boosted through `tid`. Uses the same `updateEffectivePriority` building block. Prove `revert_correct`: after revert, `effectivePriority = computeEffectivePriority` for all affected threads. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/Propagate.lean` | Medium |
| V3-I | SV-2 | **Update `isBetterCandidate` to use `effectivePriority`.** Modify `isBetterCandidate` (Selection.lean:38) to compare `effectivePriority` instead of `priority`. The signature changes from accepting `Priority` to accepting `Priority` (same type — the caller now passes `tcb.effectivePriority` instead of `tcb.priority`). Re-prove `isBetterCandidate_irrefl`, `isBetterCandidate_asymm`, `isBetterCandidate_transitive` — these are structurally identical proofs since the comparison logic is unchanged. | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | Small |
| V3-J | SV-2 | **Update `RunQueue` bucketing for effective priority.** Modify `RunQueue.insert` (RunQueue.lean:103) to accept and bucket by `effectivePriority`. Modify `RunQueue.remove` (RunQueue.lean:176) — no signature change needed since it uses `threadPriority` lookup. Update `schedulerPriorityMatch` (Invariant.lean:272) to assert `threadPriority[tid] = tcb.effectivePriority`. Update `maxPriority` tracking to use effective priority values. Re-prove `insert_maxPriority_consistency` and existing bridge lemmas (`mem_insert`, `mem_remove`, etc. — structurally unchanged). | `SeLe4n/Kernel/Scheduler/RunQueue.lean`, `SeLe4n/Kernel/Scheduler/Invariant.lean` | Medium |
| V3-K | SV-2 | **Integrate PIP into Call path.** Modify the Call IPC path (the transition that establishes `blockedOnReply`) to call `propagatePriorityInheritance` on the server thread after the client enters `blockedOnReply`. The call sequence: (1) client enters `blockedOnReply epId (some serverId)`, (2) `propagatePriorityInheritance st serverId` walks upward, boosting effective priorities. | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | Medium |
| V3-L | SV-2 | **Integrate PIP revert into Reply path.** Modify the Reply IPC path to call `revertPriorityInheritance` on the replying server thread after the client is unblocked. If the server's effective priority changed, perform RunQueue remove-then-insert to migrate it to the new bucket. This ensures the server drops back to its correct effective priority immediately upon completing the reply. | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | Medium |
| V3-M | SV-2 | **Prove `updateEffectivePriority` preserves scheduler component invariants.** Create `SeLe4n/Kernel/Scheduler/PriorityInheritance/Preservation.lean`. Prove 4 per-component lemmas: (1) `update_preserves_queueCurrentConsistent` — remove-then-insert preserves dequeue-on-dispatch (reuse `not_mem_remove_self` + `mem_insert`); (2) `update_preserves_runQueueUnique` — reuse `remove_preserves_nodup` + `insert_preserves_nodup`; (3) `update_preserves_currentThreadValid` — objects unchanged at current TID; (4) `update_preserves_currentThreadInActiveDomain` — domain field unchanged. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/Preservation.lean` | Medium |
| V3-N | SV-2 | **Prove `propagatePriorityInheritance` preserves `schedulerInvariantBundleFull`.** In the same file, compose V3-M per-component lemmas across the chain walk. By induction on chain length: each step applies `updateEffectivePriority` which preserves all components (V3-M), and the invariant is transitive across steps. Handle the additional bundle components: `timeSlicePositive` (time-slice untouched), `edfCurrentHasEarliestDeadline` (key case: if current thread's effective priority changes, it may need re-selection — prove this case separately), `contextMatchesCurrent` (registers untouched), `runnableThreadsAreTCBs` (objects structure preserved), `schedulerPriorityMatch` (updated by RunQueue migration). Bundle composition: `⟨comp1, ..., comp7⟩`. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/Preservation.lean` | Medium |
| V3-O | SV-2 | **Prove PIP preserves IPC invariants (frame preservation).** In the same file, prove that `propagatePriorityInheritance` and `revertPriorityInheritance` do not modify IPC state fields (`tcb.ipcState`), endpoint queues, notification wait lists, or pending messages. The propagation only touches `tcb.effectivePriority` and `RunQueue` bucket placement. Prove: (1) `propagate_preserves_ipcInvariantFull` via backward transport (IPC objects unchanged); (2) `propagate_preserves_dualQueueSystemInvariant` — queue links preserved because `effectivePriority` update uses `storeTcbQueueLinks`-free path; (3) `propagate_preserves_crossSubsystemInvariant` — frame preservation. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/Preservation.lean` | Medium |
| V3-P | SV-2 | **Prove single-step inversion bound.** Create `SeLe4n/Kernel/Scheduler/PriorityInheritance/BoundedInversion.lean`. Prove `pip_single_step_bound`: if thread H (priority P_H) is `blockedOnReply` on server S, and S has `effectivePriority ≥ P_H` (from PIP), then S is selected within `WCRT(P_H)` ticks. This is a direct application of the V1 `bounded_scheduling_latency` theorem (V1-L) with `effectivePriority` substituted for priority. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/BoundedInversion.lean` | Small |
| V3-Q | SV-2 | **Prove transitive inversion bound.** In the same file, prove `pip_bounded_inversion`: if thread H is `blockedOnReply` on server S, and the blocking chain from S has depth D, then H is transitively blocked for at most `D × WCRT(P_H)` ticks. Proof by induction on D: base case D=1 uses `pip_single_step_bound` (V3-P); inductive step composes the bound for the next link in the chain. The chain depth is bounded by thread count (from `blockingChain_acyclic`, V3-C). | `SeLe4n/Kernel/Scheduler/PriorityInheritance/BoundedInversion.lean` | Medium |
| V3-R | SV-2 | **Prove PIP determinism.** In the same file, prove `pip_deterministic`: `propagatePriorityInheritance` and `revertPriorityInheritance` produce identical results given identical input states. This follows immediately from the fact that both are defined as pure functions (no monadic state, no IO) over the blocking graph, which is fully determined by the `SystemState`. The proof is `rfl` or structural unfolding. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/BoundedInversion.lean` | Trivial |
| V3-S | — | **Create re-export hub.** Create `SeLe4n/Kernel/Scheduler/PriorityInheritance.lean` as a thin import-only file re-exporting `BlockingGraph`, `Compute`, `Propagate`, `Preservation`, and `BoundedInversion`. | `SeLe4n/Kernel/Scheduler/PriorityInheritance.lean` | Trivial |
| V3-T | — | **Add test coverage.** Add test cases: (1) PIP activates on Call to lower-priority server — `effectivePriority` elevated, (2) PIP deactivates on Reply — `effectivePriority` reverted, (3) transitive PIP through chain of 3 threads, (4) PIP does not affect threads outside the blocking chain, (5) `effectivePriority ≥ priority` always holds, (6) RunQueue bucket placement matches `effectivePriority` after propagation. | `tests/PriorityInheritanceSuite.lean`, `lakefile.lean` | Small |
| V3-U | — | **Documentation sync.** Update `docs/spec/SELE4N_SPEC.md` with PIP semantics (effective priority, blocking graph, propagation/reversion). Update `docs/CLAIM_EVIDENCE_INDEX.md` with bounded-inversion claim referencing `pip_bounded_inversion`. Update `CLAUDE.md` source layout for `Scheduler/PriorityInheritance/`. Regenerate `docs/codebase_map.json`. | `docs/spec/SELE4N_SPEC.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, `CLAUDE.md`, `docs/codebase_map.json` | Small |

**Intra-phase ordering constraints:**
- Type foundation: V3-A (TCB field) must come first
- Graph model: V3-A → V3-B → V3-C (define graph → prove acyclicity)
- Compute: V3-B → V3-D (graph model → effective priority computation)
- Propagation: V3-D → V3-E → V3-F → V3-G (compute → update single → chain walk → correctness)
- Revert: V3-E → V3-H (update single → revert uses same building block)
- V3-F/V3-G and V3-H can run in parallel (propagate vs revert)
- Scheduler integration: V3-F → V3-I → V3-J (chain walk → isBetterCandidate → RunQueue)
- IPC integration: V3-F + V3-H → V3-K/V3-L (parallel Call/Reply integration)
- Preservation proofs: V3-J + V3-K + V3-L → V3-M → V3-N (component → bundle → IPC frame)
- V3-N and V3-O are independent (scheduler vs IPC preservation)
- Liveness: V3-N + V1-L → V3-P → V3-Q → V3-R
- Infrastructure: V3-R → V3-S → V3-T → V3-U (sequential post-proof)

---

## 7. Phase V4 — MCS Scheduling Contexts (v0.21.3)

**Scope**: Introduce scheduling context objects that decouple CPU time budgets
from thread identity, enabling passive servers (zero-priority servers that
borrow client scheduling contexts), hard bandwidth reservation, and timeout
endpoints. This is the complete solution that subsumes PIP and adds CPU resource
accounting.

**Rationale**: MCS (Mixed-Criticality Scheduling) contexts are seL4's answer to
the same starvation problems addressed in V1–V3. Rather than patching individual
issues, MCS introduces a first-class scheduling abstraction: a `SchedContext`
kernel object that holds a CPU budget, period, and priority. Threads are bound
to scheduling contexts; when a thread makes a Call IPC, it donates its scheduling
context to the server, which then executes with the client's budget and priority.
This naturally solves priority inversion (the server runs at the client's
priority), enables passive servers (servers with no scheduling context of their
own), and provides hard CPU budgets (a thread cannot exceed its budget without
replenishment). seLe4n would be the first kernel to provide machine-checked
proofs of MCS scheduling context correctness.

**Dependencies**: V1 (trace model), V2 (timeout infrastructure), V3 (effective
priority mechanism, blocking graph). Also depends on WS-U platform types for
hardware timer resolution.

**Gate**: `test_full.sh` passes. `SchedContext` object type fully integrated.
Budget accounting proven correct. Passive server pattern works end-to-end.
Timeout endpoints functional. No `sorry`, no `axiom`. Module builds verified.

**Sub-tasks (24):**

| ID | Finding | Description | Files | Estimate |
|----|---------|-------------|-------|----------|
| V4-A | SV-1, SV-2, SV-3 | **Define `SchedContext` kernel object type.** Add `SchedContext` structure to `Model/Object/Types.lean`: fields `budget : Nat` (ticks per period), `period : Nat` (replenishment period), `consumed : Nat` (ticks consumed in current period), `basePriority : Priority`, `boundThread : Option ThreadId` (currently bound thread), `replenishmentTime : Nat` (next replenishment tick). Add `.schedContext` constructor to `KernelObject` inductive. Update all exhaustive `match` on `KernelObject` with the new constructor (lifecycle cleanup, object store, etc.). | `SeLe4n/Model/Object/Types.lean` | Medium |
| V4-B | SV-1, SV-2 | **Define scheduling context capability.** Add `SchedContextCap` to capability types with rights: `Bind`, `Unbind`, `SetParams`. Add `SchedContextId` typed identifier to `SeLe4n/Prelude.lean` following the existing typed-identifier pattern (`ThreadId`, `ObjId`, etc.). | `SeLe4n/Model/Object/Types.lean`, `SeLe4n/Prelude.lean` | Medium |
| V4-C | SV-1, SV-2 | **Add `schedContext : Option ObjId` to TCB.** Add the binding field with default `none`. The TCB's effective scheduling parameters are now derived from its bound scheduling context. If `schedContext = none`, the thread is not schedulable (passive server pattern). Keep `priority` as base priority and `timeSlice` for legacy paths during migration. | `SeLe4n/Model/Object/Types.lean` | Small |
| V4-D | SV-1 | **Implement budget consumption.** Create `SeLe4n/Kernel/SchedContext/Core.lean`. Implement `consumeBudget (scId : ObjId) (ticks : Nat) : Kernel Unit` — looks up `SchedContext`, increments `consumed` by `ticks`, returns error if `consumed > budget`. Implement `budgetExhausted (sc : SchedContext) : Bool` — returns `sc.consumed ≥ sc.budget`. | `SeLe4n/Kernel/SchedContext/Core.lean` | Small |
| V4-E | SV-1 | **Implement budget replenishment.** In the same file, implement `replenishBudget (scId : ObjId) (currentTick : Nat) : Kernel Unit` — if `currentTick ≥ sc.replenishmentTime`, resets `consumed := 0` and sets `replenishmentTime := currentTick + sc.period`. Implement `needsReplenishment (sc : SchedContext) (currentTick : Nat) : Bool`. | `SeLe4n/Kernel/SchedContext/Core.lean` | Small |
| V4-F | SV-1 | **Implement budget-aware preemption in `timerTick`.** Modify `timerTick` (Core.lean:313) to add a budget-check path: after the existing time-slice check, if the current thread has `schedContext = some scId`, call `consumeBudget scId 1`. If `budgetExhausted`, preempt the thread (re-enqueue, call `schedule`). The existing time-slice path remains as fallback for threads without scheduling contexts. | `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | Medium |
| V4-G | SV-1 | **Implement replenishment in `timerTick`.** Add a replenishment sweep to the timer path: for each scheduling context in `st.objects` with `needsReplenishment sc currentTick`, call `replenishBudget`. If the bound thread was preempted due to budget exhaustion and is still runnable-eligible, re-enqueue it. This can be a separate `replenishmentSweep : Kernel Unit` called from `timerTick`. | `SeLe4n/Kernel/Scheduler/Operations/Core.lean`, `SeLe4n/Kernel/SchedContext/Core.lean` | Medium |
| V4-H | SV-2 | **Implement `donateSchedContext` (unbind + rebind).** Create `SeLe4n/Kernel/SchedContext/Donation.lean`. Implement the donation as two atomic steps: (1) `unbindSchedContext (fromTid : ThreadId) : Kernel ObjId` — clears `fromTid.schedContext`, sets `sc.boundThread := none`, removes `fromTid` from run queue (now unschedulable); (2) `bindSchedContext (toTid : ThreadId) (scId : ObjId) : Kernel Unit` — sets `toTid.schedContext := some scId`, sets `sc.boundThread := some toTid`, derives effective priority from `sc.basePriority`, ensures `toTid` is runnable. | `SeLe4n/Kernel/SchedContext/Donation.lean` | Medium |
| V4-I | SV-2 | **Implement `donateSchedContext` composite.** In the same file, implement `donateSchedContext (fromTid toTid : ThreadId) : Kernel Unit` as the composition: `let scId ← unbindSchedContext fromTid; bindSchedContext toTid scId`. Validate preconditions: `fromTid` must have a scheduling context, `toTid` must not already have one (passive server). Return appropriate errors for invalid states. | `SeLe4n/Kernel/SchedContext/Donation.lean` | Small |
| V4-J | SV-2 | **Implement `returnSchedContext`.** In the same file, implement `returnSchedContext (fromTid toTid : ThreadId) : Kernel Unit` — symmetric to donation: unbinds from server `fromTid`, rebinds to client `toTid`. The server becomes unschedulable (passive), the client becomes schedulable. Reuses `unbindSchedContext` and `bindSchedContext` building blocks from V4-H. | `SeLe4n/Kernel/SchedContext/Donation.lean` | Small |
| V4-K | SV-2 | **Integrate donation into Call/Reply.** Modify the Call path (Endpoint.lean) to call `donateSchedContext` after establishing `blockedOnReply`. Modify the Reply path to call `returnSchedContext` before unblocking the client. Guard donation behind `fromTid.schedContext.isSome` check — if the client has no scheduling context, skip donation (non-MCS path). | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | Medium |
| V4-L | SV-3 | **Implement timeout endpoints.** Create `SeLe4n/Kernel/SchedContext/TimeoutEndpoint.lean`. Add `timeoutEndpoint : Option ObjId` field to `SchedContext`. When budget expires in `timerTick` (V4-F), if `sc.timeoutEndpoint = some notifId`, call `notificationSignal notifId badge` instead of (or in addition to) preempting. This enables user-space timeout handling. | `SeLe4n/Kernel/SchedContext/TimeoutEndpoint.lean` | Medium |
| V4-M | SV-1 | **Define `SchedContext` invariants.** Create `SeLe4n/Kernel/SchedContext/Invariant.lean`. Define: `budgetValid (sc : SchedContext) : Prop` (`consumed ≤ budget`), `periodPositive (sc : SchedContext) : Prop` (`period > 0`), `bindingConsistent (st : SystemState) : Prop` (bidirectional: `sc.boundThread = some tid ↔ tid.schedContext = some scId`), `timeoutEndpointValid (st : SystemState) : Prop` (if `sc.timeoutEndpoint = some notifId`, notification exists). Define `schedContextInvariant` as the conjunction. | `SeLe4n/Kernel/SchedContext/Invariant.lean` | Medium |
| V4-N | SV-1 | **Prove budget accounting correctness.** Create `SeLe4n/Kernel/SchedContext/Preservation.lean`. Prove: (1) `consumeBudget_monotone` — `consumed' = consumed + ticks` and `consumed' ≤ budget` (or error); (2) `replenishBudget_resets` — `consumed' = 0` and `replenishmentTime' = currentTick + period`; (3) `consumeBudget_preserves_periodPositive` — period unchanged; (4) `replenishBudget_preserves_budgetValid` — `0 ≤ budget` (trivially true). | `SeLe4n/Kernel/SchedContext/Preservation.lean` | Small |
| V4-O | SV-2 | **Prove `unbindSchedContext` preserves invariants.** In the same file, prove per-component: (1) `unbind_preserves_queueCurrentConsistent` — removing from run queue, current cleared if it was the unbound thread; (2) `unbind_preserves_runQueueUnique` — `remove_preserves_nodup`; (3) `unbind_clears_binding` — `sc.boundThread = none` and `tid.schedContext = none` after unbind. Compose into `unbind_preserves_schedContextInvariant` (binding consistency: the pair is atomically cleared). | `SeLe4n/Kernel/SchedContext/Preservation.lean` | Medium |
| V4-P | SV-2 | **Prove `bindSchedContext` preserves invariants.** In the same file, prove per-component: (1) `bind_preserves_queueCurrentConsistent` — `ensureRunnable` adds to queue, follows existing pattern; (2) `bind_preserves_runQueueUnique` — `ensureRunnable_nodup`; (3) `bind_establishes_binding` — `sc.boundThread = some tid` and `tid.schedContext = some scId`. Compose into `bind_preserves_schedContextInvariant`. | `SeLe4n/Kernel/SchedContext/Preservation.lean` | Medium |
| V4-Q | SV-2 | **Prove `donateSchedContext` preserves full invariant bundle.** Compose V4-O + V4-P: donation = unbind + bind. Prove `donate_preserves_schedulerInvariantBundleFull` by composing unbind (removes donor from queue) and bind (adds recipient to queue). Prove `donate_preserves_schedContextInvariant` by showing binding consistency is maintained atomically (old cleared, new established). Frame-preserve IPC invariants (donation doesn't touch IPC queues or notifications). | `SeLe4n/Kernel/SchedContext/Preservation.lean` | Medium |
| V4-R | SV-2 | **Prove `returnSchedContext` preserves full invariant bundle.** Symmetric to V4-Q: return = unbind (server) + bind (client). Prove `return_preserves_schedulerInvariantBundleFull` and `return_preserves_schedContextInvariant`. The server loses its scheduling context and becomes unschedulable; the client regains it. Frame-preserve IPC invariants. | `SeLe4n/Kernel/SchedContext/Preservation.lean` | Medium |
| V4-S | SV-1 | **Prove budget-bounded execution.** Create `SeLe4n/Kernel/SchedContext/Liveness.lean`. Prove `budget_bounded_execution`: a thread with scheduling context `sc` executes for at most `sc.budget` ticks per period. Proof: `consumeBudget_monotone` shows `consumed` increases monotonically; `budgetExhausted` triggers preemption (V4-F); therefore `consumed ≤ budget` bounds execution to `budget` ticks. After budget exhaustion, thread is not re-enqueued until replenishment (V4-G). Uses V1 trace model. | `SeLe4n/Kernel/SchedContext/Liveness.lean` | Medium |
| V4-T | SV-2 | **Prove passive server correctness.** In the same file, prove `passive_server_executes_at_client_priority`: when a passive server (no own scheduling context) receives a donated scheduling context via Call, it executes at the donor's `basePriority` and within the donor's `budget`. Proof: `bindSchedContext` sets effective priority from `sc.basePriority` (V4-P); `consumeBudget` bounds execution within `sc.budget` (V4-S). Priority inversion is eliminated because the server literally holds the client's scheduling parameters. | `SeLe4n/Kernel/SchedContext/Liveness.lean` | Medium |
| V4-U | — | **Add `SyscallId` variants for scheduling context operations.** Add 4 new variants to `SyscallId` in `Model/Object/Types.lean`: `SchedControl_Configure`, `SchedContext_Bind`, `SchedContext_Unbind`, `SchedContext_Consumed`. Add typed argument decode structures in `Architecture/SyscallArgDecode.lean` for each syscall (following existing patterns: `struct SchedControlConfigureArgs`, etc.). | `SeLe4n/Model/Object/Types.lean`, `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` | Medium |
| V4-V | — | **Add API wrappers and policy gates.** Add syscall handlers in `Kernel/API.lean` that dispatch to the underlying operations (V4-D, V4-E, V4-H/I/J). Gate `SchedControl_Configure` through information-flow policy wrapper (only the scheduling authority domain may configure budgets). Gate `SchedContext_Bind`/`Unbind` through capability checks. `SchedContext_Consumed` is read-only (no gate needed beyond capability). | `SeLe4n/Kernel/API.lean`, `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` | Medium |
| V4-W | — | **Add comprehensive test coverage.** Test cases: (1) budget exhaustion triggers preemption, (2) replenishment resets consumed, (3) donation on Call transfers scheduling context, (4) return on Reply restores scheduling context, (5) passive server with no scheduling context is not schedulable, (6) passive server becomes schedulable after donation, (7) timeout endpoint signals on budget expiry, (8) binding consistency holds across all operations, (9) `SchedControl_Configure` respects information-flow policy. | `tests/SchedContextSuite.lean`, `lakefile.lean` | Medium |
| V4-X | — | **Documentation and closure.** Update `docs/spec/SELE4N_SPEC.md` with MCS scheduling context semantics (budget, period, donation, passive servers, timeout endpoints). Update `docs/CLAIM_EVIDENCE_INDEX.md` with budget-bounded execution and passive server claims. Update `CLAUDE.md` source layout for all new directories (`SchedContext/`). Update `docs/WORKSTREAM_HISTORY.md` with WS-V summary. Update `README.md` metrics. Regenerate `docs/codebase_map.json`. Update `CHANGELOG.md` with v0.21.0–v0.21.3 entries. | `docs/spec/SELE4N_SPEC.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, `CLAUDE.md`, `docs/WORKSTREAM_HISTORY.md`, `README.md`, `CHANGELOG.md`, `docs/codebase_map.json` | Medium |

**Intra-phase ordering constraints:**
- Type foundation: V4-A → V4-B → V4-C (object type → capability → TCB binding)
- Budget core: V4-A → V4-D → V4-E (object → consume → replenish)
- Timer integration: V4-D + V4-E → V4-F → V4-G (accounting → preemption → replenishment sweep)
- Donation building blocks: V4-C → V4-H (TCB binding → unbind/bind primitives)
- Donation composite: V4-H → V4-I → V4-J (primitives → donate → return)
- IPC integration: V4-I + V4-J → V4-K (donate/return → Call/Reply hooks)
- Timeout: V4-D + V4-F → V4-L (budget + preemption → timeout endpoint)
- Invariants: V4-A + V4-C → V4-M (types → predicates)
- Budget proofs: V4-D + V4-E → V4-N (accounting → correctness)
- Donation proofs: V4-H → V4-O → V4-P → V4-Q (unbind → bind → donate composite)
- Return proof: V4-O + V4-P → V4-R (symmetric to donate)
- Liveness: V4-F + V4-N → V4-S, V4-K + V4-Q → V4-T (preservation → liveness)
- Syscall: V4-K + V4-L → V4-U → V4-V (ops defined → types → API wrappers)
- Testing: V4-V → V4-W → V4-X (API → tests → docs)
- V4-D/V4-E and V4-H are independent chains (can run in parallel after V4-A/V4-C)

---

## 8. Scope Summary

### 8.1 Sub-task Count by Phase

| Phase | Version | Sub-tasks | Complexity | Nature |
|-------|---------|-----------|-----------|--------|
| V1 — Bounded Latency Theorem | v0.21.0 | 15 | Medium | Proof-only (zero kernel code changes) |
| V2 — IPC Timeout Mechanism | v0.21.1 | 18 | High | New transitions + preservation proofs |
| V3 — Priority Inheritance Protocol | v0.21.2 | 21 | High | TCB extension + scheduler + proofs |
| V4 — MCS Scheduling Contexts | v0.21.3 | 24 | Very High | New kernel object type + full subsystem |
| **Total** | | **78** | | |

### 8.2 Starvation Vector Coverage

| ID | Vector | Severity | Addressed In | Resolution |
|----|--------|----------|-------------|------------|
| SV-1 | Strict priority starvation | HIGH | V1 (bound), V4 (budget) | V1: conditional WCRT bound. V4: hard CPU budget prevents monopoly. |
| SV-2 | Priority inversion via Call/Reply | HIGH | V3 (PIP), V4 (donation) | V3: priority inheritance bounds inversion. V4: scheduling context donation eliminates it. |
| SV-3 | Unbounded IPC blocking | HIGH | V2 (timeout) | V2: optional timeout on all blocking IPC operations. |
| SV-4 | Notification LIFO ordering | MEDIUM | Deferred | See Section 9 (deferred items). |
| SV-5 | Domain schedule imbalance | MEDIUM | V1 (bound) | V1: domain rotation bound proves each domain gets CPU within bounded time. |
| SV-6 | Run queue cycling without bound | LOW | V1 (bound) | V1: FIFO progress within priority band proven. |

### 8.3 Files Impacted by Phase

| Phase | New Lean Files | Modified Lean Files | New Test Files | Doc Files |
|-------|---------------|--------------------|--------------|---------:|
| V1 | ~7 (Liveness/: TraceModel, TimerTick, Yield, BandExhaustion, DomainRotation, WCRT, re-export) | 0 | 1 | 4 |
| V2 | ~3 (IPC/Operations/Timeout, IPC/Invariant/TimeoutPreservation, IPC/Liveness/TimeoutBound) | ~5 (Types, Endpoint, Core, Preservation, DualQueue/Core) | 1–2 | 4 |
| V3 | ~6 (PriorityInheritance/: BlockingGraph, Compute, Propagate, Preservation, BoundedInversion, re-export) | ~4 (Types, Selection, RunQueue, Endpoint) | 1 | 4 |
| V4 | ~7 (SchedContext/: Core, Donation, TimeoutEndpoint, Invariant, Preservation, Liveness, re-export) | ~6 (Types, Prelude, Core, Endpoint, API, SyscallArgDecode) | 1 | 7 |
| **Total** | **~23** | **~15** | **4–5** | **19** |

### 8.4 Effort Distribution

| Estimate | V1 | V2 | V3 | V4 | Total |
|----------|----|----|----|----|-------|
| Trivial | 1 | 0 | 2 | 0 | **3** |
| Small | 9 | 6 | 6 | 6 | **27** |
| Medium | 5 | 12 | 13 | 18 | **48** |
| Large | 0 | 0 | 0 | 0 | **0** |
| **Total** | **15** | **18** | **21** | **24** | **78** |

**Note**: All original Large tasks have been decomposed into Medium and Small
sub-tasks. No individual sub-task requires more than ~1 day of focused work.
The decomposition preserves the original proof pattern: component lemmas composed
into bundle proofs, matching the project's established `⟨comp1, comp2, ...⟩`
composition style.

---

## 9. Deferred Items

### 9.1 Deferred Starvation Vectors

| ID | Vector | Severity | Reason for Deferral |
|----|--------|----------|---------------------|
| SV-4 | Notification LIFO ordering | MEDIUM | Notification LIFO semantics match seL4's design. Changing to FIFO would break semantic compatibility. The practical impact is limited: notification signals typically wake exactly one waiter, and notification-heavy patterns use bounded-badge coalescing. A fairness wrapper (round-robin over waiters) could be added as a future enhancement but is not critical for the liveness story. |

### 9.2 Deferred Enhancements

| Enhancement | Description | Reason for Deferral |
|-------------|-------------|---------------------|
| Priority aging / decay | Gradually boost starved threads' effective priority over time | Violates strict priority ordering, incompatible with hard real-time guarantees. MCS budgets (V4) provide a better mechanism for mixed-criticality scheduling. |
| Priority ceiling protocol (PCP) | Alternative to PIP that prevents deadlock by ceiling-setting | PIP (V3) is simpler and sufficient for the acyclic blocking graph guaranteed by `tcbQueueChainAcyclic`. PCP adds complexity without clear benefit given the existing acyclicity proof. |
| Deadline-based starvation prevention | Threads that miss deadlines get priority boost | Requires deadline monitoring infrastructure not yet in the kernel. Could be added atop V4's budget accounting in a future workstream. |
| Non-interference liveness | Prove that information-flow policy does not create liveness-visible side channels | Requires extending the NI projection model (InformationFlow/Projection.lean) with trace-level properties. Orthogonal to scheduling liveness and better addressed in a dedicated security workstream. |
| User-space yield hints | Syscall for cooperative yield with priority hint | Low value given preemptive scheduling with MCS budgets. User-space scheduling libraries can implement this atop existing mechanisms. |

### 9.3 Future Workstream Candidates

| Candidate | Scope | Prerequisite |
|-----------|-------|-------------|
| WS-W: Real-Time Analysis Framework | Formal schedulability analysis tools (Rate Monotonic, response-time analysis) built on V1 trace model | WS-V (V1 WCRT theorem) |
| WS-X: Mixed-Criticality Scheduling | Criticality-level assignment, mode changes, graceful degradation | WS-V (V4 MCS contexts) |

---

## 10. Technical Risks

### 10.1 Implementation Risks

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| V1 WCRT proof requires stronger assumptions than expected | Medium | Low | V1 is proof-only with zero code changes. If the bound requires assumptions (e.g., no higher-priority threads perpetually runnable), state them as explicit hypotheses. A conditional bound is still valuable. |
| V2 timeout forced removal breaks IPC queue invariants | Medium | High | Reuse proven `spliceOutMidQueueNode` and `removeFromAllEndpointQueues` infrastructure from WS-T5. The forced removal is structurally identical to lifecycle cleanup — same proof patterns apply. |
| V3 PIP propagation loop exceeds reasonable fuel bound | Low | Medium | Blocking chain depth is bounded by thread count (finite). `tcbQueueChainAcyclic` prevents cycles. Use `Nat.lt_wfRel` on chain length for termination. |
| V3 effective priority change invalidates RunQueue bucket placement | Medium | High | Re-insert thread at new effective priority after propagation. Prove that remove-then-insert preserves `RunQueue.wellFormed`. This pattern already exists in `timerTick` (Core.lean:313). |
| V4 `SchedContext` object type breaks `KernelObject` exhaustiveness | Low | Medium | Add `.schedContext` constructor to `KernelObject` inductive. Update all `match` expressions (lifecycle cleanup, object store, etc.). Follow the pattern used when `Notification` was added. |
| V4 scheduling context donation creates unexpected aliasing | Medium | High | Enforce single-binding invariant: a scheduling context is bound to at most one thread at a time. Prove `bindingConsistent` bidirectionally. Donation atomically unbinds old + binds new. |
| V4 budget replenishment timing interacts badly with domain scheduling | Medium | Medium | Replenishment is per-scheduling-context, independent of domain schedule. Prove that replenishment does not violate `currentThreadInActiveDomain` — the thread's domain doesn't change, only its budget resets. |

### 10.2 Schedule Risks

| Risk | Mitigation |
|------|------------|
| V4 is very large (24 sub-tasks) and may slip | V1–V3 are independently valuable. Ship V1 as soon as it's ready — it provides the first formal WCRT bound with zero code risk. V2 and V3 each close specific starvation vectors. V4 can be split into sub-phases (V4a: types + budget V4-A–G, V4b: donation V4-H–K, V4c: invariants + proofs V4-M–T, V4d: syscalls + tests V4-U–X) if needed. |
| V3 depends on V2's type changes, creating a serial bottleneck | V3-A (add `effectivePriority` field) and V3-B/V3-C (blocking graph model) can be prototyped independently of V2's timeout field. Only V3-H/V3-I (Call/Reply integration) depend on V2's modified IPC state type. |
| WS-U (RPi5 hardware) may need scheduler changes that conflict with V2–V4 | WS-V and WS-U operate on disjoint file sets: WS-U owns `Platform/RPi5/`, WS-V owns `Scheduler/Liveness/`, `Scheduler/PriorityInheritance/`, `SchedContext/`, and IPC timeout extensions. The only shared files are `Model/Object/Types.lean` (additive fields) and `Scheduler/Operations/Core.lean` (timer tick modification). Coordinate field additions via explicit merge points. |

---

## 11. Invariant Landscape

This section maps how WS-V's new mechanisms interact with the existing
invariant proof surface, to ensure preservation proof coverage is complete.

### 11.1 Invariants Preserved by Each Phase

| Invariant Bundle | V1 | V2 | V3 | V4 |
|-----------------|----|----|----|----|
| `schedulerInvariantBundleFull` | Read-only (no state change) | V2-M: `ensureRunnable` on timeout unblock | V3-N: effective priority bucket migration | V4-F: budget-based preemption, V4-Q/R: donation/return |
| `ipcInvariantFull` | Read-only | V2-L: notification state transition on timeout | V3-O: frame-preserved (PIP doesn't touch IPC) | V4-K: donation integrated into Call/Reply |
| `dualQueueSystemInvariant` | Read-only | V2-K: forced mid-queue removal | V3-O: frame-preserved | V4-K: donation doesn't modify queues |
| `crossSubsystemInvariant` | Read-only | V2-N: TCB persists after timeout unblock | Frame-preserved | V4-M: new `schedContextBindingConsistent` added |
| `kernelInvariant` (base triad + domain) | Read-only | V2-P: composed from above | V3-N: composed from above | V4-F/Q/R: composed from above |

### 11.2 New Invariant Predicates Introduced

| Phase | Predicate | Description |
|-------|-----------|-------------|
| V1 | `validTrace` | Trace of scheduler steps where each precondition holds |
| V1 | `selectedAt` | Thread is current at trace index k |
| V2 | `timeoutMonotone` | Timeout countdown decreases by 1 each tick (or thread unblocks) |
| V2 | `timeoutBounded` | Thread with `timeout = some n` unblocks within n ticks |
| V3 | `effectivePriorityGeBase` | `effectivePriority ≥ priority` always |
| V3 | `effectivePriorityConsistent` | `effectivePriority = computeEffectivePriority` at all times |
| V3 | `pipBoundedInversion` | Inversion bounded by chain depth × WCRT |
| V4 | `budgetValid` | `consumed ≤ budget` |
| V4 | `periodPositive` | `period > 0` |
| V4 | `bindingConsistent` | Bidirectional TCB ↔ SchedContext binding |
| V4 | `budgetBoundedExecution` | Thread executes ≤ budget ticks per period |
| V4 | `passiveServerPriority` | Donated scheduling context determines server's priority |

---

## 12. Workstream Naming Convention

This workstream is designated **WS-V** (following the alphabetical sequence
after WS-U, the planned Raspberry Pi 5 hardware binding workstream). The "V"
can be read as "Vitality" — ensuring threads make progress and the kernel
provides liveness guarantees alongside its existing safety properties.

| Workstream | Focus | Version Range |
|------------|-------|---------------|
| WS-T | Deep-Dive Audit Remediation | v0.20.0–v0.20.7 |
| WS-U (planned) | Raspberry Pi 5 Hardware Binding | v0.21.0+ |
| **WS-V** | **Kernel Starvation Prevention & Liveness** | **v0.21.0–v0.21.3** |

**Note**: WS-V's version range overlaps with WS-U because the workstreams are
independent and can execute in parallel on disjoint file sets. Version numbers
may be adjusted during execution to maintain sequential ordering if WS-U
ships first.

---

## 13. Acceptance Criteria Summary

| Phase | Test Gate | Proof Gate | Code Gate |
|-------|-----------|------------|-----------|
| V1 | `test_full.sh` passes | All liveness theorems compile; `bounded_scheduling_latency` proven | Zero code changes to existing files |
| V2 | `test_full.sh` passes; timeout tests pass | `ipcTimeoutTick` preserves `ipcInvariantFull`, `dualQueueSystemInvariant`, `schedulerInvariantBundleFull`, `crossSubsystemInvariant` | `ipcTimeoutTick` integrated into timer path |
| V3 | `test_full.sh` passes; PIP tests pass | `propagatePriorityInheritance` and `revertPriorityInheritance` preserve full invariant bundles; `pip_bounded_inversion` proven | PIP activates on Call, deactivates on Reply |
| V4 | `test_full.sh` passes; SchedContext tests pass | Budget accounting, donation, return all preserve invariant bundles; `budget_bounded_execution` and `passive_server_executes_at_client_priority` proven | Full MCS syscall interface, timeout endpoints |

**Universal gates (all phases)**:
- Zero `sorry` in production proof surface
- Zero `axiom` in production proof surface
- Module build verified for every modified `.lean` file (`lake build <Module.Path>`)
- No website-linked paths renamed or removed (see `scripts/website_link_manifest.txt`)
- Documentation synchronized (spec, claims, source layout, codebase map)
