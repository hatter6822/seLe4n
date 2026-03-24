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
  after V1 completes; V2-E through V2-H (preservation proofs) depend on V2-D.
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

**Sub-tasks (12):**

| ID | Finding | Description | Files | Estimate |
|----|---------|-------------|-------|----------|
| V1-A | SV-6 | **Define trace model.** Create `SeLe4n/Kernel/Scheduler/Liveness/TraceModel.lean`. Define `SchedulerTrace` as a list of `SchedulerStep` (an inductive covering `timerTick`, `schedule`, `handleYield`, `switchDomain`, `scheduleDomain`). Define `validTrace` predicate: each step's precondition holds and postcondition state feeds into the next step. Define `selectedAt` predicate: thread `tid` is the `current` thread at trace index `k`. | `SeLe4n/Kernel/Scheduler/Liveness/TraceModel.lean` | Medium |
| V1-B | SV-6 | **Define counting predicates.** In the same or adjacent file, define `countHigherOrEqualPriority (tid : ThreadId) (st : SystemState) : Nat` — number of threads in `runQueue` with priority ≥ `tid`'s priority in the same domain. Define `maxQuantumInBand (tid : ThreadId) (st : SystemState) : Nat` — maximum `timeSlice` among those threads. These are pure read-only functions over existing state. | `SeLe4n/Kernel/Scheduler/Liveness/TraceModel.lean` | Small |
| V1-C | SV-6 | **Prove timer-tick monotonicity.** Create `SeLe4n/Kernel/Scheduler/Liveness/TimerTick.lean`. Prove `timerTick_decrements_timeSlice`: if `current = some tid` and `tcb.timeSlice > 1`, then after `timerTick`, `tcb'.timeSlice = tcb.timeSlice - 1`. This follows directly from the `timerTick` definition (Core.lean:313). | `SeLe4n/Kernel/Scheduler/Liveness/TimerTick.lean` | Small |
| V1-D | SV-6 | **Prove timer-tick preemption.** In the same file, prove `timerTick_preempts_at_one`: if `current = some tid` and `tcb.timeSlice ≤ 1`, then after `timerTick`, `tid` is re-enqueued and `schedule` is called. Combined with V1-C, this shows every thread is preempted within exactly `tcb.timeSlice` ticks. | `SeLe4n/Kernel/Scheduler/Liveness/TimerTick.lean` | Small |
| V1-E | SV-6 | **Prove yield rotates to back.** Create `SeLe4n/Kernel/Scheduler/Liveness/Yield.lean`. Prove `handleYield_rotates_to_back`: after `handleYield`, the yielding thread is at the tail of its priority bucket in `runQueue.byPriority`. Use `RunQueue.rotateToBack` semantics (RunQueue.lean:335). | `SeLe4n/Kernel/Scheduler/Liveness/Yield.lean` | Small |
| V1-F | SV-6 | **Prove FIFO progress within priority band.** In the same file, prove `fifo_progress_in_band`: if thread `tid` is at position `k` (0-indexed) in its priority bucket, and no higher-priority threads exist in the active domain, then `tid` is selected within `k × defaultTimeSlice` ticks (assuming all preceding threads exhaust their quantum without yielding early). This is the core intra-band fairness lemma. Proof by induction on `k`, using V1-C and V1-D at each step. | `SeLe4n/Kernel/Scheduler/Liveness/Yield.lean` | Large |
| V1-G | SV-1 | **Prove priority-band exhaustion.** Create `SeLe4n/Kernel/Scheduler/Liveness/BandExhaustion.lean`. Prove `higher_band_exhaustion`: if all threads at priority > P are eventually removed from the run queue (blocked, yielded to lower priority, or deleted), then a thread at priority P will be selected. This is a conditional liveness lemma — it does not prove that higher-priority threads *will* leave, only that *if* they do, progress occurs. | `SeLe4n/Kernel/Scheduler/Liveness/BandExhaustion.lean` | Medium |
| V1-H | SV-5 | **Prove domain rotation bound.** Create `SeLe4n/Kernel/Scheduler/Liveness/DomainRotation.lean`. Prove `domain_rotation_bound`: if `domainSchedule` has `D` entries with maximum length `L_max`, then every domain receives CPU time within `D × L_max` ticks. Uses `switchDomain` round-robin semantics (Core.lean:356) and modular index arithmetic. | `SeLe4n/Kernel/Scheduler/Liveness/DomainRotation.lean` | Medium |
| V1-I | SV-1, SV-6 | **Prove the main WCRT theorem.** Create `SeLe4n/Kernel/Scheduler/Liveness/WCRT.lean`. Prove `bounded_scheduling_latency`: if thread `tid` at priority P is in `runQueue`, `countHigherOrEqualPriority tid st ≤ N`, all threads in band have quantum ≤ Q, and `tid` is in domain with schedule entry length ≥ `N × Q`, then `tid` is selected within `N × Q` ticks from any valid trace. Composes V1-F (intra-band), V1-G (inter-band conditional), and V1-H (domain rotation). | `SeLe4n/Kernel/Scheduler/Liveness/WCRT.lean` | Large |
| V1-J | — | **Create re-export hub.** Create `SeLe4n/Kernel/Scheduler/Liveness.lean` as a thin import-only file re-exporting `TraceModel`, `TimerTick`, `Yield`, `BandExhaustion`, `DomainRotation`, and `WCRT`. Follow the project's re-export hub convention. | `SeLe4n/Kernel/Scheduler/Liveness.lean` | Trivial |
| V1-K | — | **Add test surface anchors.** Add invariant surface anchor tests in `tests/` that verify the new liveness theorems are reachable from the test harness. Follow existing anchor test patterns from `test_full.sh` (Tier 3). | `tests/LivenessSuite.lean`, `lakefile.lean` | Small |
| V1-L | — | **Documentation sync.** Update `docs/spec/SELE4N_SPEC.md` with the WCRT bound statement. Update `docs/CLAIM_EVIDENCE_INDEX.md` with new liveness claims. Update source layout in `CLAUDE.md` to include the new `Scheduler/Liveness/` directory. Regenerate `docs/codebase_map.json`. | `docs/spec/SELE4N_SPEC.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, `CLAUDE.md`, `docs/codebase_map.json` | Small |

**Intra-phase ordering constraints:**
- Trace model foundation: V1-A → V1-B (counting predicates need trace types)
- Timer-tick chain: V1-C → V1-D (preemption builds on decrement)
- Yield chain: V1-E → V1-F (FIFO progress builds on rotate semantics)
- Main theorem: V1-F + V1-G + V1-H → V1-I (WCRT composes all three)
- Infrastructure: V1-I → V1-J → V1-K → V1-L (sequential post-proof)
- V1-C/D and V1-E/F are independent chains (can run in parallel)
- V1-G and V1-H are independent of each other (can run in parallel)

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

**Sub-tasks (14):**

| ID | Finding | Description | Files | Estimate |
|----|---------|-------------|-------|----------|
| V2-A | SV-3 | **Extend ThreadIpcState with timeout.** Add optional `timeout : Option Nat` field to each blocking variant of `ThreadIpcState` (Types.lean:290–297): `blockedOnSend`, `blockedOnReceive`, `blockedOnCall`, `blockedOnReply`, `blockedOnNotification`. Default to `none` (no timeout). This is a backward-compatible extension — all existing pattern matches on `ThreadIpcState` continue to work because `timeout` is a field within each constructor, not a new constructor. | `SeLe4n/Model/Object/Types.lean` | Medium |
| V2-B | SV-3 | **Update IPC operations to accept timeout.** Modify `notificationWait` (Endpoint.lean:202), and the blocking paths of send/receive/call operations to accept an optional `timeout : Option Nat` parameter. Thread the timeout value into `storeTcbIpcState` calls. When `timeout = none`, behavior is identical to current (no timeout). When `timeout = some n`, the blocking state carries the countdown. | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | Medium |
| V2-C | SV-3 | **Update dual-queue enqueue for timeout.** Modify `endpointQueueEnqueue` (DualQueue/Core.lean:254) to store the timeout value in the enqueued thread's IPC state. Ensure the `alreadyWaiting` guard (line 264) still functions correctly with the new field. | `SeLe4n/Kernel/IPC/DualQueue/Core.lean` | Small |
| V2-D | SV-3 | **Implement `ipcTimeoutTick`.** Create a new kernel transition `ipcTimeoutTick : Kernel Unit` in a new file `SeLe4n/Kernel/IPC/Operations/Timeout.lean`. For each thread in the system with a blocking IPC state and `timeout = some n`: if `n ≤ 1`, forcibly unblock the thread (set `ipcState := .ready`, call `ensureRunnable`, remove from endpoint queue or notification wait list, set `pendingMessage := some (.error .timeout)`); if `n > 1`, decrement to `some (n - 1)`. This transition is called from `timerTick` (or a dedicated timeout tick handler). | `SeLe4n/Kernel/IPC/Operations/Timeout.lean` | Large |
| V2-E | SV-3 | **Implement forced endpoint queue removal.** In the timeout file, implement `forceRemoveFromEndpointQueue (tid : ThreadId) (epId : ObjId) (isReceiveQ : Bool) : Kernel Unit`. Reuse the splice logic from `removeFromAllEndpointQueues` (Lifecycle/Operations.lean:83) — the same `spliceOutMidQueueNode` + head/tail pointer patching. This ensures mid-queue removal is safe. | `SeLe4n/Kernel/IPC/Operations/Timeout.lean` | Medium |
| V2-F | SV-3 | **Implement forced notification wait list removal.** In the timeout file, implement `forceRemoveFromNotificationWaitList (tid : ThreadId) (notifId : ObjId) : Kernel Unit`. Filter `tid` from `notification.waitingThreads` (same pattern as `removeFromAllNotificationWaitLists`, Lifecycle/Operations.lean:98). | `SeLe4n/Kernel/IPC/Operations/Timeout.lean` | Small |
| V2-G | SV-3 | **Prove `ipcTimeoutTick` preserves `dualQueueSystemInvariant`.** The forced removal must maintain `intrusiveQueueWellFormed` (Defs.lean:107), `tcbQueueLinkIntegrity` (Defs.lean:121), and `tcbQueueChainAcyclic` (Defs.lean:145). Leverage the existing `endpointQueueRemoveDual_preserves_dualQueueSystemInvariant` proof structure from T4-D (IPC/Invariant/EndpointPreservation.lean). | `SeLe4n/Kernel/IPC/Invariant/TimeoutPreservation.lean` | Large |
| V2-H | SV-3 | **Prove `ipcTimeoutTick` preserves `ipcInvariantFull`.** Show that forced unblocking maintains `notificationQueueWellFormed` (state transitions from `.waiting` to `.idle` when last waiter is removed), `allPendingMessagesBounded` (timeout error message is bounded), and `badgeWellFormed` (no badge modification on timeout). | `SeLe4n/Kernel/IPC/Invariant/TimeoutPreservation.lean` | Medium |
| V2-I | SV-3 | **Prove `ipcTimeoutTick` preserves scheduler invariants.** Show that `ensureRunnable` on timeout-unblocked threads preserves `schedulerInvariantBundleFull`: the thread transitions from "blocked, not in runQueue" to "ready, in runQueue" — exactly the `ensureRunnable` pattern already proven in SchedulerLemmas.lean:55–122. | `SeLe4n/Kernel/IPC/Invariant/TimeoutPreservation.lean` | Medium |
| V2-J | SV-3 | **Prove `ipcTimeoutTick` preserves cross-subsystem invariants.** Show that `noStaleEndpointQueueReferences` (CrossSubsystem.lean:58) and `noStaleNotificationWaitReferences` (CrossSubsystem.lean:76) are maintained after forced removal. The thread is removed from queues but its TCB still exists — so no stale reference is created. | `SeLe4n/Kernel/IPC/Invariant/TimeoutPreservation.lean` | Small |
| V2-K | SV-3 | **Prove timeout liveness.** In a new file `SeLe4n/Kernel/IPC/Liveness/TimeoutBound.lean`, prove `ipc_timeout_bound`: if a thread enters a blocking IPC state with `timeout = some n`, then within `n` applications of `ipcTimeoutTick`, the thread is either unblocked by the counterparty or forcibly unblocked by timeout. Uses the V1 trace model. | `SeLe4n/Kernel/IPC/Liveness/TimeoutBound.lean` | Medium |
| V2-L | SV-3 | **Integrate `ipcTimeoutTick` into `timerTick`.** Modify `timerTick` (Core.lean:313) to call `ipcTimeoutTick` on each timer interrupt, after the time-slice decrement. Alternatively, create a composite `systemTick` that sequences `ipcTimeoutTick` and `timerTick`. Update `timerTick` preservation proofs in Preservation.lean to compose the new timeout preservation. | `SeLe4n/Kernel/Scheduler/Operations/Core.lean`, `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean` | Medium |
| V2-M | — | **Add negative-state tests.** Add test cases to `tests/NegativeStateSuite.lean` verifying: (1) timeout of 0 causes immediate unblock on next tick, (2) timeout decrement is monotonic, (3) forced removal from mid-queue endpoint is structurally correct, (4) timeout error message is propagated correctly. Add timeout trace tests to `tests/` or extend `MainTraceHarness`. | `tests/NegativeStateSuite.lean`, `tests/TimeoutSuite.lean` | Small |
| V2-N | — | **Documentation sync.** Update `docs/spec/SELE4N_SPEC.md` with timeout semantics. Update `docs/CLAIM_EVIDENCE_INDEX.md` with bounded-blocking claim. Update `CLAUDE.md` source layout. Regenerate `docs/codebase_map.json`. | `docs/spec/SELE4N_SPEC.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, `CLAUDE.md`, `docs/codebase_map.json` | Small |

**Intra-phase ordering constraints:**
- Type extension chain: V2-A → V2-B → V2-C (each builds on the extended type)
- Implementation chain: V2-A → V2-D → V2-E/V2-F (parallel forced-removal implementations)
- Proof chain: V2-D + V2-E + V2-F → V2-G → V2-H → V2-I → V2-J (proofs build on implementation)
- Liveness proof: V2-D + V1 trace model → V2-K
- Integration: V2-G + V2-H + V2-I + V2-J → V2-L (integration needs all preservation proofs)
- Testing: V2-L → V2-M → V2-N (tests after integration, docs last)

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

**Sub-tasks (16):**

| ID | Finding | Description | Files | Estimate |
|----|---------|-------------|-------|----------|
| V3-A | SV-2 | **Add `effectivePriority` field to TCB.** Add `effectivePriority : Priority` field to the `TCB` structure (Types.lean:308). Initialize to `tcb.priority` (base priority). This field is the scheduling-visible priority; `priority` remains the base/configured priority. Backward compatible — all existing code that reads `tcb.priority` for non-scheduling purposes continues to work. | `SeLe4n/Model/Object/Types.lean` | Small |
| V3-B | SV-2 | **Define the blocking graph.** Create `SeLe4n/Kernel/Scheduler/PriorityInheritance/BlockingGraph.lean`. Define `blockedOnThread (st : SystemState) (waiter server : ThreadId) : Prop` — `waiter` has `ipcState = .blockedOnReply epId (some server)`. Define `blockingChain (st : SystemState) : ThreadId → List ThreadId` — the transitive chain from a thread through all threads it's blocked on (follows `blockedOnReply` → server → server's `blockedOnReply` → ...). Prove `blockingChain_acyclic`: the chain is finite and acyclic (follows from `tcbQueueChainAcyclic` or independent induction on finite thread set). | `SeLe4n/Kernel/Scheduler/PriorityInheritance/BlockingGraph.lean` | Medium |
| V3-C | SV-2 | **Define `computeEffectivePriority`.** In the same directory, create `SeLe4n/Kernel/Scheduler/PriorityInheritance/Compute.lean`. Define `computeEffectivePriority (st : SystemState) (tid : ThreadId) : Priority` — the maximum of `tid.priority` and all priorities of threads transitively blocked on `tid` via `blockedOnReply`. This is a pure function over the current state. Prove `computeEffectivePriority_ge_base`: effective priority ≥ base priority. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/Compute.lean` | Medium |
| V3-D | SV-2 | **Implement `propagatePriorityInheritance`.** Create `SeLe4n/Kernel/Scheduler/PriorityInheritance/Propagate.lean`. Implement `propagatePriorityInheritance (st : SystemState) (tid : ThreadId) : SystemState` — walks the blocking chain from `tid`, updating each thread's `effectivePriority` to `computeEffectivePriority`. The walk is bounded by chain length (which is bounded by total thread count). Prove termination via well-founded recursion on chain length. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/Propagate.lean` | Large |
| V3-E | SV-2 | **Implement `revertPriorityInheritance`.** In the same file, implement `revertPriorityInheritance (st : SystemState) (tid : ThreadId) : SystemState` — called when `tid` completes a Reply, removing it from the blocking graph. Recomputes `effectivePriority` for all threads that were transitively boosted through `tid`. Prove that after revert, `effectivePriority = computeEffectivePriority` for all affected threads. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/Propagate.lean` | Large |
| V3-F | SV-2 | **Update `isBetterCandidate` to use `effectivePriority`.** Modify `isBetterCandidate` (Selection.lean:38) to compare `effectivePriority` instead of `priority`. This is a single-field change: replace `chalPrio.toNat > incPrio.toNat` with effective priority comparison. All existing selection proofs (irreflexivity, asymmetry, transitivity at Selection.lean:50–130) carry over because the comparison structure is identical — only the field being compared changes. | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | Small |
| V3-G | SV-2 | **Update `RunQueue` for effective priority.** Modify `RunQueue.insert` (RunQueue.lean:103) and `RunQueue.remove` (RunQueue.lean:176) to bucket by `effectivePriority` instead of `priority`. Update `schedulerPriorityMatch` (Invariant.lean:272) to match on `effectivePriority`. Update `RunQueue.maxPriority` tracking to use effective priority. | `SeLe4n/Kernel/Scheduler/RunQueue.lean`, `SeLe4n/Kernel/Scheduler/Invariant.lean` | Medium |
| V3-H | SV-2 | **Integrate PIP into Call path.** Modify the Call IPC path (or the transition that establishes `blockedOnReply`) to call `propagatePriorityInheritance` on the server thread after the client enters `blockedOnReply`. This ensures the server's effective priority is elevated immediately when a higher-priority client blocks on it. | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | Medium |
| V3-I | SV-2 | **Integrate PIP revert into Reply path.** Modify the Reply IPC path to call `revertPriorityInheritance` on the replying server thread after the client is unblocked. The server's effective priority drops back to `computeEffectivePriority` (which may still be elevated if other clients are waiting). Update the server's position in `RunQueue` if its effective priority changed. | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | Medium |
| V3-J | SV-2 | **Prove PIP preserves `schedulerInvariantBundleFull`.** Show that `propagatePriorityInheritance` and `revertPriorityInheritance` preserve all seven components of the full scheduler invariant bundle. Key challenge: `edfCurrentHasEarliestDeadline` (Invariant.lean:149) must account for effective priority changes. The current thread's effective priority may change if a new client blocks on it. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/Preservation.lean` | Large |
| V3-K | SV-2 | **Prove PIP preserves IPC invariants.** Show that priority inheritance propagation does not modify IPC state, endpoint queues, notification wait lists, or pending messages. The propagation only touches `effectivePriority` fields in TCBs and `RunQueue` bucket placement — IPC structural invariants are frame-preserved. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/Preservation.lean` | Medium |
| V3-L | SV-2 | **Prove bounded inversion theorem.** Create `SeLe4n/Kernel/Scheduler/PriorityInheritance/BoundedInversion.lean`. Prove `pip_bounded_inversion`: if thread H (priority P_H) enters `blockedOnReply` waiting for server S, and the blocking chain from S has depth D, then H is transitively blocked for at most `D × WCRT(P_H)` ticks (where `WCRT(P_H)` is the V1 bound for priority P_H). This composes the V1 WCRT theorem with the blocking chain depth. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/BoundedInversion.lean` | Large |
| V3-M | SV-2 | **Prove PIP determinism.** In the same file, prove `pip_deterministic`: `propagatePriorityInheritance` and `revertPriorityInheritance` produce identical results given identical input states. This follows from the fact that both are pure functions over the blocking graph, which is fully determined by the system state. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/BoundedInversion.lean` | Small |
| V3-N | — | **Create re-export hub.** Create `SeLe4n/Kernel/Scheduler/PriorityInheritance.lean` as a thin import-only file re-exporting `BlockingGraph`, `Compute`, `Propagate`, `Preservation`, and `BoundedInversion`. | `SeLe4n/Kernel/Scheduler/PriorityInheritance.lean` | Trivial |
| V3-O | — | **Add test coverage.** Add test cases: (1) PIP activates on Call to lower-priority server, (2) PIP deactivates on Reply, (3) transitive PIP through chain of 3 threads, (4) PIP does not affect threads outside the blocking chain, (5) effective priority ≥ base priority always holds. Add to trace harness or dedicated suite. | `tests/PriorityInheritanceSuite.lean`, `lakefile.lean` | Small |
| V3-P | — | **Documentation sync.** Update `docs/spec/SELE4N_SPEC.md` with PIP semantics. Update `docs/CLAIM_EVIDENCE_INDEX.md` with bounded-inversion claim. Update `CLAUDE.md` source layout. Regenerate `docs/codebase_map.json`. | `docs/spec/SELE4N_SPEC.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, `CLAUDE.md`, `docs/codebase_map.json` | Small |

**Intra-phase ordering constraints:**
- Type foundation: V3-A (TCB field) must come first
- Graph model: V3-A → V3-B → V3-C (graph → compute → propagate)
- Implementation: V3-C → V3-D/V3-E (parallel propagate/revert implementations)
- Scheduler integration: V3-D → V3-F → V3-G (selection uses effective priority, RunQueue buckets by it)
- IPC integration: V3-D + V3-E → V3-H/V3-I (parallel Call/Reply integration)
- Proofs: V3-F + V3-G + V3-H + V3-I → V3-J/V3-K (parallel scheduler/IPC preservation)
- Liveness: V3-J + V1-I → V3-L → V3-M
- Infrastructure: V3-L → V3-N → V3-O → V3-P (sequential post-proof)

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

**Sub-tasks (18):**

| ID | Finding | Description | Files | Estimate |
|----|---------|-------------|-------|----------|
| V4-A | SV-1, SV-2, SV-3 | **Define `SchedContext` kernel object type.** Add `SchedContext` structure to `Model/Object/Types.lean`: fields `budget : Nat` (ticks per period), `period : Nat` (replenishment period), `consumed : Nat` (ticks consumed in current period), `basePriority : Priority`, `boundThread : Option ThreadId` (currently bound thread), `replenishmentTime : Nat` (next replenishment tick). Add `.schedContext` constructor to `KernelObject` inductive. | `SeLe4n/Model/Object/Types.lean` | Medium |
| V4-B | SV-1, SV-2 | **Define scheduling context capability.** Add `SchedContextCap` to capability types with rights: `Bind`, `Unbind`, `SetParams`. Add `SchedContextId` typed identifier to `SeLe4n/Prelude.lean`. Follow the existing capability pattern (mint, derive, revoke paths). | `SeLe4n/Model/Object/Types.lean`, `SeLe4n/Prelude.lean` | Medium |
| V4-C | SV-1, SV-2 | **Add `schedContext : Option ObjId` to TCB.** Replace the current direct `timeSlice` / `priority` scheduling fields with a binding to a `SchedContext` object. The TCB's effective scheduling parameters are now derived from its bound scheduling context. If `schedContext = none`, the thread is not schedulable (passive server pattern). Maintain backward compatibility by keeping `priority` as base priority for non-MCS paths during migration. | `SeLe4n/Model/Object/Types.lean` | Medium |
| V4-D | SV-1 | **Implement budget accounting.** Create `SeLe4n/Kernel/SchedContext/Core.lean`. Implement `consumeBudget (scId : ObjId) (ticks : Nat) : Kernel Unit` — decrements `consumed` and checks `consumed ≤ budget`. Implement `replenishBudget (scId : ObjId) : Kernel Unit` — resets `consumed := 0` when `replenishmentTime` is reached. Implement `budgetExhausted (scId : ObjId) (st : SystemState) : Bool` — returns `consumed ≥ budget`. | `SeLe4n/Kernel/SchedContext/Core.lean` | Medium |
| V4-E | SV-1 | **Implement budget-aware `timerTick`.** Modify `timerTick` (Core.lean:313) to consume one budget tick from the current thread's scheduling context instead of decrementing `timeSlice` directly. When budget is exhausted, preempt the thread and mark its scheduling context as needing replenishment. When replenishment time arrives, reset consumed and re-enqueue if the thread is still runnable. | `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | Large |
| V4-F | SV-2 | **Implement scheduling context donation.** Create `SeLe4n/Kernel/SchedContext/Donation.lean`. Implement `donateSchedContext (fromTid toTid : ThreadId) : Kernel Unit` — transfers the scheduling context binding from `fromTid` to `toTid`. The donor thread becomes unschedulable (passive) until the context is returned. This is called on the Call IPC path: the client donates its scheduling context to the server. | `SeLe4n/Kernel/SchedContext/Donation.lean` | Large |
| V4-G | SV-2 | **Implement scheduling context return.** In the same file, implement `returnSchedContext (fromTid toTid : ThreadId) : Kernel Unit` — returns the scheduling context from `fromTid` to `toTid`. Called on the Reply IPC path: the server returns the client's scheduling context. The server becomes unschedulable again (if it has no scheduling context of its own). | `SeLe4n/Kernel/SchedContext/Donation.lean` | Medium |
| V4-H | SV-2 | **Integrate donation into Call/Reply.** Modify the Call path (Endpoint.lean) to call `donateSchedContext` after establishing `blockedOnReply`. Modify the Reply path to call `returnSchedContext` before unblocking the client. This replaces V3's PIP mechanism with a more fundamental solution — the server literally runs with the client's scheduling parameters. | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | Medium |
| V4-I | SV-3 | **Implement timeout endpoints.** Create `SeLe4n/Kernel/SchedContext/TimeoutEndpoint.lean`. A timeout endpoint is a special notification bound to a scheduling context. When the scheduling context's budget expires, the kernel signals the timeout endpoint instead of (or in addition to) preempting the thread. This enables user-space timeout handling — the thread can catch the timeout signal and clean up. | `SeLe4n/Kernel/SchedContext/TimeoutEndpoint.lean` | Medium |
| V4-J | SV-1 | **Define `SchedContext` invariants.** Create `SeLe4n/Kernel/SchedContext/Invariant.lean`. Define: `budgetValid (sc : SchedContext) : Prop` (consumed ≤ budget), `periodPositive (sc : SchedContext) : Prop` (period > 0), `bindingConsistent (st : SystemState) : Prop` (if `sc.boundThread = some tid`, then `tid.schedContext = some scId` — bidirectional binding). Define `schedContextInvariant` as the conjunction. | `SeLe4n/Kernel/SchedContext/Invariant.lean` | Medium |
| V4-K | SV-1 | **Prove budget monotonicity.** In a new file `SeLe4n/Kernel/SchedContext/Preservation.lean`, prove `consumeBudget_monotone`: after `consumeBudget`, `consumed' = consumed + ticks` and `consumed' ≤ budget` (or error). Prove `replenishBudget_resets`: after `replenishBudget`, `consumed' = 0`. | `SeLe4n/Kernel/SchedContext/Preservation.lean` | Small |
| V4-L | SV-2 | **Prove donation preserves invariants.** In the same file, prove `donateSchedContext_preserves_schedContextInvariant`: binding consistency is maintained (old binding cleared, new binding established atomically). Prove `donateSchedContext_preserves_schedulerInvariantBundleFull`: the donor is removed from the run queue (no scheduling context → not schedulable), the recipient's effective priority and bucket placement are updated. | `SeLe4n/Kernel/SchedContext/Preservation.lean` | Large |
| V4-M | SV-2 | **Prove return preserves invariants.** Prove `returnSchedContext_preserves_schedContextInvariant` and `returnSchedContext_preserves_schedulerInvariantBundleFull`. Symmetric to V4-L: the server's binding is cleared, the client's binding is restored, run queue updated. | `SeLe4n/Kernel/SchedContext/Preservation.lean` | Large |
| V4-N | SV-1 | **Prove budget-bounded execution.** Create `SeLe4n/Kernel/SchedContext/Liveness.lean`. Prove `budget_bounded_execution`: a thread with scheduling context `sc` executes for at most `sc.budget` ticks per period. After budget exhaustion, the thread is preempted and does not execute again until replenishment. Composes `consumeBudget_monotone` with `budgetExhausted` check in `timerTick`. | `SeLe4n/Kernel/SchedContext/Liveness.lean` | Medium |
| V4-O | SV-2 | **Prove passive server correctness.** In the same file, prove `passive_server_executes_at_client_priority`: when a passive server (no own scheduling context) receives a donated scheduling context via Call, it executes at the donor's priority and within the donor's budget. This is the key PIP-replacement theorem — priority inversion is impossible because the server *is* the client for scheduling purposes. | `SeLe4n/Kernel/SchedContext/Liveness.lean` | Medium |
| V4-P | — | **Add syscall interface.** Add new syscalls to `Kernel/API.lean`: `SchedControl_Configure` (set budget/period), `SchedContext_Bind` (bind thread to scheduling context), `SchedContext_Unbind`, `SchedContext_Consumed` (query consumed budget). Add corresponding `SyscallId` variants and argument decode in `Architecture/SyscallArgDecode.lean`. Gate all operations through information-flow policy wrappers. | `SeLe4n/Kernel/API.lean`, `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`, `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` | Large |
| V4-Q | — | **Add comprehensive test coverage.** Test cases: (1) budget exhaustion triggers preemption, (2) replenishment resets consumed, (3) donation on Call transfers scheduling context, (4) return on Reply restores scheduling context, (5) passive server with no scheduling context is not schedulable, (6) passive server becomes schedulable after donation, (7) timeout endpoint signals on budget expiry, (8) binding consistency holds across all operations. | `tests/SchedContextSuite.lean`, `lakefile.lean` | Medium |
| V4-R | — | **Documentation and closure.** Update `docs/spec/SELE4N_SPEC.md` with MCS scheduling context semantics. Update `docs/CLAIM_EVIDENCE_INDEX.md` with budget-bounded execution and passive server claims. Update `CLAUDE.md` source layout for all new directories. Update `docs/WORKSTREAM_HISTORY.md` with WS-V summary. Update `README.md` metrics. Regenerate `docs/codebase_map.json`. Update `CHANGELOG.md` with v0.21.0–v0.21.3 entries. | `docs/spec/SELE4N_SPEC.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, `CLAUDE.md`, `docs/WORKSTREAM_HISTORY.md`, `README.md`, `CHANGELOG.md`, `docs/codebase_map.json` | Medium |

**Intra-phase ordering constraints:**
- Type foundation: V4-A → V4-B → V4-C (object type → capability → TCB binding)
- Budget core: V4-A → V4-D → V4-E (object → accounting → timer integration)
- Donation core: V4-C → V4-F → V4-G (TCB binding → donate → return)
- IPC integration: V4-F + V4-G → V4-H (donation/return → Call/Reply integration)
- Timeout: V4-D → V4-I (budget → timeout endpoint)
- Invariants: V4-A + V4-C → V4-J (types defined → invariant predicates)
- Preservation chain: V4-D → V4-K, V4-F → V4-L, V4-G → V4-M (impl → proof)
- Liveness: V4-E + V4-K → V4-N, V4-H + V4-L → V4-O (preservation → liveness)
- Syscall: V4-H + V4-I → V4-P (all operations defined → API surface)
- Testing: V4-P → V4-Q → V4-R (API → tests → docs)
- V4-D/V4-F and V4-I are independent chains (can run in parallel after V4-A/V4-C)

---

## 8. Scope Summary

### 8.1 Sub-task Count by Phase

| Phase | Version | Sub-tasks | Complexity | Nature |
|-------|---------|-----------|-----------|--------|
| V1 — Bounded Latency Theorem | v0.21.0 | 12 | Medium | Proof-only (zero kernel code changes) |
| V2 — IPC Timeout Mechanism | v0.21.1 | 14 | High | New transitions + preservation proofs |
| V3 — Priority Inheritance Protocol | v0.21.2 | 16 | High | TCB extension + scheduler + proofs |
| V4 — MCS Scheduling Contexts | v0.21.3 | 18 | Very High | New kernel object type + full subsystem |
| **Total** | | **60** | | |

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
| V1 | ~7 (Liveness/) | 0 | 1 | 4 |
| V2 | ~3 (Timeout/, IPC/Liveness/) | ~5 (Types, Endpoint, Core, Preservation, DualQueue) | 1–2 | 4 |
| V3 | ~6 (PriorityInheritance/) | ~4 (Types, Selection, RunQueue, Endpoint) | 1 | 4 |
| V4 | ~7 (SchedContext/) | ~6 (Types, Prelude, Core, Endpoint, API, SyscallArgDecode) | 1 | 7 |
| **Total** | **~23** | **~15** | **4–5** | **19** |

### 8.4 Effort Distribution

| Estimate | V1 | V2 | V3 | V4 | Total |
|----------|----|----|----|----|-------|
| Trivial | 1 | 0 | 1 | 0 | **2** |
| Small | 6 | 5 | 5 | 1 | **17** |
| Medium | 3 | 7 | 6 | 12 | **28** |
| Large | 2 | 2 | 4 | 5 | **13** |
| **Total** | **12** | **14** | **16** | **18** | **60** |

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
| V4 is very large (18 sub-tasks) and may slip | V1–V3 are independently valuable. Ship V1 as soon as it's ready — it provides the first formal WCRT bound with zero code risk. V2 and V3 each close specific starvation vectors. V4 can be split into sub-phases (V4a: types + budget, V4b: donation, V4c: syscalls) if needed. |
| V3 depends on V2's type changes, creating a serial bottleneck | V3-A (add `effectivePriority` field) and V3-B/V3-C (blocking graph model) can be prototyped independently of V2's timeout field. Only V3-H/V3-I (Call/Reply integration) depend on V2's modified IPC state type. |
| WS-U (RPi5 hardware) may need scheduler changes that conflict with V2–V4 | WS-V and WS-U operate on disjoint file sets: WS-U owns `Platform/RPi5/`, WS-V owns `Scheduler/Liveness/`, `Scheduler/PriorityInheritance/`, `SchedContext/`, and IPC timeout extensions. The only shared files are `Model/Object/Types.lean` (additive fields) and `Scheduler/Operations/Core.lean` (timer tick modification). Coordinate field additions via explicit merge points. |

---

## 11. Invariant Landscape

This section maps how WS-V's new mechanisms interact with the existing
invariant proof surface, to ensure preservation proof coverage is complete.

### 11.1 Invariants Preserved by Each Phase

| Invariant Bundle | V1 | V2 | V3 | V4 |
|-----------------|----|----|----|----|
| `schedulerInvariantBundleFull` | Read-only (no state change) | V2-I: `ensureRunnable` on timeout unblock | V3-J: effective priority bucket migration | V4-E: budget-based preemption, V4-L/M: donation/return |
| `ipcInvariantFull` | Read-only | V2-H: notification state transition on timeout | V3-K: frame-preserved (PIP doesn't touch IPC) | V4-H: donation integrated into Call/Reply |
| `dualQueueSystemInvariant` | Read-only | V2-G: forced mid-queue removal | V3-K: frame-preserved | V4-H: donation doesn't modify queues |
| `crossSubsystemInvariant` | Read-only | V2-J: TCB persists after timeout unblock | Frame-preserved | V4-J: new `schedContextBindingConsistent` added |
| `kernelInvariant` (base triad + domain) | Read-only | V2-I: composed from above | V3-J: composed from above | V4-E/L/M: composed from above |

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
