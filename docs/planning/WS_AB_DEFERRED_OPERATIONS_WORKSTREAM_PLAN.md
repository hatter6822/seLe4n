# WS-AB Workstream Plan — Deferred Operations & Liveness Completion
 
**Created**: 2026-04-02
**Baseline version**: 0.23.22
**Prior portfolios**: WS-B through WS-AA (all COMPLETE)
**Constraint**: Zero `sorry`/`axiom` in production proof surface
**Hardware target**: Raspberry Pi 5 (ARM64)
**Relationship to WS-Z**: Dependent. WS-AB implements the five deferred operations
from spec §5.14 whose prerequisites (MCS scheduling, thread lifecycle state machine)
were delivered by WS-Z (Z1–Z10) and WS-V (V8-G1). WS-AB also completes the
starvation prevention work originally planned as WS-V (bounded latency theorem,
priority inheritance protocol) that was superseded by WS-Z's runtime CBS approach
but whose formal liveness guarantees remain undelivered.
 
---
 
## 1. Motivation
 
### 1.1 Deferred Operations Gap
 
Section 5.14 of `docs/spec/SELE4N_SPEC.md` identifies five seL4 operations
intentionally deferred from the model:
 
| Operation | seL4 Equivalent | Original Prerequisite | Status |
|-----------|----------------|----------------------|--------|
| `setPriority` | `seL4_TCB_SetPriority` | MCS scheduling model | **MET** (WS-Z: SchedContext + CBS) |
| `setMCPriority` | `seL4_TCB_SetMCPriority` | MCS scheduling model | **MET** (WS-Z: SchedContext + CBS) |
| `suspend` | `seL4_TCB_Suspend` | Thread lifecycle state machine | **MET** (V8-G1: ThreadState enum) |
| `resume` | `seL4_TCB_Resume` | Thread lifecycle state machine | **MET** (V8-G1: ThreadState enum) |
| `setIPCBuffer` | `seL4_TCB_SetIPCBuffer` | VSpace validation via page walk | **PARTIALLY MET** (VSpace map/unmap exist) |
 
All five prerequisites have been met or substantially met. These operations are
tracked in `SeLe4n/Kernel/API.lean` (stability table, lines 88–100) and
`docs/CLAIM_EVIDENCE_INDEX.md`. With WS-Z delivering the MCS scheduling context
infrastructure (Z1–Z10, 213 sub-tasks) and V8-G1 delivering the explicit
`ThreadState` enum (8 variants including `Inactive`), every blocker is resolved.
 
### 1.2 Starvation Prevention Gap
 
The starvation prevention work originally planned as WS-V
(`docs/planning/WS_V_KERNEL_STARVATION_PREVENTION_PLAN.md`, baseline v0.20.7)
identified six starvation vectors (SV-1 through SV-6). WS-Z addressed some of
these through runtime mechanisms (CBS budgets, SchedContext donation, budget-driven
IPC timeout) but two critical formal gaps remain:
 
| Gap | Original Phase | Status | Why It Matters |
|-----|---------------|--------|----------------|
| **No formal WCRT bound** | V1 (Bounded Latency Theorem) | NOT IMPLEMENTED | The kernel proves no liveness property. Every theorem is safety-only. System integrators cannot prove schedulability. |
| **No transitive priority inheritance** | V3 (Priority Inheritance Protocol) | PARTIALLY IMPLEMENTED | Z4 provides static effective priority from SchedContext binding. But transitive priority inversion via blocking chains (the Mars Pathfinder scenario) is not mitigated. |
 
### 1.3 Audit of WS-V Starvation Prevention Plan
 
The WS-V plan (78 sub-tasks across 4 phases) was written at v0.20.7. The codebase
is now at v0.23.22. Here is the disposition of each phase:
 
| WS-V Phase | Planned Scope | Actual Disposition | Remaining Work |
|------------|--------------|-------------------|----------------|
| **V1** (15 sub-tasks) | Bounded Latency Theorem — proof-only trace model, WCRT bound | **NOT IMPLEMENTED**. No `Scheduler/Liveness/` directory, no trace model, no WCRT proofs. WS-Z chose runtime CBS over proof bounds. | **All 15 sub-tasks remain relevant** but must be updated for CBS budget model (budget exhaustion + replenishment cycles affect WCRT). |
| **V2** (18 sub-tasks) | IPC Timeout Mechanism — per-tick countdown on IPC blocking states | **PARTIALLY IMPLEMENTED as Z6**. Budget-driven timeout via `timeoutBudget : Option SchedContextId` on TCB + `timeoutThread`/`timeoutBlockedThreads` in `timerTickBudget`. Achieves SV-3 (bounded IPC blocking) but through budget exhaustion, not independent countdown timers. | **Substantially complete.** Z6 solves the core problem. Optional per-operation timeouts (independent of SchedContext) would be a refinement, not critical. **Absorbed — no dedicated phase needed.** |
| **V3** (21 sub-tasks) | Priority Inheritance Protocol — blocking graph, transitive propagation, bounded inversion proofs | **PARTIALLY IMPLEMENTED as Z4**. `effectivePriority` function (Selection.lean:218) resolves priority from SchedContext binding. But NO blocking graph, NO `propagatePriorityInheritance`, NO transitive chain walk. Static effective priority from SchedContext handles single-level inversion; transitive chains remain unmitigated. | **Core sub-tasks remain relevant** (blocking graph, propagation, reversion, bounded inversion proofs). Must be updated for SchedContext-aware effective priority and Z7 donation semantics. |
| **V4** (24 sub-tasks) | MCS Scheduling Contexts — new kernel object type, CBS budget, donation, timeout endpoints | **SUBSTANTIALLY IMPLEMENTED as WS-Z (Z1–Z10)**. SchedContext types (Z1), CBS budget engine (Z2), replenishment queue (Z3), scheduler integration (Z4), capability-controlled binding (Z5), timeout endpoints (Z6), SchedContext donation (Z7), API surface (Z8), invariant composition (Z9). | **Complete. No remaining work.** |
 
**Specific WS-V sub-tasks superseded by WS-Z:**
 
| WS-V Sub-task | WS-Z Equivalent | Status |
|--------------|-----------------|--------|
| V2-D/E/F (timeout decrement/unblock/fold) | Z6-C `timeoutThread`, Z6-E `timeoutBlockedThreads` | ✅ Superseded |
| V2-G (forced endpoint queue removal) | Z6-B `endpointQueueRemove` | ✅ Superseded |
| V2-P (timer integration) | Z4-F `timerTickBudget` branch F3 | ✅ Superseded |
| V3-I (isBetterCandidate effective priority) | Z4-B `effectivePriority` + Z4-D `resolveEffectivePrioDeadline` | ✅ Superseded |
| V3-J (RunQueue bucketing) | Z5-G `schedContextBind_runQueue_insert_uses_sc_priority` | ✅ Superseded |
| V4-A through V4-X (all MCS sub-tasks) | Z1-A through Z10-J2 | ✅ Superseded |
 
**WS-V sub-tasks with outdated assumptions:**
 
| WS-V Sub-task | Outdated Assumption | Required Update |
|--------------|---------------------|-----------------|
| V1-D/E (timerTick monotonicity/preemption) | Assumes only `timerTick` path | Must also cover `timerTickBudget` (Z4-F) with 3 branches: active budget decrement, exhaustion preemption, timeout unblock |
| V1-H (FIFO progress in band) | Assumes quantum = `defaultTimeSlice` = 5 | Must account for SchedContext budget as alternative preemption source; a thread may be preempted by budget exhaustion before time-slice expires |
| V1-K/L (WCRT hypotheses/theorem) | WCRT = `N × Q` ticks | WCRT must incorporate CBS budget period: a thread may be descheduled for budget replenishment, extending latency by up to one period |
| V3-A (effectivePriority on TCB) | Add field to TCB structure | Field is NOT on TCB; effective priority is computed dynamically from SchedContext binding. PIP must update SchedContext priority, not a TCB field |
| V3-E/F (propagation updates TCB field) | `updateEffectivePriority` modifies `tcb.effectivePriority` | Must modify SchedContext priority or introduce a transient TCB-level override field for PIP boost. Design decision required. |
| V3-I (isBetterCandidate uses effectivePriority) | Modify `isBetterCandidate` to accept `effectivePriority` | Already done — `effectivePriority` (Selection.lean:218) resolves from SchedContext. PIP must hook into this resolution chain. |
| V3-K/L (PIP in Call/Reply) | Activate PIP on Call, deactivate on Reply | Must integrate with Z7 donation semantics: `endpointCallWithDonation` already donates SchedContext. PIP propagation should compose with donation, not replace it. |
 
---
 
## 2. Starvation Analysis — Updated State (v0.23.22)
 
### 2.1 Starvation Vectors — Updated Disposition
 
| ID | Vector | Original Severity | Current Status | Resolution |
|----|--------|-------------------|---------------|------------|
| SV-1 | Strict priority starvation | HIGH | **MITIGATED** by WS-Z | CBS budget prevents monopoly: thread preempted on budget exhaustion regardless of priority. But no formal WCRT bound exists. |
| SV-2 | Priority inversion via Call/Reply | HIGH | **PARTIALLY MITIGATED** | Z7 SchedContext donation: server executes at client's SchedContext priority during Call. But transitive chains (H→S1→S2) are NOT mitigated — S2 runs at S1's priority, not H's. |
| SV-3 | Unbounded IPC blocking | HIGH | **RESOLVED** by Z6 | Budget-driven timeout: `timeoutBudget` on TCB triggers forced unblock when SchedContext budget expires. `blockedThreadTimeoutConsistent` invariant (10th conjunct of `ipcInvariantFull`). |
| SV-4 | Notification LIFO ordering | MEDIUM | **ACCEPTED** | seL4 semantic compatibility. Not addressed in this workstream. |
| SV-5 | Domain schedule imbalance | MEDIUM | **UNRESOLVED** | Static `domainSchedule` table. No formal bound on domain rotation. V1 would prove this. |
| SV-6 | Run queue cycling without bound | LOW | **UNRESOLVED** | No theorem bounds rotations before a specific thread is selected. V1 would prove this. |
 
### 2.2 New Starvation Vectors Introduced by WS-Z
 
| ID | Vector | Severity | Mechanism |
|----|--------|----------|-----------|
| SV-7 | Budget starvation via admission over-commitment | LOW | `admissionCheck` (Operations.lean:58) validates bandwidth ≤ 100%, but rounding in per-mille arithmetic could allow marginal over-commitment. `cbs_bandwidth_bounded` theorem exists but bounds are per-context, not system-wide. |
| SV-8 | Replenishment queue delay under high load | LOW | `processReplenishmentsDue` (ReplenishQueue.lean) processes prefix of sorted queue. Under many simultaneous replenishments, O(k) processing in timer tick could delay later replenishments. Bounded by queue size (finite). |
| SV-9 | Donation chain unbounded depth | MEDIUM | Z7 `donationChainAcyclic` prevents cycles but no depth bound exists. A chain H→S1→S2→…→Sn requires n donations, each with overhead. No formal bound on chain traversal time. |
 
---
 
## 3. Phase Dependency Graph
 
```
D1 (Thread Suspend/Resume)         — new syscalls, lifecycle transitions
 │
 ├──→ D4 (Priority Inheritance)    — depends on D1 for suspend cleanup patterns
 │     │
 │     └──→ D5 (Bounded Latency)   — depends on D4 for PIP-aware WCRT
 │
D2 (Priority Management)           — independent of D1; uses SchedContext
 │
 ├──→ D4 (PIP needs priority update primitives from D2)
 │
D3 (IPC Buffer Configuration)      — independent of D1/D2
 │
D6 (API Surface & Closure)         — depends on D1+D2+D3+D4+D5
```
 
**Critical path**: D1 → D4 → D5 → D6
 
**Parallelism opportunities**:
- D1, D2, and D3 are fully independent (disjoint syscalls, disjoint type changes)
- D4 depends on D1 (suspend cleanup patterns reused in PIP reversion) and D2
  (priority update primitives)
- D5 depends on D4 (PIP-aware WCRT requires effective priority resolution)
- D6 depends on all prior phases
 
**File ownership by phase** (disjoint new files; shared files use additive changes):
- **D1** owns: `SeLe4n/Kernel/Lifecycle/Suspend.lean` (new),
  `SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean` (new).
  Modifies: `Model/Object/Types.lean` (SyscallId variants), `Kernel/API.lean`
  (dispatch), `Architecture/SyscallArgDecode.lean` (decode structures).
- **D2** owns: `SeLe4n/Kernel/SchedContext/PriorityManagement.lean` (new),
  `SeLe4n/Kernel/SchedContext/Invariant/PriorityPreservation.lean` (new).
  Modifies: `Model/Object/Types.lean` (SyscallId variants + MCP field),
  `Kernel/API.lean` (dispatch), `Architecture/SyscallArgDecode.lean`.
- **D3** owns: `SeLe4n/Kernel/Architecture/IpcBufferValidation.lean` (new).
  Modifies: `Model/Object/Types.lean` (SyscallId variant), `Kernel/API.lean`
  (dispatch), `Architecture/SyscallArgDecode.lean`.
- **D4** owns: `SeLe4n/Kernel/Scheduler/PriorityInheritance/` (new directory,
  all files). Modifies: `IPC/Operations/Endpoint.lean` (Call/Reply PIP hooks),
  `IPC/Operations/Donation.lean` (donation-aware propagation).
- **D5** owns: `SeLe4n/Kernel/Scheduler/Liveness/` (new directory, all files).
  No modifications to existing files (proof-only).
- **D6** owns: no new Lean files. Modifies: `InformationFlow/Enforcement/Wrappers.lean`,
  `FrozenOps/Operations.lean`, test files, documentation.
 
**Shared file coordination**: `Model/Object/Types.lean` receives additive SyscallId
variants in D1 (2 variants), D2 (2 variants), and D3 (1 variant). Each phase adds
new constructors — no conflicting modifications. D1/D2/D3 can run in parallel
because they add disjoint enum variants.
 
---
 
## 4. Phase D1 — Thread Suspension & Resumption (v0.24.0)
 
**Scope**: Implement `suspend` and `resume` as first-class kernel operations with
full invariant preservation proofs. These are the most complex deferred operations
because they touch every subsystem: scheduler (run queue removal/insertion), IPC
(blocking state cleanup, endpoint queue removal), lifecycle (state machine
transitions), SchedContext (donation cleanup on suspend), and information flow
(policy-gated wrappers).
 
**Rationale**: `seL4_TCB_Suspend` and `seL4_TCB_Resume` are fundamental thread
control primitives used by every non-trivial seL4 user-space system: process
managers, fault handlers, debuggers, and migration agents. Without them, the
kernel cannot support supervised thread lifecycle management from user space.
The `ThreadState` enum (V8-G1) and lifecycle cleanup infrastructure (retype,
donation cleanup) provide all necessary building blocks.
 
**Dependencies**: None. D1 builds on existing infrastructure (ThreadState,
lifecycle cleanup, queue removal utilities).
 
**Gate**: `test_full.sh` passes. `suspend` correctly removes thread from all
queues, cancels IPC blocking, cleans up donations, and transitions to `Inactive`.
`resume` correctly validates state, inserts into run queue, and transitions to
`Ready`. All preservation theorems compile without `sorry`/`axiom`. Module builds
verified for every modified `.lean` file.
 
**Sub-tasks (18):**
 
| ID | Description | Files | Estimate |
|----|-------------|-------|----------|
| D1-A | **Add `SyscallId.tcbSuspend` and `SyscallId.tcbResume` variants.** Add two new constructors to the `SyscallId` inductive (Types.lean:869). Update the `SyscallId.COUNT` constant from 20 to 22. Update all exhaustive `match` on `SyscallId` across the codebase (dispatch, decode, enforcement boundary, information flow). Follow the pattern established by Z5-D (schedContext variants). | `SeLe4n/Model/Object/Types.lean` | Small |
| D1-B | **Add `SyscallArgDecode` structures.** Create `SuspendArgs` and `ResumeArgs` structures in `SyscallArgDecode.lean`. Both are trivial: the target thread is identified by the invoked capability (no additional message-register arguments needed). Add `decodeSuspendArgs` and `decodeResumeArgs` functions that validate the capability resolves to a TCB. Follow existing capability-only decode patterns. | `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` | Small |
| D1-C | **Implement `cancelIpcBlocking`.** Create `SeLe4n/Kernel/Lifecycle/Suspend.lean`. Implement `cancelIpcBlocking (st : SystemState) (tid : ThreadId) (tcb : TCB) : Except KernelError SystemState` — case-splits on `tcb.ipcState`: (1) `.ready` → no-op; (2) `.blockedOnSend epId` / `.blockedOnReceive epId` → call `endpointQueueRemove` (Z6-B); (3) `.blockedOnCall epId` → call `endpointQueueRemove`; (4) `.blockedOnReply epId _` → no queue removal (thread not in endpoint queue), clear reply target; (5) `.blockedOnNotification notifId` → filter from notification wait list. Reset `ipcState := .ready`. This reuses Z6-C `timeoutThread` patterns but without error-code injection or re-enqueue. | `SeLe4n/Kernel/Lifecycle/Suspend.lean` | Medium |
| D1-D | **Implement `cancelDonation`.** In the same file, implement `cancelDonation (st : SystemState) (tid : ThreadId) (tcb : TCB) : SystemState` — if `tcb.schedContextBinding = .donated scId originalOwner`, call `cleanupDonatedSchedContext` (Z7-D) to return the SchedContext to its original owner. If `tcb.schedContextBinding = .bound scId`, unbind the SchedContext (set `sc.boundThread := none`, clear binding). This ensures no dangling SchedContext references after suspend. | `SeLe4n/Kernel/Lifecycle/Suspend.lean` | Medium |
| D1-E | **Implement `removeFromRunQueue`.** In the same file, implement `removeFromRunQueue (st : SystemState) (tid : ThreadId) : SystemState` — if `tid` is in the run queue, remove it. If `scheduler.current = some tid`, clear current. This wraps `RunQueue.remove` with the scheduler state update. Guard: if thread is not in run queue and not current, no-op. | `SeLe4n/Kernel/Lifecycle/Suspend.lean` | Small |
| D1-F | **Implement `clearPendingState`.** In the same file, implement `clearPendingState (st : SystemState) (tid : ThreadId) (tcb : TCB) : SystemState` — clear `tcb.pendingMessage := none`, clear `tcb.timeoutBudget := none`, clear `tcb.queuePrev := none`, `tcb.queueNext := none`, `tcb.queuePPrev := none`. This ensures clean state on suspend. | `SeLe4n/Kernel/Lifecycle/Suspend.lean` | Small |
| D1-G | **Implement `suspendThread` (composite).** In the same file, implement `suspendThread (st : SystemState) (tid : ThreadId) : Except KernelError SystemState` — the complete suspension sequence: (1) look up TCB, validate `threadState ≠ .Inactive`; (2) `cancelIpcBlocking` (D1-C); (3) `cancelDonation` (D1-D); (4) `removeFromRunQueue` (D1-E); (5) `clearPendingState` (D1-F); (6) set `threadState := .Inactive`; (7) if suspended thread was `scheduler.current`, trigger `schedule`. Return updated state. Each step is a pure function; composition is sequential. | `SeLe4n/Kernel/Lifecycle/Suspend.lean` | Medium |
| D1-H | **Implement `resumeThread`.** In the same file, implement `resumeThread (st : SystemState) (tid : ThreadId) : Except KernelError SystemState` — the resumption sequence: (1) look up TCB, validate `threadState = .Inactive` (cannot resume an already-active thread); (2) set `threadState := .Ready`; (3) set `ipcState := .ready`; (4) call `ensureRunnable tid` to insert into run queue at the thread's effective priority; (5) if the resumed thread has higher effective priority than current, trigger `schedule` for immediate preemption check. Return updated state. | `SeLe4n/Kernel/Lifecycle/Suspend.lean` | Medium |
| D1-I | **Prove `cancelIpcBlocking` transport lemmas.** Create `SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean`. Prove 4 transport lemmas: (1) `cancelIpc_scheduler_eq` — scheduler state unchanged (only TCB and endpoint/notification modified); (2) `cancelIpc_cdt_eq` — CDT unchanged; (3) `cancelIpc_lifecycle_eq` — lifecycle objects unchanged; (4) `cancelIpc_services_eq` — service registry unchanged. These follow the `endpointQueueRemove_*_eq` transport pattern from Z6. | `SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean` | Medium |
| D1-J | **Prove `cancelIpcBlocking` preserves `ipcInvariantFull`.** In the same file, prove that removing a thread from endpoint queues and notification wait lists preserves all 14 conjuncts of `ipcInvariantFull`. Key cases: (1) `intrusiveQueueWellFormed` — reuse Z6-B `endpointQueueRemove` invExt proof; (2) `blockedThreadTimeoutConsistent` — timeout cleared; (3) `donationChainAcyclic` — IPC state change does not affect donation chains; (4) remaining conjuncts preserved by frame (non-IPC fields unchanged). | `SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean` | Medium |
| D1-K | **Prove `suspendThread` preserves `schedulerInvariantBundleFull`.** In the same file, decompose into per-component lemmas: (1) `suspend_preserves_queueCurrentConsistent` — thread removed from queue, current cleared if it was the suspended thread; (2) `suspend_preserves_runQueueUnique` — `remove_preserves_nodup`; (3) `suspend_preserves_currentThreadValid` — current cleared or unchanged; (4) `suspend_preserves_timeSlicePositive` — time-slice fields unchanged on other TCBs; (5) `suspend_preserves_domainTimeRemainingPositive` — domain time unchanged. Bundle composition via `⟨comp1, ..., compN⟩`. | `SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean` | Medium |
| D1-L | **Prove `suspendThread` preserves `schedulerInvariantBundleExtended`.** Extend D1-K to cover the 15-tuple extended bundle (Z4 additions): `replenishQueueSorted`, `replenishQueueSizeConsistent`, `replenishQueueConsistent`, `budgetPositive`, `currentBudgetPositive`, `effectivePriorityConsistent`. Key insight: suspend removes thread from run queue but does NOT modify replenishment queue or SchedContext objects (budget/period unchanged). Frame preservation for all Z4-specific conjuncts. | `SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean` | Medium |
| D1-M | **Prove `suspendThread` preserves `crossSubsystemInvariant`.** In the same file, prove preservation of all 8 cross-subsystem predicates: `noStaleEndpointQueueReferences` (thread removed from queues), `noStaleNotificationWaitReferences` (thread removed from wait lists), `schedContextStoreConsistent` (SchedContext cleaned up via D1-D), `schedContextNotDualBound` (binding cleared), `schedContextRunQueueConsistent` (thread removed from run queue). | `SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean` | Medium |
| D1-N | **Prove `resumeThread` preserves full invariant bundle.** In the same file, prove that resuming an `Inactive` thread preserves: (1) `schedulerInvariantBundleExtended` — `ensureRunnable` adds to queue (reuse existing `ensureRunnable_nodup` lemmas from SchedulerLemmas.lean); (2) `ipcInvariantFull` — IPC state set to `.ready`, no queue modifications; (3) `crossSubsystemInvariant` — thread enters run queue consistently. Key case: preemption check (if resumed thread is higher priority) triggers `schedule` which has existing preservation proofs. | `SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean` | Medium |
| D1-O | **Wire into API dispatch.** Add `tcbSuspend` and `tcbResume` arms to `dispatchCapabilityOnly` in `Kernel/API.lean`. These are capability-only operations (target TCB identified by invoked capability, no additional arguments). Add structural equivalence theorems: `dispatchCapabilityOnly_tcbSuspend_eq` and `dispatchCapabilityOnly_tcbResume_eq`. Update `enforcementBoundary` in Wrappers.lean to include the 2 new entries (25→27). | `SeLe4n/Kernel/API.lean`, `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` | Medium |
| D1-P | **Add frozen operations.** Add `frozenSuspendThread` and `frozenResumeThread` to `FrozenOps/Operations.lean`. These wrap the pure functions with `FrozenKernel` monad lookup/store. Update `frozenOpCoverage_count` from 15 to 17. Follow the existing pattern from Z8-E frozen SchedContext operations. | `SeLe4n/Kernel/FrozenOps/Operations.lean` | Small |
| D1-Q | **Add test coverage.** Create test cases in `tests/SuspendResumeSuite.lean`: (1) suspend removes thread from run queue; (2) suspend cancels IPC blocking (each of 5 IPC states); (3) suspend cleans up donated SchedContext; (4) suspend of current thread triggers reschedule; (5) resume of Inactive thread inserts into run queue; (6) resume of non-Inactive thread returns error; (7) suspend then resume round-trip; (8) suspended thread is not selected by `chooseThreadEffective`; (9) double-suspend returns error. Add to `lakefile.lean`. Add negative-state tests for error paths. | `tests/SuspendResumeSuite.lean`, `lakefile.lean` | Medium |
| D1-R | **Documentation sync.** Update `docs/spec/SELE4N_SPEC.md` §5.14 to mark `suspend`/`resume` as implemented. Update `docs/CLAIM_EVIDENCE_INDEX.md`. Update `CLAUDE.md` source layout with `Lifecycle/Suspend.lean` and `Lifecycle/Invariant/SuspendPreservation.lean`. Regenerate `docs/codebase_map.json`. | Docs | Small |
 
**Intra-phase ordering constraints:**
- Type foundation: D1-A → D1-B (SyscallId variants → decode structures)
- Implementation chain: D1-C → D1-D → D1-E → D1-F → D1-G (cancelIpc → cancelDonation → removeRunQueue → clearPending → composite)
  - D1-C, D1-D, D1-E, D1-F are independent building blocks; can be implemented in parallel
  - D1-G depends on all four
- Resume: D1-H (independent of D1-C through D1-F; depends on D1-A for types)
- Transport lemmas: D1-C → D1-I (implementation → transport proofs)
- Preservation chain: D1-I → D1-J → D1-K → D1-L → D1-M (transport → IPC → scheduler → extended → cross-subsystem)
  - D1-J, D1-K, D1-L are somewhat independent (IPC vs scheduler vs extended)
- Resume preservation: D1-H → D1-N
- API integration: D1-G + D1-H + D1-A + D1-B → D1-O → D1-P (ops + types → dispatch → frozen)
- Testing: D1-O → D1-Q → D1-R
 
---
 
## 5. Phase D2 — Priority Management (v0.24.1)
 
**Scope**: Implement `setPriority` and `setMCPriority` as capability-controlled
operations that modify thread scheduling priority through the SchedContext
subsystem. In seL4's MCS model, priority is a property of the scheduling context,
not the thread directly. seLe4n already models this via `SchedContext.priority`
and `effectivePriority` resolution (Selection.lean:218). D2 adds the user-space
syscall interface for priority modification with proper authority checks.
 
**Rationale**: `seL4_TCB_SetPriority` and `seL4_TCB_SetMCPriority` are essential
for user-space resource management. Priority assignment is the primary mechanism
for expressing scheduling intent. The MCP (Maximum Controlled Priority) ceiling
prevents privilege escalation: a thread can only set another thread's priority
up to its own MCP, ensuring the authority hierarchy is respected.
 
**Dependencies**: None for core implementation. D4 (PIP) will use D2's priority
update primitives for transitive propagation.
 
**Gate**: `test_full.sh` passes. Priority changes correctly propagate to run queue
bucket placement. MCP authority check prevents escalation. All preservation
theorems compile. No `sorry`/`axiom`. Module builds verified.
 
**Sub-tasks (14):**
 
| ID | Description | Files | Estimate |
|----|-------------|-------|----------|
| D2-A | **Add `maxControlledPriority` field to TCB.** Add `maxControlledPriority : SeLe4n.Priority := ⟨0xFF⟩` field to the TCB structure (Types.lean:407). This is the MCP ceiling: the maximum priority this thread can assign to other threads (or itself). Default is maximum priority (no restriction). seL4 convention: `setPriority newPrio` requires `newPrio ≤ caller.maxControlledPriority`. | `SeLe4n/Model/Object/Types.lean` | Small |
| D2-B | **Add `SyscallId.tcbSetPriority` and `SyscallId.tcbSetMCPriority` variants.** Add two new constructors to `SyscallId`. Update `COUNT` from 22 to 24 (assuming D1 added 2). Update all exhaustive `match` expressions. | `SeLe4n/Model/Object/Types.lean` | Small |
| D2-C | **Add argument decode structures.** Create `SetPriorityArgs` with `newPriority : Priority` field, decoded from message register 0. Create `SetMCPriorityArgs` with `newMCP : Priority` field, decoded from message register 0. Add `decodeSetPriorityArgs` and `decodeSetMCPriorityArgs` with bounds validation (`priority.toNat ≤ 0xFF`). | `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` | Small |
| D2-D | **Implement `validatePriorityAuthority`.** Create `SeLe4n/Kernel/SchedContext/PriorityManagement.lean`. Implement `validatePriorityAuthority (callerTcb : TCB) (targetPriority : Priority) : Except KernelError Unit` — validates `targetPriority.toNat ≤ callerTcb.maxControlledPriority.toNat`. Returns `.error .rangeError` on violation. This is the MCP authority check. | `SeLe4n/Kernel/SchedContext/PriorityManagement.lean` | Small |
| D2-E | **Implement `setPriorityOp`.** In the same file, implement `setPriorityOp (st : SystemState) (callerTid targetTid : ThreadId) (newPriority : Priority) : Except KernelError SystemState`. Sequence: (1) look up caller TCB, validate MCP authority (D2-D); (2) look up target TCB; (3) determine priority update path: if target has `schedContextBinding = .bound scId`, update `SchedContext.priority` on the bound SchedContext; if unbound, update `TCB.priority` directly; (4) if target is in run queue, perform remove-then-insert at new priority (bucket migration); (5) if target is `scheduler.current` and priority decreased, trigger `schedule` for preemption check. Return updated state. | `SeLe4n/Kernel/SchedContext/PriorityManagement.lean` | Medium |
| D2-F | **Implement `setMCPriorityOp`.** In the same file, implement `setMCPriorityOp (st : SystemState) (callerTid targetTid : ThreadId) (newMCP : Priority) : Except KernelError SystemState`. Sequence: (1) look up caller TCB, validate `newMCP ≤ callerTcb.maxControlledPriority` (caller cannot grant more authority than it has); (2) look up target TCB; (3) update `targetTcb.maxControlledPriority := newMCP`; (4) if `targetTcb.priority > newMCP`, cap priority at MCP: `targetTcb.priority := newMCP` (seL4 behavior: reducing MCP may reduce effective priority); (5) if priority was capped, perform run queue bucket migration as in D2-E. | `SeLe4n/Kernel/SchedContext/PriorityManagement.lean` | Medium |
| D2-G | **Prove `setPriorityOp` preserves `schedulerInvariantBundleExtended`.** Create `SeLe4n/Kernel/SchedContext/Invariant/PriorityPreservation.lean`. Decompose: (1) `setPriority_preserves_queueCurrentConsistent` — remove-then-insert preserves dequeue-on-dispatch; (2) `setPriority_preserves_runQueueUnique` — `remove_preserves_nodup` + `insert_preserves_nodup`; (3) `setPriority_preserves_timeSlicePositive` — time-slice unchanged; (4) `setPriority_preserves_budgetPositive` — budget unchanged; (5) `setPriority_preserves_schedulerPriorityMatch` — updated by bucket migration. Bundle composition. | `SeLe4n/Kernel/SchedContext/Invariant/PriorityPreservation.lean` | Medium |
| D2-H | **Prove `setPriorityOp` preserves IPC and cross-subsystem invariants.** Frame preservation: priority change does not modify IPC state, endpoint queues, notification wait lists, CDT, or service registry. Prove: (1) `setPriority_preserves_ipcInvariantFull` — backward transport (IPC objects unchanged); (2) `setPriority_preserves_crossSubsystemInvariant` — `schedContextStoreConsistent` updated if SchedContext priority changed (prove new priority still satisfies `wellFormed`). | `SeLe4n/Kernel/SchedContext/Invariant/PriorityPreservation.lean` | Medium |
| D2-I | **Prove `setMCPriorityOp` preserves invariant bundles.** Similar structure to D2-G/H. Additional case: if MCP reduction caps priority, compose priority-cap preservation with MCP-field preservation. The priority cap case is structurally identical to `setPriorityOp` preservation (D2-G). | `SeLe4n/Kernel/SchedContext/Invariant/PriorityPreservation.lean` | Medium |
| D2-J | **Prove authority non-escalation.** In the same file, prove `setPriority_authority_bounded`: after `setPriorityOp`, `targetTcb'.priority ≤ callerTcb.maxControlledPriority`. Prove `setMCPriority_authority_bounded`: `targetTcb'.maxControlledPriority ≤ callerTcb.maxControlledPriority`. These are security-critical: they ensure the authority hierarchy is monotonically non-increasing. Direct from the validation checks in D2-D/D2-F. | `SeLe4n/Kernel/SchedContext/Invariant/PriorityPreservation.lean` | Small |
| D2-K | **Wire into API dispatch.** Add `tcbSetPriority` and `tcbSetMCPriority` arms to `dispatchWithCap` in `Kernel/API.lean` (these require argument decoding, unlike capability-only ops). Add structural equivalence theorems. Update `enforcementBoundary` (27→29 entries). | `SeLe4n/Kernel/API.lean`, `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` | Medium |
| D2-L | **Add frozen operations.** Add `frozenSetPriority` and `frozenSetMCPriority` to `FrozenOps/Operations.lean`. Update `frozenOpCoverage_count` (17→19). | `SeLe4n/Kernel/FrozenOps/Operations.lean` | Small |
| D2-M | **Add test coverage.** Test cases: (1) setPriority within MCP succeeds, thread migrates to new priority bucket; (2) setPriority above MCP returns error; (3) setMCPriority caps existing priority; (4) setPriority on SchedContext-bound thread updates SchedContext; (5) setPriority on unbound thread updates TCB; (6) priority decrease of current thread triggers reschedule; (7) MCP authority is transitive (A sets B's MCP, B cannot exceed A's ceiling); (8) negative-state: setPriority with invalid priority value. | `tests/PriorityManagementSuite.lean`, `lakefile.lean` | Medium |
| D2-N | **Documentation sync.** Update spec §5.14 to mark `setPriority`/`setMCPriority` as implemented. Update claims index, CLAUDE.md source layout, codebase map. | Docs | Small |
 
**Intra-phase ordering constraints:**
- Type foundation: D2-A → D2-B → D2-C (MCP field → SyscallId variants → decode)
- Authority check: D2-A → D2-D (MCP field → validation function)
- Operations: D2-D → D2-E → D2-F (authority → setPriority → setMCPriority)
  - D2-E and D2-F are independent after D2-D
- Preservation: D2-E → D2-G → D2-H (setPriority → scheduler preservation → IPC frame)
- MCP preservation: D2-F → D2-I (setMCPriority → preservation)
- Authority proofs: D2-E + D2-F → D2-J (both ops → authority bound proofs)
- D2-G/H/I/J are independent proof tasks (can run in parallel)
- API: D2-E + D2-F + D2-B + D2-C → D2-K → D2-L (ops + types → dispatch → frozen)
- Testing: D2-K → D2-M → D2-N
 
---
 
## 6. Phase D3 — IPC Buffer Configuration (v0.24.2)
 
**Scope**: Implement `setIPCBuffer` as a capability-controlled operation that
changes a thread's IPC buffer virtual address with VSpace validation. The IPC
buffer is a user-space memory region used for message transfer; the kernel must
validate that the specified address is mapped, writable, properly aligned, and
within the thread's VSpace.
 
**Rationale**: `seL4_TCB_SetIPCBuffer` enables dynamic IPC buffer relocation,
which is essential for thread migration between address spaces, memory
compaction, and advanced IPC patterns. The operation is a simple field update
but requires VSpace validation to prevent the kernel from later faulting on an
unmapped or read-only address.
 
**Dependencies**: None. The VSpace map/unmap/lookup infrastructure exists.
 
**Gate**: `test_full.sh` passes. `setIPCBuffer` validates address before
accepting. Invalid addresses (unmapped, read-only, unaligned) return errors.
Preservation proofs compile. No `sorry`/`axiom`.
 
**Sub-tasks (12):**
 
| ID | Description | Files | Estimate |
|----|-------------|-------|----------|
| D3-A | **Add `SyscallId.tcbSetIPCBuffer` variant.** Add one new constructor to `SyscallId`. Update `COUNT` (24→25 assuming D1+D2 already applied). Update all exhaustive `match` expressions. | `SeLe4n/Model/Object/Types.lean` | Small |
| D3-B | **Add argument decode structure.** Create `SetIPCBufferArgs` with `bufferAddr : VAddr` field, decoded from message register 0. Add `decodeSetIPCBufferArgs` with alignment validation: `bufferAddr.toNat % ipcBufferAlignment = 0` where `ipcBufferAlignment` is a constant (typically 512 bytes for seL4, matching message size). | `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` | Small |
| D3-C | **Define `ipcBufferAlignment` constant.** Add `def ipcBufferAlignment : Nat := 512` to `SeLe4n/Prelude.lean` (or `Architecture/Assumptions.lean`). This matches seL4's `seL4_IPCBufferSizeBits = 9` (2^9 = 512). Document the derivation. | `SeLe4n/Prelude.lean` or `SeLe4n/Kernel/Architecture/Assumptions.lean` | Trivial |
| D3-D | **Implement `validateIpcBufferAddress`.** Create `SeLe4n/Kernel/Architecture/IpcBufferValidation.lean`. Implement `validateIpcBufferAddress (st : SystemState) (tid : ThreadId) (addr : VAddr) : Except KernelError Unit`. Validation steps: (1) check alignment (`addr.toNat % ipcBufferAlignment = 0`); (2) look up thread's VSpace root (`tcb.vspaceRoot`); (3) check address is within `physicalAddressBound` (ARM64 LPA); (4) verify address is mapped in the thread's VSpace via `vspaceLookup` (existing VSpace.lean lookup); (5) verify mapped page has write permission (no W^X conflict for data pages). Return `.error .invalidArgument` for any failure. | `SeLe4n/Kernel/Architecture/IpcBufferValidation.lean` | Medium |
| D3-E | **Implement `setIPCBufferOp`.** In the same file, implement `setIPCBufferOp (st : SystemState) (tid : ThreadId) (addr : VAddr) : Except KernelError SystemState`. Sequence: (1) call `validateIpcBufferAddress` (D3-D); (2) look up TCB; (3) update `tcb.ipcBuffer := addr` via `storeTcb`; (4) return updated state. This is a simple field update after validation. The thread does NOT need to be suspended — seL4 allows changing the IPC buffer of a running thread (the change takes effect on next IPC operation). | `SeLe4n/Kernel/Architecture/IpcBufferValidation.lean` | Small |
| D3-F | **Prove `setIPCBufferOp` preserves all invariant bundles.** Create preservation proofs in the same file or adjacent. The operation modifies exactly one TCB field (`ipcBuffer`). Frame preservation is trivial: (1) scheduler invariants — `ipcBuffer` is not referenced by any scheduler predicate; (2) IPC invariants — `ipcBuffer` is not referenced by any IPC queue or blocking predicate; (3) cross-subsystem — `ipcBuffer` is not referenced by any cross-subsystem predicate; (4) capability — no capability state modified. Prove `setIPCBuffer_preserves_proofLayerInvariantBundle` as a single frame theorem. | `SeLe4n/Kernel/Architecture/IpcBufferValidation.lean` | Small |
| D3-G | **Prove validation correctness.** Prove `validateIpcBufferAddress_implies_mapped`: if validation succeeds, the address is mapped in the thread's VSpace with write permission. Prove `validateIpcBufferAddress_implies_aligned`: if validation succeeds, `addr.toNat % ipcBufferAlignment = 0`. These are security theorems ensuring the kernel never stores an invalid IPC buffer address. | `SeLe4n/Kernel/Architecture/IpcBufferValidation.lean` | Small |
| D3-H | **Wire into API dispatch.** Add `tcbSetIPCBuffer` arm to `dispatchWithCap` in `Kernel/API.lean` (requires argument decoding for the buffer address). Add structural equivalence theorem. Update `enforcementBoundary` (29→30 entries). | `SeLe4n/Kernel/API.lean`, `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` | Small |
| D3-I | **Add frozen operation.** Add `frozenSetIPCBuffer` to `FrozenOps/Operations.lean`. Update `frozenOpCoverage_count` (19→20). | `SeLe4n/Kernel/FrozenOps/Operations.lean` | Small |
| D3-J | **Add test coverage.** Test cases: (1) setIPCBuffer with valid aligned mapped address succeeds; (2) unaligned address returns error; (3) unmapped address returns error; (4) address beyond physical bound returns error; (5) setIPCBuffer on running thread succeeds (no suspend required); (6) setIPCBuffer preserves all other TCB fields; (7) negative-state: read-only page returns error. | `tests/IpcBufferSuite.lean`, `lakefile.lean` | Small |
| D3-K | **Handle VSpace lookup gap.** If `vspaceLookup` does not exist as a query function (only `vspaceMapPage`/`vspaceUnmapPage` exist), implement `vspaceLookupPage (st : SystemState) (vspaceRoot : ObjId) (addr : VAddr) : Option (PAddr × AccessRightSet)` — looks up the VSpace HashMap for the address and returns the mapped physical address and permissions. This may already be available via `VSpaceRoot.mappings` HashMap lookup. | `SeLe4n/Kernel/Architecture/VSpace.lean` | Small |
| D3-L | **Documentation sync.** Update spec §5.14 to mark `setIPCBuffer` as implemented. Update claims index, CLAUDE.md, codebase map. | Docs | Small |
 
**Intra-phase ordering constraints:**
- Type foundation: D3-A → D3-B → D3-C (SyscallId → decode → alignment constant)
- VSpace query: D3-K (may be needed by D3-D; check first, implement if missing)
- Validation: D3-C + D3-K → D3-D → D3-E (alignment + lookup → validate → setIPCBuffer)
- Proofs: D3-E → D3-F → D3-G (operation → frame preservation → validation correctness)
  - D3-F and D3-G are independent (can run in parallel)
- API: D3-E + D3-A + D3-B → D3-H → D3-I (op + types → dispatch → frozen)
- Testing: D3-H → D3-J → D3-L
 
---
 
## 7. Phase D4 — Priority Inheritance Protocol (v0.24.3)
 
**Scope**: Implement a deterministic priority inheritance protocol (PIP) that
temporarily elevates a server thread's effective scheduling priority when it
holds a pending Reply on behalf of a higher-priority client. Prove that PIP
preserves all existing invariants, bounds the duration of priority inversion,
and composes correctly with WS-Z's SchedContext donation semantics.
 
**Rationale**: Priority inversion via Call/Reply IPC (SV-2) remains the most
dangerous starvation vector for client-server patterns. WS-Z's SchedContext
donation (Z7) solves *single-level* inversion: when client H calls server S,
S executes at H's SchedContext priority. But *transitive* inversion (H→S1→S2
where S2 runs at S1's priority, not H's) is unmitigated. PIP resolves this by
walking the blocking chain and elevating each server's effective priority to the
maximum of all clients transitively waiting for it.
 
**Key design decision — PIP composition with SchedContext donation**:
In the current WS-Z model, `effectivePriority` (Selection.lean:218) resolves
from SchedContext binding. PIP must compose with this, not replace it. The design
uses a `pipBoost : Option Priority` field on the TCB: when `pipBoost = some p`,
the effective priority is `max(SchedContext.priority, p)`. When `pipBoost = none`,
effective priority resolves purely from SchedContext (existing behavior). This
additive approach preserves all existing Z4 proofs by construction.
 
**Dependencies**: D1 (suspend cleanup patterns reused in PIP reversion when a
thread is suspended while holding boosted priority), D2 (priority update
primitives for run queue bucket migration).
 
**Gate**: `test_full.sh` passes. PIP activates on Call (blocking chain walk),
deactivates on Reply (reversion walk). `effectivePriority` incorporates
`pipBoost`. All scheduler preservation theorems updated. Inversion bounded by
chain depth × WCRT. No `sorry`/`axiom`.
 
**Sub-tasks (20):**
 
| ID | Description | Files | Estimate |
|----|-------------|-------|----------|
| D4-A | **Add `pipBoost` field to TCB.** Add `pipBoost : Option SeLe4n.Priority := none` field to the TCB structure (Types.lean:407). When `some p`, the thread's effective priority is boosted to at least `p` regardless of its SchedContext binding. This is the PIP transient override. Update `TCB.default` and all TCB construction sites. | `SeLe4n/Model/Object/Types.lean` | Small |
| D4-B | **Update `effectivePriority` to incorporate `pipBoost`.** Modify `effectivePriority` (Selection.lean:218) to compute: `let scPrio := <existing SchedContext resolution>; match tcb.pipBoost with \| some p => max scPrio p \| none => scPrio`. Prove `effectivePriority_ge_base_with_pip`: effective priority ≥ base priority (existing proof + `Nat.le_max_left`). Prove `effectivePriority_ge_pipBoost`: if `pipBoost = some p`, effective priority ≥ `p`. | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | Small |
| D4-C | **Define the blocking graph.** Create `SeLe4n/Kernel/Scheduler/PriorityInheritance/BlockingGraph.lean`. Define `blockedOnThread (st : SystemState) (waiter server : ThreadId) : Prop` — waiter has `ipcState = .blockedOnReply epId (some server)` or `ipcState = .blockedOnCall epId` where the endpoint's current server is identified. Define `waitersOf (st : SystemState) (tid : ThreadId) : List ThreadId` — all threads directly blocked on `tid` via Call/Reply. Define `blockingChain (st : SystemState) (tid : ThreadId) (fuel : Nat) : List ThreadId` — transitive chain following blockedOnReply → server → server's blockedOnReply → …, with fuel bounded by `st.objects.size`. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/BlockingGraph.lean` | Medium |
| D4-D | **Prove blocking graph acyclicity.** In the same file, prove `blockingChain_acyclic`: no thread appears twice in its own blocking chain. Proof: each step follows `blockedOnReply` requiring the waiter to be in a blocking state; the server must be distinct (a thread cannot be blocked on itself — would violate `tcbQueueChainAcyclic`, IPC/Invariant/Defs.lean:145). Use well-founded induction on unvisited thread set (finite, strictly decreasing). | `SeLe4n/Kernel/Scheduler/PriorityInheritance/BlockingGraph.lean` | Medium |
| D4-E | **Prove blocking chain depth bound.** In the same file, prove `blockingChain_bounded`: `blockingChain st tid fuel |>.length ≤ countTCBs st`. The chain visits distinct threads (from D4-D), and the number of TCBs is finite. This bounds PIP propagation cost. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/BlockingGraph.lean` | Small |
| D4-F | **Define `computeMaxWaiterPriority`.** Create `SeLe4n/Kernel/Scheduler/PriorityInheritance/Compute.lean`. Define `computeMaxWaiterPriority (st : SystemState) (tid : ThreadId) : Option Priority` — returns the maximum effective priority among all threads in `waitersOf st tid`, or `none` if no waiters. Prove `computeMaxWaiterPriority_ge`: if result is `some p`, then `∃ waiter ∈ waitersOf st tid, effectivePriority st waiter ≥ p`. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/Compute.lean` | Small |
| D4-G | **Implement `updatePipBoost` (single-thread).** Create `SeLe4n/Kernel/Scheduler/PriorityInheritance/Propagate.lean`. Implement `updatePipBoost (st : SystemState) (tid : ThreadId) : SystemState` — computes `computeMaxWaiterPriority st tid`. If result is `some p` and `p > basePriority`, sets `tcb.pipBoost := some p`; otherwise clears `tcb.pipBoost := none`. If the thread is in the run queue and effective priority changed, performs remove-then-insert for bucket migration (reuses D2-E pattern). | `SeLe4n/Kernel/Scheduler/PriorityInheritance/Propagate.lean` | Medium |
| D4-H | **Implement `propagatePriorityInheritance` (chain walk).** In the same file, implement `propagatePriorityInheritance (st : SystemState) (startTid : ThreadId) (fuel : Nat := st.objects.size) : SystemState`. Walks the blocking chain upward from `startTid`: (1) apply `updatePipBoost` to `startTid`; (2) if `startTid` has `ipcState = .blockedOnReply _ (some server)`, recurse on `server` with `fuel - 1`; (3) terminate when `fuel = 0` or no further server. The walk is guaranteed to terminate (acyclicity D4-D + fuel bound D4-E). | `SeLe4n/Kernel/Scheduler/PriorityInheritance/Propagate.lean` | Medium |
| D4-I | **Implement `revertPriorityInheritance`.** In the same file, implement `revertPriorityInheritance (st : SystemState) (tid : ThreadId) (fuel : Nat := st.objects.size) : SystemState` — called when `tid` completes a Reply (client unblocked). Walks the chain from `tid` downward, recomputing `pipBoost` for `tid` and all threads that were transitively boosted through `tid`. Uses `updatePipBoost` at each step. If the chain collapses (no more waiters), `pipBoost` clears naturally. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/Propagate.lean` | Medium |
| D4-J | **Prove propagation correctness.** In the same file, prove `propagate_correct`: after `propagatePriorityInheritance st startTid`, every thread on the blocking chain has `pipBoost = computeMaxWaiterPriority`. Proof by induction on chain length: each step applies `updatePipBoost` (correct by construction), and the chain visits every thread on the path (from blocking chain definition). | `SeLe4n/Kernel/Scheduler/PriorityInheritance/Propagate.lean` | Medium |
| D4-K | **Prove reversion correctness.** Prove `revert_correct`: after `revertPriorityInheritance st tid`, every thread on the chain has `pipBoost` reflecting only its remaining waiters (excluding the unblocked client). Structural: same induction as D4-J, but `waitersOf` returns fewer threads after client removal. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/Propagate.lean` | Medium |
| D4-L | **Integrate PIP into Call path.** Modify `endpointCallWithDonation` (Donation.lean) to call `propagatePriorityInheritance st serverId` after the client enters `blockedOnReply`. The propagation walks upward from the server: if the server is itself blocked on another server, that server's `pipBoost` is also updated. This ensures transitive priority inheritance through the full chain. | `SeLe4n/Kernel/IPC/Operations/Donation.lean` | Medium |
| D4-M | **Integrate PIP revert into Reply path.** Modify `endpointReplyWithDonation` (Donation.lean) to call `revertPriorityInheritance st replyingServerId` after the client is unblocked. The reversion walks downward, clearing `pipBoost` values that are no longer needed. If the server has other clients still waiting, `pipBoost` reflects the highest remaining client. | `SeLe4n/Kernel/IPC/Operations/Donation.lean` | Medium |
| D4-N | **Integrate PIP cleanup into suspend.** Modify `suspendThread` (D1-G) to call `revertPriorityInheritance` before clearing state. If a suspended thread has `pipBoost`, it may be holding boosted priority for upstream servers — those servers' `pipBoost` values must be recomputed after the suspended thread is removed from the blocking graph. | `SeLe4n/Kernel/Lifecycle/Suspend.lean` | Small |
| D4-O | **Prove `propagatePriorityInheritance` preserves `schedulerInvariantBundleExtended`.** Create `SeLe4n/Kernel/Scheduler/PriorityInheritance/Preservation.lean`. Each chain step applies `updatePipBoost` which only modifies `tcb.pipBoost` and performs conditional run queue bucket migration. Per-component proofs: queue consistency (remove-then-insert), uniqueness, time-slice/budget unchanged, priority match updated. Compose across chain by induction. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/Preservation.lean` | Medium |
| D4-P | **Prove PIP preserves IPC and cross-subsystem invariants (frame).** In the same file, prove that propagation and reversion do not modify IPC state (`tcb.ipcState`), endpoint queues, notification wait lists, SchedContext objects, or CDT. The only TCB field modified is `pipBoost`. Frame preservation for all IPC and cross-subsystem predicates. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/Preservation.lean` | Medium |
| D4-Q | **Prove bounded inversion.** Create `SeLe4n/Kernel/Scheduler/PriorityInheritance/BoundedInversion.lean`. Prove `pip_bounded_inversion`: if thread H is `blockedOnReply` and the blocking chain from H has depth D, then H is transitively blocked for at most `D × WCRT(effectivePriority(H))` ticks. Proof: at each chain link, PIP ensures the server runs at ≥ H's effective priority; from D5's WCRT bound (or parametrically if D5 is not yet complete), each server completes within `WCRT(effectivePriority(H))` ticks. Compose D links. Chain depth bounded by D4-E. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/BoundedInversion.lean` | Medium |
| D4-R | **Prove PIP determinism.** In the same file, prove `pip_deterministic`: both `propagatePriorityInheritance` and `revertPriorityInheritance` are pure functions of `SystemState` and produce identical results for identical inputs. Follows from deterministic blocking graph traversal. | `SeLe4n/Kernel/Scheduler/PriorityInheritance/BoundedInversion.lean` | Trivial |
| D4-S | **Create re-export hub and test coverage.** Create `SeLe4n/Kernel/Scheduler/PriorityInheritance.lean` re-export hub. Create `tests/PriorityInheritanceSuite.lean` with test cases: (1) PIP activates on Call — server `pipBoost` elevated; (2) PIP deactivates on Reply — server `pipBoost` cleared; (3) transitive PIP through 3-thread chain; (4) PIP does not affect threads outside blocking chain; (5) `effectivePriority ≥ basePriority` always; (6) run queue placement matches boosted priority; (7) suspend clears PIP boost and reverts chain; (8) PIP with SchedContext donation composes correctly. | `SeLe4n/Kernel/Scheduler/PriorityInheritance.lean`, `tests/PriorityInheritanceSuite.lean`, `lakefile.lean` | Medium |
| D4-T | **Documentation sync.** Update spec with PIP semantics (pipBoost, blocking graph, propagation/reversion, composition with SchedContext donation). Update claims index with bounded-inversion claim. Update CLAUDE.md source layout for `Scheduler/PriorityInheritance/`. Regenerate codebase map. | Docs | Small |
 
**Intra-phase ordering constraints:**
- Type foundation: D4-A → D4-B (TCB field → effectivePriority update)
- Graph model: D4-C → D4-D → D4-E (define → acyclicity → depth bound)
- Compute: D4-C → D4-F (graph → max waiter priority)
- Propagation: D4-F → D4-G → D4-H → D4-J (compute → single-update → chain-walk → correctness)
- Reversion: D4-G → D4-I → D4-K (single-update → revert → correctness)
  - D4-H/J and D4-I/K can run in parallel
- IPC integration: D4-H + D4-I → D4-L/D4-M (propagate + revert → Call/Reply hooks; parallel)
- Suspend integration: D4-I → D4-N (revert → suspend cleanup)
- Preservation: D4-H + D4-I + D4-L + D4-M → D4-O → D4-P (ops → scheduler preservation → frame)
  - D4-O and D4-P are independent
- Bounded inversion: D4-D + D4-E + D4-J → D4-Q → D4-R
- Infrastructure: D4-R → D4-S → D4-T
 
---
 
## 8. Phase D5 — Bounded Latency Theorem (v0.24.4)
 
**Scope**: Prove a conditional worst-case response time (WCRT) bound for the
existing scheduler — with zero kernel code changes. Establish the trace model
infrastructure that formalizes liveness guarantees for the CBS budget model,
domain scheduling, and PIP-aware effective priority resolution. This is the
first machine-checked WCRT for a microkernel with MCS scheduling contexts.
 
**Rationale**: The kernel proves extensive safety properties but zero liveness
properties. Every theorem says "nothing bad happens" but none says "something
good eventually happens." This gap is critical for real-time systems on the RPi5
target: system integrators need formal WCRT bounds to prove schedulability of
their task sets. D5 closes this gap by proving that a runnable thread with
sufficient budget is selected within a bounded number of ticks.
 
**Key update from WS-V V1**: The original V1 plan assumed a simple quantum-based
scheduler. The current codebase has CBS budget accounting (Z2), SchedContext-aware
effective priority (Z4), replenishment queues (Z3), and PIP boost (D4). The WCRT
bound must account for:
1. Budget exhaustion: a thread may be preempted by budget depletion, not just
   time-slice expiry, and must wait for replenishment.
2. CBS period: the WCRT includes at most one replenishment period per budget cycle.
3. Effective priority: with PIP (D4), a thread's effective priority may change
   dynamically; the WCRT depends on the effective priority at the time of analysis.
4. Domain scheduling: unchanged from V1 — rotation bound over static table.
 
**Dependencies**: D4 (PIP-aware effective priority for WCRT hypothesis).
Strictly, D5 can proceed with a parametric `effectivePriorityResolution` function
and plug in D4's concrete implementation later. This allows partial parallelism.
 
**Gate**: All liveness theorems compile without `sorry`/`axiom`. `test_full.sh`
passes. Zero code changes to existing kernel files. New `Scheduler/Liveness/`
module builds via `lake build SeLe4n.Kernel.Scheduler.Liveness.WCRT`.
 
**Sub-tasks (16):**
 
| ID | Description | Files | Estimate |
|----|-------------|-------|----------|
| D5-A | **Define trace model types.** Create `SeLe4n/Kernel/Scheduler/Liveness/TraceModel.lean`. Define `SchedulerStep` inductive: `timerTick`, `timerTickBudget`, `schedule`, `scheduleEffective`, `handleYield`, `handleYieldWithBudget`, `switchDomain`, `processReplenishmentsDue`, `ipcTimeoutTick`. Define `SchedulerTrace := List (SchedulerStep × SystemState)`. Define `validTrace` predicate: each step's precondition holds and postcondition state feeds into next step's precondition. Include `timerTickBudget` 3-branch case analysis (Z4-F). | `SeLe4n/Kernel/Scheduler/Liveness/TraceModel.lean` | Medium |
| D5-B | **Define trace query predicates.** In the same file, define: `selectedAt (trace) (k : Nat) (tid) : Prop` — thread `tid` is `scheduler.current` at trace index `k`; `runnableAt (trace) (k : Nat) (tid) : Prop` — thread is in run queue at index `k`; `budgetAvailableAt (trace) (k : Nat) (tid) : Prop` — thread's bound SchedContext has `hasSufficientBudget`. Prove `selectedAt_implies_not_runnableAt` (from `queueCurrentConsistent`). Prove `selectedAt_implies_budgetAvailableAt` (from `chooseThreadEffective` selection criteria). | `SeLe4n/Kernel/Scheduler/Liveness/TraceModel.lean` | Medium |
| D5-C | **Define counting predicates.** Define `countHigherOrEqualEffectivePriority (tid : ThreadId) (st : SystemState) : Nat` — threads in run queue with `effectivePriority ≥ effectivePriority(tid)` in the same domain. Define `maxBudgetInBand (tid) (st) : Nat` — maximum SchedContext budget among those threads. Define `maxPeriodInBand (tid) (st) : Nat` — maximum SchedContext period. Define `bucketPosition (tid) (st) : Option Nat` — 0-indexed position in priority bucket. These are pure read-only functions. | `SeLe4n/Kernel/Scheduler/Liveness/TraceModel.lean` | Small |
| D5-D | **Prove timer-tick budget monotonicity.** Create `SeLe4n/Kernel/Scheduler/Liveness/TimerTick.lean`. Prove `timerTickBudget_decrements_budget`: if `current = some tid` and `hasSufficientBudget sc`, after `timerTickBudget`, `sc'.budget.remaining = sc.budget.remaining - 1` (saturating). This follows from `consumeBudget` (Budget.lean) definition. Prove `timerTickBudget_preempts_on_exhaustion`: if `sc.budget.remaining ≤ 1`, after `timerTickBudget`, thread is re-enqueued and `schedule` called (Z4-F branch F2). | `SeLe4n/Kernel/Scheduler/Liveness/TimerTick.lean` | Medium |
| D5-E | **Prove replenishment bound.** Create `SeLe4n/Kernel/Scheduler/Liveness/Replenishment.lean`. Prove `replenishment_within_period`: if a SchedContext's budget is exhausted at tick T, its budget is replenished by tick `T + sc.period` (from `processReplenishmentsDue` + `cbsUpdateDeadline`). This bounds the "dead time" between budget exhaustion and replenishment. | `SeLe4n/Kernel/Scheduler/Liveness/Replenishment.lean` | Medium |
| D5-F | **Prove time-slice preemption bound.** In `TimerTick.lean`, prove `timerTick_preemption_bound`: for threads without SchedContext binding (legacy path), preemption occurs within `tcb.timeSlice` ticks. This is the original V1-D/V1-E result, unchanged for unbound threads. Combined with D5-D for bound threads: preemption occurs within `min(tcb.timeSlice, sc.budget.remaining)` ticks. | `SeLe4n/Kernel/Scheduler/Liveness/TimerTick.lean` | Small |
| D5-G | **Prove yield/rotation semantics.** Create `SeLe4n/Kernel/Scheduler/Liveness/Yield.lean`. Prove `handleYieldWithBudget_rotates_to_back`: after yield, thread is at tail of priority bucket. Prove `fifo_single_step_advance`: if thread at position `k > 0` in bucket and thread at `k-1` is preempted or yields, position becomes `k-1`. Structurally identical to original V1-F/V1-G but references `handleYieldWithBudget` (Core.lean:656). | `SeLe4n/Kernel/Scheduler/Liveness/Yield.lean` | Small |
| D5-H | **Prove FIFO progress within priority band.** In the same file, prove `fifo_progress_in_band`: thread at position `k` in its priority bucket, with no higher-effective-priority threads in active domain, is selected within `k × max_preemption_interval` ticks. The `max_preemption_interval` for a bound thread is `min(timeSlice, budget) + period` (budget exhaustion + one replenishment wait). For unbound threads, it is `timeSlice`. Proof by induction on `k`. | `SeLe4n/Kernel/Scheduler/Liveness/Yield.lean` | Medium |
| D5-I | **Prove priority-band exhaustion.** Create `SeLe4n/Kernel/Scheduler/Liveness/BandExhaustion.lean`. Prove `higher_band_exhaustion`: if all threads at effective priority > P are eventually removed from run queue (blocked, budget-exhausted-and-not-yet-replenished, suspended, or deleted), then a thread at priority P will be selected. Conditional liveness lemma. Updated to use `effectivePriority` (which incorporates `pipBoost` from D4). | `SeLe4n/Kernel/Scheduler/Liveness/BandExhaustion.lean` | Medium |
| D5-J | **Prove domain rotation bound.** Create `SeLe4n/Kernel/Scheduler/Liveness/DomainRotation.lean`. Prove `domain_rotation_bound`: if `domainSchedule` has `D` entries with maximum length `L_max`, every domain receives CPU within `D × L_max` ticks. Unchanged from original V1-J — domain scheduling is static and unaffected by CBS/PIP. Uses `switchDomain` round-robin semantics (Core.lean). | `SeLe4n/Kernel/Scheduler/Liveness/DomainRotation.lean` | Medium |
| D5-K | **Define CBS-aware WCRT hypotheses.** Create `SeLe4n/Kernel/Scheduler/Liveness/WCRT.lean`. Define `WCRTHypotheses` structure: (1) thread `tid` is in run queue with `hasSufficientBudget`; (2) `tid` is in domain `d` in `domainSchedule`; (3) `countHigherOrEqualEffectivePriority tid st ≤ N`; (4) all threads in band have budget ≤ B and period ≤ P; (5) domain schedule entry for `d` has length ≥ `N × (B + P)` (accounts for budget + replenishment per thread). Prove `wcrt_hypotheses_stable_under_timerTickBudget`. | `SeLe4n/Kernel/Scheduler/Liveness/WCRT.lean` | Medium |
| D5-L | **Prove the main WCRT theorem.** In the same file, prove `bounded_scheduling_latency`: given `WCRTHypotheses`, thread `tid` is selected within `D × L_max + N × (B + P)` ticks. Structure: (1) `domain_rotation_bound` (D5-J) → domain active within `D × L_max`; (2) `fifo_progress_in_band` (D5-H) → thread selected within `N × (B + P)` ticks in active domain; (3) compose via `Nat.le_trans`. The bound `N × (B + P)` accounts for each higher-priority thread consuming its budget `B` then waiting for replenishment `P` before the target thread advances one position. | `SeLe4n/Kernel/Scheduler/Liveness/WCRT.lean` | Medium |
| D5-M | **Prove PIP-enhanced WCRT.** In the same file, prove `bounded_scheduling_latency_pip`: if thread `tid` has `pipBoost = some p` (from D4), the WCRT bound uses `effectivePriority(tid)` which is `max(scPrio, p)`. This means PIP-boosted threads have a tighter bound (fewer higher-priority competitors). Corollary of D5-L with `effectivePriority` substitution. | `SeLe4n/Kernel/Scheduler/Liveness/WCRT.lean` | Small |
| D5-N | **Create re-export hub.** Create `SeLe4n/Kernel/Scheduler/Liveness.lean` re-exporting `TraceModel`, `TimerTick`, `Replenishment`, `Yield`, `BandExhaustion`, `DomainRotation`, `WCRT`. | `SeLe4n/Kernel/Scheduler/Liveness.lean` | Trivial |
| D5-O | **Add test surface anchors.** Add Tier 3 invariant surface anchor tests referencing `bounded_scheduling_latency`, `domain_rotation_bound`, `fifo_progress_in_band`, `timerTickBudget_preempts_on_exhaustion`, `replenishment_within_period`, `pip_bounded_inversion` (D4-Q). | `tests/LivenessSuite.lean`, `lakefile.lean` | Small |
| D5-P | **Documentation sync.** Update spec with WCRT bound statement, CBS-aware hypotheses, and PIP enhancement. Update claims index with liveness claims. Update CLAUDE.md with `Scheduler/Liveness/` directory. Regenerate codebase map. | Docs | Small |
 
**Intra-phase ordering constraints:**
- Trace model foundation: D5-A → D5-B → D5-C (types → queries → counting)
- Timer-tick chain: D5-D → D5-F (budget monotonicity → preemption bound)
- Replenishment: D5-D → D5-E (budget exhaustion → replenishment bound)
- Yield/FIFO chain: D5-G → D5-H (rotation → FIFO progress)
- D5-H depends on D5-D + D5-E + D5-F (preemption + replenishment → interval)
- Band exhaustion: D5-I (depends on D5-C for counting; independent of yield chain)
- Domain rotation: D5-J (depends on D5-A for trace model; otherwise independent)
- WCRT: D5-H + D5-I + D5-J → D5-K → D5-L → D5-M
- D5-D/D5-E and D5-G are independent chains (can run in parallel)
- D5-I and D5-J are independent (can run in parallel)
- Infrastructure: D5-M → D5-N → D5-O → D5-P
 
---
 
## 9. Phase D6 — API Surface Integration & Closure (v0.24.5)
 
**Scope**: Finalize the public API surface for all deferred operations, ensure
full enforcement boundary coverage, complete documentation synchronization, and
perform the closure audit to verify zero regressions across all subsystems.
 
**Rationale**: Each preceding phase implemented individual operations and their
proofs. D6 ensures these integrate cleanly into the unified kernel API, that
information-flow enforcement covers all new syscalls, that the Rust ABI layer
is synchronized, and that all documentation is consistent.
 
**Dependencies**: D1, D2, D3, D4, D5 (all prior phases must be complete).
 
**Gate**: `test_full.sh` passes. `enforcementBoundary` covers all 30 syscalls.
`frozenOpCoverage_count = 20`. All documentation synchronized. Zero `sorry`/`axiom`.
Nightly test suite passes.
 
**Sub-tasks (10):**
 
| ID | Description | Files | Estimate |
|----|-------------|-------|----------|
| D6-A | **Verify enforcement boundary completeness.** Confirm `enforcementBoundary` in Wrappers.lean has entries for all 30 SyscallId variants (25 existing + 5 new deferred operations). Prove `enforcementBoundary_names_nonempty` and `enforcementBoundaryComplete_counts` updated. Verify every new syscall is classified as `.capabilityOnly` or `.withArgs` consistently with its dispatch path. | `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` | Small |
| D6-B | **Verify `dispatchWithCap_wildcard_unreachable`.** After adding 5 new SyscallId arms, confirm the wildcard case in `dispatchWithCap` remains unreachable. Update or re-prove `dispatchWithCap_wildcard_unreachable` (W2-C). This ensures no syscall silently falls through to a default error path. | `SeLe4n/Kernel/API.lean` | Small |
| D6-C | **Verify frozen operation coverage.** Confirm `frozenOpCoverage_count = 20` (15 existing + 5 new: frozenSuspendThread, frozenResumeThread, frozenSetPriority, frozenSetMCPriority, frozenSetIPCBuffer). Verify each frozen operation correctly wraps its pure-function counterpart with `FrozenKernel` monad lookup/store. | `SeLe4n/Kernel/FrozenOps/Operations.lean` | Small |
| D6-D | **Synchronize Rust ABI types.** Update `SyscallId` in the Rust ABI layer: add `TcbSuspend = 20`, `TcbResume = 21`, `TcbSetPriority = 22`, `TcbSetMCPriority = 23`, `TcbSetIPCBuffer = 24`. Update `SyscallId.COUNT` to 25. Verify compile-time constant sync assertions (W6-G pattern). Update any Rust argument decode structures. | Rust ABI files | Medium |
| D6-E | **Run comprehensive test suite.** Execute `test_full.sh` (Tier 0-3). Verify all new test suites pass: SuspendResumeSuite, PriorityManagementSuite, IpcBufferSuite, PriorityInheritanceSuite, LivenessSuite. Run `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh` for full Tier 4 coverage. Fix any regressions. | Tests | Medium |
| D6-F | **Update `docs/spec/SELE4N_SPEC.md` §5.14 comprehensively.** Replace the deferred operations table with an "Implemented Operations" table showing all 5 operations with their version, invariant preservation references, and key theorem names. Add new subsections: §5.14.1 (Thread Suspension Semantics), §5.14.2 (Priority Management via MCS), §5.14.3 (IPC Buffer Validation), §5.14.4 (Priority Inheritance Protocol), §5.14.5 (Bounded Latency Guarantees). | `docs/spec/SELE4N_SPEC.md` | Medium |
| D6-G | **Update `docs/CLAIM_EVIDENCE_INDEX.md`.** Add 8 new claims: (1) suspend preserves all invariants; (2) resume preserves all invariants; (3) MCP authority non-escalation; (4) IPC buffer validation correctness; (5) PIP bounded inversion; (6) PIP determinism; (7) CBS-aware WCRT bound; (8) domain rotation bound. Each claim references the specific theorem name, file, and line. | `docs/CLAIM_EVIDENCE_INDEX.md` | Small |
| D6-H | **Update `CLAUDE.md` source layout and active workstream context.** Add new file entries: `Lifecycle/Suspend.lean`, `Lifecycle/Invariant/SuspendPreservation.lean`, `SchedContext/PriorityManagement.lean`, `SchedContext/Invariant/PriorityPreservation.lean`, `Architecture/IpcBufferValidation.lean`, `Scheduler/PriorityInheritance/*` (6 files), `Scheduler/Liveness/*` (7 files). Update workstream context to show WS-AB as COMPLETE. Update known large files if any new file exceeds 500 lines. | `CLAUDE.md` | Medium |
| D6-I | **Regenerate `docs/codebase_map.json` and update metrics.** Run codebase map generation. Update `README.md` metrics: syscall count (20→25), theorem count, proof line count, object types, invariant count. Update `docs/WORKSTREAM_HISTORY.md` with WS-AB summary (6 phases, sub-task counts, version range). Update `CHANGELOG.md` with v0.24.0–v0.24.5 entries. | `docs/codebase_map.json`, `README.md`, `docs/WORKSTREAM_HISTORY.md`, `CHANGELOG.md` | Medium |
| D6-J | **Update website link manifest.** Verify all new files and directories are listed in `scripts/website_link_manifest.txt` if they are referenced by the website. Run `scripts/check_website_links.sh` to verify consistency. | `scripts/website_link_manifest.txt` | Small |
 
**Intra-phase ordering constraints:**
- D6-A/B/C are verification tasks, independent of each other (parallel)
- D6-D (Rust ABI) independent of D6-A/B/C
- D6-E depends on D6-A/B/C/D (all verifications → comprehensive test)
- D6-F/G/H/I are documentation tasks, largely independent (parallel after D6-E)
- D6-J depends on D6-F/H (new paths may need manifest entries)
 
---
 
## 10. Scope Summary
 
### 10.1 Sub-task Count by Phase
 
| Phase | Version | Sub-tasks | Complexity | Nature |
|-------|---------|-----------|-----------|--------|
| D1 — Thread Suspend/Resume | v0.24.0 | 18 | High | New syscalls + lifecycle transitions + full preservation proofs |
| D2 — Priority Management | v0.24.1 | 14 | Medium | SchedContext priority updates + authority model |
| D3 — IPC Buffer Configuration | v0.24.2 | 12 | Low | VSpace validation + simple field update |
| D4 — Priority Inheritance Protocol | v0.24.3 | 20 | High | Blocking graph + transitive propagation + bounded inversion proofs |
| D5 — Bounded Latency Theorem | v0.24.4 | 16 | High | Proof-only: CBS-aware WCRT bound (zero code changes) |
| D6 — API Surface & Closure | v0.24.5 | 10 | Medium | Integration, verification, documentation |
| **Total** | | **90** | | |
 
### 10.2 Deferred Operation Coverage
 
| Operation | Phase | SyscallId | Dispatch Path | Key Theorem |
|-----------|-------|-----------|--------------|-------------|
| `suspend` | D1 | `.tcbSuspend` | `dispatchCapabilityOnly` | `suspend_preserves_proofLayerInvariantBundle` |
| `resume` | D1 | `.tcbResume` | `dispatchCapabilityOnly` | `resume_preserves_proofLayerInvariantBundle` |
| `setPriority` | D2 | `.tcbSetPriority` | `dispatchWithCap` | `setPriority_authority_bounded` |
| `setMCPriority` | D2 | `.tcbSetMCPriority` | `dispatchWithCap` | `setMCPriority_authority_bounded` |
| `setIPCBuffer` | D3 | `.tcbSetIPCBuffer` | `dispatchWithCap` | `validateIpcBufferAddress_implies_mapped` |
 
### 10.3 Starvation Vector Coverage (Updated)
 
| ID | Vector | Severity | Addressed In | Resolution |
|----|--------|----------|-------------|------------|
| SV-1 | Strict priority starvation | HIGH | D5 (WCRT) + Z2 (CBS) | Formal WCRT bound + runtime CBS budget |
| SV-2 | Priority inversion via Call/Reply | HIGH | D4 (PIP) + Z7 (donation) | Transitive PIP + SchedContext donation |
| SV-3 | Unbounded IPC blocking | HIGH | Z6 (budget timeout) | Budget-driven forced unblock (COMPLETE) |
| SV-4 | Notification LIFO ordering | MEDIUM | Deferred | seL4 semantic compatibility; accepted |
| SV-5 | Domain schedule imbalance | MEDIUM | D5 (domain rotation bound) | Formal rotation bound proves each domain gets CPU |
| SV-6 | Run queue cycling without bound | LOW | D5 (FIFO progress) | Formal FIFO progress within priority band |
| SV-7 | Admission over-commitment | LOW | Existing (Z5) | `admissionCheck` validates bandwidth ≤ 100% |
| SV-8 | Replenishment queue delay | LOW | D5 (replenishment bound) | Formal replenishment-within-period bound |
| SV-9 | Donation chain depth | MEDIUM | D4 (depth bound) | `blockingChain_bounded` proves finite depth |
 
### 10.4 Files Impacted by Phase
 
| Phase | New Lean Files | Modified Lean Files | New Test Files | Doc Files |
|-------|---------------|--------------------|--------------|---------:|
| D1 | 2 (Lifecycle/Suspend, Invariant/SuspendPreservation) | ~5 (Types, API, SyscallArgDecode, Wrappers, FrozenOps) | 1 | 4 |
| D2 | 2 (SchedContext/PriorityManagement, Invariant/PriorityPreservation) | ~5 (Types, API, SyscallArgDecode, Wrappers, FrozenOps) | 1 | 4 |
| D3 | 1 (Architecture/IpcBufferValidation) | ~5 (Types, API, SyscallArgDecode, Wrappers, FrozenOps) | 1 | 4 |
| D4 | 6 (PriorityInheritance/: BlockingGraph, Compute, Propagate, Preservation, BoundedInversion, re-export) | ~3 (Types, Donation, Suspend) | 1 | 4 |
| D5 | 8 (Liveness/: TraceModel, TimerTick, Replenishment, Yield, BandExhaustion, DomainRotation, WCRT, re-export) | 0 | 1 | 4 |
| D6 | 0 | ~3 (Wrappers, API, FrozenOps verification) | 0 | 7 |
| **Total** | **~19** | **~21** | **5** | **27** |
 
### 10.5 Effort Distribution
 
| Estimate | D1 | D2 | D3 | D4 | D5 | D6 | Total |
|----------|----|----|----|----|----|----|-------|
| Trivial | 0 | 0 | 1 | 1 | 1 | 0 | **3** |
| Small | 6 | 7 | 10 | 6 | 6 | 5 | **40** |
| Medium | 12 | 7 | 1 | 13 | 9 | 5 | **47** |
| Large | 0 | 0 | 0 | 0 | 0 | 0 | **0** |
| **Total** | **18** | **14** | **12** | **20** | **16** | **10** | **90** |
 
All tasks decomposed to ≤ Medium. No individual sub-task requires more than ~1
day of focused work. The decomposition preserves the project's established
invariant preservation proof pattern: component lemmas composed into bundle
proofs via `⟨comp1, comp2, ..., compN⟩`.
 
---
 
## 11. Technical Risks
 
### 11.1 Implementation Risks
 
| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| D1 suspend cleanup misses a queue/state combination | Medium | High | Systematic case-split on all 6 `ThreadIpcState` variants × `SchedContextBinding` variants × `threadState` variants. The `cancelIpcBlocking` function explicitly handles every IPC state. Reuse proven patterns from Z6 `timeoutThread` and lifecycle `cleanupTcbReferences`. |
| D1 suspend of current thread creates invalid scheduler state | Medium | High | Clear `scheduler.current` immediately on self-suspend. Trigger `schedule` to select next thread. Follow the pattern from `timerTick` preemption (Core.lean:362) which handles the same "current thread leaves run queue" scenario. |
| D2 priority change during active PIP creates inconsistency | Medium | High | If target thread has `pipBoost`, `setPriorityOp` must recompute effective priority after the base priority change. The `effectivePriority` resolution (D4-B) already computes `max(scPrio, pipBoost)`, so changing the base does not invalidate the boost — it may change the `max` result. Rerun `updatePipBoost` on the target thread after priority change. |
| D3 VSpace lookup returns stale mapping after concurrent unmap | Low | High | The kernel is single-threaded (cooperative scheduling within kernel). No concurrent unmap can occur between validation and field update. If the user-space VSpace is modified after `setIPCBuffer` returns, the kernel must handle page faults on next IPC — this is existing behavior, not a new concern. |
| D4 PIP propagation loop exceeds heartbeat budget in Lean | Medium | Medium | Blocking chain depth bounded by thread count (D4-E). In practice, chains rarely exceed depth 3–4. Set `set_option maxHeartbeats 400000` in propagation proofs if needed (following W2-H pattern). Use fuel parameter for well-founded termination. |
| D4 PIP interaction with Z7 donation creates double-boost | Medium | High | Design prevents this: `pipBoost` and SchedContext donation operate on orthogonal fields. `pipBoost` boosts the TCB's scheduling visibility; donation transfers the SchedContext itself. `effectivePriority` computes `max(scPrio, pipBoost)`, correctly handling both. If a thread receives a donated SchedContext AND has `pipBoost`, it runs at the higher of the two — this is correct behavior (conservative overapproximation). |
| D5 WCRT proof requires assumptions too strong for practical use | Medium | Low | State hypotheses explicitly in `WCRTHypotheses` structure. A conditional bound with clear assumptions is still valuable — system integrators can verify the hypotheses hold for their specific task sets. Follow V1's approach: the bound is parametric, not absolute. |
| D5 CBS period variability invalidates simple WCRT formula | Low | Medium | The WCRT formula `N × (B + P)` uses worst-case per-thread values. If actual budgets and periods vary, the bound is conservative but still valid. A tighter analysis (response-time iteration) is deferred to a future real-time analysis framework workstream. |
 
### 11.2 Schedule Risks
 
| Risk | Mitigation |
|------|------------|
| D4 + D5 combined is very large (36 sub-tasks) and may slip | D1/D2/D3 are independently valuable and can ship immediately. D4 and D5 each close specific starvation vectors. D4 can be split into sub-phases (D4a: types + graph D4-A–E, D4b: propagation D4-F–K, D4c: integration D4-L–N, D4d: proofs D4-O–T). |
| D1 depends on understanding all subsystem interactions | Systematic audit: enumerate every reference to `ThreadIpcState`, `ThreadState`, `scheduler.current`, and run queue insertion/removal. The existing lifecycle cleanup (`lifecyclePreRetypeCleanup`, `cleanupTcbReferences`) already performs most of this work — suspend is structurally similar. |
| D2/D3 type changes conflict with D1 if developed in parallel | Additive changes only: D1 adds 2 SyscallId variants, D2 adds 2, D3 adds 1. Each adds new constructors — no conflicting modifications to existing constructors. D2-A adds a new TCB field; D4-A adds another. Both are additive. Merge conflicts are simple enum-extension merges. |
| D5 proof work is unbounded in difficulty | D5 is proof-only with zero code changes. If proofs are harder than expected, D5 can be delivered incrementally: (1) trace model infrastructure first (D5-A–C), (2) per-mechanism bounds (D5-D–J), (3) composite WCRT last (D5-K–M). Each intermediate result is independently publishable. |
 
---
 
## 12. Invariant Landscape
 
### 12.1 Invariants Preserved by Each Phase
 
| Invariant Bundle | D1 | D2 | D3 | D4 | D5 | D6 |
|-----------------|----|----|----|----|----|----|
| `schedulerInvariantBundleExtended` (15-tuple) | D1-K/L: suspend removes from queue; resume inserts | D2-G: priority bucket migration | Frame (ipcBuffer not referenced) | D4-O: PIP bucket migration across chain | Read-only | Verify |
| `ipcInvariantFull` (14 conjuncts) | D1-J: IPC blocking cancellation | D2-H: frame (priority not in IPC) | Frame | D4-P: frame (pipBoost not in IPC) | Read-only | Verify |
| `crossSubsystemInvariant` (8 predicates) | D1-M: SchedContext cleanup, queue removal | D2-H: `schedContextStoreConsistent` | Frame | D4-P: frame | Read-only | Verify |
| `proofLayerInvariantBundle` (10 conjuncts) | Composed from above | Composed from above | D3-F: single frame theorem | Composed from above | Read-only | Verify |
 
### 12.2 New Invariant Predicates Introduced
 
| Phase | Predicate | Description |
|-------|-----------|-------------|
| D2 | `mcpAuthorityMonotone` | `∀ target, target.priority ≤ caller.maxControlledPriority` after `setPriority` |
| D4 | `pipBoostConsistent` | `tcb.pipBoost = computeMaxWaiterPriority st tid` for all threads on blocking chains |
| D4 | `effectivePriorityGeBase` | `effectivePriority st tid ≥ basePriority tid` always (incorporates pipBoost) |
| D4 | `pipBoundedInversion` | Inversion bounded by `chainDepth × WCRT(effectivePriority)` |
| D5 | `validTrace` | Trace of scheduler steps where each precondition holds |
| D5 | `selectedAt` | Thread is `scheduler.current` at trace index k |
| D5 | `budgetAvailableAt` | Thread has `hasSufficientBudget` at trace index k |
| D5 | `bounded_scheduling_latency` | CBS-aware WCRT: thread selected within `D×L_max + N×(B+P)` ticks |
 
---
 
## 13. Acceptance Criteria Summary
 
| Phase | Test Gate | Proof Gate | Code Gate |
|-------|-----------|------------|-----------|
| D1 | `test_full.sh` + SuspendResumeSuite | `suspendThread`/`resumeThread` preserve `proofLayerInvariantBundle` | 2 new syscalls dispatched; 2 frozen ops |
| D2 | `test_full.sh` + PriorityManagementSuite | `setPriorityOp`/`setMCPriorityOp` preserve bundles; authority non-escalation proven | 2 new syscalls; MCP field on TCB; 2 frozen ops |
| D3 | `test_full.sh` + IpcBufferSuite | `setIPCBufferOp` frame preservation; validation correctness | 1 new syscall; VSpace validation; 1 frozen op |
| D4 | `test_full.sh` + PriorityInheritanceSuite | PIP propagation/reversion preserve bundles; `pip_bounded_inversion`; determinism | PIP activates on Call, deactivates on Reply; composes with Z7 donation |
| D5 | `test_full.sh` + LivenessSuite (Tier 3 anchors) | `bounded_scheduling_latency` proven; CBS-aware WCRT; domain rotation bound | Zero code changes (proof-only) |
| D6 | `test_full.sh` + nightly | Enforcement boundary complete (30 entries); frozen op coverage (20) | All docs synchronized; Rust ABI updated |
 
**Universal gates (all phases)**:
- Zero `sorry` in production proof surface
- Zero `axiom` in production proof surface
- Module build verified for every modified `.lean` file (`lake build <Module.Path>`)
- No website-linked paths renamed or removed (see `scripts/website_link_manifest.txt`)
- Documentation synchronized (spec, claims, source layout, codebase map)
 
---
 
## 14. Workstream Naming Convention
 
This workstream is designated **WS-AB** (following the alphabetical sequence
after WS-AA, the Rust ABI Type Synchronization workstream). The designation
reflects the dual nature of the work: implementing the five **deferred
operations** from spec §5.14 while completing the **liveness guarantees**
originally planned in the WS-V starvation prevention workstream.
 
| Workstream | Focus | Version Range |
|------------|-------|---------------|
| WS-Z | Composable Performance Objects (SchedContext, CBS, MCS) | v0.23.0–v0.23.22 |
| WS-AA | Rust ABI Type Synchronization | v0.23.22 |
| **WS-AB** | **Deferred Operations & Liveness Completion** | **v0.24.0–v0.24.5** |
 
---
 
## 15. Relationship to WS-V Starvation Prevention Plan
 
The file `docs/planning/WS_V_KERNEL_STARVATION_PREVENTION_PLAN.md` is retained
as historical context. WS-AB supersedes it with the following mapping:
 
| WS-V Phase | WS-AB Disposition | Notes |
|------------|-------------------|-------|
| V1 (Bounded Latency Theorem, 15 tasks) | **→ D5** (16 tasks, updated) | Updated for CBS budget model, effective priority with pipBoost, replenishment periods |
| V2 (IPC Timeout, 18 tasks) | **→ ABSORBED** (by WS-Z Z6) | Z6 budget-driven timeout resolves SV-3. No dedicated D-phase needed. |
| V3 (Priority Inheritance, 21 tasks) | **→ D4** (20 tasks, updated) | Updated for SchedContext-aware effective priority, pipBoost field design, Z7 donation composition |
| V4 (MCS Scheduling Contexts, 24 tasks) | **→ COMPLETE** (WS-Z Z1–Z10) | Fully implemented. No remaining work. |
 
**Net effect**: WS-V's 78 sub-tasks reduce to 36 in WS-AB (D4: 20 + D5: 16)
plus 54 new sub-tasks for the five deferred operations (D1: 18 + D2: 14 +
D3: 12) and closure (D6: 10), totaling 90 sub-tasks.
 
---
 
## 16. Deferred Items
 
### 16.1 Deferred Starvation Vectors
 
| ID | Vector | Severity | Reason for Deferral |
|----|--------|----------|---------------------|
| SV-4 | Notification LIFO ordering | MEDIUM | seL4 semantic compatibility. Notification LIFO matches seL4's design. Changing to FIFO would break compatibility. Practical impact limited: notification signals typically wake exactly one waiter, and notification-heavy patterns use bounded-badge coalescing. |
 
### 16.2 Deferred Enhancements
 
| Enhancement | Description | Reason for Deferral |
|-------------|-------------|---------------------|
| General per-operation IPC timeout | Independent countdown timers on IPC operations (not tied to SchedContext budget) | Z6 budget-driven timeout already resolves SV-3. Independent timeouts would add complexity with marginal benefit. If needed, can be layered atop Z6 in a future workstream. |
| Priority aging / decay | Gradually boost starved threads' effective priority | Violates strict priority ordering, incompatible with hard real-time. CBS budgets (Z2) provide a better mechanism. |
| Priority ceiling protocol (PCP) | Alternative to PIP preventing deadlock by ceiling-setting | PIP (D4) is sufficient given `tcbQueueChainAcyclic`. PCP adds complexity without clear benefit. |
| Response-time iteration analysis | Tighter WCRT via iterative fixed-point computation | D5's `N × (B + P)` bound is conservative. Tighter analysis deferred to a dedicated real-time analysis workstream built on D5's trace model. |
| Non-interference liveness | Prove information-flow policy does not create liveness-visible side channels | Orthogonal to scheduling liveness. Better addressed in a dedicated security workstream extending NI projection with trace-level properties. |
 
### 16.3 Future Workstream Candidates
 
| Candidate | Scope | Prerequisite |
|-----------|-------|-------------|
| WS-AC: Real-Time Analysis Framework | Formal schedulability analysis (RMA, response-time iteration) on D5 trace model | WS-AB (D5 WCRT theorem) |
| WS-AD: Mixed-Criticality Scheduling | Criticality levels, mode changes, graceful degradation | WS-AB (D4 PIP + D5 WCRT) |
| WS-AE: Hardware Timer Binding | RPi5 ARM Generic Timer → kernel timer tick integration | WS-AB complete + WS-U platform types |
