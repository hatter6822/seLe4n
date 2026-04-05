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
(`docs/dev_history/WS_V_KERNEL_STARVATION_PREVENTION_PLAN.md`, baseline v0.20.7)
identified six starvation vectors (SV-1 through SV-6). WS-Z addressed some of
these through runtime mechanisms (CBS budgets, SchedContext donation, budget-driven
IPC timeout) but two critical formal gaps remain:
 
| Gap | Original Phase | Status | Why It Matters |
|-----|---------------|--------|----------------|
| **No formal WCRT bound** | V1 (Bounded Latency Theorem) | **COMPLETE (D5)** | Resolved by Phase D5: `bounded_scheduling_latency` proves WCRT = D*L_max + N*(B+P). PIP enhancement via `pip_enhanced_wcrt_le_base`. 58 surface anchor tests. Zero sorry/axiom. |
| **No transitive priority inheritance** | V3 (Priority Inheritance Protocol) | **COMPLETE (D4)** | Resolved by Phase D4: transitive PIP via blocking graph, `propagatePriorityInheritance`/`revertPriorityInheritance` chain walk, 16 frame preservation theorems, `pip_bounded_inversion`. Zero sorry/axiom. |
 
### 1.3 Audit of WS-V Starvation Prevention Plan
 
The WS-V plan (78 sub-tasks across 4 phases) was written at v0.20.7. The codebase
is now at v0.23.22. Here is the disposition of each phase:
 
| WS-V Phase | Planned Scope | Actual Disposition | Remaining Work |
|------------|--------------|-------------------|----------------|
| **V1** (15 sub-tasks) | Bounded Latency Theorem — proof-only trace model, WCRT bound | **COMPLETE as D5** (v0.25.0). `Scheduler/Liveness/` directory with 7 files + re-export hub. Trace model, CBS-aware WCRT bound, PIP enhancement. 58 surface anchor tests. Zero sorry/axiom. | **No remaining work.** |
| **V2** (18 sub-tasks) | IPC Timeout Mechanism — per-tick countdown on IPC blocking states | **PARTIALLY IMPLEMENTED as Z6**. Budget-driven timeout via `timeoutBudget : Option SchedContextId` on TCB + `timeoutThread`/`timeoutBlockedThreads` in `timerTickBudget`. Achieves SV-3 (bounded IPC blocking) but through budget exhaustion, not independent countdown timers. | **Substantially complete.** Z6 solves the core problem. Optional per-operation timeouts (independent of SchedContext) would be a refinement, not critical. **Absorbed — no dedicated phase needed.** |
| **V3** (21 sub-tasks) | Priority Inheritance Protocol — blocking graph, transitive propagation, bounded inversion proofs | **COMPLETE as D4** (v0.25.0). Blocking graph (`blockedOnThread`, `waitersOf`, `blockingChain`), acyclicity invariant, depth bound, `propagatePriorityInheritance`/`revertPriorityInheritance` chain walk, 16 frame preservation theorems, `pip_bounded_inversion`, Call/Reply/Suspend/Timeout integration. Zero sorry/axiom. | **No remaining work.** |
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
 
## 4. Phase D1 — Thread Suspension & Resumption (v0.24.0) — COMPLETE
 
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

### 4.1 Detailed Task Decomposition

The following breaks down each Medium-complexity D1 task into atomic
implementation steps. Each step is independently verifiable via
`lake build SeLe4n.Kernel.Lifecycle.Suspend`.

**D1-C: `cancelIpcBlocking` — Per-IPC-State Handlers (6 steps)**

| Step | Scope | Key Operation | Verifiable Output |
|------|-------|---------------|-------------------|
| D1-C1 | Handle `.ready` state | Guard: if `ipcState = .ready`, return state unchanged (no-op) | Pattern match compiles; trivial base case |
| D1-C2 | Handle `.blockedOnSend epId` | Call `endpointQueueRemove st epId tid` on send queue (DualQueue/Core.lean:461); patches predecessor `queueNext` and successor `queuePrev`; clears `queuePrev`/`queuePPrev`/`queueNext` on removed thread; reset `ipcState := .ready` | Reuse Z6-B removal; verify send queue head/tail updated |
| D1-C3 | Handle `.blockedOnReceive epId` | Mirror D1-C2 for receive queue; call `endpointQueueRemove` on recv side; reset `ipcState := .ready` | Symmetric to D1-C2; validate recv queue consistency |
| D1-C4 | Handle `.blockedOnCall epId` | Call `endpointQueueRemove` on send queue (Call uses send queue semantics); clear `pendingMessage := none`; reset `ipcState := .ready` | Also clear reply tracking to prevent stale Reply |
| D1-C5 | Handle `.blockedOnReply epId replyTarget` | **No queue removal** — reply-waiting threads are NOT in endpoint queues (they wait for a specific server Reply, not queued in endpoint). Clear `replyTarget`; reset `ipcState := .ready` | Verify zero queue mutation; only TCB field update |
| D1-C6 | Handle `.blockedOnNotification notifId` | Look up notification object; filter `tid` from `notif.waitList` (simple `List.filter`); store updated notification; reset `ipcState := .ready` | Notification wait list is `List ThreadId`; filter preserves ordering of remaining waiters |

*Implementation order*: D1-C1 first (trivial base case validates function
signature and return type), then D1-C2 through D1-C6 in any order (independent
match arms). Compose all cases into the final `match tcb.ipcState` expression
last. Each step compiles independently as a standalone helper function before
integration.

**D1-D: `cancelDonation` — Per-Binding-State Handlers (3 steps)**

| Step | Scope | Key Operation |
|------|-------|---------------|
| D1-D1 | Handle `.unbound` | No-op — thread has no SchedContext to clean up. Return state unchanged. |
| D1-D2 | Handle `.bound scId` | Unbind: set `sc.boundThread := none` on the SchedContext object; clear `tcb.schedContextBinding := .unbound`. If thread was in replenishment queue, leave it (replenishment queue cleanup is handled by SchedContext lifecycle, not suspend). |
| D1-D3 | Handle `.donated scId originalOwner` | Call `cleanupDonatedSchedContext` (Donation.lean Z7-D pattern): return SchedContext to `originalOwner` by setting `ownerTcb.schedContextBinding := .bound scId`; set `sc.boundThread := some originalOwner`; clear suspended thread's binding to `.unbound`. |

*Key invariant*: After D1-D completes, the suspended thread's
`schedContextBinding = .unbound`. The SchedContext (if any) is consistently
owned by exactly one thread (`schedContextNotDualBound` preserved).

**D1-G: `suspendThread` Composite — Sequential Pipeline (7 steps)**

| Step | Operation | Input | Output | Failure Mode |
|------|-----------|-------|--------|-------------|
| D1-G1 | TCB lookup + state validation | `SystemState × ThreadId` | `TCB` or error | `.invalidArgument` if ObjId not found or not a TCB; `.invalidState` if `threadState = .Inactive` |
| D1-G2 | `cancelIpcBlocking` (D1-C) | State after G1 | IPC queues cleaned | Infallible — all 6 IPC states handled exhaustively |
| D1-G3 | `cancelDonation` (D1-D) | State after G2 | SchedContext bindings cleaned | Infallible — all 3 binding states handled |
| D1-G4 | `removeFromRunQueue` (D1-E) | State after G3 | Run queue updated | Infallible — no-op if thread not in queue |
| D1-G5 | `clearPendingState` (D1-F) | State after G4 | TCB fields zeroed | Infallible — pure field clear |
| D1-G6 | Set `threadState := .Inactive` | State after G5 | Thread marked inactive | Infallible |
| D1-G7 | Conditional `schedule` | State after G6 | New current thread selected | Only triggers if suspended thread was `scheduler.current`; reuses existing `schedule` (Core.lean) |

*Step ordering rationale*: G2 (IPC cleanup) before G3 (donation cleanup)
ensures no stale IPC references to donated SchedContexts. G4 (run queue
removal) before G6 (state transition) ensures the run queue never contains an
Inactive thread, even transiently. G7 must be last because it reads the final
run queue state to select the next thread.

**D1-H: `resumeThread` — Sequential Pipeline (5 steps)**

| Step | Operation | Validation |
|------|-----------|-----------|
| D1-H1 | TCB lookup | `.invalidArgument` if not found or not a TCB |
| D1-H2 | State validation | `.invalidState` if `threadState ≠ .Inactive` (cannot resume an active/blocked thread) |
| D1-H3 | Set `threadState := .Ready`, `ipcState := .ready` | Clean state for newly runnable thread |
| D1-H4 | `ensureRunnable tid` — insert into run queue at `effectivePriority` | Reuse `ensureRunnable` from SchedulerLemmas.lean; inserts into correct priority bucket via `RunQueue.insert` |
| D1-H5 | Conditional preemption check | If `effectivePriority(resumed) > effectivePriority(current)`, call `schedule` for immediate preemption. Uses `effectivePriority` resolution (Selection.lean:218) |

**D1-J: `cancelIpcBlocking` Preserves `ipcInvariantFull` — Grouped by
Conjunct Category (4 proof groups)**

The 14-conjunct `ipcInvariantFull` (Defs.lean:1075) decomposes into 4 proof
groups by modification relevance:

| Group | Conjuncts (by number) | Strategy | Difficulty |
|-------|----------------------|----------|-----------|
| J-G1: Queue structure (3) | `dualQueueSystemInvariant`, `endpointQueueNoDup`, `queueNextBlockingConsistent` | Reuse `endpointQueueRemove` well-formedness lemma from Z6-B (DualQueue/Core.lean:461). Removal patches `queuePrev`/`queueNext` maintaining doubly-linked invariant. `endpointQueueNoDup`: removed thread exits queue → NoDup preserved. `queueNextBlockingConsistent`: removed thread's links cleared → no dangling `queueNext`. | Low — direct Z6-B lemma reuse |
| J-G2: Blocking consistency (4) | `ipcInvariant` (base), `waitingThreadsPendingMessageNone`, `ipcStateQueueMembershipConsistent`, `queueHeadBlockedConsistent` | Removed thread transitions to `.ready` → blocking predicates vacuously satisfied for `tid`. Other threads unchanged (frame). `ipcStateQueueMembershipConsistent`: removed thread not in queue and not blocked → consistent. `queueHeadBlockedConsistent`: if removed thread was head, new head (if any) was `queueNext` which is still blocked. | Medium — per-thread case split: `tid` vs others |
| J-G3: Notification (2) | `allPendingMessagesBounded`, `badgeWellFormed` | Only the `.blockedOnNotification` case modifies notification object. `allPendingMessagesBounded`: `pendingMessage` cleared → vacuously bounded. `badgeWellFormed`: notification badge field untouched by wait list filter. Remaining 4 IPC states: pure frame (notification objects unchanged). | Low |
| J-G4: Donation & transfer (5) | `blockedThreadTimeoutConsistent`, `donationChainAcyclic`, `donationOwnerValid`, `passiveServerIdle`, `donationBudgetTransfer` | `blockedThreadTimeoutConsistent`: `timeoutBudget` cleared in D1-F → predicate satisfied (no timeout on non-blocked thread). Donation invariants (4 conjuncts from Z7): IPC state change does NOT modify `schedContextBinding` → donation chain frame. `passiveServerIdle`: thread moves to Inactive (not running) → still satisfies idle condition. | Medium — donation frame requires `schedContextBinding` unchanged by IPC cleanup |

*Proof skeleton*: Prove 4 bundle lemmas (`cancelIpc_ipcInv_queueStructure`,
`cancelIpc_ipcInv_blockingConsistency`, `cancelIpc_ipcInv_notification`,
`cancelIpc_ipcInv_donationTransfer`). Compose:
`cancelIpc_preserves_ipcInvariantFull := ⟨g1.1, g1.2, g1.3, g2.1, ..., g4.5⟩`.

**D1-K/L: Scheduler Invariant Preservation — Per-Component Proof Map**

| Component | Bundle | Suspend Modifies? | Proof Approach |
|-----------|--------|-------------------|----------------|
| `queueCurrentConsistent` | Base (K) | Yes — clears current if suspended | If `scheduler.current = some tid`: set `current := none`, restores consistency. Else: frame. Pattern from `timerTick` (Core.lean:362). |
| `runQueueUnique` | Base (K) | Yes — removes from queue | `RunQueue.remove` preserves NoDup (RunQueue.lean:135). Direct import of `remove_preserves_nodup`. |
| `currentThreadValid` | Base (K) | Yes — clears current | `current := none` → trivially valid. If current was different thread: frame (that thread still in queue). |
| `timeSlicePositive` | Base (K) | No | Frame: only suspended thread's TCB modified; other threads' `timeSlice` unchanged. Suspended thread leaves queue → predicate not checked for non-queued threads. |
| `domainTimeRemainingPositive` | Base (K) | No | Frame: domain scheduler state untouched by `suspendThread`. |
| `replenishQueueSorted` | Extended (L) | No | Frame: suspend does NOT modify replenishment queue (it modifies SchedContext *binding*, not *budget/period*). |
| `replenishQueueSizeConsistent` | Extended (L) | No | Frame: same as above. |
| `replenishQueueConsistent` | Extended (L) | No | Frame: replenishment entries reference SchedContextIds, not thread state. |
| `budgetPositive` | Extended (L) | No | Frame: SchedContext `budget.remaining` field unchanged by donation cleanup (D1-D changes binding, not budget). |
| `currentBudgetPositive` | Extended (L) | Conditional | If current cleared → vacuously true (no current thread to check). Else: frame. |
| `effectivePriorityConsistent` | Extended (L) | Yes — thread removed | Suspended thread exits run queue → predicate not checked. Remaining threads: effective priority unchanged (their SchedContexts untouched). |

*Optimization*: D1-L's 6 extended conjuncts are ALL frame proofs. Implement as
a single `suspend_extendedBundle_frame` lemma using backward transport: since
extended fields (replenishment queue, budgets, periods) are unchanged in state,
the extended invariant transfers directly from pre-state to post-state.

**D1-M: Cross-Subsystem Invariant — Per-Predicate Proof Plan**

The 8-predicate `crossSubsystemInvariant` (CrossSubsystem.lean:236)
decomposes by modification:

| Predicate | Modified? | Proof Strategy |
|-----------|-----------|----------------|
| `noStaleEndpointQueueReferences` | Yes | Thread removed from queues → no stale ref from `tid`. Other threads: frame (their queue links untouched). |
| `noStaleNotificationWaitReferences` | Yes | Thread filtered from wait lists → no stale ref. Others: frame. |
| `schedContextStoreConsistent` | Yes | After D1-D cleanup: binding cleared → no stale SchedContext reference. SchedContext object updated to reflect unbind. |
| `schedContextNotDualBound` | Yes | Cleared binding cannot be dual-bound. Donation return (D1-D3) restores single-owner. Others: frame. |
| `schedContextRunQueueConsistent` | Yes | Thread removed from run queue → predicate vacuously satisfied for `tid`. Others: frame (their SchedContexts unchanged). |
| `registryEndpointValid` | No | Pure frame — suspend doesn't touch service registry. |
| `registryDependencyConsistent` | No | Pure frame. |
| `serviceGraphInvariant` | No | Pure frame. |

*Optimization*: Group the 5 modified predicates into
`suspend_crossSubsystem_modified`, the 3 frame predicates into
`suspend_crossSubsystem_frame`. Compose:
`suspend_preserves_crossSubsystemInvariant := ⟨mod.1, ..., mod.5, frame.1, frame.2, frame.3⟩`.

### 4.2 Verification Checkpoints

| Checkpoint | After Tasks | Validation Command | What It Proves |
|-----------|-------------|-------------------|---------------|
| CP-D1a | D1-A, D1-B | `lake build SeLe4n.Model.Object.Types && lake build SeLe4n.Kernel.Architecture.SyscallArgDecode` | Type foundation compiles; all exhaustive matches updated |
| CP-D1b | D1-C through D1-F | `lake build SeLe4n.Kernel.Lifecycle.Suspend` | All helper functions compile; no `sorry` |
| CP-D1c | D1-G, D1-H | `lake build SeLe4n.Kernel.Lifecycle.Suspend` | Composite operations compile and compose correctly |
| CP-D1d | D1-I through D1-N | `lake build SeLe4n.Kernel.Lifecycle.Invariant.SuspendPreservation` | All preservation proofs compile without `sorry` |
| CP-D1e | D1-O, D1-P | `lake build SeLe4n.Kernel.API && lake build SeLe4n.Kernel.FrozenOps.Operations` | API dispatch and frozen ops compile |
| CP-D1f | D1-Q | `./scripts/test_smoke.sh` | All tests pass including new SuspendResumeSuite |

---

## 5. Phase D2 — Priority Management (v0.24.1) ✅ COMPLETE
 
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

### 5.1 Detailed Task Decomposition

**D2-E: `setPriorityOp` — Branching Pipeline (5 steps)**

| Step | Operation | Branch Condition | Key Detail |
|------|-----------|-----------------|-----------|
| D2-E1 | Caller TCB lookup + MCP authority check | — | Call `validatePriorityAuthority` (D2-D): `newPriority.toNat ≤ callerTcb.maxControlledPriority.toNat`. Fail with `.rangeError` on violation. |
| D2-E2 | Target TCB lookup | — | Look up target thread. If `callerTid = targetTid`, self-modification is allowed (seL4 permits setting own priority within MCP). |
| D2-E3 | Determine priority update path | `tcb.schedContextBinding` | If `.bound scId` or `.donated scId _`: update `SchedContext.priority` (the SchedContext owns the scheduling priority). If `.unbound`: update `TCB.priority` directly (legacy path for unbound threads). |
| D2-E4 | Run queue bucket migration | Thread in run queue? | If target `tid ∈ runQueue.membership`: call `RunQueue.remove` (RunQueue.lean:135), then `RunQueue.insert` at new priority. This is O(k+n) removal + O(k'+n) insertion. If not in queue (blocked/inactive): skip migration. |
| D2-E5 | Conditional preemption check | Priority decreased + is current? | If target is `scheduler.current` AND new priority < old priority: call `schedule` to check if a higher-priority thread should preempt. If priority increased: no preemption needed (current thread is now higher). |

*Edge case*: If target has `.donated scId originalOwner`, modifying the
SchedContext priority affects BOTH the target (current user) and the original
owner (who will reclaim it on Reply). This is correct seL4 behavior: the
SchedContext is a shared resource, and priority changes apply to the object.

**D2-F: `setMCPriorityOp` — MCP Authority Chain (4 steps)**

| Step | Operation | Key Detail |
|------|-----------|-----------|
| D2-F1 | Caller MCP authority validation | `newMCP.toNat ≤ callerTcb.maxControlledPriority.toNat` — caller cannot grant higher MCP than it possesses. This ensures monotonic authority reduction. |
| D2-F2 | Target TCB lookup + MCP update | Set `targetTcb.maxControlledPriority := newMCP`. Pure field update. |
| D2-F3 | Priority capping (conditional) | If `targetTcb.priority > newMCP`: reduce priority to MCP ceiling. `targetTcb.priority := newMCP`. This prevents a thread from holding a priority above its new MCP. seL4 behavior: reducing MCP retroactively caps existing priority. |
| D2-F4 | Run queue migration (conditional) | If priority was capped in D2-F3 AND thread is in run queue: perform remove-then-insert bucket migration (same as D2-E4). If priority was capped AND thread is current: trigger `schedule` for preemption check. |

*Security property*: After D2-F completes,
`targetTcb'.priority ≤ targetTcb'.maxControlledPriority` (invariant). This
follows from D2-F3: if priority was already ≤ newMCP, it remains so; if it
was >, it's capped to newMCP.

**D2-G: `setPriorityOp` Preserves Scheduler Invariants — Decomposed Proof
Strategy (5 component lemmas)**

| Lemma | Invariant Component | Proof |
|-------|-------------------|-------|
| `setPrio_queueCurrentConsistent` | `queueCurrentConsistent` | Remove-then-insert: thread leaves queue, then re-enters at new bucket. `current` unchanged (we don't modify `scheduler.current` except in preemption path). If preemption triggers `schedule`, reuse existing `schedule` preservation. |
| `setPrio_runQueueUnique` | `runQueueUnique` | `remove_preserves_nodup` (removes from membership set + priority bucket), then `insert_preserves_nodup` (fresh insert after removal guarantees no duplicate). Compose: `NoDup (remove ∘ insert)`. |
| `setPrio_timeSlicePositive` | `timeSlicePositive` | Frame: `timeSlice` field untouched by priority change. |
| `setPrio_budgetPositive` | `budgetPositive` (extended) | If SchedContext priority changed: budget/period fields are distinct from priority field → frame. If TCB priority changed: SchedContext untouched → frame. |
| `setPrio_priorityMatch` | `effectivePriorityConsistent` | After bucket migration, thread is in the bucket matching its new `effectivePriority`. Prove: `RunQueue.insert` places thread in `byPriority[newPrio]`, and `effectivePriority` resolves to `newPrio` after the priority update. |

**D2-J: Authority Non-Escalation — Two Key Theorems**

| Theorem | Statement | Proof Sketch |
|---------|-----------|-------------|
| `setPriority_authority_bounded` | `∀ st st' callerTid targetTid newPrio, setPriorityOp st callerTid targetTid newPrio = .ok st' → targetPriority st' targetTid ≤ callerMCP st callerTid` | Direct from D2-E1 validation: `newPriority ≤ caller.maxControlledPriority` is checked before any state modification. If check fails, operation returns error. If succeeds, `targetPriority` after update = `newPriority ≤ caller.mcp`. |
| `setMCPriority_authority_bounded` | `∀ st st' callerTid targetTid newMCP, setMCPriorityOp st callerTid targetTid newMCP = .ok st' → targetMCP st' targetTid ≤ callerMCP st callerTid` | Direct from D2-F1 validation: `newMCP ≤ caller.maxControlledPriority`. These two theorems together prove the authority hierarchy is monotonically non-increasing: no thread can create a more-privileged thread than itself. |

### 5.2 Verification Checkpoints

| Checkpoint | After Tasks | Validation Command |
|-----------|-------------|-------------------|
| CP-D2a | D2-A, D2-B, D2-C | `lake build SeLe4n.Model.Object.Types && lake build SeLe4n.Kernel.Architecture.SyscallArgDecode` |
| CP-D2b | D2-D, D2-E, D2-F | `lake build SeLe4n.Kernel.SchedContext.PriorityManagement` |
| CP-D2c | D2-G through D2-J | `lake build SeLe4n.Kernel.SchedContext.Invariant.PriorityPreservation` |
| CP-D2d | D2-K, D2-L | `lake build SeLe4n.Kernel.API && lake build SeLe4n.Kernel.FrozenOps.Operations` |
| CP-D2e | D2-M | `./scripts/test_smoke.sh` |

---

## 6. Phase D3 — IPC Buffer Configuration (v0.24.2) — COMPLETE
 
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

### 6.1 Detailed Task Decomposition

D3 is the lowest-complexity phase (most tasks are Small/Trivial). The following
expands the two tasks that benefit from further granularity.

**D3-D: `validateIpcBufferAddress` — 5-Step Validation Pipeline**

| Step | Check | Error on Failure | seL4 Equivalent |
|------|-------|-----------------|-----------------|
| D3-D1 | Alignment: `addr.toNat % ipcBufferAlignment = 0` | `.alignmentError` | `seL4_AlignmentError` — IPC buffer must be 512-byte aligned (2^9, matching `seL4_IPCBufferSizeBits`) |
| D3-D2 | Physical bound: `addr.toNat < physicalAddressBound` | `.invalidArgument` | Prevents addresses that exceed ARM64 LPA physical address space (Architecture/Assumptions.lean) |
| D3-D3 | VSpace root validity: look up `tcb.vspaceRoot`, confirm it resolves to a `VSpaceRoot` object | `.invalidArgument` | Thread must have a valid VSpace assigned |
| D3-D4 | Mapping check: call `vspaceLookupFull asid addr` (VSpace.lean:126) — verify address is mapped | `.vmFault` | Address must be present in the thread's page table; unmapped addresses would cause kernel fault on IPC |
| D3-D5 | Write permission: check `permissions.write = true` from the `PagePermissions` returned by D3-D4 | `.vmFault` | IPC buffer is written by kernel during message delivery; read-only pages are insufficient. No W^X conflict since IPC buffers are data pages, not executable. |

*Dependency on D3-K*: Step D3-D4 requires `vspaceLookupFull` (VSpace.lean:126).
The codebase already provides this function. D3-K is therefore a **pre-check**
rather than an implementation task: verify the function signature matches
expectations, then proceed directly to D3-D.

**D3-F: Frame Preservation — Single Theorem with Per-Invariant Justification**

The `setIPCBufferOp` modifies exactly ONE TCB field: `tcb.ipcBuffer : VAddr`.
This field is not referenced by any invariant predicate in the entire kernel
proof surface:

| Invariant Bundle | References `ipcBuffer`? | Proof |
|-----------------|------------------------|-------|
| `schedulerInvariantBundleExtended` (15-tuple) | No — scheduler predicates reference `priority`, `domain`, `timeSlice`, `budget`, run queue membership | Backward transport: `∀ p ∈ schedulerPredicates, p st = p st'` because modified fields are disjoint |
| `ipcInvariantFull` (14 conjuncts) | No — IPC predicates reference `ipcState`, queue linkage (`queuePrev`/`queueNext`), `pendingMessage`, `schedContextBinding` | Same disjoint-field argument |
| `crossSubsystemInvariant` (8 predicates) | No — cross-subsystem predicates reference `schedContextBinding`, queue membership, service registry | Same argument |
| `capabilityInvariant` | No — capability predicates reference CNode slots, CDT | Same argument |

*Implementation*: A single theorem `setIPCBuffer_preserves_proofLayerInvariantBundle`
with proof body: `⟨sched_frame, ipc_frame, cross_frame, cap_frame⟩` where each
component is a 1-line backward transport citing field disjointness. This is the
simplest preservation proof in the entire workstream.

### 6.2 Verification Checkpoints

| Checkpoint | After Tasks | Validation Command |
|-----------|-------------|-------------------|
| CP-D3a | D3-A, D3-B, D3-C | `lake build SeLe4n.Model.Object.Types && lake build SeLe4n.Kernel.Architecture.SyscallArgDecode` |
| CP-D3b | D3-K (pre-check), D3-D, D3-E | `lake build SeLe4n.Kernel.Architecture.IpcBufferValidation` |
| CP-D3c | D3-F, D3-G | Preservation proofs compile: `lake build SeLe4n.Kernel.Architecture.IpcBufferValidation` |
| CP-D3d | D3-H, D3-I | `lake build SeLe4n.Kernel.API && lake build SeLe4n.Kernel.FrozenOps.Operations` |
| CP-D3e | D3-J | `./scripts/test_smoke.sh` |

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

### 7.1 Detailed Task Decomposition

D4 is the most complex phase in WS-AB. The following decomposes each Medium
task into atomic, independently verifiable steps grounded in the actual
codebase structures.

**D4-C: Blocking Graph Definition — 3 Independent Definitions + 2 Helpers**

| Step | Definition | Signature | Key Detail |
|------|-----------|-----------|-----------|
| D4-C1 | `blockedOnThread` (predicate) | `(st : SystemState) (waiter server : ThreadId) : Prop` | True when `waiter` has `ipcState = .blockedOnReply epId (some server)` (direct blocking) OR `ipcState = .blockedOnCall epId` where the endpoint's receive-side head is `server`. The first case is the primary PIP path (Call → Reply pattern). |
| D4-C2 | `waitersOf` (direct dependents) | `(st : SystemState) (tid : ThreadId) : List ThreadId` | Collects all `waiter` where `blockedOnThread st waiter tid`. Implementation: fold over all TCB objects, filter by `blockedOnThread`. O(n) in thread count — acceptable because PIP propagation happens on the Call path, not the hot scheduler path. |
| D4-C3 | `blockingChain` (transitive closure) | `(st : SystemState) (tid : ThreadId) (fuel : Nat := st.objects.size) : List ThreadId` | Walks upward: start at `tid`, if `tid` has `ipcState = .blockedOnReply _ (some server)`, prepend `server` and recurse on `server` with `fuel - 1`. Terminate when `fuel = 0` or thread is not in `blockedOnReply` state. Returns the list of servers in the transitive blocking chain. |
| D4-C4 | `chainContains` (helper) | `(chain : List ThreadId) (tid : ThreadId) : Bool` | Simple `List.elem`. Used in acyclicity proof to check whether a thread appears twice. |
| D4-C5 | `blockingGraphEdges` (helper) | `(st : SystemState) : List (ThreadId × ThreadId)` | All `(waiter, server)` pairs where `blockedOnThread st waiter server`. Used in visualization/testing, not in proofs. |

*Design note*: `blockingChain` uses fuel (not well-founded recursion on a
decreasing measure) because the chain walks through *arbitrary* thread IDs,
not structurally decreasing data. The acyclicity proof (D4-D) establishes
that fuel = `countTCBs st` is always sufficient.

**D4-D: Blocking Graph Acyclicity — 3-Step Proof Structure**

| Step | Lemma | Proof Technique |
|------|-------|----------------|
| D4-D1 | `blockedOnReply_not_self` | A thread cannot have `ipcState = .blockedOnReply epId (some tid)` where `tid` is itself. Follows from `tcbQueueChainAcyclic` (IPC/Invariant/Defs.lean:145): no self-loops in IPC queue chains. This is the base case preventing trivial cycles. |
| D4-D2 | `blockingChain_no_repeat` | No thread appears twice in its blocking chain. Proof by strong induction on the unvisited thread set: each `blockingChain` step follows `blockedOnReply` to a new server; by D4-D1, each server is distinct from the waiter; by the induction hypothesis, the remaining chain has no repeats; therefore the full chain has no repeats. Well-founded on `Finset.card (unvisited)` strictly decreasing. |
| D4-D3 | `blockingChain_acyclic` | Corollary of D4-D2: if no thread appears twice, the chain cannot form a cycle. Formally: `∀ tid, tid ∉ (blockingChain st tid).tail` (the starting thread does not appear later in its own chain). |

**D4-G: `updatePipBoost` — Single-Thread Priority Update (4 steps)**

| Step | Operation | Detail |
|------|-----------|--------|
| D4-G1 | Compute max waiter priority | Call `computeMaxWaiterPriority st tid` (D4-F). Returns `Option Priority`: `some p` if thread has waiters, `none` if no one is blocked on this thread. |
| D4-G2 | Determine new `pipBoost` | If `some p` and `p > basePriority(tid)`: set `pipBoost := some p`. If `some p` and `p ≤ basePriority(tid)`: clear `pipBoost := none` (base priority already sufficient). If `none`: clear `pipBoost := none`. |
| D4-G3 | TCB update | Store updated TCB with new `pipBoost` value via `storeTcb`. |
| D4-G4 | Conditional run queue migration | If thread is in run queue AND `effectivePriority` changed (because `pipBoost` changed the `max(scPrio, pipBoost)` result): perform `RunQueue.remove` then `RunQueue.insert` at new effective priority. Reuses the D2-E4 bucket migration pattern. If thread is not in run queue (blocked/inactive): skip. |

*Invariant*: After D4-G, `tcb.pipBoost = computeMaxWaiterPriority st tid` for
the updated thread. This is the single-thread correctness property that D4-J
composes across the chain.

**D4-H: `propagatePriorityInheritance` — Chain Walk Algorithm (4 steps)**

| Step | Operation | Termination Argument |
|------|-----------|---------------------|
| D4-H1 | Apply `updatePipBoost st startTid` | Base step: update the directly-involved server. |
| D4-H2 | Check continuation condition | If `startTid` has `ipcState = .blockedOnReply _ (some nextServer)`: the server is itself blocked on another server. Propagation must continue upward. If not blocked: propagation terminates here. |
| D4-H3 | Recurse: `propagatePriorityInheritance st' nextServer (fuel - 1)` | `st'` is the state after D4-H1's update. `fuel` decreases by 1 each step. By D4-D (acyclicity) and D4-E (depth bound), `fuel = countTCBs st` is always sufficient. |
| D4-H4 | Fuel exhaustion guard | If `fuel = 0`: terminate. This is a defensive guard that should never trigger if the chain is acyclic. In practice, chains of depth > 4–5 are extremely rare. |

*Composition with Z7 donation*: When `propagatePriorityInheritance` walks
through a server that has `schedContextBinding = .donated scId originalOwner`,
the `effectivePriority` resolution already incorporates the donated
SchedContext's priority. The `pipBoost` provides an ADDITIONAL boost if the
transitive client priority exceeds the donated SchedContext priority. The
`max(scPrio, pipBoost)` computation in `effectivePriority` (D4-B) handles
this composition automatically.

**D4-I: `revertPriorityInheritance` — Chain Reversion (4 steps)**

| Step | Operation | Key Difference from D4-H |
|------|-----------|-------------------------|
| D4-I1 | Recompute `pipBoost` for `tid` | After a client is unblocked (Reply completes), `waitersOf st tid` has one fewer entry. `updatePipBoost` recomputes from remaining waiters. If no waiters remain, `pipBoost := none`. |
| D4-I2 | Check continuation condition | If `tid` has `ipcState = .blockedOnReply _ (some nextServer)`: reversion must propagate upward because `nextServer`'s max waiter priority may have changed (one of its transitive waiters became unblocked). |
| D4-I3 | Recurse: `revertPriorityInheritance st' nextServer (fuel - 1)` | Each step recomputes `pipBoost` for a server whose transitive waiters changed. |
| D4-I4 | Fuel exhaustion guard | Same as D4-H4. |

*Key insight*: Reversion is structurally identical to propagation (same chain
walk, same `updatePipBoost` at each step). The difference is purely in the
`waitersOf` computation: during propagation, a new waiter was added; during
reversion, a waiter was removed. The `updatePipBoost` function handles both
cases uniformly because it always recomputes from the current `waitersOf`.

**D4-L: Call Path Integration — 3 Steps**

| Step | Location | Modification |
|------|----------|-------------|
| D4-L1 | After `endpointCallWithDonation` blocks the client | Insert: `let serverId := <resolved from endpoint receive queue head>`. The server is the thread that will handle the client's request. |
| D4-L2 | After client enters `blockedOnReply` state | Insert: `let st' ← propagatePriorityInheritance st serverId`. The propagation walks upward from the server, boosting any servers in the server's own blocking chain. |
| D4-L3 | Return updated state | The state after propagation includes updated `pipBoost` values for all servers on the transitive chain. The Call operation's return state is `st'`. |

*Handshake vs. blocking path*: In the handshake path (server was already
waiting in receive queue), the server is immediately dequeued and runs. PIP
propagation still applies because the server may itself be blocked on another
server via a nested Call. In the blocking path (client blocked, no server
available), PIP propagation defers until a server arrives — handled by the
receive-side endpoint wakeup path (not modified here).

**D4-M: Reply Path Integration — 3 Steps**

| Step | Location | Modification |
|------|----------|-------------|
| D4-M1 | After `endpointReplyWithDonation` unblocks the client | The client transitions from `blockedOnReply` to `Ready`. The client is no longer a waiter of the replying server. |
| D4-M2 | After client unblock | Insert: `let st' ← revertPriorityInheritance st replyingServerId`. The reversion recomputes the server's `pipBoost` based on remaining waiters. If no clients remain blocked on this server, `pipBoost` clears to `none`. |
| D4-M3 | Run queue adjustment | If the server's effective priority decreased (because `pipBoost` was cleared or reduced), and the server is in the run queue, the bucket migration in `updatePipBoost` (D4-G4) handles repositioning automatically. |

**D4-O: Scheduler Preservation — Chain Induction Strategy**

The proof that `propagatePriorityInheritance` preserves
`schedulerInvariantBundleExtended` requires induction over the blocking chain:

| Induction Step | What to Prove | Key Lemma |
|---------------|---------------|-----------|
| Base case | `updatePipBoost st tid` preserves the 15-tuple for a single thread | `updatePipBoost_preserves_schedulerInv`: decompose into (1) `pipBoost` field change preserves time-slice/budget/domain invariants (frame on non-priority fields); (2) conditional bucket migration preserves queue consistency (reuse D2-G `setPrio_runQueueUnique` pattern). |
| Inductive step | If `propagatePIP st tid (fuel+1)` preserves invariants and applies `updatePipBoost` then recurses, the recursion preserves invariants | `propagatePIP_step_preserves`: compose base case preservation with inductive hypothesis. The inductive state satisfies the invariant (by IH), and the next `updatePipBoost` preserves it (by base case). |
| Composition | `propagatePriorityInheritance st startTid fuel` preserves invariants | `Nat.rec` on `fuel` with base case (fuel=0, no-op) and step case (base + IH). |

**D4-Q: Bounded Inversion — Layered Proof (3 lemmas)**

| Lemma | Statement | Depends On |
|-------|-----------|-----------|
| `pip_single_link_bound` | If thread H is blocked on server S, and S has `effectivePriority ≥ effectivePriority(H)` (from PIP), then S completes within `WCRT(effectivePriority(H))` ticks. | D5-L (parametric) or assumed as hypothesis if D5 not yet complete |
| `pip_chain_composition` | If blocking chain has depth D, total inversion time ≤ `D × WCRT(effectivePriority(H))`. | D4-E (depth bound) + `pip_single_link_bound` (per-link). Proof by induction on D: each link adds at most one WCRT interval. |
| `pip_bounded_inversion` | Final theorem: priority inversion for thread H is bounded by `countTCBs(st) × WCRT(effectivePriority(H))`. | D4-E (`blockingChain_bounded` ≤ `countTCBs`) + `pip_chain_composition`. Conservative bound using max possible chain depth. |

*Parametric design*: `pip_single_link_bound` takes `WCRT` as a parameter
(not computed). This allows D4-Q to be proven before D5 is complete. When D5
delivers `bounded_scheduling_latency`, the concrete WCRT is substituted via
`pip_bounded_inversion.instantiate`.

### 7.2 Sub-Phase Decomposition for Schedule Risk Mitigation

D4's 20 tasks can be split into 4 independently deliverable sub-phases:

| Sub-Phase | Tasks | Deliverable | Can Ship Independently? |
|-----------|-------|-------------|------------------------|
| D4a: Types & Graph | D4-A, D4-B, D4-C, D4-D, D4-E | `pipBoost` field, updated `effectivePriority`, blocking graph with acyclicity/depth proofs | Yes — no runtime behavior change (field defaults to `none`, `effectivePriority` returns same value when `pipBoost = none`) |
| D4b: Propagation | D4-F, D4-G, D4-H, D4-I, D4-J, D4-K | `propagatePriorityInheritance`, `revertPriorityInheritance` with correctness proofs | Yes — functions exist but are not called yet |
| D4c: Integration | D4-L, D4-M, D4-N | PIP hooks in Call/Reply/Suspend paths | No — requires D4a + D4b; activates runtime behavior |
| D4d: Proofs & Tests | D4-O, D4-P, D4-Q, D4-R, D4-S, D4-T | Preservation theorems, bounded inversion, tests, docs | No — requires D4c for integration proofs |

*Risk mitigation*: If D4 takes longer than expected, D4a and D4b can be
delivered as intermediate versions. D4a alone is valuable because it adds the
`pipBoost` TCB field and proves the blocking graph properties that D5 can
reference parametrically.

### 7.3 Verification Checkpoints

| Checkpoint | After Tasks | Validation Command |
|-----------|-------------|-------------------|
| CP-D4a | D4-A, D4-B | `lake build SeLe4n.Model.Object.Types && lake build SeLe4n.Kernel.Scheduler.Operations.Selection` |
| CP-D4b | D4-C, D4-D, D4-E | `lake build SeLe4n.Kernel.Scheduler.PriorityInheritance.BlockingGraph` |
| CP-D4c | D4-F, D4-G | `lake build SeLe4n.Kernel.Scheduler.PriorityInheritance.Compute && lake build SeLe4n.Kernel.Scheduler.PriorityInheritance.Propagate` |
| CP-D4d | D4-H, D4-I, D4-J, D4-K | `lake build SeLe4n.Kernel.Scheduler.PriorityInheritance.Propagate` |
| CP-D4e | D4-L, D4-M, D4-N | `lake build SeLe4n.Kernel.IPC.Operations.Donation && lake build SeLe4n.Kernel.Lifecycle.Suspend` |
| CP-D4f | D4-O, D4-P | `lake build SeLe4n.Kernel.Scheduler.PriorityInheritance.Preservation` |
| CP-D4g | D4-Q, D4-R | `lake build SeLe4n.Kernel.Scheduler.PriorityInheritance.BoundedInversion` |
| CP-D4h | D4-S, D4-T | `./scripts/test_full.sh` |

---

## 8. Phase D5 — Bounded Latency Theorem (v0.25.0) — COMPLETE
 
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

### 8.1 Detailed Task Decomposition

D5 is proof-only (zero code changes to existing kernel files). Every task
produces Lean `theorem` or `def` declarations in a new `Scheduler/Liveness/`
module. The following decomposes the most complex proof tasks.

**D5-A: Trace Model Types — 4 Independent Definitions**

| Step | Definition | Type | Key Detail |
|------|-----------|------|-----------|
| D5-A1 | `SchedulerStep` inductive | 9 constructors | `timerTick`, `timerTickBudget`, `schedule`, `scheduleEffective`, `handleYield`, `handleYieldWithBudget`, `switchDomain`, `processReplenishmentsDue`, `ipcTimeoutTick`. Each constructor carries the precondition parameters needed to invoke the corresponding kernel function. |
| D5-A2 | `SchedulerTrace` type alias | `List (SchedulerStep × SystemState)` | A trace is a sequence of (step, resulting-state) pairs. The first element's state is the initial state; each subsequent state is the result of applying the step to the previous state. |
| D5-A3 | `stepPrecondition` function | `SchedulerStep → SystemState → Prop` | Maps each step to its precondition: e.g., `timerTickBudget` requires `scheduler.current = some tid ∧ tcb.schedContextBinding ≠ .unbound`. Extracted from the `if` guards in each kernel function (Core.lean). |
| D5-A4 | `validTrace` predicate | `SchedulerTrace → Prop` | Inductively: empty trace is valid; `step :: rest` is valid if `stepPrecondition step state` holds AND applying the step to `state` produces `nextState` AND `validTrace rest` with `nextState` as initial state. This is the fundamental well-formedness property of scheduler execution sequences. |

**D5-B: Trace Query Predicates — 3 Definitions + 2 Proofs**

| Step | Item | Type | Detail |
|------|------|------|--------|
| D5-B1 | `selectedAt` | `SchedulerTrace → Nat → ThreadId → Prop` | Thread `tid` is `scheduler.current` at trace index `k`. Defined as: `(trace.get? k).map (·.2.scheduler.current) = some (some tid)`. |
| D5-B2 | `runnableAt` | `SchedulerTrace → Nat → ThreadId → Prop` | Thread is in run queue at index `k`: `tid ∈ (trace.get? k).map (·.2.scheduler.runQueue.membership)`. |
| D5-B3 | `budgetAvailableAt` | `SchedulerTrace → Nat → ThreadId → Prop` | Thread's bound SchedContext has `hasSufficientBudget`: requires resolving `tcb.schedContextBinding` to a SchedContext and checking `sc.budget.remaining > 0`. |
| D5-B4 | Proof: `selectedAt_implies_not_runnableAt` | `theorem` | Selected thread is current, not in run queue. Follows from `queueCurrentConsistent` (scheduler invariant): current thread is dequeued before dispatch. |
| D5-B5 | Proof: `selectedAt_implies_budgetAvailableAt` | `theorem` | Selected thread has budget. Follows from `chooseThreadEffective` selection criteria (Selection.lean): threads are only selected if their SchedContext has sufficient budget (Z4 integration). |

**D5-D: Timer-Tick Budget Monotonicity — 2 Theorems from 3 Branches**

`timerTickBudget` (Core.lean:519) has 3 branches (Z4-F). Each branch requires
a separate monotonicity lemma:

| Branch | Condition | Theorem | Proof |
|--------|-----------|---------|-------|
| Z4-F1 (unbound) | `tcb.schedContextBinding = .unbound` | `timerTickBudget_F1_delegates_legacy` | Delegates to `timerTick` which decrements `tcb.timeSlice`. No SchedContext budget involved. |
| Z4-F2 (budget > 1) | `.bound scId` and `sc.budget.remaining > 1` | `timerTickBudget_F2_decrements` | `consumeBudget` (Budget.lean) sets `remaining := remaining - 1`. Prove: `sc'.budget.remaining = sc.budget.remaining - 1`. Direct from `consumeBudget` definition. |
| Z4-F3 (budget ≤ 1) | `.bound scId` and `sc.budget.remaining ≤ 1` | `timerTickBudget_F3_preempts` | Budget exhausted: schedules replenishment entry in `replenishQueue`, re-enqueues thread, calls `schedule`. Prove: thread is no longer current AND replenishment entry added. |

*Composition*: `timerTickBudget_decrements_budget` is the disjunction of F2
(decrement) and F3 (exhaustion). `timerTickBudget_preempts_on_exhaustion` is
specifically F3.

**D5-H: FIFO Progress Within Priority Band — 3-Stage Induction**

| Stage | Lemma | Statement | Proof Technique |
|-------|-------|-----------|-----------------|
| D5-H1 | `fifo_head_selected` (base case, k=0) | Thread at position 0 (head) in priority bucket is selected on next `schedule` call (if no higher-priority thread exists and domain is active) | Direct from `chooseThreadEffective` (Selection.lean): selects highest-priority thread, FIFO within bucket. Head of bucket is first candidate. |
| D5-H2 | `fifo_position_advance` (step lemma) | If thread at position `k > 0` and thread at `k-1` is preempted (by `timerTickBudget` F2/F3) or yields (`handleYieldWithBudget`), position becomes `k-1` | From `handleYieldWithBudget` (Core.lean:656): yielding thread moves to tail. All threads ahead of position `k` shift forward by one. From `timerTickBudget` F3: preempted thread re-enqueued at tail. Same shift. |
| D5-H3 | `fifo_progress_in_band` (composition) | Thread at position `k` selected within `k × max_preemption_interval` ticks | Induction on `k`: base case (k=0) from D5-H1; inductive step: thread at `k` waits for thread at `k-1` to be preempted (within `max_preemption_interval` ticks by D5-D/D5-F), then advances to `k-1` (by D5-H2), then IH applies. `max_preemption_interval` for bound threads: `min(timeSlice, budget) + period` (budget exhaustion + one replenishment wait). For unbound: `timeSlice`. |

**D5-L: Main WCRT Theorem — 3-Lemma Composition**

The main `bounded_scheduling_latency` theorem composes 3 independent bounds:

| Component | Bound | Source Lemma | Contribution to WCRT |
|-----------|-------|-------------|---------------------|
| Domain rotation | `D × L_max` ticks | `domain_rotation_bound` (D5-J) | Time until the target thread's domain becomes active. `D` = number of domain schedule entries, `L_max` = maximum domain time allocation. |
| Priority band exhaustion | Implicit | `higher_band_exhaustion` (D5-I) | Higher-priority threads must either be preempted (budget exhaustion), block (IPC), or yield before the target thread's band is reached. Not a direct tick bound — establishes precondition for FIFO progress. |
| FIFO progress | `N × (B + P)` ticks | `fifo_progress_in_band` (D5-H) | Once domain is active and no higher-effective-priority threads exist, target thread advances through FIFO queue. Each position takes at most `B + P` ticks (budget `B` for current thread + period `P` for replenishment wait). `N` = threads at same or higher effective priority. |

*Theorem statement*:
```
theorem bounded_scheduling_latency
    (hyp : WCRTHypotheses st tid D L_max N B P)
    (trace : SchedulerTrace)
    (hvalid : validTrace trace)
    (hinit : trace.head?.map (·.2) = some st) :
    ∃ k ≤ D * L_max + N * (B + P),
      selectedAt trace k tid
```

*Proof structure*: (1) By `domain_rotation_bound`, ∃ k₁ ≤ D × L_max where
domain `d` is active at trace index k₁. (2) At k₁, apply
`higher_band_exhaustion`: all higher-effective-priority threads in domain `d`
have either consumed their budgets or blocked. (3) Apply `fifo_progress_in_band`:
thread `tid` is selected within N × (B + P) additional ticks. (4) Compose:
`k = k₁ + k₂ ≤ D × L_max + N × (B + P)` via `Nat.add_le_add`.

**D5-K: WCRT Hypotheses — Field-by-Field Specification**

| Hypothesis Field | Type | Meaning |
|-----------------|------|---------|
| `threadRunnable` | `runnableAt trace 0 tid` | Target thread is in run queue at start of analysis |
| `threadHasBudget` | `budgetAvailableAt trace 0 tid` | Thread's SchedContext has positive budget |
| `threadInDomain` | `∃ i, domainSchedule[i] = tid.domain` | Thread's domain appears in the static domain schedule |
| `higherPriorityBound` | `countHigherOrEqualEffectivePriority tid st ≤ N` | At most N threads with effective priority ≥ target's in same domain |
| `maxBudgetBound` | `maxBudgetInBand tid st ≤ B` | All same-or-higher-priority threads have budget ≤ B |
| `maxPeriodBound` | `maxPeriodInBand tid st ≤ P` | All same-or-higher-priority threads have period ≤ P |
| `domainScheduleAdequate` | `domainLength(tid.domain) ≥ N × (B + P)` | Domain allocation is long enough for all threads in band to execute |
| `invariantHolds` | `proofLayerInvariantBundle st` | All kernel invariants hold at analysis start |

*Stability lemma*: `wcrt_hypotheses_stable_under_timerTickBudget` proves that
`WCRTHypotheses` is preserved by `timerTickBudget` steps (budget decrements
don't change the counting predicates, and replenishment restores budget).

### 8.2 Sub-Phase Decomposition for D5

| Sub-Phase | Tasks | Deliverable | Independent? |
|-----------|-------|-------------|-------------|
| D5a: Infrastructure | D5-A, D5-B, D5-C | Trace model types, query predicates, counting functions | Yes — pure definitions with basic properties |
| D5b: Mechanism Bounds | D5-D, D5-E, D5-F, D5-G | Per-mechanism bounds: budget monotonicity, replenishment, time-slice, yield | Yes — each mechanism bound is self-contained |
| D5c: Progress Proofs | D5-H, D5-I, D5-J | FIFO progress, band exhaustion, domain rotation | Requires D5a + D5b |
| D5d: WCRT Composition | D5-K, D5-L, D5-M | Hypotheses, main WCRT theorem, PIP enhancement | Requires D5c |

*Parallelism within D5b*: D5-D/D5-F (timer-tick) and D5-G (yield) are
independent mechanism proofs that can be developed simultaneously. D5-E
(replenishment) depends on D5-D (budget exhaustion triggers replenishment).

### 8.3 Verification Checkpoints

| Checkpoint | After Tasks | Validation Command |
|-----------|-------------|-------------------|
| CP-D5a | D5-A, D5-B, D5-C | `lake build SeLe4n.Kernel.Scheduler.Liveness.TraceModel` |
| CP-D5b | D5-D, D5-F | `lake build SeLe4n.Kernel.Scheduler.Liveness.TimerTick` |
| CP-D5c | D5-E | `lake build SeLe4n.Kernel.Scheduler.Liveness.Replenishment` |
| CP-D5d | D5-G, D5-H | `lake build SeLe4n.Kernel.Scheduler.Liveness.Yield` |
| CP-D5e | D5-I | `lake build SeLe4n.Kernel.Scheduler.Liveness.BandExhaustion` |
| CP-D5f | D5-J | `lake build SeLe4n.Kernel.Scheduler.Liveness.DomainRotation` |
| CP-D5g | D5-K, D5-L, D5-M | `lake build SeLe4n.Kernel.Scheduler.Liveness.WCRT` |
| CP-D5h | D5-N, D5-O, D5-P | `./scripts/test_full.sh` |

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

### 9.1 Detailed Task Decomposition

D6 is an integration and verification phase. The following expands the tasks
that involve multiple files or complex coordination.

**D6-D: Rust ABI Synchronization — 5 Steps**

| Step | Operation | Validation |
|------|-----------|-----------|
| D6-D1 | Add 5 new `SyscallId` enum variants to Rust ABI | `TcbSuspend = 20`, `TcbResume = 21`, `TcbSetPriority = 22`, `TcbSetMCPriority = 23`, `TcbSetIPCBuffer = 24` |
| D6-D2 | Update `SyscallId::COUNT` constant | From 20 to 25. Update compile-time `static_assert!` (W6-G pattern). |
| D6-D3 | Add Rust argument decode structures | `SuspendArgs`, `ResumeArgs` (no fields — capability-only), `SetPriorityArgs { new_priority: u8 }`, `SetMCPriorityArgs { new_mcp: u8 }`, `SetIPCBufferArgs { buffer_addr: u64 }` |
| D6-D4 | Update Rust dispatch match | Add 5 new arms to the syscall dispatch. Map each to its Lean-side operation name for traceability. |
| D6-D5 | Run Rust compile + sync assertions | `cargo build` in ABI crate. Verify compile-time assertions match Lean-side `SyscallId.COUNT = 25`. |

**D6-F: Spec §5.14 Comprehensive Update — 5 Subsections**

| Subsection | Content | Source |
|-----------|---------|--------|
| D6-F1 | §5.14.1 Thread Suspension Semantics | `suspendThread` pipeline (D1-G), state transitions, cleanup sequence, self-suspend behavior |
| D6-F2 | §5.14.2 Priority Management via MCS | `setPriorityOp`/`setMCPriorityOp`, SchedContext-aware priority path, MCP authority model |
| D6-F3 | §5.14.3 IPC Buffer Validation | 5-step validation pipeline (D3-D), alignment requirements, VSpace lookup |
| D6-F4 | §5.14.4 Priority Inheritance Protocol | Blocking graph, propagation/reversion, composition with Z7 donation, bounded inversion |
| D6-F5 | §5.14.5 Bounded Latency Guarantees | WCRT hypotheses, CBS-aware bound formula, PIP enhancement, domain rotation |

**D6-I: Metrics Regeneration — 4 Independent Updates**

| Step | File | Update |
|------|------|--------|
| D6-I1 | `docs/codebase_map.json` | Regenerate with new Lean source files (~19 new files) |
| D6-I2 | `README.md` | Syscall count 20→25, theorem count increment (~30 new theorems), proof line count, invariant count |
| D6-I3 | `docs/WORKSTREAM_HISTORY.md` | WS-AB entry: 6 phases, 90 sub-tasks, v0.24.0–v0.24.5, deferred ops + liveness completion |
| D6-I4 | `CHANGELOG.md` | 6 version entries (v0.24.0 through v0.24.5) with per-phase highlights |

### 9.2 Verification Checkpoints

| Checkpoint | After Tasks | Validation Command |
|-----------|-------------|-------------------|
| CP-D6a | D6-A, D6-B, D6-C | `lake build SeLe4n.Kernel.InformationFlow.Enforcement.Wrappers && lake build SeLe4n.Kernel.API && lake build SeLe4n.Kernel.FrozenOps.Operations` |
| CP-D6b | D6-D | `cargo build` in Rust ABI crate + sync assertion check |
| CP-D6c | D6-E | `./scripts/test_full.sh && NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh` |
| CP-D6d | D6-F through D6-J | `./scripts/test_tier0_hygiene.sh` (includes website link manifest check) |

---

## 10. Execution Strategy & Parallelism Optimization

### 10.1 Wave-Based Execution Model

The 6 phases organize into 4 execution waves based on dependency analysis:

```
Wave 1 (parallel):  D1 ─────── D2 ─────── D3
                     │          │
                     └────┬─────┘
                          ▼
Wave 2 (sequential): D4 (depends on D1 suspend cleanup + D2 priority primitives)
                          │
                          ▼
Wave 3 (sequential): D5 (depends on D4 PIP-aware effective priority)
                          │
                          ▼
Wave 4 (sequential): D6 (depends on all prior phases)
```

**Wave 1 parallelism**: D1, D2, and D3 are fully independent. They modify
disjoint syscall IDs, create disjoint new files, and add non-conflicting
constructors to `SyscallId`. Maximum parallelism: 3 concurrent workstreams.
The only shared file is `Model/Object/Types.lean`, but each phase adds new
enum constructors (additive, non-conflicting merge).

**Wave 2–3 sequential constraint**: D4 requires D1's suspend cleanup patterns
(D4-N reuses `revertPriorityInheritance` in suspend path) and D2's priority
update primitives (D4-G reuses bucket migration). D5 requires D4's
`effectivePriority` with `pipBoost` for PIP-aware WCRT.

**Wave 3 partial parallelism**: D5-A through D5-C (trace model infrastructure)
are independent of D4's integration phase. D5a can begin as soon as D4a
(types and graph) is complete, overlapping with D4b/D4c. This reduces the
critical path by ~1 sub-phase.

### 10.2 Critical Path Analysis

```
D1-A ──→ D1-C/D/E/F (parallel) ──→ D1-G ──→ D1-I/J/K/L/M (proofs) ──→ D1-O ──→ D1-Q
                                                                              ↓
D4-A ──→ D4-C/D/E (graph) ──→ D4-F/G ──→ D4-H/I (chain walk) ──→ D4-L/M ──→ D4-O/P ──→ D4-S
                                                                                    ↓
                         D5-A/B/C ──→ D5-D/E/G (parallel) ──→ D5-H/I/J ──→ D5-K/L/M ──→ D5-P
                                                                                          ↓
                                                                                    D6-A/B/C ──→ D6-E ──→ D6-F/G/H/I
```

**Critical path length**: D1 (18 tasks) → D4 (20 tasks) → D5 (16 tasks) → D6
(10 tasks) = 64 tasks on the longest dependency chain. The remaining 26 tasks
(D2: 14 + D3: 12) run in parallel with Wave 1.

### 10.3 Shared File Coordination Protocol

Five shared files receive modifications from multiple phases:

| File | D1 | D2 | D3 | D4 | D6 | Coordination |
|------|----|----|----|----|-----|-------------|
| `Model/Object/Types.lean` | +2 SyscallId variants | +2 variants, +1 TCB field (MCP) | +1 variant | +1 TCB field (pipBoost) | — | All additive: new enum constructors and new struct fields. No conflicting edits. Safe for parallel merge. |
| `Kernel/API.lean` | +2 dispatch arms | +2 dispatch arms | +1 dispatch arm | — | Verification only | Each phase adds new `match` arms. Arms are independent clauses. Git merge: trivial. |
| `Architecture/SyscallArgDecode.lean` | +2 decode structures | +2 decode structures | +1 decode structure | — | — | All additive. |
| `InformationFlow/Enforcement/Wrappers.lean` | +2 boundary entries | +2 entries | +1 entry | — | Verification | Additive list extension. |
| `FrozenOps/Operations.lean` | +2 frozen ops | +2 frozen ops | +1 frozen op | — | Verification | Additive function definitions. |

**Merge strategy**: When Wave 1 phases complete, merge D1 first (it's on the
critical path), then D2, then D3. Each merge adds non-overlapping content.
If developed on separate branches, use `git merge` (not rebase) to preserve
the additive nature of changes.

### 10.4 Proof Reuse Map

Many D1–D5 proofs follow established patterns from prior workstreams. The
following maps each proof type to its reusable template:

| Proof Pattern | Template Source | Used In |
|--------------|----------------|---------|
| Queue removal preserves NoDup | `remove_preserves_nodup` (RunQueue.lean:135) | D1-K, D2-G, D4-O |
| Endpoint queue remove well-formedness | Z6-B `endpointQueueRemove` (DualQueue/Core.lean:461) | D1-I, D1-J |
| Frame preservation (disjoint fields) | Z9-A `schedContextStoreConsistent` frame pattern | D1-L, D2-H, D3-F, D4-P |
| Bucket migration (remove + insert) | `ensureRunnable_nodup` (SchedulerLemmas.lean) | D2-E4, D4-G4 |
| Chain induction on fuel | Z7-D `donationChainAcyclic` pattern | D4-D, D4-H, D4-I |
| Bundle composition via ⟨...⟩ | Every prior invariant preservation proof | All phases |

---

## 11. Scope Summary

### 11.1 Sub-task Count by Phase

| Phase | Version | Sub-tasks | Atomic Steps | Complexity | Nature |
|-------|---------|-----------|-------------|-----------|--------|
| D1 — Thread Suspend/Resume | v0.24.0 | 18 | ~55 | High | New syscalls + lifecycle transitions + full preservation proofs |
| D2 — Priority Management | v0.24.1 | 14 | ~38 | Medium | SchedContext priority updates + authority model |
| D3 — IPC Buffer Configuration | v0.24.2 | 12 | ~25 | Low | VSpace validation + simple field update |
| D4 — Priority Inheritance Protocol | v0.24.3 | 20 | ~62 | High | Blocking graph + transitive propagation + bounded inversion proofs |
| D5 — Bounded Latency Theorem | v0.24.4 | 16 | ~48 | High | Proof-only: CBS-aware WCRT bound (zero code changes) |
| D6 — API Surface & Closure | v0.24.5 | 10 | ~27 | Medium | Integration, verification, documentation |
| **Total** | | **90** | **~255** | | |

*Note*: "Atomic Steps" counts the individual implementation/proof steps from
the §X.1 Detailed Task Decomposition subsections. Each atomic step is
independently compilable and verifiable. The 90 top-level sub-tasks decompose
into ~255 atomic steps, ensuring no single work unit requires holding complex
multi-step context in working memory.
 
### 11.2 Deferred Operation Coverage
 
| Operation | Phase | SyscallId | Dispatch Path | Key Theorem |
|-----------|-------|-----------|--------------|-------------|
| `suspend` | D1 | `.tcbSuspend` | `dispatchCapabilityOnly` | `suspend_preserves_proofLayerInvariantBundle` |
| `resume` | D1 | `.tcbResume` | `dispatchCapabilityOnly` | `resume_preserves_proofLayerInvariantBundle` |
| `setPriority` | D2 | `.tcbSetPriority` | `dispatchWithCap` | `setPriority_authority_bounded` |
| `setMCPriority` | D2 | `.tcbSetMCPriority` | `dispatchWithCap` | `setMCPriority_authority_bounded` |
| `setIPCBuffer` | D3 | `.tcbSetIPCBuffer` | `dispatchWithCap` | `validateIpcBufferAddress_implies_mapped` |
 
### 11.3 Starvation Vector Coverage (Updated)
 
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
 
### 11.4 Files Impacted by Phase
 
| Phase | New Lean Files | Modified Lean Files | New Test Files | Doc Files |
|-------|---------------|--------------------|--------------|---------:|
| D1 | 2 (Lifecycle/Suspend, Invariant/SuspendPreservation) | ~5 (Types, API, SyscallArgDecode, Wrappers, FrozenOps) | 1 | 4 |
| D2 | 2 (SchedContext/PriorityManagement, Invariant/PriorityPreservation) | ~5 (Types, API, SyscallArgDecode, Wrappers, FrozenOps) | 1 | 4 |
| D3 | 1 (Architecture/IpcBufferValidation) | ~5 (Types, API, SyscallArgDecode, Wrappers, FrozenOps) | 1 | 4 |
| D4 | 6 (PriorityInheritance/: BlockingGraph, Compute, Propagate, Preservation, BoundedInversion, re-export) | ~3 (Types, Donation, Suspend) | 1 | 4 |
| D5 | 8 (Liveness/: TraceModel, TimerTick, Replenishment, Yield, BandExhaustion, DomainRotation, WCRT, re-export) | 0 | 1 | 4 |
| D6 | 0 | ~3 (Wrappers, API, FrozenOps verification) | 0 | 7 |
| **Total** | **~19** | **~21** | **5** | **27** |
 
### 11.5 Effort Distribution
 
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

### 11.6 Verification Checkpoint Summary

All 6 phases include explicit verification checkpoints (CP-D1a through CP-D6d).
Total: **30 checkpoints** across the workstream. Each checkpoint specifies:
- The exact `lake build <Module.Path>` command to run
- Which sub-tasks must be complete before the checkpoint
- What the checkpoint validates (compilation, proof correctness, test pass)

Checkpoints enforce the project's mandatory module build verification: no
commit proceeds without `lake build <Module.Path>` for every modified `.lean`
file. This catches proof regressions immediately rather than at PR time.

### 11.7 Critical Path Duration Estimate

| Segment | Tasks on Path | Parallelizable? |
|---------|--------------|----------------|
| Wave 1 (D1) | D1-A → D1-C..F → D1-G → D1-I..N → D1-O → D1-Q → D1-R | D2/D3 run in parallel; D1 determines wave completion |
| Wave 2 (D4) | D4-A → D4-C..E → D4-F/G → D4-H/I → D4-L/M → D4-O/P → D4-S/T | D5-A/B/C can overlap with late D4 |
| Wave 3 (D5) | D5-D..G → D5-H/I/J → D5-K/L/M → D5-N..P | Internal parallelism within mechanism bounds |
| Wave 4 (D6) | D6-A..C → D6-E → D6-F..J | Short closure phase; mostly verification |

The critical path runs through D1 → D4 → D5 → D6 (64 top-level tasks, ~180
atomic steps). D2 (14 tasks) and D3 (12 tasks) are fully off the critical path
and can be completed during Wave 1 without impacting overall delivery.

---

## 12. Technical Risks

### 12.1 Implementation Risks
 
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
 
### 12.2 Schedule Risks
 
| Risk | Mitigation |
|------|------------|
| D4 + D5 combined is very large (36 sub-tasks) and may slip | D1/D2/D3 are independently valuable and can ship immediately. D4 and D5 each close specific starvation vectors. D4 can be split into sub-phases (D4a: types + graph D4-A–E, D4b: propagation D4-F–K, D4c: integration D4-L–N, D4d: proofs D4-O–T). |
| D1 depends on understanding all subsystem interactions | Systematic audit: enumerate every reference to `ThreadIpcState`, `ThreadState`, `scheduler.current`, and run queue insertion/removal. The existing lifecycle cleanup (`lifecyclePreRetypeCleanup`, `cleanupTcbReferences`) already performs most of this work — suspend is structurally similar. |
| D2/D3 type changes conflict with D1 if developed in parallel | Additive changes only: D1 adds 2 SyscallId variants, D2 adds 2, D3 adds 1. Each adds new constructors — no conflicting modifications to existing constructors. D2-A adds a new TCB field; D4-A adds another. Both are additive. Merge conflicts are simple enum-extension merges. |
| D5 proof work is unbounded in difficulty | D5 is proof-only with zero code changes. If proofs are harder than expected, D5 can be delivered incrementally: (1) trace model infrastructure first (D5-A–C), (2) per-mechanism bounds (D5-D–J), (3) composite WCRT last (D5-K–M). Each intermediate result is independently publishable. |
 
---
 
## 13. Invariant Landscape
 
### 13.1 Invariants Preserved by Each Phase
 
| Invariant Bundle | D1 | D2 | D3 | D4 | D5 | D6 |
|-----------------|----|----|----|----|----|----|
| `schedulerInvariantBundleExtended` (15-tuple) | D1-K/L: suspend removes from queue; resume inserts | D2-G: priority bucket migration | Frame (ipcBuffer not referenced) | D4-O: PIP bucket migration across chain | Read-only | Verify |
| `ipcInvariantFull` (14 conjuncts) | D1-J: IPC blocking cancellation | D2-H: frame (priority not in IPC) | Frame | D4-P: frame (pipBoost not in IPC) | Read-only | Verify |
| `crossSubsystemInvariant` (8 predicates) | D1-M: SchedContext cleanup, queue removal | D2-H: `schedContextStoreConsistent` | Frame | D4-P: frame | Read-only | Verify |
| `proofLayerInvariantBundle` (10 conjuncts) | Composed from above | Composed from above | D3-F: single frame theorem | Composed from above | Read-only | Verify |
 
### 13.2 New Invariant Predicates Introduced
 
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
 
## 14. Acceptance Criteria Summary
 
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
 
## 15. Workstream Naming Convention
 
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
 
## 16. Relationship to WS-V Starvation Prevention Plan
 
The file `docs/dev_history/WS_V_KERNEL_STARVATION_PREVENTION_PLAN.md` is retained
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
 
## 17. Deferred Items
 
### 17.1 Deferred Starvation Vectors
 
| ID | Vector | Severity | Reason for Deferral |
|----|--------|----------|---------------------|
| SV-4 | Notification LIFO ordering | MEDIUM | seL4 semantic compatibility. Notification LIFO matches seL4's design. Changing to FIFO would break compatibility. Practical impact limited: notification signals typically wake exactly one waiter, and notification-heavy patterns use bounded-badge coalescing. |
 
### 17.2 Deferred Enhancements
 
| Enhancement | Description | Reason for Deferral |
|-------------|-------------|---------------------|
| General per-operation IPC timeout | Independent countdown timers on IPC operations (not tied to SchedContext budget) | Z6 budget-driven timeout already resolves SV-3. Independent timeouts would add complexity with marginal benefit. If needed, can be layered atop Z6 in a future workstream. |
| Priority aging / decay | Gradually boost starved threads' effective priority | Violates strict priority ordering, incompatible with hard real-time. CBS budgets (Z2) provide a better mechanism. |
| Priority ceiling protocol (PCP) | Alternative to PIP preventing deadlock by ceiling-setting | PIP (D4) is sufficient given `tcbQueueChainAcyclic`. PCP adds complexity without clear benefit. |
| Response-time iteration analysis | Tighter WCRT via iterative fixed-point computation | D5's `N × (B + P)` bound is conservative. Tighter analysis deferred to a dedicated real-time analysis workstream built on D5's trace model. |
| Non-interference liveness | Prove information-flow policy does not create liveness-visible side channels | Orthogonal to scheduling liveness. Better addressed in a dedicated security workstream extending NI projection with trace-level properties. |
 
### 17.3 Future Workstream Candidates
 
| Candidate | Scope | Prerequisite |
|-----------|-------|-------------|
| WS-AC: Real-Time Analysis Framework | Formal schedulability analysis (RMA, response-time iteration) on D5 trace model | WS-AB (D5 WCRT theorem) |
| WS-AD: Mixed-Criticality Scheduling | Criticality levels, mode changes, graceful degradation | WS-AB (D4 PIP + D5 WCRT) |
| WS-AE: Hardware Timer Binding | RPi5 ARM Generic Timer → kernel timer tick integration | WS-AB complete + WS-U platform types |
