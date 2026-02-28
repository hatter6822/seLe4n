# WS-F Workstream Plan — v0.12.2 Audit Remediation

**Created:** 2026-02-28
**Findings baseline:** [`AUDIT_CODEBASE_v0.12.2_v1.md`](AUDIT_CODEBASE_v0.12.2_v1.md), [`AUDIT_CODEBASE_v0.12.2_v2.md`](AUDIT_CODEBASE_v0.12.2_v2.md)
**Prior portfolio:** WS-E (v0.11.6, all 6 workstreams completed)
**Project direction:** Production microkernel targeting Raspberry Pi 5 (ARM64)

---

## 1. Planning Objective

Close all findings from two independent v0.12.2 codebase audits, advancing the
kernel toward production readiness. Combined findings: 6 CRITICAL, 6 HIGH,
12 MEDIUM, 9 LOW across proof coverage, model fidelity, information flow,
testing, and documentation.

This plan prioritizes work that directly enables the production kernel path:
IPC message transfer, Untyped memory, and complete information-flow coverage
are prerequisites for Raspberry Pi 5 hardware binding.

## 2. Planning Principles

1. **Production-oriented**: every workstream advances toward a deployable kernel.
2. **Proof-first**: no operation ships without invariant preservation theorems.
3. **Evidence-gated**: every workstream closes with reproducible command evidence.
4. **Canonical-first docs**: root docs updated before GitBook mirrors.
5. **No sorry/axiom**: zero tolerance in production proof surface.
6. **Deterministic semantics**: all transitions remain explicit success/failure.

---

## 3. Finding-to-Workstream Matrix

### Cross-reference: v1 audit (CRIT/HIGH/MED/LOW) + v2 audit (F-01..F-28)

| Finding (v1) | Finding (v2) | Severity | Workstream |
|--------------|--------------|----------|------------|
| CRIT-01 (No message transfer) | — | CRITICAL | WS-F1 |
| CRIT-05 (Dual-queue unverified) | F-10 | CRITICAL | WS-F1 |
| — | F-11 (endpointCall/ReplyRecv) | HIGH | WS-F1 |
| CRIT-04 (No Untyped memory) | — | CRITICAL | WS-F2 |
| CRIT-02 (Incomplete projection) | F-22 | CRITICAL | WS-F3 |
| CRIT-03 (NI covers 5 of 30+) | F-20, F-21 | CRITICAL | WS-F3 |
| — | F-03 (timerTick no proofs) | HIGH | WS-F4 |
| — | F-06 (cspaceMutate etc.) | HIGH | WS-F4 |
| — | F-12 (notification preservation) | HIGH | WS-F4 |
| CRIT-06 (Badge semantics) | — | CRITICAL | WS-F5 |
| HIGH-01 (Single-level CSpace) | — | HIGH | WS-F5 |
| HIGH-02 (No per-thread regs) | — | HIGH | WS-F5 |
| HIGH-04 (Rights as ordered List) | — | HIGH | WS-F5 |
| HIGH-03 (No IpcState→scheduler link) | F-13 | HIGH | WS-F6 |
| HIGH-05 (Dual queue no consistency) | — | HIGH | WS-F6 |
| HIGH-06 (serviceCountBounded) | — | HIGH | WS-F6 |
| HIGH-07 (No intransitive NI) | — | HIGH | WS-F6 |
| HIGH-08 (AdapterProofHooks) | F-18 | HIGH | WS-F6 |
| MED-01 (Invariant inflation) | F-07, F-15 | MEDIUM | WS-F6 |
| MED-02 (Unpreserved invariants) | F-04 | MEDIUM | WS-F6 |
| MED-05 (schedulerWellFormed) | — | MEDIUM | WS-F6 |
| MED-06 (runnableThreadsAreTCBs) | — | MEDIUM | WS-F6 |
| MED-07 (VSpace ASID isolation) | — | MEDIUM | WS-F6 |
| MED-08 (Tier 3 grep-only) | — | MEDIUM | WS-F7 |
| — | F-24 (Runtime oracle gaps) | MEDIUM | WS-F7 |
| — | F-25 (Unused fixtures) | LOW | WS-F7 |
| — | F-26 (Probe covers 3 ops) | LOW | WS-F7 |
| MED-03 (Missing operations) | — | MEDIUM | WS-F5 |
| MED-04 (Dead domain lattice) | — | MEDIUM | WS-F8 |
| — | F-01 (Redundant endpoint fields) | LOW | WS-F8 |
| — | F-14 (Dead endpointInvariant) | LOW | WS-F8 |
| — | F-19 (Stub declarations) | LOW | WS-F8 |
| MED-17/F-17 (Service is extension) | — | MEDIUM | WS-F8 |

---

## 4. Workstream Definitions

### WS-F1: IPC Message Transfer and Dual-Queue Verification (CRITICAL)

**Objective:** Make IPC actually transfer data between threads and formally verify
the dual-queue endpoint model.

**Entry criteria:** Current codebase compiles with zero sorry.

**Deliverables:**
1. Wire `IpcMessage` (registers, caps, badge) into `endpointSend`/`endpointReceive` and dual-queue variants.
2. Prove `ipcInvariant` and `schedulerInvariantBundle` preservation for `endpointSendDual`, `endpointReceiveDual`, `endpointQueueRemoveDual`.
3. Prove preservation for `endpointCall` and `endpointReplyRecv` (composed from primitives).
4. Add capability transfer through IPC (at minimum, badge propagation).
5. Extend trace harness and fixture expectations for message content.

**Exit evidence:**
- `lake build` passes.
- `test_full.sh` passes including new Tier-3 anchors for dual-queue theorems.
- At least one trace scenario shows actual data moving between sender and receiver.

**Dependencies:** None (can start immediately).

### WS-F2: Untyped Memory Model (CRITICAL)

**Objective:** Add the foundational seL4 memory safety mechanism.

**Deliverables:**
1. Define `UntypedObject` with region bounds and watermark.
2. Implement `retypeFromUntyped` that carves typed objects from untyped regions.
3. Add watermark-based allocation tracking.
4. Prove that retype respects region bounds and watermark monotonicity.
5. Prove that typed object addresses do not overlap within an untyped region.

**Exit evidence:**
- `lake build` passes.
- `test_full.sh` passes with new Tier-3 anchors.
- Trace harness exercises retype-from-untyped path.

**Dependencies:** None (can start immediately, parallel with WS-F1).

### WS-F3: Information-Flow Completeness (HIGH) — **COMPLETED**

**Objective:** Extend information-flow proofs from 5 operations to full API coverage
and connect the enforcement layer to non-interference theorems.

**Deliverables (completed):**
1. Extended `ObservableState` with 3 new security-relevant fields: `activeDomain` (scheduling transparency), `irqHandlers` (filtered by target observability), `objectIndex` (filtered by object observability).
2. Proved non-interference for all new projection fields across high-step and low-step unwinding (7+ NI theorems covering `endpointSend`, `notificationSignal`, `storeObject`, `cspaceRevoke`, `serviceRestartChecked`, etc.).
3. Proved enforcement-to-NI connection: `serviceRestartChecked` enforcement-NI bridge via Bool case-splitting pattern; existing bridges for `endpointSendChecked` and `cspaceMintChecked` extended with new field preservation.
4. Added `notificationSignal` non-interference theorem with full 7-field preservation.
5. Implemented CNode slot filtering via `projectKernelObject` to prevent high-domain capability target leakage (F-22). Proved `projectKernelObject_idempotent` and `projectKernelObject_objectType` safety theorems.

**Exit evidence (met):**
- `lake build` passes with zero errors/warnings.
- `test_full.sh` passes (Tier 0-3).
- InformationFlowSuite extended with WS-F3 tests: activeDomain projection, IRQ handler projection, object index projection, CNode slot filtering (F-22), 7-field low-equivalence, `serviceRestartChecked` enforcement.

**Dependencies:** WS-F1 (IPC message transfer affects NI proofs for IPC operations).

### WS-F4: Proof Gap Closure (HIGH)

**Objective:** Close high-value proof gaps for defined operations that lack theorems.

**Deliverables:**
1. Prove `timerTick` preserves `queueCurrentConsistent`, `runQueueUnique`, `currentThreadValid`, `currentThreadInActiveDomain`.
2. Prove `cspaceMutate` preserves `capabilityInvariantBundle`.
3. Prove `notificationSignal` and `notificationWait` preserve full `ipcInvariant` + `schedulerInvariantBundle`.
4. Prove `cspaceRevokeCdt` and `cspaceRevokeCdtStrict` preserve `capabilityInvariantBundle`.

**Exit evidence:**
- `lake build` passes.
- `test_full.sh` passes with new Tier-3 anchors.
- No new sorry/axiom.

**Dependencies:** None (can start immediately, parallel with WS-F1/F2).

### WS-F5: Model Fidelity (MEDIUM)

**Objective:** Close the gap between the seLe4n model and seL4 reality where it
matters for production.

**Deliverables:**
1. Change `Notification.pendingBadge` to word-sized bitmask with OR-accumulation.
2. Add per-thread register context (move from global `MachineState.regs` to `TCB.regs`).
3. Implement recursive multi-level CSpace resolution with guard/radix bits.
4. Replace `List AccessRight` with order-independent representation (e.g., `Finset`).
5. Add missing operations: `setPriority`, `suspend`/`resume`, or document their deferral.

**Exit evidence:**
- `lake build` passes.
- `test_smoke.sh` passes.
- Trace harness exercises multi-level CSpace path.

**Dependencies:** WS-F4 (existing proofs should be sound before model changes).

### WS-F6: Invariant Quality (MEDIUM)

**Objective:** Strengthen the invariant surface and close architectural gaps.

**Deliverables:**
1. Reclassify `cspaceAttenuationRule`, `lifecycleAuthorityMonotonicity`, `lifecycleIdentityNoTypeAliasConflict` as operation correctness lemmas (not state invariants).
2. Extend `ipcSchedulerContractPredicates` to cover `blockedOnNotification` and `blockedOnReply`.
3. Instantiate `AdapterProofHooks` with at least one concrete proof.
4. Discharge `serviceCountBounded` (currently assumed).
5. Add `runnableThreadsAreTCBs` invariant.
6. Prove `timeSlicePositive` and `edfCurrentHasEarliestDeadline` preservation for at least `schedule`.
7. Add VSpace cross-ASID isolation theorem.

**Exit evidence:**
- `lake build` passes.
- `test_full.sh` passes.

**Dependencies:** WS-F4 (proof gap closure provides foundation).

### WS-F7: Testing Expansion (LOW)

**Objective:** Strengthen runtime validation and close testing gaps.

**Deliverables:**
1. Extend runtime invariant oracle (`InvariantChecks.lean`) to check `blockedOnSendNotRunnable`, `blockedOnReceiveNotRunnable`, `currentThreadInActiveDomain`, `uniqueWaiters`.
2. Extend `TraceSequenceProbe` to cover dual-queue, notification, scheduler, and capability operations.
3. Exercise `runtimeContractTimerOnly` and `runtimeContractReadOnlyMemory` fixtures.
4. Add CDT structural integrity runtime checks.

**Exit evidence:**
- `lake build` passes.
- `test_smoke.sh` passes.

**Dependencies:** WS-F1 (dual-queue operations needed for extended probe).

### WS-F8: Cleanup (LOW)

**Objective:** Remove dead code and resolve architectural divergences.

**Deliverables:**
1. Remove dead `endpointInvariant` definition.
2. Resolve legacy/dual-queue divergence: deprecate legacy operations or add refinement bridge.
3. Remove or document `ServiceStatus.failed`/`isolated` dead states.
4. Remove dead generic domain lattice code.
5. Remove forward-declared stubs without consumers.
6. Label Service subsystem clearly as a seLe4n extension (not seL4 formalization).

**Exit evidence:**
- `lake build` passes.
- `test_smoke.sh` passes.
- No orphaned definitions in the codebase.

**Dependencies:** WS-F1 (legacy/dual-queue resolution depends on dual-queue verification).

---

## 5. Execution Phases

| Phase | Workstreams | Description |
|-------|-------------|-------------|
| **P0** | — | Publish WS-F backbone, update all docs (this PR) |
| **P1** | WS-F1, WS-F2, WS-F4 | Critical IPC/memory + high-value proof gaps (parallel) |
| **P2** | WS-F3 | Information-flow completeness (depends on WS-F1 IPC) |
| **P3** | WS-F5, WS-F6 | Model fidelity + invariant quality |
| **P4** | WS-F7, WS-F8 | Testing expansion + cleanup |

---

## 6. Status Dashboard

| Workstream | Priority | Status | Findings addressed |
|------------|----------|--------|-------------------|
| WS-F1 | Critical | **Completed** | CRIT-01, CRIT-05, F-10, F-11 |
| WS-F2 | Critical | **Completed** | CRIT-04 |
| WS-F3 | High | **Completed** | CRIT-02, CRIT-03, F-20, F-21, F-22 |
| WS-F4 | High | Planning | F-03, F-06, F-12 |
| WS-F5 | Medium | Planning | CRIT-06, HIGH-01..04, MED-03 |
| WS-F6 | Medium | Planning | HIGH-03..08, MED-01..02, MED-05..07, F-07, F-13, F-15, F-18 |
| WS-F7 | Low | Planning | MED-08, F-24, F-25, F-26 |
| WS-F8 | Low | Planning | MED-04, MED-17, F-01, F-14, F-19 |
