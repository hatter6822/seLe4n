# WS-F Workstream Plan — v0.12.2 Audit Remediation

**Created:** 2026-02-28
**Last updated:** 2026-03-01 (PR #290 H3-prep integration, WS-F1..F4 completion records)
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
are prerequisites for Raspberry Pi 5 hardware binding. With WS-F1..F4
completed and H3-prep platform binding infrastructure delivered (PR #290),
remaining workstreams operate on a stable foundation with concrete platform
targets (SimPlatform, RPi5Platform) available for contract instantiation.

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
| — | F-19 (Stub declarations) | LOW | ~~WS-F8~~ **Closed (PR #290)** |
| MED-17/F-17 (Service is extension) | — | MEDIUM | WS-F8 |

---

## 4. Workstream Definitions

### WS-F1: IPC Message Transfer and Dual-Queue Verification (CRITICAL) — **COMPLETED**

**Objective:** Make IPC actually transfer data between threads and formally verify
the dual-queue endpoint model.

**Entry criteria:** Current codebase compiles with zero sorry.

**Deliverables (completed):**
1. `IpcMessage` (registers, caps, badge) wired into `endpointSendDual`/`endpointReceiveDual` and compound operations (`endpointCall`, `endpointReply`, `endpointReplyRecv`). Messages staged in `TCB.pendingMessage` during IPC and transferred on handshake/dequeue.
2. 14 invariant preservation theorems for dual-queue and compound operations preserving `ipcInvariant`, `schedulerInvariantBundle`, and `ipcSchedulerContractPredicates`.
3. `storeTcbIpcStateAndMessage` and `storeTcbPendingMessage` helpers for combined state+message updates with supporting proof lemmas.
4. Badge propagation through IPC message transfer.
5. 7 trace scenarios (F1-01a..F1-03b) demonstrating send-then-receive with registers/badge, rendezvous delivery, and call/reply roundtrip.

**Exit evidence (met):**
- `lake build` passes with zero errors/warnings.
- `test_full.sh` passes (Tier 0-3) with dual-queue Tier-3 anchors.
- Trace scenarios show actual data (registers, badge) moving between sender and receiver.

**Dependencies:** None.

### WS-F2: Untyped Memory Model (CRITICAL) — **COMPLETED**

**Objective:** Add the foundational seL4 memory safety mechanism.

**Deliverables (completed):**
1. `UntypedObject` with `regionBase`, `regionSize`, `watermark`, `children`, `isDevice`. `UntypedChild` tracks carved children with `objId`, `offset`, `size`.
2. `retypeFromUntyped` carves typed objects from untyped regions with authority via `cspaceLookupSlot`, region bounds via `canAllocate`, and device restrictions.
3. Watermark-based allocation: `allocate_watermark_advance`, `allocate_watermark_monotone`, `allocate_preserves_watermarkValid`.
4. `allocate_some_iff` decomposition, `retypeFromUntyped_ok_decompose` with allocSize bound conjunct, region bounds and watermark monotonicity proofs.
5. `untypedChildrenNonOverlapInvariant` and `untypedChildrenUniqueIdsInvariant` prove non-overlapping typed object addresses within untyped regions.

**Exit evidence (met):**
- `lake build` passes with zero errors/warnings.
- `test_full.sh` passes (Tier 0-3) with 27 Tier-3 surface anchors.
- 8 trace scenarios (F2-01..F2-08) exercise retype-from-untyped path.

**Dependencies:** None.

### WS-F3: Information-Flow Completeness (HIGH) — **COMPLETED**

**Objective:** Extend information-flow proofs from 5 operations to full API coverage
and connect the enforcement layer to non-interference theorems.

**Deliverables (completed):**
1. Extended `ObservableState` with 3 new security-relevant fields: `activeDomain` (scheduling transparency), `irqHandlers` (filtered by target observability), `objectIndex` (filtered by object observability).
2. Proved non-interference for all new projection fields across high-step and low-step unwinding (12 standalone NI theorems covering `endpointSend`, `chooseThread`, `cspaceMint`, `cspaceRevoke`, `lifecycleRetypeObject`, `notificationSignal`, `notificationWait`, `cspaceInsertSlot`, `serviceStart`, `serviceStop`, `serviceRestart`, `storeObject`; plus 3 enforcement-NI bridge theorems).
3. Proved enforcement-to-NI connection: `serviceRestartChecked` enforcement-NI bridge via Bool case-splitting pattern; existing bridges for `endpointSendChecked` and `cspaceMintChecked` extended with new field preservation.
4. Added `notificationSignal` non-interference theorem with full 7-field preservation.
5. Implemented CNode slot filtering via `projectKernelObject` to prevent high-domain capability target leakage (F-22). Proved `projectKernelObject_idempotent` and `projectKernelObject_objectType` safety theorems.

**Exit evidence (met):**
- `lake build` passes with zero errors/warnings.
- `test_full.sh` passes (Tier 0-3).
- InformationFlowSuite extended with WS-F3 tests: activeDomain projection, IRQ handler projection, object index projection, CNode slot filtering (F-22), 7-field low-equivalence, `serviceRestartChecked` enforcement.

**Dependencies:** WS-F1 (IPC message transfer affects NI proofs for IPC operations).

### WS-F4: Proof Gap Closure (HIGH) — **COMPLETED**

**Objective:** Close high-value proof gaps for defined operations that lack theorems.

**Deliverables (completed):**
1. `timerTick_preserves_schedulerInvariantBundle` and `timerTick_preserves_kernelInvariant` — covers `queueCurrentConsistent`, `runQueueUnique`, `currentThreadValid`, `currentThreadInActiveDomain`. Expired-timeslice path delegates to `schedule_preserves_*`; non-expired path proves scheduler unchanged directly.
2. `cspaceMutate_preserves_capabilityInvariantBundle` — uses `revert/unfold` decomposition pattern; case-splits on capability lookup, rights check, and storeObject.
3. `notificationSignal_preserves_ipcInvariant`, `notificationSignal_preserves_schedulerInvariantBundle`, `notificationWait_preserves_ipcInvariant`, `notificationWait_preserves_schedulerInvariantBundle` — compositional through `storeObject_notification_preserves_ipcInvariant` helper; wake/merge/badge-consume/wait paths fully covered.
4. `cspaceRevokeCdt_preserves_capabilityInvariantBundle` and `cspaceRevokeCdtStrict_preserves_capabilityInvariantBundle` — fold induction via extracted `revokeCdtFoldBody` with error propagation lemmas; CDT-only state updates handled by `capabilityInvariantBundle_of_cdt_update`.
5. `notificationSignal_preserves_ipcSchedulerContractPredicates` and `notificationWait_preserves_ipcSchedulerContractPredicates` — M3.5 contract predicate gap closure for notification operations. Wake/badge-consume paths use backward TCB transport through storeObject + storeTcbIpcState; merge path via `contracts_of_same_scheduler_ipcState`; wait path handles `.blockedOnNotification` (orthogonal to `blockedOnSend`/`blockedOnReceive` predicates) with removeRunnable.

**Exit evidence (met):**
- `lake build` passes with zero errors/warnings.
- `test_full.sh` passes (Tier 0-3) with 11 Tier-3 surface anchors.
- Zero `sorry`/`axiom` in production proof surface.

**Dependencies:** None.

### WS-F5: Model Fidelity (MEDIUM) — **COMPLETED**

**Objective:** Close the gap between the seLe4n model and seL4 reality where it
matters for production. Badge values must be word-bounded, capability rights must
be order-independent, and missing scheduler operations must be explicitly
dispositioned.

**Prior work (already delivered, no longer in scope):**
- ~~Per-thread register context~~: Delivered in WS-H12c (v0.14.0). `TCB.registerContext : RegisterFile`
  with context-switch save/restore is live and proven.
- ~~Multi-level CSpace resolution~~: Delivered in WS-H13 (v0.14.4). `resolveCapAddress` performs
  recursive guard/radix resolution with termination proof. CNode has `depth`, `guardWidth`,
  `guardValue`, `radixWidth` fields.

**Remaining deliverables (3):**

#### F5-D1: Word-Bounded Badge with Bitmask Semantics (CRIT-06)

**Problem:** `Badge.val : Nat` is unbounded. seL4 badges are exactly one machine
word (64 bits on ARM64). An unbounded badge permits values that cannot exist on
real hardware, creating a model fidelity gap that could mask overflow bugs.

**Security rationale:** Badge overflow in a real kernel is a potential information
leak — if the model allows 65-bit badge values but hardware truncates silently,
proven badge-routing theorems do not hold on actual hardware. Bounding the model
type closes this gap.

**Implementation plan:**

- **F5-D1a: Define `machineWordBits` constant and `Badge` bounding predicate.**
  Add `def machineWordBits : Nat := 64` to `Prelude.lean`. Add a `Badge.valid`
  predicate (`badge.val < 2 ^ machineWordBits`) and a `Badge.ofNatMasked`
  constructor that applies `val % (2 ^ machineWordBits)` truncation, matching
  seL4's silent word-truncation semantics.

- **F5-D1b: Add `Badge.bor` (bitwise OR) combiner with validity preservation.**
  Define `Badge.bor (a b : Badge) : Badge` that OR-merges and masks to word
  size. Prove `badge_bor_valid`: if both inputs are valid, the result is valid
  (since `a ||| b < 2 ^ n` when `a, b < 2 ^ n`). Prove `badge_bor_comm` and
  `badge_bor_idempotent`.

- **F5-D1c: Migrate `notificationSignal` to use `Badge.bor`.**
  Replace the inline `Badge.ofNat (existing.toNat ||| badge.toNat)` in
  `Endpoint.lean` with `Badge.bor existing badge`. Update
  `notificationSignal_badge_stored_fresh` and `badge_merge_idempotent` theorems
  in `Authority.lean` to reference the new combiner.

- **F5-D1d: Add `badgeWellFormed` invariant predicate.**
  In `IPC/Invariant/Defs.lean`, add a predicate asserting that all badges in
  notification objects and capabilities are word-bounded. Prove preservation
  through `notificationSignal`, `notificationWait`, `cspaceMint`, and
  `cspaceMutate`.

- **F5-D1e: Update trace harness and test fixtures.**
  Update `NegativeStateSuite` badge accumulation tests to use `Badge.ofNatMasked`.
  Add a negative test: signaling with a value exceeding 2^64 is truncated.
  Update `main_trace_smoke.expected` if trace output changes.

#### F5-D2: Order-Independent Access Rights (HIGH-04)

**Problem:** `Capability.rights : List AccessRight` is order-dependent. Two
capabilities with the same rights in different order are not equal under `DecidableEq`,
which violates seL4 semantics where rights are a bitmask. This creates false
negative equality checks and fragile test assertions.

**Security rationale:** If `[.read, .write] ≠ [.write, .read]` in the model,
a capability with reordered rights could bypass attenuation checks or produce
false invariant violations. Order-independence is required for sound
rights-subset reasoning.

**Implementation plan:**

- **F5-D2a: Define `AccessRightSet` as a deduplicated sorted representation.**
  In `Model/Object/Types.lean`, define:
  ```
  def AccessRight.toOrd : AccessRight → Nat
  structure AccessRightSet where
    rights : List AccessRight  -- sorted, deduplicated
    sorted_dedup : rights.Pairwise (· .toOrd < ·.toOrd) := by decide
  ```
  This gives `DecidableEq` for free (structural equality on sorted lists),
  avoids importing `Mathlib.Data.Finset`, and keeps the representation
  computable for `native_decide` proofs. Provide `AccessRightSet.ofList`
  (sort + dedup), `AccessRightSet.mem`, `AccessRightSet.subset`.

- **F5-D2b: Migrate `Capability.rights` to `AccessRightSet`.**
  Change `rights : List AccessRight` → `rights : AccessRightSet` in the
  `Capability` structure. Update `hasRight` to use `AccessRightSet.mem`.
  Update `rightsSubset` to use `AccessRightSet.subset`. Update all capability
  construction sites to use `AccessRightSet.ofList [...]`.

- **F5-D2c: Update capability invariant proofs.**
  Update `capAttenuates` in `Operations.lean` to use `AccessRightSet.subset`.
  Re-prove `rightsSubset_sound`, `mintDerivedCap_rights_attenuated_with_badge_override`,
  and all `Authority.lean` attenuation theorems. Since subset on sorted-dedup
  lists is equivalent to the old `List.all (· ∈ ·)` check, most proofs adapt
  by unfolding the new definition.

- **F5-D2d: Update information-flow wrappers and NI proofs.**
  Update `Enforcement/Wrappers.lean` and `Invariant/Composition.lean` function
  signatures from `List AccessRight` to `AccessRightSet`. Update
  `cspaceMintChecked`, `enforcedCspaceMutate`, and non-interference step
  constructors.

- **F5-D2e: Update test fixtures and assertions.**
  Migrate all `rights := [.read, .write]` constructions to
  `rights := AccessRightSet.ofList [.read, .write]`. Fix equality assertions
  that relied on list ordering. Verify `NegativeStateSuite` and
  `InformationFlowSuite` pass.

#### F5-D3: Missing Operations Disposition (MED-03)

**Problem:** seL4 provides `setPriority`, `setMCPriority`, `suspend`, `resume`,
and `setIPCBuffer` operations. seLe4n does not implement them. The workstream
plan requires explicit disposition: implement or document deferral.

**Decision: Document deferral with rationale and tracking.**

- **F5-D3a: Add deferred operations section to `API.lean`.**
  Document `setPriority`, `suspend`, `resume`, and `setIPCBuffer` as
  explicitly deferred with rationale:
  - `setPriority`/`setMCPriority`: Requires MCS scheduling context model
    (long-horizon item). Priority is currently set at TCB creation. Runtime
    priority modification deferred until MCS scheduling contexts are modeled.
  - `suspend`/`resume`: Requires thread lifecycle state machine beyond
    `ThreadIpcState`. Deferred until WS-F6 invariant quality work establishes
    thread-lifecycle invariants.
  - `setIPCBuffer`: Trivial field update, but VSpace validation of the buffer
    address requires `VSpaceBackend` integration. Deferred until H3 hardware
    binding populates VSpace validation.

- **F5-D3b: Add deferred operations table to `SELE4N_SPEC.md`.**
  Create a "Deferred Operations" section in the spec listing each operation,
  seL4 reference, deferral rationale, and prerequisite workstream/milestone.

- **F5-D3c: Update `CLAIM_EVIDENCE_INDEX.md`.**
  Add explicit tracking entries for deferred operations so auditors can verify
  the disposition is intentional and tracked.

**Exit evidence:**
- `lake build` passes with zero errors/warnings.
- `test_full.sh` passes (Tier 0-3).
- All existing badge theorems updated to word-bounded representation.
- `badgeWellFormed` invariant defined and preservation proven for signal/wait/mint/mutate.
- `AccessRightSet` equality is order-independent: `[.read, .write] = [.write, .read]`.
- Trace harness exercises badge bitmask accumulation with word-bounded values.
- Deferred operations documented in API, spec, and evidence index.
- No `sorry` or `axiom` in production proof surface.

**Dependencies:** WS-F4 (existing proofs should be sound before model changes — completed).

### WS-F6: Invariant Quality (MEDIUM)

**Objective:** Strengthen the invariant surface and close architectural gaps.

**Enabling infrastructure (delivered by PR #290):**
- `PlatformBinding` typeclass with `RuntimeBoundaryContract` field provides the
  concrete pathway for `AdapterProofHooks` instantiation: platform bindings (Sim,
  RPi5) supply decidable contract predicates that can be threaded into the hooks.
- `VSpaceBackend` typeclass with per-operation ASID preservation proofs
  (`mapPage_preserves_asid`, `unmapPage_preserves_asid`) and round-trip correctness
  obligations. `listVSpaceBackend` instance demonstrates the current flat-list model
  satisfies these obligations. Cross-ASID *isolation* (operations on one ASID root
  do not affect another) remains a deliverable.

**Deliverables:**
1. Reclassify `cspaceAttenuationRule`, `lifecycleAuthorityMonotonicity`, `lifecycleIdentityNoTypeAliasConflict` as operation correctness lemmas (not state invariants).
2. Extend `ipcSchedulerContractPredicates` to cover `blockedOnNotification` and `blockedOnReply`.
3. Instantiate `AdapterProofHooks` with at least one concrete proof, using the `PlatformBinding` → `RuntimeBoundaryContract` infrastructure from PR #290. The Sim platform's permissive contract (`simRuntimeContractPermissive`) is the natural first target, as its trivially-true predicates simplify the proof obligations.
4. Discharge `serviceCountBounded` (currently assumed).
5. Add `runnableThreadsAreTCBs` invariant.
6. Prove `timeSlicePositive` and `edfCurrentHasEarliestDeadline` preservation for at least `schedule`.
7. Add VSpace cross-ASID isolation theorem. Note: per-operation ASID preservation is already proved in `VSpaceBackend`; this deliverable requires the stronger cross-root non-interference property.

**Exit evidence:**
- `lake build` passes.
- `test_full.sh` passes.

**Dependencies:** WS-F4 (proof gap closure provides foundation). H3-prep infrastructure (PR #290) provides the platform binding pathway for deliverable 3.

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
1. Remove dead `endpointInvariant` definition (F-14).
2. Resolve legacy/dual-queue divergence: deprecate legacy operations or add refinement bridge.
3. Remove or document `ServiceStatus.failed`/`isolated` dead states.
4. Remove dead generic domain lattice code (MED-04). *Note: no domain lattice code found in current codebase — verify whether this was addressed in a prior commit or was misidentified.*
5. ~~Remove forward-declared stubs without consumers (F-19).~~ **Closed by PR #290:** `BootBoundaryContract`, `InterruptBoundaryContract`, and `RuntimeBoundaryContract` are now instantiated in both `Platform/Sim/` and `Platform/RPi5/` with concrete consumers in `PlatformBinding`. Only `boundedAddressTranslation` (VSpaceInvariant.lean) remains a forward declaration, tracked separately under WS-E6 model completeness.
6. Label Service subsystem clearly as a seLe4n extension (not seL4 formalization).

**Exit evidence:**
- `lake build` passes.
- `test_smoke.sh` passes.
- No orphaned definitions in the codebase.

**Dependencies:** WS-F1 (legacy/dual-queue resolution depends on dual-queue verification).

---

## 5. Execution Phases

| Phase | Workstreams | Description | Status |
|-------|-------------|-------------|--------|
| **P0** | — | Publish WS-F backbone, update all docs | **Done** |
| **P1** | WS-F1, WS-F2, WS-F4 | Critical IPC/memory + high-value proof gaps (parallel) | **Done** |
| **P2** | WS-F3 | Information-flow completeness (depends on WS-F1 IPC) | **Done** |
| **H3-prep** | — | Platform binding infrastructure (PR #290): `PlatformBinding` typeclass, `MachineConfig`/`MemoryRegion`, `VSpaceBackend`, Sim + RPi5 bindings | **Done** |
| **P3** | WS-F5, WS-F6 | Model fidelity + invariant quality | **WS-F5 in progress** |
| **P4** | WS-F7, WS-F8 | Testing expansion + cleanup | Planning |

**Phase notes:**
- P0–P2 are complete. All CRITICAL and HIGH findings from P1/P2 are closed.
- H3-prep (PR #290) was executed between P2 and P3 as cross-cutting infrastructure.
  It is not a numbered workstream but delivers enabling assets: the `PlatformBinding`
  typeclass, `VSpaceBackend` abstraction, and concrete platform bindings that P3
  deliverables (particularly WS-F6 deliverable 3: `AdapterProofHooks` instantiation)
  depend on. It also closed F-19 (stub declarations) ahead of P4/WS-F8.
- P3 and P4 can now leverage H3-prep platform binding infrastructure.

---

## 6. Status Dashboard

| Workstream | Priority | Status | Findings addressed |
|------------|----------|--------|-------------------|
| WS-F1 | Critical | **Completed** | CRIT-01, CRIT-05, F-10, F-11 |
| WS-F2 | Critical | **Completed** | CRIT-04 |
| WS-F3 | High | **Completed** | CRIT-02, CRIT-03, F-20, F-21, F-22 |
| WS-F4 | High | **Completed** | F-03, F-06, F-12 |
| WS-F5 | Medium | **In Progress** | CRIT-06, ~~HIGH-01~~ (WS-H13), ~~HIGH-02~~ (WS-H12c), HIGH-04, MED-03 |
| WS-F6 | Medium | Planning (H3-prep infra available) | HIGH-03..08, MED-01..02, MED-05..07, F-07, F-13, F-15, F-18 |
| WS-F7 | Low | Planning | MED-08, F-24, F-25, F-26 |
| WS-F8 | Low | Planning (F-19 closed) | MED-04, MED-17, F-01, F-14, ~~F-19~~ |

**Aggregate finding closure (by matrix row):**
- **Closed:** 5 CRITICAL (CRIT-01, CRIT-04, CRIT-05 by WS-F1/F2; CRIT-02, CRIT-03 by WS-F3), 6 HIGH (F-11 by WS-F1; F-03, F-06, F-12 by WS-F4; HIGH-01 by WS-H13; HIGH-02 by WS-H12c), 1 LOW (F-19 by PR #290) = **12 of 33**
- **Open:** 1 CRITICAL (CRIT-06), 8 HIGH, 10 MEDIUM, 4 LOW = **23 of 33**

### Cross-cutting: H3-prep Platform Binding (PR #290)

PR #290 delivered foundational infrastructure between P2 and P3. While not a
numbered workstream, it has material impact on remaining work:

| Asset | Location | Impact |
|-------|----------|--------|
| `PlatformBinding` typeclass | `Platform/Contract.lean` | Unblocks WS-F6 deliverable 3 (AdapterProofHooks instantiation) |
| `MachineConfig` + `MemoryRegion` + `wellFormed` | `Machine.lean` | Provides hardware parameter vocabulary for WS-F5 model fidelity |
| `VSpaceBackend` + `listVSpaceBackend` | `Architecture/VSpaceBackend.lean` | Per-operation ASID preservation proved; cross-ASID isolation remains WS-F6 |
| `SimPlatform` binding | `Platform/Sim/*` | Permissive contract provides natural first target for `AdapterProofHooks` |
| `RPi5Platform` binding | `Platform/RPi5/*` | BCM2712 hardware stubs ready for H3 population |
| `ExtendedBootBoundaryContract` | `Architecture/Assumptions.lean` | ARM64-specific boot parameters for H3 execution |
| Boundary contract consumers | `Platform/Sim/*`, `Platform/RPi5/*` | Closes F-19 (stubs without consumers) |
| Platform Binding ADR | `docs/PLATFORM_BINDING_ADR.md` | Documents monorepo-over-fork decision and import boundaries |
