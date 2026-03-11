# WS-F Workstream Plan — v0.12.2 Audit Remediation

**Created:** 2026-02-28
**Last updated:** 2026-03-11 (WS-F6 completion — invariant quality)
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

### WS-F5: Model Fidelity (MEDIUM)

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

### WS-F6: Invariant Quality (MEDIUM) — **COMPLETED** (v0.14.9)

**Objective:** Strengthen the invariant surface, eliminate tautological predicates
from state-invariant bundles, close scheduler/IPC/VSpace architectural gaps, and
discharge all assumed invariant predicates. Every change must strengthen the
security posture of the proof surface without introducing `sorry` or `axiom`.

**Enabling infrastructure (delivered by PR #290):**
- `PlatformBinding` typeclass with `RuntimeBoundaryContract` field provides the
  concrete pathway for `AdapterProofHooks` instantiation: platform bindings (Sim,
  RPi5) supply decidable contract predicates that can be threaded into the hooks.
- `VSpaceBackend` typeclass with per-operation ASID preservation proofs
  (`mapPage_preserves_asid`, `unmapPage_preserves_asid`) and round-trip correctness
  obligations. `listVSpaceBackend` instance demonstrates the current flat-list model
  satisfies these obligations. Cross-ASID *isolation* (operations on one ASID root
  do not affect another) remains a deliverable.

**Prior work (already delivered, no longer in scope):**
- ~~Instantiate `AdapterProofHooks` with concrete proof~~: Delivered in WS-H15d (v0.14.7).
  `simRestrictiveAdapterProofHooks` instantiates all three proof obligations for the
  Sim restrictive contract. End-to-end theorems proved for timer/register/memory
  adapter paths. Permissive contract cannot satisfy `contextMatchesCurrent`
  obligation (documented limitation in `Platform/Sim/ProofHooks.lean`).
- ~~`blockedOnReply` coverage in `ipcSchedulerContractPredicates`~~: Already covered
  by `blockedOnReplyNotRunnable` since WS-H1 (v0.12.16). The 5-predicate bundle
  includes `blockedOnCallNotRunnable` and `blockedOnReplyNotRunnable`.

**Deliverables (7):**

#### F6-D1: Reclassify Tautological Invariants (MED-01 / F-07 / F-15)

**Problem:** Three predicates in state-invariant bundles are not state invariants:
`cspaceAttenuationRule` (operation property, no `st` parameter),
`lifecycleAuthorityMonotonicity` (operation-correctness — asserts what delete/revoke
must achieve, not a state property preserved through transitions), and
`lifecycleIdentityNoTypeAliasConflict` (structural tautology — same lookup cannot
return two different values). Their presence inflates the capability invariant bundle
from 6 meaningful predicates to 8, and every preservation theorem must carry these
trivially-true obligations as dead weight.

**Security rationale:** Tautological predicates in invariant bundles weaken audit
assurance by creating a false impression of proof density. Reclassification
concentrates the bundle on genuine security properties, making the proof surface
more honest and auditable.

**Implementation plan:**

- **F6-D1a: Move `cspaceAttenuationRule` to operation-specification section.**
  In `Capability/Invariant/Defs.lean`, remove `cspaceAttenuationRule` from the
  `capabilityInvariantBundle` conjunction. Retain the definition and its proof
  (`cspaceAttenuationRule_holds`) in a clearly labeled "Operation Correctness
  Lemmas" section. Add a `cspaceAttenuationRule_holds` standalone theorem if
  not already present. Update the bundle docstring to reflect the 6-tuple
  (removing the "8-tuple" reference).

- **F6-D1b: Move `lifecycleAuthorityMonotonicity` to operation-specification section.**
  Remove from `capabilityInvariantBundle`. Retain the definition, `_holds` proof,
  and the `lifecycleCapabilityStaleAuthorityInvariant` bridge (which uses it) in
  a separate section. Update all extraction theorems that index into the bundle
  tuple (`.2.2.2.2.1` etc.) to use the new 6-tuple layout.

- **F6-D1c: Reclassify `lifecycleIdentityNoTypeAliasConflict`.**
  This is proved from `lifecycleIdentityTypeExact` via
  `lifecycleIdentityNoTypeAliasConflict_of_exact`. Move the standalone definition
  to a "Structural Lemmas" section in `Lifecycle/Invariant.lean`. The
  `lifecycleIdentityAliasingInvariant` bundle keeps `lifecycleIdentityTypeExact`
  as its sole conjunct (since `NoTypeAliasConflict` is derivable from it). Update
  `lifecycleInvariantBundle` accordingly.

- **F6-D1d: Update all downstream bundle references.**
  Update `capabilityInvariantBundle` extraction theorems, all `_preserves_capabilityInvariantBundle`
  theorems across IPC/Lifecycle/Service modules, and composed bundles
  (`coreIpcInvariantBundle`, `proofLayerInvariantBundle`). The removal of two
  conjuncts from the 8-tuple simplifies every preservation proof that currently
  carries `hAttRule` and `lifecycleAuthorityMonotonicity_holds _` obligations.

- **F6-D1e: Update Tier 3 anchor checks.**
  Update `test_tier3_invariant_surface.sh` to check for the reclassified locations
  and new bundle arity. Add anchors for the "Operation Correctness Lemmas" section.

#### F6-D2: Extend IPC-Scheduler Contract with Notification Blocking (HIGH-03)

**Problem:** `ipcSchedulerContractPredicates` covers 5 blocking states (ready,
blockedOnSend, blockedOnReceive, blockedOnCall, blockedOnReply) but omits
`blockedOnNotification`. A thread calling `notificationWait` transitions to
`ipcState = .blockedOnNotification oid` and is removed from the run queue, but
no contract predicate asserts this exclusion. Without it, a scheduler bug could
leave a notification-blocked thread in the runnable queue, violating temporal
isolation.

**Security rationale:** An unreachable thread that remains runnable can execute
despite being logically blocked, breaking information-flow non-interference. The
`notificationWaiterConsistent` predicate (WS-G7) couples waitlist membership to
ipcState but does not assert non-runnability. This gap must be closed.

**Implementation plan:**

- **F6-D2a: Define `blockedOnNotificationNotRunnable` predicate.**
  In `IPC/Invariant/Defs.lean`, add:
  ```
  def blockedOnNotificationNotRunnable (st : SystemState) : Prop :=
    ∀ (tid : ThreadId) tcb oid,
      st.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.ipcState = .blockedOnNotification oid →
      tid ∉ st.scheduler.runnable
  ```

- **F6-D2b: Extend `ipcSchedulerContractPredicates` to 6-tuple.**
  Add `blockedOnNotificationNotRunnable` as the 6th conjunct. Update the bundle
  definition and all extraction/construction sites.

- **F6-D2c: Prove preservation through notification operations.**
  Prove `notificationWait_preserves_blockedOnNotificationNotRunnable` and
  `notificationSignal_preserves_blockedOnNotificationNotRunnable`. The wait path
  calls `removeRunnable` before setting ipcState; the signal wake path calls
  `ensureRunnable` after setting ipcState to `.ready`.

- **F6-D2d: Prove preservation through non-notification operations.**
  Prove preservation through `endpointSendDual`, `endpointReceiveDual`,
  `schedule`, `handleYield`, `timerTick`, `cspaceMint`, `cspaceMutate`,
  `lifecycleRetypeObject`, and service operations. Most follow from
  scheduler-unchanged or ipcState-unchanged frame lemmas.

- **F6-D2e: Update composed bundles and Tier 3 anchors.**
  Update `ipcSchedulerCoherenceComponent` to include the new predicate.
  Add Tier 3 anchor for `blockedOnNotificationNotRunnable`.

#### F6-D3: Add `runnableThreadsAreTCBs` Invariant (MED-06)

**Problem:** No invariant asserts that every thread ID in the scheduler's runnable
queue corresponds to a valid TCB in the object store. Only `currentThreadValid`
covers the *current* thread. A lifecycle `retypeObject` that overwrites a TCB with
a non-TCB object while leaving the thread ID in the run queue would violate this
property silently.

**Security rationale:** If a non-TCB object ID is in the run queue, `chooseThread`
will select it and attempt to read TCB fields from a non-TCB object, producing
undefined behavior in a production kernel. This invariant is a type-safety
backstop for the scheduler.

**Implementation plan:**

- **F6-D3a: Define `runnableThreadsAreTCBs` predicate.**
  In `Scheduler/Invariant.lean`, add:
  ```
  def runnableThreadsAreTCBs (st : SystemState) : Prop :=
    ∀ tid, tid ∈ st.scheduler.runnable →
      ∃ tcb : TCB, st.objects[tid.toObjId]? = some (.tcb tcb)
  ```

- **F6-D3b: Prove default-state satisfaction.**
  Prove `default_runnableThreadsAreTCBs`: the default `SystemState` has an empty
  run queue, so the predicate is vacuously true.

- **F6-D3c: Prove preservation through scheduler operations.**
  `ensureRunnable` only adds a thread after verifying TCB lookup succeeds.
  `removeRunnable` only removes threads. `chooseThread`/`schedule` use
  `removeRunnable` + `ensureRunnable` patterns. Prove preservation for
  `schedule`, `handleYield`, `timerTick`.

- **F6-D3d: Prove preservation through IPC operations.**
  IPC operations that modify the run queue (`endpointSendDual`, `endpointReceiveDual`,
  `notificationSignal`, `notificationWait`) use `ensureRunnable`/`removeRunnable`
  and `storeObject` (which does not modify the scheduler). Prove frame preservation
  through `storeObject` (TCBs at other ObjIds are unchanged).

- **F6-D3e: Add to `schedulerInvariantBundleFull` and Tier 3 anchors.**
  Extend `schedulerInvariantBundleFull` from 5-tuple to 6-tuple. Update all
  extraction and composition theorems. Add Tier 3 surface anchor.

#### F6-D4: Discharge `serviceCountBounded` (HIGH-06)

**Problem:** `serviceCountBounded` is used as a precondition for
`bfs_complete_for_nontrivialPath` and
`serviceRegisterDependency_preserves_acyclicity`. It asserts that a BFS traversal
universe exists within the fuel budget. Currently, callers must assume it; it is
not proved from first principles or preserved through state transitions.

**Security rationale:** Without a proof that `serviceCountBounded` holds for all
reachable states, the acyclicity guarantee for the service dependency graph is
conditional. An adversary who could register enough services to exceed the fuel
budget could bypass the cycle detection, creating a circular dependency that causes
the kernel to loop on service startup.

**Implementation plan:**

- **F6-D4a: Prove `serviceCountBounded` for initial/default state.**
  The default state has an empty services HashMap, so the predicate holds with
  `ns := []`. Prove `default_serviceCountBounded`.

- **F6-D4b: Prove preservation through `storeServiceState`.**
  `storeServiceState` modifies a service entry's status but does not add/remove
  service registrations. The existing `serviceCountBounded_of_storeServiceState_sameDeps`
  theorem handles this case. Verify it composes cleanly with `serviceStart`,
  `serviceStop`, and `serviceRestart`.

- **F6-D4c: Prove preservation through `serviceRegisterDependency`.**
  `serviceRegisterDependency` adds edges but does not add service registrations.
  The BFS universe (`bfsUniverse`) is service-node based. Prove that edge
  insertion does not invalidate the universe.

- **F6-D4d: Prove construction from finite `services` HashMap.**
  The `services` field is `Std.HashMap ServiceId ServiceGraphEntry`. Prove
  that `services.toList.map (·.1)` satisfies `bfsUniverse` and has length
  bounded by `serviceBfsFuel`. This gives a constructive proof for any state
  with a finite services map.

#### F6-D5: Scheduler Invariant Preservation for `schedule` (MED-05)

**Problem:** `timeSlicePositive` and `edfCurrentHasEarliestDeadline` preservation
through `schedule` must be explicitly proved. While WS-H6 defined these invariants
and proved them for basic cases, the `schedule` transition (which selects a new
thread via `chooseThread` and sets `current`) is the critical path.

**Security rationale:** If `timeSlicePositive` is not preserved through scheduling,
a zero-timeslice thread could be scheduled indefinitely (starvation attack). If
`edfCurrentHasEarliestDeadline` is not preserved, a later-deadline thread could
preempt an earlier one (temporal isolation violation).

**Implementation plan:**

- **F6-D5a: Verify existing `schedule_preserves_schedulerInvariantBundleFull`.**
  Check that the existing preservation theorem for `schedulerInvariantBundleFull`
  includes `timeSlicePositive` and `edfCurrentHasEarliestDeadline`. If only the
  base triad is covered, extend the proof.

- **F6-D5b: Prove `schedule_preserves_timeSlicePositive`.**
  `schedule` calls `chooseThread` which selects the best runnable thread and
  removes it from the queue via `removeRunnable`. The removed thread's timeslice
  remains positive (it was in the queue, covered by pre-state `timeSlicePositive`).
  Remaining queue threads are a subset, so their timeslices remain positive.

- **F6-D5c: Prove `schedule_preserves_edfCurrentHasEarliestDeadline`.**
  `chooseThread` selects via `chooseBestRunnableInDomain`, which picks the thread
  with the earliest deadline in the active domain at the highest priority. After
  removal and promotion to current, the remaining queue threads have later-or-equal
  deadlines by selection semantics.

#### F6-D6: VSpace Cross-ASID Isolation Theorem (MED-07)

**Problem:** Per-operation ASID preservation is proved (`mapPage_preserves_asid`,
`unmapPage_preserves_asid` in `VSpaceBackend`), but the stronger cross-root
non-interference property is not: "operations on VSpaceRoot A do not modify the
mappings or ASID of VSpaceRoot B (B ≠ A)." Without this, a compromised VSpace
could theoretically affect another address space's translations.

**Security rationale:** Cross-ASID isolation is the memory-safety foundation of
process separation. It is the VSpace analog of non-interference: operations
within one address space must not be observable in another. This is a prerequisite
for the RPi5 hardware binding, where page table walks for different processes must
be provably independent.

**Implementation plan:**

- **F6-D6a: Define `vspaceCrossAsidIsolation` predicate.**
  In `Architecture/VSpaceInvariant.lean`, add:
  ```
  def vspaceCrossAsidIsolation (st : SystemState) : Prop :=
    ∀ (oidA oidB : ObjId) (rootA rootB : VSpaceRoot),
      st.objects[oidA]? = some (.vspaceRoot rootA) →
      st.objects[oidB]? = some (.vspaceRoot rootB) →
      oidA ≠ oidB →
      rootA.asid ≠ rootB.asid
  ```
  This expresses ASID uniqueness across distinct VSpaceRoot objects, which
  combined with `vspaceAsidRootsUnique` gives full cross-root isolation.

- **F6-D6b: Prove `vspaceMapPage_preserves_crossAsidIsolation`.**
  `vspaceMapPage` modifies exactly one VSpaceRoot (looked up by ASID). Prove
  that other VSpaceRoot objects are unchanged via `storeObject_objects_ne`,
  and the modified root's ASID is preserved via `root'.asid = root.asid`.

- **F6-D6c: Prove `vspaceUnmapPage_preserves_crossAsidIsolation`.**
  Same structure as D6b: the unmap modifies one root, preserving its ASID.

- **F6-D6d: Add to `vspaceInvariantBundle` and Tier 3 anchors.**
  Extend `vspaceInvariantBundle` from 5-tuple to 6-tuple with
  `vspaceCrossAsidIsolation`. Update all preservation theorems. Add anchor.

#### F6-D7: Invariant Bundle Coherence and Integration

**Problem:** After D1-D6, the invariant bundle structure has changed. All composed
bundles must be updated, and the default-state satisfaction theorem must be
reproved.

- **F6-D7a: Update `proofLayerInvariantBundle` composition.**
  Verify that the composed bundle correctly includes all updated sub-bundles.

- **F6-D7b: Reprove `default_system_state_proofLayerInvariantBundle`.**
  With new invariant predicates added, prove the default (empty) state still
  satisfies the full composed bundle.

- **F6-D7c: Update `AdapterProofHooks` preservation theorems.**
  Timer/register/memory adapter paths must preserve the expanded bundles.
  Since these operations do not modify the object store or scheduler, new
  predicates (which quantify over objects/scheduler) are trivially preserved.

- **F6-D7d: Run `test_full.sh` and fix any regressions.**
  Verify Tier 0-3 pass. Update `test_tier3_invariant_surface.sh` with new
  anchors for all reclassified and added invariants.

**Exit evidence:**
- `lake build` passes with zero errors/warnings.
- `test_full.sh` passes (Tier 0-3) with updated Tier 3 surface anchors.
- Zero `sorry` or `axiom` in production proof surface.
- `capabilityInvariantBundle` reduced from 8-tuple to 6-tuple (tautologies removed).
- `ipcSchedulerContractPredicates` extended to 6-tuple (notification blocking).
- `runnableThreadsAreTCBs` defined and preservation proven for all scheduler-affecting operations.
- `serviceCountBounded` discharged with constructive proof from finite `services` map.
- `vspaceCrossAsidIsolation` defined and preservation proven for `mapPage`/`unmapPage`.
- `schedulerInvariantBundleFull` extended to 6-tuple with `runnableThreadsAreTCBs`.
- All existing tests pass, updated fixture if trace output changes.
- No tautological predicates remain in state-invariant bundles.

**Dependencies:** WS-F4 (proof gap closure provides foundation — completed).
WS-F5 (model fidelity — completed). H3-prep infrastructure (PR #290) provides
the platform binding pathway (delivered). WS-H15d provided `AdapterProofHooks`
instantiation (delivered).

### WS-F7: Testing Expansion (LOW)

**Objective:** Strengthen runtime validation and close residual testing gaps
identified by the v0.12.2 audit (MED-08, F-24, F-25, F-26). Every new runtime
check must be machine-exercised by at least one trace or probe scenario. Zero
`sorry`/`axiom` in production proof surface.

**Deliverables — broken into implementation units:**

#### D1: Invariant Oracle Expansion (`InvariantChecks.lean`)

Add four new runtime invariant check families to the existing
`stateInvariantChecksFor` oracle. Each check strengthens the scheduler/IPC
contract and catches violations that formal proofs alone cannot exercise at
runtime.

| Check | Semantic | Security Rationale |
|-------|----------|-------------------|
| `blockedOnSendNotRunnable` | Every thread with `ipcState = .blockedOnSend ep` must NOT appear in the runnable list. | Prevents scheduler from dispatching a thread that is logically blocked, which could cause message duplication or ordering violations. |
| `blockedOnReceiveNotRunnable` | Every thread with `ipcState = .blockedOnReceive ep` must NOT appear in the runnable list. | Same as above for the receive path — a blocked receiver dispatched prematurely could observe partial state. |
| `currentThreadInActiveDomain` | If `scheduler.current = some tid`, then the TCB for `tid` must have `domain = scheduler.activeDomain`. | Enforces domain-based temporal isolation. A current thread outside the active domain violates the scheduling invariant that only threads in the active domain are eligible for dispatch. |
| `uniqueWaiters` | No `ThreadId` appears in more than one notification `waitingThreads` list across all notification objects. | Prevents double-wake: if a thread is on two waiting lists, a single signal could corrupt both notification objects' state machines. |

**Implementation steps:**
- D1a: Add `blockedOnSendNotRunnable` and `blockedOnReceiveNotRunnable` checks
  that iterate all objects, find TCBs with blocking IPC states, and verify
  absence from `scheduler.runnable`.
- D1b: Add `currentThreadInActiveDomain` check that verifies the current
  thread's TCB domain matches `scheduler.activeDomain`.
- D1c: Add `uniqueWaiters` check that collects all notification waiting lists
  and verifies no `ThreadId` appears more than once across all lists.
- D1d: Wire all four checks into `stateInvariantChecksFor` so they run on
  every assertion point in MainTraceHarness, NegativeStateSuite, and
  TraceSequenceProbe.

#### D2: TraceSequenceProbe Expansion (`tests/TraceSequenceProbe.lean`)

Extend the randomized probe from 3 operations (send, awaitReceive, receive) to
cover notification, scheduler, and capability operation families. This closes
F-26 (probe covers only 3 ops).

| Operation Family | New ProbeOps | Kernel Function |
|-----------------|-------------|-----------------|
| Notification | `notifySignal`, `notifyWait` | `notificationSignal`, `notificationWait` |
| Scheduler | `scheduleOp` | `schedule` |
| Capability | `capLookup` | `cspaceLookupSlot` |

**Implementation steps:**
- D2a: Add a notification object to the probe base state at a fixed `ObjId`.
- D2b: Add `ProbeOp` variants: `notifySignal`, `notifyWait`, `scheduleOp`,
  `capLookup`.
- D2c: Add a CNode with per-thread capability slots to the probe base state
  for `capLookup`.
- D2d: Implement `stepOp` cases for each new operation with appropriate error
  classification (expected vs unexpected failures).
- D2e: Update `pickOp` to distribute across 7 operations (was 3).
- D2f: Verify that `probeInvariantObjectIds` includes the new notification
  and CNode objects.

#### D3: Runtime Contract Fixture Exercise (`MainTraceHarness.lean`)

Exercise the `runtimeContractTimerOnly` and `runtimeContractReadOnlyMemory`
fixtures with explicit trace scenarios that verify the expected
success/denied branch combinations. This closes F-25 (unused fixtures).

**Implementation steps:**
- D3a: Add `runRuntimeContractFixtureTrace` function that:
  - Calls adapter timer with `runtimeContractTimerOnly` → expects success.
  - Calls adapter register with `runtimeContractTimerOnly` → expects denied.
  - Calls adapter memory with `runtimeContractReadOnlyMemory` → expects success.
  - Calls adapter timer with `runtimeContractReadOnlyMemory` → expects denied.
- D3b: Add corresponding expected output lines to
  `tests/fixtures/main_trace_smoke.expected`.
- D3c: Wire `runRuntimeContractFixtureTrace` into `runMainTraceFrom`.

#### D4: CDT Structural Integrity (already delivered)

The `cdtChildMapConsistentCheck` in `InvariantChecks.lean` (lines 210-223)
already validates bidirectional consistency between `childMap` and `edges`.
This deliverable is **closed** — it was delivered during WS-G audit
remediation. No additional work required.

**Exit evidence:**
- `lake build` passes with zero errors and zero warnings.
- `test_smoke.sh` passes (Tier 0-2).
- `test_full.sh` passes (Tier 0-3) — invariant surface anchors updated.
- All four new invariant checks exercise at least one violation-free and one
  structurally correct scenario.
- TraceSequenceProbe exercises 7 operation families (was 3).
- Runtime contract fixtures produce deterministic trace output matched by
  fixture comparison.
- Zero `sorry` or `axiom` in production proof surface.
- Documentation synchronized: WORKSTREAM_HISTORY, CLAIM_EVIDENCE_INDEX,
  DEVELOPMENT.md, GitBook chapters.

**Dependencies:** WS-F1 (dual-queue operations — completed). WS-F6 (invariant
quality — completed). All dependencies satisfied.

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
| **P3** | WS-F5, WS-F6 | Model fidelity + invariant quality | **Done** |
| **P4** | WS-F7, WS-F8 | Testing expansion + cleanup | WS-F7 **Done**, WS-F8 Planning |

**Phase notes:**
- P0–P3 are complete. All CRITICAL, HIGH, and targeted MEDIUM findings from P1–P3 are closed.
- H3-prep (PR #290) was executed between P2 and P3 as cross-cutting infrastructure.
  It is not a numbered workstream but delivers enabling assets: the `PlatformBinding`
  typeclass, `VSpaceBackend` abstraction, and concrete platform bindings that P3
  deliverables depend on. It also closed F-19 (stub declarations) ahead of P4/WS-F8.
- P4 can now leverage H3-prep platform binding infrastructure and WS-F6 invariant quality improvements.

---

## 6. Status Dashboard

| Workstream | Priority | Status | Findings addressed |
|------------|----------|--------|-------------------|
| WS-F1 | Critical | **Completed** | CRIT-01, CRIT-05, F-10, F-11 |
| WS-F2 | Critical | **Completed** | CRIT-04 |
| WS-F3 | High | **Completed** | CRIT-02, CRIT-03, F-20, F-21, F-22 |
| WS-F4 | High | **Completed** | F-03, F-06, F-12 |
| WS-F5 | Medium | **Completed** | CRIT-06, ~~HIGH-01~~ (WS-H13), ~~HIGH-02~~ (WS-H12c), HIGH-04, MED-03 |
| WS-F6 | Medium | **Completed** | HIGH-03, ~~HIGH-05~~ (WS-H5), HIGH-06, ~~HIGH-07~~ (WS-H9), ~~HIGH-08~~ (WS-H15d), MED-01, MED-02, MED-05, MED-06, MED-07, F-07, F-13, F-15, ~~F-18~~ (WS-H15d) |
| WS-F7 | Low | **Completed** | MED-08, F-24, F-25, F-26 |
| WS-F8 | Low | Planning (F-19 closed) | MED-04, MED-17, F-01, F-14, ~~F-19~~ |

**Aggregate finding closure (by matrix row):**
- **Closed:** 6 CRITICAL (CRIT-01, CRIT-04, CRIT-05 by WS-F1/F2; CRIT-02, CRIT-03 by WS-F3; CRIT-06 by WS-F5), 10 HIGH (F-11 by WS-F1; F-03, F-06, F-12 by WS-F4; HIGH-01 by WS-H13; HIGH-02 by WS-H12c; HIGH-03, HIGH-06 by WS-F6; HIGH-05 by WS-H5; HIGH-04 by WS-F5; HIGH-07 by WS-H9; HIGH-08/F-18 by WS-H15d), 8 MEDIUM (MED-01, MED-02, MED-05, MED-06, MED-07 by WS-F6; MED-03 by WS-F5; MED-08 by WS-F7; F-07, F-13, F-15 by WS-F6), 4 LOW (F-19 by PR #290; F-24, F-25, F-26 by WS-F7) = **28 of 33**
- **Open:** 0 CRITICAL, 0 HIGH, 2 MEDIUM (MED-04, MED-17), 3 LOW (F-01, F-14) = **5 of 33** (WS-F8 only)

### Cross-cutting: H3-prep Platform Binding (PR #290)

PR #290 delivered foundational infrastructure between P2 and P3. While not a
numbered workstream, it has material impact on remaining work:

| Asset | Location | Impact |
|-------|----------|--------|
| `PlatformBinding` typeclass | `Platform/Contract.lean` | Enabled WS-H15d AdapterProofHooks instantiation (completed) |
| `MachineConfig` + `MemoryRegion` + `wellFormed` | `Machine.lean` | Provides hardware parameter vocabulary for WS-F5 model fidelity |
| `VSpaceBackend` + `listVSpaceBackend` | `Architecture/VSpaceBackend.lean` | Per-operation ASID preservation proved; cross-ASID isolation remains WS-F6 |
| `SimPlatform` binding | `Platform/Sim/*` | Permissive contract provides natural first target for `AdapterProofHooks` |
| `RPi5Platform` binding | `Platform/RPi5/*` | BCM2712 hardware stubs ready for H3 population |
| `ExtendedBootBoundaryContract` | `Architecture/Assumptions.lean` | ARM64-specific boot parameters for H3 execution |
| Boundary contract consumers | `Platform/Sim/*`, `Platform/RPi5/*` | Closes F-19 (stubs without consumers) |
| Platform Binding ADR | `docs/PLATFORM_BINDING_ADR.md` | Documents monorepo-over-fork decision and import boundaries |
