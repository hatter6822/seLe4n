# WS-AE Workstream Plan — Comprehensive Audit Remediation (v0.25.14)

**Created**: 2026-04-06
**Baseline version**: 0.25.14
**Baseline audits**:
  - `docs/audits/AUDIT_v0.25.14_COMPREHENSIVE.md` (88 findings)
  - `docs/audits/AUDIT_v0.25.12_KERNEL_MODULES.md` (166+ findings)
**Prior portfolios**: WS-B through WS-AD (all COMPLETE — see `docs/WORKSTREAM_HISTORY.md`)
**Constraint**: Zero `sorry`/`axiom` in production proof surface

---

## 1. Executive Summary

Two comprehensive audits of seLe4n v0.25.12–v0.25.14 were conducted on
2026-04-06, covering all 150 Lean modules (~45,000+ lines), 30 Rust ABI
files, test infrastructure, and CI/build system. Both audits were
independently verified against source code — all findings confirmed
accurate with exact line references (3 erroneous findings in v0.25.14
were already removed by the audit itself; IPC-01 dual-condition check
mitigates the stated risk more than originally characterized).

**Combined verified finding counts (after deduplication)**:

| Severity | v0.25.14 | v0.25.12 | Deduplicated Total | Actionable |
|----------|----------|----------|--------------------|------------|
| HIGH     | 4        | 6        | 8                  | 8          |
| MEDIUM   | 20       | 38       | 37                 | 27         |
| LOW      | 39       | 50       | 53                 | 22         |
| INFO     | 25       | 72+      | 72+                | 0          |

### 1.1 Deduplication Analysis

Many findings appear in both audits with different IDs. The following
cross-references were established:

| v0.25.14 ID | v0.25.12 ID | Unified ID | Notes |
|-------------|-------------|------------|-------|
| F-01        | —           | U-01       | Unique to v0.25.14 |
| F-02        | —           | U-02       | Unique to v0.25.14 |
| IF-01       | —           | U-03       | Unique to v0.25.14 |
| IF-02       | —           | U-04       | Unique to v0.25.14 |
| F-03        | —           | U-05       | Unique to v0.25.14 |
| F-04        | —           | U-06       | Unique to v0.25.14 |
| F-05        | —           | U-07       | Unique to v0.25.14 |
| IF-03       | IF-13       | U-08       | v0.25.12 also notes one-sided NI proof |
| IF-04       | IF-02(v12)  | U-09       | v0.25.12 HIGH → v0.25.14 LOW |
| IF-06       | IF-04(v12)  | U-10       | Both identify projection gap |
| S-02        | —           | U-11       | Unique to v0.25.14 |
| SC-01       | SC-02(v12)  | U-12       | Both identify CBS 8x bound |
| SC-02       | —           | U-13       | Unique to v0.25.14 |
| SC-03       | SC-L04(v12) | U-14       | Both identify reconfigure gap |
| SC-04       | —           | U-15       | Unique to v0.25.14 |
| SC-05       | SC-L06(v12) | U-16       | Both identify resumeThread priority |
| CAP-01      | —           | U-17       | Unique to v0.25.14 |
| CAP-02      | C-CAP07(v12)| U-18       | Both identify CDT acyclicity gap |
| SVC-01      | SC-L07(v12) | U-19       | Both identify serviceHasPathTo |
| SVC-02      | —           | U-20       | Unique to v0.25.14 |
| PLT-01      | —           | U-21       | Unique to v0.25.14 |
| PLT-02      | CS-01(v12)  | U-22       | Both identify fuel exhaustion |
| IPC-01      | I-T01(v12)  | U-23       | Both identify sentinel value |
| IPC-02      | —           | U-24       | Unique to v0.25.14 |
| T-06        | T-F01(v12)  | U-25       | Both identify PIP suite not executed |
| ARCH-03     | A-SA01(v12) | U-26       | v0.25.12 HIGH → v0.25.14 LOW |
| —           | A-T01(v12)  | U-27       | TLB flush — unique to v0.25.12 |
| —           | D-RH01(v12) | U-28       | RobinHood capacity — unique to v0.25.12 |
| —           | D-RT01(v12) | U-29       | RadixTree precondition — unique to v0.25.12 |
| —           | D-RH02(v12) | U-30       | RobinHood fuel exhaustion defaults |
| —           | D-FO01(v12) | U-31       | FrozenOps partial mutation |
| —           | A-IB01(v12) | U-32       | IPC buffer cross-page |
| —           | A-SA02(v12) | U-33       | Slot.ofNat silent accept |
| —           | A-SA03(v12) | U-34       | AccessRightSet silent mask |
| —           | C-CAP01(v12)| U-35       | CSpace traversal rights |
| —           | C-CAP06(v12)| U-36       | cdtMintCompleteness not in bundle |
| —           | I-WC01(v12) | U-37       | Cap transfer slot-0-only |

### 1.2 Erroneous/Downgraded Findings (No Action Required)

| ID | Status | Reason |
|----|--------|--------|
| IF-05 (v0.25.14) | REMOVED | Erroneous — separate `confidentialityFlowsTo`/`integrityFlowsTo` predicates already exist with distinct orderings |
| IPC-01 / I-T01 | DOWNGRADED | Dual-condition check (register AND state) substantially mitigates false positives; recommend documentation rather than code change |
| S-01 (v0.25.14) | DOWNGRADED | LOW — `updatePipBoost` only modifies `pipBoost`, never `ipcState`; functionally equivalent |
| IF-04 (v0.25.14) | DOWNGRADED | LOW — by-design default with `defaultLabelingContext_insecure` witness |

### 1.3 Plan Structure

This plan organizes all actionable findings into **6 phases** (AE1–AE6) with
**55 top-level sub-tasks** (73 atomic units after decomposition of complex
tasks), explicit dependencies, gate conditions, and scope estimates. Phases are ordered by severity impact and dependency chain:

| Phase | Focus | Sub-tasks | Findings | Gate |
|-------|-------|-----------|----------|------|
| AE1 | Critical: API dispatch & NI composition | 8 top-level (15 atomic) | F-01, F-04, F-05, IF-01, IF-02, IF-03 | `lake build` + `test_smoke.sh` |
| AE2 | Data structure hardening | 8 | D-RH01, D-RT01, D-RH02, D-FO01, F-02, F-03 | `lake build` + module verification |
| AE3 | Scheduler & SchedContext correctness | 12 top-level (15 atomic) | S-02, SC-01–SC-05, SC-06, SC-07, SC-09, S-03, S-05 | `lake build` + `test_smoke.sh` |
| AE4 | Capability, IPC & architecture hardening | 10 top-level (20 atomic) | CAP-01, CAP-02, IPC-02, ARCH-03, A-IB01, I-WC01, C-CAP06 | `lake build` + `test_full.sh` |
| AE5 | Platform, service & cross-subsystem | 7 | PLT-01, PLT-02, SVC-02, SVC-04, IF-06, IF-04, PLT-04 | `lake build` + `test_full.sh` |
| AE6 | Testing, documentation & closure | 8 | T-06, T-07, T-F02–03, T-F05, T-F17, doc sync | `test_full.sh` + doc sync |

**Estimated scope**: ~995–1,345 total lines of changes (worst case with all
risks: ~1,495–1,665). See Section 10 for per-phase breakdown.


---

## 2. Consolidated Finding Registry

### 2.1 HIGH Findings (8 actionable)

| Unified ID | Source | Subsystem | Description | Verified | Phase |
|------------|--------|-----------|-------------|----------|-------|
| U-01 | F-01 (v14) | Kernel/API | `dispatchWithCapChecked` missing `.tcbSetPriority` and `.tcbSetMCPriority` arms — both fall to wildcard `.illegalState` error. Unchecked `dispatchWithCap` handles them correctly (lines 731–757). Root cause: D2 arms added to unchecked path but not checked path or shared helper. | YES — API.lean:802–989 | AE1 |
| U-02 | F-02 (v14) | FrozenOps | 4 production-quality modules (Core, Operations, Commutativity, Invariant) with proofs unreachable from production import chain. Only imported by test suites. | YES — zero production imports | AE2 |
| U-03 | IF-01 (v14) | InformationFlow | `switchDomain` missing from `NonInterferenceStep` inductive (32 constructors, none for domain switch). Per-step theorem `switchDomain_preserves_lowEquivalent` exists in Operations.lean:580–596 but is not wired into composition. | YES — Composition.lean:34–308 | AE1 |
| U-04 | IF-02 (v14) | InformationFlow | PIP/donation mutations in call/reply arms occur AFTER the IPC operation that NI constructors cover. `applyCallDonation`/`propagatePriorityInheritance` (API.lean:845–855) and `applyReplyDonation`/`revertPriorityInheritance` (API.lean:869–873) are outside the NI proof envelope. | YES — Composition.lean:183–202, 157–162 | AE1 |
| U-25 | T-06/T-F01 | Testing | `priority_inheritance_suite` compiled (lakefile.toml:75–78) but never executed in any test script. D4 PIP tests are dead — gap between D3 and D5 in test_tier2_negative.sh. | YES — zero script matches | AE6 |
| U-26 | ARCH-03/A-SA01 | Architecture | `decodeVSpaceUnmapArgs` does not validate VAddr canonical (line 237) while `decodeVSpaceMapArgs` does (line 213). Non-canonical VAddr fails safely via `.translationFault`. Defense-in-depth gap. | YES — SyscallArgDecode.lean:228–237 | AE4 |
| U-28 | D-RH01 (v12) | RobinHood | `RHTable.empty` accepts any `cap > 0` (Core.lean:90–96). `insert_size_lt_capacity` requires `4 ≤ capacity` (Bridge.lean:361). `invExt` (Preservation.lean:447) lacks the constraint; `invExtK` (Bridge.lean:858) includes it. Tables with capacity 1–3 bypass the insert-size guard. | YES — all four locations confirmed | AE2 |
| U-29 | D-RT01 (v12) | RadixTree | `buildCNodeRadix_lookup_equiv` requires `UniqueRadixIndices` + `hNoPhantom` (Bridge.lean:317–324) as caller-side proof obligations not enforced by the type system. `uniqueRadixIndices_sufficient` (line 420) shows automatic discharge for bounded keys, but base theorem has no enforcement. | YES — Bridge.lean:309–324 | AE2 |

### 2.2 MEDIUM Findings (27 actionable + 3 deferred, after deduplication)

| Unified ID | Source | Subsystem | Description | Phase |
|------------|--------|-----------|-------------|-------|
| U-05 | F-03 (v14) | Scheduler/Liveness | 7+1 Liveness files unreachable from production import chain. WCRT bounded latency theorem and all liveness proofs are test-only. | AE2 |
| U-06 | F-04 (v14) | Kernel/API | `.tcbSetIPCBuffer` duplicated in both dispatch paths instead of routed through `dispatchCapabilityOnly`. Same pattern that caused U-01. | AE1 |
| U-07 | F-05 (v14) | Kernel/API | Wildcard unreachability comment at line 987 is incorrect for `dispatchWithCapChecked`. No `dispatchWithCapChecked_wildcard_unreachable` theorem exists. | AE1 |
| U-08 | IF-03/IF-13 | InformationFlow | `NonInterferenceStep` proves per-operation NI. `syscallDispatchHigh` bridges via `hProj` hypothesis — gap between per-op NI and full dispatch NI is bridged by assumption, not proof. | AE1 |
| U-10 | IF-06/IF-04(v12) | InformationFlow | Service orchestration internals (lifecycle, restart, heartbeat) outside NI projection boundary. Documented by `serviceOrchestrationOutsideNiBoundary` theorem. | AE5 |
| U-11 | S-02 (v14) | Scheduler | Domain filter uses `tcb.domain` but effective priority uses `sc.domain` (Selection.lean:363). Bound threads may pass domain filter by TCB domain but be prioritized by SchedContext domain. | AE3 |
| U-12 | SC-01/SC-02(v12) | SchedContext | CBS bandwidth bound proves 8×budget per window (maxReplenishments=8), not budget per period. Admission control not formally connected to bound theorem. | AE3 |
| U-13 | SC-02 (v14) | SchedContext | Admission control per-mille truncation allows up to n/1000 aggregate over-admission. With 64 contexts, up to 6.4% overcommit. | AE3 |
| U-14 | SC-03/SC-L04 | SchedContext | `schedContextConfigure` resets `budgetRemaining` but not replenishment queue entries. Old entries may reference stale budget/period values. `min` in `applyRefill` caps actual refill. | AE3 |
| U-15 | SC-04 (v14) | Lifecycle | `cancelDonation` for `.bound` does not set `isActive := false` (Suspend.lean:96–108). Compare with `schedContextUnbind` (Operations.lean:191) which correctly sets both `boundThread := none` AND `isActive := false`. | AE3 |
| U-16 | SC-05/SC-L06 | Lifecycle | `resumeThread` preemption check uses `tcb.priority` instead of effective priority (Suspend.lean:207–211). Missed preemptions when current thread's effective priority is SchedContext-derived. | AE3 |
| U-17 | CAP-01 (v14) | Capability | CPtr masking inconsistency: `resolveCapAddress` (Operations.lean:96) uses `addr.toNat` without masking; `resolveSlot` (Structures.lean:500) masks to 64 bits. Model-level inconsistency for unbounded Nat. | AE4 |
| U-18 | CAP-02/C-CAP07 | Capability | CDT acyclicity externalized as post-state hypothesis (`hCdtPost`). No proven `addEdge_preserves_acyclicity` lemma. If cycle forms, `descendantsOf` may miss descendants, making revocation incomplete. | AE4 |
| U-20 | SVC-02 (v14) | Service | `lookupServiceByCap` first-match depends on RHTable insertion order. No `registryEndpointUnique` invariant. Multiple services can register same endpoint with nondeterministic lookup. | AE5 |
| U-21 | PLT-01 (v14) | Platform | Boot-to-runtime invariant bridge proven only for empty config. Non-empty hardware boot lacks formal invariant guarantee. Deferred to WS-V. | AE5 |
| U-22 | PLT-02/CS-01 | CrossSubsystem | `collectQueueMembers` fuel exhaustion returns `[]`, silently truncating remaining queue. Fuel-sufficiency argument relies on `tcbQueueChainAcyclic` but connection not formalized. | AE5 |
| U-23 | IPC-01/I-T01 | IPC | Timeout detection via sentinel `0xFFFFFFFF` in gpr x0. Dual-condition check (register AND ipcState=.ready) mitigates false positives substantially. Recommend documentation + eventual out-of-band field. | AE4 |
| U-24 | IPC-02 (v14) | IPC | `endpointQueueRemove` silently absorbs predecessor/successor lookup failures (DualQueue/Core.lean:493–507). Fallback masks queue corruption. | AE4 |
| U-27 | A-T01 (v12) | Architecture | Full TLB flush on every map/unmap. Targeted variants exist but no production entry point uses them. Transitioning to targeted flush for H3 requires composition theorems not yet written. | AE4 |
| U-30 | D-RH02 (v12) | RobinHood | Fuel exhaustion in insert/get/erase returns silent defaults (Core.lean:119,179,233). Correct under invariants but no defense-in-depth. | AE2 |
| U-31 | D-FO01 (v12) | FrozenOps | `frozenQueuePushTailObjects` applies partial mutation on intermediate failure (Core.lean:181–230). Lookups fail after some writes applied. | AE2 |
| U-32 | A-IB01 (v12) | Architecture | IPC buffer validation: no explicit check that `addr` to `addr + ipcBufferSize` fits within a single mapped page (IpcBufferValidation.lean:49–70). | AE4 |
| U-33 | A-SA02 (v12) | Architecture | `Slot.ofNat` may silently accept out-of-range values (SyscallArgDecode.lean:146). | DEFERRED (WS-V) |
| U-34 | A-SA03 (v12) | Architecture | `AccessRightSet.ofNat` silently masks to 5 bits (inconsistent with `PagePermissions.ofNat?` which rejects). | DEFERRED (WS-V) |
| U-35 | C-CAP01 (v12) | Capability | CSpace traversal rights check intentionally omitted (seL4 divergence). Rights enforced at operation layer but not machine-checked across all call sites. | DEFERRED (design review) |
| U-36 | C-CAP06 (v12) | Capability | `cdtMintCompleteness` not included in main `capabilityInvariantBundle`. Revocation via `cspaceRevokeCdt` may miss orphaned capabilities if mint-tracking preservation is incomplete. | AE4 |
| U-37 | I-WC01 (v12) | IPC | All capability transfers target `Slot.ofNat 0` (WithCaps.lean:28–33). Overwrites previous transfers. Must be generalized for hardware binding. | AE4 |
| — | S-03/S-04(v12) | Scheduler | `handleYield` re-enqueues at raw priority, not effective priority (Core.lean:330). `*Effective`/`*WithBudget` variants lack full invariant preservation proofs. | AE3 |
| — | S-05/S-02(v12) | Scheduler | `timeoutBlockedThreads` O(n) scan over entire object store (Core.lean:500–515). Performance-sensitive on RPi5. | AE3 |
| — | IF-14(v12) | InformationFlow | `LabelingContextValid` coherence is deployment requirement, not enforced at runtime (Composition.lean:535–592). | AE5 |
| U-09 | IF-04(v14)/IF-02(v12) | InformationFlow | Default `publicLabel` permits all flows — by-design default proven by `defaultLabelingContext_insecure`. Production deployments MUST override. | AE5 |

### 2.3 LOW Findings (22 actionable — selected for inclusion)

| Unified ID | Source | Subsystem | Description | Phase |
|------------|--------|-----------|-------------|-------|
| — | SC-06 (v14) | SchedContext | `Budget.refill` has inverted semantics — dead code (Types.lean:49). Delete or rename. | AE3 |
| — | SC-07 (v14) | SchedContext | `cancelDonation` for `.bound` does not remove SchedContext from replenish queue. Harmless no-op but wasted work. | AE3 |
| — | SC-09 (v14) | SchedContext | `schedContextBind` reads pre-update SchedContext for run queue insertion. Currently safe; pattern fragile. | AE3 |
| — | F-10 (v14) | Platform | `fromDtb` stub always returns `none`. Should be deprecated. | AE5 |
| — | S-01 (v14) | Scheduler | PIP reads `blockingServer` from pre-mutation state. Functionally equivalent now. Frame theorem recommended. | AE3 |
| — | IPC-03 (v14) | IPC | Notification wait uses LIFO instead of FIFO. Documented seL4 divergence. | — |
| — | CAP-03 (v14) | Capability | No `cspaceRevoke` syscall ID. Revocation not exposed to userspace. Intentional. | — |
| — | CAP-04 (v14) | Capability | Same-slot `cspaceMove`/`cspaceCopy` returns error instead of no-op. Safe. | — |
| — | ARCH-01 (v14) | Architecture | No PA aliasing protection in VSpace. Consistent with seL4 design. | — |
| — | ARCH-02 (v14) | Architecture | `vspaceMapPageCheckedWithFlush` uses model-default PA bound. Production path uses correct bound. | — |
| — | IF-07 (v14) | InformationFlow | Declassification well-formedness not structurally enforced. | AE5 |
| — | IF-08 (v14) | InformationFlow | Enforcement dispatch tightly coupled to operation structure. | — |
| — | IF-09 (v14) | InformationFlow | `replyRecv` NI proof assumes sequential decomposition. Sound for sequential model. | — |
| — | IF-10 (v14) | InformationFlow | Scheduling covert channel not modeled. Standard scope limitation. | — |
| — | T-07/T-F03 | Testing | Some test suites use unchecked `builder.build` instead of `buildChecked`. | AE6 |
| — | T-F02 (v12) | Testing | `TraceSequenceProbe` raw struct construction bypassing `buildChecked`. | AE6 |
| — | T-F05 (v12) | Testing | LivenessSuite — 58 tests are `#check` anchors only, no behavioral execution. | AE6 |
| — | T-F17 (v12) | Testing | `test_rust.sh` silently exits 0 when `cargo` is missing. | AE6 |
| — | SVC-04 (v14) | Service | `registryInterfaceValid` not in `crossSubsystemInvariant`. | AE5 |
| — | PLT-04 (v14) | Platform | `parseFdtNodes` fuel exhaustion returns partial results, not error. | AE5 |
| — | PLT-03 (v14) | Platform | Simulation PA width (52) diverges from RPi5 (44). By design. | — |
| — | R-F01 (v12) | Rust ABI | SchedContext args register comment says "x6=domain" but should say overflow. | AE6 |

### 2.4 Findings Excluded from Remediation

The following findings require no code changes — they are by-design,
already addressed, informational, or deferred to future workstreams:

| Category | Finding IDs | Rationale |
|----------|-------------|-----------|
| **By design** | IF-10, IPC-03, CAP-03, CAP-04, ARCH-01, ARCH-02, IF-08, IF-09, PLT-03, SVC-01(v14) | Documented design decisions consistent with seL4 architecture |
| **Already removed** | IF-05 (v14) | Erroneous finding — separate predicates already exist |
| **Informational (v0.25.14)** | F-12–F-18, SC-10, SC-11, CAP-05, CAP-06, C-02, C-03, ARCH-04–06, PLT-07, PLT-08, T-02–T-05 | Positive confirmations, no action needed |
| **Informational (v0.25.12)** | All positive findings from Sections 1–10 (scheduler irreflexivity/asymmetry/transitivity, badge idempotency, etc.), R-02 (stale variant counts), R-05 (missing wrappers), R-06 (phantom types) | Positive confirmations or documentation-only |
| **No action — LOW/confirmed correct (v0.25.14)** | F-06 (boot-path only), F-07 (RunQueue complexity), F-08 (WithCaps API-only), F-09 (yieldTo no SyscallId), F-11 (test panic), C-01 (zero-bit confirmed correct), SC-08 (popDue size), SVC-03 (existential), T-01 (happy-path focus), PLT-05 (checked variant recommended) | Confirmed correct behavior, documented design, or test-only code. PLT-05 mitigated by `bootFromPlatformChecked` |
| **No action — LOW (v0.25.12)** | F-P02 (naming), F-M03 (Bool/Prop inconsistency), F-T03 (decode safe), F-S02 (mitigated by cnodeWellFormed), F-ST02 (O(n) acceptable), F-ST04 (O(R+S) acceptable), F-B02 (builder-phase only), S-08 through S-12, I-E01/E02/C02/T02/D02/DQ02/WC02/CC03, A-V02/VI02/IB02/RD01/RC01, D-RH05/RH06/RT02, SC-L01/L03, SV-01, T-F04/F06/F07/F09/F11/F20 | Low-severity code quality, documentation, or performance items — not security-relevant |
| **Deferred to H3** | A-T01 targeted flush transition, VSpaceBackend integration | Hardware binding workstream |
| **Deferred to profiling** | S-05/S-02(v12) (O(n) timeout scan) | Post-RPi5 bring-up optimization |
| **Deferred — v0.25.12 MEDIUM (accepted risk)** | S-03(v12) (silent error in timeout fold — masked by invariant), S-04(v12) (vacuous for non-TCB — safe under `currentThreadValid`), S-05(v12) (`blockingChain` fuel — depends on external `blockingAcyclic`), S-06(v12) (PIP bound conservative — not incorrect), S-07(v12) (WCRT external hypotheses — definitional theorem), I-TR02(v12) (pre-dequeue TCB — proven safe by transport lemmas), I-ST01(v12) (11 externalized hypotheses — deferred to cross-subsystem), SC-01(v12) (`Budget.decrement` saturating — proven correct), SC-03(v12) (bind thread state — relies on `runnableThreadsAreReady`), SC-04(v12) (defensive re-lookup — stale fallback unreachable under invariant) | These findings were verified as correct under existing invariants or involve proof-architecture trade-offs. Not security vulnerabilities. Monitoring-only. |
| **Deferred — v0.25.12 MEDIUM (documentation/maintenance)** | D-RH03(v12) (high-heartbeat proof fragility), D-RH04(v12) (`relaxedPCD` documentation), R-F02(v12) (Rust client-side validation), R-F03(v12) (Rust service_register validation), T-F08(v12) (`TRACE_ARTIFACT_DIR` path validation) | Maintenance improvements with no immediate security impact. Deferred to post-release hardening or WS-V. |
| **Deferred — v0.25.12 MEDIUM (architecture)** | IF-01(v12) (non-standard BIBA — intentional, formally witnessed), IF-03(v12) (scheduling covert channel — accepted), IF-13(v12) (one-sided NI — covered by U-08/AE1-G), A-V01(v12) (model-default PA bound — same as ARCH-02/v14) | Architectural design choices with formal witnesses or already deduplicated into v0.25.14 findings |
| **Deferred — v0.25.12 LOW (Rust ABI)** | R-F04 through R-F08 | Low-severity Rust ABI documentation and defense-in-depth items. No security impact; kernel validates on entry. Deferred to WS-V. |


---

## 3. Phase AE1 — Critical: API Dispatch & NI Composition

**Status**: COMPLETE (v0.25.15)

**Goal**: Fix the two highest-impact categories: (1) the checked dispatch path
dropping two syscalls, and (2) the information-flow non-interference proof gaps.
**Gate**: `lake build` + `lake build SeLe4n.Kernel.API` +
`lake build SeLe4n.Kernel.InformationFlow.Invariant.Composition` +
`./scripts/test_smoke.sh`
**Dependencies**: None (first phase).
**Estimated scope**: ~365–480 lines of changes (dominated by AE1-F ~210
lines and AE1-G ~80–100 lines of NI proofs).

### AE1-A: Add `.tcbSetPriority` and `.tcbSetMCPriority` to `dispatchCapabilityOnly` (U-01)

**Finding**: `dispatchWithCapChecked` (API.lean:802–989) is missing both
priority management arms. They fall through to `| _ => .error .illegalState`
at line 989. The unchecked `dispatchWithCap` (API.lean:731–757) handles them
correctly. The enforcement boundary (Wrappers.lean:221–222) correctly classifies
both as `.capabilityOnly`.

**Root cause**: D2 implementation (v0.24.1) added arms to `dispatchWithCap`
but not to the shared helper `dispatchCapabilityOnly` or `dispatchWithCapChecked`.

**Change**: Add two match arms to `dispatchCapabilityOnly` (API.lean:437–540):
```lean
| .tcbSetPriority => some fun st => do
  let args ← Architecture.SyscallArgDecode.decodeTcbSetPriorityArgs decoded
  match cap.target, st.objects[cap.target]? with
  | targetId, some (.tcb _targetTcb) =>
    SchedContext.PriorityManagement.setPriorityOp targetId args.newPriority tid st
  | _, _ => .error .invalidArgument
| .tcbSetMCPriority => some fun st => do
  let args ← Architecture.SyscallArgDecode.decodeTcbSetMCPriorityArgs decoded
  match cap.target, st.objects[cap.target]? with
  | targetId, some (.tcb _targetTcb) =>
    SchedContext.PriorityManagement.setMCPriorityOp targetId args.newMCPriority tid st
  | _, _ => .error .invalidArgument
```

This simultaneously fixes both `dispatchWithCap` (where the explicit arms at
lines 731–757 become redundant but harmless — the `dispatchCapabilityOnly`
check at line 666 short-circuits before reaching them) and
`dispatchWithCapChecked` (where the wildcard is no longer reachable for these
IDs).

**Files modified**: `SeLe4n/Kernel/API.lean` (~20 lines added to
`dispatchCapabilityOnly`).

**Verification**: Build `SeLe4n.Kernel.API` and confirm the new arms resolve
through the same code paths as the existing `dispatchWithCap` arms.

### AE1-B: Move `.tcbSetIPCBuffer` into `dispatchCapabilityOnly` (U-06)

**Finding**: `.tcbSetIPCBuffer` is handled by explicit match arms in BOTH
`dispatchWithCap` (lines 759–769) and `dispatchWithCapChecked` (lines 976–986),
creating a duplication that is the same pattern that caused U-01.

**Change**: Add `.tcbSetIPCBuffer` to `dispatchCapabilityOnly` alongside
the other capability-only TCB operations (`.tcbSuspend`, `.tcbResume`):
```lean
| .tcbSetIPCBuffer => some fun st => do
  let args ← Architecture.SyscallArgDecode.decodeTcbSetIPCBufferArgs decoded
  match cap.target with
  | targetId =>
    Architecture.IpcBufferValidation.setIPCBufferOp targetId args.bufferAddr st
```

Remove the duplicate explicit arms from both `dispatchWithCap` and
`dispatchWithCapChecked`.

**Files modified**: `SeLe4n/Kernel/API.lean` (~8 lines added, ~20 lines
removed — net reduction).

### AE1-C: Fix wildcard unreachability comment (U-07)

**Finding**: Comment at API.lean:987 claims remaining arms are unreachable
via `dispatchCapabilityOnly`. This is incorrect for the checked path before
AE1-A — after AE1-A/B it becomes correct.

**Change**: Update the comment to accurately reflect the post-fix state:
```lean
-- AE1-C: All 25 SyscallId arms are exhaustively handled:
-- 14 by dispatchCapabilityOnly (capability-only operations),
-- 11 by explicit match arms above (IPC, mint, copy, move, etc.).
-- This wildcard is provably unreachable (see
-- dispatchWithCapChecked_wildcard_unreachable below).
```

**Files modified**: `SeLe4n/Kernel/API.lean` (~3 lines).

### AE1-D: Add `dispatchWithCapChecked_wildcard_unreachable` theorem (U-07)

**Finding**: No compile-time completeness theorem exists for the checked
dispatch path. `dispatchWithCap_wildcard_unreachable` (line 1195) exists
for the unchecked path and would have caught U-01 at compile time.

**Change**: Add a theorem analogous to `dispatchWithCap_wildcard_unreachable`
that proves all 25 `SyscallId` variants are handled by
`dispatchWithCapChecked`. This theorem should enumerate all 25 variants and
prove each one does not reach the wildcard arm.

```lean
theorem dispatchWithCapChecked_wildcard_unreachable
    (ctx : LabelingContext) (tid : ThreadId) (cap : ...)
    (decoded : DecodedSyscall) (gate : GateDescriptor)
    (syscallId : SyscallId)
    : ∀ sid, dispatchWithCapChecked ctx tid cap decoded gate sid ≠
        fun _ => .error .illegalState := by
  intro sid; cases sid <;> simp [dispatchWithCapChecked, dispatchCapabilityOnly]
```

**Files modified**: `SeLe4n/Kernel/API.lean` (~30 lines).

### AE1-E: Add `switchDomain` constructor to `NonInterferenceStep` (U-03)

**Finding**: The `NonInterferenceStep` inductive (Composition.lean:34–308) has
32 constructors but none for `switchDomain`. The per-step theorem
`switchDomain_preserves_lowEquivalent` (Operations.lean:580–596) already
exists and proves domain switch preserves low-equivalence. This is a wiring
gap, not a proof gap.

**Change**: Add a 33rd constructor to `NonInterferenceStep`:
```lean
| switchDomain
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hCurrentHigh₁ : ∀ t, s₁.scheduler.current = some t →
      threadObservable ctx observer t = false)
    (hCurrentHigh₂ : ∀ t, s₂.scheduler.current = some t →
      threadObservable ctx observer t = false)
    (hObjInv₁ : s₁.objects.invExt)
    (hObjInv₂ : s₂.objects.invExt)
    (hStep₁ : Scheduler.switchDomain s₁ = .ok ((), s₁'))
    (hStep₂ : Scheduler.switchDomain s₂ = .ok ((), s₂'))
    : NonInterferenceStep ctx observer s₁ s₂ s₁' s₂'
```

**Then** add the corresponding case to `step_preserves_projection`
(Composition.lean:312–476):
```lean
| .switchDomain ctx observer s₁ s₂ s₁' s₂' hLow hCH1 hCH2 hI1 hI2 h1 h2 =>
  switchDomain_preserves_lowEquivalent ctx observer s₁ s₂ s₁' s₂'
    hLow hCH1 hCH2 hI1 hI2 h1 h2
```

**Files modified**: `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean`
(~20 lines).

**Verification**: `lake build SeLe4n.Kernel.InformationFlow.Invariant.Composition`

### AE1-F: Extend NI constructors for call/reply with donation/PIP (U-04)

**Finding**: The NI constructors `endpointCallHigh` (Composition.lean:183–202)
and `endpointReply` (Composition.lean:157–162) reference base IPC operations
(`endpointCall`, `endpointReply`) without accounting for post-operation
`applyCallDonation`/`propagatePriorityInheritance` and
`applyReplyDonation`/`revertPriorityInheritance` mutations.

**Why this is complex**: The existing NI proofs use a projection-based approach
where each operation must prove `projectState ctx observer st' = projectState
ctx observer st`. The donation/PIP mutations modify `objects` (SchedContext
binding, TCB `pipBoost`) and optionally `scheduler.runQueue`. We must prove
these modifications are either (a) non-observable to the observer, or
(b) identical across both executions.

This task is decomposed into 6 sub-steps:

#### AE1-F1: Prove `applyCallDonation_preserves_projection`

**Scope**: Prove that `applyCallDonation` preserves NI projection.

`applyCallDonation` (Donation.lean:63–82) is a conditional wrapper:
- If receiver is passive (`.unbound`) AND caller has `.bound clientScId`,
  calls `donateSchedContext` which modifies two TCBs' `schedContextBinding`
  fields and one SchedContext's `boundThread` field.
- Otherwise returns state unchanged.

The `applyCallDonation_scheduler_eq` theorem (Donation.lean:128) already
proves scheduler state is preserved. The remaining proof obligation is that
the `objects` modifications (SchedContext binding changes on caller/receiver
TCBs) do not affect `projectState`.

**Strategy**: The projection model (`projectState`) projects per-thread state
through `threadObservable`. Both the caller and receiver are already involved
in the IPC operation — if they are high (non-observable), their binding
changes are invisible. If either is low (observable), the binding change is
deterministic (same on both runs because the IPC step was already proven
equivalent).

**Proof skeleton**:
```lean
theorem applyCallDonation_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (caller receiver : SeLe4n.ThreadId)
    (s₁ s₂ : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hCallerEq : s₁.objects[caller.toObjId]? = s₂.objects[caller.toObjId]?)
    (hReceiverEq : s₁.objects[receiver.toObjId]? = s₂.objects[receiver.toObjId]?) :
    lowEquivalent ctx observer
      (applyCallDonation s₁ caller receiver)
      (applyCallDonation s₂ caller receiver) := by
  unfold applyCallDonation
  -- Both sides evaluate identically because caller/receiver objects match
  -- Scheduler preserved by applyCallDonation_scheduler_eq
  ...
```

**Files**: `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` (~30 lines)
**Dependency**: None within AE1-F

#### AE1-F2: Prove `propagatePriorityInheritance_preserves_projection`

**Scope**: Prove that `propagatePriorityInheritance` preserves NI projection.

`propagatePriorityInheritance` (Propagate.lean:60–72) walks the blocking chain
upward from `startTid`, applying `updatePipBoost` at each step. It modifies
only `pipBoost` fields on TCBs along the chain (via `updatePipBoost`, which
computes `computeMaxWaiterPriority` from the thread's waiters).

**Key insight**: `pipBoost` is a scheduler-internal field. The NI projection
model (`projectState`) projects TCB state through `projectTcb`, which includes
priority but `pipBoost` is a derived value used only by the scheduler's
`resolveEffectivePrioDeadline`. If `pipBoost` is NOT included in
`ObservableState` / `projectTcb`, then PIP propagation is trivially
non-observable.

**Sub-step**: First verify whether `projectTcb` includes `pipBoost`:
- Read `Projection.lean` `projectTcb` definition to check which TCB fields
  are projected.
- If `pipBoost` is NOT projected → proof is straightforward (field not
  observable, modification invisible).
- If `pipBoost` IS projected → must prove both runs compute identical
  `pipBoost` values because the blocking graph is identical (from IPC
  equivalence).

**Proof skeleton** (assuming `pipBoost` not projected):
```lean
theorem propagatePIP_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (startTid : SeLe4n.ThreadId) (fuel : Nat)
    (s₁ s₂ : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hObjEq : ∀ tid, s₁.objects[tid]? = s₂.objects[tid]?) :
    lowEquivalent ctx observer
      (propagatePriorityInheritance s₁ startTid fuel)
      (propagatePriorityInheritance s₂ startTid fuel) := by
  induction fuel with
  | zero => exact hLow
  | succ n ih =>
    simp [propagatePriorityInheritance]
    -- updatePipBoost only modifies pipBoost (not projected)
    -- blockingServer reads ipcState (identical by hObjEq)
    ...
```

**Files**: `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` (~40 lines)
**Dependency**: None within AE1-F (can run parallel with F1)

#### AE1-F3: Prove `applyReplyDonation_preserves_projection`

**Scope**: Prove NI preservation for `applyReplyDonation`.

`applyReplyDonation` (Donation.lean:163–172) conditionally:
1. Returns the donated SchedContext to its original owner
   (`returnDonatedSchedContext`)
2. Removes the replier from the run queue (`removeRunnable`)

Step 2 modifies `scheduler.runQueue`, which IS observable in the NI
projection (scheduling state fields are unconditionally visible per
IF-03/Projection.lean:256–288). However, the run queue modification is
deterministic — given identical pre-states, `removeRunnable` produces
identical post-states.

**Strategy**: Leverage the existing `removeRunnableHigh` NI constructor
(Composition.lean:243) which already proves `removeRunnable` preserves
low-equivalence. Compose with the objects-only `returnDonatedSchedContext`
proof (similar pattern to AE1-F1).

**Files**: `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` (~30 lines)
**Dependency**: None within AE1-F (can run parallel with F1, F2)

#### AE1-F4: Prove `revertPriorityInheritance_preserves_projection`

**Scope**: Prove NI preservation for `revertPriorityInheritance`.

`revertPriorityInheritance` (Propagate.lean) is the dual of
`propagatePriorityInheritance` — it walks the blocking chain and recomputes
`pipBoost` downward. Same proof strategy as AE1-F2: if `pipBoost` is not
projected, the proof is straightforward.

**Files**: `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` (~25 lines)
**Dependency**: AE1-F2 (reuse proof strategy and intermediate lemmas)

#### AE1-F5: Compose into `endpointCallWithDonation` NI theorem

**Scope**: Compose AE1-F1 + AE1-F2 with the existing `endpointCall_preserves_lowEquivalent`
theorem to prove the full call-with-donation path.

The API dispatch path for `.call` (API.lean:845–855) is:
```
endpointCallChecked → applyCallDonation → propagatePriorityInheritance
```

The composed theorem chains three NI preservation results:
1. `endpointCall_preserves_lowEquivalent` (existing) → proves IPC step
2. `applyCallDonation_preserves_projection` (AE1-F1) → proves donation step
3. `propagatePIP_preserves_projection` (AE1-F2) → proves PIP step

```lean
theorem endpointCallWithDonation_preserves_lowEquivalent
    (ctx : LabelingContext) (observer : IfObserver)
    (epId : ObjId) (caller : ThreadId) (receiver : ThreadId)
    (msg : IpcMessage)
    (s₁ s₂ s₁_ipc s₂_ipc s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hIpc₁ : endpointCall epId caller msg s₁ = .ok ((), s₁_ipc))
    (hIpc₂ : endpointCall epId caller msg s₂ = .ok ((), s₂_ipc))
    (hDon₁ : s₁' = propagatePriorityInheritance
                       (applyCallDonation s₁_ipc caller receiver) receiver)
    (hDon₂ : s₂' = propagatePriorityInheritance
                       (applyCallDonation s₂_ipc caller receiver) receiver)
    ... :
    lowEquivalent ctx observer s₁' s₂' := by
  -- Step 1: IPC preserves low-equivalence
  have hLowIpc := endpointCall_preserves_lowEquivalent ... hLow ...
  -- Step 2: Donation preserves low-equivalence
  have hLowDon := applyCallDonation_preserves_projection ... hLowIpc ...
  -- Step 3: PIP preserves low-equivalence
  exact propagatePIP_preserves_projection ... hLowDon ...
```

**Files**: `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` (~30 lines)
**Dependency**: AE1-F1, AE1-F2

#### AE1-F6: Compose into `endpointReplyWithReversion` NI theorem and add constructors

**Scope**: Compose AE1-F3 + AE1-F4 with `endpointReply_preserves_lowEquivalent`
for the reply path. Then add both new constructors to `NonInterferenceStep`
and handle the new cases in `step_preserves_projection`.

The API dispatch path for `.reply` (API.lean:869–873) is:
```
endpointReplyChecked → applyReplyDonation → revertPriorityInheritance
```

After composing the reply theorem, add two constructors:
```lean
| endpointCallWithDonation
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hProj₁ : projectState ctx observer s₁' = projectState ctx observer s₁)
    (hProj₂ : projectState ctx observer s₂' = projectState ctx observer s₂)
    : NonInterferenceStep ctx observer s₁ s₂ s₁' s₂'
| endpointReplyWithReversion
    (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hProj₁ : projectState ctx observer s₁' = projectState ctx observer s₁)
    (hProj₂ : projectState ctx observer s₂' = projectState ctx observer s₂)
    : NonInterferenceStep ctx observer s₁ s₂ s₁' s₂'
```

Add corresponding cases in `step_preserves_projection` that delegate to
the composed theorems from AE1-F5 and this sub-step.

**Files**:
- `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` (~25 lines)
- `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` (~30 lines)
**Dependency**: AE1-F3, AE1-F4, AE1-F5

#### AE1-F Summary

| Sub-step | Description | Lines | Dependencies |
|----------|-------------|-------|--------------|
| F1 | `applyCallDonation` NI proof | ~30 | None |
| F2 | `propagatePriorityInheritance` NI proof | ~40 | None |
| F3 | `applyReplyDonation` NI proof | ~30 | None |
| F4 | `revertPriorityInheritance` NI proof | ~25 | F2 |
| F5 | Composed call-with-donation theorem | ~30 | F1, F2 |
| F6 | Composed reply theorem + constructors | ~55 | F3, F4, F5 |
| **Total** | | **~210** | |

**Critical prerequisite**: Before starting F1–F4, verify whether `pipBoost`
is included in `projectTcb` (Projection.lean). This determines the proof
strategy for F2 and F4. If `pipBoost` IS projected, the proofs become
significantly harder (~+50 lines each) because we must prove identical
`pipBoost` values across both runs rather than non-observability.

**Parallelism**: F1, F2, F3 can run in parallel. F4 depends on F2 (reuse
lemmas). F5 depends on F1+F2. F6 depends on F3+F4+F5.

### AE1-G: Add master dispatch NI theorem (U-08)

**Finding**: `NonInterferenceStep` proves per-operation NI. The
`syscallDispatchHigh` constructor (Composition.lean:295–299) bridges to
full dispatch via a `hProj` hypothesis — the gap between per-op NI and
full dispatch NI is bridged by assumption.

**Why this is complex**: This theorem must case-split on all 25 `SyscallId`
variants and discharge each case via the corresponding per-operation NI
proof. The complexity comes from matching each dispatch arm to the correct
NI theorem and providing all required hypotheses.

This task is decomposed into 3 sub-steps:

#### AE1-G1: Map each SyscallId to its NI theorem

**Scope**: Create a reference mapping from each of the 25 `SyscallId`
variants to the NI theorem that covers it. This is a planning step that
produces a table, not code.

| SyscallId | Dispatch path | NI theorem |
|-----------|--------------|------------|
| `.send` | `endpointSendDualWithCaps` | `endpointSendDual` constructor |
| `.receive` | `endpointReceiveDualChecked` | `endpointReceiveDualHigh` constructor |
| `.call` | `endpointCallChecked` + donation + PIP | `endpointCallWithDonation` (AE1-F) |
| `.reply` | `endpointReplyChecked` + donation + PIP | `endpointReplyWithReversion` (AE1-F) |
| `.replyRecv` | compound reply + receive | `endpointReplyRecvHigh` constructor |
| `.cspaceMint` | `cspaceMintChecked` | `cspaceMint` constructor |
| `.cspaceCopy` | `cspaceCopyChecked` | `cspaceCopy` constructor |
| `.cspaceMove` | `cspaceMoveChecked` | `cspaceMove` constructor |
| `.cspaceDelete` | via `dispatchCapabilityOnly` | `cspaceDeleteSlot` constructor |
| `.lifecycleRetype` | via `dispatchCapabilityOnly` | `lifecycleRetype` constructor |
| `.vspaceMap` | via `dispatchCapabilityOnly` | `vspaceMapPage` constructor |
| `.vspaceUnmap` | via `dispatchCapabilityOnly` | `vspaceUnmapPage` constructor |
| `.notificationSignal` | `notificationSignalChecked` | `notificationSignal` constructor |
| `.notificationWait` | `notificationWaitChecked` | `notificationWait` constructor |
| `.serviceRegister` | `registerServiceChecked` | `registerServiceChecked` constructor |
| `.serviceRevoke` | via `dispatchCapabilityOnly` | compose from `cspaceDeleteSlot` |
| `.serviceQuery` | via `dispatchCapabilityOnly` | read-only (trivial NI) |
| `.schedContextConfigure` | via `dispatchCapabilityOnly` | `.capabilityOnly` — NI by capability gate |
| `.schedContextBind` | via `dispatchCapabilityOnly` | `.capabilityOnly` — NI by capability gate |
| `.schedContextUnbind` | via `dispatchCapabilityOnly` | `.capabilityOnly` — NI by capability gate |
| `.tcbSuspend` | via `dispatchCapabilityOnly` | `.capabilityOnly` — NI by capability gate |
| `.tcbResume` | via `dispatchCapabilityOnly` | `.capabilityOnly` — NI by capability gate |
| `.tcbSetPriority` | via `dispatchCapabilityOnly` (AE1-A) | `.capabilityOnly` — NI by capability gate |
| `.tcbSetMCPriority` | via `dispatchCapabilityOnly` (AE1-A) | `.capabilityOnly` — NI by capability gate |
| `.tcbSetIPCBuffer` | via `dispatchCapabilityOnly` (AE1-B) | `.capabilityOnly` — NI by capability gate |

**Key insight**: Operations routed through `dispatchCapabilityOnly` are
classified as `.capabilityOnly` in the enforcement boundary. Their NI
follows from the capability gate check: if the caller lacks the required
capability, the operation fails identically on both runs; if the caller
has the capability, the operation's effect is determined by the capability
target, which is identical across low-equivalent states (capabilities are
projected in the NI model).

**Files**: None (planning artifact)
**Dependency**: AE1-A, AE1-B (dispatch arms must be in place)

#### AE1-G2: Prove `capabilityOnly_preserves_projection` lemma

**Scope**: Factor out a shared lemma for all capability-only operations.

All 14 operations in `dispatchCapabilityOnly` share the same NI argument:
the operation is gated by a capability lookup, and the capability is
projected in the NI model. A single lemma can cover all of them:

```lean
theorem capabilityOnly_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (op : SystemState → KernelResult SystemState)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hCapEq : capLookup s₁ = capLookup s₂)
    (hOpProj : ∀ s s', op s = .ok ((), s') →
      projectState ctx observer s' = projectState ctx observer s)
    (hStep₁ : op s₁ = .ok ((), s₁'))
    (hStep₂ : op s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂'
```

This lemma generalizes the existing `syscallDispatchHigh` constructor
pattern but with a dischargeable `hOpProj` rather than an assumed one.

**Files**: `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` (~20 lines)
**Dependency**: None

#### AE1-G3: Assemble master dispatch theorem

**Scope**: Write the final `dispatchSyscallChecked_preserves_projection`
theorem with 25-way case split.

```lean
theorem dispatchSyscallChecked_preserves_projection
    (ctx : LabelingContext) (observer : IfObserver)
    (sid : SyscallId) (tid : ThreadId) (cap : ...)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hStep₁ : dispatchSyscallChecked ctx sid tid cap ... s₁ = .ok ((), s₁'))
    (hStep₂ : dispatchSyscallChecked ctx sid tid cap ... s₂ = .ok ((), s₂'))
    ... :
    lowEquivalent ctx observer s₁' s₂' := by
  cases sid
  -- 14 capability-only arms: apply capabilityOnly_preserves_projection
  all_goals try { apply capabilityOnly_preserves_projection <;> assumption }
  -- 11 explicit arms: apply per-operation NI theorems
  · -- .send
    apply endpointSendDual_preserves_lowEquivalent ...
  · -- .call
    apply endpointCallWithDonation_preserves_lowEquivalent ...
  · -- .reply
    apply endpointReplyWithReversion_preserves_lowEquivalent ...
  ...
```

The `all_goals try` tactic handles the 14 capability-only arms
uniformly. The remaining 11 arms are handled by explicit per-operation
theorem applications.

**Files**: `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` (~60–80 lines)
**Dependency**: AE1-G1, AE1-G2, AE1-F (all NI constructors in place)

#### AE1-G Summary

| Sub-step | Description | Lines | Dependencies |
|----------|-------------|-------|--------------|
| G1 | Map SyscallId → NI theorem (planning) | 0 | AE1-A, AE1-B |
| G2 | `capabilityOnly_preserves_projection` lemma | ~20 | None |
| G3 | Master dispatch theorem (25-way case split) | ~60–80 | G1, G2, AE1-F |
| **Total** | | **~80–100** | |

### AE1-H: Verify AE1 gate conditions

**Gate verification**:
1. `lake build SeLe4n.Kernel.API` — confirms dispatch changes compile
2. `lake build SeLe4n.Kernel.InformationFlow.Invariant.Composition` — confirms
   NI composition changes compile
3. `lake build` — full build with no regressions
4. `./scripts/test_smoke.sh` — all tiers pass
5. `grep -r 'sorry' SeLe4n/Kernel/API.lean SeLe4n/Kernel/InformationFlow/` —
   zero matches
6. Verify fixture: main trace smoke test still matches expected output

**Files modified**: None (verification only).


---

## 4. Phase AE2 — Data Structure Hardening & Production Reachability

**Status**: COMPLETE (v0.25.16)
**Goal**: Fix data structure safety gaps (RobinHood capacity guard, RadixTree
precondition enforcement) and resolve production reachability for FrozenOps
and Liveness subsystems.
**Gate**: `lake build` + module-specific builds for modified files +
`./scripts/test_smoke.sh` — ALL PASSED
**Dependencies**: None (independent of AE1).
**Estimated scope**: ~100–135 lines of changes.

### AE2-A: Enforce `4 ≤ capacity` in `RHTable.empty` (U-28)

**Finding**: `RHTable.empty` (Core.lean:90–96) accepts any `cap > 0`.
`insert_size_lt_capacity` (Bridge.lean:361) requires `4 ≤ capacity`.
The kernel-level invariant `invExtK` (Bridge.lean:858) includes the
constraint, but the public `invExt` does not.

**Change**: Modify `RHTable.empty` to require `4 ≤ cap`:
```lean
def RHTable.empty (cap : Nat) (hCapGe4 : 4 ≤ cap := by omega) : RHTable α β :=
  { slots     := ⟨List.replicate cap none⟩
    size      := 0
    capacity  := cap
    hCapPos   := by omega  -- 4 ≤ cap → 0 < cap
    hSlotsLen := by simp [Array.size] }
```

**Impact analysis**: All call sites of `RHTable.empty` must provide
`4 ≤ cap`. Scan the codebase for all uses:
- `SeLe4n/Prelude.lean` (likely uses default capacity ≥ 4)
- `SeLe4n/Model/State.lean` (system state initialization)
- `SeLe4n/Testing/StateBuilder.lean` (test state construction)
- Any test files creating empty tables

Each call site must be verified to use `cap ≥ 4` or updated accordingly.

**Files modified**: `SeLe4n/Kernel/RobinHood/Core.lean` (~3 lines changed),
plus call-site updates (~5–10 lines across 2–4 files).

**Verification**: `lake build SeLe4n.Kernel.RobinHood.Core` +
`lake build SeLe4n.Kernel.RobinHood.Bridge` (confirms `insert_size_lt_capacity`
no longer needs separate `hCapGe4` parameter — it follows from WF).

### AE2-B: Add bounded key enforcement to `buildCNodeRadix` (U-29)

**Finding**: `buildCNodeRadix_lookup_equiv` (Bridge.lean:317–324) requires
`UniqueRadixIndices` and `hNoPhantom` as caller-side proof obligations.
`uniqueRadixIndices_sufficient` (line 420) shows these are automatically
satisfied when keys are bounded by `2^radixWidth`, but no enforcement exists.

**Change**: Add a runtime key-bounds check at the entry of `buildCNodeRadix`:
```lean
def buildCNodeRadix (rt : RHTable SeLe4n.Slot Capability)
    (config : CNodeConfig) : CNodeRadix :=
  -- AE2-B: Validate all keys are bounded by 2^radixWidth
  let radixBound := 2 ^ config.radixWidth
  let bounded := rt.fold true fun acc k _ => acc && (k.toNat < radixBound)
  if bounded then
    buildCNodeRadixUnchecked rt config
  else
    CNodeRadix.empty config  -- Safe fallback: empty radix on invalid keys
```

Alternatively, add a `BoundedSlotTable` type wrapper that carries the
key-boundedness proof as a witness, allowing `buildCNodeRadix_lookup_equiv`
to discharge its preconditions from the type.

**Files modified**: `SeLe4n/Kernel/RadixTree/Bridge.lean` (~15–20 lines).

### AE2-C: Document RobinHood fuel exhaustion defaults (U-30)

**Finding**: Fuel exhaustion in `insert`/`get`/`erase` (Core.lean:119,179,233)
returns silent defaults. Correct under WF invariant but no defense-in-depth.

**Change**: Add `-- FUEL-SAFETY: ...` documentation annotations at each fuel
exhaustion return point explaining:
1. Why the branch is unreachable under the WF invariant
2. What the consequence would be if reached (dropped entry, none result)
3. The WF property that guarantees unreachability

Additionally, add a `-- AUDIT-NOTE: D-RH02` annotation for traceability.

This is a documentation-only change. No behavioral changes.

**Files modified**: `SeLe4n/Kernel/RobinHood/Core.lean` (~12 lines of
comments).

### AE2-D: Fix `frozenQueuePushTailObjects` partial mutation (U-31)

**Finding**: `frozenQueuePushTailObjects` (FrozenOps/Core.lean:181–230)
applies partial mutations on intermediate failure — if a lookup fails
after some writes have already been applied, the state is partially
mutated.

**Change**: Refactor to validate all lookups BEFORE performing any writes:
```lean
-- Phase 1: Validate all required objects exist
let allPresent := tids.all fun tid => (st.objects.get? tid.toObjId).isSome
if !allPresent then .error .lookupFailure
-- Phase 2: Apply all writes (now guaranteed to succeed)
else
  let st' := tids.foldl (fun acc tid => ...) st
  .ok ((), st')
```

**Files modified**: `SeLe4n/Kernel/FrozenOps/Core.lean` (~25 lines).

**Note**: Since FrozenOps is currently test-only (U-02), this fix improves
code quality for future production integration but does not affect current
production behavior.

### AE2-E: Resolve FrozenOps production status (U-02)

**Finding**: 4 FrozenOps modules are unreachable from production. Decision
needed: integrate into production or document as experimental.

**Decision**: Document as **future/experimental** infrastructure. The
two-phase frozen architecture (Q7) is designed for a future kernel
evolution where syscall processing operates on immutable frozen state.
This is preparatory infrastructure, not dead code.

**Change**:
1. Add a module-level documentation block to `FrozenOps/Core.lean` (if
   not already present) explicitly stating non-production status:
   ```lean
   /- FrozenOps — Two-Phase Kernel Architecture (Q7)
      STATUS: Experimental/Future — not in production import chain.
      These modules implement the frozen-state kernel monad for a future
      architecture where syscall processing operates on immutable
      FrozenSystemState snapshots. Currently exercised by 5 test suites.
      Integration into the production API layer is planned for WS-V
      (hardware binding) when the performance characteristics of the
      two-phase approach can be benchmarked on RPi5. -/
   ```
2. Update `CLAUDE.md` source layout section to annotate FrozenOps as
   `(experimental, Q7)`.

**Files modified**: `SeLe4n/Kernel/FrozenOps/Core.lean` (~8 lines),
`CLAUDE.md` (~2 lines).

### AE2-F: Import Liveness into production chain (U-05)

**Finding**: 7+1 Liveness files are test-only. The WCRT bounded latency
theorem and all liveness proofs could silently diverge from actual scheduler
implementation if `Operations/Core.lean` is modified.

**Change**: Import `SeLe4n.Kernel.Scheduler.Liveness` from the
`Scheduler/Invariant.lean` re-export hub (or from `CrossSubsystem.lean`
if import cycles arise, following the AD1 precedent):
```lean
import SeLe4n.Kernel.Scheduler.Liveness
```

This brings all 7 Liveness submodules into the production build, ensuring
the Lean type-checker verifies liveness theorem compatibility with actual
scheduler operations on every build.

**Import cycle risk**: Check whether `Liveness/WCRT.lean` imports
anything that creates a cycle through `Scheduler/Invariant.lean`. If so,
use `CrossSubsystem.lean` as the integration point (same resolution
strategy as WS-AD phase AD1).

**Files modified**: `SeLe4n/Kernel/Scheduler/Invariant.lean` or
`SeLe4n/Kernel/CrossSubsystem.lean` (~2 lines).

### AE2-G: Import PriorityInheritance/Preservation into production chain

**Finding**: `PriorityInheritance/Preservation.lean` and
`PriorityInheritance/BoundedInversion.lean` are only imported by Liveness
(test-only before AE2-F). After AE2-F, Liveness enters production — but
verify these PIP modules are transitively included.

**Change**: Verify transitive import chain. If
`PriorityInheritance/Preservation.lean` is not transitively imported via
Liveness, add an explicit import to `Scheduler/PriorityInheritance.lean`
(the re-export hub) or `CrossSubsystem.lean`.

**Files modified**: Potentially `SeLe4n/Kernel/Scheduler/PriorityInheritance.lean`
(~1 line) or none if transitively covered.

### AE2-H: Verify AE2 gate conditions

**Gate verification**:
1. `lake build SeLe4n.Kernel.RobinHood.Core` — capacity constraint compiles
2. `lake build SeLe4n.Kernel.RadixTree.Bridge` — key bounds compiles
3. `lake build SeLe4n.Kernel.FrozenOps.Core` — partial mutation fix compiles
4. `lake build SeLe4n.Kernel.Scheduler.Liveness` — Liveness reachable
5. `lake build` — full build clean
6. `./scripts/test_smoke.sh` — all tiers pass
7. Verify zero sorry/axiom in all modified files


---

## 5. Phase AE3 — Scheduler & SchedContext Correctness

**Goal**: Fix correctness gaps in the scheduler, SchedContext, and lifecycle
subsystems — including effective priority usage, CBS budget accounting, and
donation cleanup consistency.
**Gate**: `lake build` + `./scripts/test_smoke.sh` + relevant module builds
**Dependencies**: AE1 (dispatch must be fixed first so priority ops work in
checked path).
**Estimated scope**: ~135–185 lines of changes (AE3-A domain consistency
~45 lines, AE3-B/C/D/E/F ~30 lines code + ~30 lines proofs, rest docs).

### AE3-A: Enforce `sc.domain == tcb.domain` invariant for bound threads (U-11)

**Finding**: `chooseBestRunnableInDomainEffective` filters by `tcb.domain`
but `effectivePriority` resolves from `sc.domain` (Selection.lean:363).
If a thread is bound to a SchedContext in a different domain, the thread
passes the domain filter by its TCB domain but is prioritized by its
SchedContext domain.

This task is decomposed into 4 sub-steps:

#### AE3-A1: Define `boundThreadDomainConsistent` predicate

**Scope**: Add the invariant predicate to the scheduler invariant module.

The predicate must cover the binding established by `schedContextBind`
(Operations.lean:130–154). The binding mechanism uses
`tcb.schedContextBinding := .bound scIdTyped`, and the bidirectional link
is `sc.boundThread := some threadId`. The domain consistency must hold for
ALL bound pairs, not just newly-bound ones.

```lean
def boundThreadDomainConsistent (st : SystemState) : Prop :=
  ∀ (tid : ThreadId) (scId : SchedContextId),
    (match st.objects[tid.toObjId]? with
     | some (.tcb tcb) => tcb.schedContextBinding = .bound scId
     | _ => False) →
    match st.objects[scId.toObjId]? with
    | some (.schedContext sc) =>
      match st.objects[tid.toObjId]? with
      | some (.tcb tcb) => tcb.domain = sc.domain
      | _ => True
    | _ => True
```

Note: Use `tcb.schedContextBinding` (from the TCB's perspective) rather than
`st.scheduler.threadSchedContext` (which may not exist as a separate field —
verify in `Model/State.lean`). The binding is stored directly on the TCB.

**Files**: `SeLe4n/Kernel/Scheduler/Invariant.lean` or a new file
`SeLe4n/Kernel/SchedContext/Invariant/Defs.lean` (~12 lines)

#### AE3-A2: Add domain-match check to `schedContextBind`

**Scope**: Add a runtime check in `schedContextBind` (Operations.lean:130–154)
that rejects cross-domain binding.

Insert after the TCB and SchedContext lookups (line ~138), before establishing
the binding:
```lean
-- AE3-A2/S-02: Reject cross-domain binding
if tcb.domain != sc.domain then .error .invalidArgument
```

This check must go BEFORE the `match tcb.schedContextBinding` guard at line
~139, so that domain mismatch is caught even for unbound threads.

**Impact analysis**: Any test that creates a cross-domain binding will fail.
Scan test suites for `schedContextBind` calls with mismatched domains. Update
tests to use matching domains.

**Files**: `SeLe4n/Kernel/SchedContext/Operations.lean` (~3 lines)

#### AE3-A3: Add `boundThreadDomainConsistent` to scheduler invariant bundle

**Scope**: Include the new predicate in the appropriate invariant bundle.

Candidate bundles:
- `schedulerInvariantBundleExtended` (15-tuple) in `Scheduler/Invariant.lean`
- `schedContextInvariantBundle` (4-tuple) in `SchedContext/Invariant/Defs.lean`

The predicate bridges scheduler (domain filter) and SchedContext (binding),
so `schedContextInvariantBundle` is the natural home. Add it as a 5th
conjunct.

**Files**: `SeLe4n/Kernel/SchedContext/Invariant/Defs.lean` (~3 lines)

#### AE3-A4: Prove preservation for binding-modifying operations

**Scope**: Prove `boundThreadDomainConsistent` is preserved by all operations
that modify the TCB↔SchedContext binding:

| Operation | File | Binding change | Proof strategy |
|-----------|------|---------------|----------------|
| `schedContextBind` | Operations.lean:130 | Establishes `.bound` | Domain check (AE3-A2) ensures `tcb.domain = sc.domain` at bind time |
| `schedContextUnbind` | Operations.lean:170 | Clears to `.unbound` | Vacuously true — no bound pair to check |
| `cancelDonation` | Suspend.lean:96 | Clears `.bound` | Same as unbind — vacuously true |
| `applyCallDonation` | Donation.lean:63 | Changes to `.donated` | `.donated` is not `.bound`, so not in scope |
| `applyReplyDonation` | Donation.lean:163 | Returns to `.bound` | Must show domain unchanged during donation round-trip |

The most complex case is `applyReplyDonation`: when a SchedContext is returned
to its original owner, we must prove the original owner's domain still matches
the SchedContext's domain. This follows from the fact that `donateSchedContext`
does not modify either party's domain.

**Files**: `SeLe4n/Kernel/SchedContext/Invariant/Preservation.lean` (~25 lines)

### AE3-B: Set `isActive := false` in `cancelDonation` for `.bound` (U-15)

**Finding**: `cancelDonation` (Suspend.lean:96–108) sets
`boundThread := none` but NOT `isActive := false` for the `.bound` case.
`schedContextUnbind` (Operations.lean:191) correctly sets both.

**Change**: Update the `.bound` case in `cancelDonation`:
```lean
| some (.schedContext sc) =>
  let sc' := { sc with boundThread := none, isActive := false }
  { st with objects := st.objects.insert scId.toObjId (.schedContext sc') }
```

**Files modified**: `SeLe4n/Kernel/Lifecycle/Suspend.lean` (~1 line changed).

**Verification**: `lake build SeLe4n.Kernel.Lifecycle.Suspend`

### AE3-C: Remove SchedContext from replenish queue in `cancelDonation` (SC-07)

**Finding**: Unlike `schedContextUnbind` which calls `ReplenishQueue.remove`,
`cancelDonation` for `.bound` does not remove the SchedContext from the
system replenish queue. Replenishments are processed for an orphaned context.

**Change**: After setting `isActive := false` (AE3-B), add replenish queue
removal:
```lean
let st2 := { st1 with replenishQueue :=
  ReplenishQueue.remove st1.replenishQueue scId }
```

**Dependency**: AE3-B must be complete first.

**Files modified**: `SeLe4n/Kernel/Lifecycle/Suspend.lean` (~3 lines).

### AE3-D: Use effective priority in `resumeThread` preemption check (U-16)

**Finding**: `resumeThread` (Suspend.lean:207–211) compares
`tcb'.priority.val > curTcb.priority.val`. Should use effective priority
from `resolveEffectivePrioDeadline` or `getCurrentPriority`.

**Change**: Replace the raw priority comparison with effective priority:
```lean
let needsReschedule : Bool := match st.scheduler.current with
  | some curTid =>
    match st.objects[curTid.toObjId]? with
    | some (.tcb curTcb) =>
      let curEffective := resolveEffectivePrioDeadline curTcb st
      let resumedEffective := resolveEffectivePrioDeadline tcb' st
      resumedEffective.priority.val > curEffective.priority.val
    | _ => false
  | none => true
```

Where `resolveEffectivePrioDeadline` looks up the thread's SchedContext
binding to determine effective priority. Import
`SchedContext.PriorityManagement` if needed.

**Files modified**: `SeLe4n/Kernel/Lifecycle/Suspend.lean` (~8 lines).

### AE3-E: Use effective priority in `handleYield` re-enqueue (S-03)

**Finding**: `handleYield` (Core.lean:330) re-enqueues at `tcb.priority`,
not effective priority. PIP-boosted threads go into wrong priority bucket.

**Change**: Replace `tcb.priority` with the effective priority derived from
`resolveEffectivePrioDeadline` for the run queue re-insertion:
```lean
let effectivePrio := resolveEffectivePrioDeadline tcb st
runQueueEnqueue tid effectivePrio.priority st
```

**Files modified**: `SeLe4n/Kernel/Scheduler/Operations/Core.lean` (~5 lines).

### AE3-F: Clear replenishment queue in `schedContextConfigure` (U-14)

**Finding**: `schedContextConfigure` (Operations.lean:98–106) resets
`budgetRemaining` but not the `replenishments` list. Old entries may
reference stale budget/period values, transiently violating
`replenishmentAmountsBounded`.

**Change**: Reset the replenishment list during reconfiguration:
```lean
let sc' := { sc with
  budget := newBudget
  period := newPeriod
  priority := newPriority
  deadline := newDeadline
  domain := newDomain
  budgetRemaining := newBudget
  replenishments := [{ amount := newBudget, time := st.machine.timer }]
}
```

This creates a single fresh replenishment entry with the new budget amount,
matching the reset `budgetRemaining`. The `min` in `applyRefill` is no
longer needed as a safety net for stale entries.

**Files modified**: `SeLe4n/Kernel/SchedContext/Operations.lean` (~2 lines).

**Verification**: `lake build SeLe4n.Kernel.SchedContext.Operations` +
verify that `schedContextConfigure_preserves_invariant` still proves
(it should, as the new state is more strongly invariant-satisfying).

### AE3-G: Document CBS bandwidth bound gap and admission precision (U-12, U-13)

**Finding**: CBS bandwidth bound proves 8×budget per window
(maxReplenishments=8), not budget/period. Admission control uses per-mille
truncation with up to n/1000 aggregate error.

**Change**: Add documentation to `SchedContext/Invariant/Defs.lean`:
```lean
/- CBS Bandwidth Bound — Known Precision Gap (U-12/SC-01)
   The proven bound `cbs_bandwidth_bounded` establishes:
     totalConsumed ≤ maxReplenishments × budget = 8 × budget
   This is 8× weaker than the ideal CBS guarantee of `budget` per period.
   The per-object `budgetWithinBounds` invariant prevents actual overrun at
   any single tick. The proven bound reflects worst-case replenishment
   accumulation across the full replenishment window.

   Admission Control Precision (U-13/SC-02)
   `admissionCheck` uses integer per-mille arithmetic (budget×1000/period)
   which truncates per-context. Aggregate error ≤ n/1000 where n is the
   number of active SchedContexts. For n=64, this is ≤6.4% overcommit.
   The `budgetWithinBounds` invariant provides per-object isolation
   regardless of aggregate admission precision. -/
```

**Files modified**: `SeLe4n/Kernel/SchedContext/Invariant/Defs.lean` (~15 lines).

### AE3-H: Delete dead `Budget.refill` function (SC-06)

**Finding**: `Budget.refill` (Types.lean:49) has inverted semantics — caps
down to ceiling instead of refilling. Unused by the CBS engine. Misleading
name.

**Change**: Delete `Budget.refill` entirely. Verify no call sites exist
(expected: zero, since the CBS engine uses `applyRefill` in Budget.lean).

**Files modified**: `SeLe4n/Kernel/SchedContext/Types.lean` (~3 lines removed).

### AE3-I: Add PIP `blockingServer` frame theorem (S-01)

**Finding**: `propagatePriorityInheritance` reads `blockingServer` from
pre-mutation state (Propagate.lean:60–72). Currently safe because
`updatePipBoost` only modifies `pipBoost`, never `ipcState`. Latent risk.

**Change**: Add a frame theorem to `PriorityInheritance/Propagate.lean`:
```lean
theorem updatePipBoost_preserves_ipcState (tid : ThreadId)
    (newBoost : Priority) (st : SystemState) :
    ∀ t, (updatePipBoost tid newBoost st).objects[t]?.map
      (fun o => match o with | .tcb tcb => some tcb.ipcState | _ => none)
    = st.objects[t]?.map
      (fun o => match o with | .tcb tcb => some tcb.ipcState | _ => none) := by
  ...
```

**Files modified**: `SeLe4n/Kernel/Scheduler/PriorityInheritance/Propagate.lean`
(~15 lines).

### AE3-J: Document `schedContextBind` pre-update read pattern (SC-09)

**Finding**: `schedContextBind` (Operations.lean:146–149) reads pre-update
SchedContext for run queue insertion. Currently correct because bind does
not change priority. Pattern fragile if bind is extended.

**Change**: Add inline documentation:
```lean
-- AE3-J/SC-09: Run queue insertion uses pre-update sc.priority.
-- This is correct because schedContextBind does not modify priority.
-- If future changes to bind modify priority, this must be updated
-- to read from the post-update SchedContext.
```

**Files modified**: `SeLe4n/Kernel/SchedContext/Operations.lean` (~4 lines).

### AE3-K: Document `timeoutBlockedThreads` O(n) performance (S-05)

**Finding**: O(n) scan over entire object store on budget exhaustion
(Core.lean:500–515). Performance-sensitive on RPi5 with many objects.

**Change**: Add performance annotation:
```lean
-- PERF-NOTE (S-05/AE3-K): O(n) scan over all objects. Acceptable for
-- current object counts (≤65K). If RPi5 benchmarking shows this as a
-- bottleneck, consider maintaining a secondary index of blocked threads
-- keyed by SchedContext ID. Deferred to post-benchmarking optimization.
```

**Files modified**: `SeLe4n/Kernel/Scheduler/Operations/Core.lean` (~4 lines).

### AE3-L: Verify AE3 gate conditions

**Gate verification**:
1. Module builds for all modified files
2. `lake build` — full build clean
3. `./scripts/test_smoke.sh` — all tiers pass
4. Verify `schedContextConfigure` preservation theorem still proves after
   replenishment queue reset
5. Verify zero sorry/axiom in all modified files


---

## 6. Phase AE4 — Capability, IPC & Architecture Hardening

**Goal**: Address model-level inconsistencies in the capability subsystem,
IPC queue safety, architecture decode symmetry, and TLB transition
preparation.
**Gate**: `lake build` + `./scripts/test_full.sh` (theorem changes require
full test suite)
**Dependencies**: AE1 (dispatch fix enables correct testing of capability ops
through checked path).
**Estimated scope**: ~240–330 lines of changes (AE4-C CDT acyclicity ~60
lines, AE4-I slot generalization ~40+ lines, AE4-E queue proof ~46 lines).

### AE4-A: Add CPtr masking to `resolveCapAddress` (U-17)

**Finding**: `resolveCapAddress` (Operations.lean:96) uses `addr.toNat`
without masking to 64-bit word width. `resolveSlot` (Structures.lean:500)
explicitly masks: `cptr.toNat % SeLe4n.machineWordMax`. For unbounded Lean
`Nat`, the two functions could resolve to different slots for the same CPtr.

**Change**: Add masking at the entry of `resolveCapAddress`:
```lean
def resolveCapAddress (cnode : CNode) (addr : CPtr)
    (bitsRemaining : Nat) ... : KernelResult ... :=
  -- AE4-A/CAP-01: Mask CPtr to machine word width for consistency
  -- with CNode.resolveSlot (S4-C)
  let maskedAddr := CPtr.ofNat (addr.toNat % SeLe4n.machineWordMax)
  if hZero : bitsRemaining = 0 then .error .illegalState
  else
    let consumed := min bitsRemaining cnode.radixBits
    let shiftedAddr := maskedAddr.toNat >>> (bitsRemaining - consumed)
    ...
```

**Impact**: All downstream theorem proofs that reference `resolveCapAddress`
must be checked. The masking is idempotent for values already < 2^64, so
existing proofs should hold or require trivial `Nat.mod_eq_of_lt` lemma
insertions.

**Files modified**: `SeLe4n/Kernel/Capability/Operations.lean` (~5 lines).

### AE4-B: Add VAddr canonicity check to `decodeVSpaceUnmapArgs` (U-26)

**Finding**: `decodeVSpaceMapArgs` validates VAddr canonical (line 213:
`if !vaddr.isCanonical then .error .addressOutOfBounds`) but
`decodeVSpaceUnmapArgs` (line 237) does not. Defense-in-depth gap.

**Change**: Add the same canonicity check:
```lean
def decodeVSpaceUnmapArgs (regs : RegisterFile) : KernelResult VSpaceUnmapArgs :=
  let r0 := regs.gpr 0
  let r1 := regs.gpr 1
  let asid := r0.val
  let vaddr := VAddr.ofNat r1.val
  -- AE4-B/ARCH-03: Validate VAddr canonical for consistency with map
  if !vaddr.isCanonical then .error .addressOutOfBounds
  else if asid > maxAsid then .error .invalidArgument
  else .ok { asid := Asid.ofNat asid, vaddr := vaddr }
```

**Files modified**: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`
(~3 lines added).

### AE4-C: Add CDT `addEdge_preserves_acyclicity` lemma (U-18)

**Finding**: CDT acyclicity is externalized as a post-state hypothesis
(`hCdtPost`) in capability preservation proofs. No proven
`addEdge_preserves_acyclicity` lemma exists.

This task is decomposed into 4 sub-steps:

#### AE4-C1: Understand CDT acyclicity formulation

**Scope**: `cdtAcyclicity` (Defs.lean:100–101) is defined as
`st.cdt.edgeWellFounded`, which uses the well-founded relation formulation.
The CDT stores edges as a list of `CdtEdge` where each edge has a
`parent : CdtNodeId` and `child : CdtNodeId` with an `edgeType`.

Before writing the proof, determine:
1. The exact type of `cdt.edges` (List or Array)
2. How `edgeWellFounded` is defined (well-founded induction vs fuel-bounded
   search)
3. How `addEdge` is implemented (likely list append)
4. Whether `isReachable` or an equivalent exists for the CDT

**Files**: Read `SeLe4n/Model/Object/Types.lean` for CDT types, then
`Capability/Invariant/Defs.lean` for `edgeWellFounded`.

#### AE4-C2: Prove `addEdge_preserves_acyclicity` core lemma

**Scope**: The key theorem:
```lean
theorem addEdge_preserves_acyclicity
    (st : SystemState) (parentNode childNode : CdtNodeId)
    (edgeType : CdtEdgeType)
    (hAcyclic : cdtAcyclicity st)
    (hNotReachable : ¬ cdtReachable st.cdt childNode parentNode) :
    cdtAcyclicity { st with cdt :=
      st.cdt.addEdge parentNode childNode edgeType }
```

**Proof strategy**: By contradiction. If the new edge creates a cycle, then
there exists a path from `childNode` back to `parentNode` in the OLD CDT
(since the only new edge is `parentNode → childNode`). But `hNotReachable`
states no such path exists. Contradiction.

The difficulty depends on the formulation of `edgeWellFounded`:
- If formulated as "no non-trivial cycle exists" → straightforward
- If formulated via `WellFounded` relation → requires showing the
  accessibility predicate extends to the new edge

**Files**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean` (~30 lines)

#### AE4-C3: Prove `hNotReachable` for `cspaceMintWithCdt`

**Scope**: Discharge the `hNotReachable` precondition for the mint case.

When minting a capability, the CDT edge is: `sourceSlot → destSlot`.
The destination slot is freshly written by the mint operation. Since the
destination was previously empty (guaranteed by the `targetSlotEmpty`
precondition in `cspaceMint`), no CDT node exists for it, so it cannot
be reachable from the source. Therefore `¬ cdtReachable cdt destNode
sourceNode` holds trivially — `destNode` has no outgoing edges.

```lean
theorem cspaceMint_notReachable
    (st : SystemState) (srcSlot dstSlot : CSpaceAddr)
    (hFresh : st.objects[dstSlot.rootId]?.map (fun o =>
      match o with | .cnode cn => cn.slots[dstSlot.slot]? | _ => none)
      = some none)
    (hCdtFresh : ¬ ∃ edge ∈ st.cdt.edges,
      edge.parent = cdtNodeOf dstSlot ∨ edge.child = cdtNodeOf dstSlot) :
    ¬ cdtReachable st.cdt (cdtNodeOf dstSlot) (cdtNodeOf srcSlot) := by
  intro hReach
  -- destNode has no outgoing edges (hCdtFresh), so no path from dest to src
  ...
```

**Files**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean` (~15 lines)

#### AE4-C4: Update `cspaceMintWithCdt` preservation to use proven acyclicity

**Scope**: Replace the externalized `hCdtPost` hypothesis in
`cspaceMintWithCdt_preserves_capabilityInvariantBundle` with a call to
`addEdge_preserves_acyclicity` + `cspaceMint_notReachable`.

This changes the theorem from:
```lean
theorem cspaceMintWithCdt_preserves ...
    (hCdtPost : cdtCompleteness st' ∧ cdtAcyclicity st') :
    capabilityInvariantBundle st'
```
to:
```lean
theorem cspaceMintWithCdt_preserves ...
    (hFresh : ...) (hCdtFresh : ...) :
    capabilityInvariantBundle st'
```

The acyclicity is now PROVEN from the operation's semantics, not assumed.

**Files**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean` (~15 lines
changed, replacing hypothesis with proof)

### AE4-D: Add `cdtMintCompleteness` to capability invariant bundle (U-36)

**Finding**: `cdtMintCompleteness` (Defs.lean:115–119) is not included in
the main `capabilityInvariantBundle` (Defs.lean:173–176, a 7-tuple). The
codebase provides a `capabilityInvariantBundleWithMintCompleteness` (line
114) as a convenience, but the main bundle used in cross-subsystem
composition does not include it.

This task is decomposed into 3 sub-steps:

#### AE4-D1: Add `cdtMintCompleteness` to bundle

**Scope**: Extend the bundle from 7-tuple to 8-tuple. This requires
updating all ~60 destructuring sites that pattern-match on the bundle.

**Risk mitigation**: Rather than modifying `capabilityInvariantBundle`
(which would require updating 60+ theorem signatures), use the existing
`capabilityInvariantBundleWithMintCompleteness` and make it the canonical
bundle at the cross-subsystem level. This avoids churn inside the
capability module while ensuring mint completeness is checked at the
composition layer.

**Change**: In `CrossSubsystem.lean`, replace any `capabilityInvariantBundle`
reference with `capabilityInvariantBundleWithMintCompleteness`.

**Files**: `SeLe4n/Kernel/CrossSubsystem.lean` (~3 lines)

#### AE4-D2: Prove `cdtMintCompleteness` preservation for `cspaceMint`

**Scope**: When minting, a new CDT edge is added (`src → dst`). Prove
the new child node (`dst`) satisfies `cdtMintCompleteness` — it is either
a child of an edge (it is, by construction of `addEdge`), or isolated.

**Files**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean` (~15 lines)

#### AE4-D3: Prove `cdtMintCompleteness` preservation for `cspaceDelete` and `cspaceRevokeCdt`

**Scope**: When deleting or revoking, edges are removed. Prove that
remaining nodes still satisfy `cdtMintCompleteness`. This follows from
the fact that deletion only removes edges involving the target node —
other nodes' edge relationships are unchanged.

**Files**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean` (~20 lines)

### AE4-E: Prove `endpointQueueRemove` fallback unreachability (U-24)

**Finding**: `endpointQueueRemove` (DualQueue/Core.lean:493–507) silently
absorbs predecessor/successor lookup failures. The fallback masks queue
corruption.

**Preferred approach**: Prove unreachability (maintains existing return type
and avoids adding a new error path that would need handling at all call sites).

This task is decomposed into 3 sub-steps:

#### AE4-E1: Identify the exact invariant that guarantees reachability

**Scope**: The `endpointQueueRemove` function patches predecessor's
`queueNext` and successor's `queuePrev`. The predecessor/successor exist
because the queue is well-linked. The relevant invariant is
`tcbQueueLinkIntegrity` from `IPC/Invariant/Structural.lean`.

Specifically, `tcbQueueLinkIntegrity` states: if a TCB has
`queuePrev = some predTid`, then `predTid` exists as a TCB in the object
store AND `predTid.queueNext = some tid`. Symmetrically for `queueNext`.

Determine the exact predicate name and signature by reading
`IPC/Invariant/Defs.lean` or `Structural.lean`.

**Files**: Research only — no code changes.

#### AE4-E2: Prove predecessor lookup always succeeds

**Scope**: Prove that under `dualQueueSystemInvariant` (which includes
`tcbQueueLinkIntegrity`), the predecessor TCB lookup always succeeds:

```lean
theorem queueRemove_predecessor_exists
    (st : SystemState) (tid : ThreadId) (predTid : ThreadId)
    (hInv : dualQueueSystemInvariant st)
    (hTcb : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hPrev : tcb.queuePrev = some predTid) :
    ∃ predTcb, st.objects[predTid.toObjId]? = some (.tcb predTcb) := by
  -- Extract tcbQueueLinkIntegrity from hInv
  -- Apply backward link consistency: queuePrev = some predTid →
  --   predTid is a TCB in the object store
  ...
```

Similarly prove `queueRemove_successor_exists` for the `queueNext` case.

**Files**: `SeLe4n/Kernel/IPC/DualQueue/Core.lean` or
`SeLe4n/Kernel/IPC/Invariant/Structural.lean` (~20 lines each)

#### AE4-E3: Annotate fallback branches as invariant-unreachable

**Scope**: Add documentation annotations at the fallback sites
(Core.lean:496, 504) referencing the unreachability theorems:

```lean
-- AE4-E/IPC-02: This branch is unreachable under dualQueueSystemInvariant.
-- See queueRemove_predecessor_exists / queueRemove_successor_exists.
-- Fallback preserves state unchanged (defensive, no corruption).
| _ => objs  -- unreachable under invariant (AE4-E2)
```

**Files**: `SeLe4n/Kernel/IPC/DualQueue/Core.lean` (~6 lines of comments)

### AE4-F: Document timeout sentinel and dual-condition mitigation (U-23)

**Finding**: Timeout detection uses `0xFFFFFFFF` sentinel in gpr x0
combined with `ipcState = .ready` check. The dual-condition substantially
mitigates false positives. For hardware binding, recommend replacing with
out-of-band `timedOut : Bool` TCB field.

**Change**: Add documentation to `Timeout.lean`:
```lean
/- Timeout Detection Sentinel (U-23/IPC-01)
   `timeoutAwareReceive` detects prior timeouts via a composite check:
   (1) gpr x0 = timeoutErrorCode (0xFFFFFFFF), AND
   (2) ipcState = .ready

   The AND condition mitigates false positives: legitimate IPC messages are
   delivered via `pendingMessage` and set ipcState to `.waitingForReply` or
   `.blocked`, not `.ready`. The gpr x0 sentinel is only written by
   `timeoutThread`, which also sets ipcState to `.ready`.

   For H3 hardware binding, consider replacing with a dedicated
   `timedOut : Bool` field on TCB to eliminate the sentinel pattern entirely.
   The composite check is sound for the current model but fragile if future
   operations modify gpr x0 without updating ipcState. -/
```

**Files modified**: `SeLe4n/Kernel/IPC/Operations/Timeout.lean` (~12 lines).

### AE4-G: Add TLB targeted flush composition theorem stubs (U-27)

**Finding**: Full TLB flush is used on every map/unmap. Targeted variants
exist but lack composition theorems. Required before H3 transition.

**Change**: Add theorem stubs (with `sorry` annotated as `TPI-H3`) for
the targeted flush composition theorems that will be needed for H3:

**WAIT** — the project forbids `sorry` in production proof surface. Instead,
add documentation-only preparation:

```lean
/- H3 Preparation: Targeted TLB Flush Composition (U-27/A-T01)
   When transitioning from full flush (`adapterFlushTlb`) to targeted
   flush (`adapterFlushTlbByAsid`, `adapterFlushTlbByVAddr`) for H3,
   the following composition theorems are required:

   1. `targetedFlushByAsid_sufficient`: prove that flushing only the
      modified ASID is sufficient for VSpace map/unmap correctness
   2. `targetedFlushByVAddr_sufficient`: prove that flushing only the
      modified VAddr within an ASID preserves VSpace invariants
   3. `targetedFlush_crossAsid_isolation`: prove that targeted flush
      does not affect other ASIDs

   These theorems must reference `tlbFlushByAsid_preserves_others`
   (TlbModel.lean:95) and `tlbFlush_crossAsid_isolation`
   (TlbModel.lean:128) as building blocks. -/
```

**Files modified**: `SeLe4n/Kernel/Architecture/VSpace.lean` (~15 lines
of documentation).

### AE4-H: Add IPC buffer cross-page validation (U-32)

**Finding**: IPC buffer validation (IpcBufferValidation.lean:49–70) does
not explicitly check that the buffer region (`addr` to
`addr + ipcBufferSize`) fits within a single mapped page.

**Change**: Add a cross-page boundary check after the existing alignment
and mapping checks:
```lean
-- AE4-H/A-IB01: Validate buffer does not cross page boundary
let pageSize := 4096  -- ARM64 4KB page
let pageStart := addr.toNat / pageSize * pageSize
let bufferEnd := addr.toNat + ipcBufferSize
if bufferEnd > pageStart + pageSize then
  .error .alignmentError
```

This check is redundant if the alignment check already guarantees
page-alignment of the IPC buffer address, but provides defense-in-depth
for hardware binding where page sizes may vary.

**Files modified**: `SeLe4n/Kernel/Architecture/IpcBufferValidation.lean`
(~6 lines).

### AE4-I: Generalize IPC capability transfer slot targeting (U-37)

**Finding**: All capability transfers target `Slot.ofNat 0`
(WithCaps.lean:28–33), overwriting previous transfers. Must be
generalized for hardware binding.

**Why this is complex**: `ipcTransferSingleCap` is defined in
`Capability/Operations.lean` (lines 1017–1038) and already accepts a
`slotBase` parameter and `scanLimit`. The slot-0 hardcoding occurs at
the API dispatch layer (API.lean) where the receiver's `capRecvSlot`
information is not threaded through. The change spans the API layer,
WithCaps wrappers, and potentially the IPC invariant proofs.

This task is decomposed into 4 sub-steps:

#### AE4-I1: Thread `capRecvSlot` from API dispatch to WithCaps

**Scope**: The receiver's `capRecvSlot` is extracted from the message info
register during syscall decode. Currently, the WithCaps functions
(`endpointSendDualWithCaps`, `endpointCallWithCaps`) receive the sender's
extra caps but not the receiver's target slot information.

Add a `capRecvSlot : Slot` parameter to `endpointSendDualWithCaps` and
`endpointCallWithCaps` (WithCaps.lean). Thread this from the
`dispatchWithCapChecked` call sites in API.lean where the decoded message
info is available.

**Files**: `SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean` (~5 lines parameter
changes), `SeLe4n/Kernel/API.lean` (~4 lines to pass `capRecvSlot`)

#### AE4-I2: Use `capRecvSlot` as `slotBase` in `ipcUnwrapCaps`

**Scope**: `ipcUnwrapCaps` (CapTransfer.lean or WithCaps.lean) calls
`ipcTransferSingleCap` with `slotBase := Slot.ofNat 0`. Replace with
the `capRecvSlot` parameter from AE4-I1.

For multiple cap transfers (up to `maxExtraCaps = 3`), use
`slotBase + transferIndex` to target consecutive slots:
```lean
let targetSlot := Slot.ofNat (capRecvSlot.toNat + capIndex)
```

This matches seL4 semantics where the receiver specifies a CSpace region
and caps are placed at consecutive slots starting from `capRecvSlot`.

**Files**: `SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean` (~8 lines)

#### AE4-I3: Update CDT tracking for per-slot transfers

**Scope**: Currently, CDT entries for transferred caps all reference
`Slot.ofNat 0`. With per-slot targeting, each transferred cap gets its
own unique slot in the CDT. This is actually a correctness improvement —
CDT-based revocation of one transferred cap will no longer inadvertently
revoke all transferred caps (eliminates the over-revocation noted at
WithCaps.lean lines 37–42).

Update `ensureCdtNodeForSlot` calls to use the actual target slot.

**Files**: `SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean` (~5 lines)

#### AE4-I4: Verify IPC invariant preservation after slot generalization

**Scope**: The `ipcInvariantFull` preservation proofs (Structural.lean)
must still hold with per-slot targeting. The key invariants are:
- `capabilityRightsMonotonicity` — still holds (attenuated caps)
- `cdtCompleteness` — each slot has its own CDT node now
- `cspaceSlotUnique` — must verify no slot collision when `maxExtraCaps`
  caps are placed at `capRecvSlot + 0..2`

Run `lake build SeLe4n.Kernel.IPC.Invariant` and fix any breakages.

**Files**: Potentially `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
(~10 lines if proofs need updating)

### AE4-J: Verify AE4 gate conditions

**Gate verification**:
1. Module builds for all modified files
2. `lake build` — full build clean
3. `./scripts/test_full.sh` — all tiers including invariant surface anchors
4. Verify CDT acyclicity preservation proof compiles without sorry
5. Verify CPtr masking does not break existing `resolveCapAddress` tests
6. Verify zero sorry/axiom in all modified files


---

## 7. Phase AE5 — Platform, Service & Cross-Subsystem

**Goal**: Address platform boot invariant gaps, cross-subsystem fuel
exhaustion, service registry ordering, and NI boundary documentation.
**Gate**: `lake build` + `./scripts/test_full.sh`
**Dependencies**: AE2 (Liveness integration), AE3 (SchedContext fixes).
**Estimated scope**: ~90–125 lines of changes (mostly documentation +
~25 lines for registryEndpointUnique invariant/check).

### AE5-A: Formalize `collectQueueMembers` fuel sufficiency (U-22)

**Finding**: `collectQueueMembers` (CrossSubsystem.lean:50–60) returns `[]`
on fuel exhaustion, silently truncating the queue. The fuel-sufficiency
argument depends on `tcbQueueChainAcyclic` but this connection is not
formalized (TPI-DOC deferred at line 96–98).

**Change**: Two options (choose based on proof complexity):

**Option 1 — Error on exhaustion** (simpler):
```lean
def collectQueueMembers ... (fuel : Nat) ... : Option (List ThreadId) :=
  match fuel with
  | 0 => none  -- Changed: return none instead of []
  | fuel' + 1 => ...
```

Update callers to handle the `none` case as an invariant violation.

**Option 2 — Prove fuel sufficiency** (stronger):
```lean
theorem collectQueueMembers_fuel_sufficient
    (st : SystemState) (headTid : ThreadId)
    (hAcyclic : tcbQueueChainAcyclic st headTid)
    (hFuel : fuel ≥ queueLength st headTid) :
    (collectQueueMembers st headTid fuel).length = queueLength st headTid := by
  ...
```

Option 1 is recommended for this phase. Option 2 can be pursued as
follow-up if the invariant violation scenario needs formal exclusion.

**Files modified**: `SeLe4n/Kernel/CrossSubsystem.lean` (~5–10 lines).

### AE5-B: Add `registryEndpointUnique` invariant (U-20)

**Finding**: `lookupServiceByCap` depends on RHTable insertion order.
No invariant prevents multiple services from registering the same endpoint.

**Change**: Add an invariant to `Service/Registry/Invariant.lean`:
```lean
def registryEndpointUnique (st : SystemState) : Prop :=
  ∀ svc1 svc2 : ServiceId,
    st.serviceRegistry.get? svc1 |>.map (·.endpointId) =
    st.serviceRegistry.get? svc2 |>.map (·.endpointId) →
    svc1 = svc2 ∨
    st.serviceRegistry.get? svc1 = none ∨
    st.serviceRegistry.get? svc2 = none
```

Add preservation proofs for `registerService` (which should check for
duplicates before registration) and `revokeService`.

Add a runtime uniqueness check in `registerService`:
```lean
-- AE5-B: Reject duplicate endpoint registration
let duplicate := st.serviceRegistry.fold false fun acc _ entry =>
  acc || (entry.endpointId == newEndpointId)
if duplicate then .error .invalidArgument
```

**Files modified**:
- `SeLe4n/Kernel/Service/Registry.lean` (~5 lines for check)
- `SeLe4n/Kernel/Service/Registry/Invariant.lean` (~20 lines for invariant
  + preservation)

### AE5-C: Add `registryInterfaceValid` to `crossSubsystemInvariant` (SVC-04)

**Finding**: `crossSubsystemInvariant` includes `registryEndpointValid`
but not `registryInterfaceValid`. Gap in cross-subsystem coverage.

**Change**: Add `registryInterfaceValid` to the cross-subsystem invariant
bundle in `CrossSubsystem.lean`:
```lean
def crossSubsystemInvariant (st : SystemState) : Prop :=
  ... ∧
  registryInterfaceValid st ∧  -- AE5-C: Added
  ...
```

Add preservation to the appropriate bridge lemmas.

**Files modified**: `SeLe4n/Kernel/CrossSubsystem.lean` (~5 lines +
preservation updates).

### AE5-D: Document boot invariant bridge limitation (U-21)

**Finding**: `bootToRuntime_invariantBridge_empty` proves the 10-component
`proofLayerInvariantBundle` holds for the empty config only. Non-empty
hardware boot lacks formal guarantee. Deferred to WS-V.

**Change**: Add documentation to `Platform/Boot.lean`:
```lean
/- Boot-to-Runtime Invariant Bridge — Known Limitation (U-21/PLT-01)
   `bootToRuntime_invariantBridge_empty` proves the full 10-component
   `proofLayerInvariantBundle` holds after booting with an empty
   PlatformConfig. For non-empty configs (real hardware with IRQ tables,
   pre-allocated objects), the full bundle is NOT proven to hold.

   The checked boot path `bootFromPlatformChecked` validates per-object
   well-formedness and uniqueness, but does not prove the resulting state
   satisfies all 10 runtime invariants simultaneously.

   Remediation deferred to WS-V (hardware binding). When RPi5 boot is
   implemented, either:
   (a) Prove `bootToRuntime_invariantBridge` for arbitrary well-formed
       PlatformConfig, or
   (b) Add a post-boot runtime invariant validation pass that asserts all
       10 invariants hold before enabling syscall dispatch. -/
```

**Files modified**: `SeLe4n/Platform/Boot.lean` (~15 lines).

### AE5-E: Document NI boundary for service orchestration (U-10)

**Finding**: Service orchestration internals are explicitly documented as
outside the NI projection boundary by `serviceOrchestrationOutsideNiBoundary`
theorem. If orchestration becomes security-relevant, the boundary must be
extended.

**Change**: Add documentation to `Projection.lean` near the existing
boundary theorem:
```lean
/- NI Projection Boundary — Service Orchestration (U-10/IF-06)
   Service orchestration actions (lifecycle transitions, restart policies,
   heartbeat monitoring) are explicitly OUTSIDE the NI projection boundary.
   This means the NI proofs do not cover information flows through:
   - Restart timing (a service restart could leak cross-domain timing)
   - Lifecycle state transitions visible to other domains
   - Heartbeat failure detection patterns

   This is an accepted scope limitation for the current kernel model.
   If service orchestration becomes security-relevant for a deployment,
   extend `ObservableState` to include orchestration state and prove NI
   preservation for orchestration transitions. -/
```

**Files modified**: `SeLe4n/Kernel/InformationFlow/Projection.lean` (~12 lines).

### AE5-F: Document `LabelingContextValid` runtime enforcement gap (IF-14)

**Finding**: `LabelingContextValid` coherence is a deployment requirement
but not enforced at runtime. A malformed labeling context could permit
unauthorized flows.

**Change**: Add documentation to `Composition.lean` near the
`LabelingContextValid` definition and to the deployment guide:
```lean
/- LabelingContextValid — Deployment Requirement (IF-14)
   `LabelingContextValid` ensures the labeling context is coherent:
   all thread labels are consistent with their domain assignments,
   all kernel object labels respect the capability derivation tree,
   and no label escalation paths exist.

   This is a DEPLOYMENT REQUIREMENT — the kernel does not validate
   `LabelingContextValid` at runtime. The platform binding (H3) must
   construct a valid labeling context during boot, and the boot
   sequence must be proven (or runtime-checked) to produce a valid
   context. See PLT-01 (U-21) for the boot invariant bridge. -/
```

**Files modified**: `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean`
(~12 lines).

### AE5-G: Verify AE5 gate conditions

**Gate verification**:
1. Module builds for all modified files
2. `lake build` — full build clean
3. `./scripts/test_full.sh` — all tiers pass
4. Verify `registryEndpointUnique` preservation compiles
5. Verify `collectQueueMembers` behavior change does not break cross-subsystem
   invariant checks
6. Verify zero sorry/axiom in all modified files


---

## 8. Phase AE6 — Testing, Documentation & Closure

**Goal**: Fix testing gaps (execute PIP suite, upgrade test state construction,
fix silent CI failures), synchronize documentation, and close the workstream.
**Gate**: `./scripts/test_full.sh` + documentation sync + workstream history
**Dependencies**: AE1–AE5 (all code changes must be complete before closure).
**Estimated scope**: ~65–90 lines of changes (test script edits, doc sync,
fixture update).

### AE6-A: Execute PriorityInheritanceSuite in test scripts (U-25)

**Finding**: `priority_inheritance_suite` is registered in `lakefile.toml`
(line 76) but never invoked by any test script. D4 PIP tests (propagation,
blocking chains, reversion, SchedContext integration) are dead tests.

**Change**: Add the suite to `scripts/test_tier2_negative.sh` between
the D3 (IPC buffer) and D5 (liveness) entries:
```bash
# D4: Priority Inheritance Protocol
run_check "TRACE" lake exe priority_inheritance_suite
```

Also verify the suite passes: `lake exe priority_inheritance_suite`

**Files modified**: `scripts/test_tier2_negative.sh` (~1 line).

### AE6-B: Upgrade test suites to use `buildChecked` (T-07, T-F02, T-F03)

**Finding**: Several test suites use unchecked `builder.build` or raw
struct construction, creating states without invariant validation.

**Change**: Update the following test files to use `buildChecked` where
appropriate:
1. `tests/SuspendResumeSuite.lean` — replace `builder.build` with
   `builder.buildChecked` for main test states
2. `tests/PriorityManagementSuite.lean` — same
3. `tests/PriorityInheritanceSuite.lean` — same
4. `tests/IpcBufferSuite.lean` — same
5. `tests/TraceSequenceProbe.lean` — replace raw struct construction
   with `buildChecked` where feasible

For test cases that deliberately create invalid states (e.g., already-inactive
threads), keep `builder.build` with an explicit annotation:
```lean
-- Intentionally unchecked: testing edge case with pre-inactive thread
let st := builder.build
```

**Files modified**: 4–5 test files (~30 lines total).

### AE6-C: Fix `test_rust.sh` silent exit on missing cargo (T-F17)

**Finding**: `test_rust.sh` silently exits 0 when `cargo` is not found,
causing Rust ABI tests to be skipped without failing CI.

**Change**: Make the cargo check explicit and fail loudly:
```bash
if ! command -v cargo &>/dev/null; then
  echo "ERROR: cargo not found — Rust ABI tests SKIPPED"
  echo "Install Rust toolchain to run ABI tests"
  exit 1
fi
```

Alternatively, if skipping Rust tests on non-Rust environments is
intentional, make it a warning but set a non-zero exit status:
```bash
if ! command -v cargo &>/dev/null; then
  echo "WARN: cargo not found — Rust ABI tests skipped"
  echo "RUST_TESTS_SKIPPED=true" >> "$GITHUB_OUTPUT" 2>/dev/null || true
  exit 0  # Keep exit 0 but log the skip
fi
```

**Decision**: Use warning + log approach for CI compatibility, since not
all environments have Rust installed. Add a CI check that verifies Rust
tests ran on at least the primary CI runner.

**Files modified**: `scripts/test_rust.sh` (~5 lines).

### AE6-D: Fix Rust ABI SchedContext register comment (R-F01)

**Finding**: `sele4n-abi/src/args/sched_context.rs:16,29` says "x6=domain"
but x6 is not in the ABI register array. The 5th field (domain) is correctly
handled via IPC buffer overflow.

**Change**: Update the comment:
```rust
// Register mapping: x0=budget, x1=period, x2=priority, x3=deadline
// overflow[0]=domain (5th field via IPC buffer overflow pattern)
```

**Files modified**: `sele4n-abi/src/args/sched_context.rs` (~2 lines).

### AE6-E: Update CLAUDE.md with large file sizes and new annotations

**Finding**: Several file sizes in `CLAUDE.md` are stale. New annotations
needed for FrozenOps experimental status.

**Change**:
1. Update the "Known large files" section with current line counts
2. Add `(experimental, Q7)` annotation to FrozenOps entries in source layout
3. Add the workstream plan file itself to the large-files list

**Files modified**: `CLAUDE.md` (~10 lines).

### AE6-F: Synchronize documentation

**Change**: Update the following documents to reflect AE1–AE5 changes:
1. `docs/WORKSTREAM_HISTORY.md` — add WS-AE entry with phase summary
2. `docs/DEVELOPMENT.md` — update dispatch coverage, NI proof status
3. `docs/CLAIM_EVIDENCE_INDEX.md` — update any claims affected by new
   theorems (dispatch completeness, NI composition, CDT acyclicity)
4. `docs/codebase_map.json` — regenerate if Lean source structure changed

**Files modified**: 3–4 documentation files (~40 lines total).

### AE6-G: Final verification and closure

**Gate verification**:
1. `./scripts/test_full.sh` — all tiers pass including new PIP suite
2. `grep -r 'sorry' SeLe4n/` — zero matches
3. `grep -r 'axiom' SeLe4n/` — zero matches (excluding `axiom` in comments)
4. Verify main trace smoke fixture still matches:
   `diff <(lake exe sele4n) tests/fixtures/main_trace_smoke.expected`
5. All documentation synchronized
6. Workstream history updated

### AE6-H: Update test fixture if dispatch changes affect trace output

**Finding**: AE1-A adds `.tcbSetPriority` and `.tcbSetMCPriority` to the
checked dispatch path. If the main trace harness exercises these syscalls
through `syscallEntryChecked`, the trace output may change.

**Change**: If the fixture changes:
1. Run `lake exe sele4n > /tmp/new_trace.txt`
2. Diff against `tests/fixtures/main_trace_smoke.expected`
3. Verify all differences are expected (new success paths for previously-
   failing priority syscalls)
4. Update `tests/fixtures/main_trace_smoke.expected` with the new output
5. Update the SHA-256 companion file if present

**Files modified**: `tests/fixtures/main_trace_smoke.expected` (conditional).


---

## 9. Dependency Graph

```
AE1 ─────────────────────────────────────────────────────────────────┐
 ├── AE1-A: dispatchCapabilityOnly + tcbSetPriority/MCPriority       │
 ├── AE1-B: dispatchCapabilityOnly + tcbSetIPCBuffer (depends: A)    │
 ├── AE1-C: Fix wildcard comment (depends: A, B)                     │
 ├── AE1-D: Wildcard unreachability theorem (depends: A, B, C)       │
 ├── AE1-E: switchDomain NI constructor                              │
 ├── AE1-F: call/reply donation/PIP NI (depends: E)                  │
 │    ├── F1: applyCallDonation NI proof                              │
 │    ├── F2: propagatePIP NI proof                    ─┐             │
 │    ├── F3: applyReplyDonation NI proof               │ parallel    │
 │    ├── F4: revertPIP NI proof (depends: F2)         ─┘             │
 │    ├── F5: Composed call theorem (depends: F1, F2)                 │
 │    └── F6: Composed reply theorem + constructors (depends: F3–F5)  │
 ├── AE1-G: Master dispatch NI theorem (depends: A–F)                │
 │    ├── G1: SyscallId → NI theorem mapping (depends: A, B)         │
 │    ├── G2: capabilityOnly_preserves_projection lemma               │
 │    └── G3: 25-way dispatch theorem (depends: G1, G2, F)           │
 └── AE1-H: Gate verification (depends: A–G)                         │
                                                                      │
AE2 (parallel with AE1) ─────────────────────────────────────────────┤
 ├── AE2-A: RHTable capacity guard                                    │
 ├── AE2-B: RadixTree key bounds                                      │
 ├── AE2-C: RobinHood fuel docs (parallel with A, B)                 │
 ├── AE2-D: FrozenOps partial mutation fix                            │
 ├── AE2-E: FrozenOps status documentation (parallel with D)         │
 ├── AE2-F: Liveness production import                                │
 ├── AE2-G: PIP Preservation reachability (depends: F)                │
 └── AE2-H: Gate verification (depends: A–G)                         │
                                                                      │
AE3 (depends: AE1) ──────────────────────────────────────────────────┤
 ├── AE3-A: Domain consistency invariant                              │
 │    ├── A1: Define boundThreadDomainConsistent predicate             │
 │    ├── A2: Add domain check to schedContextBind                    │
 │    ├── A3: Add to scheduler invariant bundle (depends: A1)         │
 │    └── A4: Prove preservation for 5 operations (depends: A1–A3)   │
 ├── AE3-B: cancelDonation isActive fix                               │
 ├── AE3-C: cancelDonation replenish queue (depends: B)               │
 ├── AE3-D: resumeThread effective priority                           │
 ├── AE3-E: handleYield effective priority                            │
 ├── AE3-F: schedContextConfigure replenishment reset                 │
 ├── AE3-G: CBS/admission docs (parallel with A–F)                   │
 ├── AE3-H: Delete Budget.refill                                      │
 ├── AE3-I: PIP blockingServer frame theorem                          │
 ├── AE3-J: schedContextBind docs                                     │
 ├── AE3-K: timeoutBlockedThreads docs                                │
 └── AE3-L: Gate verification (depends: A–K)                         │
                                                                      │
AE4 (depends: AE1) ──────────────────────────────────────────────────┤
 ├── AE4-A: CPtr masking                                              │
 ├── AE4-B: VAddr canonical check on unmap                            │
 ├── AE4-C: CDT addEdge acyclicity lemma                              │
 │    ├── C1: Understand edgeWellFounded formulation                  │
 │    ├── C2: Prove addEdge_preserves_acyclicity (depends: C1)        │
 │    ├── C3: Prove hNotReachable for mint (depends: C1)              │
 │    └── C4: Wire into cspaceMintWithCdt (depends: C2, C3)          │
 ├── AE4-D: cdtMintCompleteness bundle (depends: C)                  │
 │    ├── D1: Promote at CrossSubsystem level                         │
 │    ├── D2: Prove preservation for cspaceMint                       │
 │    └── D3: Prove preservation for delete/revoke                    │
 ├── AE4-E: endpointQueueRemove proof/annotation                     │
 │    ├── E1: Identify guaranteeing invariant                         │
 │    ├── E2: Prove predecessor/successor existence (depends: E1)     │
 │    └── E3: Annotate unreachable fallbacks (depends: E2)            │
 ├── AE4-F: Timeout sentinel documentation                            │
 ├── AE4-G: TLB targeted flush docs                                   │
 ├── AE4-H: IPC buffer cross-page check                              │
 ├── AE4-I: Cap transfer slot generalization                          │
 │    ├── I1: Thread capRecvSlot from API to WithCaps                 │
 │    ├── I2: Use capRecvSlot as slotBase (depends: I1)               │
 │    ├── I3: Update CDT tracking (depends: I2)                       │
 │    └── I4: Verify IPC invariant preservation (depends: I1–I3)      │
 └── AE4-J: Gate verification (depends: A–I)                         │
                                                                      │
AE5 (depends: AE2, AE3) ────────────────────────────────────────────┤
 ├── AE5-A: collectQueueMembers fuel                                  │
 ├── AE5-B: registryEndpointUnique                                    │
 ├── AE5-C: registryInterfaceValid in cross-subsystem                │
 ├── AE5-D: Boot invariant bridge documentation                      │
 ├── AE5-E: NI boundary service documentation                        │
 ├── AE5-F: LabelingContextValid documentation                       │
 └── AE5-G: Gate verification (depends: A–F)                         │
                                                                      │
AE6 (depends: AE1–AE5) ─────────────────────────────────────────────┘
 ├── AE6-A: Execute PIP suite in test scripts
 ├── AE6-B: Upgrade test suites to buildChecked
 ├── AE6-C: Fix test_rust.sh silent exit
 ├── AE6-D: Fix Rust ABI register comment
 ├── AE6-E: Update CLAUDE.md
 ├── AE6-F: Synchronize documentation
 ├── AE6-G: Final verification and closure
 └── AE6-H: Update test fixture if needed
```

**Parallelism opportunities**:
- AE1 and AE2 can execute in parallel (independent subsystems)
- AE3 and AE4 can execute in parallel (both depend only on AE1)
- Within AE1-F: F1, F2, F3 are fully parallel; F4 depends on F2 only
- Within AE4: C and E are independent; I is independent of C/D/E
- Within each phase, documentation-only sub-tasks can execute in parallel
  with code changes (e.g., AE3-G/J/K parallel with AE3-A/B/D;
  AE4-F/G parallel with AE4-C/E/I)

**Critical path**: AE1-A → AE1-B → AE1-F (F1+F2∥F3 → F5 → F6) → AE1-G3 → AE3 → AE5 → AE6

---

## 10. Scope Estimates

Estimates are based on the decomposed sub-task analysis. Line counts include
code, proofs, and documentation changes per phase.

| Phase | Code (lines) | Proofs (lines) | Docs (lines) | Total |
|-------|--------------|----------------|---------------|-------|
| AE1   | 60–80        | 290–380        | 15–20         | 365–480 |
| AE2   | 45–60        | 20–30          | 35–45         | 100–135 |
| AE3   | 35–50        | 55–80          | 45–55         | 135–185 |
| AE4   | 55–75        | 130–190        | 55–65         | 240–330 |
| AE5   | 15–25        | 20–30          | 55–70         | 90–125 |
| AE6   | 15–20        | 0              | 50–70         | 65–90  |
| **Total** | **225–310** | **515–710** | **255–325** | **995–1345** |

### Decomposition-informed estimates (key tasks)

| Task | Sub-steps | Lines | Confidence |
|------|-----------|-------|------------|
| AE1-F (NI for donation/PIP) | 6 (F1–F6) | ~210 | Medium — depends on `pipBoost` in `projectTcb` |
| AE1-G (master dispatch NI) | 3 (G1–G3) | ~80–100 | High — mostly mechanical case split |
| AE3-A (domain consistency) | 4 (A1–A4) | ~45 | High — straightforward predicate + check |
| AE4-C (CDT acyclicity) | 4 (C1–C4) | ~60 | Medium — depends on `edgeWellFounded` formulation |
| AE4-D (cdtMintCompleteness) | 3 (D1–D3) | ~38 | High — bundle churn avoided via existing convenience |
| AE4-E (queue remove proof) | 3 (E1–E3) | ~46 | High — invariant already in place |
| AE4-I (cap slot generalize) | 4 (I1–I4) | ~40+ | Medium — IPC invariant cascade risk |

### Risk-adjusted estimates

| Risk Factor | Impact | Mitigation |
|-------------|--------|------------|
| AE1-F2/F4: `pipBoost` IS projected in `projectTcb` | +80–100 lines | Must prove identical `pipBoost` across runs (via blocking graph equivalence). Sub-steps F2/F4 documented both branches. |
| AE2-A: `RHTable.empty` call-site breakage | +20–30 lines | Scan all call sites first; provide `by omega` default parameter |
| AE4-C2: `edgeWellFounded` uses WellFounded relation | +20–40 lines | Accessibility predicate extension requires careful construction. Contradiction strategy documented in C2. |
| AE4-I4: IPC invariant cascade after slot generalization | +30–50 lines | Conservative approach: verify all 14 IPC invariants. `cspaceSlotUnique` most likely to need attention. |

**Worst-case total (all risks materialize)**: ~1,495–1,665 lines

---

## 11. Risk Analysis

### 11.1 Proof Regression Risks

| Change | Risk | Mitigation |
|--------|------|------------|
| AE1-E/F: NI constructor additions | New constructors in `NonInterferenceStep` add cases to `step_preserves_projection` | Each case directly delegates to existing per-op theorems; type-checker catches missing cases |
| AE2-A: `RHTable.empty` constraint change | All callers of `RHTable.empty` must provide `4 ≤ cap` proof | Default `by omega` handles all literal capacities ≥ 4 |
| AE3-F: Replenishment queue reset | `schedContextConfigure_preserves_invariant` may need reproving | New state is MORE invariant-satisfying (no stale entries) |
| AE4-A: CPtr masking | `resolveCapAddress` proofs may need `Nat.mod_eq_of_lt` | All CPtr values from `RegisterDecode` are bounded to 64 bits |
| AE4-C: CDT acyclicity lemma | Capability preservation proofs switch from hypothesis to proved | Strictly stronger — can only help, not break |

### 11.2 Behavioral Change Risks

| Change | Behavioral Impact | Risk Level |
|--------|-------------------|------------|
| AE1-A: Add priority dispatch arms | `.tcbSetPriority`/`.tcbSetMCPriority` now succeed in checked path | **Expected** — this is the fix |
| AE3-B: `isActive := false` in cancelDonation | Orphaned SchedContexts no longer processed by replenishment queue | **Correctness improvement** — matches `schedContextUnbind` |
| AE3-D: Effective priority in resumeThread | Preemption check may trigger more often (correct behavior) | **Correctness improvement** — catches missed preemptions |
| AE3-F: Replenishment queue reset | Old replenishment entries discarded on reconfigure | **Correctness improvement** — prevents stale entries |
| AE5-A: `collectQueueMembers` returns `none` | Callers must handle fuel exhaustion explicitly | **Breaking change** if callers expect `[]` on exhaustion |

### 11.3 Test Fixture Impact

The main trace fixture (`tests/fixtures/main_trace_smoke.expected`) may be
affected by AE1-A if the trace harness exercises `.tcbSetPriority` or
`.tcbSetMCPriority` through `syscallEntryChecked`. AE6-H handles fixture
updates.

---

## 12. Finding-to-Phase Traceability Matrix

Every actionable finding from both audits is mapped to exactly one phase
and sub-task. This matrix ensures no finding is overlooked.

| Finding ID(s) | Unified ID | Sub-task | Status |
|---------------|------------|----------|--------|
| F-01 (v14) | U-01 | AE1-A | COMPLETE (v0.25.15) |
| F-02 (v14) | U-02 | AE2-E | COMPLETE (v0.25.16) |
| IF-01 (v14) | U-03 | AE1-E | COMPLETE (v0.25.15) |
| IF-02 (v14) | U-04 | AE1-F | COMPLETE (v0.25.15) |
| F-03 (v14) | U-05 | AE2-F | COMPLETE (v0.25.16) |
| F-04 (v14) | U-06 | AE1-B | COMPLETE (v0.25.15) |
| F-05 (v14) | U-07 | AE1-C, AE1-D | COMPLETE (v0.25.15) |
| IF-03 (v14), IF-13 (v12) | U-08 | AE1-G | COMPLETE (v0.25.15) |
| IF-04 (v14), IF-02 (v12) | U-09 | AE5-F | PLANNED |
| IF-06 (v14), IF-04 (v12) | U-10 | AE5-E | PLANNED |
| S-02 (v14) | U-11 | AE3-A | PLANNED |
| SC-01 (v14), SC-02 (v12) | U-12 | AE3-G | PLANNED |
| SC-02 (v14) | U-13 | AE3-G | PLANNED |
| SC-03 (v14), SC-L04 (v12) | U-14 | AE3-F | PLANNED |
| SC-04 (v14) | U-15 | AE3-B | PLANNED |
| SC-05 (v14), SC-L06 (v12) | U-16 | AE3-D | PLANNED |
| CAP-01 (v14) | U-17 | AE4-A | PLANNED |
| CAP-02 (v14), C-CAP07 (v12) | U-18 | AE4-C | PLANNED |
| SVC-02 (v14) | U-20 | AE5-B | PLANNED |
| PLT-01 (v14) | U-21 | AE5-D | PLANNED |
| PLT-02 (v14), CS-01 (v12) | U-22 | AE5-A | PLANNED |
| IPC-01 (v14), I-T01 (v12) | U-23 | AE4-F | PLANNED |
| IPC-02 (v14) | U-24 | AE4-E | PLANNED |
| T-06 (v14), T-F01 (v12) | U-25 | AE6-A | PLANNED |
| ARCH-03 (v14), A-SA01 (v12) | U-26 | AE4-B | PLANNED |
| A-T01 (v12) | U-27 | AE4-G | PLANNED |
| D-RH01 (v12) | U-28 | AE2-A | COMPLETE (v0.25.16) |
| D-RT01 (v12) | U-29 | AE2-B | COMPLETE (v0.25.16) |
| D-RH02 (v12) | U-30 | AE2-C | COMPLETE (v0.25.16) |
| D-FO01 (v12) | U-31 | AE2-D | COMPLETE (v0.25.16) |
| A-IB01 (v12) | U-32 | AE4-H | PLANNED |
| A-SA02 (v12) | U-33 | — | DEFERRED (low risk) |
| A-SA03 (v12) | U-34 | — | DEFERRED (low risk) |
| C-CAP01 (v12) | U-35 | — | DEFERRED (seL4 design) |
| C-CAP06 (v12) | U-36 | AE4-D | PLANNED |
| I-WC01 (v12) | U-37 | AE4-I | PLANNED |
| SC-06 (v14) | — | AE3-H | PLANNED |
| SC-07 (v14) | — | AE3-C | PLANNED |
| SC-09 (v14) | — | AE3-J | PLANNED |
| S-01 (v14) | — | AE3-I | PLANNED |
| S-03 (v14) | — | AE3-E | PLANNED |
| S-05 (v14), S-02 (v12) | — | AE3-K | PLANNED |
| SVC-04 (v14) | — | AE5-C | PLANNED |
| IF-14 (v12) | — | AE5-F | PLANNED |
| T-07 (v14), T-F02/03 (v12) | — | AE6-B | PLANNED |
| T-F17 (v12) | — | AE6-C | PLANNED |
| R-F01 (v12) | — | AE6-D | PLANNED |
| SVC-01 (v14) | U-19 | — | NO ACTION (bridged by declarative layer) |

---

## 13. Deferred Findings (Future Workstreams)

The following findings are acknowledged but deferred to future workstreams:

| Finding | Reason for Deferral | Target Workstream |
|---------|--------------------|--------------------|
| A-SA02: `Slot.ofNat` range acceptance | Low risk; kernel validates at operation layer | WS-V (H3 hardening) |
| A-SA03: `AccessRightSet.ofNat` silent mask | Consistent with existing masking pattern; no exploit path | WS-V |
| C-CAP01: CSpace traversal rights omitted | Intentional seL4 divergence; rights enforced at operation layer | Design review |
| S-05: `timeoutBlockedThreads` O(n) | Performance optimization; needs benchmarking data first | Post-RPi5 profiling |
| IPC-03: Notification LIFO vs FIFO | Documented design choice; seL4 abstract model compatible | No change planned |
| CAP-03: No `cspaceRevoke` syscall | Design-in-progress for hardware target | WS-V |
| PLT-03: Sim PA width divergence | By design (simulation is idealized) | No change planned |
| PLT-06: RPi5 boot contract validates empty state | Requires hardware bring-up | WS-V |
| IF-07: Declassification well-formedness | Low risk; runtime checks exist | WS-V |
| IF-09: replyRecv decomposition assumption | Sound for sequential model | No change planned |
| IF-10: Scheduling covert channel | Standard NI scope limitation per Murray et al. | No change planned |
| F-10: `fromDtb` stub | Remove when `fromDtbFull` is canonical | WS-V |

---

## 14. Success Criteria

The WS-AE workstream is complete when ALL of the following are satisfied:

1. **Zero sorry/axiom**: `grep -r 'sorry\|axiom' SeLe4n/` returns zero
   matches in production code (excluding comments and string literals).

2. **All HIGH findings resolved**: U-01 through U-29 are either fixed
   with code changes or documented with explicit deferral rationale.

3. **All gate conditions pass**:
   - `lake build` — clean full build
   - `./scripts/test_smoke.sh` — all tiers pass
   - `./scripts/test_full.sh` — all tiers including invariant anchors
   - `lake exe priority_inheritance_suite` — D4 PIP tests execute

4. **Dispatch completeness proven**:
   - `dispatchWithCapChecked_wildcard_unreachable` theorem compiles
   - All 25 `SyscallId` variants handled in both dispatch paths

5. **NI composition complete**:
   - `NonInterferenceStep` has 35 constructors (32 existing + switchDomain
     + endpointCallWithDonation + endpointReplyWithReversion)
   - `step_preserves_projection` handles all 35 cases
   - Master dispatch NI theorem discharges all per-op proofs

6. **Data structure safety**:
   - `RHTable.empty` requires `4 ≤ capacity`
   - `buildCNodeRadix` validates key bounds
   - `collectQueueMembers` fails explicitly on fuel exhaustion

7. **Scheduler/SchedContext correctness**:
   - `cancelDonation` sets `isActive := false` and removes from replenish queue
   - `resumeThread` and `handleYield` use effective priority
   - `schedContextConfigure` resets replenishment queue

8. **Documentation synchronized**: `WORKSTREAM_HISTORY.md`, `DEVELOPMENT.md`,
   `CLAIM_EVIDENCE_INDEX.md`, and `CLAUDE.md` all updated.

---

*This workstream plan was generated from the combined findings of
`AUDIT_v0.25.12_KERNEL_MODULES.md` (166+ findings) and
`AUDIT_v0.25.14_COMPREHENSIVE.md` (88 findings). All HIGH and MEDIUM
findings were independently verified against source code before inclusion.
Deduplication identified 37 unique MEDIUM+ findings across both audits
(8 HIGH, 27 actionable MEDIUM, 3 deferred MEDIUM). Complex tasks were
decomposed into 73 atomic sub-steps across 6 phases with explicit
dependencies, parallelism analysis, gate conditions, and scope estimates
(~995–1,345 lines nominal; ~1,495–1,665 worst case).*

