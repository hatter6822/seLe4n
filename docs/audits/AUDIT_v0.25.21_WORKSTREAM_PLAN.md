# WS-AF Workstream Plan — Pre-Release Comprehensive Audit Remediation (v0.25.21)

**Created**: 2026-04-08
**Baseline version**: 0.25.21
**Baseline audits**:
  - `docs/audits/AUDIT_v0.25.21_PRE_RELEASE_COMPREHENSIVE.md` (2 HIGH, 24 MEDIUM, 53 LOW)
  - `docs/audits/AUDIT_v0.25.21_PRE_RELEASE_REVIEW.md` (1 HIGH, 22 MEDIUM, 30+ LOW)
**Prior portfolios**: WS-B through WS-AE (all COMPLETE — see `docs/WORKSTREAM_HISTORY.md`)
**Constraint**: Zero `sorry`/`axiom` in production proof surface

---

## 1. Executive Summary

Two independent pre-release audits of seLe4n v0.25.21 were conducted on
2026-04-07, collectively covering all 132 Lean modules (~100,000+ lines) and
31 Rust files across 3 ABI crates (~5,500 lines). Both audits independently
confirmed zero `sorry`/`axiom` across the entire production Lean codebase and
zero CVE-worthy vulnerabilities.

Every finding from both audits was independently verified against the source
code at claimed line references. This verification identified **5 erroneous
findings** (refuted by source evidence), plus **2 self-retracted findings**
already corrected by Audit 1's own errata (MED-S3 retracted: `switchDomain`
branch IS proven unreachable; MED-S7 retracted: `bounded_scheduling_latency_exists`
IS genuine proof work). Additionally, **3 intentional-design findings** were
confirmed but require documentation only, not code changes. All remaining
findings were confirmed accurate.

**Combined verified finding counts (after deduplication and refutation)**:

| Severity | Audit 1 | Audit 2 | Deduplicated | Refuted | Actionable |
|----------|---------|---------|--------------|---------|------------|
| HIGH     | 2       | 1       | 3            | 0       | 3          |
| MEDIUM   | 24      | 22      | 36           | 5       | 31         |
| LOW      | 53      | 30+     | 60+          | 0       | 15         |
| INFO     | 170+    | 20+     | 170+         | 0       | 0          |

### 1.1 Deduplication Analysis

Many findings appear in both audits with different IDs. The following
cross-references were established during source verification:

| Audit 1 ID | Audit 2 ID | Unified ID | Status |
|-------------|------------|------------|--------|
| HIGH-1 | — | AF-01 | CONFIRMED — `blockingAcyclic` absent from `crossSubsystemInvariant` |
| HIGH-2 | — | AF-02 | CONFIRMED — `bounded_scheduling_latency` is definitional unfolding |
| MED-M3 | CF-01 (HIGH) | AF-03 | CONFIRMED — `storeObject` always returns `.ok` |
| MED-I2 | IP-01 | AF-04 | CONFIRMED — timeout sentinel `0xFFFFFFFF` + ipcState |
| MED-D1 | PL-02 | AF-05 | CONFIRMED — `parseFdtNodes` fuel exhaustion returns `some []` |
| MED-I3 | IP-03 | AF-06 | CONFIRMED — direct `RHTable.insert`, not `storeObject` |
| MED-CS2 | LS-03 | AF-07 | CONFIRMED — fuel-sufficiency not formalized |
| MED-SC1 | SX-01 | AF-08 | CONFIRMED — CBS 8x bound / truncation (related) |
| MED-MM1 | PL-01 | AF-09 | CONFIRMED — MMIO model divergence + range validation |
| MED-S1 | SC-03 (Audit 2) | AF-10 | CONFIRMED — static tcb.priority/domain fallback |
| — | SC-01 (Audit 2) | AF-11 | CONFIRMED — `handleYield` uses static `tcb.priority` |
| — | IP-02 | AF-12 | CONFIRMED — stale documentation claims |

Findings unique to one audit were assigned AF-13 through AF-49.

### 1.2 Erroneous/Refuted Findings (No Action Required)

The following findings were **refuted** during independent source verification:

| Audit ID | Status | Evidence |
|----------|--------|----------|
| MED-M1 (Audit 1) | **REFUTED** | `AccessRightSet` has safe public constructors (`ofNat`, `mk_checked`, `singleton`, `ofList`) with formal validity proofs. Raw `mk` exists per Lean 4 limitation but is not the recommended API path. No exploitable bypass found. |
| MED-R3 (Audit 1) | **REFUTED** | `tcb_set_priority` accepts raw `u64` at the wrapper layer, but `SetPriorityArgs::decode()` in `sele4n-abi/src/args/tcb.rs` validates `regs[0] > MAX_PRIORITY` and returns `InvalidArgument`. Layered validation is by design. |
| MED-A1 (Audit 1) | **REFUTED** | `ThreadId.ofNat objId.toNat` is type-safe newtype conversion through `Nat` intermediate. Both types are `Nat` wrappers. The match statement enforces `.object objId` before conversion. Not identity conflation. |
| CF-04 (Audit 2) | **REFUTED** | `CNode.resolveSlot` does not need explicit `guardBounded` check because `CNode.wellFormed` includes `node.guardBounded` at construction, and `resolveSlot_guardMismatch_of_not_guardBounded` proves unbounded guards always fail. Sound by construction. |
| AP-01 (Audit 2) | **REFUTED** | `endpointSendDualChecked` receives resolved extra caps from `resolveExtraCaps` and validates downstream. Validation at enforcement layer, not resolution time, is correct design. |

### 1.3 Intentional-Design Findings (Document Only)

| Audit ID | Status | Evidence |
|----------|--------|----------|
| MED-R4 (Audit 1) | CONFIRMED — intentional | `lateout("x6") _` is correct ARM64 `clobber_abi("C")` behavior. x6 is caller-saved. No ABI extension planned. |
| IF-02 (Audit 2) | CONFIRMED — intentional | Non-standard BIBA integrity direction is formally witnessed by `integrityFlowsTo_is_not_biba` theorem. Deliberately reverses standard BIBA for authority-flow tracking. Documented in `DEPLOYMENT_GUIDE.md`. |
| LOW-SC1 (Audit 1) | CONFIRMED — intentional | `insertSorted` allows duplicate SchedContextId entries by design. `processReplenishments` is idempotent. Avoids O(n) deduplication scan per insert. |

### 1.4 Plan Structure

This plan organizes all actionable findings into **6 phases** (AF1–AF6) with
**49 top-level sub-tasks**, explicit dependencies, gate conditions, and scope
estimates. Phases are ordered by severity impact and dependency chain:

| Phase | Focus | Sub-tasks | Key Findings | Gate |
|-------|-------|-----------|--------------|------|
| AF1 | Scheduler correctness & proof gaps | 10 | HIGH-1, HIGH-2, SC-01, SC-03, MED-S1, MED-S4, MED-S5, SC-02 | `lake build` + `test_smoke.sh` |
| AF2 | State & model hardening | 7 | CF-01/MED-M3, CF-02, BF-02, BF-03, CF-03, MED-M2 | `lake build` + module verification |
| AF3 | Platform & DeviceTree hardening | 7 | MED-D1/PL-02, PL-01, PL-04, MED-MM1, MED-B1 | `lake build` + `test_smoke.sh` |
| AF4 | Information flow, cross-subsystem & SchedContext | 8 | MED-IF1, MED-CS1, MED-CS2, MED-SV1, IF-01, MED-SC1/SX-01, SX-02 | `lake build` + `test_full.sh` |
| AF5 | IPC, capability, lifecycle & documentation | 10 | IP-02, MED-I1, MED-I2, MED-I3, CA-02/BF-01, CA-03, LS-01, MED-S3 | `lake build` + `test_full.sh` |
| AF6 | Rust ABI fixes & documentation closure | 7 | MED-R1, MED-R2, LOW-R1, LOW-R3, LOW-R7, LOW-R8, doc sync | `test_full.sh` + doc sync |

**Estimated scope**: ~643 base, ~993 worst-case total lines of changes.


---

## 2. Consolidated Finding Registry

### 2.1 HIGH Findings (3 actionable)

| Unified ID | Source | Subsystem | Description | Verified | Phase |
|------------|--------|-----------|-------------|----------|-------|
| AF-01 | HIGH-1 (A1) | Scheduler/PIP | `blockingAcyclic` defined at BlockingGraph.lean:115–116 but **absent** from `crossSubsystemInvariant` (CrossSubsystem.lean:284–293, 9 predicates). Comments at BlockingGraph.lean:62–77 **incorrectly claim** it is part of `crossSubsystemInvariant`. Never consumed by any downstream proof. PIP propagation terminates via fuel bound but correctness depends on this unproven assumption. | YES — all locations confirmed | AF1 |
| AF-02 | HIGH-2 (A1) | Scheduler/Liveness | `bounded_scheduling_latency` (WCRT.lean:132–139) proves `wcrtBound D L N B P = D * L + N * (B + P)` via `simp [wcrtBound]` — definitional unfolding with zero assurance beyond the definition. `bounded_scheduling_latency_exists` (line 153) IS genuine composition with real hypotheses (`hDomainActiveRunnable`, `hBandProgress`) but `WCRTHypotheses` must be instantiated externally. `pip_enhanced_wcrt_le_base` (line 278) is a genuine inequality. | YES — definitional vs genuine confirmed | AF1 |
| AF-03 | MED-M3 (A1) / CF-01 (A2) | Model/State | `storeObject` (State.lean:471–496) always returns `.ok` regardless of object store size. `storeObjectChecked` (State.lean:511–523) exists with `maxObjects = 65536` gate but `storeObject` is not restricted to internal use. Manual callsite audit (lines 458–470) is thorough but not machine-checked. | YES — both functions confirmed | AF2 |

### 2.2 MEDIUM Findings (28 actionable, after deduplication and refutation)

| Unified ID | Source | Subsystem | Description | Phase |
|------------|--------|-----------|-------------|-------|
| AF-04 | MED-I2 / IP-01 | IPC/Timeout | Timeout sentinel `0xFFFFFFFF` in gpr x0 + `ipcState = .ready` dual-condition check. Fragile — could collide with legitimate IPC data. H3 migration to `timedOut : Bool` recommended. Documented in AE4-F. | AF5 |
| AF-05 | MED-D1 / PL-02 | Platform/DeviceTree | `parseFdtNodes` fuel exhaustion returns `some ([], offset)` (silent success) instead of `none` (error). Malformed DTB could cause incomplete parse treated as success. `findMemoryRegProperty` correctly returns `none` on fuel exhaustion — inconsistency. | AF3 |
| AF-06 | MED-I3 / IP-03 | IPC/DualQueue | `endpointQueueRemove` (DualQueue/Core.lean:492–517) uses direct `RHTable.insert` instead of `storeObject`. Proven correct under `dualQueueSystemInvariant`. Defensive fallbacks silently preserve state on corruption, proven unreachable under invariants (AE4-E). | AF5 |
| AF-07 | MED-CS2 / LS-03 | CrossSubsystem | `collectQueueMembers` fuel-sufficiency not formally connected to `tcbQueueChainAcyclic`. AE5-A already changed return type to `Option` (fuel exhaustion → `none`). Documentation at lines 92–126 argues sufficiency but no theorem exists. TPI-DOC annotation at line 124. | AF4 |
| AF-08 | MED-SC1 / SX-01 | SchedContext | CBS bandwidth bound proves `totalConsumed <= 8 * budget` (8x gap from `maxReplenishments = 8`). Admission control uses integer floor division — each context underestimated by ≤1 per-mille. With 64 contexts, aggregate error ≤6.4%. Documented in AE3-G. | AF4 |
| AF-09 | MED-MM1 / PL-01 | Platform/RPi5 | (a) `mmioWrite32`/`mmioWrite64` validate only base address alignment and device region membership, not full [addr, addr+size) byte range. (b) General write functions use direct memory store; only `mmioWrite32W1C` models write-one-to-clear semantics. No `MmioWriteSafe` witness type. | AF3 |
| AF-10 | MED-S1 / SC-03 (A2) | Scheduler | `resolveEffectivePrioDeadline` (Selection.lean:307–318) falls back to `tcb.priority`/`tcb.deadline` when SchedContext lookup fails. `schedule` (Core.lean:292) uses static `tcb.domain` for domain check instead of effective domain. Inconsistent with `effectivePriority` which resolves from SchedContext. | AF1 |
| AF-11 | SC-01 (A2) | Scheduler | `handleYield` (Core.lean:337) re-enqueues at `tcb.priority` (static) instead of effective priority. Comment at line 330 acknowledges this as "legacy" behavior. 48-proof-site debt documented. | AF1 |
| AF-12 | IP-02 (A2) | IPC | Stale documentation at Endpoint.lean:325–337 claims `pendingMessage = none` invariant is "not formally proven" but `waitingThreadsPendingMessageNone` exists and is proven in WaitingThreadHelpers.lean (extracted in AC1-A). | AF5 |
| AF-13 | MED-S4 (A1) | Scheduler/PIP | `pip_deterministic` (BoundedInversion.lean:53–58) proves `f x = f x` given identical inputs via `subst; subst; subst; rfl`. Tautological — follows from purity. Name "deterministic" is misleading. | AF1 |
| AF-14 | MED-S5 (A1) | Scheduler/Liveness | `eventuallyExits` (BandExhaustion.lean:31–37) is an externalized Prop definition used as hypothesis in `higherBandExhausted` (line 47). Not derived from CBS budget finiteness or any kernel invariant. | AF1 |
| AF-15 | MED-I1 (A1) | IPC | `Badge.ofNatMasked badge.toNat` (Endpoint.lean:372) round-trips through unbounded `Nat`. Model-safe via `ofNatMasked` 64-bit masking. Hardware binding must ensure consistent masking. Documented in AC3/I-04. | AF5 |
| AF-16 | MED-IF1 (A1) | InformationFlow | `native_decide` at Wrappers.lean:286 for `enforcementBoundary_is_complete`. Only `native_decide` #1 in codebase. Bypasses proof kernel for 33-element enumeration. Replace with `decide` for stronger trust. | AF4 |
| AF-17 | MED-CS1 (A1) | CrossSubsystem | `native_decide` at CrossSubsystem.lean:705 for pairwise coverage proof. `native_decide` #2 in codebase. Extends TCB to Lean runtime evaluator. | AF4 |
| AF-18 | MED-SV1 (A1) | Service | `serviceHasPathTo` (Operations.lean:144) returns `true` on fuel exhaustion. Conservative for safety (prevents missed cycles) but causes spurious dependency rejection. Correctness proven under `serviceCountBounded`. | AF4 |
| AF-19 | MED-B1 (A1) | Platform/Boot | `natKeysNoDup` (Boot.lean:66–72) uses opaque `Std.HashSet`. Transparent alternative `listAllDistinct` (lines 79–81) exists but is not used in primary path. | AF3 |
| AF-20 | MED-R1 (A1) | Rust ABI | Unrecognized kernel errors (≥44) mapped to `InvalidSyscallNumber` (decode.rs:42). Semantic mismatch — an unknown error code is not an invalid syscall number. | AF6 |
| AF-21 | MED-R2 (A1) | Rust ABI | `endpoint_reply_recv` (ipc.rs:179–182) silently truncates to 3 registers when `msg.length > 3`. No error returned. | AF6 |
| AF-22 | CF-02 (A2) | Model/Prelude | `SchedContextId.ofObjId` (Prelude.lean:373) lacks sentinel check. `ThreadId.toObjIdChecked` (lines 140–143) has one. Asymmetry. | AF2 |
| AF-23 | CF-03 (A2) | Machine | `RegisterFile` BEq instance (Machine.lean:208–210) compares only GPR 0–31. Non-lawful — `not_lawfulBEq` theorem (line 217) provides formal counterexample. Safe for ARM64 but violates `LawfulBEq`. | AF2 |
| AF-24 | BF-02 (A2) | Model/Builder | `mapPage` (Builder.lean:284–296) accepts `perms : PagePermissions` without W^X validation. Boot could construct W+X mappings that freeze into execution state. | AF2 |
| AF-25 | BF-03 (A2) | Model/FreezeProofs | `apiInvariantBundle_frozenDirect` (FreezeProofs.lean:1085–1088) only checks `objects` field agreement via existential witness, not other SystemState fields. | AF2 |
| AF-26 | BF-01 / CA-02 | Builder/Capability | Raw `.2.2.2...` tuple projections in Builder.lean:128–210 and Capability/Invariant/Defs.lean:173–176 despite warning at Builder.lean:112. 16-tuple `schedulerInvariantBundleExtended` and 7-tuple `capabilityInvariantBundle` use unwieldy positional projections. | AF5 |
| AF-27 | CA-03 (A2) | Capability | `cspaceResolvePath` (Operations.lean:43–51) vs `resolveCapAddress` (Operations.lean:85–120) — overlapping semantics (single-level vs multi-level CSpace resolution). Relationship undocumented. | AF5 |
| AF-28 | LS-01 (A2) | Lifecycle | `suspendThread` (Suspend.lean:159–163) re-lookups TCB after `cancelIpcBlocking` because state may have changed. Fragile if cancellation ever modifies `schedContextBinding`. | AF5 |
| AF-29 | SC-02 (A2) | Scheduler/PIP | PIP propagation (Propagate.lean:60–72) reads `blockingServer` from pre-mutation state `st` (line 68) instead of post-`updatePipBoost` state `st'`. Sound by frame theorem `updatePipBoost_preserves_blockingServer` (AE3-I/S-01). | AF1 |
| AF-30 | SX-02 (A2) | SchedContext | `schedContextYieldTo` (Operations.lean:234–262) has no capability check. Pure function returning `SystemState`, not `Kernel Unit`. Documented as kernel-internal helper. | AF4 |
| AF-31 | MED-S3 (A1) | Scheduler | High heartbeat proofs: `handleYield_preserves_edfCurrentHasEarliestDeadline` requires 1,600,000 (Preservation.lean:2409), `timerTick` variant requires 800,000 (line 2494). 8x and 4x default respectively. Maintenance/fragility risk. | AF5 |
| AF-32 | PL-04 (A2) | Platform/DeviceTree | `extractPeripherals` (DeviceTree.lean:750–766) only searches top-level nodes + direct children (2 levels). May miss peripherals on complex board configs. | AF3 |
| AF-33 | IF-01 (A2) | InformationFlow | `LabelingContextValid` (Composition.lean:670–695) is a deployment requirement, not runtime-enforced. Documented in AE5-F. | AF4 |
| AF-34 | MED-M2 / CF-05 | Model/CDT | `descendantsOf` BFS transitive closure completeness deferred (Structures.lean:2232–2240). Direct children proven; full transitive closure deferred to hardware binding phase. | AF2 |

### 2.3 LOW Findings (18 actionable — selected for inclusion)

| Unified ID | Source | Subsystem | Description | Phase |
|------------|--------|-----------|-------------|-------|
| AF-35 | LOW-R1 (A1) | Rust ABI | Doc comment in `sele4n-types/src/lib.rs` says "43-variant" — should be "44-variant". | AF6 |
| AF-36 | LOW-R3 (A1) | Rust ABI | Stale comment in `decode.rs:39` says error codes "0–42" — actual max is 43. | AF6 |
| AF-37 | LOW-R7 (A1) | Rust ABI | Missing `SchedContext` marker type in `sele4n-sys/src/cap.rs`. Other object types (Endpoint, Notification, CNode, Tcb, VSpaceRoot, Untyped) all have markers. | AF6 |
| AF-38 | LOW-R8 (A1) | Rust ABI | `IpcMessage.length` (ipc.rs:28) is `pub` — allows external mutation bypassing `length ≤ 4` invariant. Should be private with getter. | AF6 |
| AF-39 | LOW-I7 (A1) | IPC | `donationChainAcyclic` (Invariant/Defs.lean:960–967) only prevents 2-cycles. Longer cycle prevention by structural argument (blocked-on-reply threads cannot initiate Call). Document explicitly. | AF5 |
| AF-40 | LOW-S1 (A1) | Scheduler | `RunQueue.size` field maintained but never consumed by scheduler decisions. Dead state. | AF1 |
| AF-41 | LOW-D2 (A1) | Platform | `classifyMemoryRegion` (DeviceTree.lean:317) always returns `.ram`. TODO for WS-V. | AF3 |
| AF-42 | LOW-D3 (A1) | Platform | `fromDtb` stub (DeviceTree.lean:136) always returns `none`. | AF3 |
| AF-43 | AP-04 (A2) | FrozenOps | Header claims "21 operations" but file defines 15. Stale count in module docstring. | AF5 |
| AF-44 | PL-05 (A2) | Platform/Boot | `bootFromPlatform` silently accepts empty `PlatformConfig`. | AF3 |
| AF-45 | PL-06 (A2) | Platform/Boot | `applyMachineConfig` only copies `physicalAddressWidth`, not full config. Name misleading. | AF3 |
| AF-46 | CI-04 (A2) | CI/Scripts | `shellcheck` enforcement is optional (skipped if unavailable). CI should install it. | AF6 |
| AF-47 | LOW-SC4 (A1) | SchedContext | `schedContextYieldTo` is pure function returning `SystemState`, not `Kernel Unit`. Cannot signal errors to callers. | AF4 |
| AF-48 | IF-03 (A2) | InformationFlow | Duplicate `cdt_only_preserves_projection` definitions (Operations.lean:46–70 and 958–985). | AF5 |
| AF-49 | LOW-S2 (A1) | Scheduler | `chooseBestRunnableBy` tie-breaking semantics (FIFO) implicit, not documented. | AF1 |

### 2.4 Findings Excluded from Remediation

The following findings require no code changes:

| Category | Finding IDs | Rationale |
|----------|-------------|-----------|
| **Refuted** | MED-M1, MED-R3, MED-A1, CF-04, AP-01 | Disproven by source evidence — see §1.2 |
| **Intentional design** | MED-R4, IF-02, LOW-SC1, LOW-I5, LOW-I6, LOW-A1, LOW-A2 | Documented design choices with formal witnesses or seL4 compatibility |
| **Already addressed by WS-AE** | MED-I2 (AE4-F), MED-CS2 (AE5-A), MED-SC1 (AE3-G), SC-02 (AE3-I/S-01), MED-I3 (AE4-E), IF-01 (AE5-F) | Prior workstream addressed the core issue; remaining items are documentation refinements |
| **Informational (A1)** | All 170+ INFO findings | Positive confirmations, no action needed |
| **Informational (A2)** | RH-01–RH-04, RS-03–RS-04, CI-01–CI-03, AR-03, IF-04 | Positive confirmations |
| **By-design LOW** | LOW-ML1–ML6, LOW-CA1–CA2, LOW-IF1–IF2, LOW-S3–S8, LOW-I1–I4, LOW-RH1–RH2, LOW-RT1, LOW-SC2–SC3, LOW-A1–A2, LOW-MM2, LOW-S01, LOW-F1–F2, LOW-B2, LOW-R2, LOW-R4–R6, LOW-R9 | Low-severity code quality or documented design decisions with no security impact |
| **Deferred to H3/WS-V** | MED-I2 (timedOut field), MED-MM1 (MmioWriteSafe type), MED-I1 (hardware masking), LOW-CA2, LOW-I3 | Hardware binding phase dependencies |


---

## 3. Phase AF1 — Scheduler Correctness & Proof Gaps

**Status**: PLANNED
**Goal**: Address the two HIGH findings (blocking graph acyclicity, WCRT
naming) and the scheduler priority/domain consistency issues that represent
the most significant formal-assurance gaps in the codebase.
**Gate**: `lake build` + `lake build SeLe4n.Kernel.Scheduler.PriorityInheritance.BlockingGraph`
+ `lake build SeLe4n.Kernel.Scheduler.Liveness.WCRT` + `./scripts/test_smoke.sh`
**Dependencies**: None (first phase).
**Estimated scope**: ~180–260 lines of changes.

### AF1-A: Correct misleading `blockingAcyclic` comments (AF-01)

**Finding**: Comments at BlockingGraph.lean:62–77 claim `blockingAcyclic` is
"from `crossSubsystemInvariant` (CrossSubsystem.lean)" but inspection of
CrossSubsystem.lean:284–293 reveals the 9-predicate bundle does NOT include
`blockingAcyclic`. The predicate is defined (line 115) but unintegrated.

**Change**: Correct the misleading comments in BlockingGraph.lean to accurately
state the current status. Replace claims of invariant membership with:
```lean
-- NOTE: `blockingAcyclic` is defined here as a safety property but is NOT
-- currently part of `crossSubsystemInvariant`. Fuel-bounded PIP propagation
-- (`propagatePriorityInheritance` uses `objectIndex.length` as fuel) prevents
-- non-termination, but chain-walk correctness depends on this assumption.
-- Formal integration is tracked as AF-01 (WS-AF workstream).
```

Update the docstring at `blockingChain_acyclic` (line 119) to note it is a
trivial restatement, not a proof from invariants.

**Files modified**: `SeLe4n/Kernel/Scheduler/PriorityInheritance/BlockingGraph.lean` (~15 lines)

### AF1-B: Add `blockingAcyclic` to `crossSubsystemInvariant` (AF-01)

**Finding**: The predicate exists but is not part of any invariant bundle.
PIP correctness structurally depends on it.

**Change**: Extend `crossSubsystemInvariant` from 9 to 10 predicates by adding
`blockingAcyclic st` as the 10th conjunct. This requires:

1. Add `blockingAcyclic` import to CrossSubsystem.lean (check for import cycle:
   `Scheduler.PriorityInheritance.BlockingGraph` — this is already transitively
   imported via Liveness import chain added in AE2-F, so no new cycle risk).

2. Add predicate to `crossSubsystemInvariant`:
   ```lean
   def crossSubsystemInvariant (st : SystemState) : Prop :=
     registryEndpointValid st ∧ registryInterfaceValid st ∧
     registryDependencyConsistent st ∧ noStaleEndpointQueueReferences st ∧
     noStaleNotificationWaitReferences st ∧ serviceGraphInvariant st ∧
     schedContextStoreConsistent st ∧ schedContextNotDualBound st ∧
     schedContextRunQueueConsistent st ∧ blockingAcyclic st  -- AF1-B
   ```

3. Update `crossSubsystemFieldSets` (9→10 entries, currently lines 865–874)
   and the `native_decide` pairwise coverage proof. The theorem
   `crossSubsystemFieldSets.length = 9` (line 877) must become `= 10`.
   New pairwise disjointness entries needed for `blockingAcyclic` vs each
   existing predicate (9 new pairs to prove).

4. Thread `hBlockAcyclic` through all 33+ per-operation bridge lemmas. Since
   `blockingAcyclic` depends only on `objects` (TCB `ipcState` fields),
   operations that don't modify `ipcState` can use a frame argument. Operations
   that DO modify `ipcState` (IPC send, receive, call, reply, notification,
   timeout) need per-operation proofs.

**Decomposition**:
- AF1-B1: Add predicate to bundle + update field disjointness (~20 lines)
- AF1-B2: Frame lemma for non-IPC operations (~30 lines, covers ~26 ops)
- AF1-B3: Per-operation proofs for IPC operations modifying `ipcState` (~40 lines, ~7 ops)
- AF1-B4: Boot state proof `bootState_blockingAcyclic` (~10 lines — empty state trivial)

**Risk**: Largest sub-task in AF1. If import cycle is discovered despite AE2-F
chain, fall back to AF1-A (comment correction only) and defer integration
to H3 workstream.

**Files modified**:
- `SeLe4n/Kernel/CrossSubsystem.lean` (~60 lines)
- `SeLe4n/Kernel/Scheduler/PriorityInheritance/BlockingGraph.lean` (~15 lines)
- `SeLe4n/Platform/Boot.lean` (~10 lines)

**Verification**: `lake build SeLe4n.Kernel.CrossSubsystem` +
`lake build SeLe4n.Platform.Boot`

### AF1-C: Rename `bounded_scheduling_latency` to `wcrtBound_unfold` (AF-02)

**Finding**: The name suggests a proven scheduling bound but the proof is
definitional unfolding (`simp [wcrtBound]`).

**Change**: Rename to `wcrtBound_unfold` and add clarifying docstring:
```lean
/-- `wcrtBound` definition unfolding. This is a definitional equality, not a
    scheduling guarantee. The substantive theorem is
    `bounded_scheduling_latency_exists` (below) which composes domain rotation
    and band exhaustion bounds under `WCRTHypotheses`. -/
theorem wcrtBound_unfold ...
```

Grep for `bounded_scheduling_latency` (excluding `_exists` and `_pip`) and
rename all references. Update Liveness test suite anchors if needed.

**Files modified**: `SeLe4n/Kernel/Scheduler/Liveness/WCRT.lean` (~10 lines)
**Verification**: `lake build SeLe4n.Kernel.Scheduler.Liveness.WCRT`

### AF1-D: Document `WCRTHypotheses` instantiation obligation (AF-02)

**Finding**: `bounded_scheduling_latency_exists` requires externally-provided
`WCRTHypotheses`. Neither `hDomainActiveRunnable` nor `hBandProgress` are
derived from kernel invariants.

**Change**: Add documentation block to WCRT.lean:
```lean
/-- ## WCRTHypotheses Instantiation Guide
    To use the WCRT bound for a concrete system:
    1. `hDomainMember`: Prove target thread is in a scheduled domain
    2. `hBandProgress`: Derive from CBS budget finiteness + `eventuallyExits`
    3. `hDomainActiveRunnable`: Prove a runnable thread exists per domain tick
    Future: derive (2) and (3) from kernel invariants + CBS budget bounds.
    See AF-14 for `eventuallyExits` status. -/
```

**Files modified**: `SeLe4n/Kernel/Scheduler/Liveness/WCRT.lean` (~15 lines)

### AF1-E: Rename `pip_deterministic` to `pip_congruence` (AF-13)

**Finding**: Proves `f x = f x` via `subst; subst; subst; rfl`. Congruence,
not determinism.

**Change**: Rename and update docstring:
```lean
/-- Congruence: `propagatePriorityInheritance` respects argument equality.
    Follows from purity — retained for explicit documentation. -/
theorem pip_congruence ...
```

**Files modified**: `SeLe4n/Kernel/Scheduler/PriorityInheritance/BoundedInversion.lean` (~5 lines)

### AF1-F: Document `eventuallyExits` hypothesis status (AF-14)

**Finding**: Used as hypothesis in `higherBandExhausted` but never derived.

**Change**: Add documentation to BandExhaustion.lean:31–37:
```lean
/-- `eventuallyExits` is an EXTERNALIZED HYPOTHESIS, not a derived property.
    For CBS-bound threads: should follow from budget finiteness (once
    `budgetRemaining` hits 0, `timerTick` removes the thread).
    For unbound threads: NOT satisfiable without external progress assumption.
    Future: derive from CBS budget finiteness for bound threads. -/
```

**Files modified**: `SeLe4n/Kernel/Scheduler/Liveness/BandExhaustion.lean` (~10 lines)

### AF1-G: Document priority/domain fallback rationale (AF-10)

**Finding**: `resolveEffectivePrioDeadline` falls back to static priority.
`schedule` uses static `tcb.domain`. Both safe under existing invariants.

**Change**: Add documentation to Selection.lean:307–318 and Core.lean:292:
```lean
-- AF1-G: Fallback to static TCB priority is safe because:
-- (1) Unbound threads pass budget check (`hasSufficientBudget` = true)
-- (2) Bound threads with missing SchedContext rejected by
--     `schedContextStoreConsistent` (crossSubsystemInvariant)
-- Domain check at Core.lean:292 safe under `boundThreadDomainConsistent`
-- (AE3-A: sc.domain == tcb.domain for bound threads).
```

**Files modified**: `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` (~8 lines),
`SeLe4n/Kernel/Scheduler/Operations/Core.lean` (~8 lines)

### AF1-H: Document `handleYield` legacy priority (AF-11)

**Finding**: Uses `tcb.priority` for re-insertion, not effective priority.

**Change**: Expand comment at Core.lean:330:
```lean
-- AF1-H: Re-enqueues at tcb.priority (static base), not effective priority.
-- Intentional: yield surrenders timeslice, moves to back of priority band.
-- PIP boost determines scheduling ORDER but not yield POSITION. The 48-proof
-- debt is tracked but yield semantics make this a non-bug.
```

**Files modified**: `SeLe4n/Kernel/Scheduler/Operations/Core.lean` (~8 lines)

### AF1-I: Document `RunQueue.size` and FIFO tie-breaking (AF-40, AF-49)

**Change**: Add annotations to RunQueue.lean and Selection.lean documenting
`size` field purpose and implicit FIFO tie-breaking semantics.

**Files modified**: `SeLe4n/Kernel/Scheduler/RunQueue.lean` (~5 lines),
`SeLe4n/Kernel/Scheduler/Operations/Selection.lean` (~5 lines)

### AF1-J: Document `blockingServer` pre-mutation read (AF-29)

**Change**: Add cross-reference at Propagate.lean:68:
```lean
-- AF1-J: Reads `blockingServer` from pre-mutation state `st`, not post-
-- `updatePipBoost` state `st'`. Sound because `updatePipBoost` only modifies
-- `pipBoost` (never `ipcState`). See AE3-I/S-01 frame theorems.
```

**Files modified**: `SeLe4n/Kernel/Scheduler/PriorityInheritance/Propagate.lean` (~6 lines)

### AF1 Summary

| Sub-task | Findings | Type | Lines | Dependencies |
|----------|----------|------|-------|--------------|
| AF1-A | AF-01 | Comment fix | ~15 | None |
| AF1-B | AF-01 | Proof + code | ~100 | AF1-A |
| AF1-C | AF-02 | Rename | ~10 | None |
| AF1-D | AF-02 | Documentation | ~15 | None |
| AF1-E | AF-13 | Rename | ~5 | None |
| AF1-F | AF-14 | Documentation | ~10 | None |
| AF1-G | AF-10 | Documentation | ~16 | None |
| AF1-H | AF-11 | Documentation | ~8 | None |
| AF1-I | AF-40, AF-49 | Documentation | ~10 | None |
| AF1-J | AF-29 | Documentation | ~6 | None |
| **Total** | | | **~195** | |

**Parallelism**: AF1-C through AF1-J can all run in parallel (no
interdependencies). AF1-B depends on AF1-A (comment correction first,
then integration). AF1-B is the critical path.


---

## 4. Phase AF2 — State & Model Hardening

**Status**: PLANNED
**Goal**: Address the `storeObject` capacity enforcement gap (the only
remaining HIGH from Audit 2), builder-phase W^X enforcement, identifier
sentinel consistency, and freeze pipeline documentation.
**Gate**: `lake build` + `lake build SeLe4n.Model.State` +
`lake build SeLe4n.Model.Builder` + `./scripts/test_smoke.sh`
**Dependencies**: None (independent of AF1).
**Estimated scope**: ~120–180 lines of changes.

### AF2-A: Make `storeObject` private or add machine-checked callsite proof (AF-03)

**Finding**: `storeObject` (State.lean:471–496) always returns `.ok`.
`storeObjectChecked` (State.lean:511–523) gates on `maxObjects` but
`storeObject` is publicly callable. Manual callsite audit at lines 458–470
is thorough but not machine-checked.

**Strategy**: Two options (choose one during implementation):

**Option A** (preferred): Add a machine-checked callsite theorem proving all
production `storeObject` callers are either (a) in-place mutations (ObjId
already in `objectIndexSet`) or (b) preceded by a `storeObjectChecked` gate.
```lean
/-- All non-retype callers of `storeObject` operate on existing ObjIds.
    New ObjId insertions go through `retypeFromUntyped` which uses
    `storeObjectChecked`. -/
theorem storeObject_callers_are_mutations_or_gated ...
```

**Option B** (simpler): Mark `storeObject` as `private` and expose only
`storeObjectChecked`. This requires auditing all direct `storeObject` callers
(~40+ sites) and routing them through `storeObjectChecked` or a new
`storeObjectExisting` variant that asserts ObjId already exists.

**Risk**: Option B has high blast radius (~40 callsite changes). Option A
is proof-only but requires a callsite enumeration lemma.

**Recommended approach**: Option A — add the callsite proof without modifying
the operational code. This preserves existing proof chains while providing
machine-checked assurance.

**Files modified**: `SeLe4n/Model/State.lean` (~30–50 lines for proof)

### AF2-B: Add `SchedContextId.ofObjIdChecked` sentinel guard (AF-22)

**Finding**: `SchedContextId.ofObjId` (Prelude.lean:373) unconditionally wraps
without sentinel check, unlike `ThreadId.toObjIdChecked`.

**Change**: Add a checked variant:
```lean
/-- AF2-B: Checked conversion that rejects the reserved sentinel (value 0).
    Mirrors `ThreadId.toObjIdChecked` for consistency. -/
def SchedContextId.ofObjIdChecked (oid : ObjId) : Option SchedContextId :=
  if oid.toNat = 0 then .none else .some ⟨oid.toNat⟩
```

Leave the unchecked `ofObjId` for backward compatibility but document
that `ofObjIdChecked` should be preferred at ABI boundaries.

**Files modified**: `SeLe4n/Prelude.lean` (~10 lines)

### AF2-C: Enforce W^X in builder-phase `mapPage` (AF-24)

**Finding**: `mapPage` (Builder.lean:284–296) accepts `perms : PagePermissions`
without W^X validation. Boot could construct W+X mappings.

**Change**: Add W^X check to `mapPage`:
```lean
def mapPage (ist : IntermediateState)
    (vsId : SeLe4n.ObjId) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions)
    : Except String IntermediateState :=
  if !perms.wxCompliant then
    .error "mapPage: W^X violation — write+execute permissions not permitted"
  else
    -- existing implementation
```

Update callers to handle the new error return. Boot sequence must use
W^X-compliant permissions.

**Files modified**: `SeLe4n/Model/Builder.lean` (~15 lines),
`SeLe4n/Platform/Boot.lean` (~5 lines for caller update)

### AF2-D: Document `apiInvariantBundle_frozenDirect` scope (AF-25)

**Finding**: `apiInvariantBundle_frozenDirect` (FreezeProofs.lean:1085–1088)
uses existential witness checking only `objects` field agreement.

**Change**: Add documentation explaining the existential design:
```lean
/-- AF2-D: This definition uses an existential witness (`∃ sst`) with
    objects-only field agreement because `apiInvariantBundle` predicates
    (scheduler, capability, IPC invariants) only examine `objects`. The
    theorem `apiInvariantBundle_frozenDirect_iff_frozen` (below) proves
    equivalence at freeze time. Non-objects fields (scheduler state,
    machine state) are frozen separately by `freezeSchedulerState`. -/
```

**Files modified**: `SeLe4n/Model/FreezeProofs.lean` (~8 lines)

### AF2-E: Document `RegisterFile` non-lawful BEq (AF-23)

**Finding**: BEq instance compares only GPR 0–31; formal counterexample at
line 217.

**Change**: Add documentation to Machine.lean:208 expanding the safety
analysis already present at lines 230–243:
```lean
-- AF2-E: Non-lawful BEq is a known and accepted limitation. ARM64 has
-- exactly 32 GPRs (x0–x30 + xzr). The `not_lawfulBEq` counterexample
-- at line 217 uses index 32 which is unreachable in practice. All
-- kernel code constructs RegisterFile from 32-element arrays.
-- LawfulBEq would require dependent typing (RegisterFile over Fin 32)
-- which conflicts with Lean 4 function extensionality.
```

**Files modified**: `SeLe4n/Machine.lean` (~8 lines)

### AF2-F: Document CDT transitive closure completeness deferral (AF-34)

**Finding**: `descendantsOf` BFS completeness for transitive closure deferred
to hardware binding phase.

**Change**: Add documentation to Structures.lean:2232–2240:
```lean
-- AF2-F: Transitive closure completeness is deferred to WS-V/H3 where
-- concrete CDT depth bounds (ARM64 page table levels) are available.
-- Direct-child completeness is proven by `descendantsOf_fuel_sufficiency`.
-- The structural argument: CDT is acyclic (proven by `cdtAcyclicity`),
-- so BFS with `edges.length` fuel terminates after visiting every node.
-- The formal connection between BFS fuel and acyclicity-bounded depth
-- requires the hardware-binding CDT depth constant.
```

**Files modified**: `SeLe4n/Model/Object/Structures.lean` (~10 lines)

### AF2-G: Gate verification

Build all modified modules and run `test_smoke.sh`.

### AF2 Summary

| Sub-task | Findings | Type | Lines | Dependencies |
|----------|----------|------|-------|--------------|
| AF2-A | AF-03 | Proof | ~40 | None |
| AF2-B | AF-22 | Code + doc | ~10 | None |
| AF2-C | AF-24 | Code | ~20 | None |
| AF2-D | AF-25 | Documentation | ~8 | None |
| AF2-E | AF-23 | Documentation | ~8 | None |
| AF2-F | AF-34 | Documentation | ~10 | None |
| AF2-G | — | Gate | — | AF2-A–F |
| **Total** | | | **~96** | |

**Parallelism**: AF2-A through AF2-F are all independent. AF2-C is the
riskiest (changes `mapPage` return type).


---

## 5. Phase AF3 — Platform & DeviceTree Hardening

**Status**: PLANNED
**Goal**: Fix the DTB parser fuel-exhaustion silent truncation, MMIO range
validation, and other platform-layer issues needed before RPi5 deployment.
**Gate**: `lake build` + `lake build SeLe4n.Platform.DeviceTree` +
`lake build SeLe4n.Platform.RPi5.MmioAdapter` + `./scripts/test_smoke.sh`
**Dependencies**: None (independent of AF1/AF2).
**Estimated scope**: ~100–160 lines of changes.

### AF3-A: Fix `parseFdtNodes` fuel exhaustion to return `none` (AF-05)

**Finding**: `parseFdtNodes` fuel exhaustion returns `some ([], offset)` (silent
success) at lines 585 and 616. `findMemoryRegProperty` correctly returns `none`.

**Change**: Change the fuel-exhaustion branch from:
```lean
| 0 => some ([], offset) -- Fuel exhausted
```
to:
```lean
| 0 => none -- AF3-A: Fuel exhausted — signal parse failure
```

Similarly update `parseNodeContents` (line 616). Update callers that pattern
match on `parseFdtNodes` to handle `none` as parse failure. The caller at
line 800 (`match parseFdtNodes blob hdr with | some ns => ns | none => []`)
already handles `none` by falling back to empty list — verify this is
acceptable or propagate the error upward.

**Files modified**: `SeLe4n/Platform/DeviceTree.lean` (~15 lines)

### AF3-B: Validate full MMIO write byte range (AF-09a)

**Finding**: `mmioWrite32` (MmioAdapter.lean:389) and `mmioWrite64` (line 416)
validate only base address alignment and device region membership. A 4/8-byte
write at the boundary of a device region could spill into adjacent memory.

**Change**: Add full range check:
```lean
-- AF3-B: Validate entire write range [addr, addr+3] for 32-bit writes
if !isDeviceAddress addr || !isDeviceAddress (addr + 3) then
  .error .mmioAddressOutOfRange
```

Similarly for `mmioWrite64` check `addr + 7`.

**Files modified**: `SeLe4n/Platform/RPi5/MmioAdapter.lean` (~20 lines)

### AF3-C: Document MMIO write-semantics model gap (AF-09b)

**Finding**: General `mmioWrite32`/`mmioWrite64` use direct memory store.
Only `mmioWrite32W1C` models write-one-to-clear. No `MmioWriteSafe` witness.

**Change**: Add documentation block to MmioAdapter.lean:
```lean
/-- AF3-C: MMIO Write Semantics Model
    The abstract model provides three write semantics:
    • `mmioWrite32`/`mmioWrite64`: Direct byte-by-byte replacement (standard store)
    • `mmioWrite32W1C`: Write-one-to-clear (new = old & ~write)
    • [Missing] Set-only: new = old | write

    Hardware W1C registers (e.g., GIC-400 ICPENDR) MUST use `mmioWrite32W1C`.
    Using `mmioWrite32` on a W1C register produces model-correct but
    hardware-incorrect behavior.

    H3 TODO: Introduce `MmioWriteSafe` witness type gating correct write
    function usage per register address range. -/
```

**Files modified**: `SeLe4n/Platform/RPi5/MmioAdapter.lean` (~15 lines)

### AF3-D: Document `extractPeripherals` depth limitation (AF-32)

**Finding**: Only searches 2 levels. May miss deeply nested peripherals.

**Change**: Add documentation:
```lean
-- AF3-D: Searches top-level + direct children only (2 levels).
-- DTB standard allows arbitrary nesting depth. RPi5 BCM2712 DTB has
-- peripherals at depth 1–2, so this is sufficient for the target platform.
-- H3 TODO: If non-RPi5 platforms have deeper nesting, add recursive descent.
```

**Files modified**: `SeLe4n/Platform/DeviceTree.lean` (~8 lines)

### AF3-E: Document `natKeysNoDup` opacity (AF-19)

**Finding**: Uses opaque `Std.HashSet`. Transparent `listAllDistinct` exists.

**Change**: Add documentation:
```lean
-- AF3-E: `natKeysNoDup` uses opaque `Std.HashSet` for O(n) runtime
-- checking. The transparent O(n²) alternative `listAllDistinct` (below)
-- is usable by `decide` but too slow for large key sets. Boot-time
-- callers use `natKeysNoDup` for runtime speed; proofs requiring
-- kernel-evaluable noDup should use `listAllDistinct`.
```

**Files modified**: `SeLe4n/Platform/Boot.lean` (~8 lines)

### AF3-F: Document DTB stubs and limitations (AF-41, AF-42, AF-44, AF-45)

**Finding**: `classifyMemoryRegion` always returns `.ram`, `fromDtb` always
returns `none`, `bootFromPlatform` accepts empty config, `applyMachineConfig`
copies only `physicalAddressWidth`.

**Change**: Add documentation annotations to each function noting the WS-V
TODO status and current limitation:
```lean
-- AF3-F: classifyMemoryRegion always returns .ram (WS-V TODO: ARM64 device
-- memory type classification from DTB `device_type` property)
```

**Files modified**: `SeLe4n/Platform/DeviceTree.lean` (~10 lines),
`SeLe4n/Platform/Boot.lean` (~10 lines)

### AF3-G: Gate verification

Build all modified platform modules and run `test_smoke.sh`.

### AF3 Summary

| Sub-task | Findings | Type | Lines | Dependencies |
|----------|----------|------|-------|--------------|
| AF3-A | AF-05 | Code fix | ~15 | None |
| AF3-B | AF-09a | Code fix | ~20 | None |
| AF3-C | AF-09b | Documentation | ~15 | None |
| AF3-D | AF-32 | Documentation | ~8 | None |
| AF3-E | AF-19 | Documentation | ~8 | None |
| AF3-F | AF-41,42,44,45 | Documentation | ~20 | None |
| AF3-G | — | Gate | — | AF3-A–F |
| **Total** | | | **~86** | |

**Parallelism**: All sub-tasks are independent. AF3-A and AF3-B are the
code changes; rest are documentation.


---

## 6. Phase AF4 — Information Flow, Cross-Subsystem & SchedContext

**Status**: PLANNED
**Goal**: Replace `native_decide` with `decide` (TCB reduction),
formalize fuel-sufficiency connections, and document deployment requirements.
**Gate**: `lake build` + `lake build SeLe4n.Kernel.InformationFlow.Enforcement.Wrappers`
+ `lake build SeLe4n.Kernel.CrossSubsystem` + `./scripts/test_full.sh`
**Dependencies**: AF1-B (if `crossSubsystemInvariant` changes to 10 predicates,
AF4-B must account for this).
**Estimated scope**: ~90–140 lines of changes.

### AF4-A: Replace `native_decide` with `decide` in enforcement boundary (AF-16)

**Finding**: `enforcementBoundary_is_complete` (Wrappers.lean:286) uses
`native_decide` — the only `native_decide` #1 in the codebase. Bypasses
proof kernel for a 33-element Bool enumeration.

**Change**: Replace `native_decide` with `decide`:
```lean
theorem enforcementBoundary_is_complete :
    enforcementBoundaryComplete = true := by decide
```

This may increase compile time for this theorem (from milliseconds to seconds)
but removes the Lean runtime evaluator from the TCB. If `decide` fails due to
timeout, decompose the proof into per-SyscallId cases:
```lean
theorem enforcementBoundary_is_complete :
    enforcementBoundaryComplete = true := by
  simp [enforcementBoundaryComplete, SyscallId.all]
  decide
```

**Files modified**: `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` (~3 lines)

### AF4-B: Replace `native_decide` with `decide` in pairwise coverage (AF-17)

**Finding**: `native_decide` #2 at CrossSubsystem.lean:705 for the pairwise
field-disjointness count proof.

**Change**: Replace with `decide`. If the 12-element countP check is too slow
for `decide`, split into sub-lemmas:
```lean
-- AF4-B: Replace native_decide with decide (or decomposed proof)
].countP id = 12 := by decide
```

Note: If AF1-B changes `crossSubsystemFieldSets` from 9 to 10 entries, the
count changes from 12 to a new value. Coordinate with AF1-B.

**Files modified**: `SeLe4n/Kernel/CrossSubsystem.lean` (~3 lines)

### AF4-C: Document `collectQueueMembers` fuel-sufficiency gap (AF-07)

**Finding**: Fuel-sufficiency not formally connected to `tcbQueueChainAcyclic`.
AE5-A already changed return type to `Option`. TPI-DOC at line 124.

**Change**: Expand the documentation at CrossSubsystem.lean:92–126 with a
formal argument sketch:
```lean
/-- AF4-C: Fuel-sufficiency informal argument:
    Given `tcbQueueChainAcyclic st` and `collectQueueMembers` with
    fuel = `st.objectIndex.length`:
    1. Acyclicity → chain visits each thread at most once
    2. Each visited thread is in `objectIndex` (by `noStaleEndpointQueueReferences`)
    3. Therefore chain length ≤ `objectIndex.length` = fuel
    Formalizing requires `QueueNextPath` inductive bridge (TPI-DOC). -/
```

**Files modified**: `SeLe4n/Kernel/CrossSubsystem.lean` (~12 lines)

### AF4-D: Document `serviceHasPathTo` conservative fuel-exhaustion (AF-18)

**Finding**: Returns `true` on fuel exhaustion — conservative for cycle
prevention but causes spurious rejection.

**Change**: Add documentation:
```lean
-- AF4-D: Returns `true` on fuel exhaustion (line 144). This is
-- CONSERVATIVE for cycle detection: false positive rejects a valid
-- edge registration; false negative would silently allow a cycle.
-- Proven correct under `serviceCountBounded` via `serviceBfsFuel_sound`
-- and `serviceBfsFuel_sufficient`. Spurious rejection is acceptable
-- because fuel is bounded by service count (typically < 50).
```

**Files modified**: `SeLe4n/Kernel/Service/Operations.lean` (~10 lines)

### AF4-E: Document `LabelingContextValid` deployment status (AF-33)

**Finding**: Deployment requirement, not runtime-enforced. Already documented
in AE5-F.

**Change**: Add cross-reference to the AE5-F documentation and note that
this is consistent with seL4 separation kernel design:
```lean
-- AF4-E: See AE5-F `labelingContextValid_is_deployment_requirement` theorem.
-- This matches seL4's approach: boot-time configuration is trusted,
-- runtime enforcement occurs via capability checks + NI projection.
-- DEPLOYMENT_GUIDE.md §4.1 documents the pre-deployment obligation.
```

**Files modified**: `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` (~8 lines)

### AF4-F: Document CBS bandwidth bound precision (AF-08)

**Finding**: 8x gap from `maxReplenishments = 8`. Per-mille truncation in
admission control. Already documented in AE3-G.

**Change**: Add cross-reference and precision analysis:
```lean
-- AF4-F: CBS 8x bandwidth gap is a proof-precision issue, not correctness.
-- The bound `totalConsumed <= 8 * budget` holds because each of up to 8
-- replenishments can refill the full budget in worst case. The ideal 1x
-- bound requires proving that replenishments partition the budget (no
-- double-counting), which is tracked for future proof tightening.
-- Admission control truncation: ≤1 per-mille per context, ≤6.4% with 64
-- contexts. See AE3-G documentation.
```

**Files modified**: `SeLe4n/Kernel/SchedContext/Invariant/Defs.lean` (~10 lines)

### AF4-G: Document `schedContextYieldTo` as kernel-internal (AF-30, AF-47)

**Finding**: No capability check. Pure function, not monadic.

**Change**: Add documentation:
```lean
/-- AF4-G: `schedContextYieldTo` is a KERNEL-INTERNAL helper, not a
    syscall entry point. No capability check because callers (API dispatch)
    validate capabilities before invoking. Pure function (returns SystemState)
    because the yield operation cannot fail — both SchedContexts must
    exist (validated by caller). -/
```

**Files modified**: `SeLe4n/Kernel/SchedContext/Operations.lean` (~8 lines)

### AF4-H: Gate verification

Build all modified modules. Run `test_full.sh` (theorem changes in AF4-A/B).

### AF4 Summary

| Sub-task | Findings | Type | Lines | Dependencies |
|----------|----------|------|-------|--------------|
| AF4-A | AF-16 | Code fix (proof) | ~3 | None |
| AF4-B | AF-17 | Code fix (proof) | ~3 | AF1-B (coordinate) |
| AF4-C | AF-07 | Documentation | ~12 | None |
| AF4-D | AF-18 | Documentation | ~10 | None |
| AF4-E | AF-33 | Documentation | ~8 | None |
| AF4-F | AF-08 | Documentation | ~10 | None |
| AF4-G | AF-30, AF-47 | Documentation | ~8 | None |
| AF4-H | — | Gate | — | AF4-A–G |
| **Total** | | | **~54** | |

**Parallelism**: All sub-tasks independent except AF4-B depends on AF1-B
completion for correct field count.


---

## 7. Phase AF5 — IPC, Capability, Lifecycle & Documentation

**Status**: PLANNED
**Goal**: Fix stale documentation, add missing cross-references, document
design rationale for IPC/capability/lifecycle patterns.
**Gate**: `lake build` + `./scripts/test_full.sh`
**Dependencies**: None (all documentation and minor code changes).
**Estimated scope**: ~120–170 lines of changes.

### AF5-A: Fix stale `pendingMessage = none` documentation (AF-12)

**Finding**: Endpoint.lean:325–337 claims the invariant is "not formally
proven" but `waitingThreadsPendingMessageNone` was proven in AC1-A and
extracted to WaitingThreadHelpers.lean.

**Change**: Update the comment to reflect current status:
```lean
-- AF5-A: `pendingMessage = none` for waiting threads IS formally proven:
-- defined as `waitingThreadsPendingMessageNone` in IPC/Invariant/Defs.lean:284
-- with preservation theorems in IPC/Invariant/WaitingThreadHelpers.lean
-- (helper extraction in WS-AC Phase AC1-A). The safety argument is now both
-- structural AND formally verified.
```

**Files modified**: `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` (~8 lines)

### AF5-B: Document timeout sentinel design (AF-04)

**Finding**: Dual-condition check documented in AE4-F. Remaining action is
cross-reference and H3 migration path.

**Change**: Add cross-reference at Timeout.lean:27–38:
```lean
-- AF5-B: Timeout sentinel design documented in AE4-F. Migration path:
-- H3 hardware binding should add `timedOut : Bool` to TCB, eliminating
-- the gpr x0 sentinel. The dual-condition check (register AND ipcState)
-- prevents false positives in the current model.
```

**Files modified**: `SeLe4n/Kernel/IPC/Operations/Timeout.lean` (~8 lines)

### AF5-C: Document `endpointQueueRemove` direct insert rationale (AF-06)

**Finding**: Proven correct and fallbacks proven unreachable in AE4-E.

**Change**: Add cross-reference:
```lean
-- AF5-C: Direct RHTable.insert (bypassing storeObject) is intentional for
-- the queue-remove path where only queue links and ipcState are modified,
-- not object lifecycle. Fallback unreachability proven by
-- `queueRemove_predecessor_exists` and `queueRemove_successor_exists`
-- (AE4-E). See dualQueueSystemInvariant for correctness proof.
```

**Files modified**: `SeLe4n/Kernel/IPC/DualQueue/Core.lean` (~8 lines)

### AF5-D: Document Badge Nat round-trip (AF-15)

**Finding**: Documented in AC3/I-04 (`bor_valid` theorem).

**Change**: Add cross-reference at Endpoint.lean:372:
```lean
-- AF5-D: Nat round-trip via `Badge.ofNatMasked badge.toNat` is safe:
-- `ofNatMasked` applies `% machineWordMax` (64-bit masking).
-- `bor_valid` theorem (AC3/I-04) proves result validity.
-- H3 TODO: Verify hardware masking consistency at ABI boundary.
```

**Files modified**: `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` (~6 lines)

### AF5-E: Document `donationChainAcyclic` 2-cycle scope (AF-39)

**Finding**: Only prevents 2-cycles. Longer cycles prevented by protocol.

**Change**: Expand documentation at Invariant/Defs.lean:959–967:
```lean
-- AF5-E: `donationChainAcyclic` explicitly prevents 2-cycles (mutual
-- donation pairs). Longer cycles (k > 2) are prevented by IPC protocol:
-- a thread blocked on .waitingReply cannot initiate a new Call (its
-- ipcState is not .ready), breaking any potential chain. This structural
-- argument is not formalized but follows from the ipcState state machine.
```

**Files modified**: `SeLe4n/Kernel/IPC/Invariant/Defs.lean` (~8 lines)

### AF5-F: Document tuple projection pattern (AF-26)

**Finding**: Deep `.2.2.2...` projections in Builder.lean and Capability
invariant despite warning at Builder.lean:112.

**Change**: Add documentation noting the limitation and future refactoring:
```lean
-- AF5-F: Deep tuple projections (.2.2.2...) are a known maintenance burden.
-- Refactoring to named structures (e.g., `SchedulerInvariantBundle` with
-- named fields instead of 16-tuple) is deferred to post-release because:
-- (1) It would require updating 100+ proof sites that destructure tuples
-- (2) Named structures in Lean 4 have different `cases`/`rcases` behavior
-- (3) Current approach is functionally correct, just unwieldy.
-- Tracked for WS-V code quality phase.
```

**Files modified**: `SeLe4n/Model/Builder.lean` (~8 lines),
`SeLe4n/Kernel/Capability/Invariant/Defs.lean` (~8 lines)

### AF5-G: Document `cspaceResolvePath` vs `resolveCapAddress` relationship (AF-27)

**Finding**: Overlapping semantics, relationship undocumented.

**Change**: Add documentation to Operations.lean:
```lean
/-- AF5-G: CSpace Resolution Layers
    • `cspaceResolvePath`: Single-level resolution within one CNode (guard check
      + radix index extraction). Used by `resolveCapAddress` as the base step.
    • `resolveCapAddress`: Multi-level recursive resolution through nested CNodes.
      Calls `cspaceResolvePath` at each level, then recurses into child CNodes.
    The single-level function is also used standalone for direct slot access
    when the CNode is already known (e.g., `resolveExtraCaps`). -/
```

**Files modified**: `SeLe4n/Kernel/Capability/Operations.lean` (~10 lines)

### AF5-H: Document `suspendThread` re-lookup rationale (AF-28)

**Finding**: Re-lookups TCB after IPC cleanup.

**Change**: Expand comment at Suspend.lean:159–163:
```lean
-- AF5-H: Re-lookup is necessary because `cancelIpcBlocking` may modify
-- the TCB's ipcState, queueNext, queuePrev, and pendingMessage fields.
-- The `schedContextBinding` field is NOT modified by IPC cancellation
-- (proven by `cancelIpcBlocking_schedContextBinding_eq` transport lemma
-- in SuspendPreservation.lean). However, re-lookup is defensive against
-- future IPC cleanup changes.
```

**Files modified**: `SeLe4n/Kernel/Lifecycle/Suspend.lean` (~8 lines)

### AF5-I: Fix stale FrozenOps operation count (AF-43) and duplicate NI defs (AF-48)

**Finding**: FrozenOps header claims 21 operations, file defines 15.
Duplicate `cdt_only_preserves_projection` in Operations.lean.

**Change**:
1. Update FrozenOps/Operations.lean header to say "15 operations".
2. Remove one duplicate `cdt_only_preserves_projection` definition
   (keep the one used by downstream proofs).

**Files modified**: `SeLe4n/Kernel/FrozenOps/Operations.lean` (~2 lines),
`SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` (~20 lines removed)

### AF5-J: Document high-heartbeat proof fragility (AF-31)

**Finding**: 1.6M and 800K heartbeats. Toolchain update risk.

**Change**: Add documentation at Preservation.lean:2409:
```lean
-- AF5-J: High heartbeats (1.6M for handleYield, 800K for timerTick) are
-- caused by EDF reasoning requiring full run queue analysis after
-- enqueue + schedule composition. Potential mitigations:
-- (1) Extract intermediate lemmas to reduce per-proof complexity
-- (2) Introduce custom tactics for EDF property threading
-- (3) Accept and pin Lean toolchain version during release cycles
-- Tracked for post-release maintenance.
```

**Files modified**: `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean` (~8 lines)

### AF5 Summary

| Sub-task | Findings | Type | Lines | Dependencies |
|----------|----------|------|-------|--------------|
| AF5-A | AF-12 | Doc fix | ~8 | None |
| AF5-B | AF-04 | Documentation | ~8 | None |
| AF5-C | AF-06 | Documentation | ~8 | None |
| AF5-D | AF-15 | Documentation | ~6 | None |
| AF5-E | AF-39 | Documentation | ~8 | None |
| AF5-F | AF-26 | Documentation | ~16 | None |
| AF5-G | AF-27 | Documentation | ~10 | None |
| AF5-H | AF-28 | Documentation | ~8 | None |
| AF5-I | AF-43, AF-48 | Code fix | ~22 | None |
| AF5-J | AF-31 | Documentation | ~8 | None |
| **Total** | | | **~102** | |

**Parallelism**: All sub-tasks fully independent. Can be parallelized.


---

## 8. Phase AF6 — Rust ABI Fixes & Documentation Closure

**Status**: PLANNED
**Goal**: Fix Rust ABI error mapping, truncation handling, stale comments,
missing marker types, and synchronize all documentation.
**Gate**: `./scripts/test_full.sh` + `cargo test --manifest-path rust/Cargo.toml`
+ documentation sync verification
**Dependencies**: AF1–AF5 complete (documentation sync requires all prior phases).
**Estimated scope**: ~100–150 lines of changes.

### AF6-A: Add `UnknownKernelError` variant to Rust ABI (AF-20)

**Finding**: Unrecognized error codes (≥44) mapped to `InvalidSyscallNumber` —
semantic mismatch.

**Change**: Add a new variant to `KernelError` in `sele4n-types/src/error.rs`:
```rust
/// Kernel returned an error code not recognized by this ABI version.
/// This indicates a version mismatch between the kernel and ABI crate.
#[non_exhaustive]
UnknownKernelError = 255,  // Reserved sentinel outside kernel range
```

Update `decode.rs` to map unrecognized codes to `UnknownKernelError` instead
of `InvalidSyscallNumber`:
```rust
KernelError::from_u32(regs[0] as u32)
    .unwrap_or(KernelError::UnknownKernelError)
```

Update conformance tests. Note: `#[non_exhaustive]` on the enum already
allows this addition without breaking downstream.

**Files modified**: `rust/sele4n-types/src/error.rs` (~5 lines),
`rust/sele4n-abi/src/decode.rs` (~3 lines),
`rust/sele4n-abi/tests/conformance.rs` (~5 lines)

### AF6-B: Return error for `endpoint_reply_recv` truncation (AF-21)

**Finding**: Silent truncation to 3 registers when `msg.length > 3`.

**Change**: Return an error instead of silently truncating:
```rust
pub fn endpoint_reply_recv(
    cap: Cap<Endpoint>, reply_target: u64, msg: &IpcMessage,
) -> Result<IpcResult, TruncationError> {
    if msg.length > 3 {
        return Err(TruncationError::ReplyMessageTooLong {
            provided: msg.length, max: 3
        });
    }
    // ... existing implementation
}
```

Alternative (backward compatible): Add `endpoint_reply_recv_checked` that
returns `Result`, keep existing function with documentation warning.

**Recommended**: Backward-compatible approach — add checked variant and
document the existing function's truncation behavior.

**Files modified**: `rust/sele4n-sys/src/ipc.rs` (~20 lines)

### AF6-C: Fix stale Rust comments (AF-35, AF-36)

**Finding**: Doc comment says "43-variant" (should be "44-variant").
Decode comment says "0–42" (should be "0–43").

**Change**:
1. `sele4n-types/src/lib.rs`: Change "43-variant" to "44-variant"
2. `sele4n-abi/src/decode.rs:39`: Change "0–42" to "0–43"

**Files modified**: 2 files (~2 lines each)

### AF6-D: Add `SchedContext` marker type (AF-37)

**Finding**: Missing from `sele4n-sys/src/cap.rs` while all other object
types have markers.

**Change**: Add:
```rust
/// Marker type for scheduling context capabilities.
pub struct SchedContext;
```

**Files modified**: `rust/sele4n-sys/src/cap.rs` (~3 lines)

### AF6-E: Make `IpcMessage.length` private (AF-38)

**Finding**: Public field allows external mutation bypassing invariant.

**Change**: Make `length` field private and add accessor:
```rust
pub struct IpcMessage {
    pub(crate) length: u8,
    pub registers: [u64; 4],
}

impl IpcMessage {
    pub fn length(&self) -> u8 { self.length }
}
```

Update callers that directly set `length`.

**Files modified**: `rust/sele4n-sys/src/ipc.rs` (~15 lines)

### AF6-F: Install shellcheck in CI (AF-46)

**Finding**: `shellcheck` enforcement is optional — skipped if unavailable.

**Change**: Add `shellcheck` installation to CI workflow:
```yaml
- name: Install shellcheck
  run: sudo apt-get install -y shellcheck
```

Alternatively, document that `shellcheck` is required for full hygiene
checking in DEVELOPMENT.md.

**Files modified**: `.github/workflows/lean_action_ci.yml` (~3 lines) or
`docs/DEVELOPMENT.md` (~5 lines)

### AF6-G: Documentation synchronization & closure

**Change**: After all AF1–AF5 phases complete:
1. Update `docs/WORKSTREAM_HISTORY.md` with WS-AF completion
2. Update `docs/DEVELOPMENT.md` if new coding conventions emerged
3. Update `docs/CLAIM_EVIDENCE_INDEX.md` if claims changed
4. Regenerate `docs/codebase_map.json`
5. Update CLAUDE.md large-file list if file sizes changed significantly
6. Update `README.md` metrics if applicable
7. Verify trace fixture unchanged (no dispatch-affecting changes expected)

**Files modified**: ~5–7 documentation files (~50 lines total)

### AF6 Summary

| Sub-task | Findings | Type | Lines | Dependencies |
|----------|----------|------|-------|--------------|
| AF6-A | AF-20 | Code fix | ~13 | None |
| AF6-B | AF-21 | Code fix | ~20 | None |
| AF6-C | AF-35, AF-36 | Comment fix | ~4 | None |
| AF6-D | AF-37 | Code | ~3 | None |
| AF6-E | AF-38 | Code | ~15 | None |
| AF6-F | AF-46 | CI/doc | ~5 | None |
| AF6-G | — | Doc sync | ~50 | AF1–AF5 |
| **Total** | | | **~110** | |

**Parallelism**: AF6-A through AF6-F are independent. AF6-G requires
all prior phases to complete.


---

## 9. Scope Estimates & Dependency Graph

### 9.1 Per-Phase Scope

| Phase | Code | Proof | Documentation | Total Lines | Risk |
|-------|------|-------|---------------|-------------|------|
| AF1 | ~15 | ~100 | ~80 | ~195 | HIGH (AF1-B bridge lemmas) |
| AF2 | ~45 | ~40 | ~36 | ~96 | MEDIUM (AF2-A callsite proof, AF2-C return type) |
| AF3 | ~35 | ~0 | ~51 | ~86 | LOW |
| AF4 | ~6 | ~0 | ~48 | ~54 | LOW (AF4-A/B may need fallback decomposition) |
| AF5 | ~22 | ~0 | ~80 | ~102 | LOW |
| AF6 | ~55 | ~0 | ~55 | ~110 | LOW |
| **Total** | **~178** | **~140** | **~350** | **~643** | |

**Worst-case**: If AF1-B requires individual per-operation proofs for all 33
bridge lemmas (~15 lines each) instead of a shared frame argument, add ~200
lines. If AF2-A Option B is chosen (~40 callsite changes), add ~150 lines.
**Worst-case total**: ~643 + 350 = ~993 lines.

### 9.2 Dependency Graph

```
AF1 (Scheduler)  ──┐
AF2 (State)        │──→ AF6-G (Doc sync)
AF3 (Platform)     │
AF4 (IF/Cross) ────┘
AF5 (IPC/Cap)  ────┘

AF1-A → AF1-B (comment fix before integration)
AF1-B → AF4-B (field count coordination)

All other sub-tasks within each phase are independent.
```

### 9.3 Phase Ordering

Phases AF1–AF5 can run **in parallel** (independent subsystems with
disjoint file sets). The recommended sequential order for a single
implementer is:

1. **AF1** first — highest severity, most complex (AF1-B is critical path)
2. **AF2** second — second HIGH finding + model layer
3. **AF3** third — platform hardening before RPi5
4. **AF4** fourth — depends on AF1-B for field count
5. **AF5** fifth — documentation sweep
6. **AF6** last — Rust ABI + closure (requires all prior phases)


---

## 10. Risk Register

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| AF1-B import cycle discovered | LOW | HIGH | AE2-F already established Liveness import chain through CrossSubsystem; BlockingGraph is transitively imported. If cycle found, fall back to AF1-A (comment-only fix) and defer integration to H3. |
| AF1-B bridge lemma explosion | MEDIUM | MEDIUM | If frame argument doesn't cover non-IPC operations, individual proofs needed for all 33 operations. Mitigated by: most operations don't modify `ipcState`, so `blockingAcyclic_frame` should cover ~26/33. |
| AF2-C `mapPage` return type change breaks boot | MEDIUM | MEDIUM | Boot sequence must use W^X-compliant permissions. Verify boot test fixtures. Fallback: make the check a warning annotation instead of hard error. |
| AF4-A `decide` timeout | LOW | LOW | If `decide` takes >60s for 33-element enumeration, decompose into per-SyscallId cases or use `simp [enforcementBoundaryComplete, SyscallId.all]; decide`. |
| AF6-E `IpcMessage.length` privacy breaks callers | LOW | MEDIUM | If external crates set `length` directly, add a `pub fn set_length(len: u8)` with bounds check. Current codebase has no external crate consumers. |
| High heartbeat proofs break on Lean update | MEDIUM | LOW | Not addressed in this workstream (documented in AF5-J). Pin Lean toolchain version. |


---

## 11. Verification Protocol

Each phase follows this verification protocol before merge:

1. **Module build**: `source ~/.elan/env && lake build <Module.Path>` for every
   modified `.lean` file
2. **Full build**: `source ~/.elan/env && lake build`
3. **Sorry/axiom scan**: `grep -r '\bsorry\b\|\baxiom\b' SeLe4n/` → 0 matches
4. **Test tier**: Minimum `test_smoke.sh` for code changes; `test_full.sh` for
   theorem/invariant changes
5. **Fixture check**: Verify `tests/fixtures/main_trace_smoke.expected` unchanged
   (no dispatch-affecting changes expected in this workstream)
6. **Rust tests**: `cargo test --manifest-path rust/Cargo.toml` for AF6
7. **Website links**: `scripts/check_website_links.sh` (Tier 0 hygiene)


---

## 12. Conclusion

This workstream remediates all actionable findings from two independent
pre-release audits. The 7 refuted findings were rigorously disproven against
source evidence, preventing wasted effort on erroneous items. The remaining 49
sub-tasks across 6 phases are organized by severity and dependency, with the
most impactful work (blocking acyclicity integration, storeObject capacity
assurance) front-loaded.

**Key outcomes when complete**:
- `blockingAcyclic` formally integrated into `crossSubsystemInvariant` with
  preservation proofs for all kernel operations
- WCRT theorem naming reflects actual assurance level
- `storeObject` capacity gating machine-checked
- Builder-phase W^X enforcement prevents boot-time violations
- DTB parser fails safely on fuel exhaustion
- MMIO writes validate full byte range
- `native_decide` eliminated from TCB (replaced with `decide`)
- Rust ABI error mapping semantically correct
- All documentation synchronized with current codebase state

**Estimated total**: ~643–993 lines of changes across ~30 files.
Zero sorry/axiom throughout.

