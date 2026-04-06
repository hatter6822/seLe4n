# WS-AD Workstream Plan — Pre-Release Audit Remediation (v0.25.10)

**Created**: 2026-04-06
**Baseline version**: 0.25.10
**Baseline audit**: `docs/audits/AUDIT_v0.25.10_PRE_RELEASE.md`
**Prior portfolios**: WS-B through WS-AC (all COMPLETE — see `docs/WORKSTREAM_HISTORY.md`)
**Constraint**: Zero `sorry`/`axiom` in production proof surface

---

## 1. Executive Summary

A comprehensive pre-release audit of seLe4n v0.25.10 was conducted on
2026-04-05, covering all ~150 Lean modules (~91,000 LOC), 30 Rust ABI files
(3 crates), and the full test/CI infrastructure. The audit found **zero
Critical**, **3 High** (architectural limitations, not bugs), **4 Medium**,
**6 Low**, and **8 Informational** findings. Zero `sorry`, zero `axiom`, and
zero `unsafe` Rust beyond the single ARM64 `svc #0` instruction.

### 1.1 Audit Verification Results

Every finding was independently verified against the codebase before inclusion
in this plan. The verification confirmed:

- **All 21 findings are accurate** — line numbers, behavioral descriptions,
  and severity assessments match the codebase as inspected on 2026-04-06.
- **No phantom or erroneous findings** — unlike the prior v0.25.3 audit which
  had 16 discrepancies, this audit's consolidated findings table (Section 17)
  is consistent with the detailed body text (Sections 2–16).
- **F-10 is already addressed** — the audit recommends adding a warning comment
  to `RuntimeContractFixtures.lean`, but the file already contains the warning
  "MUST NOT be imported by production kernel modules" (line 18). No action
  needed beyond acknowledging this.
- **F-12 is already addressed** — the audit recommends documenting IPC
  defensive fallbacks at the module boundary, but `endpointQueueRemove` already
  has comprehensive documentation under the `AUD-Z6-1` annotation (lines
  430–460 of `DualQueue/Core.lean`) explaining the invariant dependency and
  why the fallback is unreachable.

### 1.2 Verified Finding Counts

| Severity | Audit Count | After Verification | Actionable |
|----------|-------------|--------------------|------------|
| Critical | 0 | 0 | 0 |
| High | 3 | 3 | 3 (documentation/process) |
| Medium | 4 | 4 (F-10 already addressed; F-12 already addressed) | 2 |
| Low | 6 | 6 | 2 |
| Info | 8 | 8 | 0 (monitoring only) |

### 1.3 Finding Disposition Summary

| ID | Severity | Disposition | Phase |
|----|----------|-------------|-------|
| F-01 | MEDIUM | **FIX**: Add orphaned imports | AD1 |
| F-02 | LOW | **IMPROVE**: Add fresh-TCB convenience helper | AD2 |
| F-03 | LOW | **DOCUMENT**: Module-boundary annotation | AD2 |
| F-04 | HIGH | **DOCUMENT**: Deployment guide + external review rec | AD3 |
| F-05 | HIGH | **DOCUMENT**: Deployment guide NI boundary scope | AD3 |
| F-06 | HIGH | **DOCUMENT**: Deployment guide covert channel ack | AD3 |
| F-07 | MEDIUM | **DOCUMENT**: Deployment guide labeling override | AD3 |
| F-08 | MEDIUM | **PROOF**: Cross-subsystem composition proofs | AD4 |
| F-09 | INFO | **NO ACTION**: By design (VSpaceRoot boot excl.) | — |
| F-10 | INFO | **ALREADY ADDRESSED**: Warning comment exists | — |
| F-11 | LOW | **NO ACTION**: Acceptable const-eval pattern | — |
| F-12 | MEDIUM | **ALREADY ADDRESSED**: AUD-Z6-1 documentation | — |
| F-13 | LOW | **DEFERRED**: To profiling workstream (WS-AD/perf) | — |
| F-14 | LOW | **NO ACTION**: Proven impossible; documented | — |
| F-15 | LOW | **NO ACTION**: By design (same as F-09) | — |
| F-16 | INFO | **DEFERRED**: To H3 hardware binding | — |
| F-17 | INFO | **DEFERRED**: Implicit assumption; external review | — |
| F-18 | INFO | **NO ACTION**: Correct CDT architecture | — |
| F-19 | INFO | **NO ACTION**: Forward-looking H3 prep | — |
| F-20 | INFO | **NO ACTION**: Proven (X4-E) | — |
| F-21 | INFO | **NO ACTION**: Correct `no_std` throughout | — |

### 1.4 Plan Structure

This plan organizes all actionable findings into **5 phases** (AD1–AD5) with
**19 atomic sub-tasks**, explicit dependencies, gate conditions, and scope
estimates. Phases are ordered by severity impact and dependency chain:

| Phase | Focus | Sub-tasks | Gate |
|-------|-------|-----------|------|
| AD1 | Integration fix (F-01) | 3 | `lake build` + module verification |
| AD2 | Code quality hardening (F-02, F-03) | 4 | `lake build` + `test_smoke.sh` |
| AD3 | Production deployment documentation (F-04–F-07) | 6 | `test_full.sh` + doc sync |
| AD4 | Cross-subsystem composition (F-08) | 4 | `lake build` + `test_full.sh` |
| AD5 | Closure & documentation sync | 2 | `test_full.sh` + doc sync |

**Estimated scope**: ~365–495 total lines of changes (Lean code, proofs,
documentation). See Section 9 for detailed breakdown.

---

## 2. Consolidated Finding Registry

### 2.1 HIGH Findings (3 — architectural limitations, not bugs)

| ID | Subsystem | Description | Verified | Action |
|----|-----------|-------------|----------|--------|
| F-04 | InformationFlow | Non-standard BIBA integrity model: `integrityFlowsTo .trusted .untrusted = true` allows write-down. Witnessed by `integrityFlowsTo_is_not_biba`; escalation blocked by `integrityFlowsTo_prevents_escalation` | YES — Policy.lean:75–79 | Document in deployment guide; recommend external threat-model review |
| F-05 | InformationFlow | Service orchestration state outside NI boundary. `serviceOrchestrationOutsideNiBoundary` (Projection.lean:551) explicitly scopes this exclusion | YES — Projection.lean:537–605 | Document in deployment guide |
| F-06 | InformationFlow | Scheduling covert channel (~400 bps). `acceptedCovertChannel_scheduling` (Projection.lean:404) formally witnesses 4 observable values visible to all observers | YES — Projection.lean:404–440 | Document in deployment guide; accepted per seL4 precedent (Murray et al., IEEE S&P 2013) |

**Severity rationale**: All three are intentional design decisions with formal
witnesses and proofs. They are HIGH because they affect the security model's
trust assumptions, but they are NOT bugs — each has a machine-checked theorem
documenting the precise scope and limitation.

### 2.2 MEDIUM Findings (4 — 2 actionable, 2 already addressed)

| ID | Subsystem | Description | Verified | Action |
|----|-----------|-------------|----------|--------|
| F-01 | SchedContext | `SchedContext/Invariant.lean` re-export hub imports only `Defs.lean`; `Preservation.lean` (160 lines, 7 theorems) and `PriorityPreservation.lean` (159 lines, 11 theorems) are orphaned — not imported by any production or test module | YES — zero grep matches for either import across codebase | **FIX**: Add 2 import lines to re-export hub |
| F-07 | InformationFlow | `defaultLabelingContext` assigns `publicLabel` to ALL entities. `defaultLabelingContext_insecure` (Policy.lean:240) proves all object pairs allow information flow. Production MUST override | YES — Policy.lean:220–256 | Document in deployment guide with override code example |
| F-08 | CrossSubsystem | Cross-subsystem invariant composition gap: 8-predicate `crossSubsystemInvariant` has sharing-pair operations that need per-operation preservation proofs. Documented at CrossSubsystem.lean:306–327 | YES — gap is real; 6 disjoint pairs have frame lemmas; 4 sharing pairs have conditional frame coverage | **PROOF**: Add targeted operation-specific preservation proofs |
| F-12 | IPC | `endpointQueueRemove` defensive fallbacks depend on external invariants (`ipcStateQueueMembershipConsistent`, `queueNextBlockingConsistent`) | YES — DualQueue/Core.lean:430–460 | **ALREADY ADDRESSED**: AUD-Z6-1 annotation provides comprehensive documentation |

### 2.3 LOW Findings (6 — 2 actionable, 4 no-action)

| ID | Subsystem | Description | Verified | Action |
|----|-----------|-------------|----------|--------|
| F-02 | IPC | `endpointQueuePopHead` returns stale TCB (queue links cleared in post-state but returned from pre-state). Documented under WS-L1/L1-A | YES — DualQueue/Core.lean:243–282 | **IMPROVE**: Add convenience helper to retrieve fresh TCB from post-state |
| F-03 | IPC | `ipcTransferSingleCap` errors converted to `.noSlot` by `ipcUnwrapCapsLoop` in CapTransfer.lean. Documented as seL4 cursor-preservation semantics | YES — CapTransfer.lean:71–86 | **DOCUMENT**: Add module-level docstring clarifying error-to-noSlot conversion |
| F-11 | Rust ABI | `MessageInfo::new_const` uses `assert!()` for compile-time validation; can panic at const-eval but not at runtime | YES — message_info.rs:73–78 | **NO ACTION**: Acceptable const-eval pattern |
| F-13 | Scheduler | `timeoutBlockedThreads` is O(n) via `st.objects.fold`; optimization deferred to WS-AD/perf | YES — Core.lean:502 | **DEFERRED**: To profiling after RPi5 bring-up |
| F-14 | Machine | `RegisterFile.not_lawfulBEq` proves `¬ LawfulBEq RegisterFile` via out-of-range index counterexample | YES — Machine.lean:217–228 | **NO ACTION**: Proven impossible; gap only at invalid indices (≥32) |
| F-15 | Platform | VSpaceRoots excluded from `bootSafeObject` due to ASID registration unavailability at boot | YES — Boot.lean:780–781 | **NO ACTION**: By design; post-boot ASID path documented |

### 2.4 INFORMATIONAL Findings (8 — all no-action)

| ID | Subsystem | Description | Verified | Action |
|----|-----------|-------------|----------|--------|
| F-09 | Platform | VSpaceRoot boot exclusion is by design | YES — Boot.lean:780, 930 | **NO ACTION**: Same root cause as F-15 |
| F-10 | Testing | `RuntimeContractFixtures.lean` isolation from production imports | YES — line 18: "MUST NOT be imported by production kernel modules" | **ALREADY ADDRESSED**: Warning comment exists |
| F-16 | Platform | MMIO volatile non-determinism gap bounded by `MmioSafe` hypothesis type | YES — MmioAdapter.lean:163–189, 281–317 | **DEFERRED**: To H3 hardware binding |
| F-17 | InformationFlow | Cache/timing side channels not modeled | YES — implicit assumption | **DEFERRED**: External review scope |
| F-18 | Capability | CDT acyclicity via hypothesis pattern (`addEdge` defers cycle-freedom to composition) | YES — correct architecture | **NO ACTION**: Correct design |
| F-19 | Architecture | `VSpaceBackend` abstract operations for H3 hardware prep | YES — forward-looking | **NO ACTION**: H3 prep |
| F-20 | Service | BFS fuel sufficiency proven (X4-E) with 800K heartbeat proof | YES — Acyclicity.lean | **NO ACTION**: Proven |
| F-21 | Rust ABI | All 3 crates are `no_std` throughout | YES — correct for kernel ABI | **NO ACTION**: Correct |

### 2.5 Findings Excluded from Remediation

The following findings require no code or documentation changes:

| ID | Reason for Exclusion |
|----|---------------------|
| F-09 | By design — VSpaceRoots correctly require post-boot ASID registration |
| F-10 | Already addressed — warning comment already present at line 18 |
| F-11 | Acceptable pattern — `const fn` assertions are compile-time-only |
| F-12 | Already addressed — AUD-Z6-1 annotation provides comprehensive invariant-dependency documentation |
| F-13 | Deferred — O(n) performance optimization deferred to profiling workstream after RPi5 bring-up |
| F-14 | Proven impossible — `not_lawfulBEq` counterexample at invalid register indices is correct |
| F-15 | By design — duplicate root cause with F-09 |
| F-16 | Deferred — MMIO volatile semantics deferred to H3 hardware binding; safely bounded by `MmioSafe` |
| F-17 | Deferred — cache/timing channels require hardware-level analysis at H3 |
| F-18 | Correct architecture — CDT hypothesis pattern is standard for compositional verification |
| F-19 | Forward-looking — abstract VSpaceBackend is correct H3 preparation |
| F-20 | Proven — fuel sufficiency is machine-checked |
| F-21 | Correct — `no_std` is required for kernel ABI crates |

---

## 3. Phase AD1 — Integration Fix (F-01) ✅ COMPLETE

**Goal**: Integrate orphaned SchedContext invariant modules into the production
proof chain.
**Gate**: `lake build SeLe4n.Kernel.CrossSubsystem` + `lake build` (full) +
`test_smoke.sh`.
**Dependencies**: None (first phase).
**Status**: COMPLETE — all 21 theorems (7 + 14) reachable via production chain.

### AD1 Implementation Note: Import Cycle Resolution

The original plan called for adding imports to `SchedContext/Invariant.lean`
(the re-export hub). During implementation, this was found to create an import
cycle:

```
Object/Types.lean → SchedContext.lean → SchedContext/Invariant.lean
  → Preservation.lean → SchedContext/Operations.lean → Model.State
  → Object/Types.lean  (CYCLE)
```

The `SchedContext/Invariant.lean` hub is transitively imported by
`Object/Types.lean` via the `SchedContext.lean` re-export hub, and both
preservation modules depend on `Operations.lean` which requires `Model.State`.

**Resolution**: Both preservation modules are instead imported from
`CrossSubsystem.lean`, which:
1. Already sits downstream of the cycle boundary
2. Is the natural integration point for cross-subsystem preservation theorems
3. Feeds into the production chain via `Architecture/Invariant.lean` → `API.lean`

The `SchedContext/Invariant.lean` hub retains a documentation note explaining
the architectural constraint and pointing to `CrossSubsystem.lean` as the
integration point.

### AD1-A: Add Preservation.lean import to CrossSubsystem.lean (F-01)

**Finding**: `SchedContext/Invariant/Preservation.lean` contains 7 proven
theorems covering SchedContext configure, bind, unbind, and yieldTo operations
(Z5-M, Z5-I, Z5-K, Z5-L, Z5-N1/N2). Zero sorry/axiom, not imported anywhere.

**Change**: In `SeLe4n/Kernel/CrossSubsystem.lean`, add:
```lean
import SeLe4n.Kernel.SchedContext.Invariant.Preservation
```

**Files modified**: `CrossSubsystem.lean` (1 import line + comment).

### AD1-B: Add PriorityPreservation.lean import to CrossSubsystem.lean (F-01)

**Finding**: `SchedContext/Invariant/PriorityPreservation.lean` contains 14
proven theorems covering priority transport lemmas and authority bounds for
setPriority/setMCPriority operations (D2-G/H/I/J). Orphaned identically.

**Change**: In `SeLe4n/Kernel/CrossSubsystem.lean`, add:
```lean
import SeLe4n.Kernel.SchedContext.Invariant.PriorityPreservation
```

**Files modified**: `CrossSubsystem.lean` (1 import line).

### AD1-C: Verify integrated proof chain (F-01 closure) ✅

**Verified**:
1. Module build: `lake build SeLe4n.Kernel.CrossSubsystem` — 69 jobs, PASS
2. Full build: `lake build` — 236 jobs, PASS
3. Smoke test: `./scripts/test_smoke.sh` — all checks passed
4. Theorem reachability: 21 theorems (7 + 14) confirmed reachable via
   `CrossSubsystem.lean` → `Architecture/Invariant.lean` → `API.lean`
5. Zero sorry/axiom in modified files

**Gate condition**: All commands pass with zero errors. ✅

**Files modified**: None (verification only).

---

## 4. Phase AD2 — Code Quality Hardening (F-02, F-03) ✅ COMPLETE

**Goal**: Address two LOW-severity code quality findings with minimal,
targeted improvements — a convenience helper for stale-TCB handling and
a module-boundary documentation annotation.
**Gate**: `lake build` (full) + `./scripts/test_smoke.sh`.
**Dependencies**: AD1 (ensures clean build baseline).
**Status**: COMPLETE — all 4 sub-tasks verified; full build + smoke tests pass.

### AD2-A: Add fresh-TCB retrieval helper (F-02) ✅

**Finding**: `endpointQueuePopHead` (DualQueue/Core.lean:243–282) returns the
pre-dequeue TCB snapshot with stale queue link fields (queuePrev, queueNext
cleared in post-state but returned from pre-state). This is documented under
WS-L1/L1-A and is intentional for efficiency, but callers must remember to
re-fetch the TCB from post-state if they need current queue links.

**Change**: Add a convenience function `endpointQueuePopHeadFresh` in
`SeLe4n/Kernel/IPC/DualQueue/Core.lean` that wraps `endpointQueuePopHead` and
returns the post-state TCB instead of the pre-state snapshot:

```lean
/-- WS-L1/L1-A (AD2-A): Convenience wrapper that returns the *post-state* TCB
    with cleared queue links, avoiding the stale-snapshot footgun.
    Use this when the caller needs accurate queue link fields. -/
def endpointQueuePopHeadFresh (ep : Endpoint) (st : SystemState)
    : KernelResult (ThreadId × TCB × SystemState) :=
  match endpointQueuePopHead ep st with
  | .ok (tid, _staleTcb, st') =>
    match st'.objects[tid.toObjId]? with
    | some (.tcb freshTcb) => .ok (tid, freshTcb, st')
    | _ => .error .objectNotFound  -- unreachable under invariant
  | .error e => .error e
```

**Proof impact**: None — new function, no existing proofs affected. The helper
is additive and does not modify `endpointQueuePopHead`.

**Build verification**: `lake build SeLe4n.Kernel.IPC.DualQueue.Core`

**Files modified**: `DualQueue/Core.lean` (~12 lines added).
**Estimated effort**: Minimal.

### AD2-B: Add staleness documentation to endpointQueuePopHead callers (F-02) ✅

**Finding**: Callers of `endpointQueuePopHead` should be aware that the returned
TCB has stale queue links. While the function itself is well-documented, the
call sites may benefit from a one-line annotation.

**Change**: Audit all callers of `endpointQueuePopHead` in the codebase.
Actual call sites are in `DualQueue/Transport.lean` (3 call sites:
`endpointSendDual`, `endpointReceiveDual`, `endpointCall`), not in
`Endpoint.lean` or `WithCaps.lean` as originally expected. Added inline
comments at each call site:

```lean
-- Note: _tcb/senderTcb has stale queue links (WS-L1/L1-A); use st' for current state
```

**Proof impact**: None — comments only.

**Build verification**: `lake build SeLe4n.Kernel.IPC.DualQueue.Transport`

**Files modified**: `DualQueue/Transport.lean` (3 comment lines added).
**Estimated effort**: Minimal.

### AD2-C: Add module-boundary docstring to CapTransfer.lean (F-03) ✅

**Finding**: `ipcTransferSingleCap` errors are converted to `.noSlot` by
`ipcUnwrapCapsLoop` in `CapTransfer.lean:71–86`. The conversion is documented
inline but the module lacks a top-level docstring explaining this seL4-compatible
cursor-preservation semantic to readers encountering the module for the first time.

**Change**: Add a module-level documentation comment at the top of
`SeLe4n/Kernel/IPC/Operations/CapTransfer.lean` (after imports):

```lean
/--
# IPC Capability Transfer

This module implements seL4-compatible capability transfer during IPC.

**Key semantic (F-03/AD2-C):** When `ipcTransferSingleCap` fails (e.g.,
receiver CSpace root not found or slot insertion error), the error is
converted to `.noSlot` in the transfer results array. Remaining capabilities
in the batch are padded with `.noSlot` (short-circuit semantics). This
matches seL4's cursor-preservation behavior where the receiver sees a
consistent result count regardless of individual transfer failures.

The error-to-noSlot conversion is intentional and does NOT mask security-
relevant failures — the receiver simply sees fewer successfully transferred
capabilities, which is the correct degraded behavior.
-/
```

**Proof impact**: None — documentation only.

**Build verification**: `lake build SeLe4n.Kernel.IPC.Operations.CapTransfer`

**Files modified**: `CapTransfer.lean` (~15 lines added).
**Estimated effort**: Minimal.

### AD2-D: Phase AD2 gate verification ✅

**Steps**:
1. Full build: `source ~/.elan/env && lake build`
2. Smoke test: `./scripts/test_smoke.sh`
3. Verify no regressions in IPC test suites

**Verified**:
1. Module build: `lake build SeLe4n.Kernel.IPC.DualQueue.Core` — 30 jobs, PASS
2. Module build: `lake build SeLe4n.Kernel.IPC.Operations.CapTransfer` — 26 jobs, PASS
3. Module build: `lake build SeLe4n.Kernel.IPC.DualQueue.Transport` — 31 jobs, PASS
4. Full build: `lake build` — 236 jobs, PASS
5. Smoke test: `./scripts/test_smoke.sh` — all checks passed
6. Zero sorry/axiom in modified files
7. Codebase map regenerated

**Gate condition**: All commands pass with zero errors. ✅

**Files modified**: None (verification only).

---

## 5. Phase AD3 — Production Deployment Documentation (F-04, F-05, F-06, F-07) ✅ COMPLETE

**Goal**: Create a production deployment guide that consolidates security
model limitations, NI boundary scope, and configuration requirements
identified by the HIGH and MEDIUM findings. This documentation is critical
for any production deployment and must exist before the RPi5 hardware binding
(H3) milestone.
**Gate**: `./scripts/test_full.sh` + documentation sync checks.
**Dependencies**: AD1, AD2 (clean codebase baseline).
**Status**: COMPLETE — deployment guide created (238 lines), spec/advisory/claims/GitBook updated.

### AD3-A: Create DEPLOYMENT_GUIDE.md (F-04, F-05, F-06, F-07) ✅

**Finding**: No production deployment guide currently exists. Four audit
findings (3 HIGH, 1 MEDIUM) require deployment-facing documentation:

- **F-04**: Non-BIBA integrity model — deployers must understand the trust model
- **F-05**: Service orchestration NI exclusion — deployers must scope NI guarantees
- **F-06**: Scheduling covert channel — deployers must assess acceptable bandwidth
- **F-07**: Default labeling context — deployers MUST override before production

**Change**: Create `docs/DEPLOYMENT_GUIDE.md` with the following structure:

```markdown
# seLe4n Production Deployment Guide

## 1. Security Model Overview
### 1.1 Information Flow Enforcement
- Kernel NI covers: IPC, scheduling, capability operations, lifecycle
- Kernel NI does NOT cover: service orchestration (F-05)

### 1.2 Integrity Model (F-04)
- seLe4n uses a non-BIBA integrity model
- Trusted→untrusted write-down is ALLOWED (authority delegation)
- Untrusted→trusted escalation is BLOCKED
- Formal witnesses: `integrityFlowsTo_is_not_biba`,
  `integrityFlowsTo_prevents_escalation`
- RECOMMENDATION: Commission external threat-model review before
  production deployment in high-assurance environments

### 1.3 Known Covert Channels (F-06)
- Domain scheduling metadata visible to all observers
- Bandwidth: ≤ log₂(|schedule|) × switchFreq bits/second
- Typical: ≤ 400 bits/second (16 entries, 100 Hz)
- Matches seL4 design precedent (Murray et al., IEEE S&P 2013)
- Formal witness: `acceptedCovertChannel_scheduling`

## 2. Required Configuration
### 2.1 Security Labeling (F-07) — MANDATORY
- `defaultLabelingContext` assigns `publicLabel` to ALL entities
- Proven insecure: `defaultLabelingContext_insecure`
- Production MUST override with domain-specific labeling policy
- [Code example showing custom LabelingContext construction]

### 2.2 Platform Binding
- Hardware-specific MachineConfig validation
- MMIO region configuration (BCM2712 for RPi5)

## 3. NI Boundary Scope (F-05)
- Service orchestration internals outside kernel NI
- Formal witness: `serviceOrchestrationOutsideNiBoundary`
- Service-layer information flows must be analyzed separately

## 4. Pre-Deployment Checklist
- [ ] Custom LabelingContext configured (F-07)
- [ ] Integrity model reviewed for deployment context (F-04)
- [ ] Covert channel bandwidth acceptable for threat model (F-06)
- [ ] Service-layer NI analyzed separately (F-05)
- [ ] Platform binding validated for target hardware
- [ ] Security advisory (docs/SECURITY_ADVISORY.md) reviewed
```

**Cross-references**: Links to existing `docs/SECURITY_ADVISORY.md` (SA-1,
SA-2, SA-3) and formal theorems in the Lean codebase.

**Files created**: `docs/DEPLOYMENT_GUIDE.md` (~80–100 lines).
**Estimated effort**: Moderate — requires careful drafting of security-
sensitive documentation.

### AD3-B: Add labeling context override example (F-07) ✅

**Finding**: `docs/SECURITY_ADVISORY.md` (SA-2) states that production
deployments MUST override `defaultLabelingContext`, but no code example
shows HOW to construct a domain-specific labeling policy.

**Change**: Add a concrete code example in `docs/DEPLOYMENT_GUIDE.md`
Section 2.1 showing how to build a custom `LabelingContext`:

```lean
-- Example: Two-domain labeling policy
-- Domain A (trusted): threads 0-3, endpoints 0-1
-- Domain B (untrusted): threads 4-7, endpoints 2-3
def productionLabelingContext : LabelingContext :=
  { objectLabelOf := fun oid =>
      if oid.toNat < 4 then highConfidentialLabel
      else lowPublicLabel
    threadLabelOf := fun tid =>
      if tid.toNat < 4 then highConfidentialLabel
      else lowPublicLabel
    endpointLabelOf := fun eid =>
      if eid.toNat < 2 then highConfidentialLabel
      else lowPublicLabel
    serviceLabelOf := fun _ => highConfidentialLabel }
```

**Files modified**: `docs/DEPLOYMENT_GUIDE.md` (included in AD3-A).

### AD3-C: Update SELE4N_SPEC.md with NI boundary scope (F-05) ✅

**Finding**: The specification document should explicitly state the NI
boundary scope — that service orchestration is outside the kernel NI model.

**Change**: Add a subsection to the Information Flow section of
`docs/spec/SELE4N_SPEC.md` documenting:
1. The 32 `NonInterferenceStep` constructors cover kernel primitives
2. Service orchestration NI is explicitly scoped out
3. Cross-reference to `serviceOrchestrationOutsideNiBoundary` theorem

**Files modified**: `docs/spec/SELE4N_SPEC.md` (~10–15 lines added).
**Estimated effort**: Minimal.

### AD3-D: Update SECURITY_ADVISORY.md cross-references (F-04, F-07) ✅

**Finding**: `docs/SECURITY_ADVISORY.md` already documents SA-2
(`defaultLabelingContext` override requirement) but does not cross-reference
the new deployment guide or the formal insecurity proofs.

**Change**: Add cross-references from SA-2 to:
1. `docs/DEPLOYMENT_GUIDE.md` Section 2.1 (override instructions)
2. `defaultLabelingContext_insecure` theorem (Policy.lean:240)
3. `defaultLabelingContext_all_threads_observable` theorem (Policy.lean:250)

Also add a new SA-4 entry for the non-BIBA integrity model (F-04) with
cross-reference to `integrityFlowsTo_is_not_biba`.

**Files modified**: `docs/SECURITY_ADVISORY.md` (~15–20 lines added).
**Estimated effort**: Minimal.

### AD3-E: Update CLAIM_EVIDENCE_INDEX.md (F-04, F-05, F-06, F-07) ✅

**Finding**: The claim-evidence index should reflect the deployment-facing
documentation additions and cross-reference the formal witnesses.

**Change**: Add entries for:
1. Claim: "Integrity model prevents privilege escalation" →
   Evidence: `integrityFlowsTo_prevents_escalation` + deployment guide F-04
2. Claim: "NI covers kernel primitives" →
   Evidence: `serviceOrchestrationOutsideNiBoundary` + deployment guide F-05
3. Claim: "Scheduling covert channel bandwidth bounded" →
   Evidence: `acceptedCovertChannel_scheduling` + deployment guide F-06
4. Claim: "Default labeling is insecure" →
   Evidence: `defaultLabelingContext_insecure` + deployment guide F-07

**Files modified**: `docs/CLAIM_EVIDENCE_INDEX.md` (~20–30 lines added).
**Estimated effort**: Minimal.

### AD3-F: Phase AD3 gate verification ✅

**Steps**:
1. Full test: `./scripts/test_full.sh`
2. Documentation sync: verify all new docs are consistent with codebase
3. Website link check: `./scripts/check_website_links.sh`
4. Verify cross-references resolve correctly

**Gate condition**: All checks pass. ✅

**Verified**:
1. Full test: `./scripts/test_full.sh` — all tiers passed
2. Website link check: `./scripts/check_website_links.sh` — passed
3. Documentation sync: all cross-references verified
4. Zero sorry/axiom in production code

**Files modified**: None (verification only).

### AD3 Implementation Summary

| Sub-task | Files Modified | Lines Added |
|----------|---------------|-------------|
| AD3-A/B | `docs/DEPLOYMENT_GUIDE.md` (NEW) | 238 |
| AD3-C | `docs/spec/SELE4N_SPEC.md` | ~18 |
| AD3-D | `docs/SECURITY_ADVISORY.md` | ~40 |
| AD3-E | `docs/CLAIM_EVIDENCE_INDEX.md` | ~1 (table row) |
| AD3-F (GitBook) | `docs/gitbook/28-threat-model-and-security-hardening.md` | ~25 |
| **Total** | **6 files (1 new, 5 modified)** | **~322 lines** |

---

## 6. Phase AD4 — Cross-Subsystem Composition Proofs (F-08) ✅ COMPLETE

**Goal**: Strengthen the cross-subsystem invariant composition by adding
targeted operation-specific preservation proofs for sharing-pair predicates.
This phase addresses the composition gap documented at CrossSubsystem.lean:306–327.
**Gate**: `lake build SeLe4n.Kernel.CrossSubsystem` + `./scripts/test_full.sh`.
**Dependencies**: AD1–AD3 (clean codebase with integrated SchedContext proofs).
**Status**: COMPLETE — 2 core bridges + 31 per-operation bridge lemmas (33 total) covering all 31 kernel operations that modify `objects`. Zero sorry/axiom.

### Background: Current Composition Infrastructure

The existing infrastructure in `CrossSubsystem.lean` provides:

1. **8-predicate conjunction** (`crossSubsystemInvariant`):
   `registryEndpointValid`, `registryDependencyConsistent`,
   `noStaleEndpointQueueReferences`, `noStaleNotificationWaitReferences`,
   `serviceGraphInvariant`, `schedContextStoreConsistent`,
   `schedContextNotDualBound`, `schedContextRunQueueConsistent`

2. **12 disjoint pairs** with frame lemmas (6 original + 6 Z9-E):
   Predicates with non-overlapping read-sets are automatically preserved
   when the other predicate's fields change.

3. **4 sharing pairs** with conditional frame coverage:
   - `noStaleEndpointQueueReferences` ↔ `noStaleNotificationWaitReferences`
     (both read `objects`)
   - `registryEndpointValid` ↔ `noStaleEndpointQueueReferences`
     (both read `objects`)
   - `registryEndpointValid` ↔ `noStaleNotificationWaitReferences`
     (both read `objects`)
   - `registryDependencyConsistent` ↔ `serviceGraphInvariant`
     (both read `services`)

4. **2 full-bundle frame theorems**:
   - `crossSubsystemInvariant_objects_frame` (when non-objects fields unchanged)
   - `crossSubsystemInvariant_services_change` (when objects/registry unchanged)

**Gap**: When an operation modifies `objects`, all predicates reading `objects`
must be individually proven to preserve. Currently, each subsystem's
`Invariant/Preservation.lean` proves its own subsystem predicates, but the
cross-subsystem bridge connecting these proofs to the full bundle is incomplete
for certain operations.

### AD4-A: Audit operation coverage for sharing-pair predicates ✅

**Purpose**: Systematically identify which kernel operations modify `objects`
or `services` and which sharing-pair preservation proofs already exist vs.
are missing.

**Steps**:
1. Enumerate all operations in API.lean that modify `objects`:
   - IPC: `sendToEndpoint`, `receiveFromEndpoint`, `endpointReply`,
     `callEndpoint`, `replyRecv`, `notificationSignal`, `notificationWait`
   - Scheduler: `schedule`, `handleYield`, `timerTick`
   - Capability: `cspaceInsert`, `cspaceDelete`, `cspaceRevoke`, `cspaceMint`
   - Lifecycle: `suspendThread`, `resumeThread`
   - SchedContext: `schedContextConfigure`, `schedContextBind`,
     `schedContextUnbind`, `schedContextYieldTo`
2. For each operation, check:
   - Does `noStaleEndpointQueueReferences` preservation exist?
   - Does `noStaleNotificationWaitReferences` preservation exist?
   - Does `cdtConsistentWithObjectStore` preservation exist?
   - Does `noOrphanedQueueChains` preservation exist?
3. Enumerate all operations that modify `services`:
   - Service: `registerService`, `unregisterService`, `revokeService`
4. For each, check `registryDependencyConsistent` and `serviceGraphInvariant`
   preservation.
5. Document the coverage matrix.

**Output**: Coverage matrix identifying gaps. This is a research-only task.

**Files modified**: None (analysis only).
**Estimated effort**: Moderate — requires reading multiple Preservation.lean files.

### AD4-B: Add IPC operation cross-subsystem bridge lemmas (F-08) ✅

**Finding**: IPC operations are the highest-impact sharing-pair gap because
they modify `objects` extensively (TCB state changes, queue link updates,
pending message writes).

**Change**: In `SeLe4n/Kernel/CrossSubsystem.lean`, add bridge lemmas that
connect IPC subsystem preservation proofs to the cross-subsystem bundle.
For each major IPC operation, add a theorem of the form:

```lean
/-- AD4-B: IPC send preserves cross-subsystem invariant when
    per-subsystem preservation holds. -/
theorem sendToEndpoint_preserves_crossSubsystemInvariant
    (h_pre : crossSubsystemInvariant st)
    (h_ipc : ipcInvariantBundle st')
    (h_sched : schedulerInvariantBundle st')
    (h_eq_services : st'.services = st.services)
    (h_eq_registry : st'.serviceRegistry = st.serviceRegistry)
    : crossSubsystemInvariant st' := by
  ...
```

The key insight is that IPC operations do not modify `services` or
`serviceRegistry`, so the services-side predicates are preserved by the
existing `services_frame` lemma, and we only need to bridge the `objects`-
side predicates.

**Scope**: Add bridge lemmas for the 7 core IPC operations. Each lemma
follows the same structural pattern — the proof decomposes the 8-predicate
conjunction and reassembles it using per-subsystem preservation hypotheses
plus the services-frame lemma.

**Proof strategy**:
1. Decompose `crossSubsystemInvariant st` into 8 hypotheses
2. For predicates reading only `services`: apply services-frame lemma
   (services unchanged by IPC)
3. For predicates reading `objects`: apply the corresponding IPC preservation
   theorem from `IPC/Invariant/Preservation.lean` or
   `IPC/Invariant/EndpointPreservation.lean`
4. Reassemble the 8-predicate conjunction

**Files modified**: `CrossSubsystem.lean` (~80–120 lines added).
**Estimated effort**: Moderate — structural proofs following established pattern.

### AD4-C: Add Scheduler/Lifecycle operation cross-subsystem bridge lemmas (F-08) ✅

**Finding**: Scheduler operations (`schedule`, `handleYield`, `timerTick`) and
lifecycle operations (`suspendThread`, `resumeThread`) also modify `objects`.

**Change**: Add bridge lemmas in `CrossSubsystem.lean` following the same
pattern as AD4-B. Scheduler operations additionally modify `scheduler` state,
but the cross-subsystem predicates that read `scheduler` (only
`schedContextRunQueueConsistent`) already have frame coverage via
the SchedContext preservation proofs integrated in AD1.

**Scope**: Add bridge lemmas for 5 operations (3 scheduler + 2 lifecycle).

**Files modified**: `CrossSubsystem.lean` (~110 lines added).

### AD4-D: Phase AD4 gate verification ✅

**Verified**:
1. Module build: `lake build SeLe4n.Kernel.CrossSubsystem` — 69 jobs, PASS
2. Full build: `lake build` — 236 jobs, PASS
3. Full test: `./scripts/test_full.sh` — all tiers passed
4. Zero sorry/axiom in production code (3 matches are comments only)

**Gate condition**: All commands pass; zero sorry/axiom in production code. ✅

**Files modified**: None (verification only).

### AD4 Implementation Summary

| Sub-task | Change | Bridges |
|----------|--------|---------|
| AD4-A | Coverage matrix audit (33 operations documented) | 0 |
| AD4-B | 7 IPC operation bridges | 7 |
| AD4-C | 7 Scheduler/Lifecycle bridges (+switchDomain, scheduleDomain) | 7 |
| AD4-D | 7 Capability operation bridges | 7 |
| AD4-E | 4 SchedContext operation bridges | 4 |
| AD4-F | 2 Priority management bridges | 2 |
| AD4-G | 2 VSpace operation bridges | 2 |
| AD4-H | 1 IPC buffer bridge | 1 |
| AD4-I | 3 Lifecycle retype bridges (monotone objectIndex) | 3 |
| Core | 2 core bridge theorems (objects_change + retype) | 2 |
| **Total** | **2 core + 33 per-operation bridge lemmas** | **35** |
| **Lines** | **~773 lines added to CrossSubsystem.lean** | |

---

## 7. Phase AD5 — Closure & Documentation Sync ✅ COMPLETE

**Goal**: Final documentation synchronization, workstream history update,
and full validation.
**Gate**: `./scripts/test_full.sh` + all documentation sync checks.
**Dependencies**: AD1–AD4 (all code and proof changes complete).
**Status**: COMPLETE — all documentation synchronized, all tests pass, zero sorry/axiom.

### AD5-A: Update documentation artifacts ✅

**Change**: Synchronize all documentation touched by this workstream:

1. **`docs/WORKSTREAM_HISTORY.md`**: Add WS-AD entry:
   - Portfolio: Pre-Release Audit Remediation
   - Version range: v0.25.10–v0.25.1x
   - Phases: AD1–AD5, 19 sub-tasks
   - Finding count: 21 findings (7 actionable, 2 already addressed, 12 no-action)
   - Zero sorry/axiom

2. **`CHANGELOG.md`**: Add entry documenting:
   - F-01 fix (orphaned module integration)
   - F-02 improvement (fresh-TCB helper)
   - F-03 documentation (CapTransfer module docstring)
   - F-04/F-05/F-06/F-07 documentation (deployment guide)
   - F-08 proof strengthening (cross-subsystem bridge lemmas)

3. **`docs/codebase_map.json`**: Regenerate if Lean source files were added
   or module structure changed.

4. **`README.md`**: Sync metrics from `docs/codebase_map.json` if applicable.

5. **`scripts/website_link_manifest.txt`**: Add `docs/DEPLOYMENT_GUIDE.md`
   to the protected path list if the deployment guide is linked from the
   project website.

**Files modified**: 3–5 documentation files (~40–60 lines total).
**Estimated effort**: Minimal.

### AD5-B: Final validation and closure ✅

**Steps**:
1. Full test suite: `./scripts/test_full.sh`
2. Hygiene check: `./scripts/test_tier0_hygiene.sh`
3. Website link check: `./scripts/check_website_links.sh`
4. Sorry/axiom scan: `grep -rn 'sorry\|axiom' SeLe4n/ --include='*.lean'`
5. Verify all 21 findings have documented disposition in this workstream plan
6. Verify all actionable findings have corresponding sub-tasks marked complete

**Gate condition**: All commands pass; all findings accounted for.

**Closure criteria**: WS-AD is COMPLETE when:
- All 19 sub-tasks are marked complete
- All gate conditions satisfied
- Zero sorry/axiom in production code
- All documentation synchronized
- `test_full.sh` passes

---

## 8. Dependency Graph

```
AD1 (Integration Fix)
 │
 ├──→ AD2 (Code Quality)
 │     │
 │     └──→ AD3 (Deployment Docs)
 │           │
 │           └──→ AD4 (Composition Proofs)
 │                 │
 │                 └──→ AD5 (Closure)
 │
 └──────────────────────→ (all phases sequential)
```

**Rationale for sequential ordering**:
- AD1 must be first because it integrates orphaned modules that AD4's
  composition proofs may reference.
- AD2 establishes code quality improvements that AD3 documents.
- AD3 must precede AD4 because the deployment guide provides context for
  understanding which composition gaps matter for production.
- AD4 is the most substantial phase and should have a clean baseline.
- AD5 is always last (closure and sync).

**Parallelization opportunity**: AD2 and AD3 could technically run in parallel
since they modify disjoint files (Lean code vs. documentation). However,
sequential execution is recommended to maintain a clear audit trail and
avoid merge conflicts in documentation files.

---

## 9. Scope Estimates

### 9.1 Per-Phase Breakdown

| Phase | Lean Code | Proofs | Documentation | Total |
|-------|-----------|--------|---------------|-------|
| AD1 ✅ | 2 import + 10 doc lines | 0 | 0 | ~12 lines |
| AD2 | ~12 lines | 0 | ~20 lines | ~32 lines |
| AD3 | 0 | 0 | ~150–200 lines | ~150–200 lines |
| AD4 | 0 | ~140–200 lines | 0 | ~140–200 lines |
| AD5 | 0 | 0 | ~40–60 lines | ~40–60 lines |
| **Total** | **~14 lines** | **~140–200 lines** | **~210–280 lines** | **~364–494 lines** |

### 9.2 Files Modified Summary

| File | Phase | Change Type | Lines |
|------|-------|-------------|-------|
| `SchedContext/Invariant.lean` | AD1 | Doc note (cycle constraint) | ~10 |
| `CrossSubsystem.lean` | AD1 | 2 import lines + comment | ~6 |
| `IPC/DualQueue/Core.lean` | AD2 | New helper function | ~19 |
| `IPC/DualQueue/Transport.lean` | AD2 | Staleness comments (3 call sites) | ~3 |
| `IPC/Operations/CapTransfer.lean` | AD2 | Module docstring enhancement | ~11 |
| `docs/DEPLOYMENT_GUIDE.md` | AD3 | New file | ~80–100 |
| `docs/spec/SELE4N_SPEC.md` | AD3 | NI scope section | ~10–15 |
| `docs/SECURITY_ADVISORY.md` | AD3 | Cross-refs + SA-4 | ~15–20 |
| `docs/CLAIM_EVIDENCE_INDEX.md` | AD3 | New entries | ~20–30 |
| `CrossSubsystem.lean` | AD4 | Bridge lemmas | ~140–200 |
| `docs/WORKSTREAM_HISTORY.md` | AD5 | WS-AD entry | ~15–20 |
| `CHANGELOG.md` | AD5 | Version entry | ~15–20 |
| `docs/codebase_map.json` | AD5 | Regenerate | ~10 |

### 9.3 Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| AD4 composition proofs require unexpected helper lemmas | Medium | Medium | AD4-A audit step identifies gaps before proof work begins |
| Deployment guide content requires domain expert review | Low | Low | Cross-reference existing SECURITY_ADVISORY.md and formal theorems |
| F-01 import addition causes import cycle | **REALIZED** | Medium | Resolved: imports moved from re-export hub to CrossSubsystem.lean (downstream of cycle boundary) |
| AD4 proofs introduce sorry | Very Low | High | Gate condition requires sorry-free build; pre-commit hook enforces |
| Documentation sync misses a cross-reference | Low | Low | AD5-B systematic verification catches gaps |

---

## 10. Deferred Items (Out of Scope for WS-AD)

The following items are identified by the audit but explicitly deferred to
future workstreams:

| Item | Finding | Deferred To | Rationale |
|------|---------|-------------|-----------|
| `timeoutBlockedThreads` O(n) optimization | F-13 | WS-AD/perf (post-H3) | Requires hardware profiling to confirm bottleneck |
| MMIO volatile read formalization | F-16 | H3 hardware binding | Requires real GIC-400 hardware for validation |
| Cache/timing covert channel analysis | F-17 | External review | Requires hardware-level measurement |
| External threat-model review of non-BIBA | F-04 | External engagement | Process recommendation, not code work |
| Service orchestration NI | F-05 | Future NI workstream | Substantial new proof work beyond current scope |

---

## 11. Acceptance Criteria

WS-AD is COMPLETE when ALL of the following are satisfied:

1. **F-01 RESOLVED**: `SchedContext/Invariant.lean` imports both
   `Preservation.lean` and `PriorityPreservation.lean`; 18 theorems
   reachable from production import chain.

2. **F-02 IMPROVED**: `endpointQueuePopHeadFresh` helper exists in
   `DualQueue/Core.lean`; stale-TCB call sites annotated.

3. **F-03 DOCUMENTED**: `CapTransfer.lean` has module-level docstring
   explaining error-to-noSlot semantics.

4. **F-04 DOCUMENTED**: `DEPLOYMENT_GUIDE.md` Section 1.2 covers non-BIBA
   integrity model with formal theorem references.

5. **F-05 DOCUMENTED**: `DEPLOYMENT_GUIDE.md` Section 3 and `SELE4N_SPEC.md`
   cover NI boundary scope with formal theorem reference.

6. **F-06 DOCUMENTED**: `DEPLOYMENT_GUIDE.md` Section 1.3 covers scheduling
   covert channel with bandwidth analysis and seL4 precedent.

7. **F-07 DOCUMENTED**: `DEPLOYMENT_GUIDE.md` Section 2.1 provides labeling
   context override requirement with code example.

8. **F-08 STRENGTHENED**: Cross-subsystem bridge lemmas added for IPC (7 ops)
   and Scheduler/Lifecycle (5 ops) operations.

9. **F-10, F-12 VERIFIED**: Already-addressed findings confirmed with no
   additional action needed.

10. **Zero sorry/axiom**: `grep -rn 'sorry\|axiom' SeLe4n/ --include='*.lean'`
    returns zero matches.

11. **All tests pass**: `./scripts/test_full.sh` exits 0.

12. **Documentation synchronized**: WORKSTREAM_HISTORY.md, CHANGELOG.md,
    codebase_map.json, CLAIM_EVIDENCE_INDEX.md all updated.

---

*End of workstream plan.*
