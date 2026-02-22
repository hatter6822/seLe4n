# Repository Audit — v0.11.0 (2026-02-19)

## Executive Summary

This audit is an end-to-end analysis of the seLe4n repository at version 0.11.0. Every source file, test file, documentation page, CI workflow, and shell script was read and cross-referenced. The project is a Lean 4 formal-verification model of core seL4 microkernel semantics with ~1,400 lines of Lean source, three executable test suites, 14 shell scripts, four CI workflows, and 50+ documentation files.

**Overall assessment:** The architecture is sound, the type system is used well, and the CI/infrastructure layer is strong. The most significant weaknesses are in the executable test suites, where silent error suppression, tautological assertions, and incomplete state verification create false confidence in correctness. The formal proof layer is clean (zero `sorry` placeholders) but relies heavily on trivial error-case preservation theorems that, while technically correct, do not constitute meaningful security evidence. Documentation is accurate with one version-badge discrepancy.

---

## Table of Contents

1. [Architecture & Design](#1-architecture--design)
2. [Source Code Analysis](#2-source-code-analysis)
3. [Proof & Invariant Layer](#3-proof--invariant-layer)
4. [Testing Audit](#4-testing-audit)
5. [CI/CD & Build System](#5-cicd--build-system)
6. [Documentation Accuracy](#6-documentation-accuracy)
7. [Security Assessment](#7-security-assessment)
8. [Consolidated Findings Table](#8-consolidated-findings-table)
9. [Recommendations for Future Development](#9-recommendations-for-future-development)

---

## 1. Architecture & Design

### 1.1 Strengths

- **Clean layered architecture.** Five well-separated layers (Prelude → Machine → Model → Kernel subsystems → Testing) with explicit import boundaries. No circular dependencies.
- **Zero external dependencies.** `lake-manifest.json` declares an empty packages list. The entire formalization is self-contained, eliminating supply-chain risk at the Lean package level.
- **Typed identifier discipline.** `Prelude.lean` wraps every domain concept (`ObjId`, `ThreadId`, `DomainId`, `Priority`, `Irq`, `ServiceId`, `Badge`, `Slot`, `PAddr`, `VAddr`) in a distinct newtype, preventing accidental confusion between ID domains at the type level.
- **Operations/Invariant separation.** Every kernel subsystem (Scheduler, Capability, IPC, Lifecycle, Service, Architecture, InformationFlow) has a paired `Operations.lean` and `Invariant.lean`, enforcing a clean division between transition logic and proof obligations.

### 1.2 Weaknesses

- **List-based data structures throughout.** Object stores, runnable queues, CNode slots, and ASID root resolution all use `List`-based lookups (`find?`, `filter`, `any`), resulting in O(n) for every operation. Acceptable for a bounded formal model, but makes the model non-executable at real-kernel scale and distances the semantics from any concrete implementation.
- **No resource bounding.** Timer values (`Nat`), waiting lists (notification/endpoint queues), priority values, and badge accumulators are all unbounded. While intentional for the abstract model, this means the formalization does not capture the resource-bounded properties that real seL4 enforces.
- **Metadata redundancy.** `LifecycleMetadata` in `Model/State.lean` duplicates type and capability-reference information that is already derivable from the object store. While atomic-update theorems mitigate divergence risk, this doubles the surface area that must be kept consistent.

---

## 2. Source Code Analysis

### 2.1 Prelude & Machine (`Prelude.lean`, `Machine.lean`)

- **Quality:** Excellent. Clean newtype wrappers with `DecidableEq`, `Inhabited`, and `ToString` instances.
- **KernelM monad:** Custom `StateT`/`ExceptT` composition. Correct for sequential formal model; would not be thread-safe in a real kernel (intentional).
- **Machine model:** Memory as `PAddr → UInt8` function avoids concrete allocation. Timer increments without overflow modeling.

### 2.2 Object Model (`Model/Object.lean`, `Model/State.lean`)

- **CNode slot resolution** uses modulo arithmetic (`cptr.toNat % slotCount`) — correct but silent-wraparound behavior should be noted in documentation.
- **VSpaceRoot.mapPage** returns `none` on existing mapping — correct conflict prevention.
- **SystemState** carries 21 `KernelError` variants — comprehensive error enumeration.
- **Object indexing** via `objectIndex: List ObjId` for `resolveAsidRoot` — linear scan, no hash index.

### 2.3 Kernel Subsystems

| Subsystem | Finding | Severity |
|-----------|---------|----------|
| **Scheduler** | `chooseBestRunnable` is O(n) scan with deterministic tie-breaking (first-in-queue wins). Priority values unbounded (real seL4: 256 levels). No priority-inversion prevention. | Low |
| **Capability** | `cspaceRevoke` is local-only (same CNode). Cross-CNode revoke deferred. `cspaceMint` allows badge override from parent — no proof this cannot enable privilege escalation. | Medium |
| **IPC** | Endpoint state machine is correct (idle/send/receive). No double-wait prevention — a thread can call `notificationWait` twice without rejection. Notification waiting lists unbounded. | Medium |
| **Lifecycle** | `lifecycleRetypeObject` does atomic metadata + object-store update. `lifecycleRevokeDeleteRetype` prevents self-revoke (`authority = cleanup` check) but doesn't document why. | Low |
| **Service** | `serviceRestart` is non-atomic: stop can succeed while start fails, leaving service stopped. Dependency cycles not prevented (no cycle detection). | Medium |
| **InformationFlow** | Security lattice (confidentiality + integrity) defined with reflexivity/transitivity proofs. **No enforcement in any kernel operation.** Policy exists in isolation. | High |
| **Architecture** | Adapter operations require contract proofs. `adapterAdvanceTimer` rejects zero ticks without documenting why. No `adapterWriteMemory` defined. | Low |

### 2.4 Cross-Cutting Issues

- **No dead code detected.** All imports are used; all theorems reference other definitions.
- **No security vulnerabilities in traditional sense** (no SQL, XSS, command injection — pure Lean).
- **Information flow policy is defined but never enforced** — the `securityFlowsTo` function in `Policy.lean` is never called by any kernel operation. This is the single largest semantic gap in the codebase.

---

## 3. Proof & Invariant Layer

### 3.1 Zero `sorry` Placeholders

A complete scan of all Lean files found **zero** uses of `sorry`. All proofs are complete. This is a strong result.

### 3.2 Tracked Proof Issues

Two issues are explicitly tracked in `dev_history/audits/AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md`:

| ID | Description | Status |
|----|-------------|--------|
| TPI-001 | VSpace semantic obligations (determinism is a meta-property) | Tracked |
| TPI-002 | Information-flow projection tautologies (self-equality) | Tracked |

### 3.3 Tautological and Trivial Proofs

While no proofs are *incorrect*, a significant portion provide minimal assurance:

1. **Error-case preservation theorems** (14+ instances across Invariant files): Every invariant file contains theorems of the form "if the operation fails, the invariant is preserved" proven by `exact hInv`. These are trivially true because a failed operation returns the unchanged state. While technically correct, they inflate the theorem count without providing security evidence.

2. **Reflexivity proofs:** `lowEquivalent_refl` in `Projection.lean` proves `lowEquivalent ctx observer st st` by `rfl` — comparing a state to itself.

3. **Computational `decide` proofs:** `assumptionContractMap_nonempty`, `assumptionTransitionMap_nonempty`, `assumptionInvariantMap_nonempty` in `Assumptions.lean` — proven by finite case analysis. Technically useful but shallow.

4. **Definitional aliases:** `schedulerWellFormed_iff_queueCurrentConsistent` proves two names are the same definition via `simp`.

### 3.4 Missing Proofs (Not `sorry`, But Absent)

- **VSpace successful-operation preservation:** Only error cases are proven for `vspaceMapPage` and `vspaceUnmapPage`. No theorem proves that a *successful* map/unmap preserves `vspaceInvariantBundle`.
- **Information-flow non-interference:** No theorem proves that kernel operations preserve `lowEquivalent` for appropriate observers. The `endpointSend_preserves_lowEquivalent` theorem exists but is the only one — no coverage for scheduler, capability, lifecycle, or service operations.
- **Badge safety in mint:** `cspaceMint` allows badge override, but no theorem proves this cannot enable privilege escalation.

---

## 4. Testing Audit

### 4.1 Framework Overview

The testing framework uses five tiers (0-4) with tiered shell scripts, three executable Lean test suites, and a meta-test (`audit_testing_framework.sh`) that proves the framework itself works.

### 4.2 Critical Finding: TraceSequenceProbe — Silent Error Suppression

**File:** `tests/TraceSequenceProbe.lean`
**Severity:** Critical

The `stepOp` function (the core of the "randomized" probe) silently swallows all errors:

```lean
def stepOp (op : ProbeOp) (tid : ThreadId) (st : SystemState) : SystemState :=
  match op with
  | .send =>
      match Kernel.endpointSend probeEndpointId tid st with
      | .ok (_, st') => st'
      | .error _ => st    -- ← ERROR SILENTLY IGNORED
```

When an operation fails, the probe returns the *unchanged state* and continues. The invariant checks that follow then pass trivially because no mutation occurred. **This means the probe cannot detect any operation that fails when it shouldn't.** The entire 250-step "randomized" probe is operationally equivalent to repeatedly checking invariants on the initial state.

Additionally, the "randomized" seed is always 7 (hardcoded default), making this a fixed deterministic sequence, not a stochastic test.

### 4.3 Critical Finding: NegativeStateSuite — Incomplete State Verification

**File:** `tests/NegativeStateSuite.lean`
**Severity:** High

Multiple tests verify return values or invariant-bundle booleans but do not verify the actual state mutations:

1. **Badge accumulation test (lines 196-209):** Checks that the final badge equals `66 ||| 5` but never independently verifies what the badge was *before* the final signal. If the prior state already contained the expected value by coincidence, the test passes without validating accumulation.

2. **VSpace map test (line 115):** Calls `assertStateInvariantsFor` on the post-operation state but never verifies the mapping was actually created (i.e., a subsequent lookup would find it).

3. **Yield test (lines 256-261):** Verifies the runnable list is rotated but does not verify which thread is now `current`.

4. **Notification wait (lines 166-182):** Verifies the return value is `none` but inconsistently checks TCB `ipcState` — some waits check it, others don't.

### 4.4 Critical Finding: InformationFlowSuite — Tautological Security Claims

**File:** `tests/InformationFlowSuite.lean`
**Severity:** High

1. **`lowEquivalent` reflexivity witness (line 76-78):** Proves `lowEquivalent sampleLabeling reviewer sampleState sampleState` — comparing a state to itself. This is a tautology that verifies nothing about the projection system.

2. **Service projection test (lines 83-90):** Both `serviceBefore` and `serviceAfter` are set to `none` via projection of a state where the service is above the observer, making the `decide (serviceBefore = serviceAfter)` check trivially true regardless of whether the projection logic works.

3. **No service projection coverage:** `projectServiceStatus` is completely untested.

4. **No observer discrimination test:** No test verifies that a high-clearance observer sees more than a low-clearance observer.

### 4.5 Moderate Finding: MainTraceHarness — Output-Only, No Assertions

**File:** `SeLe4n/Testing/MainTraceHarness.lean`
**Severity:** Medium

The main trace harness prints results via `IO.println` but performs almost no assertions. It is a trace generator for fixture comparison (Tier 2), not a test suite. This is architecturally intentional but means the harness provides zero standalone correctness guarantees.

### 4.6 Moderate Finding: InvariantChecks — Bounded Discovery Window

**File:** `SeLe4n/Testing/InvariantChecks.lean`
**Severity:** Medium

`stateInvariantChecks` uses `(List.range 512).map ObjId.ofNat` as the default object-ID discovery range. Objects stored with IDs >= 512 are silently excluded from all invariant checks.

### 4.7 Moderate Finding: RuntimeContractFixtures — Binary Extremes Only

**File:** `SeLe4n/Testing/RuntimeContractFixtures.lean`
**Severity:** Medium

Only two fixtures exist: `runtimeContractAcceptAll` (accepts everything) and `runtimeContractDenyAll` (rejects everything). No intermediate contracts test realistic access-control policies. The accept-all contract is used by the main trace harness, meaning adapter tests cannot detect permission violations.

### 4.8 Testing Summary

| Test Component | Verdict | Key Issue |
|----------------|---------|-----------|
| TraceSequenceProbe | **Broken** | Silent error suppression; deterministic "random" seed |
| NegativeStateSuite | **Weak** | Incomplete state-mutation verification |
| InformationFlowSuite | **Weak** | Tautological assertions; missing service coverage |
| MainTraceHarness | **Output-only** | No standalone assertions (intentional) |
| InvariantChecks | **Limited** | Bounded 512-ID window; boolean approximation |
| RuntimeContractFixtures | **Insufficient** | Only accept-all / deny-all extremes |
| Shell test framework | **Strong** | Tiered gates work correctly; meta-tested |
| Tier 3 anchor checks | **Strong** | 450+ structural validators |

---

## 5. CI/CD & Build System

### 5.1 Strengths

- **Tiered CI pipeline** with proper dependency ordering (fast → smoke → full).
- **Supply-chain hardening:** `setup_lean_env.sh` pins the elan installer to a specific commit SHA with SHA256 checksum verification. This is excellent.
- **All shell scripts use `set -euo pipefail`** — strict error handling throughout.
- **Temporary file handling** uses `mktemp` + `trap` cleanup in all scripts that need it.
- **Meta-test of the testing framework** (`audit_testing_framework.sh`) creates an impossible fixture and verifies Tier 2 correctly rejects it.
- **Architecture-aware caching** includes `runner.arch` in cache keys for ARM64 isolation.
- **Security scanning** with Gitleaks (secrets), Trivy (vulnerabilities), and CodeQL (workflow analysis).

### 5.2 Weaknesses

| Finding | Severity |
|---------|----------|
| **GitHub Actions use floating tags** (`actions/checkout@v6`, `actions/cache@v5`, etc.) instead of SHA-pinned versions. While these are GitHub-maintained actions, SHA pinning prevents tag-hijacking attacks. | Low |
| **`lean_action_ci.yml` lacks explicit `permissions:` block.** Inherits default permissions, which may be overly broad. The `platform_security_baseline.yml` correctly restricts permissions. | Low |
| **No Lean-level test runner.** All tests run as standalone executables (`lake exe ...`). There is no Lean-native test framework collecting results, meaning test discovery is manual. | Low |

---

## 6. Documentation Accuracy

### 6.1 Version Badge Discrepancy

**README.md line 11** displays version badge `0.10.5`, but the actual version is `0.11.0` per `lakefile.toml`, `CHANGELOG.md`, and `docs/spec/SELE4N_SPEC.md`. This is the only factual discrepancy found across 50+ documentation files.

### 6.2 Verified Claims

All of the following were cross-referenced against source code:

- All 19 modules in the codebase map exist and match their documented purpose.
- All 8 WS-C workstreams marked "completed" have corresponding implemented code.
- All milestone slices (Bootstrap through M7) have supporting source.
- Quick-start commands (`setup_lean_env.sh`, `lake build`, `lake exe sele4n`) are correct.
- Validation commands (`test_fast.sh` through `test_nightly.sh`) exist and implement the documented tiers.
- CI policy claims in `docs/CI_POLICY.md` match actual workflow definitions.
- Architecture descriptions in the GitBook accurately reflect import structure.
- All documented executables in `lakefile.toml` are documented.
- No undocumented features were found.

### 6.3 Documentation Quality

- **Excessive volume:** 50+ markdown files with significant content overlap. The `DOCS_DEDUPLICATION_MAP.md` acknowledges this and tracks canonical sources, but the sheer volume creates maintenance burden.
- **GitBook synchronization requirement** (canonical docs → GitBook mirrors) adds friction and risks drift despite automation.

---

## 7. Security Assessment

### 7.1 Supply Chain

- **Lean packages:** Zero external dependencies. No supply-chain risk.
- **Elan installer:** Commit-SHA pinned + SHA256 verified. Excellent.
- **GitHub Actions:** Floating tags (minor risk). No untrusted input in `run:` blocks.
- **No secrets in repository.** `.gitignore` excludes `.env*`, `*.pem`, `*.key`, etc. Gitleaks scans full history.

### 7.2 Formal-Model Security Properties

| Property | Status |
|----------|--------|
| Capability attenuation | Proven (`mintDerivedCap_attenuates`) |
| Scheduler invariant preservation | Proven (error + success cases) |
| IPC well-formedness | Proven (endpoint queue consistency) |
| Lifecycle metadata coherence | Proven (atomic update theorems) |
| Information-flow non-interference | **NOT PROVEN** (policy defined, not enforced) |
| VSpace mapping isolation | Partially proven (error cases only) |
| Badge safety in mint | **NOT PROVEN** |

### 7.3 Operational Security Gaps

1. **No double-wait prevention** in IPC notification operations.
2. **Cyclic service dependencies** can deadlock without detection.
3. **Cross-CNode capability revocation** not implemented (local only).

---

## 8. Consolidated Findings Table

| # | Finding | Category | Severity | File(s) |
|---|---------|----------|----------|---------|
| F-01 | TraceSequenceProbe silently ignores operation errors | Testing | **Critical** | `tests/TraceSequenceProbe.lean` |
| F-02 | Information-flow policy defined but never enforced by kernel operations | Design | **High** | `Kernel/InformationFlow/Policy.lean` |
| F-03 | NegativeStateSuite does not verify actual state mutations | Testing | **High** | `tests/NegativeStateSuite.lean` |
| F-04 | InformationFlowSuite uses tautological assertions | Testing | **High** | `tests/InformationFlowSuite.lean` |
| F-05 | No non-interference proof for any kernel operation | Proof | **High** | `Kernel/InformationFlow/Invariant.lean` |
| F-06 | Badge override in cspaceMint lacks safety proof | Proof | **Medium** | `Kernel/Capability/Operations.lean` |
| F-07 | Service dependency cycles not prevented | Design | **Medium** | `Kernel/Service/Operations.lean` |
| F-08 | VSpace successful-operation preservation not proven | Proof | **Medium** | `Kernel/Architecture/VSpaceInvariant.lean` |
| F-09 | RuntimeContractFixtures only accept-all / deny-all | Testing | **Medium** | `SeLe4n/Testing/RuntimeContractFixtures.lean` |
| F-10 | InvariantChecks bounded to ObjId < 512 | Testing | **Medium** | `SeLe4n/Testing/InvariantChecks.lean` |
| F-11 | serviceRestart is non-atomic (stop succeeds, start fails) | Design | **Medium** | `Kernel/Service/Operations.lean` |
| F-12 | No double-wait prevention in notification operations | Design | **Medium** | `Kernel/IPC/Operations.lean` |
| F-13 | README version badge shows 0.10.5, actual is 0.11.0 | Documentation | **Low** | `README.md` |
| F-14 | GitHub Actions use floating tags instead of SHA pins | CI/CD | **Low** | `.github/workflows/*.yml` |
| F-15 | lean_action_ci.yml lacks explicit permissions block | CI/CD | **Low** | `.github/workflows/lean_action_ci.yml` |
| F-16 | Trivial error-preservation proofs inflate theorem count | Proof | **Low** | All `Invariant.lean` files |
| F-17 | List-based data structures give O(n) lookups everywhere | Design | **Low** | `Model/State.lean`, `Model/Object.lean` |

---

## 9. Recommendations for Future Development

### 9.1 Priority 1 — Fix Broken Tests

1. **F-01: Fix TraceSequenceProbe error handling.** Replace silent error suppression in `stepOp` with error propagation. When an operation fails unexpectedly, the probe should record and report it. Consider adding a distinction between "expected failures" (e.g., sending to a full endpoint) and "unexpected failures" (e.g., operation on missing object).

2. **F-03: Add state-mutation assertions to NegativeStateSuite.** After every operation, verify the expected state change occurred (not just that invariants still hold). For example, after `vspaceMapPage`, verify a subsequent `vspaceLookup` returns the mapped address.

3. **F-04: Replace tautological assertions in InformationFlowSuite.** Test `lowEquivalent` with *different* states (not identical ones). Add observer discrimination tests (high-clearance sees more than low-clearance). Test `projectServiceStatus` explicitly.

### 9.2 Priority 2 — Close Proof Gaps

4. **F-05: Prove non-interference for core operations.** Starting with scheduler and IPC (the most critical paths), prove that each operation preserves `lowEquivalent` for appropriate observers. This is the project's stated goal and the current gap between aspiration and evidence.

5. **F-06: Prove badge-override safety.** Show that `cspaceMint` with a non-parent badge cannot enable privilege escalation.

6. **F-08: Prove VSpace successful-operation preservation.** Complete the missing theorems for `vspaceMapPage` and `vspaceUnmapPage` success cases.

### 9.3 Priority 3 — Design Improvements

7. **F-07: Add service dependency cycle detection.** Either validate the dependency graph at registration time or prove the absence of cycles as an invariant.

8. **F-12: Add double-wait prevention.** Check whether a thread is already waiting before allowing `notificationWait` to add it to the waiting list.

9. **F-11: Make serviceRestart atomic** or document the intentional failure semantics (stop succeeds, start fails → service remains stopped).

### 9.4 Priority 4 — Infrastructure Polish

10. **F-13: Fix README version badge** to show 0.11.0.

11. **F-14: SHA-pin GitHub Actions** or use Dependabot to manage action version updates.

12. **F-15: Add explicit permissions block** to `lean_action_ci.yml`.

13. **F-09: Add intermediate RuntimeContractFixtures** that test realistic access-control policies (e.g., allow timer but deny memory, allow specific address ranges).

14. **F-10: Remove the 512-ID bound** in `InvariantChecks.stateInvariantChecks` by deriving the check list from the actual `objectIndex`.

---

*Audit conducted 2026-02-19 against commit HEAD on branch main, package version 0.11.0.*
