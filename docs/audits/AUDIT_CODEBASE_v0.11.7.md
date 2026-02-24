# seLe4n Codebase Audit — v0.11.7 (2026-02-24)

**Scope**: End-to-end audit of the entire seLe4n Lean 4 codebase (v0.11.7)
**Toolchain**: Lean 4.28.0, Lake v0.11.7
**Files audited**: 33 `.lean` source files, 16 shell scripts, 50+ documentation files
**Total lines of Lean**: 9,258
**Total theorems/lemmas**: 366 across 21 files
**Proof-soundness sweep**: Zero `sorry`, `axiom`, `native_decide`, `unsafe`, `panic!`, `unreachable!`, `noncomputable`, `Classical.*`, or `@[extern]` instances found
**Single `partial` usage**: `runProbeLoop` in `tests/TraceSequenceProbe.lean` (test-only, acceptable)

---

## Executive Summary

seLe4n is a Lean 4 formalization of core seL4 microkernel semantics producing
machine-checked proofs of invariant preservation over executable transition
semantics. The model covers scheduler transitions, capability-space operations,
synchronous IPC, notification signaling, object lifecycle, service orchestration,
architecture boundary contracts, and information-flow policy enforcement.

**The codebase is mechanically sound.** Every theorem compiles without `sorry`
or axioms. The build completes cleanly on Lean 4.28.0. The v0.11.6 audit
identified 32 findings (4 CRITICAL, 9 HIGH, 11 MEDIUM, 8 LOW). This audit
independently validates those findings, identifies documentation discrepancies,
and provides updated status.

### Severity Tally (v0.11.7 Independent Assessment)

| Severity | Count | Change from v0.11.6 |
|----------|-------|---------------------|
| CRITICAL | 4 | Unchanged — C-01 through C-04 remain open |
| HIGH     | 9 | Unchanged — H-01 through H-09 remain open |
| MEDIUM   | 12 | +1 new (M-14: documentation discrepancies) |
| LOW      | 8 | Unchanged |
| NEW      | 3 | Documentation/metadata accuracy issues |

### Key Positive Changes Since v0.11.6

1. **TPI-D07 fully resolved**: Service dependency acyclicity now has a complete
   BFS completeness bridge proof (940 lines in `Service/Invariant.lean`). No
   `sorry` remains in the acyclicity proof surface.
2. **Theorem count increased**: 366 theorems (up from ~295 estimated in v0.11.6
   audit; the prior count was an underestimate, not new additions).
3. **Toolchain upgraded**: Lean 4.27.0 → 4.28.0 with clean build.
4. **WS-E1 completed**: Test infrastructure and CI hardening delivered.

---

## Section 1: Proof Soundness Surface

### 1.1 Zero Unsound Constructs (CONFIRMED)

A comprehensive sweep of all 33 `.lean` files confirms:

- **0** `sorry` — no deferred proof obligations
- **0** `axiom` — no unproven logical assumptions
- **0** `native_decide` — no reflection bypasses
- **0** `unsafe` / `unsafeCast` — no memory-unsafe operations
- **0** `panic!` / `unreachable!` — no runtime abort paths
- **0** `noncomputable` — all definitions are computable
- **0** `Classical.*` — no classical logic dependencies
- **0** `@[extern]` — no FFI calls
- **1** `partial def` — `runProbeLoop` in test-only code (acceptable)
- **1** `set_option maxHeartbeats 800000` — BFS completeness proof in
  `Service/Invariant.lean:681` (justified by loop-invariant complexity)

This is a genuine strength. The entire proof surface is constructive, computable,
and self-contained within Lean's kernel.

### 1.2 Tautological Proofs (CONFIRMED — C-01, still open)

The v0.11.6 finding stands: `cspaceSlotUnique_holds` and `cspaceLookupSound_holds`
in `Capability/Invariant.lean` are mathematically trivial. Pure function
determinism (`f x = f x`) is guaranteed by the type system. These theorems
provide no additional assurance beyond what Lean already guarantees.

**Status**: Open. Targeted by WS-E2 (proof quality and invariant strengthening).

### 1.3 Non-Compositional Preservation Proofs (CONFIRMED — H-01, still open)

All `*_preserves_capabilityInvariantBundle` theorems destructure the pre-state
invariant, discard it, and re-prove components from scratch on the post-state.
The `_hStep` hypothesis (the actual operation) is unused in most cases.

**Status**: Open. Targeted by WS-E2.

---

## Section 2: Subsystem-by-Subsystem Analysis

### 2.1 Scheduler (Operations: 415 LOC, Invariant: 73 LOC)

**Proof Quality**: EXCELLENT — 25 theorems, all fully proven, zero sorry/axiom.

**Strengths**:
- Priority comparison logic correct (higher Nat = higher priority)
- `chooseThread_preserves_state` proves scheduler reads are side-effect-free
- `handleYield_preserves_runQueueUnique` correctly proves rotation preserves Nodup
- Three meaningful invariants: `queueCurrentConsistent`, `runQueueUnique`,
  `currentThreadValid`

**Open Findings** (all pre-existing, confirmed):
- **M-03**: Priority tie-breaking uses first-in-queue, not round-robin (WS-E6)
- **M-04**: No time-slice or preemption model (WS-E6)
- **M-05**: No domain scheduling — `DomainId` field exists but is unused (WS-E6)
- **L-06**: No initialization proof for default state (WS-E3)

**New Finding**:
- `handleYield` has formal proofs but zero empirical test invocations in any
  test harness. Recommend adding one test case. (LOW)

### 2.2 Capability (Operations: 237 LOC, Invariant: 895 LOC)

**Proof Quality**: EXCELLENT — 55 theorems, all fully proven, zero sorry/axiom.

**Strengths**:
- Badge-override safety fully proven (F-06 / TPI-D04): three theorems guarantee
  badge override cannot escalate privilege
- Rights attenuation always enforced via `rightsSubset` check
- Authority monotonicity proven for delete/revoke operations
- Guard/radix CNode resolution is deterministic and correct

**Open Findings** (all pre-existing, confirmed):
- **C-02**: Missing `cspaceCopy` and `cspaceMove` operations (WS-E4)
- **C-03**: No Capability Derivation Tree model (WS-E4)
- **C-04**: `cspaceRevoke` is local-only — cannot trace derivation chains
  across CNode boundaries (WS-E4)
- **H-02**: `cspaceInsertSlot` silently overwrites occupied slots (WS-E4)
- **H-03**: Badge override not proven safe w.r.t. notification routing (WS-E2)

### 2.3 IPC (Operations: 352 LOC, Invariant: 890 LOC)

**Proof Quality**: HIGH — 30+ theorems, all proven, but 18% are vacuous (H-09).

**Strengths**:
- Endpoint state machine (idle/send/receive) correctly modeled
- Notification badge accumulation via bitwise OR matches seL4 semantics
- Double-wait prevention (F-12) proven with Nodup waiting-list invariant
- Waiter wake-up correctly transitions TCB to `.ready` and adds to runnable

**Open Findings** (all pre-existing, confirmed):
- **H-09** (CRITICAL semantic gap): Endpoint operations never transition thread
  IPC state. `endpointSend` does not set `.blockedOnSend`, `endpointAwaitReceive`
  does not set `.blockedOnReceive`, `endpointReceive` does not unblock the dequeued
  sender. This makes `blockedOnSendNotRunnable` and `blockedOnReceiveNotRunnable`
  vacuously true for all reachable states. 6 of 33 preservation theorems (18%)
  are philosophically empty. (WS-E3)
- **M-01**: Single queue + optional single receiver diverges from seL4's separate
  send/receive queues (WS-E4)
- **M-02**: No message payload in IPC — endpoints exchange only thread IDs (WS-E4)
- **M-12**: No reply operation for bidirectional IPC (WS-E4)

**New Observation**:
- `storeTcbIpcState` silently returns `.ok st` when the thread TCB is not found
  (`lookupTcb` returns `none`). This is a defensive design choice but could mask
  bugs if a caller passes an invalid ThreadId. (LOW — informational)

### 2.4 Lifecycle (Operations: 316 LOC, Invariant: 227 LOC)

**Proof Quality**: EXCELLENT — 25+ theorems, all fully proven, zero sorry/axiom.

**Strengths**:
- Atomic retype with simultaneous metadata update prevents consistency violations
- Aliasing guard (`authority ≠ cleanup`) prevents self-invalidation
- Post-delete verification prevents use-after-free patterns
- `lifecycleRevokeDeleteRetype` composes revoke→delete→verify→retype cleanly
- Preservation of `lifecycleInvariantBundle` proven through operation

**No new findings**. This subsystem is well-structured and complete for its scope.

### 2.5 Service (Operations: 264 LOC, Invariant: 940 LOC)

**Proof Quality**: EXCELLENT — 47 definitions/theorems, all proven, zero sorry/axiom.

**Strengths**:
- TPI-D07 fully resolved: declarative acyclicity definition replaces vacuous
  BFS-based definition; BFS completeness bridge formally proved via loop-invariant
  argument with `go_complete` theorem
- Service dependency cycle detection via bounded BFS with cycle-rejection proof
- Cross-subsystem composition: service operations proven to preserve lifecycle
  and capability invariant bundles
- Restart failure semantics clearly documented and proven (F-11)

**Open Findings** (confirmed):
- **H-08**: BFS fuel exhaustion returns `false` (no path found), which is
  conservative but potentially unsound for very large service graphs. Mitigated
  by `serviceCountBounded` precondition. (WS-E2)
- `ServiceStatus.failed` and `ServiceStatus.isolated` are defined but no
  transition produces them — dead states in the model (LOW)
- `isolatedFrom` field populated but never enforced in start/stop ops (LOW)

### 2.6 Architecture (926 LOC across 5 files)

**Proof Quality**: EXCELLENT — 27 theorems, all proven, zero sorry/axiom.

**Strengths**:
- VSpace round-trip correctness: 4 theorems prove map→lookup, unmap→fault,
  cross-vaddr isolation (TPI-001/TPI-D05 CLOSED)
- ASID uniqueness + non-overlap preserved under successful map/unmap (F-08)
- Clean adapter architecture with timer/register/memory boundary contracts
- 5 ArchAssumptions fully enumerated with completeness proofs

**Open Findings** (confirmed):
- **H-07**: `vspaceInvariantBundle` omitted from `proofLayerInvariantBundle`
  — VSpace not included in the composed invariant bundle (WS-E3)
- **M-08**: Architecture assumptions are documentation infrastructure, not proof
  infrastructure — boundary contracts are never instantiated or consumed (WS-E6)
- Flat mapping model cannot reason about hierarchical page-table walks,
  permission bits, or TLB invalidation (documented design choice)

### 2.7 InformationFlow (740 LOC across 4 files)

**Proof Quality**: HIGH — 31 theorems, all proven, zero sorry/axiom.

**Strengths**:
- 5 non-interference preservation theorems (TPI-D01 through TPI-D03 CLOSED):
  `endpointSend`, `chooseThread`, `cspaceMint`, `cspaceRevoke`,
  `lifecycleRetypeObject` all proven to preserve `lowEquivalent`
- Reusable proof skeleton: `storeObject_at_unobservable_preserves_lowEquivalent`
- 3 enforcement gates: `endpointSendChecked`, `cspaceMintChecked`,
  `serviceRestartChecked` with allow/deny correctness proofs

**Open Findings** (confirmed):
- **H-04**: 4-element product lattice too coarse for real policies (WS-E5)
- **H-05**: No composed non-interference bundle theorem — individual operation
  proofs exist but cannot be directly composed into system-level guarantees (WS-E5)
- **M-07**: Enforcement is pre-gate only — no theorem proves unchecked operations
  cannot leak information (WS-E5)
- **M-13**: Integrity flow semantics use non-standard "both dimensions flow
  upward" lattice rather than BLP+BIBA. The comment says "integrity must not
  flow up" but the code allows it. The tests confirm this is intended behavior,
  but the documentation is misleading. (WS-E5)

### 2.8 Kernel API (21 LOC)

The API file is import-only — no public interface definition, no entry point
composition, no API-level invariant bundle. (L-01, confirmed)

---

## Section 3: Testing Infrastructure

### 3.1 Test Harness (MainTraceHarness: 531 LOC, 56+ test invocations)

**Coverage**: 15 unique kernel functions exercised across 7 subsystems. The
harness covers success paths, error branches, boundary cases, and parameterized
topologies (3 configurations: minimal, medium, large). Pre/post invariant checks
validate state consistency after major transitions.

**Quality**: Strong. All error branches validated. Cross-subsystem integration
tested. State invariants checked pre/post transitions. Parameterized topologies
exercise scaling.

### 3.2 Test Executables

| Executable | Lines | Coverage |
|-----------|-------|----------|
| `TraceSequenceProbe` | 163 | Randomized IPC endpoint probing with invariant checks |
| `NegativeStateSuite` | 372 | 25+ negative cases (CSpace, VSpace, IPC, scheduling, notifications, services) |
| `InformationFlowSuite` | 300 | Policy, projection, enforcement boundaries, distinct-state low-equivalence |

**Finding**: The `NegativeStateSuite` is exceptionally thorough — it covers
CNode guard mismatches, VSpace duplicate mapping conflicts, endpoint state
machine violations, notification double-wait prevention, scheduler malformed
state rejection, and service dependency cycle detection.

### 3.3 Test Script Infrastructure (16 scripts)

**Security**: No command injection vulnerabilities. All variable expansions
properly quoted. Python JSON encoding used safely.

**Coverage**: 4-tier testing strategy (fast/smoke/full/nightly) provides
layered quality gates.

**Findings**:
- **Tier 3 brittleness**: 500+ hardcoded anchor assertions in linear sequence;
  any single regex failure halts entire suite. Recommend refactoring as
  configuration-driven validator. (MEDIUM)
- **Toolchain archive integrity**: Elan installer is SHA-256 verified (WS-B9),
  but Lean toolchain `.tar.zst` archives are downloaded without SHA verification.
  (MEDIUM — consistency gap with WS-B9 hardening)
- **Nightly determinism check**: Uses exact `diff -u` on raw trace output;
  benign formatting changes cause false failures. (LOW)

---

## Section 4: Documentation Accuracy (NEW FINDINGS)

### 4.1 Toolchain Version Mismatch (NEW — M-14)

The v0.11.6 audit document (`docs/audits/AUDIT_CODEBASE_v0.11.6.md`, line 4)
states **"Lean 4.27.0, Lake 0.11.6"** but:
- `lean-toolchain` specifies `leanprover/lean4:v4.28.0`
- `lakefile.toml` specifies `version = "0.11.7"`

The audit was written against the v0.11.6 label but the actual toolchain had
already been upgraded. This mismatch could mislead readers about which Lean
version the audit findings apply to.

**Recommendation**: Correct the prior audit header or add a versioning note.

### 4.2 Theorem Count Underestimate (NEW — informational)

The v0.11.6 audit (Section 10.3) estimated ~295 theorems. A `grep` for
`theorem|lemma` across all `.lean` files finds **366 occurrences**. The prior
count appears to be an underestimate, not a result of new additions. The
discrepancy is informational and does not affect any finding.

### 4.3 SELE4N_SPEC.md Active Portfolio Header (NEW — informational)

`docs/spec/SELE4N_SPEC.md` Section 4 header reads "Active Workstream Portfolio
(WS-D)" but the body correctly describes the WS-E portfolio. The section heading
is stale.

---

## Section 5: Cross-Cutting Observations

### 5.1 Operations/Invariant Split (CONFIRMED POSITIVE)

Every kernel subsystem maintains the `Operations.lean` / `Invariant.lean` split
consistently. 5% of preservation theorems remain in Operations files
(Capability/Operations.lean lines 63-109) — minor stylistic inconsistency.

### 5.2 Deterministic Error Ordering (CONFIRMED POSITIVE)

17 distinct `KernelError` variants, all used consistently. Every operation
documents its error-checking order. Error-case theorems explicitly verify
failure conditions.

### 5.3 Typed Identifiers (CONFIRMED POSITIVE)

12 wrapper types (`ObjId`, `ThreadId`, `DomainId`, `Priority`, `Irq`,
`ServiceId`, `CPtr`, `Slot`, `Badge`, `ASID`, `VAddr`, `PAddr`) with explicit
`.toNat`/`.ofNat` conversions prevent accidental type confusion.

### 5.4 `Inhabited` Default ID 0 Risk (CONFIRMED — H-06)

All 12 identifier types derive `Inhabited`, making `default` return `⟨0⟩`.
ID 0 is not reserved or treated specially. Uninitialized variables silently
refer to object 0.

### 5.5 Data Structure Performance Characteristics (informational)

All collections use `List`:
- `VSpaceRoot.mappings`: O(n) lookup per address translation
- `CNode.slots`: O(n) lookup per capability resolution
- `SchedulerState.runnable`: O(n) priority selection
- `objectIndex`: O(n) membership check, grows monotonically (L-05)

This is acceptable for a formal model but means the model cannot reason about
performance-sensitive properties of real seL4.

---

## Section 6: Theorem Quality Classification

Building on the v0.11.6 audit's proof qualification (C-01/H-01):

| Category | Count | Assurance |
|----------|-------|-----------|
| **Substantive preservation** | ~200 | HIGH — proves operation preserves invariant through state transformation |
| **Error-case preservation** | ~80 | LOW — trivially true (state unchanged on error) |
| **Non-compositional preservation** | ~30 | MEDIUM — re-proves from scratch, discarding pre-state evidence |
| **Tautological** | 2 | NONE — `cspaceSlotUnique_holds`, `cspaceLookupSound_holds` |
| **Vacuously true** | 6 | NONE — `blockedOnSend/ReceiveNotRunnable` preservation (H-09) |
| **Non-interference** | 5 | HIGH — operation preserves low-equivalence |
| **Structural/bridge** | ~43 | HIGH — reusable infrastructure enabling composition |

**Summary**: ~248 theorems carry meaningful assurance. ~38 are trivially true
by construction (tautological, vacuous, or error-case). The remaining ~80 are
error-case preservations — technically correct but low value. The project's
own documentation (CLAIM_EVIDENCE_INDEX.md) correctly classifies these
categories.

---

## Section 7: Consolidated Finding Status

### 7.1 CRITICAL (4 findings — all remain open)

| ID | Title | Subsystem | Status | Target WS |
|----|-------|-----------|--------|-----------|
| C-01 | Tautological proofs | Capability | Open | WS-E2 |
| C-02 | Missing copy/move operations | Capability | Open | WS-E4 |
| C-03 | No Capability Derivation Tree | Capability | Open | WS-E4 |
| C-04 | Local-only revocation | Capability | Open | WS-E4 |

### 7.2 HIGH (9 findings — all remain open)

| ID | Title | Subsystem | Status | Target WS |
|----|-------|-----------|--------|-----------|
| H-01 | Non-compositional preservation proofs | Capability | Open | WS-E2 |
| H-02 | Silent slot overwrites | Capability | Open | WS-E4 |
| H-03 | Badge override safety gap | Capability | Open | WS-E2 |
| H-04 | Two-level lattice too coarse | InformationFlow | Open | WS-E5 |
| H-05 | No non-interference bundle theorem | InformationFlow | Open | WS-E5 |
| H-06 | Inhabited instances create magic ID 0 | Foundation | Open | WS-E3 |
| H-07 | VSpace missing from composed bundle | Architecture | Open | WS-E3 |
| H-08 | BFS fuel exhaustion unsoundness | Service | Open | WS-E2 |
| H-09 | Endpoint ops never transition thread IPC state | IPC | Open | WS-E3 |

### 7.3 MEDIUM (12 findings — 11 pre-existing + 1 new)

| ID | Title | Status | Target WS |
|----|-------|--------|-----------|
| M-01 | Endpoint model diverges from seL4 | Open | WS-E4 |
| M-02 | No message payload in IPC | Open | WS-E4 |
| M-03 | Priority scheduling bias | Open | WS-E6 |
| M-04 | No time-slice or preemption model | Open | WS-E6 |
| M-05 | No domain scheduling | Open | WS-E6 |
| M-07 | Enforcement is pre-gate only | Open | WS-E5 |
| M-08 | Assumptions are structural only | Open | WS-E6 |
| M-09 | Metadata sync hazard in storeObject | Open | WS-E3 |
| M-12 | No reply operation for bidirectional IPC | Open | WS-E4 |
| M-13 | Integrity flow semantics contradict docs | Open | WS-E5 |
| **M-14** | **v0.11.6 audit toolchain version mismatch (NEW)** | **Open** | **WS-E6** |
| — | Tier 3 test brittleness | Open | WS-E1 follow-up |

### 7.4 LOW (8 findings — all remain open)

| ID | Title | Status |
|----|-------|--------|
| L-01 | API.lean is just imports | Open (WS-E6) |
| L-02 | Default memory returns zero | Open (WS-E6) |
| L-03 | Missing monad helpers | Open (WS-E6) |
| L-04 | ID conversion without validation | Open (WS-E6) |
| L-05 | objectIndex never pruned | Open (WS-E6) |
| L-06 | No initialization proof | Open (WS-E3) |
| — | `handleYield` untested empirically | Open |
| — | Dead service states (failed/isolated) | Open |

---

## Section 8: Resolved Issues Since v0.11.6

| ID | Title | Resolution |
|----|-------|------------|
| TPI-D07 | Service dependency acyclicity | **CLOSED** — Declarative definition + BFS completeness bridge (940 LOC). No `sorry` remains. |
| TPI-D07-BRIDGE | BFS completeness proof | **CLOSED** — `go_complete` theorem proved via loop-invariant + measure descent. |
| WS-E1 | Test infrastructure/CI hardening | **CLOSED** — Tiered testing gates operational. |
| F-12 | Notification waiting-list uniqueness | **CLOSED** — Nodup invariant proven with preservation. |
| F-06/TPI-D04 | Badge-override safety | **CLOSED** — Three theorems prove no privilege escalation. |
| TPI-D05/F-08 | VSpace round-trip theorems | **CLOSED** — 4 round-trip theorems proven. |
| TPI-D01–D03 | Non-interference seeds | **CLOSED** — 5 operation-level low-equivalence preservation theorems. |

---

## Section 9: Security Assessment

### 9.1 No CVE-Worthy Vulnerabilities Identified

No exploitable vulnerabilities were found in the formal model, test infrastructure,
or build scripts. The model is a Lean 4 formalization — it does not execute on
real hardware and carries no runtime attack surface.

### 9.2 Model-Level Security Gaps

The following are **model fidelity gaps**, not vulnerabilities, but they limit
the security claims the project can make:

1. **Capability authority can leak across CNode boundaries** (C-04): Local-only
   revocation means capabilities in other CNodes pointing to the same target
   are not revoked. This is a known design limitation documented in the audit.

2. **VSpace not in composed invariant bundle** (H-07): Page-table modifications
   are not subject to information-flow enforcement, creating a gap where covert
   channels through memory mapping could go undetected.

3. **No thread blocking** (H-09): The IPC model cannot verify deadlock-freedom
   or scheduling liveness because senders/receivers never actually block.

4. **4-element security lattice** (H-04): Cannot model multi-domain policies
   or intransitive non-interference (declassifiers).

### 9.3 Build/CI Security

- **Elan installer**: SHA-256 verified (WS-B9 hardening) ✓
- **Lean toolchain archive**: Downloaded without SHA verification ⚠
- **Shell scripts**: No command injection vulnerabilities ✓
- **GitHub Actions**: SHA-pinned (checked by Tier 0 hygiene) ✓
- **.gitignore**: Excludes secrets, credentials, scanner output ✓

---

## Section 10: Recommendations

### Tier 1: Critical (WS-E2, WS-E4)

1. **Implement CDT model** (C-02, C-03, C-04): Add `CapDerivation` tracking
   parent-child edges. This is prerequisite for cross-CNode revocation and
   `cspaceCopy`/`cspaceMove`.

2. **Replace tautological proofs** (C-01, H-01): Either strengthen invariant
   definitions or explicitly document them as meta-properties.

### Tier 2: High (WS-E3, WS-E5)

3. **Implement thread blocking in IPC** (H-09): Make `blockedOnSend/Receive`
   predicates non-vacuous by adding `storeTcbIpcState` calls to endpoint
   operations.

4. **Add VSpace to composed invariant bundle** (H-07).

5. **Parameterize security lattice** (H-04) and add non-interference bundle
   theorem (H-05).

### Tier 3: Medium (WS-E6)

6. Fix documentation discrepancies (M-14, SELE4N_SPEC.md header).
7. Add message payload and reply operations to IPC (M-01, M-02, M-12).
8. Add domain scheduling using existing `DomainId` field (M-05).

---

*Audit conducted 2026-02-24 against commit on branch `claude/codebase-audit-uRwon`.*
*Toolchain: Lean 4.28.0, Lake v0.11.7.*
