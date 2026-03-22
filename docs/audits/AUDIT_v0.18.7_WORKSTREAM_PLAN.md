# WS-S Workstream Plan — Pre-Benchmark Audit Remediation (v0.18.7)

**Created**: 2026-03-22
**Baseline version**: 0.18.7
**Baseline audits**:
- `docs/audits/AUDIT_COMPREHENSIVE_v0.18.7_PRE_BENCHMARK.md` (50 findings)
- `docs/audits/AUDIT_COMPREHENSIVE_v0.18.7_KERNEL_RUST.md` (65+ findings)
**Prior portfolios**: WS-B through WS-R (all COMPLETE — see `docs/WORKSTREAM_HISTORY.md`)
**Constraint**: Zero `sorry`/`axiom` in production proof surface
**Combined finding count**: 5 High, 29 Medium (deduplicated), 30 Low, 80+ Info (across both audits)

---

## 1. Executive Summary

Two comprehensive audits of seLe4n v0.18.7 were conducted independently on
2026-03-22: a pre-benchmark audit (9 parallel agents, 50 findings) and a kernel
& Rust audit (multi-agent, 65+ findings). Neither audit found Critical
vulnerabilities. The codebase has zero `sorry`, zero `axiom` (outside 5
documented architectural assumptions), and zero `unsafe` Rust beyond the single
ARM64 `svc #0` instruction.

The 5 High findings are concentrated in two areas:
1. **Model specification gaps** — `MemoryRegion.wellFormed` is a runtime check
   not a proof obligation (F-H1), `Badge.ofNat` deprecated but callable (F-H2),
   `ThreadId.toObjId` identity mapping trust boundary undocumented (F-H3)
2. **Testing brittleness** — `toString`-based assertions in NegativeStateSuite
   (T-H1), golden-output fixture fragility in MainTraceHarness (T-H2)

The 29 deduplicated Medium findings cluster around six themes:

1. **Rust type-safety defects** — `Cap::restrict()` panics instead of returning
   `Result` (M-01), `Restricted::RIGHTS = EMPTY` semantic bug (M-02)
2. **Proof surface gaps** — CDT map consistency unproven (M-03),
   `scheduleDomain` lacks full-bundle preservation (M-08),
   `remove_preserves_wellFormed` missing (M-09), starvation-freedom unproven (S-M3)
3. **Model fidelity** — `objectIndex` unbounded growth (M-04),
   `AccessRightSet.bits` unbounded (L-09), `maxObjects` not enforced in
   `KernelState` (M-M4), `MemoryRegion.wellFormed` runtime-only (F-H1)
4. **API hygiene** — deprecated wrappers still in tests (M-05), `Badge.ofNat`
   still callable (M-07/F-H2), simulation contracts all-True (M-06)
5. **Hardware-binding preparation** — TLB invalidation not modeled in VSpace
   (A-M3), memory scrubbing on delete absent (L-M2), RPi5 board constants need
   datasheet validation (P-M2)
6. **Testing improvements** — `StateBuilder` bypasses `Builder` invariants
   (T-M1), error-path test coverage gaps (T-M2), `toString` assertions (T-H1)

This workstream plan organizes all actionable findings into **7 phases** (S1–S7)
with **81 atomic sub-tasks** (plus 1 stretch goal), explicit dependencies, gate
conditions, and scope estimates. The plan addresses all 5 High findings, all 29
deduplicated Medium findings, and selects 19 Low findings for inclusion based on
security relevance, proof chain completeness, and hardware readiness.

---

## 2. Consolidated Finding Registry

### 2.1 Cross-Reference Key

Findings from both audits are unified under a single registry. Where both audits
identified the same issue, the finding is listed once with both source IDs.

| Unified ID | Pre-Benchmark ID | Kernel-Rust ID | Severity | Description |
|------------|-------------------|----------------|----------|-------------|
| U-H1 | M-07 | F-H2 | HIGH | `Badge.ofNat` deprecated but callable |
| U-H2 | — | F-H1 | HIGH | `MemoryRegion.wellFormed` is runtime Bool, not Prop |
| U-H3 | — | F-H3 | HIGH | `ThreadId.toObjId` trust boundary undocumented |
| U-H4 | — | T-H1 | HIGH | `toString`-based test assertions brittle |
| U-H5 | — | T-H2 | HIGH | Golden-output fixture fragility |

### 2.2 Medium Findings — Rust Type Safety (2)

| Unified ID | Pre-Benchmark ID | Kernel-Rust ID | Location | Description |
|------------|-------------------|----------------|----------|-------------|
| U-M01 | M-01 | — | `rust/sele4n-sys/src/cap.rs:153-174` | `Cap::restrict()` and `Cap::to_read_only()` use runtime panics instead of `Result` |
| U-M02 | M-02 | — | `rust/sele4n-sys/src/cap.rs:122-127` | `Restricted::RIGHTS = EMPTY` — `.rights()` returns incorrect empty set |

### 2.3 Medium Findings — Proof Surface Gaps (5)

| Unified ID | Pre-Benchmark ID | Kernel-Rust ID | Location | Description |
|------------|-------------------|----------------|----------|-------------|
| U-M03 | M-03 | — | `Model/Object/Structures.lean:800-808` | CDT `childMap`/`parentMap` not proven consistent with `edges` |
| U-M08 | M-08 | — | `Scheduler/Operations/Preservation.lean:574` | `scheduleDomain` lacks `schedulerInvariantBundleFull` preservation |
| U-M09 | M-09 | — | `Scheduler/RunQueue.lean:170-282` | No `remove_preserves_wellFormed` for `RunQueue.remove` |
| U-M10 | — | S-M3 | `Scheduler/Operations/Core.lean` | `handleYield` — no starvation-freedom liveness proof |
| U-M11 | — | IF-M1 | `InformationFlow/Policy.lean` | `SecurityLabel` lattice properties assumed, not computationally verified |

### 2.4 Medium Findings — Model Fidelity (6)

| Unified ID | Pre-Benchmark ID | Kernel-Rust ID | Location | Description |
|------------|-------------------|----------------|----------|-------------|
| U-M04 | M-04 | — | `Model/State.lean:162-176` | `objectIndex` monotonic list unbounded growth |
| U-M12 | — | M-M4 | `Model/State.lean` | `maxObjects` not enforced as capacity invariant on `KernelState` |
| U-M13 | — | F-M1 | `Machine.lean` | `machineWordBounded` only validates GPR indices 0..31 |
| U-M14 | — | F-M2 | `Machine.lean:168` | `BEq RegisterFile` compares 32 GPRs — not lawful |
| U-M15 | — | F-M5 | `Machine.lean` | `Memory := PAddr → UInt8` — no alignment fault modeling |
| U-M16 | — | F-M6 | `Prelude.lean:511` | `KernelM` lacks `MonadStateOf`/`MonadExceptOf` instances |

### 2.5 Medium Findings — API & Hygiene (2)

| Unified ID | Pre-Benchmark ID | Kernel-Rust ID | Location | Description |
|------------|-------------------|----------------|----------|-------------|
| U-M05 | M-05 | — | `API.lean:245-360`, tests | Deprecated `api*` wrappers still exercised in test suites |
| U-M06 | M-06 | — | `Platform/Sim/*` | Simulation platform contracts are all `True` |

Note: Pre-benchmark M-07 / Kernel-Rust F-H2 (`Badge.ofNat`) is consolidated
under U-H1 in section 2.1. It is not double-counted as a Medium finding.

### 2.6 Medium Findings — Hardware Binding (5)

| Unified ID | Pre-Benchmark ID | Kernel-Rust ID | Location | Description |
|------------|-------------------|----------------|----------|-------------|
| U-M17 | — | A-M1 | `Architecture/RegisterDecode.lean` | `decodeCapPtr` accepts full Nat range, wraps silently |
| U-M18 | — | A-M3 | `Architecture/VSpace.lean` | VSpace `mapPage` does not model TLB invalidation |
| U-M19 | — | L-M2 | `Lifecycle/Operations.lean` | `deleteObject` does not scrub backing memory |
| U-M20 | — | P-M2 | `Platform/RPi5/Board.lean` | BCM2712 MMIO addresses hardcoded, no device tree abstraction |
| U-M21 | — | L-M1 | `Lifecycle/Operations.lean` | `retypeUntyped` byte-aligned, not page-aligned |

### 2.7 Medium Findings — Capability & IPC (5)

| Unified ID | Pre-Benchmark ID | Kernel-Rust ID | Location | Description |
|------------|-------------------|----------------|----------|-------------|
| U-M22 | — | C-M1 | `Capability/Operations.lean` | `deriveCap` Mint on endpoint — any Mint holder can forge badges |
| U-M23 | — | C-M2 | `Capability/Operations.lean` | `revokeCap` O(n) CDT traversal per level |
| U-M24 | — | I-M2 | `IPC/Operations/Endpoint.lean` | `callIPC` — no timeout mechanism for blocked callers |
| U-M25 | — | SV-M1 | `Service/Invariant/Policy.lean` | Bridge theorem signature drift risk |
| U-M26 | — | CS-M1 | `CrossSubsystem.lean` | 6-subsystem composition — adding 7th requires manual update |

### 2.8 Medium Findings — Data Structure & Performance (4)

| Unified ID | Pre-Benchmark ID | Kernel-Rust ID | Location | Description |
|------------|-------------------|----------------|----------|-------------|
| U-M27 | — | M-M1 | `Model/State.lean` | `HashMap` iteration order nondeterministic |
| U-M28 | — | RH-M1 | `RobinHood/Core.lean` | Load factor not explicitly bounded in spec |
| U-M29 | — | FO-M2 | `FrozenOps/Operations.lean` | 12 frozen ops must stay in sync with `API.lean` |
| U-M30 | — | F-M4 | `Prelude.lean` | `native_decide` used for 9 `isPowerOfTwo` proofs — TCB concern |

### 2.9 Selected Low Findings (19)

| Unified ID | Source ID | Location | Description | Included because |
|------------|-----------|----------|-------------|------------------|
| U-L01 | L-01 | `Machine.lean:147` | `RegisterFile.gpr` function type — not structurally comparable | Hardware fidelity |
| U-L02 | L-03 | `Model/Object/Structures.lean:375` | `resolveSlot` unbounded arithmetic | Hardware correctness |
| U-L03 | L-06 | `Model/Object/Structures.lean:810` | `CapDerivationTree.removeEdge` not defined | CDT completeness |
| U-L04 | L-07 | `Model/Object/Types.lean:158` | `IpcMessage.registers` `Array Nat` not `Array RegValue` | Type consistency |
| U-L05 | L-09 | `Model/Object/Types.lean:63` | `AccessRightSet.bits` unbounded Nat | Security boundary |
| U-L06 | L-11 | `Model/Object/Types.lean:326` | Notification `waitingThreads` is List not queue | Performance model |
| U-L07 | L-05 | `Model/Object/Types.lean:404` | `allocate` prepends children (reverse order) | Documentation |
| U-L08 | L-10 | `Model/Object/Types.lean:689` | `SyscallId` proofs use case-enumeration | Maintainability |
| U-L09 | R-L2 | `rust/sele4n-abi/` | No `#[deny(unsafe_code)]` on sele4n-abi | Defense-in-depth |
| U-L10 | R-L3 | `rust/sele4n-kernel/` | Panic handler uses bare `loop {}` | Diagnostics |
| U-L11 | — | T-M1 | `Testing/StateBuilder.lean` | `StateBuilder` bypasses `Builder` invariants | Test fidelity |
| U-L12 | — | T-M2 | tests/ | Error-path test coverage gaps | Coverage |
| U-L13 | — | T-L2 | `tests/InformationFlowSuite.lean` | Duplicates helpers from `Invariant/Helpers.lean` | DRY |
| U-L14 | — | SV-M2 | `Service/Invariant/Acyclicity.lean` | Dependency graph manually constructed | Maintainability |
| U-L15 | — | IF-L1 | `InformationFlow/Invariant/Composition.lean` | NI trace not indexed by operation sequence | Proof strength |
| U-L16 | — | S-M1 | `Scheduler/Operations/Selection.lean` | EDF tie-breaking uses `List.head?` — FIFO undocumented | Documentation |
| U-L17 | L-02 | `Machine.lean:393` | `noOverlapAux` O(n²) pairwise check | Documentation |
| U-L18 | L-04 | `Model/State.lean:130` | TlbState O(n) list operations | Documentation |
| U-L19 | L-12 | `Scheduler/RunQueue.lean:170` | `RunQueue.remove`/`rotateToBack` O(n) | Documentation |

---

## 3. Planning Principles

1. **Security-first ordering.** Findings that weaken the security boundary or
   enable type confusion are addressed before proof completeness or ergonomics.
   `Badge.ofNat` removal (U-H1) and `MemoryRegion.wellFormed` refinement (U-H2)
   ship in S1. Rust `Cap::restrict()` panic elimination (U-M01) ships in S1.

2. **Proof chain closure.** Composition theorems that carry hypotheses as
   parameters create seams. Each phase closes specific gaps by proving invariants
   from pre-state witnesses. CDT map consistency (U-M03), scheduler full-bundle
   preservation (U-M08), and `RunQueue.remove` well-formedness (U-M09) are
   addressed in dedicated proof phases.

3. **Hardware readiness.** The next milestone after WS-S is RPi5 hardware
   binding. Findings related to model–hardware fidelity (TLB invalidation,
   memory scrubbing, alignment, register bounds) are grouped in a dedicated
   hardware-preparation phase to minimize rework during bring-up.

4. **Test hardening before code changes.** Testing brittleness findings (U-H4,
   U-H5, U-L11) are addressed early so that subsequent code changes have
   robust regression detection. Structural assertions replace `toString`
   comparisons before any behavioral changes are made.

5. **Additive-first, deprecate-later.** New correct implementations are added
   alongside legacy code. Deprecated wrappers are removed only after all
   callers have migrated. This prevents cascade breakage.

6. **Zero sorry/axiom invariant.** No phase may introduce `sorry`, `axiom`,
   `admit`, or `partial` in production Lean code. Every phase gate includes
   a `sorry`/`axiom` scan.

7. **Atomic sub-task discipline.** Each sub-task is scoped to a single logical
   change that can be committed independently. Sub-tasks within a phase may
   depend on earlier sub-tasks in the same phase but never on later phases.

---

## 4. Phase Dependency Graph

```
S1 (Security & Rust)
 │
 └──→ S2 (Test Hardening)
       │
       └──→ S3 (Proof Surface Closure)
             │
             ├──→ S4 (Model Fidelity & Type Safety)
             │     │
             │     └──→ S5 (API Cleanup & Platform Contracts)
             │
             └──→ S6 (Hardware Preparation)  ←── parallel track
                   │
                   └─── ─── ─── ─── ─── ─── ──┐
                                                ↓
                              S7 (Documentation & Polish) ← waits for S4+S5+S6
```

**Critical path**: S1 → S2 → S3 → S4 → S5 → S7
**Hardware track**: S3 → S6 → S7 (runs in parallel with S4–S5 after S3)
**Parallelism opportunity**: After S3 completes, S4, S5, and S6 can proceed
concurrently on disjoint file sets:
- **S4** owns: `Model/`, `Machine.lean`, `Architecture/RegisterDecode.lean`
- **S5** owns: `Kernel/API.lean`, `Platform/Sim/`, `Lifecycle/`, tests, scripts
- **S6** owns: `Architecture/VSpace*.lean`, `Architecture/TlbModel.lean`,
  `Platform/RPi5/`, `InformationFlow/` (NI scrubbing proofs only)

---

## 5. Phase Specifications

### Phase S1 — Security Boundary & Rust Type Safety (v0.19.0)

**Scope**: Eliminate all High-severity findings and Rust type-safety defects.
Remove deprecated security-sensitive APIs. Harden trust boundaries.

**Rationale**: These findings represent the most direct risk to correctness and
security. `Badge.ofNat` allows constructing badges that exceed machine word
size. `Cap::restrict()` panics crash the kernel on programming errors.
`MemoryRegion.wellFormed` as a runtime check means malformed regions can be
constructed and passed to address-range functions.

**Dependencies**: None (first phase).

**Gate**: `test_smoke.sh` passes. Zero `sorry`/`axiom`. All Rust tests pass.
Specific module builds verified for every modified `.lean` file.

**Sub-tasks (14):**

**Intra-phase ordering constraints:**
- Rust chain: S1-D → S1-E → S1-F (restrict → read_only → Restricted rights fix)
- All Lean tasks are independent of each other and of Rust tasks
- Documentation tasks (S1-C, S1-M) can run in parallel with everything

| ID | Unified Finding | Description | Files | Estimate |
|----|-----------------|-------------|-------|----------|
| S1-A | U-H1 | Remove `Badge.ofNat` entirely — delete the deprecated function and its associated theorems. Zero production and test callers remain (all migrated to `Badge.ofNatMasked` in WS-R6). Verify no references remain via `grep`. | `Prelude.lean` | Trivial |
| S1-B | U-H2 | Convert `MemoryRegion.wellFormed` from `Bool` function to `Prop` field (refinement subtype or structure field). Update `MemoryRegion.contains`, `MemoryRegion.overlaps`, and all callers to require the proof obligation. | `Machine.lean`, `Platform/RPi5/Board.lean` | Medium |
| S1-C | U-H3 | Add end-to-end documentation of `ThreadId.toObjId` identity mapping trust boundary. Add a doc comment at the definition site and a validation section in `docs/spec/SELE4N_SPEC.md` explaining that callers must verify `.tcb tcb` after lookup. | `Prelude.lean`, `docs/spec/SELE4N_SPEC.md` | Small |
| S1-D | U-M01 | Convert `Cap::restrict()` from panic to `Result<Cap<Obj, Restricted>, CapError>`. Update all call sites. Add `CapError` type if not present. | `rust/sele4n-sys/src/cap.rs` | Medium |
| S1-E | U-M01 | Convert `Cap::to_read_only()` from panic to `Result` return type. Update all call sites. | `rust/sele4n-sys/src/cap.rs` | Small |
| S1-F | U-M02 | Fix `Restricted::RIGHTS` — store actual computed rights in `Cap` struct field instead of using `EMPTY` constant. Ensure `.rights()` returns the real restricted mask. | `rust/sele4n-sys/src/cap.rs` | Medium |
| S1-G | U-L05 | Add well-formedness predicate `bits < 2^5` to `AccessRightSet` or mask on construction via `AccessRightSet.ofNat`. Prove the mask is idempotent. | `Model/Object/Types.lean` | Small |
| S1-H | U-L09 | Add `#![deny(unsafe_code)]` crate-level attribute to `sele4n-abi`. Add a targeted `#[allow(unsafe_code)]` on `raw_syscall` in `trap.rs` (the single `svc #0` block). This ensures any *new* unsafe is rejected while preserving the necessary syscall instruction. | `rust/sele4n-abi/src/lib.rs`, `rust/sele4n-abi/src/trap.rs` | Small |
| S1-I | U-M30 | Evaluate replacing `native_decide` with `decide` for `isPowerOfTwo` proofs. If `decide` is feasible without excessive compile time, migrate. Document rationale if `native_decide` is retained. | `Prelude.lean`, affected files | Small |
| S1-J | U-M14 | Fix `BEq RegisterFile` lawfulness — either prove `a == b → a = b` for the 32-GPR comparison or document the limitation with a `nonLawful` annotation. | `Machine.lean` | Small |
| S1-K | U-M16 | Add `MonadStateOf` and `MonadExceptOf` typeclass instances for `KernelM` to enable generic monadic composition. Verify existing `LawfulMonad` instance compatibility. | `Prelude.lean` | Small |
| S1-L | U-L10 | Improve Rust panic handler — add minimal UART diagnostic output before `loop {}` or use a `wfe` (wait-for-event) instruction for power efficiency. | `rust/sele4n-kernel/src/main.rs` | Trivial |
| S1-M | U-M22 | Document badge-forging implications of Mint right on endpoint capabilities. Add doc comment at `deriveCap` site and security note in spec. This matches seL4 semantics but must be explicitly documented. | `Capability/Operations.lean`, `docs/spec/SELE4N_SPEC.md` | Small |
| S1-N | U-M13 | Extend `machineWordBounded` to validate all register file fields (not just GPR indices 0..31). Ensure PC, SP, CPSR are also word-bounded. | `Machine.lean` | Small |

---

### Phase S2 — Test Hardening (v0.19.1) **COMPLETE**

**Scope**: Eliminate testing brittleness before making behavioral changes in
subsequent phases. Replace `toString`-based assertions with structural equality.
Integrate `Builder` invariant checking into test state construction.

**Rationale**: Phases S3–S7 will modify kernel transitions, invariants, and
proofs. If the test suite is brittle (fragile assertions, bypassed invariants),
those changes will produce false failures or miss real regressions. Hardening
tests first provides a reliable safety net for all subsequent work.

**Dependencies**: S1 (Badge.ofNat removal may affect test files).

**Gate**: `test_full.sh` passes. All modified test suites exercise both positive
and negative paths. Zero `sorry`/`axiom`.

**Sub-tasks (10):**

| ID | Unified Finding | Description | Files | Estimate |
|----|-----------------|-------------|-------|----------|
| S2-A | U-H4 | Replace all 78 `reprStr`-based assertions in `NegativeStateSuite.lean` with structural pattern matching or `BEq` comparison on `KernelError` / result types. This is the highest-volume file (78 of 99 total `reprStr` occurrences). | `tests/NegativeStateSuite.lean` | Large |
| S2-B | U-H4 | Replace 7 `reprStr`-based assertions in `OperationChainSuite.lean` with structural comparisons. | `tests/OperationChainSuite.lean` | Small |
| S2-C | U-H4 | Replace remaining 14 `reprStr`-based assertions in `TwoPhaseArchSuite.lean` (6) and `TraceSequenceProbe.lean` (8). | `tests/TwoPhaseArchSuite.lean`, `tests/TraceSequenceProbe.lean` | Small |
| S2-D | U-H5 | Document golden-output fixture management in `docs/DEVELOPMENT.md` — explain when and how to update `main_trace_smoke.expected`, include rationale requirements for fixture changes. | `docs/DEVELOPMENT.md` | Small |
| S2-E | U-H5 | Add a fixture-diff check to `test_smoke.sh` that reports which specific lines changed (not just pass/fail), making fixture update review easier. | `scripts/test_smoke.sh`, `tests/fixtures/` | Small |
| S2-F | U-L11 | Create `BuilderTestState` module that wraps `StateBuilder` with `Builder` invariant validation. New test states go through `Builder` checks, failing on invariant violations rather than silently constructing invalid states. | `SeLe4n/Testing/StateBuilder.lean` | Medium |
| S2-G | U-L12 | Add error-path test cases for capability operations — test `cspaceMint` with insufficient rights, `cspaceCopy` with full destination CNode, `cspaceRevoke` with deep CDT tree. | `tests/OperationChainSuite.lean` or new test file | Medium |
| S2-H | U-L12 | Add error-path test cases for lifecycle operations — test `retypeFromUntyped` with insufficient untyped capacity, device untyped TCB rejection, child ID collision. | test files | Small |
| S2-I | U-L13 | Extract duplicated helpers from `InformationFlowSuite.lean` into `Testing/Helpers.lean` shared module. Update imports. | `tests/InformationFlowSuite.lean`, `SeLe4n/Testing/` | Small |
| S2-J | U-M05 | Migrate all remaining test cases from deprecated `api*` wrappers to `syscallEntry`/`dispatchWithCap` path. Only 2 call sites remain: `apiCspaceMint` in `OperationChainSuite.lean:358` and `apiEndpointSend` in `NegativeStateSuite.lean:1519`. After migration, remove `set_option linter.deprecated false` from test files. | `tests/OperationChainSuite.lean`, `tests/NegativeStateSuite.lean` | Small |

---

### Phase S3 — Proof Surface Closure (v0.19.2)

**Scope**: Close all identified gaps in the proof chain. Add missing preservation
theorems, CDT consistency invariants, and scheduler well-formedness proofs.

**Rationale**: These gaps represent seams in the machine-checked proof surface
where callers must manually compose sub-results or carry unproven assumptions.
Closing them makes the proof chain end-to-end compositional.

**Dependencies**: S1 (type changes in S1 may affect proof statements), S2
(test hardening provides regression net for proof refactoring).

**Gate**: `test_full.sh` passes. All new theorems compile with `lake build
<Module.Path>`. Zero `sorry`/`axiom`. Every new theorem has at least one
downstream consumer exercising it.

**Sub-tasks (14):**

**Intra-phase ordering constraints:**
- CDT chain: S3-A → S3-B → S3-C → S3-D (each builds on the prior definition/proof)
- Scheduler chain: S3-F → S3-G (well-formedness proof before consumption)
- Independent tracks: {S3-E, S3-H, S3-I, S3-J, S3-K, S3-L, S3-N} have no intra-phase deps
- Stretch: S3-M is independent but has high risk (see risk assessment)

| ID | Unified Finding | Description | Files | Estimate |
|----|-----------------|-------------|-------|----------|
| S3-A | U-M03 | Define `cdtMapsConsistent` invariant: `∀ p c, (p, c) ∈ edges ↔ c ∈ childMap[p] ∧ parentMap[c] = some p`. Prove it holds for the empty CDT. | `Model/Object/Structures.lean` | Medium |
| S3-B | U-M03 | **(Requires S3-A)** Prove `addEdge_preserves_cdtMapsConsistent` — `addEdge` maintains the bidirectional equivalence between `edges`, `childMap`, and `parentMap`. | `Model/Object/Structures.lean` | Medium |
| S3-C | U-L03 | **(Requires S3-A)** Define `removeEdge` for `CapDerivationTree`. Implement as removal from `edges`, `childMap`, and `parentMap`. Prove `removeEdge_preserves_cdtMapsConsistent`. Expose only through `revokeTargetLocal`; do not export standalone. | `Model/Object/Structures.lean` | Medium |
| S3-D | U-M03 | **(Requires S3-B, S3-C)** Add `cdtMapsConsistent` to the capability invariant bundle (`capabilityInvariant`). Thread through preservation theorems one operation at a time: mint → copy → move → delete → revoke. | `Capability/Invariant/Defs.lean`, `Capability/Invariant/Preservation.lean` | Large |
| S3-E | U-M08 | Prove `scheduleDomain_preserves_schedulerInvariantBundleFull` by composing existing `switchDomain_preserves_*` and `schedule_preserves_*` full-bundle theorems. | `Scheduler/Operations/Preservation.lean` | Medium |
| S3-F | U-M09 | Prove `remove_preserves_wellFormed` for `RunQueue.remove`. Show that removing a thread from a well-formed run queue preserves priority-bucket consistency. | `Scheduler/RunQueue.lean` | Medium |
| S3-G | U-M09 | **(Requires S3-F)** Update `schedule` operation's dequeue path to use `remove_preserves_wellFormed` instead of the current workaround that reasons on pre-remove state. | `Scheduler/Operations/Preservation.lean` | Small |
| S3-H | U-M11 | Add computational verification for `SecurityLabel` lattice properties — prove reflexivity, transitivity, and antisymmetry of `flowsTo` for concrete test labels. Add a decidable `flowsTo` check function. | `InformationFlow/Policy.lean` | Medium |
| S3-I | U-M25 | Add compile-time bridge signature witness — define a type alias or constant capturing the operation signature, so bridge theorems fail to compile if signatures change. | `Service/Invariant/Policy.lean` | Small |
| S3-J | U-M26 | Parameterize `crossSubsystemInvariant` composition — replace hardcoded 6-subsystem conjunction with a list-folded composition so adding a subsystem requires only extending the list. | `CrossSubsystem.lean` | Medium |
| S3-K | U-M28 | Add explicit load factor bound to `RHTable` specification — document or prove that insert fails when load exceeds 75%. Add a theorem `insert_fails_at_capacity`. | `RobinHood/Core.lean`, `RobinHood/Invariant/Defs.lean` | Small |
| S3-L | U-M29 | Add a compile-time check that frozen operations cover all `SyscallId` arms. Define a correspondence proof or exhaustiveness check linking `FrozenOps/Operations.lean` to `API.lean`. | `FrozenOps/Operations.lean` | Small |
| S3-M | U-L15 | **[STRETCH GOAL]** Strengthen NI trace composition — index the trace by the actual operation sequence (dependent list) rather than an unindexed `List NonInterferenceStep`. This is a deep proof refactoring with high risk of scope expansion. **Defer to WS-T if effort exceeds estimate.** | `InformationFlow/Invariant/Composition.lean` | Large |
| S3-N | U-L14 | Semi-automate dependency graph construction — derive the graph from subsystem module imports rather than manual enumeration. At minimum, add a compile-time check that the graph matches actual import dependencies. | `Service/Invariant/Acyclicity.lean` | Medium |

---

### Phase S4 — Model Fidelity & Type Safety (v0.19.3)

**Scope**: Strengthen the Lean model's fidelity to hardware semantics. Add
word-boundedness invariants, typed fields, and capacity enforcement.

**Rationale**: The Lean model uses unbounded `Nat` in several places where
real hardware uses fixed-width words. While the model is provably correct for
the abstract semantics, these gaps create a false-assurance risk: proofs about
`Nat`-valued fields don't guarantee the same properties hold for 64-bit values
on real hardware. Closing these gaps before hardware binding reduces rework.

**Dependencies**: S3 (proof surface must be complete before adding new
invariants that thread through existing proofs).

**Gate**: `test_full.sh` passes. All `isWord64` and bounds predicates are
exercised by at least one theorem. Zero `sorry`/`axiom`.

**Sub-tasks (13):**

| ID | Unified Finding | Description | Files | Estimate |
|----|-----------------|-------------|-------|----------|
| S4-A | U-M04 | Document `objectIndex` growth rate for typical RPi5 workloads. Calculate maximum memory consumption for 65536 objects. Add a `objectIndexBounded` advisory predicate. | `Model/State.lean`, `docs/spec/SELE4N_SPEC.md` | Small |
| S4-B | U-M12 | Add `objectCount_le_maxObjects` invariant to `KernelState` or `SystemState`. Enforce in `storeObject` — return error when capacity exceeded. Update preservation proofs. | `Model/State.lean` | Medium |
| S4-C | U-L02 | Add `isWord64 cptr.toNat` precondition to `resolveSlot` or mask the input to 64 bits before guard extraction. Prove the mask is idempotent for valid CNode configurations. | `Model/Object/Structures.lean` | Medium |
| S4-D | U-L04 | Change `IpcMessage.registers` from `Array Nat` to `Array RegValue` for type consistency. Update all IPC operations that read/write message registers. Update all affected proofs. | `Model/Object/Types.lean`, IPC operation files | Medium |
| S4-E | U-M15 | Document `Memory := PAddr → UInt8` alignment limitation. Add `alignedRead`/`alignedWrite` predicates for word-aligned memory access that the hardware binding can enforce. Add alignment faults as a documented model gap in `docs/spec/SELE4N_SPEC.md`. (Consolidates with hardware-prep alignment work — S6-F removed as duplicate.) | `Machine.lean`, `docs/spec/SELE4N_SPEC.md` | Small |
| S4-F | U-L01 | Evaluate replacing `RegisterFile.gpr : RegName → RegValue` with `Array RegValue` (size 32). If migration is feasible without excessive proof rework, implement. Otherwise, document the design rationale. | `Machine.lean` | Medium–Large |
| S4-G | U-L06 | Evaluate migrating `Notification.waitingThreads` from `List` to intrusive queue (matching endpoints). If the migration is tractable, implement. Otherwise, document the expected bound on waiting thread count and O(n) cost. | `Model/Object/Types.lean` | Medium |
| S4-H | U-L07 | Document `UntypedObject.allocate` children prepend convention explicitly — add a doc comment explaining reverse-chronological order and how proofs handle it. | `Model/Object/Types.lean` | Trivial |
| S4-I | U-L08 | Evaluate tactic automation for `SyscallId` case-enumeration proofs. If a `decide`-based tactic or macro can replace manual case splits, implement. | `Model/Object/Types.lean` | Small |
| S4-J | U-M27 | Document `HashMap` iteration order constraint — assert that all `KernelState.objects` uses are lookup-only (no iteration). Add a comment at the field definition. If any iteration exists, migrate to ordered structure. | `Model/State.lean` | Small |
| S4-K | U-M17 | Change `decodeCapPtr` to return `Option CPtr` for out-of-range register values. Update callers to handle `none` case. | `Architecture/RegisterDecode.lean` | Small |
| S4-L | U-M23 | Document `revokeCap` CDT traversal complexity — O(n) per level, bounded by `maxObjects`. Add complexity annotation at the definition site. | `Capability/Operations.lean` | Trivial |
| S4-M | U-M24 | Document `callIPC` timeout absence — explain that seL4's `Call` semantics provide no caller-side timeout, and that timeout monitoring is the responsibility of the scheduler/fault handler. Add to spec. | `IPC/Operations/Endpoint.lean`, `docs/spec/SELE4N_SPEC.md` | Small |

---

### Phase S5 — API Cleanup & Platform Contracts (v0.19.4)

**Scope**: Remove deprecated API wrappers, add restrictive simulation contracts,
and clean up cross-subsystem coupling.

**Rationale**: Deprecated `api*` wrappers bypass the production syscall entry
path (register decode, bounds checking, information-flow enforcement). Their
continued presence in the API surface creates risk that new code uses the
deprecated path. Simulation contracts being all-`True` means contract-level
bugs are only caught on hardware. A restrictive simulation variant catches
these earlier.

**Dependencies**: S2 (tests migrated off deprecated wrappers), S4 (model type
changes settled).

**Gate**: `test_full.sh` passes. No deprecated wrapper usage remains in test
suites. Simulation restrictive contracts produce non-trivial validation.
Zero `sorry`/`axiom`.

**Sub-tasks (9):**

| ID | Unified Finding | Description | Files | Estimate |
|----|-----------------|-------------|-------|----------|
| S5-A | U-M05 | **(Requires S2-J)** Remove all 14 deprecated `api*` wrappers from `API.lean`. Test migration completed in S2-J; this task is pure deletion. Verify `lake build SeLe4n.Kernel.API` succeeds after removal. | `Kernel/API.lean` | Small |
| S5-B | U-M05 | Audit invariant files and proofs for any references to removed `api*` wrappers. Update or remove affected proof statements. Verify `crossSubsystemInvariant` preservation holds for `syscallEntry` path only. | Invariant files | Medium |
| S5-D | U-M06 | Create `SimRestrictive` platform variant with substantive contracts mirroring RPi5 structure. Use simulation-appropriate bounds (e.g., 256MB RAM, 4-core, 1GHz timer) but enforce the same contract shape. | `Platform/Sim/` (new files) | Large |
| S5-E | U-M06 | Add a `SimRestrictive` test target to `test_smoke.sh` or `test_full.sh` that exercises the restrictive simulation contracts alongside the permissive defaults. | `scripts/test_*.sh` | Small |
| S5-F | U-M20 | Document BCM2712 address validation requirement — create a checklist for RPi5 board constant verification against the datasheet. Add as a pre-hardware-binding gate. | `Platform/RPi5/Board.lean`, `docs/DEVELOPMENT.md` | Small |
| S5-G | U-M21 | Add page-alignment check to `retypeUntyped` — validate that allocation base address is page-aligned (4KB boundary) for VSpace-bound objects. Return error on misalignment. | `Lifecycle/Operations.lean` | Medium |
| S5-H | U-M21 | Prove `retypeUntyped` page-alignment check preserves lifecycle invariants. Update preservation theorems. | `Lifecycle/Invariant.lean` | Medium |
| S5-I | U-L16 | Document EDF tie-breaking FIFO semantics — add doc comment at `selectNextThread` explaining that `List.head?` on the filtered list implements FIFO within priority level, matching seL4 behavior. | `Scheduler/Operations/Selection.lean` | Trivial |
| S5-J | U-L17/L18/L19 | Add complexity documentation to `noOverlapAux` (O(n²)), TlbState operations (O(n)), `RunQueue.remove`/`rotateToBack` (O(n)). Document expected bounds and why these are acceptable. | `Machine.lean`, `Model/State.lean`, `Scheduler/RunQueue.lean` | Small |

---

### Phase S6 — Hardware Preparation (v0.19.5)

**Scope**: Address all findings related to hardware-binding readiness. Model
TLB invalidation, memory scrubbing, and register decode bounds for clean RPi5
bring-up.

**Rationale**: The next major milestone after WS-S is Raspberry Pi 5 hardware
binding. Every model–hardware gap identified in the audits represents potential
rework during bring-up. Addressing these in the model first ensures the formal
spec accurately captures hardware behavior, so proofs carry over to the real
system.

**Dependencies**: S3 (proof surface complete), S4 (model type changes settled).
Can run partially in parallel with S5 if file sets don't overlap.

**Gate**: `test_full.sh` passes. RPi5 platform binding compiles with
`lake build SeLe4n.Platform.RPi5.Contract`. All TLB-related operations use
the flush-aware wrappers. Zero `sorry`/`axiom`.

**Sub-tasks (7):**

| ID | Unified Finding | Description | Files | Estimate |
|----|-----------------|-------------|-------|----------|
| S6-A | U-M18 | Audit all `vspaceMapPage`/`vspaceUnmapPage` call sites (7 found in `MainTraceHarness.lean`, plus API dispatch paths). Verify production paths use `vspaceMapPageWithFlush`/`vspaceUnmapPageWithFlush` (added in WS-R7, VSpace.lean:110-137). Migrate test harness calls that should use flushing variants. | `Testing/MainTraceHarness.lean`, `Kernel/API.lean` | Small |
| S6-B | U-M18 | Make unflushed `vspaceMapPage`/`vspaceUnmapPage` `private` or add `@[deprecated]` annotation marking them as internal proof decomposition helpers. Add spec-level documentation that all external callers must use the `WithFlush` variants. | `Architecture/VSpace.lean` | Small |
| S6-C | U-M19 | Add memory-scrubbing step to `deleteObject` — zero the backing memory region after object removal. Add a `memoryZeroed` postcondition predicate. | `Lifecycle/Operations.lean` | Medium |
| S6-D | U-M19 | Prove `deleteObject` memory scrubbing preserves lifecycle invariants. Prove the `memoryZeroed` postcondition holds. | `Lifecycle/Invariant.lean` | Medium |
| S6-E | U-M19 | Add `memoryZeroed` to the information flow invariant — scrubbed memory must not leak data between security domains. Prove `deleteObject` maintains NI after scrubbing. | `InformationFlow/Invariant/Operations.lean` | Medium |
| S6-F | U-M20 | Create device tree abstraction — define `DeviceTree` structure with parsed board configuration, so RPi5 addresses can be loaded from a device tree blob rather than hardcoded. (Preparation only — actual DT parsing is future work.) | `Platform/RPi5/Board.lean` or new file | Medium |
| S6-G | — | RPi5 board constant validation — cross-reference every address in `RPi5/Board.lean` against the BCM2712 datasheet. Document verification results as comments at each constant. | `Platform/RPi5/Board.lean` | Medium |

---

### Phase S7 — Documentation & Polish (v0.19.6)

**Scope**: Final documentation synchronization, workstream closure, and
comprehensive verification pass.

**Rationale**: Every prior phase introduces code, proof, and behavioral changes
that require documentation updates. This phase consolidates all documentation
work, runs the full test suite, and produces the closure report.

**Dependencies**: All prior phases (S1–S6).

**Gate**: `test_full.sh` passes. `test_nightly.sh` passes. All documentation
files synchronized. Zero `sorry`/`axiom`. Website link manifest verified.

**Sub-tasks (14):**

| ID | Unified Finding | Description | Files | Estimate |
|----|-----------------|-------------|-------|----------|
| S7-A | — | Synchronize `README.md` metrics from `docs/codebase_map.json`. Update Lean file count, theorem count, proof line count. | `README.md` | Small |
| S7-B | — | Update `docs/spec/SELE4N_SPEC.md` with all spec changes from S1–S6 (trust boundary documentation, alignment requirements, memory scrubbing, timeout semantics). | `docs/spec/SELE4N_SPEC.md` | Medium |
| S7-C | — | Update `docs/DEVELOPMENT.md` with new testing practices (structural assertions, golden-output fixture management, Builder-based test states). | `docs/DEVELOPMENT.md` | Small |
| S7-D | — | Update `docs/CLAIM_EVIDENCE_INDEX.md` with new claims from WS-S (CDT consistency, RunQueue well-formedness, memory scrubbing, page alignment). | `docs/CLAIM_EVIDENCE_INDEX.md` | Small |
| S7-E | — | Update `docs/WORKSTREAM_HISTORY.md` with WS-S summary (7 phases, 83 sub-tasks, version range v0.19.0–v0.19.6). | `docs/WORKSTREAM_HISTORY.md` | Small |
| S7-F | — | Regenerate `docs/codebase_map.json` to reflect new and modified Lean source files. | `docs/codebase_map.json` | Trivial |
| S7-G | — | Update affected GitBook chapters to mirror canonical doc changes. | `docs/gitbook/*.md` | Medium |
| S7-H | — | Verify `scripts/website_link_manifest.txt` — ensure no protected paths were renamed or removed during WS-S. | `scripts/website_link_manifest.txt` | Trivial |
| S7-I | — | Run `test_full.sh` end-to-end validation. Capture and archive results. | scripts | Small |
| S7-J | — | Run `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh` — full nightly validation including experimental checks. | scripts | Small |
| S7-K | — | Run full Rust test suite (`cargo test --workspace`). Verify all tests pass including new `Result`-based `restrict()` tests. | `rust/` | Small |
| S7-L | — | Final `sorry`/`axiom` scan across entire codebase. Verify zero sorry, zero axiom (outside `Assumptions.lean`). | all `.lean` files | Trivial |
| S7-M | — | Update `CHANGELOG.md` with WS-S release notes for v0.19.0–v0.19.6. | `CHANGELOG.md` | Small |
| S7-N | — | Produce WS-S closure report summarizing all remediated findings, test results, and residual items deferred to future workstreams. | `docs/audits/` (new file) | Medium |

---

## 6. Scope Summary

### Sub-task Count by Phase

| Phase | Version | Sub-tasks | Estimated Complexity |
|-------|---------|-----------|---------------------|
| S1 — Security & Rust | v0.19.0 | 14 | Medium |
| S2 — Test Hardening | v0.19.1 | 10 | Medium–Large |
| S3 — Proof Surface Closure | v0.19.2 | 14 (1 stretch) | Large |
| S4 — Model Fidelity | v0.19.3 | 13 | Medium |
| S5 — API Cleanup & Platform | v0.19.4 | 9 | Medium |
| S6 — Hardware Preparation | v0.19.5 | 7 | Medium |
| S7 — Documentation & Polish | v0.19.6 | 14 | Small–Medium |
| **Total** | | **81** (+ 1 stretch) | |

### Finding Coverage

| Severity | Total (deduplicated) | Addressed in WS-S | Deferred | Coverage |
|----------|---------------------|-------------------|----------|----------|
| High | 5 | 5 | 0 | 100% |
| Medium | 29 | 29 | 0 | 100% |
| Low | 30 | 19 | 11 | 63% |
| Info | 80+ | 0 (observational) | 80+ | N/A |

Note: U-M07 (Badge.ofNat) was deduplicated with U-H1 (same finding). Original
combined count was 30 Medium; after deduplication, 29 unique Medium findings.

### Files Impacted by Phase

| Phase | Lean Files Modified | Rust Files Modified | Script/Doc Files |
|-------|--------------------|--------------------|-----------------|
| S1 | ~8 | ~4 | ~2 |
| S2 | ~6 | 0 | ~3 |
| S3 | ~12 | 0 | 0 |
| S4 | ~10 | 0 | ~2 |
| S5 | ~8 | 0 | ~4 |
| S6 | ~6 | 0 | ~1 |
| S7 | 0 | 0 | ~10 |

---

## 7. Risk Assessment

### Technical Risks

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| CDT consistency invariant threads through many preservation proofs (S3-D) | Medium | High — could cascade across capability subsystem | Break into sub-phases: define invariant first, then thread through one operation at a time |
| `MemoryRegion.wellFormed` refinement (S1-B) changes structure signatures | Medium | Medium — callers must provide proof | Start with `Subtype` wrapper that auto-discharges for validated regions |
| `IpcMessage.registers` type change (S4-D) affects IPC proof surface | Medium | High — IPC proofs are the largest subsystem | Audit all proof sites before starting; use `Array.map RegValue.ofNat` bridge for migration |
| Restrictive simulation contracts (S5-D) may reveal latent contract bugs | Low | Medium — could require model fixes | Run restrictive contracts in CI but don't gate on them until validated |
| `removeEdge` definition (S3-C) introduces new CDT state transitions | Low | Medium — must compose with existing revocation proofs | Define `removeEdge` to be used only through `revokeTargetLocal`; don't expose standalone |
| NI trace indexing (S3-M) is a deep proof refactoring | High | Medium — may require significant proof rework | Treat as optional stretch goal; can defer to WS-T if effort exceeds estimate |

### Schedule Risks

| Risk | Mitigation |
|------|------------|
| S3 (proof surface) takes longer than estimated | S4 and S5 can start in parallel for non-overlapping files |
| S6 (hardware prep) reveals new model–hardware gaps | S6 includes a validation sub-task (S6-G) that discovers gaps early |
| Documentation drift during multi-phase work | S7 is dedicated to synchronization; intermediate phases include doc stubs |

### Codebase Validation Notes

The following assumptions were validated against the actual codebase before
finalizing the plan. Results informed scope estimates and task descriptions:

| Assumption | Validated | Impact on Plan |
|-----------|-----------|---------------|
| `Badge.ofNat` has remaining callers | Zero callers (all migrated in WS-R6) | S1-A downgraded from Small → Trivial |
| `toString`-based test assertions | 99 `reprStr` occurrences across 4 files (78 in NegativeStateSuite alone) | S2-A upgraded from Medium → Large |
| `MemoryRegion.wellFormed` is Bool | Confirmed: `Bool` function at Machine.lean:337 | S1-B validated |
| TLB flush wrappers exist (WS-R7) | Confirmed: `vspaceMapPageWithFlush`/`vspaceUnmapPageWithFlush` at VSpace.lean:110-137 with preservation proofs | S6-A/B revised to audit+migrate, not create |
| Deprecated `api*` test usage | Only 2 remaining call sites (OperationChainSuite:358, NegativeStateSuite:1519) | S2-J downgraded from Medium → Small |
| `sele4n-abi` has `#[deny(unsafe_code)]` | NOT present; crate contains the `svc #0` unsafe block | S1-H revised to use per-function `#[allow]` |
| `CDT.removeEdge` exists | NOT present — confirmed absent | S3-C validated |
| `KernelM` has `MonadStateOf`/`MonadExceptOf` | NOT present — custom helpers only | S1-K validated |
| `native_decide` count | 24 occurrences across 7 files (9 in Machine.lean for isPowerOfTwo) | S1-I validated |

---

## 8. Deferred Findings

The following Low and Info findings are **not addressed** in WS-S. They are
either purely informational, already documented, or represent future-work
opportunities that don't affect correctness or security.

### Deferred Low Findings (11)

| Source ID | Description | Reason for Deferral |
|-----------|-------------|---------------------|
| L-02 / F-M3 | `noOverlapAux` O(n²) | Acceptable for typical memory maps (<20 regions). Documented in S5-J. |
| L-04 | TlbState O(n) list | Abstract model only; hardware TLBs are O(1). Documented in S5-J. |
| L-08 | `findFirstEmptySlot` linear scan | Bounded by `limit` (typically 3). Acceptable. |
| L-12 / S-L1 | `RunQueue` O(n) operations | Acceptable for expected thread counts. Documented in S5-J. |
| S-L2 | `domainScheduleLength_pos` fragile proof | Correct; low risk of breakage. |
| S-M2 | `timerTick` fixed granularity | Matches current spec; variable-rate is future work. |
| C-L1 | `CapRights` Bool fields vs bitfield | Idiomatic for proof; diverges from seL4 but semantically equivalent. |
| C-L2 | `capInvariant_retype` verbose proof | Correct; tactic automation is nice-to-have. |
| I-L2 | `endpointInvariant` O(n) check | Proof-only cost; no runtime impact. |
| M-L1/L2 | Endpoint/VSpace List-based | Abstract model; fine for spec level. |
| M-L3 | `SchedContext.budgetRemaining` unbounded | No overflow in pure model; runtime binding must bound. |

### Deferred Info Findings (80+)

All Info findings are observational — they document positive security
properties, implementation choices, and architecture notes. No action required.
Key positive findings are highlighted in the audit reports' "Positive Findings"
sections.

---

## 9. Workstream Naming Convention

This workstream is designated **WS-S** (following the alphabetical sequence
after WS-R). The "S" can be read as "Strengthening" — strengthening the proof
surface, model fidelity, type safety, and hardware readiness ahead of the
benchmark and hardware-binding phases.

| Workstream | Focus | Version Range |
|------------|-------|---------------|
| WS-R | Comprehensive Audit Remediation | v0.18.0–v0.18.7 |
| **WS-S** | **Pre-Benchmark Strengthening** | **v0.19.0–v0.19.6** |
| WS-T (future) | Raspberry Pi 5 Hardware Binding | v0.20.0+ |

---

## 10. Acceptance Criteria

WS-S is complete when all of the following hold:

1. **All 5 High findings remediated** — `Badge.ofNat` removed, `MemoryRegion`
   uses refinement type, `ThreadId.toObjId` trust boundary documented, test
   assertions structural, fixture management documented.
2. **All 29 Medium findings remediated** — each finding either fixed in code/
   proof or documented with explicit rationale (for design-intentional findings
   like seL4 badge semantics).
3. **19 selected Low findings remediated** — per sub-task specifications.
4. **Zero `sorry`/`axiom` in production Lean** — outside `Assumptions.lean`.
5. **Zero `unsafe` Rust** — outside `svc #0` in `trap.rs`.
6. **`test_full.sh` passes** — all 4 test tiers green.
7. **`test_nightly.sh` passes** — including experimental checks.
8. **All Rust tests pass** — `cargo test --workspace` green.
9. **Documentation synchronized** — README, spec, development guide, claims
   index, workstream history, GitBook chapters all updated.
10. **Website links verified** — manifest check passes.
11. **Closure report produced** — comprehensive summary of remediation status.

---

## Appendix A: Finding Cross-Reference Matrix

This matrix maps each unified finding to its phase, sub-task, and source audit.

| Unified ID | Phase | Sub-task | Pre-Benchmark Audit | Kernel-Rust Audit |
|------------|-------|----------|---------------------|-------------------|
| U-H1 | S1 | S1-A | M-07 | F-H2 |
| U-H2 | S1 | S1-B | — | F-H1 |
| U-H3 | S1 | S1-C | — | F-H3 |
| U-H4 | S2 | S2-A/B/C | — | T-H1 |
| U-H5 | S2 | S2-D/E | — | T-H2 |
| U-M01 | S1 | S1-D/E | M-01 | — |
| U-M02 | S1 | S1-F | M-02 | — |
| U-M03 | S3 | S3-A/B/C/D | M-03 | — |
| U-M04 | S4 | S4-A | M-04 | — |
| U-M05 | S5 | S5-A/B/C | M-05 | — |
| U-M06 | S5 | S5-D/E | M-06 | — |
| ~~U-M07~~ | — | — | M-07 | F-H2 | (deduplicated → U-H1) |
| U-M08 | S3 | S3-E | M-08 | — |
| U-M09 | S3 | S3-F/G | M-09 | — |
| U-M10 | S3 | (deferred note) | — | S-M3 |
| U-M11 | S3 | S3-H | — | IF-M1 |
| U-M12 | S4 | S4-B | — | M-M4 |
| U-M13 | S1 | S1-N | — | F-M1 |
| U-M14 | S1 | S1-J | — | F-M2 |
| U-M15 | S4 | S4-E | — | F-M5 |
| U-M16 | S1 | S1-K | — | F-M6 |
| U-M17 | S4 | S4-K | — | A-M1 |
| U-M18 | S6 | S6-A/B | — | A-M3 |
| U-M19 | S6 | S6-C/D/E | — | L-M2 |
| U-M20 | S5/S6 | S5-F/S6-G | — | P-M2 |
| U-M21 | S5 | S5-G/H | — | L-M1 |
| U-M22 | S1 | S1-M | — | C-M1 |
| U-M23 | S4 | S4-L | — | C-M2 |
| U-M24 | S4 | S4-M | — | I-M2 |
| U-M25 | S3 | S3-I | — | SV-M1 |
| U-M26 | S3 | S3-J | — | CS-M1 |
| U-M27 | S4 | S4-J | — | M-M1 |
| U-M28 | S3 | S3-K | — | RH-M1 |
| U-M29 | S3 | S3-L | — | FO-M2 |
| U-M30 | S1 | S1-I | — | F-M4 |

## Appendix B: Starvation-Freedom Note (U-M10)

Finding U-M10 (scheduler starvation-freedom liveness proof) is classified as
Medium but represents a fundamental formal verification milestone that exceeds
the scope of a remediation workstream. Proving liveness requires:

1. A fairness assumption about the domain schedule (every domain gets scheduled
   infinitely often)
2. A progress assumption about threads (runnable threads eventually consume
   their time slice)
3. An inductive argument over infinite traces

This is categorized as **future work** for a dedicated liveness-verification
workstream (potentially WS-T or WS-U), not as a gap in the current safety-
property proof surface. All safety invariants (no deadlock, no priority
inversion within a domain, deterministic selection) are already proven.

---

**End of WS-S Workstream Plan**

*Author: Claude Opus 4.6 | Date: 2026-03-22 | Baseline: seLe4n v0.18.7*
*Source audits: AUDIT_COMPREHENSIVE_v0.18.7_PRE_BENCHMARK.md,
AUDIT_COMPREHENSIVE_v0.18.7_KERNEL_RUST.md*
