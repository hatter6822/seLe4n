# Comprehensive Lean + Rust Kernel Audit — seLe4n v0.21.7

**Date**: 2026-03-25
**Auditor**: Claude Opus 4.6 automated line-by-line security review
**Scope**: All 111 Lean source files (72,564 lines) + 27 Rust source files (4,081 lines)
**Method**: 9 parallel specialized audit agents, each performing complete file reads in ≤500-line chunks

---

## Executive Summary

| Severity | Count | Description |
|----------|-------|-------------|
| **CRITICAL** | **0** | No privilege escalation, capability forgery, information leakage, or memory safety vulnerabilities |
| **HIGH** | **1** | Rust ABI: u64→u32 truncation in error code decode could cause false-success |
| **MEDIUM** | **39** | Model/hardware gaps, test coverage gaps, proof performance, code quality |
| **LOW** | **28** | Style issues, documentation gaps, minor improvements |
| **INFO** | **200+** | Design decisions, architectural observations, positive findings |

### Key Result: **Zero `sorry` or `axiom`** across the entire Lean codebase. All proofs are machine-checked.

### Audit Coverage

| Subsystem | Files | Lines | CRIT | HIGH | MED | LOW |
|-----------|-------|-------|------|------|-----|-----|
| Foundation (Prelude, Machine, Model) | 10 | ~5,500 | 0 | 0 | 3 | 1 |
| Scheduler | 6 | ~5,100 | 0 | 0 | 4 | 3 |
| Capability | 5 | ~5,500 | 0 | 0 | 4 | 0 |
| IPC | 14 | ~15,300 | 0 | 0 | 1 | 0 |
| Information Flow | 9 | ~6,500 | 0 | 0 | 2 | 3 |
| Data Structures (RobinHood, RadixTree, FrozenOps) | 17 | ~7,700 | 0 | 0 | 2 | 1 |
| Architecture + Platform + Lifecycle + Service | 33 | ~8,400 | 0 | 0 | 9 | 12 |
| API + Testing + Main | 7 | ~4,250 | 0 | 0 | 7 | 6 |
| Rust Implementation (3 crates) | 27+3 | ~4,100 | 0 | 1 | 7 | 2 |
| **TOTAL** | **138** | **~76,600** | **0** | **1** | **39** | **28** |

---

## HIGH Severity Findings (1)

### H-01: Rust ABI — u64-to-u32 truncation in error code decode
- **File**: `rust/sele4n-abi/src/decode.rs:35`
- **Severity**: HIGH
- **Description**: `regs[0] as u32` truncates a u64 to u32 when decoding kernel error codes. If the kernel (or an attacker controlling return registers) places a value like `0x1_0000_0000` in x0, the truncation yields `0`, which means "success" — a **false success** interpretation when the kernel actually returned an error.
- **Impact**: A malicious or buggy kernel could cause userspace to interpret an error as success, potentially leading to use of uninitialized data or skipped error handling.
- **Mitigation**: The `unwrap_or(InvalidSyscallNumber)` fallback handles cases where the truncated value is in the 1–39 range but unrecognized. However, values that truncate to 0 are misinterpreted as success.
- **Recommendation**: Add a guard before the cast:
  ```rust
  if regs[0] > u32::MAX as u64 {
      return Err(KernelError::InvalidSyscallNumber);
  }
  ```
- **Exploitability**: Low in practice (requires kernel to return an invalid error code), but the fix is trivial and the defense-in-depth value is high.

---

## MEDIUM Severity Findings (39)

### Foundation Layer (3)

**M-FND-01**: `native_decide` in `RegisterFile.not_lawfulBEq` negative witness
- **File**: `SeLe4n/Machine.lean:220-222`
- **Impact**: Expands TCB for a non-security-critical negative theorem. Minimal risk.

**M-FND-02**: `TCB.BEq` inherits non-lawful `BEq` from `RegisterFile`
- **File**: `SeLe4n/Model/Object/Types.lean:402-414`
- **Impact**: Code relying on `tcb1 == tcb2 → tcb1 = tcb2` would be unsound. Guarded by explicit negative witness preventing accidental misuse.

**M-FND-03**: `storeObject` capability-refs rebuild is O(n)
- **File**: `SeLe4n/Model/State.lean:427`
- **Impact**: Performance concern for large CNodes. Not a security issue.

### Scheduler (4)

**M-SCH-01**: `currentThreadInActiveDomain` vacuously true for non-TCB objects in isolation
- **File**: `SeLe4n/Kernel/Scheduler/Invariant.lean:66-72`
- **Impact**: Mitigated by `currentThreadValid` in the composed bundle.

**M-SCH-02**: `handleYield` does not explicitly assert QCC pre-condition in code
- **File**: `SeLe4n/Kernel/Scheduler/Operations/Core.lean:309`
- **Impact**: Covered by proof-layer hypotheses in Preservation.lean.

**M-SCH-03**: `switchDomain` reads from `st` rather than `stSaved`
- **File**: `SeLe4n/Kernel/Scheduler/Operations/Core.lean:387-414`
- **Impact**: Intentional design; safety proven by `saveOutgoingContext_scheduler` frame lemma.

**M-SCH-04**: O(n) flat-list operations in RunQueue insert/remove
- **File**: `SeLe4n/Kernel/Scheduler/RunQueue.lean:119-304`
- **Impact**: Performance concern for production on RPi5. Acceptable for < 256 threads per documentation.

### Capability (4)

**M-CAP-01**: `radixMask` computed via unbounded Nat exponentiation
- **File**: `SeLe4n/Kernel/Capability/Operations.lean:97`
- **Impact**: Safe in model (arbitrary-precision Nat). Hardware binding must enforce 64-bit bounds.

**M-CAP-02**: Temporary double-occupancy during `cspaceMove`
- **File**: `SeLe4n/Kernel/Capability/Operations.lean:659-678`
- **Impact**: Safe in pure-functional model (no interleaving). Not observable.

**M-CAP-03**: `cspaceRevokeCdt` materializes full descendant list
- **File**: `SeLe4n/Kernel/Capability/Operations.lean:830-849`
- **Impact**: Memory concern for large CDTs. Addressed by streaming BFS variant.

**M-CAP-04**: CDT node removed on delete failure in strict revoke variant
- **File**: `SeLe4n/Kernel/Capability/Operations.lean:945-968`
- **Impact**: Intentional partial-progress design. Failure report surfaced to caller.

### IPC (1)

**M-IPC-01**: Mixed pre/post state reads in `endpointSendDualWithCaps`
- **File**: `SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean:80-97`
- **Impact**: Correct but subtle pattern. Receiver identity from pre-state, CSpace root from post-state.

### Information Flow (2)

**M-IF-01**: Declassification policy lacks runtime audit logging
- **File**: `SeLe4n/Kernel/InformationFlow/Policy.lean:552-568`
- **Impact**: Operations are formally sound but operationally unobservable. Deployment concern.

**M-IF-02**: `niStepCoverage` uses `syscallDecodeError` as universal witness
- **File**: `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean:728-747`
- **Impact**: Proves existence of some NI step per operation, not the specific correct one. Real coverage from `step_preserves_projection` exhaustiveness.

### Data Structures (2)

**M-DS-01**: Elevated `maxHeartbeats` in RobinHood Bridge.lean (3.2M, 8x default)
- **File**: `SeLe4n/Kernel/RobinHood/Bridge.lean:585`
- **Impact**: Proof-performance fragility under toolchain updates.

**M-DS-02**: Elevated `maxHeartbeats` in RobinHood Preservation.lean (800K, 2x default)
- **File**: `SeLe4n/Kernel/RobinHood/Invariant/Preservation.lean`
- **Impact**: Same as above.

### Architecture + Platform + Lifecycle + Service (9)

**M-ARCH-01**: VSpace permission bits not cross-checked against `MemoryKind` at decode
- **File**: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`
- **Impact**: Device regions could receive rwx permissions at decode time. VSpace layer enforces separately.

**M-ARCH-02**: Non-flush VSpace map/unmap variants are public (not `private`)
- **File**: `SeLe4n/Kernel/Architecture/VSpace.lean`
- **Impact**: Callers could accidentally use stale-TLB-prone variants. Production entry points include flush.

**M-LIFE-01**: No uniqueness-within-queue invariant for endpoint queue TCBs
- **File**: `SeLe4n/Kernel/Lifecycle/Operations.lean`
- **Impact**: `spliceOutMidQueueNode` only removes one occurrence if a TCB appears twice. Double-enqueue guards prevent this in practice.

**M-PLAT-01**: Truncated DTB `reg` property entries silently ignored
- **File**: `SeLe4n/Platform/DeviceTree.lean`
- **Impact**: Malformed DTB could hide memory regions. Low risk (DTB is trusted input).

**M-PLAT-02**: Boot-to-runtime invariant bridge only proven for empty config
- **File**: `SeLe4n/Platform/Boot.lean`
- **Impact**: Non-empty boot configs lack end-to-end proof that runtime invariant bundle holds after freeze. Tracked for WS-V.

**M-PLAT-03**: RPi5 memory map hardcoded for 4 GB model
- **File**: `SeLe4n/Platform/RPi5/Board.lean`
- **Impact**: 2 GB or 8 GB RPi5 variants would have incorrect RAM region bounds.

**M-PLAT-04**: MMIO write-one-clear modeled as direct store
- **File**: `SeLe4n/Platform/RPi5/MmioAdapter.lean:212-218`
- **Impact**: Proofs about GIC interrupt acknowledgment would be unsound if they rely on post-write register values.

**M-PLAT-05**: MMIO 32/64-bit writes lack alignment enforcement
- **File**: `SeLe4n/Platform/RPi5/MmioAdapter.lean:229-258`
- **Impact**: Unaligned MMIO writes on ARM64 cause unpredictable hardware behavior.

**M-CROSS-01**: Cross-subsystem invariant composition relies on informal field-disjointness argument
- **File**: `SeLe4n/Kernel/CrossSubsystem.lean:96-116`
- **Impact**: Most significant proof gap — subsystem non-interference not formally verified.

### API + Testing (7)

**M-API-01**: `resolveExtraCaps` silently drops failed resolutions
- **File**: `SeLe4n/Kernel/API.lean:309-318`
- **Impact**: By design per seL4 semantics. Userspace receives fewer caps with no error.

**M-API-02**: Code duplication between checked and unchecked dispatch
- **File**: `SeLe4n/Kernel/API.lean:331-687`
- **Impact**: Maintenance risk. Partially mitigated by 6 structural equivalence theorems.

**M-TEST-01**: No end-to-end test of `syscallEntryChecked` pipeline
- **File**: `SeLe4n/Testing/MainTraceHarness.lean`
- **Impact**: Information-flow-checked syscall pipeline not integration-tested.

**M-TEST-02**: `intrusiveQueueReachable` is `partial` (termination unchecked)
- **File**: `SeLe4n/Testing/InvariantChecks.lean:20`
- **Impact**: Test-only code. Uses explicit fuel for bounded traversal.

**M-TEST-03**: Inter-transition checks often validate original `st1` rather than mutated state
- **File**: `SeLe4n/Testing/MainTraceHarness.lean`
- **Impact**: Partially mitigated by T7-B additions.

**M-TEST-04**: No test coverage for `cspaceMove` end-to-end
- **File**: `SeLe4n/Testing/MainTraceHarness.lean`
- **Impact**: Dispatch path only covered by structural equivalence proofs.

**M-TEST-05**: `buildValidated` Check 8 conflicts with dequeue-on-dispatch semantics
- **File**: `SeLe4n/Testing/StateBuilder.lean:160-164`
- **Impact**: Rejects valid post-schedule states. Mitigated by using `build` directly.

### Rust Implementation (7)

**M-RS-01**: Several identifier types lack sentinel/validation concepts
- **File**: `rust/sele4n-types/src/identifiers.rs`
- **Impact**: No `is_reserved()` for Slot, DomainId, Priority, etc.

**M-RS-02**: `Reply` syscall maps to `Write` access right (policy choice)
- **File**: `rust/sele4n-types/src/syscall.rs:69`
- **Impact**: Matches Lean model. Worth documenting rationale.

**M-RS-03**: `IpcBuffer.get_mr()` returns `InvalidMessageInfo` for inline indices
- **File**: `rust/sele4n-abi/src/ipc_buffer.rs:99-106`
- **Impact**: Misleading error variant name.

**M-RS-04**: `InvalidMessageInfo` used for invalid rights in CSpace args
- **File**: `rust/sele4n-abi/src/args/cspace.rs:32`
- **Impact**: Should be `InvalidArgument`. Incorrect but non-breaking.

**M-RS-05**: `new_type` stored as raw `u64` in `LifecycleRetypeArgs`
- **File**: `rust/sele4n-abi/src/args/lifecycle.rs:14`
- **Impact**: ABI layer doesn't enforce TypeTag validity at decode time.

**M-RS-06**: `BitOr` on `PagePerms` not W^X validated
- **File**: `rust/sele4n-abi/src/args/page_perms.rs:66`
- **Impact**: By design (W^X checked at use-site), but could surprise callers.

**M-RS-07**: `Cap::from_cptr()` trusts caller about object type
- **File**: `rust/sele4n-sys/src/cap.rs:161`
- **Impact**: By design (kernel validates on syscall). Documented.

---

## Positive Findings

### Proof Discipline
- **Zero `sorry`/`axiom`** across all 111 Lean files — every theorem is machine-checked
- **Deterministic semantics** — all transitions return explicit `Except` results, no non-deterministic branches
- **Typed identifiers** — all wrapper structures enforce explicit `.toNat`/`.ofNat` conversion, preventing accidental mixing

### Security Architecture
- **Capability authority monotonicity**: Formally verified — no operation can amplify rights or substitute targets. Proven across mint, copy, mutate, move, delete, and revoke.
- **Non-interference**: 32-constructor `NonInterferenceStep` inductive covers all kernel operations. `step_preserves_projection` and `composedNonInterference_trace` provide trace-level NI.
- **IPC message integrity**: Atomic `storeTcbIpcStateAndMessage` prevents partial delivery. Message bounds enforced at every send boundary.
- **Endpoint state machine**: All blocking state transitions are deterministic and correct. Reply-target validation prevents confused-deputy attacks.
- **W^X enforcement**: Built into `PagePermissions` and checked at VSpace map time.
- **Memory scrubbing**: `scrubObjectMemory` zeros deleted object memory, preventing inter-domain leakage.

### Data Structure Verification
- **RobinHood hash table**: All 4 fundamental roundtrip properties machine-checked (get-after-insert/erase × same/different key). Probe chain dominance preserved by all operations.
- **CNodeRadix**: 24 correctness proofs including roundtrip, WF preservation, size bounds, fold completeness.
- **FrozenMap**: Roundtrip property proven. Key immutability proven. All non-objects fields preserved by store.

### Rust Implementation Quality
- **Minimal unsafe surface**: Exactly 1 `unsafe` block (ARM64 `svc #0` instruction) with correct clobber declarations
- **Zero external dependencies** across all 3 crates
- **Full `no_std` compatibility** with no heap allocation
- **1:1 ABI correspondence** verified against Lean model for all enums, constants, and register layouts
- **Comprehensive conformance tests** (19+ XVAL tests with register-by-register verification)

### Invariant Coverage
- **Scheduler**: 7-component bundle (QCC, RQU, CTV, domain-awareness, time-slice, EDF, context-matches)
- **Capability**: 7-property bundle (slotUnique, lookupSound, slotCountBounded, cdtCompleteness, cdtAcyclicity, depthConsistent, invExt)
- **IPC**: 4-component full bundle (ipcInvariant, dualQueueSystem, pendingMessagesBounded, badgeWellFormed) + 6-tuple scheduler-IPC contract
- **VSpace**: 7-component bundle including W^X and canonical address validation
- **Cross-subsystem**: 5-component conjunction bridging lifecycle, service, and IPC

---

## Recommendations

### Pre-Benchmarking (Priority: Immediate)

1. **Fix H-01**: Add u64 range guard in `rust/sele4n-abi/src/decode.rs:35` before the `as u32` cast. Trivial fix, high defense-in-depth value.

2. **Add test coverage** for `syscallEntryChecked` end-to-end pipeline, `cspaceMove` via register decode, and `cspaceMutate` success path (M-TEST-01, M-TEST-04).

### Pre-Hardware-Binding (Priority: WS-V)

3. **Make non-flush VSpace variants private** (M-ARCH-02) to prevent accidental stale-TLB usage.

4. **Add MMIO alignment enforcement** (M-PLAT-05) for 32/64-bit writes.

5. **Model write-one-clear semantics** (M-PLAT-04) for GIC registers before interrupt handling proofs.

6. **Parameterize RPi5 RAM region** (M-PLAT-03) from DTB rather than hardcoding 4 GB.

7. **Prove cross-subsystem invariant composition formally** (M-CROSS-01) rather than relying on informal field-disjointness argument.

8. **Extend boot-to-runtime invariant bridge** (M-PLAT-02) beyond empty config.

### Long-Term Hardening

9. **Add queue-member uniqueness invariant** (M-LIFE-01) for endpoint dual queues.

10. **Refactor high-heartbeat proofs** (M-DS-01, M-DS-02) for toolchain resilience.

11. **Add declassification audit trail** (M-IF-01) for operational observability.

---

## Methodology

Nine specialized audit agents operated in parallel, each assigned a disjoint partition of the codebase:

1. **Foundation Agent**: Prelude.lean, Machine.lean, Model/* (10 files)
2. **Scheduler Agent**: Scheduler/* (6 files)
3. **Capability Agent**: Capability/* (5 files)
4. **IPC Agent**: IPC/* (14 files)
5. **Information Flow Agent**: InformationFlow/* (9 files)
6. **Data Structures Agent**: RobinHood/*, RadixTree/*, FrozenOps/* (17 files)
7. **Architecture+Platform Agent**: Architecture/*, Platform/*, Lifecycle/*, Service/*, CrossSubsystem (33 files)
8. **API+Testing Agent**: API.lean, Testing/*, Main.lean (7 files)
9. **Rust Agent**: All rust/**/*.rs files + Cargo.toml (30 files)

Each agent read every file in its partition completely (using ≤500-line chunks for large files), checking for: security vulnerabilities, proof soundness (sorry/axiom), determinism, type safety, ABI correctness, and invariant completeness. Results were cross-validated and consolidated into this report.

---

*End of audit report.*
