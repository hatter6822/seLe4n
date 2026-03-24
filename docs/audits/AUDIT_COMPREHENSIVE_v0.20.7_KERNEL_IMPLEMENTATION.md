# Comprehensive Kernel Implementation Audit — seLe4n v0.20.7

**Date**: 2026-03-24
**Scope**: All 112 Lean modules + 26 Rust source files (complete kernel + userspace ABI)
**Auditor**: Automated deep-dive audit (Claude Opus 4.6)
**Method**: Line-by-line review of every source file, cross-referenced dead-code analysis via codebase-wide grep

---

## Executive Summary

This audit reviewed **every line** of the seLe4n v0.20.7 codebase: 112 Lean files
(~60,000 lines) and 26 Rust files (~3,500 lines). The codebase is in excellent shape
for a pre-release kernel — **zero `sorry` or `axiom` usage** across the entire Lean
proof surface. Two high-severity findings were identified, along with substantial
dead code that should be cleaned before the benchmark milestone.

### Findings Summary

| Severity | Count | Description |
|----------|-------|-------------|
| **High** | 2 | Frozen queue pop bug; API dispatch duplication |
| **Medium** | 22 | Dead modules, missing invariant integration, silent truncation, design gaps |
| **Low** | 60+ | Dead theorems/functions, trivial tautologies, proof duplication |
| **Info** | 40+ | Style, naming, documentation, minor ergonomics |

### Zero Sorry/Axiom Confirmation

All 112 Lean files were checked. **No `sorry` or `axiom` usage found anywhere in
the production proof surface.** This is the strongest possible result for a formally
verified kernel.

---

## HIGH SEVERITY FINDINGS

### H-01: `frozenQueuePopHead` Does Not Clear `queuePPrev` — Functional Correctness Bug

**File**: `SeLe4n/Kernel/FrozenOps/Core.lean:293`
**Severity**: HIGH

When dequeuing the head of an intrusive queue, the function sets:
```lean
let headTcb' := { headTcb with queuePrev := none, queueNext := none }
```

But `queuePPrev` is **NOT** cleared. After a `frozenQueuePopHead` followed by
`frozenQueuePushTail`, the `queuePPrev.isSome` check at line 219 will reject the
enqueue because `queuePPrev` retains its old value (e.g., `.endpointHead` or
`.tcbNext _`).

**Impact**: Legitimate IPC operations (e.g., send-receive-send) could fail with
`.illegalState` in the frozen phase. This is a functional correctness bug that
would manifest during benchmarking of multi-round IPC sequences.

**Fix**: Add `queuePPrev := none` to the record update at line 293.

---

### H-02: Massive Dispatch Duplication in API.lean (~320 Duplicated Lines)

**File**: `SeLe4n/Kernel/API.lean:331-672`
**Severity**: HIGH (code quality / maintenance risk)

`dispatchWithCap` (lines 331-491) and `dispatchWithCapChecked` (lines 510-672) are
nearly identical — ~160 lines each with 14 match arms. They differ only in that the
checked version uses `*Checked` variants for 7 operations. The remaining 7 arms are
character-for-character identical.

**Impact**: Any bug fix or operation change must be applied in two places. Divergence
between the two dispatch paths would create subtle security gaps where the checked
path behaves differently from the unchecked path.

**Fix**: Extract shared match arms into a common function. Have both dispatch paths
call it, with only the 7 policy-gated operations overridden.

---

## MEDIUM SEVERITY FINDINGS

### M-01: `MessageInfo::encode()` Silent Truncation (Rust)

**File**: `rust/sele4n-abi/src/message_info.rs:61-63`

`encode()` validates labels but silently masks `length` and `extra_caps`:
- `MessageInfo { length: 200, ... }.encode()` produces `(200 & 0x7F) = 72`
- `MessageInfo { extra_caps: 7, ... }.encode()` produces `(7 & 0x3) << 7 = 384`

The kernel re-validates on decode, but the Rust side silently truncates, causing
confusing mismatches. Additionally, `MessageInfo` fields are public, bypassing
`new()` validation.

**Fix**: Either make fields private (force `new()`) or add validation in `encode()`.

### M-02: `KMap` Module Is Entirely Dead Code

**File**: `SeLe4n/Kernel/RobinHood/KMap.lean` (219 lines)

`KMap` and all its operations, instances, and lemmas are defined but **never imported
by any other `.lean` file**. Designed as a "drop-in HashMap replacement" but never
integrated.

**Fix**: Remove the module or integrate it.

### M-03: `BEq` Instance for `RHTable` Is Asymmetric

**File**: `SeLe4n/Kernel/RobinHood/Bridge.lean:40-48`

The `BEq` instance checks `a.size == b.size && (fold over a checking b)` but does
NOT verify the reverse direction. Under `noDupKeys` + size equality this is
practically safe, but the instance is not provably reflexive for arbitrary tables.

### M-04: `serviceGraphInvariant` Not Integrated Into Global Invariant

**File**: `SeLe4n/Kernel/Service/Invariant/Acyclicity.lean`

`serviceDependencyAcyclic` is defined and preservation is proven, but
`serviceGraphInvariant` is **not composed into `CrossSubsystem.lean`**. The acyclicity
guarantee exists in isolation from the global kernel invariant.

**Fix**: Wire `serviceGraphInvariant` into `crossSubsystemInvariant`.

### M-05: Missing `registryInterfaceValid` Preservation for Cleanup

**File**: `SeLe4n/Kernel/Service/Registry/Invariant.lean`

`cleanupEndpointServiceRegistrations` only has a `_preserves_registryEndpointValid`
theorem. The `_preserves_registryInterfaceValid` half is missing, leaving a gap in
the cleanup path's invariant coverage.

### M-06: `native_decide` Usage Inconsistent With Project Policy

**Files**: `Model/Object/Types.lean:889,922`, `Model/Object/Structures.lean:100`

The project documents a policy of migrating `native_decide` to `decide` (Machine.lean
line 596), but 3 locations still use `native_decide`. These proofs rely on compiled
Lean code rather than the verified kernel evaluator, expanding the TCB.

### M-07: `decodeVSpaceMapArgs` Returns `.policyDenied` for Decode Error

**File**: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean:215`

Returns `.error .policyDenied` for invalid permissions, but this is a decode-level
validation error, not a policy denial. Semantically misleading error code.

### M-08: DeviceTree `readBE32` Uses Panic-Capable `get!`

**File**: `SeLe4n/Platform/DeviceTree.lean:183-186`

Uses `blob.get!` which panics on out-of-bounds. The bounds check exists but using
the panic-capable accessor undermines the safety model.

**Fix**: Use `blob.get` with bounds proof.

### M-09: DeviceTree Hardcoded 48-bit PA Width

**File**: `SeLe4n/Platform/DeviceTree.lean:314`

`fromDtbWithRegions` uses hardcoded `physicalAddressWidth := 48` but BCM2712 uses
44-bit PA. Would produce incorrect config for RPi5.

### M-10: Badge Value 0 Cannot Be Explicitly Set

**File**: `SeLe4n/Kernel/API.lean:385-388`

`if args.badge.val = 0 then none else some args.badge` means badge 0 is treated as
"no badge." A user cannot explicitly set badge 0, which could be a semantic surprise.

### M-11: Duplicate Frame Lemmas (FrozenOps)

**Files**: `FrozenOps/Commutativity.lean` vs `FrozenOps/Invariant.lean`

`frozenStoreObject_preserves_cdtSlotNode` and `frozenStoreObject_preserves_cdtNodeSlot`
are duplicated between these files (unprimed vs primed versions). The unprimed versions
are dead code.

### M-12: VSpace Operations Skip TLB Flush Without Compile-Time Guard

**File**: `SeLe4n/Kernel/Architecture/VSpace.lean:41-50`

`vspaceMapPage` and `vspaceUnmapPage` are documented as internal-only (skip TLB
flush), but there is no compile-time enforcement preventing misuse from dispatch paths.

### M-13: RPi5 Production Contract Admits All Register Writes

**File**: `SeLe4n/Platform/RPi5/RuntimeContract.lean:54-57`

The production `registerContextStable` checks SP preservation OR scheduler.current
change. Since `writeReg` modifies GPRs but not SP, the contract is trivially `True`
for all register writes — providing no meaningful guard.

### M-14: Sim Memory Map Duplication

**File**: `SeLe4n/Platform/Sim/RuntimeContract.lean:57-60`

`simSubstantiveMemoryMap` duplicates the memory map from `simMachineConfig`. Comment
warns "Must be kept in sync" — a maintenance hazard.

### M-15-22: Additional Dead Code Clusters (Medium)

| Module | Dead Items |
|--------|-----------|
| `Capability/Operations.lean` | `resolveCapAddressK`, `severDerivationEdge`, `processRevokeNode_lenient` (deprecated) |
| `Capability/Invariant/Defs.lean` | `capabilityInvariantBundleFull`, `WithMintCompleteness`, `WithCdtMaps` bundles + extractors; 9 dead private CNode field-equality lemmas |
| `Scheduler/Invariant.lean` | `canonicalSchedulerInvariantBundle` |
| `Scheduler/RunQueue.lean` | `rotateHead` + `mem_rotateHead` (~40 lines with proof obligations) |
| `InformationFlow/Policy.lean` | `bibaPolicy`, `bibaSecurityFlowsTo` + proofs, `defaultGenericLabelingContext`, `threeDomainExample` |
| `FrozenOps/Commutativity.lean` | Unprimed frame lemmas, `frozenQueuePushTail_preserves_*` (6 theorems) |
| `Architecture/Assumptions.lean` | `TransitionSurface`, `InvariantSurface`, `ContractRef`, `ExtendedBootBoundaryContract` |
| `Platform/RPi5/MmioAdapter.lean` | `MmioOp`, `MmioOpKind`, `MemoryBarrier`, `hasAppropriateBarriers`, `isMmioPeripheralAddress`, `isValid` |

---

## LOW SEVERITY FINDINGS (Selected — 60+ total)

### Dead Functions/Types (Not Referenced Outside Defining File)

| File | Definition | Lines |
|------|-----------|-------|
| `Prelude.lean` | `ObjId.valid`, `Deadline.none`, `Deadline.immediate` | 57, 204, 207 |
| `Prelude.lean` | `InterfaceId.toNat_ofNat`, `InterfaceId.ofNat_toNat` | 283-287 |
| `Machine.lean` | `alignedRead`, `alignedWrite` | 372, 376 |
| `FrozenState.lean` | `FrozenMap.fold`, `FrozenSet.mem`, `minObjectSize`, `objectCapacity` | 113, 124, 511, 522 |
| `Structures.lean` | `PagePermissions.ofNat_deterministic` | 91 |
| `Types.lean` | `MessageInfo.maxExtraCaps'` | 847 |
| `Selection.lean` | `chooseThreadInDomain` (trivial alias) | 344 |
| `Core.lean` | `restoreIncomingContext_establishes_context`, `_machine_no_tcb` | 191, 199 |
| `RunQueue.lean` | `maxPriorityValue`, `filterToList` | 378, 367 |
| `VSpace.lean` | `asidBoundToRoot`, `storeObject_objectIndex_eq_of_mem` | 25, 272 |
| `VSpaceBackend.lean` | `hashMapVSpaceBackend` (explicitly marked unused) | 150 |
| `DeviceTree.lean` | `fromDtb` (always `none`), `classifyMemoryRegion` (always `.ram`), FDT constants, `fromDtbWithRegions` | various |
| `Projection.lean` | `projectStateFast`, `computeObservableSet` | various |
| `Wrappers.lean` | `enforcementBoundary` (superseded by Extended) | 179 |
| `Policy.lean` | `bridgeSignatureWitness`, `fullBridgeSignatureWitness`, `ServicePolicyPredicate` | various |
| `Defs.lean` (IPC) | `badgeValid`, `tcbQueueChainAcyclic_no_self_loop`, `_no_two_cycle` | various |
| `CapTransfer.lean` | (no dead code — fuel pattern is sound) | -- |
| `RobinHood/Invariant/Defs.lean` | `robinHoodOrdered`, `invariant`, `loadFactorBounded` + theorems | 35-77 |
| `RadixTree/Core.lean` | `extractBits_zero_width`, `CNodeRadix.size`, `CNodeRadix.fanout` | various |
| `Rust: sele4n-abi` | `ServiceQueryArgs` (empty struct, no encode/decode), `REG_CAP_ADDR`/`REG_MSG_INFO`/`REG_MSG_BASE` | various |

### Trivial Tautology Theorems (`f x = f x` proved by `rfl`)

These theorems assert `f x = f x` and carry zero proof content:

| File | Theorem |
|------|---------|
| `FrozenState.lean` | `freeze_deterministic`, `objectCapacity_deterministic`, `FrozenMap.get?_deterministic` |
| `FreezeProofs.lean` | `freeze_deterministic'` (duplicate) |
| `RegisterDecode.lean` | `extractMessageRegisters_deterministic`, `decodeSyscallArgs_deterministic` |
| `SyscallArgDecode.lean` | 9 `*_deterministic` theorems |
| `RadixTree/Bridge.lean` | `buildCNodeRadix_deterministic` |
| `FrozenOps/Invariant.lean` | `frozenLookupObject_deterministic`, `frozenStoreObject_deterministic` |
| `Boot.lean` | `bootFromPlatform_deterministic` |
| `Structures.lean` | `PagePermissions.ofNat_deterministic` |
| `Capability/Operations.lean` | `resolveCapAddress_deterministic` |

### Proof Duplication Patterns

| Location | Pattern | ~Lines Duplicated |
|----------|---------|-------------------|
| `Capability/Invariant/Preservation.lean` | `cspaceRevoke_preserves_cdtNodeSlot` proof copied 4 times | ~100 |
| `Scheduler/Operations/Preservation.lean` | `schedule/handleYield/timerTick/switchDomain_preserves_*` identical case-splits | ~2000 |
| `IPC/Invariant/EndpointPreservation.lean` | 6-conjunct `ipcSchedulerContractPredicates` decomposition repeated 8+ times | ~400 |
| `IPC/Operations/Endpoint.lean` | 6 backward preservation theorems identical except constructor | ~100 |
| `IPC/Operations/SchedulerLemmas.lean` | 3 parallel `storeTcb*_preserves_*` families | ~400 |
| `Architecture/VSpaceInvariant.lean` | Map/unmap preservation + round-trip theorems duplicate structure | ~200 |
| `Platform/Sim+RPi5/ProofHooks.lean` | Structurally identical proof hooks | ~100 |

### Superseded Invariant Bundles

The scheduler has 3 bundle layers where only the largest is consumed:
- `schedulerInvariantBundle` (3-tuple) — vestigial
- `kernelInvariant` (4-tuple) — vestigial
- `schedulerInvariantBundleFull` (7-tuple) — **canonical, consumed by cross-subsystem code**

The capability subsystem has 4 bundle variants where only the base is consumed:
- `capabilityInvariantBundle` (7-tuple) — **canonical**
- `WithMintCompleteness`, `WithCdtMaps`, `BundleFull` — all unused

~500+ lines of preservation theorems maintain vestigial bundles.

### Unused Hypotheses

| File | Theorem | Unused Hypothesis |
|------|---------|-------------------|
| `InformationFlow/Invariant/Helpers.lean` | VSpace NI theorems | `_hOwnerHigh` |
| `Lifecycle/Invariant.lean` | `scrubObjectMemory_preserves_*` | `objects_eq`, `lifecycle_eq` have-bindings |
| `Scheduler/Preservation.lean` | `timerTick_preserves_currentTimeSlicePositive` | Current time-slice positive hypothesis |

---

## RUST IMPLEMENTATION FINDINGS

### Unsafe Code Audit

**Total unsafe blocks**: 2 (both in `sele4n-abi/src/trap.rs`)

1. **AArch64 `raw_syscall`** (line 22): Sound. Single `svc #0` instruction with correct
   register mapping and clobber specification.
2. **Mock `raw_syscall`** (line 52): Sound. Test-only mock.

All three crates use `#![deny(unsafe_code)]`. The two exceptions are well-scoped.

### Lean-Rust Type Consistency

| Type | Lean Variants | Rust Variants | Status |
|------|--------------|---------------|--------|
| `KernelError` | 38 (0-37) | 38 (0-37) | MATCH |
| `SyscallId` | 14 (0-13) | 14 (0-13) | MATCH |
| `KernelObjectType` / `TypeTag` | 6 (0-5) | 6 (0-5) | MATCH |
| `AccessRight` / `AccessRights` | 5 bits (0-4) | 5 bits (0-4) | MATCH |

### Rust Positive Findings

- **Panic freedom**: Zero `unwrap()`/`expect()` in production code paths
- **`no_std` compatibility**: All three crates correctly use `#![no_std]`
- **Fixed-size types**: No `Vec`, `String`, or heap allocation in core paths
- **`#[repr(C)]`**: Applied to `IpcBuffer` for FFI compatibility

### Additional Rust Issues

| ID | Severity | File | Finding |
|----|----------|------|---------|
| R-01 | Low | `sele4n-types/identifiers.rs` | `From<u64>` is public but inner fields are `pub(crate)` — allows constructing arbitrary IDs |
| R-02 | Low | `sele4n-types/rights.rs` | `From<u8>` accepts invalid bitmasks (bits 5-7) |
| R-03 | Low | `sele4n-abi/args/lifecycle.rs` | `new_type` is raw `u64`, not `TypeTag` |
| R-04 | Low | `sele4n-sys/ipc.rs` | `IpcMessage` fields are public, allowing invalid state |
| R-05 | Info | `sele4n-abi/decode.rs` | `SyscallResponse` missing `Copy` derive |
| R-06 | Info | `sele4n-sys/ipc.rs` | `MAX_MSG_REGS`/`MAX_EXTRA_CAPS` duplicated from `sele4n_abi` |

---

## PER-SUBSYSTEM ASSESSMENT

### Foundation Layer (Prelude, Machine, Model) — EXCELLENT

- 10 files, ~6,500 lines
- Zero sorry/axiom
- 3 `native_decide` usages inconsistent with project policy (M-06)
- ~15 dead definitions (Low)
- Strong typed-identifier discipline with complete `LawfulBEq`/`LawfulHashable` instances
- FreezeProofs layer is exemplary — well-structured proof chain

### Scheduler — EXCELLENT

- 6 files, ~5,600 lines
- Zero sorry/axiom
- `saveOutgoingContext`/`restoreIncomingContext` silently return unchanged state on
  invariant violation (documented as unreachable under `currentThreadValid`)
- `rotateHead` is dead code (~40 lines)
- ~20 dead theorem definitions in Preservation.lean (superseded by `*BundleFull`)
- `recomputeMaxPriority` is O(p) on priority-bucket removal — acceptable for <256 priorities

### Capability — EXCELLENT

- 5 files, ~3,500 lines
- Zero sorry/axiom
- Sound authority reduction proofs, badge routing consistency
- `CSpacePathAddr`/`cspaceResolvePath`/`cspaceLookupPath` are vestigial
- CDT postcondition-as-hypothesis pattern is a conscious design trade-off
- 4 duplicated `cdtNodeSlot` preservation proof blocks

### IPC — EXCELLENT

- 14 files, ~9,100 lines
- Zero sorry/axiom
- Complete invariant preservation coverage for all operations
- Blanket `linter.unusedVariables false` in Structural.lean (should be scoped)
- Significant proof duplication (~900 lines of repeated patterns)
- `endpointQueuePopHead_preserves_dualQueueSystemInvariant` is 354 lines — longest
  single theorem, could benefit from factoring

### Information Flow — EXCELLENT

- 9 files, ~5,800 lines
- Zero sorry/axiom
- Complete NI (non-interference) proof chain from per-operation to trace composition
- `bibaPolicy` and example code in Policy.lean are dead
- `projectStateFast` optimization path defined but unused

### Service — GOOD

- 7 files, ~2,300 lines
- Zero sorry/axiom
- `serviceGraphInvariant` not integrated into global invariant (M-04)
- `cleanupEndpointServiceRegistrations` missing half of invariant preservation (M-05)
- `serviceBfsFuel` naming is incorrect (algorithm is DFS)

### Lifecycle — EXCELLENT

- 2 files, ~1,400 lines
- Zero sorry/axiom
- Thorough defense-in-depth in `retypeFromUntyped` (7 error guards)
- Memory scrubbing correctly placed before retype
- Clean separation between operations and invariants

### RobinHood Hash Table — EXCELLENT

- 9 files, ~5,400 lines
- Zero sorry/axiom
- Complete functional correctness proofs (insert, erase, get)
- `KMap` module entirely dead (M-02)
- `BEq` instance asymmetry (M-03)
- Some duplicate helpers between Preservation.lean and Lookup.lean

### Radix Tree — EXCELLENT

- 4 files, ~1,200 lines
- Zero sorry/axiom
- 24 correctness proofs all complete
- `toList` is O(n^2) due to `acc ++ [item]` pattern — use `cons` + reverse
- `UniqueRadixIndices` precondition integration verified in FreezeProofs.lean

### Frozen Ops — GOOD (H-01 bug)

- 5 files, ~1,400 lines
- Zero sorry/axiom
- **H-01: `frozenQueuePopHead` queuePPrev bug** — must fix before benchmarking
- Dead frame lemmas in Commutativity.lean
- `frozenDefaultTimeSlice` hardcoded (should match builder phase)

### Architecture — GOOD

- 9 files, ~3,800 lines
- Zero sorry/axiom
- `SyscallArgDecode.lean` has 9 trivial tautology theorems
- VSpace TLB-skip operations lack compile-time misuse prevention (M-12)
- `ServiceQueryArgs` empty stub in both Lean and Rust

### Platform — GOOD

- 13 files, ~1,800 lines
- Zero sorry/axiom
- DeviceTree has multiple stubs (always-none, always-ram)
- RPi5 MmioAdapter has significant dead code (~6 unused types/functions)
- Sim/RPi5 ProofHooks are structurally identical (duplication)

### API — NEEDS WORK (H-02 duplication)

- 1 file, ~1,000 lines
- Zero sorry/axiom
- **H-02: ~320 lines of duplicated dispatch code** — highest-priority refactor
- Badge value 0 semantic surprise (M-10)

### Rust Implementation — EXCELLENT

- 26 files, ~3,500 lines
- 2 unsafe blocks, both sound and well-justified
- Lean-Rust type parity confirmed across all 4 dimensions
- Panic-free production paths
- `MessageInfo::encode()` silent truncation (M-01) is the only notable issue

---

## DEAD CODE QUANTIFICATION

| Category | Estimated Dead Lines | Files Affected |
|----------|---------------------|----------------|
| Dead modules (`KMap.lean`) | ~220 | 1 |
| Dead types/enums (Assumptions, MmioAdapter, etc.) | ~300 | 5 |
| Dead functions/definitions | ~400 | 15 |
| Trivial tautology theorems | ~150 | 10 |
| Superseded invariant bundle preservation theorems | ~500 | 3 |
| Duplicated proof blocks | ~3,500 | 8 |
| Dead documentation-only anchor theorems | ~200 | 10 |
| **Total estimated removable/refactorable** | **~5,300** | **~25** |

This represents approximately **8-9% of the Lean codebase** that could be removed or
consolidated without losing any proof coverage or functionality.

---

## PRIORITY RECOMMENDATIONS

### Before Benchmarking (Must Fix)

1. **Fix H-01**: Add `queuePPrev := none` to `frozenQueuePopHead` record update
2. **Fix M-01**: Add validation to `MessageInfo::encode()` or make fields private

### Before Release (Should Fix)

3. **Fix H-02**: Refactor API.lean dispatch duplication
4. **Fix M-04**: Integrate `serviceGraphInvariant` into `CrossSubsystem.lean`
5. **Fix M-05**: Add `cleanupEndpointServiceRegistrations_preserves_registryInterfaceValid`
6. **Fix M-08**: Replace `get!` with bounds-proven access in DeviceTree
7. **Remove M-02**: Delete `KMap.lean` (entirely dead)
8. **Fix M-06**: Migrate 3 remaining `native_decide` to `decide`

### Cleanup (Nice to Have)

9. Remove trivial tautology theorems (~15 theorems)
10. Remove superseded invariant bundles and their preservation theorems
11. Delete dead types in `Architecture/Assumptions.lean` and `RPi5/MmioAdapter.lean`
12. Extract duplicated `cspaceRevoke_preserves_cdtNodeSlot` into reusable lemma
13. Scope `linter.unusedVariables false` in `IPC/Invariant/Structural.lean`
14. Fix `CNodeRadix.toList` O(n^2) append pattern
15. Rename `serviceBfsFuel` to `serviceDfsFuel`

---

## SECURITY ASSESSMENT

No CVE-worthy vulnerabilities were identified. The kernel's security architecture
is sound:

- **Capability access control**: Bidirectional guard correctness proven, authority
  reduction on delete/revoke, badge-override safety
- **Information flow**: Complete NI proof chain from per-operation to trace composition
  with declassification support
- **Memory safety**: Scrubbing before retype prevents information leakage
- **IPC integrity**: Grant-right gating on cap transfer, bounded message payloads,
  intrusive queue acyclicity
- **Deterministic semantics**: All transitions return explicit success/failure with
  no non-deterministic branches

The Rust userspace ABI has minimal attack surface (2 justified unsafe blocks) and
maintains exact type parity with the Lean model.

---

*End of audit report.*
