# WS-S Closure Report — Pre-Benchmark Strengthening

**Workstream**: WS-S (Pre-Benchmark Strengthening)
**Version range**: v0.19.0–v0.19.6
**Created**: 2026-03-23
**Status**: PORTFOLIO COMPLETE

---

## 1. Executive Summary

WS-S addressed all actionable findings from two comprehensive v0.18.7 audits:
- `AUDIT_COMPREHENSIVE_v0.18.7_PRE_BENCHMARK.md` (50 findings)
- `AUDIT_COMPREHENSIVE_v0.18.7_KERNEL_RUST.md` (65+ findings)

**7 phases**, **83 sub-tasks** (including 1 stretch goal deferred to WS-T).
All 5 High, 29 Medium, and 19 Low findings resolved. Zero sorry/axiom across
the entire production proof surface.

---

## 2. Phase Summary

| Phase | Version | Scope | Sub-tasks | Status |
|-------|---------|-------|-----------|--------|
| S1 | v0.19.0 | Security Boundary & Rust Type Safety | 14 | COMPLETE |
| S2 | v0.19.1 | Test Hardening | 10 | COMPLETE |
| S3 | v0.19.2 | Proof Surface Closure | 14 (1 stretch) | COMPLETE |
| S4 | v0.19.3 | Model Fidelity & Type Safety | 13 | COMPLETE |
| S5 | v0.19.4 | API Cleanup & Platform Hardening | 10 | COMPLETE |
| S6 | v0.19.5 | Hardware Preparation | 7 | COMPLETE |
| S7 | v0.19.6 | Documentation & Polish | 14 | COMPLETE |
| **Total** | | | **82 + 1 stretch (83)** | |

---

## 3. Finding Resolution

### 3.1 High Findings (5/5 resolved)

| ID | Description | Resolution |
|----|-------------|------------|
| U-H1 | `Badge.ofNat` deprecated but callable | S1-A: Removed entirely |
| U-H2 | `MemoryRegion.wellFormed` is runtime Bool | S1-B: Converted to Prop |
| U-H3 | `ThreadId.toObjId` trust boundary undocumented | S1-C: Documented |
| U-H4 | `toString`-based test assertions | S2-A/B/C: Structural `==` |
| U-H5 | Golden-output fixture fragility | S2-D/E: Enhanced diff reporting |

### 3.2 Medium Findings (29/29 resolved)

| ID | Description | Phase |
|----|-------------|-------|
| U-M01 | `Cap::restrict()` panics | S1-D/E |
| U-M02 | `Restricted::RIGHTS = EMPTY` | S1-F |
| U-M03 | CDT maps consistency unproven | S3-A/B/C/D |
| U-M04 | `objectIndex` unbounded growth | S4-A |
| U-M05 | Deprecated wrappers in tests | S2-J |
| U-M05b | Deprecated wrappers in API | S5-A |
| U-M08 | `scheduleDomain` lacks full bundle | S3-E |
| U-M09 | `remove_preserves_wellFormed` missing | S3-F |
| U-M10 | Starvation-freedom liveness | S3-G (documented) |
| U-M11 | SecurityLabel lattice assumed | S3-H |
| U-M12 | `maxObjects` not enforced | S4-B |
| U-M13 | `machineWordBounded` GPR coverage | S1-N |
| U-M14 | `BEq RegisterFile` non-lawful | S1-J |
| U-M15 | No alignment fault modeling | S4-E |
| U-M16 | `KernelM` lacks instances | S1-K |
| U-M17 | `decodeCapPtr` unbounded | S4-K |
| U-M18 | Sim contracts all-True | S5-D |
| U-M19 | BCM2712 constants unvalidated | S5-F, S6-G |
| U-M20 | TLB invalidation not modeled | S6-A/B |
| U-M21 | Page alignment not enforced | S5-G/H |
| U-M22 | EDF tie-breaking undocumented | S5-I |
| U-M23 | Revocation complexity undocumented | S4-L |
| U-M23b | TlbState/RunQueue complexity | S5-J |
| U-M24 | Timeout semantics undocumented | S4-M |
| U-M25 | Service policy bridge witness | S3-I |
| U-M26 | Cross-subsystem parameterization | S3-J |
| U-M27 | Object iteration order | S4-J |
| U-M28 | Load factor bounds | S3-K |
| U-M29 | Frozen op exhaustiveness | S3-L |
| U-M30 | `native_decide` in `isPowerOfTwo` | S1-I |

### 3.3 Low Findings (19/30 resolved, 11 deferred)

| ID | Description | Phase | Status |
|----|-------------|-------|--------|
| U-L01 | RegisterFile Array migration | S4-F | Evaluated, rejected |
| U-L02 | CPtr masking | S4-C | Resolved |
| U-L03 | CDT removeEdge | S3-C | Resolved |
| U-L04 | IpcMessage registers typed | S4-D | Resolved |
| U-L05 | AccessRightSet.valid | S1-G | Resolved |
| U-L06 | Notification intrusive queue | S4-G | Evaluated, rejected |
| U-L07 | UntypedObject.allocate docs | S4-H | Resolved |
| U-L08 | SyscallId proof simplification | S4-I | Resolved |
| U-L09 | `deny(unsafe_code)` | S1-H | Resolved |
| U-L11 | StateBuilder bypasses Builder | S2-F | Resolved |
| U-L12 | Error-path test gaps | S2-G/H | Resolved |
| U-L13 | Shared test helpers | S2-I | Resolved |
| U-L14 | Semi-automated dep graph | S3-N | Resolved |
| + 6 more | Various | S1–S6 | Resolved |

### 3.4 Deferred Items

| ID | Description | Deferred To | Rationale |
|----|-------------|-------------|-----------|
| S3-M | NI trace indexing | WS-T | Deep proof refactoring; effort exceeds estimate |
| 11 Low findings | Various observational | Future | Low security impact, informational |

---

## 4. Codebase Metrics (v0.19.6)

| Metric | Before (v0.18.7) | After (v0.19.6) | Delta |
|--------|-------------------|-----------------|-------|
| Production files | ~98 | 100 | +2 |
| Production LoC | ~55,499 | 57,506 | +2,007 |
| Test files | 10 | 10 | 0 |
| Test LoC | ~7,309 | 7,559 | +250 |
| Proved declarations | ~1,686 | 1,756 | +70 |
| Sorry count | 0 | 0 | 0 |
| Axiom count | 0 | 0 | 0 |

---

## 5. Key Deliverables

### Security Hardening
- Removed deprecated `Badge.ofNat` (eliminated trust boundary)
- `MemoryRegion.wellFormed` is now a Prop proof obligation
- `Cap::restrict()` and `Cap::to_read_only()` return `Result` (no panics)
- `#![deny(unsafe_code)]` on `sele4n-abi`
- `AccessRightSet.valid` predicate enforcing 5-bit bounds

### Proof Surface
- `cdtMapsConsistent` invariant with 5 operation preservation theorems
- `scheduleDomain` full-bundle preservation
- `remove_preserves_wellFormed` for RunQueue
- SecurityLabel lattice antisymmetry with `Decidable` instance
- Parameterized `crossSubsystemInvariant`
- RobinHood load factor bounds and resize theorem
- Frozen ops exhaustiveness verification

### Model Fidelity
- Object capacity enforcement at `maxObjects` (65536)
- `IpcMessage.registers` typed as `Array RegValue`
- `resolveSlot` 64-bit CPtr masking
- `wordAligned`/`pageAligned` predicates
- `decodeCapPtr` bounds checking

### Hardware Preparation
- WithFlush VSpace variants in production API paths
- Memory scrubbing (`zeroMemoryRange`, `scrubObjectMemory`)
- `DeviceTree` platform abstraction
- BCM2712 address validation against datasheet
- SimRestrictive platform variant with substantive contracts

### Testing
- All `reprStr` replaced with structural `==` via `BEq Except`
- `buildChecked` with 8 runtime invariant checks
- 11 error-path tests added
- Shared `Testing/Helpers.lean` module
- Deprecated `api*` wrappers fully removed

---

## 6. Validation Results

- `test_full.sh`: All tiers (0-3) pass
- `test_nightly.sh`: All experimental checks pass
- Rust test suite: All tests pass
- Sorry/axiom scan: Zero instances
- Website link manifest: All protected paths verified

---

## 7. Next Steps

With WS-S complete, the project is ready for the next major milestone:
**Raspberry Pi 5 hardware binding** — ARMv8 page table walk, GIC-400 interrupt
routing, ARM Generic Timer binding, and verified boot sequence construction.

Deferred item S3-M (NI trace indexing) is tracked for WS-T.
