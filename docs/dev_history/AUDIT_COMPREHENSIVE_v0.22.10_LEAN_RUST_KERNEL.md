# Comprehensive Audit Report: seLe4n v0.22.10

**Date**: 2026-03-28
**Scope**: Full Lean kernel (102 modules, ~73K lines) + Rust ABI/sys layer (27 files, ~4.5K lines)
**Auditor**: Claude (Opus 4.6)
**Version**: 0.22.10
**Previous audit**: v0.21.7 (AUDIT_COMPREHENSIVE_v0.21.7_LEAN_RUST_KERNEL.md)

---

## Executive Summary

This pre-release audit covers every Lean module in the seLe4n kernel and
the complete Rust ABI implementation. The audit found **2 critical bugs**,
**1 high-severity ABI mismatch**, **1 high-severity missing error variant**,
and significant dead code bloat (~1,194 unused definitions across the
codebase). The Lean proof surface is clean — zero `sorry`, zero `axiom`,
zero `implemented_by` in kernel modules. The Rust crate architecture is
sound with proper `#![deny(unsafe_code)]` and a single justified `unsafe`
block.

### Severity Summary

| Severity | Count | Category |
|----------|-------|----------|
| CRITICAL | 2 | Rust ABI: wrong syscall IDs for notification ops |
| HIGH | 2 | Missing Rust error variant; notification badge ABI mismatch |
| MEDIUM | 5 | Dead code bloat, `native_decide` TCB, documentation drift |
| LOW | 8 | Minor naming, redundant theorems, test coverage gaps |
| INFO | 6 | Architecture observations, performance notes |

---

## Section 1: Critical Findings

### CRIT-01: `notification_signal()` uses wrong SyscallId (sele4n-sys)

**File**: `rust/sele4n-sys/src/ipc.rs:127-135`
**Severity**: CRITICAL
**Impact**: Notification signal dispatched as IPC endpoint Send

```rust
pub fn notification_signal(ntfn: CPtr) -> KernelResult<SyscallResponse> {
    let msg_info = MessageInfo::new_const(0, 0, 0);
    invoke_syscall(SyscallRequest {
        cap_addr: ntfn,
        msg_info,
        msg_regs: [0; 4],
        syscall_id: SyscallId::Send,  // BUG: should be SyscallId::NotificationSignal
    })
}
```

The function uses `SyscallId::Send` (value 0) instead of
`SyscallId::NotificationSignal` (value 14). This causes notification signal
operations to be dispatched as IPC endpoint sends on the kernel side,
resulting in incorrect behavior: the kernel will attempt to send an empty
IPC message to an endpoint instead of signaling a notification object.

**Additionally**: The function passes zero message registers, but the Lean
kernel's `decodeNotificationSignalArgs` expects `MR[0]` to contain the badge
value. Even with the correct syscall ID, the badge would be zero.

**Fix**: Change `SyscallId::Send` to `SyscallId::NotificationSignal` and
pass the badge in `msg_regs[0]`. However, note the documentation claims
"badge comes from the resolved capability" — this contradicts the Lean
model where badge comes from `MR[0]`. This semantic question needs
resolution (see HIGH-02).

### CRIT-02: `notification_wait()` uses wrong SyscallId (sele4n-sys)

**File**: `rust/sele4n-sys/src/ipc.rs:141-150`
**Severity**: CRITICAL
**Impact**: Notification wait dispatched as IPC endpoint Receive

```rust
pub fn notification_wait(ntfn: CPtr) -> KernelResult<Badge> {
    ...
    syscall_id: SyscallId::Receive,  // BUG: should be SyscallId::NotificationWait
    ...
}
```

Same class of bug as CRIT-01. Uses `SyscallId::Receive` (value 1) instead
of `SyscallId::NotificationWait` (value 15). The kernel will attempt an
IPC endpoint receive instead of a notification wait.

**Fix**: Change `SyscallId::Receive` to `SyscallId::NotificationWait`.

**Note**: The conformance tests in `sele4n-abi/tests/conformance.rs`
(RUST-XVAL-015, RUST-XVAL-016) correctly use the right syscall IDs,
but they test the low-level encode/decode layer, not the `sele4n-sys`
wrappers. The `sele4n-sys` crate has no tests for notification operations
that would have caught this.

---

## Section 2: High-Severity Findings

### HIGH-01: Missing `mmioUnaligned` error variant in Rust (sele4n-types)

**File**: `rust/sele4n-types/src/error.rs`
**Severity**: HIGH
**Impact**: Lean-Rust ABI desynchronization for error codes

The Lean `KernelError` inductive has **41 variants** (0-40), with
`mmioUnaligned = 40` added for V4-B/M-HW-1 MMIO alignment checks.
The Rust `KernelError` enum has only **40 variants** (0-39), missing
`mmioUnaligned`.

This means:
1. If the kernel returns error code 40, `KernelError::from_u32(40)`
   returns `None`, which `decode_response` maps to
   `InvalidSyscallNumber` — a misleading error.
2. The `from_u32` roundtrip tests pass because they only test 0-39.
3. The Lean `KernelError.toNat` for `mmioUnaligned` produces 40,
   which is unrepresentable in Rust.

**Fix**: Add `MmioUnaligned = 40` to the Rust enum and update
`from_u32` to handle value 40. Update tests to cover 0-40.

### HIGH-02: Notification badge source ABI mismatch (Lean vs Rust)

**File**: `rust/sele4n-sys/src/ipc.rs` vs `SeLe4n/Kernel/API.lean:543-551`
**Severity**: HIGH
**Impact**: Incorrect badge delivery for notification signal

The Lean kernel's `dispatchWithCap` for `.notificationSignal` calls
`decodeNotificationSignalArgs`, which reads the badge from `MR[0]`
(message register 0). The Rust `notification_signal()` wrapper:
1. Passes `msg_regs: [0; 4]` (all zeros) — badge always 0
2. Documents "badge comes from the resolved capability" — this is
   **incorrect** for the current Lean model

The Rust documentation references seL4 behavior where
`seL4_Signal(dest)` uses the capability's badge. But the Lean model
takes the badge from message registers, which is a deliberate design
choice for the seLe4n model.

**Resolution options**:
- A) Update Rust to pass badge in `msg_regs[0]` (match Lean model)
- B) Update Lean to use capability badge (match seL4/Rust docs)
- Either way, the Lean model and Rust ABI must agree.

---

## Section 3: Medium-Severity Findings

### MED-01: Massive dead code accumulation (~1,194 unused definitions)

**Scope**: Entire Lean codebase (SeLe4n/)
**Severity**: MEDIUM
**Impact**: Codebase bloat, maintenance burden, false sense of coverage

Automated analysis found **1,194 definitions** (def/theorem/lemma/abbrev)
that appear in only the file where they are defined and are never
referenced by any other file in `SeLe4n/`, `tests/`, or `Main.lean`.

**Top offenders by file** (unused definition count):

| File | Unused | Total est. | Notes |
|------|--------|-----------|-------|
| `IPC/Invariant/Structural.lean` | 91 | ~100 | Largest invariant file |
| `Capability/Invariant/Preservation.lean` | 59 | ~65 | |
| `Machine.lean` | 46 | ~94 | Many unused config helpers |
| `Model/Object/Structures.lean` | 44 | ~141 | CDT helpers never used |
| `Model/FreezeProofs.lean` | 40 | ~50 | Frozen state proofs |
| `Kernel/API.lean` | 39 | ~50 | Dispatch delegation thms |
| `Lifecycle/Operations.lean` | 39 | ~50 | |
| `InformationFlow/Policy.lean` | 36 | ~40 | |
| `Architecture/SyscallArgDecode.lean` | 33 | ~35 | |
| `Model/State.lean` | 32 | ~110 | State field helpers |
| `Platform/Boot.lean` | 30 | ~40 | Boot proofs |
| `Prelude.lean` | 29 | ~203 | RHTable theorems |
| `Scheduler/Ops/Preservation.lean` | 29 | ~35 | |

**Categories of dead code**:

1. **Orphaned theorems** (~600): Proofs that were written for future use
   or workstream deliverables but are never composed into any larger proof
   chain. Examples: `bootFromPlatform_*` family (30 theorems about boot
   state properties that no consumer references), `addEdge_*` family
   (CDT edge theorems), all TLB flush theorems in `TlbModel.lean`.

2. **Unused helper definitions** (~200): Functions like `addressInMap`,
   `arm64GPRCount`, `CSpaceOwner`, `SlotAddr`, `atPriority` that were
   defined for anticipated use but never called.

3. **Redundant re-export aliases** (~50): Abbreviations that duplicate
   existing names without adding value.

4. **Dead proof infrastructure** (~300): Intermediate lemmas for proofs
   that were later restructured, leaving the helper lemmas orphaned.

**Recommendation**: Perform a targeted dead-code elimination pass. For
theorems, distinguish between:
- Proofs that anchor invariant claims (keep even if unused — they serve
  as specification surface)
- Internal helper lemmas with no specification value (remove)
- Definitions that were superseded by later refactors (remove)

### MED-02: `native_decide` usage in kernel proofs (TCB concern)

**Files**: `Platform/Boot.lean` (3 uses), `Platform/RPi5/Board.lean` (3 uses)
**Severity**: MEDIUM
**Impact**: These proofs depend on native code execution, expanding the TCB

Six theorems use `native_decide` instead of `decide`:
- `bootFromPlatform_noDupThreadIds` (Boot.lean:169)
- `bootFromPlatform_noDupObjIds` (Boot.lean:174)
- `bootFromPlatform_noDupAsids` (Boot.lean:184)
- `mmioRegionDisjoint_holds` (Board.lean:171)
- `rpi5MachineConfig_wellFormed` (Board.lean:176)
- `rpi5DeviceTree_valid` (Board.lean:237)

All are documented with rationale (HashSet opacity for Boot, concrete
config values for RPi5). The Boot.lean uses are necessary because
`Std.HashSet` is opaque to the kernel checker. The RPi5 uses could
potentially be replaced with `decide` if the config structures derive
`DecidableEq` properly.

**Recommendation**: Investigate whether RPi5 board proofs can use `decide`
now that `DecidableEq` instances are more broadly derived. For Boot.lean,
the `native_decide` usage is justified and documented.

### MED-03: Missing `ReplyRecv` wrapper in sele4n-sys

**File**: `rust/sele4n-sys/src/ipc.rs`
**Severity**: MEDIUM
**Impact**: Users cannot invoke the ReplyRecv compound syscall from Rust

The Lean model has a `replyRecv` syscall (ID=16) fully implemented in
both checked and unchecked dispatch paths. The Rust `sele4n-types` crate
defines `SyscallId::ReplyRecv = 16` and the conformance tests verify its
encoding. However, `sele4n-sys/src/ipc.rs` provides no `endpoint_reply_recv()`
wrapper function.

The crate header claims "all 14 seLe4n syscalls" — but there are 17
syscalls in the current model (the original 14 + NotificationSignal,
NotificationWait, ReplyRecv added in V2-A/V2-C).

**Fix**: Add `endpoint_reply_recv()` wrapper and update crate documentation
to reflect 17 syscalls.

### MED-04: `dispatchWithCap` wildcard arm unreachability not proven

**File**: `SeLe4n/Kernel/API.lean:582`
**Severity**: MEDIUM
**Impact**: The `| _ => fun _ => .error .illegalState` arm at the end of
`dispatchWithCap` should be unreachable (all 17 SyscallId variants are
handled by `dispatchCapabilityOnly` or the explicit match arms), but
there is no theorem proving this arm is dead code.

A theorem of the form `∀ sid, dispatchCapabilityOnly ... = some _ ∨
sid ∈ explicitArms` would close this gap.

### MED-05: Documentation drift in Rust wrapper comments

**Files**: Multiple files in `rust/sele4n-sys/src/`
**Severity**: MEDIUM
**Impact**: Misleading documentation for developers

Several Rust doc comments reference removed Lean functions:
- `ipc.rs` comments reference `apiEndpointSend`, `apiEndpointReceive`,
  `apiEndpointCall`, `apiEndpointReply` — all removed in S5-A (v0.19.4)
- The actual Lean entry points are now `syscallEntry`/`dispatchSyscall`
- `lib.rs` header says "all 14 seLe4n syscalls" — should be 17

---

## Section 4: Low-Severity Findings

### LOW-01: Prelude contains 29 unused RHTable theorems

**File**: `SeLe4n/Prelude.lean` lines 916-1049
**Severity**: LOW

Theorems like `RHTable_contains_iff_get_some`, `RHTable_contains_insert_self`,
`RHTable_contains_erase_self`, `RHTable_filter_preserves_key`,
`RHTable_fold_preserves`, etc. are defined in Prelude but never used
anywhere in the codebase. These appear to be spec-surface theorems
characterizing RHTable behavior, which may have been intended for
composition but were superseded by the dedicated `RobinHood/Invariant/`
module.

**Recommendation**: Either integrate into the proof chain or remove.

### LOW-02: `DeviceTree.fromDtb` stub returns `none` with `implemented_by` comment

**File**: `SeLe4n/Platform/DeviceTree.lean:134-135`
**Severity**: LOW

```lean
def DeviceTree.fromDtb (_blob : ByteArray) : Option DeviceTree :=
  none  -- V4-M4: Overridden by fromDtbFull via @[implemented_by] below
```

The comment says it's overridden by `@[implemented_by]`, but no
`@[implemented_by]` attribute is actually present in the file. This is
either a stale comment or the attribute was removed. The function
unconditionally returns `none`.

### LOW-03: `addServiceGraph` in Builder.lean is dead code

**File**: `SeLe4n/Model/Builder.lean:122`
**Severity**: LOW

`addServiceGraph` is defined but never called anywhere in the codebase.

### LOW-04: CDT edge theorems in Structures.lean are comprehensive but unused

**File**: `SeLe4n/Model/Object/Structures.lean` (~44 unused definitions)
**Severity**: LOW

The `addEdge_*`, `addEdgeWouldBeSafe`, `addEdge_childMapConsistent`,
`addEdge_parentMapConsistent`, `addEdge_preserves_cdtMapsConsistent`,
`addEdge_preserves_edgeWellFounded_fresh`,
`addEdge_preserves_edgeWellFounded_noParent` theorems form a complete
proof suite for CDT edge operations but are never composed into any
larger proof chain.

### LOW-05: `IpcMessage.push()` trusts `length` field (Rust)

**File**: `rust/sele4n-sys/src/ipc.rs:43-50`
**Severity**: LOW

The `push()` method uses `self.length as usize` as an array index.
Since `length` is a `u8` and the array is `[u64; 4]`, the bounds check
`if self.length >= 4` is correct. However, `length` is a public field
(`pub length: u8`) and could be set to any value externally. If a user
sets `length = 255` and then calls `push()`, the bounds check prevents
the write, but a subsequent `endpoint_send()` would encode
`MessageInfo::new(255, 0, label)` which returns `InvalidMessageInfo`
(length > 120). This is safe but the error path is indirect.

### LOW-06: `DeclassificationAuditLog` type alias is unused

**File**: `SeLe4n/Kernel/InformationFlow/Policy.lean:638`
**Severity**: LOW

```lean
abbrev DeclassificationAuditLog := List DeclassificationEvent
```

Defined but never referenced anywhere.

### LOW-07: `RegisterWriteInvariant` is unused

**File**: `SeLe4n/Platform/RPi5/RuntimeContract.lean:178`
**Severity**: LOW

Defined but never referenced outside its definition file.

### LOW-08: `ServicePolicyPredicate` type alias is unused

**File**: `SeLe4n/Kernel/Service/Invariant/Policy.lean:30`
**Severity**: LOW

```lean
abbrev ServicePolicyPredicate := SystemState → ServiceGraphEntry → Prop
```

Defined but never used.

---

## Section 5: Informational Findings

### INFO-01: Zero `sorry` / zero `axiom` — proof surface is clean

**Scope**: All 102 Lean modules in `SeLe4n/`
**Finding**: No `sorry` or `axiom` found anywhere in the production
proof surface. The only references to `sorry` are in test comments
explaining what would happen if `sorry` were present. This is excellent
for a pre-release kernel.

### INFO-02: Single `unsafe` block in Rust — well justified

**File**: `rust/sele4n-abi/src/trap.rs:31-53`
**Finding**: The entire Rust codebase has exactly one `unsafe` block:
the `raw_syscall` function containing the ARM64 `svc #0` instruction.
It is properly documented, uses `clobber_abi("C")` for register safety,
and has a mock implementation for non-AArch64 targets. The crate-level
`#![deny(unsafe_code)]` ensures no other unsafe code can be introduced.

### INFO-03: Syscall ID encoding matches between Lean and Rust

**Files**: `SeLe4n/Model/Object/Types.lean:831-876` vs
`rust/sele4n-types/src/syscall.rs:12-37`
**Finding**: All 17 syscall IDs have identical numeric encoding:
Send=0, Receive=1, ..., ReplyRecv=16. The `required_right` mapping
also matches exactly between `syscallRequiredRight` (Lean) and
`SyscallId::required_right` (Rust).

### INFO-04: Access rights encoding matches between Lean and Rust

**Files**: `SeLe4n/Model/Object/Types.lean` vs
`rust/sele4n-types/src/rights.rs`
**Finding**: All 5 access rights (Read=0, Write=1, Grant=2,
GrantReply=3, Retype=4) match in bit position. The Rust `AccessRights`
bitmask operations (union, intersection, subset) match the Lean
`AccessRightSet` operations semantically.

### INFO-05: MessageInfo bitfield encoding matches

**Files**: `SeLe4n/Model/Object/Types.lean` vs
`rust/sele4n-abi/src/message_info.rs`
**Finding**: Bit layout is identical:
- bits 0-6: length (7 bits, max 120)
- bits 7-8: extraCaps (2 bits, max 3)
- bits 9-28: label (20 bits)
Both enforce V2-H 20-bit label limit.

### INFO-06: Typed identifiers use `#[repr(transparent)]` correctly

**File**: `rust/sele4n-types/src/identifiers.rs`
**Finding**: All 14 identifier newtypes use `#[repr(transparent)]`
over `u64`, ensuring zero-cost ABI compatibility. The `From<u64>`
and `Into<u64>` conversions are provided for all types.

---

## Section 6: Lean Module-by-Module Audit Summary

### 6.1 Prelude.lean (~1049 lines)

- **29 unused definitions** (mostly RHTable theorems)
- Clean typed identifier definitions (ThreadId, ObjId, CPtr, etc.)
- `KernelM` monad and `bind_assoc_law`/`bind_pure_law` are proven but
  unused — these are spec-surface theorems
- `Badge.bor` correctly uses bitwise OR with 64-bit masking
- No issues with the core identifier infrastructure

### 6.2 Machine.lean (~530+ lines)

- **46 unused definitions** including `arm64GPRCount`, `addressInMap`,
  `allGPRIndicesValid`, many config validation helpers
- `MemoryRegion.wellFormed` has proper `Decidable` instance
- Successfully migrated from `native_decide` to `decide` (S1-I)
- `MachineConfig` structure is comprehensive for RPi5 target
- `RegisterFile` correctly models ARM64 32-register file

### 6.3 Model/Object/Types.lean

- Core data types (TCB, Endpoint, Notification, etc.) are well-structured
- `UntypedObject` has proper well-formedness conditions with proofs
- **26 unused theorems** in the UntypedObject section
- `MessageInfo` encode/decode matches Rust implementation
- `SyscallId` enum matches Rust 1:1

### 6.4 Model/Object/Structures.lean (~833 lines)

- **44 unused definitions** — primarily CDT edge theorems
- `CapDerivationTree` structure is well-designed with parent/child maps
- `CNode` guard/radix resolution is correct
- `SlotAddr` abbreviation is dead code

### 6.5 Model/State.lean (~1073 lines)

- **32 unused definitions** including `CSpaceOwner`, `allTablesInvExtK_witness`
- `KernelError` has 41 variants (Rust only has 40 — see HIGH-01)
- `SystemState` structure is comprehensive with all subsystem fields
- `storeObject` correctly validates `invExt` invariant

### 6.6 Kernel/API.lean (~1462 lines)

- **39 unused definitions** — mostly dispatch delegation theorems
- `syscallLookupCap` correctly validates capability rights before dispatch
- `dispatchWithCap` and `dispatchWithCapChecked` share
  `dispatchCapabilityOnly` correctly
- 6 structural equivalence theorems (checked=unchecked for cap-only arms)
  are proven and correct
- `resolveExtraCaps` silently drops unresolvable caps (seL4 behavior)
- The `| _ => fun _ => .error .illegalState` wildcard in both dispatch
  functions should be provably unreachable

### 6.7 Scheduler Subsystem

- `RunQueue` O(1) operations are correct
- EDF scheduling predicates are properly defined
- **29 unused theorems** in Preservation.lean
- **12 unused definitions** in RunQueue.lean (including `atPriority`)
- Domain scheduling (`scheduleDomain`, `switchDomain`) properly modeled
- `domainTimeRemainingPositive` invariant (8th conjunct) has full
  preservation proofs

### 6.8 IPC Subsystem

- **91 unused definitions** in Structural.lean alone
- `endpointSendDual` / `endpointReceiveDual` correctly implement
  dual-queue IPC semantics
- `notificationSignal` has proper badge accumulation with `Badge.bor`
- Queue no-dup invariants (`QueueNoDup.lean`) are well-proven
- The `_fromTcb` variants correctly optimize TCB lookups
- `endpointReplyRecv` correctly composes reply + receive

### 6.9 Capability Subsystem

- `resolveCapAddress` is correctly recursive with termination proof
- Guard check theorems (`guard_reject`, `guard_match`) provide
  bidirectional characterization
- **59 unused theorems** in Preservation.lean
- Rights attenuation (`capAttenuates`) is sound
- Multi-level CSpace walk handles all error cases

### 6.10 Information Flow Subsystem

- `lowEquivalent` and `projectState` correctly define NI
- Enforcement wrappers gate all cross-domain operations
- **25 unused theorems** in Operations.lean
- `DeclassificationEvent` has proper `authorizationBasis` audit trail
- `kernelOperationNiConstructor` covers all 32 operation variants
- `acceptedCovertChannel_scheduling` is documented but unused

### 6.11 RobinHood + RadixTree

- Robin Hood hash table is fully verified (WF, distCorrect, noDupKeys)
- `CNodeRadix` O(1) lookup/insert/erase is correct
- **11 unused theorems** in RH Preservation.lean
- **12 unused definitions** in RadixTree Bridge.lean
- `LawfulBEq` requirement properly propagated (V7 18-file ripple)

### 6.12 Lifecycle + Service + FrozenOps

- `lifecycleRetypeDirectWithCleanup` properly handles cleanup + scrubbing
- Service registry acyclicity proofs are comprehensive
- FrozenOps commutativity proofs are correct
- **18 unused definitions** in CrossSubsystem.lean

### 6.13 Architecture Subsystem

- `RegisterDecode` is total and deterministic
- `SyscallArgDecode` covers all 17 syscall argument types
- TLB model has proper flush theorems (all unused externally)
- VSpace map/unmap with TLB flush is correct
- **18 unused theorems** in VSpaceInvariant.lean

### 6.14 Platform + Boot

- Boot sequence correctly constructs `IntermediateState`
- RPi5 board config has proper well-formedness proofs
- MMIO adapter has alignment checks (source of `mmioUnaligned` error)
- **30 unused boot proofs** — specification surface theorems
- **26 unused definitions** in MmioAdapter.lean

---

## Section 7: Rust Crate Audit Summary

### 7.1 sele4n-types (5 files, ~700 lines)

- **Clean**: All types match Lean model
- **Issue**: Missing `MmioUnaligned` error variant (HIGH-01)
- Good: `#[non_exhaustive]` on `KernelError` for future compatibility
- Good: `#[repr(transparent)]` on all identifier types
- Good: `TryFrom<u8>` for `AccessRights` prevents invalid bitmasks

### 7.2 sele4n-abi (12 files, ~2200 lines)

- **Clean**: Single `unsafe` block is well-justified (INFO-02)
- **Clean**: Encode/decode roundtrip tests are comprehensive
- Good: `MessageInfo` fields are private with validated constructors
- Good: `clobber_abi("C")` prevents register corruption
- Good: `decode_response` guards against u64 truncation (V1-A)
- Conformance tests properly test all 17 syscall encodings

### 7.3 sele4n-sys (7 files, ~530 lines)

- **CRITICAL**: Wrong syscall IDs for notifications (CRIT-01, CRIT-02)
- **MEDIUM**: Missing `ReplyRecv` wrapper (MED-03)
- Good: `Cap<Obj, Rts>` phantom typing is sound
- Good: W^X enforcement in `vspace_map`
- Good: Sealed trait pattern prevents external CapObject impls
- Issue: No integration tests for notification wrappers

---

## Section 8: Recommendations

### 8.1 Immediate (Pre-Release Blockers)

1. **Fix CRIT-01/CRIT-02**: Update `notification_signal()` and
   `notification_wait()` to use correct `SyscallId` values.
2. **Resolve HIGH-02**: Decide whether badge source is MR[0] (Lean model)
   or capability badge (seL4 convention), and align both implementations.
3. **Fix HIGH-01**: Add `MmioUnaligned = 40` to Rust `KernelError`.

### 8.2 Short-Term (Before Benchmarking)

4. **Add `endpoint_reply_recv()`** wrapper to `sele4n-sys` (MED-03).
5. **Update Rust documentation** to reference current Lean API names and
   correct syscall count (MED-05).
6. **Add integration tests** for all notification/replyRecv wrappers in
   `sele4n-sys`.

### 8.3 Medium-Term (Code Health)

7. **Dead code elimination pass**: Remove the ~1,194 unused definitions.
   Prioritize:
   - Helper lemmas with no specification value (~300 candidates)
   - Superseded definitions from refactored workstreams (~200)
   - Keep specification-surface theorems even if unused
8. **Investigate `native_decide` elimination** for RPi5 board proofs.

### 8.4 Verification Recommendations

9. **Prove wildcard arm unreachability** in `dispatchWithCap` (MED-04).
10. **Add cross-crate ABI conformance test** that auto-detects Lean-Rust
    enum divergence (would have caught HIGH-01 and CRIT-01/02).

---

## Section 9: Positive Observations

The seLe4n kernel demonstrates exceptional engineering quality in several
areas:

1. **Zero sorry/axiom**: The entire Lean proof surface is machine-checked
   with no escape hatches.
2. **Single unsafe block**: The Rust crate architecture confines all
   unsafe code to a single, well-documented `svc #0` instruction.
3. **Comprehensive invariant bundles**: The `proofLayerInvariantBundle`
   composes all subsystem invariants into a single verifiable predicate.
4. **Defense-in-depth**: The checked dispatch path gates every cross-domain
   operation through information-flow wrappers, even for operations like
   reply where it's arguably redundant.
5. **Deterministic semantics**: All kernel transitions return explicit
   success/failure with no non-deterministic branches.
6. **Sound capability architecture**: Multi-level CSpace resolution with
   guard correctness proofs, rights attenuation, and capability-gated
   dispatch.
7. **Robust ABI design**: Private fields with validated constructors
   (`MessageInfo`), `TryFrom` instead of `From` for fallible conversions,
   `#[non_exhaustive]` for future compatibility.

---

*End of audit report.*
*Audit session: https://claude.ai/code/session_01XBHosRPEVoGnVnxpgzmrS8*
