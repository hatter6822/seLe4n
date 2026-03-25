# WS-V Workstream Plan — Pre-Release Audit Remediation (v0.21.7)

**Created**: 2026-03-25
**Baseline version**: 0.21.7
**Baseline audits**:
- `docs/audits/AUDIT_COMPREHENSIVE_v0.21.7_PRE_BENCHMARK.md` (4 HIGH, 29 MEDIUM, 41 LOW)
- `docs/audits/AUDIT_COMPREHENSIVE_v0.21.7_LEAN_RUST_KERNEL.md` (1 HIGH, 39 MEDIUM, 28 LOW)
- `docs/audits/AUDIT_COMPREHENSIVE_v0.21.7_KERNEL_IMPLEMENTATION.md` (0 HIGH, 20 MEDIUM, 55 LOW)
**Prior portfolios**: WS-B through WS-U (all COMPLETE — see `docs/WORKSTREAM_HISTORY.md`)
**Constraint**: Zero `sorry`/`axiom` in production proof surface

---

## 1. Executive Summary

Three comprehensive audits of seLe4n v0.21.7 were conducted on 2026-03-25: a
full pre-benchmark audit (9 parallel agents, 119 findings), a Lean+Rust kernel
audit (9 parallel agents, 68 findings), and a kernel implementation audit (10
parallel agents, 75 findings). Independent cross-validation confirmed all
findings; one finding (L-02/AccessRightSet spurious bits) was determined to be
mitigated by existing safe constructors and is excluded from remediation.

**No Critical vulnerabilities were found.** The codebase has zero `sorry`, zero
`axiom`, zero `unsafeCast`, and a single justified `unsafe` Rust block (ARM64
`svc #0`). All prior TPI-D tracked proof items remain CLOSED.

The **5 HIGH findings** (deduplicated) concentrate in four areas:
1. **Rust ABI safety** — u64→u32 truncation in error decode creates false-success
   risk (H-RS-1)
2. **Boot invariant bridge** — Only proven for empty config; non-empty boot
   configs lack end-to-end invariant proof (H-BOOT-1)
3. **Service availability** — BFS fuel exhaustion returns `true`, rejecting
   valid service registrations (H-SVC-1)
4. **Data structure proof ergonomics** — Robin Hood erase requires redundant
   hypothesis (H-RH-1); radix tree non-interference requires radix-index
   inequality (H-RAD-1)

The **61 deduplicated MEDIUM findings** cluster around eight themes:
1. **API surface gaps** — Missing notification/replyRecv syscalls, MessageInfo
   label unbounded
2. **Proof chain gaps** — CDT acyclicity externalized, ipcUnwrapCaps Grant loop
   missing, cross-subsystem informal composition
3. **Platform/hardware fidelity** — MMIO alignment, write-one-clear semantics,
   RPi5 4GB hardcoding, VSpace variant visibility
4. **Defensive coding** — Panicking `get!`, public bypass functions, silent drops
5. **Information flow** — Covert channels documented, NI coverage proof vs
   operational correspondence, endpoint policy widening
6. **Rust hardening** — TypeTag validation, unwrap() in no_std, error variant
   naming
7. **Data structure fragility** — High maxHeartbeats, LawfulBEq implicit
8. **Test gaps** — Missing end-to-end checked pipeline, cspaceMove, inter-state
   validation

This workstream plan organizes all actionable findings into **8 phases** (V1–V8)
with **94 atomic sub-tasks**, explicit dependencies, gate conditions, and scope
estimates. The plan addresses all 5 HIGH findings, all 61 MEDIUM findings, and
selects 29 LOW findings for inclusion based on security relevance, proof chain
completeness, and hardware readiness. The remaining LOW/Info findings are
documented as accepted design decisions or deferred to post-release hardening.

---

## 2. Deduplication Methodology

Findings were cross-referenced across all three audits by: (1) matching file
paths and line numbers, (2) matching semantic descriptions, (3) matching
recommended remediations. Where two or more audits report the same underlying
issue, a single canonical ID is assigned. The source audits contributing to
each canonical finding are listed in the registry below.

**Deduplication results:**
- Raw findings: 119 + 68 + 75 = 262
- After deduplication: 5 HIGH, 61 MEDIUM, 29 actionable LOW = **95 unique findings**
- Excluded (mitigated): 1 (L-02/AccessRightSet — safe constructors enforce 5-bit boundary)
- Accepted (no remediation): 42 LOW/Info findings (design decisions, seL4-consistent)

**Verification:** Each finding was verified against source code by reading the
referenced file and line numbers. All 95 actionable findings were confirmed
genuine. The single exclusion (L-02) was verified: `AccessRightSet.ofNat` masks
to 5 bits, `mk_checked` requires proof, and `ofNat_valid` theorem guarantees
safety. The raw `.mk` constructor is a Lean structure default, not a public API.

---

## 3. Consolidated Finding Registry

### 3.1 HIGH Findings (5)

| ID | Audit Sources | Subsystem | Description | Phase |
|----|---------------|-----------|-------------|-------|
| H-RS-1 | LEAN_RUST H-01, PRE L-35 | Rust ABI | `decode_response` truncates u64→u32; value `0x1_0000_0000` yields false success | V1 |
| H-BOOT-1 | PRE H-02, LEAN_RUST M-PLAT-02, IMPL L-arch-7 | Boot/Platform | Boot-to-runtime invariant bridge only proven for empty `PlatformConfig` | V4 |
| H-SVC-1 | PRE H-01 | Service | `serviceHasPathTo` returns `true` on fuel exhaustion, rejecting valid registrations | V5 |
| H-RH-1 | PRE H-03 | RobinHood | `erase_preserves_invExt` requires separate `hSize` hypothesis not in `invExt` | V3 |
| H-RAD-1 | PRE H-04 | RadixTree | `lookup_insert_ne` requires radix-index inequality, not key inequality | V3 |

### 3.2 MEDIUM Findings — API Surface (5)

| ID | Audit Sources | Description | Phase |
|----|---------------|-------------|-------|
| M-API-1 | PRE M-28, IMPL M-07 | `notificationSignal`/`notificationWait` absent from `SyscallId` and dispatch | V2 |
| M-API-2 | IMPL M-06 | `replyRecv` not in `SyscallId` — seL4's primary compound syscall missing | V2 |
| M-API-3 | IMPL M-08 | `MessageInfo.decode` label field unbounded (55 bits vs seL4 20-bit limit) | V2 |
| M-API-4 | LEAN_RUST M-API-02 | Code duplication between checked and unchecked dispatch paths | V8 |
| M-API-5 | PRE L-40, LEAN_RUST M-API-01 | `dispatchWithCap` hardcodes `Slot.ofNat 0` for IPC cap transfer | V2 |

### 3.3 MEDIUM Findings — Proof Chain (6)

| ID | Audit Sources | Description | Phase |
|----|---------------|-------------|-------|
| M-PRF-1 | PRE M-05, IMPL L-cap-2 | CDT acyclicity externalized as hypothesis, not proven from pre-state | V3 |
| M-PRF-2 | IMPL M-02 | `ipcUnwrapCaps` Grant=true loop composition proof missing | V3 |
| M-PRF-3 | PRE M-04 | Missing composition-level theorem for post-resolution rights checks | V3 |
| M-PRF-4 | LEAN_RUST M-CROSS-01, IMPL M-03 | Cross-subsystem invariant relies on informal field-disjointness | V6 |
| M-PRF-5 | IMPL M-01 | No formal `pendingMessage = none` invariant for waiting threads | V3 |
| M-PRF-6 | IMPL M-04 | `serviceCountBounded` preservation across non-service operations unverified | V6 |

### 3.4 MEDIUM Findings — Platform & Hardware (9)

| ID | Audit Sources | Description | Phase |
|----|---------------|-------------|-------|
| M-HW-1 | PRE M-25, LEAN_RUST M-PLAT-05 | MMIO read/write lacks alignment enforcement | V4 |
| M-HW-2 | LEAN_RUST M-PLAT-04 | MMIO write-one-clear modeled as direct store (GIC unsound) | V4 |
| M-HW-3 | LEAN_RUST M-PLAT-03 | RPi5 memory map hardcoded for 4GB model only | V4 |
| M-HW-4 | LEAN_RUST M-ARCH-02 | Non-flush VSpace map/unmap variants are public | V4 |
| M-HW-5 | LEAN_RUST M-ARCH-01 | VSpace permission bits not cross-checked against MemoryKind at decode | V4 |
| M-HW-6 | PRE M-24 | Simulation boot/interrupt contracts trivially `True` | V4 |
| M-HW-7 | PRE M-11 | Missing `domainTimeRemaining > 0` initialization invariant | V5 |
| M-HW-8 | LEAN_RUST M-PLAT-01 | Truncated DTB `reg` entries silently ignored | V4 |
| M-HW-9 | IMPL M-14 | RPi5 `registerContextStableCheck` ignores pre-state parameter | V4 |

### 3.5 MEDIUM Findings — Defensive Coding (8)

| ID | Audit Sources | Description | Phase |
|----|---------------|-------------|-------|
| M-DEF-1 | IMPL M-10 | `readBE32` uses panicking `blob.get!` inside bounds guard | V5 |
| M-DEF-2 | IMPL M-09 | `lifecycleRetypeObject`/`lifecycleRetypeDirect` public, bypass cleanup | V5 |
| M-DEF-3 | IMPL M-11 | `bootFromPlatform` silently drops duplicate IRQs/objects (last-wins) | V5 |
| M-DEF-4 | PRE M-07 | `saveOutgoingContext` silently drops save on TCB lookup failure | V5 |
| M-DEF-5 | PRE M-08 | `restoreIncomingContext` silently skips restore on failure | V5 |
| M-DEF-6 | PRE M-10 | `handleYield` with `current = none` falls through to schedule | V5 |
| M-DEF-7 | PRE M-06 | Single-CNode vs cross-CNode revocation routing confusion risk | V5 |
| M-DEF-8 | IMPL M-13 | Internal `vspaceMapPage` defaults permissions to `readOnly` | V4 |

### 3.6 MEDIUM Findings — Information Flow (7)

| ID | Audit Sources | Description | Phase |
|----|---------------|-------------|-------|
| M-IF-1 | PRE M-15, IMPL M-15 | Non-standard integrity flow direction (reversed BIBA) | V6 |
| M-IF-2 | PRE M-16, IMPL M-16 | NI proofs conditioned on domain-separation hypotheses | V6 |
| M-IF-3 | PRE M-17 | Service layer not covered by NI projection model | V6 |
| M-IF-4 | PRE M-18 | Enforcement boundary lists are data, not type-enforced | V6 |
| M-IF-5 | PRE M-19 | Per-endpoint flow policy can widen global policy | V6 |
| M-IF-6 | LEAN_RUST M-IF-01 | Declassification policy lacks runtime audit logging | V6 |
| M-IF-7 | LEAN_RUST M-IF-02 | `niStepCoverage` uses `syscallDecodeError` as universal witness | V6 |

### 3.7 MEDIUM Findings — Rust Hardening (7)

| ID | Audit Sources | Description | Phase |
|----|---------------|-------------|-------|
| M-RS-1 | PRE M-26, LEAN_RUST M-RS-05 | `LifecycleRetypeArgs.new_type` raw u64 bypasses TypeTag validation | V1 |
| M-RS-2 | PRE M-27 | 13 `unwrap()` calls on `MessageInfo::new()` in no_std context | V1 |
| M-RS-3 | LEAN_RUST M-RS-03 | `IpcBuffer.get_mr()` returns `InvalidMessageInfo` for inline indices | V1 |
| M-RS-4 | LEAN_RUST M-RS-04 | `InvalidMessageInfo` used for invalid rights in CSpace args | V1 |
| M-RS-5 | LEAN_RUST M-RS-06 | `BitOr` on `PagePerms` not W^X validated at combine time | V1 |
| M-RS-6 | PRE M-01, LEAN_RUST M-FND-01 | `native_decide` in RegisterFile negative witness (TCB concern) | V7 |
| M-RS-7 | LEAN_RUST M-RS-01 | Several identifier types lack sentinel/validation concepts | V1 |

### 3.8 MEDIUM Findings — Data Structure & Performance (5)

| ID | Audit Sources | Description | Phase |
|----|---------------|-------------|-------|
| M-DS-1 | PRE M-22, LEAN_RUST M-DS-01 | `maxHeartbeats 3200000` in RobinHood Bridge.lean (16x default) | V7 |
| M-DS-2 | LEAN_RUST M-DS-02 | `maxHeartbeats 800000` in RobinHood Preservation.lean (2x default) | V7 |
| M-DS-3 | IMPL M-18 | `LawfulBEq` requirement essential but implicit in RobinHood API | V7 |
| M-DS-4 | PRE M-20 | `buildCNodeRadix_lookup_equiv` requires `hNoPhantom` precondition | V3 |
| M-DS-5 | PRE M-21 | General `filter_preserves_key` not proved (specific instances only) | V7 |

### 3.9 MEDIUM Findings — Test Coverage (9)

| ID | Audit Sources | Description | Phase |
|----|---------------|-------------|-------|
| M-TST-1 | LEAN_RUST M-TEST-01 | No end-to-end test of `syscallEntryChecked` pipeline | V8 |
| M-TST-2 | LEAN_RUST M-TEST-04 | No test coverage for `cspaceMove` end-to-end | V8 |
| M-TST-3 | LEAN_RUST M-TEST-03 | Inter-transition checks validate original state, not mutated | V8 |
| M-TST-4 | LEAN_RUST M-TEST-05 | `buildValidated` Check 8 conflicts with dequeue-on-dispatch | V8 |
| M-TST-5 | LEAN_RUST M-TEST-02 | `intrusiveQueueReachable` is `partial` (termination unchecked) | V8 |
| M-TST-6 | PRE M-29 | Test harness fixture drift risk (2144-line harness) | V8 |
| M-TST-7 | PRE L-39 | Missing Rust conformance tests for edge cases | V8 |
| M-TST-8 | PRE M-03 | Non-lawful `BEq RegisterFile` — false positives in tests | V7 |
| M-TST-9 | IMPL M-19 | Thread state machine implicit; states inferred from queue membership | V8 |

### 3.10 Actionable LOW Findings (29)

| ID | Audit Sources | Description | Phase |
|----|---------------|-------------|-------|
| L-RS-1 | PRE L-36, IMPL M-20 | Stale comment: error codes "0-37" should be "0-39" | V1 |
| L-RS-2 | PRE L-37 | `ServiceRegisterArgs` missing `method_count`/`max_message_size` bounds | V1 |
| L-RS-3 | PRE L-38 | `IpcBuffer::get_mr` semantically imprecise error variant | V1 |
| L-FND-1 | PRE L-01 | `ThreadId.toObjId` unchecked identity mapping | V5 |
| L-FND-2 | PRE L-05 | `PagePermissions.ofNat` accepts W^X-violating inputs | V4 |
| L-FND-3 | PRE L-03 | `storeObject` infallible — no capacity check at store time | V5 |
| L-FND-4 | PRE M-02 | Unbounded `Nat` identifiers model-hardware gap | V4 |
| L-SCH-1 | PRE L-13 | `defaultTimeSlice` hardcoded to 5, not configurable | V5 |
| L-SCH-2 | PRE L-15 | `timerTick` re-enqueue uses pre-reset TCB priority | V5 |
| L-IPC-1 | PRE L-16 | Notification pendingMessage overwrite lacks "was none" lemma | V3 |
| L-IPC-2 | PRE L-19 | Cap transfer slot base hardcoded to `Slot.ofNat 0` | V2 |
| L-IPC-3 | PRE L-20 | `ipcStateQueueConsistent` weak form (existence, not membership) | V3 |
| L-IPC-4 | PRE L-22 | Timing side-channel through queue length not modeled | V6 |
| L-CAP-1 | PRE L-09 | `processRevokeNode` double-detaches CDT slot (idempotent) | V5 |
| L-CAP-2 | PRE L-10 | `cspaceRevokeCdtStrict` removes CDT node on delete failure | V5 |
| L-DS-1 | PRE L-27 | RadixTree `toList` uses O(n²) append pattern | V7 |
| L-DS-2 | PRE L-28 | Robin Hood `erase` size decrement relies on WF invariant | V7 |
| L-DS-3 | PRE L-29 | Frozen queue operations don't verify membership before dequeue | V5 |
| L-DS-4 | PRE L-31 | `frozenCspaceMint` inserts without occupied-slot check | V5 |
| L-PLAT-1 | PRE L-32 | DTB parsing stub `fromDtb` always returns `none` | V4 |
| L-PLAT-2 | PRE L-33 | Boot `irqKeysNoDup`/`objIdKeysNoDup` use O(n²) detection | V7 |
| L-PLAT-3 | PRE L-34 | `extractMemoryRegions` assumes 64-bit address cells only | V4 |
| L-IF-1 | PRE L-23 | Scheduling state visible to all observers (covert channel) | V6 |
| L-IF-2 | PRE L-25 | `defaultLabelingContext` assigns public label to everything | V6 |
| L-IF-3 | IMPL L-if-5 | `enforcementBoundaryExtended` stale (18 vs 20 entries) | V6 |
| L-TST-1 | PRE L-41 | `resolveExtraCaps` silently drops unresolvable caps | V8 |
| L-SCH-3 | PRE L-14 | `RunQueue.wellFormed` external predicate, not structural | V7 |
| L-LIFE-1 | LEAN_RUST M-LIFE-01 | No uniqueness-within-queue invariant for endpoint TCBs | V3 |
| L-FRZ-1 | PRE L-30 | `frozenSchedule` dequeue-on-dispatch doesn't re-enqueue preempted | V5 |

---

## 4. Phase Definitions

### Phase V1: Rust ABI Hardening & Immediate Fixes (12 sub-tasks)

**Priority**: Immediate (pre-benchmark blocker)
**Gate**: `cargo test --all` passes; `lake build` succeeds; `test_smoke.sh` green
**Estimated scope**: ~200 lines Rust, ~20 lines Lean

These are low-risk, high-value fixes that harden the Rust ABI boundary and
correct documentation drift. All changes are confined to the Rust crates and
do not affect Lean proof surface.

| ID | Finding | Task | Files | Scope |
|----|---------|------|-------|-------|
| V1-A | H-RS-1 | Add u64 range guard before `as u32` cast in `decode_response`. Return `Err(InvalidSyscallNumber)` if `regs[0] > u32::MAX as u64`. | `rust/sele4n-abi/src/decode.rs` | S |
| V1-B | L-RS-1 | Fix stale comment: change "0–37" to "0–39" in decode.rs line 33 | `rust/sele4n-abi/src/decode.rs` | XS |
| V1-C | M-RS-1 | Change `LifecycleRetypeArgs.new_type` from raw `u64` to `TypeTag`. Add `TypeTag::from_u64()` validation in `decode()`. | `rust/sele4n-abi/src/args/lifecycle.rs`, `args/type_tag.rs` | S |
| V1-D | M-RS-2 | Replace 13 `unwrap()` calls on `MessageInfo::new()` with pre-computed `const` values or infallible helper `MessageInfo::new_unchecked()` for compile-time-constant args. | `rust/sele4n-sys/src/*.rs` | M |
| V1-E | M-RS-3 | Rename error variant: `IpcBuffer.get_mr()` should return `InvalidArgument` (not `InvalidMessageInfo`) for out-of-range inline register indices. | `rust/sele4n-abi/src/ipc_buffer.rs` | S |
| V1-F | M-RS-4 | Fix `CSpaceMintArgs` decode: return `InvalidArgument` instead of `InvalidMessageInfo` for invalid rights. | `rust/sele4n-abi/src/args/cspace.rs` | S |
| V1-G | M-RS-5 | Add W^X validation to `BitOr` impl on `PagePerms`. Return `Result` or document panic on W^X violation. | `rust/sele4n-abi/src/args/page_perms.rs` | S |
| V1-H | M-RS-7 | Add `is_reserved()` / `is_valid()` methods to `Slot`, `DomainId`, `Priority` identifier types. | `rust/sele4n-types/src/identifiers.rs` | S |
| V1-I | L-RS-2 | Add `method_count` and `max_message_size` bounds validation to `ServiceRegisterArgs::decode()`. | `rust/sele4n-abi/src/args/service.rs` | S |
| V1-J | L-RS-3 | Align `IpcBuffer::get_mr` error variant with V1-E naming. | `rust/sele4n-abi/src/ipc_buffer.rs` | XS |
| V1-K | M-TST-7 | Add Rust conformance tests: `decode_response` with `u64::MAX`, `LifecycleRetypeArgs::decode` with invalid type tag, `PagePerms` W^X combinations. | `rust/sele4n-abi/tests/conformance.rs` | M |
| V1-L | — | Run full Rust test suite (`cargo test --all`) and verify all V1 changes compile. | All Rust crates | XS |

**Dependencies**: None (V1 is the entry phase).

---

### Phase V2: API Surface Completion (9 sub-tasks)

**Priority**: Pre-benchmark (required for hardware exercising)
**Gate**: `lake build SeLe4n.Kernel.API`; all new syscalls have dispatch + delegation theorems; `test_smoke.sh` green
**Estimated scope**: ~400 lines Lean
**Depends on**: V1 (Rust ABI must match new Lean syscalls)

| ID | Finding | Task | Files | Scope |
|----|---------|------|-------|-------|
| V2-A | M-API-1 | Add `notificationSignal` and `notificationWait` to `SyscallId` enum. Update Lean `SyscallId` definition with discriminants 14, 15. | `SeLe4n/Kernel/Architecture/RegisterDecode.lean`, `SeLe4n/Model/Object/Types.lean` | M |
| V2-B | M-API-1 | Wire `notificationSignal`/`notificationWait` into `dispatchWithCap` and `dispatchWithCapChecked` dispatch arms. Add delegation theorems. | `SeLe4n/Kernel/API.lean` | M |
| V2-C | M-API-2 | Add `replyRecv` to `SyscallId` enum (discriminant 16). Wire into dispatch with compound operation semantics (reply + receive in one transition). | `SeLe4n/Kernel/API.lean`, `RegisterDecode.lean` | M |
| V2-D | M-API-1 | Add Rust `SyscallId` variants 14-16 to match Lean. Update encode/decode. | `rust/sele4n-types/src/syscall.rs`, `rust/sele4n-abi/src/encode.rs` | S |
| V2-E | M-API-3 | Add 20-bit label bound check in `MessageInfo.decode`. Values exceeding `2^20 - 1` return `.invalidMessageInfo`. | `SeLe4n/Model/Object/Types.lean` | S |
| V2-F | M-API-5 | Make cap transfer slot base configurable via `SyscallArgs` rather than hardcoded `Slot.ofNat 0`. Update `dispatchWithCap` callers. | `SeLe4n/Kernel/API.lean`, `IPC/DualQueue/WithCaps.lean` | M |
| V2-G | L-IPC-2 | Align IPC cap transfer slot base with V2-F changes. Update `endpointSendDualWithCaps` to accept slot base parameter. | `SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean` | S |
| V2-H | M-API-3 | Update Rust `MessageInfo::new()` to enforce 20-bit label bound (reject labels ≥ 2^20). | `rust/sele4n-abi/src/message_info.rs` | S |
| V2-I | — | Update `SyscallArgDecode.lean` with decode structs for notification and replyRecv syscalls. Add round-trip proofs. | `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` | M |

**Dependencies**: V1 (Rust enum alignment), V2-A before V2-B/V2-C, V2-E before V2-H.

---

### Phase V3: Proof Chain Hardening (13 sub-tasks)

**Priority**: Pre-release (proof completeness for first major release)
**Gate**: `lake build` succeeds; zero `sorry`; `test_full.sh` green
**Estimated scope**: ~600 lines Lean (proofs)
**Depends on**: V2 (new syscalls must be covered by invariant preservation)

| ID | Finding | Task | Files | Scope |
|----|---------|------|-------|-------|
| V3-A | H-RH-1 | Add lemma `invExt_implies_size_lt_capacity` proving `invExt t → t.size < t.capacity` via `loadFactorBounded`. If `loadFactorBounded` is not in `invExt`, add it or add a separate `invExtFull` bundle. | `SeLe4n/Kernel/RobinHood/Invariant/Defs.lean` | M |
| V3-B | H-RH-1 | Refactor `erase_preserves_invExt` to derive `hSize` from `invExt` via V3-A lemma. Update all call sites to remove redundant hypothesis. | `SeLe4n/Kernel/RobinHood/Invariant/Preservation.lean` | M |
| V3-C | H-RAD-1 | Add documentation theorem `uniqueRadixIndices_sufficient` proving that `UniqueRadixIndices` at build time guarantees safe radix tree operations. Verify all `buildCNodeRadix` call sites supply this precondition. | `SeLe4n/Kernel/RadixTree/Bridge.lean` | S |
| V3-D | M-PRF-1 | Verify CDT acyclicity hypothesis discharge at cross-subsystem layer. If not discharged, add `addEdge_preserves_acyclicity` theorem for `cspaceCopy`, `cspaceMove`, `cspaceMintWithCdt`. | `SeLe4n/Kernel/Capability/Invariant/Preservation.lean`, `CrossSubsystem.lean` | L |
| V3-E | M-PRF-2 | Complete `ipcUnwrapCaps` Grant=true loop composition proof. Expose `ipcUnwrapCapsLoop` sufficiently for inductive proof, or add wrapper lemma. | `SeLe4n/Kernel/IPC/Operations/CapTransfer.lean`, `Capability/Invariant/Preservation.lean` | L |
| V3-F | M-PRF-3 | Add composition-level theorem: all callers of `resolveCapAddress` must perform post-resolution rights checks. Prove via exhaustive dispatch analysis. | `SeLe4n/Kernel/Capability/Operations.lean`, `API.lean` | M |
| V3-G | M-PRF-5 | Add formal invariant `waitingThreadsPendingMessageNone`: for all threads in `blockedOnReceive`/`blockedOnNotification` state, `tcb.pendingMessage = none`. Prove preservation for all IPC operations. | `SeLe4n/Kernel/IPC/Invariant/Defs.lean`, `EndpointPreservation.lean`, `NotificationPreservation.lean` | L |
| V3-H | M-DS-4 | Add documentation or assertion that `buildCNodeRadix` callers supply `hNoPhantom`. If not auto-dischargeable, add `buildCNodeRadix_safe` variant that checks at runtime. | `SeLe4n/Kernel/RadixTree/Bridge.lean` | S |
| V3-I | L-IPC-1 | Add lemma `notificationWake_pendingMessage_was_none` proving that `pendingMessage` was `none` before wake sets it. | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | S |
| V3-J | L-IPC-3 | Strengthen `ipcStateQueueConsistent` to check queue membership (not just endpoint existence). Add thread-in-queue predicate. | `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` | M |
| V3-K | L-LIFE-1 | Add `endpointQueueNoDup` invariant: no thread appears twice in any endpoint queue. Prove preservation for enqueue/dequeue operations. | `SeLe4n/Kernel/IPC/Invariant/Defs.lean`, `Structural.lean` | M |
| V3-L | — | Verify all V3 proofs compile: `lake build SeLe4n.Kernel.RobinHood.Invariant.Preservation`, `lake build SeLe4n.Kernel.Capability.Invariant.Preservation`, `lake build SeLe4n.Kernel.IPC.Invariant.Structural`. | All modified modules | XS |
| V3-M | — | Run `test_full.sh` to verify invariant surface anchors and full proof chain. | Scripts | XS |

**Dependencies**: V3-A before V3-B; V3-G before V3-K; V3-D depends on reading `CrossSubsystem.lean`.

---

### Phase V4: Platform & Hardware Fidelity (14 sub-tasks)

**Priority**: Pre-hardware-binding (RPi5 deployment blocker)
**Gate**: `lake build SeLe4n.Platform.RPi5.Contract`; `lake build SeLe4n.Platform.Boot`; `test_smoke.sh` green
**Estimated scope**: ~500 lines Lean
**Depends on**: V1 (Rust ABI stable), V2 (API surface finalized)

| ID | Finding | Task | Files | Scope |
|----|---------|------|-------|-------|
| V4-A | H-BOOT-1 | Extend boot-to-runtime invariant bridge beyond empty config. Prove each builder operation (`registerIrq`, `createObject`) preserves all 9 components of `proofLayerInvariantBundle`. | `SeLe4n/Platform/Boot.lean`, `Model/Builder.lean` | XL |
| V4-B | M-HW-1 | Add 4-byte alignment check to `mmioRead32`/`mmioWrite32` and 8-byte alignment check to `mmioRead64`/`mmioWrite64`. Return `MmioError.unaligned` on violation. | `SeLe4n/Platform/RPi5/MmioAdapter.lean` | M |
| V4-C | M-HW-2 | Model write-one-clear (W1C) semantics for GIC registers. Add `MmioWriteKind.writeOneClear` case to `mmioWrite32` that computes `old_val & ~write_val`. | `SeLe4n/Platform/RPi5/MmioAdapter.lean` | M |
| V4-D | M-HW-3 | Parameterize RPi5 RAM region from `PlatformConfig` rather than hardcoding 4GB. Add `ramSize` field to `BCM2712Config`. | `SeLe4n/Platform/RPi5/Board.lean` | M |
| V4-E | M-HW-4 | Make non-flush `vspaceMapPage`/`vspaceUnmapPage` variants `private`. Only flush-inclusive versions remain in public API. | `SeLe4n/Kernel/Architecture/VSpace.lean` | S |
| V4-F | M-HW-5 | Add `MemoryKind` cross-check in `VSpaceMapArgs` decode: device regions cannot receive execute permission. | `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` | S |
| V4-G | M-HW-6 | Add substantive boot precondition checks to simulation `BootContract`. At minimum: non-empty object store validation, IRQ range check. | `SeLe4n/Platform/Sim/BootContract.lean` | S |
| V4-H | M-HW-8 | Add validation for truncated DTB `reg` entries: reject entries with fewer than `address-cells + size-cells` bytes. | `SeLe4n/Platform/DeviceTree.lean` | S |
| V4-I | M-HW-9 | Fix `registerContextStableCheck` to actually use pre-state parameter in comparison, or document why it's intentionally ignored. | `SeLe4n/Platform/RPi5/RuntimeContract.lean` | S |
| V4-J | M-DEF-8 | Document that internal `vspaceMapPage` default permissions are overridden by all production entry points. Add assertion or comment. | `SeLe4n/Kernel/Architecture/VSpace.lean` | XS |
| V4-K | L-FND-2 | Add W^X rejection in `PagePermissions.ofNat`: if both write and execute are set, return `readOnly` or error. | `SeLe4n/Model/Object/Structures.lean` | S |
| V4-L | L-FND-4 | Document `machineWordBounded` invariant scope. Add `isWord64` predicates to `Badge`, `CPtr`, `Slot` flowing to hardware decode. | `SeLe4n/Prelude.lean`, `Architecture/RegisterDecode.lean` | M |
| V4-M | L-PLAT-1 | Implement basic DTB parsing in `fromDtb` (at minimum: magic number check, version check, structure block traversal for `/memory` node). | `SeLe4n/Platform/DeviceTree.lean` | L |
| V4-N | L-PLAT-3 | Generalize `extractMemoryRegions` to handle both 1-cell (32-bit) and 2-cell (64-bit) address formats. | `SeLe4n/Platform/DeviceTree.lean` | M |

**Dependencies**: V4-A is the largest task (XL) and can be parallelized with V4-B through V4-N. V4-E before V4-J.

---

### Phase V5: Defensive Coding & Robustness (16 sub-tasks)

**Priority**: Pre-release (defense-in-depth hardening)
**Gate**: `lake build` succeeds; zero `sorry`; `test_smoke.sh` green
**Estimated scope**: ~350 lines Lean
**Depends on**: V2 (API surface stable), V3 (proof chain updates)

| ID | Finding | Task | Files | Scope |
|----|---------|------|-------|-------|
| V5-A | M-DEF-1 | Replace `blob.get!` with `blob.get?` in `readBE32` and all DTB parsing functions. Propagate `Option` through callers. | `SeLe4n/Platform/DeviceTree.lean` | M |
| V5-B | M-DEF-2 | Make `lifecycleRetypeObject` and `lifecycleRetypeDirect` `private`. Add `@[private]` attribute or move to `where` clause. | `SeLe4n/Kernel/Lifecycle/Operations.lean` | S |
| V5-C | M-DEF-3 | Make `bootFromPlatformChecked` (with duplicate rejection) the default. Rename current `bootFromPlatform` to `bootFromPlatformUnchecked` with deprecation notice. | `SeLe4n/Platform/Boot.lean` | S |
| V5-D | M-DEF-4 | Add explicit error logging path in `saveOutgoingContext` when TCB lookup fails. Return `SystemState × Bool` where `Bool` indicates success. | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | S |
| V5-E | M-DEF-5 | Same as V5-D for `restoreIncomingContext`: add explicit failure indicator. | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | S |
| V5-F | M-DEF-6 | Add explicit guard in `handleYield`: if `current = none`, return `.invalidArgument` immediately instead of falling through to `schedule`. | `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | S |
| V5-G | M-DEF-7 | Add API-level documentation distinguishing `cspaceRevoke` (single-CNode) from `cspaceRevokeCdt`/`cspaceRevokeCdtStrict` (cross-CNode). Add routing helper or unified entry point. | `SeLe4n/Kernel/Capability/Operations.lean` | S |
| V5-H | M-HW-7 | Add `domainTimeRemaining > 0` to scheduler initialization invariant. Prove it is maintained by `scheduleDomain` and `timerTick`. | `SeLe4n/Kernel/Scheduler/Invariant.lean`, `Operations/Preservation.lean` | M |
| V5-I | H-SVC-1 | Document fuel bounds for `serviceHasPathTo`. Add `maxServiceFuel` constant based on `maxServices`. Consider proving fuel sufficiency: `fuel ≥ maxServices → serviceHasPathTo` terminates without fuel exhaustion for any valid graph. | `SeLe4n/Kernel/Service/Operations.lean`, `Invariant/Acyclicity.lean` | M |
| V5-J | L-FND-1 | Add `ThreadId.toObjIdChecked` that verifies TCB type in object store. Document when to use checked vs unchecked variant. | `SeLe4n/Prelude.lean` | S |
| V5-K | L-FND-3 | Document `storeObject` infallibility design rationale. Add comment explaining capacity enforcement deferred to `retypeFromUntyped`. | `SeLe4n/Model/State.lean` | XS |
| V5-L | L-SCH-1 | Make `defaultTimeSlice` configurable via `SchedulerConfig` field (with 5 as default). Thread-level time slices deferred. | `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | S |
| V5-M | L-SCH-2 | Document that `timerTick` re-enqueue using pre-reset priority is correct because priority is immutable during tick. Add comment. | `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | XS |
| V5-N | L-CAP-1 | Remove redundant second `cdtDetachSlot` call in `processRevokeNode` or add idempotency comment. | `SeLe4n/Kernel/Capability/Operations.lean` | XS |
| V5-O | L-DS-3 | Add membership check before `frozenQueueDequeue`: verify thread is actually in queue. Return error on mismatch. | `SeLe4n/Kernel/FrozenOps/Operations.lean` | S |
| V5-P | L-DS-4 | Add occupied-slot check in `frozenCspaceMint`: if slot occupied, return `.slotOccupied` error instead of silent overwrite. | `SeLe4n/Kernel/FrozenOps/Operations.lean` | S |

**Dependencies**: V5-D/V5-E may require updating `Preservation.lean` proofs. V5-H depends on V3 proof patterns.

---

### Phase V6: Information Flow & Cross-Subsystem (12 sub-tasks)

**Priority**: Pre-release (security property completeness)
**Gate**: `lake build SeLe4n.Kernel.InformationFlow.Invariant.Composition`; `lake build SeLe4n.Kernel.CrossSubsystem`; `test_full.sh` green
**Estimated scope**: ~500 lines Lean
**Depends on**: V3 (proof chain), V5 (defensive patterns)

| ID | Finding | Task | Files | Scope |
|----|---------|------|-------|-------|
| V6-A | M-PRF-4 | Formalize cross-subsystem field-disjointness. Add theorem `subsystemFieldDisjoint` proving each subsystem's invariant reads disjoint state fields. | `SeLe4n/Kernel/CrossSubsystem.lean` | L |
| V6-B | M-PRF-6 | Prove `serviceCountBounded` preservation across lifecycle retype and IPC endpoint operations. | `SeLe4n/Kernel/Service/Invariant/Acyclicity.lean`, `CrossSubsystem.lean` | M |
| V6-C | M-IF-1 | Add comprehensive documentation for non-standard integrity flow direction. Add theorem `integrityFlowsTo_is_not_biba` as explicit documentation anchor. | `SeLe4n/Kernel/InformationFlow/Policy.lean` | S |
| V6-D | M-IF-2 | Document NI deployment requirements: domain-separation hypotheses must be discharged by system integrator's labeling context. Add `LabelingContextValid` predicate. | `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` | M |
| V6-E | M-IF-3 | Extend NI projection model to include service registry state. Add `ObservableState.serviceRegistry` field and projection logic. | `SeLe4n/Kernel/InformationFlow/Projection.lean` | M |
| V6-F | M-IF-4 | Promote enforcement boundary from `List` to type-level guarantee. Add `EnforcementBoundaryComplete` theorem proving all `KernelOperation` constructors are covered. | `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` | M |
| V6-G | M-IF-5 | Add `endpointPolicyRestricted` well-formedness requirement: per-endpoint policy must be a subset of global policy. Add theorem. | `SeLe4n/Kernel/InformationFlow/Policy.lean` | M |
| V6-H | M-IF-6 | Add declassification audit trail: `DeclassificationEvent` structure recording source, target, authorization, timestamp. Thread through enforcement wrappers. | `SeLe4n/Kernel/InformationFlow/Policy.lean`, `Enforcement/Wrappers.lean` | M |
| V6-I | M-IF-7 | Strengthen `niStepCoverage`: replace `syscallDecodeError` universal witness with per-operation specific NI step constructors. Prove operational correspondence. | `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` | L |
| V6-J | L-IF-1 | Document scheduling covert channel as accepted. Add `acceptedCovertChannel_scheduling` theorem establishing explicit bound. | `SeLe4n/Kernel/InformationFlow/Projection.lean` | S |
| V6-K | L-IF-2 | Add `defaultLabelingContext_insecure` warning theorem. Document that production deployments must override with domain-specific labeling. | `SeLe4n/Kernel/InformationFlow/Policy.lean` | S |
| V6-L | L-IF-3 | Update `enforcementBoundaryExtended` to include all 20 current entries (was 18). Add completeness assertion. | `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` | S |

**Dependencies**: V6-A is the critical path (largest, enables V6-B). V6-E may affect V6-I.

---

### Phase V7: Performance & Data Structure Optimization (10 sub-tasks)

**Priority**: Pre-hardware (performance-sensitive for RPi5 benchmarking)
**Gate**: `lake build` succeeds; zero `sorry`; `test_full.sh` green; heartbeat budgets reduced
**Estimated scope**: ~400 lines Lean
**Depends on**: V3 (RobinHood proof changes)

| ID | Finding | Task | Files | Scope |
|----|---------|------|-------|-------|
| V7-A | M-DS-1 | Refactor `filter_fold_present` proof in Bridge.lean to reduce heartbeat budget from 3.2M. Split into intermediate lemmas; target ≤ 800K heartbeats. | `SeLe4n/Kernel/RobinHood/Bridge.lean` | L |
| V7-B | M-DS-2 | Refactor high-heartbeat proofs in Preservation.lean. Split large omega/simp blocks into named intermediate steps. Target ≤ 400K heartbeats per theorem. | `SeLe4n/Kernel/RobinHood/Invariant/Preservation.lean` | L |
| V7-C | M-DS-3 | Make `LawfulBEq` an explicit API-level requirement for `RHTable`. Add `[LawfulBEq α]` to public operation signatures (not just theorem signatures). Document in module docstring. | `SeLe4n/Kernel/RobinHood/Core.lean` | S |
| V7-D | M-DS-5 | Prove general `filter_preserves_key` theorem for arbitrary predicates on `RHTable`. Remove need for per-predicate proof instances. | `SeLe4n/Kernel/RobinHood/Bridge.lean` | M |
| V7-E | M-RS-6 | Replace `native_decide` in `RegisterFile.not_lawfulBEq` with `decide` if feasible. If not feasible (timeout), document TCB impact and add tracking comment. | `SeLe4n/Machine.lean` | S |
| V7-F | M-TST-8 | Document non-lawful `BEq RegisterFile` in test code. Add warning comment where `==` is used on `RegisterFile` or `TCB` values. | `SeLe4n/Machine.lean`, test files | S |
| V7-G | L-DS-1 | Refactor `CNodeRadix.toList` from O(n²) `acc ++ [(slot, cap)]` to O(n) `(slot, cap) :: acc` with final `List.reverse`. | `SeLe4n/Kernel/RadixTree/Core.lean` | S |
| V7-H | L-DS-2 | Document that Robin Hood `erase` size decrement is safe under `invExt` (which guarantees `size > 0` when key exists). Add comment. | `SeLe4n/Kernel/RobinHood/Core.lean` | XS |
| V7-I | L-PLAT-2 | Optimize `irqKeysNoDup`/`objIdKeysNoDup` from O(n²) to O(n log n) using sorted comparison or HashSet. | `SeLe4n/Platform/Boot.lean` | S |
| V7-J | L-SCH-3 | Document `RunQueue.wellFormed` as external predicate design rationale. Consider adding `RunQueue.mk_checked` constructor for validated creation. | `SeLe4n/Kernel/Scheduler/RunQueue.lean` | S |

**Dependencies**: V7-A/V7-B depend on V3-A/V3-B (RobinHood invariant changes). V7-G independent.

---

### Phase V8: Test Coverage & Documentation (8 sub-tasks)

**Priority**: Pre-release (quality assurance)
**Gate**: `test_full.sh` green; fixture updated; all new tests pass
**Estimated scope**: ~500 lines Lean (test code), ~100 lines documentation
**Depends on**: V2 (new syscalls to test), V5 (defensive changes to validate)

| ID | Finding | Task | Files | Scope |
|----|---------|------|-------|-------|
| V8-A | M-TST-1 | Add end-to-end test of `syscallEntryChecked` pipeline: register decode → capability lookup → IF check → dispatch → result encode. | `SeLe4n/Testing/MainTraceHarness.lean` | L |
| V8-B | M-TST-2 | Add `cspaceMove` end-to-end test: register decode → move operation → verify source empty, dest populated. | `SeLe4n/Testing/MainTraceHarness.lean` | M |
| V8-C | M-TST-3 | Fix inter-transition invariant checks to validate mutated state (not original `st1`). Add post-mutation checks after each operation in trace. | `SeLe4n/Testing/MainTraceHarness.lean` | M |
| V8-D | M-TST-4 | Fix `buildValidated` Check 8 to account for dequeue-on-dispatch semantics. Current thread may not be in run queue after `schedule`. | `SeLe4n/Testing/StateBuilder.lean` | S |
| V8-E | M-TST-5 | Replace `partial` in `intrusiveQueueReachable` with explicit fuel parameter and `Decidable` instance. Add termination proof. | `SeLe4n/Testing/InvariantChecks.lean` | S |
| V8-F | M-TST-6 | Add fixture drift detection: compute hash of `MainTraceHarness.lean` semantic operations and compare against recorded hash in expected fixture. | `tests/fixtures/`, `scripts/test_smoke.sh` | S |
| V8-G | M-TST-9 | Add explicit `ThreadState` enum to model (Running, Ready, BlockedSend, BlockedRecv, BlockedCall, BlockedNotif, Inactive). Refactor queue membership inference to use explicit state field. | `SeLe4n/Model/Object/Types.lean`, `Scheduler/Invariant.lean` | L |
| V8-H | M-API-4 | Reduce dispatch code duplication: extract common dispatch logic into shared helper used by both `dispatchWithCap` and `dispatchWithCapChecked`. Add structural equivalence theorem for shared path. | `SeLe4n/Kernel/API.lean` | M |

**Dependencies**: V8-A depends on V2 (notification syscalls). V8-G is a model-level change that may affect V3/V5 proofs — schedule last within V8.

---

## 5. Dependency Graph

```
V1 (Rust ABI)
 ├──→ V2 (API Surface) ──→ V8 (Test Coverage)
 │     │                      ↑
 │     └──→ V3 (Proof Chain) ─┤
 │           │                 │
 │           └──→ V5 (Defensive) ──→ V6 (Info Flow)
 │           │                        │
 │           └──→ V7 (Performance) ───┘
 │
 └──→ V4 (Platform/Hardware) [parallel with V2–V3]
```

### Critical Path

**V1 → V2 → V3 → V6** is the longest dependency chain:
1. V1 stabilizes Rust ABI (required for V2 syscall alignment)
2. V2 completes API surface (required for V3 proof coverage)
3. V3 hardens proof chain (required for V6 cross-subsystem formalization)
4. V6 formalizes information flow properties (final security milestone)

### Parallelization Opportunities

- **V4** (Platform) is largely independent and can execute in parallel with V2/V3
- **V7** (Performance) only depends on V3-A/V3-B (RobinHood changes) and can start once those complete
- **V5** (Defensive) can start after V2 completes, in parallel with V3
- Within each phase, sub-tasks marked with independent file sets can execute concurrently

### Phase Summary

| Phase | Sub-tasks | Depends On | Parallel With |
|-------|-----------|------------|---------------|
| V1 | 12 | — | — |
| V2 | 9 | V1 | V4 |
| V3 | 13 | V2 | V4, V5 |
| V4 | 14 | V1 | V2, V3, V5 |
| V5 | 16 | V2, V3 | V4, V7 |
| V6 | 12 | V3, V5 | V7, V8 |
| V7 | 10 | V3 (partial) | V5, V6, V8 |
| V8 | 8 | V2, V5 | V6, V7 |
| **Total** | **94** | | |

---

## 6. Accepted Findings (No Remediation Required)

The following findings require no code changes. They are accepted design
decisions, seL4-consistent behaviors, or issues already mitigated by existing
mechanisms. Each is documented here with rationale for acceptance.

### 6.1 seL4-Consistent Design (No Remediation)

| Finding | Description | Rationale |
|---------|-------------|-----------|
| PRE M-12 | No timeout on IPC Call operations | Matches seL4 classic design. Watchdog threads handle liveness. |
| PRE M-13 | No priority inheritance mechanism | Matches seL4 classic (non-MCS). MCS scheduler deferred to future. |
| PRE M-14 | No deadlock detection/prevention | Matches seL4 design. User-space responsibility. |
| PRE L-04 | Notification waitingThreads LIFO ordering | seL4 does not guarantee FIFO for notifications. |
| PRE L-07 | `cspaceMutate` bypasses occupied-slot guard | Intentional in-place update. |
| PRE L-08 | Badge forging via Mint authority | By design; proofs confirm no privilege escalation. |
| PRE L-17 | LIFO notification wait queue ordering | Documented, intentional. |
| PRE L-41 | `resolveExtraCaps` silently drops failures | seL4 behavior — userspace receives fewer caps. |
| LEAN_RUST M-RS-02 | Reply syscall maps to Write access right | Policy choice matching Lean model. |
| LEAN_RUST M-RS-07 | `Cap::from_cptr()` trusts caller about type | By design — kernel validates on syscall entry. |
| LEAN_RUST M-CAP-02 | Temporary double-occupancy during `cspaceMove` | Safe in pure-functional model (no interleaving). |
| LEAN_RUST M-CAP-04 | CDT node removed on delete failure (strict) | Intentional partial-progress design. |
| IMPL L-cap-4 | `cspaceRevokeCdtStrict` partial revocation | Failure report surfaced to caller. |

### 6.2 Mitigated by Existing Mechanisms (No Remediation)

| Finding | Description | Mitigation |
|---------|-------------|------------|
| L-02 | AccessRightSet raw `.mk` constructor | `ofNat` masks to 5 bits; `mk_checked` requires proof; `ofNat_valid` theorem. |
| PRE M-09 | `switchDomain` mixes `st` and `stSaved` | Proven correct by `saveOutgoingContext_scheduler` frame lemma. |
| LEAN_RUST M-SCH-01 | `currentThreadInActiveDomain` vacuously true | Mitigated by `currentThreadValid` in composed bundle. |
| LEAN_RUST M-SCH-02 | `handleYield` no explicit QCC pre-condition | Covered by Preservation.lean proof hypotheses. |
| LEAN_RUST M-SCH-03 | `switchDomain` reads from `st` not `stSaved` | Proven safe; save only affects `registerContext`. |
| LEAN_RUST M-IPC-01 | Mixed pre/post state in `endpointSendDualWithCaps` | Correct — receiver from pre-state, CSpace from post-state. |
| LEAN_RUST M-PLAT-12 | `mmioRead` returns concrete for volatile | `MmioSafe` hypothesis mitigates. |
| IMPL L-state-3 | `FrozenMap.get?` redundant bounds check | Redundancy under `freezeMap` construction. |
| IMPL L-state-4 | `FrozenMap.set` cannot add new keys | By design for execution phase. |
| PRE L-18 | Badge unbounded Nat | `ofNatMasked` provides 64-bit clamping. |

### 6.3 Documentation-Only (Tracked, No Code Change)

| Finding | Description | Status |
|---------|-------------|--------|
| PRE L-06 | `objectIndex` append-only, never pruned | Documented design with size analysis (max 512KB). |
| PRE L-11 | O(n) flat-list scan in `chooseBestInBucket` | Acceptable for <256 threads per documentation. |
| PRE L-12 | O(k+n) RunQueue.remove/rotateToBack | Acceptable for production thread counts. |
| LEAN_RUST M-FND-03 | `storeObject` capabilityRefs O(n) rebuild | Performance concern, not security. |
| LEAN_RUST M-CAP-01 | `radixMask` unbounded Nat exponentiation | Safe in model; hardware binding must enforce. |
| LEAN_RUST M-CAP-03 | `cspaceRevokeCdt` materializes full list | Addressed by streaming BFS variant. |
| LEAN_RUST M-SCH-04 | O(n) flat-list RunQueue operations | Acceptable for <256 threads. |
| LEAN_RUST M-FND-02 | TCB BEq inherits non-lawful from RegisterFile | Guarded by negative witness. |
| IMPL L-life-3 | `lifecycleIdentityNoTypeAliasConflict` tautology | Retained for compatibility. |
| PRE L-24 | Memory projection optional ownership model | Default = no projection; deployment configurable. |
| PRE L-26 | `projectStateFast` requires sync preconditions | Documented requirement. |

---

## 7. Verification & Gate Conditions

### Per-Phase Gate Conditions

| Phase | Gate Condition | Verification Command |
|-------|---------------|---------------------|
| V1 | All Rust tests pass, no compile warnings | `cd rust && cargo test --all 2>&1 \| tail -20` |
| V2 | New syscalls build and have delegation theorems | `source ~/.elan/env && lake build SeLe4n.Kernel.API` |
| V3 | Zero sorry, all modified modules build | `source ~/.elan/env && lake build <each module>` |
| V4 | Platform modules build, RPi5 contract valid | `source ~/.elan/env && lake build SeLe4n.Platform.RPi5.Contract` |
| V5 | Defensive changes compile, no regressions | `./scripts/test_smoke.sh` |
| V6 | IF composition builds, cross-subsystem passes | `source ~/.elan/env && lake build SeLe4n.Kernel.CrossSubsystem` |
| V7 | Heartbeat budgets reduced, perf tests pass | `source ~/.elan/env && lake build SeLe4n.Kernel.RobinHood.Bridge` |
| V8 | All tests green, fixture updated | `./scripts/test_full.sh` |

### Global Gate Conditions (All Phases)

1. **Zero sorry/axiom**: `grep -r "sorry\|axiom " SeLe4n/ --include="*.lean" | grep -v "^--"` returns empty
2. **No website link breakage**: `./scripts/check_website_links.sh` passes
3. **Tier 0 hygiene**: `./scripts/test_tier0_hygiene.sh` passes
4. **No `sorry` in staged content**: Pre-commit hook catches (install: `cp scripts/pre-commit-lean-build.sh .git/hooks/pre-commit`)
5. **Module build verification**: Each modified `.lean` file must pass `lake build <Module.Path>` before commit

### Version Milestones

| Version | Phases Included | Description |
|---------|----------------|-------------|
| v0.22.0 | V1 | Rust ABI hardened |
| v0.22.1 | V2 | API surface complete (notification + replyRecv syscalls) |
| v0.22.2 | V3 | Proof chain gaps closed |
| v0.22.3 | V4 | Platform/hardware fidelity |
| v0.22.4 | V5 | Defensive coding hardened |
| v0.22.5 | V6 | Information flow formalized |
| v0.22.6 | V7 | Performance optimized |
| v0.22.7 | V8 | Test coverage complete — **WS-V PORTFOLIO COMPLETE** |

---

## 8. Risk Assessment

### 8.1 Technical Risks

| Risk | Severity | Mitigation |
|------|----------|------------|
| V3-D (CDT acyclicity) may require deep proof refactoring | High | Start early; if too complex, add runtime check as intermediate step |
| V3-E (ipcUnwrapCaps loop) requires exposing private internal | Medium | May need Lean `@[private]` removal or wrapper pattern |
| V4-A (boot invariant bridge) is XL scope across 9 invariant components | High | Decompose into per-builder-operation sub-proofs; parallelize |
| V6-A (cross-subsystem formalization) may reveal actual interference | High | If interference found, it becomes a Critical finding requiring immediate remediation |
| V6-I (niStepCoverage strengthening) touches 32 constructors | Medium | Incremental: prove 5-8 constructors per sub-task |
| V7-A/V7-B (heartbeat reduction) may not be achievable for all proofs | Low | Set target budgets; document remaining high-heartbeat proofs with justification |
| V8-G (explicit ThreadState) is a model-level change with wide blast radius | High | Schedule last in V8; run full test suite after; consider as optional if time-constrained |

### 8.2 Dependency Risks

| Risk | Impact | Mitigation |
|------|--------|------------|
| Lean 4.28.0 toolchain change during WS-V | Build breakage | Pin toolchain in `lean-toolchain`; test on upgrade before adopting |
| V2 syscall additions may break Rust conformance tests | Test failures | V1 and V2-D must be coordinated (same PR or sequential) |
| V3 proof changes may increase build time significantly | CI slowdown | Monitor build times; parallelize CI with `lake build` per-module |

### 8.3 Scope Containment

**Hard boundaries for WS-V:**
- No MCS scheduler (deferred to post-release)
- No IPC timeouts (seL4 design decision, not a bug)
- No priority inheritance (seL4 classic design)
- No VSpaceBackend concrete instance (deferred to hardware binding)
- No garbage collection for `objectIndex` (documented design)
- No formal verification of Rust code (Lean proofs only)

**Stretch goals (include if time permits):**
- V8-G (explicit ThreadState enum) — beneficial but high blast radius
- V4-M (DTB parsing beyond stub) — useful for RPi5 but not blocking
- V7-D (general `filter_preserves_key`) — proof elegance, not soundness

---

## 9. Finding Coverage Matrix

Every finding from every audit is accounted for below. Findings map to exactly
one of: a WS-V sub-task, an accepted finding (Section 6), or an exclusion.

### 9.1 PRE_BENCHMARK Audit (119 findings)

| Category | Count | Remediation | Accepted | Excluded |
|----------|-------|-------------|----------|----------|
| HIGH (4) | 4 | 4 → V1,V3,V4,V5 (H-RS-1, H-BOOT-1, H-SVC-1, H-RH-1, H-RAD-1) | 0 | 0 |
| MEDIUM (29) | 29 | 25 → V1–V8 | 4 (M-09, M-12, M-13, M-14) | 0 |
| LOW (41) | 41 | 21 → V1–V8 | 13 (§6.1, §6.2) | 7 (Info) |
| Info (54) | 54 | 0 | 0 | 54 (observations) |

### 9.2 LEAN_RUST_KERNEL Audit (68 findings)

| Category | Count | Remediation | Accepted | Excluded |
|----------|-------|-------------|----------|----------|
| HIGH (1) | 1 | H-RS-1 (dedup with PRE L-35) | 0 | 0 |
| MEDIUM (39) | 39 | 27 → V1–V8 | 12 (§6.1–§6.3) | 0 |
| LOW (28) | 28 | 8 → V1–V8 | 11 (§6.2–§6.3) | 9 (Info) |

### 9.3 KERNEL_IMPLEMENTATION Audit (75 findings)

| Category | Count | Remediation | Accepted | Excluded |
|----------|-------|-------------|----------|----------|
| HIGH (0) | 0 | — | — | — |
| MEDIUM (20) | 20 | 17 → V1–V8 | 3 (§6.1, §6.2) | 0 |
| LOW (55) | 55 | 12 → V1–V8 | 18 (§6.1–§6.3) | 25 (Info) |
| Info (150+) | 150+ | 0 | 0 | 150+ (observations) |

### 9.4 Totals

| | Remediation | Accepted | Excluded | Total |
|--|-------------|----------|----------|-------|
| Unique findings | **94 sub-tasks** | **42** | **~245 Info** | **~381** |
| Finding severity | 5 HIGH, 61 MED, 29 LOW | 13+10+11 LOW | Info only | |

---

*End of workstream plan.*
