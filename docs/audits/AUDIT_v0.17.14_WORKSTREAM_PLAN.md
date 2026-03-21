# WS-R Workstream Plan — Comprehensive Audit Remediation (v0.17.14)

**Created**: 2026-03-21
**Baseline version**: 0.17.14
**Baseline audit**: `docs/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`
**Prior portfolios**: WS-B through WS-Q (all COMPLETE — see `docs/WORKSTREAM_HISTORY.md`)
**Constraint**: Zero `sorry`/`axiom` in production proof surface
**Finding count**: 1 High, 19 Medium, 34 Low, 28 Info (82 total)

---

## 1. Executive Summary

The comprehensive pre-release audit of seLe4n v0.17.13 identified **82 findings**
across the Lean kernel, Rust userspace library, and infrastructure. Zero Critical
findings. The single High-severity finding (`Cap::downgrade()` rights bypass) is
in the Rust library and enables phantom-typed capability escalation. The 19 Medium
findings cluster around five themes:

1. **Silent failure paths** — operations that discard errors or return success on
   internal failures (M-05, M-06, M-10, M-11, M-16)
2. **Deferred proof obligations** — composition theorems that accept critical
   properties as hypotheses rather than proving them (M-01, M-09, M-18, M-19)
3. **Cross-subsystem consistency gaps** — lifecycle operations that invalidate
   service registry or IPC queue invariants (M-12, M-13, M-14, M-15)
4. **API surface defects** — convenience wrappers that bypass capability
   resolution (M-04), CDT proofs incomplete for remove/acyclicity (M-07, M-08)
5. **Hardware-binding model gaps** — TLB flush not enforced, memory projection
   returns dummy bytes (M-03, M-17)

This workstream plan organizes all actionable findings into **8 phases** (R1–R8)
with explicit dependencies, atomic sub-tasks, gate conditions, and scope estimates.
The plan addresses all 20 High+Medium findings and selects 12 Low findings for
inclusion based on security relevance and proof chain completeness.

---

## 2. Finding Registry

### 2.1 High (1)

| ID | Location | Description |
|----|----------|-------------|
| H-01 | `rust/sele4n-sys/src/cap.rs:141` | `Cap::downgrade()` converts rights without subset check |

### 2.2 Medium — Silent Failure (5)

| ID | Severity | Location | Description |
|----|----------|----------|-------------|
| M-05 | MEDIUM | `Capability/Operations.lean:789` | `streamingRevokeBFS` fuel exhaustion returns `.ok` |
| M-06 | MEDIUM | `Capability/Operations.lean:728` | `processRevokeNode` swallows delete errors |
| M-10 | MEDIUM | `FrozenOps/Core.lean:139` | `frozenSaveOutgoingContext` silently discards registers |
| M-11 | MEDIUM | `FrozenOps/Core.lean:149` | `frozenRestoreIncomingContext` returns wrong context |
| M-16 | MEDIUM | `IPC/Operations/Endpoint.lean:172` | `notificationSignal` wake path discards badge |

### 2.3 Medium — Deferred Proofs (4)

| ID | Severity | Location | Description |
|----|----------|----------|-------------|
| M-01 | MEDIUM | `InformationFlow/Invariant/Operations.lean:85-98` | IPC NI proofs accept NI as hypothesis parameter |
| M-09 | MEDIUM | `Model/FreezeProofs.lean:1033` | Frozen invariant existential stales on mutation |
| M-18 | MEDIUM | `IPC/Invariant/Structural.lean:2386-2411` | `ipcInvariantFull` preservation externalized |
| M-19 | MEDIUM | `IPC/Invariant/Defs.lean:576-610` | `notificationWaiterConsistent` preservation deferred |

### 2.4 Medium — Cross-Subsystem Consistency (4)

| ID | Severity | Location | Description |
|----|----------|----------|-------------|
| M-12 | MEDIUM | `Lifecycle/Operations.lean:27-36` | `cleanupTcbReferences` misses IPC endpoint queues |
| M-13 | MEDIUM | Multiple | No registry/lifecycle cross-subsystem consistency |
| M-14 | MEDIUM | `Service/Registry.lean:53-67` | `registerService` performs no capability authority check |
| M-15 | MEDIUM | `Service/Registry.lean:87-93` | `revokeService` does not clean dependency graph |

### 2.5 Medium — API & Model (4)

| ID | Severity | Location | Description |
|----|----------|----------|-------------|
| M-02 | MEDIUM | `InformationFlow/Invariant/Composition.lean:34-233` | `registerServiceChecked` absent from NI bundle |
| M-03 | MEDIUM | `InformationFlow/Projection.lean:260-262` | Memory projection returns dummy bytes |
| M-04 | MEDIUM | `Kernel/API.lean:244-321` | `api*` convenience wrappers discard resolved capability |
| M-17 | MEDIUM | `Architecture/TlbModel.lean:87-141` | TLB flush not enforced after page table modification |

### 2.6 Medium — CDT Model (2)

| ID | Severity | Location | Description |
|----|----------|----------|-------------|
| M-07 | MEDIUM | `Model/Object/Structures.lean:838-859` | CDT `removeAsChild`/`removeAsParent` lack consistency proofs |
| M-08 | MEDIUM | `Model/Object/Structures.lean:964-968` | CDT acyclicity only proven for fresh child nodes |

### 2.7 Medium — Rust Library (3)

| ID | Severity | Location | Description |
|----|----------|----------|-------------|
| R-M01 | MEDIUM | `rust/sele4n-abi/src/args/cspace.rs:31` | AccessRights u64-to-u8 silent truncation |
| R-M02 | MEDIUM | `rust/sele4n-abi/src/args/page_perms.rs:46` | PagePerms u64-to-u8 silent truncation |
| R-M03 | MEDIUM | `rust/sele4n-abi/src/decode.rs:40-41` | SyscallResponse badge/msg_info semantic overlap in x1 |

### 2.8 Medium — Infrastructure (4)

| ID | Severity | Location | Description |
|----|----------|----------|-------------|
| I-M01 | MEDIUM | `scripts/setup_lean_env.sh:282` | Elan binary download not SHA-verified (primary path) |
| I-M02 | MEDIUM | `.github/workflows/codebase_map_sync.yml` | Auto-pushes to main with `contents: write` |
| I-M03 | MEDIUM | CI | Rust tests silently skipped when cargo unavailable |
| I-M04 | INFO | CI | 3 test suites compiled but never executed |

### 2.9 Selected Low Findings (12)

| ID | Location | Description | Included because |
|----|----------|-------------|------------------|
| L-01 | `Prelude.lean` | `Badge.ofNat` bypasses word-size bounds | Security boundary |
| L-02 | `Prelude.lean` | `RegName` unbounded — no ARM64 upper-bound | Hardware correctness |
| L-03 | Multiple | `RegValue`, `VAddr`, `PAddr` wrap unbounded `Nat` | Hardware correctness |
| L-04 | `Machine.lean` | `BEq RegisterFile` partial — magic number 32 | Proof completeness |
| L-05 | `Model/Object/Types.lean` | `IpcMessage` arrays lack structural bounds | IPC correctness |
| L-06 | `Model/Object/Types.lean` | TCB missing `faultHandler`, `boundNotification` | seL4 fidelity |
| L-07 | `Capability/Invariant/Preservation.lean` | CDT postconditions deferred for copy/move/mint | Proof chain |
| L-08 | `IPC/Invariant/Structural.lean` | `set_option linter.all false` on 2440-line file | Code quality |
| L-09 | `Service/Registry.lean` | `registerService` does not verify endpoint object type | Invariant safety |
| L-10 | `Architecture/VSpaceInvariant.lean` | `LifecycleRetypeArgs.newType` as raw Nat | Type safety |
| L-11 | Rust | Newtype inner fields `pub` | Encapsulation |
| L-12 | `Scheduler/Operations/Preservation.lean` | `schedulerPriorityMatch` not in invariant bundle | Proof bundle |

---

## 3. Planning Principles

1. **Security-first ordering.** Findings that enable privilege escalation or
   silent security failures are addressed before proof completeness or
   ergonomics improvements. H-01 is the only finding that can be weaponized
   by userspace code — it ships in R1.

2. **Silent-failure elimination.** Operations that return success on internal
   failures violate deterministic semantics. Every transition must return an
   explicit error when postconditions cannot be established.

3. **Proof internalization.** Composition theorems that accept critical
   invariants as external hypotheses create seams in the proof chain. Each
   phase closes specific hypothesis parameters by proving them from
   pre-state invariants and step witnesses.

4. **Cross-subsystem coherence.** Lifecycle, service, IPC, and capability
   subsystems share state. Retype/revocation must preserve invariants across
   subsystem boundaries, not just within a single subsystem.

5. **Additive-first, deprecate-later.** New correct implementations are added
   alongside legacy code. Old wrappers are deprecated in the same phase but
   removed only after all callers migrate. This prevents cascade breakage.

6. **Zero sorry/axiom invariant.** No phase may introduce `sorry`, `axiom`,
   `admit`, or `partial` into production Lean code. Every new theorem must
   compile with full proof. Tracked exceptions require `TPI-D*` annotation.

7. **Gate-per-subtask.** Each atomic subtask ends with a compilation gate
   (`lake build <Module.Path>`) and a test gate (`test_smoke.sh` minimum).
   Theorem-changing subtasks require `test_full.sh`.

8. **Rust and Lean parity.** Rust library fixes in R1 must align with the
   Lean-side capability model. Runtime assertions in Rust mirror
   machine-checked properties in Lean.

---

## 4. Phase Overview

| Phase | ID | Focus | Tasks / Sub-tasks | Deps | Target | Findings |
|-------|----|-------|-------------------|------|--------|----------|
| 1 | **R1** | Pre-Release Blockers | 6 / 17 | — | v0.18.0 | H-01, M-04, M-10, M-11, R-M01, R-M02, R-M03 |
| 2 | **R2** | Capability & CDT Hardening | 7 / 17 | — | v0.18.1 | M-05, M-06, M-07, M-08, L-07 |
| 3 | **R3** | IPC Invariant Completion | 6 / 15 | R2 | v0.18.2 | M-16, M-18, M-19, L-05, L-08 |
| 4 | **R4** | Lifecycle & Service Coherence | 6 / 19 | R2 | v0.18.3 | M-12, M-13, M-14, M-15, L-09 |
| 5 | **R5** | Information Flow Completion | 5 / 13 | R3, R4 | v0.18.4 | M-01, M-02, M-03 |
| 6 | **R6** | Model & Frozen State Correctness | 5 / 10 | R1 | v0.18.5 | M-09, L-01, L-04, L-12 |
| 7 | **R7** | Architecture & Hardware Preparation | 5 / 10 | R6 | v0.18.6 | M-17, L-02, L-03, L-06, L-10 |
| 8 | **R8** | Infrastructure & CI Hardening | 5 / 10 | — | v0.18.7 | I-M01, I-M02, I-M03, I-M04, L-11 |

**Total**: 8 phases, 45 task groups, 111 atomic sub-tasks, addressing 20 High+Medium + 12 Low findings.

**Parallel paths**: R1 and R2 have no mutual dependencies and can execute
concurrently. R8 (infrastructure) is independent of all Lean/Rust phases.
R3 and R4 depend on R2 but are independent of each other. R5 depends on
both R3 and R4 (NI composition requires IPC and service fixes). R6 depends
only on R1 (frozen context error handling). R7 depends on R6.

```
R1 ──────────────────→ R6 → R7
                         │
R2 ──→ R3 ──┐            │
       │    ├──→ R5 ──────┘
R2 ──→ R4 ──┘

R8 ─────────────────── (independent)
```

**Critical path**: R2 → R3 → R5 (IPC proof chain through capability hardening
and invariant completion to non-interference).

---

## 5. Detailed Phase Plans

### Phase R1: Pre-Release Blockers

**Target version**: v0.18.0
**Goal**: Eliminate all findings that enable privilege escalation or silent
security failures in the public API surface.
**Priority**: CRITICAL — these findings are pre-release blockers.
**Dependencies**: None
**Findings addressed**: H-01, M-04, M-10, M-11, R-M01, R-M02, R-M03

This phase addresses the single High-severity finding (Rust capability rights
bypass), the Lean-side API wrapper defects, and the frozen context silent
failures. These are the most urgent findings because they affect the security
boundary between userspace and kernel.

#### R1-A: Fix `Cap::downgrade()` rights bypass (H-01)

**Problem**: `Cap<Obj, Rts>::downgrade<NewRts>()` performs a phantom-type cast
without verifying that `NewRts ⊆ Rts`. A `Cap<Endpoint, ReadOnly>` can be
converted to `Cap<Endpoint, FullRights>`, bypassing the type-level capability
enforcement that the phantom-typed system is designed to provide.

**Scope**: `rust/sele4n-sys/src/cap.rs:136-143`

**Strategy**: Replace generic `downgrade()` with explicit typed conversion
methods and add a runtime subset assertion as a safety net.

**Sub-tasks**:

##### R1-A.1: Add `CapRights::RIGHTS` subset check infrastructure

Add a `const fn is_subset_of(&self, other: &AccessRightSet) -> bool` method
to `AccessRightSet` (if not already present). Add a `const fn rights_value()`
method to the `CapRights` trait to enable compile-time comparison where possible.

**Scope**: `rust/sele4n-sys/src/rights.rs`
**Gate**: `cargo build --all` succeeds, `cargo test --all` passes

##### R1-A.2: Replace `downgrade()` with explicit typed conversions

Remove the generic `downgrade<NewRts>()` method. Replace with:
- `to_read_only(self) -> Cap<Obj, ReadOnly>` (always safe — ReadOnly ⊆ anything)
- `restrict(self, mask: AccessRightSet) -> Cap<Obj, Restricted>` with runtime
  assertion that mask is a subset of current rights

Add `#[deprecated]` annotation if backward compatibility is needed for one
release cycle.

**Scope**: `rust/sele4n-sys/src/cap.rs:136-143`
**Gate**: `cargo build --all` succeeds, `cargo test --all` passes, no
compilation of `downgrade()` call sites

##### R1-A.3: Add test coverage for rights subset enforcement

Add tests:
- `test_to_read_only_always_safe` — ReadOnly from any rights succeeds
- `test_restrict_subset_succeeds` — restricting to subset succeeds
- `test_restrict_superset_panics` — restricting to superset panics in debug
- `test_cannot_upgrade_via_downgrade` — compile-time prevention of escalation

**Scope**: `rust/sele4n-sys/tests/` or `rust/sele4n-sys/src/cap.rs` (inline tests)
**Gate**: `cargo test --all` passes with new tests

**Files modified (R1-A total)**:
- `rust/sele4n-sys/src/cap.rs` — remove `downgrade()`, add typed conversions
- `rust/sele4n-sys/src/rights.rs` — add `is_subset_of` if missing
- `rust/sele4n-sys/tests/` — new test file or inline tests

**R1-A exit evidence**:
- `cargo build --all` succeeds
- `cargo test --all --features std` passes
- `rg "downgrade" rust/` returns zero call sites (or only deprecated stubs)

---

#### R1-B: Fix AccessRights and PagePerms silent truncation (R-M01, R-M02)

**Problem**: `AccessRights` and `PagePerms` decode from `u64` syscall registers
to `u8` via unchecked `as u8` cast. Values > 255 are silently truncated,
potentially masking protocol violations or enabling unintended permission
combinations.

**Scope**: `rust/sele4n-abi/src/args/cspace.rs:31`, `rust/sele4n-abi/src/args/page_perms.rs:44-46`

**Sub-tasks**:

##### R1-B.1: Add validation to `CSpaceMintArgs::decode()`

Replace `rights: AccessRights(regs[2] as u8)` with bounds-checked conversion:
```rust
if regs[2] > u8::MAX as u64 {
    return Err(KernelError::InvalidMessageInfo);
}
let rights = AccessRights(regs[2] as u8);
```

Optionally validate that only bits 0–4 are set (5 valid rights flags).

**Scope**: `rust/sele4n-abi/src/args/cspace.rs:28-35`
**Gate**: `cargo test -p sele4n-abi` passes

##### R1-B.2: Add validation to `PagePerms::from(u64)`

Replace the `From<u64>` impl with a fallible `TryFrom<u64>`:
```rust
impl TryFrom<u64> for PagePerms {
    type Error = KernelError;
    fn try_from(v: u64) -> Result<Self, Self::Error> {
        if v > 0x1F { return Err(KernelError::InvalidMessageInfo); }
        Ok(Self(v as u8))
    }
}
```

Update all call sites to use `PagePerms::try_from()` and propagate errors.

**Scope**: `rust/sele4n-abi/src/args/page_perms.rs:44-46`, call sites
**Gate**: `cargo build --all` succeeds, `cargo test --all` passes

##### R1-B.3: Add truncation regression tests

Add tests for boundary values: 0, 0x1F, 0x20, 0xFF, 0x100, u64::MAX.

**Scope**: `rust/sele4n-abi/tests/`
**Gate**: `cargo test -p sele4n-abi --features std --test conformance` passes

**Files modified (R1-B total)**:
- `rust/sele4n-abi/src/args/cspace.rs` — bounds check on rights decode
- `rust/sele4n-abi/src/args/page_perms.rs` — `TryFrom<u64>` replaces `From<u64>`
- Call sites of `PagePerms::from()` — update to `try_from()`

---

#### R1-C: Fix SyscallResponse semantic overlap (R-M03)

**Problem**: `SyscallResponse` stores both `badge: Badge` and `msg_info_raw: u64`
from the same x1 register. Callers must know which syscall was invoked to
interpret x1 correctly. The struct provides no type-level disambiguation.

**Scope**: `rust/sele4n-abi/src/decode.rs:8-16, 38-43`

**Sub-tasks**:

##### R1-C.1: Refactor `SyscallResponse` to use context-typed x1

Replace the dual-field design with a single `x1_raw: u64` field and typed
accessor methods:
```rust
pub struct SyscallResponse {
    pub error: Option<KernelError>,
    x1_raw: u64,
    pub msg_regs: [u64; 4],
}

impl SyscallResponse {
    /// Interpret x1 as IPC badge (valid for Receive/ReplyRecv syscalls).
    pub const fn badge(&self) -> Badge { Badge(self.x1_raw) }

    /// Interpret x1 as message info (valid for Send/Call/Reply syscalls).
    pub fn msg_info(&self) -> KernelResult<MessageInfo> {
        MessageInfo::decode(self.x1_raw)
    }
}
```

##### R1-C.2: Update all `SyscallResponse` consumers

Migrate callers from `resp.badge` / `resp.msg_info_raw` to `resp.badge()` /
`resp.msg_info()`. The compiler will catch all sites via missing field errors.

**Scope**: All files that reference `SyscallResponse` fields
**Gate**: `cargo build --all` succeeds, `cargo test --all` passes

**Files modified (R1-C total)**:
- `rust/sele4n-abi/src/decode.rs` — restructured `SyscallResponse`
- All consumers of `SyscallResponse` fields

---

#### R1-D: Deprecate `api*` convenience wrappers (M-04)

**Problem**: `apiEndpointSend`, `apiEndpointReceive`, `apiEndpointCall`,
`apiEndpointReply`, and `apiServiceRegister` discard the resolved capability
and accept user-supplied target IDs directly. A caller with Write capability
on endpoint A could pass `epId = B`, bypassing capability-target binding.
The authoritative `syscallEntry`/`dispatchWithCap` path (lines 399-559) is
correct.

**Scope**: `SeLe4n/Kernel/API.lean:244-321`

**Sub-tasks**:

##### R1-D.1: Mark `api*` wrappers as deprecated

Add `@[deprecated]` attributes to all five convenience wrappers. Add doc
comments directing callers to `syscallEntry`/`dispatchWithCap`.

**Scope**: `SeLe4n/Kernel/API.lean:244-321`
**Gate**: `lake build SeLe4n.Kernel.API`

##### R1-D.2: Add capability-target validation to wrappers

For each wrapper, add a guard that validates the user-supplied target ID
matches `cap.target`:
```lean
if cap.target ≠ .object epId then .error .invalidCapability
else <existing body>
```

This makes the wrappers safe even if callers continue to use them.

**Scope**: `SeLe4n/Kernel/API.lean:244-321`
**Gate**: `lake build SeLe4n.Kernel.API`, `test_smoke.sh` passes

##### R1-D.3: Update API theorem surface for validated wrappers

Add/update postcondition theorems reflecting the new guard. Existing callers
in test harnesses that rely on the old behavior must be updated.

**Scope**: `SeLe4n/Kernel/API.lean`, `SeLe4n/Testing/MainTraceHarness.lean`
**Gate**: `lake build SeLe4n.Kernel.API`, `test_smoke.sh` passes

**Files modified (R1-D total)**:
- `SeLe4n/Kernel/API.lean` — deprecation + validation guards
- `SeLe4n/Testing/MainTraceHarness.lean` — update trace calls if needed
- `tests/fixtures/main_trace_smoke.expected` — update if output changes

---

#### R1-E: Fix frozen context save/restore silent failures (M-10, M-11)

**Problem**: `frozenSaveOutgoingContext` silently discards registers when the
current thread's ObjId is missing from the frozen map. `frozenRestoreIncomingContext`
silently returns the previous thread's register context when the incoming
thread is missing. Both should return explicit errors.

**Scope**: `SeLe4n/Kernel/FrozenOps/Core.lean:130-149`

**Sub-tasks**:

##### R1-E.1: Change return type to `Except KernelError FrozenSystemState`

Update both functions to return `Except KernelError FrozenSystemState`:

For `frozenSaveOutgoingContext`:
```lean
def frozenSaveOutgoingContext (st : FrozenSystemState)
    : Except KernelError FrozenSystemState :=
  match st.scheduler.current with
  | none => .ok st
  | some outTid =>
      match st.objects.get? outTid.toObjId with
      | some (.tcb outTcb) =>
          let obj := FrozenKernelObject.tcb { outTcb with registerContext := st.machine.regs }
          match st.objects.set outTid.toObjId obj with
          | some objects' => .ok { st with objects := objects' }
          | none => .error .objectNotFound
      | _ => .error .objectNotFound
```

Apply the same pattern to `frozenRestoreIncomingContext`.

**Scope**: `SeLe4n/Kernel/FrozenOps/Core.lean:130-149`
**Gate**: `lake build SeLe4n.Kernel.FrozenOps.Core`

##### R1-E.2: Update all callers in FrozenOps/Operations.lean

Every caller that chains `frozenSaveOutgoingContext` or
`frozenRestoreIncomingContext` must handle the `Except` return. Update the
12 per-subsystem frozen operations.

**Scope**: `SeLe4n/Kernel/FrozenOps/Operations.lean`
**Gate**: `lake build SeLe4n.Kernel.FrozenOps.Operations`

##### R1-E.3: Update preservation theorems in FrozenOps/Invariant.lean

The `frozenStoreObject` preservation theorems may need updating to account
for the new error paths. Add theorems:
- `frozenSaveOutgoingContext_error_preserves_state` — error case returns
  original state unchanged
- `frozenSaveOutgoingContext_success_preserves_invExt` — success case
  preserves `invExt`

**Scope**: `SeLe4n/Kernel/FrozenOps/Invariant.lean`
**Gate**: `lake build SeLe4n.Kernel.FrozenOps.Invariant`, `test_smoke.sh`

**Files modified (R1-E total)**:
- `SeLe4n/Kernel/FrozenOps/Core.lean` — return type change
- `SeLe4n/Kernel/FrozenOps/Operations.lean` — caller updates
- `SeLe4n/Kernel/FrozenOps/Invariant.lean` — new preservation theorems
- `SeLe4n/Kernel/FrozenOps/Commutativity.lean` — if affected by type change

---

#### R1-F: Update test fixtures and documentation

**Problem**: R1 changes modify visible output from trace harness and Rust
conformance tests. Fixtures must be updated atomically with the code changes.

**Sub-tasks**:

##### R1-F.1: Regenerate `main_trace_smoke.expected`

Run `lake exe sele4n` and capture output to update the expected fixture
if any output changes from R1-D (API wrapper changes).

**Scope**: `tests/fixtures/main_trace_smoke.expected`
**Gate**: `test_smoke.sh` passes

##### R1-F.2: Update Rust conformance tests

Ensure `cargo test -p sele4n-abi --features std --test conformance` passes
with the new `TryFrom<u64>` conversions and `SyscallResponse` restructure.

**Scope**: `rust/sele4n-abi/tests/conformance.rs`
**Gate**: `cargo test --all --features std` passes

##### R1-F.3: Regenerate `codebase_map.json`

Run `python3 scripts/generate_codebase_map.py --pretty` to update the
codebase map with any new files or changed line counts.

**Scope**: `docs/codebase_map.json`
**Gate**: `test_full.sh` passes

**R1 phase exit evidence**:
- `lake build` succeeds with zero warnings
- `cargo build --all` succeeds
- `test_smoke.sh` passes
- `cargo test --all --features std` passes
- `rg "downgrade" rust/sele4n-sys/src/cap.rs` returns zero unguarded sites
- No `sorry`/`axiom` in any modified file

---

### Phase R2: Capability & CDT Hardening

**Target version**: v0.18.1
**Goal**: Eliminate silent failure paths in capability revocation and close
CDT consistency/acyclicity proof gaps.
**Priority**: HIGH — revocation soundness is a security-critical property.
**Dependencies**: None (parallel with R1)
**Findings addressed**: M-05, M-06, M-07, M-08, L-07

Capability revocation is the kernel's primary mechanism for revoking authority.
Two findings (M-05, M-06) show that revocation can silently leave capabilities
alive. Two model-layer findings (M-07, M-08) show that CDT remove operations
and acyclicity proofs are incomplete. This phase closes all four.

**Intra-phase ordering**:
```
R2-A, R2-B ──→ R2-F (preservation updates need new return types)
R2-C ──→ R2-D (acyclicity uses consistency lemmas)
R2-C, R2-D ──→ R2-E (postconditions use consistency + acyclicity)
R2-F, R2-E ──→ R2-G (tests verify final behavior)
```

#### R2-A: Fix `processRevokeNode` error swallowing (M-06)

**Problem**: When `cspaceDeleteSlot` fails for a CDT descendant, the CDT node
is removed but the capability persists in the CNode. The capability survives
CDT revocation.

**Scope**: `SeLe4n/Kernel/Capability/Operations.lean:723-731`

Current code:
```lean
| .error _ => { st with cdt := st.cdt.removeNode node }
```

**Strategy**: Propagate the error instead of swallowing it. The existing
`cspaceRevokeCdtStrict` variant already exists for callers requiring error
visibility — make this the default behavior.

**Sub-tasks**:

##### R2-A.1: Change `processRevokeNode` return type to `Except KernelError SystemState`

```lean
def processRevokeNode (st : SystemState) (node : CdtNodeId)
    : Except KernelError SystemState :=
  match SystemState.lookupCdtSlotOfNode st node with
  | none => .ok { st with cdt := st.cdt.removeNode node }
  | some descAddr =>
      match cspaceDeleteSlot descAddr st with
      | .error e => .error e
      | .ok ((), stDel) =>
          let stDetached := SystemState.detachSlotFromCdt stDel descAddr
          .ok { stDetached with cdt := stDetached.cdt.removeNode node }
```

**Scope**: `SeLe4n/Kernel/Capability/Operations.lean:723-731`
**Gate**: `lake build SeLe4n.Kernel.Capability.Operations`

##### R2-A.2: Update `cspaceRevokeCdt` to propagate errors

Update the `foldl` in `cspaceRevokeCdt` (line 762-766) to propagate errors
from the now-fallible `processRevokeNode`:
```lean
let result := descendants.foldl (fun acc node =>
  match acc with
  | .error e => .error e
  | .ok ((), stAcc) =>
      match processRevokeNode stAcc node with
      | .error e => .error e
      | .ok stRevoked => .ok ((), stRevoked)
) (.ok ((), stLocal))
```

**Scope**: `SeLe4n/Kernel/Capability/Operations.lean:751-767`
**Gate**: `lake build SeLe4n.Kernel.Capability.Operations`

##### R2-A.3: Preserve legacy `processRevokeNode_lenient` for backward compatibility

Rename the old swallowing version to `processRevokeNode_lenient` with a
deprecation notice. Existing callers that explicitly want lenient behavior
can migrate to this variant.

**Scope**: `SeLe4n/Kernel/Capability/Operations.lean`
**Gate**: `lake build SeLe4n.Kernel.Capability.Operations`

---

#### R2-B: Fix `streamingRevokeBFS` fuel exhaustion (M-05)

**Problem**: When fuel is exhausted with a non-empty BFS queue,
`streamingRevokeBFS` returns `.ok` with potentially un-revoked descendants.

**Scope**: `SeLe4n/Kernel/Capability/Operations.lean:784-792`

Current code:
```lean
| 0, _ :: _ => .ok ((), st)  -- fuel exhausted (safety bound)
```

**Sub-tasks**:

##### R2-B.1: Return error on fuel exhaustion

```lean
| 0, _ :: _ => .error .resourceExhausted
```

This makes fuel exhaustion an explicit failure that callers must handle.

**Scope**: `SeLe4n/Kernel/Capability/Operations.lean:789`
**Gate**: `lake build SeLe4n.Kernel.Capability.Operations`

##### R2-B.2: Update `streamingRevokeCdt` caller

The wrapper `streamingRevokeCdt` (around line 800) must propagate the
`.resourceExhausted` error to its callers instead of treating it as success.

**Scope**: `SeLe4n/Kernel/Capability/Operations.lean:794-820`
**Gate**: `lake build SeLe4n.Kernel.Capability.Operations`

##### R2-B.3: Add fuel exhaustion test case

Add a negative test case in `tests/NegativeStateSuite.lean` that verifies
fuel exhaustion returns an error, not success.

**Scope**: `tests/NegativeStateSuite.lean`
**Gate**: `lake build tests.NegativeStateSuite`, `test_smoke.sh`

---

#### R2-C: Prove CDT remove consistency (M-07)

**Problem**: CDT maintains triple redundancy (edges, childMap, parentMap).
Consistency is proven for `addEdge` but NOT for `removeAsChild`/`removeAsParent`.

**Scope**: `SeLe4n/Model/Object/Structures.lean:838-859`

**Sub-tasks**:

##### R2-C.1: Prove `removeAsChild_preserves_cdtTripleConsistency`

Prove that `removeAsChild` preserves the `cdtTripleConsistency` predicate —
i.e., after removing a child relationship, `edges`, `childMap`, and `parentMap`
remain mutually consistent.

The proof strategy mirrors `addEdge_preserves_cdtTripleConsistency`:
1. Show `childMap` and `parentMap` updates correspond to edge removal
2. Show no other edges are affected (frame lemma)
3. Compose with existing consistency predicate

**Scope**: `SeLe4n/Model/Object/Structures.lean` (new theorem ~40 lines)
**Gate**: `lake build SeLe4n.Model.Object.Structures`

##### R2-C.2: Prove `removeAsParent_preserves_cdtTripleConsistency`

Same pattern as R2-C.1 but for parent-side removal.

**Scope**: `SeLe4n/Model/Object/Structures.lean` (new theorem ~40 lines)
**Gate**: `lake build SeLe4n.Model.Object.Structures`

##### R2-C.3: Add composition theorem `removeEdge_preserves_cdtTripleConsistency`

Compose R2-C.1 and R2-C.2 into a single theorem covering full edge removal
(which calls both `removeAsChild` and `removeAsParent`).

**Scope**: `SeLe4n/Model/Object/Structures.lean` (new theorem ~20 lines)
**Gate**: `lake build SeLe4n.Model.Object.Structures`

---

#### R2-D: Extend CDT acyclicity beyond fresh nodes (M-08)

**Problem**: `addEdge_preserves_edgeWellFounded_fresh` requires the child node
to be completely new. The general case (adding an edge between two existing
nodes) is not proven.

**Scope**: `SeLe4n/Model/Object/Structures.lean:964-968`

**Sub-tasks**:

##### R2-D.1: Prove `addEdge_preserves_edgeWellFounded_general`

Prove that `addEdge parent child` preserves well-foundedness when:
1. `child` is not an ancestor of `parent` in the current CDT (no cycle)
2. `child` has no existing parent (single-parent invariant)

The proof uses the existing `edgeWellFounded` definition and extends the
freshness argument to a general no-ancestor check.

**Scope**: `SeLe4n/Model/Object/Structures.lean` (new theorem ~60 lines)
**Gate**: `lake build SeLe4n.Model.Object.Structures`

##### R2-D.2: Add `isAncestor` decidable predicate

Add a decidable predicate `isAncestor (cdt : CDT) (ancestor child : CdtNodeId) : Bool`
that performs DFS upward through parent edges to check reachability. Prove
termination via well-foundedness of the existing CDT.

**Scope**: `SeLe4n/Model/Object/Structures.lean` (new definition + termination proof ~30 lines)
**Gate**: `lake build SeLe4n.Model.Object.Structures`

---

#### R2-E: Close CDT postconditions for copy/move/mint (L-07)

**Problem**: `cspaceCopy`, `cspaceMove`, and `cspaceMint` have CDT postconditions
deferred to callers. These should be proven at the operation level.

**Scope**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean`

**Sub-tasks**:

##### R2-E.1: Prove `cspaceCopy_preserves_cdtCompleteness`

Prove that `cspaceCopy` preserves CDT completeness — every slot with a
capability has a corresponding CDT node.

**Scope**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean` (~50 lines)
**Gate**: `lake build SeLe4n.Kernel.Capability.Invariant.Preservation`

##### R2-E.2: Prove `cspaceMint_preserves_cdtCompleteness`

Same pattern for `cspaceMint`.

**Scope**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean` (~50 lines)
**Gate**: `lake build SeLe4n.Kernel.Capability.Invariant.Preservation`

##### R2-E.3: Prove `cspaceMove_preserves_cdtCompleteness`

Same pattern for `cspaceMove`. Move is more complex because it must also prove
the source slot's CDT node is cleaned up.

**Scope**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean` (~60 lines)
**Gate**: `lake build SeLe4n.Kernel.Capability.Invariant.Preservation`

---

#### R2-F: Update capability invariant preservation proofs

**Problem**: The return type changes in R2-A and R2-B cascade into preservation
theorems that pattern-match on `processRevokeNode` and `streamingRevokeBFS`
return values.

**Sub-tasks**:

##### R2-F.1: Update revocation preservation theorems

Update all theorems in `Capability/Invariant/Preservation.lean` that reference
`processRevokeNode` or `streamingRevokeBFS` to handle the new `Except` return
types.

**Scope**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean`
**Gate**: `lake build SeLe4n.Kernel.Capability.Invariant.Preservation`

##### R2-F.2: Add fuel exhaustion preservation theorem

Prove that when `streamingRevokeBFS` returns `.error .resourceExhausted`,
the state is unchanged from the input state (error-state preservation).

**Scope**: `SeLe4n/Kernel/Capability/Invariant/Preservation.lean` (~30 lines)
**Gate**: `lake build SeLe4n.Kernel.Capability.Invariant.Preservation`

---

#### R2-G: Test suite updates

##### R2-G.1: Add revocation error propagation tests

Add test cases to `tests/NegativeStateSuite.lean` verifying:
- `processRevokeNode` returns error on failed delete
- `streamingRevokeBFS` returns error on fuel exhaustion
- `cspaceRevokeCdt` propagates descendant delete failures

**Scope**: `tests/NegativeStateSuite.lean`
**Gate**: `test_smoke.sh` passes

**R2 phase exit evidence**:
- `lake build` succeeds
- `test_full.sh` passes (theorem changes)
- All CDT consistency/acyclicity theorems compile without `sorry`
- Revocation error paths verified in negative test suite
- No `sorry`/`axiom` in any modified file

---

### Phase R3: IPC Invariant Completion

**Target version**: v0.18.2
**Goal**: Internalize externalized IPC invariant hypotheses and fix the
notification badge delivery gap.
**Priority**: HIGH — IPC is the primary cross-domain communication mechanism.
**Dependencies**: R2 (CDT consistency proofs feed into IPC preservation chain)
**Findings addressed**: M-16, M-18, M-19, L-05, L-08

The IPC subsystem has the largest concentration of deferred proof obligations.
Three findings show composition theorems that accept critical invariant
components as external hypotheses rather than proving them from pre-state
conditions. One finding shows a functional gap (badge not delivered on
notification wake).

#### R3-A: Fix `notificationSignal` badge delivery (M-16)

**Problem**: When waking a waiter via `notificationSignal`, the signaled badge
is not delivered to the woken thread. In seL4, the badge from `Signal` is
delivered as the return value of the waiter's `Wait` syscall. Here it is
discarded.

**Scope**: `SeLe4n/Kernel/IPC/Operations/Endpoint.lean:155-172`

**Sub-tasks**:

##### R3-A.1: Deliver badge to woken thread via TCB IPC state

After waking the waiter (line 170-172), store the badge in the waiter's TCB
IPC state so the receive path can return it:

```lean
| .ok ((), st') =>
    match storeTcbIpcStateAndMessage st' waiter .ready
        { msg with badge := some badge } with
    | .error e => .error e
    | .ok st'' => .ok ((), ensureRunnable st'' waiter)
```

If `storeTcbIpcStateAndMessage` does not exist, use `storeTcbIpcState` +
a separate register/badge store operation.

**Scope**: `SeLe4n/Kernel/IPC/Operations/Endpoint.lean:170-172`
**Gate**: `lake build SeLe4n.Kernel.IPC.Operations.Endpoint`

##### R3-A.2: Update notification preservation proofs

The badge delivery changes the post-state TCB content. Update:
- `notificationSignal_preserves_ipcInvariant`
- `notificationSignal_preserves_notificationWaiterConsistent` (if it exists)
- Badge-related frame lemmas

**Scope**: `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation.lean`
**Gate**: `lake build SeLe4n.Kernel.IPC.Invariant.NotificationPreservation`

##### R3-A.3: Add badge delivery test

Add a trace test that signals a notification with badge B, then verifies the
woken thread receives badge B in its registers/IPC state.

**Scope**: `tests/NegativeStateSuite.lean` or `SeLe4n/Testing/MainTraceHarness.lean`
**Gate**: `test_smoke.sh` passes

---

#### R3-B: Internalize `dualQueueSystemInvariant` preservation (M-18)

**Problem**: `endpointSendDual_preserves_ipcInvariantFull` and
`endpointReceiveDual_preserves_ipcInvariantFull` accept
`dualQueueSystemInvariant st'`, `allPendingMessagesBounded st'`, and
`badgeWellFormed st'` as external hypotheses on the post-state.

**Scope**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean:2385-2407`

**Sub-tasks**:

##### R3-B.1: Prove `endpointSendDual_preserves_dualQueueSystemInvariant`

Prove that `endpointSendDual` preserves `dualQueueSystemInvariant` from
pre-state invariant + step witness. The key insight is that send enqueues
a message in the sender queue, which maintains dual-queue disjointness
because the sender was not previously in the receiver queue.

**Scope**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean` or new file
  `SeLe4n/Kernel/IPC/Invariant/DualQueuePreservation.lean` (~80 lines)
**Gate**: `lake build` succeeds for the module

##### R3-B.2: Prove `endpointSendDual_preserves_allPendingMessagesBounded`

Prove that the message stored by `endpointSendDual` satisfies the bounds
predicate. The bounds check at the entry point ensures `msg` satisfies
`bounded`; the proof lifts this to the stored message.

**Scope**: Same file as R3-B.1 (~40 lines)
**Gate**: `lake build` succeeds

##### R3-B.3: Prove `endpointSendDual_preserves_badgeWellFormed`

Prove badge well-formedness preservation. Badge is either unchanged or
comes from a well-formed capability badge (proven at mint time).

**Scope**: Same file as R3-B.1 (~30 lines)
**Gate**: `lake build` succeeds

##### R3-B.4: Compose into self-contained `ipcInvariantFull` preservation

Replace the externalized theorems with self-contained versions that derive
all four components from pre-state invariants:

```lean
theorem endpointSendDual_preserves_ipcInvariantFull
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ⟨endpointSendDual_preserves_ipcInvariant ...,
   endpointSendDual_preserves_dualQueueSystemInvariant ...,
   endpointSendDual_preserves_allPendingMessagesBounded ...,
   endpointSendDual_preserves_badgeWellFormed ...⟩
```

Rename the old versions with `_externalized` suffix for backward compatibility.

**Scope**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean:2385-2407`
**Gate**: `lake build SeLe4n.Kernel.IPC.Invariant.Structural`

##### R3-B.5: Repeat for `endpointReceiveDual`, `endpointCall`, `endpointReplyRecv`

Apply the same pattern to the remaining three IPC operations that have
externalized hypotheses (lines 2397-2411+).

**Scope**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Gate**: `lake build SeLe4n.Kernel.IPC.Invariant.Structural`

---

#### R3-C: Complete `notificationWaiterConsistent` preservation (M-19)

**Problem**: `notificationWaiterConsistent` preservation through
`notificationSignal`, endpoint operations, and lifecycle transitions is
deferred (comment references "WS-G7+").

**Scope**: `SeLe4n/Kernel/IPC/Invariant/Defs.lean:576-610`

**Sub-tasks**:

##### R3-C.1: Prove preservation through `notificationSignal`

The key property: after signaling, the woken thread is removed from the
notification's waiting list. The remaining waiters are still consistent
(they were consistent before, and only the head was removed).

**Scope**: `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation.lean` (~60 lines)
**Gate**: `lake build SeLe4n.Kernel.IPC.Invariant.NotificationPreservation`

##### R3-C.2: Prove preservation through endpoint operations

Endpoint send/receive/call/replyRecv do not modify notification state.
The proof is a frame argument: notification objects are untouched by
endpoint operations, so waiter consistency is trivially preserved.

**Scope**: `SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean` (~40 lines)
**Gate**: `lake build SeLe4n.Kernel.IPC.Invariant.EndpointPreservation`

##### R3-C.3: Prove preservation through lifecycle transitions

TCB retype must ensure the retyped thread is not in any notification's
waiting list (or is cleaned up). This depends on R4-A (endpoint queue
cleanup in `cleanupTcbReferences`).

**Scope**: `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation.lean` (~50 lines)
**Gate**: `lake build SeLe4n.Kernel.IPC.Invariant.NotificationPreservation`
**Note**: R3-C.3 has a soft dependency on R4-A (endpoint queue cleanup).
**Recommended execution order**: complete R4-A before R3-C.3 so the cleanup
guarantee is available as a proved lemma. If R3 and R4 execute in parallel,
R3-C.3 should accept the cleanup hypothesis externally and be internalized
when R5 unifies the proof chains. This does not change the phase dependency
graph — R3 and R4 remain independently schedulable from R2.

---

#### R3-D: Add `IpcMessage` structural bounds (L-05)

**Problem**: `IpcMessage` arrays lack structural bounds. The `caps` and
`extraCaps` fields have unbounded `List` types, but hardware and protocol
impose limits (seL4 uses 4 message registers and 3 extra caps).

**Sub-tasks**:

##### R3-D.1: Add bounds predicate `ipcMessageBounded`

Define:
```lean
def ipcMessageBounded (msg : IpcMessage) : Prop :=
  msg.msgRegs.length ≤ maxMsgRegs ∧
  msg.extraCaps.length ≤ maxExtraCaps
```

where `maxMsgRegs := 4` and `maxExtraCaps := 3` match seL4 constants.

**Scope**: `SeLe4n/Model/Object/Types.lean` (~15 lines)
**Gate**: `lake build SeLe4n.Model.Object.Types`

##### R3-D.2: Thread bounds predicate into `allPendingMessagesBounded`

Ensure `allPendingMessagesBounded` includes `ipcMessageBounded` for each
pending message. This may already be partially done; verify and extend.

**Scope**: `SeLe4n/Kernel/IPC/Invariant/Defs.lean`
**Gate**: `lake build SeLe4n.Kernel.IPC.Invariant.Defs`

---

#### R3-E: Remove `set_option linter.all false` from Structural.lean (L-08)

**Problem**: The 2440-line `Structural.lean` disables all linters. This masks
potential issues in proof code.

**Sub-tasks**:

##### R3-E.1: Remove `set_option linter.all false` and fix linter warnings

Remove the directive and address each linter warning individually. Common
fixes include:
- Adding explicit `@[simp]` annotations
- Removing unused variables
- Adding type annotations to `fun` parameters

**Scope**: `SeLe4n/Kernel/IPC/Invariant/Structural.lean`
**Gate**: `lake build SeLe4n.Kernel.IPC.Invariant.Structural` with zero warnings

---

#### R3-F: Documentation and test updates

##### R3-F.1: Update IPC proof map in documentation

Update `docs/gitbook/12-proof-and-invariant-map.md` to reflect internalized
hypotheses and new preservation theorems.

**Scope**: `docs/gitbook/12-proof-and-invariant-map.md`
**Gate**: `test_full.sh` passes

**R3 phase exit evidence**:
- `lake build` succeeds
- `test_full.sh` passes (theorem changes)
- `rg "hDualQueue'" SeLe4n/Kernel/IPC/Invariant/Structural.lean` returns
  zero externalized hypothesis parameters
- Notification badge delivery verified in test suite
- No `sorry`/`axiom` in any modified file

---

### Phase R4: Lifecycle & Service Coherence

**Target version**: v0.18.3
**Goal**: Establish cross-subsystem invariant preservation between lifecycle,
service registry, and IPC subsystems.
**Priority**: HIGH — cross-subsystem gaps enable invariant violations that
no single subsystem can detect.
**Dependencies**: R2 (capability hardening provides CDT consistency for
service revocation)
**Findings addressed**: M-12, M-13, M-14, M-15, L-09

The four Medium findings in this phase all relate to the same architectural
gap: kernel subsystems operate independently with limited cross-boundary
invariant enforcement. Lifecycle retype can invalidate service registrations
and leave stale IPC queue references. Service registration has no capability
authority check and revocation does not clean the dependency graph.

#### R4-A: Add IPC endpoint queue cleanup to `cleanupTcbReferences` (M-12)

**Problem**: `cleanupTcbReferences` removes a TCB from the scheduler run
queue but not from endpoint send/receive queues or notification waiting
lists. After TCB retype, stale `ThreadId` entries persist in IPC queues.

**Scope**: `SeLe4n/Kernel/Lifecycle/Operations.lean:37-38`

Current code:
```lean
def cleanupTcbReferences (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  removeRunnable st tid
```

**Sub-tasks**:

##### R4-A.1: Add `removeFromAllEndpointQueues` helper

Define a function that iterates over all endpoint objects in `st.objects`
and removes `tid` from both sender and receiver queues:

```lean
def removeFromAllEndpointQueues (st : SystemState) (tid : SeLe4n.ThreadId)
    : SystemState :=
  st.objects.fold (init := st) fun acc objId obj =>
    match obj with
    | .endpoint ep =>
        if ep.senderQueue.contains tid || ep.receiverQueue.contains tid then
          let ep' := { ep with
            senderQueue := ep.senderQueue.filter (· ≠ tid)
            receiverQueue := ep.receiverQueue.filter (· ≠ tid) }
          match storeObject objId (.endpoint ep') acc with
          | .ok ((), acc') => acc'
          | .error _ => acc  -- object existed in fold source; store should not fail
        else acc
    | _ => acc
```

**Design note**: The `storeObject` fallback returns `acc` unchanged. This is
safe because the fold iterates objects already in the map, so `storeObject`
should always succeed. A future refinement could prove this invariant.

**Scope**: `SeLe4n/Kernel/Lifecycle/Operations.lean` (~20 lines)
**Gate**: `lake build SeLe4n.Kernel.Lifecycle.Operations`

##### R4-A.2: Add `removeFromAllNotificationWaitLists` helper

Same pattern for notification objects:

```lean
def removeFromAllNotificationWaitLists (st : SystemState)
    (tid : SeLe4n.ThreadId) : SystemState :=
  st.objects.fold (init := st) fun acc objId obj =>
    match obj with
    | .notification ntfn =>
        let ntfn' := { ntfn with
          waitingThreads := ntfn.waitingThreads.filter (· ≠ tid) }
        match storeObject objId (.notification ntfn') acc with
        | .ok ((), acc') => acc'
        | .error _ => acc
    | _ => acc
```

**Scope**: `SeLe4n/Kernel/Lifecycle/Operations.lean` (~20 lines)
**Gate**: `lake build SeLe4n.Kernel.Lifecycle.Operations`

##### R4-A.3: Compose into `cleanupTcbReferences`

```lean
def cleanupTcbReferences (st : SystemState) (tid : SeLe4n.ThreadId)
    : SystemState :=
  let st1 := removeRunnable st tid
  let st2 := removeFromAllEndpointQueues st1 tid
  removeFromAllNotificationWaitLists st2 tid
```

**Scope**: `SeLe4n/Kernel/Lifecycle/Operations.lean:37-38`
**Gate**: `lake build SeLe4n.Kernel.Lifecycle.Operations`

##### R4-A.4: Prove `cleanupTcbReferences_removes_from_endpoints`

Prove that after cleanup, `tid` does not appear in any endpoint's sender
or receiver queue.

**Scope**: `SeLe4n/Kernel/Lifecycle/Operations.lean` (~40 lines)
**Gate**: `lake build SeLe4n.Kernel.Lifecycle.Operations`

##### R4-A.5: Update existing `cleanupTcbReferences` theorems

The existing `cleanupTcbReferences_removes_from_runnable` and
`cleanupTcbReferences_preserves_runnable_ne` theorems remain valid but
their proofs need updating to account for the new intermediate states.

**Scope**: `SeLe4n/Kernel/Lifecycle/Operations.lean:41-49`
**Gate**: `lake build SeLe4n.Kernel.Lifecycle.Operations`

---

#### R4-B: Add lifecycle/service cross-subsystem guard (M-13)

**Problem**: Retyping an endpoint that backs a registered service does not
revoke the service registration. `registryEndpointValid` would be violated.

**Scope**: `SeLe4n/Kernel/Lifecycle/Operations.lean`, `SeLe4n/Kernel/Service/Registry.lean`

**Sub-tasks**:

##### R4-B.1: Add `cleanupEndpointServiceRegistrations` helper

Before retyping an endpoint object, revoke all service registrations that
reference it:

```lean
def cleanupEndpointServiceRegistrations (st : SystemState)
    (epId : SeLe4n.ObjId) : SystemState :=
  let toRevoke := st.serviceRegistry.fold (init := []) fun acc sid reg =>
    match reg.endpointCap.target with
    | .object id => if id == epId then sid :: acc else acc
    | _ => acc
  toRevoke.foldl (fun acc sid =>
    { acc with serviceRegistry := acc.serviceRegistry.erase sid }) st
```

**Scope**: `SeLe4n/Kernel/Service/Registry.lean` (~15 lines)
**Gate**: `lake build SeLe4n.Kernel.Service.Registry`

##### R4-B.2: Integrate into retype path

Call `cleanupEndpointServiceRegistrations` from the retype entry point
when the source object is an endpoint:

**Scope**: `SeLe4n/Kernel/Lifecycle/Operations.lean`
**Gate**: `lake build SeLe4n.Kernel.Lifecycle.Operations`

##### R4-B.3: Prove `registryEndpointValid` preservation through retype

Prove that after cleanup + retype, `registryEndpointValid` holds —
every registered service's endpoint still exists in `st.objects`.

**Scope**: `SeLe4n/Kernel/Service/Invariant/Policy.lean` (~40 lines)
**Gate**: `lake build SeLe4n.Kernel.Service.Invariant.Policy`

---

#### R4-C: Add capability authority check to `registerService` (M-14)

**Problem**: `registerService` allows any caller to register any endpoint
as a service without holding the endpoint capability or verifying rights.

**Scope**: `SeLe4n/Kernel/Service/Registry.lean:53-67`

**Sub-tasks**:

##### R4-C.1: Add capability lookup and rights check

Before registering, verify the caller holds a capability targeting the
endpoint with at least Write rights:

```lean
def registerService (reg : ServiceRegistration) (callerCNode : ObjId)
    : Kernel Unit :=
  fun st =>
    -- Verify caller holds capability to endpoint with Write rights
    match st.objects[callerCNode]? with
    | some (.cnode cn) =>
        let hasCap := cn.slots.any fun _ cap =>
          cap.target == .object reg.endpointCap.target.toObjId &&
          Capability.hasRight cap .write
        if !hasCap then .error .invalidCapability
        else <existing registration logic>
    | _ => .error .invalidCapability
```

**Scope**: `SeLe4n/Kernel/Service/Registry.lean:53-67`
**Gate**: `lake build SeLe4n.Kernel.Service.Registry`

##### R4-C.2: Add endpoint object type verification (L-09)

Verify the target object actually is an endpoint, not just that it exists:

```lean
match st.objects[epId]? with
| some (.endpoint _) => <proceed>
| _ => .error .invalidCapability
```

**Scope**: `SeLe4n/Kernel/Service/Registry.lean:62-63`
**Gate**: `lake build SeLe4n.Kernel.Service.Registry`

##### R4-C.3: Update API wrappers and callers

Update `apiServiceRegister` and `dispatchWithCap` service path to pass
the caller's CNode ID. Update test harness fixtures.

**Scope**: `SeLe4n/Kernel/API.lean`, `SeLe4n/Testing/MainTraceHarness.lean`
**Gate**: `lake build SeLe4n.Kernel.API`, `test_smoke.sh`

---

#### R4-D: Fix `revokeService` dependency graph cleanup (M-15)

**Problem**: `revokeService` removes the service registration but leaves
dependency graph entries that reference the revoked service, causing
inconsistency between the service registry and dependency graph.

**Scope**: `SeLe4n/Kernel/Service/Registry.lean:87-93`

**Sub-tasks**:

##### R4-D.1: Add dependency graph cleanup to `revokeService`

After erasing from `serviceRegistry`, clean the dependency graph:

```lean
def revokeService (sid : ServiceId) : Kernel Unit :=
  fun st =>
    if st.serviceRegistry[sid]? = none then
      .error .objectNotFound
    else
      let st' := { st with
        serviceRegistry := st.serviceRegistry.erase sid
        serviceDependencyGraph :=
          st.serviceDependencyGraph.removeDependenciesOf sid }
      .ok ((), st')
```

**Scope**: `SeLe4n/Kernel/Service/Registry.lean:87-93`
**Gate**: `lake build SeLe4n.Kernel.Service.Registry`

##### R4-D.2: Add `removeDependenciesOf` to dependency graph

If `removeDependenciesOf` does not exist, add it to the dependency graph
type. It should remove all edges where `sid` appears as either source or
target.

**Scope**: `SeLe4n/Kernel/Service/` (graph module)
**Gate**: `lake build` for the module

##### R4-D.3: Prove `revokeService_preserves_acyclicity`

Prove that removing a node and its edges preserves acyclicity.
Edge removal from a DAG always preserves acyclicity (monotonicity).

**Scope**: `SeLe4n/Kernel/Service/Invariant/Acyclicity.lean` (~30 lines)
**Gate**: `lake build SeLe4n.Kernel.Service.Invariant.Acyclicity`

##### R4-D.4: Prove `revokeService_preserves_registryDependencyConsistency`

Prove that after revocation, every dependency graph edge references
services that still exist in the registry.

**Scope**: `SeLe4n/Kernel/Service/Invariant/Policy.lean` (~40 lines)
**Gate**: `lake build SeLe4n.Kernel.Service.Invariant.Policy`

---

#### R4-E: Cross-subsystem invariant composition

##### R4-E.1: Define `crossSubsystemInvariant`

Create a top-level invariant that composes service, lifecycle, and IPC
cross-boundary consistency:

```lean
def crossSubsystemInvariant (st : SystemState) : Prop :=
  registryEndpointValid st ∧
  registryDependencyConsistent st ∧
  noStaleEndpointQueueReferences st
```

**Scope**: `SeLe4n/Kernel/API.lean` or new file `SeLe4n/Kernel/CrossSubsystem.lean`
**Gate**: `lake build` for the module

##### R4-E.2: Add to `apiInvariantBundle`

Thread `crossSubsystemInvariant` into the top-level invariant bundle so
it is checked at every kernel entry/exit point.

**Scope**: `SeLe4n/Kernel/API.lean`
**Gate**: `lake build SeLe4n.Kernel.API`, `test_full.sh`

---

#### R4-F: Test and documentation updates

##### R4-F.1: Add cross-subsystem negative tests

Test scenarios:
- Retype endpoint → verify service registration auto-revoked
- Register service without capability → verify error
- Revoke service → verify dependency graph cleaned

**Scope**: `tests/NegativeStateSuite.lean`
**Gate**: `test_smoke.sh` passes

##### R4-F.2: Update documentation

Update `docs/spec/SELE4N_SPEC.md` service registry section and
`docs/gitbook/12-proof-and-invariant-map.md`.

**Scope**: `docs/spec/SELE4N_SPEC.md`, `docs/gitbook/12-proof-and-invariant-map.md`
**Gate**: `test_full.sh` passes

**R4 phase exit evidence**:
- `lake build` succeeds
- `test_full.sh` passes
- `rg "cleanupTcbReferences" Lifecycle/Operations.lean` shows endpoint + notification cleanup
- Service registration requires capability authority
- Dependency graph cleaned on revocation
- No `sorry`/`axiom` in any modified file

---

### Phase R5: Information Flow Completion

**Target version**: v0.18.4
**Goal**: Close the IPC non-interference proof gap, add service operation
to NI composition, and strengthen memory projection.
**Priority**: HIGH — IPC NI is the most significant proof gap in the audit.
**Dependencies**: R3 (IPC invariant internalization), R4 (service coherence
for `registerServiceChecked` NI)
**Findings addressed**: M-01, M-02, M-03

This is the most technically challenging phase. The four deferred IPC
non-interference proofs (M-01) are the audit's most significant finding.
Completing them requires the dual-queue decomposition lemmas referenced
in the code comments, which in turn depend on the IPC invariant
internalization from R3.

**Intra-phase ordering**:
```
R5-A.1 (decomposition lemma) ──→ R5-A.2 (send NI) ──→ R5-A.4 (call/reply NI)
                                 R5-A.3 (recv NI) ──→ R5-A.4
R5-A.2..A.4 ──→ R5-A.5 (remove hypothesis parameters)
R5-B (service NI) — independent of R5-A
R5-C (memory projection) — independent of R5-A, R5-B
R5-A.5, R5-B.3, R5-C.3 ──→ R5-D (composition update) ──→ R5-E (docs)
```

#### R5-A: Complete IPC non-interference proofs (M-01)

**Problem**: The non-interference proofs for `endpointSendDual`,
`endpointReceiveDual`, `endpointCall`, and `endpointReplyRecv` accept
their NI property as a **hypothesis parameter** (`hSendDualNI`, etc.)
rather than proving it compositionally. These are the most
security-critical operations in the kernel.

**Scope**: `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean:85-98, 1155-1228`

**Strategy**: The dual-queue architecture is designed so that high-security
sends only modify the sender queue, which is projected away for low observers.
The proof strategy is:

1. Show `endpointSendDual` only modifies the endpoint object and the sender TCB
2. Show that if both the endpoint and sender are high-security (not observable),
   the modification is invisible to the observer
3. Compose with the `projectState` frame lemma

**Sub-tasks**:

##### R5-A.1: Prove dual-queue decomposition lemma for send

Prove that `endpointSendDual` modifies exactly two objects: the endpoint
(enqueue sender) and the sender TCB (set IPC state to blocked). Prove
frame: all other objects are unchanged.

```lean
theorem endpointSendDual_modifies_only
    (st st' : SystemState) (eid : ObjId) (sender : ThreadId) (msg : IpcMessage)
    (hStep : endpointSendDual eid sender msg st = .ok ((), st')) :
    ∀ oid, oid ≠ eid → oid ≠ sender.toObjId →
      st'.objects[oid]? = st.objects[oid]? := by
  <proof via unfolding endpointSendDual and storeObject frame lemmas>
```

**Scope**: `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` (~80 lines)
**Gate**: `lake build SeLe4n.Kernel.IPC.DualQueue.Transport`

##### R5-A.2: Prove NI for `endpointSendDualChecked` (internalized)

Replace the hypothesis-accepting version with a self-contained proof:

```lean
theorem endpointSendDualChecked_nonInterference
    (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : ObjId) (sender : ThreadId) (msg : IpcMessage)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (hStep₁ : endpointSendDualChecked ctx endpointId sender msg s₁ = .ok ((), s₁'))
    (hStep₂ : endpointSendDualChecked ctx endpointId sender msg s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  -- 1. Extract flow check → endpoint and sender are high-security
  -- 2. Apply dual-queue decomposition → only high objects modified
  -- 3. Apply projectState frame → projection unchanged
  -- 4. Conclude low-equivalence
```

**Scope**: `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean:85-98`
**Gate**: `lake build SeLe4n.Kernel.InformationFlow.Invariant.Operations`

##### R5-A.3: Prove NI for `endpointReceiveDualChecked` (internalized)

Same decomposition strategy: receive modifies the endpoint (dequeue sender)
and the receiver TCB (set IPC state to ready, copy message). Both objects
must be high-security for the NI hypothesis.

**Scope**: `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean`
**Gate**: `lake build SeLe4n.Kernel.InformationFlow.Invariant.Operations`

##### R5-A.4: Prove NI for `endpointCallChecked` and `endpointReplyRecvChecked`

These are compositions of send+receive. The proofs compose the individual
NI lemmas from R5-A.2 and R5-A.3.

**Scope**: `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean:1155-1228`
**Gate**: `lake build SeLe4n.Kernel.InformationFlow.Invariant.Operations`

##### R5-A.5: Remove hypothesis parameters from `NonInterferenceStep` constructors

Update the `endpointSendDual` constructor in `NonInterferenceStep` (Composition.lean)
to derive `hProjection` from the new internalized proof rather than accepting
it as a parameter.

**Scope**: `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean:41-50`
**Gate**: `lake build SeLe4n.Kernel.InformationFlow.Invariant.Composition`

---

#### R5-B: Add `registerServiceChecked` to NI composition bundle (M-02)

**Problem**: 34 operation constructors are covered by `NonInterferenceStep`,
but service registration is missing.

**Scope**: `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean:34-233`

**Sub-tasks**:

##### R5-B.1: Add `registerServiceChecked` constructor to `NonInterferenceStep`

```lean
| registerServiceChecked
    (reg : ServiceRegistration) (callerCNode : ObjId)
    (hServiceHigh : objectObservable ctx observer reg.endpointCap.target.toObjId = false)
    (hStep : registerServiceChecked ctx reg callerCNode st = .ok ((), st'))
  : NonInterferenceStep ctx observer st st'
```

**Scope**: `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean`
**Gate**: `lake build SeLe4n.Kernel.InformationFlow.Invariant.Composition`

##### R5-B.2: Prove `registerServiceChecked_nonInterference`

Service registration modifies only `serviceRegistry` (not objects). If the
service endpoint is high-security, the registry change is invisible to the
observer (registry is not part of `projectState` observable surface).

**Scope**: `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` (~40 lines)
**Gate**: `lake build SeLe4n.Kernel.InformationFlow.Invariant.Operations`

##### R5-B.3: Integrate into trace composition theorem

Update the main trace composition theorem to include the new constructor
in its exhaustive match.

**Scope**: `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean`
**Gate**: `lake build SeLe4n.Kernel.InformationFlow.Invariant.Composition`

---

#### R5-C: Strengthen memory projection (M-03)

**Problem**: `projectMemory` returns `some 0` for all observable addresses
regardless of actual memory content. The NI framework verifies memory
address set isolation but not content isolation.

**Scope**: `SeLe4n/Kernel/InformationFlow/Projection.lean:260-262`

**Sub-tasks**:

##### R5-C.1: Implement content-aware memory projection

Replace dummy-byte projection with actual memory content lookup:

```lean
def projectMemory (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (addr : VAddr) : Option RegValue :=
  if memoryObservable ctx observer addr then
    st.machine.memory.get? addr  -- actual content, not dummy
  else
    none
```

**Scope**: `SeLe4n/Kernel/InformationFlow/Projection.lean:260-262`
**Gate**: `lake build SeLe4n.Kernel.InformationFlow.Projection`

##### R5-C.2: Update `lowEquivalent` to use content-aware projection

Verify that the `lowEquivalent` definition compares projected memory
content, not just the observable address set. Update if needed.

**Scope**: `SeLe4n/Kernel/InformationFlow/Projection.lean`
**Gate**: `lake build SeLe4n.Kernel.InformationFlow.Projection`

##### R5-C.3: Update NI proofs affected by content-aware projection

Operations that modify memory content in observable regions need updated
NI proofs. The key operations are `vspaceMapPage` and memory writes.
Most kernel operations only modify objects, not memory, so the cascade
should be limited.

**Scope**: `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean`
**Gate**: `lake build SeLe4n.Kernel.InformationFlow.Invariant.Operations`

---

#### R5-D: Update composition theorems

##### R5-D.1: Update `traceNonInterference` exhaustive match

Ensure the main trace-level NI theorem handles all new constructors
(service registration, internalized IPC).

**Scope**: `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean`
**Gate**: `lake build SeLe4n.Kernel.InformationFlow.Invariant.Composition`

---

#### R5-E: Documentation and verification

##### R5-E.1: Update information flow documentation

Update `docs/gitbook/12-proof-and-invariant-map.md` and
`docs/spec/SELE4N_SPEC.md` information flow sections.

**Scope**: Documentation files
**Gate**: `test_full.sh` passes

**R5 phase exit evidence**:
- `lake build` succeeds
- `test_full.sh` passes
- `rg "hSendDualNI" SeLe4n/Kernel/InformationFlow/` returns zero hypothesis
  parameters (all internalized)
- 35 operations (34 + registerServiceChecked) in NI composition bundle
- Memory projection returns actual content, not dummy bytes
- No `sorry`/`axiom` in any modified file

---

### Phase R6: Model & Frozen State Correctness

**Target version**: v0.18.5
**Goal**: Strengthen the frozen invariant to survive mutation and close
model-layer proof gaps for value bounds and invariant bundles.
**Priority**: MEDIUM — frozen state correctness is critical for the
builder→execution phase transition but does not affect builder-phase proofs.
**Dependencies**: R1 (frozen context error handling)
**Findings addressed**: M-09, L-01, L-04, L-12

#### R6-A: Fix frozen invariant existential staleness (M-09)

**Problem**: `apiInvariantBundle_frozen` is defined existentially — it
asserts existence of an `IntermediateState` witness. After `FrozenMap.set`
mutations, the witness becomes stale because the frozen state no longer
equals `freeze ist` for the original `ist`.

**Scope**: `SeLe4n/Model/FreezeProofs.lean:1033-1048`

**Sub-tasks**:

##### R6-A.1: Define direct frozen invariant predicate

Define a non-existential version that checks invariant properties directly
on the frozen state, without requiring a witness `IntermediateState`:

```lean
def apiInvariantBundle_frozenDirect (fst : FrozenSystemState) : Prop :=
  schedulerInvariant_frozen fst ∧
  capabilityInvariant_frozen fst ∧
  ipcInvariant_frozen fst ∧
  lifecycleInvariant_frozen fst ∧
  serviceInvariant_frozen fst ∧
  vspaceInvariant_frozen fst
```

Each `*_frozen` predicate operates directly on `FrozenSystemState` fields
using `FrozenMap` lookups.

**Scope**: `SeLe4n/Model/FreezeProofs.lean` (~60 lines of definitions)
**Gate**: `lake build SeLe4n.Model.FreezeProofs`

##### R6-A.2: Prove equivalence with existential version at freeze time

```lean
theorem apiInvariantBundle_frozenDirect_iff_frozen
    (ist : IntermediateState)
    (hInv : apiInvariantBundle ist.state) :
    apiInvariantBundle_frozenDirect (freeze ist) ↔
    apiInvariantBundle_frozen (freeze ist) := by
  <proof via lookup equivalence theorems from Q6>
```

**Scope**: `SeLe4n/Model/FreezeProofs.lean` (~40 lines)
**Gate**: `lake build SeLe4n.Model.FreezeProofs`

##### R6-A.3: Prove `FrozenMap.set` preserves direct invariant

Prove that well-typed mutations via `FrozenMap.set` preserve the direct
frozen invariant. This is the key theorem that the existential version
cannot provide:

```lean
theorem frozenMap_set_preserves_invariant
    (fst : FrozenSystemState) (oid : ObjId) (obj : FrozenKernelObject)
    (hInv : apiInvariantBundle_frozenDirect fst)
    (hObjInv : frozenObjectInvariant obj)
    (hSet : fst.objects.set oid obj = some objects') :
    apiInvariantBundle_frozenDirect { fst with objects := objects' } := by
  <proof by cases on each invariant component, using FrozenMap frame lemmas>
```

**Scope**: `SeLe4n/Model/FreezeProofs.lean` (~80 lines)
**Gate**: `lake build SeLe4n.Model.FreezeProofs`

##### R6-A.4: Migrate FrozenOps invariant theorems to direct predicate

Update `SeLe4n/Kernel/FrozenOps/Invariant.lean` to use
`apiInvariantBundle_frozenDirect` instead of `apiInvariantBundle_frozen`.
The existential version remains available for backward compatibility.

**Scope**: `SeLe4n/Kernel/FrozenOps/Invariant.lean`
**Gate**: `lake build SeLe4n.Kernel.FrozenOps.Invariant`

---

#### R6-B: Fix `Badge.ofNat` word-size bypass (L-01)

**Problem**: `Badge.ofNat` wraps an unbounded `Nat` without masking to
word size. On hardware, badges are 64-bit values.

**Sub-tasks**:

##### R6-B.1: Deprecate `Badge.ofNat` in favor of `Badge.ofNatMasked`

Add `@[deprecated]` to `Badge.ofNat`. Ensure all production code uses
`Badge.ofNatMasked` which applies `% 2^64` masking.

**Scope**: `SeLe4n/Prelude.lean`
**Gate**: `lake build SeLe4n.Prelude`

##### R6-B.2: Migrate all `Badge.ofNat` call sites

Search and replace `Badge.ofNat` with `Badge.ofNatMasked` across the codebase.

**Scope**: Multiple files
**Gate**: `lake build` succeeds, `rg "Badge.ofNat[^M]" SeLe4n/` returns zero

---

#### R6-C: Fix `BEq RegisterFile` partial comparison (L-04)

**Problem**: `BEq RegisterFile` compares only 32 GPRs via a magic number.
ARM64 has 31 GPRs + SP + PC, and the comparison should be structural.

**Sub-tasks**:

##### R6-C.1: Replace magic-number comparison with structural equality

Use `DecidableEq` or compare all register indices that appear in the
`RegisterFile` map, rather than hard-coding 32.

**Scope**: `SeLe4n/Machine.lean`
**Gate**: `lake build SeLe4n.Machine`

---

#### R6-D: Add `schedulerPriorityMatch` to invariant bundle (L-12)

**Problem**: `schedulerPriorityMatch` and `wellFormed` are proven preserved
but not included in the scheduler invariant bundle, meaning they are not
automatically checked at kernel entry/exit.

**Sub-tasks**:

##### R6-D.1: Add to `schedulerInvariantBundle`

Add `schedulerPriorityMatch` and `schedulerWellFormed` to the scheduler
invariant bundle definition.

**Scope**: `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean`
**Gate**: `lake build SeLe4n.Kernel.Scheduler.Operations.Preservation`

##### R6-D.2: Prove preservation through existing bundle theorems

The preservation proofs already exist individually. Compose them into
the bundle preservation theorems.

**Scope**: `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean`
**Gate**: `lake build SeLe4n.Kernel.Scheduler.Operations.Preservation`

---

#### R6-E: Regenerate documentation

##### R6-E.1: Update proof map and codebase map

**Scope**: `docs/gitbook/12-proof-and-invariant-map.md`, `docs/codebase_map.json`
**Gate**: `test_full.sh` passes

**R6 phase exit evidence**:
- `lake build` succeeds
- `test_full.sh` passes
- Frozen invariant survives `FrozenMap.set` mutations
- `Badge.ofNat` deprecated, all sites use `ofNatMasked`
- No `sorry`/`axiom` in any modified file

---

### Phase R7: Architecture & Hardware Preparation

**Target version**: v0.18.6
**Goal**: Strengthen the architecture model for hardware binding, including
TLB flush enforcement, value bounds, and seL4 TCB fidelity.
**Priority**: MEDIUM — required for RPi5 hardware target but not blocking
proof chain completion.
**Dependencies**: R6 (model-layer value bounds)
**Findings addressed**: M-17, L-02, L-03, L-06, L-10

#### R7-A: Enforce TLB flush after page table modification (M-17)

**Problem**: Proofs show *if* you flush *then* consistency holds, but
nothing prevents forgetting the flush. On hardware, a missing TLB flush
after unmap is a critical security concern.

**Scope**: `SeLe4n/Kernel/Architecture/TlbModel.lean:87-141`

**Sub-tasks**:

##### R7-A.1: Integrate `TlbState` into `SystemState`

Add `tlb : TlbState` field to `SystemState`. This makes TLB state
part of the kernel state that invariants can reference.

**Scope**: `SeLe4n/Model/State.lean`, `SeLe4n/Kernel/Architecture/TlbModel.lean`
**Gate**: `lake build SeLe4n.Model.State`
**Note**: This is a potentially high-cascade change. The `SystemState`
structure is referenced in ~90 files. The field addition should be
backward-compatible (existing code ignores it via structural subtyping).

##### R7-A.2: Add `tlbConsistent` to `apiInvariantBundle`

Thread TLB consistency into the top-level invariant:

```lean
def apiInvariantBundle (st : SystemState) : Prop :=
  <existing conjuncts> ∧
  tlbConsistent st st.tlb
```

**Scope**: `SeLe4n/Kernel/API.lean`
**Gate**: `lake build SeLe4n.Kernel.API`

##### R7-A.3: Prove VSpace operations invalidate + flush TLB

Prove that `vspaceMapPage` and `vspaceUnmapPage` must flush before
returning. This can be enforced by having the operations include the
flush as part of their implementation:

```lean
def vspaceMapPage (asid vaddr paddr perms) : Kernel Unit :=
  fun st =>
    <existing map logic producing st'>
    .ok ((), { st' with tlb := adapterFlushTlbEntry st'.tlb asid vaddr })
```

**Scope**: `SeLe4n/Kernel/Architecture/VSpace.lean` or equivalent
**Gate**: `lake build` for the architecture module

##### R7-A.4: Prove `tlbConsistent` preservation through all operations

Operations that do not modify page tables preserve TLB consistency
trivially (frame argument). VSpace operations preserve it via the
integrated flush from R7-A.3.

**Scope**: `SeLe4n/Kernel/Architecture/TlbModel.lean` (~60 lines)
**Gate**: `lake build SeLe4n.Kernel.Architecture.TlbModel`

---

#### R7-B: Add ARM64 bounds to `RegName` (L-02)

**Problem**: `RegName` wraps unbounded `Nat`. ARM64 has 31 GPRs (x0-x30)
plus SP and PC.

**Sub-tasks**:

##### R7-B.1: Add `RegName.isValid` predicate and validation

```lean
def RegName.isValid (r : RegName) : Prop := r.toNat < 33
```

Add bounds check to register operations.

**Scope**: `SeLe4n/Prelude.lean`, `SeLe4n/Machine.lean`
**Gate**: `lake build SeLe4n.Machine`

---

#### R7-C: Add bounded newtypes for `RegValue`, `VAddr`, `PAddr` (L-03)

**Problem**: These types wrap unbounded `Nat` but hardware values are 64-bit.

**Sub-tasks**:

##### R7-C.1: Add `isWord64` predicate

```lean
def isWord64 (n : Nat) : Prop := n < 2^64
```

Add this as a refinement predicate on `RegValue`, `VAddr`, and `PAddr`.
Do not change the underlying type (keep `Nat` for proof ergonomics),
but add the predicate to relevant invariants.

**Scope**: `SeLe4n/Prelude.lean`
**Gate**: `lake build SeLe4n.Prelude`

##### R7-C.2: Thread bounds into machine state invariant

Add a machine-state invariant asserting all register values and addresses
satisfy `isWord64`.

**Scope**: `SeLe4n/Machine.lean`
**Gate**: `lake build SeLe4n.Machine`

---

#### R7-D: Add TCB missing fields for seL4 fidelity (L-06)

**Problem**: TCB is missing `faultHandler`, `boundNotification`, and
`scContext` compared to seL4.

**Sub-tasks**:

##### R7-D.1: Add `faultHandler` and `boundNotification` to TCB

Add optional fields with `none` defaults:

```lean
structure TCB where
  <existing fields>
  faultHandler : Option CSpaceAddr := none
  boundNotification : Option ObjId := none
```

Default values ensure backward compatibility — existing code that
constructs TCBs without these fields compiles unchanged.

**Scope**: `SeLe4n/Model/Object/Types.lean`
**Gate**: `lake build SeLe4n.Model.Object.Types`

##### R7-D.2: Update TCB-related theorems

Verify that existing TCB theorems still compile. The default values
should make this a zero-cascade change.

**Scope**: Multiple files
**Gate**: `lake build` succeeds

---

#### R7-E: Replace raw `Nat` in `LifecycleRetypeArgs.newType` (L-10)

**Problem**: `newType` is a raw `Nat` instead of an enumeration of valid
kernel object types.

**Sub-tasks**:

##### R7-E.1: Define `KernelObjectType` enumeration

```lean
inductive KernelObjectType where
  | tcb | endpoint | notification | cnode | untyped | vspaceRoot | frame
  deriving DecidableEq, Repr
```

Replace `newType : Nat` with `newType : KernelObjectType` in
`LifecycleRetypeArgs`.

**Scope**: `SeLe4n/Kernel/Architecture/RegisterDecode.lean` or
  `SeLe4n/Model/Object/Types.lean`
**Gate**: `lake build` for the module

**R7 phase exit evidence**:
- `lake build` succeeds
- `test_full.sh` passes
- TLB flush structurally enforced (part of VSpace operations)
- ARM64 register bounds enforced
- No `sorry`/`axiom` in any modified file

---

### Phase R8: Infrastructure & CI Hardening

**Target version**: v0.18.7
**Goal**: Close supply chain, CI, and test infrastructure gaps.
**Priority**: MEDIUM — these findings do not affect kernel correctness
but affect development process security.
**Dependencies**: None (independent of all Lean/Rust phases)
**Findings addressed**: I-M01, I-M02, I-M03, I-M04, L-11

#### R8-A: Add SHA-256 verification for elan binary download (I-M01)

**Problem**: The primary elan download path (`/releases/latest/`) does
not verify the binary's SHA-256 hash. The fallback installer path does
have SHA verification.

**Scope**: `scripts/setup_lean_env.sh:282`

**Sub-tasks**:

##### R8-A.1: Pin elan release version

Replace `/releases/latest/` with a specific release tag:
```bash
ELAN_VERSION="v4.8.0"  # or current stable
ELAN_URL="https://github.com/leanprover/elan/releases/download/${ELAN_VERSION}/elan-${arch_name}.tar.gz"
```

**Scope**: `scripts/setup_lean_env.sh`
**Gate**: `./scripts/setup_lean_env.sh --skip-test-deps` succeeds

##### R8-A.2: Add SHA-256 verification for binary

Add hash verification after download:
```bash
ELAN_BINARY_SHA256_X86="<hash>"
ELAN_BINARY_SHA256_ARM="<hash>"
echo "${expected_sha}  ${elan_tar}" | sha256sum -c -
```

**Scope**: `scripts/setup_lean_env.sh`
**Gate**: `./scripts/setup_lean_env.sh --skip-test-deps` succeeds

---

#### R8-B: Fix codebase_map_sync auto-push (I-M02)

**Problem**: `codebase_map_sync.yml` auto-pushes to main with
`contents: write`, creating race conditions and unattributed commits.

**Scope**: `.github/workflows/codebase_map_sync.yml`

**Sub-tasks**:

##### R8-B.1: Convert to PR-based workflow

Instead of auto-pushing, create a PR:
```yaml
- name: Create PR if changed
  if: steps.check.outputs.changed == 'true'
  run: |
    git checkout -b ci/refresh-codebase-map-${{ github.run_id }}
    git add docs/codebase_map.json
    git commit -m "ci: refresh codebase map"
    git push -u origin ci/refresh-codebase-map-${{ github.run_id }}
    gh pr create --title "ci: refresh codebase map" \
      --body "Automated codebase map refresh" --base main
```

**Scope**: `.github/workflows/codebase_map_sync.yml`
**Gate**: Workflow file validates with `actionlint`

##### R8-B.2: Downgrade permissions to `contents: read` + `pull-requests: write`

```yaml
permissions:
  contents: read
  pull-requests: write
```

**Scope**: `.github/workflows/codebase_map_sync.yml`
**Gate**: Workflow file validates

---

#### R8-C: Make Rust test skip explicit in CI (I-M03)

**Problem**: Rust tests silently skip when cargo is unavailable, providing
false confidence.

**Sub-tasks**:

##### R8-C.1: Add explicit cargo availability check with warning

```bash
if ! command -v cargo &>/dev/null; then
    echo "⚠️  WARNING: cargo not found — Rust tests SKIPPED"
    echo "::warning::Rust tests skipped (cargo not available)"
    exit 0
fi
```

**Scope**: `scripts/test_rust.sh`
**Gate**: `./scripts/test_rust.sh` produces visible warning when cargo absent

##### R8-C.2: Ensure CI environment has cargo installed

Add cargo installation step to CI workflow or document the requirement.

**Scope**: `.github/workflows/lean_action_ci.yml`
**Gate**: CI workflow runs Rust tests successfully

---

#### R8-D: Execute compiled test suites in CI (I-M04)

**Problem**: `FrozenStateSuite`, `FreezeProofSuite`, and `FrozenOpsSuite`
are compiled but never executed in CI.

**Sub-tasks**:

##### R8-D.1: Add execution to Tier 2 test script

Add to `scripts/test_tier2_negative.sh`:
```bash
run_check "TRACE" "lake exe frozen_state_suite"
run_check "TRACE" "lake exe freeze_proof_suite"
run_check "TRACE" "lake exe frozen_ops_suite"
```

**Scope**: `scripts/test_tier2_negative.sh`
**Gate**: `./scripts/test_smoke.sh` passes with new suites executing

##### R8-D.2: Verify suite outputs and add expected fixtures

If the suites produce deterministic output, capture expected output
to fixture files for regression testing.

**Scope**: `tests/fixtures/`
**Gate**: Suites execute and produce consistent output

---

#### R8-E: Rust encapsulation improvements (L-11)

**Problem**: Newtype inner fields are `pub`, allowing direct access
that bypasses constructors and validation.

**Sub-tasks**:

##### R8-E.1: Make newtype inner fields `pub(crate)` or private

For types like `Slot(pub u64)`, `Badge(pub u64)`, etc., change to:
```rust
pub struct Slot(pub(crate) u64);
```

Add accessor methods: `pub const fn raw(&self) -> u64 { self.0 }`

**Scope**: `rust/sele4n-types/src/lib.rs` and related files
**Gate**: `cargo build --all` succeeds, `cargo test --all` passes

##### R8-E.2: Update external consumers

Migrate any code that accesses `.0` directly to use `.raw()` accessor.

**Scope**: All Rust crate files
**Gate**: `cargo build --all` succeeds

**R8 phase exit evidence**:
- `./scripts/setup_lean_env.sh --skip-test-deps` succeeds with SHA verification
- `codebase_map_sync.yml` creates PRs instead of auto-pushing
- Rust test skip produces explicit warning
- All 3 frozen test suites execute in CI
- Newtype fields encapsulated
- CI pipeline green

---

## 6. Scope Estimates

| Phase | Tasks / Sub-tasks | New Lines (est.) | Modified Lines (est.) | Modified Files | New Files |
|-------|-------------------|-------------------|-----------------------|----------------|-----------|
| R1 | 6 / 17 | ~350 | ~200 | ~12 | 1 |
| R2 | 7 / 17 | ~600 | ~300 | ~8 | 0 |
| R3 | 6 / 15 | ~700 | ~250 | ~10 | 1 |
| R4 | 6 / 19 | ~550 | ~200 | ~11 | 1 |
| R5 | 5 / 13 | ~800 | ~150 | ~7 | 0 |
| R6 | 5 / 10 | ~400 | ~100 | ~8 | 0 |
| R7 | 5 / 10 | ~450 | ~150 | ~12 | 0 |
| R8 | 5 / 10 | ~200 | ~100 | ~8 | 0 |
| **Total** | **45 / 111** | **~4,050** | **~1,450** | **~50 unique** | **3** |

**Notes**:
- R5 has the highest new-line count due to the IPC non-interference proof
  decomposition lemmas. Each NI proof requires ~100-150 lines of structured
  reasoning.
- R7-A (TLB integration into SystemState) has the highest cascade risk.
  The field addition to `SystemState` affects ~90 files, though most changes
  are mechanical (struct update syntax).
- R1 is the only phase that touches Rust code significantly.
- New files: R1 may add a Rust test file; R3 may add
  `DualQueuePreservation.lean`; R4 may add `CrossSubsystem.lean`.

---

## 7. Risk Analysis

### Risk 1: R7-A `SystemState` TLB field addition (HIGH cascade)

**Description**: Adding `tlb : TlbState` to `SystemState` touches every file
that constructs or pattern-matches on `SystemState`. With ~90 references,
this is the highest-cascade change in the plan.

**Likelihood**: HIGH | **Impact**: MEDIUM (mechanical but numerous)

**Mitigation**:
- Use `tlb := TlbState.empty` as the default field value. Existing
  `SystemState` constructions compile unchanged (Lean fills defaults).
- If default fields are insufficient, batch the update with a search-and-replace
  pass. Verify each file individually with `lake build <Module.Path>`.
- Execute R7-A first within Phase R7 to identify cascade scope early.

### Risk 2: R5-A IPC NI proof complexity (HIGH difficulty)

**Description**: The four IPC NI proofs are the most technically challenging
theorems in the plan. The dual-queue decomposition strategy is referenced
in code comments but not yet implemented. Proof strategies may need
multiple iterations.

**Likelihood**: MEDIUM | **Impact**: HIGH (blocks R5 completion)

**Mitigation**:
- R3 internalizes the IPC invariant hypotheses first, providing a solid
  foundation for the NI proofs.
- Start with `endpointSendDual` (simplest — only modifies endpoint + sender).
  Use it as a template for the other three.
- If a proof requires lemmas beyond the current infrastructure, add them to
  `DualQueue/Transport.lean` as reusable building blocks.
- Accept that `endpointCall` and `endpointReplyRecv` NI proofs may compose
  the send/receive proofs rather than proving from scratch.

### Risk 3: R2-D CDT acyclicity general case (MEDIUM difficulty)

**Description**: Extending acyclicity from fresh nodes to the general case
requires proving that `addEdge parent child` preserves well-foundedness
when `child` is not an ancestor of `parent`. This is a non-trivial
well-foundedness argument.

**Likelihood**: MEDIUM | **Impact**: MEDIUM (blocks R2-D only)

**Mitigation**:
- The `isAncestor` decidable predicate (R2-D.2) provides the computational
  hook for the proof. The well-foundedness argument reduces to showing
  that the new edge does not create a cycle.
- If the general case proves too complex, scope down to the case where
  `child` has no existing parent (the single-parent invariant guarantees
  this for all `addEdge` calls in the kernel).

### Risk 4: R1-C SyscallResponse restructure (MEDIUM cascade)

**Description**: Restructuring `SyscallResponse` changes the public API
of the Rust ABI crate. All consumers must update.

**Likelihood**: LOW | **Impact**: LOW (Rust crate has few consumers)

**Mitigation**:
- The compiler catches all breakage (field access becomes method call).
- The Rust crate has zero external consumers — all code is in-tree.

### Risk 5: R4-A Endpoint queue cleanup performance (LOW)

**Description**: `removeFromAllEndpointQueues` iterates all objects to
find endpoints. On a system with many objects, this is O(n).

**Likelihood**: LOW | **Impact**: LOW (retype is rare operation)

**Mitigation**:
- Retype is a low-frequency operation. O(n) scan is acceptable.
- If performance becomes a concern, maintain a reverse index from
  `ThreadId → List ObjId` (IPC queues containing this thread).

---

## 8. Dependency Graph (Detailed)

```
Phase R1: Pre-Release Blockers ─────────────────────────────────┐
  R1-A: Cap::downgrade() fix                                    │
  R1-B: AccessRights/PagePerms truncation                       │
  R1-C: SyscallResponse restructure                             │
  R1-D: api* wrapper deprecation                                │
  R1-E: Frozen context error handling ──────────────────────────►│
  R1-F: Test fixture updates                                    │
                                                                │
Phase R2: Capability & CDT Hardening (parallel with R1) ──┐     │
  R2-A: processRevokeNode error propagation               │     │
  R2-B: streamingRevokeBFS fuel exhaustion                 │     │
  R2-C: CDT remove consistency proofs                      │     │
  R2-D: CDT acyclicity general case                        │     │
  R2-E: CDT postconditions for copy/move/mint              │     │
  R2-F: Preservation theorem updates                       │     │
  R2-G: Test suite updates                                 │     │
                                                           │     │
                    ┌──────────────────────────────────────►│     │
                    │                                      │     │
Phase R3: IPC Invariant Completion ────────────────────┐   │     │
  R3-A: notificationSignal badge delivery              │   │     │
  R3-B: dualQueueSystemInvariant internalization       │   │     │
  R3-C: notificationWaiterConsistent preservation      │   │     │
  R3-D: IpcMessage structural bounds                   │   │     │
  R3-E: Linter re-enable                               │   │     │
  R3-F: Documentation                                  │   │     │
                                                       │   │     │
Phase R4: Lifecycle & Service Coherence ───────────┐   │   │     │
  R4-A: IPC endpoint queue cleanup                 │   │   │     │
  R4-B: Lifecycle/service cross-subsystem guard    │   │   │     │
  R4-C: registerService capability authority       │   │   │     │
  R4-D: revokeService dependency graph cleanup     │   │   │     │
  R4-E: Cross-subsystem invariant composition      │   │   │     │
  R4-F: Test and documentation                     │   │   │     │
                                                   │   │   │     │
                    ┌──────────────────────────────►│   │   │     │
                    │              ┌────────────────►   │   │     │
                    │              │                    │   │     │
Phase R5: Information Flow Completion              │   │   │     │
  R5-A: IPC NI proofs (internalized) ◄─────────────┘───┘   │     │
  R5-B: registerServiceChecked NI ◄────────────────────┘   │     │
  R5-C: Memory projection content-aware                     │     │
  R5-D: Composition theorem updates                         │     │
  R5-E: Documentation                                       │     │
                                                            │     │
Phase R6: Model & Frozen State Correctness ◄────────────────┘─────┘
  R6-A: Frozen invariant non-existential
  R6-B: Badge.ofNat deprecation
  R6-C: BEq RegisterFile fix
  R6-D: schedulerPriorityMatch in bundle
  R6-E: Documentation
         │
         ▼
Phase R7: Architecture & Hardware Preparation
  R7-A: TLB state in SystemState
  R7-B: RegName ARM64 bounds
  R7-C: RegValue/VAddr/PAddr bounds
  R7-D: TCB missing fields
  R7-E: LifecycleRetypeArgs.newType enum

Phase R8: Infrastructure & CI (fully independent)
  R8-A: Elan SHA-256 verification
  R8-B: codebase_map_sync PR-based
  R8-C: Rust test skip explicit
  R8-D: Execute frozen test suites
  R8-E: Rust encapsulation
```

**Critical path**: R2 → R3 → R5 (capability hardening → IPC invariant
internalization → IPC non-interference proof completion)

**Parallel execution opportunities**:
- R1 ∥ R2 ∥ R8 (three independent streams)
- R3 ∥ R4 (both depend on R2, independent of each other)
- R6 can start after R1 completes (parallel with R3/R4/R5)

**Optimal execution order** (minimizing wall-clock time):

```
Week 1:  R1 + R2 + R8 (parallel)
Week 2:  R3 + R4 + R6 (parallel, after R1/R2)
Week 3:  R5 (after R3 + R4)
Week 4:  R7 (after R6)
```

---

## 9. Finding Coverage Matrix

| Finding | Phase | Sub-task | Status |
|---------|-------|----------|--------|
| **H-01** | R1 | R1-A | Planned |
| **M-01** | R5 | R5-A | Planned |
| **M-02** | R5 | R5-B | Planned |
| **M-03** | R5 | R5-C | Planned |
| **M-04** | R1 | R1-D | Planned |
| **M-05** | R2 | R2-B | Planned |
| **M-06** | R2 | R2-A | Planned |
| **M-07** | R2 | R2-C | Planned |
| **M-08** | R2 | R2-D | Planned |
| **M-09** | R6 | R6-A | Planned |
| **M-10** | R1 | R1-E | Planned |
| **M-11** | R1 | R1-E | Planned |
| **M-12** | R4 | R4-A | Planned |
| **M-13** | R4 | R4-B | Planned |
| **M-14** | R4 | R4-C | Planned |
| **M-15** | R4 | R4-D | Planned |
| **M-16** | R3 | R3-A | Planned |
| **M-17** | R7 | R7-A | Planned |
| **M-18** | R3 | R3-B | Planned |
| **M-19** | R3 | R3-C | Planned |
| **R-M01** | R1 | R1-B | Planned |
| **R-M02** | R1 | R1-B | Planned |
| **R-M03** | R1 | R1-C | Planned |
| **I-M01** | R8 | R8-A | Planned |
| **I-M02** | R8 | R8-B | Planned |
| **I-M03** | R8 | R8-C | Planned |
| **I-M04** | R8 | R8-D | Planned |
| **L-01** | R6 | R6-B | Planned |
| **L-02** | R7 | R7-B | Planned |
| **L-03** | R7 | R7-C | Planned |
| **L-04** | R6 | R6-C | Planned |
| **L-05** | R3 | R3-D | Planned |
| **L-06** | R7 | R7-D | Planned |
| **L-07** | R2 | R2-E | Planned |
| **L-08** | R3 | R3-E | Planned |
| **L-09** | R4 | R4-C | Planned |
| **L-10** | R7 | R7-E | Planned |
| **L-11** | R8 | R8-E | Planned |
| **L-12** | R6 | R6-D | Planned |

**Coverage**: 1/1 High, 19/19 Medium, 12/34 Low, 0/28 Info = **32/82 findings addressed**.

Low/Info findings not included are design-level observations (strict-priority
starvation, timing covert channels), documentation gaps, ergonomics issues,
or hardware-specific concerns deferred to the RPi5 hardware binding workstream.

---

## 10. Findings Explicitly Deferred

The following findings are **not addressed** by WS-R and are explicitly
deferred to future workstreams:

| Category | Count | Rationale |
|----------|-------|-----------|
| Design-level observations (scheduler starvation, timing channels) | 3 | Architectural tradeoffs matching seL4 design; not bugs |
| `native_decide` usage (~12 instances) | 1 | All on ground-truth concrete values; sound |
| VSpace flat model vs hierarchical page tables | 1 | Deferred to RPi5 hardware binding (WS-S) |
| VAddr/PAddr alignment validation | 1 | Deferred to RPi5 hardware binding (WS-S) |
| RPi5 boot contract vs actual boot state | 1 | Deferred to RPi5 hardware binding (WS-S) |
| Boot sequence scheduler/label initialization | 1 | Deferred to RPi5 boot integration |
| Remaining Low findings (informational) | 22 | Low impact; tracked but not prioritized |
| Info findings | 28 | Informational only; no action required |

---

**End of Workstream Plan**

*This plan was created from the comprehensive pre-release audit of seLe4n
v0.17.13 (`docs/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`).
All 20 High+Medium findings are addressed across 8 phases with 111 atomic
sub-tasks. The plan maintains the project's zero-sorry/axiom invariant
and follows the additive-first, deprecate-later migration strategy.*

