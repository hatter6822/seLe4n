# WS-W Workstream Plan — Pre-Release Audit Remediation (v0.22.10)

**Created**: 2026-03-28
**Baseline version**: 0.22.10
**Baseline audits**:
- `docs/audits/AUDIT_COMPREHENSIVE_v0.22.10_PRE_RELEASE.md` (2 CRIT, 1 HIGH, 3 MED, 2 LOW)
- `docs/audits/AUDIT_COMPREHENSIVE_v0.22.10_LEAN_RUST_KERNEL.md` (2 CRIT, 2 HIGH, 5 MED, 8 LOW, 6 INFO)
- `docs/audits/AUDIT_COMPREHENSIVE_v0.22.10_FULL_KERNEL.md` (3 HIGH, 11 MED, 18 LOW)
**Prior portfolios**: WS-B through WS-V (all COMPLETE — see `docs/WORKSTREAM_HISTORY.md`)
**Constraint**: Zero `sorry`/`axiom` in production proof surface

---

## 1. Executive Summary

Three comprehensive audits of seLe4n v0.22.10 were conducted on 2026-03-28: a
pre-release audit, a Lean+Rust kernel audit, and a full-kernel audit. After
cross-referencing all three audits, deduplicating findings, and verifying each
against the actual codebase, we identified **49 unique actionable findings**
(2 CRITICAL, 4 HIGH, 16 MEDIUM, 27 LOW) plus **8 erroneous or overstated
findings** that require no action.

The **2 CRITICAL findings** are Rust ABI bugs where notification syscall
wrappers dispatch to the wrong kernel transition. The **4 HIGH findings**
cover a missing Rust error variant, a badge ABI semantic mismatch, and two
proof formalism gaps. The remaining findings address dead code, test
infrastructure, documentation drift, and platform readiness.

This workstream plan organizes all actionable findings into **6 phases**
(W1-W6) with **52 atomic sub-tasks**, explicit dependencies, gate conditions,
and scope estimates. All production Lean changes must maintain the zero
sorry/axiom invariant.

### Finding Deduplication Summary

| Audit | Raw Findings | After Dedup | Erroneous |
|-------|-------------|-------------|-----------|
| PRE_RELEASE | 8 | 6 unique | 2 overstated |
| LEAN_RUST | 23 | 12 unique | 3 overstated |
| FULL_KERNEL | 36 | 31 unique | 3 erroneous |
| **Cross-audit total** | 67 | **49 actionable** | **8 erroneous** |

### Phase Overview

| Phase | Name | Sub-tasks | Priority | Gate |
|-------|------|-----------|----------|------|
| W1 | Critical Rust ABI Fixes | 9 | **BLOCKER** | Rust tests pass, ABI conformance green |
| W2 | Proof Formalism & Architecture | 8 | HIGH | `lake build` clean, `test_full.sh` green |
| W3 | Dead Code Elimination | 8 | MEDIUM | `test_smoke.sh` green, no sorry introduced |
| W4 | Platform & Architecture Hardening | 7 | MEDIUM | Module builds pass, test_smoke green |
| W5 | Test Infrastructure & Coverage | 8 | MEDIUM | All test suites pass |
| W6 | Code Quality & Documentation | 12 | LOW | `test_fast.sh` green, docs consistent |

**Dependencies**: W1 is independent and must complete first. W2-W4 can proceed
in parallel after W1. W5 depends on W1 (new wrappers need tests). W6 depends
on W3 (dead code removal changes line counts for docs).

---

## 2. Erroneous and Overstated Findings

The following findings were verified against the codebase and found to be
erroneous, overstated, or already addressed. **No action required.**

### ERR-1: Dead code counts grossly overstated (PRE_RELEASE MED-1, LEAN_RUST MED-01)

**Claimed**: ~450 (PRE_RELEASE) to ~1,194 (LEAN_RUST) unused definitions.
**Reality**: Both audits define "dead" as "never referenced outside the
defining file." This captures:
- **Internal helpers** used within their own file (e.g., `arm64GPRCount` used
  by `RegName.isValid` in Machine.lean; `CSpaceOwner` used by `ownerOfSlot`
  in State.lean; `SlotAddr` used in CDT structure fields in Structures.lean)
- **Specification-surface theorems** that serve as formal documentation even
  without downstream consumers (e.g., lattice proofs in Policy.lean,
  capability authority reduction proofs)
- **Re-export hub targets** where the definition is consumed via a re-export
  import rather than direct reference

Sample verification of 8 items showed **5 of 8 (62.5%) were false positives**.
The actual dead code count is significantly lower than claimed. Phase W3
addresses dead code with a verification-first methodology.

### ERR-2: DeviceTree.lean and MmioAdapter.lean claimed as "entire dead modules"

**Claimed** (PRE_RELEASE MED-1): Both modules have "zero external consumers."
**Reality**: `DeviceTree.lean` is imported by `SeLe4n/Platform/RPi5/Board.lean`.
`MmioAdapter.lean` is imported by `SeLe4n/Platform/RPi5/Contract.lean`. Both
are part of the RPi5 platform binding chain. Not dead.

### ERR-3: FrozenOps "all exports actively consumed" (FULL_KERNEL Section 5)

**Claimed** (FULL_KERNEL): "All RobinHood/RadixTree/FrozenOps exports are
actively consumed."
**Reality**: FrozenOps has **zero production consumers**. Only 2 test files
(`FrozenOpsSuite.lean`, `TwoPhaseArchSuite.lean`) import it. The kernel API
(`API.lean`) does not reference FrozenOps. The FULL_KERNEL audit's dead code
analysis is too permissive here. However, the PRE_RELEASE audit's
recommendation to remove FrozenOps is also overstated — it serves as
architectural validation infrastructure for the two-phase (builder→frozen)
state model. Phase W3-G addresses this.

### ERR-4: FULL_KERNEL H-3 overstated severity

**Claimed**: HIGH — "no enforcement mechanism ensures metadata is updated when
objects are deleted."
**Reality**: The `lifecycleCapabilityRefObjectTargetBacked` predicate is
maintained by the pre-retype cleanup contract (`lifecyclePreRetypeCleanup`
calls `revokeAndClearRefsState`). The cleanup contract is proven to clear
metadata references before object deletion. The finding correctly notes the
mechanism relies on contract discipline rather than automatic enforcement, but
this is a design pattern (hypothesis-carrying operations), not a bug. Severity
should be LOW (documentation gap). Addressed in W6-K.

### ERR-5: FULL_KERNEL M-2 not actionable

**Claimed**: MEDIUM — `defaultLabelingContext` is insecure by design.
**Reality**: This is documented, intentional, and has explicit `_insecure`
witness theorems. No action needed beyond what already exists.

### ERR-6: FULL_KERNEL M-1 not actionable

**Claimed**: MEDIUM — Service registry NI coverage gap.
**Reality**: Documented as "accepted" in the audit itself. The gap is
acknowledged with explicit `acceptedCovertChannel_scheduling` documentation.
No remediation needed.

### ERR-7: LEAN_RUST LOW-05 not a real issue

**Claimed**: LOW — `IpcMessage.push()` trusts `length` field.
**Reality**: The bounds check `if self.length >= 4` correctly prevents
out-of-bounds writes. The `length` field is `pub` but the worst case
(setting `length = 255` then calling `push`) is safely rejected by the
bounds check, and subsequent encode returns a clear error. The API is
correct; the error path is indirect but safe.

### ERR-8: FULL_KERNEL L-5 not actionable

**Claimed**: LOW — Tautological predicate retained for backward compatibility.
**Reality**: `lifecycleIdentityNoTypeAliasConflict` is explicitly retained
for backward compatibility per its documentation. Removing it would break
downstream import patterns. No action.

---

## 3. Phase W1 — Critical Rust ABI Fixes (BLOCKER)

**Priority**: BLOCKER — must complete before any release or benchmarking
**Scope**: `rust/sele4n-sys/src/ipc.rs`, `rust/sele4n-types/src/error.rs`,
conformance tests
**Gate**: All Rust tests pass (`cargo test --workspace`), ABI conformance green
**Estimated sub-tasks**: 9
**Dependencies**: None (independent)

### Findings Addressed

| Finding | Source Audit(s) | Severity |
|---------|----------------|----------|
| CRIT-1/CRIT-01 | PRE_RELEASE, LEAN_RUST | CRITICAL |
| CRIT-2/CRIT-02 | PRE_RELEASE, LEAN_RUST | CRITICAL |
| HIGH-1/HIGH-01 | PRE_RELEASE, LEAN_RUST | HIGH |
| HIGH-02 | LEAN_RUST | HIGH |
| MED-03 | LEAN_RUST | MEDIUM |
| MED-05 | LEAN_RUST, FULL_KERNEL L-12 note | MEDIUM |

### Sub-tasks

#### W1-A: Fix `notification_signal` SyscallId (CRIT-1/CRIT-01)

**File**: `rust/sele4n-sys/src/ipc.rs:133`
**Change**: Replace `SyscallId::Send` with `SyscallId::NotificationSignal`
**Verification**: `cargo test -p sele4n-sys`
**Risk**: Minimal — single enum variant swap

#### W1-B: Fix `notification_wait` SyscallId (CRIT-2/CRIT-02)

**File**: `rust/sele4n-sys/src/ipc.rs:147`
**Change**: Replace `SyscallId::Receive` with `SyscallId::NotificationWait`
**Verification**: `cargo test -p sele4n-sys`
**Risk**: Minimal — single enum variant swap

#### W1-C: Resolve notification badge ABI mismatch (HIGH-02)

**Files**: `rust/sele4n-sys/src/ipc.rs:127-135` + Lean `SyscallArgDecode.lean:869-872`
**Problem**: The Lean `decodeNotificationSignalArgs` reads badge from `MR[0]`
via `requireMsgReg decoded.msgRegs 0`. The Rust `notification_signal()` passes
`msg_regs: [0; 4]` (all zeros), so badge is always 0.
**Design decision required**: Two options:
- **Option A (match Lean)**: Update `notification_signal(ntfn, badge)` to accept
  a `Badge` parameter and place `badge.0` in `msg_regs[0]`. This matches the
  current Lean model.
- **Option B (match seL4)**: Update Lean to use the resolved capability's badge
  (seL4 convention where `seL4_Signal(dest)` accumulates the cap's badge).
  This requires changing `decodeNotificationSignalArgs` and `dispatchWithCap`.
**Recommendation**: Option A — match the Lean model. The Lean model's design
choice to pass badge via MR[0] is deliberate and allows user-controlled badge
values. Update the Rust function signature to:
```rust
pub fn notification_signal(ntfn: CPtr, badge: Badge) -> KernelResult<SyscallResponse>
```
And place `badge.into(): u64` in `msg_regs[0]`.
**Verification**: New test `test_notification_signal_badge_passthrough`
**Risk**: API-breaking change for Rust consumers — requires version bump note

#### W1-D: Add `MmioUnaligned` to Rust `KernelError` (HIGH-1/HIGH-01)

**File**: `rust/sele4n-types/src/error.rs`
**Changes**:
1. Add `MmioUnaligned = 40` variant to the `KernelError` enum
2. Update `from_u32` match to include `40 => Some(Self::MmioUnaligned)`
3. Update `Display` impl with descriptive message
4. Update conformance test range from 0-39 to 0-40
5. Update test comment "All 40 variants" → "All 41 variants"
**Verification**: `cargo test -p sele4n-types`
**Risk**: Minimal — additive change, `#[non_exhaustive]` protects consumers

#### W1-E: Add `endpoint_reply_recv` wrapper (MED-03)

**File**: `rust/sele4n-sys/src/ipc.rs`
**Change**: Add new function:
```rust
pub fn endpoint_reply_recv(
    recv_cap: CPtr,
    reply_target: ThreadId,
    msg: &IpcMessage,
) -> KernelResult<SyscallResponse> { ... }
```
This wraps `SyscallId::ReplyRecv` (discriminant 16), matching the Lean
`endpointReplyRecv` in `API.lean:566-576`. Per `decodeReplyRecvArgs` in
`SyscallArgDecode.lean:881-884`, `MR[0]` contains `replyTarget` (ThreadId).
The `recv_cap` goes in `cap_addr` (the capability used for the receive side).
**Verification**: New test `test_endpoint_reply_recv_syscall_id`
**Risk**: Additive — new function, no breaking changes
**Note**: Must verify argument layout matches `decodeReplyRecvArgs` in
`SyscallArgDecode.lean`.

#### W1-F: Add notification wrapper tests

**File**: New tests in `rust/sele4n-sys/tests/` or inline in `ipc.rs`
**Changes**: Add tests that verify:
1. `notification_signal()` encodes `SyscallId::NotificationSignal` (14)
2. `notification_wait()` encodes `SyscallId::NotificationWait` (15)
3. `endpoint_reply_recv()` encodes `SyscallId::ReplyRecv` (16)
4. `notification_signal()` passes badge in `msg_regs[0]`
**Rationale**: These tests would have caught CRIT-1 and CRIT-2 at development
time. They prevent regression.
**Risk**: None — test-only

#### W1-G: Update Rust documentation and syscall count (MED-05)

**Files**: `rust/sele4n-sys/src/lib.rs`, `rust/sele4n-sys/src/ipc.rs`
**Changes**:
1. Update `lib.rs` header from "all 14 seLe4n syscalls" to "all 17 seLe4n
   syscalls" (original 14 + NotificationSignal, NotificationWait, ReplyRecv)
2. Update `ipc.rs` module header to list all 7 IPC wrappers (adding
   `notification_signal`, `notification_wait`, `endpoint_reply_recv`)
3. Update individual function doc comments to reference current Lean entry
   points (`syscallEntry`/`dispatchSyscall`) rather than removed names
**Verification**: `cargo doc --no-deps` builds without warnings
**Risk**: Documentation-only

#### W1-H: Add cross-crate ABI conformance test

**File**: `rust/sele4n-abi/tests/conformance.rs` (extend existing)
**Changes**: Add tests that automatically detect Lean-Rust enum divergence:
1. `KernelError` variant count assertion: `assert_eq!(KERNEL_ERROR_COUNT, 41)`
2. `SyscallId` variant count assertion: `assert_eq!(SYSCALL_COUNT, 17)`
3. Compile-time `const_assert!` for `MAX_LABEL`, `MAX_MSG_LENGTH`,
   `MAX_EXTRA_CAPS` matching Lean values
**Rationale**: Would have caught HIGH-01 (missing error variant) and provides
ongoing drift detection for all ABI-critical constants.
**Risk**: None — test-only

#### W1-I: Verify Rust test suite passes end-to-end

**Command**: `cd rust && cargo test --workspace`
**Gate check**: All 92+ tests pass (original 92 + new tests from W1-F/W1-H)
**Risk**: None — verification-only

---

## 4. Phase W2 — Proof Formalism & Architecture (HIGH)

**Priority**: HIGH — closes formalism gaps identified by all three audits
**Scope**: `SeLe4n/Kernel/CrossSubsystem.lean`, `SeLe4n/Kernel/API.lean`,
`SeLe4n/Kernel/Service/Operations.lean`
**Gate**: `source ~/.elan/env && lake build` clean, `test_full.sh` green
**Estimated sub-tasks**: 8
**Dependencies**: None (independent of W1)

### Findings Addressed

| Finding | Source Audit(s) | Severity |
|---------|----------------|----------|
| H-1 | FULL_KERNEL | HIGH |
| H-2 | FULL_KERNEL | HIGH |
| MED-04 | LEAN_RUST | MEDIUM |
| M-4 | FULL_KERNEL | MEDIUM |
| M-5 | FULL_KERNEL | MEDIUM |
| M-6 | FULL_KERNEL | MEDIUM |
| M-3 | FULL_KERNEL | MEDIUM |
| L-3 | FULL_KERNEL | LOW |

### Sub-tasks

#### W2-A: Close V6-A field-disjointness formalism (H-2)

**File**: `SeLe4n/Kernel/CrossSubsystem.lean:205-302`
**Problem**: `StateField` enum and `fieldsDisjoint` produce decidable equality
facts, but no theorem proves that field disjointness implies operation-wise
frame independence. The vocabulary exists without closing the proof.
**Change**: Add a frame theorem of the form:
```lean
theorem fieldsDisjoint_implies_preservation
    (hDisj : fieldsDisjoint (predicateFields p₁) (predicateFields p₂) = true)
    (hOp : modifiedFields op ⊆ predicateFields p₁)
    (hPres : p₁ st → p₁ st') :
    p₂ st → p₂ st'
```
If this general form is not achievable (the `modifiedFields` abstraction may
be too coarse for some operations), document precisely why and add a targeted
comment explaining the assurance boundary.
**Build**: `lake build SeLe4n.Kernel.CrossSubsystem`
**Risk**: Medium — may require significant proof engineering. If the general
theorem is infeasible, the fallback is documentation (W2-A-alt).

#### W2-B: Document crossSubsystemInvariant composition gap (H-1)

**File**: `SeLe4n/Kernel/CrossSubsystem.lean:104-123`
**Problem**: The 5-predicate conjunction has no tightness proof. The existing
comment (U6-L / U-M14) acknowledges this but no formal statement exists.
**Change**: Add a formal documentation theorem:
```lean
/-- The 5-predicate conjunction may not be the strongest composite invariant.
    This theorem documents the gap: we do not prove that no additional
    cross-subsystem predicate is needed. -/
theorem crossSubsystemInvariant_composition_gap_documented :
    True := trivial  -- Documentation marker: gap acknowledged, not closed
```
And strengthen the existing comment block to reference W2-A's frame theorem
(if achieved) as partial mitigation.
**Build**: `lake build SeLe4n.Kernel.CrossSubsystem`
**Risk**: Low — documentation-only if W2-A succeeds; medium if W2-A fails
and this must carry the full burden of explanation

#### W2-C: Prove `dispatchWithCap` wildcard arm unreachability (MED-04)

**File**: `SeLe4n/Kernel/API.lean:578-582`
**Problem**: The `| _ => fun _ => .error .illegalState` arm should be provably
unreachable since all 17 `SyscallId` variants are handled either by
`dispatchCapabilityOnly` or the explicit match arms. A comment (V8-H)
documents this but no theorem exists.
**Change**: Add a theorem:
```lean
theorem dispatchWithCap_wildcard_unreachable (sid : SyscallId) :
    dispatchCapabilityOnly sid ... = some _ ∨
    sid ∈ [.send, .receive, .call, .reply, .notificationSignal,
           .notificationWait, .replyRecv]
```
This proves every `SyscallId` variant is handled by one of the two dispatch
mechanisms, making the wildcard arm dead code.
**Build**: `lake build SeLe4n.Kernel.API`
**Risk**: Low — the proof should follow by `decide` or enumeration over all
17 `SyscallId` constructors

#### W2-D: Add fuel sufficiency assertion for `collectQueueMembers` (M-6)

**File**: `SeLe4n/Kernel/CrossSubsystem.lean:40-80`
**Problem**: `collectQueueMembers` uses bounded fuel (`st.objects.size`) but
returns `[]` silently on exhaustion. The traversal may silently stop if the
queue is longer than the object table (impossible by invariant, but unproven).
**Change**: Add a theorem proving fuel sufficiency:
```lean
theorem collectQueueMembers_fuel_sufficient
    (hInv : ipcInvariantFull st)
    (hHead : head = some tid) :
    (collectQueueMembers st.objects head st.objects.size).length
    ≤ st.objects.size
```
Or alternatively, change `noStaleEndpointQueueReferences` to return a `Bool`
witness that includes fuel sufficiency.
**Build**: `lake build SeLe4n.Kernel.CrossSubsystem`
**Risk**: Medium — the proof requires connecting queue length to object table
size via the IPC invariant. May require a helper lemma about queue acyclicity
implying bounded length.

#### W2-E: Document `serviceHasPathTo` fuel exhaustion semantics (M-4)

**File**: `SeLe4n/Kernel/Service/Operations.lean:138-158`
**Problem**: Returns `true` on fuel exhaustion (conservative safety). This is
intentional (H-08/WS-E3) and documented inline, but no formal statement
captures the semantics.
**Change**: Add a documentation theorem and audit the fuel bound:
```lean
/-- Fuel exhaustion conservatively assumes path exists, preventing
    registration of potentially cyclic dependencies. -/
theorem serviceHasPathTo_fuel_exhaustion_conservative :
    serviceHasPathTo.go st visited target 0 = true := by rfl
```
Also verify that the fuel bound (`st.objects.size + 256`) is adequate for
all realistic service graphs. Document the worst-case graph size.
**Build**: `lake build SeLe4n.Kernel.Service.Operations`
**Risk**: Low — documentation + trivial proof

#### W2-F: Strengthen `serviceCountBounded` maintenance documentation (M-5)

**File**: `SeLe4n/Kernel/Service/Invariant/Acyclicity.lean`
**Problem**: `serviceCountBounded` assumes a NoDup list of all services but no
mechanism verifies this across all operations.
**Change**: Add preservation theorems for the key service operations:
```lean
theorem serviceRegisterDependency_preserves_serviceCountBounded ...
theorem serviceRegisterInterface_preserves_serviceCountBounded ...
theorem revokeService_preserves_serviceCountBounded ...
```
Or document which operations preserve this predicate with a comment block
listing the chain.
**Build**: `lake build SeLe4n.Kernel.Service.Invariant.Acyclicity`
**Risk**: Medium — preservation proofs may require threading the NoDup
hypothesis through service registry operations

#### W2-G: Unify enforcement boundary tables (M-3)

**File**: `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean`
**Problem**: `enforcementBoundary` and `enforcementBoundaryExtended` are
identical 22-entry lists with only cardinality correspondence proof, no
element-wise proof. Maintenance debt if one is updated without the other.
**Change**: Either:
1. Merge into a single canonical list (preferred), or
2. Add element-wise correspondence: `theorem enforcementBoundary_eq_extended :
   enforcementBoundary = enforcementBoundaryExtended`
**Build**: `lake build SeLe4n.Kernel.InformationFlow.Enforcement.Wrappers`
**Risk**: Low — if the lists are truly identical, option 2 is trivial by `rfl`

#### W2-H: Reduce `maxHeartbeats` fragility (L-3, FULL_KERNEL L-10, L-14)

**Files**: `Service/Invariant/Acyclicity.lean:355`,
`Scheduler/Operations/Preservation.lean:2266`,
`RobinHood/Invariant/Preservation.lean:1048`
**Problem**: Several proofs use elevated `set_option maxHeartbeats` (400K-1.6M),
indicating fragile proofs that may break with Lean toolchain updates.
**Change**: For each elevated heartbeat setting, investigate whether:
1. A helper lemma can break the proof into smaller steps
2. `simp` calls can be replaced with more targeted `rw`/`exact`
3. The proof structure can be simplified
Document findings. Do not force changes that introduce `sorry`.
**Build**: `lake build <affected module>` for each
**Risk**: Medium — proof optimization is unpredictable. Some elevated heartbeat
settings may be inherent to the problem complexity. Accept and document those.

---

## 5. Phase W3 — Dead Code Elimination (MEDIUM)

**Priority**: MEDIUM — reduces build time, maintenance burden, and false
coverage signals
**Scope**: All `SeLe4n/` Lean files, `SeLe4n/Testing/` files
**Gate**: `test_smoke.sh` green, no `sorry` introduced, module builds pass
**Estimated sub-tasks**: 8
**Dependencies**: None (independent of W1/W2)

### Methodology

The three audits reported dramatically different dead code counts (~450,
~1,194, and ~4). Sample verification showed 62.5% false-positive rate in the
larger counts. This phase uses a **verification-first** approach:

1. **Define "dead"**: A definition is dead if it has zero references outside
   its defining file AND is not a specification-surface theorem (formal
   documentation of a security or correctness property).
2. **Verify before removing**: Each candidate must be grep-verified across the
   entire codebase (`SeLe4n/`, `tests/`, `Main.lean`) before removal.
3. **Preserve spec surface**: Theorems that characterize security properties
   (lattice proofs, authority reduction, invariant bundle projections) are
   retained even if unused, as they serve as machine-checked documentation.
4. **Batch by module**: Remove dead code one module at a time, building after
   each batch to catch hidden dependencies.

### Findings Addressed

| Finding | Source Audit(s) | Severity |
|---------|----------------|----------|
| MED-1/MED-01 (dead code) | PRE_RELEASE, LEAN_RUST | MEDIUM |
| MED-2 (FrozenOps) | PRE_RELEASE | MEDIUM |
| MED-3 (monad orphans) | PRE_RELEASE | MEDIUM |
| LOW-03 (addServiceGraph) | LEAN_RUST | LOW |
| LOW-06 (DeclassAuditLog) | LEAN_RUST | LOW |
| LOW-07 (RegisterWriteInv) | LEAN_RUST | LOW |
| LOW-08 (ServicePolicyPred) | LEAN_RUST | LOW |
| L-1 (maxServiceFuel) | FULL_KERNEL | LOW |
| L-9 (unused projection thms) | FULL_KERNEL | LOW |

### Sub-tasks

#### W3-A: Build verified dead code inventory

**Scope**: Entire `SeLe4n/` directory
**Method**: For each `def`/`theorem`/`lemma`/`abbrev` in the codebase:
1. Grep for the identifier name across all `.lean` files
2. Exclude the definition site itself
3. If zero external references, classify as:
   - **Category A (remove)**: Internal helper with no specification value
   - **Category B (keep)**: Specification-surface theorem (security property,
     invariant characterization, lattice proof, authority reduction)
   - **Category C (defer)**: Platform scaffolding for future hardware binding
**Output**: A categorized list in a scratch file, used by W3-B through W3-F
**Risk**: Low — read-only analysis

#### W3-B: Remove confirmed dead helpers — Foundation layer

**Files**: `Prelude.lean`, `Machine.lean`, `Model/Object/Types.lean`,
`Model/Object/Structures.lean`, `Model/State.lean`
**Candidates** (verified dead from audit + sample check):
- `Prelude.lean`: Monad law proofs (`pure_bind_law`, `bind_pure_law`,
  `bind_assoc_law`, `get_returns_state`, `set_replaces_state`,
  `modify_applies_function`, `liftExcept_ok`, `liftExcept_error`,
  `throw_errors`) — these are orphaned. If a `LawfulMonad` instance is
  desired, wire them in (W3-B-alt); otherwise remove.
- `Machine.lean`: Unused alignment definitions (`wordAligned`, `pageAligned`
  and associated proofs), unused RAM model (`totalRAM`, `addressInMap`),
  unused config helpers — verify each before removal
- `Types.lean`: Duplicate constants (`maxLength`, `maxExtraCaps'`), unused
  `UntypedObject` proofs — verify each
- `Structures.lean`: Unused CDT navigation helpers (`isChildOf`, `isParentOf`,
  `parentOf`, `removeAsChild`, `removeAsParent`, `isAncestor`), unused
  `makeObjectCap` — verify each
- `State.lean`: Unused type aliases (`CSpaceOwner` — verify internal use first),
  unused observation helpers (`observedCdtEdges`, `ownerOfSlot`, `ownedSlots`)
**Process**: Remove in batches of ~10 definitions per file. After each batch:
`lake build <Module.Path>`. If build fails, restore and investigate.
**Build**: `lake build SeLe4n.Prelude`, `lake build SeLe4n.Machine`, etc.
**Risk**: Low — each removal is individually verified

#### W3-C: Remove confirmed dead helpers — Kernel subsystems

**Files**: `Scheduler/RunQueue.lean`, `Scheduler/Invariant.lean`,
`Capability/Operations.lean`, `Lifecycle/Operations.lean`,
`Service/Operations.lean`, `Service/Registry.lean`
**Candidates**: Items listed in PRE_RELEASE audit's "Kernel Subsystems" section
(~140 candidates), but each must be verified before removal. Key targets:
- `RunQueue.lean`: `atPriority` (verified dead), rotation membership proofs
- `Capability/Operations.lean`: `resolveCapAddressK`, `hasCdtChildren`,
  `severDerivationEdge` — verify each
- `Lifecycle/Operations.lean`: `lifecycleRetypeAuthority`,
  `cleanupTcbReferences` + proofs, `lookupUntyped` — verify each
- `Service/Operations.lean`: `maxServiceFuel` (verified dead)
- `Service/Registry.lean`: Error/success proofs that are never composed
**Process**: Same batch-and-build methodology as W3-B
**Build**: `lake build <Module.Path>` for each affected module
**Risk**: Low — individually verified removals

#### W3-D: Remove confirmed dead helpers — Architecture & Info Flow

**Files**: `Architecture/VSpace.lean`, `Architecture/TlbModel.lean`,
`InformationFlow/Policy.lean`, `InformationFlow/Projection.lean`,
`InformationFlow/Enforcement/Wrappers.lean`
**Candidates**:
- `VSpace.lean`: Unused ASID bound helpers, unused TLB flush variants
- `TlbModel.lean`: Most definitions are unused externally but form a coherent
  TLB consistency theory. **Classify as Category B (keep)** unless the TLB
  model is not planned for H3 integration.
- `Policy.lean`: Unused lattice proofs, unused legacy label functions. Many
  of these are spec-surface (Category B). Only remove clearly internal helpers.
- `Projection.lean`: `projectStateFast` and fast projection variants (unused)
- `Wrappers.lean`: `capabilityOnlyOperations`, `enforcementBoundaryComplete_counts`,
  `enforcementBoundary_names_nonempty` — verify
**Build**: `lake build <Module.Path>` for each
**Risk**: Low-Medium — Info Flow spec-surface decisions require judgment

#### W3-E: Remove confirmed dead helpers — Data structures & Platform

**Files**: `FrozenOps/Core.lean`, `FrozenOps/Commutativity.lean`,
`RobinHood/Bridge.lean`, `RobinHood/Set.lean`, `RadixTree/Core.lean`,
`Platform/Boot.lean`, `Platform/RPi5/Board.lean`
**Candidates**:
- `FrozenOps/Core.lean`: Typed lookup/store helpers (`frozenLookupEndpoint`,
  etc.) — verify if used by Operations.lean internally
- `FrozenOps/Commutativity.lean`: Frame lemmas — verify
- `RobinHood/Set.lean`: `RHSet` accessors and proofs — verify
- `RobinHood/Bridge.lean`: `ofList` proofs, `invExtK` bridge proofs — verify
- `RadixTree/Core.lean`: `extractBits_zero_width` — verify
- `Boot.lean`: Frame lemmas (`bootFromPlatform_scheduler_eq`, etc.), empty
  boot proofs — many are spec-surface, classify carefully
- `RPi5/Board.lean`: Unused constants (`peripheralBaseLow/High`,
  `bcm2712DefaultConfig`) — classify as Category C (platform scaffolding)
**Build**: `lake build <Module.Path>` for each
**Risk**: Low — individually verified

#### W3-F: Remove confirmed dead helpers — Testing layer

**Files**: `SeLe4n/Testing/StateBuilder.lean`
**Candidates**: `listLookup`, `withMachine`, `buildValidated` (all verified dead)
**Build**: `lake build SeLe4n.Testing.StateBuilder`
**Risk**: Minimal

#### W3-G: Evaluate FrozenOps subsystem status

**Files**: `SeLe4n/Kernel/FrozenOps/*.lean` (4 files)
**Problem**: FrozenOps has zero production consumers. Only test files use it.
However, it provides architectural validation for the two-phase state model.
**Decision tree**:
1. If FrozenOps is planned for integration into the kernel runtime path before
   H3: **keep**, document timeline
2. If FrozenOps is architectural proof-of-concept only: **keep but move** to a
   `SeLe4n/Kernel/FrozenOps/` subdirectory with a README explaining its status
   (it already lives there, just add documentation)
3. If FrozenOps provides no ongoing value: **remove** (saves ~29 definitions
   and ~4 files of build time)
**Recommendation**: Option 2 — keep with documentation. The frozen-state model
validates the builder→frozen transition and its commutativity proofs support
the FreezeProofs module's correctness argument.
**Build**: `test_smoke.sh` after any changes
**Risk**: Low

#### W3-H: Remove unused type aliases and abbreviations

**Files**: Multiple (cross-cutting)
**Candidates** (verified dead):
- `DeclassificationAuditLog` in `Policy.lean:638`
- `RegisterWriteInvariant` in `RPi5/RuntimeContract.lean:178`
- `ServicePolicyPredicate` in `Service/Invariant/Policy.lean:30`
- `addServiceGraph` in `Model/Builder.lean:122`
- `encodeMsgRegs` in `Architecture/RegisterDecode.lean:51-52`
**Build**: `lake build <Module.Path>` for each
**Risk**: Minimal — verified dead abbreviations

---

## 6. Phase W4 — Platform & Architecture Hardening (MEDIUM)

**Priority**: MEDIUM — pre-H3 hardware binding readiness
**Scope**: `SeLe4n/Platform/`, `SeLe4n/Kernel/Architecture/`
**Gate**: Module builds pass, `test_smoke.sh` green
**Estimated sub-tasks**: 7
**Dependencies**: None (independent of W1-W3)

### Findings Addressed

| Finding | Source Audit(s) | Severity |
|---------|----------------|----------|
| M-8 | FULL_KERNEL | MEDIUM |
| M-9 | FULL_KERNEL | MEDIUM |
| MED-02 | LEAN_RUST | MEDIUM |
| L-15 | FULL_KERNEL | LOW |
| L-16 | FULL_KERNEL | LOW |
| LOW-02 | LEAN_RUST | LOW |
| L-12 | FULL_KERNEL | LOW |

### Sub-tasks

#### W4-A: Complete BCM2712 datasheet validation checklist (M-8)

**File**: `SeLe4n/Platform/RPi5/Board.lean:213-298`
**Problem**: S5-F checklist marks all BCM2712 address constants as "Pending"
while S6-G claims "Validated" with no datasheet citations. Must be resolved
before H3 hardware binding.
**Change**: For each constant (`peripheralBase`, `gic400Base`, `uartBase`,
`timerBase`, etc.), add inline comments with:
1. Datasheet title and revision (e.g., "BCM2712 Peripherals Rev 1.0")
2. Page/section reference
3. Date of verification
If datasheets are not available, document which constants are extrapolated
from BCM2711 and flag for hardware bring-up verification.
**Build**: `lake build SeLe4n.Platform.RPi5.Board`
**Risk**: Low — documentation-only changes to Lean file

#### W4-B: Harden FDT parsing against integer overflow (M-9)

**File**: `SeLe4n/Platform/DeviceTree.lean:180-185`
**Problem**: `readBE32` field additions (`offset + 1`, `offset + 4`) could
overflow on malformed DTB input. Currently safe due to bounds checks on
individual byte accesses, but the arithmetic could produce unexpected values.
**Change**: Add explicit bounds validation before arithmetic:
```lean
if offset + 4 > blob.size then none
else ...
```
Ensure all `readBE32`, `readBE64`, `readCells`, and `readCString` have
overflow-safe index computation.
**Build**: `lake build SeLe4n.Platform.DeviceTree`
**Risk**: Low — defensive hardening, no semantic change

#### W4-C: Investigate `native_decide` elimination for RPi5 board proofs (MED-02)

**Files**: `SeLe4n/Platform/RPi5/Board.lean` (2 instances)
**Problem**: `mmioRegionDisjoint_holds` and `rpi5MachineConfig_wellFormed` use
`native_decide` which expands the TCB. Boot.lean's 3 instances are justified
(HashSet opacity), but RPi5 proofs may work with `decide` if `DecidableEq`
instances are properly derived.
**Change**: Attempt to replace `native_decide` with `decide` for:
1. `mmioRegionDisjoint_holds` (line 171)
2. `rpi5MachineConfig_wellFormed` (line 176)
If `decide` works (finishes within reasonable heartbeats), use it. If not,
document why `native_decide` is required and add to the "accepted
`native_decide`" list.
**Build**: `lake build SeLe4n.Platform.RPi5.Board`
**Risk**: Low — if `decide` times out, keep `native_decide` with documentation

#### W4-D: Fix stale `@[implemented_by]` comment in DeviceTree (LOW-02)

**File**: `SeLe4n/Platform/DeviceTree.lean:134-135`
**Problem**: Comment says "Overridden by fromDtbFull via @[implemented_by]"
but no `@[implemented_by]` attribute exists. The function returns `none`.
**Change**: Remove the stale comment. If `fromDtbFull` is intended to replace
`fromDtb`, add the `@[implemented_by]` attribute. If not, update the comment
to "Stub — returns none. Production DTB parsing deferred to H3."
**Build**: `lake build SeLe4n.Platform.DeviceTree`
**Risk**: Minimal

#### W4-E: Deprecate `bootFromPlatformUnchecked` (L-15)

**File**: `SeLe4n/Platform/Boot.lean`
**Problem**: `bootFromPlatformUnchecked` uses last-wins semantics on duplicates,
while `bootFromPlatformChecked` validates `PlatformConfig.wellFormed`.
**Change**: Add a deprecation comment:
```lean
/-- Deprecated: Use `bootFromPlatformChecked` for production boot paths.
    This function does not validate PlatformConfig.wellFormed and uses
    last-wins semantics on duplicate object IDs. Retained for testing only. -/
```
Do NOT remove — test suites may depend on the unchecked path for invalid-state
testing.
**Build**: `lake build SeLe4n.Platform.Boot`
**Risk**: Minimal — comment-only

#### W4-F: Document MMIO formalization gap (L-16)

**File**: `SeLe4n/Platform/RPi5/MmioAdapter.lean:185-195`
**Problem**: MMIO volatile/writeOneClear semantics not fully formalized.
**Change**: Add a documentation block explaining the formalization boundary:
which MMIO semantics are modeled (alignment, region bounds) vs. which are
deferred to hardware bring-up (volatile ordering, write-1-to-clear behavior,
device-specific register semantics).
**Build**: `lake build SeLe4n.Platform.RPi5.MmioAdapter`
**Risk**: Minimal — documentation-only

#### W4-G: Remove unused `encodeMsgRegs` identity function (L-12)

**File**: `SeLe4n/Kernel/Architecture/RegisterDecode.lean:51-52`
**Problem**: Defined as identity for "proof-surface completeness" but never
used anywhere.
**Change**: Remove the definition. If future proof chains need an identity
encoding, it can be re-introduced when there's a consumer.
**Build**: `lake build SeLe4n.Kernel.Architecture.RegisterDecode`
**Risk**: Minimal — verified dead

---

## 7. Phase W5 — Test Infrastructure & Coverage (MEDIUM)

**Priority**: MEDIUM — improves regression safety and catches future ABI drift
**Scope**: `tests/`, `SeLe4n/Testing/`, `rust/` test directories
**Gate**: All test suites pass
**Estimated sub-tasks**: 8
**Dependencies**: W1 (new Rust wrappers need tests)

### Findings Addressed

| Finding | Source Audit(s) | Severity |
|---------|----------------|----------|
| M-10 | FULL_KERNEL | MEDIUM |
| M-11 | FULL_KERNEL | MEDIUM |
| L-17 | FULL_KERNEL | LOW |
| L-18 | FULL_KERNEL | LOW |
| L-7 | FULL_KERNEL | LOW |
| L-2 | FULL_KERNEL | LOW |

### Sub-tasks

#### W5-A: Consolidate `expectError` implementations (M-10)

**Files**: `tests/NegativeStateSuite.lean:129`, `tests/OperationChainSuite.lean:48`,
`SeLe4n/Testing/Helpers.lean:31`
**Problem**: Three separate `expectError` implementations create inconsistency
risk. The canonical version exists in `Helpers.lean`.
**Change**:
1. Remove `private def expectError` from `NegativeStateSuite.lean`
2. Remove `private def expectError` from `OperationChainSuite.lean`
3. Ensure both suites import `SeLe4n.Testing.Helpers` and use the canonical version
4. Verify all call sites produce identical behavior (check error message format)
**Build**: `lake build negative_state_suite && lake build operation_chain_suite`
**Risk**: Low — may need minor signature adjustments if the private versions
had slightly different behavior

#### W5-B: Document test fixture OID ranges (L-17)

**Files**: All test suite files (`tests/*.lean`)
**Problem**: Test suites use different OID ranges (MainTrace: 1-40,
OperationChain: 200-300, NegativeState: 6-42) with no collision documentation.
**Change**: Add a comment block to each test suite header declaring its
reserved OID range, and add a summary table to `SeLe4n/Testing/Helpers.lean`:
```lean
/-- Test fixture OID ranges (prevent collisions between suites):
    MainTraceHarness:     1-40   (threads: 1-5, objects: 6-40)
    OperationChainSuite:  200-300
    NegativeStateSuite:   6-42   (NOTE: overlaps MainTrace — runs independently)
    FrozenOpsSuite:       100-150
    ...
-/
```
**Risk**: Minimal — documentation-only

#### W5-C: Add service lifecycle tests (L-18)

**File**: `tests/OperationChainSuite.lean` (extend) or new `tests/ServiceSuite.lean`
**Problem**: Service lifecycle operations (start/stop/restart/dependency chains)
are completely absent from testing.
**Change**: Add test scenarios covering:
1. Service registration success path
2. Service registration with duplicate rejection
3. Service dependency registration (acyclic)
4. Service dependency registration (cyclic — should reject)
5. Service revocation and cleanup
6. Service query by capability
**Build**: `lake build operation_chain_suite` (or new suite)
**Risk**: Low — additive tests

#### W5-D: Improve `buildChecked` error reporting (M-11)

**File**: `SeLe4n/Testing/StateBuilder.lean:174-177`
**Problem**: `buildChecked` uses `panic!` on invariant violation instead of
returning a descriptive error.
**Change**: Convert `buildChecked` to return `Except String SystemState`
instead of panicking. Update call sites to handle the error explicitly.
If this is too disruptive (many test suites use `.build` not `.buildChecked`),
at minimum improve the panic message to include which invariant failed.
**Build**: `lake build SeLe4n.Testing.StateBuilder`
**Risk**: Medium if return type changes — ripple through test suites

#### W5-E: Add weak mutation testing documentation (FULL_KERNEL testing gaps)

**File**: `tests/OperationChainSuite.lean`
**Problem**: Some operations verified for success without checking actual state
mutation (e.g., chain5).
**Change**: For each `expectOk` assertion that lacks a post-state check, add
a comment `-- TODO: verify post-state mutation` or add the actual assertion.
Priority targets:
1. Operations that modify thread state (verify TCB fields changed)
2. Operations that modify capability state (verify slot contents changed)
3. Operations that modify queue membership (verify queue containment)
**Build**: `lake build operation_chain_suite`
**Risk**: Low — additive assertions

#### W5-F: Remove unused `_hCap` parameter (L-2)

**File**: `SeLe4n/Kernel/Service/Invariant/Policy.lean:102-112`
**Problem**: `_hCap` parameter in `policyOwnerAuthoritySlotPresent_of_capabilityLookup`
is unused.
**Change**: Remove the unused parameter if it doesn't affect the theorem's
public API. If external proofs pass this parameter, add `_` prefix to
suppress the warning instead.
**Build**: `lake build SeLe4n.Kernel.Service.Invariant.Policy`
**Risk**: Low — may have downstream callers passing the argument

#### W5-G: Add `resolveExtraCaps` silent-drop documentation (L-7)

**File**: `SeLe4n/Kernel/API.lean:327-337`
**Problem**: `resolveExtraCaps` silently drops failed capability resolutions,
matching seL4 but limiting debuggability.
**Change**: Add an inline documentation comment explaining the design choice
and its implications:
```lean
/-- Resolves extra capabilities from IPC buffer. Failed resolutions are
    silently dropped (matching seL4 `lookupExtraCaps` behavior). This means
    the receiver gets fewer extra caps than the sender specified. For
    debugging, callers should check `extraCaps.length` against expected. -/
```
**Build**: `lake build SeLe4n.Kernel.API`
**Risk**: Minimal — documentation-only

#### W5-H: Verify Lean test suites pass end-to-end

**Command**: `./scripts/test_smoke.sh`
**Gate check**: All tiers 0-2 pass
**Risk**: None — verification-only

---

## 8. Phase W6 — Code Quality & Documentation (LOW)

**Priority**: LOW — improves maintainability without affecting correctness
**Scope**: Multiple files across all layers
**Gate**: `test_fast.sh` green, documentation consistent
**Estimated sub-tasks**: 12
**Dependencies**: W3 (dead code removal changes line counts for docs)

### Findings Addressed

| Finding | Source Audit(s) | Severity |
|---------|----------------|----------|
| M-7 | FULL_KERNEL | MEDIUM |
| LOW-1 | PRE_RELEASE | LOW |
| LOW-2 | PRE_RELEASE | LOW |
| L-4 | FULL_KERNEL | LOW |
| L-6 | FULL_KERNEL | LOW |
| L-8 | FULL_KERNEL | LOW |
| L-11 | FULL_KERNEL | LOW |
| L-13 | FULL_KERNEL | LOW |
| LOW-01 | LEAN_RUST | LOW |
| LOW-04 | LEAN_RUST | LOW |
| H-3 (downgraded) | FULL_KERNEL | LOW |

### Sub-tasks

#### W6-A: Add TCB existence assertion to `removeThreadFromQueue` (M-7)

**File**: `SeLe4n/Kernel/Lifecycle/Operations.lean:37-42`
**Problem**: Falls back to `(none, none)` if TCB lookup fails during cleanup.
Should log/assert TCB existence rather than silently degrading.
**Change**: Add a documentation comment explaining the fallback rationale:
```lean
/-- Defensive fallback: if TCB lookup fails during thread removal, treat as
    already-removed. This can only occur if the TCB was deleted concurrently
    (impossible in the single-threaded kernel model), or if the invariant
    `runnableThreadsAreTCBs` was violated. The fallback is safe but masks
    invariant violations. -/
```
If appropriate, change the fallback to return an error instead of `(none, none)`.
**Build**: `lake build SeLe4n.Kernel.Lifecycle.Operations`
**Risk**: Low if documentation-only; Medium if changing behavior

#### W6-B: Factor redundant lifecycle preservation proofs (L-4)

**File**: `SeLe4n/Kernel/Lifecycle/Operations.lean:127-203`
**Problem**: 77 lines of redundant preservation proofs (3 cleanup ops × 3+
fields) with identical proof structure.
**Change**: Extract a parameterized lemma:
```lean
theorem cleanup_preserves_field (op : SystemState → Except KernelError SystemState)
    (field : SystemState → α)
    (hEq : ∀ st st', op st = .ok st' → field st' = field st) :
    ...
```
Then instantiate for each cleanup/field combination.
**Build**: `lake build SeLe4n.Kernel.Lifecycle.Operations`
**Risk**: Medium — proof refactoring may be more complex than expected

#### W6-C: Simplify redundant CrossSubsystem triple (L-6)

**File**: `SeLe4n/Kernel/CrossSubsystem.lean:164-172`
**Problem**: Redundant triple: definition + predicate list + equivalence proof
for the same 5-tuple.
**Change**: Remove the predicate list and equivalence proof, keeping only the
primary definition. Update any consumers.
**Build**: `lake build SeLe4n.Kernel.CrossSubsystem`
**Risk**: Low — verify no consumers of the predicate list

#### W6-D: Document double-dispatch structure in API (L-8)

**File**: `SeLe4n/Kernel/API.lean:435-499`
**Problem**: Double-dispatch structure (`dispatchCapabilityOnly` + match) could
be flattened, but the current design serves a purpose (W2-C proves the split).
**Change**: Add documentation comment explaining the design rationale:
```lean
/-- Two-tier dispatch: `dispatchCapabilityOnly` handles syscalls that need
    only the resolved capability (no additional arguments), while the match
    arms handle syscalls requiring decoded arguments. This split enables the
    wildcard unreachability proof (W2-C) and shares the checked/unchecked
    dispatch implementations (V8-H). -/
```
**Build**: `lake build SeLe4n.Kernel.API`
**Risk**: Minimal — documentation-only

#### W6-E: Extract default-state proof helper (L-11)

**File**: `SeLe4n/Kernel/Architecture/Invariant.lean:228-279`
**Problem**: 24 identical default-state proof patterns.
**Change**: Extract a helper:
```lean
theorem default_preserves_invariant_field (f : SystemState → Prop)
    (hDef : f default) : f default := hDef
```
Or more usefully, a tactic macro that handles the common pattern. Evaluate
whether the refactoring saves meaningful lines vs. adding abstraction.
**Build**: `lake build SeLe4n.Kernel.Architecture.Invariant`
**Risk**: Low — but may not be worth the abstraction if patterns are trivial

#### W6-F: Add `RHSet.invExtK` public preservation theorems (L-13)

**File**: `SeLe4n/Kernel/RobinHood/Set.lean`
**Problem**: `RHSet.invExtK` lacks public preservation theorems. Kernel code
accesses `table.table` directly, bypassing the `RHSet` abstraction.
**Change**: Add preservation theorems for `insert` and `erase`:
```lean
theorem RHSet.insert_preserves_invExtK ...
theorem RHSet.erase_preserves_invExtK ...
```
These delegate to the underlying `RHTable` preservation proofs.
**Build**: `lake build SeLe4n.Kernel.RobinHood.Set`
**Risk**: Low — thin wrappers around existing proofs

#### W6-G: Add `const_assert!` for Lean-Rust constant sync (LOW-1)

**File**: `rust/sele4n-abi/src/message_info.rs` (or new `constants.rs`)
**Problem**: If `maxLabel` were changed independently on Lean or Rust side,
decode would silently diverge.
**Change**: Add compile-time assertions:
```rust
const_assert!(MAX_LABEL == 1_048_575);  // 2^20 - 1
const_assert!(MAX_MSG_LENGTH == 120);
const_assert!(MAX_EXTRA_CAPS == 3);
```
**Risk**: Minimal — compile-time checks

#### W6-H: Improve `IpcBuffer.set_mr` consistency (LOW-2, LEAN_RUST)

**File**: `rust/sele4n-abi/src/ipc_buffer.rs:86`
**Problem**: `set_mr(0..3)` returns `Ok(false)` (silent no-op) while
`get_mr(0..3)` returns `Err(InvalidArgument)` — asymmetric API.
**Change**: Either:
1. Return `Err(InvalidArgument)` from `set_mr` for indices 0-3 (match `get_mr`)
2. Add prominent doc comment explaining the split interface
**Recommendation**: Option 2 — changing the return type would break existing
callers and the current behavior is safe.
**Risk**: Low for option 2; Medium for option 1 (breaking change)

#### W6-I: Document CDT edge theorem preservation (LOW-04)

**File**: `SeLe4n/Model/Object/Structures.lean`
**Problem**: ~44 CDT edge theorems form a complete but unused proof suite.
**Change**: Add a documentation header to the CDT section:
```lean
/-- CDT edge theorems: Complete proof suite for capability derivation tree
    edge operations. Currently unused by the kernel proof chain (operations
    use hypothesis-carrying patterns instead). Retained as specification
    surface for CDT correctness. -/
```
**Risk**: Minimal — documentation-only

#### W6-J: Document Prelude RHTable theorem status (LOW-01)

**File**: `SeLe4n/Prelude.lean:916-1049`
**Problem**: 29 RHTable theorems in Prelude are unused but may be spec-surface.
**Change**: Add a section header comment:
```lean
/-- RHTable specification surface theorems: These characterize RHTable
    behavior for external reasoning. They are not currently composed into
    the kernel proof chain but serve as machine-checked documentation of
    hash table properties. See RobinHood/Invariant/ for the actively-used
    proof infrastructure. -/
```
**Risk**: Minimal — documentation-only

#### W6-K: Document lifecycle metadata enforcement chain (H-3 downgraded)

**File**: `SeLe4n/Kernel/Lifecycle/Invariant.lean:80-83`
**Problem**: `lifecycleCapabilityRefObjectTargetBacked` relies on pre-retype
cleanup contract rather than automatic enforcement.
**Change**: Add documentation tracing the enforcement chain:
```lean
/-- Enforcement chain for metadata backing:
    1. `lifecyclePreRetypeCleanup` calls `revokeAndClearRefsState`
    2. `revokeAndClearRefsState` clears all metadata references for the target
    3. `lifecycleRetypeObject` only creates new metadata after cleanup
    Invariant is maintained by contract discipline, not automatic enforcement.
    All retype paths go through `lifecycleRetypeDirectWithCleanup` which
    calls cleanup before retyping. -/
```
**Build**: `lake build SeLe4n.Kernel.Lifecycle.Invariant`
**Risk**: Minimal — documentation-only

#### W6-L: Sync documentation after changes

**Files**: `README.md`, `docs/spec/SELE4N_SPEC.md`, `CHANGELOG.md`,
`docs/WORKSTREAM_HISTORY.md`, `docs/codebase_map.json`
**Changes**:
1. Update `WORKSTREAM_HISTORY.md` to add WS-W entry
2. Update `CHANGELOG.md` with version bump for W1 fixes
3. Regenerate `docs/codebase_map.json` if Lean sources changed
4. Sync `README.md` metrics if definition counts changed (W3)
5. Update `docs/CLAIM_EVIDENCE_INDEX.md` if any claims changed
**Risk**: Low — documentation sync

---

## 9. Dependency Graph & Implementation Order

```
W1 (BLOCKER) ──────────────────────────────────┐
  W1-A (CRIT-1 fix)                            │
  W1-B (CRIT-2 fix)                            │
  W1-C (badge ABI) ──depends on──► W1-A        │
  W1-D (mmioUnaligned)                          │
  W1-E (ReplyRecv wrapper)                      │
  W1-F (notification tests) ──► W1-A,B,C,E     │
  W1-G (doc update) ──► W1-E                    │
  W1-H (conformance tests) ──► W1-D             │
  W1-I (verify all) ──► W1-A through W1-H      │
                                                │
W2 (HIGH) ─── parallel with W1 ────────────────┤
  W2-A (field-disjointness)                     │
  W2-B (composition gap doc) ──► W2-A           │
  W2-C (wildcard unreachability)                │
  W2-D (fuel sufficiency)                       │
  W2-E (serviceHasPathTo doc)                   │
  W2-F (serviceCountBounded)                    │
  W2-G (enforcement boundary)                   │
  W2-H (heartbeat reduction)                    │
                                                │
W3 (MEDIUM) ─── parallel with W1/W2 ───────────┤
  W3-A (build inventory) ──► first              │
  W3-B (foundation dead code) ──► W3-A          │
  W3-C (kernel dead code) ──► W3-A              │
  W3-D (arch/IF dead code) ──► W3-A             │
  W3-E (data struct/platform) ──► W3-A          │
  W3-F (testing dead code) ──► W3-A             │
  W3-G (FrozenOps evaluation) ──► W3-A          │
  W3-H (type aliases) ──► W3-A                  │
                                                │
W4 (MEDIUM) ─── parallel with W1/W2/W3 ────────┤
  W4-A through W4-G (all independent)           │
                                                │
W5 (MEDIUM) ─── depends on W1 ─────────────────┤
  W5-A (expectError consolidation)              │
  W5-B (OID range docs)                         │
  W5-C (service tests)                          │
  W5-D (buildChecked improvement)               │
  W5-E (mutation testing docs)                  │
  W5-F (unused parameter)                       │
  W5-G (resolveExtraCaps doc)                   │
  W5-H (verify all) ──► W5-A through W5-G      │
                                                │
W6 (LOW) ─── depends on W3 ────────────────────┘
  W6-A through W6-K (most independent)
  W6-L (doc sync) ──► ALL prior phases
```

### Recommended Execution Order

**Sprint 1** (Pre-release blocker):
- W1-A, W1-B, W1-D in parallel (3 independent Rust fixes)
- W1-C after W1-A (badge decision + implementation)
- W1-E (ReplyRecv wrapper)
- W1-F, W1-G, W1-H after fixes land
- W1-I gate check

**Sprint 2** (Parallel tracks):
- **Track A** (Proof): W2-C, W2-E, W2-G (quick wins), then W2-A (hard), W2-B
- **Track B** (Dead code): W3-A inventory, then W3-B through W3-H in sequence
- **Track C** (Platform): W4-A through W4-G (all independent)

**Sprint 3** (Test & quality):
- W5-A through W5-H (test infrastructure)
- W2-D, W2-F, W2-H (remaining proof tasks)

**Sprint 4** (Cleanup):
- W6-A through W6-L (code quality and documentation)

---

## 10. Risk Summary

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| W1-C badge ABI breaks Rust consumers | Medium | High | Version bump, migration guide |
| W2-A frame theorem infeasible | Medium | Low | Fall back to documentation (W2-B) |
| W3 false-positive dead code removal | Low | Medium | Verify-before-remove methodology |
| W2-H heartbeat reduction breaks proofs | Low | Low | Accept current settings if optimization fails |
| W5-D buildChecked type change ripple | Medium | Medium | Fall back to improved panic message |
| W4-C native_decide elimination timeout | Medium | Low | Keep native_decide with documentation |

---

## 11. Completion Criteria

The WS-W portfolio is complete when:

1. **All Rust tests pass** (`cargo test --workspace` — 95+ tests)
2. **All Lean modules build** (`source ~/.elan/env && lake build`)
3. **Zero sorry/axiom** in production proof surface
4. **`test_full.sh` passes** (Tiers 0-3)
5. **All 49 actionable findings** are either resolved or documented with
   rationale for deferral
6. **Documentation synchronized** (WORKSTREAM_HISTORY, CHANGELOG, README)
7. **No website-linked paths** renamed or removed

---

## Appendix A: Finding Cross-Reference Matrix

This matrix maps every finding from the three audits to its disposition in this
workstream plan.

### PRE_RELEASE Audit Findings

| Finding | Severity | Disposition | Phase |
|---------|----------|-------------|-------|
| CRIT-1 | CRITICAL | Fix | W1-A |
| CRIT-2 | CRITICAL | Fix | W1-B |
| HIGH-1 | HIGH | Fix | W1-D |
| MED-1 | MEDIUM | Overstated (ERR-1) — partial action | W3 |
| MED-2 | MEDIUM | Evaluate | W3-G |
| MED-3 | MEDIUM | Remove or wire in | W3-B |
| LOW-1 | LOW | Const assert | W6-G |
| LOW-2 | LOW | Document | W6-H |

### LEAN_RUST Audit Findings

| Finding | Severity | Disposition | Phase |
|---------|----------|-------------|-------|
| CRIT-01 | CRITICAL | Fix (= CRIT-1) | W1-A |
| CRIT-02 | CRITICAL | Fix (= CRIT-2) | W1-B |
| HIGH-01 | HIGH | Fix (= HIGH-1) | W1-D |
| HIGH-02 | HIGH | Design decision + fix | W1-C |
| MED-01 | MEDIUM | Overstated (ERR-1) — partial action | W3 |
| MED-02 | MEDIUM | Investigate | W4-C |
| MED-03 | MEDIUM | Add wrapper | W1-E |
| MED-04 | MEDIUM | Prove | W2-C |
| MED-05 | MEDIUM | Update docs | W1-G |
| LOW-01 | LOW | Document | W6-J |
| LOW-02 | LOW | Not actionable (ERR-7) | — |
| LOW-03 | LOW | Remove | W3-H |
| LOW-04 | LOW | Document | W6-I |
| LOW-05 | LOW | Not actionable (ERR-7) | — |
| LOW-06 | LOW | Remove | W3-H |
| LOW-07 | LOW | Remove | W3-H |
| LOW-08 | LOW | Remove | W3-H |
| INFO-01 through INFO-06 | INFO | No action | — |

### FULL_KERNEL Audit Findings

| Finding | Severity | Disposition | Phase |
|---------|----------|-------------|-------|
| H-1 | HIGH | Document | W2-B |
| H-2 | HIGH | Prove or document | W2-A |
| H-3 | HIGH | Downgraded to LOW — document | W6-K |
| M-1 | MEDIUM | Not actionable (ERR-6) | — |
| M-2 | MEDIUM | Not actionable (ERR-5) | — |
| M-3 | MEDIUM | Unify | W2-G |
| M-4 | MEDIUM | Document | W2-E |
| M-5 | MEDIUM | Strengthen | W2-F |
| M-6 | MEDIUM | Prove fuel sufficiency | W2-D |
| M-7 | MEDIUM | Document/fix fallback | W6-A |
| M-8 | MEDIUM | Datasheet validation | W4-A |
| M-9 | MEDIUM | Harden parsing | W4-B |
| M-10 | MEDIUM | Consolidate | W5-A |
| M-11 | MEDIUM | Improve error reporting | W5-D |
| L-1 | LOW | Remove (= confirmed dead) | W3-C |
| L-2 | LOW | Remove unused param | W5-F |
| L-3 | LOW | Reduce heartbeats | W2-H |
| L-4 | LOW | Factor proofs | W6-B |
| L-5 | LOW | Not actionable (ERR-8) | — |
| L-6 | LOW | Simplify triple | W6-C |
| L-7 | LOW | Document | W5-G |
| L-8 | LOW | Document | W6-D |
| L-9 | LOW | Remove | W3-D |
| L-10 | LOW | Reduce heartbeats | W2-H |
| L-11 | LOW | Extract helper | W6-E |
| L-12 | LOW | Remove | W4-G |
| L-13 | LOW | Add preservation theorems | W6-F |
| L-14 | LOW | Reduce heartbeats | W2-H |
| L-15 | LOW | Deprecate | W4-E |
| L-16 | LOW | Document | W4-F |
| L-17 | LOW | Document | W5-B |
| L-18 | LOW | Add tests | W5-C |
| Dead-1..4 | — | Remove | W3 |

---

## Appendix B: Sub-task Count Summary

| Phase | Sub-tasks | Est. Files Modified | Risk Level |
|-------|-----------|-------------------|------------|
| W1 | 9 | ~8 Rust files | Low (mostly single-line fixes) |
| W2 | 8 | ~6 Lean files | Medium (proof engineering) |
| W3 | 8 | ~30+ Lean files | Low (verified removals) |
| W4 | 7 | ~5 Lean files | Low (documentation + hardening) |
| W5 | 8 | ~8 files (Lean + Rust) | Low-Medium |
| W6 | 12 | ~12 files (Lean + Rust + docs) | Low |
| **Total** | **52** | **~60+ files** | |

---

*End of workstream plan.*
