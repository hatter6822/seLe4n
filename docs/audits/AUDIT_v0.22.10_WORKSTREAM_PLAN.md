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
via `requireMsgReg decoded.msgRegs 0`, then passes `args.badge` to
`notificationSignal notifId args.badge st` (API.lean:549). The Rust
`notification_signal()` passes `msg_regs: [0; 4]` (all zeros), so badge is
always 0 — notification signals from Rust always accumulate a zero badge.
**Design decision required**: Two options:
- **Option A (match Lean)**: Update Rust to pass badge via `msg_regs[0]`
- **Option B (match seL4)**: Update Lean to use capability badge
**Recommendation**: Option A — the Lean model's MR[0] design is deliberate.

**Sub-steps**:

**W1-C-1**: Update function signature in `rust/sele4n-sys/src/ipc.rs`:
```rust
pub fn notification_signal(ntfn: CPtr, badge: Badge) -> KernelResult<SyscallResponse> {
    let msg_info = MessageInfo::new_const(1, 0, 0);  // length=1 (one MR used)
    invoke_syscall(SyscallRequest {
        cap_addr: ntfn,
        msg_info,
        msg_regs: [badge.into(), 0, 0, 0],  // badge in MR[0]
        syscall_id: SyscallId::NotificationSignal,  // also fixes CRIT-1
    })
}
```
Note: `MessageInfo` length must be 1 (not 0) to indicate one message register
is populated. Verify `decodeNotificationSignalArgs` checks `msgRegs` length.

**W1-C-2**: Verify `MessageInfo::new_const(1, 0, 0)` is valid. Check that the
Lean decode path does not reject length=1 for notification signal. Read
`SyscallArgDecode.lean:869-872` — `requireMsgReg` checks that the register
index is within `msgRegs.size`, which depends on `MessageInfo.length`. Confirm
length=1 allows MR[0] access.

**W1-C-3**: Add `use sele4n_types::Badge;` import to `ipc.rs` if not present.
Verify `Badge` has `Into<u64>` impl in `identifiers.rs` (confirmed: `Badge`
is `#[repr(transparent)]` over `u64` with `From<u64>` conversions).

**W1-C-4**: Update Rust doc comment on `notification_signal` to explain badge
semantics: "The badge value is passed via message register 0. The kernel
accumulates it into the notification object's badge word via bitwise OR."

**W1-C-5**: Verify no existing callers of `notification_signal()` in the Rust
test suite or sele4n-sys examples need updating for the new signature. Search
for `notification_signal(` across all Rust files.

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
**Lean reference**: `API.lean:566-576` dispatches `.replyRecv` to
`endpointReplyRecv`. `decodeReplyRecvArgs` (SyscallArgDecode.lean:881-884)
reads `MR[0]` as `replyTarget : ThreadId`.

**Sub-steps**:

**W1-E-1**: Verify full argument decode chain. Read `decodeReplyRecvArgs`:
```lean
def decodeReplyRecvArgs (decoded : SyscallDecodeResult) := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  pure { replyTarget := ThreadId.ofNat r0.val }
```
The wrapper needs: `cap_addr` = endpoint capability for receive,
`msg_regs[0]` = reply target thread ID, `MessageInfo.length` >= 1.

**W1-E-2**: Determine how the reply message is passed. Check if `dispatchWithCap`
for `.replyRecv` uses `decoded.msgRegs` for the reply payload or only for
argument decoding. If the reply uses the same message registers as
`endpoint_reply`, the wrapper must populate msg_regs with both the reply
target ID and any reply data.

**W1-E-3**: Implement the wrapper function:
```rust
pub fn endpoint_reply_recv(
    recv_cap: CPtr,
    reply_target: ThreadId,
    msg: &IpcMessage,
) -> KernelResult<SyscallResponse> {
    let msg_info = MessageInfo::new(msg.length, 0, msg.label)
        .map_err(|_| sele4n_types::KernelError::InvalidMessageInfo)?;
    invoke_syscall(SyscallRequest {
        cap_addr: recv_cap,
        msg_info,
        msg_regs: [reply_target.into(), msg.regs[1], msg.regs[2], msg.regs[3]],
        syscall_id: SyscallId::ReplyRecv,
    })
}
```
Note: `msg_regs[0]` is occupied by `reply_target`, so reply data starts at
`msg_regs[1]`. Verify this is consistent with how `endpoint_reply` works.

**W1-E-4**: Add `use sele4n_types::ThreadId;` import if not present.

**W1-E-5**: Add doc comment explaining the compound operation: "Atomically
replies to `reply_target` with the message payload and then blocks waiting
for a new message on the endpoint identified by `recv_cap`."

**Verification**: New test `test_endpoint_reply_recv_syscall_id` verifying
SyscallId::ReplyRecv (16) is encoded, and `test_endpoint_reply_recv_args`
verifying reply_target in MR[0].
**Risk**: Additive — new function, no breaking changes

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
**Problem**: The `StateField` enum (16 variants), `fieldsDisjoint` function,
and 10 pairwise disjointness/overlap witnesses exist. But no theorem connects
field disjointness to operational frame independence. The existing field-read
sets are:
- `registryEndpointValid_fields` = `[.serviceRegistry, .objects]`
- `registryDependencyConsistent_fields` = `[.services]`
- `noStaleEndpointQueueReferences_fields` = `[.objects]`
- `noStaleNotificationWaitReferences_fields` = `[.objects]`
- `serviceGraphInvariant_fields` = `[.services, .objectIndex]`

6 pairs are proven disjoint, 4 pairs share fields (both read `.objects` or
`.services`). The gap is: disjointness of read-sets does not automatically
imply that an operation modifying only the fields of one predicate preserves
another predicate.

**Sub-steps**:

**W2-A-1**: Define `modifiedFields` for each cross-subsystem-relevant
operation. For each kernel operation that appears in cross-subsystem
preservation proofs, declare which `StateField` values it writes:
```lean
def serviceRegisterDependency_modifiedFields : List StateField := [.services]
def storeObject_modifiedFields : List StateField := [.objects, .objectIndex, .objectIndexSet]
def lifecycleRetypeObject_modifiedFields : List StateField :=
  [.objects, .objectIndex, .objectIndexSet, .lifecycle]
```

**W2-A-2**: Attempt the general frame theorem. The ideal form is:
```lean
theorem fieldsDisjoint_implies_preservation
    (pred : SystemState → Prop)
    (predFields : List StateField)
    (opFields : List StateField)
    (hDisj : fieldsDisjoint predFields opFields = true)
    (hPred : pred st)
    (hFrame : ∀ f ∈ predFields, getField st f = getField st' f) :
    pred st'
```
This requires a `getField : SystemState → StateField → _` accessor, which is
problematic because different fields have different types. The general theorem
may not be expressible in this form.

**W2-A-3 (fallback if W2-A-2 fails)**: Instead of the general theorem, prove
**per-predicate frame lemmas** for each of the 5 predicates:
```lean
theorem registryDependencyConsistent_frame
    (hServices : st'.services = st.services) :
    registryDependencyConsistent st → registryDependencyConsistent st'

theorem noStaleEndpointQueueReferences_frame
    (hObjects : st'.objects = st.objects) :
    noStaleEndpointQueueReferences st → noStaleEndpointQueueReferences st'
```
Then add a documentation comment explaining that field disjointness + per-
predicate frame lemmas together establish frame independence.

**W2-A-4**: For each of the 6 disjoint pairs, verify that the existing per-
predicate frame lemmas (if they exist in `CrossSubsystem.lean`) are sufficient.
Check for `registryDependencyConsistent_frame`, `serviceGraphInvariant_frame`,
`serviceGraphInvariant_monotone` (all known to exist at lines 337-389).

**W2-A-5**: Document the formalism boundary. Add a comment block:
```lean
/-- V6-A Formalism Closure: Field disjointness implies frame independence
    via per-predicate frame lemmas. For each disjoint pair (P₁, P₂), if
    an operation only modifies fields in P₁'s read-set, the corresponding
    P₂ frame lemma proves P₂ is preserved. The 4 sharing pairs (which read
    overlapping fields) require operation-specific preservation proofs. -/
```

**Build**: `lake build SeLe4n.Kernel.CrossSubsystem`
**Risk**: Medium — W2-A-2 (general theorem) likely infeasible due to
heterogeneous field types. W2-A-3 (per-predicate frames) is achievable and
may already be partially done.

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
**Problem**: `collectQueueMembers` traverses the intrusive linked list of TCBs
in a queue using `st.objects.size` as fuel. On fuel exhaustion (fuel=0), it
returns `[]`, silently truncating the traversal. The IPC invariant
`tcbQueueChainAcyclic` ensures no cycles, so queue length <= object count,
making fuel sufficient — but this is unproven.

The function definition (lines 40-50):
```lean
private def collectQueueMembers (objects) (start) (fuel) :=
  match fuel, start with
  | 0, _ => []                  -- Silent truncation
  | _, none => []               -- Natural termination
  | fuel + 1, some tid =>
    match objects[tid.toObjId]? with
    | some (.tcb tcb) => tid :: collectQueueMembers objects tcb.queueNext fuel
    | _ => [tid]                -- Non-TCB termination
```

**Sub-steps**:

**W2-D-1**: Prove a length bound lemma. The key insight: `tcbQueueChainAcyclic`
(from `dualQueueSystemInvariant`) implies every thread appears at most once
in any queue traversal. Since all threads are in `st.objects`, the traversal
visits at most `st.objects.size` distinct threads.
```lean
theorem collectQueueMembers_length_le_objects_size
    (hAcyclic : tcbQueueChainAcyclic st) :
    (collectQueueMembers st.objects head st.objects.size).length
    ≤ st.objects.size
```

**W2-D-2**: Prove a no-truncation lemma. This is the core fuel sufficiency
result — when acyclicity holds, fuel is never exhausted:
```lean
theorem collectQueueMembers_no_truncation
    (hAcyclic : tcbQueueChainAcyclic st)
    (hFuel : fuel ≥ st.objects.size) :
    collectQueueMembers st.objects head fuel
    = collectQueueMembers st.objects head (fuel + 1)
```
This shows increasing fuel beyond `objects.size` does not change the result.

**W2-D-3**: If W2-D-1/W2-D-2 prove difficult (the acyclicity invariant
operates on `QueueNextPath` which is an inductive predicate, not a direct
list length bound), fall back to a weaker but useful statement:
```lean
/-- Fuel sufficiency argument: `tcbQueueChainAcyclic` prevents cycles in
    queue traversal. Each step consumes 1 fuel and visits 1 unique thread.
    With fuel = objects.size and at most objects.size threads, exhaustion
    implies all threads visited. -/
theorem collectQueueMembers_fuel_sufficiency_documented :
    True := trivial  -- See inline argument above
```
Plus strengthen the comment at the `| 0, _ => []` arm.

**W2-D-4**: Add a comment to `noStaleEndpointQueueReferences` documenting
the fuel adequacy argument and citing the `tcbQueueChainAcyclic` invariant.

**Build**: `lake build SeLe4n.Kernel.CrossSubsystem`
**Risk**: Medium — W2-D-1 is the ideal proof but may require substantial
infrastructure connecting `QueueNextPath` to list length. W2-D-3 is the
safe fallback.

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
**Problem**: `serviceCountBounded` requires `∃ ns, bfsUniverse st ns ∧
ns.length ≤ serviceBfsFuel st`. The invariant is bundled as part of
`serviceGraphInvariant` (conjunction with `serviceDependencyAcyclic`).
Existing preservation theorems:
- `serviceCountBounded_of_storeServiceState_sameDeps` (same deps → preserved)
- `serviceCountBounded_of_eq` (frame: services + objectIndex unchanged)
- `serviceCountBounded_monotone` (objectIndex grows → fuel grows → preserved)

The gap: `serviceRegisterDependency` *changes* dependencies (appends a new
dep), so the `_sameDeps` theorem does not directly apply. And `revokeService`
calls `removeDependenciesOf` which modifies the `services` table.

**Sub-steps**:

**W2-F-1**: Verify that `serviceRegisterDependency` preservation is already
covered. Check `serviceRegisterDependency_preserves_acyclicity` in
Acyclicity.lean (~line 550) — it requires `serviceCountBounded` as a
hypothesis and returns preservation of `serviceDependencyAcyclic`. But does
it also return `serviceCountBounded`? If not, that's the gap.

**W2-F-2**: If `serviceRegisterDependency` does NOT preserve
`serviceCountBounded`, add the theorem:
```lean
theorem serviceRegisterDependency_preserves_serviceCountBounded
    (hBound : serviceCountBounded st)
    (hOk : serviceRegisterDependency svcId depId st = .ok ((), st')) :
    serviceCountBounded st'
```
The proof strategy: `serviceRegisterDependency` only appends `depId` to
`svc.dependencies`. The BFS universe doesn't change (both `svcId` and `depId`
already exist in `services`). The fuel doesn't change (objectIndex unchanged).
So the existing witness `ns` still satisfies `bfsUniverse st' ns`.

**W2-F-3**: Verify `revokeService` preservation. `revokeService` calls
`removeDependenciesOf` which erases dependency edges. Removing edges from a
graph cannot increase the BFS universe (it can only shrink it). Prove:
```lean
theorem revokeService_preserves_serviceCountBounded
    (hBound : serviceCountBounded st)
    (hOk : revokeService sid st = .ok ((), st')) :
    serviceCountBounded st'
```

**W2-F-4**: Add a documentation block listing the complete preservation chain:
```lean
/-- serviceCountBounded preservation chain:
    - storeObject (objects only): preserved via _monotone (objectIndex grows)
    - registerInterface: preserved via _of_eq (services unchanged)
    - registerService: preserved via _of_eq (services unchanged)
    - serviceRegisterDependency: preserved (universe unchanged, fuel unchanged)
    - revokeService: preserved (universe shrinks, fuel unchanged)
    - All other kernel ops: preserved via _of_eq (services/objectIndex unchanged)
-/
```

**Build**: `lake build SeLe4n.Kernel.Service.Invariant.Acyclicity`
**Risk**: Low-Medium — the preservation arguments are straightforward since
adding edges doesn't grow the universe and removing edges shrinks it. The
main risk is the `bfsUniverse` predicate requiring careful reasoning about
the universe witness.

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
**Output**: A categorized list used by W3-B through W3-F

**Sub-steps**:

**W3-A-1**: Extract all definition names. Run a script that greps for
`def `, `theorem `, `lemma `, `abbrev `, `instance ` declarations across
all `SeLe4n/*.lean` files and extracts the identifier name + file + line.
Expected output: ~2,000+ definitions.

**W3-A-2**: For each definition, count external references. For each
identifier from W3-A-1, grep across all `.lean` files (`SeLe4n/`, `tests/`,
`Main.lean`) for that identifier. Exclude matches in the definition file
itself. Record the reference count.

**W3-A-3**: Filter to zero-external-reference candidates. This is the
"potentially dead" list. Expected size: 200-400 based on sample rates.

**W3-A-4**: Classify each candidate into categories:
- **Category A (remove)**: Internal helper lemma, intermediate proof step,
  superseded definition, or duplicate. Criteria: name suggests helper purpose
  (e.g., `_aux`, `_go`, `_step`), or proof is intermediate (feeds no other
  theorem), or a duplicate exists (e.g., `maxLength` vs `maxMessageRegisters`).
- **Category B (keep as spec-surface)**: Characterizes a security property,
  invariant, or correctness condition. Criteria: name suggests specification
  (e.g., `_refl`, `_trans`, `_antisymm` for lattice; `_preserves_` for
  invariant; `_sound`, `_complete` for correctness). Keep even if unused.
- **Category C (defer — platform scaffolding)**: Definitions in Platform/,
  RPi5/, Boot.lean, DeviceTree.lean that are scaffolding for future hardware
  binding. Keep until H3 integration determines their fate.

**W3-A-5**: For Category A candidates, do a final deep-check: verify the
definition is not referenced via typeclass resolution, `@[simp]` lemma
application, or `open` namespace imports that make the grep miss. Run
`lake build <Module>` after a trial removal of 2-3 candidates to validate
the methodology.

**W3-A-6**: Write the inventory to `docs/audits/DEAD_CODE_INVENTORY_v0.22.10.md`
organized by file, with each entry showing: definition name, file:line,
category (A/B/C), and rationale.

**Risk**: Low — read-only analysis. W3-A-5 catches false negatives.

#### W3-B: Remove confirmed dead helpers — Foundation layer

**Files**: `Prelude.lean`, `Machine.lean`, `Model/Object/Types.lean`,
`Model/Object/Structures.lean`, `Model/State.lean`

**Sub-steps** (one per file, each independently buildable):

**W3-B-1**: `Prelude.lean` — monad law proofs decision.
Decision: Remove `pure_bind_law`, `bind_pure_law`, `bind_assoc_law`,
`get_returns_state`, `set_replaces_state`, `modify_applies_function`,
`liftExcept_ok`, `liftExcept_error`, `throw_errors` (9 definitions).
Rationale: No `LawfulMonad` instance exists and no downstream proof uses
them. If a `LawfulMonad` instance is desired in the future, re-derive from
the monad definition.
Alternative (W3-B-1-alt): Wire into `instance : LawfulMonad KernelM` instead
of removing. This creates a consumer, making the proofs non-dead. Choose this
only if downstream proofs would benefit from `LawfulMonad` lemmas.
Build: `lake build SeLe4n.Prelude`

**W3-B-2**: `Prelude.lean` — RHTable bridge lemmas.
From W3-A inventory, identify which of the ~29 RHTable theorems (lines
916-1049) are Category A vs B. Bridge lemmas like `RHTable_contains_iff_get_some`
characterize hash table behavior — classify as Category B (spec-surface) and
keep. Internal helpers like `RHTable_size_insert_bound` that feed no proof
chain — classify as Category A and remove.
Build: `lake build SeLe4n.Prelude`

**W3-B-3**: `Machine.lean` — remove unused config/alignment helpers.
Candidates: `wordAligned`, `pageAligned`, `pageAligned_implies_wordAligned`,
`wordAligned_zero`, `pageAligned_zero`, `totalRAM`, `addressInMap`,
`isPowerOfTwo_spec`. Verify each with grep first. Keep
`zeroMemoryRange_*` proofs only if `zeroMemoryRange` itself is used.
Build: `lake build SeLe4n.Machine`

**W3-B-4**: `Types.lean` — remove duplicates and unused UntypedObject proofs.
Remove `maxLength` (duplicate of `maxMessageRegisters`), `maxExtraCaps'`
(duplicate of `maxExtraCaps`). For UntypedObject proofs (`allocate_*`,
`reset_*`, `empty_*`): classify as Category B (specification of memory
allocator correctness) — keep unless they are clearly intermediate.
Build: `lake build SeLe4n.Model.Object.Types`

**W3-B-5**: `Structures.lean` — remove unused CDT navigation helpers.
Candidates: `isChildOf`, `isParentOf`, `parentOf`, `removeAsChild`,
`removeAsParent`, `isAncestor`, `makeObjectCap`. These are unused because
the kernel uses hypothesis-carrying CDT operations instead. Verify no test
file references them. Remove. Keep `addEdge_*` theorems as Category B
(specification surface for CDT correctness).
Build: `lake build SeLe4n.Model.Object.Structures`

**W3-B-6**: `State.lean` — audit internal-use aliases.
`CSpaceOwner` is used internally by `ownerOfSlot`, `ownsSlot`, `ownedSlots`.
If all three consumers are themselves unused externally, remove the entire
cluster. If any has external consumers, keep. For `observedCdtEdges`,
`observedCdtEdges_eq_projection`: check if these are CDT observation
spec-surface (Category B) or dead helpers (Category A).
Build: `lake build SeLe4n.Model.State`

**Risk**: Low — each sub-step targets one file with individual build gate

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
**Problem**: Three `expectError` implementations with identical signatures:
```lean
def expectError (label : String) (actual : Except KernelError α)
    (expected : KernelError) : IO Unit
```
All three have the same logic but differ only in the success message prefix:
- `Helpers.lean`: `"check passed [{label}]: {toString err}"`
- `NegativeStateSuite.lean`: `"negative check passed [{label}]: {toString err}"`
- `OperationChainSuite.lean`: `"operation-chain check passed [{label}]"` (no error string)

**Sub-steps**:

**W5-A-1**: Add an optional `prefix` parameter to the canonical `Helpers.lean`
version to support suite-specific message formatting:
```lean
def expectError (label : String) (actual : Except KernelError α)
    (expected : KernelError) (prefix : String := "check") : IO Unit :=
  match actual with
  | .ok _ => throw <| IO.userError s!"{label}: expected error {toString expected}, got success"
  | .error err =>
      if err = expected then
        IO.println s!"{prefix} passed [{label}]: {toString err}"
      else
        throw <| IO.userError s!"{label}: expected {toString expected}, got {toString err}"
```

**W5-A-2**: Update `NegativeStateSuite.lean` — remove `private def expectError`,
add `import SeLe4n.Testing.Helpers` if not present, replace all call sites
with `expectError label actual expected (prefix := "negative check")`.

**W5-A-3**: Update `OperationChainSuite.lean` — remove `private def expectError`,
add `import SeLe4n.Testing.Helpers` if not present, replace all call sites
with `expectError label actual expected (prefix := "operation-chain check")`.
Note: This suite's version omits `{toString err}` from success message — the
unified version will include it, which is a minor behavioral change (more
informative output, not a correctness issue).

**W5-A-4**: Also check for duplicate `expectOkState` and `expectOk` — the
NegativeStateSuite defines private versions of these too. If duplicates exist,
consolidate following the same pattern.

**W5-A-5**: Verify: `lake build negative_state_suite && lake build operation_chain_suite && lake build information_flow_suite`
**Risk**: Low — signatures are identical, only message format changes

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

**File**: `tests/OperationChainSuite.lean` (extend)
**Problem**: Service lifecycle operations are completely absent from testing.
The service subsystem has 3 operations (`registerInterface`, `registerService`,
`revokeService`) in Registry.lean and 1 (`serviceRegisterDependency`) in
Operations.lean, plus `serviceQuery` via the API layer.

**Sub-steps**:

**W5-C-1**: Build test state with service infrastructure. Using `StateBuilder`,
create a state with: 2+ threads, 2+ endpoint objects (for service binding),
2+ interface specs, appropriate CSpace capabilities with `.write` rights.

**W5-C-2**: Test `registerInterface` success path. Register an interface spec
and verify `st.interfaceRegistry[ifaceId]?` contains the spec.

**W5-C-3**: Test `registerInterface` duplicate rejection. Register the same
interface spec twice — second call should return `.error .illegalState`.

**W5-C-4**: Test `registerService` success path. After registering an
interface, register a service with a valid endpoint capability. Verify
`st.serviceRegistry[sid]?` contains the registration.

**W5-C-5**: Test `registerService` error paths:
- Missing interface → `.error .objectNotFound`
- Invalid capability (non-endpoint target) → `.error .invalidCapability`
- Missing write right → `.error .illegalAuthority`
- Duplicate service ID → `.error .illegalState`

**W5-C-6**: Test `serviceRegisterDependency` acyclic path. Register services
A and B, add dependency A→B. Verify success.

**W5-C-7**: Test `serviceRegisterDependency` cycle rejection. After A→B,
attempt B→A. Should return `.error .cyclicDependency`.

**W5-C-8**: Test `revokeService` success path. Register a service, revoke it,
verify `st.serviceRegistry[sid]?` is `none` and dependency edges are cleaned.

**W5-C-9**: Run `stateInvariantChecksFor` after each operation to verify
invariant preservation.

**Build**: `lake build operation_chain_suite`
**Risk**: Low — additive tests, but requires careful state setup

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
**Problem**: 77 lines of redundant preservation proofs. The pattern is:
3 cleanup operations (`cleanupTcbReferences`, `detachCNodeSlots`,
`lifecyclePreRetypeCleanup`) × multiple state fields (`scheduler`,
`irqHandlers`, `asidTable`, etc.) = ~12 near-identical theorems, each
proving `field st' = field st` after the cleanup operation succeeds.

**Sub-steps**:

**W6-B-1**: Read lines 127-203 to catalog all redundant proofs. Identify the
exact pattern: does each proof use `simp [cleanupOp]` or `unfold; split; simp`?
Record the proof tactic used.

**W6-B-2**: Determine if a generic frame lemma is feasible. The ideal form:
```lean
theorem cleanup_frame {α} (op : SystemState → Except KernelError SystemState)
    (field : SystemState → α)
    (hFrame : ∀ st st', op st = .ok st' → field st' = field st)
    (hOp : op st = .ok st') : field st' = field st :=
  hFrame st st' hOp
```
This is trivially true — the real work is proving each `hFrame` instance.
If all cleanup operations share the pattern "only modify `objects`/`cdt`
fields," a single lemma per cleanup op listing all preserved fields would
be more effective than one-per-field.

**W6-B-3**: If the per-op approach works, create:
```lean
theorem cleanupTcbReferences_preserves (st st' : SystemState)
    (hOk : cleanupTcbReferences tid st = .ok st') :
    st'.scheduler = st.scheduler ∧ st'.irqHandlers = st.irqHandlers ∧
    st'.asidTable = st.asidTable ∧ st'.serviceRegistry = st.serviceRegistry ∧
    st'.interfaceRegistry = st.interfaceRegistry
```
Then delete the 5 individual theorems it replaces.

**W6-B-4**: Repeat for `detachCNodeSlots` and `lifecyclePreRetypeCleanup`.

**W6-B-5**: Update any consumers of the individual theorems to use the
bundled version with `.1`, `.2.1`, etc. projections.

**Build**: `lake build SeLe4n.Kernel.Lifecycle.Operations`
**Risk**: Medium — consumers may use the individual theorem names explicitly

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

| Phase | Sub-tasks | Atomic Steps | Est. Files Modified | Risk Level |
|-------|-----------|-------------|-------------------|------------|
| W1 | 9 | 23 | ~8 Rust files | Low (mostly single-line fixes) |
| W2 | 8 | 24 | ~6 Lean files | Medium (proof engineering) |
| W3 | 8 | 18 | ~30+ Lean files | Low (verified removals) |
| W4 | 7 | 7 | ~5 Lean files | Low (documentation + hardening) |
| W5 | 8 | 20 | ~8 files (Lean + Rust) | Low-Medium |
| W6 | 12 | 17 | ~12 files (Lean + Rust + docs) | Low |
| **Total** | **52** | **109** | **~60+ files** | |

**Note**: "Sub-tasks" are the top-level work items (W1-A through W6-L).
"Atomic Steps" are the detailed internal steps (e.g., W1-C-1 through W1-C-5)
within complex sub-tasks. Simple sub-tasks have 1 atomic step each.

---

*End of workstream plan.*
