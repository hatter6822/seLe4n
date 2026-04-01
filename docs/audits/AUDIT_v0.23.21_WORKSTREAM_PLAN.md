# WS-AA Workstream Plan — Comprehensive Audit Remediation (v0.23.21)

**Created**: 2026-03-31
**Baseline version**: 0.23.21
**Baseline audit**:
- `docs/audits/AUDIT_COMPREHENSIVE_v0.23.21_LEAN_RUST_KERNEL.md` (0 CRIT, 5 HIGH, 8 MED, 30 LOW, 35+ INFO)
**Prior portfolios**: WS-B through WS-Z (all COMPLETE — see `docs/WORKSTREAM_HISTORY.md`)
**Constraint**: Zero `sorry`/`axiom` in production proof surface

---

## 1. Executive Summary

A comprehensive full-kernel audit of seLe4n v0.23.21 was conducted on 2026-03-31,
covering all 124 Lean kernel modules (~79,730 lines), 27 Rust ABI files (~4,675
lines), and 34 build/CI infrastructure files. The audit found **zero CVE-worthy
vulnerabilities**, zero `sorry`/`axiom`/`native_decide` in production code, and
complete invariant preservation coverage across all kernel subsystems.

After validating every finding against the actual codebase, we identified **39
unique actionable findings** and **4 erroneous findings** requiring no action.
The most significant gaps are: (1) three Lean-Rust ABI type desync issues that
make the entire SchedContext subsystem unreachable from Rust userspace, (2) a
compositional non-interference gap where SchedContext operations lack dedicated
NI proof constructors, and (3) CI supply chain issues with unverified Rust
toolchain installation.

### Finding Validation Summary

| Severity | Raw Findings | Erroneous/No-Action | Actionable |
|----------|-------------|---------------------|------------|
| Critical | 0 | 0 | 0 |
| High | 5 | 0 | 5 |
| Medium | 8 | 1 (M-5) | 7 |
| Low | 30 | 3 (L-24, L-26, L-28) | 27 |
| **Total** | **43** | **4** | **39** |

### Erroneous Findings (No Action Required)

| ID | Audit Claim | Reason for Rejection |
|----|-------------|---------------------|
| M-5 | `ServiceRegisterArgs` encodes 5 registers but only 4 inline slots | IPC buffer overflow routing handles the 5th register correctly — `set_mr(4, encoded[4])` writes to overflow slot 0, and `MessageInfo.length=5` signals the kernel to read both inline and overflow slots. This is the intended two-tier message passing mechanism. |
| L-24 | `admissionCheck` integer truncation could admit >100% bandwidth | Intentional, documented CBS practice. `utilizationPerMille` uses integer division that truncates down, causing slight underestimation. This is standard in Constant Bandwidth Scheduling and explicitly documented in the source. |
| L-26 | `decode` extracts 55 bits for label | Already fixed. `MAX_LABEL` is now `(1u64 << 20) - 1` (20 bits) with explicit validation. The 55-bit issue is historical and documented as resolved in the source comments. |
| L-28 | Missing conformance tests (generic) | Partially subsumed by L-29 (SchedContext tests) and AA3-C (edge case tests). The generic claim lacks specific actionable scope. |

### Phase Overview

| Phase | Name | Sub-tasks | Priority | Gate | Status |
|-------|------|-----------|----------|------|--------|
| AA1 | Rust ABI Type Synchronization | 8 | CRITICAL | Rust tests pass, conformance tests green | **COMPLETE** |
| AA2 | CI & Infrastructure Hardening | 6 | HIGH | CI workflows pass, pre-commit hook functional | NOT STARTED |
| AA3 | Rust ABI Semantic Alignment | 4 | MEDIUM | Rust tests pass, no Lean-Rust semantic divergence | NOT STARTED |
| AA4 | IPC Timeout & Kernel Hardening | 13 | MEDIUM | Module builds pass, `test_smoke.sh` green | NOT STARTED |
| AA5 | Information Flow & Safety Guards | 7 | MEDIUM | Module builds pass, `test_full.sh` green | NOT STARTED |
| AA6 | Platform & Architecture Fixes | 5 | LOW | Module builds pass, `test_smoke.sh` green | NOT STARTED |
| AA7 | Non-Interference Composition | 10 | HIGH | All NI proofs compile, `test_full.sh` green | NOT STARTED |
| AA8 | Documentation & Closure | 8 | LOW | All docs consistent, `test_fast.sh` green | NOT STARTED |

**Total**: 61 atomic sub-tasks across 8 phases.

### Dependencies

```
AA1 ──→ AA3 (Rust ABI semantics depend on type sync)
AA1 ──→ AA8 (docs reference new Rust variants)
AA2 ───────→ AA8 (CI hardening referenced in docs)
AA4 ──→ AA7 (timeout TCB flag changes NI proof surface)
AA4 ──→ AA8 (kernel changes need doc sync)
AA5 ──→ AA7 (guard rails inform NI composition)
AA5 ──→ AA8 (guard rail docs)
AA6 ──→ AA8 (platform changes need doc sync)
AA7 ──→ AA8 (NI composition needs doc sync)

Independent parallel tracks:
  Track A: AA1 → AA3 → AA8
  Track B: AA2 → AA8
  Track C: AA4 → AA7 → AA8
  Track D: AA5 → AA7 → AA8
  Track E: AA6 → AA8
```

AA1 and AA2 have no mutual dependencies and should be tackled first in parallel.
AA4, AA5, and AA6 are independent of each other but AA4 and AA5 feed into AA7.
AA7 (NI Composition) is the most complex phase and depends on AA4 completing the
timeout TCB flag change. AA8 is the terminal phase.

---

## 2. Finding-to-Phase Mapping

| Finding | Severity | Phase | Sub-task(s) |
|---------|----------|-------|-------------|
| H-1 | HIGH | AA1 | AA1-A, AA1-B |
| H-2 | HIGH | AA1 | AA1-C |
| H-3 | HIGH | AA1 | AA1-D |
| H-4 | HIGH | AA2 | AA2-A, AA2-B |
| H-5 | HIGH | AA2 | AA2-C |
| M-1 | MEDIUM | AA7 | AA7-A through AA7-J |
| M-2 | MEDIUM | AA4 | AA4-A, AA4-B, AA4-C |
| M-3 | MEDIUM | AA5 | AA5-A |
| M-4 | MEDIUM | AA4 | AA4-D |
| M-6 | MEDIUM | AA3 | AA3-A |
| M-7 | MEDIUM | AA2 | AA2-D |
| M-8 | MEDIUM | AA2 | AA2-E |
| L-1 | LOW | AA4 | AA4-E |
| L-2 | LOW | AA4 | AA4-F |
| L-3 | LOW | AA4 | AA4-G |
| L-5 | LOW | AA6 | AA6-D (note only) |
| L-6 | LOW | AA6 | AA6-D (note only) |
| L-7 | LOW | AA6 | AA6-D (note only) |
| L-8 | LOW | AA6 | AA6-D (note only) |
| L-9 | LOW | AA4 | AA4-H |
| L-10 | LOW | AA4 | AA4-I |
| L-11 | LOW | — | No action (intentional per spec) |
| L-12 | LOW | AA4 | AA4-J |
| L-13 | LOW | AA4 | AA4-K |
| L-14 | LOW | AA4 | AA4-L |
| L-15 | LOW | AA5 | AA5-B |
| L-16 | LOW | AA5 | AA5-C |
| L-17 | LOW | AA5 | AA5-D |
| L-18 | LOW | AA5 | AA5-E |
| L-19 | LOW | AA5 | AA5-F |
| L-20 | LOW | AA6 | AA6-A |
| L-21 | LOW | AA6 | AA6-B |
| L-22 | LOW | AA6 | AA6-C |
| L-23 | LOW | AA4 | AA4-M |
| L-25 | LOW | AA1 | AA1-E |
| L-27 | LOW | AA3 | AA3-B |
| L-29 | LOW | AA1 | AA1-F, AA1-G, AA1-H |
| L-30 | LOW | AA2 | AA2-F |
| L-4 | LOW | AA6 | AA6-D (note only) |

### Non-Actionable Findings (No Sub-task)

| Finding | Reason |
|---------|--------|
| L-11 | LIFO notification wait is intentional per spec — documented design choice |
| L-5 | Hash flooding is a known limitation, documented — no randomized hashing in Lean |
| L-6 | Resize doubling bounded by kernel policy — documented |
| L-7 | Post-insert load proven safe by `insert_size_lt_capacity` — documented |
| L-8 | O(n) append acceptable for ≤256 threads — documented |
| L-4 | `maxHeartbeats 2000000` is justified for complex CDT proofs — documented |

These findings are acknowledged as design decisions or known limitations. They
are recorded in AA6-D documentation sub-task for audit trail completeness.

---

## 3. Phase AA1 — Rust ABI Type Synchronization — **COMPLETE**

**Priority**: CRITICAL (release-blocking)
**Gate**: `cargo test` passes in all 3 crates, conformance tests green
**Findings addressed**: H-1, H-2, H-3, L-25, L-29
**Status**: COMPLETE — All 8 sub-tasks delivered. 197 Rust tests pass (77 unit + 73 conformance + 12 sele4n-sys + 35 sele4n-types). Zero warnings. `test_smoke.sh` green.

The entire WS-Z SchedContext subsystem (10 phases, 213 sub-tasks of kernel work)
was unreachable from Rust userspace due to three Lean-Rust type desync gaps. This
phase synchronized the Rust ABI types with the Lean model and added conformance
tests to prevent future drift.

**Implementation summary**:
- **AA1-A**: Added `SchedContextConfigure` (17), `SchedContextBind` (18), `SchedContextUnbind` (19) to `SyscallId`. COUNT 17→20. All require `.write` access.
- **AA1-B**: 6 conformance tests for new SyscallId variants (roundtrip, boundary, required_rights).
- **AA1-C**: Added `IpcTimeout = 42` to `KernelError`. 43 variants total. Updated `from_u32`, `Display`, all inline tests.
- **AA1-D**: Added `SchedContext = 6` to `TypeTag`. 7 variants total. Updated `from_u64`, all inline tests. Fixed lifecycle retype boundary test (6→7).
- **AA1-E**: Updated `lib.rs` doc comments: "34-variant error" → "43-variant", "14-variant syscall" → "20-variant".
- **AA1-F**: Created `sched_context.rs` module with `SchedContextConfigureArgs` (5 fields, priority/domain validation), `SchedContextBindArgs` (1 field), `SchedContextUnbindArgs` (empty). 7 inline tests + 6 conformance tests.
- **AA1-G**: 2 conformance tests for `TypeTag::SchedContext` retype integration.
- **AA1-H**: 4 conformance tests for `KernelError::IpcTimeout` (roundtrip, distinctness, result wrapping, boundary).
- **Ripple fixes**: Updated `decode.rs` stale comment and unknown-error-code test (42→43). Fixed 8 existing conformance tests that checked old boundaries.

### AA1-A: Add `SyscallId` SchedContext variants (H-1)

**Finding**: Lean `SyscallId` has 20 variants (0–19) including
`.schedContextConfigure` (17), `.schedContextBind` (18), `.schedContextUnbind`
(19). Rust enum has only 17 variants (0–16).

**Files**: `rust/sele4n-types/src/syscall.rs`

**Fix**:
1. Add three variants to the `SyscallId` enum:
   ```rust
   SchedContextConfigure = 17,
   SchedContextBind = 18,
   SchedContextUnbind = 19,
   ```
2. Update `COUNT` constant from `17` to `20`.
3. Update `from_u64` to handle discriminants 17–19.
4. Update `as_str()` with corresponding string representations.
5. Verify the enum comment ("17 variants" → "20 variants").

**Verification**: `cargo test -p sele4n-types`

### AA1-B: Add `SyscallId` conformance tests (H-1, L-29)

**Finding**: No SchedContext syscall conformance tests exist.

**Files**: `rust/sele4n-types/src/syscall.rs` (inline tests) or
`rust/sele4n-abi/tests/conformance.rs`

**Fix**:
1. Add roundtrip tests for discriminants 17, 18, 19.
2. Add `from_u64(20)` returns `None` test (boundary).
3. Add `COUNT == 20` assertion.
4. Verify `as_str()` output for all three new variants.

**Verification**: `cargo test`

### AA1-C: Add `KernelError::IpcTimeout` variant (H-2)

**Finding**: Lean `KernelError` has 43 variants (0–42) with `.ipcTimeout` at
discriminant 42. Rust stops at `InvalidSyscallArgument = 41`.

**Files**: `rust/sele4n-types/src/error.rs`

**Fix**:
1. Add `IpcTimeout = 42` variant to the `KernelError` enum.
2. Update `from_u32` to handle discriminant 42.
3. Update `as_str()` with `"IpcTimeout"` string.
4. Update discriminant documentation comment.
5. Add roundtrip conformance test for discriminant 42.
6. Add boundary test: `from_u32(43)` returns `None`.

**Verification**: `cargo test -p sele4n-types`

### AA1-D: Add `TypeTag::SchedContext` variant (H-3)

**Finding**: Lean `KernelObjectType` has 7 variants (0–6) with `.schedContext`
at discriminant 6. Rust `TypeTag` has only 6 variants (0–5).

**Files**: `rust/sele4n-abi/src/args/type_tag.rs`

**Fix**:
1. Add `SchedContext = 6` variant to the `TypeTag` enum.
2. Update enum comment ("6 variants" → "7 variants").
3. Update `from_u64` to accept discriminant 6.
4. Fix existing test that asserts `TypeTag::from_u64(6)` returns error —
   it should now succeed.
5. Add roundtrip conformance test.
6. Add boundary test: `from_u64(7)` returns `Err(InvalidTypeTag)`.

**Verification**: `cargo test -p sele4n-abi`

### AA1-E: Update stale Rust doc comments (L-25)

**Finding**: `sele4n-types/src/lib.rs` says "34-variant error enum" (actual: 43
after AA1-C) and "14-variant syscall" (actual: 20 after AA1-A).

**Files**: `rust/sele4n-types/src/lib.rs`

**Fix**:
1. Update "34-variant error enum" → "43-variant error enum".
2. Update "14-variant syscall" → "20-variant syscall identifier enum".
3. Review all other doc comments in the file for staleness.

**Verification**: Manual review + `cargo doc --no-deps`

### AA1-F: Add SchedContext syscall decode conformance tests (L-29)

**Files**: `rust/sele4n-abi/tests/conformance.rs`

**Fix**:
1. Add `SchedContextConfigureArgs` encode/decode roundtrip test.
2. Add `SchedContextBindArgs` encode/decode roundtrip test.
3. Add `SchedContextUnbindArgs` encode/decode roundtrip test.
4. Add boundary/error tests for each (missing registers, invalid values).

**Note**: This requires checking whether `SchedContextConfigureArgs`,
`SchedContextBindArgs`, and `SchedContextUnbindArgs` Rust types exist. If they
do not exist yet, this sub-task creates them (matching Lean's
`SyscallArgDecode.lean` structures).

**Verification**: `cargo test -p sele4n-abi`

### AA1-G: Add SchedContext `TypeTag` retype conformance test (L-29)

**Files**: `rust/sele4n-abi/tests/conformance.rs`

**Fix**:
1. Add `LifecycleRetypeArgs` test with `TypeTag::SchedContext` as target type.
2. Verify encode produces correct discriminant (6) in the output register.
3. Verify decode accepts discriminant 6 and produces `TypeTag::SchedContext`.

**Verification**: `cargo test -p sele4n-abi`

### AA1-H: Add `IpcTimeout` error handling conformance test (L-29)

**Files**: `rust/sele4n-abi/tests/conformance.rs` or
`rust/sele4n-types/src/error.rs` (inline tests)

**Fix**:
1. Add `KernelError::IpcTimeout` roundtrip test (encode to `u32`, decode back).
2. Add test that `KernelResult` correctly wraps timeout errors.
3. Verify `IpcTimeout` is distinct from all other error discriminants.

**Verification**: `cargo test`

---

## 4. Phase AA2 — CI & Infrastructure Hardening

**Priority**: HIGH
**Gate**: CI workflows pass, pre-commit hook functional on filenames with spaces
**Findings addressed**: H-4, H-5, M-7, M-8, L-30

This phase addresses supply chain and scripting vulnerabilities in the build
infrastructure. All sub-tasks are independent and can be parallelized.

### AA2-A: Pin Rust toolchain version in CI (H-4)

**Finding**: `.github/workflows/lean_action_ci.yml:156` installs Rust via
`curl https://sh.rustup.rs | sh` with no integrity check or version pinning.

**Files**: `.github/workflows/lean_action_ci.yml`

**Fix**:
1. Replace the curl-pipe `rustup` installation with the `dtolnay/rust-toolchain`
   GitHub Action, SHA-pinned to a specific commit hash.
2. Pin a specific Rust toolchain version (e.g., `1.82.0` or current stable).
3. Alternatively, if the Action approach is not viable:
   a. Download the `rustup-init` binary directly.
   b. Verify its SHA-256 hash against a pinned value.
   c. Run with `--default-toolchain <pinned-version>`.
4. Add a comment documenting the pinned version and how to update it.

**Verification**: Push to a test branch and verify CI passes.

### AA2-B: Add Rust toolchain version to SHA-pinning documentation (H-4)

**Files**: `.github/workflows/lean_action_ci.yml`, `scripts/setup_lean_env.sh`

**Fix**:
1. Document the pinned Rust version alongside the existing Lean toolchain SHA
   pinning documentation.
2. Add a `RUST_TOOLCHAIN_VERSION` variable or equivalent for consistency with
   the `LEAN_TOOLCHAIN_VERSION` pattern used elsewhere.

**Verification**: Documentation review.

### AA2-C: Fix unquoted `$STAGED_LEAN_FILES` word-splitting (H-5)

**Finding**: `scripts/pre-commit-lean-build.sh:56,81` uses unquoted
`$STAGED_LEAN_FILES` in `for` loops. Filenames with spaces would be
incorrectly word-split.

**Files**: `scripts/pre-commit-lean-build.sh`

**Fix**:
1. Replace `for file in $STAGED_LEAN_FILES; do` with a bash array approach:
   ```bash
   mapfile -t staged_files < <(git diff --cached --name-only --diff-filter=ACMR -- '*.lean')
   for file in "${staged_files[@]}"; do
   ```
2. Apply this pattern to both loop locations (lines 56 and 81).
3. Add a ShellCheck directive comment (`# shellcheck disable=` is NOT
   appropriate here — fix the actual issue).
4. Test with a filename containing spaces to verify correctness.

**Verification**: Create a test `.lean` file with a space in its name, stage it,
and run the pre-commit hook.

### AA2-D: Make SHA-256 verification fail-closed (M-7)

**Finding**: `scripts/setup_lean_env.sh:180-185` silently skips hash
verification on unrecognized architectures (fail-open).

**Files**: `scripts/setup_lean_env.sh`

**Fix**:
1. Change the empty-hash fallback from `return 0` to `return 1`:
   ```bash
   if [ -z "${expected_sha}" ]; then
     log_elapsed "error: no SHA-256 hash configured for architecture $(uname -m); aborting"
     return 1
   fi
   ```
2. Update surrounding logic to handle the failure (skip install or abort).

**Verification**: Test on a non-x86_64/aarch64 system or mock `uname -m`.

### AA2-E: Lock down `TRACE_FIXTURE_PATH` in CI (M-8)

**Finding**: `scripts/test_tier2_trace.sh:18` accepts `TRACE_FIXTURE_PATH` from
the environment, allowing fixture override in CI.

**Files**: `scripts/test_tier2_trace.sh`

**Fix**:
1. At the top of the script, forcefully unset the variable:
   ```bash
   unset TRACE_FIXTURE_PATH
   ```
2. Or validate that the resolved path is within the repository tree and tracked
   by git:
   ```bash
   if [ -n "${TRACE_FIXTURE_PATH:-}" ]; then
     if ! git ls-files --error-unmatch "$TRACE_FIXTURE_PATH" >/dev/null 2>&1; then
       echo "ERROR: TRACE_FIXTURE_PATH must be a git-tracked file" >&2
       exit 1
     fi
   fi
   ```

**Verification**: Set `TRACE_FIXTURE_PATH=/tmp/fake` and verify the script
rejects it.

### AA2-F: JSON-escape `lane` variable in timing capture (L-30)

**Finding**: `scripts/ci_capture_timing.sh:33` inserts `$lane` into JSON output
without escaping. Quotes or backslashes in the value would produce invalid JSON.

**Files**: `scripts/ci_capture_timing.sh`

**Fix**:
1. Route `$lane` through the same Python JSON escaping used for `$command_json`:
   ```bash
   lane_json="$(printf '%s\n' "$lane" | python3 -c 'import json,sys; print(json.dumps(sys.stdin.read().rstrip("\n")))')"
   ```
2. Use `%s` instead of `"%s"` for the lane field in the printf format string
   (since `json.dumps` already adds quotes).

**Verification**: Test with `lane='test"lane'` and verify valid JSON output.

---

## 5. Phase AA3 — Rust ABI Semantic Alignment

**Priority**: MEDIUM
**Gate**: `cargo test` passes, Lean-Rust decode semantics aligned
**Findings addressed**: M-6, L-27
**Depends on**: AA1 (type sync must land first)

This phase resolves semantic divergences between Lean and Rust decode logic.

### AA3-A: Align `requires_grant` boolean decode (M-6)

**Finding**: Lean uses `r4.val != 0` (any non-zero = true) while Rust uses
strict `match { 0 => false, 1 => true, _ => Err }`. A Lean-side value of 2
succeeds in Lean but fails in Rust.

**Files**: `rust/sele4n-abi/src/args/service.rs:59-62`

**Fix** (two options — choose one):

**Option A (preferred): Make Rust permissive to match Lean.**
```rust
let requires_grant = regs[4] != 0;
```
This matches Lean's `r4.val != 0` semantics exactly. Simpler, no error path.

**Option B: Make Lean strict to match Rust.**
Add validation in `SyscallArgDecode.lean` `decodeServiceRegisterArgs`:
```lean
if r4.val > 1 then throw .invalidSyscallArgument
```
This is more restrictive and would require updating the error-exclusivity theorem.

**Recommendation**: Option A — the Rust side should match the Lean specification,
not the other way around. The kernel is the source of truth.

**Verification**: Add conformance test with values 0, 1, 2, and `u64::MAX`.

### AA3-B: Document `endpoint_reply_recv` truncation behavior (L-27)

**Finding**: `sele4n-sys/src/ipc.rs:180` silently truncates user data beyond 3
registers without returning an error.

**Files**: `rust/sele4n-sys/src/ipc.rs`

**Fix**:
1. Add explicit documentation to `endpoint_reply_recv` explaining the 3-register
   inline limit and the truncation behavior.
2. Add a `debug_assert!(msg.length <= 3, "...")` to catch truncation in
   development builds.
3. Consider returning `Err(KernelError::IpcMessageTooLarge)` if
   `msg.length > 3`, or adding an explicit `TruncatedWarning` to the return type.
   **Decision**: Document-only for now — changing the return type would be a
   breaking API change better suited for a dedicated ABI versioning effort.

**Verification**: `cargo test -p sele4n-sys`

### AA3-C: Add edge-case conformance tests (L-28 partial)

**Files**: `rust/sele4n-abi/tests/conformance.rs`

**Fix**:
1. Add test: `IpcMessage::push` overflow beyond capacity.
2. Add test: zero-length message encode/decode.
3. Add test: zero-valued identifiers (`ObjId(0)`, `ThreadId(0)`, `CPtr(0)`).
4. Add test: `endpoint_reply_recv` with `msg.length > 3` (truncation path).

**Verification**: `cargo test -p sele4n-abi`

### AA3-D: Validate Lean-Rust constant sync assertions (L-29 related)

**Files**: All `rust/sele4n-*/` source files with `const` definitions

**Fix**:
1. Audit all Rust `const` values against their Lean counterparts.
2. Verify `SyscallId::COUNT == 20` (post-AA1).
3. Verify `KernelError` variant count == 43 (post-AA1).
4. Verify `TypeTag` variant count == 7 (post-AA1).
5. Verify `AccessRights` bitmask constants match Lean.
6. Verify `IpcBuffer` size constant (960 bytes) matches Lean.
7. Add compile-time assertions (`const_assert!`) where possible.

**Verification**: `cargo test`, manual review.

---

## 6. Phase AA4 — IPC Timeout & Kernel Hardening

**Priority**: MEDIUM
**Gate**: All modified modules build, `test_smoke.sh` green, zero sorry/axiom
**Findings addressed**: M-2, M-4, L-1, L-2, L-3, L-9, L-10, L-12, L-13,
L-14, L-23 (13 sub-tasks covering 11 findings)

This phase addresses kernel-level code quality issues. The most significant
change is replacing the sentinel-value timeout detection (M-2) with a dedicated
TCB field, which has ripple effects on the IPC invariant proofs.

Sub-tasks AA4-A/B/C form a dependency chain (timeout refactor). All other
sub-tasks (AA4-D through AA4-M) are independent of each other and of the
timeout chain.

### AA4-A: Add `isTimedOut` flag to TCB structure (M-2, part 1)

**Finding**: `timeoutAwareReceive` uses `gpr x0 == 0xFFFFFFFF` as the sole
timeout signal. A legitimate IPC message writing `0xFFFFFFFF` to register x0
would falsely trigger timeout detection.

**Files**: `SeLe4n/Model/Object/Types.lean`

**Fix**:
1. Add `isTimedOut : Bool := false` field to the `TCB` structure.
2. Update `TCB.default` to include `isTimedOut := false`.
3. Update all `{ tcb with ... }` expressions that should reset the flag
   (e.g., when transitioning out of blocked state).
4. Update `BEq TCB` instance if it exists, to include the new field.

**Verification**: `source ~/.elan/env && lake build SeLe4n.Model.Object.Types`

### AA4-B: Use `isTimedOut` flag in timeout operations (M-2, part 2)

**Files**: `SeLe4n/Kernel/IPC/Operations/Timeout.lean`

**Fix**:
1. In `timeoutThread`: Set `isTimedOut := true` on the timed-out TCB instead
   of (or in addition to) writing `timeoutErrorCode` to register x0.
2. In `timeoutAwareReceive`: Replace the sentinel check
   `tcb.registerContext.gpr ⟨0⟩ = timeoutErrorCode ∧ tcb.ipcState = .ready`
   with `tcb.isTimedOut = true ∧ tcb.ipcState = .ready`.
3. After detecting timeout, clear the flag: `{ tcb with isTimedOut := false }`.
4. Remove or deprecate `timeoutErrorCode` constant (or retain as secondary
   signal for backward compatibility).

**Verification**: `source ~/.elan/env && lake build SeLe4n.Kernel.IPC.Operations.Timeout`

### AA4-C: Update timeout invariant proofs (M-2, part 3)

**Files**: `SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean` (or relevant
invariant files)

**Fix**:
1. Update `blockedThreadTimeoutConsistent` invariant to reference `isTimedOut`
   instead of the sentinel register value.
2. Update all preservation theorems that mention `timeoutErrorCode`.
3. Verify the invariant is still the 10th conjunct of `ipcInvariantFull` (14
   conjuncts total).
4. Update transport lemmas if affected.

**Verification**: `source ~/.elan/env && lake build SeLe4n.Kernel.IPC.Invariant`
then `./scripts/test_smoke.sh`

### AA4-D: Add TCB-existence precondition to `preserveContextSwitch` (M-4)

**Finding**: The generic `preserveContextSwitch` hook in `AdapterProofHooks`
does not type-enforce that the new thread's TCB exists or that the registers
match. The RPi5 contract enforces this, but the generic interface does not.

**Files**: `SeLe4n/Kernel/Architecture/Invariant.lean`

**Fix**:
1. Add precondition hypotheses to `preserveContextSwitch`:
   ```lean
   preserveContextSwitch :
     ∀ newTid newRegs st,
       proofLayerInvariantBundle st →
       (hTcbExists : st.objects[newTid.toObjId]?.isSome = true) →
       contract.registerContextStable st (contextSwitchState newTid newRegs st) →
       proofLayerInvariantBundle (contextSwitchState newTid newRegs st)
   ```
2. Update all implementations of `AdapterProofHooks` (Sim and RPi5) to carry
   the new hypothesis through.
3. Update callers that invoke `preserveContextSwitch` to supply the existence
   proof.

**Verification**: `source ~/.elan/env && lake build SeLe4n.Kernel.Architecture.Invariant`
and `lake build SeLe4n.Platform.Sim.ProofHooks` and
`lake build SeLe4n.Platform.RPi5.ProofHooks`

### AA4-E: Unify `TCB.timeSlice` default with `defaultTimeSlice` (L-1)

**Finding**: `TCB.timeSlice` is hardcoded to `5` (Types.lean:421) rather than
referencing the `defaultTimeSlice` constant.

**Files**: `SeLe4n/Model/Object/Types.lean`

**Fix**:
1. Locate the `defaultTimeSlice` constant definition.
2. Replace `timeSlice : Nat := 5` with `timeSlice : Nat := defaultTimeSlice`.
3. If `defaultTimeSlice` is defined after `TCB`, reorganize or use a forward
   reference.

**Verification**: `source ~/.elan/env && lake build SeLe4n.Model.Object.Types`

### AA4-F: Add `Notification.waitingThreads` size documentation (L-2)

**Finding**: `Notification.waitingThreads : List ThreadId` is unbounded. No
size invariant defined at type level.

**Files**: `SeLe4n/Model/Object/Types.lean`

**Fix**:
1. Add a documentation comment explaining the design decision: the list is
   unbounded at the type level, bounded in practice by the finite number of
   TCBs in the system (enforced by `objectStoreFinite` or equivalent).
2. Optionally, add a predicate `notificationWaitersWithinBound` that asserts
   `n.waitingThreads.length ≤ maxThreadCount` and document it as a future
   invariant candidate.

**Note**: This is documentation-only. Adding a type-level bound would require
pervasive changes to all notification operations and is not justified by the
risk level.

**Verification**: Manual review.

### AA4-G: Make `PagePermissions.ofNat` private (L-3)

**Finding**: `PagePermissions.ofNat` is public and can create W^X-violating
values. The safe `ofNat?` exists as an alternative.

**Files**: `SeLe4n/Model/Object/Structures.lean`

**Fix**:
1. Add `private` modifier to `PagePermissions.ofNat`.
2. Verify no external callers depend on `ofNat` (search for
   `PagePermissions.ofNat` across the codebase).
3. If external callers exist, migrate them to `ofNat?` or add a safe wrapper.

**Verification**: `source ~/.elan/env && lake build`

### AA4-H: Fix `hasSufficientBudget` fail-open on missing SchedContext (L-9)

**Finding**: Returns `true` (fail-open) when the SchedContext object is missing
from the store. This is asymmetric with `effectivePriority` which returns
`none`.

**Files**: `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`

**Fix**:
1. Change the `| _ => true` fallback to `| _ => false` (fail-closed).
2. Update the inline documentation comment to explain the change.
3. Verify all callers handle the `false` return correctly (a missing
   SchedContext should prevent scheduling, not allow it).
4. Check if any invariant guarantees prevent this branch from being reached
   (if so, document that the fail-closed behavior is defense-in-depth).

**Verification**: `source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Operations.Selection`
then `./scripts/test_smoke.sh`

### AA4-I: Document `pendingMessage` overwrite safety (L-10)

**Finding**: Notification signal overwrites `pendingMessage` without a
machine-checked invariant that `pendingMessage = none` at that point.

**Files**: `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`

**Fix**:
1. Add a documentation theorem (or comment block) explaining why overwrite is
   safe: the structural entry path analysis shows that `pendingMessage` is
   consumed before the next signal can arrive.
2. Optionally, add a `debug_assert`-style check in the test harness that
   verifies `pendingMessage = none` before overwrite.

**Note**: A full machine-checked invariant for this property would require
tracking message lifecycle across operations — disproportionate effort for
LOW severity. Document the safety argument instead.

**Verification**: Manual review.

### AA4-J: Add explicit self-donation guard (L-12)

**Finding**: `donateSchedContext` has no explicit `clientTid != serverTid` check.
Self-donation is structurally prevented by the caller (`applyCallDonation`
requires receiver to be `.unbound`), but no defense-in-depth guard exists.

**Files**: `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`

**Fix**:
1. Add an early-return guard at the top of `donateSchedContext`:
   ```lean
   if clientTid = serverTid then .error .invalidArgument
   ```
2. Add a documentation comment explaining this is defense-in-depth.

**Verification**: `source ~/.elan/env && lake build SeLe4n.Kernel.IPC.Operations.Endpoint`

### AA4-K: Fix slot-advance-on-error with short-circuit (L-13) — COMPLETE

**Finding**: Failed cap transfer in `ipcUnwrapCapsLoop` still advances the
receiver slot position. This differs from seL4 which preserves the cursor.

**Files**: `SeLe4n/Kernel/IPC/Operations/CapTransfer.lean`,
`SeLe4n/Kernel/Capability/Invariant/Preservation.lean`

**Implementation** (Design C — don't advance nextBase on error AND short-circuit
on fatal error):
1. Added `fillRemainingNoSlot` pure helper: fills remaining cap results with
   `.noSlot` without touching state or advancing the slot cursor.
2. Modified `ipcUnwrapCapsLoop` error branch: on `ipcTransferSingleCap` failure,
   the loop no longer advances `nextBase` and immediately short-circuits via
   `fillRemainingNoSlot` for all remaining caps. This exploits the observation
   that error conditions persist (receiver CSpace root unchanged), so subsequent
   transfers would fail identically.
3. Fixed all 8 loop-level preservation theorem error branches: replaced recursive
   `ih ... hStep` with direct `obtain ⟨_, rfl⟩ := hStep; ...` since the error
   branch now returns state unchanged (no recursion).
4. Fixed downstream proof in `Preservation.lean:2046`: same pattern — error
   branch proof simplified from `ih` application to direct extraction.
5. Updated module docstring to document the new semantics.

**Benefits**:
- Aligns with seL4's cursor-preservation semantics (no slot gaps on error).
- Short-circuit avoids redundant computation for caps that would all fail.
- Preservation proofs are simpler (direct `rfl` vs. induction hypothesis).
- Zero sorry/axiom. Full build + smoke tests pass.

**Post-implementation audit** (completed):
- Verified only reachable error from `ipcTransferSingleCap` is `.objectNotFound`
  (line 1027) — `targetSlotOccupied` is unreachable per `findFirstEmptySlot_spec`.
- Confirmed error persistence: state unchanged on error, subsequent caps would
  fail identically in single-threaded model.
- Fixed docstring inaccuracy: "Failures on individual caps do NOT abort" changed
  to "Non-fatal failures (`.noSlot`, `.grantDenied`) do NOT abort" — fatal
  errors now correctly documented as triggering short-circuit.
- Added `ipcUnwrapCaps` docstring bullet for fatal error short-circuit behavior.
- Added 3 negative test cases in `tests/NegativeStateSuite.lean`:
  - L13-01: 3 caps with receiver root = TCB → all `.noSlot`
  - L13-02: State (objects, services) unchanged after short-circuit
  - L13-03: 1 cap with missing receiver root → `.noSlot`, state unchanged

**Verification**: `lake build` (216 modules), `test_full.sh` (all tiers pass),
zero warnings/sorry/axiom.

### AA4-L: Remove unused `_endpointId` parameter from `timeoutAwareReceive` (L-14)

**Finding**: The `_endpointId` parameter in `timeoutAwareReceive` is unused
(prefixed with underscore, documented as "reserved for future validation").

**Files**: `SeLe4n/Kernel/IPC/Operations/Timeout.lean`

**Fix**:
1. Remove the `_endpointId` parameter from `timeoutAwareReceive`.
2. Update all callers to remove the argument.
3. Remove the "reserved for future validation" comment.

**Note**: If a future validation use case is imminent, retain the parameter.
Given that no validation was added across Z6–Z9, removal is appropriate.

**Verification**: `source ~/.elan/env && lake build SeLe4n.Kernel.IPC.Operations.Timeout`

### AA4-M: Remove or rename unused `Budget.refill` (L-23)

**Finding**: `Budget.refill` (Types.lean:49) uses `min b.val ceiling.val` which
caps at ceiling rather than increasing. The function is unused in the codebase —
actual refill logic is in `Budget.lean:applyRefill`.

**Files**: `SeLe4n/Kernel/SchedContext/Types.lean`

**Fix**:
1. Search for `Budget.refill` or `.refill` usage across the codebase.
2. If truly unused, remove the function entirely.
3. If used, rename to `Budget.capAtCeiling` to match actual semantics.

**Verification**: `source ~/.elan/env && lake build SeLe4n.Kernel.SchedContext.Types`

---

## 7. Phase AA5 — Information Flow & Safety Guards

**Priority**: MEDIUM
**Gate**: All modified modules build, `test_full.sh` green, zero sorry/axiom
**Findings addressed**: M-3, L-15, L-16, L-17, L-18, L-19

This phase adds compile-time and documentation guards to prevent insecure
configurations from reaching production. All sub-tasks are independent.

### AA5-A: Add production guard for `defaultLabelingContext` (M-3)

**Finding**: `defaultLabelingContext` assigns `publicLabel` to ALL entities,
defeating all information-flow enforcement. Formally proven insecure
(Policy.lean:228-256). No compile-time guard prevents production use.

**Files**: `SeLe4n/Kernel/InformationFlow/Policy.lean`

**Fix**:
1. Add a `@[deprecated]` attribute to `defaultLabelingContext`:
   ```lean
   @[deprecated "defaultLabelingContext defeats all IF enforcement — use only in tests"]
   def defaultLabelingContext : GenericLabelingContext := ...
   ```
2. Alternatively, gate it behind a `TEST_ONLY` namespace or section.
3. Add a compile-time check in the kernel API module that the labeling context
   used by production dispatch is not `defaultLabelingContext`. This could be a
   simple `#guard` or a theorem asserting the production context differs.

**Note**: The existing `defaultLabelingContext_insecure` theorem already proves
the insecurity — this sub-task adds a practical guard against accidental use.

**Verification**: `source ~/.elan/env && lake build SeLe4n.Kernel.InformationFlow.Policy`

### AA5-B: Add production guard for `DomainFlowPolicy.allowAll` (L-15)

**Finding**: `DomainFlowPolicy.allowAll` permits all inter-domain flows,
defeating enforcement. No production guard.

**Files**: `SeLe4n/Kernel/InformationFlow/Policy.lean`

**Fix**:
1. Add a `@[deprecated]` attribute or documentation warning to `allowAll`.
2. Add a documentation theorem that `allowAll` is the top element of the
   policy lattice (equivalent to no enforcement).

**Verification**: `source ~/.elan/env && lake build SeLe4n.Kernel.InformationFlow.Policy`

### AA5-C: Document `EndpointFlowPolicy` widening risk (L-16)

**Finding**: Per-endpoint flow policy overrides can widen beyond the global
policy. The `endpointPolicyRestricted` predicate exists as an optional guard
but is not enforced by `endpointFlowCheck` itself.

**Files**: `SeLe4n/Kernel/InformationFlow/Policy.lean`

**Fix**:
1. Add documentation to `endpointFlowCheck` explaining that callers MUST assert
   `endpointPolicyRestricted` as a precondition for security guarantees.
2. Add a documentation theorem showing that without `endpointPolicyRestricted`,
   the endpoint override can permit flows blocked by the global policy.
3. Consider adding an `endpointFlowCheckRestricted` variant that takes the
   predicate as a hypothesis parameter (type-level enforcement).

**Verification**: `source ~/.elan/env && lake build SeLe4n.Kernel.InformationFlow.Policy`

### AA5-D: Document `registerContext` projection limitations (L-17)

**Finding**: TCB `registerContext` is stripped to `default` in the information
flow projection (Projection.lean:200). This means the NI proof cannot detect
register-level information leaks between security domains.

**Files**: `SeLe4n/Kernel/InformationFlow/Projection.lean`

**Fix**:
1. Add a documentation comment at line 200 explaining:
   - Why register contents are projected away (registers may contain
     domain-private computation results that would trivially violate NI).
   - The resulting limitation: scheduler-level register leaks (e.g., via
     context switch timing or register residue) are not covered by NI proofs.
   - This is an accepted covert channel, consistent with `acceptedCovertChannel_scheduling`.
2. Add a cross-reference to the accepted covert channel documentation.

**Verification**: Manual review.

### AA5-E: Strengthen `assumptionInventoryComplete` (L-18)

**Finding**: `assumptionInventoryComplete` is a tautology — it quantifies over
a finite enum and proves membership by case exhaustion. It cannot detect missing
assumptions if a new assumption category is added to the enum without adding it
to the inventory.

**Files**: `SeLe4n/Kernel/Architecture/Assumptions.lean`

**Fix**:
1. Add a `#guard` or `static_assert`-style check that the assumption inventory
   list length equals the number of `ArchAssumptionCategory` constructors:
   ```lean
   #guard assumptionInventory.length = 5  -- Update when adding variants
   ```
2. Add documentation explaining the limitation: this theorem proves inventory
   completeness for the CURRENT enum, but adding a new constructor without
   updating the inventory will be caught only if the `#guard` count is updated.
3. Alternatively, derive the inventory automatically from the enum.

**Verification**: `source ~/.elan/env && lake build SeLe4n.Kernel.Architecture.Assumptions`

### AA5-F: Document boot contract defaults (L-19)

**Finding**: `objectStoreNonEmpty` and `irqRangeValid` in the boot contract
structure default to `True` — vacuous truths for platforms that don't override.

**Files**: `SeLe4n/Kernel/Architecture/Assumptions.lean`

**Fix**:
1. Add documentation comments to both fields explaining:
   - The default `True` is a deliberately permissive baseline for platforms
     that cannot provide a substantive proof.
   - Production platforms (RPi5) override with substantive contracts.
   - The Sim platform keeps `True` as it is non-production.
2. Add a documentation theorem showing that the RPi5 boot contract provides
   non-trivial values for both fields.

**Note**: Changing the default to `False` would break all platforms that don't
override — disproportionate. Documentation is the appropriate fix.

**Verification**: Manual review.

### AA5-G: Add `endpointFlowCheckRestricted` type-safe variant (L-16, stretch)

**Finding**: This is an optional stretch goal extending AA5-C.

**Files**: `SeLe4n/Kernel/InformationFlow/Policy.lean`

**Fix**:
1. Define `endpointFlowCheckRestricted` that takes `endpointPolicyRestricted`
   as a hypothesis:
   ```lean
   def endpointFlowCheckRestricted (ctx : GenericLabelingContext)
       (epPolicy : EndpointFlowPolicy)
       (hRestricted : endpointPolicyRestricted ctx.domainPolicy epPolicy)
       (endpointId : ObjId) (src dst : SecurityDomain) : Bool := ...
   ```
2. Prove that this variant is always at least as restrictive as the global
   policy check.
3. Use this variant in enforcement wrappers.

**Verification**: `source ~/.elan/env && lake build SeLe4n.Kernel.InformationFlow.Policy`

---

## 8. Phase AA6 — Platform & Architecture Fixes

**Priority**: LOW
**Gate**: All modified modules build, `test_smoke.sh` green
**Findings addressed**: L-20, L-21, L-22, plus documentation for L-4, L-5,
L-6, L-7, L-8

This phase addresses platform-level code quality issues and documents
acknowledged design decisions.

### AA6-A: Add deeper bus hierarchy search to `extractInterruptController` (L-20)

**Finding**: DTB interrupt controller search only checks top-level nodes and
immediate children (2 levels). Deep bus hierarchies (e.g., PCIe→GIC) would
be missed.

**Files**: `SeLe4n/Platform/DeviceTree.lean`

**Fix**:
1. Replace the two-level search with a fuel-bounded recursive search:
   ```lean
   def findGicNode (nodes : List FdtNode) (fuel : Nat) : Option FdtNode :=
     match fuel with
     | 0 => none
     | fuel' + 1 =>
       match nodes.find? isGicNode with
       | some n => some n
       | none => nodes.findSome? fun n => findGicNode n.children fuel'
   ```
2. Use a reasonable fuel bound (e.g., 4 levels, matching typical DTB depth).
3. Keep the existing `isGicNode` predicate logic unchanged.
4. Add a test case for nested GIC nodes.

**Note**: Most ARM platforms have GIC at top level or one level deep. This is
defense-in-depth for unusual board configurations.

**Verification**: `source ~/.elan/env && lake build SeLe4n.Platform.DeviceTree`

### AA6-B: Add DTB memory region overflow validation (L-21)

**Finding**: DTB memory regions with `size=0` or `base+size > 2^64` are not
validated before use in `MachineConfig` construction.

**Files**: `SeLe4n/Platform/DeviceTree.lean`

**Fix**:
1. In `fdtRegionsToMemoryRegions`, add validation:
   - Reject regions where `size = 0`.
   - Reject regions where `base + size` would overflow 64-bit address space.
2. Use `Option` return type or filter out invalid regions.
3. Add documentation comment explaining the validation.

**Verification**: `source ~/.elan/env && lake build SeLe4n.Platform.DeviceTree`

### AA6-C: Add `foldIrqs` duplicate detection documentation (L-22)

**Finding**: `foldIrqs` uses `foldl` with `registerIrq` which uses last-wins
semantics on duplicate IRQ entries.

**Files**: `SeLe4n/Platform/Boot.lean`

**Fix**:
1. Add a documentation comment to `foldIrqs` explaining:
   - Last-wins semantics on duplicate IRQ IDs.
   - This is the unchecked boot path — the checked path
     (`bootFromPlatformChecked`) validates uniqueness.
   - In practice, DTB IRQ entries are unique per interrupt controller spec.
2. Optionally, add a `debug_assert`-style noDup check in the test harness.

**Note**: Adding runtime duplicate detection would change the function signature
and ripple through boot proofs — disproportionate for LOW severity.

**Verification**: Manual review.

### AA6-D: Document acknowledged design decisions (L-4, L-5, L-6, L-7, L-8)

**Finding**: Several LOW findings are acknowledged design decisions that
require documentation rather than code changes:
- L-4: `maxHeartbeats 2000000` for CDT acyclicity proofs
- L-5: No keyed/randomized hashing (known hash-flooding limitation)
- L-6: Unconditional capacity doubling (bounded by kernel policy)
- L-7: Post-insert load can slightly exceed 75% (proven safe)
- L-8: O(n) RunQueue append (acceptable for ≤256 threads)

**Files**: Various (documentation comments in source)

**Fix**:
1. For each finding, verify that existing documentation comments adequately
   explain the design decision and its justification.
2. Where documentation is missing or insufficient, add inline comments.
3. Create a centralized "Design Decisions" section in
   `docs/spec/SELE4N_SPEC.md` or `docs/DEVELOPMENT.md` referencing these
   acknowledged limitations.

**Verification**: Manual review.

### AA6-E: Verify all platform module builds

**Files**: All `SeLe4n/Platform/**/*.lean` files

**Fix**:
1. Run `source ~/.elan/env && lake build SeLe4n.Platform.DeviceTree`.
2. Run `source ~/.elan/env && lake build SeLe4n.Platform.Boot`.
3. Run `source ~/.elan/env && lake build SeLe4n.Platform.Sim.Contract`.
4. Run `source ~/.elan/env && lake build SeLe4n.Platform.RPi5.Contract`.
5. Run `./scripts/test_smoke.sh`.

**Verification**: All module builds pass, smoke tests green.

---

## 9. Phase AA7 — Non-Interference Composition

**Priority**: HIGH (most significant formal gap in the kernel)
**Gate**: All NI proofs compile, `test_full.sh` green, zero sorry/axiom
**Findings addressed**: M-1
**Depends on**: AA4-A/B/C (timeout TCB flag changes the proof surface)

This is the most complex phase in the workstream. The `NonInterferenceStep`
inductive (32 constructors) and `KernelOperation` mapping do NOT include
dedicated constructors for the 8+ WS-Z SchedContext operations. These operations
currently rely on the `syscallDispatchHigh` fallback constructor which accepts
an opaque `hProj` hypothesis rather than proving projection preservation from
the operation's semantics. This means NI for the entire SchedContext subsystem
is **assumed at the composition layer, not proved from operational semantics**.

### Strategy

The fix requires:
1. Adding dedicated `NonInterferenceStep` constructors for each SchedContext
   operation (AA7-A through AA7-E).
2. Proving projection preservation for each operation (AA7-F through AA7-H).
3. Updating the coverage and composition theorems (AA7-I, AA7-J).

Each constructor requires a per-operation projection preservation lemma of
the form:

```lean
theorem schedContextConfigure_projection_preservation
    (labelCtx : GenericLabelingContext)
    (observer : SecurityDomain)
    (st : SystemState) (st' : SystemState)
    (hOp : schedContextConfigure args st = .ok st')
    (hInv : proofLayerInvariantBundle st)
    (hAuth : hasAuthority labelCtx.threadLabelOf tid observer) :
    projectState labelCtx observer st = projectState labelCtx observer st' := by
  ...
```

This proof pattern shows that the operation does not change the projected view
of any observer who does not have authority over the acting domain.

### AA7-A: Add `NonInterferenceStep.schedContextConfigure` constructor

**Files**: `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean`

**Fix**:
1. Add a new constructor to the `NonInterferenceStep` inductive:
   ```lean
   | schedContextConfigure :
       ∀ args tid st st',
         schedContextConfigure args st = .ok st' →
         proofLayerInvariantBundle st →
         (∀ observer, ¬hasAuthority labelCtx.threadLabelOf tid observer →
           projectState labelCtx observer st = projectState labelCtx observer st') →
         NonInterferenceStep labelCtx st st'
   ```
2. The hypothesis `hProj` must be discharged by a standalone lemma in AA7-F.

**Verification**: `source ~/.elan/env && lake build SeLe4n.Kernel.InformationFlow.Invariant.Composition`

### AA7-B: Add `NonInterferenceStep.schedContextBind` constructor

**Files**: `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean`

**Fix**: Same pattern as AA7-A, substituting `schedContextBind` for
`schedContextConfigure`. The bind operation modifies both TCB and SchedContext
objects, so the projection preservation proof must show that both modifications
are invisible to unauthorized observers.

**Verification**: `source ~/.elan/env && lake build SeLe4n.Kernel.InformationFlow.Invariant.Composition`

### AA7-C: Add `NonInterferenceStep.schedContextUnbind` constructor

**Files**: `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean`

**Fix**: Same pattern as AA7-A, substituting `schedContextUnbind`. The unbind
operation clears TCB binding and may remove from RunQueue/ReplenishQueue, so
the projection proof must account for scheduler state changes.

**Verification**: `source ~/.elan/env && lake build SeLe4n.Kernel.InformationFlow.Invariant.Composition`

### AA7-D: Add `NonInterferenceStep.timerTickBudget` constructor

**Files**: `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean`

**Fix**: `timerTickBudget` has 3 branches (budget remaining, budget exhausted,
replenishment). Each branch modifies different state. The constructor must
cover all branches. The existing `timerTick` constructor covers the basic
timer tick — this new constructor covers the budget-aware extension.

**Verification**: `source ~/.elan/env && lake build SeLe4n.Kernel.InformationFlow.Invariant.Composition`

### AA7-E: Add `NonInterferenceStep.donateSchedContext` constructor

**Files**: `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean`

**Fix**: Donation transfers a SchedContext from caller to callee. The projection
preservation proof must show that this transfer is only visible to observers
with authority over the caller's domain. This is the most subtle proof because
donation crosses domain boundaries during IPC.

**Note**: The donation constructors may need to cover:
- `donateSchedContext` (core transfer)
- `returnDonatedSchedContext` (return on reply)
- `cleanupDonatedSchedContext` (cleanup on destruction)

Depending on how these are wired through the IPC dispatch path, they may be
covered by existing `endpointCall`/`endpointReply` constructors with the
donation as a sub-operation. Investigate before adding separate constructors.

**Verification**: `source ~/.elan/env && lake build SeLe4n.Kernel.InformationFlow.Invariant.Composition`

### AA7-F: Prove `schedContextConfigure` projection preservation

**Files**: `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean`

**Fix**:
1. Add theorem `schedContextConfigure_projection_preservation` following the
   pattern described in the Strategy section above.
2. The proof proceeds by:
   a. Unfolding `schedContextConfigure` to expose the state modifications.
   b. Showing that only the target SchedContext object and possibly the
      caller's TCB are modified.
   c. Using field-disjointness lemmas to show unrelated objects are unchanged.
   d. Showing that the modified objects are only visible to observers with
      authority over the caller's domain.
3. This may require new helper lemmas about `projectState` behavior when
   only specific objects change.

**Verification**: `source ~/.elan/env && lake build SeLe4n.Kernel.InformationFlow.Invariant.Operations`

### AA7-G: Prove `schedContextBind`/`Unbind` projection preservation

**Files**: `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean`

**Fix**:
1. Add `schedContextBind_projection_preservation` theorem.
2. Add `schedContextUnbind_projection_preservation` theorem.
3. Both proofs follow the same pattern as AA7-F but must additionally handle:
   - TCB `schedContextBinding` field changes.
   - RunQueue insertions/removals (bind inserts, unbind removes).
   - ReplenishQueue removals (unbind).
4. Use existing scheduler field-disjointness witnesses.

**Verification**: `source ~/.elan/env && lake build SeLe4n.Kernel.InformationFlow.Invariant.Operations`

### AA7-H: Prove `timerTickBudget`/`donation` projection preservation

**Files**: `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean`

**Fix**:
1. Add `timerTickBudget_projection_preservation` theorem.
2. Add `donateSchedContext_projection_preservation` theorem (if needed per
   AA7-E investigation).
3. The timer tick proof must handle all 3 branches:
   - Budget remaining: only `budgetRemaining` decremented.
   - Budget exhausted: thread descheduled + timeout processing.
   - Replenishment: `processReplenishmentsDue` modifies replenish queue.
4. The donation proof must handle the cross-domain transfer case.

**Verification**: `source ~/.elan/env && lake build SeLe4n.Kernel.InformationFlow.Invariant.Operations`

### AA7-I: Update `niStepCoverage` for operational correspondence

**Finding**: `niStepCoverage` currently uses `syscallDecodeError` as a universal
witness — it proves constructor existence only, not operational correspondence.

**Files**: `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean`

**Fix**:
1. Update `KernelOperation` to include SchedContext operation variants:
   - `.schedContextConfigure`
   - `.schedContextBind`
   - `.schedContextUnbind`
   - `.timerTickBudget`
   - `.donateSchedContext` (if separate from IPC)
2. Update `niStepCoverage` to map each new `KernelOperation` variant to its
   corresponding `NonInterferenceStep` constructor.
3. Update `niStepCoverage_operational` to prove the mapping is semantically
   correct (not just existential).
4. Update `niStepCoverage_injective` and `niStepCoverage_count` as needed.

**Verification**: `source ~/.elan/env && lake build SeLe4n.Kernel.InformationFlow.Invariant.Composition`

### AA7-J: Integration with trace composition theorems

**Files**: `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean`

**Fix**:
1. Verify that the existing `traceNonInterference` theorem still holds with
   the new constructors (it should, since the new constructors are strictly
   more specific than the fallback they replace).
2. Remove reliance on `syscallDispatchHigh` fallback for SchedContext operations.
3. Update `enforcementBoundary` if the new operations need explicit entries
   (they may already be covered by the 3 `.capabilityOnly` SchedContext entries).
4. Run `./scripts/test_full.sh` to verify all invariant surface anchors pass.

**Verification**: `source ~/.elan/env && lake build SeLe4n.Kernel.InformationFlow.Invariant.Composition`
then `./scripts/test_full.sh`

---

## 10. Phase AA8 — Documentation & Closure

**Priority**: LOW
**Gate**: All docs consistent, `test_fast.sh` green, website links intact
**Depends on**: All prior phases

This phase synchronizes all documentation with the code changes made in
AA1–AA7 and closes out the workstream.

### AA8-A: Update `docs/spec/SELE4N_SPEC.md`

**Fix**:
1. Update Rust ABI section to reflect 20 syscall variants, 43 error variants,
   7 TypeTag variants.
2. Document the `isTimedOut` TCB flag (replaces sentinel timeout).
3. Document the `hasSufficientBudget` fail-closed change.
4. Document new NI constructors for SchedContext operations.
5. Update any SchedContext section references.

### AA8-B: Update `docs/DEVELOPMENT.md`

**Fix**:
1. Update Rust ABI synchronization guidance.
2. Document the CI Rust toolchain pinning approach.
3. Update pre-commit hook documentation.

### AA8-C: Update `docs/WORKSTREAM_HISTORY.md`

**Fix**:
1. Add WS-AA entry with phase summaries and sub-task counts.
2. Mark WS-AA as COMPLETE with version number.
3. Update the "Next milestone" pointer.

### AA8-D: Update `README.md`

**Fix**:
1. Sync metrics from `docs/codebase_map.json` (`readme_sync` key).
2. Update version number references.
3. Update Rust ABI variant counts in any summary tables.

### AA8-E: Regenerate `docs/codebase_map.json`

**Fix**:
1. Run the codebase map generation script.
2. Update module counts, line counts, theorem counts.
3. Verify `readme_sync` key is current.

### AA8-F: Update `CHANGELOG.md`

**Fix**:
1. Add version entry documenting all WS-AA changes.
2. Organize by phase (AA1: Rust ABI, AA2: CI, etc.).
3. Highlight the NI composition closure (AA7) as a major milestone.

### AA8-G: Update `docs/CLAIM_EVIDENCE_INDEX.md`

**Fix**:
1. Update any claims affected by the NI composition changes.
2. Add evidence references for the new SchedContext NI proofs.
3. Update Rust ABI completeness claims.

### AA8-H: Verify website link manifest

**Fix**:
1. Run `./scripts/check_website_links.sh`.
2. If any paths were renamed or moved, update
   `scripts/website_link_manifest.txt`.
3. Verify CI passes.

---

## 11. Risk Assessment

### High-Risk Sub-tasks

| Sub-task | Risk | Mitigation |
|----------|------|------------|
| AA4-A/B/C (timeout TCB flag) | Ripple through IPC invariant proofs | Implement in 3 stages with verification at each |
| AA4-H (hasSufficientBudget fail-closed) | May change scheduler behavior | Verify all callers; check if invariants prevent the branch |
| AA7-F/G/H (projection preservation proofs) | Complex proof engineering | Build on existing `Operations.lean` patterns; start with simplest op |
| AA7-J (trace composition integration) | May surface hidden assumptions | Run full test suite; verify no `sorry` introduced |

### Low-Risk Sub-tasks

Most AA1, AA2, AA3 sub-tasks are straightforward mechanical changes with
clear specifications. AA5 and AA6 are primarily documentation additions.
AA8 is documentation-only.

### Rollback Strategy

Each phase produces independently verifiable results:
- AA1: Rust tests must pass (cargo test).
- AA2: CI must pass on the branch.
- AA3: Rust tests must pass.
- AA4: Each module must build individually; smoke tests pass.
- AA5: Each module must build; full tests pass.
- AA6: Each module must build; smoke tests pass.
- AA7: Each NI module must build; full tests pass.
- AA8: Fast tests + website link check pass.

If a phase introduces regressions, revert the phase and investigate.
Individual sub-tasks within a phase are atomic and independently revertible.

---

## 12. Effort Estimates

| Phase | Estimated Effort | Parallelizable |
|-------|-----------------|----------------|
| AA1 | 2–3 hours | Yes (sub-tasks independent) |
| AA2 | 1–2 hours | Yes (all independent) |
| AA3 | 1–2 hours | Partially (AA3-D depends on AA1) |
| AA4 | 4–6 hours | Partially (AA4-A/B/C sequential; rest parallel) |
| AA5 | 2–3 hours | Yes (all independent) |
| AA6 | 1–2 hours | Yes (all independent) |
| AA7 | 8–16 hours | Partially (proofs build on each other) |
| AA8 | 2–3 hours | Partially (needs prior phase results) |
| **Total** | **21–37 hours** | |

AA7 (NI Composition) dominates the effort. The projection preservation proofs
require careful analysis of each operation's state modifications and their
interaction with the projection function. If the existing NI proof infrastructure
in `Operations.lean` provides reusable patterns, the lower bound is achievable.

---

## 13. Completion Criteria

The workstream is COMPLETE when:

1. **Zero erroneous findings remain** — all 39 actionable findings addressed.
2. **Zero sorry/axiom** in production proof surface.
3. **Rust ABI fully synchronized** — all Lean variants reflected in Rust with
   conformance tests.
4. **NI composition gap closed** — dedicated constructors for all SchedContext
   operations with per-operation projection preservation proofs.
5. **CI hardened** — Rust toolchain pinned, pre-commit hook safe, SHA-256
   fail-closed.
6. **All test tiers pass**:
   - `./scripts/test_fast.sh` (Tier 0+1)
   - `./scripts/test_smoke.sh` (Tier 0–2)
   - `./scripts/test_full.sh` (Tier 0–3)
   - `cargo test` (all Rust crates)
7. **Documentation synchronized** — spec, dev docs, workstream history,
   README, changelog, claims index, website manifest.

---

*End of workstream plan.*
