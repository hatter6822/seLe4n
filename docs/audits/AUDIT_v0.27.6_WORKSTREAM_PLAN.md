# WS-AI Workstream Plan — Post-Audit Comprehensive Remediation (v0.27.6)

**Created**: 2026-04-12
**Baseline version**: 0.27.6
**Baseline audit**: `docs/audits/AUDIT_v0.27.6_COMPREHENSIVE.md` (5 HIGH, 27 MEDIUM, 28 LOW)
**Prior portfolios**: WS-AH (COMPLETE), WS-AG (COMPLETE), WS-AF (COMPLETE), WS-AE (COMPLETE), WS-AD (COMPLETE), WS-AC (COMPLETE), WS-AB (COMPLETE), WS-AA (COMPLETE) — see `docs/WORKSTREAM_HISTORY.md`
**Hardware target**: Raspberry Pi 5 (ARM64)
**Constraint**: Zero sorry/axiom. All phases must pass `lake build` + `test_smoke.sh` at minimum.

---

## 1. Executive Summary

The v0.27.6 Comprehensive Pre-Release Audit examined all 159 Lean files
(~90,000 lines) and 48 Rust files (~7,500 lines). It identified 60 findings
(5 HIGH, 27 MEDIUM, 28 LOW). This workstream plan addresses all actionable
findings through 7 phases with 37 sub-tasks, after filtering out erroneous
findings, already-tracked deferrals, and confirmed-correct design decisions.

### 1.1 Finding Disposition Summary

| Disposition | Count | Details |
|-------------|-------|---------|
| **Actionable (code change)** | 22 | H-01, H-02, H-03, H-04, H-05, M-01, M-04, M-09, M-14, M-15, M-19, M-20, M-22, M-26, M-27, L-05, L-09, L-10, L-15, L-17, L-24, L-26 |
| **Documentation-only** | 15 | M-02, M-03, M-07, M-08, M-10, M-11, M-13, M-16, M-17, M-18, M-21, M-23, M-24, M-25, L-02 |
| **Erroneous / refuted** | 5 | M-05, M-12, L-06, L-13, L-28 |
| **No-action (confirmed correct)** | 12 | M-06, L-01, L-03, L-04, L-07, L-08, L-11, L-12, L-14, L-16, L-19, L-22 |
| **Deferred (WS-V / hardware)** | 6 | L-18, L-20, L-21, L-23, L-25, L-27 |

### 1.2 Plan Structure

| Phase | Focus | Sub-tasks | Key Findings | Gate |
|-------|-------|-----------|-------------|------|
| AI1 | Rust ABI & Trap Correctness | 5 | H-04, H-05, M-26, M-27 | `cargo test` + `cargo clippy` |
| AI2 | Interrupt & Architecture Safety | 5 | H-03, M-14, M-15, M-20 | `lake build` + `test_smoke.sh` |
| AI3 | Scheduler & PIP Correctness | 5 | M-04, M-22, L-09, L-10 | `lake build` + `test_smoke.sh` |
| AI4 | IPC & SchedContext Hardening | 4 | M-01, M-09, L-05 | `lake build` + `test_smoke.sh` |
| AI5 | Platform & Simulation Safety | 5 | H-01, H-02, M-19 | `lake build` + `test_smoke.sh` |
| AI6 | Documentation & Proof Gaps | 7 | M-02..M-25, L-02, L-15, L-24 | `test_full.sh` + doc sync |
| AI7 | Testing, Closure & Final Gate | 6 | L-17, L-26, fixture sync | `test_full.sh` + `cargo test` |

**Estimated scope**: ~450–650 lines Lean (functions, theorems, test sites),
~120–180 lines Rust, ~200–350 lines documentation.

**Total sub-tasks**: 37 (across 7 phases)

---

## 2. Finding Cross-Reference and Verification

Every finding from the baseline audit was independently re-verified against
source code before inclusion in this plan. This section classifies each finding
and provides the verification rationale.

### 2.1 Erroneous / Refuted Findings (5)

| Finding | Audit Severity | Actual | Rationale |
|---------|---------------|--------|-----------|
| M-05 | MEDIUM | **ERRONEOUS** | `timeoutBlockedThreads` does NOT discard per-thread timeout errors. Return type is `SystemState × List (ThreadId × KernelError)` (Core.lean:505). Errors are explicitly collected via `errs ++ [(tid, e)]` (line 519). This was fixed in AG1-B. The audit finding is factually incorrect. |
| M-12 | MEDIUM | **ERRONEOUS** | `resolveCapAddress` intermediate CNode read-right skipping is a **documented deliberate design divergence** from seL4 (Operations.lean:85-92, U-M25 annotation). Rights are enforced at the operation layer via `capHasRight` guards at each callsite (`cspaceMint`, `cspaceCopy`, etc.), covering all access paths. This is an architectural design decision, not a vulnerability. |
| L-06 | LOW | **ERRONEOUS** | CDT acyclicity is NOT externalized for expanding operations. Grep for `retype.*acyclicity` returns no results. Acyclicity proofs for retype remain internal via `edgeWellFounded` and `freshChild_not_reachable` bridge (AE4-C/U-18). |
| L-13 | LOW | **ERRONEOUS** | `schedContextBind` DOES check thread state. Precondition checks at line 142-144 verify the TCB is `.unbound` before binding. The audit claim that "doesn't check thread state" is factually wrong. |
| L-28 | LOW | **ERRONEOUS** | StateBuilder DOES check IPC/SchedContext/CDT invariants. `InvariantChecks.stateInvariantChecksFor` (lines 321-363) includes endpoint dual-queue validation, notification queue/state checks, CDT childMap/parentMap consistency, and blocked-thread runability checks. |

### 2.2 No-Action Findings (12)

These findings describe confirmed-correct design patterns, seL4-matching
semantics, or invariant-protected code paths. No code or documentation changes
are needed.

| Finding | Rationale |
|---------|-----------|
| M-06 | FFI.lean's 17 `@[extern]` declarations are correctly disconnected from the production chain. They are Lean-side FFI stubs for hardware binding. They will be wired when the Lean→Rust FFI bridge is activated (WS-V / hardware bring-up). Wiring them prematurely without a working FFI runtime would break the build. This is correct architecture, not dead code. |
| L-01 | Unbounded `Nat` identifiers are by design (AC4-C/F-01). ABI validation occurs at decode boundaries (`RegisterDecode`, `SyscallArgDecode`), not at type wrapping. Internal `Nat` allows unbounded proof reasoning. |
| L-03 | Notification LIFO wait semantics are seL4-compliant. O(1) enqueue via cons. Documented at Types.lean:671-676. |
| L-04 | `donateSchedContext` defensive check at Endpoint.lean:192 validates `sc.boundThread != some clientTid` (AUD-3b). The binding check is present, just structured differently than the audit expects. |
| L-07 | `cspaceRevokeCdt` materializing the full descendant list upfront is correct for the sequential model. No concurrent modification is possible. The list is computed once and consumed. |
| L-08 | Arbitrary badge values through mint matches seL4 semantics exactly. Badge validation is the caller's responsibility. Documented with `BadgeOverflowSuite` (22 tests). |
| L-11 | `schedContextYieldTo` returns explicit errors — confirmed via code review. Not a silent no-op. |
| L-12 | Replenishment truncation dropping oldest entries is correct CBS semantics — oldest replenishments are least likely to be relevant. Budget.lean:76. |
| L-14 | `pip_bounded_inversion` using `objectIndex.length` as bound is sound because thread count ≤ object count. The bound is conservative but correct. |
| L-16 | CBS bandwidth 8× weaker than ideal is a documented proof-precision issue (AF4-F, Budget.lean:81). Per-context budget bounds still hold. |
| L-19 | InterruptId `Fin 224` hardcoded to BCM2712/GIC-400 is correct for the sole hardware target (RPi5). Parameterization deferred to multi-platform support (WS-V). |
| L-22 | `extractPeripherals` 2-level DTB depth limitation is documented (AF3-D) and sufficient for RPi5's flat device tree topology. |

### 2.3 Deferred Findings (6)

| Finding | Deferral | Rationale |
|---------|----------|-----------|
| L-18 | WS-V | Bump allocator page table memory reclamation. Not needed until multi-process runtime with VSpace teardown. |
| L-20 | WS-V | Timer division truncation guard. Sequential model uses exact `Nat` arithmetic. Hardware binding will use fixed-point. |
| L-21 | WS-V | Targeted TLB flush wiring into production paths — `adapterFlushTlbByVAddr` exists and is proven; wiring depends on VSpaceARMv8 production integration. |
| L-23 | WS-V | `bootFromPlatform` empty config validation. `bootFromPlatformChecked` variant already exists for production paths (Boot.lean:370). |
| L-25 | WS-V | `pendingMessage` NI declassification formal bridge. Requires WS-H11 memory projection model. |
| L-27 | WS-V | RadixTree `lookup_insert_ne` precondition strengthening. Current precondition (distinct radix indices) is stricter but correct. The weaker precondition (distinct keys) is a proof improvement, not a correctness issue. |

### 2.4 Actionable Findings — Verification Summary (22)

| Finding | Severity | Verified | Evidence | Phase |
|---------|----------|----------|----------|-------|
| H-01 | **HIGH** | Confirmed | `simBootContract` (BootContract.lean:33-36): all 4 predicates literally `True`. `objectTypeMetadataConsistent := True`, `capabilityRefMetadataConsistent := True`, `objectStoreNonEmpty := True`, `irqRangeValid := True`. Tests never validate boot invariants. | AI5 |
| H-02 | **HIGH** | Confirmed | `simInterruptContract` (BootContract.lean:44-45): `irqLineSupported := fun _ => True`, `irqHandlerMapped := fun _ _ => True`. Accepts ALL IRQs unconditionally. | AI5 |
| H-03 | **HIGH** | Confirmed | `interruptDispatchSequence` (InterruptDispatch.lean:127-134): error path returns `.error e` without calling `endOfInterrupt`. Success path correctly calls `endOfInterrupt` at line 133. Comment at lines 104-105 acknowledges the bug. | AI2 |
| H-04 | **HIGH** | Confirmed | `handle_exception` SVC arm (trap.rs:162-165): sets `x0 = 0` and returns. No Lean FFI dispatch. Documented as "AG7 will wire this." Deliberate stub but HIGH for hardware bring-up. | AI1 |
| H-05 | **HIGH** | Confirmed | trap.rs:179 and 184: both alignment and unknown exceptions set `x0 = 43` (AlignmentError). Lean ExceptionModel.lean:175-177 maps both to `.userException` (discriminant 45). ABI mismatch. | AI1 |
| M-01 | **MEDIUM** | Confirmed | `cleanupPreReceiveDonation` (Donation.lean:191) has zero production callers. API dispatch `.receive` paths (API.lean:633-638, 837-842) call `endpointReceiveDual` without cleanup. Donated SchedContext leaks on receive-without-reply. | AI4 |
| M-04 | **MEDIUM** | Confirmed | `handleYield` (Core.lean:341) re-enqueues at `tcb.priority` (base). Comment at lines 332-340 calls it intentional, but PIP-boosted threads drop to base priority band on yield — priority inversion risk. `resolveInsertPriority` helper exists (Selection.lean:345) and is used at 5 other sites. | AI3 |
| M-09 | **MEDIUM** | Confirmed | DTB parser fuel=2000 (DeviceTree.lean:619). Returns `none` on fuel exhaustion (line 627). Large DTBs silently fail parse. Should surface fuel exhaustion as a distinct error. | AI4 |
| M-14 | **MEDIUM** | Confirmed | `unmapPage` (VSpaceARMv8.lean:189-206) returns `some { vs with shadow := shadow' }` on HW walk failure. Shadow state updated, no error surfaced. Shadow/HW divergence possible. | AI2 |
| M-15 | **MEDIUM** | Confirmed | ASID reuse from free list (AsidManager.lean:91-96) sets `requiresFlush := false`. No type-level constraint forces TLB flush before reuse. Boolean flag only. | AI2 |
| M-19 | **MEDIUM** | Confirmed | `defaultLabelingContext` (Policy.lean:220-226) assigns `publicLabel` to all entities. Proven insecure via `defaultLabelingContext_insecure` theorem (line 240). No runtime guard prevents deployment. | AI5 |
| M-20 | **MEDIUM** | Confirmed | `suspendThread` (Suspend.lean:150-169) re-lookups TCB after `cancelIpcBlocking`. Temporal window where `schedContextBinding` metadata may be inconsistent. Safe in sequential model. | AI2 |
| M-22 | **MEDIUM** | Confirmed | `migrateRunQueueBucket` (PriorityManagement.lean:99-108) re-inserts at `newPriority` without consulting `pipBoost`. Same issue as M-04 — should use `resolveInsertPriority`. | AI3 |
| M-26 | **MEDIUM** | Confirmed | Dual timer reprogram: `ffi_timer_reprogram()` (ffi.rs:40-42) calls `reprogram_timer()` + `increment_tick_count()`. Same pair at trap.rs:199-200. Both paths firing doubles tick count. | AI1 |
| M-27 | **MEDIUM** | Confirmed | `pub static mut BOOT_UART` (uart.rs:179) with no synchronization. `kprint!` macro (line 220) accesses via raw pointer. UB after interrupts enabled. | AI1 |
| L-05 | **LOW** | Confirmed | `timeoutAwareReceive` (Timeout.lean:114-115) takes `_endpointId : ObjId` with underscore prefix. Unused parameter. Comment says "reserved for future validation." Dead parameter should be removed or activated. | AI4 |
| L-09 | **LOW** | Confirmed | `saveOutgoingContext` (Selection.lean:478-486) returns state unchanged on TCB lookup miss. Comment says "unreachable under currentThreadValid invariant." Should add `Except` return or defensive assertion. | AI3 |
| L-10 | **LOW** | Confirmed | `configDefaultTimeSlice` is plain `Nat` field (no `Pos` constraint). Test suites assign values like 5, 12 without bounds. Should enforce positivity. | AI3 |
| L-15 | **LOW** | Confirmed | BlockingGraph.lean:67 references `maxBlockingDepth (= 32)` in documentation comment but no such definition exists in code. Stale doc reference. | AI6 |
| L-17 | **LOW** | Confirmed | CBS admission ~6.4% over-admission from integer truncation in `budget * 1000 / period` (Budget.lean:204-217). Runtime impact. Should document tolerance or add rounding guard. | AI7 |
| L-24 | **LOW** | Confirmed | RPi5 RuntimeContract.lean:28-31 says "H3-prep stub" but lines 39-66 implement comprehensive 6-condition checks. Stale comment contradicts substantive implementation. | AI6 |
| L-26 | **LOW** | Confirmed | `lifecycleRetypeObject` (Operations.lean:460-469) is `public` despite internal-only intent. Comment notes proof dependencies require public visibility. Should use `protected` or scoped access. | AI7 |

### 2.5 Documentation-Only Findings (15)

| Finding | Documentation Action | Phase |
|---------|---------------------|-------|
| M-02 | Document `resolveExtraCaps` silent-drop semantics as seL4-matching design (API.lean:409-416 already has comment; add spec cross-reference in SELE4N_SPEC.md). | AI6 |
| M-03 | Document `RunQueue.size` as diagnostics-only field not proof-linked, with rationale (AF-40 precedent). | AI6 |
| M-07 | Document boot invariant bridge scope limitation (Boot.lean:503-519). Note that `bootToRuntime_invariantBridge_empty` proves only empty PlatformConfig; general config deferred to WS-V. | AI6 |
| M-08 | Document `fromDtb` stub status (DeviceTree.lean:139) and `fromDtbFull` alternative. Mark as H3 DTB parsing placeholder. | AI6 |
| M-10 | Document MMIO read RAM semantics limitation (MmioAdapter.lean:340-356). Note sequential model does not capture volatile register behavior. Hardware binding must substitute real MMIO reads. | AI6 |
| M-11 | Document `bootSafeObject` VSpaceRoot exclusion rationale (Boot.lean:947-960). ASID table registration unavailable during boot phase. | AI6 |
| M-13 | Document `physicalAddressBound` 2^52 default as proof-layer-only (VSpace.lean:50-61). Production dispatch uses `physicalAddressBoundForConfig` via `st.machine.physicalAddressWidth`. | AI6 |
| M-16 | Document D-cache → I-cache pipeline ordering gap (CacheModel.lean:275-287). Note hardware protocol requirement for self-modifying code safety. | AI6 |
| M-17 | Document context switch TLB/ASID maintenance gap (Adapter.lean:136-140). Note that VSpace operations handle ASID maintenance separately. | AI6 |
| M-18 | Document absence of cross-module TLB + cache + page table composition theorem. Note per-subsystem preservation is proven but relational composition deferred to WS-V. | AI6 |
| M-21 | Document CDT `descendantsOf` depth-1 fuel sufficiency scope (Structures.lean:2234-2246). Cross-reference TPI-DOC deferral. | AI6 |
| M-23 | Document `blockingChain` fuel-exhaustion truncation behavior (BlockingGraph.lean:70-82). Note PIP propagation terminates safely (stale boosts, not unsound). | AI6 |
| M-24 | Document `eventuallyExits` externalized hypothesis scope (BandExhaustion.lean:34-43). Note unbound-thread limitation and required external progress assumption. | AI6 |
| M-25 | Document WCRT theorem externalized hypotheses (WCRT.lean:167-187): `hDomainActiveRunnable` and `hBandProgress`. Note these encode runtime properties not mechanically derivable. | AI6 |
| L-02 | Document `allTablesInvExtK` 17-deep tuple projection fragility (State.lean:344) and named-extractor mitigation (Builder.lean:30-116). Cross-reference AF-26 tuple projection documentation. | AI6 |

---

## 3. Phase AI1 — Rust ABI & Trap Correctness (H-04, H-05, M-26, M-27)

**Objective**: Fix all Rust-side defects that would cause incorrect behavior
on ARM64 hardware: wrong exception error codes, no-op syscall handler, dual
timer reprogram, and unsafe UART static. These are the highest-priority fixes
because they affect the Lean–Rust ABI contract and would manifest immediately
on hardware bring-up.

**Dependencies**: None (first phase, Rust-only).

**Gate**: `cargo test --workspace` + `cargo clippy --workspace` (0 warnings)

### 3.1 Sub-tasks

#### AI1-A: Fix exception error codes in `trap.rs` (H-05)

**Finding**: H-05 — Alignment and unknown exception error codes use
discriminant 43 (`AlignmentError`) instead of 45 (`UserException`)
**File**: `rust/sele4n-hal/src/trap.rs`, lines 176-185
**Type**: Atomic fix

The Lean `ExceptionModel.lean` (lines 175-177) maps `pcAlignment`,
`spAlignment`, and `unknownReason` to `.error .userException`. The Rust
`KernelError` enum assigns `UserException = 45` (error.rs:77). The trap
handler currently hardcodes 43 for both cases.

**Atomic steps**:

1. **Read**: trap.rs lines 170-190.
2. **Fix alignment arm** (line 179): Change `frame.set_x0(43)` to
   `frame.set_x0(45)`.
3. **Fix unknown arm** (line 184): Change `frame.set_x0(43)` to
   `frame.set_x0(45)`.
4. **Add constant**: Replace bare numeric literals with
   `KernelError::UserException as u64` for maintainability. Import
   `sele4n_types::KernelError` if not already imported.
5. **Add test**: In the trap test module, add test cases verifying alignment
   and unknown exceptions return discriminant 45.
6. **Build**: `cargo test -p sele4n-hal` + `cargo clippy -p sele4n-hal`

#### AI1-B: Document syscall dispatch stub with TODO marker (H-04)

**Finding**: H-04 — Syscall dispatch handler is a no-op stub
**File**: `rust/sele4n-hal/src/trap.rs`, lines 159-165
**Type**: Documentation + stub improvement

The SVC handler currently returns 0 (success) unconditionally. This is a
deliberate pre-FFI stub. The fix adds a proper "not ready" error code and
documents the integration point.

**Atomic steps**:

1. **Read**: trap.rs lines 155-170.
2. **Change return value**: Replace `frame.set_x0(0)` with
   `frame.set_x0(KernelError::InvalidOperation as u64)` to signal that the
   kernel syscall path is not yet wired. This prevents userspace from
   interpreting a no-op as success.
3. **Add doc comment**: Mark the function with `// TODO(WS-V/AG10): Wire
   Lean FFI dispatch via @[extern] bridge` and reference FFI.lean.
4. **Add test**: Verify SVC handler returns `InvalidOperation` discriminant.
5. **Build**: `cargo test -p sele4n-hal`

#### AI1-C: Eliminate dual timer reprogram path (M-26)

**Finding**: M-26 — Both `ffi_timer_reprogram()` (ffi.rs:40-42) and
`handle_irq()` (trap.rs:199-200) call `reprogram_timer()` +
`increment_tick_count()`. If both paths fire, ticks double-count.
**Files**: `rust/sele4n-hal/src/ffi.rs`, `rust/sele4n-hal/src/trap.rs`
**Type**: Multi-file fix

**Atomic steps**:

1. **Read**: ffi.rs lines 35-50, trap.rs lines 190-210.
2. **Designate canonical path**: The FFI path (`ffi_timer_reprogram`) is the
   Lean-controlled path and should be the sole reprogram + tick increment
   site. The IRQ handler path should only acknowledge the interrupt and
   defer tick management to the FFI layer.
3. **Fix trap.rs**: In `handle_irq()`, remove the `increment_tick_count()`
   call. Keep `reprogram_timer()` as a hardware-level timer re-arm only
   (no tick accounting). Add comment: "Tick accounting is performed by the
   Lean kernel via `ffi_timer_reprogram` — IRQ handler only re-arms the
   hardware timer."
4. **Fix ffi.rs**: Add comment documenting this as the canonical tick
   accounting path.
5. **Add test**: Verify that `handle_irq` does not increment tick count.
6. **Build**: `cargo test -p sele4n-hal` + `cargo clippy -p sele4n-hal`

#### AI1-D: Make BOOT_UART safe with synchronization (M-27)

**Finding**: M-27 — `pub static mut BOOT_UART` with no synchronization
**File**: `rust/sele4n-hal/src/uart.rs`, line 179
**Type**: Atomic fix

**Atomic steps**:

1. **Read**: uart.rs lines 170-230.
2. **Replace `static mut`**: Change from `pub static mut BOOT_UART` to a
   `static BOOT_UART: SpinLock<Option<Uart>>` pattern using a minimal
   spinlock (or `core::sync::atomic` flag + unsafe block with documented
   single-writer invariant). If a `SpinLock` type already exists in the
   crate, use it. Otherwise, use the lightweight pattern:
   ```rust
   use core::sync::atomic::{AtomicBool, Ordering};
   static BOOT_UART_LOCK: AtomicBool = AtomicBool::new(false);
   static mut BOOT_UART_INNER: Option<Uart> = None;
   ```
3. **Update `kprint!` macro**: Modify line 220 to acquire the lock before
   accessing the UART.
4. **Restrict visibility**: Change from `pub` to `pub(crate)` to limit the
   blast radius.
5. **Build**: `cargo test -p sele4n-hal` + `cargo clippy -p sele4n-hal`

#### AI1-E: Phase AI1 gate verification

**Type**: Gate

1. `cargo test --workspace` (all 362+ tests pass)
2. `cargo clippy --workspace` (0 warnings)
3. Verify discriminant alignment: spot-check that trap.rs error codes
   match `sele4n-types` KernelError enum values.

---

## 4. Phase AI2 — Interrupt & Architecture Safety (H-03, M-14, M-15, M-20)

**Objective**: Fix the missing EOI on interrupt error, address shadow/HW
divergence in VSpaceARMv8, add TLB flush enforcement for ASID reuse, and
tighten the `suspendThread` metadata consistency window. These are all
architecture-layer issues that affect correctness on hardware.

**Dependencies**: None (Lean-only, independent of AI1).

**Gate**: `source ~/.elan/env && lake build` + `./scripts/test_smoke.sh`

### 4.1 Sub-tasks

#### AI2-A: Add EOI on interrupt dispatch error path (H-03)

**Finding**: H-03 — Missing EOI on interrupt handle error in
`interruptDispatchSequence`
**File**: `SeLe4n/Kernel/Architecture/InterruptDispatch.lean`, lines 127-134
**Type**: Atomic fix

The success path (line 133) calls `endOfInterrupt st' intId`. The error path
(line 134) returns `.error e` without EOI. On real hardware, this would leave
the interrupt active in the GIC, making the kernel deaf to that IRQ line.

**Atomic steps**:

1. **Read**: InterruptDispatch.lean lines 120-140.
2. **Fix error path**: Change line 134 from:
   ```lean
   | .error e => .error e
   ```
   to:
   ```lean
   | .error _ => .ok ((), endOfInterrupt st intId)
   ```
   **Design decision**: EOI must always fire regardless of handler outcome
   to prevent GIC lockup. Since `Except` discards state on error, and EOI
   is a state update, we return `.ok` with the EOI-updated state. Handler
   errors are non-fatal — the interrupt was acknowledged. This matches
   Linux's unconditional EOI pattern.

3. **Update comment**: Replace lines 104-105 acknowledging the bug with:
   "EOI is always sent regardless of handler outcome to prevent GIC lockup."
4. **Build module**: `lake build SeLe4n.Kernel.Architecture.InterruptDispatch`

#### AI2-B: Surface error on VSpaceARMv8 `unmapPage` HW walk failure (M-14)

**Finding**: M-14 — `unmapPage` silently succeeds when hardware walk fails
**File**: `SeLe4n/Kernel/Architecture/VSpaceARMv8.lean`, lines 189-206
**Type**: Multi-step fix

The current implementation updates shadow state even when `readDescriptor`
returns a non-table entry (indicating the HW walk failed to reach the target
level). This can cause shadow/HW divergence.

**Atomic steps**:

1. **Read**: VSpaceARMv8.lean lines 180-210.
2. **Change return type**: Change `unmapPage` return from `Option ARMv8VSpace`
   to `Except VSpaceError ARMv8VSpace` (or use the existing error type).
3. **Add error on walk failure**: When `readDescriptor` returns a non-table
   entry at intermediate levels (L1, L2), return `.error .walkFailed` instead
   of silently proceeding with shadow-only update.
4. **Preserve shadow-only update on L3 success**: The final level (L3) should
   still update the shadow when the descriptor matches.
5. **Update callers**: Check if any caller of `unmapPage` needs to handle
   the new error type.
6. **Update preservation theorems**: Any VSpaceARMv8 theorem referencing
   `unmapPage` may need `Except` unwrapping.
7. **Build module**: `lake build SeLe4n.Kernel.Architecture.VSpaceARMv8`

#### AI2-C: Add type-level TLB flush witness for ASID reuse (M-15)

**Finding**: M-15 — ASID reuse path has no type-level TLB flush enforcement
**File**: `SeLe4n/Kernel/Architecture/AsidManager.lean`, lines 80-115
**Type**: Multi-step fix

Currently, `AsidAllocResult` has a boolean `requiresFlush` field. Callers
must manually check this flag and perform a TLB flush, but nothing in the
type system enforces it.

**Atomic steps**:

1. **Read**: AsidManager.lean lines 75-120.
2. **Add proof witness to allocation result**: Change `AsidAllocResult` to
   carry a proof obligation:
   ```lean
   structure AsidAllocResult where
     asid : AsidEntry
     flushPerformed : Bool
     -- When reusing an ASID, caller must provide evidence of TLB flush
     flushRequired : Bool := false
   ```
   **Alternative (stronger)**: Use a dependent type:
   ```lean
   structure AsidAllocResult (flushed : Prop) where
     asid : AsidEntry
     flushWitness : flushed ∨ ¬requiresFlush
   ```
   The simpler boolean approach is recommended for this phase. The dependent
   type approach can be pursued in WS-V when the TLB model is fully
   integrated.
3. **Add flush documentation**: Add comment at the reuse path (line 91-96)
   documenting the flush obligation and referencing TlbModel's
   `tlbFlushByAsid` for the required operation.
4. **Add assertion helper**: Create `asidAllocRequiresFlush` predicate that
   callers can use in proofs to verify flush was performed.
5. **Build module**: `lake build SeLe4n.Kernel.Architecture.AsidManager`

#### AI2-D: Document `suspendThread` transient inconsistency window (M-20)

**Finding**: M-20 — `suspendThread` has a transient metadata inconsistency
during donation return
**File**: `SeLe4n/Kernel/Lifecycle/Suspend.lean`, lines 150-169
**Type**: Documentation + defensive assertion

This is safe in the sequential model (no concurrent access during the
transient window). The concern is relevant for hardware binding.

**Atomic steps**:

1. **Read**: Suspend.lean lines 145-175.
2. **Add atomicity comment**: Document the transient window between
   `cancelIpcBlocking` (line 161) and the TCB re-lookup (line 169). Note
   that in the sequential model, no other operation can observe the
   intermediate state.
3. **Add defensive assertion**: After the re-lookup, assert that the
   `schedContextBinding` field is consistent with the expected post-cleanup
   state. This catches any future refactoring that breaks the assumption.
4. **Add H3 annotation**: Mark with `-- H3-ATOMICITY: This sequence must
   execute atomically on hardware (interrupts disabled)` to flag the
   hardware binding requirement.
5. **Build module**: `lake build SeLe4n.Kernel.Lifecycle.Suspend`

#### AI2-E: Phase AI2 gate verification

**Type**: Gate

1. `source ~/.elan/env && lake build` (256 jobs)
2. `./scripts/test_smoke.sh`
3. Verify: `lake build SeLe4n.Kernel.Architecture.InterruptDispatch`
4. Verify: `lake build SeLe4n.Kernel.Architecture.VSpaceARMv8`
5. Verify: `lake build SeLe4n.Kernel.Architecture.AsidManager`

---

## 5. Phase AI3 — Scheduler & PIP Correctness (M-04, M-22, L-09, L-10)

**Objective**: Fix priority inheritance consistency in `handleYield` and
`migrateRunQueueBucket` by using the established `resolveInsertPriority`
helper. Also tighten `saveOutgoingContext` and `configDefaultTimeSlice`.

**Dependencies**: None (independent of AI1 and AI2).

**Gate**: `source ~/.elan/env && lake build` + `./scripts/test_smoke.sh`

### 5.1 Sub-tasks

#### AI3-A: Use effective priority in `handleYield` (M-04)

**Finding**: M-04 — `handleYield` re-enqueues at base priority
**File**: `SeLe4n/Kernel/Scheduler/Operations/Core.lean`, line 341
**Type**: Multi-step fix

Currently: `st.scheduler.runQueue.insert tid tcb.priority` uses `tcb.priority`
(static base). The `resolveInsertPriority` helper (Selection.lean:345-349)
already computes effective priority (max of base and PIP boost) and is used
at 5 other insertion sites.

**Atomic steps**:

1. **Read**: Core.lean lines 315-345, Selection.lean lines 340-355.
2. **Replace priority source**: Change line 341 from:
   ```lean
   let rq' := (st.scheduler.runQueue.insert tid tcb.priority).rotateToBack tid
   ```
   to:
   ```lean
   let effectivePrio := (resolveEffectivePrioDeadline st tcb).1
   let rq' := (st.scheduler.runQueue.insert tid effectivePrio).rotateToBack tid
   ```
   This requires `resolveEffectivePrioDeadline` to be accessible. It is
   defined in `Selection.lean` which is imported by `Core.lean` via
   `Operations.lean`.
3. **Update comment**: Replace the "intentional" comment (lines 332-340)
   with: "Re-enqueues at effective priority (max of base priority and PIP
   boost). This ensures PIP-boosted threads maintain their elevated priority
   band after yield, preventing priority inversion."
4. **Update preservation theorem**: `handleYield_scheduler_eq` or any
   theorem that depends on the specific priority used for insertion may need
   adjustment. Check `Preservation.lean` for `handleYield` references.
5. **Build module**: `lake build SeLe4n.Kernel.Scheduler.Operations.Core`
6. **Build preservation**: `lake build SeLe4n.Kernel.Scheduler.Operations.Preservation`

#### AI3-B: Use effective priority in `migrateRunQueueBucket` (M-22)

**Finding**: M-22 — `migrateRunQueueBucket` ignores PIP boost
**File**: `SeLe4n/Kernel/SchedContext/PriorityManagement.lean`, lines 99-108
**Type**: Multi-step fix

Currently: `rq.insert tid newPriority` uses the raw `newPriority` argument
without considering PIP boost.

**Atomic steps**:

1. **Read**: PriorityManagement.lean lines 90-115.
2. **Add state parameter**: `migrateRunQueueBucket` currently takes only
   the RunQueue, tid, and newPriority. Add a `st : SystemState` parameter
   (or the TCB directly) to access `pipBoost`.
3. **Compute effective priority**:
   ```lean
   let effectivePrio := max newPriority (tcb.pipBoost.getD 0)
   let rq := rq.insert tid effectivePrio
   ```
   Or use `resolveInsertPriority st tid sc` if a SchedContext is available.
4. **Update callers**: `setPriorityOp` and `setMCPriorityOp` call
   `migrateRunQueueBucket`. They must pass the additional state parameter.
5. **Update preservation theorems**: Check
   `PriorityPreservation.lean` for `migrateRunQueueBucket` references.
6. **Build**: `lake build SeLe4n.Kernel.SchedContext.PriorityManagement`
7. **Build**: `lake build SeLe4n.Kernel.SchedContext.Invariant.PriorityPreservation`

#### AI3-C: Add `Except` return to `saveOutgoingContext` (L-09)

**Finding**: L-09 — `saveOutgoingContext` silently returns state on TCB miss
**File**: `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`, lines 478-486
**Type**: Atomic fix

The function returns the unchanged state when TCB lookup fails. The comment
documents this as "unreachable under currentThreadValid invariant," but
silent failure hides invariant violations during development.

**Atomic steps**:

1. **Read**: Selection.lean lines 472-490.
2. **Change return type**: From `SystemState` to `Except KernelError SystemState`.
3. **Return error on miss**: Replace the silent `st` return with
   `.error .invalidThread` on TCB lookup failure.
4. **Update callers**: `saveOutgoingContext` is called from context switch
   paths. Update callers to propagate or handle the error.
5. **Build**: `lake build SeLe4n.Kernel.Scheduler.Operations.Selection`

#### AI3-D: Enforce `configDefaultTimeSlice` positivity (L-10)

**Finding**: L-10 — `configDefaultTimeSlice` positivity not enforced
**File**: `SeLe4n/Kernel/Scheduler/Operations/Core.lean` or
`SeLe4n/Model/Object/Types.lean` (wherever the config field is defined)
**Type**: Atomic fix

A zero time slice would cause immediate timer expiry on every schedule,
effectively preventing any thread from executing.

**Atomic steps**:

1. **Find definition**: Search for `configDefaultTimeSlice` to locate its
   type declaration.
2. **Add guard**: Either:
   - Change the type from `Nat` to `Nat` with a runtime check at
     assignment (e.g., `if ts == 0 then defaultTimeSlice else ts`), or
   - Use `Pos` type (requires more invasive changes), or
   - Add a `configDefaultTimeSlice_pos` theorem stating `0 < configDefaultTimeSlice`
     as an invariant predicate.
3. **Recommended approach**: Add a runtime guard at the single assignment
   point, plus a documentation comment noting the positivity requirement.
4. **Build**: Build the module containing the definition.

#### AI3-E: Phase AI3 gate verification

**Type**: Gate

1. `source ~/.elan/env && lake build` (256 jobs)
2. `./scripts/test_smoke.sh`
3. Verify: `lake build SeLe4n.Kernel.Scheduler.Operations.Core`
4. Verify: `lake build SeLe4n.Kernel.SchedContext.PriorityManagement`

---

## 6. Phase AI4 — IPC & SchedContext Hardening (M-01, M-09, L-05)

**Objective**: Wire `cleanupPreReceiveDonation` into the production receive
path to prevent SchedContext leaks, improve DTB parser fuel exhaustion
reporting, and clean up the unused parameter in `timeoutAwareReceive`.

**Dependencies**: None (independent of AI1–AI3).

**Gate**: `source ~/.elan/env && lake build` + `./scripts/test_smoke.sh`

### 6.1 Sub-tasks

#### AI4-A: Wire `cleanupPreReceiveDonation` into production receive (M-01)

**Finding**: M-01 — `cleanupPreReceiveDonation` tested but never called
from production API dispatch
**Files**: `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` (insertion point),
`SeLe4n/Kernel/API.lean` (dispatch verification)
**Type**: Multi-step fix

The abnormal path: a server does `.receive` without replying to a prior
`.call`. The donated SchedContext from the prior call remains bound to the
server. `cleanupPreReceiveDonation` checks for this condition and returns
the SchedContext to the original owner.

**Insertion point**: The pure receive path in `endpointReceiveDual`
(Transport.lean), specifically the branch where no sender is waiting and
the receiver is about to block. This is the exact point where the server
transitions from "processing a prior call" to "waiting for a new message."

**Atomic steps**:

1. **Read**: Transport.lean — find the `endpointReceiveDual` function and
   locate the "no sender waiting" branch where the receiver is enqueued.
2. **Insert cleanup**: Before the receiver is enqueued into the wait queue,
   call `cleanupPreReceiveDonation`:
   ```lean
   -- AI4-A (M-01): Clean up any donated SchedContext from a prior
   -- unanswered call before blocking on receive.
   let st_cleaned := cleanupPreReceiveDonation st receiver
   ```
   Then use `st_cleaned` instead of `st` for the subsequent enqueue
   operation.
3. **Verify import**: Confirm `cleanupPreReceiveDonation` is accessible.
   It is defined in `Donation.lean`. Check if Transport.lean imports the
   Donation module (directly or transitively via the IPC Operations hub).
   If not, add the import.
4. **Update preservation theorems**: Any theorem about `endpointReceiveDual`
   that tracks state equality may need to account for the cleanup step.
   Check `EndpointPreservation.lean` and `Structural.lean` for relevant
   theorems.
5. **Build**:
   ```bash
   lake build SeLe4n.Kernel.IPC.DualQueue.Transport
   lake build SeLe4n.Kernel.IPC.Invariant.EndpointPreservation
   ```

#### AI4-B: Surface DTB parser fuel exhaustion as distinct error (M-09)

**Finding**: M-09 — DTB parser fuel=2000 silently drops peripherals
**File**: `SeLe4n/Platform/DeviceTree.lean`, lines 619-627
**Type**: Atomic fix

The parser returns `none` on fuel exhaustion, which is indistinguishable
from "no valid DTB" or "parse error." Callers cannot tell if peripherals
were silently dropped.

**Atomic steps**:

1. **Read**: DeviceTree.lean lines 610-635.
2. **Change return type**: The parsing function currently returns
   `Option DeviceTree`. Change to `Except DeviceTreeError DeviceTree` where:
   ```lean
   inductive DeviceTreeError where
     | fuelExhausted : DeviceTreeError
     | malformedBlob : DeviceTreeError
     | emptyTree : DeviceTreeError
   ```
   Or, if adding a new error type is too invasive, change the fuel-exhaustion
   path to return a specific sentinel that callers can distinguish:
   ```lean
   | 0 => .error .fuelExhausted  -- was: none
   ```
3. **Update callers**: Check all callers of the parsing function. The main
   caller is `bootFromPlatform` which should log or propagate the fuel
   exhaustion warning.
4. **Consider increasing fuel**: 2000 may be insufficient for complex DTBs.
   Document the fuel value as a function of expected DTB complexity and
   add a comment noting the RPi5 DTB is well under 2000 nodes.
5. **Build**: `lake build SeLe4n.Platform.DeviceTree`

#### AI4-C: Remove unused `_endpointId` parameter from `timeoutAwareReceive` (L-05)

**Finding**: L-05 — `timeoutAwareReceive` has unused `_endpointId` parameter
**File**: `SeLe4n/Kernel/IPC/Operations/Timeout.lean`, lines 114-115
**Type**: Atomic fix

The underscore prefix explicitly marks this as unused. The comment "reserved
for future validation" has been present since the function was created.
Since no future validation has materialized across multiple workstreams,
remove the parameter to clean up the API surface.

**Atomic steps**:

1. **Read**: Timeout.lean lines 110-120.
2. **Remove parameter**: Delete `(_endpointId : SeLe4n.ObjId)` from the
   function signature.
3. **Update callers**: Search for all call sites of `timeoutAwareReceive`
   and remove the endpoint ID argument. Expected callers: API.lean dispatch
   paths and test suites.
4. **Update theorems**: Any theorem referencing `timeoutAwareReceive` in its
   statement must have the parameter removed from the universally quantified
   variables.
5. **Build**: `lake build SeLe4n.Kernel.IPC.Operations.Timeout`
6. **Build callers**: `lake build SeLe4n.Kernel.API`

#### AI4-D: Phase AI4 gate verification

**Type**: Gate

1. `source ~/.elan/env && lake build` (256 jobs)
2. `./scripts/test_smoke.sh`
3. Verify: `lake build SeLe4n.Kernel.IPC.DualQueue.Transport`
4. Verify: `lake build SeLe4n.Platform.DeviceTree`
5. Verify: `lake build SeLe4n.Kernel.IPC.Operations.Timeout`

---

## 7. Phase AI5 — Platform & Simulation Safety (H-01, H-02, M-19)

**Objective**: Replace the vacuously-true simulation boot and interrupt
contracts with substantive predicates that actually validate boot invariants
and IRQ ranges. Add a runtime guard for the insecure `defaultLabelingContext`.

**Dependencies**: None (independent of AI1–AI4).

**Gate**: `source ~/.elan/env && lake build` + `./scripts/test_smoke.sh`

### 7.1 Sub-tasks

#### AI5-A: Create substantive simulation boot contract (H-01)

**Finding**: H-01 — Simulation boot contract is vacuously `True` for all 4
predicates
**File**: `SeLe4n/Platform/Sim/BootContract.lean`, lines 23-36
**Type**: Multi-step fix

All 4 predicates (`objectTypeMetadataConsistent`, `capabilityRefMetadataConsistent`,
`objectStoreNonEmpty`, `irqRangeValid`) are `True`. This means simulation
tests never validate that the boot sequence produces a well-formed initial
state.

**Atomic steps**:

1. **Read**: BootContract.lean lines 20-50.
2. **Read RPi5 boot contract**: Read `RPi5/BootContract.lean` to understand
   the substantive predicate patterns used for the production platform.
3. **Replace predicates**: Change from `True` to substantive checks that
   mirror the RPi5 contract structure:
   ```lean
   def simBootContract : BootContract where
     objectTypeMetadataConsistent := fun st =>
       -- Every object in the store has a valid type discriminant
       st.objects.values.all (fun obj => obj.isWellTyped)
     capabilityRefMetadataConsistent := fun st =>
       -- Every capability reference points to an existing object
       st.capabilityRefsValid
     objectStoreNonEmpty := fun st =>
       -- At least one object exists (idle thread, root CNode)
       ¬st.objects.isEmpty
     irqRangeValid := fun st =>
       -- IRQ table entries reference valid handler objects
       st.irqTable.all (fun entry => entry.handler ∈ st.objects.keys)
   ```
   **Note**: The exact predicate implementations depend on available
   decidable predicates in `State.lean` and `InvariantChecks.lean`. Use
   the `stateInvariantChecksFor` helper functions that already exist in
   `InvariantChecks.lean` as building blocks.
4. **Verify simulation tests still pass**: The existing test suites construct
   state via `buildChecked` which should satisfy these predicates. If any
   test fails, the test was relying on invalid state — fix the test.
5. **Build**: `lake build SeLe4n.Platform.Sim.BootContract`

#### AI5-B: Create substantive simulation interrupt contract (H-02)

**Finding**: H-02 — Simulation interrupt contract accepts ALL IRQs
**File**: `SeLe4n/Platform/Sim/BootContract.lean`, lines 42-48
**Type**: Multi-step fix

`irqLineSupported := fun _ => True` and `irqHandlerMapped := fun _ _ => True`
means any IRQ number is accepted, hiding validation bugs.

**Atomic steps**:

1. **Read**: BootContract.lean lines 38-50 (interrupt contract section).
2. **Define valid IRQ range**: For simulation, restrict to a bounded range
   matching the BCM2712 GIC-400 (0–223, matching `InterruptId := Fin 224`):
   ```lean
   def simInterruptContract : InterruptContract where
     irqLineSupported := fun irq => irq < 224
     irqHandlerMapped := fun irq st =>
       -- Handler is mapped if the IRQ table has an entry for this line
       st.irqTable.contains irq
   ```
3. **Update callers**: Verify `simBootAndInterruptContract` composition
   still type-checks.
4. **Update tests**: If any test deliberately sends out-of-range IRQs
   (e.g., IRQ 999), it should now get a validation error instead of silent
   acceptance. Update expectations accordingly.
5. **Build**: `lake build SeLe4n.Platform.Sim.BootContract`

#### AI5-C: Add runtime guard for `defaultLabelingContext` (M-19)

**Finding**: M-19 — `defaultLabelingContext` defeats all security
**File**: `SeLe4n/Kernel/InformationFlow/Policy.lean`, lines 215-226
**Type**: Multi-step fix

The `defaultLabelingContext` assigns `publicLabel` to all entities, which is
correct for testing but dangerous for production deployment. The codebase
already has `defaultLabelingContext_insecure` proving this is insecure.
However, there is no runtime guard preventing accidental deployment.

**Atomic steps**:

1. **Read**: Policy.lean lines 210-260.
2. **Add deployment guard predicate**: Create a function that checks whether
   a `LabelingContext` is the insecure default:
   ```lean
   def isInsecureDefaultContext (ctx : LabelingContext) : Bool :=
     -- Check if all labels are public (the signature of the insecure default)
     ctx.threadLabelOf (ThreadId.ofNat 0) == publicLabel &&
     ctx.objectLabelOf (ObjId.ofNat 0) == publicLabel
   ```
3. **Add assertion to checked dispatch**: In `dispatchWithCapChecked`
   (API.lean), add an early check:
   ```lean
   -- AI5-C (M-19): Guard against insecure default labeling context
   if isInsecureDefaultContext ctx then
     .error .insecureLabelingContext
   ```
   **Alternative (less invasive)**: Add a `LabelingContextValid` check to
   the boot sequence that logs a warning when the default context is used.
   This approach is preferred because it doesn't add runtime overhead to
   every syscall.
4. **Recommended approach**: Add the guard at boot time in
   `bootFromPlatform` or the platform contract. The `LabelingContextValid`
   predicate already exists and is documented as a "deployment requirement"
   (Composition.lean:753). Wire it into the simulation platform's boot
   validation so that tests exercising information flow must provide a
   proper labeling context.
5. **Build**: `lake build SeLe4n.Kernel.InformationFlow.Policy`

#### AI5-D: Update test suites for new contracts (H-01, H-02)

**Files**: Test suites that use `simBootContract` or `simInterruptContract`
**Type**: Multi-step test update

After AI5-A and AI5-B change the contracts from vacuous to substantive,
some test suites may need updates.

**Atomic steps**:

1. **Search**: Find all test files importing `Sim.BootContract` or
   `Sim.Contract`.
2. **Verify**: Run each affected test suite individually to identify
   failures.
3. **Fix**: For each failure, determine if:
   - The test state construction needs to be updated to satisfy the new
     contract predicates (likely: add missing objects, fix IRQ ranges)
   - The test was deliberately testing edge cases that should now fail
     (update expectations)
4. **Build + test**: Run full `test_smoke.sh`

#### AI5-E: Phase AI5 gate verification

**Type**: Gate

1. `source ~/.elan/env && lake build` (256 jobs)
2. `./scripts/test_smoke.sh`
3. Verify: `lake build SeLe4n.Platform.Sim.BootContract`
4. Verify: `lake build SeLe4n.Kernel.InformationFlow.Policy`

---

## 8. Phase AI6 — Documentation & Proof Gaps (15 documentation-only findings + L-15, L-24)

**Objective**: Systematically address all 15 documentation-only findings plus
two stale-comment fixes. This phase makes no behavioral changes — only
comments, documentation strings, and spec text are modified.

**Dependencies**: AI1–AI5 (documentation should reflect post-fix behavior).

**Gate**: `./scripts/test_full.sh` + documentation sync verification

### 8.1 Sub-tasks

#### AI6-A: Scheduler documentation batch (M-02, M-03, M-23, M-24, M-25)

**Findings**: 5 scheduler/liveness documentation items
**Type**: Documentation-only batch

All 5 findings require adding or updating documentation comments in existing
files. No behavioral changes.

| Finding | File | Action |
|---------|------|--------|
| M-02 | `API.lean:409-416` | Add spec cross-reference to `SELE4N_SPEC.md` documenting silent-drop semantics as seL4-matching. Current inline comment is sufficient; add spec section reference. |
| M-03 | `RunQueue.lean:44` | Add documentation comment: "Diagnostics-only field (AF-40). Not referenced by scheduling selection. Proof-linking to `flat.length` deferred as zero functional benefit." |
| M-23 | `BlockingGraph.lean:70-82` | Add scope note: "Fuel exhaustion returns `[]` (empty chain). PIP propagation stops at cycle → stale boosts retained (conservative, not unsound). Cycle detection deferred to WS-V." |
| M-24 | `BandExhaustion.lean:34-43` | Add scope note: "`eventuallyExits` is externalized for unbound threads. Required: external progress assumption (scheduler liveness guarantee). See WCRT.lean for integration." |
| M-25 | `WCRT.lean:167-187` | Add scope note on both hypotheses: "`hDomainActiveRunnable` and `hBandProgress` encode runtime properties (domain scheduler liveness, band exhaustion ordering). These are deployment obligations, not kernel invariants." |

**Atomic steps**:

1. Read each file at the specified lines.
2. Add or update the documentation comment as specified.
3. Verify no behavioral change: `lake build <module>` for each.

#### AI6-B: Platform & boot documentation batch (M-07, M-08, M-10, M-11)

**Findings**: 4 platform documentation items
**Type**: Documentation-only batch

| Finding | File | Action |
|---------|------|--------|
| M-07 | `Boot.lean:503-519` | Add scope note: "Proven for empty PlatformConfig only. General config bridge requires `bootSafe` predicate (deferred to WS-V hardware binding)." |
| M-08 | `DeviceTree.lean:136-140` | Update stub comment: "AF3-F: Placeholder. Use `fromDtbFull` for DTB parsing. Stub retained for backward compatibility." |
| M-10 | `MmioAdapter.lean:340-356` | Add note: "Sequential model limitation: returns `st.machine.memory addr` (RAM semantics). Real hardware volatile registers may return different values on each read. Hardware binding must substitute actual MMIO reads via FFI." |
| M-11 | `Boot.lean:947-960` | Add note: "VSpaceRoots excluded because ASID table registration is unavailable during boot. VSpaceRoot support requires AsidManager integration (deferred to WS-V)." |

#### AI6-C: Architecture documentation batch (M-13, M-16, M-17, M-18)

**Findings**: 4 architecture documentation items
**Type**: Documentation-only batch

| Finding | File | Action |
|---------|------|--------|
| M-13 | `VSpace.lean:50-61` | Add note: "`physicalAddressBound` (2^52) is proof-layer default only. Production dispatch uses `physicalAddressBoundForConfig` via `st.machine.physicalAddressWidth`. Internal helpers do not need platform-specific bounds." |
| M-16 | `CacheModel.lean:275-287` | Add note: "D-cache → I-cache pipeline ordering gap: the sequential model does not capture the hardware requirement that D-cache writeback must complete before I-cache refetch for self-modifying code. Hardware binding must insert DC CVAU + DSB ISH + IC IVAU + DSB ISH + ISB sequence." |
| M-17 | `Adapter.lean:136-140` | Add note: "Context switch does not model TLB/ASID maintenance. ASID switching is performed by VSpace operations (VSpaceBackend.lean) independently. Atomic TLB+ASID+context switch coordination deferred to WS-V." |
| M-18 | `Adapter.lean` or `Invariant.lean` | Add note: "Cross-module composition gap: per-subsystem invariant preservation is proven independently (TLB consistency, cache coherency, page table WF). Relational composition theorem (proving TLB + cache + page table maintain simultaneous coherency through compound operations) deferred to WS-V." |

#### AI6-D: Model & capability documentation batch (M-21, L-02)

**Findings**: 2 model-layer documentation items
**Type**: Documentation-only batch

| Finding | File | Action |
|---------|------|--------|
| M-21 | `Structures.lean:2234-2246` | Verify existing scope note is sufficient. Add cross-reference: "See TPI-DOC for full fuel sufficiency formal bridge (deferred to WS-V). Current proof covers direct children (depth 1) only. `edgeWellFounded` provides the inductive foundation for the full proof." |
| L-02 | `State.lean:344` | Add note: "`allTablesInvExtK` 17-deep tuple projection is structurally fragile but stable under the current invariant bundle. Named extractors (Builder.lean:30-116) provide maintainable access. See AF-26 for design rationale." |

#### AI6-E: Fix stale documentation references (L-15, L-24)

**Findings**: 2 stale-comment fixes
**Type**: Comment correction

| Finding | File | Action |
|---------|------|--------|
| L-15 | `BlockingGraph.lean:67` | Fix stale reference to `maxBlockingDepth (= 32)`. Replace with reference to actual bound: `blockingDepthBound` theorem which bounds chain length by `st.objectIndex.length`. |
| L-24 | `RPi5/RuntimeContract.lean:28-31` | Replace "H3-prep stub" with: "Substantive runtime contract implementing 6-condition register consistency, dequeue readiness, time-slice, IPC readiness, EDF, and budget validation." |

#### AI6-F: SELE4N_SPEC.md documentation sync

**File**: `docs/spec/SELE4N_SPEC.md`
**Type**: Documentation sync

Add or update the following sections to reflect audit findings:

1. **Silent-drop semantics** (M-02): Add section documenting `resolveExtraCaps`
   seL4-matching behavior in the IPC chapter.
2. **Boot invariant scope** (M-07): Note limitation in the boot chapter.
3. **MMIO model limitations** (M-10): Add to platform chapter.
4. **Externalized hypotheses** (M-24, M-25): Add to liveness/WCRT chapter.

#### AI6-G: Phase AI6 gate verification

**Type**: Gate

1. `./scripts/test_full.sh`
2. Verify no `sorry` or `axiom` introduced.
3. Verify all modified files build: `lake build` (256 jobs).
4. Verify documentation sync: check `SELE4N_SPEC.md`, `DEVELOPMENT.md`,
   and `CLAIM_EVIDENCE_INDEX.md` for consistency.

---

## 9. Phase AI7 — Testing, Closure & Final Gate (L-17, L-26 + fixture sync)

**Objective**: Address remaining actionable LOW findings, run full regression
suite, verify fixture alignment, update version references, and perform
final closure.

**Dependencies**: AI1–AI6 (all code and documentation changes complete).

**Gate**: `./scripts/test_full.sh` + `cargo test --workspace` + version sync

### 9.1 Sub-tasks

#### AI7-A: Document CBS admission truncation tolerance (L-17)

**Finding**: L-17 — CBS admission ~6.4% over-admission from integer truncation
**File**: `SeLe4n/Kernel/SchedContext/Budget.lean`, lines 204-217
**Type**: Documentation + optional guard

The integer division `budget * 1000 / period` can over-admit by up to 1/16
(6.25%) per context. The aggregate error scales with context count.

**Atomic steps**:

1. **Read**: Budget.lean lines 200-220.
2. **Add precision documentation**: Document the truncation bound formally:
   "Per-context admission error ≤ `period / 1000` time units. Aggregate
   over-admission ≤ `n * period / 1000` where `n` is the number of
   admitted contexts. For RPi5 at 54 MHz with typical periods (1-100ms),
   this is negligible."
3. **Optional**: Add a rounding-up guard (`(budget * 1000 + period - 1) / period`)
   to eliminate under-counting. This is a pure improvement with no
   semantic change to admission policy.
4. **Build**: `lake build SeLe4n.Kernel.SchedContext.Budget`

#### AI7-B: Restrict `lifecycleRetypeObject` visibility (L-26)

**Finding**: L-26 — `lifecycleRetypeObject` is public despite internal intent
**File**: `SeLe4n/Kernel/Lifecycle/Operations.lean`, lines 460-469
**Type**: Atomic fix

**Atomic steps**:

1. **Read**: Operations.lean lines 455-475.
2. **Check proof dependencies**: Search for external references to
   `lifecycleRetypeObject`. If only used within the Lifecycle module and
   by proofs in `Invariant/`, it can be marked `protected`.
3. **Apply visibility**: Change `def lifecycleRetypeObject` to
   `protected def lifecycleRetypeObject` (or `private` if no cross-file
   usage exists).
4. **Build**: `lake build SeLe4n.Kernel.Lifecycle.Operations`
5. **If build fails**: Some proof files outside the Lifecycle namespace may
   reference this function. In that case, keep it `protected` and add a
   comment: "-- Public for proof accessibility. Not part of the kernel API."

#### AI7-C: Update test fixtures

**Type**: Fixture verification

After all code changes in AI1–AI5, the main trace harness output may have
changed.

**Atomic steps**:

1. **Run trace harness**: `source ~/.elan/env && lake exe sele4n > /tmp/trace_output.txt 2>&1`
2. **Diff against fixture**: `diff /tmp/trace_output.txt tests/fixtures/main_trace_smoke.expected`
3. **If changed**: Update the fixture file with a header comment noting
   which phase(s) caused the change.
4. **Run smoke test**: `./scripts/test_smoke.sh`

#### AI7-D: Version bump and sync

**Type**: Version management

Bump version from `0.27.6` to `0.28.0` (new minor version for workstream
completion).

**Atomic steps**:

1. **Update `lakefile.toml`**: version field.
2. **Update `rust/Cargo.toml`**: workspace version field.
3. **Update `KERNEL_VERSION`**: in `rust/sele4n-hal/src/boot.rs`.
4. **Update CLAUDE.md**: version references.
5. **Update README badges**: all 10 i18n READMEs.
6. **Run version sync check**: `./scripts/check_version_sync.sh`

#### AI7-E: WORKSTREAM_HISTORY.md and CHANGELOG.md updates

**Type**: Documentation closure

**Atomic steps**:

1. **Add WS-AI entry to WORKSTREAM_HISTORY.md**: Following the established
   format, add entry for WS-AI with all 7 phases, sub-task counts, key
   findings addressed, and completion status.
2. **Add CHANGELOG.md entry**: Document all behavioral changes by phase.
3. **Update CLAUDE.md**: Add WS-AI to the active workstream context section.

#### AI7-F: Final gate verification

**Type**: Gate (comprehensive)

1. `source ~/.elan/env && lake build` (256 jobs, clean build)
2. `./scripts/test_full.sh` (Tier 0–3)
3. `cargo test --workspace` (362+ tests)
4. `cargo clippy --workspace` (0 warnings)
5. `./scripts/check_version_sync.sh`
6. Verify zero `sorry` / `axiom`: `grep -r "sorry\|axiom " SeLe4n/ --include="*.lean" | grep -v "^--" | wc -l` = 0
7. Verify fixture match: `diff <(lake exe sele4n 2>&1) tests/fixtures/main_trace_smoke.expected`

---

## 10. Dependency Graph and Execution Order

### 10.1 Phase Dependencies

```
AI1 (Rust ABI)    ──────────────────────────────────────┐
AI2 (Architecture) ─────────────────────────────────────┤
AI3 (Scheduler)    ─────────────────────────────────────┤
AI4 (IPC)          ─────────────────────────────────────┼──▶ AI6 (Documentation) ──▶ AI7 (Closure)
AI5 (Platform)     ─────────────────────────────────────┘
```

**Parallelism opportunities**: AI1–AI5 are fully independent and can
execute in parallel. AI1 is Rust-only; AI2–AI5 are Lean-only with no
file overlap. AI6 depends on all code phases completing (documentation
must reflect post-fix behavior). AI7 is sequential after AI6.

### 10.2 File Modification Overlap Analysis

| Phase | Primary Files | Overlap Risk |
|-------|--------------|--------------|
| AI1 | `rust/sele4n-hal/src/{trap,ffi,uart}.rs` | None (Rust only) |
| AI2 | `InterruptDispatch.lean`, `VSpaceARMv8.lean`, `AsidManager.lean`, `Suspend.lean` | None (architecture modules, disjoint from AI3–AI5) |
| AI3 | `Core.lean`, `Selection.lean`, `PriorityManagement.lean` | None (scheduler modules, disjoint from AI2/AI4/AI5) |
| AI4 | `Transport.lean`, `DeviceTree.lean`, `Timeout.lean` | None (IPC + platform parser, disjoint from AI2/AI3/AI5) |
| AI5 | `BootContract.lean`, `Policy.lean` | None (platform contracts, disjoint from AI2–AI4) |
| AI6 | Multiple (doc-only changes) | Low (comments only, no behavioral overlap) |
| AI7 | Fixtures, version files, history | Low (metadata only) |

**Conclusion**: AI1–AI5 have zero file overlap and can safely run in
parallel. The strict partition means no merge conflicts between phases.

### 10.3 Estimated Scope per Phase

| Phase | New/Modified Lines | Files Touched | Complexity |
|-------|-------------------|---------------|------------|
| AI1 | ~120 Rust | 3-4 | Medium (unsafe code, synchronization) |
| AI2 | ~80 Lean | 4 | Medium (Except type changes, theorem updates) |
| AI3 | ~100 Lean | 3-4 | Medium (PIP-aware insertion, preservation theorems) |
| AI4 | ~90 Lean | 3-4 | Medium (production path change, import wiring) |
| AI5 | ~80 Lean | 2-3 | Medium (substantive predicate design) |
| AI6 | ~250 documentation | 15-20 | Low (comments and spec text only) |
| AI7 | ~80 mixed | 8-12 | Low (fixture sync, version bump) |

---

## 11. Risk Assessment

### 11.1 High-Risk Sub-tasks

| Sub-task | Risk | Mitigation |
|----------|------|------------|
| AI1-D (UART sync) | Changing `static mut` to synchronized access may break bare-metal boot sequence if lock is not available at early init. | Use a two-phase pattern: raw access during pre-interrupt boot, locked access after GIC init. Test boot sequence in QEMU. |
| AI2-A (EOI fix) | Changing error semantics of `interruptDispatchSequence` may break preservation theorems that depend on the error path not modifying state. | Read all theorems referencing `interruptDispatchSequence` before modifying. The recommended fix (EOI + return success) avoids state-on-error issues. |
| AI3-A (handleYield PIP) | Changing insertion priority may break the `handleYield` preservation theorem and any theorem that assumes base-priority insertion. | Check `Preservation.lean` for all `handleYield` references. The fix pattern matches 5 existing sites that use `resolveInsertPriority`, so the preservation proof structure is established. |
| AI4-A (cleanupPreReceive) | Inserting a cleanup call into `endpointReceiveDual` changes the state transition semantics. All 15 IPC invariant conjuncts must still be preserved. | The cleanup function (`cleanupPreReceiveDonation`) is already tested. Run `test_full.sh` after this change. Check `EndpointPreservation.lean` and `Structural.lean`. |
| AI5-A (boot contract) | Substantive predicates may cause existing test suites to fail if test state construction doesn't satisfy the new invariants. | Design predicates conservatively. Use `buildChecked` as the reference — any state it produces should satisfy the new contracts. |

### 11.2 Low-Risk Sub-tasks

All documentation-only changes (AI6-A through AI6-F) and metadata changes
(AI7-D, AI7-E) are low risk. They do not affect behavior, proofs, or
compilation. The primary risk is documentation drift, mitigated by the
`test_full.sh` gate which checks documentation anchors.

---

## 12. Appendix A — Complete Finding Disposition Matrix

| ID | Severity | Disposition | Phase | Rationale |
|----|----------|-------------|-------|-----------|
| H-01 | HIGH | Actionable | AI5 | Sim boot contract vacuously True |
| H-02 | HIGH | Actionable | AI5 | Sim interrupt contract accepts all IRQs |
| H-03 | HIGH | Actionable | AI2 | Missing EOI on interrupt error |
| H-04 | HIGH | Actionable | AI1 | Syscall dispatch stub returns success |
| H-05 | HIGH | Actionable | AI1 | Wrong exception error codes (43 vs 45) |
| M-01 | MEDIUM | Actionable | AI4 | cleanupPreReceiveDonation not wired |
| M-02 | MEDIUM | Doc-only | AI6 | resolveExtraCaps seL4-matching silent drop |
| M-03 | MEDIUM | Doc-only | AI6 | RunQueue.size diagnostics-only |
| M-04 | MEDIUM | Actionable | AI3 | handleYield base priority |
| M-05 | MEDIUM | **Erroneous** | — | Already fixed in AG1-B; errors are collected |
| M-06 | MEDIUM | No-action | — | FFI.lean correctly disconnected pre-hardware |
| M-07 | MEDIUM | Doc-only | AI6 | Boot bridge empty-config scope |
| M-08 | MEDIUM | Doc-only | AI6 | fromDtb stub status |
| M-09 | MEDIUM | Actionable | AI4 | DTB parser silent fuel exhaustion |
| M-10 | MEDIUM | Doc-only | AI6 | MMIO read RAM semantics |
| M-11 | MEDIUM | Doc-only | AI6 | bootSafeObject VSpaceRoot exclusion |
| M-12 | MEDIUM | **Erroneous** | — | Deliberate design (U-M25 documented) |
| M-13 | MEDIUM | Doc-only | AI6 | PA bound 2^52 proof-layer default |
| M-14 | MEDIUM | Actionable | AI2 | unmapPage silent HW walk failure |
| M-15 | MEDIUM | Actionable | AI2 | ASID reuse no flush enforcement |
| M-16 | MEDIUM | Doc-only | AI6 | D-cache/I-cache pipeline gap |
| M-17 | MEDIUM | Doc-only | AI6 | Context switch TLB/ASID gap |
| M-18 | MEDIUM | Doc-only | AI6 | No cross-module composition theorem |
| M-19 | MEDIUM | Actionable | AI5 | defaultLabelingContext insecure |
| M-20 | MEDIUM | Actionable | AI2 | suspendThread transient inconsistency |
| M-21 | MEDIUM | Doc-only | AI6 | descendantsOf depth-1 scope |
| M-22 | MEDIUM | Actionable | AI3 | migrateRunQueueBucket ignores PIP |
| M-23 | MEDIUM | Doc-only | AI6 | blockingChain fuel truncation |
| M-24 | MEDIUM | Doc-only | AI6 | eventuallyExits externalized |
| M-25 | MEDIUM | Doc-only | AI6 | WCRT externalized hypotheses |
| M-26 | MEDIUM | Actionable | AI1 | Dual timer reprogram |
| M-27 | MEDIUM | Actionable | AI1 | BOOT_UART unsafe static |
| L-01 | LOW | No-action | — | Unbounded Nat by design |
| L-02 | LOW | Doc-only | AI6 | Tuple projection fragility documented |
| L-03 | LOW | No-action | — | LIFO seL4-compliant |
| L-04 | LOW | No-action | — | Binding check present (AUD-3b) |
| L-05 | LOW | Actionable | AI4 | Unused _endpointId parameter |
| L-06 | LOW | **Erroneous** | — | Acyclicity not externalized |
| L-07 | LOW | No-action | — | Full-list materialization correct |
| L-08 | LOW | No-action | — | Badge freedom matches seL4 |
| L-09 | LOW | Actionable | AI3 | saveOutgoingContext silent failure |
| L-10 | LOW | Actionable | AI3 | configDefaultTimeSlice no positivity |
| L-11 | LOW | No-action | — | Not a silent no-op |
| L-12 | LOW | No-action | — | Oldest-first truncation correct |
| L-13 | LOW | **Erroneous** | — | Thread state IS checked |
| L-14 | LOW | No-action | — | Object count bound conservative |
| L-15 | LOW | Actionable | AI6 | Stale maxBlockingDepth reference |
| L-16 | LOW | No-action | — | 8× bound documented (AF4-F) |
| L-17 | LOW | Actionable | AI7 | CBS truncation tolerance |
| L-18 | LOW | Deferred | WS-V | Bump allocator reclamation |
| L-19 | LOW | No-action | — | BCM2712-specific correct |
| L-20 | LOW | Deferred | WS-V | Timer division guard |
| L-21 | LOW | Deferred | WS-V | Targeted TLB flush wiring |
| L-22 | LOW | No-action | — | 2-level DTB sufficient for RPi5 |
| L-23 | LOW | Deferred | WS-V | Empty config validation |
| L-24 | LOW | Actionable | AI6 | Stale "stub" comment |
| L-25 | LOW | Deferred | WS-V | pendingMessage NI bridge |
| L-26 | LOW | Actionable | AI7 | Public visibility leak |
| L-27 | LOW | Deferred | WS-V | RadixTree precondition |
| L-28 | LOW | **Erroneous** | — | StateBuilder does check invariants |

---

## 13. Appendix B — Files Modified per Phase

| Phase | Lean Files | Rust Files | Doc Files | Scripts |
|-------|-----------|------------|-----------|---------|
| AI1 | — | `trap.rs`, `ffi.rs`, `uart.rs` | — | — |
| AI2 | `InterruptDispatch.lean`, `VSpaceARMv8.lean`, `AsidManager.lean`, `Suspend.lean` | — | — | — |
| AI3 | `Core.lean`, `Selection.lean`, `PriorityManagement.lean`, `Preservation.lean`, `PriorityPreservation.lean` | — | — | — |
| AI4 | `Transport.lean`, `DeviceTree.lean`, `Timeout.lean`, `API.lean`, `EndpointPreservation.lean` | — | — | — |
| AI5 | `BootContract.lean`, `Policy.lean`, test suites | — | — | — |
| AI6 | `API.lean`†, `RunQueue.lean`†, `BlockingGraph.lean`†, `BandExhaustion.lean`†, `WCRT.lean`†, `Boot.lean`†, `DeviceTree.lean`†, `MmioAdapter.lean`†, `VSpace.lean`†, `CacheModel.lean`†, `Adapter.lean`†, `Structures.lean`†, `State.lean`†, `RuntimeContract.lean`† | — | `SELE4N_SPEC.md` | — |
| AI7 | `Budget.lean`†, `Operations.lean`, fixtures | `boot.rs`, `Cargo.toml` | `CHANGELOG.md`, `WORKSTREAM_HISTORY.md`, `CLAUDE.md`, READMEs | `check_version_sync.sh` |

† = documentation-only changes (comments, no behavioral modification)

---

## 14. Appendix C — Verification Commands Quick Reference

```bash
# Environment setup
source ~/.elan/env

# Per-module build verification
lake build SeLe4n.Kernel.Architecture.InterruptDispatch
lake build SeLe4n.Kernel.Architecture.VSpaceARMv8
lake build SeLe4n.Kernel.Architecture.AsidManager
lake build SeLe4n.Kernel.Scheduler.Operations.Core
lake build SeLe4n.Kernel.SchedContext.PriorityManagement
lake build SeLe4n.Kernel.IPC.DualQueue.Transport
lake build SeLe4n.Platform.DeviceTree
lake build SeLe4n.Kernel.IPC.Operations.Timeout
lake build SeLe4n.Platform.Sim.BootContract
lake build SeLe4n.Kernel.InformationFlow.Policy

# Full build
lake build

# Tiered test suites
./scripts/test_fast.sh        # Tier 0+1: hygiene + build
./scripts/test_smoke.sh       # Tier 0-2: + trace + negative-state
./scripts/test_full.sh        # Tier 0-3: + invariant surface anchors

# Rust workspace
cargo test --workspace
cargo clippy --workspace

# Version sync
./scripts/check_version_sync.sh

# Zero sorry/axiom check
grep -rn "sorry\|axiom " SeLe4n/ --include="*.lean" | grep -v "^.*:.*--" | wc -l

# Fixture verification
lake exe sele4n 2>&1 | diff - tests/fixtures/main_trace_smoke.expected
```
