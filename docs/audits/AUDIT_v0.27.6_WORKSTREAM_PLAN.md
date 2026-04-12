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
findings through 7 phases with 37 sub-tasks, after filtering out 4 erroneous
findings, 6 already-tracked deferrals, and 12 confirmed-correct design decisions.

### 1.1 Finding Disposition Summary

| Disposition | Count | Details |
|-------------|-------|---------|
| **Actionable (code change)** | 22 | H-01, H-02, H-03, H-04, H-05, M-01, M-04, M-09, M-14, M-15, M-19, M-20, M-22, M-26, M-27, L-05, L-09, L-10, L-15, L-17, L-24, L-26 |
| **Documentation-only** | 16 | M-02, M-03, M-07, M-08, M-10, M-11, M-13, M-16, M-17, M-18, M-21, M-23, M-24, M-25, L-02, L-13 |
| **Erroneous / refuted** | 4 | M-05, M-12, L-06, L-28 |
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

**Estimated scope**: ~620–850 lines Lean (functions, theorems, frame lemmas,
test sites), ~150 lines Rust, ~250 lines documentation.

**Total sub-tasks**: 37 (across 7 phases)

---

## 2. Finding Cross-Reference and Verification

Every finding from the baseline audit was independently re-verified against
source code before inclusion in this plan. This section classifies each finding
and provides the verification rationale.

### 2.1 Erroneous / Refuted Findings (4)

| Finding | Audit Severity | Actual | Rationale |
|---------|---------------|--------|-----------|
| M-05 | MEDIUM | **ERRONEOUS** | `timeoutBlockedThreads` does NOT discard per-thread timeout errors. Return type is `SystemState × List (ThreadId × KernelError)` (Core.lean:505). Errors are explicitly collected via `errs ++ [(tid, e)]` (line 519). This was fixed in AG1-B. The audit finding is factually incorrect. |
| M-12 | MEDIUM | **ERRONEOUS** | `resolveCapAddress` intermediate CNode read-right skipping is a **documented deliberate design divergence** from seL4 (Operations.lean:85-92, U-M25 annotation). Rights are enforced at the operation layer via `capHasRight` guards at each callsite (`cspaceMint`, `cspaceCopy`, etc.), covering all access paths. This is an architectural design decision, not a vulnerability. |
| L-06 | LOW | **ERRONEOUS** | CDT acyclicity is NOT externalized for expanding operations. Grep for `retype.*acyclicity` returns no results. Acyclicity proofs for retype remain internal via `edgeWellFounded` and `freshChild_not_reachable` bridge (AE4-C/U-18). |
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
| L-13 | Document `schedContextBind` thread-state gap: lines 142-144 check `tcb.schedContextBinding` (binding state: `.unbound`/`.bound`/`.donated`) but NOT the thread's operational state (`ipcState`, scheduler state). Binding a thread mid-IPC-operation is permitted by design (matches seL4 MCS semantics where binding is independent of execution state). Add design-rationale comment noting this is intentional. | AI6 |

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
**Type**: Multi-step fix (4 sub-steps)

Current state:
- Line 179: `pub static mut BOOT_UART: Uart = Uart::new(UART0_BASE)`
- Lines 188-194: `with_boot_uart()` helper wraps unsafe access via `&raw mut`
- Lines 200-203: `init_boot_uart()` called once from `boot.rs:23`
- Line 213: `kprint!` macro accesses via raw pointer dereference
- No `SpinLock` or `Mutex` type exists in the crate (zero dependencies)
- Only file referencing `BOOT_UART` is `uart.rs` itself

**Sub-step AI1-D-1: Implement minimal spinlock guard**

Since `sele4n-hal` has zero external dependencies (bare-metal, `#![no_std]`),
implement a lightweight IRQ-safe lock using `AtomicBool`:

```rust
use core::sync::atomic::{AtomicBool, Ordering};

/// Minimal IRQ-safe spinlock for boot UART access.
/// Safety: Disables interrupts during critical section to prevent
/// deadlock from nested IRQ handlers accessing the UART.
struct UartLock {
    locked: AtomicBool,
}

impl UartLock {
    const fn new() -> Self {
        Self { locked: AtomicBool::new(false) }
    }

    fn with<R>(&self, f: impl FnOnce(&mut Uart) -> R) -> R {
        // Spin-acquire (single-core: interrupt handler is the only contender)
        while self.locked.compare_exchange_weak(
            false, true, Ordering::Acquire, Ordering::Relaxed
        ).is_err() {
            core::hint::spin_loop();
        }
        // SAFETY: Lock held, single writer guaranteed
        let result = unsafe { f(&mut *core::ptr::addr_of_mut!(BOOT_UART_INNER)) };
        self.locked.store(false, Ordering::Release);
        result
    }
}

static UART_LOCK: UartLock = UartLock::new();
static mut BOOT_UART_INNER: Uart = Uart::new(UART0_BASE);
```

**Sub-step AI1-D-2: Update `with_boot_uart()` and `init_boot_uart()`**

Replace the existing `with_boot_uart()` (lines 188-194) to use the lock:
```rust
pub(crate) fn with_boot_uart<R>(f: impl FnOnce(&mut Uart) -> R) -> R {
    UART_LOCK.with(f)
}
```

Update `init_boot_uart()` to use the lock for initialization:
```rust
pub fn init_boot_uart() {
    UART_LOCK.with(|uart| uart.init());
}
```

**Sub-step AI1-D-3: Update `kprint!` macro**

The macro (line 220) currently uses unsafe raw pointer access. Change to
use `with_boot_uart`:
```rust
macro_rules! kprint {
    ($($arg:tt)*) => ({
        use core::fmt::Write;
        crate::uart::with_boot_uart(|uart| {
            let _ = write!(uart, $($arg)*);
        });
    });
}
```

**Sub-step AI1-D-4: Restrict visibility and clean up**

- Change `BOOT_UART_INNER` from `pub` to module-private (it's accessed
  only through `with_boot_uart` and the lock).
- Verify `boot.rs:23` calls `init_boot_uart()` (unchanged — init function
  signature is preserved).

Build: `cargo test -p sele4n-hal` + `cargo clippy -p sele4n-hal`

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
**Type**: Multi-step fix (4 sub-steps)

The current implementation has 4 match arms after `readDescriptor` calls at
levels L0, L1, L2. Only the innermost arm (L2 → `.table l3base`) writes the
`.invalid` descriptor to hardware memory. The other 3 wildcard arms
(`| _ => some { vs with shadow := shadow' }`) silently succeed after updating
only the shadow — creating shadow/HW divergence.

Current function structure:
```lean
def ARMv8VSpace.unmapPage (vs : ARMv8VSpace) (va : VAddr) : Option ARMv8VSpace :=
  match vs.shadow.unmapPage va with
  | none => none                               -- Shadow unmap failed → propagate
  | some shadow' =>
    let d0 := readDescriptor vs.pageTableMemory vs.ttbr (l0Index va) .l0
    match d0 with
    | .table l1base =>                          -- L0 success
      let d1 := readDescriptor vs.pageTableMemory l1base (l1Index va) .l1
      match d1 with
      | .table l2base =>                        -- L1 success
        let d2 := readDescriptor vs.pageTableMemory l2base (l2Index va) .l2
        match d2 with
        | .table l3base =>                      -- L2 success → write .invalid
          let mem' := writeDescriptor vs.pageTableMemory l3base (l3Index va) .invalid
          some { vs with pageTableMemory := mem', shadow := shadow' }
        | _ => some { vs with shadow := shadow' }  -- L2 walk fail → BUG
      | _ => some { vs with shadow := shadow' }    -- L1 walk fail → BUG
    | _ => some { vs with shadow := shadow' }      -- L0 walk fail → BUG
```

**Sub-step AI2-B-1: Change return type to `Except`**

No `VSpaceError` type exists in the Architecture modules. Define one:
```lean
inductive VSpaceWalkError where
  | shadowUnmapFailed  : VSpaceWalkError
  | walkFailedAtLevel  : PageTableLevel → VSpaceWalkError
```

Change the function signature from `Option ARMv8VSpace` to
`Except VSpaceWalkError ARMv8VSpace`. Change the shadow-unmap failure
(currently `none`) to `.error .shadowUnmapFailed`.

**Sub-step AI2-B-2: Replace wildcard arms with errors**

Change the 3 wildcard arms:
```lean
-- Was: | _ => some { vs with shadow := shadow' }
-- L0 failure:
| _ => .error (.walkFailedAtLevel .l0)
-- L1 failure:
| _ => .error (.walkFailedAtLevel .l1)
-- L2 failure:
| _ => .error (.walkFailedAtLevel .l2)
```
The success path becomes `.ok { vs with pageTableMemory := mem', shadow := shadow' }`.

**Sub-step AI2-B-3: Update callers (4 sites)**

| Location | Current Usage | Update |
|----------|--------------|--------|
| VSpaceARMv8.lean:279 — VSpaceBackend instance `unmapPage` delegation | Calls `ARMv8VSpace.unmapPage` and returns `Option` | Wrap with `match ... \| .ok v => some v \| .error _ => none` to preserve `VSpaceBackend` typeclass contract (which uses `Option`). The error is still surfaced at the `VSpaceBackend` level as `none` but the ARMv8 layer now distinguishes failure causes. |
| VSpaceARMv8.lean:287 — `unmapPage_preserves_asid` theorem | References `unmapPage` in statement | Add `Except` unwrapping: change `match unmapPage vs va with \| some vs' => ...` to `match unmapPage vs va with \| .ok vs' => ...`. |
| VSpaceARMv8.lean:299, 304 — shadow sync proofs | Same pattern as above | Same `Except` unwrapping. |

**Sub-step AI2-B-4: Update 3 local theorems**

| Theorem | Line | Change |
|---------|------|--------|
| `unmapPage_preserves_asid` | ~228 | Replace `Option` matching with `Except` matching in hypothesis and conclusion. The proof body likely uses `unfold unmapPage; simp` — after the change, `simp` must reduce through `Except` constructors instead of `Option`. |
| `unmapPage_shadow_eq` | ~256 | Same pattern change. The key insight: the `.ok` branch preserves the same shadow relationship, so the proof structure survives. |
| `lookupPage_refines` / `vspaceProperty_transfer` | Used transitively | These may reference `unmapPage` indirectly via the VSpaceBackend instance. Since the instance wrapper converts back to `Option`, these theorems should be unaffected. |

Build verification:
```bash
lake build SeLe4n.Kernel.Architecture.VSpaceARMv8
lake build SeLe4n.Kernel.Architecture.VSpaceInvariant  # transitive dependents
```

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

Current function:
```lean
def handleYield : Kernel Unit :=
  fun st =>
    match st.scheduler.current with
    | none => .error .invalidArgument
    | some tid =>
        match st.objects[tid.toObjId]? with
        | some (.tcb tcb) =>
            let rq' := (st.scheduler.runQueue.insert tid tcb.priority).rotateToBack tid
            let st' := { st with scheduler := { st.scheduler with runQueue := rq' } }
            schedule st'
        | _ => .error .schedulerInvariantViolation
```

Established pattern (from `refillSchedContextFIFO`, Core.lean:460-461):
```lean
runQueue := refilled.scheduler.runQueue.insert tid (resolveInsertPriority refilled tid sc)
```

**Sub-step AI3-A-1: Replace priority source in `handleYield`**

Change Core.lean line 341 from:
```lean
let rq' := (st.scheduler.runQueue.insert tid tcb.priority).rotateToBack tid
```
to:
```lean
let effectivePrio := (resolveEffectivePrioDeadline st tcb).1
let rq' := (st.scheduler.runQueue.insert tid effectivePrio).rotateToBack tid
```

`resolveEffectivePrioDeadline` (Selection.lean:323-349) is already imported
by Core.lean via the Operations hub. It computes
`max(basePriority, tcb.pipBoost.getD 0)`.

**Sub-step AI3-A-2: Update comment block**

Replace the AF1-H "intentional" comment (lines 332-340) with:
```
-- AI3-A (M-04): Re-enqueues at effective priority (max of base and PIP
-- boost). This ensures PIP-boosted threads retain elevated scheduling
-- band after yield, preventing priority inversion. Pattern matches
-- resolveInsertPriority usage at 5 other insertion sites (AG1-A).
```

**Sub-step AI3-A-3: Update 15 preservation theorems in Preservation.lean**

The following theorems reference `handleYield` and may depend on the
specific priority value used for insertion. Each must be checked:

| # | Theorem | Line | Likely Impact |
|---|---------|------|--------------|
| 1 | `handleYield_preserves_queueCurrentConsistent` | 359 | Low — checks current ∉ runQueue, not priority |
| 2 | `handleYield_preserves_wellFormed` | 379 | **Medium** — may unfold `insert` and check bucket structure |
| 3 | `handleYield_preserves_runQueueUnique` | 396 | Low — uniqueness is priority-independent |
| 4 | `handleYield_preserves_currentThreadValid` | 428 | Low — checks TCB existence, not priority |
| 5 | `handleYield_preserves_currentThreadInActiveDomain` | 451 | Low — domain check, not priority |
| 6 | `handleYield_preserves_schedulerInvariantBundle` | 497 | **Medium** — composes sub-invariants |
| 7 | `handleYield_preserves_timeSlicePositive` | 911 | Low — time-slice field, not priority |
| 8 | `handleYield_preserves_currentTimeSlicePositive` | 1165 | Low — same |
| 9 | `handleYield_preserves_runnableThreadsAreTCBs` | 1484 | Low — TCB existence |
| 10 | `handleYield_preserves_domainTimeRemainingPositive` | 1774 | Low — domain time |
| 11 | `handleYield_preserves_domainSchedule` | 1949 | Low — domain schedule |
| 12 | `handleYield_preserves_edfCurrentHasEarliestDeadline` | 2423 | **High** — EDF ordering depends on priority |
| 13 | `handleYield_preserves_contextMatchesCurrent` | 2681 | Low — register context |
| 14 | `handleYield_preserves_schedulerPriorityMatch` | 2925 | **High** — directly checks priority consistency |
| 15 | `handleYield_preserves_schedulerInvariantBundleFull` | 3112 | **Medium** — full bundle composition |

**Strategy**: Theorems marked **High** require proof body changes. The
key change: where proofs previously assumed `insert tid tcb.priority`,
they must now handle `insert tid (resolveEffectivePrioDeadline st tcb).1`.
Since 5 other insertion sites already use this pattern, the proof
structure for effective-priority insertion is established. The `simp
[resolveEffectivePrioDeadline]` tactic should reduce the new expression.

**Sub-step AI3-A-4: Update API.lean caller**

`handleYield` is called from `handleYieldChecked` (API.lean:156). Since
`handleYield` does not change its function signature (still `Kernel Unit`),
the caller needs no update. Verify: `lake build SeLe4n.Kernel.API`

**Sub-step AI3-A-5: Build verification**
```bash
lake build SeLe4n.Kernel.Scheduler.Operations.Core
lake build SeLe4n.Kernel.Scheduler.Operations.Preservation
lake build SeLe4n.Kernel.API
```

#### AI3-B: Use effective priority in `migrateRunQueueBucket` (M-22)

**Finding**: M-22 — `migrateRunQueueBucket` ignores PIP boost
**File**: `SeLe4n/Kernel/SchedContext/PriorityManagement.lean`, lines 101-108
**Type**: Multi-step fix (4 sub-steps)

Current function:
```lean
def migrateRunQueueBucket (st : SystemState) (tid : SeLe4n.ThreadId)
    (newPriority : SeLe4n.Priority) : SystemState :=
  if tid ∈ st.scheduler.runQueue then
    let rq := st.scheduler.runQueue.remove tid
    let rq := rq.insert tid newPriority
    { st with scheduler := { st.scheduler with runQueue := rq } }
  else st
```

Already takes `SystemState`, so has access to TCB data. The TCB
`pipBoost` field is `Option SeLe4n.Priority := none` (Types.lean:552).

**Sub-step AI3-B-1: Add PIP-aware priority computation**

Add a TCB lookup to resolve effective priority. Change the function body:
```lean
def migrateRunQueueBucket (st : SystemState) (tid : SeLe4n.ThreadId)
    (newPriority : SeLe4n.Priority) : SystemState :=
  if tid ∈ st.scheduler.runQueue then
    let rq := st.scheduler.runQueue.remove tid
    -- AI3-B (M-22): Apply PIP boost to new priority
    let effectivePrio := match st.objects[tid.toObjId]? with
      | some (.tcb tcb) => max newPriority (tcb.pipBoost.getD 0)
      | _ => newPriority  -- defensive fallback
    let rq := rq.insert tid effectivePrio
    { st with scheduler := { st.scheduler with runQueue := rq } }
  else st
```

No signature change — callers (`setPriorityOp`, `setMCPriorityOp`) are
unaffected. The change is internal to the function body only.

**Sub-step AI3-B-2: Update 5 transport lemmas in PriorityPreservation.lean**

| # | Theorem | Line | Impact |
|---|---------|------|--------|
| 1 | `migrateRunQueueBucket_objects_eq` | 52 | **None** — proves objects field unchanged; new code only modifies scheduler |
| 2 | `migrateRunQueueBucket_serviceRegistry_eq` | 57 | **None** — same reasoning |
| 3 | `migrateRunQueueBucket_lifecycle_eq` | 62 | **None** — same reasoning |
| 4 | `migrateRunQueueBucket_irqHandlers_eq` | 96 | **None** — same reasoning |
| 5 | `migrateRunQueueBucket_machine_eq` | 101 | **None** — same reasoning |

All 5 theorems prove that `migrateRunQueueBucket` preserves fields
*outside* the scheduler. Since the new code still only modifies
`st.scheduler.runQueue`, these proofs should survive unchanged. The
proofs likely use `unfold migrateRunQueueBucket; simp [*]` which
will still close because the struct-with only touches `scheduler`.

**Sub-step AI3-B-3: Verify callers unchanged**

`setPriorityOp` (line ~130) and `setMCPriorityOp` (line ~170) call
`migrateRunQueueBucket st tid newPriority`. Since the signature is
unchanged, no caller updates are needed.

**Sub-step AI3-B-4: Build verification**
```bash
lake build SeLe4n.Kernel.SchedContext.PriorityManagement
lake build SeLe4n.Kernel.SchedContext.Invariant.PriorityPreservation
```

#### AI3-C: Add `Except` return to `saveOutgoingContext` (L-09)

**Finding**: L-09 — `saveOutgoingContext` silently returns state on TCB miss
**File**: `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`, lines 478-486
**Type**: Multi-step fix (3 sub-steps)

Current function:
```lean
def saveOutgoingContext (st : SystemState) : SystemState :=
  match st.scheduler.current with
  | none => st                                   -- No current thread
  | some outTid =>
      match st.objects[outTid.toObjId]? with
      | some (.tcb outTcb) =>                    -- Save registers to TCB
          let obj := KernelObject.tcb { outTcb with registerContext := st.machine.regs }
          { st with objects := st.objects.insert outTid.toObjId obj }
      | _ => st                                  -- BUG: silent failure
```

A checked variant `saveOutgoingContextChecked` already exists
(Selection.lean:495-503) returning `SystemState × Bool`. The unchecked
variant is used by 5 internal call sites in Core.lean.

**Sub-step AI3-C-1: Change return type and error paths**

Change `saveOutgoingContext` from `SystemState` to
`Except KernelError SystemState`:
```lean
def saveOutgoingContext (st : SystemState) : Except KernelError SystemState :=
  match st.scheduler.current with
  | none => .ok st                               -- No current thread (valid)
  | some outTid =>
      match st.objects[outTid.toObjId]? with
      | some (.tcb outTcb) =>
          let obj := KernelObject.tcb { outTcb with registerContext := st.machine.regs }
          .ok { st with objects := st.objects.insert outTid.toObjId obj }
      | _ => .error .schedulerInvariantViolation  -- Surfaces violation
```

**Sub-step AI3-C-2: Update 5 callers in Core.lean**

All callers currently use `let stSaved := saveOutgoingContext st'`. Each
must be updated to propagate the error:

| # | Location | Context | Update |
|---|----------|---------|--------|
| 1 | Core.lean:287 | `schedule`, idle branch | `match saveOutgoingContext st' with \| .error e => .error e \| .ok stSaved => ...` |
| 2 | Core.lean:296 | `schedule`, dispatch branch | Same pattern |
| 3 | Core.lean:613 | `scheduleEffective`, idle | Same pattern |
| 4 | Core.lean:619 | `scheduleEffective`, dispatch | Same pattern |
| 5 | Core.lean:771 | `switchDomain` | Same pattern |

Each is a mechanical transformation: `let x := f y` becomes
`match f y with | .error e => .error e | .ok x => ...`. Since all
callers already return `Kernel Unit` (which is `SystemState → Except ...`),
error propagation integrates naturally.

**Sub-step AI3-C-3: Update 16 theorems**

Key theorems to check (Selection.lean + Preservation.lean + others):
- `saveOutgoingContext_scheduler` — proves scheduler field unchanged
- `saveOutgoingContext_preserves_tcb` — proves TCB fields preserved
- `saveOutgoingContext_preserves_objects_invExt` — invariant extension
- `schedulerPriorityMatch_of_saveOutgoingContext` — priority consistency
- 12 additional transport lemmas

**Strategy**: All theorems that previously had conclusion
`saveOutgoingContext st = st'` must change to
`saveOutgoingContext st = .ok st'`. Proofs that unfold the definition
will encounter `Except` constructors; `simp` should close them since
the success path is structurally identical. Theorems about the
failure path don't exist yet (the failure was previously invisible).

Build:
```bash
lake build SeLe4n.Kernel.Scheduler.Operations.Selection
lake build SeLe4n.Kernel.Scheduler.Operations.Core
lake build SeLe4n.Kernel.Scheduler.Operations.Preservation
```

#### AI3-D: Enforce `configDefaultTimeSlice` positivity (L-10)

**Finding**: L-10 — `configDefaultTimeSlice` positivity not enforced
**File**: `SeLe4n/Model/State.lean` (field in `SchedulerState` struct)
**Type**: Atomic fix (2 sub-steps)

`configDefaultTimeSlice` is a `Nat` field in `SchedulerState` with
default value `5`. Preservation theorems in Preservation.lean already
require the hypothesis `hConfigTS : st.scheduler.configDefaultTimeSlice > 0`
(13 occurrences). The gap: the definition permits zero, so the hypothesis
must be externally maintained.

**Sub-step AI3-D-1: Add positivity invariant predicate**

Add to the scheduler invariant bundle (or as a standalone predicate):
```lean
def configTimeSlicePositive (st : SystemState) : Prop :=
  st.scheduler.configDefaultTimeSlice > 0
```

Add this as a predicate to `schedulerInvariantBundle` (if not already
present — verify against the current bundle definition).

**Sub-step AI3-D-2: Add runtime guard at assignment**

Find where `configDefaultTimeSlice` is set (boot sequence, platform
config). Add a guard:
```lean
let ts := if config.defaultTimeSlice == 0 then 5 else config.defaultTimeSlice
```

This ensures the invariant holds by construction. Document:
```
-- AI3-D (L-10): Zero time slice would cause immediate timer expiry.
-- Guard ensures positivity; default 5 matches seL4 convention.
```

Build: `lake build SeLe4n.Model.State`

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
**Type**: Multi-step fix (5 sub-steps) — **highest-complexity task in AI4**

The abnormal path: a server does `.receive` without replying to a prior
`.call`. The donated SchedContext from the prior call remains bound to the
server with `.donated` binding. `cleanupPreReceiveDonation` checks for
this condition and returns the SchedContext to the original owner.

Function to wire (Donation.lean:186-200):
```lean
def cleanupPreReceiveDonation (st : SystemState) (receiver : ThreadId) : SystemState :=
  match lookupTcb st receiver with
  | none => st
  | some recvTcb =>
    match recvTcb.schedContextBinding with
    | .donated scId originalOwner =>
      match returnDonatedSchedContext st receiver scId originalOwner with
      | .error _ => st    -- Defensive: return unchanged on error
      | .ok st' => st'
    | _ => st             -- No donation to clean up
```

Return type is `SystemState` (pure, not monadic). On the common path
(no stale donation), it returns `st` unchanged — zero overhead.

**Insertion point** (Transport.lean:1672-1678):
```lean
        | none =>           -- No sender waiting → receiver blocks
            match endpointQueueEnqueue endpointId true receiver st with
            | .error e => .error e
            | .ok st' =>
                match storeTcbIpcState st' receiver (.blockedOnReceive endpointId) with
                | .error e => .error e
                | .ok st'' => .ok (receiver, removeRunnable st'' receiver)
```

**Sub-step AI4-A-1: Add import for Donation module**

Transport.lean currently imports only `SeLe4n.Kernel.IPC.DualQueue.Core`.
Core imports `SeLe4n.Kernel.IPC.Operations` which includes all Operations
submodules. **However**, the transitive import chain must be verified:
- Core.lean → check if it imports Operations hub
- If not: add `import SeLe4n.Kernel.IPC.Operations.Donation` to
  Transport.lean directly

**Sub-step AI4-A-2: Insert cleanup call at line 1672**

Change the no-sender branch:
```lean
        | none =>
            -- AI4-A (M-01): Clean up stale donated SchedContext from a
            -- prior unanswered call before blocking on receive.
            let st := cleanupPreReceiveDonation st receiver
            match endpointQueueEnqueue endpointId true receiver st with
            | .error e => .error e
            | .ok st' =>
                match storeTcbIpcState st' receiver (.blockedOnReceive endpointId) with
                | .error e => .error e
                | .ok st'' => .ok (receiver, removeRunnable st'' receiver)
```

The `let st := ...` shadowing is intentional — it replaces the original
`st` with the cleaned-up version for all subsequent operations. On the
common path (no stale donation), `cleanupPreReceiveDonation` returns `st`
unchanged, so the semantics are identical.

**Sub-step AI4-A-3: Update preservation theorems (16 affected)**

The cleanup call modifies state before `endpointQueueEnqueue`. Every
theorem that proves properties of `endpointReceiveDual` in the no-sender
branch must now account for the intermediate `cleanupPreReceiveDonation`
step. The theorems split into two groups:

**Group 1: EndpointPreservation.lean (5 theorems)**

| # | Theorem | Line |
|---|---------|------|
| 1 | `endpointReceiveDual_preserves_ipcInvariant` | 789 |
| 2 | `endpointReceiveDual_preserves_schedulerInvariantBundle` | 867 |
| 3 | `endpointReceiveDual_preserves_ipcSchedulerContractPredicates` | 1039 |
| 4 | `endpointReceiveDual_preserves_objects_invExt` | 1463 |
| 5 | `endpointReceiveDualWithCaps_preserves_ipcInvariant` | 1586 |

**Group 2: Structural.lean (11 theorems)**

| # | Theorem | Line |
|---|---------|------|
| 6 | `endpointReceiveDual_sender_exists` | 102 |
| 7 | `endpointReceiveDual_preserves_dualQueueSystemInvariant` | 1902 |
| 8 | `endpointReceiveDual_preserves_allPendingMessagesBounded` | 3315 |
| 9 | `endpointReceiveDual_preserves_badgeWellFormed` | 3402 |
| 10 | `endpointReceiveDual_preserves_endpointQueueNoDup` | 3915 |
| 11 | `endpointReceiveDual_preserves_ipcStateQueueMembershipConsistent` | 4333 |
| 12 | `endpointReceiveDual_preserves_ipcInvariantFull` | 4782 |
| 13 | `endpointReceiveDualWithCaps_preserves_ipcInvariantFull` | 4921 |
| 14 | `endpointReceiveDual_preserves_ipcStateQueueConsistent` | 5292 |
| 15 | `endpointReceiveDualWithCaps_preserves_dualQueueSystemInvariant` | 5870 |
| 16 | `endpointReceiveDual_preserves_waitingThreadsPendingMessageNone` | 7167 |

**Strategy for theorem updates**: Each theorem must handle the new
intermediate state. The key insight: `cleanupPreReceiveDonation` only
modifies `schedContextBinding` on the receiver's TCB (and potentially
the original owner's TCB). It does NOT modify:
- Endpoint state or queue structure
- IPC state of any thread other than the receiver
- Objects other than 2 TCBs and 1 SchedContext

Therefore, most invariant preservation proofs can use a **frame lemma**
approach: prove that `cleanupPreReceiveDonation` preserves each
sub-invariant independently, then compose with the existing proofs.

**Recommended**: Before attempting all 16 theorems, first create a
`cleanupPreReceiveDonation` frame lemma suite:
```lean
theorem cleanupPreReceiveDonation_preserves_endpointQueues ...
theorem cleanupPreReceiveDonation_preserves_ipcState_non_receiver ...
theorem cleanupPreReceiveDonation_preserves_pendingMessages ...
```

These frame lemmas establish that the cleanup is "transparent" to
endpoint/IPC invariants, allowing the 16 existing proofs to compose
with the cleanup step via `calc` or transitivity.

**Sub-step AI4-A-4: Verify `endpointReceiveDualWithCaps` path**

`endpointReceiveDualWithCaps` (DualQueue/WithCaps.lean) wraps
`endpointReceiveDual`. If the wrapper delegates to the same no-sender
branch, the cleanup is automatically included. Verify this. If
`WithCaps` has its own no-sender branch, the cleanup must be duplicated
or the branch must be refactored to share code.

**Sub-step AI4-A-5: Build verification**
```bash
lake build SeLe4n.Kernel.IPC.DualQueue.Transport
lake build SeLe4n.Kernel.IPC.Invariant.EndpointPreservation
lake build SeLe4n.Kernel.IPC.Invariant.Structural
lake build SeLe4n.Kernel.IPC.Invariant.CallReplyRecv
```

#### AI4-B: Surface DTB parser fuel exhaustion as distinct error (M-09)

**Finding**: M-09 — DTB parser fuel=2000 silently drops peripherals
**File**: `SeLe4n/Platform/DeviceTree.lean`, lines 618-627
**Type**: Multi-step fix (3 sub-steps)

Current function signature:
```lean
def parseFdtNodes (blob : ByteArray) (hdr : FdtHeader)
    (fuel : Nat := 2000) : Option (List FdtNode)
```

Fuel-exhaustion branch (lines 627, 658): `| 0 => none`

The sole caller is `DeviceTree.fromDtbFull` (line 851), which silently
falls back to empty list on `none`:
```lean
let nodes := match parseFdtNodes blob hdr with
  | some ns => ns
  | none => []    -- Silent fallback — fuel exhaustion indistinguishable from no nodes
```

No error types currently exist in DeviceTree.lean. All functions use
`Option` exclusively.

**Sub-step AI4-B-1: Define `DeviceTreeParseError` type**

Add near the top of DeviceTree.lean (after imports):
```lean
inductive DeviceTreeParseError where
  | fuelExhausted  : DeviceTreeParseError
  | malformedBlob  : DeviceTreeParseError
  deriving Repr, BEq
```

**Sub-step AI4-B-2: Change `parseFdtNodes` return type**

Change from `Option (List FdtNode)` to
`Except DeviceTreeParseError (List FdtNode)`:
- Fuel exhaustion: `| 0 => .error .fuelExhausted`
- Success: `| fuel + 1 => ... .ok nodes`
- The recursive `go` helper and `parseNodeContents` helper both need
  the same return type change (they also return `none` on fuel=0).

**Sub-step AI4-B-3: Update sole caller in `fromDtbFull`**

Change line 851 from:
```lean
let nodes := match parseFdtNodes blob hdr with
  | some ns => ns
  | none => []
```
to:
```lean
let nodes := match parseFdtNodes blob hdr with
  | .ok ns => ns
  | .error .fuelExhausted => []  -- AI4-B: Log warning, use partial results
  | .error _ => []               -- Malformed blob: empty fallback
```

**Note**: The fallback behavior is preserved (empty list), but the error
is now distinguishable. A future enhancement can propagate the error
to `bootFromPlatformWithWarnings` to surface fuel exhaustion in the
boot warning log. The one existing theorem
(`parseFdtHeader_fromDtbFull_some`, line ~873) references header parsing,
not node parsing, and should be unaffected.

Build: `lake build SeLe4n.Platform.DeviceTree`

#### AI4-C: Remove unused `_endpointId` parameter from `timeoutAwareReceive` (L-05)

**Finding**: L-05 — `timeoutAwareReceive` has unused `_endpointId` parameter
**File**: `SeLe4n/Kernel/IPC/Operations/Timeout.lean`, lines 114-115
**Type**: Atomic fix (low-risk, 3 update sites)

Current function:
```lean
def timeoutAwareReceive
    (_endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    : Kernel IpcTimeoutResult :=
  fun st =>
    match lookupTcb st receiver with
    | none => .error .objectNotFound
    | some tcb =>
      if tcb.timedOut ∧ tcb.ipcState = .ready then
        let tcb' := { tcb with timedOut := false }
        match storeObject receiver.toObjId (.tcb tcb') st with
        | .error e => .error e
        | .ok ((), st') => .ok (.timedOut, st')
      else
        match tcb.pendingMessage with
        | some msg => .ok (.completed msg, st)
        | none => .error .endpointQueueEmpty
```

**Update sites** (total: 3):

| # | File | Line | Argument to Remove |
|---|------|------|--------------------|
| 1 | Definition | Timeout.lean:114 | `(_endpointId : SeLe4n.ObjId)` param |
| 2 | Test call | MainTraceHarness.lean:2562 | `epId` first argument |
| 3 | Test call | MainTraceHarness.lean:2577 | `epId` first argument |

**No theorems reference `timeoutAwareReceive`** — no theorem updates needed.
No API.lean callers exist (the function is test-only currently).

**Steps**:
1. Remove parameter from signature (Timeout.lean:114).
2. Remove `epId` argument from 2 test call sites.
3. Build: `lake build SeLe4n.Kernel.IPC.Operations.Timeout`

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
**Type**: Multi-step fix (3 sub-steps)

The `BootBoundaryContract` structure (Assumptions.lean:27-33) has 4 fields:
```lean
structure BootBoundaryContract where
  objectTypeMetadataConsistent : Prop
  capabilityRefMetadataConsistent : Prop
  objectStoreNonEmpty : Prop := True
  irqRangeValid : Prop := True
```

The RPi5 boot contract (RPi5/BootContract.lean:48-54) uses:
- `objectTypeMetadataConsistent := (default : SystemState).objects.size = 0`
- `capabilityRefMetadataConsistent := (default : SystemState).lifecycle.capabilityRefs.size = 0`

Available decidable predicates in InvariantChecks.lean (lines 78-88):
- `schedulerQueueCurrentConsistentB`, `schedulerRunQueueUniqueB`
- `currentThreadValidB`, `currentThreadInActiveDomainB`
- `notificationQueueWellFormedB`, `endpointDualQueueWellFormedB`

Importers of `Sim.BootContract` or `Sim.Contract`: `SeLe4n.lean`,
`Platform/Sim/Contract.lean`.

**Sub-step AI5-A-1: Design substantive predicates**

Replace vacuous `True` with lightweight but meaningful checks. The
simulation state builder constructs state from scratch, so predicates
should validate the *output* of `buildChecked`:

```lean
def simBootContract : BootBoundaryContract where
  -- AI5-A (H-01): Substantive predicates replacing vacuous True
  objectTypeMetadataConsistent :=
    -- Default initial state has no objects (builder adds them)
    (default : SystemState).objects.size = 0
  capabilityRefMetadataConsistent :=
    -- Default initial state has no capability references
    (default : SystemState).lifecycle.capabilityRefs.size = 0
  objectStoreNonEmpty :=
    -- After build, at least 1 object exists (strengthened from True)
    True  -- Note: This predicate is about the contract *structure*, not
          -- post-build state. See Sub-step AI5-A-2 for runtime check.
  irqRangeValid :=
    -- Simulation IRQ table is initially empty (valid by construction)
    (default : SystemState).irqHandlers.size = 0
```

**Design rationale**: The predicates validate *initial* (default) state
properties. The RPi5 pattern proves these hold for `default : SystemState`.
Post-build validation is handled by `buildChecked` which verifies
invariants after state construction.

**Sub-step AI5-A-2: Add post-build boot invariant check**

Add a runtime check in the simulation contract that exercises
`InvariantChecks` predicates after boot:
```lean
def simBootPostBuildCheck (st : SystemState) : Bool :=
  schedulerQueueCurrentConsistentB st &&
  endpointDualQueueWellFormedB st &&
  notificationQueueWellFormedB st
```

Wire this into the `simRuntimeContractSubstantive` or the contract's
post-build hook.

**Sub-step AI5-A-3: Build and verify tests**

```bash
lake build SeLe4n.Platform.Sim.BootContract
lake build SeLe4n.Platform.Sim.Contract
./scripts/test_smoke.sh
```

#### AI5-B: Create substantive simulation interrupt contract (H-02)

**Finding**: H-02 — Simulation interrupt contract accepts ALL IRQs
**File**: `SeLe4n/Platform/Sim/BootContract.lean`, lines 42-48
**Type**: Multi-step fix (3 sub-steps)

The `InterruptBoundaryContract` structure (Assumptions.lean:49-53) has 4
fields: 2 predicates + 2 decidable instances:
```lean
structure InterruptBoundaryContract where
  irqLineSupported : SeLe4n.Irq → Prop
  irqHandlerMapped : SystemState → SeLe4n.Irq → Prop
  irqLineSupportedDecidable : ∀ irq, Decidable (irqLineSupported irq)
  irqHandlerMappedDecidable : ∀ st irq, Decidable (irqHandlerMapped st irq)
```

RPi5 pattern (RPi5/BootContract.lean:87-95):
- `irqLineSupported := fun irq => irq.toNat < gicSpiCount + 32`
- `irqHandlerMapped := fun st irq => irq.toNat < gicSpiCount + 32 → st.irqHandlers[irq]? ≠ none`

**Sub-step AI5-B-1: Define bounded IRQ range predicate**

```lean
def simInterruptContract : InterruptBoundaryContract where
  -- AI5-B (H-02): Restrict to GIC-400 INTID range (0–223)
  irqLineSupported := fun irq => irq.toNat < 224
  irqHandlerMapped := fun st irq =>
    irq.toNat < 224 → st.irqHandlers[irq]? ≠ none
  irqLineSupportedDecidable := fun irq => inferInstance
  irqHandlerMappedDecidable := fun st irq => inferInstance
```

**Sub-step AI5-B-2: Verify decidability**

The `Decidable` instances must discharge. `irq.toNat < 224` is decidable
via `Nat.decLt`. The handler mapping predicate `P → Q` requires both `P`
and `Q` to be decidable — `Nat.decLt` for the antecedent and
`Option.decidableNeNone` (or similar) for the consequent. If
`inferInstance` fails, provide explicit instances.

**Sub-step AI5-B-3: Update tests and build**

Search for test code that creates interrupt scenarios with out-of-range
IRQ numbers. Update expectations if any test sends IRQ ≥ 224.

Build: `lake build SeLe4n.Platform.Sim.BootContract`

#### AI5-C: Add runtime guard for `defaultLabelingContext` (M-19)

**Finding**: M-19 — `defaultLabelingContext` defeats all security
**File**: `SeLe4n/Kernel/InformationFlow/Policy.lean`, lines 215-226
**Type**: Multi-step fix (3 sub-steps)

Current definition:
```lean
def defaultLabelingContext : LabelingContext :=
  { objectLabelOf  := fun _ => SecurityLabel.publicLabel
    threadLabelOf  := fun _ => SecurityLabel.publicLabel
    endpointLabelOf := fun _ => SecurityLabel.publicLabel
    serviceLabelOf := fun _ => SecurityLabel.publicLabel }
```

Already proven insecure via `defaultLabelingContext_insecure` (line 240)
and `defaultLabelingContext_all_threads_observable` (line 250).

Callers of `defaultLabelingContext` (10 sites — all in tests):
- `MainTraceHarness.lean`: lines 459, 462, 563, 566, 600, 605, 634, 1803
- `InformationFlowSuite.lean`: line 947
- `TraceSequenceProbe.lean`: line 187

`dispatchWithCapChecked` (API.lean:814-816) takes `ctx : LabelingContext`
as its first parameter. It delegates to enforcement wrappers that check
`securityFlowsTo`.

`LabelingContextValid` (Composition.lean:708-719) is a `Prop` structure
with `∀` quantifiers — **not decidable** over infinite domains.

**Sub-step AI5-C-1: Create decidable insecurity detector**

Add to Policy.lean:
```lean
/-- AI5-C (M-19): Detect the insecure default labeling context.
    Checks sentinel labels at ID 0 — sufficient because the default
    assigns publicLabel to ALL entities uniformly. -/
def isInsecureDefaultContext (ctx : LabelingContext) : Bool :=
  ctx.threadLabelOf (ThreadId.ofNat 0) == SecurityLabel.publicLabel &&
  ctx.objectLabelOf (ObjId.ofNat 0) == SecurityLabel.publicLabel &&
  ctx.endpointLabelOf (ObjId.ofNat 0) == SecurityLabel.publicLabel
```

**Sub-step AI5-C-2: Wire guard into checked dispatch entry**

The guard should fire once at the `syscallEntryChecked` level, not on
every individual operation. Add to `syscallEntryChecked` in API.lean
(the top-level checked dispatch entry point):
```lean
-- AI5-C (M-19): Reject insecure default labeling context in checked mode
if isInsecureDefaultContext ctx then
  .error .invalidArgument  -- Use existing error; no new KernelError variant needed
else ...
```

**Impact on tests**: All 10 test sites use `defaultLabelingContext`. Tests
that exercise `syscallEntryChecked` will now fail. These tests must be
updated to provide a non-default labeling context with at least one
non-public label. Create a test helper:
```lean
def testLabelingContext : LabelingContext :=
  { objectLabelOf  := fun oid => if oid.toNat == 0 then .high else .publicLabel
    threadLabelOf  := fun tid => if tid.toNat == 0 then .high else .publicLabel
    endpointLabelOf := fun _ => .publicLabel
    serviceLabelOf := fun _ => .publicLabel }
```

Tests that specifically test flow-allowed semantics should use this
context, which allows most flows but is not the insecure default.

**Sub-step AI5-C-3: Build and verify**
```bash
lake build SeLe4n.Kernel.InformationFlow.Policy
lake build SeLe4n.Kernel.API
./scripts/test_smoke.sh  # Will fail until test sites updated
```

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

#### AI6-D: Model, capability & SchedContext documentation batch (M-21, L-02, L-13)

**Findings**: 3 model/SchedContext-layer documentation items
**Type**: Documentation-only batch

| Finding | File | Action |
|---------|------|--------|
| M-21 | `Structures.lean:2234-2246` | Verify existing scope note is sufficient. Add cross-reference: "See TPI-DOC for full fuel sufficiency formal bridge (deferred to WS-V). Current proof covers direct children (depth 1) only. `edgeWellFounded` provides the inductive foundation for the full proof." |
| L-02 | `State.lean:344` | Add note: "`allTablesInvExtK` 17-deep tuple projection is structurally fragile but stable under the current invariant bundle. Named extractors (Builder.lean:30-116) provide maintainable access. See AF-26 for design rationale." |
| L-13 | `SchedContext/Operations.lean:142-144` | Add design-rationale comment: "`schedContextBind` checks `tcb.schedContextBinding` (binding state: `.unbound`) but not the thread's operational state (`ipcState`, scheduler state). This matches seL4 MCS semantics where SchedContext binding is independent of thread execution state — binding can occur while a thread is blocked, ready, or in any other operational state. Operational safety is ensured by the SchedContext invariant bundle, not by per-bind state checks." |

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

| Phase | New/Modified Lines | Files Touched | Complexity | Key Bottleneck |
|-------|-------------------|---------------|------------|----------------|
| AI1 | ~150 Rust | 3 | Medium | AI1-D: spinlock impl in no_std |
| AI2 | ~120 Lean | 4-5 | Medium-High | AI2-B: 3 theorem updates for Except |
| AI3 | ~200 Lean + proofs | 5-7 | **High** | AI3-A: 15 preservation theorems |
| AI4 | ~180 Lean + proofs | 5-8 | **High** | AI4-A: 16 IPC theorems + frame lemmas |
| AI5 | ~120 Lean + tests | 4-6 | Medium | AI5-C: 10 test site updates |
| AI6 | ~250 documentation | 15-20 | Low | Batch comment insertion |
| AI7 | ~80 mixed | 8-12 | Low | Fixture diff |

**Critical path**: AI3 and AI4 are the highest-complexity phases due to
preservation theorem cascades. Each requires careful proof-chain analysis
before implementation. Start these phases first despite being parallelizable
with AI1/AI2/AI5.

---

## 11. Risk Assessment

### 11.1 High-Risk Sub-tasks

| Sub-task | Risk | Mitigation |
|----------|------|------------|
| AI1-D (UART sync) | Changing `static mut` to synchronized access may break bare-metal boot sequence if `AtomicBool` isn't available at early init. | Implement the `UartLock` using `core::sync::atomic` (always available in `#![no_std]`). Init through the lock wrapper. Test boot sequence output via existing UART tests. |
| AI2-A (EOI fix) | Changing `interruptDispatchSequence` error path from `.error e` to `.ok ((), endOfInterrupt st intId)` changes observable return semantics. | The recommended fix returns `.ok` — callers that matched on `.error` will now get `.ok`. Verify all callers of `interruptDispatchSequence` (likely only `ExceptionModel.lean`). |
| AI2-B (unmapPage) | Changing return type from `Option` to `Except` ripples through 3 local theorems and the VSpaceBackend instance. | The VSpaceBackend wrapper converts back to `Option`, isolating the Except change to VSpaceARMv8 module. Only 3 local theorems need `Except` matching updates. |
| AI3-A (handleYield PIP) | **15 preservation theorems** in Preservation.lean reference `handleYield`. Theorems #12 and #14 (EDF ordering, priority match) directly depend on the insertion priority value. | Start with the 2 high-impact theorems. The proof pattern for effective-priority insertion is established at 5 other sites. If `simp [resolveEffectivePrioDeadline]` doesn't close, manually unfold and case-split on `pipBoost`. |
| AI3-C (saveOutgoing) | Changing return type to `Except` ripples through **5 callers in Core.lean** and **16 theorems** across Selection/Preservation. | Mechanical transformation: `let x := f y` → `match f y with \| .ok x => ... \| .error e => .error e`. All callers already return `Kernel Unit` (Except-compatible). |
| AI4-A (cleanupPreReceive) | **Highest-complexity task**: Inserting a state-modifying call into `endpointReceiveDual` affects **16 IPC theorems** across EndpointPreservation + Structural (7591+ lines). | **Mitigation**: Build frame lemmas for `cleanupPreReceiveDonation` first (proving it preserves endpoint queues, IPC state, pending messages). These frame lemmas compose with existing proofs via transitivity. The cleanup only modifies `schedContextBinding` on ≤2 TCBs — structurally orthogonal to most IPC invariants. |
| AI5-C (labeling guard) | Adding a guard to `syscallEntryChecked` that rejects `defaultLabelingContext` will break **10 test call sites** that use the insecure default. | Create a `testLabelingContext` helper with one non-public label. Update all 10 test sites mechanically. Tests that specifically test flow-denial semantics are unaffected (they already use custom contexts). |

### 11.2 Low-Risk Sub-tasks

All documentation-only changes (AI6-A through AI6-F) and metadata changes
(AI7-D, AI7-E) are low risk. They do not affect behavior, proofs, or
compilation. The primary risk is documentation drift, mitigated by the
`test_full.sh` gate which checks documentation anchors.

### 11.3 Recommended Execution Priority

Given the risk and complexity analysis, the recommended execution order
within the parallel AI1–AI5 band is:

1. **AI4-A first** (cleanupPreReceiveDonation) — highest theorem count,
   start frame lemmas early to unblock the rest of AI4.
2. **AI3-A next** (handleYield PIP) — 15 theorems, but established pattern.
3. **AI1-A/B/C** (Rust trap fixes) — atomic, low cascade risk.
4. **AI2-A/B** (EOI + unmapPage) — moderate, localized to architecture.
5. **AI5-A/B/C** (contracts) — medium, primarily test-site updates.

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
| L-13 | LOW | Doc-only | AI6 | Binding state checked, not thread operational state |
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
| AI2 | `InterruptDispatch.lean`, `VSpaceARMv8.lean`, `AsidManager.lean`, `Suspend.lean`, `VSpaceInvariant.lean` | — | — | — |
| AI3 | `Core.lean`, `Selection.lean`, `PriorityManagement.lean`, `Preservation.lean`, `PriorityPreservation.lean`, `State.lean` | — | — | — |
| AI4 | `Transport.lean`, `Donation.lean`*, `DeviceTree.lean`, `Timeout.lean`, `EndpointPreservation.lean`, `Structural.lean`, `MainTraceHarness.lean` | — | — | — |
| AI5 | `BootContract.lean`, `Policy.lean`, `API.lean`, `MainTraceHarness.lean`, `InformationFlowSuite.lean`, `TraceSequenceProbe.lean` | — | — | — |
| AI6 | `API.lean`†, `RunQueue.lean`†, `BlockingGraph.lean`†, `BandExhaustion.lean`†, `WCRT.lean`†, `Boot.lean`†, `DeviceTree.lean`†, `MmioAdapter.lean`†, `VSpace.lean`†, `CacheModel.lean`†, `Adapter.lean`†, `Structures.lean`†, `State.lean`†, `RuntimeContract.lean`†, `SchedContext/Operations.lean`† | — | `SELE4N_SPEC.md` | — |
| AI7 | `Budget.lean`†, `Operations.lean`, fixtures | `boot.rs`, `Cargo.toml` | `CHANGELOG.md`, `WORKSTREAM_HISTORY.md`, `CLAUDE.md`, READMEs | `check_version_sync.sh` |

\* = import addition only

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
