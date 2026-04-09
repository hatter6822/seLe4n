# WS-AG Workstream Plan — H3 Hardware Binding (v0.25.27)

**Created**: 2026-04-09
**Baseline version**: 0.25.27
**Baseline audits**:
  - `docs/audits/AUDIT_v0.25.27_RELEASE_COMPREHENSIVE.md` (0 HIGH, 19 MEDIUM, 25 LOW, 3 INFO)
  - `docs/audits/AUDIT_H3_HARDWARE_BINDING_v0.25.27.md` (3 CRITICAL, 3 HIGH, 9 MEDIUM, 6 LOW)
**Prior portfolios**: WS-B through WS-AF (all COMPLETE — see `docs/WORKSTREAM_HISTORY.md`)
**Hardware target**: Raspberry Pi 5 (BCM2712, 4× Cortex-A76, GIC-400, ARM Generic Timer)
**Constraint**: Zero `sorry`/`axiom` in production proof surface

---

## 1. Executive Summary

Two independent audits of seLe4n v0.25.27 were conducted on 2026-04-08:

1. **Release Comprehensive Audit** — full codebase review (132 Lean modules,
   30 Rust files). Confirmed zero `sorry`/`axiom`/`native_decide`/`partial` in
   production code. Found 19 MEDIUM and 25 LOW findings, predominantly
   documented design decisions and known precision gaps. No critical or high
   severity issues.

2. **H3 Hardware Binding Audit** — hardware readiness assessment for Raspberry
   Pi 5 bring-up. Identified 3 CRITICAL gaps (no kernel-side HAL, restrictive-
   only proof hooks, HashMap-only VSpace), 3 HIGH gaps (no exception model, no
   multi-core model, no interrupt dispatch), and 15 MEDIUM/LOW findings across
   platform, Rust ABI, and scheduler subsystems. Catalogued 31 deferred H3 work
   items across 6 categories.

Every finding from both audits was independently verified against the source
code at claimed line references. This verification identified **2 partially
erroneous findings** (severity overstated or description inaccurate), **5
duplicate findings** (across or within audits), and **29 no-action findings**
(confirmed correct design decisions requiring no code changes). All remaining
findings were confirmed accurate and actionable.

### 1.1 Combined Finding Counts (After Verification)

| Severity | Release Audit | H3 Audit | Deduplicated | Erroneous | No-Action | Actionable |
|----------|---------------|----------|--------------|-----------|-----------|------------|
| CRITICAL | 0             | 3        | 3            | 0         | 0         | 3          |
| HIGH     | 0             | 3        | 3            | 0         | 0         | 3          |
| MEDIUM   | 19            | 9        | 25           | 1         | 14        | 10         |
| LOW      | 25            | 6        | 29           | 1         | 15        | 13         |
| INFO     | 3             | 0        | 3            | 0         | 3         | 0          |

**Actionable finding total**: 29 (after deduplication, erroneous removal, and
no-action classification). These map to **67 sub-tasks** across **10 phases**
(AG1–AG10), spanning pre-hardware code fixes, platform model completion, HAL
creation, interrupt/timer bring-up, ARMv8 memory management, FFI bridging,
model integration, testing, and documentation.

### 1.2 Plan Structure

| Phase | Focus | Sub-tasks | Key Findings Addressed | Gate |
|-------|-------|-----------|------------------------|------|
| AG1 | Pre-hardware Lean code fixes | 6 | S-04, S-05, F-T02, P-03, F-F04, T-01 | `lake build` + `test_smoke.sh` |
| AG2 | Pre-hardware Rust ABI fixes | 3 | R-05, R-01, RUST-04 | `cargo test` |
| AG3 | Platform model completion | 8 | P-01, P-04, FINDING-04/06/08, H3-ARCH-05/06/10 | `lake build` + `test_full.sh` |
| AG4 | HAL crate + boot foundation | 7 | FINDING-01, FINDING-RUST-03, H3-PLAT-04/05/06/08, H3-RUST-10 | QEMU boot to UART |
| AG5 | Interrupts + timer | 7 | FINDING-06, FINDING-08, H3-PLAT-02/03, H3-SCHED-01/02 | Timer interrupt on QEMU |
| AG6 | Memory management (ARMv8) | 9 | FINDING-03, H3-ARCH-01/02/03/04, H3-RUST-05/06 | Page table walk on QEMU |
| AG7 | FFI bridge + proof hooks | 6 | FINDING-02, P-07, H3-RUST-03/07/08, H3-PROOF-02 | Lean ↔ Rust FFI works |
| AG8 | Integration + model closure | 7 | I-01, F-S05, H3-IPC-01, H3-ARCH-07/08, H3-PROOF-03/05 | `test_full.sh` passes |
| AG9 | Testing + validation | 7 | H3-PLAT-07, H3-SCHED-03/05, H3-IPC-03, security hardening | Tests pass on hardware |
| AG10 | Documentation + closure | 7 | FINDING-05/07, doc sync, spec update | `test_full.sh` + doc sync |

**Estimated scope**: ~4,500–6,000 new lines of Lean, ~2,500–3,500 new lines of
Rust/assembly, ~500–800 lines of documentation changes.

**Decomposition depth**: 18 of the 67 sub-tasks are identified as complex
multi-step operations. Each is broken down into numbered atomic steps
(95 total atomic units) with explicit inputs, outputs, and verification
commands. This enables incremental progress tracking and reduces the risk
of partially completed sub-tasks.


---

## 2. Finding Cross-Reference and Verification

### 2.1 Erroneous / Overstated Findings

The following findings were verified against source code and found to be
partially erroneous or significantly overstated in severity:

| Finding ID | Audit | Claimed | Actual | Evidence |
|------------|-------|---------|--------|----------|
| F-T02 | Release | "Notification.waitingThreads **lacks** Nodup invariant" | `uniqueWaiters` invariant **EXISTS** at `IPC/Invariant/Defs.lean:551` with preservation proof (`notificationWait_preserves_uniqueWaiters` at Defs.lean:557). However, `uniqueWaiters` is NOT composed into `ipcInvariantFull` (Defs.lean:1084). | Finding should read: "uniqueWaiters invariant exists but is not composed into ipcInvariantFull bundle." Reclassified from "lacks invariant" to "invariant not composed." Remains actionable (compose into bundle). |
| S-04 | Release | "bucket mismatches could delay selection" (implies correctness issue) | `chooseBestRunnableEffective` (Selection.lean:346) iterates the **flat list** and resolves effective priority for every thread. `chooseBestInBucketEffective` (Selection.lean:385) uses two-stage selection: max-priority bucket first (O(k)), then full flat scan fallback (O(n)). Correctness is maintained regardless of bucket placement. | Severity overstated. The issue is: (a) misleading comment at Core.lean:573 ("effective priority" but uses `sc.priority`), (b) performance concern (PIP-boosted threads in lower buckets force Stage 2 fallback). NOT a correctness bug. Reclassified from "correctness" to "performance + documentation." Remains actionable. |

### 2.2 Duplicate Findings (Consolidated)

The following findings appear multiple times across or within the two audits.
Each group is consolidated to a single unified ID:

| Unified ID | Duplicates | Description |
|------------|------------|-------------|
| AG-PROOF-HOOKS | FINDING-02, FINDING-PLAT-02, H3-PLAT-01, H3-PROOF-01, P-07 (Release) | Production `rpi5RuntimeContract` lacks `AdapterProofHooks`. Only restrictive variant has proof hooks. 5 separate references to same gap. |
| AG-HAL | FINDING-01, FINDING-RUST-03, H3-RUST-01 through H3-RUST-08 | No kernel-side HAL / Rust code. Multiple references to same architectural gap. |
| AG-INTERRUPT | FINDING-06, parts of H3-PLAT-02, H3-PLAT-03 | No interrupt dispatch path. GIC-400 driver needed. |
| AG-TIMER | FINDING-08, H3-PLAT-03, H3-SCHED-01 | Timer model abstraction gap. ARM Generic Timer binding needed. |
| AG-VSPACE | FINDING-03, H3-ARCH-01 | VSpace HashMap-only, needs ARMv8 page table implementation. |

### 2.3 No-Action Findings (Confirmed Correct — No Code Changes)

The following findings were verified against source code and confirmed as
intentional design decisions, documented limitations, or properly handled
architectural trade-offs. No code changes required.

**Release Audit — No-Action MEDIUM:**

| ID | Title | Rationale |
|----|-------|-----------|
| F-ST02 | storeObject capacity assumption | Callers (`retypeFromUntyped`) correctly gate capacity via `storeObject_capacity_safe_of_existing` (AF2-B). |
| S-06 | WCRT externalized hypotheses | Known/tracked in AF-14. `hDomainActiveRunnable` and `hBandProgress` are environmental assumptions, not kernel invariants. |
| C-03 | seL4 divergence in traversal rights | Intentional. Operation-level enforcement sufficient since capabilities immutable during resolution. |
| C-07 | CDT acyclicity externalized | Architectural decision. Satisfied at cross-subsystem composition layer via `cdtAcyclicPreservation_*` bridge lemmas. |
| A-01 | setIPCBufferOp no W^X check | Correct by design. Operation writes to TCB `ipcBuffer` field only. W^X enforced at `mapPage` time via `mapPage_wxCompliant`. |
| IF-02 | Default labeling all-permissive | Deployment requirement. `labelingContextValid_is_deployment_requirement` witness theorem documents this. |
| IF-03 | Service orchestration outside NI | Documented boundary at `serviceOrchestrationOutsideNiBoundary`. Service registration itself has full NI proofs. |
| SA-01 | CBS 8× bandwidth precision gap | Documented in AF-08. Per-object `budgetWithinBounds` prevents actual overrun. Theoretical imprecision only. |
| SA-02 | schedContextYieldTo no cap check | Internal-only operation (not syscall entry point). Documented in AF-30/AF-47. |
| P-02 | bootFromPlatform accepts empty config | Documented in AF-44. Empty config produces valid minimal state (no userspace threads). Not a security issue. |
| P-05 | MMIO stale volatile value | Inherent limitation of pure functional modeling. Hardware provides correct volatile semantics. |
| RT-05 | Radix index collision out-of-bounds | Guarded by `buildCNodeRadixChecked` runtime validation and `UniqueRadixIndices` bridge hypothesis. |
| FO-03 | FrozenOps Phase 2 error branches | Experimental code, not in production chain. Marked `[experimental]`. |

**Release Audit — No-Action LOW:**

| ID | Title | Rationale |
|----|-------|-----------|
| F-FP05 | CNode radix UniqueRadixIndices | Satisfied for well-formed CNodes via Q4 bridge layer. |
| F-B04 | Deep tuple projections | Tracked for WS-V named-structure migration. Not blocking H3. |
| S-01 | RunQueue flat list O(n) | Acceptable for typical thread counts (<100). |
| S-02 | syncThreadStates O(n) | Idempotent post-operation step, not hot path. |
| S-03 | handleYield re-selection gap | Documented design (AF-29). Yield = "give up quantum, not time." |
| I-01 | Timeout sentinel fragility | Documented for H3 migration. Currently correct via careful ordering. |
| C-08 | cdtAcyclic structural proof | Exemplary `WellFounded` proof — no fuel needed. |
| C-14 | revokeFromSlot partial info | Fuel-bounded BFS documented in AF-07. |
| L-09 | Untyped overlap linear scan | Acceptable for small child counts per untyped region. |
| L-11 | Suspend/resume externalized | Properly managed via `SuspendPreservation.lean` transport lemmas. |
| L-15 | objectOfTypeTag zeroed fields | Gated by `lifecycleRetypeWithCleanup` well-formedness checks. |
| A-02 | 48-bit PA bound | Acceptable for RPi5 target. Cortex-A76 uses 48-bit PA. |
| A-07 | SchedContext unbounded decode | Bounds enforced downstream by CBS `admissionControl`. |
| IF-11 | Static security labels | Consistent with seL4 static information flow model. |
| P-06 | BCM2712 address constants | Validated via `decide`. Exemplary compile-time verification. |
| P-08 | Sim contracts vacuous | Intentional for test platform. Separate from production contracts. |

**Release Audit — No-Action LOW (Rust):**

| ID | Title | Rationale |
|----|-------|-----------|
| R-02 | Unsafe block correct | Exemplary `clobber_abi("C")` usage. Single `unsafe` in 30 files. |
| R-03 | Truncation guard | `UnknownKernelError` sentinel correctly handles unrecognized codes. |
| R-04 | endpoint_reply_recv truncation | `endpoint_reply_recv_checked` (AF6-B) provides strict validation. |

**Release Audit — No-Action INFO:**

| ID | Title | Rationale |
|----|-------|-----------|
| T-04 | Decoding test coverage | 40 tests for 20 decoders. Exemplary. |
| T-05 | SHA256 fixture verification | Prevents silent test weakening. Exemplary. |
| T-06 | Lean-Rust cross-validation | 5 ABI compatibility vectors. Exemplary. |

**Release Audit — No-Action LOW (Testing):**

| ID | Title | Rationale |
|----|-------|-----------|
| T-02 | Minimal test states | Adequate for current testing scope. |
| T-03 | Test targets not by default | Pre-commit hook mitigates. `defaultTargets` is intentional. |

**H3 Audit — No-Action:**

| ID | Title | Rationale |
|----|-------|-----------|
| FINDING-RUST-01 | Mock raw_syscall | Correct for non-AArch64 testing. Documented. |
| FINDING-RUST-02 | RegisterFile abstraction mismatch | Intentional. Rust `RegisterFile` (7 ABI registers: x0-x5, x7) and Lean `RegisterFile` (32 GPRs) are different abstraction levels. Trap handler (AG4-C) bridges them by extracting ABI window from saved context. |
| FINDING-07 | IPC buffer alignment 512B | Performance decision, not mismatch. 512B ≥ 8 cache lines on Cortex-A76. Proven in `ipcBuffer_within_page`. Reclassified to documentation-only (AG10). |
| FINDING-PLAT-04 | Device tree static path | Static path sufficient for RPi5 (fixed BCM2712 addresses). Runtime DTB is nice-to-have. |
| RH-02 | Robin Hood capacity | `4 ≤ capacity` enforcement (AF-U28). Appropriate. |
| RH-06 | probeChainDominant complex | ~500 lines machine-checked. No action needed. |
| RT-03 | 24 radix tree proofs | Exemplary coverage. |
| FO-05 | FrozenKernel validates-before-writes | Exemplary design. |
| SA-03 | Wildcard arm unreachable | Machine-checked unreachability (API.lean:1222-1249). |
| SA-04 | serviceHasPathTo fuel exhaustion | Conservative `true` on exhaustion prevents cycle creation. Documented AF-18. |


### 2.4 Actionable Finding Registry

All findings below are verified accurate (or partially accurate with
corrections noted) and require code, proof, or documentation changes.

#### 2.4.1 Pre-Hardware Code Fixes (Release Audit)

| Unified ID | Source | Severity | Subsystem | Description | Phase |
|------------|--------|----------|-----------|-------------|-------|
| AG-S04 | S-04 | MEDIUM (overstated) | Scheduler/CBS | 4 call sites insert threads into RunQueue at `sc.priority` (base) instead of effective priority. Comment at Core.lean:573 says "effective priority" but uses `sc.priority`. `chooseBestInBucketEffective` Stage 1 (max-bucket scan) may miss PIP-boosted threads in lower buckets, forcing O(n) fallback. Correctness maintained but performance degraded and comment misleading. | AG1 |
| AG-S05 | S-05 | MEDIUM | Scheduler | `timeoutBlockedThreads` (Core.lean:515) silently swallows `timeoutThread` errors via `.error _ => acc`. Under invariants, failures should be unreachable, but the defensive fallback masks potential violations. | AG1 |
| AG-FT02 | F-T02 | LOW (corrected) | IPC/Invariant | `uniqueWaiters` invariant exists (Defs.lean:551) with preservation proof but is NOT composed into `ipcInvariantFull` (Defs.lean:1084). Must be added to the 14-predicate IPC invariant bundle. | AG1 |
| AG-P03 | P-03 | MEDIUM | Platform/Boot | `foldIrqs` and `foldObjects` (Boot.lean:119-133) use last-wins semantics via `RHTable.insert`. `bootFromPlatformChecked` validates, but unchecked path silently loses earlier entries. | AG1 |
| AG-FF04 | F-F04 | MEDIUM | Model/Frozen | `FrozenSchedulerState` (FrozenState.lean:207-216) omits `replenishQueue`. CBS replenishment data dropped during freeze. | AG1 |
| AG-T01 | T-01 | MEDIUM | Testing | `crossSubsystemInvariant` (10 predicates) has NO runtime checks in test harness. Formal proofs cover these but runtime regression detection is absent. | AG1 |
| AG-R05 | R-05 | MEDIUM | Rust/ABI | `MAX_DOMAIN = 255` (sched_context.rs:13) but Lean `numDomainsVal = 16`. Rust accepts domain 16-255 that kernel rejects with `invalidArgument`. | AG2 |
| AG-R01 | R-01 | MEDIUM | Rust/sys | Missing `sele4n-sys/src/sched_context.rs`. ABI layer exists (`sele4n-abi/src/args/sched_context.rs`) but no typed wrappers for syscalls 17-19. | AG2 |
| AG-RUST04 | RUST-04 | MEDIUM | Rust/workspace | Workspace version 0.25.6 vs Lean 0.25.27. 21 minor versions behind. | AG2 |

#### 2.4.2 Platform Model Completion

| Unified ID | Source | Severity | Subsystem | Description | Phase |
|------------|--------|----------|-----------|-------------|-------|
| AG-P01 | P-01 | MEDIUM | Platform/DeviceTree | `classifyMemoryRegion` (DeviceTree.lean:324) unconditionally returns `.ram`. Must distinguish `.device` and `.reserved` regions before hardware boot. | AG3 |
| AG-P04 | P-04 | MEDIUM | Platform/Boot | `applyMachineConfig` (Boot.lean:278) copies only `physicalAddressWidth`. All other `MachineConfig` fields silently dropped. | AG3 |
| AG-EXCEPT | FINDING-04 | HIGH | Architecture | No exception handling model. ARM64 defines 4 exception types × 4 levels × 4 states. Model's `syscallEntry` is pure function call. | AG3 |
| AG-INTR | FINDING-06 | HIGH | Kernel/API | No `handleInterrupt` operation in API.lean. No GIC-400 acknowledge/dispatch/EOI sequence. | AG3 |
| AG-TIMER | FINDING-08 | MEDIUM | Scheduler | Timer is abstract `Nat` incremented by `timerTick`. ARM64 uses CNTPCT_EL0 (54 MHz counter). Must define mapping. | AG3 |
| AG-EL | H3-ARCH-05 | MEDIUM | Architecture | No exception level model (EL0/EL1 distinction). | AG3 |
| AG-SYSREG | H3-ARCH-06 | MEDIUM | Architecture | No system register model (ELR_EL1, ESR_EL1, SPSR_EL1, FAR_EL1). | AG3 |
| AG-VSBE | H3-ARCH-10 | LOW | Architecture | `VSpaceBackend` HashMap instance declared but not implemented (VSpaceBackend.lean:141-145). | AG3 |

#### 2.4.3 Hardware Bring-Up (New Modules)

| Unified ID | Source | Severity | Subsystem | Description | Phase |
|------------|--------|----------|-----------|-------------|-------|
| AG-HAL | FINDING-01/RUST-03 | CRITICAL | Rust/HAL | No kernel-side HAL. Must create `sele4n-hal` crate with `#![no_std]`, scoped `unsafe` blocks per hardware instruction. | AG4 |
| AG-EVEC | H3-PLAT-04/RUST-01 | CRITICAL | Rust/ASM | ARM64 exception vector table (EL1). 16 vector entries. | AG4 |
| AG-TRAP | H3-RUST-02 | CRITICAL | Rust/ASM | Trap entry/exit assembly. Save/restore 32 GPRs + system registers. | AG4 |
| AG-LINK | H3-RUST-10 | HIGH | Rust | Kernel linker script for RPi5 memory layout. | AG4 |
| AG-BOOT | H3-PLAT-08 | HIGH | Rust/ASM | Boot sequence: ATF → U-Boot → kernel entry → Lean handoff. | AG4 |
| AG-MMU | H3-PLAT-05 | CRITICAL | Rust | MMU initialization. TTBR0/TTBR1 setup, identity map → kernel map transition. | AG4 |
| AG-UART | H3-PLAT-06 | HIGH | Rust | UART PL011 driver for debug console output. | AG4 |
| AG-GIC-D | H3-PLAT-02 | CRITICAL | Rust/HAL | GIC-400 distributor initialization (GICD at 0xFF841000). | AG5 |
| AG-GIC-C | H3-PLAT-02 | CRITICAL | Rust/HAL | GIC-400 CPU interface initialization (GICC at 0xFF842000). | AG5 |
| AG-GIC-IRQ | H3-RUST-04 | CRITICAL | Rust/HAL | GIC-400 IRQ acknowledge (GICC_IAR) → dispatch → EOI (GICC_EOIR). | AG5 |
| AG-GTIMER | H3-PLAT-03 | CRITICAL | Rust/HAL | ARM Generic Timer driver (CNTPCT_EL0, CNTP_CVAL_EL0, CNTP_CTL_EL0). | AG5 |
| AG-TICK | H3-SCHED-01 | HIGH | Scheduler | Timer interrupt → `timerTick` binding. Map hardware counter to model. | AG5 |
| AG-HIRQ | FINDING-06 | HIGH | Kernel/API | `handleInterrupt` kernel integration (interrupt dispatch path). | AG5 |
| AG-IDIS | H3-SCHED-02 | HIGH | Kernel | Interrupt-disabled region enforcement for atomicity. | AG5 |
| AG-PTFMT | H3-ARCH-01/FINDING-03 | CRITICAL | Architecture | ARMv8 4-level page table descriptor format (L0-L3). | AG6 |
| AG-PTWALK | H3-ARCH-01 | CRITICAL | Architecture | 4-level page table walk implementation. | AG6 |
| AG-VSARM | FINDING-03 | CRITICAL | Architecture | `VSpaceBackend` ARMv8 instance. Prove refinement of HashMap model. | AG6 |
| AG-TTBR | FINDING-03 | CRITICAL | Architecture | TTBR0/TTBR1 switching for process isolation. | AG6 |
| AG-TLBI | H3-ARCH-02/RUST-05 | HIGH | Rust/HAL | TLB flush instruction wrappers (TLBI VMALLE1, TLBI VAE1). | AG6 |
| AG-TLBINT | H3-ARCH-02 | HIGH | Architecture | Targeted TLB flush integration with existing TlbModel.lean. | AG6 |
| AG-ISB | H3-ARCH-03 | HIGH | Architecture | ISB after TLBI instructions per ARM ARM requirement. | AG6 |
| AG-ASID | H3-ARCH-04 | HIGH | Architecture | ASID generation, allocation, and rollover handling. | AG6 |
| AG-CACHE | H3-RUST-06 | HIGH | Rust/HAL | Cache maintenance operations (DC CIVAC, IC IALLU, DC ZVA). | AG6 |

#### 2.4.4 FFI Bridge + Proof Closure

| Unified ID | Source | Severity | Subsystem | Description | Phase |
|------------|--------|----------|-----------|-------------|-------|
| AG-FFI | H3-RUST-03 | CRITICAL | Rust/Lean | Lean → Rust FFI bridge for hardware operations. `extern "C"` callable from Lean compiled code. | AG7 |
| AG-MSRMSR | H3-RUST-07 | HIGH | Rust/HAL | System register accessor wrappers (MRS/MSR for SCTLR_EL1, TCR_EL1, MAIR_EL1, etc.). | AG7 |
| AG-MMIO | H3-RUST-08 | HIGH | Rust/HAL | MMIO volatile read/write primitives bridging model to hardware. | AG7 |
| AG-PHOOKS | FINDING-02 (unified) | CRITICAL | Platform/Proof | Production `AdapterProofHooks` for `rpi5RuntimeContract`. Context-switch preservation via `contextSwitchState_preserves_contextMatchesCurrent`. | AG7 |
| AG-TLBPF | H3-PROOF-02 | HIGH | Architecture/Proof | Targeted TLB flush composition theorems binding hardware TLBI to model `adapterFlushTlbByAsid`/`adapterFlushTlbByVAddr`. | AG7 |
| AG-CSPROOF | New | HIGH | Platform/Proof | Context switch proof hooks for production contract. Prove `adapterContextSwitch` (X1-F) preserves `registerContextStablePred`. | AG7 |

#### 2.4.5 Integration + Model Closure

| Unified ID | Source | Severity | Subsystem | Description | Phase |
|------------|--------|----------|-----------|-------------|-------|
| AG-TIMEOUT | H3-IPC-01/I-01 | HIGH | IPC/Timeout | Migrate timeout sentinel (`0xFFFFFFFF` in x0) to explicit `timedOut : Bool` TCB field. | AG8 |
| AG-DCACHE | H3-ARCH-07 | MEDIUM | Architecture | Cache coherency model (D-cache / I-cache interaction). | AG8 |
| AG-BARRIER | H3-ARCH-08 | MEDIUM | Architecture | Memory barrier semantics model (DMB/DSB/ISB — already modeled in MmioAdapter, needs formalization). | AG8 |
| AG-FROZEN | H3-PROOF-05 | MEDIUM | FrozenOps | Production integration decision: promote to production or permanently mark experimental. | AG8 |
| AG-DESC | F-S05 | MEDIUM | Model/State | `descendantsOf` fuel sufficiency. Now unblocked by H3 CDT depth bounds. | AG8 |
| AG-DONATE | H3-PROOF-03 | MEDIUM | IPC/Invariant | Donation chain k>2 cycle prevention formalization. Current proof covers 2-cycle only. | AG8 |
| AG-ATOMDON | H3-IPC-04 | MEDIUM | IPC/Donation | Atomicity of donation under interrupt-disabled proof obligation. | AG8 |

#### 2.4.6 Testing + Validation

| Unified ID | Source | Severity | Subsystem | Description | Phase |
|------------|--------|----------|-----------|-------------|-------|
| AG-QEMU | New | HIGH | Testing | QEMU integration testing (raspi4b machine, closest to RPi5). | AG9 |
| AG-HWCHECK | H3-PLAT-07 | HIGH | Platform | Live hardware constant cross-check (BCM2712 addresses vs actual RPi5). | AG9 |
| AG-WCRT | H3-SCHED-05 | LOW | Scheduler | WCRT empirical validation on Cortex-A76. | AG9 |
| AG-RQPERF | H3-SCHED-03 | MEDIUM | Scheduler | Run queue cache performance validation on ARM64. | AG9 |
| AG-BADGE | H3-IPC-03 | LOW | IPC | Badge overflow hardware behavior validation (Nat → u64 roundtrip). | AG9 |
| AG-SPECTRE | New | MEDIUM | Security | Speculation barriers (CSDB) after capability address masking, run queue indexing, page table walk. Cortex-A76 Spectre v1/v2 mitigations. | AG9 |
| AG-HWTEST | New | HIGH | Testing | Full test suite execution on RPi5 hardware. | AG9 |

#### 2.4.7 Documentation

| Unified ID | Source | Severity | Subsystem | Description | Phase |
|------------|--------|----------|-----------|-------------|-------|
| AG-SMP | FINDING-05 | HIGH | Documentation | Multi-core limitation documentation. RPi5 has 4 cores; H3 is single-core only. SMP deferred to WS-V. | AG10 |
| AG-IPCBUF | FINDING-07 | MEDIUM | Documentation | IPC buffer 512B alignment rationale and hardware cache behavior documentation. | AG10 |
| AG-SPEC | New | HIGH | Documentation | SELE4N_SPEC.md update for H3 hardware binding architecture. | AG10 |
| AG-MAP | New | MEDIUM | Documentation | `docs/codebase_map.json` regeneration for new modules. | AG10 |
| AG-WSHIST | New | MEDIUM | Documentation | WORKSTREAM_HISTORY.md update for WS-AG. | AG10 |
| AG-CLOG | New | MEDIUM | Documentation | CHANGELOG.md entries for H3 phases. | AG10 |
| AG-README | New | LOW | Documentation | README.md metrics sync (new module counts, Rust crate counts). | AG10 |


---

## 3. Detailed Phase Specifications

### Phase AG1 — Pre-Hardware Lean Code Fixes (COMPLETE, v0.26.0)

**Goal**: Fix verified Lean-side code issues from the release audit before
beginning hardware work. Establishes a clean baseline.

**Dependencies**: None (first phase).
**Gate**: `source ~/.elan/env && lake build` + `./scripts/test_smoke.sh` — **PASSED**
**Estimated scope**: ~200–300 lines of Lean changes.

#### AG1-A: CBS Re-enqueue at Effective Priority (S-04)

**Finding**: 4 call sites insert threads into RunQueue at `sc.priority` (base
SchedContext priority) instead of effective priority (base + PIP boost). The
comment at `Scheduler/Operations/Core.lean:573` explicitly says "effective
priority" but the code uses `sc.priority`.

**Verification note**: This is NOT a correctness bug.
`chooseBestRunnableEffective` (Selection.lean:346) correctly resolves effective
priority during selection via `resolveEffectivePrioDeadline`, so the best thread
is always chosen regardless of bucket placement. However, incorrect bucket
placement forces `chooseBestInBucketEffective` Stage 1 (max-bucket O(k) scan)
to miss PIP-boosted threads, falling back to the O(n) flat scan unnecessarily.

**Steps** (6 atomic units):

1. **AG1-A-i: Helper function.** Create a helper
   `resolveInsertPriority (st : SystemState) (tid : ThreadId) (sc : SchedContext) : Priority`
   that calls `resolveEffectivePrioDeadline` on the thread's TCB and returns
   the effective priority. If the TCB lookup fails (invariant violation), fall
   back to `sc.priority`. Place in `Selection.lean` alongside the existing
   `resolveEffectivePrioDeadline`. Build: `lake build SeLe4n.Kernel.Scheduler.Operations.Selection`.

2. **AG1-A-ii: Fix `processReplenishmentsDue` (Core.lean:~460).** Replace
   `sc.priority` with `resolveInsertPriority st tid sc` in the RunQueue
   insertion call. Fix the surrounding comment to say "effective priority
   (base + PIP boost)". Build: `lake build SeLe4n.Kernel.Scheduler.Operations.Core`.

3. **AG1-A-iii: Fix `timerTickBudget` (Core.lean:~576).** Same replacement.
   Fix the misleading comment at line 573 from "Re-enqueue current thread
   at its effective priority" to accurately describe the new behavior. Build
   the module.

4. **AG1-A-iv: Fix `handleYieldWithBudget` (Core.lean:~700).** Same
   replacement. Build the module.

5. **AG1-A-v: Fix `schedContextYieldTo` (SchedContext/Operations.lean:~277).**
   Replace `targetSc.priority` with `resolveInsertPriority st2 tid targetSc`.
   Build: `lake build SeLe4n.Kernel.SchedContext.Operations`.

6. **AG1-A-vi: Verify preservation theorems.** Run
   `lake build SeLe4n.Kernel.Scheduler.Operations.Preservation` and
   `lake build SeLe4n.Kernel.SchedContext.Invariant.Preservation`. The theorems
   are parameterized over the inserted priority value, so no proof changes
   should be needed. If a theorem does break, the fix is to generalize the
   priority parameter. Run `./scripts/test_smoke.sh` as final gate.

#### AG1-B: timeoutBlockedThreads Diagnostic Handling (S-05)

**Finding**: `timeoutBlockedThreads` (Core.lean:515) silently swallows errors
from `timeoutThread` via `.error _ => acc`. Under well-formed invariants,
`timeoutThread` failures should be unreachable, but silent swallowing masks
potential invariant violations.

**Changes**:
1. Change the fold to collect error information rather than silently dropping
   it. Return a pair `(SystemState × List (ThreadId × KernelError))` from the
   fold, accumulating any errors encountered.
2. The caller `timerTickBudget` can then log/surface these via the existing
   `KernelError` return channel if any errors were collected.
3. Add a comment documenting that under `crossSubsystemInvariant`, the error
   list should always be empty — any non-empty result indicates an invariant
   violation that warrants investigation.

**Module verification**: `lake build SeLe4n.Kernel.Scheduler.Operations.Core`.

#### AG1-C: Compose uniqueWaiters into ipcInvariantFull (F-T02)

**Finding**: The `uniqueWaiters` invariant definition exists at
`IPC/Invariant/Defs.lean:551` with a preservation proof
(`notificationWait_preserves_uniqueWaiters` at line 557). However, it is NOT
composed into `ipcInvariantFull` (Defs.lean:1084), meaning it is not checked
as part of the system-wide invariant bundle.

**Steps** (7 atomic units):

1. **AG1-C-i: Add conjunct to `ipcInvariantFull`.** Add `uniqueWaiters st`
   as the 15th conjunct in `ipcInvariantFull` (Defs.lean:1084). This will
   immediately break all `ipcInvariantFull` preservation theorems — expected.
   Build: `lake build SeLe4n.Kernel.IPC.Invariant.Defs` (definition only).

2. **AG1-C-ii: Frame lemmas for non-notification operations.** Operations
   that do NOT modify `Notification.waitingThreads` get trivial frame lemmas:
   `endpointSend`, `endpointReceive`, `endpointReplyRecv`, `capTransfer`,
   `donation`, and all scheduler/capability operations. These pass
   `uniqueWaiters` through unchanged. Target files:
   `EndpointPreservation.lean`, `CallReplyRecv.lean`.

3. **AG1-C-iii: `notificationWait` preservation.** Wire the existing
   `notificationWait_preserves_uniqueWaiters` (Defs.lean:557) into the
   `ipcInvariantFull` preservation proof for `notificationWait`. The existing
   proof uses `notificationWaiterConsistent` to check TCB `ipcState` before
   prepending — verify this bridging invariant is already part of
   `ipcInvariantFull` or add it.

4. **AG1-C-iv: `notificationSignal` preservation.** `notificationSignal`
   clears `waitingThreads` entirely (replaces with empty list or pops head).
   `[].Nodup` is trivially true. `(hd :: tl).Nodup` follows from the
   pre-signal `uniqueWaiters` guarantee (sublist of Nodup is Nodup). Add
   preservation lemma in `NotificationPreservation.lean`.

5. **AG1-C-v: `notificationCancel` / lifecycle cleanup preservation.** Thread
   removal via `List.filter` preserves `Nodup` (standard library lemma
   `List.Nodup.filter`). Add preservation lemma for notification cleanup
   paths in `NotificationPreservation.lean`.

6. **AG1-C-vi: Cross-subsystem composition.** Update
   `crossSubsystemInvariant` bridge lemmas (33 per-operation lemmas in
   `CrossSubsystem.lean`) to thread `uniqueWaiters` through. Since
   `uniqueWaiters` is now part of `ipcInvariantFull`, the existing
   cross-subsystem framework should propagate it automatically — verify.
   Build: `lake build SeLe4n.Kernel.CrossSubsystem`.

7. **AG1-C-vii: Full suite verification.** Run
   `lake build SeLe4n.Kernel.IPC.Invariant.Defs` and all IPC invariant
   submodules. Run `./scripts/test_full.sh` to verify no regressions.

#### AG1-D: Boot Duplicate Detection Warning (P-03)

**Finding**: `foldIrqs` and `foldObjects` (Boot.lean:119-133) use last-wins
semantics via `RHTable.insert`. The checked variant (`bootFromPlatformChecked`)
validates, but the unchecked `bootFromPlatform` silently loses earlier entries
on duplicate keys.

**Changes**:
1. Add a `bootFromPlatformWithWarnings` variant that detects duplicates and
   returns a list of warnings alongside the `IntermediateState`. This provides
   a middle ground between the silent `bootFromPlatform` and the rejecting
   `bootFromPlatformChecked`.
2. Update `bootFromPlatform` documentation to explicitly warn about last-wins
   semantics and recommend `bootFromPlatformChecked` for production use.
3. No changes to the unchecked path itself — it remains available for testing
   and backwards compatibility.

**Module verification**: `lake build SeLe4n.Platform.Boot`.

#### AG1-E: FrozenSchedulerState replenishQueue (F-F04)

**Finding**: `FrozenSchedulerState` (FrozenState.lean:207-216) omits
`replenishQueue`, dropping CBS replenishment data during freeze. The frozen
execution phase cannot support CBS scheduling without this field.

**Changes**:
1. Add `replenishQueue : FrozenReplenishQueue` field to
   `FrozenSchedulerState` (define `FrozenReplenishQueue` as an immutable
   sorted list of `(Nat × SchedContextId)` pairs, mirroring the runtime
   `ReplenishQueue` structure).
2. Update `freezeScheduler` to copy `replenishQueue` into the frozen
   representation.
3. Add freeze-correctness proof: lookup equivalence between runtime and
   frozen replenishment queues (mirroring existing `FreezeProofs.lean` pattern).
4. Update FrozenOps if they reference scheduler state to account for the
   new field.

**Module verification**: `lake build SeLe4n.Model.FrozenState` and
`lake build SeLe4n.Model.FreezeProofs`.

#### AG1-F: Runtime crossSubsystemInvariant Checks (T-01)

**Finding**: `crossSubsystemInvariant` (10 predicates, CrossSubsystem.lean:295)
has NO runtime checks in the test harness. Formal proofs cover these but runtime
regression detection is absent.

**Steps** (5 atomic units):

1. **AG1-F-i: Object-store consistency checks (predicates 1–2).** Implement
   decidable boolean versions of `noStaleEndpointQueueReferences` and
   `noStaleNotificationWaitReferences` in `InvariantChecks.lean`. Both iterate
   over endpoint/notification objects and check that every ThreadId in their
   queues has a corresponding TCB in `objects`. Build:
   `lake build SeLe4n.Testing.InvariantChecks`.

2. **AG1-F-ii: Service + SchedContext checks (predicates 3–7).** Implement
   `registryDependencyConsistent`, `serviceGraphInvariant`,
   `schedContextStoreConsistent`, `schedContextNotDualBound`,
   `schedContextRunQueueConsistent`. These check service registry edges,
   dependency acyclicity (bounded depth-first walk), SchedContext store
   existence, single-binding, and budget positivity for runnable threads. Build.

3. **AG1-F-iii: Registry + blocking checks (predicates 8–10).** Implement
   `registryEndpointUnique`, `registryInterfaceValid`, `blockingAcyclic`.
   `blockingAcyclic` is the most complex — implement via bounded
   cycle-detection walk (fuel = `objects.size`). Build.

4. **AG1-F-iv: Compose and integrate.** Create
   `checkCrossSubsystemInvariant : SystemState → Bool` that runs all 10
   checks and returns `true` only if all pass. Add calls at 3–5 key points
   in `MainTraceHarness.lean`: after initial boot, after IPC chain, after
   scheduler operations, after capability operations, and after lifecycle
   operations. Build: `lake build SeLe4n.Testing.MainTraceHarness`.

5. **AG1-F-v: Fixture update.** Run `lake exe sele4n` and compare output
   against `tests/fixtures/main_trace_smoke.expected`. If trace output
   changed (new invariant check lines), update the fixture file and its
   SHA256 hash in `test_tier2_trace.sh`. Run `./scripts/test_smoke.sh`.


---

### Phase AG2 — Pre-Hardware Rust ABI Fixes (COMPLETE, v0.26.1)

**Goal**: Fix verified Rust ABI issues from the release audit. Ensures the
user-space ABI layer is correct before building kernel-side Rust code.

**Dependencies**: None (independent of AG1, can run in parallel).
**Gate**: `cd rust && cargo test --workspace` + `cargo clippy --workspace` — **PASSED** (239 tests, 0 warnings)
**Estimated scope**: ~150–200 lines of Rust changes.
**Actual scope**: ~190 lines of Rust changes + 4 conformance tests + documentation sync.

#### AG2-A: MAX_DOMAIN Constant Fix (R-05)

**Finding**: `MAX_DOMAIN = 255` in `sele4n-abi/src/args/sched_context.rs:13`
but Lean kernel enforces `domain < numDomainsVal` where `numDomainsVal = 16`
(SchedContext/Operations.lean:43). Rust accepts domain values 16-255 that the
kernel will reject with `invalidArgument`.

**Changes**:
1. Change `pub const MAX_DOMAIN: u64 = 255` to `pub const MAX_DOMAIN: u64 = 15`
   in `sele4n-abi/src/args/sched_context.rs`.
2. Add a comment: `// Matches Lean numDomainsVal = 16, zero-indexed (0..=15)`.
3. Verify that `SchedContextConfigureArgs::decode()` validation at line 26
   (`if domain > MAX_DOMAIN`) correctly rejects domain >= 16.
4. Add a conformance test in `sele4n-abi/tests/conformance.rs` verifying
   domain 15 accepted and domain 16 rejected.

#### AG2-B: SchedContext Typed Wrappers (R-01)

**Finding**: `sele4n-sys` provides typed wrappers for 22 of 25 syscalls. The 3
SchedContext syscalls (configure=17, bind=18, unbind=19) have no wrapper. The
ABI encoding layer exists in `sele4n-abi/src/args/sched_context.rs`.

**Changes**:
1. Create `rust/sele4n-sys/src/sched_context.rs` with:
   - `pub fn sched_context_configure(cap: Cap<SchedContext>, budget: u64, period: u64, extra_refills: u64, badge: u64, domain: u64) -> Result<(), KernelError>`
   - `pub fn sched_context_bind(cap: Cap<SchedContext>, thread: Cap<Tcb>) -> Result<(), KernelError>`
   - `pub fn sched_context_unbind(cap: Cap<SchedContext>) -> Result<(), KernelError>`
2. Register the module in `sele4n-sys/src/lib.rs`.
3. Each wrapper follows the existing pattern: encode args → `raw_syscall` →
   decode result.
4. Add unit tests for each wrapper.

#### AG2-C: Workspace Version Sync (RUST-04)

**Finding**: Rust workspace version is `0.25.6` (Cargo.toml:10) while Lean
project is at `0.25.27`. 21 minor versions behind.

**Changes**:
1. Update `rust/Cargo.toml` workspace `version` field to match the current
   Lean version at time of implementation.
2. Update individual crate `Cargo.toml` files if they override the workspace
   version.
3. Add a comment in `rust/Cargo.toml` noting that version should track the
   Lean `lakefile.toml` version.

---

### Phase AG3 — Platform Model Completion (COMPLETE, v0.26.4)

**Goal**: Complete Lean model gaps that block hardware bring-up. All changes
are pure Lean — no hardware code yet.

**Dependencies**: AG1 (clean baseline). AG2 independent.
**Gate**: `source ~/.elan/env && lake build` + `./scripts/test_full.sh` — **PASSED**
**Estimated scope**: ~600–900 lines of new Lean code.
**Completion**: All 8 sub-tasks (AG3-A through AG3-H) complete. Zero sorry/axiom.
3 new files created, 3 existing files extended. Full build + test_full.sh pass.

#### AG3-A: classifyMemoryRegion Implementation (P-01)

**Finding**: `classifyMemoryRegion` (DeviceTree.lean:324) unconditionally
returns `.ram`. Must distinguish `.device` and `.reserved` for hardware boot.

**Changes**:
1. Implement `classifyMemoryRegion` to classify based on address ranges:
   - Addresses within the memory map's RAM regions → `.ram`
   - Addresses within declared peripheral/MMIO regions → `.device`
   - All other addresses → `.reserved`
2. Accept a `MachineConfig` (or `List MemoryRegion`) parameter providing the
   platform memory map for classification.
3. Add tests in a new `DeviceTreeSuite.lean` or extend existing test harness.
4. Verify that RPi5 `rpi5MachineConfig` memory map correctly classifies:
   - 0x00000000–0xFC000000 as `.ram`
   - 0xFE000000–0xFF850000 as `.device`
   - 0xFC000000–0xFE000000 as `.reserved` (GPU)

**Module verification**: `lake build SeLe4n.Platform.DeviceTree`.

#### AG3-B: applyMachineConfig Full Field Application (P-04)

**Finding**: `applyMachineConfig` (Boot.lean:278) copies only
`physicalAddressWidth`. Other `MachineConfig` fields silently dropped.

**Changes**:
1. Extend `applyMachineConfig` to copy all relevant `MachineConfig` fields:
   - `registerWidth` → `machine.registerWidth`
   - `virtualAddressWidth` → `machine.virtualAddressWidth` (if field exists)
   - `pageSize` → `machine.pageSize`
   - `maxASID` → `machine.maxASID` (if field exists)
   - `memoryMap` → `machine.memoryMap`
   - `registerCount` → `machine.registerCount`
2. Thread the `IntermediateState` invariant witnesses through the extended
   copy (the additional fields are metadata, so existing witnesses should
   transfer directly).
3. Update the comment at Boot.lean:276 to reflect full field application.

**Module verification**: `lake build SeLe4n.Platform.Boot`.

#### AG3-C: Exception Model (FINDING-04)

**Finding**: No concept of ARM64 exceptions in the model. The kernel's
`syscallEntry` is a pure function call, not a trap handler. ARM64 defines
4 exception types × 4 execution states = 16 vector entries.

**Steps** (6 atomic units):

1. **AG3-C-i: Core type definitions.** Create
   `SeLe4n/Kernel/Architecture/ExceptionModel.lean` with the skeleton:
   imports, namespace, and four inductive types — `ExceptionType`
   (`synchronous | irq | fiq | serror`), `ExceptionSource`
   (`currentElSp0 | currentElSpX | lowerElAArch64 | lowerElAArch32`),
   `SynchronousExceptionClass` (`svc | dataAbort | instrAbort | pcAlignment |
   spAlignment | unknownReason`), and the `ExceptionContext` structure
   (`esr elr spsr far : UInt64`). Derive `DecidableEq`, `Repr` for all.
   Build: `lake build SeLe4n.Kernel.Architecture.ExceptionModel`.

2. **AG3-C-ii: ESR classification function.** Implement
   `classifySynchronousException : ExceptionContext → SynchronousExceptionClass`.
   Extract EC field: `(ectx.esr >>> 26) &&& 0x3F`. Map EC values:
   `0x15 → svc` (SVC from AArch64), `0x24/0x25 → dataAbort`,
   `0x20/0x21 → instrAbort`, `0x22 → pcAlignment`, `0x26 → spAlignment`,
   `_ → unknownReason`. Add `decide` proof that classification is total. Build.

3. **AG3-C-iii: Exception dispatch function.** Implement
   `dispatchException : ExceptionType → ExceptionContext → SystemState →
   Except KernelError SystemState`. Route: `synchronous` → call
   `dispatchSynchronousException` (below); `irq` → placeholder returning
   `.error .notImplemented` (wired in AG3-D); `fiq` → `.error .notSupported`;
   `serror` → `.error .hardwareFault`. Build.

4. **AG3-C-iv: Synchronous exception dispatch.** Implement
   `dispatchSynchronousException : ExceptionContext → SystemState →
   Except KernelError SystemState`. Classify via `classifySynchronousException`,
   then route: `svc` → extract syscall ID from `ectx.esr &&& 0xFFFF` and call
   existing `syscallDispatch`; `dataAbort` → `.error .vmFault`;
   `instrAbort` → `.error .vmFault`; others → `.error .userException`. Build.

5. **AG3-C-v: Wire SVC to existing syscallDispatch.** Import the existing
   `syscallDispatch` from `API.lean` and call it from the `svc` branch. Verify
   that the register extraction (`esr &&& 0xFFFF` for syscall immediate) matches
   the existing syscall ID encoding. Build.

6. **AG3-C-vi: Preservation theorem.** Prove
   `dispatchException_preserves_invariant`: for each exception type, the
   dispatch function preserves `proofLayerInvariantBundle`. The `svc` case
   delegates to existing `syscallDispatch` preservation. The `irq` case will
   be completed in AG5-F. The error-returning cases (`fiq`, `serror`)
   trivially preserve invariants (state unchanged on error). Build and run
   `./scripts/test_smoke.sh`.

**Module verification**: `lake build SeLe4n.Kernel.Architecture.ExceptionModel`.

#### AG3-D: Interrupt Dispatch Model (FINDING-06)

**Finding**: No `handleInterrupt` operation in `API.lean`. No interrupt dispatch
path exists in the kernel model.

**Steps** (6 atomic units):

1. **AG3-D-i: Types and constants.** Create
   `SeLe4n/Kernel/Architecture/InterruptDispatch.lean` with: `InterruptId`
   as a bounded Nat (`Fin 224` for GIC-400 INTIDs 0–223),
   `timerInterruptId : InterruptId := ⟨30, by omega⟩` (non-secure physical
   timer PPI), `spuriousInterruptId : Nat := 1023`. Build.

2. **AG3-D-ii: Acknowledge and EOI operations.** Implement
   `acknowledgeInterrupt : SystemState → Except KernelError (SystemState × Option InterruptId)` —
   returns `none` for spurious interrupts (INTID >= 1020).
   `endOfInterrupt : SystemState → InterruptId → SystemState` — models
   GICC_EOIR write. Both are pure state transformations at this level (the
   actual MMIO is in the HAL layer). Build.

3. **AG3-D-iii: Interrupt handler dispatch.** Implement
   `handleInterrupt : SystemState → InterruptId → Except KernelError SystemState`.
   Three cases: (a) `interruptId = timerInterruptId` → call
   `timerTickEffective`; (b) IRQ table lookup `st.irqTable[interruptId]?` →
   if `some handlerId`, deliver notification via `notificationSignal`;
   (c) unmapped IRQ → `.error .invalidIrq`. Build.

4. **AG3-D-iv: Full dispatch sequence.** Implement
   `interruptDispatchSequence : SystemState → Except KernelError SystemState`
   composing: `acknowledgeInterrupt` → match on `some intId` →
   `handleInterrupt intId` → `endOfInterrupt intId`. Spurious interrupts
   (`none`) return the state unchanged. Build.

5. **AG3-D-v: Wire into ExceptionModel.** Update the `irq` branch of
   `dispatchException` (AG3-C-iii) to call `interruptDispatchSequence`
   instead of returning `.error .notImplemented`. Build both modules.

6. **AG3-D-vi: Preservation theorem.** Prove
   `interruptDispatchSequence_preserves_invariant`. The timer path delegates
   to existing `timerTickEffective` preservation. The notification path
   delegates to existing `notificationSignal` preservation. The unmapped-IRQ
   path returns error (state unchanged). Build and run `./scripts/test_smoke.sh`.

**Module verification**: `lake build SeLe4n.Kernel.Architecture.InterruptDispatch`.

#### AG3-E: Timer Model Binding (FINDING-08)

**Finding**: Timer is abstract `Nat` incremented by `timerTick`. ARM64 uses
CNTPCT_EL0 (physical counter, 54 MHz on RPi5), CNTP_CVAL_EL0 (comparator).

**Changes**:
1. In `Machine.lean` or a new `SeLe4n/Kernel/Architecture/TimerModel.lean`:
   - Define `HardwareTimerConfig` structure: `counterFrequencyHz : Nat`,
     `tickIntervalNs : Nat`, `comparatorValue : Nat`
   - Define `hardwareTimerToModelTick : HardwareTimerConfig → Nat → Nat` that
     converts a hardware counter value to the model's abstract tick count
   - Define `reprogram_comparator : HardwareTimerConfig → Nat → HardwareTimerConfig`
     that sets the next comparator value for the desired tick rate
2. Prove `hardwareTimerToModelTick` is monotonically increasing (follows from
   hardware counter monotonicity, which is a `RuntimeBoundaryContract` predicate).
3. Wire into the RPi5 platform: `rpi5TimerConfig` with
   `counterFrequencyHz := 54000000`.
4. Document the mapping: one model `timerTick` = one timer interrupt = one
   comparator match event.

**Module verification**: `lake build SeLe4n.Kernel.Architecture.TimerModel`.

#### AG3-F: Exception Level Model (H3-ARCH-05)

**Finding**: No distinction between EL0 (user) and EL1 (kernel) in the model.
ARM64 enforces privilege separation via AP bits, PXN/UXN bits, and system
register access controls.

**Changes**:
1. In `ExceptionModel.lean` (created in AG3-C), add:
   - `ExceptionLevel` inductive: `el0 | el1` (EL2/EL3 out of scope for H3)
   - `currentExceptionLevel : SystemState → ExceptionLevel`
   - Privilege predicates: `canAccessSystemRegisters`, `canExecutePrivileged`
   - Update `dispatchException` to check `ExceptionSource` and set the
     appropriate exception level on entry/exit
2. Add to VSpace model: page table AP (Access Permission) bits that distinguish
   kernel-only vs user-accessible pages.
3. Theorem: user-mode (EL0) cannot access kernel-mapped pages.

**Module verification**: `lake build SeLe4n.Kernel.Architecture.ExceptionModel`.

#### AG3-G: System Register Model (H3-ARCH-06)

**Finding**: No model of ARM64 system registers (ELR_EL1, ESR_EL1, SPSR_EL1,
FAR_EL1) used during exception handling.

**Steps** (4 atomic units):

1. **AG3-G-i: SystemRegisterFile structure.** Create a new `SystemRegisterFile`
   structure in `Machine.lean` with fields: `elr_el1`, `esr_el1`, `spsr_el1`,
   `far_el1` (exception registers), `sctlr_el1`, `tcr_el1`, `ttbr0_el1`,
   `ttbr1_el1`, `mair_el1`, `vbar_el1` (configuration registers). All
   `UInt64`. Derive `DecidableEq`, `Repr`. Default values: all zero. Build:
   `lake build SeLe4n.Machine`.

2. **AG3-G-ii: Integrate into MachineState.** Add
   `systemRegisters : SystemRegisterFile := default` to `MachineState`.
   This preserves backward compatibility (existing code that doesn't reference
   system registers is unaffected). Fix any build breaks in files that
   pattern-match on `MachineState` (likely `Adapter.lean`,
   `RuntimeContract.lean`). Build: `lake build SeLe4n.Machine` and dependent modules.

3. **AG3-G-iii: Read/write operations.** Add `readSystemRegister` and
   `writeSystemRegister` operations that project into / update the
   `systemRegisters` field. Add an `ExceptionLevel` guard: system register
   writes require `currentExceptionLevel = .el1` (from AG3-F). Build.

4. **AG3-G-iv: Frame lemmas.** Prove 3 frame lemmas:
   (a) `writeSystemRegister_preserves_objects`: system register writes don't
   modify `objects`, `irqTable`, or `scheduler`;
   (b) `writeSystemRegister_preserves_registerFile`: system register writes
   don't modify GPR `RegisterFile`;
   (c) `writeSystemRegister_preserves_memory`: system register writes don't
   modify `Memory`. Build and run `./scripts/test_smoke.sh`.

**Module verification**: `lake build SeLe4n.Machine`.

#### AG3-H: VSpaceBackend HashMap Instance (H3-ARCH-10)

**Finding**: `VSpaceBackend` HashMap instance is declared but not implemented
at `VSpaceBackend.lean:141-145`. The file ends with just the section comment.

**Changes**:
1. Implement `hashMapVSpaceBackend : VSpaceBackend HashMapVSpace` providing
   all typeclass methods:
   - `mapPage`, `unmapPage`, `lookupPage`, `isPageMapped`
   - These should delegate to the existing `VSpace.lean` HashMap operations
2. Prove all `VSpaceBackend` typeclass laws hold for the HashMap implementation.
3. This instance serves as the specification against which the ARMv8 instance
   (AG6) will be proven to refine.

**Module verification**: `lake build SeLe4n.Kernel.Architecture.VSpaceBackend`.


---

### Phase AG4 — HAL Crate + Boot Foundation (COMPLETE, v0.26.5)

**Goal**: Create the kernel-side Rust/assembly infrastructure for Raspberry Pi 5.
This is the first phase producing hardware-executable code.

**Dependencies**: AG2 (Rust ABI clean), AG3 (exception/interrupt models defined).
**Gate**: `cargo test --workspace` (239 tests) + `cargo clippy --workspace` (0 warnings) + `lake build` + `test_smoke.sh` — **PASSED**
**Estimated scope**: ~800–1,200 lines of Rust + ~300 lines of assembly.
**Actual scope**: ~900 lines of Rust + ~300 lines of assembly + linker script.
**Completion**: All 7 sub-tasks (AG4-A through AG4-G) complete. New `sele4n-hal`
crate (4th workspace crate). Zero sorry/axiom. All 267 Rust tests pass, 0 clippy
warnings. Full Lean build + test_smoke.sh pass.

#### AG4-A: sele4n-hal Crate Skeleton (FINDING-01/RUST-03)

**Finding**: The entire Rust layer is user-space facing. No kernel-side code
exists for executing hardware instructions.

**Changes**:
1. Create `rust/sele4n-hal/` directory with:
   - `Cargo.toml`: `#![no_std]`, workspace member, `edition = "2021"`,
     `#![deny(unsafe_code)]` at crate level (individual modules opt in with
     `#[allow(unsafe_code)]`)
   - `src/lib.rs`: Module declarations
   - `src/cpu.rs`: CPU instruction wrappers (WFE, WFI, NOP, ERET)
   - `src/barriers.rs`: Memory barrier wrappers (DMB, DSB, ISB)
   - `src/registers.rs`: System register accessors (MRS/MSR macros)
   - `src/gic.rs`: GIC-400 driver (AG5)
   - `src/timer.rs`: ARM Generic Timer (AG5)
   - `src/mmu.rs`: MMU configuration (AG6)
   - `src/uart.rs`: PL011 UART driver (AG4-G)
2. Each `unsafe` block must have a `// SAFETY:` comment referencing the
   relevant ARM Architecture Reference Manual section.
3. Add `sele4n-hal` to `rust/Cargo.toml` workspace members.

#### AG4-B: ARM64 Exception Vector Table (H3-PLAT-04/RUST-01)

**Finding**: ARM64 requires a 2048-byte aligned exception vector table at
VBAR_EL1 with 16 entries (4 exception types × 4 source states), each 128
bytes (32 instructions).

**Changes**:
1. Create `rust/sele4n-hal/src/vectors.S` (assembly):
   - `.balign 2048` for VBAR alignment
   - 16 vector entries, each `.balign 128`
   - Current EL with SP0: 4 entries (sync, IRQ, FIQ, SError)
   - Current EL with SPx: 4 entries (sync → `el1_sync_handler`,
     IRQ → `el1_irq_handler`, FIQ → stub, SError → `el1_serror_handler`)
   - Lower EL AArch64: 4 entries (sync → `el0_sync_handler`,
     IRQ → `el0_irq_handler`, FIQ → stub, SError → stub)
   - Lower EL AArch32: 4 entries (all stubs — not supported)
2. Each entry saves minimal context and branches to the corresponding
   Rust handler function.
3. Register the vector table via MSR VBAR_EL1 during boot (AG4-E).

#### AG4-C: Trap Entry/Exit Assembly (H3-RUST-02)

**Finding**: Trap handler must save full 32-GPR context plus system registers
on kernel stack, extract syscall parameters, call into kernel, and restore
context on return.

**Steps** (5 atomic units):

1. **AG4-C-i: Context frame structure.** Define `TrapFrame` in
   `rust/sele4n-hal/src/trap.rs` as a `#[repr(C)]` struct holding:
   `gprs: [u64; 31]` (x0-x30), `sp_el0: u64`, `elr_el1: u64`,
   `spsr_el1: u64`. Total: 34 × 8 = 272 bytes. Add `impl TrapFrame` with
   accessors for the 7-register ABI window (`x0()..x5()`, `x7()`).

2. **AG4-C-ii: save_context / restore_context assembly macros.** In
   `rust/sele4n-hal/src/trap.S`:
   - `save_context`: `sub sp, sp, #272` → `stp x0, x1, [sp, #0]` through
     `stp x28, x29, [sp, #224]` → `str x30, [sp, #240]` → `mrs x0, SP_EL0;
     str x0, [sp, #248]` → `mrs x0, ELR_EL1; str x0, [sp, #256]` →
     `mrs x0, SPSR_EL1; str x0, [sp, #264]`.
   - `restore_context`: reverse order → `ldr x0, [sp, #264]; msr SPSR_EL1, x0`
     → restore ELR, SP_EL0 → `ldp` all GPRs → `add sp, sp, #272` → `eret`.

3. **AG4-C-iii: EL0 sync handler assembly.** `el0_sync_handler`:
   `save_context` → `mov x0, sp` (pass TrapFrame pointer as first arg) →
   `bl handle_synchronous_exception` → `restore_context`. This calls the
   Rust function with the full saved context.

4. **AG4-C-iv: Rust handler — SVC dispatch.** Implement
   `#[no_mangle] extern "C" fn handle_synchronous_exception(frame: &mut TrapFrame)`:
   - Read ESR_EL1 (already saved in frame)
   - Extract EC field: `(frame.esr >> 26) & 0x3F`
   - If `EC == 0x15` (SVC from AArch64): extract ABI registers
     `(x0..x5, x7)` → call Lean kernel dispatch via FFI → write results
     back to `frame.gprs[0..5]`
   - Other ECs: set error code in `frame.gprs[0]`

5. **AG4-C-v: EL0/EL1 IRQ handler assembly.** `el0_irq_handler` and
   `el1_irq_handler`: `save_context` → `mov x0, sp` →
   `bl handle_irq` (Rust, calls GIC acknowledge/dispatch/EOI from AG5-C) →
   `restore_context`. Implement `#[no_mangle] extern "C" fn handle_irq(frame: &mut TrapFrame)`
   as a stub initially (UART print + return). Wire to GIC in AG5.

#### AG4-D: Kernel Linker Script (H3-RUST-10)

**Finding**: Need a linker script defining the RPi5 kernel memory layout.

**Changes**:
1. Create `rust/sele4n-hal/link.ld`:
   - Kernel load address: 0x80000 (standard RPi5 kernel load point)
   - `.text.boot` section at load address (entry point)
   - `.text` section for kernel code
   - `.rodata` for read-only data
   - `.data` for initialized data
   - `.bss` for uninitialized data (with `__bss_start` / `__bss_end` symbols)
   - Kernel stack at end of BSS (16-byte aligned, 64 KiB)
   - Page table region after stack
2. Add `MEMORY` block with RPi5 memory layout:
   - RAM: 0x00000000 – 0xFC000000
   - Peripherals: 0xFE000000 – 0xFF850000

#### AG4-E: Boot Sequence (H3-PLAT-08)

**Finding**: Real boot requires ATF/U-Boot handoff, BSS zeroing, stack setup,
MMU init, and handoff to Lean kernel.

**Steps** (6 atomic units):

1. **AG4-E-i: Assembly entry point.** Create `rust/sele4n-hal/src/boot.S`
   with `_start` at link address 0x80000. Read MPIDR_EL1 to get core ID
   (`mrs x1, mpidr_el1; and x1, x1, #0xFF`). If not core 0, branch to
   `secondary_spin` (`wfe; b secondary_spin`). Save DTB pointer (x0) to a
   callee-saved register (x19).

2. **AG4-E-ii: BSS zeroing.** Zero the BSS region: load `__bss_start` and
   `__bss_end` symbols → loop storing zeros (use `stp xzr, xzr, [x0], #16`
   for 16-byte strides). This ensures all static variables start at zero.

3. **AG4-E-iii: Stack setup.** Load the stack top symbol from the linker
   script (`ldr x0, =__stack_top`) → `mov sp, x0`. Ensure 16-byte alignment
   (`and sp, sp, #~0xF`). Branch to `rust_boot_main` with DTB pointer as
   first argument (`mov x0, x19; bl rust_boot_main`).

4. **AG4-E-iv: Rust boot — early init.** Create `rust/sele4n-hal/src/boot.rs`
   with `#[no_mangle] extern "C" fn rust_boot_main(dtb_ptr: u64) -> !`.
   Phase 1: Initialize UART (AG4-G `init_uart(0xFE201000)`) → print
   `"seLe4n v0.26.5 booting on RPi5\r\n"`. Store DTB pointer for future use.

5. **AG4-E-v: Rust boot — hardware init.** Phase 2 of `rust_boot_main`:
   Initialize MMU (AG4-F `init_mmu()`) → set VBAR_EL1 to exception vector
   table (AG4-B: `write_sysreg!("vbar_el1", vectors_base)`) → DSB + ISB.
   Print `"MMU enabled, VBAR set\r\n"`.

6. **AG4-E-vi: Rust boot — handoff to Lean.** Phase 3 of `rust_boot_main`:
   GIC and timer are initialized later (AG5), so for now print
   `"Boot complete, entering kernel\r\n"` → call Lean `kernel_main()` via
   FFI (AG7-A). If `kernel_main` returns (it shouldn't), enter infinite
   `wfe` loop. The AG4 gate test verifies UART output reaches this point.

#### AG4-F: MMU Initialization (H3-PLAT-05)

**Finding**: MMU must be configured with identity mapping for boot, then
transitioned to kernel mapping with TTBR0 (user) / TTBR1 (kernel) split.

**Steps** (6 atomic units):

1. **AG4-F-i: Page table memory reservation.** In the linker script (AG4-D),
   reserve a 64 KiB aligned region for initial boot page tables
   (`.section .bss.page_tables, "aw", @nobits; .balign 4096`). This provides
   space for: 1 L0 table (4 KiB) + 4 L1 tables (16 KiB) = 20 KiB minimum.
   Export symbol `__page_tables_start`.

2. **AG4-F-ii: MAIR_EL1 configuration.** In `rust/sele4n-hal/src/mmu.rs`,
   implement `configure_mair()`: set MAIR_EL1 with attribute indices:
   - Index 0 (`0xFF`): Normal memory, Inner/Outer Write-Back Non-transient,
     Read-Allocate, Write-Allocate
   - Index 1 (`0x00`): Device-nGnRnE (strongly ordered device memory)
   - Index 2 (`0x44`): Normal Non-cacheable (for DMA if needed later)

3. **AG4-F-iii: TCR_EL1 configuration.** Implement `configure_tcr()`:
   - T0SZ = 16 (48-bit VA for TTBR0, user space)
   - T1SZ = 16 (48-bit VA for TTBR1, kernel space)
   - TG0 = 0b00 (4 KiB granule for TTBR0)
   - TG1 = 0b10 (4 KiB granule for TTBR1)
   - IPS = 0b100 (44-bit PA, matching BCM2712)
   - SH0/SH1 = 0b11 (Inner Shareable)
   - ORGN0/ORGN1 = 0b01, IRGN0/IRGN1 = 0b01 (Write-Back cacheable)

4. **AG4-F-iv: Identity-mapped L0/L1 page tables.** Implement
   `build_identity_tables()`: populate boot page tables at `__page_tables_start`:
   - L0[0] → L1 table address (table descriptor)
   - L1[0..3] → 4 × 1 GiB block descriptors for RAM (0x00000000–0xFC000000):
     Normal memory, AF=1, SH=Inner Shareable, AttrIndx=0
   - L1[3] (0xC0000000–0xFFFFFFFF) split: L1[3] → L2 table for fine-grained
     device mapping, OR use block descriptor with Device-nGnRnE for
     0xFE000000–0xFF850000 region
   - Simpler approach for H3: L1[0..3] = Normal RAM blocks,
     L1[3] = Device block for 0xC0000000-0xFFFFFFFF with AttrIndx=1.
     Refine in AG6 with 4 KiB pages.

5. **AG4-F-v: TTBR setup and MMU enable.** Implement `enable_mmu()`:
   - Write TTBR0_EL1 = L0 table physical address
   - Write TTBR1_EL1 = L0 table physical address (same for identity map)
   - DSB ISH (ensure page table writes are visible)
   - ISB (synchronize context)
   - Read SCTLR_EL1, set M bit (bit 0), set C bit (bit 2, data cache),
     set I bit (bit 12, instruction cache)
   - Write SCTLR_EL1
   - ISB (synchronize after MMU enable)

6. **AG4-F-vi: `init_mmu()` orchestrator.** Compose the above into
   `pub fn init_mmu()`: `configure_mair()` → `configure_tcr()` →
   `build_identity_tables()` → `enable_mmu()`. Add a post-MMU-enable
   verification: read a known RAM address and verify it returns expected
   value (smoke test that the identity map works). Print "MMU enabled" via
   UART.

#### AG4-G: UART PL011 Driver (H3-PLAT-06)

**Finding**: Debug console output needed for boot diagnostics.

**Changes**:
1. In `rust/sele4n-hal/src/uart.rs`:
   - PL011 register offsets: UARTDR (0x000), UARTFR (0x018), UARTIBRD (0x024),
     UARTFBRD (0x028), UARTLCR_H (0x02C), UARTCR (0x030)
   - `init_uart(base: usize)`: Configure baud rate (115200), 8N1, enable TX/RX
   - `uart_putc(base: usize, c: u8)`: Poll UARTFR.TXFF, write UARTDR
   - `uart_puts(base: usize, s: &[u8])`: Output string
   - `uart_getc(base: usize) -> Option<u8>`: Non-blocking receive
2. Base address: 0xFE201000 (BCM2712 UART0, from Board.lean validation).
3. Baud rate divisor calculation for 48 MHz UART clock (RPi5).

---

### Phase AG5 — Interrupts + Timer ✅ COMPLETE (v0.27.0)

**Goal**: GIC-400 interrupt controller and ARM Generic Timer bring-up.
Connects hardware interrupts to the Lean kernel model.

**Dependencies**: AG4 (HAL crate, UART for debugging, VBAR set).
**Gate**: Timer interrupt fires on QEMU, GIC routing demonstrated, `timerTick`
called from hardware interrupt path.
**Estimated scope**: ~500–700 lines of Rust, ~200–300 lines of Lean.

#### AG5-A: GIC-400 Distributor Initialization (H3-PLAT-02)

**Changes**:
1. In `rust/sele4n-hal/src/gic.rs`:
   - `init_distributor(base: usize)`:
     - Write GICD_CTLR = 0 (disable distributor)
     - Configure GICD_IGROUPR: all interrupts Group 0 (for IRQ delivery)
     - Set GICD_IPRIORITYR: default priority 0xA0 for all
     - Set GICD_ITARGETSR: route all SPIs to CPU 0
     - Clear all pending: write 0xFFFFFFFF to all GICD_ICPENDR
     - Enable all: write 0xFFFFFFFF to all GICD_ISENABLER
     - Write GICD_CTLR = 1 (enable distributor)
   - GIC-400 base: 0xFF841000 (from Board.lean)
   - SPI count: 192 (INTIDs 32-223, from `rpi5InterruptContract`)

#### AG5-B: GIC-400 CPU Interface Initialization (H3-PLAT-02)

**Changes**:
1. In `rust/sele4n-hal/src/gic.rs`:
   - `init_cpu_interface(base: usize)`:
     - Write GICC_PMR = 0xFF (lowest priority mask — accept all)
     - Write GICC_BPR = 0 (no priority grouping)
     - Write GICC_CTLR = 1 (enable CPU interface)
   - GIC-400 CPU interface base: 0xFF842000 (from Board.lean)

#### AG5-C: GIC-400 IRQ Acknowledge/Dispatch/EOI (H3-RUST-04)

**Changes**:
1. In `rust/sele4n-hal/src/gic.rs`:
   - `acknowledge_irq(base: usize) -> u32`: Read GICC_IAR, return INTID
   - `end_of_interrupt(base: usize, intid: u32)`: Write GICC_EOIR
   - `is_spurious(intid: u32) -> bool`: Check INTID >= 1020
   - `handle_irq()`: acknowledge → check spurious → dispatch to handler
     table → EOI. This is the function called from `el0_irq_handler` and
     `el1_irq_handler` assembly stubs (AG4-B).
2. Handler table: static array of function pointers indexed by INTID.
   Timer interrupt (INTID 30) → call into Lean `timerTick` via FFI.

#### AG5-D: ARM Generic Timer Driver (H3-PLAT-03)

**Changes**:
1. In `rust/sele4n-hal/src/timer.rs`:
   - `read_counter() -> u64`: MRS CNTPCT_EL0
   - `read_frequency() -> u32`: MRS CNTFRQ_EL0
   - `set_comparator(value: u64)`: MSR CNTP_CVAL_EL0
   - `enable_timer()`: MSR CNTP_CTL_EL0 = 1 (ENABLE=1, IMASK=0)
   - `disable_timer()`: MSR CNTP_CTL_EL0 = 0
   - `is_timer_pending() -> bool`: Read CNTP_CTL_EL0.ISTATUS
   - `init_timer(tick_hz: u32)`: Calculate interval =
     `counter_frequency / tick_hz`, set first comparator, enable
   - `reprogram_timer()`: Read current counter, set comparator =
     counter + interval
2. RPi5 counter frequency: 54 MHz (from Board.lean `timerFrequencyHz`).
3. Default tick rate: 1000 Hz (1ms ticks) — configurable.

#### AG5-E: Timer Interrupt → timerTick Binding (H3-SCHED-01)

**Changes**:
1. In the GIC IRQ handler (AG5-C), when INTID 30 (timer PPI) fires:
   - Call `reprogram_timer()` to set next comparator
   - Call into Lean kernel `timerTick` via FFI bridge (AG7-A)
   - The FFI bridge translates the `SystemState` through the Lean
     `timerTickEffective` function
2. In `SeLe4n/Kernel/Architecture/TimerModel.lean` (AG3-E), add:
   - `timerInterruptHandler : SystemState → Except KernelError SystemState`
     that composes: acknowledge timer → `timerTickEffective` → reprogram
   - Preservation theorem: timer interrupt preserves all kernel invariants
     (follows from existing `timerTick` preservation proofs)

#### AG5-F: handleInterrupt Kernel Integration (FINDING-06)

**Changes**:
1. In `API.lean`, add `KernelOperation.handleInterrupt` to the dispatch table.
2. Wire the interrupt dispatch sequence (AG3-D) into the main kernel API:
   - `handleInterrupt intId st` looks up the registered handler for `intId`
   - If timer interrupt → `timerTickEffective`
   - If device interrupt → deliver notification to registered handler
   - Return updated `SystemState`
3. Add `handleInterrupt` to the 34-constructor `KernelOperation` enum
   (becomes 35).
4. Add NI proof for `handleInterrupt` (interrupt delivery is a notification
   signal — reuse existing `notificationSignal_NI` proof).
5. Add cross-subsystem bridge lemma for `handleInterrupt`.

**Steps** (5 atomic units):

1. **AG5-F-i: KernelOperation constructor.** In `API.lean`, add
   `handleInterrupt : InterruptId → KernelOperation` to the inductive
   (becomes 35th constructor). Add the `| .handleInterrupt intId =>` match
   arm in `dispatchKernelOperation` that calls `handleInterruptOp intId st`.

2. **AG5-F-ii: Core dispatch function.** In a new section of
   `Kernel/Architecture/Adapter.lean` (or a dedicated
   `Kernel/Architecture/InterruptDispatch.lean`), define:
   `handleInterruptOp (intId : InterruptId) (st : SystemState) : KernelResult Unit`:
   - Read `st.interruptTable` to look up handler for `intId`
   - If `intId = timerInterruptId` → call `timerTickEffective st` (AG5-D)
   - If device interrupt → call `notificationSignalOp` on the registered
     notification endpoint
   - If no handler registered → return `.ok ()` (spurious interrupt)

3. **AG5-F-iii: Timer path integration.** Wire the timer tick case to call
   `timerTickEffective` (which wraps `timerTick` + CBS replenishment from
   AG5-D). Verify the return type aligns with `KernelResult Unit`.

4. **AG5-F-iv: NI proof.** In `InformationFlow/Invariant/Operations.lean`,
   add `handleInterrupt_NI` proof. Timer tick is domain-local (affects only
   current domain's budget). Device notification reuses
   `notificationSignal_NI`. Structure: case split on interrupt type, delegate
   to existing sub-proofs.

5. **AG5-F-v: Cross-subsystem bridge lemma.** In `CrossSubsystem.lean`, add
   `handleInterrupt_preserves_crossSubsystemInvariant` following the pattern
   of the existing 33 per-operation bridge lemmas. Timer tick path delegates
   to `timerTick_preserves_*`; notification path delegates to
   `notificationSignal_preserves_*`.

#### AG5-G: Interrupt-Disabled Region Enforcement (H3-SCHED-02)

**Changes**:
1. In the HAL layer, define `with_interrupts_disabled<F, R>(f: F) -> R`:
   - Save DAIF flags (MRS DAIF)
   - MSR DAIFSet, #0xF (mask all interrupts)
   - Execute `f()`
   - Restore DAIF (MSR DAIF, saved)
2. In the Lean model, add `InterruptState` to `MachineState`:
   - `interruptsEnabled : Bool`
   - `disableInterrupts`, `enableInterrupts`, `withInterruptsDisabled`
3. Document which kernel operations require interrupts disabled:
   - Scheduler transitions (schedule, handleYield, timerTick)
   - IPC operations that modify endpoint queues
   - PIP propagation
4. Theorem: kernel operations executed with interrupts disabled are atomic
   with respect to interrupt delivery.

**Steps** (4 atomic units):

1. **AG5-G-i: Rust HAL critical section primitive.** In
   `rust/sele4n-hal/src/interrupts.rs`, implement
   `pub fn with_interrupts_disabled<F: FnOnce() -> R, R>(f: F) -> R`:
   - `let saved = read_sysreg!(DAIF);` — save current DAIF state
   - `asm!("msr DAIFSet, #0xF")` — mask all interrupt types (D, A, I, F)
   - `let result = f();` — execute the critical section
   - `write_sysreg!(DAIF, saved);` — restore original DAIF (not just enable,
     to handle nested cases correctly)
   - Return `result`. Also provide `disable_interrupts()` / `enable_interrupts()`
     for the FFI bridge (AG7-A).

2. **AG5-G-ii: Lean interrupt state model.** In `Machine.lean`, add
   `interruptsEnabled : Bool := true` field to `MachineState`. Define:
   - `disableInterrupts (ms : MachineState) : MachineState :=
     { ms with interruptsEnabled := false }`
   - `enableInterrupts (ms : MachineState) : MachineState :=
     { ms with interruptsEnabled := true }`
   - `withInterruptsDisabled (f : MachineState → MachineState) (ms : MachineState) :
     MachineState := enableInterrupts (f (disableInterrupts ms))`
   Update the `MachineState` `BEq` instance to include `interruptsEnabled`.

3. **AG5-G-iii: Critical section annotation.** In `API.lean`, annotate
   `dispatchKernelOperation` to model the entry-from-exception pattern:
   the kernel is always entered via exception (SVC/IRQ) which arrives with
   interrupts masked (PSTATE.I set by hardware on exception entry). Add a
   docstring documenting which operations require interrupts disabled
   throughout, vs. which can re-enable interrupts during execution:
   - **Always disabled**: scheduler transitions, PIP propagation,
     endpoint queue mutations, donation chain operations
   - **Can re-enable**: long-running operations (future, none currently)

4. **AG5-G-iv: Atomicity theorem.** Define
   `interruptDisabledAtomicity : ∀ op st, st.machine.interruptsEnabled = false →
   dispatchKernelOperation op st = .ok (r, st') →
   st'.machine.interruptsEnabled = false`
   — kernel operations preserve interrupt-disabled state. Proof: structural
   case split on all 35 `KernelOperation` constructors, verifying none toggle
   `interruptsEnabled`. This is the Lean-side guarantee that pairs with the
   hardware DAIF masking.


---

### Phase AG6 — Memory Management (ARMv8 Page Tables)

**Goal**: Implement hardware page tables for ARMv8, proving they refine the
existing HashMap VSpace model. This preserves all existing VSpace proofs while
adding hardware-specific implementation.

**Dependencies**: AG4 (MMU init with block descriptors), AG3-H (HashMap instance).
**Gate**: Fine-grained 4KB page table walk on QEMU + TLB flush demonstrated.
**Estimated scope**: ~800–1,100 lines of Lean, ~300–400 lines of Rust.

#### AG6-A: ARMv8 Page Table Descriptor Format (H3-ARCH-01/FINDING-03)

**Changes**:
1. Create `SeLe4n/Kernel/Architecture/PageTable.lean` with:
   - `PageTableLevel` inductive: `l0 | l1 | l2 | l3`
   - `PageTableDescriptor` inductive:
     - `invalid` — Bits [1:0] = 0b00
     - `block (outputAddr : PAddr) (attrs : PageAttributes)` — L1/L2 only
     - `table (nextTableAddr : PAddr)` — L0/L1/L2 only
     - `page (outputAddr : PAddr) (attrs : PageAttributes)` — L3 only
   - `PageAttributes` structure:
     - `attrIndex : Fin 8` — MAIR index
     - `ap : AccessPermission` — EL0/EL1 access (AP[2:1])
     - `sh : Shareability` — Inner/Outer/Non-shareable
     - `af : Bool` — Access Flag
     - `pxn : Bool` — Privileged Execute Never
     - `uxn : Bool` — Unprivileged Execute Never
     - `contiguous : Bool` — Contiguous hint
     - `dirty : Bool` — DBM dirty bit
   - `AccessPermission` inductive: `rwEL1 | rwAll | roEL1 | roAll`
   - Encode/decode functions: `descriptorToUInt64`, `uint64ToDescriptor`
2. Prove encode/decode roundtrip: `uint64ToDescriptor (descriptorToUInt64 d) = d`.
3. Prove W^X enforcement: if `uxn = false` or `pxn = false` (executable),
   then AP must be `roEL1` or `roAll` (read-only). This extends the existing
   `mapPage_wxCompliant` theorem to hardware descriptors.

**Module verification**: `lake build SeLe4n.Kernel.Architecture.PageTable`.

**Steps** (5 atomic units):

1. **AG6-A-i: Type definitions.** Create
   `SeLe4n/Kernel/Architecture/PageTable.lean` with imports from `Prelude`
   and `Machine`. Define `PageTableLevel` inductive (`l0 | l1 | l2 | l3`),
   `Shareability` inductive (`nonShareable | outerShareable | innerShareable`),
   `AccessPermission` inductive (`rwEL1 | rwAll | roEL1 | roAll`), and
   `PageAttributes` structure (8 fields: `attrIndex`, `ap`, `sh`, `af`,
   `pxn`, `uxn`, `contiguous`, `dirty`). Derive `BEq`, `Repr` for all.

2. **AG6-A-ii: Descriptor inductive.** Define `PageTableDescriptor`:
   `invalid | block (outputAddr : PAddr) (attrs : PageAttributes) |
   table (nextTableAddr : PAddr) | page (outputAddr : PAddr) (attrs : PageAttributes)`.
   Add `levelValid : PageTableLevel → PageTableDescriptor → Bool` enforcing
   block only at L1/L2, table only at L0/L1/L2, page only at L3.

3. **AG6-A-iii: Encode function.** Implement
   `descriptorToUInt64 : PageTableDescriptor → UInt64` using ARMv8 bit layout:
   - `invalid`: `0`
   - `table`: `nextTableAddr ||| 0b11` (bits [1:0] = 0b11, bit [1] = table)
   - `block`: `outputAddr ||| attrs_encoded ||| 0b01` (bits [1:0] = 0b01)
   - `page`: `outputAddr ||| attrs_encoded ||| 0b11` (L3 page, bits [1:0] = 0b11)
   Helper `encodePageAttributes : PageAttributes → UInt64` packs AP into
   bits [7:6], SH into bits [9:8], AF into bit [10], PXN into bit [53],
   UXN into bit [54], etc.

4. **AG6-A-iv: Decode function + roundtrip.** Implement
   `uint64ToDescriptor : UInt64 → PageTableLevel → PageTableDescriptor`
   (needs level to distinguish block vs table vs page). Prove roundtrip:
   `uint64ToDescriptor (descriptorToUInt64 d) level = d` for all
   `levelValid level d = true`. Proof by cases on `d`.

5. **AG6-A-v: W^X enforcement theorem.** Define
   `descriptorWxCompliant : PageTableDescriptor → Prop` asserting that
   executable descriptors (¬pxn ∨ ¬uxn) have read-only AP. Prove
   `hwDescriptor_wxCompliant : ∀ d, descriptorWxCompliant d →
   mapPage_wxCompliant (toVSpaceMapping d)` bridging hardware descriptors
   to the existing VSpace W^X theorem.

#### AG6-B: 4-Level Page Table Walk (H3-ARCH-01)

**Changes**:
1. In `PageTable.lean`, implement:
   - `pageTableWalk : Memory → PAddr → VAddr → Option (PAddr × PageAttributes)`
     - Extract L0 index: VA[47:39] (9 bits, 512 entries)
     - Read L0 descriptor from `ttbr + L0_index * 8`
     - If `table`: extract L1 table address, continue
     - Extract L1 index: VA[38:30]
     - If `block`: return 1GB block mapping (L1 block)
     - If `table`: extract L2 table address, continue
     - Extract L2 index: VA[29:21]
     - If `block`: return 2MB block mapping (L2 block)
     - If `table`: extract L3 table address, continue
     - Extract L3 index: VA[20:12]
     - If `page`: return 4KB page mapping
     - Otherwise: `none` (translation fault)
2. Prove determinism: `pageTableWalk` is a total function.
3. Prove that the walk terminates (structural recursion on 4 levels).

**Module verification**: `lake build SeLe4n.Kernel.Architecture.PageTable`.

**Steps** (5 atomic units):

1. **AG6-B-i: Index extraction helpers.** In `PageTable.lean`, define
   pure bit-extraction functions:
   - `l0Index (va : VAddr) : Fin 512 := ⟨(va.toNat >>> 39) &&& 0x1FF, ...⟩`
   - `l1Index (va : VAddr) : Fin 512 := ⟨(va.toNat >>> 30) &&& 0x1FF, ...⟩`
   - `l2Index (va : VAddr) : Fin 512 := ⟨(va.toNat >>> 21) &&& 0x1FF, ...⟩`
   - `l3Index (va : VAddr) : Fin 512 := ⟨(va.toNat >>> 12) &&& 0x1FF, ...⟩`
   - `pageOffset (va : VAddr) : Fin 4096 := ⟨va.toNat &&& 0xFFF, ...⟩`
   Prove each produces a value within `Fin` bounds (shift+mask guarantees).

2. **AG6-B-ii: Memory read helper.** Define
   `readDescriptor (mem : Memory) (tableBase : PAddr) (index : Fin 512) :
   PageTableDescriptor` that reads 8 bytes from
   `tableBase + index.val * 8`, assembles a `UInt64`, and calls
   `uint64ToDescriptor` (from AG6-A-iv) at the appropriate level.

3. **AG6-B-iii: Walk function (structural recursion).** Define
   `pageTableWalk` using explicit 4-step unfolding (NOT fuel-based):
   ```
   def pageTableWalk (mem : Memory) (ttbr : PAddr) (va : VAddr)
       : Option (PAddr × PageAttributes) :=
     let d0 := readDescriptor mem ttbr (l0Index va) .l0
     match d0 with
     | .table l1base =>
       let d1 := readDescriptor mem l1base (l1Index va) .l1
       match d1 with
       | .block addr attrs => some (addr + blockOffset1G va, attrs)
       | .table l2base =>
         let d2 := readDescriptor mem l2base (l2Index va) .l2
         match d2 with
         | .block addr attrs => some (addr + blockOffset2M va, attrs)
         | .table l3base =>
           let d3 := readDescriptor mem l3base (l3Index va) .l3
           match d3 with
           | .page addr attrs => some (addr + pageOffset va, attrs)
           | _ => none
         | _ => none
       | _ => none
     | _ => none
   ```
   This is structurally terminating (no recursion, 4 nested matches).

4. **AG6-B-iv: Determinism proof.** Prove `pageTableWalk_deterministic`:
   `∀ mem ttbr va, ∃! result, pageTableWalk mem ttbr va = result`.
   Trivially holds because `pageTableWalk` is a total function (all
   `match` arms covered). Lean's definitional equality makes this `rfl`.

5. **AG6-B-v: Block offset helpers.** Define
   `blockOffset1G (va : VAddr) : PAddr` extracting bits [29:0],
   `blockOffset2M (va : VAddr) : PAddr` extracting bits [20:0].
   Prove: `pageOffset va + pageBase = fullAddr` for the 4KB case,
   and similarly for 2MB/1GB block mappings. These are used in the
   refinement proof (AG6-D) to show walk output matches HashMap lookup.

#### AG6-C: VSpaceBackend ARMv8 Instance (FINDING-03)

**Changes**:
1. Create `SeLe4n/Kernel/Architecture/VSpaceARMv8.lean`:
   - `ARMv8VSpace` structure wrapping the page table root PAddr and a
     `Memory` region containing page table pages
   - Implement `VSpaceBackend ARMv8VSpace`:
     - `mapPage`: Allocate page table pages as needed, write descriptors
     - `unmapPage`: Clear descriptor, invalidate TLB entry
     - `lookupPage`: `pageTableWalk` from AG6-B
     - `isPageMapped`: `pageTableWalk` returns `some`
2. Key challenge: page table page allocation requires a page allocator.
   For H3, use a simple bump allocator for page table pages from a
   reserved memory region.

**Module verification**: `lake build SeLe4n.Kernel.Architecture.VSpaceARMv8`.

**Steps** (5 atomic units):

1. **AG6-C-i: ARMv8VSpace structure.** Create
   `SeLe4n/Kernel/Architecture/VSpaceARMv8.lean`. Define:
   `structure ARMv8VSpace where ttbr : PAddr; pageTableMemory : Memory;
   allocator : BumpAllocator; asid : ASID`.
   `structure BumpAllocator where nextPage : PAddr; endPage : PAddr`.
   `allocatePageTablePage : BumpAllocator → Option (BumpAllocator × PAddr)` —
   returns `none` if `nextPage ≥ endPage`, otherwise returns next 4KB-aligned
   page and advances `nextPage` by 4096.

2. **AG6-C-ii: lookupPage + isPageMapped.** Implement the read-only
   `VSpaceBackend` operations first:
   - `lookupPage (vs : ARMv8VSpace) (va : VAddr) :=
     pageTableWalk vs.pageTableMemory vs.ttbr va`
   - `isPageMapped (vs : ARMv8VSpace) (va : VAddr) :=
     (lookupPage vs va).isSome`
   These delegate directly to the walk function from AG6-B.

3. **AG6-C-iii: mapPage with table creation.** Implement `mapPage`:
   Walk from L0 to L3, creating intermediate table pages on demand:
   - At each level, `readDescriptor` the current entry
   - If `invalid` and not at L3: allocate a new page table page (bump
     allocator), zero it, write a `table` descriptor pointing to it
   - At L3: write a `page` descriptor with the given attributes
   - Return updated `ARMv8VSpace` (updated memory + allocator state)
   - Return `none` if allocator exhausted (out of page table pages)

4. **AG6-C-iv: unmapPage.** Implement `unmapPage`:
   Walk to L3 entry for the given VA. If the entry is `page`, overwrite
   with `invalid` descriptor. Do NOT free the page table page (reclamation
   is a future optimization). Return updated `ARMv8VSpace`. Note: TLB
   invalidation is handled by the caller (`vspaceUnmapPageWithFlush`).

5. **AG6-C-v: VSpaceBackend instance.** Assemble the `instance :
   VSpaceBackend ARMv8VSpace` providing all 4 operations. Verify the
   instance matches the typeclass signature from `VSpaceBackend.lean`.
   Add a brief smoke check: `#check (inferInstance : VSpaceBackend ARMv8VSpace)`.

#### AG6-D: ARMv8 Refinement Proof (FINDING-03)

**Changes**:
1. Prove that `VSpaceBackend ARMv8VSpace` refines `VSpaceBackend HashMapVSpace`:
   - For any well-formed ARMv8 page table, there exists a HashMap that produces
     the same results for all operations
   - `armv8_refines_hashmap : ∀ vspace op, armv8Backend.apply op vspace =
     hashMapBackend.apply op (toHashMap vspace)`
2. This refinement proof ensures all existing VSpace invariant proofs
   (VSpaceInvariant.lean, 7-predicate composition) transfer to hardware.
3. The proof will be structured as a simulation relation.

**Module verification**: `lake build SeLe4n.Kernel.Architecture.VSpaceARMv8`.

**Steps** (5 atomic units):

1. **AG6-D-i: toHashMap extraction function.** Define
   `toHashMap : ARMv8VSpace → HashMap VAddr (PAddr × PageAttributes)` that
   enumerates all L3 page entries and L1/L2 block entries from the page
   table tree, collecting valid mappings into a HashMap. Use
   `List.foldl` over the 512 entries at each level (no fuel — bounded
   by 512⁴ worst case, but practically structured iteration).

2. **AG6-D-ii: Simulation relation.** Define
   `simulationRelation (hw : ARMv8VSpace) (sw : HashMapVSpace) : Prop :=
   ∀ va, lookupPage hw va = HashMap.find? sw.mappings va`.
   This is the core abstraction relation that all operation refinement
   proofs will maintain.

3. **AG6-D-iii: Lookup refinement.** Prove
   `lookupPage_refines : simulationRelation hw sw →
   lookupPage hw va = lookupPage sw va`.
   This follows directly from the simulation relation definition and
   the fact that both backends' `lookupPage` delegates to their respective
   lookup mechanisms.

4. **AG6-D-iv: Map/unmap refinement.** Prove:
   - `mapPage_refines : simulationRelation hw sw →
     mapPage hw va pa attrs = some hw' →
     simulationRelation hw' (mapPage sw va pa attrs)`
   - `unmapPage_refines : simulationRelation hw sw →
     unmapPage hw va = hw' →
     simulationRelation hw' (unmapPage sw va)`
   Each proof shows that writing/clearing a descriptor in the page table
   produces the same effect as inserting/erasing in the HashMap.

5. **AG6-D-v: Invariant transfer theorem.** Prove the master transfer:
   `vspaceInvariant_transfer : simulationRelation hw sw →
   vspaceInvariantFull sw → vspaceInvariantFull hw`.
   This lifts all 7 predicates of the VSpace invariant from the HashMap
   model to the hardware page table model. The proof delegates each
   predicate through the simulation relation.

#### AG6-E: TLB Flush Instruction Wrappers (H3-ARCH-02/RUST-05)

**Changes**:
1. In `rust/sele4n-hal/src/cpu.rs` or `src/mmu.rs`:
   - `tlbi_vmalle1()`: `TLBI VMALLE1` — flush all TLB entries at EL1
   - `tlbi_vae1(vaddr: u64)`: `TLBI VAE1, Xt` — flush by VA at EL1
   - `tlbi_aside1(asid: u16)`: `TLBI ASIDE1, Xt` — flush by ASID at EL1
   - `tlbi_vale1(vaddr: u64)`: `TLBI VALE1, Xt` — flush last-level by VA
2. Each wrapper followed by DSB + ISB per ARM ARM requirement (AG6-G).

#### AG6-F: Targeted TLB Flush Integration (H3-ARCH-02)

**Changes**:
1. In `TlbModel.lean`, extend the existing flush operations to include
   hardware-backed variants:
   - `adapterFlushTlbHw : SystemState → SystemState` wraps `tlbi_vmalle1`
   - `adapterFlushTlbByAsidHw : SystemState → ASID → SystemState` wraps
     `tlbi_aside1`
   - `adapterFlushTlbByVAddrHw : SystemState → ASID → VAddr → SystemState`
     wraps `tlbi_vae1`
2. Prove that hardware flush operations produce the same model state as the
   existing abstract flush operations (bridging the model to hardware).
3. Update `vspaceUnmapPageWithFlush` to use the targeted flush variant.

**Module verification**: `lake build SeLe4n.Kernel.Architecture.TlbModel`.

#### AG6-G: ISB After TLBI (H3-ARCH-03)

**Changes**:
1. In the HAL flush wrappers (AG6-E), ensure every TLBI is followed by:
   - `DSB ISH` — ensure the TLB invalidation is visible to all cores in the
     inner shareable domain
   - `ISB` — synchronize the instruction stream
2. In the Lean model, add a `tlbBarrierComplete` predicate that asserts the
   barrier sequence was executed after any TLB operation.
3. The TLB flush composition theorems (AG7-E) will require this predicate
   as a hypothesis.

#### AG6-H: ASID Generation and Management (H3-ARCH-04)

**Changes**:
1. Create `SeLe4n/Kernel/Architecture/AsidManager.lean`:
   - `AsidPool` structure: `nextAsid : Fin maxAsid`, `generation : Nat`
   - `allocateAsid : AsidPool → (AsidPool × ASID)` — bump allocator with
     rollover. On rollover (nextAsid wraps to 0), increment generation and
     flush all TLB entries (`tlbi_vmalle1`).
   - `freeAsid : AsidPool → ASID → AsidPool` — mark ASID as available for
     reuse (free list or bitmap).
   - RPi5: `maxAsid = 65536` (16-bit ASID from Board.lean).
2. Wire ASID allocation into VSpace creation and ASID into page table
   descriptors (nG bit for non-global pages).
3. Prove ASID uniqueness: no two active VSpaces share the same ASID.

**Module verification**: `lake build SeLe4n.Kernel.Architecture.AsidManager`.

#### AG6-I: Cache Maintenance Operations (H3-RUST-06)

**Changes**:
1. In `rust/sele4n-hal/src/cache.rs`:
   - `dc_civac(addr: u64)`: Clean + Invalidate by VA to PoC
   - `dc_cvac(addr: u64)`: Clean by VA to PoC
   - `dc_ivac(addr: u64)`: Invalidate by VA to PoC
   - `dc_zva(addr: u64)`: Zero by VA (cache-line-sized zero)
   - `ic_iallu()`: Invalidate all instruction caches to PoU
   - `ic_ialluis()`: Invalidate all instruction caches to PoU (Inner Shareable)
   - `cache_range(op: fn(u64), start: u64, end: u64, line_size: u64)`:
     Apply cache operation over an address range
2. Cache line size: 64 bytes on Cortex-A76 (from CTR_EL0).
3. Required for: DMA coherency, self-modifying code, page table updates.


---

### Phase AG7 — FFI Bridge + Proof Hooks

**Goal**: Connect the Lean kernel to the Rust HAL via FFI. Close the proof
gap for production platform contracts.

**Dependencies**: AG4-AG6 (HAL exists, page tables work), AG3 (models defined).
**Gate**: Lean kernel successfully calls Rust HAL functions. Production
`AdapterProofHooks` instantiated. `lake build` passes.
**Estimated scope**: ~400–600 lines of Lean, ~200–300 lines of Rust.

#### AG7-A: Lean → Rust FFI Bridge (H3-RUST-03)

**Finding**: The Lean kernel is pure — it has no way to call hardware
operations. An FFI bridge is needed for the compiled Lean code to invoke
Rust HAL functions.

**Changes**:
1. Create `rust/sele4n-hal/src/ffi.rs`:
   - `extern "C"` functions callable from Lean compiled code:
     - `ffi_timer_read_counter() -> u64`
     - `ffi_timer_reprogram(interval: u64)`
     - `ffi_gic_acknowledge() -> u32`
     - `ffi_gic_eoi(intid: u32)`
     - `ffi_tlbi_all()`
     - `ffi_tlbi_by_asid(asid: u16)`
     - `ffi_tlbi_by_vaddr(asid: u16, vaddr: u64)`
     - `ffi_mmio_read32(addr: u64) -> u32`
     - `ffi_mmio_write32(addr: u64, val: u32)`
     - `ffi_uart_putc(c: u8)`
     - `ffi_disable_interrupts()`
     - `ffi_enable_interrupts()`
2. Create `SeLe4n/Platform/FFI.lean`:
   - `@[extern "ffi_timer_read_counter"] opaque timerReadCounter : IO UInt64`
   - Similar `@[extern]` declarations for each FFI function
   - These replace the pure model operations with hardware-backed
     implementations when compiling for hardware target
3. Conditional compilation: `IO`-based FFI for hardware target,
   pure model for proof/test target. Use Lean `#if` or build flags.

**Steps** (5 atomic units):

1. **AG7-A-i: Rust FFI exports — timer + GIC group.** In
   `rust/sele4n-hal/src/ffi.rs`, implement the first group of
   `#[no_mangle] pub extern "C"` functions:
   - `ffi_timer_read_counter() -> u64`: calls `timer::read_cntpct()`
   - `ffi_timer_reprogram(interval: u64)`: calls `timer::set_cval(interval)`
   - `ffi_gic_acknowledge() -> u32`: calls `gic::acknowledge_interrupt()`
   - `ffi_gic_eoi(intid: u32)`: calls `gic::end_of_interrupt(intid)`
   Each function is a thin wrapper around the HAL module from AG5.

2. **AG7-A-ii: Rust FFI exports — TLB + MMIO + misc group.** Continue in
   `ffi.rs` with:
   - `ffi_tlbi_all()`: calls `mmu::tlbi_vmalle1()`
   - `ffi_tlbi_by_asid(asid: u16)`: calls `mmu::tlbi_aside1(asid)`
   - `ffi_tlbi_by_vaddr(asid: u16, vaddr: u64)`: calls `mmu::tlbi_vae1(...)`
   - `ffi_mmio_read32(addr: u64) -> u32`: calls `mmio::mmio_read32(addr)`
   - `ffi_mmio_write32(addr: u64, val: u32)`: calls `mmio::mmio_write32(addr, val)`
   - `ffi_uart_putc(c: u8)`: calls `uart::putc(c)`
   - `ffi_disable_interrupts()` / `ffi_enable_interrupts()`: calls
     `interrupts::disable_interrupts()` / `interrupts::enable_interrupts()`

3. **AG7-A-iii: Lean FFI declarations.** Create `SeLe4n/Platform/FFI.lean`.
   For each Rust FFI function, add a corresponding `@[extern]` declaration:
   ```
   @[extern "ffi_timer_read_counter"]
   opaque timerReadCounter : IO UInt64
   @[extern "ffi_gic_acknowledge"]
   opaque gicAcknowledge : IO UInt32
   ```
   Group declarations by subsystem (timer, GIC, TLB, MMIO, misc).
   Add docstrings documenting the hardware operation each performs.

4. **AG7-A-iv: Conditional compilation gate.** In `lakefile.lean`, add a
   `hw_target` build option (e.g., `@[lake_option] def hwTarget : Bool`).
   In `SeLe4n/Platform/FFI.lean`, use `#if HW_TARGET` guards:
   - When `HW_TARGET = true`: the `@[extern]` declarations are active
   - When `HW_TARGET = false` (default): provide pure-model stubs that
     match the `Sim` platform contract behavior
   This ensures `lake build` continues to work without a Rust HAL present.

5. **AG7-A-v: Link verification.** Add a build script step in
   `lakefile.lean` that, when `hwTarget = true`, links against
   `libsele4n_hal.a` (the static library from `cargo build`). Test by
   building with `lake build -DhwTarget=true` and verifying that all
   `@[extern]` symbols resolve against the Rust static library. Add a
   CI job for hardware-target builds.

#### AG7-B: System Register Accessors (H3-RUST-07)

**Changes**:
1. In `rust/sele4n-hal/src/registers.rs`:
   - Macro `read_sysreg!(reg)` → `MRS Xt, reg`
   - Macro `write_sysreg!(reg, val)` → `MSR reg, Xt`
   - Concrete accessors:
     - `read_sctlr_el1() -> u64` / `write_sctlr_el1(val: u64)`
     - `read_tcr_el1() -> u64` / `write_tcr_el1(val: u64)`
     - `read_ttbr0_el1() -> u64` / `write_ttbr0_el1(val: u64)`
     - `read_ttbr1_el1() -> u64` / `write_ttbr1_el1(val: u64)`
     - `read_mair_el1() -> u64` / `write_mair_el1(val: u64)`
     - `read_esr_el1() -> u64` / `read_elr_el1() -> u64`
     - `read_far_el1() -> u64` / `read_spsr_el1() -> u64`
     - `read_mpidr_el1() -> u64` (CPU identification)
     - `read_ctr_el0() -> u64` (cache type register)
2. Each accessor uses inline assembly with appropriate register constraints.

#### AG7-C: MMIO Volatile Read/Write Primitives (H3-RUST-08)

**Changes**:
1. In `rust/sele4n-hal/src/mmio.rs`:
   - `mmio_read32(addr: usize) -> u32`:
     `core::ptr::read_volatile(addr as *const u32)`
   - `mmio_write32(addr: usize, val: u32)`:
     `core::ptr::write_volatile(addr as *mut u32, val)`
   - `mmio_read64(addr: usize) -> u64`
   - `mmio_write64(addr: usize, val: u64)`
2. Bridge to Lean model: the FFI `ffi_mmio_read32` / `ffi_mmio_write32`
   functions call these volatile primitives, connecting the `MmioSafe`
   model (MmioAdapter.lean) to actual hardware register access.
3. Add alignment checks in debug builds: assert addr is aligned to
   access size.

#### AG7-D: Production AdapterProofHooks (FINDING-02, unified)

**Finding**: `AdapterProofHooks` only instantiated for `rpi5RuntimeContractRestrictive`
(which denies all register writes and context switches, making proofs vacuous).
Production `rpi5RuntimeContract` has substantive `registerContextStablePred`
but NO proof hooks.

**Changes**:
1. Create `rpi5ProductionAdapterProofHooks : AdapterProofHooks rpi5RuntimeContract`:
   - `preserveAdvanceTimer`: Reuse existing
     `advanceTimerState_preserves_proofLayerInvariantBundle` (same as restrictive).
   - `preserveWriteRegister`: Prove that individual register writes to
     the current thread's TCB `registerContext` preserve
     `registerContextStablePred`. Key insight: writing register `r` to value
     `v` in the machine state, then updating `tcb.registerContext` to match,
     maintains `machine.registers = tcb.registerContext`.
   - `preserveReadMemory`: Memory reads don't modify state (same as restrictive).
   - `preserveContextSwitch`: Prove that `adapterContextSwitch` (X1-F atomic
     operation) preserves `registerContextStablePred`. Leverage existing
     `contextSwitchState_preserves_contextMatchesCurrent` (Adapter.lean).
     The atomic context switch saves current thread's registers and loads
     new thread's `registerContext`, maintaining the invariant.
2. The critical proof is `preserveContextSwitch`:
   - Pre-condition: `machine.registers = oldThread.registerContext`
   - Operation: save `machine.registers` → `oldThread.registerContext`,
     load `newThread.registerContext` → `machine.registers`
   - Post-condition: `machine.registers = newThread.registerContext`
   - This follows from the X1-F atomic context switch design.

**Module verification**: `lake build SeLe4n.Platform.RPi5.ProofHooks`.

**Steps** (4 atomic units):

1. **AG7-D-i: preserveAdvanceTimer + preserveReadMemory.** In
   `RPi5/ProofHooks.lean`, start the `rpi5ProductionAdapterProofHooks`
   instance with the two straightforward proofs:
   - `preserveAdvanceTimer`: identical to the restrictive version — timer
     advance only modifies `MachineState.timer`, which is disjoint from
     `registerContext`. Reuse existing
     `advanceTimerState_preserves_proofLayerInvariantBundle`.
   - `preserveReadMemory`: memory reads return a value without modifying
     state — proof is `rfl` (or `Eq.refl`). Same as restrictive version.

2. **AG7-D-ii: preserveWriteRegister.** Prove that writing register `r`
   to value `v` preserves `registerContextStablePred`. The production
   contract's `registerContextStablePred` asserts
   `machine.registers = currentThread.registerContext`. The register write
   operation updates BOTH `machine.registers` (via `writeReg`) and
   `currentThread.registerContext` (via the TCB update in the adapter layer).
   Proof strategy: unfold `registerContextStablePred`, show that the
   parallel update to both fields preserves equality. Key lemma:
   `writeReg_both_preserves_match : writeReg machine.registers r v =
   writeReg tcb.registerContext r v → match preserved`.

3. **AG7-D-iii: preserveContextSwitch.** The critical proof. Structure:
   - Unfold `adapterContextSwitch` into its X1-F atomic steps:
     `save := { oldTcb with registerContext := machine.registers }`
     `load := { machine with registers := newTcb.registerContext }`
   - Pre: `machine.registers = oldTcb.registerContext` (from existing invariant)
   - After save: `oldTcb.registerContext = machine.registers` ✓
   - After load: `machine.registers = newTcb.registerContext` ✓
   - Post: the new current thread's `registerContext` matches `machine.registers`
   - Leverage `contextSwitchState_preserves_contextMatchesCurrent` from
     `Adapter.lean` as the core lemma.

4. **AG7-D-iv: Instance assembly + integration.** Assemble the 4 proofs into
   `instance : AdapterProofHooks rpi5RuntimeContract`. Update
   `RPi5/Contract.lean` to export both `rpi5RestrictiveAdapterProofHooks`
   (existing) and `rpi5ProductionAdapterProofHooks` (new). Add a
   `#check` verifying the instance resolves. Update documentation in
   `docs/spec/SELE4N_SPEC.md` noting that production proof hooks are now
   substantive (not vacuously true).

#### AG7-E: TLB Flush Composition Theorems (H3-PROOF-02)

**Changes**:
1. In `TlbModel.lean`, add:
   - `hardwareFlushAll_equiv_modelFlush`: TLBI VMALLE1 produces the same
     TLB state as `adapterFlushTlb` (both clear all entries).
   - `hardwareFlushByAsid_equiv_modelFlush`: TLBI ASIDE1 produces the same
     TLB state as `adapterFlushTlbByAsid` (both remove entries for given ASID).
   - `hardwareFlushByVAddr_equiv_modelFlush`: TLBI VAE1 produces the same
     TLB state as `adapterFlushTlbByVAddr`.
2. Composition theorem: `vspaceUnmapPageWithFlush` composed with hardware
   TLBI instruction preserves `tlbConsistent`.
3. These theorems bridge the gap between the abstract TLB model (which
   operates on sets of TLB entries) and the hardware instructions.

**Module verification**: `lake build SeLe4n.Kernel.Architecture.TlbModel`.

#### AG7-F: Context Switch Proof Hooks (New)

**Changes**:
1. Prove the context switch path end-to-end:
   - Exception entry (save registers to stack) →
   - Kernel operations (pure Lean, preserves invariants by existing proofs) →
   - `adapterContextSwitch` (save current thread context, load new thread) →
   - Exception return (restore registers from stack, ERET)
2. Key theorem: the full exception-entry → kernel → exception-return cycle
   preserves `registerContextStablePred` and all kernel invariants.
3. This closes the proof gap identified in FINDING-02: on real hardware,
   context switches ARE register writes, but the atomic X1-F design ensures
   the invariant is maintained through the entire cycle.

**Module verification**: `lake build SeLe4n.Kernel.Architecture.Adapter`.


---

### Phase AG8 — Integration + Model Closure

**Goal**: Close remaining Lean model gaps exposed by hardware integration.
Migrate legacy design patterns to H3-ready implementations.

**Dependencies**: AG5 (interrupts work), AG7 (FFI bridge, proof hooks).
**Gate**: `./scripts/test_full.sh` passes. All invariants preserved with new
models integrated.
**Estimated scope**: ~500–700 lines of Lean.

#### AG8-A: Timeout Sentinel → Explicit TCB Field (H3-IPC-01/I-01)

**Finding**: Timeout is signaled via sentinel value `0xFFFFFFFF` in GPR x0
combined with `ipcState = .ready` dual-condition check. Fragile — could collide
with legitimate IPC data. H3 migration to explicit `timedOut : Bool` TCB field
was documented in AE4-F.

**Changes**:
1. Add `timedOut : Bool := false` field to the TCB structure in
   `Model/Object/Types.lean`.
2. In `IPC/Operations/Timeout.lean`, update `timeoutThread` to:
   - Set `tcb.timedOut := true` instead of writing sentinel to register x0
   - Set `tcb.ipcState := .ready` (unchanged)
3. In `IPC/Operations/Endpoint.lean`, update receive-side operations to:
   - Check `tcb.timedOut` instead of reading x0 sentinel value
   - Clear `tcb.timedOut := false` after processing
4. Update all IPC invariant preservation proofs that reference the sentinel
   pattern.
5. Update Rust ABI: `KernelError::Timeout` detection no longer depends on
   register x0 value — it becomes an explicit error code.
6. Remove the `timeoutErrorCode` constant and associated sentinel logic.

**Module verification**: `lake build SeLe4n.Model.Object.Types`,
`lake build SeLe4n.Kernel.IPC.Operations.Timeout`.

**Steps** (6 atomic units):

1. **AG8-A-i: Add TCB field.** In `Model/Object/Types.lean`, add
   `timedOut : Bool := false` to the `TCB` structure (after the existing
   `ipcState` field). Update the `TCB` `BEq` instance to include
   `timedOut`. Update `defaultTCB` to include `timedOut := false`.
   Build: `lake build SeLe4n.Model.Object.Types`.

2. **AG8-A-ii: Update timeoutThread.** In `IPC/Operations/Timeout.lean`,
   modify `timeoutThread` (line ~91) to replace:
   `registerContext := writeReg tcb.registerContext ⟨0⟩ timeoutErrorCode`
   with: `timedOut := true`.
   Keep the `ipcState := .ready` assignment unchanged.
   Remove the `timeoutErrorCode` definition (line ~39) — it becomes unused.

3. **AG8-A-iii: Update timeout detection.** In `IPC/Operations/Timeout.lean`,
   modify `checkTimeoutStatus` (line ~127) to replace:
   `if tcb.registerContext.gpr ⟨0⟩ = timeoutErrorCode ∧ tcb.ipcState = .ready`
   with: `if tcb.timedOut ∧ tcb.ipcState = .ready`.
   In the success branch, add `timedOut := false` to clear the flag.

4. **AG8-A-iv: Update receive-side operations.** In
   `IPC/Operations/Endpoint.lean`, find any code that checks the sentinel
   pattern on the receive path. Replace sentinel checks with `tcb.timedOut`
   checks. Ensure `timedOut` is cleared (`timedOut := false`) when the
   thread is dequeued from a wait state and successfully receives a message.

5. **AG8-A-v: IPC invariant proof updates.** Search for all theorems in
   `IPC/Invariant/` that reference `timeoutErrorCode`, `gpr ⟨0⟩`, or
   the sentinel pattern. Update each proof to use `timedOut` instead.
   Key files: `EndpointPreservation.lean`, `CallReplyRecv.lean`,
   `Structural.lean`. The proof changes should be mechanical — replacing
   `registerContext.gpr ⟨0⟩ = timeoutErrorCode` with `timedOut = true`
   throughout.

6. **AG8-A-vi: Rust ABI update.** In `rust/sele4n-abi/src/error.rs`, update
   the timeout detection logic. Previously, the Rust side checked GPR x0
   for the sentinel value. Now timeout is communicated via the explicit
   `KernelError::Timeout` variant in the error enum (already exists).
   Remove any `0xFFFFFFFF` sentinel constant from the Rust ABI. Update
   the `From<RawSyscallResult>` impl if it referenced the sentinel.

#### AG8-B: Cache Coherency Model (H3-ARCH-07)

**Changes**:
1. Create `SeLe4n/Kernel/Architecture/CacheModel.lean`:
   - `CacheState` structure modeling D-cache and I-cache state
   - `CacheLineState` inductive: `invalid | clean | dirty`
   - Key operations: `dcClean`, `dcInvalidate`, `dcCleanInvalidate`,
     `icInvalidate`
   - `cacheCoherent : CacheState → Memory → Prop` — D-cache matches memory
   - `icacheCoherent : CacheState → Memory → Prop` — I-cache matches code
2. Preservation theorem: kernel operations that modify page tables must be
   followed by `dcCleanInvalidate` + `icInvalidate` to maintain coherency.
3. This model is primarily for documentation and proof structure — the HAL
   layer (AG6-I) provides the actual cache maintenance operations.

**Module verification**: `lake build SeLe4n.Kernel.Architecture.CacheModel`.

#### AG8-C: Memory Barrier Semantics (H3-ARCH-08)

**Changes**:
1. Extend the existing barrier annotations in `MmioAdapter.lean` with
   formal semantics:
   - `DMB ISH`: Data Memory Barrier, Inner Shareable — ensures ordering
     of data accesses
   - `DSB ISH`: Data Synchronization Barrier — ensures completion of
     all data accesses
   - `ISB`: Instruction Synchronization Barrier — flushes pipeline
2. Define `barrierOrdered : SystemState → SystemState → Prop` that asserts
   memory operations before the barrier are visible before operations after.
3. Theorem: MMIO writes preceded by `DSB` are guaranteed visible to hardware
   before subsequent reads (needed for GIC register access correctness).
4. This formalizes the barrier annotations already present in the MMIO model
   without changing existing code behavior.

**Module verification**: `lake build SeLe4n.Platform.RPi5.MmioAdapter`.

#### AG8-D: FrozenOps Production Decision (H3-PROOF-05)

**Finding**: FrozenOps (`SeLe4n/Kernel/FrozenOps/`) is marked experimental
and not in the production chain. Decision needed: promote or permanently defer.

**Changes**:
1. Evaluate FrozenOps readiness for production:
   - Check: all 24 operations have preservation theorems
   - Check: `FrozenSchedulerState` now includes `replenishQueue` (AG1-E)
   - Check: `FrozenMap` commutativity proofs complete
2. If ready: remove `[experimental]` annotations and add FrozenOps import
   to the production module chain.
3. If not ready: document the specific remaining gaps and defer to WS-V.
   Add `[experimental — deferred to WS-V]` annotation.
4. In either case, update `docs/codebase_map.json` to reflect the decision.

#### AG8-E: descendantsOf Fuel Sufficiency (F-S05)

**Finding**: CDT transitive closure completeness proof deferred until H3
hardware-binding CDT depth bounds are available. Now unblocked.

**Changes**:
1. With H3 providing concrete hardware bounds (RPi5 object count limits),
   define `maxCdtDepth : Nat` based on the maximum number of kernel objects
   (bounded by `maxObjects = 65536` from `storeObjectChecked`).
2. Prove fuel sufficiency: `cdtDepth ≤ maxCdtDepth` for all reachable
   states, therefore `descendantsOf` with `fuel = maxCdtDepth` is complete.
3. This proof leverages `cdtAcyclic` (which is structural, no fuel) to bound
   the longest possible descendant chain.

**Module verification**: `lake build SeLe4n.Model.State`.

#### AG8-F: Donation Chain k>2 Cycle Prevention (H3-PROOF-03)

**Finding**: Current `donationChainAcyclic` proof covers only 2-cycle
prevention. The `blockingAcyclic` predicate (added in AF-01) provides general
acyclicity but the donation chain specifically handles the PIP propagation path.

**Changes**:
1. Extend `donationChainAcyclic` to cover k-cycles for arbitrary k:
   - Leverage `blockingAcyclic` (which uses `WellFounded` on the blocking
     relation) to derive donation chain acyclicity for all chain lengths.
   - Bridge lemma: `blockingAcyclic → donationChainAcyclic_general`
2. The proof structure: blocking graph acyclicity implies no cycles in any
   sub-relation (donation chains are a sub-relation of the blocking graph).
3. Update `ipcInvariantFull` documentation to note the strengthened guarantee.

**Module verification**: `lake build SeLe4n.Kernel.IPC.Invariant.Structural`.

#### AG8-G: Donation Atomicity Under Interrupt Disable (H3-IPC-04)

**Changes**:
1. In the IPC donation path (`IPC/Operations/Donation.lean`), add
   documentation and a proof obligation showing that donation operations
   (which modify multiple TCBs and the blocking graph) execute atomically
   with respect to interrupts.
2. Define `donationAtomicRegion : SystemState → SystemState → Prop` asserting
   that the donation state transition occurs with `interruptsEnabled = false`.
3. Proof: no interrupt can fire between the read of the blocking graph and
   the completion of PIP propagation, preventing inconsistent intermediate
   states.
4. This ties into AG5-G (interrupt-disabled region enforcement).

**Module verification**: `lake build SeLe4n.Kernel.IPC.Operations.Donation`.

---

### Phase AG9 — Testing + Validation

**Goal**: Validate the H3 implementation on QEMU and real hardware.

**Dependencies**: AG4-AG8 (all implementation complete).
**Gate**: All tests pass on QEMU. Hardware cross-check verified.
Full test suite passes on RPi5 hardware.
**Estimated scope**: ~300–500 lines of test code, plus test execution.

#### AG9-A: QEMU Integration Testing (New)

**Changes**:
1. Create `scripts/test_qemu.sh`:
   - Build kernel binary: `cargo build --release --target aarch64-unknown-none`
   - Launch QEMU: `qemu-system-aarch64 -machine raspi4b -kernel <binary>
     -serial stdio -display none`
   - Verify UART output matches expected boot sequence
   - Run syscall smoke test: invoke each of the 25 syscalls
   - Verify timer interrupts fire at expected rate
   - Verify GIC routing for simulated device interrupts
2. Add QEMU test to CI pipeline (optional, gated by QEMU availability).
3. Test timeout: 60 seconds per QEMU session.

#### AG9-B: Live Hardware Constant Cross-Check (H3-PLAT-07)

**Changes**:
1. On physical RPi5 hardware, verify all BCM2712 constants from Board.lean:
   - GIC distributor: read GICD_IIDR at 0xFF841008, verify implementer/variant
   - GIC CPU interface: read GICC_IIDR at 0xFF8420FC
   - UART: write test char to 0xFE201000, verify on serial console
   - Timer: read CNTFRQ_EL0, verify = 54000000
   - Memory: verify RAM regions accessible (read/write test)
   - Peripherals: verify MMIO regions accessible
2. Record results in `docs/hardware_validation/rpi5_cross_check.md`.
3. Update Board.lean if any constants differ from actual hardware.

#### AG9-C: WCRT Empirical Validation (H3-SCHED-05)

**Changes**:
1. Instrument `timerTick` with cycle counter reads (PMCCNTR_EL0):
   - Measure worst-case scheduling latency across 10,000+ timer ticks
   - Record: min, max, mean, p99, p99.9 latencies
2. Compare measured WCRT against theoretical bound:
   `D * L_max + N * (B + P)` from `bounded_scheduling_latency_exists`.
3. Document results and any discrepancies.

#### AG9-D: Run Queue Cache Performance (H3-SCHED-03)

**Changes**:
1. Profile RunQueue operations on Cortex-A76:
   - `insert`: measure cycles for 1, 10, 50, 100 threads
   - `remove`: measure cycles for various queue sizes
   - `chooseBestInBucketEffective`: measure Stage 1 hit rate vs fallback
2. Validate that the two-stage selection (AG1-A fix) provides measurable
   improvement over flat-only scan.
3. Document cache performance characteristics.

#### AG9-E: Badge Overflow Hardware Validation (H3-IPC-03)

**Changes**:
1. Test Badge `Nat → UInt64` round-trip behavior on ARM64:
   - Verify `Badge.toNat` and `Badge.ofNat` preserve values within 64-bit range
   - Test overflow behavior: Nat values exceeding 2^64 - 1
2. Confirm hardware register width matches model assumptions.
3. This is a quick validation — document results.

#### AG9-F: Security Hardening — Speculation Barriers (New)

**Changes**:
1. Identify speculative execution attack surfaces in compiled Lean code:
   - Capability address masking (`resolveCapAddress` CPtr bit masking)
   - Run queue array indexing (priority bucket lookup)
   - Page table walk (descriptor parsing)
2. Add CSDB (Conditional Speculation Dependency Barrier) instructions after
   bounds checks at these sites in the Rust HAL layer.
3. Cortex-A76 mitigations:
   - Spectre v1: CSDB after bounds checks
   - Spectre v2: FEAT_CSV2 (branch prediction hardening) — verify enabled
4. NOT in scope for H3: MTE (Cortex-A76 does not support), PAC/BTI (deferred).

#### AG9-G: Full Test Suite on RPi5 Hardware (New)

**Changes**:
1. Execute the full tiered test suite on RPi5:
   - `test_fast.sh` (Tier 0+1)
   - `test_smoke.sh` (Tier 0-2)
   - `test_full.sh` (Tier 0-3)
2. Execute QEMU test suite on hardware (AG9-A adapted for bare-metal).
3. Execute Rust test suite: `cargo test --workspace`.
4. Record all results and any hardware-specific failures.

---

### Phase AG10 — Documentation + Closure

**Goal**: Synchronize all documentation with H3 changes. Close the workstream.

**Dependencies**: AG1-AG9 (all implementation and testing complete).
**Gate**: `./scripts/test_full.sh` passes. All documentation synchronized.
No website-linked paths broken (`scripts/check_website_links.sh`).
**Estimated scope**: ~500–800 lines of documentation changes.

#### AG10-A: Multi-Core Limitation Documentation (FINDING-05)

**Changes**:
1. In `docs/spec/SELE4N_SPEC.md`, add a "Hardware Limitations" section:
   - Document single-core operation in H3
   - RPi5 has 4 Cortex-A76 cores; H3 uses core 0 only
   - Other cores held in WFE loop (AG4-E boot sequence)
   - SMP support deferred to WS-V
2. In `README.md`, note single-core limitation in hardware target section.
3. SMP requirements for future reference:
   - Per-core run queues, IPI for cross-core scheduling
   - Spinlock/ticket lock for shared kernel state
   - Cache coherency protocol (MOESI on Cortex-A76)

#### AG10-B: IPC Buffer Alignment Documentation (FINDING-07)

**Changes**:
1. In `docs/spec/SELE4N_SPEC.md` IPC section, document:
   - Lean model: 512-byte IPC buffer alignment
   - Rust ABI: `IpcBuffer` is 960 bytes, `#[repr(C)]`, 8-byte aligned
   - Hardware: 512B alignment provides 8 × 64-byte cache lines on Cortex-A76
   - `ipcBuffer_within_page` theorem ensures no page-boundary crossing
   - 512B alignment is a performance choice, not an architectural requirement

#### AG10-C: Architecture Assumptions Update (New)

**Changes**:
1. Update `SeLe4n/Kernel/Architecture/Assumptions.lean`:
   - Add documentation for the new exception model (AG3-C)
   - Add documentation for the new interrupt dispatch model (AG3-D)
   - Add documentation for the timer model binding (AG3-E)
   - Update hardware assumptions section for ARM64-specific constraints
2. Ensure all `axiom`-free status is maintained.

#### AG10-D: SELE4N_SPEC.md Update (New)

**Changes**:
1. Major update to `docs/spec/SELE4N_SPEC.md`:
   - Add "Hardware Binding" chapter covering AG4-AG7 architecture
   - Update "Platform" chapter with RPi5 production contract details
   - Add "Exception Handling" section
   - Add "Interrupt Dispatch" section
   - Update "Scheduler" chapter with timer binding details
   - Update "Memory Management" with ARMv8 page table details
   - Add "FFI Bridge" section documenting Lean ↔ Rust interface
2. Ensure all theorem references are current.

#### AG10-E: Codebase Map Regeneration (New)

**Changes**:
1. Regenerate `docs/codebase_map.json` to include:
   - New Architecture modules (ExceptionModel, InterruptDispatch, TimerModel,
     PageTable, VSpaceARMv8, AsidManager, CacheModel)
   - New Platform modules (FFI)
   - New Rust crate (sele4n-hal) with module listing
   - Updated module counts and line counts

#### AG10-F: WORKSTREAM_HISTORY.md Update (New)

**Changes**:
1. Add WS-AG entry to `docs/WORKSTREAM_HISTORY.md`:
   - Phase summary (AG1-AG10)
   - Finding counts resolved per phase
   - Sub-task counts completed
   - Key deliverables (HAL crate, ARMv8 page tables, GIC driver, etc.)
   - Version range

#### AG10-G: README.md Metrics Sync (New)

**Changes**:
1. Update `README.md` metrics from `docs/codebase_map.json`:
   - Lean module count (132 → ~145+)
   - Rust file count (30 → ~50+)
   - Rust crate count (3 → 4)
   - Syscall count (25 — unchanged)
   - Cross-subsystem bridge lemma count (33 → 34+)
   - New: hardware platform status
2. Update CHANGELOG.md with H3 version entries.


---

## 4. Risk Register

### 4.1 Technical Risks

| ID | Risk | Likelihood | Impact | Phase | Mitigation |
|----|------|-----------|--------|-------|------------|
| TR-01 | Lean 4 compiled code performance on ARM64 insufficient for real-time guarantees | Medium | HIGH | AG7, AG9 | Profile early in AG7 (FFI prototype). If critical paths too slow, implement them in Rust with Lean proof of equivalence. |
| TR-02 | Lean-Rust FFI bridge complexity exceeds expectations (calling conventions, memory layout) | Medium | HIGH | AG7 | Prototype minimal FFI (Lean calls Rust UART write) in AG4 before full integration. Use `@[extern]` declarations with C calling convention. |
| TR-03 | ARMv8 page table refinement proof significantly more complex than expected | Low | HIGH | AG6 | Keep HashMap model as specification. Structure proof as simulation relation. Break into per-operation refinement lemmas. Allocate 2× estimated time. |
| TR-04 | GIC-400 register timing sensitivity causes interrupt storms or missed interrupts on hardware | Low | MEDIUM | AG5, AG9 | Use conservative IRQ acknowledge sequence (read IAR → process → write EOIR). Test on QEMU first. Add interrupt rate limiting in debug builds. |
| TR-05 | Cache coherency issues between Lean compiled code and Rust HAL cause data corruption | Medium | MEDIUM | AG6, AG8 | Use DSB/ISB barriers conservatively at FFI boundary. Ensure all shared memory regions are cache-coherent or explicitly maintained. |
| TR-06 | Boot sequence fragility on real RPi5 (firmware differences, DTB variations) | Medium | HIGH | AG4, AG9 | Test on QEMU (`raspi4b` closest available) before hardware. Use static board constants (not DTB) for H3. Cross-check against Linux kernel BCM2712 driver source for undocumented requirements. |
| TR-07 | Production AdapterProofHooks context-switch proof harder than expected | Medium | MEDIUM | AG7 | The X1-F atomic context-switch design was specifically created for this proof. `contextSwitchState_preserves_contextMatchesCurrent` already exists. Risk is in threading through the full exception entry/exit path. |
| TR-08 | S-04 effective priority fix breaks existing scheduler preservation theorems | Low | MEDIUM | AG1 | Theorems are parameterized over the inserted priority value. The change should be mechanical. Run `test_full.sh` after each change. |
| TR-09 | ipcInvariantFull extension (F-T02) cascades into many preservation proofs | Medium | MEDIUM | AG1 | `uniqueWaiters` preservation is already proven for `notificationWait`. Other operations that don't modify notification state get frame lemmas. Estimate ~5–10 additional lemmas. |
| TR-10 | ARMv8 page table page allocation in pure Lean model is awkward | Medium | LOW | AG6 | Use bump allocator for H3. Page table pages come from a reserved memory region. Full allocator deferred to WS-V. |

### 4.2 Process Risks

| ID | Risk | Likelihood | Impact | Mitigation |
|----|------|-----------|--------|------------|
| PR-01 | BCM2712 datasheet gaps (incomplete or inaccurate public documentation) | Medium | MEDIUM | Cross-reference with Linux kernel `drivers/` source for BCM2712. RPi Foundation community forums for undocumented behavior. |
| PR-02 | Lean 4 toolchain bugs when compiling to ARM64 native target | Low | HIGH | Test Lean compiler on ARM64 early (AG4 gate). Report upstream bugs to leanprover/lean4. Have QEMU cross-compilation as fallback. |
| PR-03 | Proof regression during H3 development (new modules break existing proofs) | Low | MEDIUM | Run `test_full.sh` at every phase gate. Never modify existing proof files without running full suite. Use `lake build Module.Path` for new modules. |
| PR-04 | Scope creep — H3 expands into SMP, DMA, or other post-H3 features | Medium | MEDIUM | Strict scope boundary: single-core, no DMA, no GPU. Document all deferrals to WS-V. Reject feature requests that cross the boundary. |
| PR-05 | Hardware availability — RPi5 development board not available for testing | Low | HIGH | QEMU for development. Order hardware early. AG9-B/AG9-G explicitly test on hardware. |

---

## 5. Dependency Map

```
AG1 (Lean fixes) ───────────┐
                             ├──→ AG3 (Platform model) ──→ AG4 (HAL+Boot) ──→ AG5 (Interrupts)
AG2 (Rust fixes) ───────────┘                                    │                    │
                                                                 │                    │
                                         AG6 (Memory mgmt) ←────┘                    │
                                              │                                       │
                                              └──→ AG7 (FFI+Proofs) ←────────────────┘
                                                        │
                                                        ↓
                                                   AG8 (Integration)
                                                        │
                                                        ↓
                                                   AG9 (Testing)
                                                        │
                                                        ↓
                                                   AG10 (Documentation)
```

### 5.1 Parallelism Opportunities

| Parallel Group | Phases | Rationale |
|----------------|--------|-----------|
| Group 1 | AG1 + AG2 | Independent subsystems (Lean vs Rust). No file overlap. |
| Group 2 | AG4 + AG6 (partial) | HAL crate creation and page table Lean model can start concurrently. Page table Rust implementation depends on AG4. |
| Group 3 | AG5 + AG6 (partial) | GIC driver and page table Lean model can proceed concurrently. |
| Group 4 | AG8 sub-tasks | Many AG8 items are independent (cache model, barrier semantics, frozen decision). |
| Group 5 | AG10 sub-tasks | Documentation items are independent of each other. |

### 5.2 Critical Path

The critical path through the dependency graph determines the minimum
completion timeline:

```
AG1/AG2 → AG3 → AG4 → AG5 → AG7 → AG8 → AG9 → AG10
```

AG6 (Memory Management) is the most complex phase but can overlap with AG5.
AG7 depends on both AG5 and AG6, making it the convergence point.

### 5.3 Phase Dependencies (Detailed)

| Phase | Hard Dependencies | Soft Dependencies |
|-------|-------------------|-------------------|
| AG1 | None | — |
| AG2 | None | — |
| AG3 | AG1 (clean baseline) | AG2 (Rust clean, but independent) |
| AG4 | AG2 (Rust workspace clean), AG3 (models defined for reference) | — |
| AG5 | AG4 (HAL crate, VBAR set, UART working) | AG3 (interrupt model) |
| AG6 | AG4 (MMU init with block descriptors), AG3-H (HashMap instance) | — |
| AG7 | AG5 (interrupts work for timer FFI), AG6 (page tables for TTBR FFI) | — |
| AG8 | AG7 (FFI bridge working, proof hooks done) | AG5 (interrupt disable) |
| AG9 | AG4-AG8 (all implementation) | — |
| AG10 | AG1-AG9 (all work complete) | — |

---

## 6. Gate Criteria

Each phase has explicit success criteria that must be met before proceeding
to the next phase.

### 6.1 Per-Phase Gates

| Phase | Gate Criteria | Verification Command |
|-------|---------------|---------------------|
| AG1 | All 6 sub-tasks complete. `lake build` succeeds. `test_smoke.sh` passes. No new `sorry`/`axiom`. | `source ~/.elan/env && lake build && ./scripts/test_smoke.sh` |
| AG2 | All 3 sub-tasks complete. `cargo test --workspace` passes. `cargo clippy --workspace` clean. | `cd rust && cargo test --workspace && cargo clippy --workspace` |
| AG3 | All 8 sub-tasks complete. `lake build` succeeds for all new modules. `test_full.sh` passes. | `source ~/.elan/env && lake build && ./scripts/test_full.sh` |
| AG4 | Kernel boots on QEMU to UART banner. Exception vector table installed. MMU enabled. | `./scripts/test_qemu.sh` (boot test) |
| AG5 | Timer interrupt fires on QEMU at configured rate. GIC routes test interrupt. `timerTick` called from hardware path. | `./scripts/test_qemu.sh` (interrupt test) |
| AG6 | 4KB page table walk resolves test mappings on QEMU. TLB flush works. ASID allocation works. All VSpace invariants preserved. | `source ~/.elan/env && lake build && ./scripts/test_qemu.sh` (memory test) |
| AG7 | Lean kernel successfully calls Rust HAL. Production `AdapterProofHooks` instantiated. `lake build` passes. | `source ~/.elan/env && lake build` (all modules including proofs) |
| AG8 | All 7 sub-tasks complete. `test_full.sh` passes. All invariants preserved with new models. No `sorry`/`axiom`. | `source ~/.elan/env && lake build && ./scripts/test_full.sh` |
| AG9 | All tests pass on QEMU. Hardware constant cross-check verified (when hardware available). | `./scripts/test_qemu.sh` + hardware validation report |
| AG10 | All documentation synchronized. No website-linked paths broken. Codebase map regenerated. | `./scripts/test_full.sh && ./scripts/check_website_links.sh` |

### 6.2 Invariant Gates (Every Phase)

These must hold after every phase, without exception:

1. **Zero `sorry`/`axiom`**: `grep -rn 'sorry\|axiom' SeLe4n/ --include='*.lean' | grep -v test | grep -v fixture` returns empty.
2. **Build clean**: `source ~/.elan/env && lake build` succeeds.
3. **No regression**: `./scripts/test_smoke.sh` passes (minimum).
4. **Website links intact**: `./scripts/check_website_links.sh` passes.

### 6.3 Final Workstream Gate (AG10 Complete)

The WS-AG workstream is complete when ALL of the following hold:

1. All 67 sub-tasks across 10 phases are completed.
2. `./scripts/test_full.sh` passes.
3. Zero `sorry`/`axiom` in production proof surface.
4. Production `AdapterProofHooks` instantiated for `rpi5RuntimeContract`.
5. Kernel boots on QEMU with timer interrupts and syscall dispatch.
6. All documentation synchronized (spec, codebase map, workstream history).
7. Hardware constant cross-check completed (when RPi5 hardware available).

---

## 7. Scope Exclusions

The following items are explicitly OUT OF SCOPE for WS-AG and deferred to
future workstreams:

| Item | Rationale | Deferred To |
|------|-----------|-------------|
| SMP / multi-core support | RPi5 has 4 cores but H3 targets single-core only. SMP requires per-core run queues, IPI, spinlocks. | WS-V |
| DMA controller support | BCM2712 has DMA engines but H3 doesn't need them for basic kernel operation. | WS-V |
| GPU interaction | VideoCore VII GPU interaction deferred. | WS-V |
| PAC/BTI security hardening | Cortex-A76 supports PAC/BTI but they're not required for functional H3. | WS-V |
| MTE (Memory Tagging Extension) | Cortex-A76 does NOT support MTE. Not applicable. | N/A |
| Runtime DTB parsing for board detection | Static board constants sufficient for RPi5. Runtime DTB is nice-to-have. | WS-V |
| Named-structure migration (F-B04) | Deep tuple projections are a code quality issue, not H3-blocking. | WS-V |
| NEON/SVE register context | Floating-point register save/restore deferred (H3-ARCH-09). | WS-V |
| Full FrozenOps production integration | Depends on AG8-D decision. If deferred, goes to WS-V. | AG8-D / WS-V |
| Lean 4 native ARM64 compilation | H3 may cross-compile. Native ARM64 Lean compilation is toolchain-dependent. | Lean upstream |

---

## 8. Version and Tagging Strategy

| Phase Completion | Version Tag | Branch |
|------------------|-------------|--------|
| AG1 complete | v0.26.0 | `main` |
| AG2 complete | v0.26.1–v0.26.2 | `main` |
| AG3 complete | v0.26.3–v0.26.4 | `main` |
| AG4 complete | v0.26.5 | `main` |
| AG5 complete | v0.27.0 | `main` |
| AG6 complete | TBD | `main` |
| AG7 complete | TBD | `main` |
| AG8 complete | TBD | `main` |
| AG9 complete | TBD | `main` |
| AG10 complete (WS-AG COMPLETE) | TBD | `main` |

Version TBD marks the first hardware-ready release of seLe4n.

---

## 9. Finding Traceability Matrix

Every finding from both baseline audits is mapped to exactly one disposition
below. This ensures complete coverage — no finding is silently dropped.

### 9.1 Release Audit Traceability

| Finding ID | Disposition | Plan Reference |
|------------|-------------|----------------|
| F-S05 | Actionable | AG-DESC (AG8-E) |
| F-ST02 | No-Action | Section 2.3 |
| F-F04 | Actionable | AG-FF04 (AG1-E) |
| F-T02 | Actionable (corrected) | AG-FT02 (AG1-C), Section 2.1 |
| F-B04 | No-Action | Section 2.3, Scope Exclusion §7 |
| F-FP05 | No-Action | Section 2.3 |
| S-04 | Actionable (overstated) | AG-S04 (AG1-A), Section 2.1 |
| S-05 | Actionable | AG-S05 (AG1-B) |
| S-06 | No-Action | Section 2.3 |
| S-01 | No-Action | Section 2.3 |
| S-02 | No-Action | Section 2.3 |
| S-03 | No-Action | Section 2.3 |
| I-01 | Actionable | AG-TIMEOUT (AG8-A) |
| C-03 | No-Action | Section 2.3 |
| C-07 | No-Action | Section 2.3 |
| C-08 | No-Action | Section 2.3 |
| C-14 | No-Action | Section 2.3 |
| L-09 | No-Action | Section 2.3 |
| L-11 | No-Action | Section 2.3 |
| L-15 | No-Action | Section 2.3 |
| A-01 | No-Action | Section 2.3 |
| A-02 | No-Action | Section 2.3 |
| A-07 | No-Action | Section 2.3 |
| IF-02 | No-Action | Section 2.3 |
| IF-03 | No-Action | Section 2.3 |
| IF-11 | No-Action | Section 2.3 |
| RT-05 | No-Action | Section 2.3 |
| FO-03 | No-Action | Section 2.3 |
| SA-01 | No-Action | Section 2.3 |
| SA-02 | No-Action | Section 2.3 |
| SA-03 | No-Action | Section 2.3 |
| SA-04 | No-Action | Section 2.3 |
| P-01 | Actionable | AG-P01 (AG3-A) |
| P-02 | No-Action | Section 2.3 |
| P-03 | Actionable | AG-P03 (AG1-D) |
| P-04 | Actionable | AG-P04 (AG3-B) |
| P-05 | No-Action | Section 2.3 |
| P-06 | No-Action | Section 2.3 |
| P-07 | Actionable (dup) | AG-PHOOKS (AG7-D), Section 2.2 |
| P-08 | No-Action | Section 2.3 |
| R-01 | Actionable | AG-R01 (AG2-B) |
| R-02 | No-Action | Section 2.3 |
| R-03 | No-Action | Section 2.3 |
| R-04 | No-Action | Section 2.3 |
| R-05 | Actionable | AG-R05 (AG2-A) |
| T-01 | Actionable | AG-T01 (AG1-F) |
| T-02 | No-Action | Section 2.3 |
| T-03 | No-Action | Section 2.3 |
| T-04 | No-Action (INFO) | Section 2.3 |
| T-05 | No-Action (INFO) | Section 2.3 |
| T-06 | No-Action (INFO) | Section 2.3 |
| RH-02 | No-Action | Section 2.3 |
| RH-06 | No-Action | Section 2.3 |
| RT-03 | No-Action | Section 2.3 |
| FO-05 | No-Action | Section 2.3 |

### 9.2 H3 Hardware Binding Audit Traceability

| Finding ID | Disposition | Plan Reference |
|------------|-------------|----------------|
| FINDING-01 | Actionable | AG-HAL (AG4-A), Section 2.2 |
| FINDING-02 | Actionable | AG-PHOOKS (AG7-D), Section 2.2 |
| FINDING-03 | Actionable | AG-PTFMT/AG-PTWALK/AG-VSARM/AG-TTBR (AG6), Section 2.2 |
| FINDING-04 | Actionable | AG-EXCEPT (AG3-C) |
| FINDING-05 | Actionable (doc) | AG-SMP (AG10-A) |
| FINDING-06 | Actionable | AG-INTR (AG3-D) + AG-HIRQ (AG5-F), Section 2.2 |
| FINDING-07 | No-Action (doc-only) | Section 2.3, AG-IPCBUF (AG10-B) |
| FINDING-08 | Actionable | AG-TIMER (AG3-E), Section 2.2 |
| FINDING-RUST-01 | No-Action | Section 2.3 |
| FINDING-RUST-02 | No-Action | RegisterFile abstraction mismatch is intentional (7 ABI registers vs 32 GPR context). Trap handler (AG4-C) bridges the two representations. |
| FINDING-RUST-03 | Actionable (dup) | AG-HAL (AG4-A), Section 2.2 |
| FINDING-RUST-04 | Actionable | AG-RUST04 (AG2-C) |
| FINDING-PLAT-01 | Actionable | AG-HWCHECK (AG9-B) |
| FINDING-PLAT-02 | Duplicate | AG-PHOOKS (AG7-D), Section 2.2 |
| FINDING-PLAT-03 | Actionable | AG-MMIO (AG7-C) — MMIO model-to-hardware bridging |
| FINDING-PLAT-04 | No-Action | Section 2.3, Scope Exclusion §7 (runtime DTB deferred to WS-V) |
| FINDING-PLAT-05 | Actionable | AG-BOOT (AG4-E) — real boot sequence replaces model-only path |
| H3-ARCH-01 | Actionable | AG-PTFMT (AG6-A), AG-PTWALK (AG6-B) |
| H3-ARCH-02 | Actionable | AG-TLBI (AG6-E), AG-TLBINT (AG6-F) |
| H3-ARCH-03 | Actionable | AG-ISB (AG6-G) |
| H3-ARCH-04 | Actionable | AG-ASID (AG6-H) |
| H3-ARCH-05 | Actionable | AG-EL (AG3-F) |
| H3-ARCH-06 | Actionable | AG-SYSREG (AG3-G) |
| H3-ARCH-07 | Actionable | AG-DCACHE (AG8-B) |
| H3-ARCH-08 | Actionable | AG-BARRIER (AG8-C) |
| H3-ARCH-09 | Scope Exclusion | Section 7 (NEON/SVE deferred to WS-V) |
| H3-ARCH-10 | Actionable | AG-VSBE (AG3-H) |
| H3-PLAT-01 | Actionable (dup) | AG-PHOOKS (AG7-D), Section 2.2 |
| H3-PLAT-02 | Actionable | AG-GIC-D (AG5-A), AG-GIC-C (AG5-B) |
| H3-PLAT-03 | Actionable | AG-GTIMER (AG5-D) |
| H3-PLAT-04 | Actionable | AG-EVEC (AG4-B) |
| H3-PLAT-05 | Actionable | AG-MMU (AG4-F) |
| H3-PLAT-06 | Actionable | AG-UART (AG4-G) |
| H3-PLAT-07 | Actionable | AG-HWCHECK (AG9-B) |
| H3-PLAT-08 | Actionable | AG-BOOT (AG4-E) |
| H3-PLAT-09 | Actionable | AG-MMIO (AG7-C) — MMIO volatile read/write bridges model to hardware |
| H3-PLAT-10 | Scope Exclusion | Section 7 (runtime DTB parsing deferred to WS-V) |
| H3-RUST-01 | Actionable (dup) | AG-EVEC (AG4-B), Section 2.2 |
| H3-RUST-02 | Actionable | AG-TRAP (AG4-C) |
| H3-RUST-03 | Actionable | AG-FFI (AG7-A) |
| H3-RUST-04 | Actionable | AG-GIC-IRQ (AG5-C) |
| H3-RUST-05 | Actionable | AG-TLBI (AG6-E) |
| H3-RUST-06 | Actionable | AG-CACHE (AG6-I) |
| H3-RUST-07 | Actionable | AG-MSRMSR (AG7-B) |
| H3-RUST-08 | Actionable | AG-MMIO (AG7-C) |
| H3-RUST-09 | Actionable | AG-RUST04 (AG2-C) — consolidated with FINDING-RUST-04 |
| H3-RUST-10 | Actionable | AG-LINK (AG4-D) |
| H3-SCHED-01 | Actionable | AG-TICK (AG5-E) |
| H3-SCHED-02 | Actionable | AG-IDIS (AG5-G) |
| H3-SCHED-03 | Actionable | AG-RQPERF (AG9-D) |
| H3-SCHED-04 | Actionable | AG-TICK (AG5-E) — domain schedule timer precision subsumed by timer binding |
| H3-SCHED-05 | Actionable | AG-WCRT (AG9-C) |
| H3-IPC-01 | Actionable | AG-TIMEOUT (AG8-A) |
| H3-IPC-02 | Actionable | AG-TIMEOUT (AG8-A) — IPC buffer layout addressed via timeout sentinel migration, buffer itself correct per FINDING-07 |
| H3-IPC-03 | Actionable | AG-BADGE (AG9-E) |
| H3-IPC-04 | Actionable | AG-ATOMDON (AG8-G) |
| H3-PROOF-01 | Actionable (dup) | AG-PHOOKS (AG7-D), Section 2.2 |
| H3-PROOF-02 | Actionable | AG-TLBPF (AG7-E) |
| H3-PROOF-03 | Actionable | AG-DONATE (AG8-F) |
| H3-PROOF-04 | No-Action | `collectQueueMembers` fuel sufficiency already has formal argument sketch (AF-07) and `Option` return type (AE5-A). Full formalization deferred — low priority, non-blocking. |
| H3-PROOF-05 | Actionable | AG-FROZEN (AG8-D) |

