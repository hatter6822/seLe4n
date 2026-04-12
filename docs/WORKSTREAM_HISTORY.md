# Workstream History

This document is the canonical record of all completed and planned workstreams
for the seLe4n project. It consolidates workstream information that was
previously spread across README.md, GitBook chapters, and audit plans.

## How to use this document

- **New contributors**: skim the "What's next" section to understand current
  priorities, then jump to the linked audit plans for details.
- **Returning contributors**: check "What's next" for the current slice, then
  review the completed workstream closest to your area of interest.
- **Auditors**: use the portfolio table as a traceability index linking each
  workstream to its version, scope, and evidence.

## What's next

**Next milestone**: Raspberry Pi 5 hardware binding — ARMv8 page table walk,
GIC-400 interrupt routing, boot sequence. All pre-benchmark workstreams (WS-B
through WS-U Phase U8) are complete. **WS-U PORTFOLIO COMPLETE.**
WS-V Phases V1 through V8 are complete. **WS-V PORTFOLIO COMPLETE.**
WS-W Phases W1–W6 complete. **WS-W PORTFOLIO COMPLETE.**
WS-X Phases X1–X5 complete. **WS-X PORTFOLIO COMPLETE.**
WS-Y Phases Y1–Y3 complete. **WS-Y PORTFOLIO COMPLETE.**
WS-Z Phases Z1–Z10 complete. **WS-Z PORTFOLIO COMPLETE.**
WS-AA Phase AA1 complete. Phase AA2 complete.
WS-AB Phase D1 complete. Phase D2 complete. Phase D3 complete. Phase D4 complete. Phase D5 complete. Phase D6 complete. **WS-AB PORTFOLIO COMPLETE.**
WS-AC Phase AC6 complete. **WS-AC PORTFOLIO COMPLETE.**
WS-AD Phase AD1 complete.
WS-AD Phase AD2 complete.
WS-AD Phase AD3 complete.
WS-AD Phase AD4 complete. Phase AD5 complete. **WS-AD PORTFOLIO COMPLETE.**
WS-AE Phase AE1 complete. Phase AE2 complete. Phase AE3 complete. Phase AE4 complete. Phase AE5 complete. Phase AE6 complete. **WS-AE PORTFOLIO COMPLETE.**
WS-AF Phase AF1 complete. Phase AF2 complete. Phase AF3 complete. Phase AF4 complete. Phase AF5 complete. Phase AF6 complete. **WS-AF PORTFOLIO COMPLETE.**
WS-AG Phase AG1 complete. Phase AG2 complete. Phase AG2 Audit complete. Phase AG3 complete. Phase AG4 complete. Phase AG5 complete. Phase AG6 complete. Phase AG7 complete. Phase AG8 complete. Phase AG9 complete. Phase AG10 complete. **WS-AG PORTFOLIO COMPLETE.**
WS-AH Phase AH1 complete. Phase AH2 complete. Phase AH3 complete. Phase AH4 complete. Phase AH5 complete. **WS-AH PORTFOLIO COMPLETE.**
WS-AI Phase AI1 complete.

### WS-AI: Post-Audit Comprehensive Remediation (IN PROGRESS)

- **Phase AI1 COMPLETE** (v0.27.7): Rust ABI & Trap Correctness — 5 sub-tasks (AI1-A through AI1-E). AI1-A (H-05/HIGH): Fixed exception error codes in `trap.rs` from discriminant 43 (`AlignmentError`) to 45 (`UserException`) for alignment and unknown exceptions — aligns with Lean `ExceptionModel.lean:175-177` mapping of `pcAlignment`, `spAlignment`, `unknownReason` to `.error .userException`. Added `error_code` module with named constants replacing bare numeric literals. AI1-B (H-04/HIGH): SVC handler stub now returns `NOT_IMPLEMENTED` (17) instead of success (0) — prevents userspace from interpreting no-op as success; TODO marker for WS-V/AG10 FFI wiring. AI1-C (M-26/MEDIUM): Eliminated dual timer reprogram path — removed `increment_tick_count()` from `handle_irq()` in `trap.rs`; canonical tick accounting path is `ffi_timer_reprogram()` in `ffi.rs` which calls both `reprogram_timer()` and `increment_tick_count()`. AI1-D (M-27/MEDIUM): Made `BOOT_UART` safe with `AtomicBool`-based `UartLock` spinlock — replaced `pub static mut BOOT_UART` with module-private `BOOT_UART_INNER` + `UART_LOCK`; updated `with_boot_uart()`, `init_boot_uart()`, `boot_puts()`, `kprint!` macro for synchronized access; eliminates UB after interrupts enabled. Gate: `cargo test --workspace` (366 tests) + `cargo clippy --workspace` (0 warnings) + `test_smoke.sh`. Zero sorry/axiom. See `docs/audits/AUDIT_v0.27.6_WORKSTREAM_PLAN.md`

### WS-AH: Pre-Release Comprehensive Audit Remediation (PORTFOLIO COMPLETE)

- **Phase AH5 COMPLETE** (v0.27.6): Documentation, Testing & Closure — 6 sub-tasks (AH5-A through AH5-F). AH5-A (M-04/M-07): Design-rationale documentation — VSpaceRoot boot exclusion rationale in `bootSafeObject` (Boot.lean), `pendingMessage` NI visibility analysis in `projectKernelObject` (Projection.lean). AH5-B (M-05/M-06/L-13): Specification-level documentation in `SELE4N_SPEC.md` — Platform Testing Limitations (Section 6.6), CNode Intermediate Rights Divergence (Section 8.10.3), TPIDR_EL0/TLS Gap (Section 6.5.6). AH5-C (M-08/L-11/L-12): Defense-in-depth documentation — cross-subsystem composition coverage assessment (CrossSubsystem.lean), Badge constructor safety analysis (Prelude.lean), `maxControlledPriority` default rationale (Types.lean). AH5-D: Test fixture verification (trace output unchanged). AH5-E: Full documentation synchronization (CHANGELOG, WORKSTREAM_HISTORY, DEVELOPMENT, README, CLAUDE.md, CLAIM_EVIDENCE_INDEX, SELE4N_SPEC, GitBook). AH5-F: Final gate — `test_full.sh` + `cargo test --workspace` + sorry/axiom scan + version sync + website links. Gate: `test_full.sh` + `cargo test --workspace` + documentation sync verified. Zero sorry/axiom. See `docs/audits/AUDIT_v0.27.1_WORKSTREAM_PLAN.md`

- **Phase AH4 COMPLETE** (v0.27.5): Version Consistency & CI Automation — 6 sub-tasks (AH4-A through AH4-F). AH4-A (H-02/HIGH): Updated `KERNEL_VERSION` in `rust/sele4n-hal/src/boot.rs` from `0.26.8` to `0.27.5` — UART boot banner now prints correct version; Rust workspace version in `rust/Cargo.toml` updated from `0.27.1` to `0.27.5` (propagates to all 4 crates via workspace inheritance). AH4-B: CLAUDE.md project description version reference updated from `0.26.9` to `0.27.5`. AH4-C: `docs/spec/SELE4N_SPEC.md` "Package version" table entry updated from `0.27.0` to `0.27.5`. AH4-D: All 10 i18n README version badges updated from `0.26.6` to `0.27.5`. AH4-E: Created `scripts/check_version_sync.sh` — CI-safe shell script validating 15 version-bearing files against canonical `lakefile.toml` version; follows project style (GPL header, `set -euo pipefail`). AH4-F: Integrated `check_version_sync.sh` into Tier 0 hygiene (`test_tier0_hygiene.sh`) via `run_check "HYGIENE"` — version sync enforced on every PR and push. Gate: `cargo test --workspace` + `test_smoke.sh` + `check_version_sync.sh`. Zero sorry/axiom. See `docs/audits/AUDIT_v0.27.1_WORKSTREAM_PLAN.md`

- **Phase AH3 COMPLETE** (v0.27.4): Capability, Architecture & Decode Hardening — 3 sub-tasks (AH3-A through AH3-C). AH3-A (L-04): Fixed `cspaceRevokeCdtStrict` CDT-orphan bug — error branch now preserves CDT node instead of removing it on slot deletion failure, preventing orphaned capabilities; preservation theorem simplified (unchanged state trivially preserves invariants). AH3-B (L-08): Refactored `setIPCBufferOp` to delegate to `storeObject` instead of manual struct-with replication — eliminates maintenance divergence risk; `setIPCBufferOp_capabilityRefs_eq` renamed to `setIPCBufferOp_capabilityRefs_cleaned` reflecting canonical `storeObject` cleanup semantics; cross-subsystem bridge verified unchanged. AH3-C (L-14): Replaced hardcoded ASID limit `65536` with `maxASID : Nat` parameter in `decodeVSpaceMapArgs` and `decodeVSpaceUnmapArgs` — API dispatch arms pass `st.machine.maxASID`; 10+ theorems updated with parameter threading; delegation theorems restructured from function-level to state-specific equality using `funext`; 12 test call sites updated (6 DecodingSuite, 5 NegativeStateSuite, 1 MainTraceHarness). Gate: `lake build` (256 jobs) + `test_smoke.sh`. Zero sorry/axiom. See `docs/audits/AUDIT_v0.27.1_WORKSTREAM_PLAN.md`

- **Phase AH2 COMPLETE** (v0.27.3): IPC Donation Safety & Boot Pipeline — 7 sub-tasks (AH2-A through AH2-G). AH2-A (M-02/MEDIUM): `applyCallDonation` return type changed from `SystemState` to `Except KernelError SystemState` — donation errors now propagate instead of being silently swallowed; 5 control-flow paths updated (4 no-op `.ok st`, 1 error `.error e`). AH2-B (M-02): `applyReplyDonation` same error propagation pattern with `removeRunnable` on success. AH2-C (M-02): Updated 7 API/donation call sites from direct binding to match-based error propagation; updated `dispatchWithCap_call_uses_withCaps` theorem; 4 test call sites updated. AH2-D (M-02): 4 preservation theorems updated to conditional postconditions (`applyCallDonation_scheduler_eq`, `applyCallDonation_machine_eq`, `applyReplyDonation_machine_eq`, `applyCallDonation_preserves_projection`). AH2-E (M-03/L-16): `defaultMachineConfig` constant (ARM64 defaults), `PlatformConfig.machineConfig` field with default. AH2-F (M-03/L-16): `applyMachineConfig` integrated as final step of `bootFromPlatform`; 8 new preservation lemmas; 10+ boot theorem proofs updated; `bootFromPlatform_machine_eq` replaced with `bootFromPlatform_machine_physicalAddressWidth` and `bootFromPlatform_machine_non_config_fields`. AH2-G (L-02): `timeoutAwareReceive` returns `.error .endpointQueueEmpty` for missing `pendingMessage` instead of `.ok (.completed IpcMessage.empty, st)`. Gate: `lake build` (256 jobs) + `test_smoke.sh`. Zero sorry/axiom. See `docs/audits/AUDIT_v0.27.1_WORKSTREAM_PLAN.md`

- **Phase AH1 COMPLETE** (v0.27.2): Critical IPC Dispatch Correctness — 5 sub-tasks (AH1-A through AH1-E). AH1-A (H-01/HIGH): `endpointSendDualChecked` now delegates to `endpointSendDualWithCaps` instead of `endpointSendDual` — checked `.send` path performs IPC capability transfer on rendezvous, matching the unchecked path; 3 new parameters (`endpointRights`, `senderCspaceRoot`, `receiverSlotBase`); return type `Kernel Unit` → `Kernel CapTransferSummary`. AH1-B: Updated `dispatchWithCapChecked` `.send` arm to pass cap transfer parameters. AH1-C: Updated 8 NI theorems across 3 files (Wrappers.lean, Soundness.lean, Operations.lean) — equivalence, flow-denied, denied-preserves-state, enforcement sufficiency, soundness, flow-denied-bundle, bridge, NI preservation. AH1-D (M-01/MEDIUM): Wired `validateVSpaceMapPermsForMemoryKind` into `.vspaceMap` dispatch — device regions with execute permission now return `.error .policyDenied`; updated `dispatchWithCap_vspaceMap_delegates` theorem. AH1-E: Updated 10 call sites across 3 test files. Gate: `lake build` (256 jobs) + `test_smoke.sh` + `test_full.sh`. Zero sorry/axiom. See `docs/audits/AUDIT_v0.27.1_WORKSTREAM_PLAN.md`

### WS-AG: H3 Hardware Binding Audit Remediation (PORTFOLIO COMPLETE)

- **Phase AG10 COMPLETE** (v0.27.1): Documentation + Closure — 7 sub-tasks (AG10-A through AG10-G). AG10-A (FINDING-05, Multi-Core Limitation Documentation): Added "Hardware Limitations" section to `SELE4N_SPEC.md` (Section 6.4) documenting single-core operation (core 0 only, other cores in WFE loop), SMP deferral to WS-V with requirements (per-core run queues, IPI, spinlocks, cache coherency, per-core TLB coordination), sequential memory model under single-core, and absence of multi-core invariants. AG10-B (FINDING-07, IPC Buffer Alignment Documentation): Added Section 8.5.1 to `SELE4N_SPEC.md` documenting 512-byte IPC buffer alignment (Lean model), 960-byte `#[repr(C)]` Rust ABI struct, Cortex-A76 cache line justification (8 × 64-byte lines), `ipcBuffer_within_page` theorem (512 + 960 = 1472 < 4096). AG10-C (Architecture Assumptions Update): Extended `Architecture/Assumptions.lean` with comprehensive documentation for AG3-C (exception model), AG3-D (interrupt dispatch), AG3-E (timer binding), AG3-F (exception levels), AG6-A/B (ARMv8 page tables), AG6-C/D (VSpace ARMv8 instance), AG6-H (ASID manager), AG6-F/G (TLB model), AG8-B (cache coherency model), and ARM64-specific constraints (single-core, sequential model, GIC range, timer frequency, page granule). AG10-D (SELE4N_SPEC.md Update): Added "Hardware Binding Architecture" section (6.5) with layered architecture diagram, subsections for Exception Handling (6.5.1), Interrupt Dispatch (6.5.2), Timer Binding (6.5.3), Memory Management ARMv8 (6.5.4), and FFI Bridge (6.5.5); updated H3 status to COMPLETE in Path to Hardware table; updated NI constructor count 34→35. AG10-E (Codebase Map Regeneration): Regenerated `docs/codebase_map.json` via `generate_codebase_map.py --pretty` with updated version 0.27.1, 141 production files, 91,466 production LoC, 2,725 theorem/lemma declarations. AG10-F (WORKSTREAM_HISTORY.md Update): Added WS-AG AG10 entry; changed WS-AG status from IN PROGRESS to PORTFOLIO COMPLETE; version range v0.26.0–v0.27.1 (10 phases, 67 sub-tasks). AG10-G (README.md Metrics Sync): Updated README.md metrics table, added single-core limitation note, version bump 0.27.0→0.27.1; CHANGELOG.md AG10 entry; Rust workspace version sync; DEVELOPMENT.md and CLAIM_EVIDENCE_INDEX.md synchronized; GitBook chapters updated. Gate: `lake build` + `test_full.sh` + documentation sync. Zero sorry/axiom.

- **Phase AG9 COMPLETE** (v0.27.0): Testing + Validation — 7 sub-tasks (AG9-A through AG9-G). AG9-A (QEMU Integration Testing): New `scripts/test_qemu.sh` — builds kernel binary via `cargo build --release --target aarch64-unknown-none`, launches QEMU `raspi4b`, validates UART boot output, checks for fatal exceptions; graceful CI skip when QEMU unavailable; boot expected fixture at `tests/fixtures/qemu_boot_expected.txt`. AG9-B (H3-PLAT-07, Hardware Cross-Check): New `scripts/test_hw_crosscheck.sh` — validates 15 BCM2712 constants from `Board.lean` on physical RPi5 (GIC addresses, timer frequency, memory regions, address widths); architecture invariants (ARM64, 4KiB pages) verified; documentation at `docs/hardware_validation/rpi5_cross_check.md`. AG9-C (H3-SCHED-05, WCRT Empirical Validation): New `profiling` module in `rust/sele4n-hal/src/profiling.rs` — `read_cycle_counter()` (PMCCNTR_EL0), `enable_cycle_counter()` (PMU setup), `LatencyStats` min/max/mean accumulator; documentation at `docs/hardware_validation/wcrt_empirical_validation.md`. AG9-D (H3-SCHED-03, RunQueue Cache Performance): Profiling infrastructure using AG9-C `LatencyStats` for RunQueue insert/remove/selection cycle counting; two-stage selection hit rate analysis; documentation at `docs/hardware_validation/runqueue_cache_performance.md`. AG9-E (H3-IPC-03, Badge Overflow Validation): `tests/BadgeOverflowSuite.lean` — 22 tests (BOV-001..022) covering round-trip identity, overflow/truncation, bor semantics, boundary values, theorem cross-checks; 7 new Rust tests in `sele4n-types` (`badge_zero_roundtrip`, `badge_max_u64_roundtrip`, `badge_power_of_two_roundtrips`, `badge_bor_max_values`, `badge_bor_disjoint_bits`, `badge_u64_size_is_8_bytes`, `badge_midrange_value`); registered as `lake exe badge_overflow_suite`; integrated into Tier 2 negative tests; documentation at `docs/hardware_validation/badge_overflow_validation.md`. AG9-F (Speculation Barriers): CSDB/SB in `barriers.rs` for Spectre v1/v2 on Cortex-A76 — `csdb()`, `sb()`, `speculation_safe_bound_check()`, `has_feat_csv2()`; deployed at exception dispatch (`trap.rs:handle_synchronous_exception` CSDB after ESR EC classification) and GIC dispatch (`gic.rs:dispatch_irq` CSDB after INTID bounds check); 7 unit tests; pre-existing clippy warnings in `mmio.rs` fixed (`is_multiple_of`); documentation at `docs/hardware_validation/speculation_barriers.md`. AG9-G (Full RPi5 Test Suite): `scripts/test_hw_full.sh` — 5-phase orchestration: Lean Tier 0-3, Rust workspace, Badge overflow, hardware cross-check, QEMU integration; report template at `docs/hardware_validation/rpi5_full_test_report.md`. New directory: `docs/hardware_validation/` (6 reports). Gate: `lake build` + `test_smoke.sh` + `cargo test --workspace` (362 tests) + `cargo clippy --workspace` (0 warnings). Zero sorry/axiom.

- **Phase AG8 COMPLETE** (v0.26.9): Integration + Model Closure — 7 sub-tasks (AG8-A through AG8-G). AG8-A (H3-IPC-01/I-01): Migrated timeout signaling from fragile sentinel value `0xFFFFFFFF` in GPR x0 to explicit `timedOut : Bool` TCB field — `timeoutThread` sets `timedOut := true`, `timeoutAwareReceive` checks `tcb.timedOut` and clears on success; eliminates collision risk with legitimate IPC data; BEq instance updated to 22 field comparisons; `timeoutErrorCode` constant removed. AG8-B (H3-ARCH-07): Cache coherency model in new `Architecture/CacheModel.lean` — `CacheLineState` (invalid/clean/dirty), `CacheState` with D-cache/I-cache function fields; operations: `dcClean`/`dcInvalidate`/`dcCleanInvalidate`/`icInvalidateAll`/`dcZeroByVA`; 17 preservation theorems covering all 5 operations including `empty_cacheCoherent`, `icInvalidateAll_coherent`, `pageTableUpdate_icache_coherent` composition, `dcInvalidate_makes_line_invalid`, `dcZeroByVA_makes_line_dirty`. AG8-C (H3-ARCH-08): Memory barrier semantics formalization in `MmioAdapter.lean` — `BarrierKind` (dmb_ish/dsb_ish/isb), `barrierOrdered` predicate; 4 theorems: `barrierOrdered_trivial`, `dsb_isb_guarantees_tlb_visibility`, `dmb_guarantees_mmio_ordering`, `dsb_guarantees_mmio_completion`; sequential model barriers trivially ordered. AG8-D (H3-PROOF-05): FrozenOps production decision — deferred to WS-V; 24 operations have preservation theorems and commutativity proofs complete, but frozen-phase type gap (e.g., `FrozenTCB` missing `timedOut` after AG8-A) and partial mutation concerns (AE2-D) warrant continued experimental status; all 4 FrozenOps files annotated "Experimental — deferred to WS-V (AG8-D)". AG8-E (F-S05): CDT `descendantsOf` fuel sufficiency placeholders — `maxCdtDepth : Nat := 65536` constant based on RPi5 maximum kernel objects; `descendantsOf_fuel_sufficient` proves only `Nat ≥ 0` (tautology — placeholder, not substantive fuel sufficiency); `cdtDepth_bounded_by_maxCdtDepth` is `P → P` identity (placeholder); substantive proofs deferred to WS-V. AG8-F (H3-PROOF-03): Donation chain k>2 cycle prevention building blocks — `donationChainAcyclic_general` re-extracts blocked-on-reply state from `donationOwnerValid` (unused `_hDCA` hypothesis carried for API completeness); `blockedOnReply_cannot_call` proves blocked threads cannot initiate new calls; formal bridge from donation edges to `blockingAcyclic` sub-relation deferred to WS-V. AG8-G (H3-IPC-04): Donation atomicity under interrupt disable — `donationAtomicRegion` predicate asserting `interruptsEnabled = false`; `donateSchedContext_machine_eq` proves machine state preserved through donation; three-component atomicity argument (AG5-G region + PIP locality + machine preservation). Additional: fixed pre-existing unused simp warnings in `RuntimeContract.lean` and `ProofHooks.lean`. New file: `CacheModel.lean`. Gate: `lake build` (256 jobs) + `test_full.sh`. Zero sorry/axiom.

- **Phase AG7 COMPLETE** (v0.26.8): FFI Bridge + Proof Hooks — 6 sub-tasks (AG7-A through AG7-F). AG7-A: Lean `@[extern]` FFI declarations in `SeLe4n/Platform/FFI.lean` for 17 Rust HAL functions (timer, GIC, TLB, MMIO, UART, interrupts); corresponding `#[no_mangle] pub extern "C"` wrappers in `rust/sele4n-hal/src/ffi.rs`. AG7-B: System register accessors in `rust/sele4n-hal/src/registers.rs` — `read_sysreg!`/`write_sysreg!` macros, 18 ARM64 system register accessor functions (SCTLR_EL1, TCR_EL1, TTBR0/1_EL1, MAIR_EL1, VBAR_EL1, ESR_EL1, ELR_EL1, FAR_EL1, SPSR_EL1, MPIDR_EL1, CTR_EL0, DAIF, CurrentEL, CNTPCT_EL0, CNTFRQ_EL0, CNTP_CTL_EL0, CNTP_CVAL_EL0, SP_EL0). AG7-C: MMIO volatile read/write primitives in `rust/sele4n-hal/src/mmio.rs` — `mmio_read32`/`mmio_write32`/`mmio_read64`/`mmio_write64` using `read_volatile`/`write_volatile` with alignment debug assertions. AG7-D: Production `AdapterProofHooks` (`rpi5ProductionAdapterProofHooks`) with substantive preservation proofs for all 4 adapter paths (timer, register write, memory read, context switch). `proofLayerInvariantBundle` extended to 11 conjuncts with `notificationWaiterConsistent`. `contextMatchesCurrent` definition changed to BEq equality for proof tractability with non-lawful RegisterFile BEq. `registerContextStableCheck_budget` bridge theorem and `contextSwitchState_preserves_ipcInvariantFull` (15-conjunct IPC with `passiveServerIdle` transfer). AG7-E: TLB flush composition theorems (carried from AG6, verified complete). AG7-F: End-to-end context-switch preservation — `contextSwitchState_preserves_proofLayerInvariantBundle` (11-conjunct, 7 hypotheses: TCB lookup, BEq register match, dequeue-on-dispatch, time-slice positivity, IPC readiness, EDF compatibility, budget sufficiency); 3 end-to-end theorems for production contract (`rpi5Production_adapterContextSwitch_preserves`, `rpi5Production_adapterAdvanceTimer_preserves`, `rpi5Production_adapterWriteRegister_preserves`). New files: `FFI.lean`, `ffi.rs`, `mmio.rs`. Gate: `lake build` (256 jobs) + `cargo test --workspace` + `test_smoke.sh` + `test_full.sh`. Zero sorry/axiom.

- **Phase AG6 COMPLETE** (v0.26.7): Memory Management (ARMv8 Page Tables) — 9 sub-tasks (AG6-A through AG6-I). AG6-A (H3-ARCH-01): ARMv8 page table descriptor types in `PageTable.lean` — `PageTableLevel` (L0–L3), `Shareability` (nonShareable/inner/outer), `AccessPermission` (kernelRW/kernelRO/userRW/userRO), `PageAttributes` (ap/shareability/af/pxn/uxn), `PageTableDescriptor` (invalid/block/table/page); `descriptorToUInt64`/`uint64ToDescriptor` encode/decode; `encodePageAttributes`/`decodePageAttributes`; W^X bridge proof `hwDescriptor_wxCompliant_bridge`. AG6-B (H3-ARCH-01): 4-level page table walk — `l0Index`/`l1Index`/`l2Index`/`l3Index` with bound proofs (div/mod for omega compatibility); `readUInt64` (little-endian), `readDescriptor`; `pageTableWalk` via structural recursion on `PageTableLevel` (no fuel); `pageTableWalk_deterministic` proof; `pageTableWalkPerms` convenience wrapper. AG6-C (H3-ARCH-01): `VSpaceBackend` ARMv8 instance in `VSpaceARMv8.lean` — `BumpAllocator` (next/limit), `ARMv8VSpace` (root/memory/allocator/shadow); shadow-first design: `mapPage`/`unmapPage` update shadow `VSpaceRoot` then write hardware page tables; `lookupPage` delegates to shadow for proof tractability; `ensureTable` L0→L3 table chain allocation; `zeroPage`/`writeDescriptor` hardware helpers. AG6-D (H3-ARCH-01): Shadow-based refinement proof — `simulationRelation` (hardware walk agrees with shadow for all mapped VAddrs); `lookupPage_refines` and `hwLookupAddr_refines` refinement theorems; `vspaceProperty_transfer` master invariant transfer theorem. AG6-E (H3-RUST-05): TLB flush instruction wrappers in `tlb.rs` — `tlbi_vmalle1()`, `tlbi_vae1(asid, vaddr)`, `tlbi_aside1(asid)`, `tlbi_vale1(asid, vaddr)`; each followed by DSB ISH + ISB per ARM ARM D8.11; `cfg(target_arch = "aarch64")` guards; 7 tests (compilation + operand encoding validation). AG6-F (H3-ARCH-02): TLB flush model integration in `TlbModel.lean` — `adapterFlushTlbHw`/`adapterFlushTlbByAsidHw`/`adapterFlushTlbByVAddrHw` hardware adapter functions; 3 hardware-model equivalence theorems; 3 consistency preservation theorems; `vspaceUnmapPage_fullFlush_preserves_tlbConsistent` composition theorem. AG6-G (H3-ARCH-03): TLB barrier model — `tlbBarrierComplete` predicate (trivially True in abstract model); `adapterFlushTlbHw_barrierComplete` and `adapterFlushTlbByAsidHw_barrierComplete` barrier completion theorems; `adapterFlushTlbHw_safe` combined safety theorem. AG6-H (H3-ARCH-04): ASID management in `AsidManager.lean` — `AsidPool` bump allocator with generation tracking and free list; `AsidPool.allocate` (3 strategies: free list reuse, bump, rollover with exhaustion guard); `AsidPool.free`; `wellFormed` predicate with 3 preservation theorems (`initial_wellFormed`, `allocate_preserves_wellFormed`, `allocate_asid_valid`); `asidPoolUnique` uniqueness invariant with `allocate_fresh`/`free` preservation. AG6-I (H3-RUST-06): Cache maintenance in `cache.rs` — `dc_civac`/`dc_cvac`/`dc_ivac`/`dc_zva`/`ic_iallu`/`ic_ialluis`; `cache_range(op, start, end)` aligned iteration; `clean_invalidate_range`/`clean_range`/`invalidate_range` convenience wrappers; 11 tests. New files: `PageTable.lean`, `VSpaceARMv8.lean`, `AsidManager.lean`, `tlb.rs`, `cache.rs`. ~1005 lines Lean + ~406 lines Rust + ~113 lines TlbModel.lean extensions. Gate: `cargo test --workspace` (306 tests), `cargo clippy --workspace` (0 warnings), `lake build` (256 jobs) + `test_smoke.sh` + `test_full.sh`. Zero sorry/axiom.

- **Phase AG5 COMPLETE** (v0.26.6): Interrupts + Timer — 7 sub-tasks (AG5-A through AG5-G). AG5-A/B (H3-PLAT-02): GIC-400 distributor + CPU interface initialization in `gic.rs` — `init_distributor()` configures GICD_CTLR, GICD_IGROUPR (Group 0), GICD_IPRIORITYR (0xA0 default), GICD_ITARGETSR (CPU 0), GICD_ICPENDR (clear), GICD_ISENABLER (enable); `init_cpu_interface()` configures GICC_PMR=0xFF, GICC_BPR=0, GICC_CTLR=1; distributor base 0xFF841000, CPU interface base 0xFF842000 (BCM2712). AG5-C (H3-RUST-04): GIC-400 acknowledge/dispatch/EOI — `acknowledge_irq()` reads GICC_IAR, `end_of_interrupt(intid)` writes GICC_EOIR, `dispatch_irq<F>()` composes acknowledge→spurious check (INTID≥1020)→handler→EOI; `init_gic()` convenience function; 14 unit tests. AG5-D (H3-PLAT-03): ARM Generic Timer driver in `timer.rs` — system register accessors (`read_counter`/`read_frequency`/`set_comparator`/`enable_timer`/`disable_timer`/`is_timer_pending`), `AtomicU64` state (`TICK_COUNT`/`TIMER_INTERVAL`), `init_timer(tick_hz)` computes interval from frequency, `reprogram_timer()` counter-relative advancement; RPi5 54 MHz, default 1000 Hz; 8 unit tests. AG5-E (H3-SCHED-01): Timer interrupt → `timerTick` binding — `TimerInterruptBinding` structure in `TimerModel.lean` with `handleTimerInterrupt` (acknowledge→timerTick→reprogram), 4 preservation theorems; `timerInterruptHandler` in `InterruptDispatch.lean` delegates to `timerTick`, `handleInterrupt_timer` dispatch theorem. AG5-F (FINDING-06): `handleInterrupt` kernel integration — `NonInterferenceStep.handleInterrupt` constructor in `Composition.lean` (35th `KernelOperation`), NI coverage proof 34→35, `step_preserves_projection` extended; `handleInterrupt_crossSubsystemInvariant_bridge` in `CrossSubsystem.lean`. AG5-G (H3-DAIF): Interrupt-disabled region model — Rust: `interrupts.rs` with `disable_interrupts()`/`restore_interrupts()`/`enable_irq()`/`with_interrupts_disabled<F,R>()`/`are_interrupts_enabled()`, 4 tests; Lean: `MachineState.interruptsEnabled` field, `disableInterrupts`/`enableInterrupts`/`withInterruptsDisabled` operations, 7 frame theorems; AG5-G atomicity proofs in `ExceptionModel.lean`: `saveOutgoingContext_preserves_interruptsEnabled`, `restoreIncomingContext_preserves_interruptsEnabled`, `setCurrentThread_preserves_interruptsEnabled`, `interruptDispatchSequence_preserves_interruptsEnabled_spurious`. New file: `interrupts.rs`. Gate: `cargo test --workspace` (281 tests), `cargo clippy --workspace` (0 warnings), `lake build` (256 jobs) + `test_smoke.sh`. Zero sorry/axiom.

- **Phase AG4 COMPLETE** (v0.26.5): HAL Crate + Boot Foundation — 7 sub-tasks (AG4-A through AG4-G). AG4-A (FINDING-01/RUST-03): Created `sele4n-hal` crate — ARM64 HAL for seLe4n kernel (`#![no_std]`, `#![allow(unsafe_code)]`); modules: `cpu` (WFE/WFI/NOP/ERET/`current_core_id`), `barriers` (DMB ISH/SY, DSB ISH/SY, ISB), `registers` (MRS/MSR macros, 11 system register accessors), `uart`, `mmu`, `trap`, `boot`, `gic` (stub), `timer` (stub); `build.rs` assembles `.S` files via `cc` crate; `cfg(target_arch = "aarch64")` guards for cross-platform compilation. AG4-B (H3-PLAT-04): ARM64 exception vector table in `vectors.S` — 16 entries (4 exception types × 4 source states), 2048-byte aligned for VBAR_EL1; Current EL SPx → `__el1_sync/irq/serror_entry`, Lower EL AArch64 → `__el0_sync/irq/serror_entry`. AG4-C (H3-RUST-02): Trap entry/exit assembly in `trap.S` — `save_context`/`restore_context` macros (31 GPRs + SP_EL0 + ELR_EL1 + SPSR_EL1, 272 bytes); `TrapFrame` Rust struct with compile-time 272-byte assertion; ESR EC dispatch (SVC→syscall stub, abort→vmFault, alignment→userException); `handle_irq` stub, `handle_serror` fatal halt. AG4-D (H3-RUST-10): Kernel linker script `link.ld` — entry `_start` at 0x80000; sections `.text.boot`→`.text.vectors` (2048-aligned)→`.text`→`.rodata`→`.data`→`.bss`→`.bss.page_tables` (4096-aligned)→`.stack` (64 KiB). AG4-E (H3-PLAT-08): Boot sequence in `boot.S`/`boot.rs` — assembly: MPIDR core check, DTB save, BSS zero, stack setup, branch to `rust_boot_main`; Rust: UART init→boot banner→MMU init→VBAR set→hardware summary→idle loop. AG4-F (H3-PLAT-05): MMU initialization in `mmu.rs` — MAIR (Normal WB/Device-nGnRnE/Normal NC), TCR (48-bit VA, 4KiB, 44-bit PA), identity-mapped L1 with 1 GiB block descriptors (3×RAM + 1×Device), SCTLR M+C+I, DSB+ISB barriers. AG4-G (H3-PLAT-06): PL011 UART driver — base 0xFE201000 (Board.lean `uart0Base`), 48 MHz/115200 baud, 8N1+FIFO, `kprint!`/`kprintln!` macros. New crate: `sele4n-hal` (4th workspace member). ~900 lines Rust + ~300 lines assembly. Gate: `cargo test --workspace` (267 tests), `cargo clippy --workspace` (0 warnings), `lake build` + `test_smoke.sh`. Zero sorry/axiom.

- **Phase AG3 COMPLETE** (v0.26.4): Platform Model Completion + post-implementation audit — 8 sub-tasks (AG3-A through AG3-H). AG3-A (P-01): `classifyMemoryRegion` refactored to accept platform memory map (`List MemoryRegion`) for address-based classification; `classifyAddress` standalone function added; `classifyAddress_unmapped` and `classifyAddress_found` correctness theorems proven. AG3-B (P-04): `applyMachineConfig` extended to copy all 7 `MachineConfig` fields (was: only `physicalAddressWidth`); 6 new `MachineState` fields (`registerWidth`, `virtualAddressWidth`, `pageSize`, `maxASID`, `memoryMap`, `registerCount`); `MemoryKind`/`MemoryRegion` definitions moved before `MachineState`; 6 new field-correctness theorems proven via `rfl`. AG3-C (FINDING-04): ARM64 exception model — `ExceptionType` (synchronous/irq/fiq/serror), `ExceptionSource` (4 variants), `SynchronousExceptionClass` (svc/dataAbort/instrAbort/pcAlignment/spAlignment/unknownReason), `ExceptionContext` structure; `classifySynchronousException` via ESR EC field extraction (bits [31:26]); `dispatchSynchronousException` routing SVC→`syscallEntry`, aborts→`.vmFault`; `dispatchException` top-level routing with 6 theorems. AG3-D (FINDING-06): Interrupt dispatch — `InterruptId` (`Fin 224` for GIC-400), `timerInterruptId` (PPI 30); `acknowledgeInterrupt`/`endOfInterrupt`/`handleInterrupt`; `interruptDispatchSequence` composing acknowledge→handle→EOI; timer interrupt→`timerTick`, mapped IRQ→`notificationSignal`, unmapped→`.invalidIrq`; IRQ branch wired into `dispatchException`; 3 preservation theorems. AG3-E (FINDING-08): Hardware timer model — `HardwareTimerConfig` with `counterFrequencyHz`/`tickIntervalNs`/`comparatorValue`; `hardwareTimerToModelTick` with monotonicity proof; `reprogramComparator` for evenly-spaced interrupts; `rpi5TimerConfig` at 54 MHz (54000 counts/tick proven via `decide`). AG3-F (H3-ARCH-05): Exception level model — `ExceptionLevel` (el0/el1); `exceptionLevelFromSpsr`/`exceptionLevelFromSource`; `canAccessSystemRegisters`/`canExecutePrivileged` privilege predicates. AG3-G (H3-ARCH-06): System register model — `SystemRegisterFile` (10 ARM64 system registers: ELR, ESR, SPSR, FAR, SCTLR, TCR, TTBR0, TTBR1, MAIR, VBAR); `SystemRegisterIndex` enum; `readSystemRegister`/`writeSystemRegister` operations; 4 frame lemmas (regs, memory, timer preservation + read-after-write). AG3-H (H3-ARCH-10): `hashMapVSpaceBackend` instance for `VSpaceRoot` — all 8 typeclass obligations discharged (2 ASID preservation, 2 round-trip, 4 non-interference); `rootWF = invExtK`. `KernelError` extended from 44→49 variants: `vmFault`, `userException`, `hardwareFault`, `notSupported`, `invalidIrq`. New files: `ExceptionModel.lean`, `InterruptDispatch.lean`, `TimerModel.lean`. Gate: `lake build` + `test_full.sh`. Zero sorry/axiom.

- **Phase AG2 Audit COMPLETE** (v0.26.2): Post-implementation audit of AG2. Fixed critical `sched_context_configure` IPC buffer overflow bug — the 5th parameter (domain) was never written to the IPC buffer overflow slot; on ARM64 hardware, the kernel's `requireMsgReg decoded.msgRegs 4` would read a stale/zero value. Added `&mut IpcBuffer` parameter and `buf.set_mr(4, encoded[4])?` matching the `service_register` pattern. Clarified `DomainId::MAX_VALID = 255` type-level vs ABI-level distinction. Corrected CHANGELOG AG2-C version text (0.26.0→0.26.1). Updated conformance test signature. Gate: `cargo test --workspace` (239 tests), `cargo clippy --workspace` (0 warnings). Zero sorry/axiom.

- **Phase AG2 COMPLETE** (v0.26.1): Pre-Hardware Rust ABI Fixes — 3 sub-tasks (AG2-A through AG2-C). AG2-A (R-05): Fixed `MAX_DOMAIN` constant from 255 to 15 in `sele4n-abi/src/args/sched_context.rs` — now matches Lean `numDomainsVal = 16` (zero-indexed 0..=15); domain values 16-255 previously accepted by Rust ABI decode but rejected by kernel; updated 2 existing unit tests, 2 existing conformance tests, added 4 new AG2-A conformance tests (boundary validation, exhaustive domain coverage). AG2-B (R-01): Created `rust/sele4n-sys/src/sched_context.rs` with 3 typed wrapper functions (`sched_context_configure`, `sched_context_bind`, `sched_context_unbind`) for syscalls 17-19 — completes sele4n-sys coverage for all 25 syscalls; module registered in `sele4n-sys/src/lib.rs`; AG2-B conformance test verifies function signature exports. AG2-C (RUST-04): Synchronized Rust workspace version from `0.25.6` to `0.26.0` in `rust/Cargo.toml` — now tracks Lean `lakefile.toml` version; added version-tracking comment. Bonus: fixed pre-existing clippy `manual_is_multiple_of` warning in `tcb.rs`. Gate: `cargo test --workspace` (239 tests), `cargo clippy --workspace` (0 warnings). Zero sorry/axiom.

- **Phase AG1 COMPLETE** (v0.26.0): Pre-Hardware Lean Code Fixes — 6 sub-tasks (AG1-A through AG1-F). AG1-A (S-04): CBS re-enqueue at effective priority — created `resolveInsertPriority` helper in `Selection.lean`, fixed 5 call sites (`processReplenishmentsDue`, `timerTickBudget`, `handleYieldWithBudget`, `schedContextBind`, `schedContextYieldTo`) that inserted threads at `sc.priority` (base) instead of effective priority (base + PIP boost). AG1-B (S-05): `timeoutBlockedThreads` diagnostic handling — changed return type from `SystemState` to `SystemState × List (ThreadId × KernelError)`, collecting per-thread error diagnostics instead of silently swallowing failures; updated 4 callers. AG1-C (F-T02): Composed `uniqueWaiters` into `ipcInvariantFull` as 15th conjunct — ensures no notification has duplicate thread IDs in `waitingThreads`; updated all 10 preservation theorems in `Structural.lean`, boot proof, `advanceTimerState` preservation, capability/lifecycle bridge, and cross-subsystem extraction. AG1-D (P-03): Boot duplicate detection — added `bootFromPlatformWithWarnings` variant that detects duplicate ObjId/IRQ entries and returns warnings; `bootFromPlatformWithWarnings_wellFormed` correctness theorem; original `bootFromPlatform` documented with last-wins semantics warning. AG1-E (F-F04): `FrozenSchedulerState` `replenishQueue` — added `FrozenReplenishQueue` structure and `replenishQueue` field to `FrozenSchedulerState`; `freezeScheduler` updated; 2 freeze-correctness proofs (`freezeScheduler_replenishQueue_entries`, `freezeScheduler_replenishQueue_size`); all test suites updated. AG1-F (T-01): Runtime `crossSubsystemInvariant` checks — 10 decidable runtime checks (full coverage of all 10 formal predicates): `checkRegistryEndpointValid`, `checkRegistryInterfaceValid`, `checkRegistryDependencyConsistent`, `checkNoStaleEndpointQueueRefs`, `checkNoStaleNotificationWaitRefs`, `checkServiceGraphInvariant`, `checkSchedContextStoreConsistent`, `checkSchedContextNotDualBound`, `checkSchedContextRunQueueConsistent`, `checkBlockingAcyclic` — composed into `checkCrossSubsystemInvariant`; integrated into `MainTraceHarness.lean` `checkInvariants` function. Broken-dependency test fixtures (`svcBroken`, `svcRestartBroken`) moved from bootstrap state to inline injection before their test scenarios to preserve invariant validity. Zero sorry/axiom.

### WS-AF: Pre-Release Comprehensive Audit Remediation v0.25.21 (PORTFOLIO COMPLETE)

- **Phase AF6 COMPLETE** (v0.25.27): Rust ABI Fixes & Documentation Closure — 7 sub-tasks (AF6-A through AF6-G). AF6-A (AF-20, MED-R1): Added `UnknownKernelError` variant (discriminant 255) to `KernelError` enum — unrecognized error codes now map to semantically correct `UnknownKernelError` instead of `InvalidSyscallNumber`; updated `from_u32`, Display impl, decode fallback, and conformance tests. AF6-B (AF-21, MED-R2): Added `endpoint_reply_recv_checked` — returns `Err(IpcTruncationError::ReplyMessageTooLong)` if `msg.length() > 3` instead of silent truncation; added `IpcTruncationError` enum; original `endpoint_reply_recv` preserved with deprecation note. AF6-C (AF-35, AF-36): Fixed stale doc comments — `sele4n-types/src/lib.rs` updated from "43-variant" to "45-variant" and "20-variant" to "25-variant"; `decode.rs` error range comments updated from "0–42" to "0–43" and "≥43" to "≥44". AF6-D (AF-37): Added `SchedContext` marker type to `sele4n-sys/src/cap.rs` — enables `Cap<SchedContext>` phantom-typed capability handles; sealed trait impls and conformance test added. AF6-E (AF-38): Made `IpcMessage.length` field private (`pub(crate)` → private) — added `length()` accessor, `new_with_length()` validated constructor; all internal callers updated to use `msg.length()`. AF6-F (AF-46): Added `shellcheck` installation to CI workflow (`lean_action_ci.yml`) — Tier 0 hygiene shell lint now enforced in CI instead of silently skipped. AF6-G: Full documentation synchronization — WORKSTREAM_HISTORY.md, DEVELOPMENT.md, CLAIM_EVIDENCE_INDEX.md, README.md version bump, CLAUDE.md active workstream update, GitBook chapters synchronized, codebase_map.json regenerated. Zero sorry/axiom. **WS-AF PORTFOLIO COMPLETE** (6 phases, 49 sub-tasks, v0.25.22–v0.25.27).

- **Phase AF5 COMPLETE** (v0.25.26): IPC, Capability, Lifecycle & Documentation — 10 sub-tasks (AF5-A through AF5-J). AF5-A (AF-12): Fixed stale `pendingMessage = none` documentation in `notificationSignal` — comment now cross-references `waitingThreadsPendingMessageNone` invariant (proven in AC1-A). AF5-B (AF-04): Documented timeout sentinel H3 migration path. AF5-C (AF-06): Documented `endpointQueueRemove` direct `RHTable.insert` rationale with AE4-E unreachability proof cross-reference. AF5-D (AF-15): Documented Badge Nat round-trip safety via `ofNatMasked` 64-bit masking. AF5-E (AF-39): Documented `donationChainAcyclic` 2-cycle scope with IPC protocol structural argument for longer cycles. AF5-F (AF-26): Documented tuple projection maintenance burden in Builder.lean and Capability/Invariant/Defs.lean (deferred to WS-V). AF5-G (AF-27): Documented `cspaceResolvePath` vs `resolveCapAddress` resolution layers. AF5-H (AF-28): Documented `suspendThread` TCB re-lookup rationale after `cancelIpcBlocking`. AF5-I (AF-43/AF-48): Fixed FrozenOps operation count from stale "21" to correct "24" (added 4 missing table entries: frozenCspaceLookupSlot, frozenSetPriority, frozenSetMCPriority, frozenSetIPCBuffer); removed duplicate `cdt_only_preserves_projection` and `ensureCdtNodeForSlot_preserves_projection` definitions from InformationFlow/Invariant/Operations.lean (consolidated to primed canonical versions). AF5-J (AF-31): Documented high-heartbeat proof fragility (1.6M/800K) with mitigation strategies. Zero sorry/axiom.

- **Phase AF4 COMPLETE** (v0.25.25): Information Flow, Cross-Subsystem & SchedContext — 8 sub-tasks (AF4-A through AF4-H). AF4-A (AF-16, MED-IF1): Replaced `native_decide` with `decide` in `enforcementBoundary_is_complete` (Wrappers.lean) — removes Lean runtime evaluator from TCB for 25-element SyscallId enumeration; compile time slightly increased but proof now kernel-checked. AF4-B (AF-17, MED-CS1): Replaced `native_decide` with `decide` in `crossSubsystem_pairwise_coverage_complete` (CrossSubsystem.lean) — 15-element pairwise disjointness proof now kernel-checked; coordinated with AF1-B 10-predicate count. AF4-B+: Bonus fix — replaced third `native_decide` in `crossSubsystemInvariant_default` (CrossSubsystem.lean:378) for `objectIndex.length = 0` proof. Zero `native_decide` remains in production code. AF4-C (AF-07, MED-CS2): Expanded `collectQueueMembers` fuel-sufficiency documentation with formal argument sketch connecting `tcbQueueChainAcyclic` to fuel bound — acyclicity implies chain visits each thread at most once, `noStaleEndpointQueueReferences` implies each thread ∈ `objectIndex`, therefore chain length ≤ `objects.size` = fuel. AF4-D (AF-18, MED-SV1): Documented `serviceHasPathTo` conservative fuel-exhaustion semantics — returns `true` on fuel=0 for safe cycle detection; false positive rejects valid edge, false negative would allow cycle; proven correct under `serviceBfsFuel_sound` and `serviceBfsFuel_sufficient` (in `Service/Invariant/Acyclicity.lean`). AF4-E (AF-33): Added seL4 separation kernel design cross-reference for `LabelingContextValid` deployment requirement — boot-time configuration trusted, runtime enforcement via capability checks + NI projection; created `labelingContextValid_is_deployment_requirement` witness theorem (AE5-F gap closure). AF4-F (AF-08, MED-SC1/SX-01): Documented CBS 8× bandwidth bound precision gap — `totalConsumed ≤ 8 × budget` holds due to worst-case replenishment accumulation; ideal 1× bound requires proving replenishment budget partitioning; per-object `budgetWithinBounds` prevents actual overrun regardless. AF4-G (AF-30/AF-47, SX-02): Documented `schedContextYieldTo` kernel-internal design — operates below capability layer (callers responsible for access validation), pure function with identity fallback on missing objects, invariant preservation via `schedContextYieldTo_crossSubsystemInvariant_bridge`. AF4-H: Gate verification — `lake build` (256 jobs), `test_full.sh` (Tier 0–3), zero sorry/axiom, `codebase_map.json` regenerated. Zero sorry/axiom.

- **Phase AF3 COMPLETE** (v0.25.24): Platform & DeviceTree Hardening — 7 sub-tasks (AF3-A through AF3-G). AF3-A (AF-05, MED-D1/PL-02): Fixed `parseFdtNodes` fuel-exhaustion branches to return `none` instead of `some ([], offset)` — both `go` and `parseNodeContents` now signal parse failure on fuel exhaustion; `fromDtbFull` caller documented with safe empty-fallback rationale; `parseFdtHeader_fromDtbFull_some` theorem unchanged (well-formed DTB implies success before fuel runs out). AF3-B (AF-09a, MED-MM1/PL-01): Added full byte-range validation to `mmioWrite32` (`addr+3`), `mmioWrite64` (`addr+7`), and `mmioWrite32W1C` (`addr+3`) — prevents boundary-spill writes into adjacent memory regions; 3 supplementary `_rejects_range_overflow` theorems prove end-of-range rejection when base address is valid but endpoint is not; dual-endpoint assumption documented (device regions ≥4 KiB, page-aligned); all existing theorems (frame, rejection, alignment) pass unchanged. AF3-C (AF-09b): Documented MMIO write-semantics model — three write modes (direct store, W1C, missing set-only), hardware W1C register guidance, `MmioWriteSafe` witness type deferred to H3. AF3-D (AF-32, PL-04): Documented `extractPeripherals` 2-level depth limitation — sufficient for RPi5 BCM2712 DTB, recursive descent deferred to H3. AF3-E (AF-19, MED-B1): Documented `natKeysNoDup` opaque `Std.HashSet` vs. transparent `listAllDistinct` design tradeoff — O(n) runtime vs. O(n²) proof-evaluable. AF3-F (AF-41/42/44/45): Documented four DTB/boot stubs — `classifyMemoryRegion` always-RAM (AF-41), `fromDtb` stub (AF-42), `bootFromPlatform` empty-config acceptance (AF-44), `applyMachineConfig` partial-copy (AF-45); all deferred to WS-V. AF3-G: Gate verification — `lake build` (256 jobs), `test_smoke.sh`, `codebase_map.json` regenerated. Zero sorry/axiom.

- **Phase AF2 COMPLETE** (v0.25.23): State & Model Hardening — 7 sub-tasks (AF2-A through AF2-G). AF2-A (AF-03, MED-M3/CF-01): Machine-checked `storeObject` capacity safety — `storeObject_existing_preserves_objectIndex_length` proves in-place mutations preserve `objectIndex.length` exactly (covers 25+ IPC/scheduler/capability/VSpace callsites), `retypeFromUntyped_capacity_gated` proves the allocation boundary gates on `maxObjects` (Lifecycle/Operations.lean:626), `storeObject_capacity_safe_of_existing` composes into full capacity invariant preservation; `storeObjectChecked` documented as unused-by-design with cross-references to the machine-checked evidence. AF2-B (AF-22, CF-02): Added `SchedContextId.ofObjIdChecked` sentinel guard — mirrors `ThreadId.toObjIdChecked` pattern, returns `.none` for reserved sentinel (value 0); `ofObjIdChecked_eq_some_of_nonzero` correctness theorem. AF2-C (AF-24, BF-02): Added W^X proof obligation (`_hWxSafe : perms.wxCompliant = true`) to builder-phase `mapPage` — makes W+X mappings statically impossible at compile time; `mapPage_wxCompliant` documentation theorem; all standard permission constructors (`readOnly`, `readWrite`, `readExecute`) satisfy W^X by `decide`. AF2-D (AF-25, BF-03): Documented `apiInvariantBundle_frozenDirect` existential design — objects-only field agreement suffices because all `apiInvariantBundle` predicates read only from `objects`. AF2-E (AF-23, CF-03): Documented `RegisterFile` non-lawful BEq limitation — ARM64 32-GPR coverage, out-of-range counterexample unreachability, LawfulBEq function extensionality conflict. AF2-F (AF-34, MED-M2/CF-05): Documented `descendantsOf` BFS transitive closure completeness deferral to WS-V/H3 — structural argument (acyclicity + `edges.length` fuel), formal connection requires hardware-binding CDT depth constant. AF2-G: Gate verification — `lake build` (256 jobs), `test_full.sh` (Tier 0–3), `codebase_map.json` regenerated. Zero sorry/axiom.
- **Phase AF1 COMPLETE** (v0.25.22): Scheduler Correctness & Proof Gaps — 10 sub-tasks (AF1-A through AF1-J). AF1-A: Corrected misleading comments in `BlockingGraph.lean` — `blockingAcyclic` now documented as 10th conjunct of `crossSubsystemInvariant`. AF1-B (AF-01, HIGH-1): Added `blockingAcyclic` as 10th predicate of `crossSubsystemInvariant` — 7 sub-steps: field set entry, pairwise disjointness (15 pairs via `native_decide`), conjunction extension, projection theorem, default state proof, core/retype bridge parameters, per-operation bridge threading (33 bridges), `blockingAcyclic_frame` theorem, boot proof. `crossSubsystemFieldSets` 9→10 entries, 36→45 disjoint pairs. AF1-C (AF-02, HIGH-2): Renamed `bounded_scheduling_latency` to `wcrtBound_unfold` — the definitional unfolding is now clearly distinguished from the substantive `bounded_scheduling_latency_exists` existential theorem. Updated `LivenessSuite.lean` and 6 documentation sites. AF1-D: Added WCRTHypotheses instantiation guide documentation. AF1-E (AF-13): Renamed `pip_deterministic` to `pip_congruence` and `pip_revert_deterministic` to `pip_revert_congruence` — relabeled as congruence theorems reflecting their actual semantics. AF1-F (AF-14): Documented `eventuallyExits` as externalized hypothesis with future derivation path from CBS budget finiteness. AF1-G (AF-10): Documented `resolveEffectivePrioDeadline` fallback rationale. AF1-H (AF-11): Documented `handleYield` static priority usage as intentional. AF1-I (AF-40/AF-49): Documented `RunQueue.size` field purpose and FIFO tie-breaking semantics. AF1-J (AF-29): Documented `blockingServer` pre-mutation read pattern in `propagatePriorityInheritance` and `revertPriorityInheritance`. New theorems: `blockingChain_step`, `blockingChain_congr`, `blockingAcyclic_frame`. Zero sorry/axiom.

### WS-AE: Production Audit Remediation v0.25.21 (PORTFOLIO COMPLETE)

- **Phase AE6 COMPLETE** (v0.25.21): Testing, Documentation & Closure — 8 sub-tasks (AE6-A through AE6-H). AE6-A (U-25): Added `priority_inheritance_suite` execution to `test_tier2_negative.sh` — D4 PIP tests (propagation, blocking chains, reversion, SchedContext integration) now run as part of Tier 2 smoke gate. AE6-B (T-07/T-F02/T-F03): Upgraded `mkState` helper in 4 test suites (`SuspendResumeSuite`, `PriorityManagementSuite`, `PriorityInheritanceSuite`, `IpcBufferSuite`) from unchecked `builder.build` to `builder.buildChecked` — test states now validated against 8 structural invariants at construction time. AE6-C (T-F17): Enhanced `test_rust.sh` cargo-missing path to propagate `RUST_TESTS_SKIPPED=true` to `$GITHUB_OUTPUT` when available, making CI skip status visible in GitHub Actions summaries. AE6-D (R-F01): Corrected `SchedContextConfigureArgs` register mapping comment from `x2=budget...x6=domain` to `regs[0]=budget...overflow[0]=domain`; corrected `SchedContextBindArgs` from `x2=threadId` to `regs[0]=threadId`. AE6-E: Refreshed CLAUDE.md known large files list with current line counts (44 entries updated; significant growth in IPC/Invariant/Structural ~7591, NegativeStateSuite ~3589, MainTraceHarness ~3114, CrossSubsystem ~2211). AE6-F: Full documentation synchronization — WORKSTREAM_HISTORY.md, DEVELOPMENT.md, CLAIM_EVIDENCE_INDEX.md, GitBook chapters updated with AE6 closure and WS-AE portfolio completion. AE6-G: Gate verification — `lake build`, `test_full.sh` (Tier 0–3), zero sorry/axiom. AE6-H: Trace fixture verified unchanged (no dispatch-affecting changes in AE6). Zero sorry/axiom. **WS-AE PORTFOLIO COMPLETE** (6 phases, 53 sub-tasks, v0.25.15–v0.25.21).
- **Phase AE5 COMPLETE** (v0.25.20): Platform, Service & Cross-Subsystem — 7 sub-tasks (AE5-A through AE5-G). AE5-A (U-22): Changed `collectQueueMembers` return type from `List ThreadId` to `Option (List ThreadId)` — fuel exhaustion now returns `none` signaling invariant violation instead of silently returning empty list; updated `noStaleEndpointQueueReferences` to quantify over `some members` result; updated all callers in `noStaleEndpointQueueReferences_frame` and boot proofs. AE5-B (U-20): Added `registryEndpointUnique` invariant — proves no two services share the same endpoint object; added `hasEndpointRegistered` runtime duplicate check to `registerService` rejecting with `.illegalState`; 5 preservation proofs (`default`, `registerService`, `registerInterface`, `revokeService`, `cleanupEndpointServiceRegistrations`) with fold-correctness bridge lemmas (`list_foldl_option_or_false`, `fold_or_false_all_slots`, `hasEndpointRegistered_false_spec`); updated NI projection proof for new branch. AE5-C (SVC-04): Extended `crossSubsystemInvariant` from 8 to 9 predicates by adding `registryInterfaceValid` — every registered service has its interfaces in the interface registry; added `registryInterfaceValid_frame` theorem, `registryInterfaceValid_fields` field-disjointness entry, updated `crossSubsystemFieldSets` (8→9 entries); threaded `hSvcReg`/`hIfaceReg` parameters through both core bridges and all 33+ per-operation bridge lemmas; updated all projection indices and destructuring patterns across CrossSubsystem, Architecture/Invariant, and Boot. AE5-D (U-21): Documented boot invariant bridge limitation — `bootToRuntime_invariantBridge_empty` proves cross-subsystem invariants for zero-object boot state but does not cover hardware-populated initial states; documented pre-deployment verification requirement. AE5-E (U-10): Documented NI boundary for service orchestration — `serviceOrchestrationOutsideNiBoundary` theorem with expanded docstring explaining why service registry operations are outside the NI proof surface and referencing `DEPLOYMENT_GUIDE.md` §2.2. AE5-F (IF-14): Documented `LabelingContextValid` as deployment requirement — `labelingContextValid_is_deployment_requirement` theorem with docstring clarifying that labeling context validity is a pre-deployment obligation, not runtime-enforced; references `DEPLOYMENT_GUIDE.md` §4.1. AE5-G: Gate verification — `lake build` (256 jobs), `test_full.sh` (Tier 0–3), zero sorry/axiom, codebase_map.json regenerated. Zero sorry/axiom.
- **Phase AE4 COMPLETE** (v0.25.19): Capability, IPC & Architecture Hardening — 10 sub-tasks (AE4-A through AE4-J). AE4-A (U-17): Added CPtr masking (`addr.toNat % machineWordMax`) to `resolveCapAddress` for consistency with `resolveSlot` — prevents unbounded Lean Nat from resolving differently than 64-bit hardware registers; updated `resolveCapAddress_guard_match` and `resolveCapAddress_guard_reject` theorem signatures. AE4-B (U-26): Added VAddr canonicity check to `decodeVSpaceUnmapArgs` matching `decodeVSpaceMapArgs` — defense-in-depth for ARM64 48-bit canonical addresses; updated `decodeVSpaceUnmapArgs_error_iff` (3-way disjunction), roundtrip theorem (new `hVAddr` hypothesis), and composed roundtrip. AE4-C (U-18): Proved CDT acyclicity preservation — added `cdtReachable` propositional reachability predicate, `freshChild_not_reachable` bridge theorem (fresh node has no CDT paths), and `cspaceMintWithCdt_cdtAcyclicity_of_freshDst` theorem using existing `addEdge_preserves_edgeWellFounded_fresh`. AE4-D (U-36): Lifted `cdtMintCompleteness` into cross-subsystem composition — added `capabilityInvariantBundleWithMintCompleteness` definition and `crossSubsystemInvariantWithCdtCoverage` to `CrossSubsystem.lean` with extraction theorems. AE4-E (U-24): Proved `endpointQueueRemove` fallback unreachability — `queueRemove_predecessor_exists` and `queueRemove_successor_exists` theorems with inlined `tcbQueueLinkIntegrity` hypotheses (import cycle prevention). AE4-F (U-23): Documented timeout sentinel dual-condition mitigation (gpr x0 AND ipcState check). AE4-G (U-27): Documented H3 targeted TLB flush composition requirements. AE4-H (U-32): Proved `ipcBuffer_within_page` theorem (512-byte aligned buffer fits within 4KB ARM64 page). AE4-I (U-37): Documented complete `receiverSlotBase` plumbing from API dispatch through `ipcUnwrapCaps` to `ipcTransferSingleCap` with per-cap CDT tracking. AE4-J: Gate verification — `lake build` (256 jobs), `test_full.sh` (Tier 0–3), zero sorry/axiom. Zero sorry/axiom.
- **Phase AE3 COMPLETE** (v0.25.18): Scheduler & SchedContext Correctness — 12 sub-tasks (AE3-A through AE3-L). AE3-A (U-11): Enforced `sc.domain == tcb.domain` invariant in `schedContextBind` — rejects cross-domain binding with `invalidArgument`, added `boundThreadDomainConsistent` predicate and `bootState_boundThreadDomainConsistent` theorem. AE3-B/C (U-15): Fixed `cancelDonation` for `.bound` case — checks `isActive` before enqueuing replenishment, clears replenishment queue on unbind to prevent stale entry accumulation; added 3 `cancelIpcBlocking_*_eq` transport lemmas. AE3-D (U-16): Changed `resumeThread` preemption check from `tcb.priority` to `resolveEffectivePriority` for PIP-aware priority comparison. AE3-E (S-03): Documented `handleYield` effective priority gap — `handleYield` uses base `tcb.priority` for re-insertion which is correct for yield semantics (PIP boost only affects scheduling order, not yield position). AE3-F (U-14): Reset replenishment list in `schedContextConfigure` to `[{ amount := budget, eligibleAt := st.machine.timer }]`, preventing stale entries from prior configuration. AE3-G (U-12/U-13): Documented CBS bandwidth bound integer arithmetic precision gap and admission control per-mille rounding. AE3-H (SC-06): Deleted dead `Budget.refill` function (unreachable, superseded by `processReplenishments`). AE3-I (S-01): Strengthened PIP frame theorems with full `invExt` threading — proved `updatePipBoost_self_ipcState` (ipcState preserved for target thread), `blockingServer_ipcState_congr` (blockingServer determined by ipcState), and completed `updatePipBoost_preserves_blockingServer` (blocking graph invariant under PIP boost). All proofs use `suffices`/`refine`/`by_cases` pattern for resolving scheduler if-then-else branches. AE3-J (SC-09): Documented `schedContextBind` pre-update read pattern for run queue insertion. AE3-K (S-05): Documented `timeoutBlockedThreads` O(n) performance. AE3-L: Gate verification — `lake build` (256 jobs), `test_smoke.sh`, zero sorry/axiom. Trace fixture updated for AE3-F replenishment queue reset behavior. Zero sorry/axiom.
- **Phase AE2 COMPLETE** (v0.25.16): Data Structure Hardening & Production Reachability — 8 sub-tasks (AE2-A through AE2-H). AE2-A (U-28): Enforced `4 ≤ capacity` in `RHTable` structure and `RHTable.empty` — changed struct field from `hCapPos : 0 < capacity` to `hCapGe4 : 4 ≤ capacity`, added backward-compatible `hCapPos` accessor theorem. Tables with capacity 1–3 can no longer bypass the `insert_size_lt_capacity` guard. Updated 13 files across RobinHood, RadixTree, Prelude, Model, and Scheduler. AE2-B (U-29): Added `buildCNodeRadixChecked` with runtime key-bounds validation (`allKeysBounded` predicate) — falls back to empty radix tree if any key exceeds `2^radixWidth`. Connecting theorems `buildCNodeRadixChecked_eq_of_bounded` and `buildCNodeRadixChecked_fallback` prove equivalence under invariants. AE2-C (U-30): Added `AUDIT-NOTE: D-RH02` annotations to all 4 fuel exhaustion points (`insertLoop`, `getLoop`, `findLoop`, `backshiftLoop`) documenting consequence-if-reached, WF property guaranteeing unreachability, and kernel-safe fallback behavior. AE2-D (U-31): Refactored `frozenQueuePushTailObjects` to two-phase design — Phase 1 validates all target object keys exist via `FrozenMap.contains` BEFORE any writes; Phase 2 applies mutations guaranteed to succeed. Prevents partial state mutation on intermediate lookup failure. AE2-E (U-02): Documented FrozenOps as experimental/future infrastructure with explicit non-production status annotation in module docstring and CLAUDE.md. AE2-F (U-05): Imported `Scheduler.Liveness` into production proof chain via `CrossSubsystem.lean` — all 7+1 Liveness modules (TraceModel, TimerTick, Replenishment, Yield, BandExhaustion, DomainRotation, WCRT) now type-checked against actual scheduler implementation on every build. Import-cycle constraint (Scheduler/Invariant → Liveness → Operations/Core → Selection → Invariant) resolved by using CrossSubsystem as integration point. AE2-G: Verified all 5 PriorityInheritance submodules transitively reachable via Liveness import chain (TraceModel → BoundedInversion → Preservation → Propagate → Compute → BlockingGraph). AE2-H: Gate verification — `lake build` (256 jobs), `test_full.sh` (Tier 0–3), zero sorry/axiom in all modified files. Zero warnings.
- **Phase AE1 COMPLETE** (v0.25.15): API Dispatch & NI Composition — 8 sub-tasks (AE1-A through AE1-H). AE1-A: Added `.tcbSetPriority` and `.tcbSetMCPriority` to `dispatchCapabilityOnly` (U-01 fix — checked/unchecked dispatch parity). AE1-B: Moved `.tcbSetIPCBuffer` into `dispatchCapabilityOnly` and removed duplicate arms (U-06 fix). AE1-C: Fixed wildcard unreachability comment in `dispatchWithCapChecked` to reflect 14→14 capability-only arms. AE1-D: Added `dispatchWithCapChecked_wildcard_unreachable` theorem proving all 25 `SyscallId` variants are handled by one of the two dispatch tiers (U-07). AE1-E: Added `switchDomain` to NI composition via `ComposedNonInterferenceStep` (IF-01/U-03 — closes domain-switch NI gap). AE1-F: Extended NI proofs for call/reply with donation/PIP — `applyCallDonation_preserves_projection`, `propagatePIP_preserves_projection`, `revertPIP_preserves_projection`, `endpointCallWithDonation_preserves_lowEquivalent`, `endpointReplyWithReversion_preserves_lowEquivalent` (IF-02/U-04). Supporting lemmas in `PriorityInheritance/Preservation.lean`: `updatePipBoost_objects_ne`, `updatePipBoost_toList_filter_neg`, `updatePipBoost_preserves_objects_invExt`. AE1-G: Master dispatch NI theorem — `projPreserving_preserves_lowEquivalent` (two-sided helper in Composition.lean), `dispatchSyscallChecked_preserves_projection` (structural decomposition through TCB lookup → CNode lookup → `syscallLookupCap` state preservation → inner dispatch, in API.lean). AE1-H: Gate verification — `lake build` (238 jobs), `test_full.sh` (Tier 0–3), zero sorry/axiom. Zero warnings.

### WS-AD: Pre-Release Audit Remediation v0.25.10 (COMPLETE)

- **Phase AD5 COMPLETE** (v0.25.14): Closure & Documentation Sync — 2 sub-tasks (AD5-A, AD5-B). Documentation sync: WORKSTREAM_HISTORY, CHANGELOG, CLAIM_EVIDENCE_INDEX, GitBook chapter 12, codebase_map.json regenerated, README version badge updated. Version bump 0.25.13 → 0.25.14. Full `test_full.sh` (Tier 0–3) pass. All 21 findings accounted for, all 19 sub-tasks complete. Zero sorry/axiom. **WS-AD PORTFOLIO COMPLETE.**
- **Phase AD4 COMPLETE** (v0.25.14): Cross-Subsystem Composition Proofs (F-08) — 9 sub-tasks (AD4-A through AD4-I). F-08: Added 35 cross-subsystem bridge lemmas to `CrossSubsystem.lean` covering all 33 kernel operations that modify `objects`: 2 core bridges (`crossSubsystemInvariant_objects_change_bridge` for in-place mutations, `crossSubsystemInvariant_retype_bridge` for objectIndex-growing lifecycle operations using `serviceGraphInvariant_monotone`); 7 IPC bridges; 7 Scheduler/Lifecycle bridges (`schedule`, `handleYield`, `timerTick`, `switchDomain`, `scheduleDomain`, `suspendThread`, `resumeThread`); 7 Capability bridges (`cspaceMint`, `cspaceCopy`, `cspaceMove`, `cspaceMutate`, `cspaceInsertSlot`, `cspaceDeleteSlot`, `cspaceRevoke`); 4 SchedContext bridges (`configure`, `bind`, `unbind`, `yieldTo`); 2 Priority bridges (`setPriority`, `setMCPriority`); 2 VSpace bridges (`mapPage`, `unmapPage`); 1 IPC buffer bridge (`setIPCBufferOp`); 3 Lifecycle retype bridges (`lifecycleRetypeObject`, `lifecycleRetypeWithCleanup`, `retypeFromUntyped`). Full build (236 jobs), `test_full.sh` (Tier 0–3), and sorry/axiom scan all pass. Zero sorry/axiom.
- **Phase AD3 COMPLETE** (v0.25.13): Production Deployment Documentation (F-04, F-05, F-06, F-07) — 6 sub-tasks (AD3-A through AD3-F). Addresses 3 HIGH + 1 MEDIUM audit findings with deployment-facing documentation. AD3-A/B: Created `docs/DEPLOYMENT_GUIDE.md` (238 lines) — security model overview covering non-BIBA integrity model (F-04) with formal witnesses (`integrityFlowsTo_is_not_biba`, `integrityFlowsTo_prevents_escalation`), NI boundary scope (F-05) with `serviceOrchestrationOutsideNiBoundary` theorem, scheduling covert channel analysis (F-06) with bandwidth bound (≤400 bps) and seL4 precedent, mandatory labeling context override requirement (F-07) with concrete `LabelingContext` code example using `kernelTrusted`/`publicLabel` two-domain policy, pre-deployment checklist (7 items). AD3-C: Added §11.2 "Information Flow and Non-Interference Boundary" to `SELE4N_SPEC.md` documenting 32 `NonInterferenceStep` constructors and service orchestration exclusion. AD3-D: Added SA-4 (non-BIBA integrity model) to `SECURITY_ADVISORY.md` with formal witnesses; added SA-2 cross-reference to deployment guide override instructions. AD3-E: Updated `CLAIM_EVIDENCE_INDEX.md` with 4 deployment-facing claims. AD3-F: Updated GitBook chapter 28 with deployment guide summary and finding table. Full `test_full.sh` (Tier 0–3) pass. Zero sorry/axiom.
- **Phase AD2 COMPLETE** (v0.25.12): Code Quality Hardening (F-02, F-03) — 4 sub-tasks (AD2-A through AD2-D). F-02: Added `endpointQueuePopHeadFresh` convenience wrapper in `DualQueue/Core.lean` that returns the post-state TCB with cleared queue links, avoiding the stale-snapshot footgun documented under WS-L1/L1-A. Staleness annotations added at all 3 call sites in `Transport.lean` (`endpointSendDual`, `endpointReceiveDual`, `endpointCall`). F-03: Enhanced module-level docstring in `IPC/Operations/CapTransfer.lean` with explicit error-to-noSlot conversion documentation — clarifies that `ipcTransferSingleCap` errors are intentionally converted to `.noSlot` by `ipcUnwrapCapsLoop`, matching seL4's cursor-preservation semantics. Full build (236 jobs) and smoke tests pass. Zero sorry/axiom.
- **Phase AD1 COMPLETE** (v0.25.11): Integration Fix (F-01) — 3 sub-tasks (AD1-A through AD1-C). F-01: Integrated 2 orphaned SchedContext preservation modules (`Preservation.lean`: 7 theorems covering Z5-M/Z5-I/Z5-K/Z5-L/Z5-N1/N2; `PriorityPreservation.lean`: 14 theorems covering D2-G/H/I/J transport lemmas and authority non-escalation) into the production proof chain. Import-cycle constraint discovered and resolved: direct import into `SchedContext/Invariant.lean` creates cycle via `Object/Types → SchedContext → Invariant → Preservation → Operations → Model.State → Object/Types`; resolved by importing from `CrossSubsystem.lean` (downstream of cycle boundary, natural integration point for cross-subsystem preservation composition). 21 theorems now reachable via `CrossSubsystem → Architecture/Invariant → API.lean`. Full build (236 jobs), `test_full.sh` (Tier 0–3), and sorry/axiom scan all pass. Zero sorry/axiom.

### WS-AC: Comprehensive Audit Remediation v0.25.3 (COMPLETE)

- **Phase AC6 COMPLETE** (v0.25.10): Documentation, Testing & Closure — 7 sub-tasks (AC6-A through AC6-G). T-03: Dedicated `DecodingSuite.lean` created — 40 tests covering Layer 1 (`RegisterDecode`: `decodeSyscallId`, `decodeMsgInfo`, `decodeCapPtr`, `validateRegBound`) and Layer 2 (`SyscallArgDecode`: 20 per-syscall decode functions across CSpace, VSpace, Lifecycle, Service, Notification, SchedContext, TCB families). Tests cover valid decode, insufficient registers, boundary conditions, and domain-specific validation failures (invalid type tags, non-canonical VAddr, ASID overflow, misaligned IPC buffer, priority overflow). Registered in `lakefile.toml` and `test_tier2_negative.sh` (Tier 2). AC6-B: Decode layer test coverage convention (#10) added to DEVELOPMENT.md §5b. AC6-C: WORKSTREAM_HISTORY.md updated with WS-AC completion. AC6-D: Corrected severity table addendum appended to audit document (16 errata catalogued). AC6-E: `codebase_map.json` regenerated. AC6-F: `test_full.sh` (Tier 0–3) pass. Zero sorry/axiom. **WS-AC PORTFOLIO COMPLETE (6 phases, 42 sub-tasks, v0.25.3–v0.25.10).**
- **Phase AC5 COMPLETE** (v0.25.9): Cross-Cutting & Infrastructure — 8 sub-tasks (AC5-A through AC5-H). X-05: CrossSubsystem field-disjointness theorem coverage completed — 18 new pairwise theorems for 3 SchedContext predicates (`schedContextStoreConsistent`, `schedContextNotDualBound`, `schedContextRunQueueConsistent`) against all 5 existing predicates. C(8,2)=28 pairs total: 12 disjoint + 16 shared, all proven via `by decide`. Compile-time summary theorem `crossSubsystem_pairwise_coverage_complete` validates all 12 disjoint pairs via `native_decide`. X-08: GitBook content-hash drift detection added to `test_docs_sync.sh` — compares H1/H2 structural headings between 6 canonical-to-GitBook pairs using SHA-256 hashes, emits warnings (not hard failures) for header divergence. S-05: `saveOutgoingContext_scheduler` theorem (Core.lean:19) verified as `@[simp]` — used 10+ times across Preservation.lean, cross-referenced from `switchDomain` documentation. F-04: Codebase-wide catch-all audit confirmed zero `| _ =>` patterns on `KernelError` in production code; all `.error _` catch-alls classified as Safe/Intentional. F-02/AC5-E: `inter_valid` strengthened to require only left operand validity (AND clears high bits; dropped unused `_hb` parameter), `subset_sound` (subset implies per-right inclusion via `Nat.testBit_and`), `mem_bit_bounded` (membership tests bounded to bits 0..4). F-03/AC5-F: `storeObjectChecked` coding convention verified complete in DEVELOPMENT.md. IF-01/AC5-G: `enforcementBoundary_is_complete` (`native_decide`) verified compiling. Full `lake build` + `test_full.sh` (Tier 0–3) pass. Zero sorry/axiom.
- **Phase AC4 COMPLETE** (v0.25.8): Architecture & Platform Tightening — 5 sub-tasks (AC4-A through AC4-E). A-04: `physicalAddressBound` (VSpace.lean) documented as proof-layer default only — production code uses `vspaceMapPageCheckedWithFlushFromState` (state-aware variant reads `st.machine.physicalAddressWidth`). 2 regression tests: AC4-A-01 verifies address at 2^44 rejected on RPi5 (44-bit PA), AC4-A-02 verifies address at 2^44-1 accepted. F-02: `AccessRightSet` constructor safety model documented — raw `mk` is TCB-internal, 5 safe constructors with validity theorems, operational safety argument for `mem`/`subset`/`inter`/`union`. `union`/`inter` AC4-B notes on raw `⟨bits⟩` return semantics. F-01: Typed Identifier Safety Model added to Prelude.lean — documents unbounded `Nat` design rationale (proof ergonomics), ABI boundary validation chain (`RegisterDecode` + `SyscallArgDecode`), internal kernel trust model, hardware deployment contract (`isWord64`/`isWord64Dec`). IF-01: Enforcement boundary completeness witness — `SyscallId.all` (25 variants), `all_length` compile-time check (`= count := by rfl`), `all_complete` membership proof (`cases s <;> decide`), `syscallIdToEnforcementName` (SyscallId → String bridge verified against API dispatch for semantic accuracy), `enforcementBoundaryComplete` (Bool check), `enforcementBoundary_is_complete` (`native_decide` theorem — fails at compile time if any SyscallId variant is missing from enforcement boundary). Enforcement boundary expanded 30→33 entries with 3 dedicated capability-only entries: `vspaceMapPageCheckedWithFlushFromState`, `vspaceUnmapPageWithFlush`, `revokeService`. Full `lake build` + `test_full.sh` (Tier 0–3) pass. Zero sorry/axiom.
- **Phase AC3 COMPLETE** (v0.25.7): IPC Atomicity & Invariant Strengthening — 6 sub-tasks (AC3-A through AC3-F). I-02: `donateSchedContext` (2 `storeObject` mutations) and `returnDonatedSchedContext` (3 `storeObject` mutations) atomicity contracts documented, monad-level atomicity argument (`.error` carries no state; `Except.bind` discards intermediates), hardware-level atomicity (interrupts disabled during kernel transitions). I-02 proof: `donateSchedContext_ok_implies_sc_bound` (precondition witness — SchedContext found and bound to client) and `donateSchedContext_ok_server_donated` (postcondition witness — server TCB has `.donated` binding in post-state, proving both `storeObject` calls succeeded). I-04: `Badge.bor` unbounded-Nat intermediate documented — `ofNatMasked` applies `% machineWordMax`, `bor_valid` theorem proves result validity. API-01: `resolveExtraCaps` silent-drop behavior documented — seL4-compatible semantics, resolved count reflects actual resolutions not attempts. New chain34 test exercises cap resolution with 3 addresses (2 valid, 1 empty slot) verifying silent-drop produces count=2. F-03: `storeObjectChecked` capacity-enforcing variant of `storeObject` added — rejects new insertions at `maxObjects` capacity, allows in-place updates. 3 theorems: `storeObjectChecked_preserves_objectIndexBounded`, `storeObjectChecked_existing_eq_storeObject`, `storeObjectChecked_headroom_eq_storeObject`. Full 232-job `lake build` + `test_smoke.sh` pass. Zero sorry/axiom.
- **Phase AC2 COMPLETE** (v0.25.6): Scheduler & SchedContext Hardening — 7 sub-tasks (AC2-A through AC2-G). S-02/SC-01: `timeoutBlockedThreads` O(n) cost documented with quantified worst-case analysis and future optimization path (per-SchedContext bound-thread index). S-03: `blockingChain` fuel-truncation behavior documented — fuel default (`objectIndex.length`), invariant dependency (`blockingAcyclic`), truncation consequences on cycle. S-04: `timerTick` and `timerTickBudget` migrated from hardcoded `defaultTimeSlice` to configurable `st.scheduler.configDefaultTimeSlice` — Core.lean (2 function bodies), Preservation.lean (18 proof sites updated with `hConfigTS : st.scheduler.configDefaultTimeSlice > 0` hypothesis), TraceModel.lean (`maxBudgetInBand` unbound thread budget), InformationFlow/Invariant/Operations.lean (`tcbReset`). S-05: `switchDomain` dual-state pattern documented — reads from `st`, returns `stSaved`, with formal reference to `saveOutgoingContext_scheduler` theorem. S-06: RunQueue flat-list complexity documented with O(1)/O(k)/O(n)/O(p) breakdown and RPi5 acceptability rationale. F-04: `KernelError` catch-all lint convention added (doc-comment + DEVELOPMENT.md coding convention). Audit-driven coding conventions section added to DEVELOPMENT.md (KernelError hygiene, multi-step mutation atomicity, identifier Nat unboundedness). Performance characteristics table added to DEVELOPMENT.md. `codebase_map.json` regenerated. Full 232-job `lake build` + `test_full.sh` (Tier 0–3) pass. Zero sorry/axiom.
- **Phase AC1 COMPLETE** (v0.25.5): High-Severity Fixes — 9 sub-tasks (AC1-A through AC1-I). S-01: `hasSufficientBudget` changed from fail-open to fail-closed (defense-in-depth; `| _ => false` instead of `| _ => true`). I-01: Circular import dependency broken — 7 primitive `waitingThreadsPendingMessageNone` helpers extracted from Structural.lean to new `WaitingThreadHelpers.lean`; 3 operation-level theorems (`notificationSignal_preserves_*`, `notificationWait_preserves_*`, `notificationWake_pendingMessage_was_none`) moved from Structural.lean to NotificationPreservation.lean with full machine-checked proofs (replacing comment cross-references). C-01: Production syscall dispatch wired through `cspaceMintWithCdt` (CDT-tracked) — `dispatchWithCap` → `cspaceMintWithCdt`, `cspaceMintChecked` → `cspaceMintWithCdt`. Minted capabilities are now revocable via `cspaceRevoke`. NI proof updated with CDT-pipeline preservation (`cdt_only_preserves_projection'`, `ensureCdtNodeForSlot_preserves_projection'`). `cspaceMint` retained as CDT-untracked base operation for internal composition and proof decomposition. `@[deprecated]` evaluated but rejected (14 suppression annotations across proof surface outweighed signal value). Preservation proofs verified (Preservation.lean, WCRT, CrossSubsystem all build unchanged). 7 negative regression tests added (AC1-G: 5 budget fail-closed, AC1-H: 2 CDT tracking). Zero sorry/axiom.

### WS-AB: Deferred Operations (COMPLETE)

- **Phase D6 COMPLETE** (v0.25.2): API Surface Integration & Closure — 10 sub-tasks (D6-A through D6-J). Rust ABI synchronized: `SyscallId` 20→25 variants (`TcbSuspend`=20, `TcbResume`=21, `TcbSetPriority`=22, `TcbSetMCPriority`=23, `TcbSetIPCBuffer`=24; COUNT 20→25). `KernelError` +`AlignmentError`=43 (44 variants total). New `rust/sele4n-abi/src/args/tcb.rs` module with `SuspendArgs`, `ResumeArgs`, `SetPriorityArgs`, `SetMCPriorityArgs`, `SetIPCBufferArgs` (decode/encode/roundtrip). Updated conformance tests (86→100+ test cases). Lean-side verification: `enforcementBoundary` 30 entries confirmed, `dispatchWithCap_wildcard_unreachable` 25 variants, `frozenOpCoverage_count` = 20/25, `frozenOpCoverage_exhaustive` proven. Spec §5.14 updated with D4 (PIP) and D5 (WCRT) subsections. Claims index, workstream history, CLAUDE.md, README metrics, CHANGELOG, codebase map, website link manifest, and GitBook synchronized. Zero sorry/axiom. **WS-AB PORTFOLIO COMPLETE (6 phases, 90 sub-tasks, v0.24.0–v0.25.5).**
- **Phase D5 COMPLETE** (v0.25.0): Bounded Latency Theorem — 16 sub-tasks (D5-A through D5-P). Proof-only phase, zero kernel code changes. Trace model infrastructure: `SchedulerStep` inductive (9 constructors), `SchedulerTrace`, `validTrace` predicate, query predicates (`selectedAt`, `runnableAt`, `budgetAvailableAt`), counting functions (`countHigherOrEqualEffectivePriority`, `maxBudgetInBand`, `maxPeriodInBand`). Per-mechanism bounds: `timerTickBudget_bound_succeeds`/`timerTickBudget_donated_succeeds` (Z4-F2/F3 characterization), `replenishment_within_period` (CBS replenishment timing), `fifo_progress_in_band` (FIFO progress within priority band). `domainRotationTotal_le_bound` (domain rotation bound). `WCRTHypotheses` structure. Main theorem `wcrtBound_unfold` / `bounded_scheduling_latency_exists`: WCRT = D*L_max + N*(B+P). PIP enhancement: `countHigherOrEqual_mono_threshold` (monotonicity in threshold) + `pip_enhanced_wcrt_le_base` (PIP-enhanced bound ≤ base bound). Closes the parametric WCRT in D4's `pip_bounded_inversion`. 58 surface anchor tests in `LivenessSuite.lean`. New directory: `SeLe4n/Kernel/Scheduler/Liveness/` (7 files + re-export hub). Zero sorry/axiom.
- **Phase D4 COMPLETE** (v0.25.0): Priority Inheritance Protocol — 20 sub-tasks (D4-A through D4-T). `pipBoost : Option Priority := none` field added to TCB. `effectivePriority` updated to compute `max(scPrio, pipBoost)` — composes with SchedContext donation (Z7). `resolveEffectivePrioDeadline` updated for PIP-aware scheduler selection. Blocking graph: `blockedOnThread` (Bool predicate), `BlockedOnThread` (Prop), `waitersOf` (direct dependents via `objectIndex` fold), `blockingChain` (fuel-bounded transitive upward walk via `blockedOnReply`), `blockingServer` (single-step server lookup). `blockingAcyclic` system-level invariant. `blockingChain_length_le_fuel` depth bound (chain ≤ fuel ≤ objectIndex.length). `computeMaxWaiterPriority` (max effective priority across direct waiters). `updatePipBoost` (single-thread pipBoost recompute + conditional RunQueue bucket migration). `propagatePriorityInheritance` / `revertPriorityInheritance` (chain walk applying updatePipBoost; revert structurally identical per `revert_eq_propagate`). Integration: `endpointCallWithDonation` propagates PIP after Call (D4-L), `endpointReplyWithDonation`/`endpointReplyRecvWithDonation` revert PIP after Reply (D4-M), `suspendThread` reverts PIP before cleanup (D4-N), `timeoutThread` reverts PIP for server when timed-out client was in `blockedOnReply` (D4-N audit fix). API dispatch: all 4 Call/Reply/ReplyRecv paths (both enforced and non-enforced) include PIP propagation/reversion inline — audit fix closed gap where enforcement wrappers (`endpointReplyChecked`/`endpointReplyRecvChecked`) called base functions without PIP, and non-enforced Call path applied donation without PIP propagation. 16 frame preservation theorems — `updatePipBoost_preserves_*` for current, activeDomain, machine, lifecycle, irqHandlers, asidTable, serviceRegistry, objectIndex, objectIndexSet, cdt, cdtSlotNode, cdtNodeSlot, cdtNextNode, interfaceRegistry, services, tlb — composed across chain via induction (`propagate_preserves_*` and `revert_preserves_*`). Parametric bounded inversion: `pip_bounded_inversion` proves inversion ≤ `objectIndex.length × WCRT`. Congruence: `pip_congruence`, `pip_revert_congruence`. 22 test cases across 10 categories (default field, effectivePriority with/without boost, SchedContext-bound with pipBoost, waitersOf, computeMaxWaiterPriority, updatePipBoost with run queue migration, blockingChain, blockingGraphEdges, blockingServer, chainContains, transitive propagation, reversion, frame isolation, zero-fuel identity). New files: `SeLe4n/Kernel/Scheduler/PriorityInheritance.lean` (re-export hub), `PriorityInheritance/BlockingGraph.lean`, `PriorityInheritance/Compute.lean`, `PriorityInheritance/Propagate.lean`, `PriorityInheritance/Preservation.lean`, `PriorityInheritance/BoundedInversion.lean`, `tests/PriorityInheritanceSuite.lean`. Zero sorry/axiom.
- **Phase D3 COMPLETE** (v0.24.2–v0.24.3): IPC Buffer Configuration — 12 sub-tasks (D3-A through D3-L) + audit refinements. `SyscallId.tcbSetIPCBuffer` (discriminant 24) added. `SyscallId.count` 24→25. `SetIPCBufferArgs` decode structure with alignment validation (`ipcBufferAlignment = 512`, matching seL4 `seL4_IPCBufferSizeBits = 9`) and roundtrip proof. `ipcBufferAlignment` constant in Prelude.lean. `alignmentError` KernelError variant added. `validateIpcBufferAddress` 5-step pipeline (alignment → canonical → VSpace root → mapping → write permission). `setIPCBufferOp` (validate → TCB lookup → ipcBuffer update). Validation correctness theorems: `validateIpcBufferAddress_implies_aligned`, `validateIpcBufferAddress_implies_canonical`, `validateIpcBufferAddress_implies_mapped_writable`. 7 transport lemmas: `setIPCBufferOp_scheduler_eq`, `setIPCBufferOp_serviceRegistry_eq`, `setIPCBufferOp_irqHandlers_eq`, `setIPCBufferOp_machine_eq`, `setIPCBufferOp_asidTable_eq`, `setIPCBufferOp_capabilityRefs_eq`, `setIPCBufferOp_deterministic`. `setIPCBufferOp_success_shape` helper theorem. `enforcementBoundary` 29→30, `enforcementBoundaryExtended_count` 29→30. Frozen operation: `frozenSetIPCBuffer`. `frozenOpCoverage` 19→20 arms. 17 test cases across 4 categories (3 success, 6 error, 1 field preservation, 7 frozen ops). XVAL-005 decode roundtrip cross-validation in MainTraceHarness. New files: `SeLe4n/Kernel/Architecture/IpcBufferValidation.lean`, `tests/IpcBufferSuite.lean`. Zero sorry/axiom.
- **Phase D2 COMPLETE** (v0.24.1): Priority Management — 14 sub-tasks (D2-A through D2-N). `SyscallId.tcbSetPriority` (discriminant 22) and `.tcbSetMCPriority` (discriminant 23) added. `SyscallId.count` 22→24. `SetPriorityArgs`/`SetMCPriorityArgs` decode structures with bounds validation and roundtrip proofs. `maxControlledPriority : SeLe4n.Priority := ⟨0xFF⟩` field added to TCB. `validatePriorityAuthority` MCP ceiling check. `getCurrentPriority` resolves effective priority through SchedContext binding (unbound→TCB, bound/donated→SchedContext). `updatePrioritySource` updates SchedContext.priority or TCB.priority depending on binding. `migrateRunQueueBucket` removes and re-inserts thread at new priority. `setPriorityOp` (caller lookup → MCP auth → target lookup → priority update → bucket migration → conditional reschedule). `setMCPriorityOp` (MCP ceiling update with retroactive priority capping). 6 transport lemmas for `updatePrioritySource` and `migrateRunQueueBucket`. 3 authority non-escalation proofs: `validatePriorityAuthority_ok_bounded`, `setPriority_authority_bounded`, `setMCPriority_authority_bounded`. `enforcementBoundary` 27→29, `enforcementBoundaryExtended_count` 27→29. Frozen operations: `frozenSetPriority`/`frozenSetMCPriority`. `frozenOpCoverage` 17→19 arms. 15 test cases across 7 categories (success, error, MCP capping, SchedContext binding, MCP transitivity, self-priority, frozen ops). New files: `SeLe4n/Kernel/SchedContext/PriorityManagement.lean`, `SeLe4n/Kernel/SchedContext/Invariant/PriorityPreservation.lean`, `tests/PriorityManagementSuite.lean`. Zero sorry/axiom.
- **Phase D1 COMPLETE** (v0.24.0–v0.24.1): Thread Suspension & Resumption — 18 sub-tasks (D1-A through D1-R) + audit refinements. `SyscallId.tcbSuspend` (discriminant 20) and `.tcbResume` (discriminant 21) added. `SyscallId.count` 20→22. `SuspendArgs`/`ResumeArgs` decode structures with trivial roundtrip proofs. `cancelIpcBlocking` (IPC queue cleanup via `clearTcbIpcFields` + `removeFromAllEndpointQueues`/`removeFromAllNotificationWaitLists`), `cancelDonation` (SchedContext donation return), `clearPendingState` (pending message/timeout/queue link cleanup). `suspendThread` 7-step composite (validate → IPC cancel → donation cancel → RunQueue remove → clear pending → set Inactive → conditional reschedule). `resumeThread` with conditional preemption check. 12 transport lemmas proving scheduler, serviceRegistry, and lifecycle preservation for `cancelIpcBlocking`, `cancelDonation`, `clearPendingState` (lifecycle preservation correctly omitted for `cancelDonation` `.donated` path since `storeObject` modifies lifecycle). `enforcementBoundary` 25→27 entries, `enforcementBoundaryExtended_count` 25→27. API dispatch: 11 capability-only arms (was 9), wildcard unreachability theorem updated (22 variants), docstring synchronized. 2 new dispatch equivalence theorems + composite updated. Frozen operations: `frozenSuspendThread`/`frozenResumeThread`. `frozenOpCoverage` 15→17 arms. 21 test cases across 7 categories (basic suspend/resume, frozen ops, IPC blocked states, SchedContext binding, wrong-object-type negatives). New files: `SeLe4n/Kernel/Lifecycle/Suspend.lean`, `SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean`, `tests/SuspendResumeSuite.lean`. Zero sorry/axiom.

### WS-AA: Comprehensive Audit Remediation v0.23.21 (COMPLETE)

- **Phase AA1 COMPLETE** (v0.23.22): Rust ABI Type Synchronization — 8 sub-tasks (AA1-A through AA1-H). SyscallId +3 variants (SchedContextConfigure=17, SchedContextBind=18, SchedContextUnbind=19; COUNT 17→20). KernelError +IpcTimeout=42 (43 variants total). TypeTag +SchedContext=6 (7 variants total). New `sched_context.rs` module (Configure/Bind/Unbind arg structs with priority/domain validation). Updated doc comments, stale boundary tests, 200 Rust tests pass. Findings addressed: H-1, H-2, H-3, L-25, L-29. Zero sorry/axiom.
- **Phase AA2 COMPLETE** (v0.23.23): CI & Infrastructure Hardening — 6 sub-tasks (AA2-A through AA2-F). AA2-A: Replaced `curl | sh` Rust toolchain install with SHA-pinned `dtolnay/rust-toolchain` action (v1, toolchain 1.82.0). AA2-B: Added `RUST_TOOLCHAIN_VERSION` documentation variable in `setup_lean_env.sh`. AA2-C: Fixed `$STAGED_LEAN_FILES` word-splitting vulnerability in pre-commit hook (unquoted string → bash array via `mapfile`). AA2-D: Made SHA-256 verification fail-closed for unrecognized architectures (`return 0` → `return 1` with error message). AA2-E: Added git-tracked file validation for `TRACE_FIXTURE_PATH` to prevent CI fixture override attacks. AA2-F: JSON-escaped `lane` variable in `ci_capture_timing.sh` to prevent invalid JSON from special characters. Findings addressed: H-4, H-5, M-7, M-8, L-30. Zero sorry/axiom. `test_smoke.sh` green.

### WS-Z: Composable Performance Objects (PORTFOLIO COMPLETE)

- **Phase Z1 COMPLETE** (v0.23.0): SchedContext Type Foundation — 18 sub-tasks (Z1-A through Z1-R). SchedContextId typed identifier, Budget/Period/Bandwidth/ReplenishmentEntry types, SchedContext structure (CBS scheduling context object), SchedContextBinding enum (unbound/bound/donated), TCB schedContextBinding field, KernelObject/KernelObjectType .schedContext variant (7th object type), FrozenKernelObject extension, threadSchedulingParams migration accessor, BEq instances, re-export hub. 24 files updated for KernelObject variant ripple. Zero sorry/axiom.
- **Phase Z2 COMPLETE** (v0.23.1, audit v0.23.2): CBS Budget Engine — 24 sub-tasks (Z2-A through Z2-Q). Pure-function CBS budget management operations: `consumeBudget` (saturating decrement), `isBudgetExhausted`, `mkReplenishmentEntry`/`truncateReplenishments`/`scheduleReplenishment` (replenishment scheduling), `partitionEligible`/`sumReplenishments`/`applyRefill`/`processReplenishments` (replenishment processing), `cbsUpdateDeadline` (CBS deadline rule), `cbsBudgetCheck` (combined per-tick entry point), `admissionCheck` (bandwidth admission control). Invariant definitions: `budgetWithinBounds`, `replenishmentListWellFormed`, `schedContextWellFormed`, `replenishmentAmountsBounded`. 12 preservation theorems composing into `cbsBudgetCheck_preserves_schedContextWellFormed`. 6 `replenishmentAmountsBounded` preservation theorems including `cbsBudgetCheck_preserves_replenishmentAmountsBounded`. Bandwidth isolation theorems: `cbs_single_period_bound`, `cbs_bandwidth_bounded`. Audit fixes: `applyRefill` `isActive` synchronization (AUD-1), `replenishmentAmountsBounded` preservation chain (AUD-2), bandwidth theorem refactoring (AUD-3). New files: `Budget.lean`, `Invariant/Defs.lean`, `Invariant.lean`. Zero sorry/axiom.
- **Phase Z3 COMPLETE** (v0.23.5, audit v0.23.6): Replenishment Queue — 12 sub-tasks (Z3-A through Z3-L). System-wide `ReplenishQueue` structure (sorted list of `SchedContextId × eligibleAt` pairs with cached size). Operations: `empty`, `insert` (sorted O(n)), `popDue` (prefix split O(k)), `remove` (filter O(n)), `peek` (O(1)), `hasDue` (O(1)). Invariant definitions: `pairwiseSortedBy` (recursive adjacency predicate), `replenishQueueSorted`, `replenishQueueSizeConsistent`, `replenishQueueConsistent` (parameterized by object store lookup — decoupled from SystemState). Preservation theorems: `insert_preserves_sorted`, `popDue_preserves_sorted`, `popDue_sizeConsistent`, `remove_preserves_sorted`, `filter_preserves_pairwiseSortedBy`. Length/membership theorems: `splitDue_length_additive`, `insertSorted_length`, `insert_sizeConsistent`, `remove_sizeConsistent`, `mem_insertSorted`, `subset_insertSorted`, `empty_sorted`/`empty_sizeConsistent`/`empty_consistent`. Public helpers: `pairwiseSortedBy_cons`, `pairwiseSortedBy_head_le_second`, `pairwiseSortedBy_tail`, `pairwiseSortedBy_nil`/`pairwiseSortedBy_singleton`. Private helpers: `pairwiseSortedBy_head_le_all`, `insertSorted_head_ge`, `insertSorted_head_time_ge`, `filter_head_time_ge`. Tier 3 invariant surface anchors: 13 `#check` entries. Audit fixes: `splitDue_length_additive`/`popDue_sizeConsistent` proofs (AUD-1), duplicate SchedContextId design documentation (AUD-2), Tier 3 anchors added (AUD-3). New file: `ReplenishQueue.lean`. Zero sorry/axiom.
- **Phase Z4 COMPLETE** (v0.23.7, audit v0.23.8): Scheduler Integration — 33 sub-tasks (Z4-A through Z4-V2). CBS budget engine and replenishment queue wired into the scheduler. `replenishQueue` field added to `SchedulerState` (Z4-A). Selection layer: `effectivePriority` (resolves scheduling params from SchedContext if bound, TCB fields if unbound), `hasSufficientBudget` (budget eligibility predicate), `resolveEffectivePrioDeadline`, `chooseBestRunnableEffective`/`chooseBestRunnableInDomainEffective`/`chooseBestInBucketEffective` (budget-filtered selection chain), `chooseThreadEffective` (parallel to `chooseThread` with SchedContext awareness). Core operations: `popDueReplenishments` (wraps Z3 `popDue`), `refillSchedContext` (per-SchedContext CBS refill), `processReplenishmentsDue` (fold over due entries with re-enqueue), `timerTickBudget` (3-branch: unbound legacy / bound decrement / bound exhaustion+preempt), `scheduleEffective` (budget-aware schedule), `timerTickWithBudget` (replenishment+budget entry point), `handleYieldWithBudget` (yield with budget charge). 6 new invariants: `budgetPositive`, `currentBudgetPositive`, `schedContextsWellFormed`, `replenishQueueValid`, `schedContextBindingConsistent`, `effectiveParamsMatchRunQueue`. Extended bundle: `schedulerInvariantBundleExtended` (15-tuple: original 9 + 6 new). Default-state proofs for all 6 new invariants. Preservation theorems: `timerTickBudget_unbound_nopreempt_scheduler_eq`, `timerTickBudget_unbound_preempt_replenishQueue_eq`, `popDueReplenishments_sorted`, `popDueReplenishments_sizeConsistent`, `refillSchedContext_noop`, `chooseThreadEffective_state_unchanged`, `effectivePriority_unbound_legacy`, `hasSufficientBudget_unbound_legacy`. Backward-compatible: original `chooseThread`/`schedule`/`timerTick`/`handleYield` preserved unchanged; all 3236 lines of existing preservation proofs pass unmodified. Modified files: `State.lean`, `Selection.lean`, `Core.lean`, `Invariant.lean`, `Preservation.lean`. Zero sorry/axiom.
- **Phase Z5 COMPLETE** (v0.23.9, audit v0.23.10, audit v0.23.11): Capability-Controlled Thread Binding — 25 sub-tasks (Z5-A through Z5-P2). Capability-gated operations to bind threads to scheduling contexts, configure scheduling parameters, and enforce admission control. 3 new `SyscallId` variants: `.schedContextConfigure` (17), `.schedContextBind` (18), `.schedContextUnbind` (19). Updated `ofNat?`/`toNat` codec, `toNat_injective`/`toNat_ofNat` proofs, `SyscallId.count` (17→20). 3 new `SyscallArgDecode` structures: `SchedContextConfigureArgs` (5 MRs), `SchedContextBindArgs` (1 MR), `SchedContextUnbindArgs` (0 MRs) with decode/encode functions and round-trip proofs. Core operations: `validateSchedContextParams` (budget/period/priority/domain validation), `collectSchedContexts` (object store traversal with `excludeId` parameter), `checkAdmission` (bandwidth admission control), `schedContextConfigure` (validate + admit + store update), `schedContextBind` (bidirectional TCB↔SchedContext binding + RunQueue re-insertion), `schedContextUnbind` (unbind + preemption guard + RunQueue removal), `schedContextYieldTo` (kernel-internal budget transfer + re-enqueue on budget restoration). Preservation theorems: `validateSchedContextParams_implies_wellFormed` (period > 0 ∧ budget ≤ period), `schedContextConfigure_output_wellFormed` (configured SchedContext well-formed), `schedContextYieldTo_target_bounded` (target budget ≤ configured budget), `schedContextBind_output_bidirectional` (Z5-K: TCB↔SC binding correctness), `schedContextUnbind_output_cleared` (Z5-L: unbind clears both sides), `schedContextBind_runQueue_insert_uses_sc_priority` (Z5-N1/N2: RunQueue priority correctness), `schedContextConfigure_admission_excludes_eq` (Z5-M: admission exclusion). API dispatch: 3 new arms in `dispatchCapabilityOnly`, 3 structural equivalence theorems (`checkedDispatch_schedContext*_eq_unchecked`), `checkedDispatch_capabilityOnly_eq_unchecked` extended (6→9 disjuncts), `dispatchWithCap_wildcard_unreachable` updated (17→20 variants). Information-flow: SchedContext ops are capability-only (no cross-domain flows); structural equivalence proven via `dispatchCapabilityOnly` shared path. FrozenOps: 3 new `frozenOpCoverage` arms (all `false` — builder-only), coverage counts updated. Test updates: `NegativeStateSuite` boundary adjusted (17→20), `MainTraceHarness` SyscallId roundtrip expanded (17→20 variants) + 12 new SchedContext ops trace tests (SCO-001 through SCO-012), fixture hash regenerated. Audit fixes (v0.23.10): AUD-1 RunQueue re-insertion in `schedContextBind` (Z5-G3), AUD-2 preemption guard in `schedContextUnbind` (Z5-H1), AUD-3 RunQueue removal in `schedContextUnbind` (Z5-H2), AUD-4 re-enqueue in `schedContextYieldTo` (Z5-I2), AUD-5 `schedContextBind_output_bidirectional`/`schedContextUnbind_output_cleared` preservation theorems (Z5-K/L), AUD-6 `schedContextBind_runQueue_insert_uses_sc_priority` (Z5-N1/N2), AUD-7 admission control `excludeId` double-count fix (Z5-M). New files: `Operations.lean`, `Invariant/Preservation.lean`. Modified files: `Object/Types.lean`, `SyscallArgDecode.lean`, `API.lean`, `FrozenOps/Operations.lean`, `NegativeStateSuite.lean`, `MainTraceHarness.lean`. Zero sorry/axiom.

- **Phase Z6 COMPLETE** (v0.23.12, audit v0.23.13): Timeout Endpoints — 26 sub-tasks (Z6-A through Z6-P2). Budget-driven timeout for IPC blocking operations. `timeoutBudget : Option SchedContextId` field on TCB (design optimization: TCB-level instead of per-ThreadIpcState variant, avoiding ~200 pattern match changes). `endpointQueueRemove` (mid-queue splice-out with `endpointQueueRemove_preserves_objects_invExt` proof). `timeoutThread` (queue removal + IPC state reset + error code write + RunQueue re-enqueue). `timeoutAwareReceive` (timeout-detecting receive wrapper). `IpcTimeoutResult` type (`.completed msg | .timedOut`). `timeoutBlockedThreads` (scan via `schedContextBinding.scId?` match — zero changes to existing IPC operations). Timer tick integration: `timerTickBudget` Z4-F3 branch calls `timeoutBlockedThreads` on budget exhaustion. `blockedThreadTimeoutConsistent` invariant (10th conjunct of `ipcInvariantFull`). Transport lemmas: `endpointQueueRemove_scheduler_eq`, `endpointQueueRemove_cdt_eq`, `endpointQueueRemove_lifecycle_eq`, `endpointQueueRemove_services_eq`. Boot safety extended with `timeoutBudget = none` requirement. Full bundle ripple fix across 6 files (~15 construction sites). New file: `SeLe4n/Kernel/IPC/Operations/Timeout.lean`. Audit (v0.23.13): AUD-Z6-1 `endpointQueueRemove` defensive fallback invariant documentation, AUD-Z6-2 `timeoutThread` precondition documentation, AUD-Z6-3 12 trace tests (SCO-020 through SCO-031), AUD-Z6-4 `timeoutAwareReceive` docstring correction. Audit 2 (v0.23.14): AUD-Z6-5 4 edge-case tests (SCO-032–SCO-035: mid-queue removal, receiveQ removal, blockedOnCall timeout, multi-thread timeout), cross-subsystem 10-tuple verification, transport lemma coverage verification, documentation accuracy audit. Zero sorry/axiom.

### WS-Z Phase Z8: API Surface & Syscall Wiring (COMPLETE)
- **Sub-tasks**: Z8-A through Z8-N2 (17 atomic units)
- **Modified files**: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`, `SeLe4n/Kernel/FrozenOps/Operations.lean`, `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean`, `SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean`, `SeLe4n/Testing/MainTraceHarness.lean`, `tests/NegativeStateSuite.lean`, `tests/InformationFlowSuite.lean`, `tests/fixtures/main_trace_smoke.expected`
- **Z8-B**: 3 error-exclusivity theorems for SchedContext decode (configure: `< 5` MRs, bind: `< 1` MR, unbind: never fails)
- **Z8-H**: 3 frozen SchedContext operations (`frozenSchedContextConfigure`, `frozenSchedContextBind`, `frozenSchedContextUnbind`) — passthrough-frozen via `FrozenMap.get?`/`FrozenMap.set`
- **Z8-I**: `frozenTimerTickBudget` — CBS budget-aware timer tick in frozen state
- **Z8-M**: `enforcementBoundary` expanded 22→25 entries (3 new `.capabilityOnly` SchedContext operations)
- **Z8-J**: 6 budget lifecycle trace scenarios (Z8J-001 through Z8J-006)
- **Z8-L**: 8 negative-state tests (Z8-L-01 through Z8-L-08)
- **Frozen op coverage**: 12→15 SyscallId arms
- **Prior Z5 work confirmed**: Z8-A (round-trip theorems), Z8-C/D/E (dispatch wiring), Z8-F (checked dispatch), Z8-G (wildcard unreachability) — all completed in Z5
- **Sorry/axiom**: Zero

### WS-Z Phase Z9: Invariant Composition & Cross-Subsystem (COMPLETE)
- **Sub-tasks**: Z9-A through Z9-P2 (20 atomic units)
- **Modified files**: `SeLe4n/Kernel/CrossSubsystem.lean`, `SeLe4n/Kernel/Architecture/Invariant.lean`, `SeLe4n/Platform/Boot.lean`, `tests/InformationFlowSuite.lean`
- **Z9-A/B/C**: 3 new cross-subsystem predicates: `schedContextStoreConsistent` (every SchedContextId in the object store has a well-formed SchedContext object), `schedContextNotDualBound` (no SchedContext is simultaneously bound via TCB and donated), `schedContextRunQueueConsistent` (bound SchedContext threads with sufficient budget are in the RunQueue iff they are runnable)
- **Z9-D**: `crossSubsystemInvariant` extended from 5 to 8 predicates (added the 3 new SchedContext consistency predicates)
- **Z9-E**: Field-disjointness analysis for all 8 predicates — 14 pairwise disjointness witnesses documenting which `StateField` pairs cannot simultaneously invalidate each predicate
- **Z9-F**: Frame lemmas for 3 new predicates: `schedContextStoreConsistent_frame`, `schedContextNotDualBound_frame`, `schedContextRunQueueConsistent_frame` — each parameterized by object store and scheduler state fields with explicit non-interference conditions
- **Z9-G**: `proofLayerInvariantBundle` extended from 9 to 10 conjuncts by adding `schedulerInvariantBundleExtended` as the 10th conjunct, composing Z4's extended scheduler bundle into the top-level proof layer
- **Z9-H**: Default state proof for extended 10-conjunct `proofLayerInvariantBundle` (`proofLayerInvariantBundle_default`)
- **Z9-I**: `bootSafeObject` extended with `SchedContext` wellFormedness constraint — the boot-safe predicate now requires any `.schedContext` kernel object to satisfy `schedContextWellFormed`
- **Z9-J**: Boot-time proofs for the 3 new cross-subsystem predicates and `schedulerInvariantBundleExtended` — `bootFromPlatform` shown to establish all 10 `proofLayerInvariantBundle` conjuncts from a valid `PlatformConfig`
- **Z9-K**: Freeze proofs — all 3 new predicates lift automatically through the existential wrapper in `FrozenSystemState`; no additional proof content required
- **Z9-L/M/N/O**: Operation preservation theorems for the 3 new predicates across the 4 major operation classes: timer tick (`timerTick`/`timerTickWithBudget`), schedule (`schedule`/`scheduleEffective`), SchedContext donation (`endpointCallWithDonation`/`endpointReplyWithDonation`), and cleanup/destroy (`lifecyclePreRetypeCleanup`/`cleanupDonatedSchedContext`)
- **Z9-P1/P2**: Build verification (`lake build SeLe4n.Kernel.CrossSubsystem`) and full test suite — all Tier 0–3 tests pass
- **Sorry/axiom**: Zero

### WS-Z Phase Z10: Documentation & Closure (COMPLETE)
- **Sub-tasks**: Z10-A1 through Z10-J2 (12 atomic units)
- **Modified files**: `docs/spec/SELE4N_SPEC.md`, `docs/DEVELOPMENT.md`, `docs/WORKSTREAM_HISTORY.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, `docs/codebase_map.json`, `docs/gitbook/12-proof-and-invariant-map.md`, `README.md`, `CLAUDE.md`, `scripts/website_link_manifest.txt`
- **Z10-A1/A2**: Added ReplenishQueue (Z3), Scheduler Integration (Z4), Capability Binding (Z5), API Surface (Z8), Cross-Subsystem (Z9) subsections to `SELE4N_SPEC.md` under §8.12
- **Z10-B**: Updated `DEVELOPMENT.md` with Z9/Z10 phase entries and ReplenishQueue/CrossSubsystem build targets
- **Z10-C**: Updated `WORKSTREAM_HISTORY.md` with Z10 closure entry
- **Z10-D**: Updated `CLAIM_EVIDENCE_INDEX.md` with CBS bandwidth isolation, donation chain acyclicity, timeout termination, and admission control claims
- **Z10-E**: Regenerated `codebase_map.json` with updated metrics
- **Z10-F**: Updated GitBook proof/invariant map with Z10 documentation closure section
- **Z10-G**: Updated `README.md` metrics from `codebase_map.json`
- **Z10-H**: Updated `CLAUDE.md` source layout and active workstream context for Z10 completion
- **Z10-I**: Updated `website_link_manifest.txt` with new SchedContext file paths
- **Z10-J1/J2**: Full test suite pass, zero sorry/axiom, documentation sync verified
- **WS-Z PORTFOLIO COMPLETE**: 10 phases, 213 sub-tasks, v0.23.0–v0.23.21
- **Sorry/axiom**: Zero

### WS-Z Phase Z7: SchedContext Donation / Passive Servers (COMPLETE)
- **Sub-tasks**: Z7-A through Z7-Q2 (26 atomic units)
- **New files**: `SeLe4n/Kernel/IPC/Operations/Donation.lean`
- **Modified files**: `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, `SeLe4n/Kernel/IPC/Invariant/Defs.lean`, `SeLe4n/Kernel/IPC/Invariant/Structural.lean`, `SeLe4n/Kernel/Capability/Invariant/Preservation.lean`, `SeLe4n/Kernel/Architecture/Invariant.lean`, `SeLe4n/Kernel/Lifecycle/Operations.lean`, `SeLe4n/Platform/Boot.lean`, `SeLe4n/Testing/MainTraceHarness.lean`
- **Key operations**: `donateSchedContext`, `returnDonatedSchedContext`, `applyCallDonation`, `applyReplyDonation`, `cleanupPreReceiveDonation`, `cleanupDonatedSchedContext`
- **Donation-aware wrappers**: `endpointCallWithDonation`, `endpointReplyWithDonation`, `endpointReplyRecvWithDonation`
- **Invariants**: `donationChainAcyclic`, `donationOwnerValid`, `passiveServerIdle`, `donationBudgetTransfer`
- **ipcInvariantFull**: Extended from 10 to 14 conjuncts
- **Tests**: 8 trace tests (Z7D-001 through Z7D-008)
- **Architecture**: Donation as post-processing wrappers preserving all existing IPC invariant proofs unchanged
- **Sorry/axiom**: Zero

### WS-Y workstream (v0.22.22 Final Audit Remediation) — COMPLETE

WS-Y addresses 14 unique actionable findings from a comprehensive full-kernel
audit of v0.22.22 (2 MED, 8 LOW, 4 INFO) across 3 phases (Y1–Y3) with 20
atomic sub-tasks. Plan:
[`AUDIT_v0.22.22_WORKSTREAM_PLAN.md`](dev_history/AUDIT_v0.22.22_WORKSTREAM_PLAN.md).

- **Y1 (Frozen State & Foundation Fixes) COMPLETE** (v0.22.23): 7 sub-tasks
  (Y1-A through Y1-G). Resolves MED-01, LOW-01, LOW-02, LOW-03:
  **MED-01**: `configDefaultTimeSlice` transferred through freeze pipeline —
  field added to `FrozenSchedulerState`, `freezeScheduler` updated,
  `freeze_preserves_configDefaultTimeSlice` proven, `frozenTimerTick` uses
  configurable value instead of hardcoded constant.
  **LOW-01**: `AccessRightSet.mk` documented as internal-only with migration
  to safe constructors.
  **LOW-02**: `descendantsOf` BFS optimized from O(n²) to O(n) via
  `Std.HashSet` visited-set with 12 updated theorems.
  **LOW-03**: All 16 `allTablesInvExtK` conjuncts have named accessors with
  completeness documentation.
  Zero sorry/axiom. `test_smoke.sh` green.

- **Y2 (Platform, Data Structures & Proof Hardening) COMPLETE** (v0.22.24): 7
  sub-tasks (Y2-A through Y2-G). Resolves LOW-04, LOW-05, LOW-06, INFO-01,
  INFO-03, INFO-04, INFO-06:
  **LOW-04**: `switchDomain` fallback documented as unreachable with
  `switchDomain_index_in_bounds` and `switchDomain_index_lookup_isSome` proofs.
  **LOW-05**: `registerContextStableCheck` dead branching removed — identical
  `if/else` branches simplified to single uniform check.
  **LOW-06**: `insertLoop`/`backshiftLoop` fuel-exhaustion documented with
  `invExtK` load-factor unreachability argument.
  **INFO-01**: `beq_converse_limitation` replaced with real `VSpaceRoot.beq_refl`
  proof (v0.22.25). `LawfulBEq PagePermissions` + `RHTable.slot_entry_implies_get`
  + `Array.foldl_induction`-based fold reflexivity. `LawfulBEq VSpaceRoot`
  impossibility rigorously documented (non-canonical Robin Hood layouts). L-FND-3 closed.
  **INFO-03**: `enforcementBridge_to_NonInterferenceStep` extended from 6/11 to
  11/11 checked wrappers with 5 new soundness theorems.
  **INFO-04**: `VSpaceBackend.lean` annotated with H3 forward-declaration status.
  **INFO-06**: `collectQueueMembers_length_bounded` fuel bound lemma added with
  `TPI-DOC` tracking annotation.
  Zero sorry/axiom. `test_smoke.sh` green.

- **Y3 (Test Infrastructure & Documentation) COMPLETE** (v0.22.26): 6
  sub-tasks (Y3-A through Y3-F). Resolves MED-02, LOW-07, LOW-08:
  **MED-02**: 59 of 62 `.build` calls across 3 test suites migrated to
  `.buildChecked` (InformationFlowSuite: 15/15, NegativeStateSuite: 35/38,
  OperationChainSuite: 9/9). 3 calls retained with per-call annotations for
  deliberately malformed negative test states.
  **LOW-07**: Duplicate `awaitReceive` probe replaced with `capCopy`
  (`cspaceCopy`), covering 7 truly distinct operation families.
  `checkStateInvariants` fixed to sync threadState before checking.
  **LOW-08**: `assertStateInvariantsFor` docstring documenting V8-G7 design
  (inference self-consistency, not drift detection). Companion function
  `assertStateInvariantsWithoutSync` added for drift-detection use cases.
  Zero sorry/axiom. `test_full.sh` green.
  **WS-Y PORTFOLIO COMPLETE.**

### WS-X workstream (v0.22.17 Pre-Release Audit Remediation) — COMPLETE

WS-X addresses 24 unique actionable findings from a comprehensive pre-release
audit of v0.22.17 (4 CRIT, 9 HIGH, 9 MED, 2 LOW) across 5 phases (X1–X5) with
40 atomic sub-tasks. Plan:
[`AUDIT_v0.22.17_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.22.17_WORKSTREAM_PLAN.md).

- **X1 (Hardware-Binding Critical Proofs) COMPLETE** (v0.22.18): 11 sub-tasks
  (X1-A through X1-K). All 4 CRITICAL findings resolved:
  **C-1**: Boot invariant bridge proven for general configs (V4-A2–A9 pre-existing).
  **C-2**: MMIO `hOutcome : True` placeholder replaced with `MmioReadOutcome`
  inductive encoding read-kind constraints (ram/volatile/w1c/fifo). Three RPi5
  device-specific witness generators (`mkMmioSafe_uart`, `mkMmioSafe_gicDist`,
  `mkMmioSafe_gicCpu`) added.
  **C-3**: `contextSwitchState` atomic operation defined — atomically loads
  register context and updates `scheduler.current`, preserving
  `contextMatchesCurrent` by construction. `AdapterProofHooks.preserveContextSwitch`
  added with `adapterContextSwitch_ok_preserves_proofLayerInvariantBundle`
  composition theorem. All platform ProofHooks updated.
  **C-4**: TPI-001 closed — 4 round-trip theorems (pre-existing) establish
  VSpace determinism through functional correctness. Documentation updated.
  Zero sorry/axiom. `test_full.sh` green.

- **X2 (Runtime Invariant Enforcement) COMPLETE** (v0.22.19): 9 sub-tasks
  (X2-A through X2-I). 5 findings resolved (H-2, H-6, H-8, M-4, M-6):
  **H-2**: `domainScheduleEntriesPositive` predicate as 9th conjunct of
  `schedulerInvariantBundleFull`. `setDomainScheduleChecked` builder validation.
  7 frame lemmas + 4 bundle preservation updates.
  **H-6**: `physicalAddressWidth` field in `MachineState`.
  `vspaceMapPageCheckedWithFlushFromState` state-aware PA bounds.
  **H-8**: `listAllDistinct` transparent duplicate detection. 3 `native_decide`
  → `decide`.
  **M-4**: `revokeService_preserves_noStaleNotificationWaitReferences` frame lemma.
  **M-6**: 4 checked scheduler wrappers with `saveOutgoingContextChecked`.
  Zero sorry/axiom. `test_full.sh` green.

- **X3 (Information Flow & Composition Closure) COMPLETE** (v0.22.20): 5 sub-tasks
  (X3-A through X3-E). 4 findings resolved (H-3, H-4, H-5, M-1):
  **H-3**: `serviceOrchestrationOutsideNiBoundary` exclusion boundary theorem.
  `serviceRegistryAffectsProjection` predicate. NI boundary formally documented.
  **H-4**: 4 sharing predicate pair frame theorems. `crossSubsystemInvariant_composition_complete`
  10-conjunct tightness theorem covering all 10 predicate interaction pairs
  (6 disjoint + 4 sharing).
  **H-5**: `enforcementBridge_to_NonInterferenceStep` unified 6-conjunct bridge
  connecting enforcement soundness to NI composition framework.
  **M-1**: `integrityFlowsTo_prevents_escalation` privilege escalation prevention.
  `securityFlowsTo_prevents_label_escalation` label-level denial.
  Zero sorry/axiom. `test_full.sh` green.

- **X4 (Platform & Architecture Completion) COMPLETE** (v0.22.21): 6 sub-tasks
  (X4-A through X4-F). 4 findings resolved (H-7, M-8, M-9, M-10):
  **H-7**: Generic FDT device node traversal (`parseFdtNodes`, `FdtNode`,
  `FdtProperty`). `extractInterruptController` GIC-400 discovery via `compatible`
  string match + `reg` property parsing. `extractTimerFrequency` `/timer` node
  discovery + `clock-frequency` extraction. `extractPeripherals` device node
  enumeration. `fromDtbFull` now performs complete device discovery.
  **M-10**: `mmioRegionsPairwiseDisjointCheck` + `mmioRegionsPairwiseDisjoint_holds`
  — 3 RPi5 MMIO regions proven pairwise disjoint via `decide`.
  **M-9**: `serviceBfsFuel_sufficient` + `serviceBfsFuel_sound` bi-directional
  correctness under `serviceCountBounded`. `serviceBfsFuel_has_margin`.
  **M-8**: `arm64_regCount_valid` + `machineConfig_registerCount_default_eq_arm64GPRCount`
  ARM64 register count consistency theorems.
  Zero sorry/axiom. `test_full.sh` green.

- **X5 (Documentation, Hardening & Low-Severity) COMPLETE** (v0.22.22): 9 sub-tasks
  (X5-A through X5-I). 9 findings resolved (H-1, H-9, M-2, M-3, M-5, M-11, L-1, L-2,
  L-4/L-5/L-6/L-7):
  **H-1**: `docs/SECURITY_ADVISORY.md` created — starvation freedom documented as
  design-level advisory with seL4 precedent and recommended user-level mitigations.
  **H-9**: `cnode_capacity_always_ge4` documentation theorem witnessing CNode.empty
  capacity = 16 ≥ 4 enforcement chain.
  **M-3**: `schedulingCovertChannel_bounded_width` theorem + formal bandwidth analysis
  (≤ 400 bits/sec for typical configurations).
  **M-5**: `contextMatchesCurrent` idle-state design rationale documented.
  **M-11**: `invalidSyscallArgument` KernelError variant (discriminant 41) added to
  Lean and Rust ABI (42 total variants). Decode paths updated in `SyscallArgDecode.lean`.
  **M-2**: Default labeling context production warning confirmed, cross-referenced to
  SECURITY_ADVISORY.md SA-2.
  **L-1**: `VSpaceRoot.beq_converse_limitation` documented — converse proof deferred
  until RHTable.LawfulBEq established.
  **L-2**: RegisterFile BEq safety analysis documented — 4-point argument that
  non-lawful edge case cannot occur in real kernel execution.
  **L-4/L-5/L-6/L-7**: All 4 low-severity items confirmed with v0.22.17 audit trail
  cross-references in source code.
  Zero sorry/axiom. `test_full.sh` green. **WS-X PORTFOLIO COMPLETE.**

### WS-W workstream (v0.22.10 Pre-Release Audit Remediation) — COMPLETE

WS-W addresses 49 unique actionable findings from three comprehensive audits of
v0.22.10 (2 CRIT, 4 HIGH, 16 MED, 27 LOW) across 6 phases (W1–W6) with 52
atomic sub-tasks. Plan:
[`AUDIT_v0.22.10_WORKSTREAM_PLAN.md`](dev_history/AUDIT_v0.22.10_WORKSTREAM_PLAN.md).

- **W1 (Critical Rust ABI Fixes) COMPLETE** (v0.22.11): 9 sub-tasks (W1-A through W1-I).
  **CRIT-1/CRIT-2 fixed**: `notification_signal` and `notification_wait` SyscallId
  corrected from `Send`/`Receive` to `NotificationSignal`/`NotificationWait`.
  **HIGH-02 fixed**: `notification_signal` now accepts `Badge` parameter and passes
  it via MR\[0\], matching Lean `decodeNotificationSignalArgs` which reads badge from
  `requireMsgReg msgRegs 0`. **HIGH-1 fixed**: `MmioUnaligned` error variant added
  (discriminant 40), matching Lean `KernelError.mmioUnaligned`. **MED-03 fixed**: new
  `endpoint_reply_recv` wrapper for compound reply+receive operation. **MED-05 fixed**:
  lib.rs updated from "14 syscalls" to "17 syscalls". XVAL-015 conformance test
  corrected from asserting zero badge to asserting badge passthrough. 8 new W1
  conformance tests added (variant counts, ABI constants, encoding verification,
  register layout). Audit fix: `endpoint_reply_recv` corrected to map user
  `msg.regs[0]` into MR\[1\] (was silently dropped) and include reply\_target
  slot in `MessageInfo.length`. 168 Rust tests pass, zero doc warnings.
  Zero sorry/axiom.

- **W2 (Proof Formalism & Architecture) COMPLETE** (v0.22.12, audit v0.22.13): 8 sub-tasks
  (W2-A through W2-H). **W2-A (H-2)**: Field-disjointness formalism closure —
  added `modifiedFields` for 6 operation categories, 3 new per-predicate frame
  lemmas (`noStaleEndpointQueueReferences_frame`, `noStaleNotificationWaitReferences_frame`,
  `registryEndpointValid_frame`), `fieldDisjointness_frameIndependence_documented`
  theorem connecting 6 disjoint pairs to frame independence. **W2-B (H-1)**:
  `crossSubsystemInvariant_composition_gap_documented` theorem with comprehensive
  docstring explaining partial mitigation via frame lemmas and remaining gap scope.
  **W2-C (MED-04)**: `dispatchWithCap_wildcard_unreachable` proves all 17 `SyscallId`
  variants are covered by explicit dispatch arms. **W2-D (M-6)**: Fuel sufficiency
  documentation for `collectQueueMembers` citing `tcbQueueChainAcyclic` invariant.
  **W2-E (M-4)**: `serviceHasPathTo_fuel_exhaustion_conservative` proves fuel=0
  returns `true` (conservative safety). **W2-F (M-5)**: `removeDependenciesOf_objectIndex_eq`
  frame lemma + `serviceCountBounded_preservation_chain_documented` theorem with
  comprehensive preservation chain documentation. **W2-G (M-3)**: `enforcementBoundaryExtended`
  unified as definitional alias of `enforcementBoundary`, adding
  `enforcementBoundaryExtended_eq_canonical` element-wise equality proof.
  **W2-H (L-3)**: Documented all 9 elevated `maxHeartbeats` settings with rationale
  for inherent complexity. Zero sorry/axiom.

- **W3 (Dead Code Elimination) COMPLETE** (v0.22.14): 8 sub-tasks (W3-A through W3-H).
  Verification-first methodology: each candidate grep-verified across entire codebase
  before removal, with Category A/B/C classification. **W3-B**: Removed 7 dead
  KernelM helper theorems, 8 alignment predicates/proofs, 9 `isPowerOfTwo_of_pow2_*`
  witnesses, duplicate `maxLength`/`maxExtraCaps'`, 4 dead CDT helpers, 2 dead CDT
  observation functions from foundation layer. **W3-C**: Removed `resolveCapAddressK`,
  `severDerivationEdge`, `lookupUntyped`, `maxServiceFuel` from kernel subsystems.
  **W3-D**: Removed entire fast-projection cluster (~200 lines) from Projection.lean,
  3 dead enforcement boundary items from Wrappers.lean, 3 orphaned HashSet bridge
  lemmas from Prelude.lean. **W3-E**: Removed `deleteObject`, `addServiceGraph` from
  Builder.lean. **W3-F**: Removed `listLookup`, `withMachine` from StateBuilder.lean.
  **W3-G**: FrozenOps retained with architectural status documentation (zero production
  consumers, H3 integration target). **W3-H**: Removed `encodeMsgRegs` (identity),
  `RegisterWriteInvariant` (stub). Zero sorry/axiom.

- **W4 (Platform & Architecture Hardening) COMPLETE** (v0.22.15): 7 sub-tasks
  (W4-A through W4-G). **W4-A (M-8)**: BCM2712 datasheet validation checklist
  completed — all 14 S5-F address constants cross-referenced with S6-G citations,
  marked **Validated** with datasheet section and date. **W4-B (M-9)**: FDT parsing
  hardened — explicit bounds checks added to `readBE32`, `readCString`, `readCells`
  to prevent integer overflow on malformed DTB input. **W4-C (MED-02)**: All 3
  `native_decide` instances in Board.lean replaced with `decide`, eliminating TCB
  expansion (`mmioRegionDisjoint_holds`, `rpi5MachineConfig_wellFormed`,
  `rpi5DeviceTree_valid`). **W4-D (LOW-02)**: Stale `@[implemented_by]` comment
  fixed in DeviceTree.lean — `fromDtb` stub now documents `fromDtbFull` as separate
  function. **W4-E (L-15)**: `bootFromPlatformUnchecked` deprecated via docstring
  directing to `bootFromPlatformChecked`. **W4-F (L-16)**: MMIO formalization gap
  documented — comprehensive boundary description (modeled: address validation,
  alignment, bounds, frame, W1C; deferred: volatile non-determinism, barriers,
  device-specific semantics, interrupt effects, cache coherency). **W4-G (L-12)**:
  `encodeMsgRegs` already removed in W3-H. Zero sorry/axiom.

- **W5 (Test Infrastructure & Coverage) COMPLETE** (v0.22.16): 8 sub-tasks
  (W5-A through W5-H). **W5-A (M-10)**: Consolidated 3 duplicate `expectError`
  implementations into shared `Helpers.lean` with `msgPrefix` parameter.
  **W5-B (L-17)**: Documented test fixture OID ranges (11-suite table in
  `Helpers.lean`). **W5-C (L-18)**: Added chain33 service lifecycle tests — 25
  assertions covering `registerInterface`, `registerService` (5 error paths),
  `serviceRegisterDependency` (acyclic + cycle + nonexistent source/target),
  `revokeService` (success + registry/graph removal + cleanup + nonexistent).
  3 `assertInvariants` calls after state-mutating operations. **W5-D (M-11)**: Improved
  `buildChecked` error reporting with check numbers and entity details.
  **W5-E**: Added mutation testing assertions to chain1 and chain5 verifying
  actual state changes. **W5-F (L-2)**: Removed unused `_hCap` parameter from
  `policyOwnerAuthoritySlotPresent_of_capabilityLookup`. **W5-G (L-7)**:
  Documented `resolveExtraCaps` silent-drop behavior (seL4-matching design).
  Zero sorry/axiom.

- **W6 (Code Quality & Documentation) COMPLETE** (v0.22.17): 12 sub-tasks
  (W6-A through W6-L). **W6-A (M-7)**: `removeThreadFromQueue` TCB existence
  invariant documented — explains defensive `(none, none)` fallback is safe,
  citing `tcbQueueChainAcyclic` and cleanup-before-retype ordering. **W6-B (L-4)**:
  Factored redundant lifecycle preservation proofs — created bundled
  `spliceOutMidQueueNode_preserves`, `removeFromAllEndpointQueues_preserves`,
  `removeFromAllNotificationWaitLists_preserves` theorems; individual accessors
  now project from bundles. **W6-C (L-6)**: Removed unused
  `crossSubsystemPredicates` list and `crossSubsystemPredicates_count` witness;
  replaced with documentation comment directing to `crossSubsystemInvariant`.
  **W6-D (L-8)**: Documented two-tier dispatch design rationale in API.lean
  (capability-only tier + argument-decoding tier). **W6-E (L-11)**: Extracted
  `default_objects_none` and `default_objects_absurd` helpers and applied them
  across 24+ default-state proofs, replacing verbose `RHTable_get?_empty`
  patterns with single-call absurdity discharge. **W6-F (L-13)**:
  Added `RHSet.insert_invExtK`, `RHSet.erase_invExtK`, `RHSet.empty_invExtK'`
  public API wrappers using `RHSet.invExtK` abstraction. **W6-G (LOW-1)**:
  Added compile-time `const_assert` block in `message_info.rs` validating
  `MAX_LABEL`, `MAX_MSG_LENGTH`, `MAX_EXTRA_CAPS` against Lean values.
  **W6-H (LOW-2)**: Documented `set_mr`/`get_mr` API asymmetry in
  `ipc_buffer.rs` — intentional design (write hint vs. read refusal).
  **W6-I (LOW-04)**: Documented CDT edge theorem suite as specification
  surface in Structures.lean. **W6-J (LOW-01)**: Documented 14 RHTable
  specification surface theorems in Prelude.lean. **W6-K (H-3 downgraded)**:
  Documented lifecycle metadata enforcement chain — 4-step contract discipline
  via `lifecyclePreRetypeCleanup` (`cleanupTcbReferences`,
  `cleanupEndpointServiceRegistrations`, `detachCNodeSlots`) with
  `lifecycleRetypeObject_preserves_lifecycleInvariantBundle`.
  **W6-L**: Documentation sync across CHANGELOG, WORKSTREAM_HISTORY, codebase_map,
  README, and GitBook. Zero sorry/axiom. **WS-W PORTFOLIO COMPLETE.**

### WS-V workstream (v0.21.7 Pre-Release Audit Remediation) — COMPLETE

WS-V addresses 95 findings from three comprehensive audits of v0.21.7 (5 HIGH,
61 MEDIUM, 29 LOW) across 8 phases (V1–V8) with 147 atomic sub-tasks. Plan:
[`AUDIT_v0.21.7_WORKSTREAM_PLAN.md`](dev_history/AUDIT_v0.21.7_WORKSTREAM_PLAN.md).

- **V3 (Proof Chain Hardening) COMPLETE** (v0.22.2): 26 sub-tasks (V3-A through V3-M).
  All 8 `True := trivial` documentation theorems replaced with real machine-checked
  proofs. **V3-B `invExtK` migration**: Kernel-level `invExtK` bundle
  (`invExt ∧ size < capacity ∧ 4 ≤ capacity`) in Bridge.lean eliminates 59
  kernel-facing `hSize`/`hCapGe4` parameters across 13 files. RunQueue fields
  reduced 9→3. `slotsUnique` = `invExtK` (transparent alias). `allTablesInvExtK`
  replaces `allTablesInvExt` with 16 `invExtK` conjuncts. Zero sorry/axiom.
  **Machine-checked**: `invExtFull` bundle + `erase_preserves_invExtFull`
  eliminating redundant `hSize` (H-RH-1). `uniqueRadixIndices_sufficient` radix
  precondition chain (H-RAD-1). `extractBits_identity` + `buildCNodeRadix_hNoPhantom_auto_discharge`
  closing `hNoPhantom` gap (M-DS-4). CDT acyclicity: `cdtShrinkingOps_preserve_acyclicity`
  via `edgeWellFounded_sub` edge-removal proof (M-PRF-1).
  V3-E loop composition: `ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle` (fuel-indexed
  induction) + `ipcUnwrapCaps_preserves_capabilityInvariantBundle` (unified Bool-parametric)
  closing M-PRF-2 capability transfer chain gap. `resolveCapAddress_callers_check_rights`
  dispatch chain rights theorem in API.lean (M-PRF-3). `notificationSignal_preserves_waitingThreadsPendingMessageNone`
  via `cases`-based path decomposition (M-PRF-5). `notificationWake_pendingMessage_was_none`
  blocking-state implies `pendingMessage = none` (L-IPC-1). 7 primitive + 7 operation-level
  preservation lemmas for `waitingThreadsPendingMessageNone` covering all IPC operations:
  `notificationWait`, `notificationSignal`, `endpointSendDual`, `endpointReceiveDual`,
  `endpointCall`, `endpointReply`, `endpointReplyRecv`. Critical semantic fix: `blockedOnCall` removed from
  invariant-constrained states (callers legitimately carry outgoing messages).
  Two backward lemmas added: `storeTcbQueueLinks_tcb_pendingMessage_backward`,
  `endpointQueueEnqueue_tcb_pendingMessage_backward`. V3-G6: `waitingThreadsPendingMessageNone`
  integrated as 5th conjunct of `ipcInvariantFull` (was 4-conjunct). All bundle
  preservation theorems, extractors, default proofs, and `ipcInvariantFull_compositional`
  updated. New extractor: `coreIpcInvariantBundle_to_waitingThreadsPendingMessageNone`.
  **V3-J/K/J-cross integration**: `ipcStateQueueMembershipConsistent` (L-IPC-3),
  `endpointQueueNoDup` (L-LIFE-1), `queueNextBlockingConsistent`, and
  `queueHeadBlockedConsistent` integrated as 6th/7th/8th/9th conjuncts of
  `ipcInvariantFull` (now 9-conjunct). New files: `QueueNoDup.lean` (3 primitive
  frame lemmas + TCB-store primitives + per-operation proofs for notification,
  notificationWait, endpointReply), `QueueMembership.lean` (prim-1 frame lemma +
  scheduler helpers + pointwise transfer + TCB-store primitives with non-blocking
  and general variants + per-operation proofs for notification, notificationWait,
  endpointReply), `QueueNextBlocking.lean` (10 primitive preservation proofs +
  QHBC primitives). 4 compound V3-J preservation proofs in `Structural.lean`:
  `endpointSendDual`, `endpointReceiveDual`, `endpointCall`, `endpointReplyRecv`
  all preserve `ipcStateQueueMembershipConsistent`. Definition fix: `blockedOnCall`
  uses `sendQ` not `receiveQ`. All 10 `_preserves_ipcInvariantFull` bundle theorems
  updated. New extractors: `coreIpcInvariantBundle_to_endpointQueueNoDup`,
  `coreIpcInvariantBundle_to_ipcStateQueueMembershipConsistent`,
  `coreIpcInvariantBundle_to_queueNextBlockingConsistent`,
  `coreIpcInvariantBundle_to_queueHeadBlockedConsistent`. Default state,
  lifecycle, and `advanceTimerState` cascade fixes. Zero sorry/axiom, 182 build
  targets pass, `test_full.sh` green.

- **V5 (Defensive Coding & Robustness) COMPLETE** (v0.22.5): 16 sub-tasks (V5-A
  through V5-P). Defense-in-depth hardening across all kernel subsystems.
  Key changes: V5-A replaced panicking `ByteArray.get!` with safe `data[·]?`
  in all DTB parsing functions; V5-F added explicit error return for `handleYield`
  with `current = none`; V5-L added configurable `configDefaultTimeSlice` to
  `SchedulerState`; V5-N removed redundant `detachSlotFromCdt` in
  `processRevokeNode` and `cspaceRevokeCdtStrict`; V5-O/V5-P added queue
  membership validation and occupied-slot guard to frozen operations;
  V5-D/V5-E added checked variants of `saveOutgoingContext`/`restoreIncomingContext`
  with explicit success indicators and design notes in `schedule`;
  V5-H `domainTimeRemainingPositive` now integrated as 8th conjunct of
  `schedulerInvariantBundleFull` with per-operation preservation proofs for
  `schedule`, `handleYield`, `timerTick`, `switchDomain`, `scheduleDomain`;
  V5-J added `ThreadId.toObjIdVerified` with TCB type verification. All 10
  affected Preservation.lean proofs updated for V5-F/V5-N changes. V5-C test
  code migrated to `bootFromPlatformUnchecked` alias. Zero sorry/axiom.

- **V6 (Information Flow & Cross-Subsystem) COMPLETE** (v0.22.7): 20 sub-tasks
  (V6-A through V6-L). Cross-subsystem field-disjointness formalization:
  `StateField` enum + 10 pairwise disjointness/overlap witnesses (6 disjoint +
  4 non-disjoint with explicit `false` witnesses) + 2 frame lemmas
  (`registryDependencyConsistent_frame`, `serviceGraphInvariant_frame`) in
  `CrossSubsystem.lean` (V6-A). `serviceCountBounded` preservation:
  `serviceCountBounded_of_eq`, `serviceCountBounded_monotone`,
  `serviceGraphInvariant_monotone` across lifecycle and IPC operations (V6-B).
  `bibaIntegrityFlowsTo` reference model with corrected docstrings (standalone
  semantics: `dst ≥ src`; designed for drop-in use in `securityFlowsTo`'s
  swapped-argument position), `integrityFlowsTo_is_not_biba` and
  `integrityFlowsTo_denies_write_up_biba_allows` comparison theorems (V6-C).
  `LabelingContextValid` predicate with `defaultLabelingContext_valid` and
  `labelingContextValid_provides_coherence` (V6-D). `ObservableState.serviceRegistry`
  field extension with `projectServiceRegistry` + full ripple fixes across
  Helpers.lean, Operations.lean, Composition.lean (V6-E).
  `enforcementBoundaryComplete_counts` (11+7+4=22) and
  `enforcementBoundary_names_nonempty` (V6-F). `endpointPolicyRestricted`
  well-formedness with `endpointPolicyRestricted_no_overrides` and
  `endpointFlowCheck_restricted_subset` (V6-G). `DeclassificationEvent` structure
  with `authorizationBasis` field, `recordDeclassification` audit trail, and
  3 preservation theorems (V6-H).
  `kernelOperationNiConstructor` 32-variant mapping, `niStepCoverage_operational`,
  `niStepCoverage_injective` (1:1), `niStepCoverage_count` (=32) (V6-I).
  `acceptedCovertChannel_scheduling` documented covert channel (V6-J).
  `defaultLabelingContext_insecure` + `defaultLabelingContext_all_threads_observable`
  warnings (V6-K). `enforcementBoundaryExtended` updated to 22 entries with
  `enforcementBoundaryExtended_count` and `enforcementBoundaryExtended_matches_canonical`
  (V6-L). 26 V6 test cases in InformationFlowSuite. Zero sorry/axiom.

- **V8 (Test Coverage & Documentation) COMPLETE** (v0.22.9, audit v0.22.10): 19 sub-tasks
  (V8-A through V8-H). V8-A: End-to-end `syscallEntryChecked` pipeline test
  (register decode → arg extraction → checked dispatch → invariant preservation
  → trace equivalence). V8-B: `cspaceMove` end-to-end test. V8-C: Post-mutation
  invariant checks for 5 additional operations. V8-D: dequeue-on-dispatch Check 8
  fix propagated to 7 test states. V8-E: `partial` removed from
  `intrusiveQueueReachable`. V8-F: Fixture drift detection via SHA-256 hash
  companion. V8-G: `ThreadState` enum (8 variants, incl. `BlockedReply`) with non-invasive
  `syncThreadStates` design preserving all operational proofs.
  V8-H: `dispatchCapabilityOnly` shared helper eliminating ~120 lines of dispatch
  duplication. 38 inter-transition invariant checks. Zero sorry/axiom.

- **V7 (Performance & Data Structure Optimization) COMPLETE** (v0.22.8): 19
  sub-tasks (V7-A through V7-J). V7-C: `LawfulBEq` made explicit API-level
  requirement for all `RHTable` public operations (get?, contains, erase, insert,
  toList, filter, insertNoResize, resize) with ripple fixes across 18 files
  including Bridge.lean, Preservation.lean, Lookup.lean, Prelude.lean,
  FrozenState.lean, FreezeProofs.lean, Commutativity.lean. V7-D: General
  `filter_preserves_key` theorem for arbitrary predicates proved via
  `filter_fold_present` / `filter_fold_absent_by_pred`. V7-A: `filter_fold_present`
  proof refactored with `filter_fold_present_step` helper; heartbeat budget reduced
  from 3.2M to 400K. V7-B: `insertLoop_preserves_noDupKeys` and
  `insertLoop_preserves_pcd` proofs refactored with `noDupKeys_after_set` and
  `distCorrect_after_set` extracted helpers; heartbeat budgets reduced from 800K
  to 420K. V7-G: `CNodeRadix.toList` refactored from O(n²) append to O(n)
  cons+reverse with updated proof chain. V7-I: `irqKeysNoDup`/`objIdKeysNoDup`
  replaced with O(n) `natKeysNoDup` using `Std.HashSet`. V7-E: `native_decide`
  replaced with `decide` in `RegisterFile.not_lawfulBEq`. V7-F: Non-lawful
  `BEq RegisterFile` documented in Machine.lean and test code. V7-H: Robin Hood
  `erase` size decrement safety documented under `invExt`. V7-J: `RunQueue.wellFormed`
  design rationale and `ofList` validated constructor documented. Zero sorry/axiom.

- **V4 (Platform & Hardware Fidelity) COMPLETE** (v0.22.3): 26 sub-tasks (V4-A1
  through V4-N). **V4-A boot-to-runtime invariant bridge**: Complete machine-checked
  proof that `bootFromPlatform` with ANY well-formed `PlatformConfig` satisfying
  `bootSafe` produces a state satisfying all 9 components of
  `proofLayerInvariantBundle`. Key contributions: `bootSafeObject` predicate
  (5-conjunct: empty endpoint queues, idle notifications, CNode slot/depth/badge
  validity, TCB clean boot state, no VSpaceRoots), `foldObjects_objects_bootSafe`
  bridge lemma connecting config entries to post-boot objects via RHTable insert
  correctness, `tcbQueueChainAcyclic_of_allNextNone` eliminating cyclic queue paths
  from boot state, `collectQueueMembers_none` public bridge for interior queue
  member discharge. Per-field preservation chain: 11 `@[simp]` operation lemmas,
  11 fold-level lemmas, 11 boot-level theorems. `bootToRuntime_invariantBridge_general`
  composes with `freeze_preserves_invariants` for the end-to-end bridge.
  V4-B through V4-N: MMIO alignment checks, W1C semantics, parameterized RAM,
  private VSpace variants, W^X enforcement in decode and permissions, DTB parsing
  pipeline (readCString, lookupFdtString, findMemoryRegProperty, full fromDtb),
  generalized extractMemoryRegions for 32/64-bit address cells. Fixed unused simp
  args in SyscallArgDecode.lean. Zero sorry/axiom, `test_full.sh` green.

- **V2 (API Surface Completion) COMPLETE** (v0.22.1): 9 sub-tasks (V2-A through V2-I).
  `SyscallId` count grew from 14 to 17: added `notificationSignal` (discriminant 14),
  `notificationWait` (discriminant 15), `replyRecv` (discriminant 16). Both unchecked
  (`dispatchWithCap`) and checked (`dispatchWithCapChecked`) dispatch paths wired with
  enforcement wrappers and delegation theorems. Rust `SyscallId` variants 14–16 added
  with matching encode/decode and `required_right`. `MessageInfo` label field bounded to
  20 bits (seL4 convention) in both Lean and Rust (was unbounded/55-bit). Cap transfer
  slot base made configurable via `capRecvSlot` field (was hardcoded `Slot.ofNat 0`).
  `SyscallArgDecode.lean` updated with notification/replyRecv decode structs, round-trip
  theorems, and error exclusivity proofs. Zero sorry/axiom.

- **V1 (Rust ABI Hardening) COMPLETE** (v0.22.0): 12 sub-tasks (V1-A through V1-L).
  Hardened the Rust ABI boundary: u64→u32 truncation guard in `decode_response`
  (H-RS-1), `LifecycleRetypeArgs.new_type` changed from raw u64 to validated
  `TypeTag` (M-RS-1), 13 `unwrap()` calls replaced with `new_const()` (M-RS-2),
  error variants corrected for `IpcBuffer::get_mr` and `CSpaceMintArgs::decode`
  (M-RS-3/M-RS-4), W^X `checked_bitor` for `PagePerms` (M-RS-5),
  `is_reserved()`/`is_valid()` for `Slot`/`DomainId`/`Priority` (M-RS-7),
  `ServiceRegisterArgs` bounds validation (L-RS-2), stale comment fix (L-RS-1),
  and 10 new conformance tests. All 157 Rust tests pass, zero warnings.

### WS-U workstream (v0.20.7 Audit Remediation) — Phase U8 COMPLETE (PORTFOLIO COMPLETE)

WS-U Phase U8 is the final documentation and closure phase. 8 sub-tasks
(U8-A through U8-H): eliminates `simSubstantiveMemoryMap` duplication with
compile-time consistency theorem, documents IRQ/INTID range limitations,
notification word overflow, scheduler starvation design, hash collision
assumptions, synchronizes all documentation to v0.21.7, runs comprehensive
validation, and writes the WS-U closure report. Version v0.21.7. Plan:
[`AUDIT_v0.20.7_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.20.7_WORKSTREAM_PLAN.md).

- **U8-A (U-L16)**: Eliminated `simSubstantiveMemoryMap` duplication — made
  `simMachineConfig.memoryMap` reference the shared definition directly,
  added compile-time consistency theorem in `Contract.lean`.
- **U8-B (U-L18, U-L19)**: Documented IRQ/INTID range limitations (SGI IPI
  usage, GIC-400 SPI cap at 223) in `RPi5/BootContract.lean` and `RPi5/Board.lean`.
- **U8-C (U-L24)**: Documented notification word overflow — model uses
  unbounded Nat, WS-V must enforce 64-bit width at platform boundary.
- **U8-D (U-L26)**: Documented scheduler design decisions — `recomputeMaxPriority`
  O(p) complexity acceptable for ≤256 priorities, starvation freedom not
  guaranteed (matches seL4 fixed-priority design).
- **U8-E (U-M35)**: Documented hash collision assumption — Robin Hood proofs
  assume `LawfulBEq` and deterministic `Hashable`, collision resistance not
  modeled (kernel uses typed system-assigned IDs, not adversary-controlled keys).
- **U8-F**: Synchronized all documentation: README, SELE4N_SPEC, DEVELOPMENT,
  WORKSTREAM_HISTORY, CLAIM_EVIDENCE_INDEX, GitBook chapters, codebase_map.json.
  Updated version badge to v0.21.7.
- **U8-G**: Comprehensive validation — `test_full.sh` and `test_nightly.sh` pass.
- **U8-H**: WS-U closure report written.

Zero sorry, zero axiom.

#### WS-U Phase U7 — COMPLETE (v0.21.6)

WS-U Phase U7 removes dead code, superseded invariant bundles, trivial
tautology theorems, fixes BEq symmetry, migrates native_decide to decide,
and adds builder/frozen commutativity proofs. 12 sub-tasks (U7-A through
U7-L). Version v0.21.6. Plan:
[`AUDIT_v0.20.7_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.20.7_WORKSTREAM_PLAN.md).

- **U7-A**: Deleted dead `KMap.lean` module (219 lines, never imported).
- **U7-B**: Removed dead types from Assumptions, MmioAdapter, Policy.
- **U7-C**: Removed dead functions from Prelude, Machine, FrozenState,
  RunQueue, VSpaceBackend.
- **U7-D**: Removed trivial `_deterministic` tautology theorems.
- **U7-E**: Removed superseded invariant bundles (scheduler, capability).
- **U7-G/H**: Fixed `BEq RHTable` symmetry + `beq_symmetric` lemma.
- **U7-I**: Migrated 5 `native_decide` to `decide` (TCB reduction).
- **U7-J**: Refactored high-heartbeat Robin Hood proofs (all ≤800K removed).
- **U7-L**: Added builder/frozen commutativity proofs in FreezeProofs.lean.

#### WS-U Phase U6 — COMPLETE (v0.21.5)

WS-U Phase U6 improves model-hardware fidelity for the RPi5 platform. 12
sub-tasks (U6-A through U6-L). Version v0.21.5. Plan:
[`AUDIT_v0.20.7_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.20.7_WORKSTREAM_PLAN.md).

- **U6-A (U-M08)**: Added formal MMIO abstraction boundary with `MmioReadKind`,
  `MmioWriteKind`, `MmioRegionDesc`, and `MmioSafe` hypothesis type.
- **U6-B (U-M08)**: Added `notInMmioRegion` predicate for VSpace proof guidance.
- **U6-C (U-M09)**: Strengthened `registerContextStable` to require TCB register
  match instead of permissive SP-preservation disjunct.
- **U6-D (U-M09)**: Updated RPi5 proof hooks documentation.
- **U6-E (U-M12)**: Added `irqsUnique` duplicate IRQ detection in boot config.
- **U6-F (U-M13)**: Added `objectIdsUnique` and `PlatformConfig.wellFormed`.
- **U6-G (U-M15)**: Proved `bootToRuntime_invariantBridge_empty` composing boot
  validity through freeze to runtime invariant bundle.
- **U6-H (U-M10)**: Added `mmioWrite32`/`mmioWrite64` for GIC register access.
- **U6-I (U-M22)**: Documented non-standard BIBA integrity direction.
- **U6-J (U-M24)**: Documented service registry NI projection gap.
- **U6-K (U-M23)**: Documented accepted covert channels.
- **U6-L (U-M14)**: Documented cross-subsystem invariant composition gap.

Zero sorry, zero axiom.

### WS-U workstream (v0.20.7 Audit Remediation) — Phase U5 COMPLETE

WS-U Phase U5 refactors API dispatch integrity. 14 sub-tasks (U5-A through
U5-N). Version v0.21.4. Plan:
[`AUDIT_v0.20.7_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.20.7_WORKSTREAM_PLAN.md).

- **U5-A (U-M02)**: Verified structural equivalence of checked/unchecked
  dispatch for all 6 capability-only syscalls with machine-checked proofs.
- **U5-B (U-M01)**: Routed `.call` through `endpointCallChecked` enforcement
  wrapper, replacing inline `securityFlowsTo` guard.
- **U5-C (U-M04)**: Routed `.reply` through `endpointReplyChecked` wrapper
  for defense-in-depth.
- **U5-D (U-L20)**: Replaced trivial `True` placeholder with 7 structural
  equivalence theorems for capability-only dispatch arms.
- **U5-E (U-M07)**: Fixed `decodeVSpaceMapArgs` error code from `.policyDenied`
  to `.invalidArgument`. Added `invalidArgument` to `KernelError`.
- **U5-F/G (U-M21)**: Added `capabilityOnlyOperations` definition with
  security rationale documentation.
- **U5-H through U5-N**: Documentation of design-intentional behaviors
  (badge-0, message handling, notification overwrite, slot 0, GrantReply,
  CDT tracking, deferred notificationSignal).

Zero sorry, zero axiom.

### WS-U workstream (v0.20.7 Audit Remediation) — Phase U4 COMPLETE

WS-U Phase U4 optimizes proof chains and invariant composition. 3 sub-task
groups completed (U4-A/B/C/D, U4-K, U4-N). Version v0.21.3. Plan:
[`AUDIT_v0.20.7_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.20.7_WORKSTREAM_PLAN.md).

- **U4-A/B/C/D**: Discharged `hProjection` preconditions for all four IPC
  endpoint operations, making scheduler preservation theorems self-contained.
- **U4-K**: Made `ipcInvariantFull` preservation self-contained for all four
  IPC operations by deriving `allPendingMessagesBounded` and `badgeWellFormed`
  internally. Added 3 primitive + 8 composed preservation theorems.
- **U4-N**: Proved BFS positional queue lemma and queue membership variant for
  CDT `descendantsOf`. Key infrastructure for transitive closure fuel
  sufficiency.

Zero sorry, zero axiom.

### WS-U workstream (v0.20.7 Audit Remediation) — Phase U3 COMPLETE

WS-U Phase U3 hardens the Rust userspace ABI layer. 10 sub-tasks (U3-A through
U3-J). Version v0.21.2. Plan:
[`AUDIT_v0.20.7_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.20.7_WORKSTREAM_PLAN.md).

- **U3-A (U-H11)**: Added `clobber_abi("C")` to `svc #0` inline assembly.
  Compiler now knows all AArch64 caller-saved registers may be clobbered by
  the kernel, preventing silent register corruption.
- **U3-B/C (U-M32)**: Made `MessageInfo` fields private. Added `length()`,
  `extra_caps()`, `label()` accessors. Updated all call sites across
  `sele4n-abi` and `sele4n-sys` to use `MessageInfo::new()`.
- **U3-D/E (U-M33)**: Replaced `From<u8>` with `TryFrom<u8>` for
  `AccessRights`. Values > 0x1F (bits 5–7 set) rejected with
  `AccessRightsError`. Full roundtrip conformance tests for 0–255.
- **U3-F (U-L08)**: Added `#[non_exhaustive]` to `KernelError` for
  forward-compatible error variant additions.
- **U3-G (U-L09)**: Added `RegisterFile` with safe `get()`/`set()` returning
  `Option` instead of panicking on out-of-bounds.
- **U3-H (U-L10)**: Added bit-layout ASCII diagrams for `MessageInfo`
  encode/decode doc-comments.
- **U3-I (U-M34)**: Added compile-time `const` layout assertions for
  `IpcBuffer` `#[repr(C)]` (960 bytes, 8-byte alignment).
- **U3-J (U-L13)**: Added `scripts/test_rust_conformance.sh` — dedicated
  conformance runner with unsafe containment check and test vector dump.

All 135 Rust tests pass. Zero sorry, zero axiom.

### WS-U workstream (v0.20.7 Audit Remediation) — Phase U2 COMPLETE

WS-U Phase U2 hardens safety boundaries across the kernel's input validation
and type-safety surface. 14 sub-tasks (U2-A through U2-N). Version v0.21.1.
Plan:
[`AUDIT_v0.20.7_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.20.7_WORKSTREAM_PLAN.md).

- **U2-A/B/C (U-H06)**: Added `VAddr.isCanonical` predicate and canonical
  address check in `vspaceMapPageChecked`, `vspaceMapPageCheckedWithFlush`,
  and `decodeVSpaceMapArgs`. Canonical address rejection theorem proved.
- **U2-D/E/F (U-H07)**: Parameterized physical address width through
  `MachineConfig.physicalAddressWidth`. Added `physicalAddressBoundForConfig`
  and `vspaceMapPageCheckedWithFlushPlatform`. Updated `DeviceTree.fromDtbWithRegions`.
- **U2-G/H (U-H08)**: Added `ASID.isValidForConfig` predicate and ASID
  validation in `decodeVSpaceMapArgs` and `decodeVSpaceUnmapArgs`. Updated all
  roundtrip and error-iff proofs with ASID preconditions.
- **U2-I/J (U-H05)**: Documented `vspaceMapPage` and `lifecycleRetypeObject`
  as internal proof helpers. Updated test harness references to use public API.
- **U2-K (U-L03)**: Added `AccessRightSet.mk_checked` proof-carrying
  constructor. Added `empty_valid` and `singleton_valid` lemmas.
- **U2-L (U-M18)**: Audited all `storeObject` call sites. Documented three
  categories: allocation-guarded, in-place mutation, and builder/boot.
- **U2-M (U-M20)**: Added `allTablesInvExt_witness` compile-time completeness
  check — mismatches between `allTablesInvExt` conjuncts and the 16-field
  witness produce a type error.
- **U2-N (U-M17)**: Added negative `LawfulBEq` instances for `RegisterFile`
  and `TCB` via counterexample proofs (out-of-range GPR index 32).

Zero sorry, zero axiom. All 14 sub-tasks complete.

### WS-U workstream (v0.20.7 Audit Remediation) — Phase U1 COMPLETE

WS-U Phase U1 addresses 7 correctness findings from the v0.20.7 audit. 13
sub-tasks (U1-A through U1-M). Version v0.21.0. Plan:
[`AUDIT_v0.20.7_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.20.7_WORKSTREAM_PLAN.md).

- **U1-A/B/C (U-H01)**: Fixed `frozenQueuePopHead` to clear `queuePPrev`,
  enabling multi-round IPC re-enqueue. Regression test FO-021 added.
- **U1-D/E (U-H02)**: Added post-allocation page-alignment re-verification in
  `retypeFromUntyped`. Updated decomposition theorem.
- **U1-F/G (U-H04)**: Replaced `lifecycleRetypeDirect` with
  `lifecycleRetypeWithCleanup` in API dispatch. Updated doc comments.
- **U1-H/I (U-H14)**: Aligned `lifecycleRetypeAuthority` from `.write` to
  `.retype`, matching `requiredRight` mapping. Updated authority theorems.
- **U1-J/K (U-H13)**: Changed `endpointReceiveDual` CSpace root fallback from
  silent `senderId.toObjId` to explicit `.invalidCapability` error. Updated IPC
  preservation theorems.
- **U1-L (U-H03)**: Extracted `cspaceDeleteSlotCore` (non-private core) with
  `cspaceDeleteSlot` as thin guard wrapper (`hasCdtChildren` check). Migrated
  6 preservation theorems to core+wrapper pattern across 3 proof files.
- **U1-M (U-M39)**: Added defensive `saveOutgoingContext` in `switchDomain`
  before clearing `current`. Updated scheduler preservation theorems.

Zero sorry, zero axiom. All 13 sub-tasks complete.

### WS-T workstream (Deep-Dive Audit Remediation) — PORTFOLIO COMPLETE

WS-T addresses all findings from dual v0.19.6 deep-dive audits (4 HIGH, 52
MEDIUM, 16 selected LOW). 8 phases (T1–T8), 94 sub-tasks. Version range
v0.20.0–v0.20.7. All 94 sub-tasks complete. See
[`AUDIT_v0.19.6_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.19.6_WORKSTREAM_PLAN.md).
Closure report: [`WS_T_CLOSURE_REPORT.md`](dev_history/audits/WS_T_CLOSURE_REPORT.md).

- **T1 (v0.20.0) — COMPLETE**: Benchmarking Blockers. Fixed frozen IPC queue
  enqueue semantics (M-FRZ-1/2/3) — implemented `frozenQueuePushTail` with
  dual-queue invariant precondition checks, integrated into all three frozen
  endpoint operations (Send/Receive/Call), added 7 preservation theorems.
  Added 4 missing Rust `KernelError` variants (H-4, discriminants 34-37) with
  cross-validation tests. Registered `OperationChainSuite` as lakefile target
  (M-TST-1). Zero sorry, zero axiom. All 10 sub-tasks complete.

- **T2 (v0.20.1) — COMPLETE**: Model & CDT Integrity. Closed 2 HIGH findings:
  `AccessRightSet.ofList` now has `valid` postcondition (H-1), CDT constructor
  made `private` with verified `mk_checked` smart constructor (H-2). Closed 4
  MEDIUM findings: frozen state preserves TLB (M-NEW-1), bundled `storeObject`
  preservation theorem (M-NEW-2), `capabilityRefs` filter/fold invExt proofs
  (M-NEW-3), Builder `objectIndex`/`objectIndexSet` updates (M-BLD-1). Closed
  1 LOW finding: CNode `guardBounded` predicate added to `wellFormed` (L-NEW-4).
  Documentation-only: `attachSlotToCdtNode` ordering rationale (M-ST-2). Zero
  sorry, zero axiom. All 12 sub-tasks complete.

- **T3 (v0.20.2) — COMPLETE**: Rust ABI Hardening. Closed 3 MEDIUM findings:
  `MessageInfo::encode()` now returns `Result` with 55-bit label bound check
  preventing silent truncation (M-NEW-9). `VSpaceMapArgs.perms` changed from
  raw `u64` to typed `PagePerms` with decode-time validation (M-NEW-10).
  `ServiceRegisterArgs` `requires_grant` decode changed from permissive
  `!= 0` to strict `match { 0 => false, 1 => true, _ => error }` (M-NEW-11).
  `#![deny(unsafe_code)]` confirmed present (WS-S S1-H). 119 Rust tests pass
  (50 unit + 32 conformance + 12 sys + 25 types). All 8 sub-tasks complete.

- **T4 (v0.20.3) — COMPLETE**: IPC & Capability Proof Closure. All 12 sub-tasks
  complete. Closed M-IPC-1: `ipcStateQueueConsistent` preservation for
  `endpointCall`, `endpointReplyRecv`, `notificationSignal`, and `notificationWait`.
  Closed M-IPC-2 (T4-D): proved `endpointQueueRemoveDual_preserves_dualQueueSystemInvariant`
  — complete sorry-free proof (1023 lines) covering all 4 paths with
  `tcbQueueChainAcyclic` acyclicity invariant. Closed M-IPC-3: `ipcInvariantFull`
  preservation for WithCaps wrapper operations. Proved `descendantsOf_fuel_sufficiency`
  with 8 BFS lemmas (M-CAP-2). Proved `buildCNodeRadix_lookup_equiv` bidirectional
  equivalence (M-DS-3). Badge override CDT tracking documentation (M-CAP-1). NI
  projection hypothesis documentation (M-IF-3). `ipcInvariantFull_compositional`
  helper (L-P10). `insert_maxPriority_consistency` for RunQueue (M-SCH-1). Zero
  sorry, zero axiom. 12 of 12 sub-tasks complete.

- **T5 (v0.20.4) — COMPLETE**: Lifecycle, Service & Cross-Subsystem. Closed 4
  MEDIUM findings: `lifecycleRetypeObject`/`lifecycleRetypeDirect` marked as
  internal building blocks with safety annotations (M-NEW-4). Defined
  `KernelObject.wellFormed` predicate with decidable validation in
  `lifecycleRetypeWithCleanup` (M-NEW-5). Fixed intrusive queue cleanup for
  mid-queue nodes via `spliceOutMidQueueNode` with predecessor/successor link
  patching (M-LCS-1). Extended `noStaleEndpointQueueReferences` to check
  interior queue members via bounded `collectQueueMembers` traversal (M-CS-1).
  Closed 3 LOW findings: `cleanupEndpointServiceRegistrations` now calls
  `removeDependenciesOf` to prevent orphaned dependency edges (L-NEW-1), with
  `registryEndpointValid` preservation proof (L-NEW-2). Defined
  `noStaleNotificationWaitReferences` predicate and added to
  `crossSubsystemInvariant` 4-tuple (L-NEW-3). Proved
  `threadPriority_membership_consistent` closing scheduler M-SCH-3 gap with
  insert/remove preservation proofs. Added `@[deprecated]` annotations to
  `lifecycleRetypeObject`/`lifecycleRetypeDirect` for compile-time enforcement.
  Fixed `spliceOutMidQueueNode` circular-queue correctness bug (successor
  lookup now reads patched objects table).
  Documentation: `lookupServiceByCap` first-match semantics (M-LCS-2),
  `Notification.waitingThreads` LIFO semantics (M-MOD-6). Zero sorry, zero
  axiom. All 13 sub-tasks complete.

- **T6 (v0.20.5) — COMPLETE**: Architecture & Hardware Preparation. Closed 5
  MEDIUM and 1 HIGH finding. Changed `vspaceMapPage` default permissions from
  `default` to explicit `PagePermissions.readOnly` enforcing least-privilege
  (M-NEW-6). Changed `VSpaceMapArgs.perms` from raw `Nat` to typed
  `PagePermissions` with decode-time validation via `PagePermissions.ofNat?`
  rejecting values ≥ 32 (M-ARCH-1). Defined MMIO adapter operations
  (`mmioRead`/`mmioWrite`) with device-region validation and memory barrier
  modeling (`MemoryBarrier` inductive: DMB, DSB, ISB) for ARM64 (M-NEW-7,
  M-NEW-8). Wired information-flow-checked dispatch (`dispatchWithCapChecked`,
  `syscallEntryChecked`) — all 7 policy-gated operations use `securityFlowsTo`
  wrappers at runtime (M-IF-1). Defined `RegisterWriteInvariant` predicate for
  context-switch-aware adapter stub (H-3). Added targeted TLB flush operations
  (`tlbFlushByASID`, `tlbFlushByPage`, `tlbFlushAll`) with state frame proofs
  (M-ARCH-4). Implemented DTB parsing foundation with FDT header parser,
  `readBE32`, `parseFdtHeader`, `FdtHeader.isValid` (M-ARCH-2). Extended RPi5
  runtime contract with `mmioAccessAllowed` predicate. Documented cache
  coherency assumptions in spec (single-core, MMIO barriers, DMA out of scope).
  Zero sorry, zero axiom. All 13 sub-tasks complete.

- **T7 (v0.20.6) — COMPLETE**: Test Coverage & Build Infrastructure. Migrated
  all `BootstrapBuilder.build` calls to `buildChecked` in MainTraceHarness and
  OperationChainSuite (T7-A), ensuring runtime structural invariant validation.
  Added 7 post-mutation invariant checks to trace harness (24→31 total) covering
  vspace-unmap, register-write, lifecycle-retype, IPC-handshake, domain-switch,
  IPC-rendezvous, and untyped-double-retype (T7-B). Added 3 frozen IPC queue
  enqueue tests (FO-016/017/018) validating send/receive/call blocking and
  intrusive queue semantics (T7-D/F). Added deep CDT cascade test with 4-level
  derivation tree and mid-chain strict revoke (T7-E). Added handleYield
  empty-queue re-selection and IRQ handler dispatch tests (T7-K). Added boot
  sequence integration test using `bootFromPlatform` with invariant witness
  verification and determinism check (T7-L). Updated trace fixture for 31
  invariant checks (T7-J). Hardened pre-commit hook with `mktemp` replacing
  PID-based temp files (T7-G). Added SHA-256 verification for Lean toolchain
  downloads with architecture-aware hash selection (T7-H). Added Rust ABI test
  job to CI pipeline (T7-I). Zero sorry, zero axiom. All 12 sub-tasks complete.

- **T8 (v0.20.7) — COMPLETE**: Documentation & Closure. Synchronized all
  documentation surfaces: README.md metrics (v0.20.7, 61,538 LoC, 1,846
  theorems), SELE4N_SPEC.md (frozen IPC queue semantics §8.8, object
  well-formedness §8.9, checked dispatch/MMIO §8.10, buildChecked §8.11),
  DEVELOPMENT.md (WS-T portfolio complete), CLAIM_EVIDENCE_INDEX.md (WS-T
  T2–T7 claims), WORKSTREAM_HISTORY.md (T8 completion, closure report link),
  CHANGELOG.md (v0.20.7 release notes), GitBook chapters (version metrics,
  proof map, spec roadmap, project overview, usage value). Regenerated
  codebase_map.json (101 files, 1,846 theorems). Verified: zero sorry/axiom
  in production, 20 native_decide usages (all justified), website link manifest
  (93 paths present), all test tiers pass. Produced WS-T closure report. All
  14 sub-tasks complete.

### WS-S workstream (Pre-Benchmark Strengthening) — PORTFOLIO COMPLETE

WS-S is a completed workstream (v0.19.0–v0.19.6), addressing all findings from
dual comprehensive v0.18.7 audits (115+ findings). 7 phases (S1–S7), 83
sub-tasks. All 5 High, 29 Medium, and 19 Low findings resolved. See
[`AUDIT_v0.18.7_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.18.7_WORKSTREAM_PLAN.md).
Closure report: [`WS_S_CLOSURE_REPORT.md`](dev_history/audits/WS_S_CLOSURE_REPORT.md).

### WS-R workstream (Comprehensive Audit Remediation) — PORTFOLIO COMPLETE

WS-R is a completed workstream (v0.18.0–v0.18.7), addressing all 82 findings from the
comprehensive pre-release audit (`AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`).
8 phases (R1–R8), 111 sub-tasks. See
[`AUDIT_v0.17.14_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md).

- **R1 (v0.18.0) — COMPLETE**: Pre-release blockers. Fixed Rust `Cap::downgrade()`
  rights bypass (H-01), AccessRights/PagePerms silent truncation (R-M01, R-M02),
  SyscallResponse semantic overlap (R-M03), api* wrapper capability-target bypass
  (M-04), frozen context save/restore silent failures (M-10, M-11). All 14 api*
  wrappers deprecated with validation guards.
- **R2 (v0.18.1) — COMPLETE**: Capability & CDT hardening. Fixed `processRevokeNode`
  error swallowing (M-06) — revocation now propagates `cspaceDeleteSlot` errors
  instead of silently dropping them. Fixed `streamingRevokeBFS` fuel exhaustion
  (M-05) — returns `.error .resourceExhausted` instead of `.ok`. Added
  `resourceExhausted` to `KernelError`. Updated all preservation proofs for new
  `Except` return types. Added `isAncestor` decidable predicate for CDT cycle
  detection (M-08). Existing `removeNode_parentMapConsistent` proof covers CDT
  remove consistency (M-07). Added `processRevokeNode_lenient` deprecated variant
  for backward compatibility. Added revocation error propagation test cases.
- **R3 (v0.18.2) — COMPLETE**: IPC invariant completion. Fixed `notificationSignal`
  badge delivery gap (M-16) — woken thread now receives signaled badge via
  `storeTcbIpcStateAndMessage`; badge delivery verified by chain22 test.
  Internalized `ipcInvariantFull` preservation hypotheses (M-18) — notification
  operations and `endpointReply` now have self-contained preservation theorems
  with zero externalized hypotheses. Completed `notificationWaiterConsistent`
  preservation chain (M-19) — `notificationSignal_preserves_notificationWaiterConsistent`
  (wake/merge paths, uses `uniqueWaiters` Nodup),
  `frame_preserves_notificationWaiterConsistent` (general frame lemma),
  `endpointReply_preserves_notificationWaiterConsistent`, plus helper
  `storeTcbIpcStateAndMessage_preserves_notificationWaiterConsistent`.
  IpcMessage structural bounds (L-05) already addressed by existing `bounded`
  predicate. Removed `set_option linter.all false` from Structural.lean (L-08).
  Added `removeNode_childMapConsistent` proof for CDT childMap consistency.
  Fixed unused variable warning (`_hNoIncoming`). Zero warnings, zero sorry.
- **R4 (v0.18.3) — COMPLETE**: Lifecycle & Service Coherence. Fixed TCB cleanup
  gaps (M-12) — `cleanupTcbReferences` now removes TCB from endpoint queues and
  notification wait lists. Fixed endpoint retype service registration revocation
  (M-13) — retyping endpoint auto-revokes registered services. Added service
  registration authority check (M-14) — `registerService` requires Write right
  and endpoint type verification (L-09). Fixed service revocation dependency
  graph cleanup (M-15) — `revokeService` cleans dependency graph via
  `removeDependenciesOf`. Cross-subsystem invariant bundle (`crossSubsystemInvariant`)
  added to `proofLayerInvariantBundle`. Zero sorry/axiom.
- **R5 (v0.18.4)**: Information Flow Completion — Internalized IPC
  non-interference proofs (M-01), added `registerServiceChecked` to NI
  composition bundle (M-02, 32 total constructors), and replaced dummy-byte
  memory projection with content-aware projection (M-03). Six bridge theorems
  internalized in-place: `endpointSendDualChecked_NI`,
  `endpointReceiveDualChecked_NI`, `endpointCall_preserves_lowEquivalent`,
  `endpointReplyRecv_preserves_lowEquivalent`, `cspaceCopyChecked_NI`,
  `cspaceMoveChecked_NI` — all now use one-sided `hProjection` parameter
  instead of two-state NI hypothesis. Service registration
  NI proved unconditionally (`registerService_preserves_projection` — service
  registry changes are invisible to projection because `projectServicePresence`
  is gated by `serviceObservable`, not registry contents). Content-aware
  `projectMemory` returns actual `st.machine.memory` bytes instead of `some 0`.
  All existing NI proofs updated for content-aware projection (12 files, ~30
  proof sites). Zero sorry/axiom.
- **R6 (v0.18.5) — COMPLETE**: Model & Frozen State Correctness. Fixed frozen
  invariant existential staleness (M-09) — direct frozen invariant predicate
  `apiInvariantBundle_frozenDirect` that survives `FrozenMap.set` mutations.
  Deprecated `Badge.ofNat` in favor of word-bounded `Badge.ofNatMasked` (L-01).
  Fixed `BEq RegisterFile` partial comparison with named `registerFileGPRCount`
  constant (L-04). Added `schedulerPriorityMatch` to scheduler invariant bundle
  (L-12). Zero sorry/axiom.
- **R7 (v0.18.6) — COMPLETE**: Architecture & Hardware Preparation. Integrated
  `TlbState` into `SystemState` and added `tlbConsistent` to the
  `proofLayerInvariantBundle` (M-17). Added TLB-flushing VSpace wrappers
  (`vspaceMapPageWithFlush`, `vspaceUnmapPageWithFlush`) with preservation
  proofs. Added `RegName.isValid` ARM64 bounds predicate and `arm64GPRCount`
  constant (L-02). Added `isWord64` predicate and `valid` checks for
  `RegValue`, `VAddr`, `PAddr` with `machineWordBounded` machine-state
  invariant (L-03). Added `faultHandler` and `boundNotification` fields to TCB
  for seL4 fidelity (L-06). Replaced raw `Nat` in
  `LifecycleRetypeArgs.newType` with typed `KernelObjectType` enum,
  added `KernelObjectType.toNat`/`ofNat?` conversions with round-trip proofs,
  and introduced `objectOfKernelType` (L-10). Zero sorry/axiom.
- **R8 (v0.18.7) — COMPLETE**: Infrastructure & CI Hardening. Pinned elan binary
  download to versioned URL (`v4.2.1`) with SHA-256 hash verification for x86_64
  and aarch64; SHA mismatch reports diagnostic warning (I-M01). Converted
  `codebase_map_sync.yml` from auto-push to PR-based workflow — changes go through
  review before reaching main (I-M02). Made Rust test skip explicit with `::warning::`
  CI annotation and direct cargo exit code propagation via temp-file capture (I-M03).
  Added execution of 4 compiled but never-run test suites (`radix_tree_suite`,
  `frozen_state_suite`, `freeze_proof_suite`, `frozen_ops_suite`) to Tier 2 negative
  tests (I-M04). Encapsulated all 14 Rust newtype identifier inner fields from `pub`
  to `pub(crate)` with `.raw()` accessors, plus `AccessRights` and `PagePerms` (L-11).
  All 99 Rust tests pass (44 abi + 22 types + 8 sys + 25 conformance). Zero sorry/axiom.

### WS-S workstream (Pre-Benchmark Strengthening) — PORTFOLIO COMPLETE (v0.19.0–v0.19.6)

WS-S is a **completed** workstream (v0.19.0–v0.19.6), addressing all findings
from two comprehensive v0.18.7 audits: `AUDIT_COMPREHENSIVE_v0.18.7_PRE_BENCHMARK.md`
(50 findings) and `AUDIT_COMPREHENSIVE_v0.18.7_KERNEL_RUST.md` (65+ findings).
7 phases (S1–S7), 83 sub-tasks (including 1 stretch goal deferred to WS-T).
All 5 High, 29 Medium, and 19 Low findings resolved. See
[`AUDIT_v0.18.7_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.18.7_WORKSTREAM_PLAN.md).
Closure report: [`WS_S_CLOSURE_REPORT.md`](dev_history/audits/WS_S_CLOSURE_REPORT.md).

- **S1 (v0.19.0) — COMPLETE**: Security Boundary & Rust Type Safety. Removed
  deprecated `Badge.ofNat` (U-H1). Converted `MemoryRegion.wellFormed` from Bool
  to Prop (U-H2). Documented `ThreadId.toObjId` trust boundary (U-H3). Converted
  `Cap::restrict()` and `Cap::to_read_only()` from panic to `Result` (U-M01).
  Fixed `Restricted::RIGHTS` semantic bug (U-M02). Added `AccessRightSet.valid`
  predicate (U-L05). Migrated `isPowerOfTwo` proofs from `native_decide` to
  `decide` (U-M30). Added `MonadStateOf`/`MonadExceptOf` for `KernelM` (U-M16).
  Added `#![deny(unsafe_code)]` to `sele4n-abi` (U-L09). Zero sorry/axiom.
- **S2 (v0.19.1) — COMPLETE**: Test Hardening. Replaced 101 `reprStr` occurrences
  with `toString` (S2-A/B/C, U-H4). Determinism checks converted to structural `==`
  via `BEq Except` instance. Added `buildChecked` and migrated primary test states
  (S2-F, U-L11). Added 11 error-path tests: full-CNode copy, deep-CDT revoke,
  region exhaustion, rights attenuation, device restriction, child ID collision
  (S2-G/H, U-L12). Created `Testing/Helpers.lean` with library import via
  `MainTraceHarness` for build reachability (S2-I, U-L13). Migrated deprecated
  `api*` wrappers (S2-J, U-M05). Zero sorry/axiom.
- **S3 (v0.19.2) — COMPLETE**: Proof Surface Closure (14 sub-tasks including
  1 stretch goal deferred). CDT maps consistency invariant with state-level
  `cdtMapsConsistent` predicate, extended capability bundle
  (`capabilityInvariantBundleFull`), transfer theorems (`cdtMapsConsistent_of_cdt_eq`,
  `_of_storeObject`, `_of_detachSlotFromCdt`, `_of_storeCapabilityRef`), and
  **5 operation preservation theorems** (`cspaceMint_preserves_cdtMapsConsistent`,
  `cspaceDeleteSlot_preserves_`, `cspaceCopy_preserves_`, `cspaceMove_preserves_`,
  `cspaceRevoke_preserves_`) (S3-A/B/C/D). CDT `addEdge_preserves_cdtMapsConsistent`
  composite theorem (S3-B). Private `removeEdge` with `removeEdge_surviving_child_ne`
  helper, `removeEdge_preserves_cdtMapsConsistent`, public `revokeDerivationEdge`
  wrapper, and production `severDerivationEdge` in Operations (S3-C).
  `scheduleDomain` full-bundle
  preservation composed from `switchDomain` + `schedule` (S3-E).
  `remove_preserves_wellFormed` for RunQueue with three private helper theorems
  (S3-F). `schedule_preserves_runQueueWellFormed` using dequeue path (S3-G).
  SecurityLabel lattice antisymmetry + `Decidable` instance + compile-time
  witness (S3-H). Bridge signature witness for service policy (S3-I).
  Parameterized `crossSubsystemInvariant` via list-folded composition (S3-J).
  RobinHood load factor bound, resize theorem, and `insert_fails_at_capacity`
  alias (S3-K). Frozen ops exhaustiveness check with `frozenOpCoverage` and
  count verification (S3-L). Semi-automated dependency graph with subsystem
  module registry, BFS fuel bounds, and 6-module cross-reference (S3-N).
  Stretch goal S3-M (NI trace indexing) deferred to WS-T. Zero sorry/axiom.
- **S4 (v0.19.3) — COMPLETE**: Model Fidelity & Type Safety (13 sub-tasks).
  **S4-A** (U-M04): `objectIndexBounded` advisory predicate with RPi5 growth
  analysis; spec section 8 added. **S4-B** (U-M12): Capacity enforcement in
  `retypeFromUntyped` — returns `objectStoreCapacityExceeded` at `maxObjects`
  (65536); `objectCount_le_maxObjects` invariant. **S4-C** (U-L02): `resolveSlot`
  masks CPtr to 64 bits before guard extraction; `resolveSlot_mask_idempotent`
  proof. **S4-D** (U-L04): Changed `IpcMessage.registers` from `Array Nat` to
  `Array RegValue`; updated `extractMessageRegisters`, all construction sites,
  all test files, and all proof references. **S4-E** (U-M15): Added
  `wordAligned`/`pageAligned` predicates, `alignedRead`/`alignedWrite` advisory
  predicates, alignment theorems, and spec documentation of the memory alignment
  model gap. **S4-F** (U-L01): Evaluated `RegisterFile.gpr` Array migration —
  rejected due to proof complexity; documented design rationale. **S4-G** (U-L06):
  Evaluated `Notification.waitingThreads` intrusive queue migration — rejected
  due to low cardinality; documented bounds analysis. **S4-H** (U-L07):
  Documented `UntypedObject.allocate` prepend convention. **S4-I** (U-L08):
  Simplified `SyscallId.toNat_ofNat` proof with collapsed match arms; documented
  tactic limitation. **S4-J** (U-M27): Audited all `objects` iteration sites;
  documented order-independence. **S4-K** (U-M17): `decodeCapPtr` now returns
  `invalidCapPtr` for out-of-range values; updated roundtrip proofs. **S4-L**
  (U-M23): Documented `cspaceRevoke`/`cspaceRevokeCdt` O(n)/O(maxObjects)
  complexity. **S4-M** (U-M24): Documented `endpointCall` timeout absence
  matching seL4 semantics. Zero sorry/axiom.
- **S5 (v0.19.4) — COMPLETE**: API Cleanup, Platform Hardening & Lifecycle Fidelity
  (10 sub-tasks). **S5-A** (U-M05b): Removed 14 deprecated `api*` wrappers from
  `API.lean`; production path: `syscallEntry` → `dispatchSyscall` → `syscallInvoke`
  → `dispatchWithCap`. **S5-B**: Audited invariant files — zero references to
  removed wrappers. **S5-D** (U-M18): Created `SimRestrictive` platform variant
  with substantive contracts (`simRuntimeContractSubstantive`): timer monotonicity,
  256 MiB RAM memory bound, register writes denied; `SimRestrictivePlatform`
  binding in `Platform/Sim/Contract.lean`; substantive proof hooks in
  `Platform/Sim/ProofHooks.lean`. **S5-E**: Added `SimRestrictive` build check to
  `test_smoke.sh`. **S5-F** (U-M19): BCM2712 address validation checklist in
  `Platform/RPi5/Board.lean`; pre-hardware-binding gate in `DEVELOPMENT.md`.
  **S5-G/S5-H** (U-M20/U-M21): Page-alignment check in `retypeFromUntyped` for
  VSpace roots and CNodes — `requiresPageAlignment`, `allocationBasePageAligned`,
  `allocationMisaligned` error variant; all lifecycle invariant preservation proofs
  updated. **S5-I** (U-M22): EDF tie-breaking FIFO semantics documented at
  `chooseThread` (`Selection.lean`). **S5-J** (U-M23b): Complexity documentation
  for `TlbState` operations (O(n)), `RunQueue.remove` (O(k+n)),
  `RunQueue.rotateHead` (O(k+n)). Zero sorry/axiom.
- **S6 (v0.19.5) — COMPLETE**: Hardware Preparation (7 sub-tasks). **S6-A**
  (U-M18): Migrated API dispatch to `WithFlush` VSpace variants
  (`vspaceMapPageCheckedWithFlush`, `vspaceUnmapPageWithFlush`); trace harness
  updated. **S6-B** (U-M18): Documented unflushed `vspaceMapPage`/`vspaceUnmapPage`
  as internal proof decomposition helpers with clear warnings against direct use.
  **S6-C** (U-M19): Added memory scrubbing (`zeroMemoryRange`, `scrubObjectMemory`)
  to `lifecycleRetypeWithCleanup`; `Machine.lean` gets `zeroMemoryRange`/`memoryZeroed`
  primitives. **S6-D** (U-M19): Proved `scrubObjectMemory` preserves lifecycle
  invariants (trivially — only modifies `machine.memory`). **S6-E** (U-M19):
  Proved `scrubObjectMemory` preserves NI (`lowEquivalent`) for non-observable
  targets. **S6-F** (U-M20): Created `Platform/DeviceTree.lean` abstraction with
  `DeviceTree` structure; RPi5 `Board.lean` constructs `rpi5DeviceTree`. **S6-G**:
  Validated all BCM2712 address constants against datasheet; comprehensive
  validation table added to `Board.lean`. Zero sorry/axiom.
- **S7 (v0.19.6) — COMPLETE**: Documentation & Polish (14 sub-tasks). **S7-A**:
  Synchronized `README.md` metrics from `codebase_map.json` — v0.19.6, 100
  production files, 57,506 LoC, 1,756 proved declarations. **S7-B**: Updated
  `SELE4N_SPEC.md` with all S1–S6 spec changes. **S7-C**: Updated
  `DEVELOPMENT.md` with WS-S testing practices. **S7-D**: Updated
  `CLAIM_EVIDENCE_INDEX.md` with WS-S claims. **S7-E**: Updated
  `WORKSTREAM_HISTORY.md` with WS-S completion. **S7-F**: Regenerated
  `codebase_map.json`. **S7-G**: Updated GitBook chapters. **S7-H**: Verified
  website link manifest. **S7-M**: Updated `CHANGELOG.md`. **S7-N**: Produced
  WS-S closure report. Version bumped to 0.19.6. Zero sorry/axiom.

### WS-Q1 workstream (Service Interface Simplification)

WS-Q1 is a **completed** workstream (v0.17.7), the first phase of WS-Q (Kernel
State Architecture). It simplifies the service subsystem from a lifecycle-based
model (`serviceStart`/`serviceStop`/`serviceRestart` with `ServiceStatus` and
`ServiceConfig`) to a stateless registry model where services are registered
entries with identity, dependencies, and isolation edges — no running/stopped
state. Key changes:

- **Removed**: `ServiceStatus` enum, `ServiceConfig` structure, `ServicePolicy`
  type, `serviceStart`/`serviceStop`/`serviceRestart` transitions,
  `serviceRestartChecked` enforcement wrapper, associated NI proofs
- **Simplified**: `ServiceGraphEntry.status` field removed; `SyscallId`
  renumbered (14 valid IDs, 0..13); `projectServicePresence` replaces
  `projectServiceStatus` (returns `Bool` instead of `Option ServiceStatus`)
- **Added (WS-Q1)**: `registerServiceChecked` policy-gated enforcement wrapper,
  `ServiceRegisterArgs`/`ServiceRevokeArgs`/`ServiceQueryArgs` decode structures
  in `SyscallArgDecode.lean`, `dispatchWithCap` service syscalls use decoded MR
  arguments, SRG-001 through SRG-010 test scenarios
- **Preserved**: `serviceRegisterDependency`, `serviceHasPathTo`,
  `hasIsolationEdge`, `lookupService`, `storeServiceEntry` — all graph
  invariants and acyclicity proofs intact
- **Test migration**: All trace harnesses, negative-state tests, information
  flow tests, operation chain tests updated; fixture files synchronized
- **Proof surface**: Zero sorry, all invariant preservation theorems intact,
  enforcement boundary updated: 3 policy-gated in base, 7 in extended (WS-Q1: `registerServiceChecked` added)

See [`MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md`](dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md)
for the full WS-Q plan (phases Q1–Q9).

### WS-Q2 workstream (Universal RHTable Migration)

WS-Q2 is a **completed** workstream (v0.17.8), the second phase of WS-Q (Kernel
State Architecture). It replaces every `Std.HashMap` and `Std.HashSet` in kernel
state with the formally verified `RHTable`/`RHSet` (Robin Hood hash table from
WS-N), establishing the builder-phase representation for the two-phase state
architecture. Scope: 16 map fields + 2 set fields across 6 structures, 30+ files
modified, 10 atomic subphases. Key changes:

- **Q2-A**: Prelude lemma foundation — `RHTable` equivalents for all 28
  `Std.HashMap` utility lemmas used by downstream proofs (re-exported from
  Bridge.lean with `[simp]` attributes)
- **Q2-B**: `RHSet` type definition — newtype wrapper around `RHTable κ Unit`
  with 14 bridge lemmas (`contains`, `insert`, `erase`, `membership`, `invExt`
  preservation), `Inhabited`/`BEq`/`Membership`/`EmptyCollection` instances,
  `ofList` constructor
- **Q2-C**: Core SystemState maps + object store (atomic group A) — `objects`,
  `objectIndexSet`, `lifecycle.objectTypes`, `lifecycle.capabilityRefs`,
  `asidTable` migrated to `RHTable`/`RHSet`; `storeObject` rewritten;
  `invExt` threading through all state-modifying operations
- **Q2-D**: Per-object maps — `VSpaceRoot.mappings` migrated to `RHTable`
- **Q2-E**: IRQ handler map — `irqHandlers` migrated to `RHTable`
- **Q2-F**: CDT maps (atomic group B) — `cdt.childMap`, `cdt.parentMap`,
  `cdtSlotNode`, `cdtNodeSlot` migrated to `RHTable`
- **Q2-G**: RunQueue internals (atomic group C) — `byPriority`,
  `threadPriority` migrated to `RHTable`; `membership` migrated to `RHSet`
- **Q2-H**: Service maps — `services`, `interfaceRegistry`, `serviceRegistry`
  migrated to `RHTable`
- **Q2-I**: Elimination verification — zero state-persistent `Std.HashMap`/
  `Std.HashSet` remaining (algorithm-local uses permitted in Acyclicity.lean,
  Projection.lean, Service/Operations.lean)
- **Q2-J**: `allTablesInvExt` predicate — global well-formedness condition
  asserting all 16 RHTable/RHSet fields satisfy `invExt`; proven for default
  state via `default_allTablesInvExt`
- **invExt threading**: Every theorem calling a state-modifying bridge lemma
  (`storeObject_*`, `storeTcbIpcState_*`, `endpointQueuePopHead_*`, etc.)
  gained an `hObjInv : st.objects.invExt` parameter, cascading across
  EndpointPreservation (~25 theorems), NotificationPreservation (~67 fixes),
  CallReplyRecv (~72 fixes), Structural (~103 fixes), Capability Preservation,
  Authority, Defs, Policy, Acyclicity, Architecture Invariant, and all
  InformationFlow invariant files
- **Proof patterns**: `HashMap_getElem?_empty` → `RHTable_get?_empty 16 (by omega)`;
  `HashMap_getElem?_insert` → `simp only [RHTable_getElem?_eq_get?]; rw [RHTable_getElem?_insert]`;
  `.fold` → `.toList.foldl` (universe constraint workaround)
- **Test migration**: NegativeStateSuite, TraceSequenceProbe updated to use
  `RHTable`/`RHSet` constructors; all test suites pass
- **Proof surface**: Zero sorry, 1,459 proved declarations, 168 build jobs

### WS-Q3 workstream (IntermediateState Formalization)

WS-Q3 is a **completed** workstream (v0.17.9), the third phase of WS-Q (Kernel
State Architecture). It defines the `IntermediateState` type — a wrapper around
`SystemState` that carries four machine-checked invariant witnesses — and
implements builder operations that construct valid intermediate states during
boot. Key changes:

- **Q3-A**: `IntermediateState` type in `SeLe4n/Model/IntermediateState.lean` —
  bundles `SystemState` with `allTablesInvExt`, `perObjectSlotsInvariant`,
  `perObjectMappingsInvariant`, `lifecycleMetadataConsistent` witnesses.
  `mkEmptyIntermediateState` constructor with `mkEmptyIntermediateState_valid` proof.
  Named predicates `perObjectSlotsInvariant`, `perObjectMappingsInvariant` with
  default-state theorems.
- **Q3-B**: 7 builder operations in `SeLe4n/Model/Builder.lean`:
  `registerIrq`, `registerService`, `addServiceGraph`, `createObject`,
  `deleteObject`, `insertCap`, `mapPage`. Each carries forward all four
  invariant witnesses through machine-checked proofs. `insertCap` and `mapPage`
  delegate to `createObject` with per-object proof obligations.
  Helper theorem `insert_capacity_ge4` for capacity preservation.
- **Q3-C**: Boot sequence in `SeLe4n/Platform/Boot.lean` — `PlatformConfig`
  type with `IrqEntry` and `ObjectEntry`, `bootFromPlatform` function that
  folds IRQ entries and initial objects through builder operations.
  Master validity theorem `bootFromPlatform_valid` proves the booted state
  satisfies all four IntermediateState invariant witnesses.
  `bootFromPlatform_deterministic` and `bootFromPlatform_empty` properties.
- **Proof surface**: Zero sorry, all three modules compile independently via
  `lake build SeLe4n.Model.IntermediateState`, `lake build SeLe4n.Model.Builder`,
  `lake build SeLe4n.Platform.Boot`. All test tiers pass.

### WS-Q4 workstream (CNode Radix Tree — Verified)

WS-Q4 is a **completed** workstream (v0.17.10), the fourth phase of WS-Q (Kernel
State Architecture). It implements a verified flat radix tree (`CNodeRadix`) for
CNode capability slot lookups, matching seLe4n's existing bit-sliced addressing
semantics (guard match + radix extraction). The radix tree provides O(1) lookup
with zero hashing — pure bitwise index computation — and will serve as the
frozen-phase CNode representation in Q5. Key changes:

- **Q4-A**: Core types in `SeLe4n/Kernel/RadixTree/Core.lean` — `extractBits`
  bit extraction helper with `extractBits_lt` bound proof, `CNodeRadix` structure
  with `guardWidth`, `guardValue`, `radixWidth`, fixed-size `Array (Option Capability)`
  with `hSlotSize` size proof.
- **Q4-B**: Operations — `CNodeRadix.empty` (O(2^radixWidth) initialization),
  `lookup` (O(1) zero-hash via `extractBits` + direct array index), `insert` (O(1)
  array set), `erase` (O(1) set to `none`), `fold` (O(2^radixWidth) traversal),
  `toList`, `size`, `fanout`.
- **Q4-C**: 24 correctness proofs in `SeLe4n/Kernel/RadixTree/Invariant.lean` —
  lookup roundtrips (`lookup_empty`, `lookup_insert_self`, `lookup_insert_ne`,
  `lookup_erase_self`, `lookup_erase_ne`, `insert_idempotent`), WF preservation
  (`wf_of_mk`, `empty_wf`, `insert_wf`, `erase_wf`), `insert_erase_cancel`,
  parameter preservation (6 theorems for guard/radix width invariance across
  insert/erase), size bounds (`size_empty`, `fanout_eq_slots_size`,
  `size_insert_le`, `size_erase_le`), enumeration (`toList_complete`,
  `toList_noDup`, `fold_visits_all`).
- **Q4-D**: Builder equivalence bridge in `SeLe4n/Kernel/RadixTree/Bridge.lean` —
  `CNodeConfig` type, `buildCNodeRadix` function (RHTable → CNodeRadix via fold),
  `buildCNodeRadix_guardWidth/guardValue/radixWidth` preservation theorems,
  `buildCNodeRadix_wf` well-formedness, `buildCNodeRadix_deterministic`,
  `buildCNodeRadix_empty_lookup` (empty RHTable yields none),
  `UniqueRadixIndices` predicate (Q6-B precondition),
  `CNodeConfig.ofCNode` and `CNodeRadix.ofCNode` convenience constructors,
  `freezeCNodeSlots` with 4 preservation theorems (Q5 integration point).
- **Q4-T**: 12-scenario test suite in `tests/RadixTreeSuite.lean` (43 checks) —
  core operation tests (RT-001 to RT-008) and bridge tests (RT-009 to RT-012).
- **Re-export hub**: `SeLe4n/Kernel/RadixTree.lean` — imports Core, Invariant,
  Bridge for backward-compatible single-import usage.
- **Proof surface**: Zero admitted proofs, all 4 modules compile independently via
  `lake build SeLe4n.Kernel.RadixTree.Core`, etc. All test tiers pass.

See [`MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md`](dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md)
for the full WS-Q plan (phases Q1–Q9).

### WS-Q5 workstream (FrozenSystemState + Freeze)

WS-Q5 is a **completed** workstream (v0.17.11), the fifth phase of WS-Q (Kernel
State Architecture). It defines the frozen execution-phase state representation
and implements the `freeze` function that transforms an `IntermediateState`
(builder phase) into a `FrozenSystemState` (execution phase). Key changes:

- **Q5-A**: `FrozenMap` and `FrozenSet` types in `SeLe4n/Model/FrozenState.lean`
  — dense `Array ν` value store + `RHTable κ Nat` index mapping. Runtime
  bounds-checked `get?` (safe-by-construction), `set` (update-only), `contains`,
  `fold` operations. `FrozenSet κ` defined as `FrozenMap κ Unit`.
- **Q5-B**: Per-object frozen types — `FrozenCNode` (uses `CNodeRadix` from Q4
  for O(1) zero-hash slot lookup), `FrozenVSpaceRoot` (uses `FrozenMap` for
  page mappings), `FrozenKernelObject` inductive (6 variants), `FrozenSchedulerState`,
  `FrozenSystemState` (19 fields mirroring `SystemState`).
- **Q5-C**: Freeze functions — `freezeMap` (RHTable → FrozenMap via fold),
  `freezeCNode`, `freezeVSpaceRoot`, `freezeObject` (per-object with CNode→CNodeRadix
  via Q4 bridge), `freezeScheduler`, `freeze` (IntermediateState → FrozenSystemState).
- **Q5-D**: Capacity planning — `minObjectSize` constant, `objectCapacity`
  (current objects + potential from untyped memory).
- **Q5-T**: 15-scenario test suite in `tests/FrozenStateSuite.lean` (49 checks):
  FrozenMap core (FS-001 to FS-007), FrozenKernelObject (FS-008 to FS-010),
  freeze integration (FS-011 to FS-015) including objectIndexSet, scheduler
  freeze, FrozenMap.set size preservation, and data size round-trip.
- **Proof surface**: 20+ theorems including `freeze_deterministic`,
  `freeze_preserves_machine`, `freeze_preserves_objectIndexSet`,
  `freezeMap_empty`, `freezeMap_data_size`, `freezeObject_preserves_type`,
  `freezeObject_tcb_passthrough`, `frozenMap_set_preserves_size`,
  `objectCapacity_ge_size`. Zero admitted proofs, all modules compile independently.

See [`MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md`](dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md)
for the full WS-Q plan (phases Q1–Q9).

### WS-Q6 workstream (Freeze Correctness Proofs)

WS-Q6 is a **completed** workstream (v0.17.12), the sixth phase of WS-Q (Kernel
State Architecture). It provides machine-checked proofs that the `freeze`
function preserves lookup semantics, structural properties, and kernel
invariants across the builder→execution phase transition. Key changes:

- **Q6-A**: Core `freezeMap` lookup equivalence — `freezeMap_get?_eq` proves
  `rt.get? k = (freezeMap rt).get? k` for any key `k`. 13 per-field theorems
  (`lookup_freeze_objects`, `lookup_freeze_objectIndexSet`,
  `lookup_freeze_irqHandlers`, etc.) instantiate this
  for every `RHTable` field in `SystemState`. Helper theorems connect
  `RHTable.toList` membership to `get?` results.
- **Q6-B**: CNode radix lookup equivalence — `lookup_freeze_cnode_slots_some`
  and `lookup_freeze_cnode_slots_none` prove that `cn.slots.get? slot` agrees
  with `(freezeCNodeSlots cn).lookup slot` in both directions. Three generic
  helper theorems (`foldl_generic_preserves_lookup`, `foldl_generic_preserves_none`,
  `foldl_generic_establishes_lookup`) work around Lean 4 match compilation
  identity differences by parameterizing over the fold step function.
- **Q6-C**: Structural properties — `freeze_deterministic'` (idempotent output),
  `freezeMap_preserves_size` (data array size = toList length),
  `freezeMap_preserves_membership` (isSome agreement),
  `freezeMap_no_duplicates` (pairwise distinct keys in toList),
  `freezeMap_total_coverage` (every source key has valid data index).
- **Q6-D**: Invariant transfer — `apiInvariantBundle_frozen` (existential
  formulation), `freeze_preserves_invariants` (keystone theorem: builder-phase
  `apiInvariantBundle` → frozen `apiInvariantBundle_frozen`),
  `frozen_lookup_transfer` (enabling lemma for per-invariant transfer proofs).
- **Q6-T**: 22-scenario test suite in `tests/FreezeProofSuite.lean` (60 checks):
  freezeMap lookup (FP-001 to FP-005), per-field lookup (FP-006 to FP-009),
  CNode radix (FP-010 to FP-013), structural properties (FP-014 to FP-018),
  invariant transfer (FP-019 to FP-021).
- **Proof surface**: 30 theorems/definitions in `SeLe4n/Model/FreezeProofs.lean`,
  zero sorry/axiom, all modules compile independently.

### WS-Q7 workstream (Frozen Kernel Operations)

WS-Q7 is a **completed** workstream (v0.17.13), the seventh phase of WS-Q (Kernel
State Architecture). It delivers the execution-phase kernel operations that run
on top of the frozen (immutable key-set) state produced by WS-Q5/Q6. Key changes:

- **Q7-A**: `FrozenKernel` monad (`KernelM FrozenSystemState KernelError`) with
  lookup/store primitives for all 5 object types (TCB, Endpoint, Notification,
  CNode, VSpaceRoot). Scheduler context-switch helpers.
- **Q7-B/C**: 14 per-subsystem frozen operations across 5 subsystems: Scheduler
  (`frozenSchedule`, `frozenHandleYield`, `frozenTimerTick`), IPC
  (`frozenNotificationSignal`, `frozenNotificationWait`, `frozenEndpointSend`,
  `frozenEndpointReceive`, `frozenEndpointCall`, `frozenEndpointReply`),
  Capability (`frozenCspaceLookup`, `frozenCspaceMint`, `frozenCspaceDelete`),
  VSpace (`frozenVspaceLookup`), Service (`frozenLookupServiceByCap`).
- **Q7-D**: FrozenMap set/get? commutativity proofs and structural lemmas.
- **Q7-E**: 18 `frozenStoreObject` frame/preservation theorems.
- **Q7-T**: 15-scenario test suite in `tests/FrozenOpsSuite.lean` covering
  TPH-005 through TPH-014.
- **Proof surface**: Zero sorry/axiom, all modules compile independently.

### WS-Q8 workstream (Rust Syscall Wrappers)

WS-Q8 is a **completed** workstream (v0.17.13), absorbing WS-O (Syscall Rust
Wrappers). It delivers `libsele4n`, a `no_std` Rust userspace library with safe
syscall wrappers for all 14 seLe4n syscalls. Key changes:

- **Q8-A**: `sele4n-types` crate — 14 newtype identifiers (`ObjId`, `ThreadId`,
  `CPtr`, `Slot`, etc.), 43-variant `KernelError` enum (AA1: +IpcTimeout), 5-variant `AccessRight`
  enum + `AccessRights` bitmask, 20-variant `SyscallId` enum (AA1: +SchedContext×3). Zero `unsafe`,
  `#![no_std]`, zero external dependencies.
- **Q8-B**: `sele4n-abi` crate — `MessageInfo` bitfield encode/decode (seL4
  convention: 7-bit length, 2-bit extraCaps, label), `SyscallRequest`/
  `SyscallResponse` register structures, ARM64 `svc #0` inline asm (the single
  `unsafe` block), per-syscall argument structures (CSpace×4, Lifecycle×1,
  VSpace×2, Service×3), `TypeTag` enum (6 variants), `PagePerms` bitmask with
  W^X enforcement.
- **Q8-C**: `sele4n-sys` crate — safe high-level wrappers: IPC (endpoint
  send/receive/call/reply, notification signal/wait), CSpace (mint/copy/move/
  delete), Lifecycle (retype + convenience constructors), VSpace (map with W^X
  pre-check, unmap), Service (register/revoke/query). Phantom-typed capability
  handles (`Cap<Obj, Rts>`) with sealed traits, rights downgrading.
- **Q8-D**: Conformance tests (RUST-XVAL-001 through RUST-XVAL-019) validating
  register-by-register ABI encoding for all 14 syscalls, notification signal/wait,
  and IPC buffer overflow. `test_rust.sh` CI script integrated into
  `test_smoke.sh` (Tier 2). Lean trace harness extended with XVAL-001 through
  XVAL-004 cross-validation vectors.
- **Proof surface**: Lean side unchanged (zero new sorry/axiom). Rust side:
  64 unit tests + 25 conformance tests across 3 crates.

### WS-Q9 workstream (Integration Testing + Documentation)

WS-Q9 is a **completed** workstream (v0.17.14), the final phase of WS-Q (Kernel
State Architecture). It delivers comprehensive integration testing for the
two-phase builder→freeze→execution pipeline and synchronizes all documentation.
Key changes:

- **Q9-A**: `TwoPhaseArchSuite.lean` — 14 integration tests (41 checks) covering
  TPH-001 (builder pipeline), TPH-003 (freeze populated + lookup equivalence),
  TPH-005 (frozen IPC send/receive/call), TPH-006 (frozen scheduler tick with
  active thread + preemption), TPH-010 (commutativity: builder→freeze =
  freeze→frozen op), TPH-012 (pre-allocated slot retype in frozen state),
  TPH-014 (RunQueue frozen operations: schedule/yield/no-eligible).
- **Q9-B**: Rust conformance tests RUST-XVAL-001 through RUST-XVAL-019 verified
  complete (25 tests in `rust/sele4n-abi/tests/conformance.rs`).
- **Q9-C**: Service interface tests SRG-001 through SRG-010 verified complete
  in `MainTraceHarness.lean`.
- **Q9-D**: Full documentation sync across 15+ files: WORKSTREAM_HISTORY.md,
  SELE4N_SPEC.md, DEVELOPMENT.md, CLAIM_EVIDENCE_INDEX.md, README.md, CLAUDE.md,
  GitBook chapters (architecture, design, spec, proofs), codebase_map.json.
- **Test infrastructure**: New `two_phase_arch_suite` executable registered in
  `lakefile.toml`, integrated into `test_tier2_negative.sh`, scenario registry
  updated with TPH-* entries, fixture file created.
- **Proof surface**: Zero sorry/axiom, all modules compile independently.

See [`MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md`](dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md)
for the full WS-Q plan (phases Q1–Q9). **WS-Q portfolio is now COMPLETE.**

### WS-N workstream (Robin Hood hashing verified implementation)

WS-N is a **completed** workstream (v0.17.0–v0.17.5), created to close the trust gap
between seLe4n's machine-checked proof surface and the unverified `Std.HashMap`
library type used across 14 production source files (114 occurrences). The
workstream delivers a formally verified Robin Hood hash table implementation
with fuel-bounded recursion (no `partial`), bounds-checked array access (no
`get!`/`set!`), and machine-checked invariant proofs.

WS-N phases N1–N3 were previously attempted and **reverted** (PRs #453–#455)
due to `partial` functions, unsafe array access, missing refinement proofs, and
incorrect cluster-ordering invariants. This re-plan addresses every failure mode
with a single-representation architecture, `Nat`-based bounded recursion, and
per-cluster modular-arithmetic ordering.

| ID | Focus | Priority |
|----|-------|----------|
| **WS-N1** | Core types + operations: `RHEntry`, `RHTable`, `empty`, `insert`, `get?`, `erase`, `fold`, `resize`; fuel-bounded loops, bounds-checked access; `empty_wf` proof | CRITICAL — **COMPLETED** (v0.17.1) |
| **WS-N2** | Invariant proofs: `wf`/`distCorrect`/`noDupKeys`/`probeChainDominant` preservation through insert/erase/resize; lookup soundness + completeness (`get_after_insert_eq`, `get_after_insert_ne`, `get_after_erase_eq`). All 6 TPI-D items completed (D1–D6), ~4,655 LoC, zero sorry | HIGH — **COMPLETED** (v0.17.2) |
| **WS-N3** | Kernel API bridge: `Inhabited`/`BEq` instances, 12 bridge lemmas (`getElem?_*`, `size_*`, `mem_iff_isSome_getElem?`, `fold_eq_slots_foldl`, `size_filter_le_*`), `filter` + `ofList` support, `get_after_erase_ne` proof. ~307 LoC Bridge.lean + ~247 LoC Lookup.lean additions, zero sorry | MEDIUM — **COMPLETED** (v0.17.3) |
| **WS-N4** | Kernel integration (first site): replaced `CNode.slots : Std.HashMap Slot Capability` with `RHTable Slot Capability`; updated CNode operations, ~25 CNode/capability theorems, ~15 invariant proofs across Capability/InformationFlow subsystems, test fixtures; `slotsUnique` repurposed as substantive `invExt` invariant; 3 new bridge lemmas (`filter_fold_absent_by_pred`, `filter_get_pred`, `filter_filter_getElem?`); 20+ files modified | MEDIUM — **COMPLETED** (v0.17.4) |
| **WS-N5** | Test coverage + documentation: `RobinHoodSuite.lean` with 12 standalone tests (RH-001–RH-012: empty table, insert/get, erase, overwrite, multi-key, collision, Robin Hood swap, backward-shift, resize, post-resize, large-scale 200-entry stress, fold/toList) + 6 CNode integration tests (RH-INT-001–RH-INT-006: lookup/insert/remove, revokeTargetLocal, findFirstEmptySlot, slotCountBounded, CSpace resolution, BEq). Full doc sync across 8 canonical files + 4 GitBook chapters. ~300 LoC tests, zero sorry | LOW — **COMPLETED** (v0.17.5) |

See [`AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md)
for the full workstream plan (5 phases: N1 through N5, 122 subtasks).

**WS-N1 (v0.17.1):** Core types + operations — 379 new lines in
`SeLe4n/Kernel/RobinHood/Core.lean` plus re-export hub. Delivers:
- **N1-A:** `RHEntry` (key, value, probe distance), `RHTable` (single-
  representation `Array (Option (RHEntry α β))` with capacity-positivity and
  slots-length invariants), `idealIndex`/`nextIndex` with `@[inline]`,
  `idealIndex_lt`/`nextIndex_lt` bound proofs via `Nat.mod_lt`.
- **N1-B:** `RHTable.empty` constructor, `countOccupied` helper, 4-conjunct
  `RHTable.WF` predicate, `empty_wf` proof (zero sorry).
- **N1-C:** Fuel-bounded `insertLoop` with 5 operational branches (empty slot,
  key match, Robin Hood swap, continue probing, fuel exhausted).
  `insertLoop_preserves_len` proof by induction on fuel.
- **N1-D:** `RHTable.insert` with 75% load-factor resize trigger,
  `insertNoResize_size_le` proof. Full `insert_size_le` deferred to N2
  (requires WF preservation through resize).
- **N1-E:** Fuel-bounded `getLoop` with Robin Hood early termination,
  `RHTable.get?`, `RHTable.contains`.
- **N1-F:** `findLoop` + `backshiftLoop` (backward-shift erasure),
  `backshiftLoop_preserves_len` proof, `RHTable.erase`.
- **N1-G:** `RHTable.fold`, `RHTable.toList`, `RHTable.resize` (double
  capacity, re-insert all), `resize_preserves_len` proof (`slots.size =
  capacity * 2` via `Array.foldl_induction`), `resize_fold_capacity` proof,
  `Membership` instance, `GetElem`/`GetElem?` instances (bracket notation
  `t[k]?`).
- **N1-H:** Re-export hub `SeLe4n/Kernel/RobinHood.lean`.
- Zero `sorry`/`axiom`. Zero warnings. All test tiers pass.

**WS-N2 (v0.17.2):** Invariant proofs — invariant definitions, WF/distCorrect
preservation, modular arithmetic helpers, and lookup correctness foundations.
Delivers:
- **Major finding:** Discovery: `robinHoodOrdered` (non-decreasing dist within
  clusters) is NOT preserved by backshift-on-erase. The `invExt` bundle was
  restructured to use `probeChainDominant` instead, which IS preserved by all
  operations.
- **N2-A:** Invariant definitions in `SeLe4n/Kernel/RobinHood/Invariant/Defs.lean`:
  `distCorrect` (probe distance accuracy), `noDupKeys` (key uniqueness),
  `robinHoodOrdered` (non-decreasing cluster distances), `probeChainDominant`
  (replaces `robinHoodOrdered` in `invExt` bundle), `RHTable.invariant`
  (restructured bundle using `probeChainDominant`).
  `empty_distCorrect`, `empty_noDupKeys`, `empty_robinHoodOrdered`,
  `empty_invariant` proofs for empty table.
- **N2-B:** WF preservation in `SeLe4n/Kernel/RobinHood/Invariant/Preservation.lean`:
  `insertNoResize_preserves_wf`, `insert_preserves_wf`, `resize_preserves_wf`,
  `erase_preserves_wf`. Modular arithmetic helpers: `mod_succ_eq`,
  `dist_step_mod`. `countOccupied_le_size` bound proof.
- **N2-C:** distCorrect preservation: `insertLoop_preserves_distCorrect` (full
  induction proof with modular arithmetic), `insertNoResize_preserves_distCorrect`,
  `insert_preserves_distCorrect`, `resize_preserves_distCorrect` (via fold
  induction).
- **N2-D:** Loop count and correctness: `insertLoop_countOccupied`,
  `backshiftLoop_countOccupied`, `findLoop_lt`, `findLoop_correct`.
- **N2-E:** Bundle preservation theorems: `insert_preserves_invariant`,
  `erase_preserves_invariant`, `resize_preserves_invariant`.
- **N2-F:** Lookup correctness signatures in
  `SeLe4n/Kernel/RobinHood/Invariant/Lookup.lean`: `get_after_insert_eq`,
  `get_after_insert_ne`, `get_after_erase_eq`.
- **N2-G:** Re-export hub `SeLe4n/Kernel/RobinHood/Invariant.lean`. Updated
  `SeLe4n/Kernel/RobinHood.lean` to import Invariant module. Changed `private`
  to `protected` for `insertNoResize`, `insertNoResize_capacity`,
  `resize_fold_capacity` in `Core.lean`.
- Files: `SeLe4n/Kernel/RobinHood/Invariant/Defs.lean`,
  `SeLe4n/Kernel/RobinHood/Invariant/Preservation.lean`,
  `SeLe4n/Kernel/RobinHood/Invariant/Lookup.lean`,
  `SeLe4n/Kernel/RobinHood/Invariant.lean` (new);
  `SeLe4n/Kernel/RobinHood/Core.lean`, `SeLe4n/Kernel/RobinHood.lean` (modified).
- **N2 additional deliverables:** `noDupKeys_after_clear`,
  `backshiftLoop_preserves_noDupKeys`, `erase_preserves_noDupKeys`,
  `displacement_backward`, `backshiftLoop_preserves_distCorrect`,
  `erase_preserves_distCorrect`.
- Preservation theorems proved: WF (all ops), distCorrect (all ops),
  noDupKeys (all ops), probeChainDominant (all ops). All 6 TPI-D items
  completed with zero sorry.
- **TPI-D1 completed:** `insertLoop_preserves_noDupKeys` — full fuel induction
  proving noDupKeys for insertLoop result (zero sorry).
- **TPI-D2 completed:** `insertLoop_preserves_pcd` — full fuel induction
  proving probeChainDominant for insertLoop result (zero sorry).
- **TPI-D3 completed:** `erase_preserves_probeChainDominant` — relaxedPCD
  framework: clear creates relaxedPCD gap, backshiftStep_relaxedPCD advances
  gap, relaxedPCD_to_pcd_at_termination recovers full PCD when loop terminates
  at empty/dist=0 slot (zero sorry).
- **TPI-D4 completed:** `get_after_insert_eq` — insert lookup correctness via
  `getLoop_finds_present` + `insertLoop_places_key` (zero sorry).
- **TPI-D5 completed:** `get_after_insert_ne` — insert non-interference via
  `insertLoop_absent_ne_key` (none case) + `insertLoop_output_source` +
  `resize_preserves_key_absence` (some case) (zero sorry).
- **TPI-D6 completed:** `get_after_erase_eq` — erase lookup correctness via
  `erase_removes_key` + `getLoop_none_of_absent` (zero sorry).
- Helper infrastructure: `offset_injective` (modular offset injectivity),
  `getElem_idx_eq` (array access proof irrelevance), `carried_key_absent`
  (key absent if probe reached empty/swap position), `getLoop_none_of_absent`
  (if key absent from all slots, getLoop returns none), `displacement_backward`
  (backshift displacement decrement), `relaxedPCD` (gap-excused PCD invariant).
- Zero `sorry`/`axiom`. Zero warnings. All test tiers pass.
- **WS-N2 COMPLETE** — 6/6 TPI-D proofs, ~4,655 LoC across Defs/Preservation/Lookup.

**WS-N4 (v0.17.4):** Kernel integration (first site — CNode.slots) — replaced
`CNode.slots : Std.HashMap Slot Capability` with `RHTable Slot Capability`
across the entire kernel. Delivers:
- **N4-A1/A2:** Type change in `Model/Object/Types.lean` — import
  `SeLe4n.Kernel.RobinHood.Bridge`, CNode.slots field type changed to
  `Kernel.RobinHood.RHTable Slot Capability`.
- **N4-A3:** CNode operations updated in `Model/Object/Structures.lean` —
  `CNode.empty` uses `RHTable.empty 16`, `CNode.mk'` uses `RHTable.ofList`,
  `CNode.lookup`/`insert`/`remove`/`revokeTargetLocal` use RHTable operations,
  `BEq CNode` uses `RHTable.fold`, manual `DecidableEq CNode` instance added,
  `CNode.slotsUnique` repurposed from `True` to substantive invariant
  `cn.slots.invExt ∧ cn.slots.size < cn.slots.capacity ∧ 4 ≤ cn.slots.capacity`.
- **N4-Bridge:** 3 new bridge lemmas in `Bridge.lean` — `filter_fold_absent_by_pred`
  (predicate-gated fold induction for filter absence), `filter_get_pred`
  (filter lookup implies predicate holds), `filter_filter_getElem?` (filter
  idempotence for projection proofs).
- **N4-Capability:** Invariant updates across `Capability/Invariant/Defs.lean`,
  `Authority.lean`, `Preservation.lean` — `cspaceSlotUnique` propagated as
  theorem parameter where RHTable operations require `invExt`; `remove_slots_sub`,
  `revokeTargetLocal_slots_sub` proofs updated with `change` for `[·]?`/`.get?`
  bridge; `cspaceRevoke_local_target_reduction` rewritten with `filter_get_pred`;
  `cspaceInsertSlot_lookup_eq` simplified with direct bridge lemma application.
- **N4-InformationFlow:** `projectKernelObject_idempotent` updated with
  `slotsUnique` hypothesis, using `filter_filter_getElem?`; `cspaceSlotUnique`
  propagated through `Helpers.lean`, `Operations.lean`, `Composition.lean`.
- **N4-State:** `RHTable.fold` argument-order updates in `State.lean`,
  `Lifecycle/Operations.lean`, `Testing/InvariantChecks.lean`.
- **N4-Tests:** All test files updated — `Std.HashMap.ofList` → `RHTable.ofList`,
  `slots := {}` → `RHTable.empty 16`, fold argument order fixes. Files:
  `MainTraceHarness.lean`, `OperationChainSuite.lean`, `NegativeStateSuite.lean`,
  `InformationFlowSuite.lean`, `TraceSequenceProbe.lean`.
- 20+ files modified. Zero `sorry`/`axiom`. Zero warnings. All test tiers pass.
- **WS-N4 COMPLETE** — CNode.slots fully migrated to verified RHTable.

### WS-M workstream (Capability subsystem audit & remediation)

WS-M is a **completed** workstream portfolio (v0.16.14–v0.17.0), created from a
comprehensive end-to-end audit of the Capability subsystem (3,520 LoC, 5 files).
The audit found zero `sorry`/`axiom`, zero critical vulnerabilities, but
identified 5 performance optimization opportunities, 4 proof strengthening
opportunities, 3 test coverage gaps, and 2 previously deferred items. All 5
phases delivered. All findings resolved.

| ID | Focus | Priority |
|----|-------|----------|
| **WS-M1** | Proof strengthening: guard-match theorem, CDT mint completeness, `addEdge_preserves_edgeWellFounded_fresh`, error-swallowing consistency, docstring updates | HIGH — **COMPLETED** (v0.16.14) |
| **WS-M2** | Performance: fused revoke fold, CDT `parentMap` index, shared reply lemma | HIGH — **COMPLETED** (v0.16.15) |
| **WS-M3** | IPC capability transfer (20 subtasks): `CapTransferResult`/`CapTransferSummary` types, `DerivationOp.ipcTransfer`, `findFirstEmptySlot`, `ipcTransferSingleCap`/`ipcUnwrapCaps`, IPC wrappers, API wiring, 2 test scenarios (resolves L-T03) | MEDIUM — **COMPLETED** (v0.16.17) |
| **WS-M4** | Test coverage (8 subtasks): multi-level resolution edge cases (guard-only, 64-bit max depth, guard mismatch at intermediate level, partial bits, single-level leaf), strict revocation stress (15+ deep chain, partial failure, BFS ordering) | MEDIUM — **COMPLETED** (v0.16.18) |
| **WS-M5** | Streaming BFS revocation (13 subtasks): `streamingRevokeBFS` interleaved BFS loop, `cspaceRevokeCdtStreaming` top-level operation, 3 preservation theorems, `SCN-REVOKE-STREAMING-BFS` test, full documentation sync; v0.17.0 optimization pass | LOW — **COMPLETED** (v0.16.19; optimized v0.17.0) |

See [`AUDIT_v0.16.13_CAPABILITY_SUBSYSTEM_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.16.13_CAPABILITY_SUBSYSTEM_WORKSTREAM_PLAN.md)
for the full workstream plan (5 phases: M1 through M5).

**WS-M1** (v0.16.14): Proof strengthening & correctness — 10 atomic subtasks.
M1-E: updated `cspaceRevoke` docstring (removed stale scope disclaimer).
M1-A: added `resolveCapAddress_guard_match` forward-direction theorem proving
successful resolution implies guard bits match stored guardValue.
M1-B1: introduced `cdtMintCompleteness` predicate (derived nodes have parent
edges, root nodes are edge-isolated). M1-B2: transfer theorem for state
transitions preserving CDT edges and nodeSlot. M1-B3: extended invariant bundle
`capabilityInvariantBundleWithMintCompleteness` with extraction theorems.
M1-C1: proved `addEdge_preserves_edgeWellFounded_fresh` — CDT acyclicity
preserved for fresh child nodes. M1-C2: `addEdgeWouldBeSafe` runtime check.
M1-D1: `cspaceRevokeCdt_swallowed_error_consistent` — invariant preservation,
object stability, and edge-set monotonicity through error-swallowing path.
M1-D2: enriched `cspaceRevokeCdt` docstring with error-handling rationale.
7 new proved declarations; zero sorry/axiom.

**WS-M2** (v0.16.15): Performance optimization — 3 targeted improvements across
the Capability subsystem hot paths. M2-A: fused `revokeAndClearRefsState` replaces
the prior two-pass revoke pattern (one O(m) traversal to revoke children, then a
second O(m) traversal to clear parent references) with a single O(m) pass that
performs both revocation and reference clearing in one fold over the child set.
M2-B: CDT `parentMap` index added to `CSpaceState` — `parentOf` lookups are now
O(1) instead of scanning the CDT edge set; `removeNode`, `removeAsChild`, and
`removeAsParent` are updated to maintain the index with targeted updates rather
than full rebuilds. M2-C: reply lemma extraction — the proof body for
`endpointReply` preservation is factored into a shared lemma consumed by both
the direct-reply and reply-recv paths, eliminating duplicated proof obligations.
Field preservation lemmas for non-interference proofs added to cover the new
`parentMap` index field. Runtime `parentMapConsistent` check added and verified.
Zero sorry/axiom.

**WS-M3** (v0.16.17): IPC capability transfer — seL4-aligned receive-side cap
unwrapping with Grant-right gate. M3-A: `CapTransferResult`/`CapTransferSummary`
types, `DerivationOp.ipcTransfer` CDT variant. M3-B: `CNode.findFirstEmptySlot`
with structural recursion and correctness theorems. M3-C: `ipcTransferSingleCap`
single-cap transfer with CDT edge tracking and `capabilityInvariantBundle`
preservation proof. M3-D: `ipcUnwrapCaps` batch unwrap with `ipcUnwrapCapsLoop`
recursive helper and scheduler preservation proof by induction;
`ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant` bundle preservation
when Grant absent. M3-E: `endpointSendDualWithCaps`, `endpointReceiveDualWithCaps`,
`endpointCallWithCaps` wrapper operations composing existing IPC ops with cap
transfer; IPC invariant preservation proofs for all three wrappers plus
`ipcUnwrapCaps_preserves_ipcInvariant`; `dualQueueSystemInvariant` preservation
for `ipcUnwrapCaps` and both WithCaps wrappers (`ipcUnwrapCaps_preserves_dualQueueSystemInvariant`,
`endpointSendDualWithCaps_preserves_dualQueueSystemInvariant`,
`endpointReceiveDualWithCaps_preserves_dualQueueSystemInvariant`);
`ipcUnwrapCaps_preserves_cnode_at_root` CNode type preservation. M3-F: `decodeExtraCapAddrs`,
`resolveExtraCaps`, API dispatch updated to use WithCaps wrappers with renamed
theorems (`dispatchWithCap_send_uses_withCaps`, `dispatchWithCap_call_uses_withCaps`).
M3-G: 4 test scenarios (SCN-IPC-CAP-TRANSFER-BASIC, SCN-IPC-CAP-TRANSFER-NO-GRANT,
SCN-IPC-CAP-TRANSFER-FULL-CNODE, SCN-IPC-CAP-BADGE-COMBINED). Resolves L-T03
(capability transfer during IPC). 12+ new proved declarations; zero sorry/axiom.

**WS-M4** (v0.16.18): Test coverage expansion — 8 atomic subtasks across 2 tasks,
addressing M-T01 (multi-level resolution) and M-T02 (strict revocation).
M4-A: 5 `resolveCapAddress` edge case tests in NegativeStateSuite — guard-only
CNode with zero radixWidth (SCN-RESOLVE-GUARD-ONLY), 64-bit resolution across 8
CNodes (SCN-RESOLVE-MAX-DEPTH), guard mismatch at intermediate level in a 3-level
chain (SCN-RESOLVE-GUARD-MISMATCH-MID), partial bit consumption where
bitsRemaining < guardWidth + radixWidth (SCN-RESOLVE-PARTIAL-BITS), and
single-level leaf resolution (SCN-RESOLVE-SINGLE-LEVEL). M4-B: 3
`cspaceRevokeCdtStrict` stress tests in OperationChainSuite — 15-level deep
derivation chain with full deletion verification (SCN-REVOKE-STRICT-DEEP),
partial failure mid-traversal with corrupted CNode triggering `.objectNotFound`
and `firstFailure` context verification (SCN-REVOKE-STRICT-PARTIAL-FAIL), and
branching tree BFS ordering verification with 5 descendants
(SCN-REVOKE-STRICT-ORDER). 8 new test scenarios; zero sorry/axiom (test-only
phase; no new proof declarations).

**WS-M5** (v0.16.19): Streaming revocation & documentation — 13 atomic subtasks
across 2 tasks, addressing M-P04 (streaming BFS optimization). M5-A:
`streamingRevokeBFS` interleaved BFS loop that processes CDT descendants
on-the-fly instead of materializing the full descendant list upfront, reducing
peak memory from O(N) to O(max branching factor); `cspaceRevokeCdtStreaming`
top-level operation composing `cspaceRevoke` with streaming BFS;
`streamingRevokeBFS_step_preserves` single-step invariant preservation
(same case analysis as `revokeCdtFoldBody_preserves`);
`streamingRevokeBFS_preserves` full induction proof by fuel;
`cspaceRevokeCdtStreaming_preserves_capabilityInvariantBundle` top-level
preservation composing local revoke with streaming BFS preservation;
`SCN-REVOKE-STREAMING-BFS` test scenario exercising 5-node branching tree
with all descendants deleted, root preserved, CDT nodes detached.
M5-B: version bump to v0.16.19, workstream plan refinement into 13 granular
subtasks, full documentation sync across WORKSTREAM_HISTORY, DEVELOPMENT,
CLAIM_EVIDENCE_INDEX, SELE4N_SPEC, and 7 GitBook chapters; codebase map
regeneration and README metrics sync. 3 new proved declarations; 1 new test
scenario. Zero sorry/axiom. Closes M-P04. **WS-M portfolio fully completed.**

**WS-M5 optimization** (v0.17.0): Extracted `processRevokeNode` shared helper
eliminating code duplication between materialized fold and streaming BFS paths.
Added `processRevokeNode_preserves_capabilityInvariantBundle` shared theorem.
Simplified `streamingRevokeBFS_step_preserves` to one-line delegation. Added 3
new edge case tests: chain19 (empty CDT), chain20 (deep linear chain), chain21
(streaming-vs-materialized equivalence). Zero sorry/axiom.

### WS-L workstream (IPC subsystem audit & remediation)

WS-L is a **completed** workstream portfolio (v0.16.9–v0.16.13), created from a
comprehensive end-to-end audit of the IPC subsystem (9,195 LoC, 12 files). The
audit found zero critical issues, zero sorry/axiom, but identified 3 performance
optimization opportunities, 5 proof strengthening opportunities, and 5 test
coverage gaps. WS-L resolved all deferred WS-I5 items. All 5 phases delivered.

| ID | Focus | Priority |
|----|-------|----------|
| **WS-L1** | IPC performance optimization: eliminate redundant TCB lookups in endpointReceiveDual, endpointReply, notificationWait | HIGH — **COMPLETED** (v0.16.9) |
| **WS-L2** | Code quality: HashMap.fold migration — eliminate all `.toList.foldl/foldr` anti-patterns (closes WS-I5/R-17) | MEDIUM — **COMPLETED** (v0.16.10) |
| **WS-L3** | Proof strengthening: enqueue-dequeue round-trip, queue link integrity, ipcState-queue consistency, tail preservation, reply contract preservation | MEDIUM — **COMPLETED** (v0.16.11) |
| **WS-L4** | Test coverage: ReplyRecv positive-path + rendezvous, endpoint lifecycle with queued threads, blocked thread rejection, multi-endpoint interleaving (3 endpoints) | MEDIUM — **COMPLETED** (v0.16.12) |
| **WS-L5** | Documentation: IF readers' guide, fixture update process, metrics automation, full doc sync (closes WS-I5/R-13/R-14/R-18) | LOW — **COMPLETED** (v0.16.13) |

**WS-L1** (v0.16.9): Eliminated 4 redundant TCB lookups on IPC hot paths.
L1-A: changed `endpointQueuePopHead` return type to `(ThreadId × TCB × SystemState)`,
providing pre-dequeue TCB to callers and eliminating redundant `lookupTcb` in
`endpointReceiveDual`. L1-B: added `storeTcbIpcStateAndMessage_fromTcb` with
equivalence theorem, eliminating redundant lookups in `endpointReply` and
`endpointReplyRecv`. L1-C: added `storeTcbIpcState_fromTcb` with equivalence
theorem, eliminating redundant lookup in `notificationWait`. Added
`lookupTcb_preserved_by_storeObject_notification` helper for cross-store TCB
stability. ~18 mechanical pattern-match updates across 6 invariant files. Zero
sorry/axiom; all proofs machine-checked.

**WS-L2** (v0.16.10): Eliminated all 4 `Std.HashMap.toList.foldl/foldr`
anti-patterns across the codebase. L2-A: migrated 3 fold patterns in
`Testing/InvariantChecks.lean` (`cspaceSlotCoherencyChecks`,
`capabilityRightsStructuralChecks`, `cdtChildMapConsistentCheck`) from
`.toList.foldr` to direct `HashMap.fold`. L2-B: migrated `detachCNodeSlots`
in `Kernel/Lifecycle/Operations.lean` from `.toList.foldl` to `HashMap.fold`,
updated 3 preservation proofs (`_objects_eq`, `_lifecycle_eq`, `_scheduler_eq`)
using `Std.HashMap.fold_eq_foldl_toList` bridge lemma. Refined WS-L2 workstream
plan with expanded scope covering all 4 sites (original plan only covered 1).
Zero sorry/axiom; all proofs machine-checked.

**WS-L3** (v0.16.11): Proof strengthening for IPC dual-queue subsystem.
L3-A: enqueue-dequeue round-trip theorem — `endpointQueueEnqueue_empty_sets_head`
(postcondition), `endpointQueueEnqueue_empty_queueNext_none` (TCB state),
`endpointQueueEnqueue_then_popHead_succeeds` (composed round-trip).
L3-B: standalone `tcbQueueLinkIntegrity` preservation for popHead and enqueue
(extracted from bundled `dualQueueSystemInvariant`).
L3-C: `ipcStateQueueConsistent` invariant definition (blocked → endpoint exists)
plus queue-operation preservation (popHead, enqueue). Forward endpoint preservation
helpers (`storeTcbQueueLinks_endpoint_forward`, `endpointQueuePopHead_endpoint_forward`,
`endpointQueueEnqueue_endpoint_forward`).
L3-C3: high-level `ipcStateQueueConsistent` preservation for `endpointSendDual`,
`endpointReceiveDual`, `endpointReply` — plus 5 sub-operation helpers
(`ensureRunnable`, `removeRunnable`, `storeTcbIpcStateAndMessage`,
`storeTcbIpcState`, `storeTcbPendingMessage`).
L3-D: tail consistency for `endpointQueueRemoveDual` — non-tail removal preserves
tail (`_preserves_tail_of_nonTail`), tail removal characterization (`_tail_update`).
L3-E: already resolved (pre-existing in `CallReplyRecv.lean:797`).
22 new theorems, 1 new invariant definition. Zero sorry/axiom; all proofs
machine-checked.

**WS-L4** (v0.16.12): IPC test coverage expansion. Filled all 4 test coverage
gaps identified during the IPC subsystem audit: L-T01 (ReplyRecv positive-path),
L-T02 (endpoint lifecycle with queued threads), L-T04 (blocked thread rejection),
L-T05 (multi-endpoint interleaving). 9 new scenario IDs (16 total across L4
test functions), 2 new cross-state blocked-thread rejection tests (L4-C4/C5).
L4-A2: extended `runReplyRecvRoundtripTrace` with second-sender rendezvous
path (RRC-002, RRC-006). L4-B: new `runEndpointLifecycleTrace` validates
graceful-failure-by-guard model when endpoint is retyped while senders are
blocked on sendQ (ELC-001 through ELC-004). L4-D2/D3: extended
`runMultiEndpointInterleavingTrace` from 2 to 3 endpoints with out-of-order
receive and FIFO verification (MEI-004, MEI-005, MEI-006). L-T03 (cap transfer)
intentionally deferred — CSpace IPC integration not yet modeled.

**WS-L5** (v0.16.13): Documentation & workstream closeout. L5-A: added
information-flow architecture readers' guide to `docs/gitbook/12-proof-and-invariant-map.md`
documenting the 3-layer Policy → Enforcement → Invariant architecture with
cross-references to all canonical source files. L5-B/L5-C: test fixture update
process and metrics regeneration documentation delivered early in v0.16.12 (already
present in `docs/DEVELOPMENT.md` §7). L5-D: split into 6 sub-tasks (D1–D6) for
version bump, README/spec sync, DEVELOPMENT.md update, workstream history/claim
evidence, GitBook sync, and test validation. Bumped version to 0.16.13.
Regenerated `docs/codebase_map.json`. Updated metrics across README, SELE4N_SPEC,
and GitBook chapters. Added WS-L3 theorem documentation to GitBook ch.12.
All findings resolved (12/13, 1 intentionally deferred). All 4 WS-I5 deferred
items closed. WS-L portfolio complete.

See [`AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md)
for the full workstream plan (5 phases: L1 through L5).

### Remaining WS-H workstreams

WS-H1..H16 are all completed. No remaining WS-H workstreams.

### WS-F workstreams (F1-F8) — ALL COMPLETED

All WS-F workstreams are completed. The v0.12.2 audit remediation portfolio is
100% closed (33/33 findings). See the
[workstream plan](dev_history/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md) for details.

| ID | Focus | Priority |
|----|-------|----------|
| **WS-F5** | Model fidelity (word-bounded badge, order-independent rights, deferred ops) | Medium — **COMPLETED** (v0.14.9) |
| **WS-F6** | Invariant quality (tautology reclassification, adapter proof hooks) | Medium — **COMPLETED** |
| **WS-F7** | Testing expansion (oracle, probe, fixtures) | Low — **COMPLETED** |
| **WS-F8** | Cleanup (dead code, dead type constructors, extension labeling) | Low — **COMPLETED** |

### WS-I workstreams (I1-I5) — Improvement recommendations from v0.14.9 audit

The v0.14.9 comprehensive codebase audit identified 18 non-blocking improvement
recommendations across testing, proof quality, documentation, code quality, and
coverage expansion. These are organized into 5 workstreams across 3 phases. See
the [workstream plan](dev_history/audits/AUDIT_v0.14.9_IMPROVEMENT_WORKSTREAM_PLAN.md) for
full details.

| ID | Focus | Priority |
|----|-------|----------|
| **WS-I1** | Test infrastructure hardening (inter-transition assertions, determinism promotion, scenario ID traceability) | HIGH — **COMPLETED** (v0.15.0) |
| **WS-I2** | Proof & hygiene strengthening (semantic L-08 validation, Tier 3 correctness anchors, VSpace memory ownership projection) | HIGH — **COMPLETED** (v0.15.1) |
| **WS-I3** | Operations coverage expansion (multi-operation chains, scheduler stress, declassification checks) | MEDIUM — **COMPLETED** (v0.15.2) |
| **WS-I4** | Subsystem coverage expansion (VSpace multi-ASID, IPC interleaving, lifecycle cascading revoke chains) | LOW — **COMPLETED** (v0.15.3) |
| **WS-I5** | Documentation and code-quality polish (remaining low-priority recommendations) | LOW — **SUPERSEDED by WS-L** (all R-12..R-18 items resolved within WS-L) |

### WS-J1 workstream (register-indexed authoritative namespaces)

WS-J1 supersedes the WS-I5 Part A documentation-only treatment of
`RegName`/`RegValue`. A comprehensive audit revealed that bare `Nat`
abbreviations are insufficient: the syscall API bypasses the machine register
file entirely, omitting the decode path where untrusted user-space register
values become trusted kernel references. WS-J1 addresses this by:

1. Replacing `RegName`/`RegValue` with typed wrapper structures.
2. Introducing a `RegisterDecode.lean` module with total, deterministic decode
   functions from raw register words to typed kernel identifiers.
3. Adding `syscallEntry` as a register-sourced syscall dispatch path.
4. Wrapping `CdtNodeId` (secondary bare-Nat alias) for consistency.
5. Proving decode correctness, invariant preservation, and NI properties.

See [`AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md)
for the full workstream plan (6 phases: J1-A through J1-F).

| ID | Focus | Priority |
|----|-------|----------|
| **WS-J1** | Replace `abbrev Nat` register types with typed wrappers, add syscall argument decode layer bridging machine registers to typed kernel operations, wrap `CdtNodeId`, prove decode correctness and NI | HIGH — **J1-A COMPLETED** (v0.15.4), **J1-B COMPLETED** (v0.15.5), **J1-C COMPLETED** (v0.15.6; audit refinements v0.15.7), **J1-D COMPLETED** (v0.15.8), **J1-E COMPLETED** (v0.15.9), **J1-F COMPLETED** (v0.15.10) — **PORTFOLIO COMPLETE** |

### WS-K workstream (full syscall dispatch completion)

WS-K completed the syscall surface that WS-J1 established. WS-J1 built the
typed register decode layer and 13-case dispatch skeleton, but 7 syscalls
returned `.illegalState` (CSpace mint/copy/move/delete, lifecycle retype,
VSpace map/unmap), 2 service syscalls used `(fun _ => true)` policy stubs,
and IPC messages carried empty register payloads. WS-K addressed all of these:

1. Extending `SyscallDecodeResult` with message register values (x2–x5).
2. Per-syscall argument structures with total decode functions.
3. Full dispatch for all 13 syscalls (zero `.illegalState` stubs).
4. Configuration-sourced service policy replacing permissive stubs.
5. IPC message body population from decoded register contents.
6. Round-trip proofs, NI integration, and deferred proof completion.

See [`AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md)
for the full workstream plan (8 phases: K-A through K-H).

| ID | Focus | Priority |
|----|-------|----------|
| **WS-K** | Extend `SyscallDecodeResult` with msgRegs, implement per-syscall argument decode, wire all 13 syscalls through dispatch, replace service policy stubs, populate IPC message bodies, prove round-trip correctness and NI, comprehensive testing and documentation | CRITICAL — **K-A COMPLETED** (v0.16.0), **K-B COMPLETED** (v0.16.1), **K-C COMPLETED** (v0.16.2), **K-D COMPLETED** (v0.16.3), **K-E COMPLETED** (v0.16.4), **K-F COMPLETED** (v0.16.5), **K-G COMPLETED** (v0.16.7), **K-H COMPLETED** (v0.16.8) — **PORTFOLIO COMPLETE** |

### Raspberry Pi 5 hardware binding

After the remaining workstreams, the next major milestone is populating the RPi5
platform stubs with hardware-validated contracts:

1. Populate RPi5 runtime contract with hardware-validated predicates.
2. Implement ARMv8 multi-level page table walk as a `VSpaceBackend` instance.
3. Implement GIC-400 interrupt routing with IRQ acknowledgment.
4. Bind timer adapter to ARM Generic Timer (CNTPCT_EL0).
5. Define boot sequence as a verified initial state construction.

### Long-horizon items

- MCS scheduling contexts (budget/period/replenishments).
- Multi-core support (per-core kernel instances).
- Device memory and IOMMU modeling.
- Cryptographic attestation of kernel image.
- Side-channel analysis at hardware binding layer.

## Completed workstream portfolio

| Portfolio | Version | Scope | Workstreams |
|-----------|---------|-------|-------------|
| **WS-M** | v0.16.14–v0.17.0 | Capability subsystem audit & remediation — 5 phases, 55+ subtasks, all 14 audit findings resolved. M1: proof strengthening (guard-match, mint completeness, addEdge acyclicity, error-swallowing consistency). M2: performance optimization (fused revoke, CDT parentMap, shared reply lemma). M3: IPC capability transfer (20 subtasks, resolves L-T03). M4: test coverage expansion (8 edge-case tests). M5: streaming BFS revocation + documentation sync; v0.17.0 optimization (shared `processRevokeNode` helper, 3 new edge case tests). Zero sorry/axiom. | M1–M5 |
| **WS-M2** | v0.16.15 | Capability subsystem performance optimization. M2-A: fused `revokeAndClearRefsState` — single-pass O(m) fold replacing two O(m) passes (revoke children + clear parent references). M2-B: CDT `parentMap` index in `CSpaceState` — O(1) `parentOf` lookup; `removeNode`/`removeAsChild`/`removeAsParent` maintain the index with targeted updates. M2-C: shared reply lemma extraction — factored `endpointReply` preservation proof body consumed by both direct-reply and reply-recv paths. Field preservation lemmas for non-interference proofs added for new `parentMap` field. Runtime `parentMapConsistent` check added and verified. Zero sorry/axiom. | M2 |
| **WS-L** | v0.16.9–v0.16.13 | IPC subsystem audit & remediation — comprehensive end-to-end audit of IPC subsystem (9,195 LoC, 12 files). L1: eliminated 4 redundant TCB lookups on IPC hot paths. L2: HashMap.fold migration (4 sites). L3: 22 new theorems + `ipcStateQueueConsistent` invariant. L4: 16 test scenario IDs, 4 coverage gaps filled. L5: IF readers' guide, version bump, full doc sync. 12/13 findings resolved, 1 deferred (L-T03). All WS-I5 deferred items closed. Zero sorry/axiom. | L1–L5 |
| **WS-K-H** | v0.16.8 | Documentation sync and workstream closeout: updated `WORKSTREAM_HISTORY.md` with WS-K portfolio completion (K-A through K-H, v0.16.0–v0.16.8); updated `SELE4N_SPEC.md` current state snapshot with v0.16.8 version, updated metrics (37,139 production LoC, 4,037 test LoC, 1,198 proved declarations), and WS-K portfolio complete status; updated `DEVELOPMENT.md` active workstream to show WS-K complete, next priority as RPi5 hardware binding; updated `CLAIM_EVIDENCE_INDEX.md` WS-K claim row with comprehensive K-A through K-H deliverables and evidence commands; updated GitBook chapters: `03-architecture-and-module-map.md` (added `SyscallArgDecode.lean` module entry with 7 structures, 7 decode functions, 7 encode functions, 14 theorems), `04-project-design-deep-dive.md` (added section 1.7 documenting two-layer syscall argument decode architecture), `05-specification-and-roadmap.md` (version and roadmap update, WS-K complete, RPi5 next), `12-proof-and-invariant-map.md` (added WS-K proof surface: layer-2 round-trip proofs, delegation theorems, NI coverage extension to 34 constructors); regenerated `docs/codebase_map.json`; synced `README.md` metrics from `readme_sync`; bumped `lakefile.toml` version to 0.16.8; refined WS-K-H workstream plan from 9 flat tasks into 13 granular subtasks (K-H.1 through K-H.13) with dependency ordering, per-file change specifications, and explicit acceptance criteria; updated completion evidence checklist from 5 to 13 K-H items. Zero sorry/axiom. Closes WS-K Phase H. WS-K portfolio fully complete. | K-H |
| **WS-K-G** | v0.16.7 | Lifecycle NI proof completion and deferred proof resolution: added `cspaceRevoke_preserves_projection` standalone theorem in `InformationFlow/Invariant/Operations.lean` extracted from inline proof for compositional reuse; added `lifecycleRevokeDeleteRetype_preserves_projection` theorem chaining projection preservation across `cspaceRevoke`, `cspaceDeleteSlot`, and `lifecycleRetypeObject` sub-operations; added `lifecycleRevokeDeleteRetype_preserves_lowEquivalent` two-run NI theorem completing the previously deferred `lifecycleRevokeDeleteRetype` NI proof using compositional projection-preservation reasoning; extended `NonInterferenceStep` inductive with `lifecycleRevokeDeleteRetype` constructor (34 constructors total, up from 33); updated `step_preserves_projection` with the new constructor case; updated `syscallNI_coverage_witness` documentation to reflect 34-constructor exhaustive match. Zero sorry/axiom. Closes WS-K Phase G | K-G |
| **WS-K-F** | v0.16.5 | Proofs: round-trip, preservation, and NI integration: added 7 encode functions in `SyscallArgDecode.lean` (`encodeCSpaceMintArgs` through `encodeVSpaceUnmapArgs`) completing encode/decode symmetry for all layer-2 structures; proved 7 round-trip theorems via structure eta reduction (`rcases + rfl`) with `decode_layer2_roundtrip_all` composed conjunction; added `extractMessageRegisters_roundtrip` in `RegisterDecode.lean` closing the layer-1 extraction round-trip gap; added `dispatchWithCap_layer2_decode_pure` proving decode functions depend only on `msgRegs` (two results with same `msgRegs` produce identical decode) and `dispatchWithCap_preservation_composition_witness` structural preservation theorem in `API.lean`; added `retypeFromUntyped_preserves_lowEquivalent` NI theorem completing the last deferred NI proof via two-stage `storeObject_at_unobservable_preserves_lowEquivalent` composition; added `syscallNI_coverage_witness` in `Composition.lean` witnessing decode-error NI step availability, step→trace composition, and `step_preserves_projection` totality over all 33 constructors; refined WS-K-F plan into 6 granular sub-phases (K-F1 through K-F6). Zero sorry/axiom. Closes WS-K Phase F | K-F |
| **WS-K-E** | v0.16.4 | Service policy and IPC message population: added `ServiceConfig` structure with `Inhabited` default (permissive `fun _ => true`) in `Model/State.lean`; extended `SystemState` with `serviceConfig : ServiceConfig := default` field; replaced `(fun _ => true)` service policy stubs in `dispatchWithCap` with `st.serviceConfig.allowStart`/`st.serviceConfig.allowStop` — service operations now read policy from system state configuration; added `extractMessageRegisters` in `RegisterDecode.lean` that converts `Array RegValue` → `Array Nat` (matching `IpcMessage.registers : Array Nat`) with triple bound (`info.length`, `maxMessageRegisters`, `msgRegs.size`); updated `.send`/`.call`/`.reply` IPC dispatch arms to populate message bodies from decoded message registers instead of empty arrays; proved `extractMessageRegisters_length` (result size ≤ `maxMessageRegisters`), `extractMessageRegisters_ipc_bounded` (constructed `IpcMessage` satisfies `bounded`), `extractMessageRegisters_deterministic`; 5 delegation theorems (`dispatchWithCap_serviceStart_uses_config`, `dispatchWithCap_serviceStop_uses_config`, `dispatchWithCap_send_populates_msg`, `dispatchWithCap_call_populates_msg`, `dispatchWithCap_reply_populates_msg`); all existing soundness theorems compile unchanged; `BootstrapBuilder` extended with `serviceConfig` field and `withServiceConfig` combinator; 11 Tier 3 invariant surface anchors (5 `rg` + 11 `#check`). Zero `(fun _ => true)` stubs remain. Zero `registers := #[]` in IPC dispatch. Zero sorry/axiom. Closes WS-K Phase E | K-E |
| **WS-K-D** | v0.16.3 | Lifecycle and VSpace syscall dispatch: wired all 3 remaining syscall stubs (`lifecycleRetype`, `vspaceMap`, `vspaceUnmap`) through `dispatchWithCap` — zero `.illegalState` stubs remain, all 13 syscalls fully dispatch; added `objectOfTypeTag` total type-tag decoder with dedicated `invalidTypeTag` error variant, `lifecycleRetypeDirect` pre-resolved authority companion, `PagePermissions.ofNat`/`toNat` bitfield codec with round-trip theorem; 3 delegation theorems, 3 error-decomposition theorems, equivalence theorem linking `lifecycleRetypeDirect` to `lifecycleRetypeObject`; Tier 3 anchors. Zero sorry/axiom. Closes WS-K Phase D | K-D |
| **WS-K-C** | v0.16.2 | CSpace syscall dispatch: wired all 4 CSpace syscalls (`cspaceMint`, `cspaceCopy`, `cspaceMove`, `cspaceDelete`) through `dispatchWithCap` using decoded message register arguments from `SyscallArgDecode`; changed `dispatchWithCap` signature from `SyscallId` to `SyscallDecodeResult`; `cspaceMint` dispatch decodes srcSlot, dstSlot, rights bitmask, badge from 4 message registers with badge=0→none seL4 convention; `cspaceCopy`/`cspaceMove` dispatch decodes srcSlot and dstSlot from 2 message registers; `cspaceDelete` dispatch decodes targetSlot from 1 message register; 4 delegation theorems proved (`dispatchWithCap_cspaceMint_delegates`, `dispatchWithCap_cspaceCopy_delegates`, `dispatchWithCap_cspaceMove_delegates`, `dispatchWithCap_cspaceDelete_delegates`); all 3 existing soundness theorems compile unchanged; refined WS-K-C workstream plan with 8 detailed subtasks (K-C.1–K-C.8). Zero sorry/axiom. Closes WS-K Phase C | K-C |
| **WS-K-B** | v0.16.1 | Per-syscall argument decode layer: added `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` implementing layer 2 of the two-layer syscall decode architecture; 7 typed argument structures (`CSpaceMintArgs`, `CSpaceCopyArgs`, `CSpaceMoveArgs`, `CSpaceDeleteArgs`, `LifecycleRetypeArgs`, `VSpaceMapArgs`, `VSpaceUnmapArgs`) with `DecidableEq` and `Repr`; shared `requireMsgReg` bounds-checked indexing helper; 7 total decode functions with explicit `Except KernelError` error handling via `do` notation; 7 determinism theorems (trivial `rfl`); 7 error-exclusivity theorems (`decode fails ↔ msgRegs.size < N`) using `by_cases`/`dif_pos`/`nomatch` proof strategy; helper theorems `requireMsgReg_unfold_ok` and `requireMsgReg_unfold_err` for rewriting `dite` in mpr direction; integrated into `API.lean` import graph. Zero sorry/axiom. Closes WS-K Phase B | K-B |
| **WS-K-A** | v0.16.0 | Message register extraction into SyscallDecodeResult: added `msgRegs : Array RegValue := #[]` field to `SyscallDecodeResult` in `Model/Object/Types.lean`; updated `decodeSyscallArgs` in `RegisterDecode.lean` to validate and read message registers (x2–x5) in single pass via `Array.mapM`; added `encodeMsgRegs` identity encoder; proved `decodeMsgRegs_length` (output size = layout size) via novel `list_mapM_except_length`/`array_mapM_except_size` helpers; proved `decodeMsgRegs_roundtrip`; extended `decode_components_roundtrip` to 4-conjunct; NegativeStateSuite J1-NEG-17 verifies `msgRegs.size = 4`; RDT-002 trace includes msgRegs count; 4 new Tier 3 anchors; WS-K-A plan refined into 8 detailed subtasks. Zero sorry/axiom. Closes WS-K Phase A | K-A |
| **WS-J1-F** | v0.15.10 | CdtNodeId cleanup and documentation sync: replaced `abbrev CdtNodeId := Nat` with `structure CdtNodeId where val : Nat` in `Model/Object/Structures.lean`; added full instance suite (`DecidableEq`, `Hashable`, `LawfulHashable`, `EquivBEq`, `LawfulBEq`, `Repr`, `ToString`, `Inhabited`, `ofNat`/`toNat`); fixed downstream compilation (`SystemState` defaults, monotone allocator, test literals); all documentation synchronized across canonical sources and GitBook chapters; codebase map regenerated. All 16 kernel identifiers are now typed wrappers. Zero sorry/axiom. Closes WS-J1 Phase F. **WS-J1 portfolio fully completed** | J1-F |
| **WS-J1-E** | v0.15.9 | Testing and trace evidence: 18 negative decode tests in `NegativeStateSuite.lean`; 5 register-decode trace scenarios (RDT-002 through RDT-010) in `MainTraceHarness.lean`; 2 operation-chain tests in `OperationChainSuite.lean`; fixture and scenario registry updates; 13 Tier 3 invariant surface anchors for RegisterDecode definitions and theorems. Zero sorry/axiom. Closes WS-J1 Phase E | J1-E |
| **WS-J1-D** | v0.15.8 | Invariant and information-flow integration: `registerDecodeConsistent` predicate bridging decode layer to kernel object store validity (implied by `schedulerInvariantBundleFull` via `currentThreadValid`), `syscallEntry_preserves_proofLayerInvariantBundle` compositional preservation theorem for success and error paths, `syscallEntry_error_preserves_proofLayerInvariantBundle` trivial error-path preservation, `decodeSyscallArgs_preserves_lowEquivalent` NI theorem for pure decode, `syscallEntry_preserves_projection` projection-preservation theorem, two new `NonInterferenceStep` constructors (`syscallDecodeError` for failed decode/state unchanged, `syscallDispatchHigh` for high-domain dispatch with projection preservation), `step_preserves_projection` extended with new constructor cases, `syscallEntry_error_yields_NI_step` and `syscallEntry_success_yields_NI_step` bridge theorems from API to NI composition framework. Default-state, timer, and register-write preservation theorems for `registerDecodeConsistent`. Tier 3 anchor entries for all new definitions and theorems (13 grep anchors + 7 `#check` anchors). Zero sorry/axiom. Closes WS-J1 Phase D | J1-D |
| **WS-J1-C** | v0.15.6; refinements v0.15.7 | Syscall entry point and dispatch: `syscallEntry` top-level user-space entry point reading current thread's register file and dispatching via capability-gated `syscallInvoke`, `lookupThreadRegisterContext` for TCB register context extraction, `dispatchSyscall` routing decoded arguments through `SyscallGate` to internal kernel operations, `dispatchWithCap` per-syscall routing for all 13 syscalls (IPC send/receive/call/reply, CSpace mint/copy/move/delete, lifecycle retype, VSpace map/unmap, service start/stop), `syscallRequiredRight` total right mapping, `MachineConfig.registerCount` promoted to configurable field (default 32). Audit refinements (v0.15.7): CSpace/lifecycle/VSpace dispatch returns `illegalState` for MR-dependent ops, `syscallEntry` accepts `regCount` parameter, `syscallEntry_implies_capability_held` strengthened to full capability-resolution chain. Soundness theorems: `syscallEntry_requires_valid_decode`, `syscallEntry_implies_capability_held`, `dispatchSyscall_requires_right`, `lookupThreadRegisterContext_state_unchanged`, `syscallRequiredRight_total`. Zero sorry/axiom. Closes WS-J1 Phase C | J1-C |
| **WS-J1-B** | v0.15.5 | Register decode layer: `SyscallId` inductive (13 modeled syscalls with injective `toNat`/total `ofNat?`, round-trip and injectivity theorems), `MessageInfo` structure (seL4 message-info word bit-field layout with `encode`/`decode`), `SyscallDecodeResult` (typed decode output), total deterministic decode functions (`decodeCapPtr`, `decodeMsgInfo`, `decodeSyscallId`, `validateRegBound`, `decodeSyscallArgs`) in new `RegisterDecode.lean` module, `SyscallRegisterLayout` with `arm64DefaultLayout` (x0–x7 convention), `MachineConfig.registerCount`, 3 new `KernelError` variants (`invalidRegister`, `invalidSyscallNumber`, `invalidMessageInfo`), round-trip lemmas (`decodeCapPtr_roundtrip`, `decodeSyscallId_roundtrip`), determinism theorem, error exclusivity theorems, universal CPtr success theorem. Self-contained module with no kernel subsystem imports. Zero sorry/axiom. Closes WS-J1 Phase B | J1-B |
| **WS-J1-A** | v0.15.4 | Typed register wrappers: replaced `abbrev RegName := Nat` and `abbrev RegValue := Nat` with typed wrapper structures (`structure RegName where val : Nat` / `structure RegValue where val : Nat`) in `Machine.lean`; added full instance suites (`DecidableEq`, `Hashable`, `LawfulHashable`, `EquivBEq`, `LawfulBEq`, `Repr`, `ToString`, `ofNat`/`toNat`, roundtrip/injectivity proofs); updated `RegisterFile.gpr` type signature from `Nat → Nat` to `RegName → RegValue`; re-proved all 10 existing machine lemmas; fixed all downstream compilation (Architecture adapter/invariant, Platform Sim/RPi5 proof hooks, Testing trace harness); zero sorry/axiom; zero behavior change. Closes WS-J1 Phase A | J1-A |
| **WS-I1** | v0.15.0 | Critical testing infrastructure: 17 inter-transition invariant assertions across all 13 trace functions (R-01), mandatory Tier 2 determinism validation via `test_tier2_determinism.sh` (R-02), scenario ID traceability with 121 tagged trace lines in pipe-delimited format, scenario registry YAML with Tier 0 validation (R-03). Zero sorry/axiom. Closes R-01/R-02/R-03 | I1 |
| **WS-F8** | v0.14.9 | Cleanup: removed dead `ServiceStatus.failed`/`isolated` constructors (D1), labeled Service subsystem as seLe4n extension with module docstrings (D2/MED-17), closed F-14 (endpointInvariant already removed in WS-H12a), closed F-01 (legacy endpoint fields already removed in WS-H12a), closed MED-04 (domain lattice alive and exercised, finding misidentified). Completes 100% of v0.12.2 audit findings (33/33). Closes MED-04/MED-17/F-01/F-14/F-19 | F8 |
| **WS-F5** | v0.14.9 | Model fidelity: word-bounded `Badge` with `ofNatMasked`/`bor`/validity theorems (F5-D1/CRIT-06), order-independent `AccessRightSet` bitmask replacing list-based rights (F5-D2/HIGH-04), deferred operations documented with rationale (F5-D3/MED-03), `badgeWellFormed` invariant with `notificationBadgesWellFormed`/`capabilityBadgesWellFormed` predicates and preservation proofs for `notificationSignal`/`notificationWait`/`cspaceMint`/`cspaceMutate`. Closes CRIT-06/HIGH-04/MED-03 | F5 |
| **WS-H16** | v0.14.8 | Testing, documentation & cleanup: 10 lifecycle negative tests (M-18), 13 semantic Tier 3 assertions (A-43), `objectIndexLive` liveness invariant with preservation proof (A-13), `runQueueThreadPriorityConsistent` predicate with default theorem (A-19), O(1) membership audit confirmation (A-18), documentation metrics sync (M-21/A-45). Closes M-18/A-43/A-13/A-18/A-19/M-21/A-45 | H16 |
| **WS-H15** | v0.14.7 | Platform & API hardening: InterruptBoundaryContract decidability + consistency theorems (H15a), RPi5 MMIO disjointness/boot contract hardening (H15b), syscall capability-checking wrappers with 3 soundness theorems and 13 `api*` entry points (H15c), generic timer-invariant preservation + concrete `AdapterProofHooks` for Sim and RPi5 restrictive contracts with 6 end-to-end theorems (H15d), 31 Tier 3 anchors + 5 trace scenarios + 6 negative tests (H15e). Closes A-33/A-41/A-42/M-13 | H15a-e |
| **WS-H14** | v0.14.6 | Type safety & Prelude foundations: `EquivBEq`/`LawfulBEq` for 14 identifier types, `LawfulMonad` for `KernelM`, `isPowerOfTwo` correctness proof, identifier roundtrip/injectivity theorems, `OfNat` instance removal (type-safety enforcement), sentinel predicate completion. Closes A-01/A-02/A-03/A-04/A-06/M-09/M-10/M-11 | H14 |
| **Restructuring** | v0.14.5 | Module decomposition: 9 monolithic files (1K-5.8K lines) split into 24 focused submodules via re-export hub pattern. 15 private defs tightened after cross-module audit. 209 Tier 3 anchor checks updated. Zero sorry/axiom | Structural |
| **WS-H13** | v0.14.4 | CSpace/service model enrichment: multi-level CSpace resolution, backing-object verification, `serviceCountBounded` | H13 |
| **WS-H12f** | v0.14.3 | Test harness update & documentation sync: 3 new trace scenarios, fixture update, 9 new Tier 3 anchors | H12f |
| **WS-H12e** | v0.14.2 | Cross-subsystem invariant reconciliation: `coreIpcInvariantBundle` upgraded to `ipcInvariantFull` 3-conjunct, `schedulerInvariantBundleFull` extended to 5-tuple, 8 frame lemmas + 3 compound preservation theorems | H12e |
| **WS-H12d** | v0.14.1 | IPC message payload bounds: `IpcMessage` Array migration, `maxMessageRegisters`(120)/`maxExtraCaps`(3), 4 bounds theorems, `allPendingMessagesBounded` system invariant. Closes A-09 | H12d |
| **WS-H12c** | v0.14.0 | Per-TCB register context with inline context switch: `registerContext` field, `contextMatchesCurrent` invariant, IF projection stripping. Closes H-03 | H12c |
| **WS-H12b** | v0.13.9 | Dequeue-on-dispatch scheduler semantics matching seL4's `switchToThread`/`tcbSchedDequeue`, ~1800 lines re-proved. Closes H-04 | H12b |
| **WS-H12a** | v0.13.8 | Legacy endpoint field & operation removal | H12a |
| **WS-H11** | v0.13.7 | VSpace & architecture enrichment: PagePermissions with W^X enforcement, TLB/cache model, `VSpaceBackend` typeclass, 23 new theorems | H11 |
| **End-to-end audit** | v0.13.6 | Comprehensive codebase audit: zero critical issues, zero sorry/axiom, stale documentation metrics fixed | Audit |
| **WS-H10** | v0.13.6 | Security model foundations: `ObservableState`, BIBA lattice alternatives, `DeclassificationPolicy`, `InformationFlowConfigInvariant` | H10 |
| **WS-H9** | v0.13.4 | Non-interference coverage >80%: 27 new NI theorems, 28-constructor `NonInterferenceStep`, `composedNonInterference_trace`. Closes C-02/A-40 (CRITICAL) | H9 |
| **WS-H8** | v0.13.2 | Enforcement-NI bridge: 5 enforcement soundness meta-theorems, 4 `*Checked` wrappers. Closes A-35/H-07, A-36/A-37/H-11 | H8 |
| **WS-H7** | v0.12.21 | HashMap equality + state-store migration: order-independent `BEq`, closure-to-HashMap migration for 5 state fields | H7 |
| **WS-H6** | v0.13.1 | Scheduler proof completion: `timeSlicePositive` fully proven, EDF domain-aware fix, `schedulerInvariantBundleFull` 5-tuple | H6 |
| **WS-H5** | v0.12.19 | IPC dual-queue structural invariant: `intrusiveQueueWellFormed`, `dualQueueSystemInvariant`, 13 preservation theorems. Closes C-04/A-22..A-24 | H5 |
| **WS-H4** | v0.12.18 | Capability invariant redesign: `capabilityInvariantBundle` 7-tuple with `cspaceSlotCountBounded`, `cdtCompleteness`, `cdtAcyclicity` | H4 |
| **WS-H3** | v0.12.17 | Build/CI infrastructure: `run_check` return value fix (H-12), docs sync CI integration (M-19), Tier 3 `rg` guard (M-20) | H3 |
| **WS-H2** | v0.12.16 | Lifecycle safety guards: childId collision/self-overwrite guards, TCB scheduler cleanup, atomic retype | H2 |
| **WS-H1** | v0.12.16 | IPC call-path semantic fix: `blockedOnCall` state, reply-target scoping, 5-conjunct `ipcSchedulerContractPredicates` | H1 |
| **WS-G** | v0.12.6-v0.12.15 | Kernel performance: all hot paths migrated to O(1) hash-based structures, 14 audit findings resolved | G1-G9 + refinement |
| **WS-F1..F4** | v0.12.2-v0.12.5 | Critical audit remediation: IPC message transfer (14 theorems), untyped memory (watermark tracking), info-flow completeness (15 NI theorems), proof gap closure | F1-F4 |
| **WS-E** | v0.11.0-v0.11.6 | Test/CI hardening, proof quality, kernel hardening, capability/IPC, info-flow enforcement, completeness | E1-E6 |
| **WS-D** | v0.11.0 | Test validity, info-flow enforcement, proof gaps, kernel design | D1-D4 |
| **WS-C** | v0.9.32 | Model structure, documentation, maintainability | C1-C8 |
| **WS-B** | v0.9.0 | Comprehensive audit (2026-02) | B1-B11 |

Prior audits (v0.8.0-v0.9.32), milestone closeouts, and legacy GitBook chapters
are archived in [`docs/dev_history/`](dev_history/README.md).

## Audit plans (canonical sources)

| Plan | Scope |
|------|-------|
| [`AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md) | **WS-N** Robin Hood hashing verified implementation (5 phases) — **active** |
| [`AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.16.8_IPC_SUBSYSTEM_WORKSTREAM_PLAN.md) | **WS-L** IPC subsystem audit & remediation (5 phases) — **completed** (v0.16.13) |
| [`AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md) | WS-K full syscall dispatch completion (8 phases) — completed |
| [`AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md) | WS-J1 register-indexed authoritative namespaces (6 phases) — completed |
| [`AUDIT_v0.14.9_IMPROVEMENT_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.14.9_IMPROVEMENT_WORKSTREAM_PLAN.md) | WS-I portfolio (v0.14.9 improvement recommendations) — completed |
| [`AUDIT_CODEBASE_v0.13.6.md`](dev_history/audits/AUDIT_CODEBASE_v0.13.6.md) | End-to-end audit (v0.13.6) — completed |
| [`AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md) | WS-H portfolio (v0.12.15 audit findings) — completed |
| [`KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md`](dev_history/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md) | WS-G portfolio (performance optimization) — completed |
| [`AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md) | WS-F portfolio (v0.12.2 audit findings) — completed |
