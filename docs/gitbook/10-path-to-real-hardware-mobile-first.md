# Path to Real Hardware (Raspberry Pi 5)

## 1. Hardware target

The first production hardware target for seLe4n is **Raspberry Pi 5** (ARM64,
Broadcom BCM2712). This is not aspirational — the kernel architecture is being
developed with this target in mind.

## 2. Why Raspberry Pi 5

1. **Practical ARM64 platform** for repeated experiments and bring-up.
2. **Realistic system profile** — interrupts, memory regions, boot sequence, DMA.
3. **Broad tooling availability** — GCC/LLVM cross-compilers, JTAG, UART debug.
4. **Accessibility** — low cost, widely available, strong community.
5. **Production-relevant** — the BCM2712 is a capable quad-core Cortex-A76.

## 3. Path stages

| Stage | Description | Status | Prerequisites |
|-------|-------------|--------|---------------|
| **H0** | Architecture-neutral semantics and proofs | **Complete** | M1–M7, WS-B..E |
| **H1** | Architecture-boundary interfaces and adapters | **Complete** | M6 |
| **H2** | Audit-driven proof deepening | **Complete** (WS-F1..F8, all findings closed) | Close CRIT/HIGH findings |
| **H3** | Platform binding — Raspberry Pi 5 hardware | **AG9 complete** (testing + validation) | ~~WS-F1..F4~~ (done) |
| **H3.5** | Hardware-binding closure (TLB/cache composition, SVC FFI, SMP) | **AN9 complete (v0.30.10)**; **WS-RC R2 complete (v0.30.11)** wired Lean ↔ Rust SVC dispatch | ~~AG9~~ (done), AN6/AN8 (done) |
| **H4** | Evidence convergence — connect proofs to platform | Planned | H3.5 complete |

### H3.5 — Hardware-binding closure (WS-AN Phase AN9, v0.30.10)

WS-AN Phase AN9 closes every hardware-binding deferred item from
`AUDIT_v0.29.0_DEFERRED.md` plus four new items surfaced by AN1-C.

- **TLB+Cache composition** (AN9-A / DEF-A-M04): substantive
  `pageTableUpdate_full_coherency` theorem.
- **`tlbBarrierComplete` substantive** (AN9-B / DEF-A-M06): bitmask
  + Bool witness on every TLB-touching path.
- **BarrierKind algebra** (AN9-C/H/I): Lean inductive + Rust
  enum mirror; `dsb osh`/`dsb oshst` for outer-shareable /
  cross-cluster ordering (DEF-A-M08, M09, R-HAL-L18, L19).
- **SuspendThread atomicity** (AN9-D / DEF-C-M04): FFI bracket via
  `interrupts::with_interrupts_disabled`.  WS-RC R2.B closes the
  Lean side: `@[export suspend_thread_inner]` now substantively
  routes into `Kernel.Lifecycle.Suspend.suspendThread` via the
  `kernelStateRef` IO.Ref instead of returning a stub.
- **SVC FFI dispatch** (AN9-F / DEF-R-HAL-L14): typed
  `SyscallArgs` + `SyscallId` + `dispatch_svc`.  WS-RC R2.B closes
  the Lean side: `@[export syscall_dispatch_inner]` is a thin
  BaseIO wrapper around the new pure `syscallDispatchFromAbi`
  entry point, which spills the FFI register values into the
  current TCB and invokes the verified `syscallEntryChecked`
  instead of returning the historical `NotImplemented = 17` stub.
- **Bounded WFE** (AN9-G / DEF-R-HAL-L17): `wfe_bounded` with
  10 ms default at 54 MHz.
- **SMP scaffolding** (AN9-J / DEF-R-HAL-L20): PSCI `cpu_on` +
  `smp.rs` secondary-core bring-up; **disabled by default** at
  v1.0.0 (`SMP_ENABLED = false`).
- **PSCI completion** (WS-SM SM1.A): full DEN0022D §5 surface
  wrapped — `cpu_off`, `affinity_info` (+ `AffinityInfoState`),
  `psci_version` (+ `PsciVersion`), `migrate_info_type` (+
  `MigrateInfoType`), `system_off` and `system_reset` (both
  `-> !`).  Every function id pinned by compile-time assertions
  to ARM SMCCC encoding (Fast call + SMC32/64 + OEN=4 + reserved
  bits clear); host-stub coverage for all wrappers in 30 unit
  tests.
- **Per-CPU data + TPIDR_EL1** (WS-SM SM1.B / closes SMP-M4):
  `PerCpuData` struct with populated `core_id` field migrated to
  `rust/sele4n-hal/src/per_cpu.rs`; `current_per_cpu()` and
  `current_core_id_from_tpidr()` accessors read TPIDR_EL1 on
  aarch64; `check_per_cpu_invariants()` boot gate verifies the
  array's slot-id consistency before the first TPIDR_EL1 write.
  Lean kernel exposure via new FFI export `ffi_current_core_id`
  and typed wrapper `Concurrency.currentCoreId : BaseIO CoreId`
  in `SeLe4n/Kernel/Concurrency/Runtime.lean`.  21 new unit tests
  in `per_cpu::tests` + 3 in `ffi::tests` + 4 back-compat tests
  in `smp::tests`.
- **Secondary-core full init** (WS-SM SM1.C / closes SMP-C2):
  `rust_secondary_main` rewritten as the full per-core boot
  sequence — `mmu::init_mmu_secondary` (with the shared per-core
  helper `init_mmu_per_core`), `boot::install_exception_vectors`
  (shared with primary's `rust_boot_main`),
  `gic::init_cpu_interface_secondary`, `timer::init_timer_secondary`
  (preserving the primary's monotonic `TICK_COUNT`), IRQ unmask,
  then `lean_secondary_kernel_main(context_id)`.  Lean side: new
  module `SeLe4n/Kernel/SecondaryEntry.lean` with
  `@[export lean_secondary_kernel_main]` placeholder
  (`pure ()` at SM1.C; SM5 replaces with per-core scheduler entry).
  Three new `build.rs` scanners pin the primary/secondary symmetry
  at the call-site level.  32 new HAL unit tests + 12 new Lean
  assertions in `SmpFoundationsSuite.lean` (surface anchors,
  marker-theorem discharges, runtime BaseIO invocation).
- **DTB cmdline + Phase 5** (WS-SM SM1.D, landed at v0.31.6):
  new module `rust/sele4n-hal/src/cmdline.rs` carries the
  self-contained DTB walker (`extract_bootargs_into` with
  fuel/depth bounds), the typed `CmdlineConfig` (`smp_enabled`,
  `smp_max_cores`), and the Phase-5 entry points
  (`parse_cmdline_from_dtb`, `apply_cmdline_and_start_smp`).
  `rust_boot_main` Phase 5 wires the parse → bring-up dispatch
  after Phase 4 (TPIDR_EL1 / IRQ enable) and before Phase 6
  (Lean kernel handoff).  Default at v0.31.6+ is
  `smp_enabled=true smp_max_cores=4` per maintainer decision #7;
  operators opt out via the kernel command line.  82 new HAL
  unit tests in `cmdline::tests` (parser branches, DTB-blob
  fixtures, MAX_BOOTARGS_LEN buffer handling) + 7 new tests
  for `smp::bring_up_secondaries_with_limit` saturation
  behaviour + 5 new tests pinning Phase 5 cmdline-helper
  resolution.  New `scan_boot_rs_phase5_uses_cmdline` build.rs
  scanner pins the Phase-5 call sites textually.  SM1.D.5
  also moved `check_per_cpu_invariants()` from Phase 4 to
  Phase 1 so const-init regressions surface at boot start.

- **Cross-core HAL completion** (WS-SM SM1.E/F/G/H, landed at
  v0.31.7): closes the SM1 Rust HAL surface so SM5+ per-core
  kernel state lands on a fully-functional cross-core HAL.
  - **SM1.E** adds IS/OS-variant broadcast TLBI primitives
    (`tlbi_*is` and `tlbi_*os` for vmalle1/vae1/aside1/vale1),
    the typed `tlbi_for_sharing(domain, op)` dispatcher with
    `SharingDomain` and `TlbInvalidation` enums, and the Lean
    typed wrapper `Architecture.tlbiForSharing` in NEW module
    `SeLe4n/Kernel/Architecture/TlbiForSharing.lean` (~330
    lines incl. tag-encoding theorems).  Mask tightened to 44
    bits per ARM ARM C6.2.311 (audit-pass-1) so adversarial
    vaddrs ≥ 2^56 cannot pollute the RES0/TTL field.  FFI
    boundary panics on unknown tags (audit-pass-1 fail-closed);
    Lean wrapper proves panic is unreachable via
    `tlbiForSharing_ffi_args_in_range` (audit-pass-3).
  - **SM1.F** adds GICD_SGIR-based SGI send primitives
    (`send_sgi`, `send_sgi_to_self`, `send_sgi_to_all_but_self`)
    each emitting `dsb ish` BEFORE the SGIR write per ARM ARM
    B2.7.5 (pinned by NEW build-script scanner
    `scan_gic_rs_send_sgi_emits_dsb_ish`).  SGI handler dispatch
    infrastructure (`SgiHandler` type, `SGI_HANDLERS` table,
    `register_sgi_handler`, `lookup_sgi_handler`, `dispatch_sgi`,
    `iar_source_cpu`).  Lean FFI bindings for each send variant.
    Audit-pass-1 refactored to testable `_in`-form helpers
    taking explicit slices so tests don't race on global state.
  - **SM1.G** audits the `UartLock` for SMP correctness
    (Acquire/Release semantics + per-acquire DAIF mask) and
    adds `kprintln_core!` / `kprint_core!` macros that prefix
    each line with `[core N]` from TPIDR_EL1.  Audit-pass-1
    fixed the macro to hold the lock for the entire formatted
    line (was non-atomic in the pre-audit form).
  - **SM1.H** wires three QEMU SMP integration tests into the
    tier-4 nightly slot (full `-smp 4` bringup, minimal `-smp 2`
    smoke, cross-core SGI round-trip) — all SKIP cleanly when
    no kernel ELF binary is available (which is the SM1.H
    state; kernel binary target lands at SM5+).
  - **Audit-pass-2/3 additions**: `init_cpu_interface_secondary`
    now writes all FOUR banked distributor registers
    (IGROUPR0, IPRIORITYR0..7, ICPENDR0, ISENABLER0) in the
    canonical GIC-400 TRM §3.1.1 Table 3-1 order, mirroring
    the primary's `init_distributor`.  Without per-core
    distributor init, SGIs sent to secondaries would stay
    pending forever and timer PPIs would never fire.
  - **Test coverage**: 531 HAL tests (was 425 pre-SM1.E; +106
    new tests across tlb.rs, gic.rs, ffi.rs, uart.rs after
    three audit passes).  Lean-side: +20 surface anchors + 13
    decidable examples + 18 runtime assertions in
    `tests/SmpFoundationsSuite.lean`.  Zero clippy warnings
    workspace-wide.

- **Miscellaneous HAL improvements** (WS-SM SM1.I, landed at
  v0.31.8): completes the SM1 Rust HAL with the SM5 landing
  seams + cross-core test infrastructure.  **WS-SM SM1 CLOSED
  at v0.31.8** with all nine sub-phases LANDED (SM1.A–SM1.I,
  61 total sub-tasks).
  - **SM1.I.1** adds `trap.rs::handle_irq_per_core` as the SM5
    landing seam: reads TPIDR_EL1, records per-core IRQ /
    timer-tick / SGI stats via `per_cpu_stats::record_*`, then
    dispatches via `gic::dispatch_irq` with per-core attribution
    in the unhandled-INTID log line.  SM5 swaps the assembly
    entry vector to this function; both share an identical
    `extern "C" fn(&mut TrapFrame)` signature.  New build-script
    scanner `scan_trap_rs_handle_irq_per_core_intact` pins four
    contract properties.
  - **SM1.I.2** documents GICC_PMR per-core banking (per
    GIC-400 TRM §4.4.2 / §3.1.4) and DAIF.I per-PE scoping
    (per ARM ARM C5.2.5) in `gic.rs` + `interrupts.rs`.  The
    kernel has two layers of per-core IRQ masking, both
    inherently per-PE.
  - **SM1.I.3** adds idle-wait primitives at three layers —
    Rust (`cpu::idle_wait`, `cpu::idle_wait_bounded`), FFI
    (`ffi_idle_wait`, `ffi_idle_wait_bounded`), Lean
    (`Concurrency.idleWait`, `Concurrency.idleWaitBounded`).
  - **SM1.I.4** introduces `per_cpu_stats.rs` (~550 LoC) with
    `PerCpuStats` (`#[repr(C, align(64))]` cache-line aligned,
    six AtomicU64 counters: irq, timer-tick, sgi, syscall,
    vmfault, user-exception).  Write path wired into
    `handle_irq_per_core` (SM1.I.1) and
    `handle_synchronous_exception` per EC branch.  Read path
    via FFI (`ffi_per_core_*_count`) and Lean
    (`Concurrency.perCore*Count`).
  - **SM1.I.5** documents the SEV / WFE coordination
    semantics (ARM ARM B2.10 / C6.2.353 / C6.2.243 / C6.2.244)
    in `cpu.rs` module header.  Plus new `cpu::sev()` and
    `cpu::sevl()` wrappers for testability.
  - **SM1.I.6** adds 8 cross-core test scenarios in
    `smp::tests::sm1i6_*` exercising the SM1.I infrastructure.
  - **Audit-pass-1** refinements: two pre-existing parallel-test
    races fixed (UART_LOCK observation via re-acquire pattern;
    TIMER_INTERVAL / TICK_COUNT via private `Mutex`); stress
    testing confirms failure rate drops from ~10–15% to 0%.
  - **Test coverage**: 583 HAL tests at initial-landing snapshot (was 510 at SM1.E/F/G/H
    close; +73 SM1.I tests).  Lean-side: +12 surface anchors +
    runtime decidable examples.  Zero clippy warnings
    workspace-wide.

The **runtime** validation that complements these static guarantees
(QEMU virt boots, RPi 5 silicon validation) is documented in
[`docs/HARDWARE_TESTING.md`](../HARDWARE_TESTING.md) with step-by-step
procedures for each AN9 sub-task.  Setup is automated by
`scripts/hardware_test_env_setup.sh`.

### H2 — Proof deepening (critical gaps resolved)

All critical/high-priority audit findings are resolved by WS-F1..F4:

- ~~**IPC message transfer** (CRIT-01)~~: **RESOLVED** (WS-F1) — 14 preservation theorems.
- ~~**Untyped memory** (CRIT-04)~~: **RESOLVED** (WS-F2) — `UntypedObject` with watermark, `retypeFromUntyped`, device restriction.
- ~~**Information flow** (CRIT-02/03)~~: **RESOLVED** (WS-F3) — 15 NI theorems, CNode slot filtering.
- ~~**Dual-queue verification** (CRIT-05)~~: **RESOLVED** (WS-F1) — dual-queue invariant proofs.

All audit findings (WS-F1..F8) are resolved. WS-J1 (typed register decode layer)
and WS-K (full syscall dispatch) are also complete, providing the typed
user-space-to-kernel boundary that H3 will bind to hardware registers.

### H3 — In progress: Raspberry Pi 5 binding

**WS-AJ PORTFOLIO COMPLETE (v0.28.1–v0.29.0).** Post-audit remediation
of the v0.28.0 comprehensive audit — 6 phases (AJ1–AJ6), 30 sub-tasks.
AJ1: IPC & Lifecycle Correctness (6 sub-tasks). AJ2: Security & Information
Flow Hardening (4 sub-tasks). AJ3: Platform & Boot Pipeline (6 sub-tasks).
AJ4: Architecture Model Correctness (4 sub-tasks). AJ5: Rust HAL Hardening
(4 sub-tasks). AJ6: Documentation, Testing & Closure (6 sub-tasks) —
Hardware Integration Roadmap §8.15 (H-01/H-02/H-03 activation plans),
by-design annotations, audit errata, deferred annotations, version bump
to v0.29.0.

**WS-AI Portfolio COMPLETE (v0.28.0).** 7 phases, 37 sub-tasks addressing all
60 findings from the v0.27.6 comprehensive audit (5 HIGH, 27 MEDIUM, 28 LOW).
Key fixes: unconditional EOI on interrupt dispatch (AI2-A), `handleYield`
PIP-aware re-enqueue (AI3-A), SchedContext donation leak prevention (AI4-A),
substantive simulation contracts (AI5-A/B), insecure labeling context guard
(AI5-C), Rust trap error codes (AI1-A), UART synchronization (AI1-D).
Phase AI7 performed final closure: CBS truncation tolerance documentation
(L-17), `lifecycleRetypeObject` visibility rationale (L-26), fixture
verification, version bump to 0.28.0, and full regression gate.

**Phase AG8 (Integration + Model Closure) is complete.** 7 sub-tasks close
remaining Lean model gaps: timeout sentinel → `timedOut : Bool` TCB field
(eliminates GPR x0 collision risk), cache coherency model (`CacheModel.lean`
with 17 preservation theorems), memory barrier semantics formalization,
FrozenOps production-promotion deferred to post-1.0 hardening,
CDT `descendantsOf` fuel sufficiency placeholders
(substantive proofs deferred to post-1.0 hardening),
donation owner blocked-on-reply extraction (`donationChainAcyclic_general`),
and donation atomicity under interrupt disable with symmetric machine state
preservation (`donateSchedContext_machine_eq` + `returnDonatedSchedContext_machine_eq`).

**Phase AG7 (FFI Bridge + Proof Hooks) is complete.** 6 sub-tasks provide the
Lean-to-Rust FFI bridge with `@[extern]` declarations for 17 HAL functions,
MMIO volatile primitives, and production `AdapterProofHooks` with substantive
(non-vacuous) preservation proofs for all 4 adapter paths. `proofLayerInvariantBundle`
extended to 11 conjuncts.

**Phase AG6 (Memory Management) is complete.** 9 sub-tasks implement ARMv8
4-level page table walk with shadow-based refinement proofs, ASID management
with uniqueness invariant, TLB/cache maintenance HAL wrappers.

**Phase AG5 (Interrupts + Timer) is complete.** 7 sub-tasks connect hardware
interrupts to the Lean kernel model. Rust HAL: full GIC-400 driver with
distributor/CPU interface initialization, acknowledge/dispatch/EOI sequence
(`dispatch_irq<F>()` generic handler), and `init_gic()` convenience function
(14 tests). ARM Generic Timer driver with system register accessors, `AtomicU64`
state, `init_timer(tick_hz)` at 54 MHz, `reprogram_timer()` with counter-relative
advancement (8 tests). Interrupt management via DAIF register: `disable_interrupts`,
`restore_interrupts`, `enable_irq`, `with_interrupts_disabled<F,R>()` (4 tests).
Lean: `TimerInterruptBinding` with `handleTimerInterrupt` (acknowledge → timerTick →
reprogram), `MachineState.interruptsEnabled` field with 7 frame theorems, AG5-G
atomicity proofs in `ExceptionModel.lean`, `handleInterrupt` as 35th
`KernelOperation` with NI step and cross-subsystem bridge. Boot sequence updated
with GIC → timer → IRQ enable phase.

**Phase AG4 (HAL Crate + Boot Foundation) is complete.** 7 sub-tasks created the
first hardware-executable code: the `sele4n-hal` Rust crate (4th workspace crate)
with ARM64 boot sequence, PL011 UART driver (0xFE201000, 115200 8N1), MMU
initialization (identity-mapped L1 block descriptors), exception vector table
(16 entries, 2048-byte aligned for VBAR_EL1), trap entry/exit assembly (272-byte
TrapFrame with full GPR save/restore), and kernel linker script (0x80000 entry).

**Phase AG3 (Platform Model Completion) is complete.** 8 sub-tasks closed all
Lean model gaps blocking hardware bring-up: `classifyMemoryRegion` platform
classification (P-01), `applyMachineConfig` full field application (P-04),
ARM64 exception model with ESR classification (FINDING-04), GIC-400 interrupt
dispatch (FINDING-06), 54 MHz hardware timer model (FINDING-08), EL0/EL1
exception level model (H3-ARCH-05), system register file with frame lemmas
(H3-ARCH-06), and VSpaceBackend HashMap instance (H3-ARCH-10).

**Phase AG1 (Pre-Hardware Lean Code Fixes) is complete.** 6 sub-tasks resolved
scheduler priority insertion bugs, timeout diagnostics, `uniqueWaiters`,
boot duplicate detection, frozen replenish queue, and runtime checks.
Plan: [`AUDIT_H3_HARDWARE_BINDING_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_H3_HARDWARE_BINDING_WORKSTREAM_PLAN.md).

**H3-prep (structural foundation) is complete.** The `Platform/` directory
provides the organizational infrastructure for hardware binding:

- **`PlatformBinding` typeclass** (`SeLe4n/Platform/Contract.lean`) — formal
  interface bundling `MachineConfig`, `RuntimeBoundaryContract`,
  `BootBoundaryContract`, and `InterruptBoundaryContract`.
- **`MachineConfig` and `MemoryRegion`** (`SeLe4n/Machine.lean`) — platform-
  declared register width, address width, page size, ASID limits, and physical
  memory map with RAM/device/reserved regions.
- **`VSpaceBackend` class** (`SeLe4n/Kernel/Architecture/VSpaceBackend.lean`) —
  abstract page map/unmap/lookup with round-trip correctness obligations and
  per-page permissions support (WS-H11).
  The `VSpaceRoot` satisfies this via `hashMapVSpaceBackend` (WS-G6/WS-H11).
- **TLB model** (`SeLe4n/Kernel/Architecture/TlbModel.lean`) —
  abstract `TlbState` with `adapterFlushTlb`/`adapterFlushTlbByAsid` operations
  and `tlbConsistent` invariant (WS-H11). Ready for ARM ISB/DSB barrier binding.
- **`ExtendedBootBoundaryContract`** — adds entry exception level, MMU state,
  device tree location, entry point, and stack pointer to the base boot contract.
- **Simulation platform** (`Platform/Sim/`) — `SimPlatform` with permissive
  runtime contract for trace harness and test execution. Boot contract validates
  empty initial object store and capability refs (AI5-A). Interrupt contract
  restricts IRQs to GIC-400 INTID range 0–223 (AI5-B).
- **RPi5 platform contracts** (`Platform/RPi5/`) — BCM2712 memory map, GIC-400
  base addresses, ARM Generic Timer frequency, PL011 UART address, ARM64
  machine config (64-bit registers, 48-bit VA, 44-bit PA, 4 KiB pages,
  16-bit ASID), and substantive runtime/boot/interrupt contracts:
  - **Runtime:** SP-preservation-or-context-switch register stability (not `True`),
    RAM-only memory access, timer monotonicity.
  - **Boot:** Empty initial object store and capability ref table (not `True`).
  - **Interrupt:** GIC-400 INTID 0–223 range validation with handler mapping
    requirement. `Decidable` instances for all predicates (WS-H15a).
  - **MMIO:** Disjointness proof (`mmioRegionDisjoint_holds`) for UART, GIC
    distributor, and GIC CPU interface regions vs. RAM.
  - **MachineConfig:** Well-formedness proof (`rpi5MachineConfig_wellFormed`).
  - **AdapterProofHooks:** Concrete instantiation for restrictive contract
    (`rpi5RestrictiveAdapterProofHooks`) with end-to-end preservation theorems
    (WS-H15d).

**WS-S Phase S6 — Hardware Preparation** (v0.19.5, COMPLETE):

- **TLB flush enforcement (S6-A/B):** Production API dispatch paths
  (`vspaceMap`, `vspaceUnmap`) now use `WithFlush` variants that integrate
  TLB invalidation. Unflushed variants documented as internal proof helpers.
- **Memory scrubbing (S6-C/D):** `scrubObjectMemory` zeros backing memory
  on `lifecycleRetypeWithCleanup`, preventing inter-domain information leakage.
  Preservation proofs for lifecycle invariants (trivial — only `machine.memory`
  changes).
- **NI for scrubbing (S6-E):** `scrubObjectMemory_preserves_lowEquivalent`
  proves non-interference is maintained when scrubbing non-observable targets.
- **Device tree abstraction (S6-F/X4-A/B/C):** `Platform/DeviceTree.lean` defines a
  platform-independent `DeviceTree` structure. `rpi5DeviceTree` constructs
  an instance from Board.lean constants. `DeviceTree.fromDtbFull` implements
  full FDT parsing with generic device node traversal (`parseFdtNodes`),
  GIC-400 interrupt controller discovery (`extractInterruptController`), and
  timer frequency extraction (`extractTimerFrequency`).
- **BCM2712 validation (S6-G):** All RPi5 address constants cross-referenced
  against BCM2712 documentation and ARM specifications. Validation results
  documented in Board.lean.
- **Testing + Validation (AG9):** QEMU integration testing
  (`scripts/test_qemu.sh`), hardware constant cross-check
  (`scripts/test_hw_crosscheck.sh` validating Board.lean constants against
  physical RPi5), WCRT empirical measurement via PMU cycle counter
  (`profiling.rs`), Badge Nat↔UInt64 overflow validation (22 Lean + 7 Rust
  tests), ARMv8 speculation barriers (CSDB/SB for Spectre v1/v2,
  `has_feat_csv2()` for Spectre v2 hardware check), and full RPi5 test suite
  orchestration (`scripts/test_hw_full.sh`). Hardware validation documentation
  at `docs/hardware_validation/`.

**H3 Hardware Binding — COMPLETE** (WS-AG AG1–AG10, v0.26.0–v0.27.1):

1. ~~Populate RPi5 runtime contract with hardware-validated predicates.~~ **DONE** (WS-H15b).
2. ~~Implement ARMv8 multi-level page table walk as a `VSpaceBackend` instance.~~ **DONE** (AG6-A/B/C/D: 4-level page table walk, shadow refinement, VSpaceBackend instance).
3. ~~Implement interrupt routing for GIC-400 with IRQ acknowledgment.~~ **DONE** (AG5-A/B/C: full GIC-400 driver with distributor/CPU interface init, acknowledge/dispatch/EOI).
4. ~~Bind timer adapter to ARM Generic Timer (CNTPCT_EL0).~~ **DONE** (AG5-D/E: timer driver + `timerTick` binding).
5. ~~Define boot sequence as a verified initial state construction.~~ **DONE** (AG4-E: boot.S/boot.rs assembly→Rust boot sequence).
6. ~~Implement DTB parsing in `DeviceTree.fromDtb`.~~ **DONE** (X4-A/B/C: full FDT node traversal, GIC discovery, timer extraction).
7. ~~AG9: Testing + Validation.~~ **DONE** (v0.27.0: QEMU integration, hardware cross-check, WCRT profiling, Badge overflow validation, speculation barriers, full RPi5 test suite).
8. ~~AG10: Documentation + Closure.~~ **DONE** (v0.27.1: SELE4N_SPEC.md Hardware Binding chapter, Architecture Assumptions update, multi-core limitation docs, IPC buffer alignment docs, codebase map regeneration, full documentation sync). **WS-AG PORTFOLIO COMPLETE.**

### H4 — Planned: evidence convergence

1. Connect executable trace scenarios to hardware test fixtures.
2. Extend Tier-3 anchors to cover platform-specific claims.
3. Run proof-carrying executable on actual Raspberry Pi 5 hardware.

## 4. Risks and mitigations

| Risk | Mitigation |
|------|------------|
| Premature platform lock-in | Architecture-neutral proofs are preserved; H3 is additive |
| Proof complexity at binding boundary | Narrow adapter contracts, local-first layering |
| Lean 4 code generation gaps | Monitor Lean compiler improvements; fallback to FFI where needed |
| Hardware-specific timing channels | Document as residual risk; address in post-H4 work |

## 5. What contributors can do now

- Review the `Platform/RPi5/` stubs and contribute hardware-specific knowledge.
- Keep kernel transitions architecture-neutral — hardware assumptions belong in
  `PlatformBinding` instances, not in `Kernel/` modules.
- Document hardware assumptions explicitly in adapter interfaces.
- Add executable evidence for boundary success/failure behavior.
- When working on platform-specific code, instantiate the `PlatformBinding`
  typeclass rather than hard-coding contracts.
