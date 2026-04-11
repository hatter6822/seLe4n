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
| **H4** | Evidence convergence — connect proofs to platform | Planned | H3 complete |

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

**Phase AG8 (Integration + Model Closure) is complete.** 7 sub-tasks close
remaining Lean model gaps: timeout sentinel → `timedOut : Bool` TCB field
(eliminates GPR x0 collision risk), cache coherency model (`CacheModel.lean`
with 17 preservation theorems), memory barrier semantics formalization,
FrozenOps deferred to WS-V, CDT `descendantsOf` fuel sufficiency placeholders
(substantive proofs deferred to WS-V),
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
Plan: [`AUDIT_H3_HARDWARE_BINDING_WORKSTREAM_PLAN.md`](../audits/AUDIT_H3_HARDWARE_BINDING_WORKSTREAM_PLAN.md).

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
  contracts for trace harness and test execution.
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
