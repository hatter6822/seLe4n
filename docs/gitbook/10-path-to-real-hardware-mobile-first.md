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
| **H3** | Platform binding — Raspberry Pi 5 hardware | **H3-prep complete** | ~~WS-F1..F4~~ (done) |
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

**Remaining H3 work** (WS-H15 has now populated substantive predicates):

1. ~~Populate RPi5 runtime contract with hardware-validated predicates.~~ **DONE** (WS-H15b).
2. Implement ARMv8 multi-level page table walk as a `VSpaceBackend` instance (with `PagePermissions` support from WS-H11).
3. Implement interrupt routing for GIC-400 with IRQ acknowledgment.
4. Bind timer adapter to ARM Generic Timer (CNTPCT_EL0).
5. Define boot sequence as a verified initial state construction.

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
