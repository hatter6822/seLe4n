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
| **H2** | Audit-driven proof deepening | **Complete** | WS-F1..F4 all closed |
| **H3** | Platform binding — Raspberry Pi 5 hardware | **Ready to begin** | H2 complete |
| **H4** | Evidence convergence — connect proofs to platform | Planned | H3 complete |

### H2 — Complete: audit proof gaps closed (WS-F)

All critical findings from the v0.12.2 audits have been resolved:

- **IPC message transfer** (CRIT-01, CRIT-05): **RESOLVED** (WS-F1) — `IpcMessage` wired into all dual-queue and compound IPC operations; 14 preservation theorems.
- **Untyped memory** (CRIT-04): **RESOLVED** (WS-F2) — `UntypedObject` with watermark, `retypeFromUntyped`, device restriction.
- **Information flow** (CRIT-02/03): **RESOLVED** (WS-F3) — 15 NI theorems, CNode slot filtering, 7-field state projection.
- **Proof gaps** (F-03, F-06, F-12): **RESOLVED** (WS-F4) — `timerTick`, `cspaceMutate`, notification preservation.

The [hardware readiness audit](../audits/AUDIT_HARDWARE_READINESS_v0.12.5.md) confirms
522 machine-checked theorems, zero sorry/axiom, and all four test tiers passing.

### H3 — Ready: Raspberry Pi 5 binding (WS-G)

The following workstreams are planned for H3:

| Workstream | Scope | Priority |
|------------|-------|----------|
| **WS-G1** | Instantiate `AdapterProofHooks` with RPi5-specific contracts | Critical |
| **WS-G2** | ARM64 register ABI mapping + multi-level VSpace page tables | High |
| **WS-G3** | Interrupt dispatch transitions + verified boot sequence | High |
| **WS-G4** | Bounded resource pools + MMIO memory separation | Medium |

Concrete tasks:
1. Map `MachineState` to BCM2712 register set and memory map.
2. Bind `VSpaceRoot` to ARMv8 4-level page table structures with permission bits.
3. Implement interrupt routing for GIC-400.
4. Bind timer adapter to ARM Generic Timer.
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

- Begin WS-G1: implement a proof-carrying `AdapterProofHooks` instance for RPi5.
- Begin WS-G2: define ARM64 register enumeration and multi-level page tables.
- Keep core transitions architecture-neutral; hardware specifics go in new adapter modules.
- Document hardware assumptions explicitly in adapter interfaces.
- Add executable evidence for boundary success/failure behavior.

## 6. Hardware readiness evidence

- Hardware readiness audit: [`docs/audits/AUDIT_HARDWARE_READINESS_v0.12.5.md`](../audits/AUDIT_HARDWARE_READINESS_v0.12.5.md)
- 522 machine-checked theorems, zero sorry/axiom
- All 4 test tiers pass (Tier 0-4, including nightly determinism probes)
- Architecture boundary layer: 5 enumerated assumptions, 3 typed contracts, 3 runtime adapters
- Composed 7-conjunct invariant bundle with default-state base case
