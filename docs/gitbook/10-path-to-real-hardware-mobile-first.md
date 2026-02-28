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
| **H2** | Audit-driven proof deepening | **Active** (WS-F) | Close CRIT/HIGH findings |
| **H3** | Platform binding — Raspberry Pi 5 hardware | Planned | WS-F2 (Untyped memory), WS-F3 (info-flow) |
| **H4** | Evidence convergence — connect proofs to platform | Planned | H3 complete |

### H2 — Active: closing proof gaps (WS-F)

The v0.12.2 audits identified critical gaps that must be closed before hardware
binding is meaningful:

- **IPC message transfer** (CRIT-01): operations must actually move data.
- **Untyped memory** (CRIT-04): memory safety is fundamental to hardware binding.
- **Information flow** (CRIT-02/03): complete projection and NI coverage.
- **Dual-queue verification** (CRIT-05): the production IPC model needs proofs.

### H3 — Planned: Raspberry Pi 5 binding

Once WS-F closes the critical proof gaps:

1. Map `MachineState` to BCM2712 register set and memory map.
2. Bind `VSpaceRoot` to ARMv8 page table structures.
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

- Focus on WS-F workstreams (especially WS-F1, WS-F2, WS-F4).
- Keep transitions architecture-neutral unless explicitly marked otherwise.
- Document hardware assumptions explicitly in adapter interfaces.
- Add executable evidence for boundary success/failure behavior.
