# Next Development Path

## Current priority: Hardware binding (WS-G / H3)

All audit remediation is complete (WS-F1..F4). The immediate development path is
hardware-specific workstreams targeting Raspberry Pi 5 (ARM64, BCM2712).

See the [hardware readiness audit](../audits/AUDIT_HARDWARE_READINESS_v0.12.5.md)
for the full assessment and findings.

## Completed audit remediation (WS-F)

- **WS-F1**: IPC message transfer + dual-queue verification — **COMPLETED**
- **WS-F2**: Untyped memory model — **COMPLETED**
- **WS-F3**: Information-flow completeness — **COMPLETED**
- **WS-F4**: Proof gap closure (timerTick, cspaceMutate, notifications) — **COMPLETED**

## Hardware binding workstreams (WS-G)

| Workstream | Scope | Priority | Status |
|------------|-------|----------|--------|
| **WS-G1** | Instantiate `AdapterProofHooks` with RPi5-specific contracts | Critical | Ready |
| **WS-G2** | ARM64 register ABI + multi-level VSpace page tables | High | Ready |
| **WS-G3** | Interrupt dispatch transitions + verified boot sequence | High | Blocked on WS-G1 |
| **WS-G4** | Bounded resource pools + MMIO memory separation | Medium | Blocked on WS-G2 |

### WS-G1: AdapterProofHooks instantiation

Provide the first concrete `AdapterProofHooks` instance for RPi5 that satisfies
`RuntimeBoundaryContract` predicates for ARM Generic Timer, register context, and
memory access. This unblocks all conditional adapter preservation theorems.

### WS-G2: ARM64 platform model

1. Define ARM64 register enumeration (x0-x30, SP, PC, PSTATE, ELR_EL1, SPSR_EL1).
2. Extend `VSpaceRoot` to ARMv8 4-level page tables with permission bits (R/W/X).
3. Add TLB coherency model as runtime contract predicate.

### WS-G3: Interrupt and boot

1. Add interrupt dispatch transitions with GIC-400 routing.
2. Define boot sequence as verified state construction from BCM2712 device tree.
3. Prove boot state satisfies `apiInvariantBundle`.

### WS-G4: Resource bounds and MMIO

1. Define `MAX_OBJECTS`, `MAX_CDT_NODES`, `MAX_DEPENDENCIES` constants.
2. Partition memory model into normal/device/reserved regions.
3. Prove resource pool invariants.

## Long-horizon items

- MCS scheduling contexts (budget/period/replenishments).
- Multi-core support (per-core kernel instances).
- Device memory and IOMMU modeling.
- Cryptographic attestation of kernel image.
- Side-channel analysis at hardware binding layer.

## Related chapters

- Specification: [Specification & Roadmap](05-specification-and-roadmap.md)
- Hardware path: [Path to Real Hardware (Raspberry Pi 5)](10-path-to-real-hardware-mobile-first.md)
- Audit findings: [End-to-End Audit and Quality Gates](19-end-to-end-audit-and-quality-gates.md)
