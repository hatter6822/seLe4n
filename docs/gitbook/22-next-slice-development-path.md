# Next Development Path

## Current state: WS-G portfolio completed (v0.12.14)

The WS-G kernel performance optimization portfolio is fully completed. All 14
performance findings (F-P01 through F-P14) from the v0.12.5 performance audit
have been resolved across WS-G1..G9 (v0.12.6–v0.12.14).

See [Specification & Roadmap](05-specification-and-roadmap.md) for full status.

## Phase sequence

### P1 — Critical IPC, memory, and proof gaps (WS-F1, WS-F2, WS-F4)

Three workstreams run in parallel:
- **WS-F1**: ~~Wire `IpcMessage` into operations, verify dual-queue model.~~ **COMPLETED** — messages flow through all IPC operations with 14 preservation theorems and 7 trace anchors.
- **WS-F2**: ~~Add Untyped memory with watermark tracking.~~ **COMPLETED** — `UntypedObject`, `retypeFromUntyped`, device restriction, 10+ theorems, 5 negative tests, 9 trace anchors.
- **WS-F4**: Close timerTick, cspaceMutate, notification proof gaps.

### P2 — Information-flow completeness (WS-F3) — **COMPLETED**

- ~~Extend `ObservableState` projection to all security-relevant fields.~~ Done: 3 new fields (activeDomain, irqHandlers, objectIndex).
- ~~Prove non-interference for new projection fields.~~ Done: 15 NI theorems (12 standalone + 3 enforcement-NI bridges).
- ~~Connect enforcement layer to NI theorems.~~ Done: enforcement-NI bridge for `serviceRestartChecked`.
- CNode slot filtering via `projectKernelObject` prevents capability target leakage (F-22).
- Test suite extended with WS-F3 coverage (IRQ projection, object index, CNode filtering, 7-field low-equivalence).

### P3 — Model fidelity and invariant quality (WS-F5, WS-F6)

- Notification badge bitmask, per-thread registers, multi-level CSpace.
- Reclassify tautological invariants, instantiate adapter proof hooks.

### P4 — Testing and cleanup (WS-F7, WS-F8)

- Extend runtime oracle and trace probe coverage.
- Resolve legacy/dual-queue divergence, remove dead code.

## After WS-F: Raspberry Pi 5 binding (H3)

Once WS-F closes critical proof gaps:

1. Map `MachineState` to BCM2712 hardware.
2. Bind `VSpaceRoot` to ARMv8 page tables.
3. Implement GIC-400 interrupt routing.
4. Verify boot sequence as initial state construction.
5. Run proof-carrying executable on hardware.

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
