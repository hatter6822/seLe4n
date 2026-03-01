# Specification & Roadmap

This chapter summarizes the project specification. For the normative document:
[`docs/spec/SELE4N_SPEC.md`](../spec/SELE4N_SPEC.md).

## Project identity

seLe4n is a **production-oriented microkernel** written in Lean 4 with
machine-checked proofs, improving on seL4 architecture. First hardware target:
**Raspberry Pi 5** (ARM64).

## Current state

| Attribute | Value |
|-----------|-------|
| Version | `0.12.12` |
| Lean toolchain | `4.28.0` |
| Production LoC | 16,485 across 34 files |
| Proved theorems | 400+ (zero sorry/axiom) |
| Active portfolio | WS-G (kernel performance optimization) — WS-G1..G7 completed |

## Milestone history

Bootstrap → M1 (scheduler) → M2 (capability) → M3/M3.5 (IPC) → M4-A/M4-B
(lifecycle) → M5 (service graph) → M6 (architecture boundary) → M7 (audit
remediation) → WS-B..E (4 audit portfolios, all completed).

## Active workstream: WS-G

The WS-G portfolio addresses kernel performance optimization findings from the
[v0.12.5 performance audit](../audits/KERNEL_PERFORMANCE_AUDIT_v0.12.5.md).

Completed:
1. **WS-G1**: ~~Typed identifier Hashable instances~~ **COMPLETED** (v0.12.6)
2. **WS-G2**: ~~Object store & ObjectIndex HashMap~~ **COMPLETED** (v0.12.7)
3. **WS-G3**: ~~ASID Resolution Table~~ **COMPLETED** (v0.12.8)
4. **WS-G4**: ~~Run queue restructure~~ **COMPLETED** (v0.12.9)
5. **WS-G5**: ~~CNode slot HashMap~~ **COMPLETED** (v0.12.10) — `Std.HashMap Slot Capability`; `HashMap.fold` for `cspaceRevoke` `revokedRefs`
6. **WS-G6**: ~~VSpace mapping HashMap~~ **COMPLETED** (v0.12.11) — `Std.HashMap VAddr PAddr`; `noVirtualOverlap` trivially true; closes F-P05
7. **WS-G7**: ~~IPC Queue Completion & Notification~~ **COMPLETED** (v0.12.12) — Legacy endpoint ops deprecated; `notificationWait` O(1) TCB check + O(1) prepend; `endpointSendDualChecked` enforcement; closes F-P04, F-P11

Prior portfolio **WS-F** (v0.12.2 audit remediation): WS-F1..F4 all **COMPLETED**.

## Hardware roadmap

H0 (neutral semantics, complete) → H1 (boundary interfaces, complete) →
H2 (proof deepening, active) → H3 (Raspberry Pi 5 binding) → H4 (evidence convergence).

See [Path to Real Hardware](10-path-to-real-hardware-mobile-first.md).

## Non-negotiable baseline contracts

1. Deterministic transition semantics (explicit success/failure).
2. IPC-scheduler handshake coherence.
3. Domain-aware scheduling (active-domain-only).
4. Local + composed invariant layering.
5. Stable theorem naming.
6. Fixture-backed executable evidence.
7. Tiered validation commands.
8. Import hygiene (`API.lean` as canonical aggregate).
