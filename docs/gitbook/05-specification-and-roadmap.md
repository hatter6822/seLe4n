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
| Version | `0.12.3` |
| Lean toolchain | `4.28.0` |
| Production LoC | 16,485 across 34 files |
| Proved theorems | 400+ (zero sorry/axiom) |
| Active portfolio | WS-F (v0.12.2 audit remediation) — WS-F1 completed |

## Milestone history

Bootstrap → M1 (scheduler) → M2 (capability) → M3/M3.5 (IPC) → M4-A/M4-B
(lifecycle) → M5 (service graph) → M6 (architecture boundary) → M7 (audit
remediation) → WS-B..E (4 audit portfolios, all completed).

## Active workstream: WS-F

The WS-F portfolio addresses v0.12.2 audit findings (6 CRIT, 6 HIGH, 12 MED, 9 LOW).

Critical priorities:
1. **WS-F1**: ~~IPC message transfer + dual-queue verification~~ **COMPLETED**
2. **WS-F2**: Untyped memory model
3. **WS-F3**: Information-flow completeness
4. **WS-F4**: Proof gap closure

See [v0.12.2 Audit Workstream Planning](24-comprehensive-audit-2026-workstream-planning.md).

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
