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
| Version | `0.12.5` |
| Lean toolchain | `4.28.0` |
| Production LoC | 19,483 across 34 files |
| Proved theorems | 522 (zero sorry/axiom) |
| Hardware readiness | H2 complete, H3 ready to begin |
| Completed portfolios | WS-F (v0.12.2), WS-E (v0.11.6), WS-D, WS-C, WS-B |

## Milestone history

Bootstrap → M1 (scheduler) → M2 (capability) → M3/M3.5 (IPC) → M4-A/M4-B
(lifecycle) → M5 (service graph) → M6 (architecture boundary) → M7 (audit
remediation) → WS-B..E (4 audit portfolios) → WS-F (v0.12.2 audit remediation,
all 4 critical workstreams completed).

## Next: Hardware binding (WS-G)

All audit remediation is complete. The project is now preparing for H3 (Raspberry Pi 5
platform binding). Planned workstreams:

| Workstream | Scope | Priority |
|------------|-------|----------|
| **WS-G1** | Instantiate `AdapterProofHooks` with RPi5-specific contracts | Critical |
| **WS-G2** | ARM64 register ABI + multi-level VSpace page tables | High |
| **WS-G3** | Interrupt dispatch transitions + verified boot sequence | High |
| **WS-G4** | Bounded resource pools + MMIO memory separation | Medium |

See [Path to Real Hardware](10-path-to-real-hardware-mobile-first.md) and
[hardware readiness audit](../audits/AUDIT_HARDWARE_READINESS_v0.12.5.md).

## Hardware roadmap

H0 (complete) → H1 (complete) → H2 (complete) → **H3 (ready to begin)** → H4 (planned).

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
