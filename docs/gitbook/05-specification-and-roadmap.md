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
| Version | `0.34.50` |
| Lean toolchain | `v4.28.0` |
| Production LoC | refresh via `scripts/generate_codebase_map.py` (regenerated each phase) |
| Test LoC | refresh via `scripts/generate_codebase_map.py` (regenerated each phase) |
| Proved declarations | refresh via `scripts/generate_codebase_map.py` (zero sorry/axiom maintained) |
| Latest audit | [`AUDIT_v0.30.11_COMPREHENSIVE`](../audits/AUDIT_v0.30.11_COMPREHENSIVE.md) + [`AUDIT_v0.30.11_DEEP_VERIFICATION`](../audits/AUDIT_v0.30.11_DEEP_VERIFICATION.md) — pre-1.0 readiness audit cut after WS-AN closure. Remediation plan: [`AUDIT_v0.30.11_WORKSTREAM_PLAN`](../audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md) (WS-RC, 15 phases R0..R14). Plan-author errata: [`AUDIT_v0.30.11_ERRATA.md`](../audits/AUDIT_v0.30.11_ERRATA.md) (E-1 DEEP-ARCH-01 verification rationale corrected; E-2 DEEP-ARCH-02 consumer count corrected; E-3 DEEP-RUST-01/02 partial-verification clarification; E-4 plan-internal corrections). WS-AN remediation artefacts archived: [`AUDIT_v0.30.6_COMPREHENSIVE`](../dev_history/audits/AUDIT_v0.30.6_COMPREHENSIVE.md). Discharge index: [`AUDIT_v0.30.6_DISCHARGE_INDEX.md`](../dev_history/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md). Predecessor (also archived): [`AUDIT_v0.29.0_COMPREHENSIVE`](../dev_history/audits/AUDIT_v0.29.0_COMPREHENSIVE.md), [`AUDIT_v0.29.0_ERRATA.md`](../dev_history/audits/AUDIT_v0.29.0_ERRATA.md), [`AUDIT_v0.29.0_DEFERRED.md`](../dev_history/audits/AUDIT_v0.29.0_DEFERRED.md) (14/15 RESOLVED at WS-AN closure). |
| Active workstream | **WS-RR (SMP release readiness)** — pre-SM10 remediation, RR0–RR6 landed. SM10 (release closure → v1.0.0) is blocked on it. **WS-LC (lock datatype completion)** runs ahead of RR7: LC1 landed at v0.34.50 |
| Registered debt | [`docs/REGISTERED_DEBT.md`](../REGISTERED_DEBT.md) |
| Metrics source of truth | [`docs/codebase_map.json`](../../docs/codebase_map.json) (`readme_sync` key) |


## Roadmap

| Stage | What it delivers | Status |
|-------|------------------|--------|
| SM0–SM9 | SMP foundations, HAL bring-up, verified locks, per-object locking, per-core scheduling, cross-core IPC, TLB shootdown, SMP information flow, declassification | landed |
| WS-RR | Pre-SM10 remediation: aarch64 compile coverage, live-path invariants, `ipcInvariantFull` de-threading, fault IPC, boot-path fail-open closure, lock-primitive completion, medium sweep | RR0–RR6 landed; RR7–RR8 open |
| WS-LC | The two SM2.C lock **datatype** residuals: a queued core may withdraw its request, and lock-delay bounds gain a time denomination. Scoped ahead of RR7, whose fine-lock migration needs unwindable footprints | LC1 landed (v0.34.50); LC2–LC4 open |
| SM10.1 | The bootable image: a `[[bin]]`, aarch64 Lean object code, bare-metal runtime hosting, `lean_kernel_main` | blocked on WS-RR |
| SM10.2–SM10.6 | Documentation sweep, hardware validation, spec closure, archive, tag | after SM10.1 |
| v1.0.0 | A bootable verified SMP microkernel on Raspberry Pi 5 | the release |

Per-phase schedules are in [`docs/planning/`](../planning/); the master
overview is
[`SMP_MULTICORE_COMPLETION_PLAN.md`](../planning/SMP_MULTICORE_COMPLETION_PLAN.md).

## Milestone record

A roadmap says where the project is going; it is not the place to record where
it has been. Every merged PR ships its own version and its own
[`CHANGELOG.md`](../../CHANGELOG.md) entry — that is the milestone record, and
it is complete. Deferred items with their owners are in
[`REGISTERED_DEBT.md`](../REGISTERED_DEBT.md).

## Hardware roadmap

H0 (neutral semantics, complete) → H1 (boundary interfaces, complete) →
H2 (proof deepening, complete) → H3 (Raspberry Pi 5 binding, complete —
WS-AG AG1–AG10) → H4 (evidence convergence, in progress via WS-SM SM10).

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
