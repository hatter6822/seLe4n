# seLe4n Development Guide

## 1) Purpose

This guide is the day-to-day operating manual for contributors.

It is aligned to the **current active slice**:

- active: **v0.11.0 WS-D execution (WS-D1 completed; WS-D2..WS-D6 planned)**,
- completed predecessor: **WS-C portfolio (WS-C1..WS-C8 completed)**,
- completed predecessor before that: **M7 remediation (WS-A1..WS-A8)**.

Canonical planning source:
[`docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md`](./audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md).

---

## 2) Non-negotiable baseline contracts

Unless a PR explicitly proposes spec-level change control, preserve:

1. deterministic transition semantics (explicit success/failure branches),
2. M3.5 IPC-scheduler handshake coherence semantics and trace anchors,
3. local + composed invariant layering,
4. theorem discoverability through stable naming,
5. fixture-backed executable evidence (`Main.lean` + trace fixture),
6. tiered validation command behavior (`test_fast`/`smoke`/`full`/`nightly`).

---

## 3) Current execution slice (WS-D portfolio)

### 3.1 Workstreams and intent

- **WS-D1** — Test error handling and validity (**completed** — F-01, F-03, F-04)
- **WS-D2** — Information-flow enforcement and proof (**planned** — F-02, F-05)
- **WS-D3** — Proof gap closure (**planned** — F-06, F-08, F-16)
- **WS-D4** — Kernel design hardening (**planned** — F-07, F-11, F-12)
- **WS-D5** — Test infrastructure expansion (**planned** — F-09, F-10)
- **WS-D6** — CI/CD and documentation polish (**planned** — F-13, F-14, F-15, F-17)

Canonical detail: [`docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md).

### 3.2 Sequencing model

Use the planning phases from the workstream backbone:

- **Phase P0:** Baseline transition — publish v0.11.0 planning backbone, demote WS-C to historical (completed)
- **Phase P1:** WS-D1 test validity restoration (critical/high) — **completed**
- **Phase P2:** WS-D2 information-flow enforcement and proof expansion (high) — current
- **Phase P3:** WS-D3 proof gap closure + WS-D4 kernel design hardening (medium)
- **Phase P4:** WS-D5 test infrastructure expansion + WS-D6 CI/documentation polish (medium/low)

### 3.3 Prior completed portfolio (WS-C, historical)

WS-C1..WS-C8 completed. See [`docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md).

### 3.4 PR-to-workstream discipline

Every milestone-moving PR should include:

1. workstream ID(s) advanced,
2. objective and exit-criterion delta,
3. command evidence,
4. synchronized docs updates (README/spec/development/GitBook as needed),
5. explicit deferrals (if any) and destination workstream.

---

## 4) Daily contributor loop

1. Sync branch and choose one coherent WS-D slice (prefer next priority in the active plan, starting with P1 blockers).
2. Implement the minimal semantic/proof/doc delta.
3. Run smallest relevant check first, then higher tiers.
4. Update docs in the same commit range.
5. Re-run validation before commit.

Recommended command loop:

```bash
./scripts/test_fast.sh
./scripts/test_smoke.sh
./scripts/test_full.sh
```

Optional nightly/staged checks:

```bash
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
```

Environment note for `./scripts/setup_lean_env.sh` on apt-based systems:

- if a third-party apt mirror is temporarily unavailable, the setup script now retries `apt-get update` with primary distro sources only so required tool installs (`shellcheck`, `ripgrep`) remain reproducible.

---

## 5) Proof engineering standards

1. Keep proofs local-first; compose afterward.
2. Prefer explicit theorem statements and stable names.
3. Keep invariant bundles factored and named.
4. Avoid hidden global simplification behavior.
5. Never add `axiom`/`sorry` to core proof surfaces.

---

## 6) Documentation synchronization rules

For changes that alter behavior, theorem surfaces, or slice status, update in the same PR:

1. `README.md`
2. `docs/spec/SELE4N_SPEC.md` (and `docs/spec/SEL4_SPEC.md` if seL4 reference material changes)
3. `docs/DEVELOPMENT.md`
4. impacted GitBook chapter(s) and `docs/gitbook/SUMMARY.md` if IA changes
5. any directly affected audit/workstream status document

Use [`docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md`](./DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md)
for cross-document synchronization expectations.

---

## 7) Definition of done (milestone-moving changes)

A change is done when all are true:

- implementation compiles,
- trace/fixture behavior is intentionally stable or intentionally updated with rationale,
- theorem/invariant surface remains coherent and discoverable,
- tiered checks pass for the claimed scope,
- docs reflect exact current state (not intended future state).

---

## 8) Quick checklist (copy into PRs)

- [ ] Workstream ID(s) identified.
- [ ] Scope is one coherent slice.
- [ ] Transition semantics are explicit and deterministic.
- [ ] Invariant/theorem updates are paired with implementation changes.
- [ ] Required validation commands were run.
- [ ] Documentation was synchronized.
