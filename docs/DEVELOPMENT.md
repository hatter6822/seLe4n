# seLe4n Development Guide

## 1) Purpose

This guide is the day-to-day operating manual for contributors.

It is aligned to the **current active slice**:

- active: **Comprehensive Audit v0.9.32 WS-C execution kickoff (Phase P0/P1 transition; execution beginning on current workstreams)**,
- completed predecessor: **M7 remediation (WS-A1..WS-A8)**,
- completed predecessor before that: **M6 architecture-boundary hardening**.

Canonical planning source:
[`docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md`](./audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md).

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

## 3) Current execution slice (WS-C portfolio)

### 3.1 Workstreams and intent

- **WS-C1** — IPC handshake correctness (**execution beginning**)
- **WS-C2** — scheduler semantic fidelity (**queued after initial blockers**)
- **WS-C3** — proof-surface de-tautologization (**execution beginning**)
- **WS-C4** — test validity hardening (**execution beginning**)
- **WS-C5** — information-flow assurance (**Phase P2 target**)
- **WS-C6** — CI and supply-chain hardening (**Phase P3 target**)
- **WS-C7** — model structure and maintainability (**Phase P3 target**)
- **WS-C8** — documentation/GitBook consolidation (**in progress**)

### 3.2 Sequencing model

Use the planning phases from the workstream backbone:

- **Phase P0:** WS-C8 baseline reset/documentation synchronization (in progress)
- **Phase P1:** WS-C1, WS-C3, core WS-C2 work, and WS-C4 fixture repairs (execution beginning)
- **Phase P2:** WS-C5 + remaining WS-C4 assurance expansion
- **Phase P3:** WS-C6 + WS-C7 sustainability hardening

### 3.3 PR-to-workstream discipline

Every milestone-moving PR should include:

1. workstream ID(s) advanced,
2. objective and exit-criterion delta,
3. command evidence,
4. synchronized docs updates (README/spec/development/GitBook as needed),
5. explicit deferrals (if any) and destination workstream.

---

## 4) Daily contributor loop

1. Sync branch and choose one coherent WS-C slice (prefer next priority in the active plan, starting with P1 blockers).
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
2. `docs/SEL4_SPEC.md`
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
