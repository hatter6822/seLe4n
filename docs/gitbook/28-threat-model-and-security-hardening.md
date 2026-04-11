# Threat Model and Security Hardening Baseline (WS-B9)

Canonical source: [`docs/THREAT_MODEL.md`](../THREAT_MODEL.md).

This chapter summarizes seLe4n's security baseline. The canonical document is normative; this chapter provides a self-contained overview for GitBook readers.

## 1) Purpose and scope

The threat model covers:

- Repository source and formal proof artifacts
- Local and CI bootstrap/update paths
- Documentation and release metadata integrity
- Automated security scanning posture

Out of scope for the current phase: hardware runtime exploit mitigation and cryptographic attestation of generated machine code. Non-interference coverage is >80% of kernel operations with 35 `NonInterferenceStep` constructors and a 33-entry enforcement boundary.

## 2) Assets and security goals

| Asset | Security goal |
|-------|--------------|
| Formal semantics and proofs (`SeLe4n/*`) | Preserve integrity of model/proof artifacts and milestone claims |
| Executable evidence (`Main.lean`, fixtures, tier scripts) | Prevent silent semantic regression |
| Supply-chain bootstrap (`scripts/setup_lean_env.sh`) | Prevent tampering in toolchain setup flow |
| Repository integrity and CI policy | Keep security scanning posture explicit and reproducible |

## 3) Threat actors and capabilities

1. **Opportunistic external attacker** — inspects public repo, attempts secret harvesting or malicious dependency injection.
2. **Compromised upstream channel** — delivers altered installer/bootstrap content over trusted URLs.
3. **Accidental insider error** — commits local secret files, stale policy text, or ad-hoc scanner output.
4. **Fork-origin CI constraints** — security-event upload permissions unavailable for untrusted fork runs.

## 4) Trust boundaries

| Boundary | Risk | Control |
|----------|------|---------|
| **A: Repo source ↔ contributor** | Accidental secret commit | Expanded `.gitignore` denylist (`.env*`, key/cert bundles, `secrets/`, scanner outputs) |
| **B: Setup script ↔ external installer** | Tampered remote installer | SHA-256 verification of downloaded elan installer before execution |
| **C: Repo policy ↔ CI environment** | Drift between docs and workflow behavior | CI policy documentation + Tier 3 anchor checks against workflow semantics |

## 5) Implemented WS-B9 controls

1. **Canonical threat model** — this artifact is the normative security-assumption ledger.
2. **Repository hygiene hardening** — `.gitignore` excludes common secret formats and scanner outputs.
3. **Bootstrap integrity verification** — `setup_lean_env.sh` downloads to temp file, verifies `ELAN_INSTALLER_SHA256`, aborts on mismatch. No piping remote content directly to shell.
4. **CI/security policy sync** — `CI_POLICY.md` records scanner controls; Tier 3 anchors enforce presence of threat-model and installer-checksum hardening symbols.
5. **SHA-pinning** — all GitHub Actions workflow references use pinned commit SHAs (WS-E1 F-14).

## 6) Residual risk and follow-on work

- Pinned installer checksum requires manual rotation when upstream changes.
- No cryptographic signature verification for installer provenance yet.
- CodeQL remains informational/non-blocking due to repository code-scanning constraints.

## 7) Validation hooks

Hardening is validated by standard test gates:

```bash
./scripts/test_fast.sh    # Tier 0+1: hygiene + build
./scripts/test_full.sh    # + Tier 3: invariant surface anchors (checks SHA-pinning, threat-model symbols)
```

### Hardware speculation mitigation (AG9-F)

The HAL crate (`sele4n-hal`) includes ARMv8-A speculation barriers for
Cortex-A76 (BCM2712) Spectre v1/v2 mitigation:

| Barrier | Purpose | Deployment sites |
|---------|---------|------------------|
| **CSDB** (Conditional Speculation Dependency Barrier) | Prevents speculative execution past bounds checks | Exception class dispatch (`trap.rs`), GIC INTID validation (`gic.rs`), `speculation_safe_bound_check` generic helper |
| **SB** (Speculation Barrier) | Full speculation fence via DSB SY + ISB | Available as `barriers::sb()` for critical permission checks |
| **FEAT_CSV2** | Hardware branch predictor hardening | `has_feat_csv2()` reads `ID_AA64PFR0_EL1[59:56]` to verify Cortex-A76 CSV2 support |

The `speculation_safe_bound_check(index, bound)` helper provides a
CSDB-guarded bounds check for array accesses on speculative-execution-capable
hardware, following the ARM recommended mitigation pattern for Spectre v1.

PMU cycle counting infrastructure (`profiling.rs`) uses PMCCNTR_EL0 for WCRT
empirical validation, with `LatencyStats` accumulator for min/max/mean
profiling on physical hardware.

See [`docs/hardware_validation/speculation_barriers.md`](../hardware_validation/speculation_barriers.md)
for the full AG9-F security hardening report.

### Security advisories

See [`docs/SECURITY_ADVISORY.md`](../SECURITY_ADVISORY.md) for documented
security advisories:

- **SA-1**: Starvation freedom not guaranteed (fixed-priority preemptive scheduler)
- **SA-2**: Default labeling context defeats information-flow enforcement
- **SA-3**: Scheduling covert channel (accepted by design, bounded bandwidth)
- **SA-4**: Non-BIBA integrity model (authority-flow design; escalation denied)

### Production deployment

See [`docs/DEPLOYMENT_GUIDE.md`](../DEPLOYMENT_GUIDE.md) for the production
deployment guide covering:

- **Security model overview**: Non-BIBA integrity model (F-04), NI boundary
  scope (F-05), scheduling covert channel analysis (F-06)
- **Required configuration**: Mandatory labeling context override (F-07) with
  code example
- **Pre-deployment checklist**: 7-item verification checklist for production
  readiness

Key deployment findings from the pre-release audit (v0.25.10):

| Finding | Severity | Summary |
|---------|----------|---------|
| F-04 | HIGH | Non-BIBA integrity model — trusted-to-untrusted delegation allowed |
| F-05 | HIGH | Service orchestration outside kernel NI boundary |
| F-06 | HIGH | Scheduling covert channel &le;400 bps (accepted per seL4 precedent) |
| F-07 | MEDIUM | Default labeling context defeats IF enforcement — MUST override |

### Related

- [CI Maturity and Telemetry](29-ci-maturity-and-telemetry-baseline.md) — WS-B10 observability
- [End-to-End Audit and Quality Gates](../dev_history/gitbook/19-end-to-end-audit-and-quality-gates.md) — quality gate contract
- [Testing & CI](07-testing-and-ci.md) — tier definitions
