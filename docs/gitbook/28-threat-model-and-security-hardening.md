# Threat Model and Security Hardening

Canonical source: [`docs/THREAT_MODEL.md`](../THREAT_MODEL.md).

This chapter summarizes seLe4n's security baseline. The canonical document is normative; this chapter provides a self-contained overview for GitBook readers.

## Scope

The threat model covers:

- Repository source and formal proof artifacts
- Local and CI bootstrap/update paths
- Documentation and release metadata integrity
- Automated security scanning posture

Out of scope for the current phase: hardware runtime exploit mitigation and cryptographic attestation of generated machine code. Non-interference coverage is >80% of kernel operations with 32 `NonInterferenceStep` constructors and a 33-entry enforcement boundary; remaining operations are documented for future workstreams.

## Assets and security goals

| Asset | Security goal |
|-------|--------------|
| Formal semantics and proofs (`SeLe4n/*`) | Preserve integrity of model/proof artifacts and milestone claims |
| Executable evidence (`Main.lean`, fixtures, tier scripts) | Prevent silent semantic regression |
| Supply-chain bootstrap (`scripts/setup_lean_env.sh`) | Prevent tampering in toolchain setup flow |
| Repository integrity and CI policy | Keep security scanning posture explicit and reproducible |

## Threat actors

1. **Opportunistic external attacker** — inspects public repo, attempts secret harvesting or malicious dependency injection.
2. **Compromised upstream channel** — delivers altered installer/bootstrap content over trusted URLs.
3. **Accidental insider error** — commits local secret files, stale policy text, or ad-hoc scanner output.
4. **Fork-origin CI constraints** — security-event upload permissions unavailable for untrusted fork runs.

## Trust boundaries and controls

| Boundary | Risk | Control |
|----------|------|---------|
| **A: Repo source ↔ contributor** | Accidental secret commit | Expanded `.gitignore` denylist (`.env*`, key/cert bundles, `secrets/`, scanner outputs) |
| **B: Setup script ↔ external installer** | Tampered remote installer | SHA-256 verification of downloaded elan installer before execution |
| **C: Repo policy ↔ CI environment** | Drift between docs and workflow behavior | CI policy documentation + Tier 3 anchor checks against workflow semantics |

## Implemented controls (WS-B9)

1. **Canonical threat model** — this artifact is the normative security-assumption ledger.
2. **Repository hygiene hardening** — `.gitignore` excludes common secret formats and scanner outputs.
3. **Bootstrap integrity verification** — `setup_lean_env.sh` downloads to temp file, verifies `ELAN_INSTALLER_SHA256`, aborts on mismatch. No piping remote content directly to shell.
4. **CI/security policy sync** — `CI_POLICY.md` records scanner controls; Tier 3 anchors enforce presence of threat-model and installer-checksum hardening symbols.
5. **SHA-pinning** — all GitHub Actions workflow references use pinned commit SHAs (WS-E1 F-14).

## Residual risk

- Pinned installer checksum requires manual rotation when upstream changes.
- No cryptographic signature verification for installer provenance yet.
- CodeQL remains informational/non-blocking due to repository code-scanning constraints.

## Validation

Hardening is validated by standard test gates:

```bash
./scripts/test_fast.sh    # Tier 0+1: hygiene + build
./scripts/test_full.sh    # + Tier 3: invariant surface anchors (checks SHA-pinning, threat-model symbols)
```

## Security advisories

See [`docs/SECURITY_ADVISORY.md`](../SECURITY_ADVISORY.md) for documented
security advisories:

- **SA-1**: Starvation freedom not guaranteed (fixed-priority preemptive scheduler)
- **SA-2**: Default labeling context defeats information-flow enforcement
- **SA-3**: Scheduling covert channel (accepted by design, bounded bandwidth)

## Related

- [CI Maturity and Telemetry](29-ci-maturity-and-telemetry-baseline.md) — WS-B10 observability
- [End-to-End Audit and Quality Gates](../dev_history/gitbook/19-end-to-end-audit-and-quality-gates.md) — quality gate contract
- [Testing & CI](07-testing-and-ci.md) — tier definitions
