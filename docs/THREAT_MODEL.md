# Threat Model and Security Hardening Baseline (WS-B9)

## 1) Purpose and scope

This document defines the canonical threat model for seLe4n and the baseline hardening controls
required by **WS-B9** in the Comprehensive Audit 2026-02 execution slice.

Scope includes:

- repository source and formal artifacts,
- local and CI bootstrap/update paths,
- documentation and release metadata integrity,
- baseline automated security scanning posture.

Out of scope for this phase:

- hardware runtime exploit mitigation on deployed targets,
- cryptographic attestation of generated machine code,
- full noninterference theorem closure (tracked in WS-B7+ follow-on work).

## 2) Assets and security goals

Primary assets:

1. **Formal semantics and proofs** (`SeLe4n/*`, theorem surfaces, invariants).
2. **Executable evidence artifacts** (`Main.lean`, trace fixtures, tier scripts).
3. **Supply-chain bootstrap path** (`scripts/setup_lean_env.sh`, Lean toolchain setup).
4. **Repository integrity and CI policy state** (workflows, docs/spec synchronization).

Security goals:

- preserve integrity of model/proof artifacts and milestone claims,
- reduce accidental credential leakage in repository history,
- prevent silent bootstrap-script tampering in setup flow,
- keep security scanning posture explicit and reproducible.

## 3) Threat actors and capabilities

1. **Opportunistic external attacker**
   - Can inspect public repository and submitted patches.
   - Attempts secret harvesting, malicious dependency/script injection, or CI abuse.
2. **Compromised upstream channel**
   - Delivers altered installer/bootstrap script content over trusted URLs.
3. **Accidental insider error**
   - Commits local secret files, ad-hoc scanner output, or stale policy text.
4. **Fork-origin CI constraints**
   - Security-event upload permissions unavailable for untrusted fork runs.

## 4) Trust boundaries

1. **Boundary A: Repository source ↔ contributor workstations**
   - Risk: accidental commit of local secret/config files.
   - Control: expanded `.gitignore` secret/artifact denylist.
2. **Boundary B: Local setup script ↔ external installer content**
   - Risk: tampered remote installer script.
   - Control: mandatory SHA-256 verification for downloaded elan installer before execution.
3. **Boundary C: Repository policy ↔ CI execution environment**
   - Risk: drift between documented policy and workflow behavior.
   - Control: CI policy documentation + Tier 3 anchor checks against workflow names/semantics.

## 5) Implemented WS-B9 controls

1. **Canonical threat model artifact**
   - This document (`docs/THREAT_MODEL.md`) is now the normative security-assumption ledger.
2. **Repository hygiene hardening**
   - `.gitignore` now excludes common local secret formats (`.env*`, key/cert bundles, `secrets/`) and
     scanner outputs (`.trivy/`, `trivy-report*.json`, `gitleaks-report*.json`).
3. **Bootstrap integrity verification**
   - `scripts/setup_lean_env.sh` no longer pipes remote installer content directly to shell.
   - It downloads to a temporary file, verifies `ELAN_INSTALLER_SHA256`, and aborts on mismatch.
4. **CI/security policy synchronization**
   - `docs/CI_POLICY.md` records baseline scanner controls and explains CodeQL non-blocking policy.
   - Tier 3 anchors enforce presence of threat-model and installer-checksum hardening symbols.

## 6) Residual risk and follow-on work

Residual risks accepted in this phase:

- pinned installer checksum requires manual rotation when upstream installer changes,
- no cryptographic signature verification for installer provenance yet,
- CodeQL remains informational/non-blocking due repository code-scanning availability constraints.

Follow-on work ownership:

- **WS-B10:** CI maturity policy ✅ completed (CodeQL policy and telemetry baseline codified).
- **WS-B11:** scenario framework hardening for security-tagged replay coverage.
- **Future IF slices:** formalize confidentiality/integrity guarantees against this threat model.

## 7) Validation hooks

Hardening changes are validated by the standard gates:

- `./scripts/test_fast.sh`
- `./scripts/test_full.sh`

Tier 3 invariant/document anchors additionally check for:

- threat-model publication,
- setup-script checksum verification symbols,
- synchronized active-slice status language across canonical docs.
