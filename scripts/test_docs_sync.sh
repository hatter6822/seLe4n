#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

python3 "${SCRIPT_DIR}/generate_doc_navigation.py"

before_hashes="$(sha256sum docs/gitbook/README.md docs/gitbook/SUMMARY.md)"
python3 "${SCRIPT_DIR}/generate_doc_navigation.py" >/dev/null
after_hashes="$(sha256sum docs/gitbook/README.md docs/gitbook/SUMMARY.md)"
if [[ "${before_hashes}" != "${after_hashes}" ]]; then
  echo "Generated navigation files are not stable across repeated generation runs." >&2
  exit 1
fi

python3 "${SCRIPT_DIR}/check_markdown_links.py"

python3 "${SCRIPT_DIR}/generate_codebase_map.py" --pretty --check

# ──────────────────────────────────────────────────────────────────────
# AC5-B / X-08: GitBook content-hash drift check
# Compare H1/H2 structural headings between canonical docs/ files and
# their GitBook chapter mirrors. Emits warnings (not hard failures) for
# header divergence, since GitBook chapters are summaries and may
# legitimately have fewer headings than canonical sources.
# ────────────────────────���────────────────────────��────────────────────
gitbook_drift_warnings=0
# Mapping: canonical → gitbook mirror (pairs with known canonical references)
declare -A CANONICAL_TO_GITBOOK=(
  ["docs/CLAIM_EVIDENCE_INDEX.md"]="docs/gitbook/31-claim-vs-evidence-index.md"
  ["docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md"]="docs/gitbook/25-documentation-sync-and-coverage-matrix.md"
  ["docs/DOCS_DEDUPLICATION_MAP.md"]="docs/gitbook/27-documentation-deduplication-map.md"
  ["docs/THREAT_MODEL.md"]="docs/gitbook/28-threat-model-and-security-hardening.md"
  ["docs/CI_TELEMETRY_BASELINE.md"]="docs/gitbook/29-ci-maturity-and-telemetry-baseline.md"
  ["docs/VSPACE_MEMORY_MODEL_ADR.md"]="docs/gitbook/26-ws-b1-vspace-memory-adr.md"
)

for canonical in "${!CANONICAL_TO_GITBOOK[@]}"; do
  gitbook="${CANONICAL_TO_GITBOOK[$canonical]}"
  if [[ -f "${REPO_ROOT}/${canonical}" ]] && [[ -f "${REPO_ROOT}/${gitbook}" ]]; then
    # Extract H1/H2 headings (lines starting with # or ##, not ###)
    canonical_headers=$(grep -E '^#{1,2} ' "${REPO_ROOT}/${canonical}" | head -20 | sha256sum | cut -d' ' -f1)
    gitbook_headers=$(grep -E '^#{1,2} ' "${REPO_ROOT}/${gitbook}" | head -20 | sha256sum | cut -d' ' -f1)
    if [[ "${canonical_headers}" != "${gitbook_headers}" ]]; then
      echo "warning: GitBook header drift detected: ${canonical} ↔ ${gitbook}" >&2
      gitbook_drift_warnings=$((gitbook_drift_warnings + 1))
    fi
  fi
done
if [[ ${gitbook_drift_warnings} -gt 0 ]]; then
  echo "warning: ${gitbook_drift_warnings} GitBook chapter(s) have divergent H1/H2 headers from canonical sources." >&2
  echo "  Run: diff <(grep -E '^#{1,2} ' docs/FILE.md) <(grep -E '^#{1,2} ' docs/gitbook/CHAPTER.md) to inspect." >&2
fi

# Prefer an already-installed elan toolchain in non-login shells.
if [[ -f "${HOME}/.elan/env" ]]; then
  # shellcheck disable=SC1091
  source "${HOME}/.elan/env"
fi

# Keep docs-sync deterministic when possible by attempting Lean setup before the
# optional doc-gen4 probe. Setup remains best-effort by default so docs-sync can
# still validate navigation/link consistency on restricted/offline environments.
if ! command -v lake >/dev/null 2>&1; then
  if [[ "${DOCS_SYNC_SKIP_LEAN_SETUP:-0}" == "1" ]]; then
    echo "DOCS_SYNC_SKIP_LEAN_SETUP=1: skipping Lean setup; doc-gen4 probe disabled in this run."
  elif [[ -x "${SCRIPT_DIR}/setup_lean_env.sh" ]]; then
    echo "lake not found; attempting setup_lean_env.sh for docs-sync doc-gen4 probe"
    if "${SCRIPT_DIR}/setup_lean_env.sh"; then
      export PATH="${HOME}/.elan/bin:${PATH}"
    else
      if [[ "${DOCS_SYNC_REQUIRE_LEAN_SETUP:-0}" == "1" ]]; then
        echo "DOCS_SYNC_REQUIRE_LEAN_SETUP=1: setup_lean_env.sh failed; failing docs-sync." >&2
        exit 1
      fi
      echo "warning: setup_lean_env.sh failed; continuing docs-sync without doc-gen4 probe." >&2
    fi
  else
    echo "lake not available and setup_lean_env.sh is missing; skipping optional doc-gen4 invocation."
  fi
fi

if command -v lake >/dev/null 2>&1; then
  if lake exe doc-gen4 --help >/dev/null 2>&1; then
    lake exe doc-gen4 SeLe4n
  else
    echo "doc-gen4 executable not available in this environment; navigation/link automation still enforced."
  fi
else
  echo "lake not available in this environment; skipping optional doc-gen4 invocation."
fi
