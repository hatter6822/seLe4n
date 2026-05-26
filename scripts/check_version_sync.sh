#!/usr/bin/env bash
# shellcheck disable=SC2154  # VERSION_SITE_* arrays are defined in the sourced manifest
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
# check_version_sync.sh — validate that EVERY version-bearing file matches
# the canonical version in lakefile.toml.
#
# The authoritative list of version sites lives in
# scripts/version_locations.sh (shared with scripts/bump_version.sh so the
# verifier and the bumper can never disagree).  Per CLAUDE.md, every PR bumps
# the patch version and updates ALL version locations (README.md, GitBook,
# i18n badges, Rust crates, the spec, codebase_map.json, …); this Tier 0 gate
# (called from test_tier0_hygiene.sh) and the pre-commit hook make a forgotten
# location a hard failure rather than a silent drift.
#
# Exit codes:
#   0  All version-bearing sites match lakefile.toml.
#   1  One or more mismatches found.
#   2  Could not extract canonical version / load the site manifest.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

# Canonical version — the single source of truth.
CANONICAL=$(grep '^version' lakefile.toml | sed 's/.*"\(.*\)"/\1/')
if [[ -z "${CANONICAL}" ]]; then
  echo "ERROR: Could not extract version from lakefile.toml" >&2
  exit 2
fi

# Regex-escaped canonical (dots are regex metacharacters).
VER_ESC="${CANONICAL//./\\.}"

MANIFEST="${SCRIPT_DIR}/version_locations.sh"
if [[ ! -f "${MANIFEST}" ]]; then
  echo "ERROR: version-site manifest missing at ${MANIFEST}" >&2
  exit 2
fi
# shellcheck source=scripts/version_locations.sh
source "${MANIFEST}"

FAIL=0

# count_matches PATTERN FILE — number of lines matching the grep -E PATTERN
# (0 on no match, never aborts under `set -e`).
count_matches() {
  grep -Ec "$1" "$2" 2>/dev/null || true
}

report_mismatch() {
  local label="$1" file="$2" detail="$3"
  echo "MISMATCH: ${label}"
  echo "  Expected: ${CANONICAL} (from lakefile.toml)"
  echo "  File:     ${file}"
  echo "  Detail:   ${detail}"
  FAIL=1
}

for i in "${!VERSION_SITE_FILE[@]}"; do
  file="${VERSION_SITE_FILE[$i]}"
  verify="${VERSION_SITE_VERIFY[$i]}"
  label="${VERSION_SITE_LABEL[$i]}"
  occurs="${VERSION_SITE_OCCURS[$i]}"

  if [[ ! -f "${file}" ]]; then
    report_mismatch "${label}" "${file}" "version-bearing file is missing"
    continue
  fi

  if [[ "${verify}" == "__CARGO_LOCK__" ]]; then
    # Bespoke verifier: each sele4n-* crate's `version` line (the line
    # immediately after its `name` line) must equal the canonical version.
    found=$(grep -A1 -E '^name = "sele4n-' "${file}" \
              | grep -Ec "^version = \"${VER_ESC}\"" || true)
    if [[ "${found}" -ne "${occurs}" ]]; then
      report_mismatch "${label}" "${file}" \
        "expected ${occurs} sele4n-* crate(s) at ${CANONICAL}, found ${found}"
    fi
    continue
  fi

  pattern="${verify//@VER@/${VER_ESC}}"
  found=$(count_matches "${pattern}" "${file}")
  if [[ "${found}" -ne "${occurs}" ]]; then
    other=$(grep -En "${verify//@VER@/[0-9]+[.][0-9]+[.][0-9]+}" "${file}" \
              | head -1 || true)
    report_mismatch "${label}" "${file}" \
      "expected ${occurs} line(s) at ${CANONICAL}, found ${found}${other:+ — actual: ${other}}"
  fi
done

echo "Canonical version: ${CANONICAL}"
echo "Checked ${#VERSION_SITE_FILE[@]} version sites."
if [[ "${FAIL}" -eq 1 ]]; then
  echo "FAIL: Version sync check found mismatches." >&2
  echo "Fix every location (or run: ./scripts/bump_version.sh ${CANONICAL})." >&2
  exit 1
else
  echo "PASS: All version-bearing sites match lakefile.toml."
fi
