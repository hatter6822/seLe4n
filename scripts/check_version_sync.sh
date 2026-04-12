#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
# check_version_sync.sh — validate that all version-bearing files match
# the canonical version in lakefile.toml.
#
# AH4-E: Prevents version drift by checking 14 files against the single
# source of truth.  Called from test_tier0_hygiene.sh (Tier 0 CI gate).
#
# Exit codes:
#   0  All version-bearing files match lakefile.toml.
#   1  One or more mismatches found.
#   2  Could not extract canonical version (setup error).

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

# Extract canonical version from lakefile.toml
CANONICAL=$(grep '^version' lakefile.toml | sed 's/.*"\(.*\)"/\1/')
if [[ -z "${CANONICAL}" ]]; then
  echo "ERROR: Could not extract version from lakefile.toml" >&2
  exit 2
fi

FAIL=0

check_file() {
  local file="$1" pattern="$2" label="$3"
  if [[ ! -f "${file}" ]]; then
    echo "WARN: ${file} not found (skipped)"
    return
  fi
  if ! grep -q "${CANONICAL}" <(grep "${pattern}" "${file}"); then
    local actual
    actual=$(grep "${pattern}" "${file}" | head -1)
    echo "MISMATCH: ${label}"
    echo "  Expected: ${CANONICAL}"
    echo "  Found:    ${actual}"
    echo "  File:     ${file}"
    FAIL=1
  fi
}

# 1. Rust HAL boot banner
check_file "rust/sele4n-hal/src/boot.rs" "KERNEL_VERSION" "Rust HAL KERNEL_VERSION"

# 2. Rust workspace Cargo.toml
check_file "rust/Cargo.toml" 'version' "Rust workspace version"

# 3. Spec document
check_file "docs/spec/SELE4N_SPEC.md" "Package version" "SELE4N_SPEC package version"

# 4. CLAUDE.md project description
check_file "CLAUDE.md" "Lake build system, version" "CLAUDE.md version reference"

# 5-14. i18n README badges (10 files)
for lang in ar de es fr hi ja ko pt-BR ru zh-CN; do
  readme="docs/i18n/${lang}/README.md"
  check_file "${readme}" "version-" "i18n README (${lang})"
done

echo "Canonical version: ${CANONICAL}"
if [[ "${FAIL}" -eq 1 ]]; then
  echo "FAIL: Version sync check found mismatches." >&2
  exit 1
else
  echo "PASS: All version-bearing files match lakefile.toml."
fi
