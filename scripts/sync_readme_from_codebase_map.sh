#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# sync_readme_from_codebase_map.sh — push metrics from codebase_map.json to
# human-facing docs.
#
# Source of truth: docs/codebase_map.json  (the `readme_sync` object)
# Targets:
#   - README.md                 "Current state" table rows
#   - docs/spec/SELE4N_SPEC.md  "Current State Snapshot" table rows
#
# This script does NOT regenerate codebase_map.json itself; run
# `scripts/generate_codebase_map.py --pretty` first (or call
# `scripts/sync_documentation_metrics.sh` which orchestrates both).
#
# Fields synced (identical in both files, formatting differs slightly):
#   production_loc  → Production [Lean] LoC
#   production_files → "across N [Lean] files"
#   test_loc         → Test [Lean] LoC
#   test_files       → "across N [Lean] test suites"
#   proved_theorem_lemma_decls → Proved declarations
#
# Version and Lean toolchain are sanity-checked but NOT rewritten here —
# `scripts/check_version_sync.sh` already owns version invariants.
#
# Usage:
#   scripts/sync_readme_from_codebase_map.sh            # write-through
#   scripts/sync_readme_from_codebase_map.sh --check    # diff-only, exit 1 on drift
#
# Exit codes:
#   0  targets in sync (or successfully rewritten)
#   1  --check: drift detected
#   2  usage / setup error

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

CHECK_MODE=0
case "${1:-}" in
  --check) CHECK_MODE=1 ;;
  "")      ;;
  -h|--help)
    sed -n '9,34p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
    exit 0 ;;
  *) echo "unknown option: $1" >&2; exit 2 ;;
esac

MAP="docs/codebase_map.json"
[[ -f "${MAP}" ]] || { echo "ERROR: ${MAP} not found; run generate_codebase_map.py first" >&2; exit 2; }

# Pull readme_sync values via Python (portable, no jq dependency).
eval "$(python3 - "${MAP}" <<'PY'
import json, sys
with open(sys.argv[1]) as f:
    d = json.load(f)
r = d["readme_sync"]
# Format integers with comma separators (matches README convention).
def fmt(n): return f"{n:,}"
print(f'VERSION={r["version"]}')
print(f'TOOLCHAIN={r["lean_toolchain"]}')
print(f'PROD_FILES={r["production_files"]}')
print(f'PROD_LOC="{fmt(r["production_loc"])}"')
print(f'TEST_FILES={r["test_files"]}')
print(f'TEST_LOC="{fmt(r["test_loc"])}"')
print(f'PROVED={fmt(r["proved_theorem_lemma_decls"])}')
PY
)"

# Apply all substitutions to a file via a python one-shot that rewrites
# each of the five metric rows. Using python (not sed) because macOS and
# GNU sed disagree on -i semantics and because the regex set is small.
apply_to_file() {
  local target="$1"
  local tmp="$2"
  python3 - "$target" "$tmp" \
           "$PROD_FILES" "$PROD_LOC" "$TEST_FILES" "$TEST_LOC" "$PROVED" <<'PY'
import re, sys, pathlib
src_path, dst_path, prod_files, prod_loc, test_files, test_loc, proved = sys.argv[1:]
text = pathlib.Path(src_path).read_text()

# README.md-style rows ("across N files"); SELE4N_SPEC-style rows
# ("across N Lean files") use the "Lean " variant. Both patterns are
# applied; whichever matches stays; non-matching is a no-op.
patterns = [
    # (regex, replacement)
    # README.md: "Production Lean LoC" | VALUE across N files
    (r'(\|\s*\*\*Production Lean LoC\*\*\s*\|\s*)[\d,]+\s+across\s+\d+\s+files(\s*\|)',
     rf'\g<1>{prod_loc} across {prod_files} files\g<2>'),
    # SELE4N_SPEC.md: "Production LoC" | VALUE across N Lean files
    (r'(\|\s*\*\*Production LoC\*\*\s*\|\s*)[\d,]+\s+across\s+\d+\s+Lean files(\s*\|)',
     rf'\g<1>{prod_loc} across {prod_files} Lean files\g<2>'),
    # README.md: "Test Lean LoC" | VALUE across N test suites
    (r'(\|\s*\*\*Test Lean LoC\*\*\s*\|\s*)[\d,]+\s+across\s+\d+\s+test suites(\s*\|)',
     rf'\g<1>{test_loc} across {test_files} test suites\g<2>'),
    # SELE4N_SPEC.md: "Test LoC" | VALUE across N Lean test suites
    (r'(\|\s*\*\*Test LoC\*\*\s*\|\s*)[\d,]+\s+across\s+\d+\s+Lean test suites(\s*\|)',
     rf'\g<1>{test_loc} across {test_files} Lean test suites\g<2>'),
    # Both files: "Proved declarations" | VALUE theorem/lemma declarations (zero sorry/axiom)
    (r'(\|\s*\*\*Proved declarations\*\*\s*\|\s*)[\d,]+(\s+theorem/lemma declarations \(zero sorry/axiom\)\s*\|)',
     rf'\g<1>{proved}\g<2>'),
]
for pat, repl in patterns:
    text = re.sub(pat, repl, text)
pathlib.Path(dst_path).write_text(text)
PY
}

TARGETS=("README.md" "docs/spec/SELE4N_SPEC.md")
FAIL=0

for f in "${TARGETS[@]}"; do
  if [[ ! -f "${f}" ]]; then
    echo "WARN: ${f} not found; skipping"; continue
  fi
  scratch="$(mktemp)"
  apply_to_file "${f}" "${scratch}"
  if cmp -s "${f}" "${scratch}"; then
    rm -f "${scratch}"
    [[ "${CHECK_MODE}" -eq 1 ]] && echo "  ${f}: in sync"
    continue
  fi
  if [[ "${CHECK_MODE}" -eq 1 ]]; then
    echo "DRIFT in ${f}:" >&2
    diff -u "${f}" "${scratch}" || true
    FAIL=1
    rm -f "${scratch}"
  else
    mv "${scratch}" "${f}"
    echo "  ${f}: updated"
  fi
done

if [[ "${CHECK_MODE}" -eq 1 ]]; then
  if [[ "${FAIL}" -eq 1 ]]; then
    echo "FAIL: README/spec metric drift. Run ./scripts/sync_readme_from_codebase_map.sh to rewrite." >&2
    exit 1
  fi
  echo "PASS: README.md + SELE4N_SPEC.md match docs/codebase_map.json (readme_sync)."
fi

echo "  canonical version: ${VERSION} (toolchain ${TOOLCHAIN})"
