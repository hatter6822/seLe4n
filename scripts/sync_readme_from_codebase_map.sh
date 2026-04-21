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

# Pull readme_sync values as safe key=value pairs. We do NOT use `eval`
# because codebase_map.json content is not a trust boundary — a
# malicious commit that sets `readme_sync.version` to shell
# metacharacters would otherwise execute arbitrary commands when any
# developer runs this script. Instead we parse tab-separated lines with
# `read`, which never interprets the value as shell syntax.
readme_kv="$(python3 - "${MAP}" <<'PY'
import json, sys
with open(sys.argv[1]) as f:
    d = json.load(f)
r = d["readme_sync"]
def fmt(n):  # comma-separated ints (matches README "103,179" convention)
    if not isinstance(n, int):
        raise SystemExit(f"readme_sync: expected int, got {type(n).__name__}: {n!r}")
    return f"{n:,}"
# Tab-delimited key<TAB>value, one per line. No quoting is required
# because the receiving side splits on TAB, not whitespace, and never
# executes the value.
print(f'VERSION\t{r["version"]}')
print(f'TOOLCHAIN\t{r["lean_toolchain"]}')
print(f'PROD_FILES\t{r["production_files"]}')
print(f'PROD_LOC\t{fmt(r["production_loc"])}')
print(f'TEST_FILES\t{r["test_files"]}')
print(f'TEST_LOC\t{fmt(r["test_loc"])}')
print(f'PROVED\t{fmt(r["proved_theorem_lemma_decls"])}')
PY
)"

# Safely decompose into shell variables. Because `value` is set by
# assignment (not by a command substitution or eval) it cannot be
# interpreted as code, even if it contains metacharacters like `; $(...`.
VERSION="" TOOLCHAIN="" PROD_FILES="" PROD_LOC="" TEST_FILES="" TEST_LOC="" PROVED=""
while IFS=$'\t' read -r key value; do
  case "${key}" in
    VERSION)    VERSION="${value}" ;;
    TOOLCHAIN)  TOOLCHAIN="${value}" ;;
    PROD_FILES) PROD_FILES="${value}" ;;
    PROD_LOC)   PROD_LOC="${value}" ;;
    TEST_FILES) TEST_FILES="${value}" ;;
    TEST_LOC)   TEST_LOC="${value}" ;;
    PROVED)     PROVED="${value}" ;;
    "")         ;;                     # skip blanks
    *) echo "ERROR: unknown readme_sync key: ${key}" >&2; exit 2 ;;
  esac
done <<<"${readme_kv}"

# Sanity-check required fields (defense-in-depth: catches schema drift
# in codebase_map.json before we attempt any rewrite).
for var in VERSION TOOLCHAIN PROD_FILES PROD_LOC TEST_FILES TEST_LOC PROVED; do
  if [[ -z "${!var}" ]]; then
    echo "ERROR: readme_sync.${var} is empty — codebase_map.json schema may have changed" >&2
    exit 2
  fi
done

# Apply all substitutions to a file via a python one-shot that rewrites
# each metric row. Using python (not sed) because GNU and BSD sed
# disagree on -i semantics and because we want structured "pattern
# missed" reporting. Values are passed via argv (never via the heredoc
# body) so they cannot inject into the Python source.
apply_to_file() {
  local target="$1"
  local tmp="$2"
  python3 - "$target" "$tmp" \
           "$PROD_FILES" "$PROD_LOC" "$TEST_FILES" "$TEST_LOC" "$PROVED" <<'PY'
import re, sys, pathlib
src_path, dst_path, prod_files, prod_loc, test_files, test_loc, proved = sys.argv[1:]
text = pathlib.Path(src_path).read_text()

# Each entry is (name, regex, lambda-replacement). Using a lambda
# replacement (not the `\g<N>` string form) avoids any interpretation of
# backslashes in the injected value — safe even if prod_loc ever grows
# `\` characters in the future.
patterns = [
    # README.md: "Production Lean LoC" | VALUE across N files
    ("README production-LoC",
     r'(\|\s*\*\*Production Lean LoC\*\*\s*\|\s*)[\d,]+\s+across\s+\d+\s+files(\s*\|)',
     lambda m: f"{m.group(1)}{prod_loc} across {prod_files} files{m.group(2)}"),
    # SELE4N_SPEC.md: "Production LoC" | VALUE across N Lean files
    ("SPEC production-LoC",
     r'(\|\s*\*\*Production LoC\*\*\s*\|\s*)[\d,]+\s+across\s+\d+\s+Lean files(\s*\|)',
     lambda m: f"{m.group(1)}{prod_loc} across {prod_files} Lean files{m.group(2)}"),
    # README.md: "Test Lean LoC" | VALUE across N test suites
    ("README test-LoC",
     r'(\|\s*\*\*Test Lean LoC\*\*\s*\|\s*)[\d,]+\s+across\s+\d+\s+test suites(\s*\|)',
     lambda m: f"{m.group(1)}{test_loc} across {test_files} test suites{m.group(2)}"),
    # SELE4N_SPEC.md: "Test LoC" | VALUE across N Lean test suites
    ("SPEC test-LoC",
     r'(\|\s*\*\*Test LoC\*\*\s*\|\s*)[\d,]+\s+across\s+\d+\s+Lean test suites(\s*\|)',
     lambda m: f"{m.group(1)}{test_loc} across {test_files} Lean test suites{m.group(2)}"),
    # Both files: "Proved declarations"
    ("shared proved-decls",
     r'(\|\s*\*\*Proved declarations\*\*\s*\|\s*)[\d,]+(\s+theorem/lemma declarations \(zero sorry/axiom\)\s*\|)',
     lambda m: f"{m.group(1)}{proved}{m.group(2)}"),
]

# Determine which patterns a given file is expected to own, so a
# genuinely missing pattern (e.g., README test-LoC regex no longer
# matches) becomes a hard error instead of a silent no-op.
basename = pathlib.Path(src_path).name
if basename == "README.md":
    required = {"README production-LoC", "README test-LoC", "shared proved-decls"}
elif basename == "SELE4N_SPEC.md":
    required = {"SPEC production-LoC", "SPEC test-LoC", "shared proved-decls"}
else:
    required = set()

missed = []
for name, pat, repl in patterns:
    new_text, count = re.subn(pat, repl, text)
    text = new_text
    if count == 0 and name in required:
        missed.append(name)

if missed:
    print(f"ERROR: {src_path}: required patterns did not match: {', '.join(missed)}",
          file=sys.stderr)
    print("       the README/spec format probably changed; update the "
          "`patterns` table in sync_readme_from_codebase_map.sh.",
          file=sys.stderr)
    sys.exit(2)  # matches shell-level "setup error" exit code

pathlib.Path(dst_path).write_text(text)
PY
}

TARGETS=("README.md" "docs/spec/SELE4N_SPEC.md")
FAIL=0

# Cleanup scratch files on any exit path (success, drift, signal).
SCRATCH_FILES=()
cleanup_scratch() {
  local s
  for s in "${SCRATCH_FILES[@]:-}"; do
    if [[ -n "${s}" && -f "${s}" ]]; then
      rm -f "${s}"
    fi
  done
}
trap cleanup_scratch EXIT

for f in "${TARGETS[@]}"; do
  if [[ ! -f "${f}" ]]; then
    echo "WARN: ${f} not found; skipping"; continue
  fi
  scratch="$(mktemp)"
  SCRATCH_FILES+=("${scratch}")
  apply_to_file "${f}" "${scratch}"
  if cmp -s "${f}" "${scratch}"; then
    [[ "${CHECK_MODE}" -eq 1 ]] && echo "  ${f}: in sync"
    continue
  fi
  if [[ "${CHECK_MODE}" -eq 1 ]]; then
    echo "DRIFT in ${f}:" >&2
    diff -u "${f}" "${scratch}" || true
    FAIL=1
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
