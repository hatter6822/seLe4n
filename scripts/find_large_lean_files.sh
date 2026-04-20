#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# find_large_lean_files.sh — rank large Lean modules and docs by line count.
#
# Used by maintainers (and the AK10-E-style "Known large files refresh"
# step) to keep CLAUDE.md's "Known large files" section current. Output is
# formatted to match the bullet style already in CLAUDE.md, so the result
# can be diffed against that file or pasted directly.
#
# Scan scope (matches CLAUDE.md §"Reading large files"):
#   - SeLe4n/**/*.lean and Main.lean
#   - tests/**/*.lean
#   - CHANGELOG.md, docs/**/*.md (including docs/dev_history for archived
#     plans already referenced in CLAUDE.md)
#
# Usage:
#   scripts/find_large_lean_files.sh                 # list files ≥ threshold, sorted
#   scripts/find_large_lean_files.sh --threshold 1000
#   scripts/find_large_lean_files.sh --top 30
#   scripts/find_large_lean_files.sh --format bullets   # default
#   scripts/find_large_lean_files.sh --format table     # file<TAB>lines
#   scripts/find_large_lean_files.sh --check            # diff vs CLAUDE.md
#
# Exit codes:
#   0  listing produced (or --check: no drift from CLAUDE.md)
#   1  --check: drift detected between actual sizes and CLAUDE.md table
#   2  usage / setup error

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

THRESHOLD=800
TOP=0
FORMAT="bullets"
CHECK_MODE=0

# require_value SWITCH VALUE — exits 2 with a clear message if VALUE is
# missing or starts with `-` (i.e. probably the next flag).
require_value() {
  local switch="$1" val="${2-}"
  if [[ -z "${val}" || "${val:0:1}" == "-" ]]; then
    echo "ERROR: ${switch} requires a value" >&2
    exit 2
  fi
}

# require_nonneg_int SWITCH VALUE — rejects non-numeric / negative args.
require_nonneg_int() {
  local switch="$1" val="$2"
  if [[ ! "${val}" =~ ^[0-9]+$ ]]; then
    echo "ERROR: ${switch} must be a non-negative integer (got: ${val})" >&2
    exit 2
  fi
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --threshold)
      require_value "--threshold" "${2-}"
      require_nonneg_int "--threshold" "$2"
      THRESHOLD="$2"; shift 2 ;;
    --top)
      require_value "--top" "${2-}"
      require_nonneg_int "--top" "$2"
      TOP="$2"; shift 2 ;;
    --format)
      require_value "--format" "${2-}"
      case "$2" in
        bullets|table) FORMAT="$2" ;;
        *) echo "ERROR: --format must be 'bullets' or 'table' (got: $2)" >&2; exit 2 ;;
      esac
      shift 2 ;;
    --check)     CHECK_MODE=1; shift ;;
    -h|--help)
      sed -n '9,28p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
      exit 0 ;;
    *) echo "unknown option: $1" >&2; exit 2 ;;
  esac
done

# Build the file list. NUL-delimited to survive spaces (none expected in
# this tree, but the discipline is free).
tmp_list="$(mktemp)"
trap 'rm -f "${tmp_list}"' EXIT

{
  find SeLe4n -type f -name '*.lean' -print0
  find tests  -type f -name '*.lean' -print0
  printf '%s\0' Main.lean
  find docs   -type f -name '*.md'   -print0
  printf '%s\0' CHANGELOG.md
} | while IFS= read -r -d '' path; do
  [[ -f "${path}" ]] || continue
  lines=$(wc -l < "${path}")
  if (( lines >= THRESHOLD )); then
    printf '%d\t%s\n' "${lines}" "${path}"
  fi
done \
  | LC_ALL=C sort -t $'\t' -k1,1rn -k2,2 > "${tmp_list}"
# -t $'\t' forces TAB as field separator (robust to paths with spaces)
# -k1,1rn: primary = line count descending (numeric)
# -k2,2:   secondary = path ascending (byte order), gives deterministic
#          output across runs and machines (LC_ALL=C pins locale).

if (( TOP > 0 )); then
  head -n "${TOP}" "${tmp_list}" > "${tmp_list}.cut"
  mv "${tmp_list}.cut" "${tmp_list}"
fi

render() {
  case "${FORMAT}" in
    bullets)
      awk -F '\t' '{ printf "- `%s` (~%d lines)\n", $2, $1 }' "${tmp_list}" ;;
    table)
      cat "${tmp_list}" ;;
    *)
      echo "unknown --format: ${FORMAT}" >&2; exit 2 ;;
  esac
}

if (( CHECK_MODE == 0 )); then
  render
  exit 0
fi

# --check: compare the bullets against the block in CLAUDE.md. The block
# starts at the "Known large files" header and ends at the first line
# after the header that is not a bullet.
[[ -f CLAUDE.md ]] || { echo "ERROR: CLAUDE.md not found; cannot --check" >&2; exit 2; }
expected="$(awk '/^\*\*Known large files\*\*/ {want=1; next}
                want && /^- `/ {print; next}
                want && !/^- `/ {exit}' CLAUDE.md)"
if [[ -z "${expected}" ]]; then
  echo "ERROR: could not locate '**Known large files**' bullet block in CLAUDE.md" >&2
  exit 2
fi
actual="$(render)"

if [[ "${expected}" == "${actual}" ]]; then
  echo "PASS: CLAUDE.md 'Known large files' matches live tree (threshold ${THRESHOLD})."
  exit 0
fi

echo "FAIL: CLAUDE.md 'Known large files' is out of sync with live tree." >&2
echo "--- expected (from CLAUDE.md) ---" >&2
printf '%s\n' "${expected}" >&2
echo "--- actual (threshold ${THRESHOLD}) ---" >&2
printf '%s\n' "${actual}" >&2
exit 1
