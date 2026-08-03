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
#   scripts/find_large_lean_files.sh --check --tolerance 0   # exact counts
#
# `--check` compares the live tree against the "Known large files" block in
# CLAUDE.md.  The block is a *curated* snapshot whose counts are explicitly
# approximate (`~N lines`), so an exact string comparison can only ever be a
# warning — and a warning nobody gates on is invisible, which is how the list
# drifted in the first place.  `--check` is therefore **tolerant** by design:
#
#   * the SET of listed files must match exactly — a file crossing the
#     threshold changes the reading guidance and is always material; and
#   * each recorded count must be within `--tolerance` percent of actual,
#     which absorbs the routine per-patch churn the `~` already signals.
#
# That makes the check strict about what matters and quiet about what does
# not, so it can be a hard gate (`test_docs_sync.sh`) rather than a warning.
# `--tolerance 0` restores exact-count comparison.
#
# Exit codes:
#   0  listing produced (or --check: no material drift from CLAUDE.md)
#   1  --check: drift detected between actual sizes and CLAUDE.md table
#   2  usage / setup error

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

THRESHOLD=800
# Percent by which a recorded `~N lines` count may differ from actual before
# `--check` calls it drift.  The list's counts are approximations by design;
# 10% absorbs ordinary per-patch growth while still catching a file whose
# size has changed enough to alter the "read in ≤500-line chunks" guidance.
TOLERANCE_PCT=10
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
    --tolerance)
      require_value "--tolerance" "${2-}"
      require_nonneg_int "--tolerance" "$2"
      TOLERANCE_PCT="$2"; shift 2 ;;
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
  echo "PASS: CLAUDE.md 'Known large files' matches live tree exactly (threshold ${THRESHOLD})."
  exit 0
fi

if (( TOLERANCE_PCT == 0 )); then
  echo "FAIL: CLAUDE.md 'Known large files' is out of sync with live tree." >&2
  echo "--- expected (from CLAUDE.md) ---" >&2
  printf '%s\n' "${expected}" >&2
  echo "--- actual (threshold ${THRESHOLD}) ---" >&2
  printf '%s\n' "${actual}" >&2
  exit 1
fi

# Tolerant comparison: parse both bullet blocks into `path<TAB>count` pairs
# and report only material drift (see the header).  Bullet shape is
# "- `path` (~N lines)".
parse_bullets() {
  sed -nE 's/^- `([^`]+)` \(~([0-9]+) lines\)$/\1\t\2/p'
}

exp_pairs="$(printf '%s\n' "${expected}" | parse_bullets | sort)"
act_pairs="$(printf '%s\n' "${actual}"   | parse_bullets | sort)"

# Defensive: a bullet that does not parse means the block shape changed, and
# a silently-empty comparison would be a vacuous gate.  Fail loudly instead.
exp_n="$(printf '%s\n' "${expected}" | grep -c '^- `' || true)"
act_n="$(printf '%s\n' "${actual}"   | grep -c '^- `' || true)"
if [[ "$(printf '%s\n' "${exp_pairs}" | grep -c . || true)" != "${exp_n}" ]] \
   || [[ "$(printf '%s\n' "${act_pairs}" | grep -c . || true)" != "${act_n}" ]]; then
  echo "FAIL: could not parse every 'Known large files' bullet as '- \`path\` (~N lines)'." >&2
  echo "      The block shape changed; refresh it with --format bullets." >&2
  exit 1
fi

drift=0

# (a) Set membership — a file entering or leaving the list is always material.
only_expected="$(comm -23 <(cut -f1 <<<"${exp_pairs}") <(cut -f1 <<<"${act_pairs}"))"
only_actual="$(comm -13 <(cut -f1 <<<"${exp_pairs}") <(cut -f1 <<<"${act_pairs}"))"
if [[ -n "${only_expected}" ]]; then
  echo "FAIL: listed in CLAUDE.md but no longer at/above the ${THRESHOLD}-line threshold:" >&2
  printf '  %s\n' ${only_expected} >&2
  drift=1
fi
if [[ -n "${only_actual}" ]]; then
  echo "FAIL: at/above the ${THRESHOLD}-line threshold but missing from CLAUDE.md:" >&2
  printf '  %s\n' ${only_actual} >&2
  drift=1
fi

# (b) Per-file magnitude — beyond the tolerance the recorded count no longer
#     conveys the right reading guidance.
while IFS=$'\t' read -r path want; do
  [[ -n "${path}" ]] || continue
  have="$(awk -F'\t' -v p="${path}" '$1==p {print $2}' <<<"${act_pairs}")"
  [[ -n "${have}" ]] || continue   # membership drift already reported above
  delta=$(( want > have ? want - have : have - want ))
  # Percentage of the ACTUAL size, so the tolerance scales with the file.
  if (( delta * 100 > have * TOLERANCE_PCT )); then
    echo "FAIL: ${path}: CLAUDE.md records ~${want} lines, actual ${have} \
(differs by ${delta}, over the ${TOLERANCE_PCT}% tolerance)." >&2
    drift=1
  fi
done <<<"${exp_pairs}"

if (( drift == 1 )); then
  echo "" >&2
  echo "Refresh with: ./scripts/find_large_lean_files.sh --format bullets" >&2
  echo "and replace the bullet block in BOTH CLAUDE.md and AGENTS.md." >&2
  exit 1
fi

echo "PASS: CLAUDE.md 'Known large files' is within the ${TOLERANCE_PCT}% tolerance \
(threshold ${THRESHOLD}); counts are approximate by design."
exit 0
