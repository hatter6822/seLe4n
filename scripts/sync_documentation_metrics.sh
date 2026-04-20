#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# sync_documentation_metrics.sh — end-to-end documentation-metrics sync.
#
# Call this after any change to Lean sources (or tests) that affects
# per-file line counts or declaration counts. It orchestrates:
#
#   1. `generate_codebase_map.py --pretty` — rebuild docs/codebase_map.json
#      from the live tree so `readme_sync` reflects reality.
#   2. `sync_readme_from_codebase_map.sh` — push the freshly-computed
#      metrics into README.md and docs/spec/SELE4N_SPEC.md.
#   3. `find_large_lean_files.sh --check` — warn (not fail) when the
#      CLAUDE.md "Known large files" list has drifted. We only warn
#      here because the list is manually curated with `(~N lines)`
#      approximations that do not need to update on every patch.
#   4. `test_docs_sync.sh` — run the existing docs-sync CI gate to
#      confirm no downstream regression (GitBook nav, markdown links,
#      codebase-map --check).
#
# Use --check to run in verify-only mode: no file is rewritten; the
# exit status reflects whether anything is out of sync.
#
# Usage:
#   scripts/sync_documentation_metrics.sh            # write-through
#   scripts/sync_documentation_metrics.sh --check    # verify only
#
# Exit codes:
#   0  all steps passed (or --check: everything in sync)
#   1  at least one step failed / drift detected
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
    sed -n '9,36p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
    exit 0 ;;
  *) echo "unknown option: $1" >&2; exit 2 ;;
esac

section() { printf '\n=== %s ===\n' "$1"; }

overall_exit=0

# ──────────────────────────────────────────────────────────────────
# Step 1 — Regenerate (or --check) docs/codebase_map.json
# ──────────────────────────────────────────────────────────────────
section "1/4  codebase_map.json"
if (( CHECK_MODE )); then
  if python3 "${SCRIPT_DIR}/generate_codebase_map.py" --pretty --check; then
    echo "  PASS"
  else
    echo "  FAIL — docs/codebase_map.json does not match live Lean surface." >&2
    overall_exit=1
  fi
else
  python3 "${SCRIPT_DIR}/generate_codebase_map.py" --pretty
  echo "  OK — docs/codebase_map.json regenerated"
fi

# ──────────────────────────────────────────────────────────────────
# Step 2 — Push readme_sync into README.md + SELE4N_SPEC.md
# ──────────────────────────────────────────────────────────────────
section "2/4  README.md / SELE4N_SPEC.md"
if (( CHECK_MODE )); then
  if "${SCRIPT_DIR}/sync_readme_from_codebase_map.sh" --check; then
    :
  else
    overall_exit=1
  fi
else
  "${SCRIPT_DIR}/sync_readme_from_codebase_map.sh"
fi

# ──────────────────────────────────────────────────────────────────
# Step 3 — Advisory check on CLAUDE.md "Known large files" list.
# Warnings only: the CLAUDE.md list is a curated snapshot with
# approximate "(~N lines)" entries; expecting exact equality on every
# commit would be noise. A full refresh (as AK10-E did) is a
# maintainer-curated step.
# ──────────────────────────────────────────────────────────────────
section "3/4  CLAUDE.md large-files advisory"
if "${SCRIPT_DIR}/find_large_lean_files.sh" --check >/dev/null 2>&1; then
  echo "  PASS — CLAUDE.md list matches live tree exactly"
else
  echo "  WARN — CLAUDE.md 'Known large files' differs from live tree."
  echo "         Run: scripts/find_large_lean_files.sh --top 45"
  echo "         and review against CLAUDE.md §'Reading large files' before release."
fi

# ──────────────────────────────────────────────────────────────────
# Step 4 — Existing docs-sync CI gate (navigation, markdown links,
# codebase_map --check). Only run when not in --check mode and only if
# the harness is expected to succeed in this environment.
# ──────────────────────────────────────────────────────────────────
section "4/4  test_docs_sync.sh"
if (( CHECK_MODE )); then
  echo "  skipped in --check mode (run test_docs_sync.sh directly for full validation)"
else
  if "${SCRIPT_DIR}/test_docs_sync.sh"; then
    echo "  PASS"
  else
    echo "  FAIL — test_docs_sync.sh reported errors" >&2
    overall_exit=1
  fi
fi

section "summary"
if (( overall_exit == 0 )); then
  echo "  all steps ${CHECK_MODE:+(check) }passed"
  exit 0
fi
echo "  at least one step failed; see output above" >&2
exit "${overall_exit}"
