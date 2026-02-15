#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"
cd "${REPO_ROOT}"

run_check "HYGIENE" bash -lc 'if rg -n "axiom|sorry|TODO" SeLe4n Main.lean; then echo "Forbidden markers found in tracked proof surface." >&2; exit 1; fi'

if command -v shellcheck >/dev/null 2>&1; then
  run_check "HYGIENE" shellcheck scripts/*.sh
else
  log_section "HYGIENE" "shellcheck not installed; skipping optional lint."
fi

finalize_report
