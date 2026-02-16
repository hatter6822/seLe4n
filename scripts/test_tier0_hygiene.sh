#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"
cd "${REPO_ROOT}"

if command -v rg >/dev/null 2>&1; then
  run_check "HYGIENE" bash -lc 'if rg -n "axiom|sorry|TODO" SeLe4n Main.lean; then echo "Forbidden markers found in tracked proof surface." >&2; exit 1; fi'
else
  log_section "HYGIENE" "ripgrep (rg) not found; using grep fallback for marker scan."
  run_check "HYGIENE" bash -lc 'if (find SeLe4n -name "*.lean" -print0; printf "Main.lean\0") | xargs -0 grep -nE "axiom|sorry|TODO"; then echo "Forbidden markers found in tracked proof surface." >&2; exit 1; fi'
fi

if command -v shellcheck >/dev/null 2>&1; then
  run_check "HYGIENE" shellcheck scripts/*.sh
else
  log_section "HYGIENE" "shellcheck unavailable; optional shell lint not executed in this environment."
fi

finalize_report
