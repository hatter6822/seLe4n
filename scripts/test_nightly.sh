#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"

sub_args=()
if [[ "${CONTINUE_MODE}" -eq 1 ]]; then
  sub_args+=("--continue")
fi

run_check "META" "${SCRIPT_DIR}/test_full.sh" "${sub_args[@]}"
run_check "META" "${SCRIPT_DIR}/test_tier4_nightly_candidates.sh" "${sub_args[@]}"
log_section "INVARIANT" "Tier 4 keeps an explicit extension-point default; set NIGHTLY_ENABLE_EXPERIMENTAL=1 to run staged candidates."

finalize_report
