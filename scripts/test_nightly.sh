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
log_section "INVARIANT" "Tier 4 nightly extensions are not yet wired; this is an explicit extension point."

finalize_report
