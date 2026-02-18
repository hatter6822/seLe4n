#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"
cd "${REPO_ROOT}"

ensure_lake_available

run_check "TRACE" lake exe negative_state_suite
run_check "TRACE" lake exe information_flow_suite

finalize_report
