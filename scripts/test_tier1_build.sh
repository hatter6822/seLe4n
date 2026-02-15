#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"
cd "${REPO_ROOT}"

ensure_lake_available

build_log="$(mktemp)"
cleanup() {
  rm -f "${build_log}"
}
trap cleanup EXIT

run_check "BUILD" bash -lc "set -o pipefail; lake build 2>&1 | tee '${build_log}'"
run_check "BUILD" bash -lc "rg -n '^warning:' '${build_log}'; status=\$?; if [ \$status -eq 0 ]; then echo 'Lean build emitted warnings; resolve warnings before merge.' >&2; exit 1; elif [ \$status -eq 1 ]; then exit 0; else echo 'Warning scan failed (rg error); cannot validate warning-free build.' >&2; exit \$status; fi"

finalize_report
