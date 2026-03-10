#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"
cd "${REPO_ROOT}"

sub_args=()
if [[ "${CONTINUE_MODE}" -eq 1 ]]; then
  sub_args+=("--continue")
fi

run_check "META" "${SCRIPT_DIR}/test_tier0_hygiene.sh" "${sub_args[@]}"
run_check "META" "${SCRIPT_DIR}/test_tier1_build.sh" "${sub_args[@]}"
run_check "META" python3 "${SCRIPT_DIR}/scenario_catalog.py" validate
run_check "META" "${SCRIPT_DIR}/test_tier2_trace.sh" "${sub_args[@]}"
run_check "META" "${SCRIPT_DIR}/test_tier2_negative.sh" "${sub_args[@]}"
# M-19: documentation sync check — catches navigation/link drift on every PR.
run_check "META" "${SCRIPT_DIR}/test_docs_sync.sh"

finalize_report
