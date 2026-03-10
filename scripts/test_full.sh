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

sub_args=()
if [[ "${CONTINUE_MODE}" -eq 1 ]]; then
  sub_args+=("--continue")
fi

run_check "META" "${SCRIPT_DIR}/test_smoke.sh" "${sub_args[@]}"
run_check "META" "${SCRIPT_DIR}/test_tier3_invariant_surface.sh" "${sub_args[@]}"

finalize_report
