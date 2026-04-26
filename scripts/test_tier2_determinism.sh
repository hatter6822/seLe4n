#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-I1/R-02: Mandatory determinism validation (Tier 2).
# Runs the trace executable twice and verifies identical output.
# Non-determinism bugs (e.g., HashMap iteration order leaking into
# scheduler selection) are caught immediately rather than at nightly.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"
cd "${REPO_ROOT}"

ensure_lake_available

DETERMINISM_DIR="$(mktemp -d)"
trap 'rm -rf "${DETERMINISM_DIR}"' EXIT

run_check_with_timeout "TRACE" bash -lc "lake exe sele4n > '${DETERMINISM_DIR}/run1.trace'"
run_check_with_timeout "TRACE" bash -lc "lake exe sele4n > '${DETERMINISM_DIR}/run2.trace'"
run_check "TRACE" bash -lc "diff -q '${DETERMINISM_DIR}/run1.trace' '${DETERMINISM_DIR}/run2.trace' || \
    { echo 'Non-determinism detected: trace output differs between runs' >&2; exit 1; }"

log_section "TRACE" "Determinism check passed: two runs produced identical output."

finalize_report
