#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${ROOT_DIR}"

echo "[AUDIT] Running baseline tiered entrypoint checks"
"${SCRIPT_DIR}/test_fast.sh"
"${SCRIPT_DIR}/test_smoke.sh"
"${SCRIPT_DIR}/test_full.sh"
"${SCRIPT_DIR}/test_nightly.sh"

echo "[AUDIT] Running Tier 4 staged candidates in experimental mode"
NIGHTLY_ENABLE_EXPERIMENTAL=1 "${SCRIPT_DIR}/test_tier4_nightly_candidates.sh"

echo "[AUDIT] Verifying Tier 2 control-data failure behavior"
TMP_FIXTURE="$(mktemp)"
trap 'rm -f "${TMP_FIXTURE}"' EXIT
cp tests/fixtures/main_trace_smoke.expected "${TMP_FIXTURE}"
echo "[CONTROL] impossible expected line" >> "${TMP_FIXTURE}"

if TRACE_FIXTURE_PATH="${TMP_FIXTURE}" "${SCRIPT_DIR}/test_tier2_trace.sh"; then
  echo "[AUDIT] ERROR: control-data mismatch did not fail Tier 2 as expected" >&2
  exit 1
fi

echo "[AUDIT] Control-data mismatch correctly causes Tier 2 failure"
echo "[AUDIT] Testing framework audit completed successfully"
