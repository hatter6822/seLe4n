#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# AN11-E.10 (TST-M12) — testing-framework self-test (umbrella script).
#
# This script is the canonical "test the testing infrastructure" runner:
# it walks every tier (`test_fast.sh`, `test_smoke.sh`, `test_full.sh`,
# `test_nightly.sh`), then runs the Tier 4 nightly candidates with
# `NIGHTLY_ENABLE_EXPERIMENTAL=1`, then synthesises a deliberately-broken
# trace fixture and asserts that `test_tier2_trace.sh` correctly rejects
# it (catching a class of "fixture compare silently passing" bugs).
#
# **When to run**: before bumping Lean/Lake/elan toolchain versions, or
# after editing `scripts/test_lib.sh` / `scripts/_common.sh` / a tier-N
# script.  This is the meta-gate that every other gate hides behind.
#
# **Why not wire into Tier 4**: integrating this into
# `test_tier4_nightly_candidates.sh` would create a circular run (this
# script invokes `test_tier4_nightly_candidates.sh` already), so it is
# documented here and in `CLAUDE.md` as a manual umbrella check rather
# than auto-wired into a tier.
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
