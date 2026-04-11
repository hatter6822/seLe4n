#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# AG9-G: Full RPi5 Hardware Test Suite Runner
#
# Executes the complete tiered test suite plus hardware-specific validation
# on a physical Raspberry Pi 5 or compatible ARM64 system.
#
# Test Sequence:
#   1. Lean tiered test suite (Tier 0-3)
#   2. Rust workspace tests
#   3. Hardware cross-check (AG9-B)
#   4. QEMU integration tests (AG9-A, if QEMU available)
#   5. Badge overflow validation (AG9-E)
#
# Usage:
#   ./scripts/test_hw_full.sh              # Run full hardware test suite
#   ./scripts/test_hw_full.sh --continue   # Continue past failures

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

log_section "META" "=== AG9-G: Full RPi5 Hardware Test Suite ==="
log_section "META" "Platform: $(uname -m) / $(uname -s) / $(uname -r)"
log_section "META" ""

# ── Phase 1: Lean Tiered Tests (Tier 0-3) ─────────────────────────────
log_section "META" "--- Phase 1: Lean Tiered Tests ---"
run_check "META" "${SCRIPT_DIR}/test_full.sh" "${sub_args[@]}"

# ── Phase 2: Rust Workspace Tests ─────────────────────────────────────
log_section "META" "--- Phase 2: Rust Workspace Tests ---"
run_check "META" "${SCRIPT_DIR}/test_rust.sh"

# ── Phase 3: Badge Overflow Validation (AG9-E) ────────────────────────
log_section "META" "--- Phase 3: Badge Overflow Validation (AG9-E) ---"
ensure_lake_available
run_check "BUILD" lake exe badge_overflow_suite

# ── Phase 4: Hardware Cross-Check (AG9-B) ─────────────────────────────
log_section "META" "--- Phase 4: Hardware Cross-Check (AG9-B) ---"
if [[ "$(uname -m)" = "aarch64" ]]; then
    run_check "META" "${SCRIPT_DIR}/test_hw_crosscheck.sh"
else
    log_section "META" "SKIP: Not ARM64 — hardware cross-check skipped"
fi

# ── Phase 5: QEMU Integration (AG9-A) ─────────────────────────────────
log_section "META" "--- Phase 5: QEMU Integration Tests (AG9-A) ---"
if command -v qemu-system-aarch64 &>/dev/null; then
    run_check "META" "${SCRIPT_DIR}/test_qemu.sh"
else
    log_section "META" "SKIP: qemu-system-aarch64 not available — QEMU tests skipped"
fi

# ── Summary ───────────────────────────────────────────────────────────
log_section "META" ""
log_section "META" "=== AG9-G: Full Hardware Test Suite Complete ==="

finalize_report
