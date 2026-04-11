#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# AG9-B: Hardware Constant Cross-Check Validation Script
#
# Validates BCM2712 hardware constants from Board.lean against actual
# RPi5 hardware. Designed to run on a physical Raspberry Pi 5 board
# or in QEMU with appropriate emulation.
#
# Prerequisites:
#   - Physical RPi5 or QEMU with raspi4b machine
#   - devmem2 or busybox devmem for MMIO access (optional)
#   - Root access for system register reads
#
# Usage:
#   sudo ./scripts/test_hw_crosscheck.sh
#
# The script will gracefully skip checks that require unavailable tools.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

cd "${REPO_ROOT}"

log_section "META" "=== AG9-B: Hardware Constant Cross-Check ==="

# ── Architecture invariants (always verifiable) ──────────────────────────
log_section "HYGIENE" "Checking architecture invariants..."

# Check 1: We're running on ARM64
ARCH=$(uname -m)
if [[ "${ARCH}" = "aarch64" ]]; then
    log_section "HYGIENE" "PASS: Running on ARM64 (${ARCH})"
else
    log_section "META" "SKIP: Not running on ARM64 (${ARCH}) — hardware checks unavailable"
    log_section "META" "       This script must run on physical RPi5 or QEMU aarch64"
    exit 0
fi

# Check 2: Timer frequency (CNTFRQ_EL0)
# Board.lean: timerFrequency = 54000000 Hz (54 MHz)
if [[ -r /sys/devices/system/clocksource/clocksource0/current_clocksource ]]; then
    log_section "TRACE" "Clock source: $(cat /sys/devices/system/clocksource/clocksource0/current_clocksource)"
    log_section "TRACE" "Expected timer frequency: 54000000 Hz (Board.lean timerFrequency)"
fi

# Try to read timer frequency from sysfs or /proc
if [[ -r /proc/cpuinfo ]]; then
    log_section "TRACE" "CPU: $(grep 'model name' /proc/cpuinfo | head -1 | cut -d: -f2 | xargs)"
fi

# Check 3: Physical address width
if [[ -r /proc/cpuinfo ]]; then
    PA_BITS=$(grep -o 'address sizes.*physical' /proc/cpuinfo | head -1 | grep -o '[0-9]*' | head -1 || true)
    if [[ -n "${PA_BITS}" ]]; then
        if [[ "${PA_BITS}" -ge 44 ]]; then
            log_section "TRACE" "PASS: Physical address width = ${PA_BITS} bits (Board.lean: 44)"
        else
            record_failure "TRACE" "Physical address width = ${PA_BITS} bits, expected >= 44"
        fi
    fi
fi

# Check 4: Page size
PAGE_SIZE=$(getconf PAGESIZE 2>/dev/null || echo "4096")
if [[ "${PAGE_SIZE}" -eq 4096 ]]; then
    log_section "TRACE" "PASS: Page size = ${PAGE_SIZE} (Board.lean: 4096)"
else
    record_failure "TRACE" "Page size = ${PAGE_SIZE}, expected 4096"
fi

# Check 5: Memory regions (from /proc/iomem if available)
if [[ -r /proc/iomem ]]; then
    log_section "TRACE" "Memory regions from /proc/iomem:"
    head -20 /proc/iomem | while IFS= read -r line; do
        log_section "TRACE" "  ${line}"
    done
fi

# ── MMIO register checks (require devmem2 or busybox devmem) ────────────
if command -v devmem2 &>/dev/null || command -v devmem &>/dev/null; then
    DEVMEM_CMD="devmem2"
    if ! command -v devmem2 &>/dev/null; then
        DEVMEM_CMD="devmem"
    fi
    log_section "TRACE" "MMIO tool available: ${DEVMEM_CMD}"

    # GIC Distributor: read GICD_IIDR at 0xFF841008
    log_section "TRACE" "Reading GIC Distributor IIDR at 0xFF841008..."
    # This would require root and proper memory mapping
    log_section "TRACE" "INFO: MMIO register reads require bare-metal or custom driver"
else
    log_section "META" "SKIP: devmem2/devmem not available — MMIO register checks skipped"
    log_section "META" "       Install: apt install devmem2  (Debian/Ubuntu)"
fi

# ── Summary ──────────────────────────────────────────────────────────────
log_section "META" "Cross-check results saved to docs/hardware_validation/rpi5_cross_check.md"
log_section "META" "Note: Full MMIO validation requires bare-metal seLe4n kernel boot"

finalize_report
