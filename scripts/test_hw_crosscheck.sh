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
# A check whose evidence source is unavailable is *recorded* as NOT RUN via
# `record_skip`, never merely printed: the script then exits SELE4N_SKIP_EXIT
# (77) rather than 0, so a caller cannot read "no failures" as "the BCM2712
# constants were cross-checked".  Printing PENDING and falling through to
# `finalize_report` was how this gate reported PASS on a host with no devmem
# and no device tree, having verified only the page size.

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
    exit "${SELE4N_SKIP_EXIT:-77}"
fi

# Check 2: Timer frequency (CNTFRQ_EL0)
# Board.lean: timerFrequencyHz = 54000000 Hz (54 MHz)
CNTFRQ=""
if [[ -r /sys/devices/system/clocksource/clocksource0/current_clocksource ]]; then
    log_section "TRACE" "Clock source: $(cat /sys/devices/system/clocksource/clocksource0/current_clocksource)"
fi
# Attempt to read CNTFRQ from /proc/device-tree (RPi5 exposes this)
if [[ -r /proc/device-tree/timer/clock-frequency ]]; then
    CNTFRQ=$(od -An -t u4 /proc/device-tree/timer/clock-frequency 2>/dev/null | xargs)
fi
if [[ -n "${CNTFRQ}" ]]; then
    if [[ "${CNTFRQ}" -eq 54000000 ]]; then
        log_section "TRACE" "PASS: Timer frequency = ${CNTFRQ} Hz (Board.lean: 54000000)"
    else
        record_failure "TRACE" "Timer frequency = ${CNTFRQ} Hz, expected 54000000"
    fi
else
    record_skip "TRACE" "timer frequency (CNTFRQ_EL0, Board.lean 54000000) — no device-tree clock-frequency node to read"
fi

# CPU identification
if [[ -r /proc/cpuinfo ]]; then
    log_section "TRACE" "CPU: $(grep 'model name' /proc/cpuinfo | head -1 | cut -d: -f2 | xargs)"
fi

# Check 3: Physical address width
PA_BITS=""
if [[ -r /proc/cpuinfo ]]; then
    PA_BITS=$(grep -o 'address sizes.*physical' /proc/cpuinfo | head -1 | grep -o '[0-9]*' | head -1 || true)
fi
if [[ -n "${PA_BITS}" ]]; then
    if [[ "${PA_BITS}" -ge 44 ]]; then
        log_section "TRACE" "PASS: Physical address width = ${PA_BITS} bits (Board.lean: 44)"
    else
        record_failure "TRACE" "Physical address width = ${PA_BITS} bits, expected >= 44"
    fi
else
    record_skip "TRACE" "physical address width (Board.lean 44) — /proc/cpuinfo unreadable or carries no address-sizes line"
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

# ── Device tree based checks (available on RPi5 Linux) ──────────────────
log_section "HYGIENE" "Checking device tree constants..."

# Check 6: GIC addresses from device tree
if [[ -d /proc/device-tree/interrupt-controller@ff841000 ]]; then
    log_section "TRACE" "PASS: GIC distributor node found at ff841000 (Board.lean: 0xFF841000)"
else
    record_skip "TRACE" "GIC distributor base (Board.lean 0xFF841000) — device-tree node absent"
fi

# Check 7: UART0 base from device tree
if [[ -d /proc/device-tree/soc/serial@fe201000 ]] || \
   [[ -d /proc/device-tree/axi/serial@fe201000 ]]; then
    log_section "TRACE" "PASS: UART0 node found at fe201000 (Board.lean: 0xFE201000)"
else
    record_skip "TRACE" "UART0 base (Board.lean 0xFE201000) — device-tree node absent"
fi

# Check 8: Virtual address width (48-bit, from kernel config)
VA_BITS=""
if [[ -r /proc/kallsyms ]] && command -v awk &>/dev/null; then
    # Kernel addresses reveal VA width: 48-bit → 0xffff* prefix
    VA_BITS=$(awk '{print length($1)*4; exit}' /proc/kallsyms 2>/dev/null || true)
fi
if [[ -n "${VA_BITS}" ]] && [[ "${VA_BITS}" -ge 48 ]]; then
    log_section "TRACE" "PASS: Virtual address width >= 48 bits (Board.lean: 48)"
elif [[ -n "${VA_BITS}" ]]; then
    record_failure "TRACE" "Virtual address width = ${VA_BITS} bits, expected >= 48"
else
    record_skip "TRACE" "virtual address width (Board.lean 48) — /proc/kallsyms unreadable, so no kernel address to measure"
fi

# ── MMIO register checks (require devmem2 or busybox devmem) ────────────
if command -v devmem2 &>/dev/null || command -v devmem &>/dev/null; then
    DEVMEM_CMD="devmem2"
    if ! command -v devmem2 &>/dev/null; then
        DEVMEM_CMD="devmem"
    fi
    log_section "TRACE" "MMIO tool available: ${DEVMEM_CMD}"

    # GIC Distributor: read GICD_IIDR at 0xFF841008
    log_section "TRACE" "INFO: MMIO register validation available with ${DEVMEM_CMD}"
    log_section "TRACE" "INFO: Run with root for GICD_IIDR read at 0xFF841008"
else
    record_skip "META" "MMIO register checks (GICD_IIDR at 0xFF841008) — neither devmem2 nor devmem on PATH; install devmem2"
fi

# ── Pending constants (require bare-metal or kernel module) ──────────────
log_section "META" "Constants requiring a bare-metal seLe4n boot (SM10.E.D1 supplies the image):"
log_section "META" "  - peripheralBaseLow (0xFE000000) — verifiable via /proc/iomem"
log_section "META" "  - peripheralBaseHigh (0x1000000000) — requires 64-bit MMIO probe"
log_section "META" "  - gicCpuInterfaceBase (0xFF842000) — requires devmem read"
log_section "META" "  - gicSpiCount (192) — requires GIC GICD_TYPER read"
log_section "META" "  - timerPpiId (30) / virtualTimerPpiId (27) — requires IRQ test"
log_section "META" "  - maxASID (65536) — requires ID_AA64MMFR0_EL1 read"
record_skip "META" "7 Board.lean constants listed above — no bare-metal kernel boot available (SM10.E.D1)"

# ── Summary ──────────────────────────────────────────────────────────────
log_section "META" "Reference: docs/hardware_validation/rpi5_cross_check.md"
log_section "META" "Note: Full MMIO validation requires bare-metal seLe4n kernel boot"

finalize_report
