#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM1.H.1 — QEMU SMP secondary-core bring-up validation.
#
# Boots seLe4n under QEMU `virt -smp 4` with PSCI firmware enabled and
# verifies all 4 cores reach their per-core ready banner from
# `rust_secondary_main`.
#
# Skip conditions:
#   * `qemu-system-aarch64` missing on PATH → SKIP (no QEMU)
#   * Kernel image not built → SKIP (run `cargo build --target
#     aarch64-unknown-none --release -p sele4n-hal` first)
#
# Pass condition:
#   * Each of the 4 cores emits a per-core "ready" banner within the
#     timeout (cores 0..3).
#
# Fail condition:
#   * Fewer than 4 ready banners observed within timeout
#   * QEMU exited unexpectedly with errors
#
# Exit codes:
#   0  PASS or SKIP (both are non-failure for CI tier-4)
#   1  FAIL (boot trace incomplete)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

# ---------------------------------------------------------------------------
# Pre-flight checks
# ---------------------------------------------------------------------------

if ! command -v qemu-system-aarch64 &>/dev/null; then
  echo "[SKIP] WS-SM SM1.H.1: qemu-system-aarch64 not found on PATH"
  echo "       Install with: sudo apt-get install qemu-system-arm  (Debian/Ubuntu)"
  echo "                     brew install qemu                      (macOS)"
  exit 0
fi

# Default kernel image location.  The Cargo target triple `aarch64-unknown-none`
# produces a freestanding `.elf` that QEMU's `-kernel` flag understands directly.
# Allow override via $SELE4N_KERNEL_IMAGE for downstream CI configurations.
KERNEL_IMAGE="${SELE4N_KERNEL_IMAGE:-${REPO_ROOT}/rust/target/aarch64-unknown-none/release/sele4n-hal}"

if [[ ! -f "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM1.H.1: kernel image not found at ${KERNEL_IMAGE}"
  echo "       Build with: (cd rust && cargo build --target aarch64-unknown-none --release)"
  echo "       Or set SELE4N_KERNEL_IMAGE to point at a pre-built image."
  exit 0
fi

# ---------------------------------------------------------------------------
# QEMU invocation
# ---------------------------------------------------------------------------

# Capture UART output to a temporary log so we can grep it after QEMU exits.
LOG="$(mktemp -t sele4n-smp-bringup.XXXXXX.log)"
# shellcheck disable=SC2064  # We want $LOG expanded NOW, not at exit.
trap "rm -f '${LOG}'" EXIT

# Run QEMU with:
#   * `-machine virt,secure=on,virtualization=on` — enables EL2/EL3 so PSCI
#     firmware (built into QEMU's `virt` machine) is functional.
#   * `-cpu cortex-a76` — RPi5 CPU model.  PSCI is implemented by QEMU's
#     own firmware at EL3; the kernel runs at EL1.
#   * `-smp 4` — 4 cores total (matches RPi5 BCM2712 / `MAX_SECONDARY_CORES + 1`).
#   * `-m 1G` — 1 GiB RAM (sufficient for boot diagnostics).
#   * `-kernel ${KERNEL_IMAGE}` — load the freestanding kernel ELF at the
#     `virt` machine's load address.
#   * `-nographic` + `-serial mon:stdio` — UART output to stdout so we can
#     capture and grep it.
#   * `-d guest_errors` — log guest exceptions to QEMU's stderr (useful
#     for diagnosing a hung secondary).
#
# Timeout via `timeout` so a hung kernel cannot pin CI forever.  30 seconds
# is generous: a healthy boot completes in under 5s on a modern host.
TIMEOUT_SECS="${SELE4N_QEMU_TIMEOUT_SECS:-30}"

echo "[META] WS-SM SM1.H.1: booting QEMU virt -smp 4 (timeout: ${TIMEOUT_SECS}s)"
echo "[META]   kernel image: ${KERNEL_IMAGE}"
echo "[META]   log: ${LOG}"

set +e
timeout "${TIMEOUT_SECS}s" qemu-system-aarch64 \
    -machine "virt,secure=on,virtualization=on" \
    -cpu cortex-a76 \
    -smp 4 \
    -m 1G \
    -kernel "${KERNEL_IMAGE}" \
    -nographic \
    -serial mon:stdio \
    -d guest_errors \
    < /dev/null \
    > "${LOG}" 2>&1
QEMU_EXIT=$?
set -e

# `timeout` exits 124 when the budget is hit.  In our case that's the
# expected outcome — the kernel doesn't shut down on its own — so we treat
# 124 as "QEMU ran for the full budget".  Any other non-zero exit means
# QEMU itself errored (e.g., bad kernel image).
case "${QEMU_EXIT}" in
  0|124)
    # Expected: 0 (clean exit, unlikely) or 124 (timeout, expected).
    ;;
  *)
    echo "[FAIL] WS-SM SM1.H.1: QEMU exited with code ${QEMU_EXIT}" >&2
    echo "       Last 40 lines of UART log:" >&2
    tail -n 40 "${LOG}" >&2
    exit 1
    ;;
esac

# ---------------------------------------------------------------------------
# Banner verification (SM1.H.4)
# ---------------------------------------------------------------------------
#
# Per the SM1.C.5 boot trace, each secondary core emits banners of the form:
#
#   [smp] core N: entering per-core init
#   [smp] core N: MMU enabled (...)
#   [smp] core N: VBAR_EL1 installed
#   [smp] core N: GIC-400 CPU interface initialized (...)
#   [smp] core N: timer armed at 1000 Hz
#   [smp] core N: IRQ delivery enabled
#   [smp] core N: ready, entering kernel
#
# We grep for the final "ready, entering kernel" banner per core because
# that's the structural witness that ALL prior init steps succeeded
# (a failure in any earlier step halts the offending core in its WFE
# fallback before reaching this line).

echo "[META] WS-SM SM1.H.1: verifying per-core ready banners"

EXPECTED_CORES=("1" "2" "3")  # boot core (0) doesn't go through rust_secondary_main
MISSING_CORES=()
for core in "${EXPECTED_CORES[@]}"; do
  if ! grep -q "\[smp\] core ${core}: ready, entering kernel" "${LOG}"; then
    MISSING_CORES+=("${core}")
  fi
done

# Also verify the boot core completed Phase 5 (the SMP bring-up).  This is
# the "structural witness" that the kernel reached the post-handoff point
# rather than hanging earlier in the boot sequence.
if ! grep -qE "\[boot\] Phase 5: [0-9]+ secondary core\(s\) online" "${LOG}"; then
  MISSING_CORES+=("0 (Phase 5 banner missing)")
fi

if [[ "${#MISSING_CORES[@]}" -gt 0 ]]; then
  echo "[FAIL] WS-SM SM1.H.1: missing ready banner(s) for core(s): ${MISSING_CORES[*]}" >&2
  echo "       Last 80 lines of UART log:" >&2
  tail -n 80 "${LOG}" >&2
  exit 1
fi

echo "[PASS] WS-SM SM1.H.1: all 4 cores online, secondaries 1..3 ready, primary completed Phase 5"
exit 0
