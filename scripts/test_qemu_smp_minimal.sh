#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM1.H.3 — Minimal SMP boot test (`-smp 2`).
#
# Companion to `test_qemu_smp_bringup.sh` for diagnostics with reduced
# parallelism.  Boots QEMU with one boot core + one secondary, useful for:
#
#   * Hunting an SMP-specific regression — `-smp 2` exercises the
#     secondary code path with minimum interleaving (only one secondary
#     racing with the primary).
#   * CI configurations with limited host cores where `-smp 4` would
#     time-share aggressively.
#   * Quick smoke check after a HAL change (faster than `-smp 4`).
#
# Skip / pass / fail conditions are identical to SM1.H.1 except the
# expected core count is 2 (boot + 1 secondary).

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

if ! command -v qemu-system-aarch64 &>/dev/null; then
  echo "[SKIP] WS-SM SM1.H.3: qemu-system-aarch64 not found on PATH"
  exit 0
fi

KERNEL_IMAGE="${SELE4N_KERNEL_IMAGE:-${REPO_ROOT}/rust/target/aarch64-unknown-none/release/sele4n-hal}"

if [[ ! -f "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM1.H.3: kernel image not found at ${KERNEL_IMAGE}"
  echo "       Build with: (cd rust && cargo build --target aarch64-unknown-none --release)"
  exit 0
fi

LOG="$(mktemp -t sele4n-smp-minimal.XXXXXX.log)"
# shellcheck disable=SC2064
trap "rm -f '${LOG}'" EXIT

TIMEOUT_SECS="${SELE4N_QEMU_TIMEOUT_SECS:-30}"

echo "[META] WS-SM SM1.H.3: booting QEMU virt -smp 2 (timeout: ${TIMEOUT_SECS}s)"
echo "[META]   kernel image: ${KERNEL_IMAGE}"
echo "[META]   log: ${LOG}"

set +e
timeout "${TIMEOUT_SECS}s" qemu-system-aarch64 \
    -machine "virt,secure=on,virtualization=on" \
    -cpu cortex-a76 \
    -smp 2 \
    -m 1G \
    -kernel "${KERNEL_IMAGE}" \
    -nographic \
    -serial mon:stdio \
    -d guest_errors \
    < /dev/null \
    > "${LOG}" 2>&1
QEMU_EXIT=$?
set -e

case "${QEMU_EXIT}" in
  0|124) ;;
  *)
    echo "[FAIL] WS-SM SM1.H.3: QEMU exited with code ${QEMU_EXIT}" >&2
    echo "       Last 40 lines of UART log:" >&2
    tail -n 40 "${LOG}" >&2
    exit 1
    ;;
esac

echo "[META] WS-SM SM1.H.3: verifying secondary 1 ready banner"

# Boot core (0) doesn't go through rust_secondary_main; only secondary 1 emits.
if ! grep -q "\[smp\] core 1: ready, entering kernel" "${LOG}"; then
  echo "[FAIL] WS-SM SM1.H.3: secondary core 1 did not emit ready banner" >&2
  echo "       Last 80 lines of UART log:" >&2
  tail -n 80 "${LOG}" >&2
  exit 1
fi

# Boot core completed Phase 5: 1 secondary online.
if ! grep -q "\[boot\] Phase 5: 1 secondary core(s) online" "${LOG}"; then
  echo "[FAIL] WS-SM SM1.H.3: Phase 5 did not report exactly 1 secondary online" >&2
  echo "       Last 80 lines of UART log:" >&2
  tail -n 80 "${LOG}" >&2
  exit 1
fi

echo "[PASS] WS-SM SM1.H.3: minimal SMP (boot + 1 secondary) bringup successful"
exit 0
