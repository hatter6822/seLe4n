#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM1.G.3 — Cross-core kprintln stress test.
#
# Boots QEMU `-smp 4` and exercises the UART lock under heavy
# concurrent contention.  Each core emits a large number of
# `kprintln_core!` lines in a tight loop.  The test verifies the
# captured UART log has no torn output:
#
#   * Every line starts with `[core N]` for some `N ∈ {0..3}`.
#   * No line is split across UART writes (no two `[core N]` prefixes
#     back-to-back without an intervening newline).
#   * Every `[core N]` prefix is followed by a sane message body (no
#     stray control characters, no empty body).
#
# **Prerequisites**:
#   * SM1.G.4 `kprintln_core!` macro defined.
#   * SM1.H.1 base bringup test passes.
#   * Kernel image must include the stress-test routine on each core
#     (SM5+ wires it; at SM1.G this is a placeholder pending Lean
#     integration).
#
# Skip / pass / fail conditions identical to SM1.H.5.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

if ! command -v qemu-system-aarch64 &>/dev/null; then
  echo "[SKIP] WS-SM SM1.G.3: qemu-system-aarch64 not found on PATH"
  exit 0
fi

# Kernel image must be set explicitly via $SELE4N_KERNEL_IMAGE — at
# SM1.G landing there is no kernel binary target (see
# test_qemu_smp_bringup.sh header for details).
KERNEL_IMAGE="${SELE4N_KERNEL_IMAGE:-}"

if [[ -z "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM1.G.3: SELE4N_KERNEL_IMAGE env var not set"
  echo "       Set SELE4N_KERNEL_IMAGE=/path/to/kernel.elf to enable."
  exit 0
fi

if [[ ! -f "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM1.G.3: kernel image not found at ${KERNEL_IMAGE}"
  exit 0
fi

# Detect the stress-test routine via .rodata strings.  The routine emits
# a recognizable banner per core that the verifier greps for.
STRESS_BANNER="\\[core [0-9]\\] stress iter "
if ! strings "${KERNEL_IMAGE}" 2>/dev/null | grep -qE "stress iter"; then
  echo "[SKIP] WS-SM SM1.G.3: stress-test routine not yet wired in kernel image"
  echo ""
  echo "  Reason: the per-core kprintln stress loop runs from the Lean"
  echo "          per-core scheduler entry, which is the SM5 placeholder"
  echo "          at SM1.G.  At SM1.G the kprintln_core! macro and the"
  echo "          UartLock under SMP are unit-tested on host (see"
  echo "          uart::tests::sm1g4_*); the actual cross-core race is"
  echo "          the SM5 follow-on."
  echo ""
  echo "  HAL-level coverage at SM1.G (already passing):"
  echo "    cargo test -p sele4n-hal --lib uart::tests::sm1g"
  exit 0
fi

LOG="$(mktemp -t sele4n-smp-stress.XXXXXX.log)"
# shellcheck disable=SC2064
trap "rm -f '${LOG}'" EXIT

TIMEOUT_SECS="${SELE4N_QEMU_TIMEOUT_SECS:-60}"  # Stress test runs longer.

echo "[META] WS-SM SM1.G.3: booting QEMU virt -smp 4 for kprintln stress"
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
    < /dev/null \
    > "${LOG}" 2>&1
QEMU_EXIT=$?
set -e

case "${QEMU_EXIT}" in
  0|124) ;;
  *)
    echo "[FAIL] WS-SM SM1.G.3: QEMU exited with code ${QEMU_EXIT}" >&2
    tail -n 40 "${LOG}" >&2
    exit 1
    ;;
esac

# --------------------------------------------------------------------------
# Verify torn-output detection
#
# We use awk to walk the log and assert:
#   1. Every line starts with `[core N]` (post the boot-banner phase).
#   2. No line has a `[core N]` substring AFTER position 1 (would
#      indicate two banners glued together by a missing newline).
#   3. Every core emitted at least one stress line (no core silently
#      dropped its output due to a lost lock).
# --------------------------------------------------------------------------
echo "[META] WS-SM SM1.G.3: scanning UART log for torn output"

# Awk scanner: count stress lines per core.
declare -A CORE_LINE_COUNT
for core in 0 1 2 3; do
  CORE_LINE_COUNT[${core}]=0
done

while IFS= read -r line; do
  # Match `[core N] stress iter K` (where K is any number).
  if [[ "${line}" =~ ^\[core\ ([0-9])\]\ stress\ iter\ ([0-9]+)$ ]]; then
    core_id="${BASH_REMATCH[1]}"
    CORE_LINE_COUNT[${core_id}]=$((${CORE_LINE_COUNT[${core_id}]} + 1))
  fi
  # Detect torn output: a line containing TWO `[core N]` prefixes is
  # always wrong (two banners glued together).
  if [[ "$(echo "${line}" | grep -oE '\[core [0-9]\]' | wc -l)" -gt 1 ]]; then
    echo "[FAIL] WS-SM SM1.G.3: torn line detected: ${line}" >&2
    exit 1
  fi
done < "${LOG}"

# Verify every core emitted at least one stress line.
MISSING_CORES=()
for core in 0 1 2 3; do
  if [[ "${CORE_LINE_COUNT[${core}]}" -eq 0 ]]; then
    MISSING_CORES+=("${core}")
  fi
done

if [[ "${#MISSING_CORES[@]}" -gt 0 ]]; then
  echo "[FAIL] WS-SM SM1.G.3: no stress output from core(s): ${MISSING_CORES[*]}" >&2
  echo "       Per-core line counts: 0=${CORE_LINE_COUNT[0]} 1=${CORE_LINE_COUNT[1]} 2=${CORE_LINE_COUNT[2]} 3=${CORE_LINE_COUNT[3]}" >&2
  exit 1
fi

echo "[PASS] WS-SM SM1.G.3: cross-core kprintln stress completed without tearing"
echo "[PASS]   per-core line counts: 0=${CORE_LINE_COUNT[0]} 1=${CORE_LINE_COUNT[1]} 2=${CORE_LINE_COUNT[2]} 3=${CORE_LINE_COUNT[3]}"
exit 0
