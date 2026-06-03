#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM5.G.6 (plan §6 Tier-4) — Per-core domain-scheduling rotation test.
#
# Boots QEMU `-smp 4` with seLe4n and exercises per-core domain scheduling: each
# core independently rotates its OWN domain schedule (plan §3.7 / §4.2), so at a
# given instant different cores can be in different scheduling domains.  The runtime
# witness for SM5.G: a per-core domain tick on each core advances THAT core's active
# domain through the (shared) domain-schedule table without disturbing the other
# cores' domain state, and the rotation cycles with the schedule's period.
#
# **What the formal layer already guarantees (SM5.G, no QEMU needed)**:
#   * `advanceDomainOnCore_cyclic` — iterating the rotation `domainSchedule.length`
#     times returns the schedule index to its start (the round-robin period).
#   * `advanceDomainOnCore_cyclic_activeDomain` — the active domain (not just the
#     index) cycles with period `length` from a consistent, in-bounds state.
#   * `advanceDomainOnCore_establishes_activeDomainOnCore_isInDomainSchedule` +
#     `scheduleDomainOnCore_preserves_activeDomainOnCore_isInDomainSchedule` — every
#     rotation lands the active domain in the schedule, preserved by the live tick.
#   * `chooseThreadOnCore_respects_activeDomain` — selection never dispatches a
#     thread of a domain other than the core's current active one (the domain
#     barrier / temporal isolation).
#   * `advanceDomainOnCore_independent_of_other_core` — rotating one core's domain
#     leaves every other core's selection unchanged (cross-core independence).
#   These are machine-checked in `tests/SmpDomainSuite.lean` (Tier 2/3) and hold for
#   ALL executions — the QEMU test is a complementary *runtime* spot-check.
#
# **Prerequisites (SM5.I+)**:
#   * A non-empty per-core domain schedule configured at boot (multi-domain mode).
#   * The per-core run loop driving `scheduleDomainOnCore` on each core's timer tick
#     (the SM5.I per-core scheduler-tick driver).
#   * A per-core domain-rotation driver in the kernel image emitting the banner below.
#
# At v0.31.52 (this script's landing) the kernel is modelled single-core at the
# abstract layer; the per-core scheduler tick that drives `scheduleDomainOnCore` per
# core lands at SM5.I.  This script therefore SKIPs with a documentation banner until
# that wiring exists.
#
# Skip / pass / fail conditions:
#   * No QEMU on PATH                       → SKIP
#   * No kernel image                       → SKIP
#   * Per-core domain driver unwired        → SKIP (current state, SM5.G)
#   * A core fails to rotate / cross-core leak → FAIL
#   * Each core rotates its own domain      → PASS

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

if ! command -v qemu-system-aarch64 &>/dev/null; then
  echo "[SKIP] WS-SM SM5.G.6: qemu-system-aarch64 not found on PATH"
  exit 0
fi

KERNEL_IMAGE="${SELE4N_KERNEL_IMAGE:-}"

if [[ -z "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM5.G.6: SELE4N_KERNEL_IMAGE env var not set"
  echo "       Set SELE4N_KERNEL_IMAGE=/path/to/kernel.elf to enable."
  exit 0
fi

if [[ ! -f "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM5.G.6: kernel image not found at ${KERNEL_IMAGE}"
  exit 0
fi

# --------------------------------------------------------------------------
# Pre-condition: the per-core domain-rotation driver must be wired in the kernel
# image.  Detect it by the banner the driver emits.  At SM5.G the driver is NOT
# present (it needs SM5.I's per-core scheduler tick driving scheduleDomainOnCore),
# so this SKIPs.  Capture `strings` first, then grep, to avoid a SIGPIPE under
# `set -o pipefail` (see test_qemu_smp_pip.sh for the rationale).
# --------------------------------------------------------------------------
KERNEL_STRINGS="$(strings "${KERNEL_IMAGE}" 2>/dev/null || true)"
if ! grep -q "smp-test.*per-core-domain" <<<"${KERNEL_STRINGS}"; then
  echo "[SKIP] WS-SM SM5.G.6: per-core domain-rotation driver not wired in kernel image"
  echo ""
  echo "  Reason: exercising real per-core domain rotation requires SM5.I's per-core"
  echo "          scheduler tick driving scheduleDomainOnCore on each core, plus a"
  echo "          multi-domain schedule configured at boot.  At SM5.G the kernel is"
  echo "          modelled single-core; the per-core domain-scheduling correctness"
  echo "          guarantee is established FORMALLY (and for ALL executions) by:"
  echo "            advanceDomainOnCore_cyclic                  (round-robin period)"
  echo "            advanceDomainOnCore_cyclic_activeDomain      (active domain cycles)"
  echo "            scheduleDomainOnCore_preserves_activeDomainOnCore_isInDomainSchedule"
  echo "            chooseThreadOnCore_respects_activeDomain     (domain barrier)"
  echo "            advanceDomainOnCore_independent_of_other_core (cross-core indep.)"
  echo "          machine-checked in tests/SmpDomainSuite.lean."
  echo ""
  echo "  When wired (SM5.I), this script will:"
  echo "    1. Boot QEMU virt -smp 4 with a multi-domain schedule."
  echo "    2. Tick each core's timer so each rotates its own domain."
  echo "    3. Assert each core advances its OWN active domain and frames the others'."
  echo "    4. Assert '[smp-test] per-core-domain: all cores rotated independently'."
  echo ""
  echo "  Formal coverage at SM5.G (already passing):"
  echo "    lake exe smp_domain_suite"
  exit 0
fi

# --------------------------------------------------------------------------
# Run the test (only reached if the per-core domain driver is wired)
# --------------------------------------------------------------------------
LOG="$(mktemp -t sele4n-smp-domain.XXXXXX.log)"
# shellcheck disable=SC2064
trap "rm -f '${LOG}'" EXIT

TIMEOUT_SECS="${SELE4N_QEMU_TIMEOUT_SECS:-60}"

echo "[META] WS-SM SM5.G.6: booting QEMU virt -smp 4 for per-core domain rotation"
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

if grep -q "smp-test.*per-core-domain: all cores rotated independently" "${LOG}"; then
  echo "[PASS] WS-SM SM5.G.6: each core rotated its own domain schedule independently"
  exit 0
else
  echo "[FAIL] WS-SM SM5.G.6: per-core domain-rotation banner not observed (qemu exit ${QEMU_EXIT})"
  echo "------ QEMU log tail ------"
  tail -40 "${LOG}" || true
  exit 1
fi
