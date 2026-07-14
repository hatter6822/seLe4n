#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM6.F.5 (plan §SM6.F Tier-4) — Cross-core IPC handshake round-trip test.
#
# Boots QEMU `-smp 4` with seLe4n and exercises the cross-core IPC rendezvous
# end-to-end: a client on core 0 `Call`s an endpoint whose server is homed on
# core 1; the kernel wakes the server on its home core, commits the verified
# post-state, and fires a `.reschedule` SGI to core 1 (`fireCrossCoreSgis` via
# `syscallDispatchCrossCoreEntry`); core 1's SGI handler dispatches the server;
# the server's `Reply` wakes the client back on core 0 the same way.  The
# runtime witness for SM6's cross-core IPC: a remote wake is not merely
# computed but actually delivered + rescheduled — on real hardware-modelled
# cores, with a real GIC delivering the SGI.
#
# **What the formal layer already guarantees (SM6.A–F, no QEMU needed)**:
#   * `endpointCallOnCore_emits_sgi_if_remote_receiver` — a rendezvous with a
#     remote-homed receiver emits exactly a `.reschedule` SGI to its home core
#     (Thm 3.2.1).
#   * `endpointReplyOnCore_remote_wake` — a reply to a remote-homed caller
#     emits the dual SGI to the caller's home core (SM6.C.2).
#   * `notificationSignalOnCore_remote_wake` — a signal waking a remote-homed
#     waiter pokes its home core (SM6.B.2).
#   * `crossCoreSgiBody_remote_wake` — the live diff seam re-derives the wake
#     SGI on the committed (pre, post) state pair (v0.31.72 audit closure).
#   * `endpointCallOnCore_perCore_blocking` / `endpointReplyOnCore_perCore_delivery`
#     — the caller blocks on its own core; the payload reaches exactly the
#     recorded caller.
#   * `…_preserves_ipcInvariantFull_perCore` — every IPC operation preserves
#     every core's twenty-conjunct invariant bundle view (SM6.D).
#   These are machine-checked in tests/SmpIpcSuite.lean,
#   tests/SmpNotificationSuite.lean, and the per-phase SM6 suites (Tier 2/3),
#   and hold for ALL executions — the QEMU test is a complementary *runtime*
#   spot-check.
#
# **Prerequisites (SM9.E)**:
#   * A bootable kernel-image `[[bin]]` target linking the Rust HAL against the
#     Lean kernel object code (the recurring SM9.E closure item).
#   * A cross-core IPC driver in the kernel image: two threads homed on
#     different cores performing a Call/Reply handshake through the live
#     `syscallDispatchCrossCoreEntry` seam, emitting the banner below.
#
# At v0.32.x the live Lean dispatch is fully cross-core (`.call` / `.reply` /
# `.replyRecv` / `.notificationSignal` / `.notificationWait` route through the
# SM6 OnCore operations and the SGI-firing seam), but no bootable kernel-image
# binary target exists yet.  This script therefore SKIPs with a documentation
# banner until that image exists.
#
# Skip / pass / fail conditions:
#   * No QEMU on PATH                    → SKIP
#   * No kernel image                    → SKIP
#   * Cross-core IPC driver unwired      → SKIP (current state, SM6.F)
#   * Wake SGI lost / no reschedule      → FAIL
#   * Reply delivered across cores       → PASS

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

if ! command -v qemu-system-aarch64 &>/dev/null; then
  echo "[SKIP] WS-SM SM6.F.5: qemu-system-aarch64 not found on PATH"
  exit 0
fi

KERNEL_IMAGE="${SELE4N_KERNEL_IMAGE:-}"

if [[ -z "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM6.F.5: SELE4N_KERNEL_IMAGE env var not set"
  echo "       Set SELE4N_KERNEL_IMAGE=/path/to/kernel.elf to enable."
  exit 0
fi

if [[ ! -f "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM6.F.5: kernel image not found at ${KERNEL_IMAGE}"
  exit 0
fi

# --------------------------------------------------------------------------
# Pre-condition: the cross-core IPC driver must be wired in the kernel image.
# We detect it by the banner the driver emits.  At SM6.F the driver is NOT
# present (it needs the SM9.E bootable kernel-image binary target), so this
# SKIPs.
#
# Capture `strings` output into a variable first, *then* grep it: under
# `set -o pipefail`, a `strings … | grep -q` pipeline can report failure even on
# a match — `grep -q` exits at the first hit and `strings` then dies with
# SIGPIPE (exit 141), failing the pipeline.  That would silently SKIP a wired
# Tier-4 test.  The capture (with `|| true` so a `strings` read error is benign)
# decouples the two stages and avoids the SIGPIPE.
# --------------------------------------------------------------------------
KERNEL_STRINGS="$(strings "${KERNEL_IMAGE}" 2>/dev/null || true)"
if ! grep -q "smp-test.*cross-core-ipc" <<<"${KERNEL_STRINGS}"; then
  echo "[SKIP] WS-SM SM6.F.5: cross-core IPC driver not wired in kernel image"
  echo ""
  echo "  Reason: exercising a real cross-core IPC handshake requires the SM9.E"
  echo "          bootable kernel-image [[bin]] target (Rust HAL linked against the"
  echo "          Lean kernel object code) plus an in-image driver: a client on"
  echo "          core 0 Call-ing an endpoint whose server is homed on core 1,"
  echo "          through the live syscallDispatchCrossCoreEntry seam.  The"
  echo "          cross-core IPC correctness guarantee is established FORMALLY"
  echo "          (and for ALL executions) by:"
  echo "            endpointCallOnCore_emits_sgi_if_remote_receiver  (Thm 3.2.1)"
  echo "            endpointReplyOnCore_remote_wake                  (SM6.C.2)"
  echo "            notificationSignalOnCore_remote_wake             (SM6.B.2)"
  echo "            crossCoreSgiBody_remote_wake                     (live diff seam)"
  echo "            …_preserves_ipcInvariantFull_perCore             (SM6.D bundle)"
  echo "          machine-checked in tests/SmpIpcSuite.lean and"
  echo "          tests/SmpNotificationSuite.lean."
  echo ""
  echo "  When wired (SM9.E), this script will:"
  echo "    1. Boot QEMU virt -smp 4."
  echo "    2. Have a client on core 0 Call an endpoint whose server is homed on"
  echo "       core 1; the kernel wakes the server on core 1 and fires the"
  echo "       .reschedule SGI (fireCrossCoreSgis)."
  echo "    3. Assert core 1's SGI handler dispatches the server, and the server's"
  echo "       Reply wakes the client back on core 0 with the reply payload."
  echo "    4. Assert '[smp-test] cross-core-ipc: reply delivered across cores'."
  echo ""
  echo "  Formal coverage at SM6.F (already passing):"
  echo "    lake exe smp_ipc_suite"
  echo "    lake exe smp_notification_suite"
  exit 0
fi

# --------------------------------------------------------------------------
# Run the test (only reached if the cross-core IPC driver is wired)
# --------------------------------------------------------------------------
LOG="$(mktemp -t sele4n-smp-ipc.XXXXXX.log)"
# shellcheck disable=SC2064
trap "rm -f '${LOG}'" EXIT

TIMEOUT_SECS="${SELE4N_QEMU_TIMEOUT_SECS:-60}"

echo "[META] WS-SM SM6.F.5: booting QEMU virt -smp 4 for cross-core IPC handshake"
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

if grep -q "smp-test.*cross-core-ipc: reply delivered across cores" "${LOG}"; then
  echo "[PASS] WS-SM SM6.F.5: cross-core IPC handshake completed (call wake + reply wake)"
  exit 0
else
  echo "[FAIL] WS-SM SM6.F.5: cross-core IPC handshake banner not observed (qemu exit ${QEMU_EXIT})"
  echo "------ QEMU log tail ------"
  tail -40 "${LOG}" || true
  exit 1
fi
