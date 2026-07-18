#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM7.B (plan Appendix A Tier-4) — TLB shootdown round-trip test.
#
# Boots QEMU `-smp 4` with seLe4n and exercises the SM7.B shootdown round
# end-to-end: a thread on core 0 unmaps a page whose translation core 1 has
# cached; the kernel commits the verified posting (`vspaceUnmapPageWithShootdown`),
# the dispatch seam (`completeShootdownRounds`) resets the masked ack vector,
# fires `.tlbShootdownReq` SGIs at the online targets, retires the initiator's
# local broadcast TLBIs, and bounded-waits for `allAcked`; each target's SGI
# handler TLBIs locally and release-acknowledges; core 1's subsequent access
# through the stale VA must fault (translation re-walk finds the unmap).
#
# **What the formal layer already guarantees (SM7.A–B, no QEMU needed)**:
#   * `tlbShootdownBroadcast_invalidatesAllCores` — Theorem 3.3.1: after a
#     completed round no core's view retains a covered entry.
#   * `shootdownRound_tlb_no_matching_entry` — the end-to-end single-view
#     corollary over the real `shootdownRound` pipeline.
#   * `vspaceUnmapPageWithShootdown_remote_retire_removes` — the coalescing
#     (total-posting) remote case the live wrappers actually use.
#   * `shootdownAck_release_acquire` (+ the 4-core multi-pair witness) — every
#     target's TLBI retirement happens-before the initiator's allAcked
#     observation.
#   * `shootdown_timeout_handling` — the bounded wait's verdict is exact, so
#     the fail-closed panic fires only on a genuinely hung round.
#   * `coalescingRound_restores_quiescent` / `coalescingRound_allAcked` — the
#     live round restores quiescence and reaches the wait's exit condition.
#   These are machine-checked in tests/SmpTlbShootdownSuite.lean (Tier 2/3)
#   and hold for ALL executions — the QEMU test is a complementary *runtime*
#   spot-check with a real GIC delivering the SGIs.
#
# **Prerequisites (SM9.E)**:
#   * A bootable kernel-image `[[bin]]` target linking the Rust HAL against the
#     Lean kernel object code (the recurring SM9.E closure item).
#   * A shootdown driver in the kernel image: two threads homed on different
#     cores sharing a mapping, the initiator unmapping through the live
#     `syscallDispatchCrossCoreEntry` seam, the target probing the stale VA,
#     emitting the banner below.
#
# Skip / pass / fail conditions:
#   * No QEMU on PATH                    → SKIP
#   * No kernel image                    → SKIP
#   * Shootdown driver unwired           → SKIP (current state, SM7.B)
#   * Round hangs / stale VA still maps  → FAIL
#   * Stale translation faults on target → PASS

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

if ! command -v qemu-system-aarch64 &>/dev/null; then
  echo "[SKIP] WS-SM SM7.B Tier-4: qemu-system-aarch64 not found on PATH"
  exit 0
fi

KERNEL_IMAGE="${SELE4N_KERNEL_IMAGE:-}"

if [[ -z "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM7.B Tier-4: SELE4N_KERNEL_IMAGE env var not set"
  echo "       Set SELE4N_KERNEL_IMAGE=/path/to/kernel.elf to enable."
  exit 0
fi

if [[ ! -f "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM7.B Tier-4: kernel image not found at ${KERNEL_IMAGE}"
  exit 0
fi

# --------------------------------------------------------------------------
# Pre-condition: the shootdown driver must be wired in the kernel image.
# We detect it by the banner the driver emits.  At SM7.B the driver is NOT
# present (it needs the SM9.E bootable kernel-image binary target), so this
# SKIPs.
#
# Capture `strings` output into a variable first, *then* grep it: under
# `set -o pipefail`, a `strings … | grep -q` pipeline can report failure even
# on a match — `grep -q` exits at the first hit and `strings` then dies with
# SIGPIPE (exit 141), failing the pipeline.  The capture (with `|| true`)
# decouples the two stages and avoids the SIGPIPE.
# --------------------------------------------------------------------------
KERNEL_STRINGS="$(strings "${KERNEL_IMAGE}" 2>/dev/null || true)"
if ! grep -q "smp-test.*tlb-shootdown" <<<"${KERNEL_STRINGS}"; then
  echo "[SKIP] WS-SM SM7.B Tier-4: TLB shootdown driver not wired in kernel image"
  echo ""
  echo "  Reason: exercising a real cross-core shootdown requires the SM9.E"
  echo "          bootable kernel-image [[bin]] target (Rust HAL linked against"
  echo "          the Lean kernel object code) plus an in-image driver: a thread"
  echo "          on core 0 unmapping a page core 1 has cached, through the live"
  echo "          completeShootdownRounds bracket.  The shootdown correctness"
  echo "          guarantee is established FORMALLY (and for ALL executions) by:"
  echo "            tlbShootdownBroadcast_invalidatesAllCores        (Thm 3.3.1)"
  echo "            shootdownRound_tlb_no_matching_entry             (pipeline corollary)"
  echo "            vspaceUnmapPageWithShootdown_remote_retire_removes (coalescing remote case)"
  echo "            shootdownAck_release_acquire                     (B.4 publication)"
  echo "            shootdown_timeout_handling                       (B.6 exact verdict)"
  echo "            coalescingRound_restores_quiescent               (live-round capstone)"
  echo "          machine-checked in tests/SmpTlbShootdownSuite.lean."
  echo ""
  echo "  When wired (SM9.E), this script will:"
  echo "    1. Boot QEMU virt -smp 4."
  echo "    2. Map a shared page; have core 1 touch it (cache the translation)."
  echo "    3. Have core 0 unmap it through the live dispatch seam; the round"
  echo "       fires .tlbShootdownReq SGIs, TLBIs locally, and waits allAcked."
  echo "    4. Assert core 1's re-access faults (translation gone) and the"
  echo "       banner '[smp-test] tlb-shootdown: stale translation removed'."
  echo ""
  echo "  Formal coverage at SM7.B (already passing):"
  echo "    lake exe smp_tlb_shootdown_suite"
  exit 0
fi

# --------------------------------------------------------------------------
# Run the test (only reached if the shootdown driver is wired)
# --------------------------------------------------------------------------
LOG="$(mktemp -t sele4n-smp-shootdown.XXXXXX.log)"
# shellcheck disable=SC2064
trap "rm -f '${LOG}'" EXIT

TIMEOUT_SECS="${SELE4N_QEMU_TIMEOUT_SECS:-60}"

echo "[META] WS-SM SM7.B Tier-4: booting QEMU virt -smp 4 for TLB shootdown round"
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

if grep -q "smp-test.*tlb-shootdown: stale translation removed" "${LOG}"; then
  echo "[PASS] WS-SM SM7.B Tier-4: shootdown round completed (SGIs + acks + fault on stale VA)"
  exit 0
else
  echo "[FAIL] WS-SM SM7.B Tier-4: shootdown banner not observed (qemu exit ${QEMU_EXIT})"
  echo "------ QEMU log tail ------"
  tail -40 "${LOG}" || true
  exit 1
fi
