#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM7.E.3 (plan §5 SM7.E / §7 risk inventory) — TLB shootdown stress:
# four cores issuing concurrent unmaps.
#
# Boots QEMU `-smp 4` with seLe4n and has all four cores unmap pages inside one
# another's shootdown windows, repeatedly.  This is the hardware-tier companion
# of the model-level storm in `tests/SmpTlbShootdownSuite.lean` §6: it exercises
# the one thing the pure model cannot — the real interleaving of the global
# round lock, the SGI delivery order, and the `SHOOTDOWN_ACK` handshake under
# contention.  The two failure modes it hunts are exactly the plan's §7 risks:
#
#   * **Round-serialisation failure** — the ack vector carries no round
#     identity, so two rounds interleaving would let an initiator observe
#     `allAcked` from someone else's round and return with a stale TLB live on a
#     remote PE (the SMP-C4 hazard).  Detected by the driver's post-round probe
#     of every unmapped VA on every core.
#   * **Deadlock / wait-timeout** — the initiator holds the round lock while
#     waiting for acks with IRQs masked, so a lock-waiter must service its own
#     pending obligation (`acquireShootdownRoundLockServicingSelf`).  A
#     regression there shows up as the SM7.B.6 fail-closed panic, or a hang.
#
# **What the formal layer already guarantees (SM7.A–F, no QEMU needed)**:
#   * `tlbShootdownBroadcast_invalidatesAllCores` — Theorem 3.3.1: after a
#     completed round no core's view retains a covered entry.
#   * `shootdownRoundPerCore_invalidates_perCore` — the same on the mounted
#     per-core model, evolved by the round's REAL per-descriptor drain.
#   * `handleTlbShootdownReqOnCorePerCore_comm` /
#     `foldl_handleTlbShootdownReqOnCorePerCore_swap` — distinct cores' handler
#     steps commute, so the model's single deterministic catch-up order stands
#     for EVERY hardware interleaving of the SGI deliveries.
#   * `enqueueShootdownOrCoalesce_{request,pending}_covered` +
#     `…_preserves_pendingBounded` — rounds posted faster than the catch-up
#     drains them never lose an invalidation and never breach the 16-deep bound.
#   * `shootdown_wait_loop_terminates` / `shootdown_timeout_handling` — the
#     bounded wait terminates and its verdict is exact.
#   These are machine-checked in tests/SmpTlbShootdownSuite.lean (Tier 2/3, §6
#   drives all four concurrently on a real page-table-backed state) and hold for
#   ALL executions — this script is a complementary *runtime* spot-check with a
#   real GIC delivering the SGIs and a real CAS lock serialising the rounds.
#
# **Prerequisites (SM9.E)**:
#   * A bootable kernel-image `[[bin]]` target linking the Rust HAL against the
#     Lean kernel object code (the recurring SM9.E closure item).
#   * A stress driver in the kernel image: four threads homed one per core,
#     each repeatedly mapping and unmapping its own page through the live
#     `syscallDispatchCrossCoreEntry` seam while probing its peers' VAs.
#
# Skip / pass / fail conditions:
#   * No QEMU on PATH                       → SKIP
#   * No kernel image                       → SKIP
#   * Shootdown stress driver unwired       → SKIP (current state, SM7.E)
#   * Hang / timeout panic / stale VA hit   → FAIL
#   * All cores complete, no stale hit      → PASS

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

if ! command -v qemu-system-aarch64 &>/dev/null; then
  echo "[SKIP] WS-SM SM7.E.3: qemu-system-aarch64 not found on PATH"
  exit 0
fi

KERNEL_IMAGE="${SELE4N_KERNEL_IMAGE:-}"

if [[ -z "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM7.E.3: SELE4N_KERNEL_IMAGE env var not set"
  echo "       Set SELE4N_KERNEL_IMAGE=/path/to/kernel.elf to enable."
  exit 0
fi

if [[ ! -f "${KERNEL_IMAGE}" ]]; then
  echo "[SKIP] WS-SM SM7.E.3: kernel image not found at ${KERNEL_IMAGE}"
  exit 0
fi

# --------------------------------------------------------------------------
# Pre-condition: the concurrent-unmap stress driver must be wired in the kernel
# image.  We detect it by the banner the driver emits.  At SM7.E the driver is
# NOT present (it needs the SM9.E bootable kernel-image binary target), so this
# SKIPs.
#
# Capture `strings` output into a variable first, *then* grep it: under
# `set -o pipefail`, a `strings … | grep -q` pipeline can report failure even on
# a match — `grep -q` exits at the first hit and `strings` then dies with
# SIGPIPE (exit 141), failing the pipeline.  The capture (with `|| true`)
# decouples the two stages and avoids the SIGPIPE.
# --------------------------------------------------------------------------
TEST_BANNER="\\[smp-test\\] tlb-shootdown-stress: all cores completed"
KERNEL_STRINGS="$(strings "${KERNEL_IMAGE}" 2>/dev/null || true)"
if ! grep -q "smp-test.*tlb-shootdown-stress" <<<"${KERNEL_STRINGS}"; then
  echo "[SKIP] WS-SM SM7.E.3: TLB shootdown stress driver not wired in kernel image"
  echo ""
  echo "  Reason: exercising four cores' concurrent shootdown rounds requires"
  echo "          the SM9.E bootable kernel-image [[bin]] target (Rust HAL"
  echo "          linked against the Lean kernel object code) plus an in-image"
  echo "          driver: four threads homed one per core, each repeatedly"
  echo "          unmapping its own page through the live"
  echo "          completeShootdownRounds bracket while probing its peers' VAs."
  echo "          The concurrent-round correctness guarantee is established"
  echo "          FORMALLY (and for ALL executions) by:"
  echo "            tlbShootdownBroadcast_invalidatesAllCores        (Thm 3.3.1)"
  echo "            shootdownRoundPerCore_invalidates_perCore        (mounted, real drain)"
  echo "            handleTlbShootdownReqOnCorePerCore_comm          (interleaving-independence)"
  echo "            enqueueShootdownOrCoalesce_pending_covered       (no invalidation lost)"
  echo "            shootdown_wait_loop_terminates                   (bounded wait)"
  echo "          machine-checked in tests/SmpTlbShootdownSuite.lean (§6 drives"
  echo "          the four-core storm on a real page-table-backed state)."
  echo ""
  echo "  When wired (SM9.E), this script will:"
  echo "    1. Boot QEMU virt -smp 4."
  echo "    2. Map one page per core and have every core touch every page"
  echo "       (each PE caches all four translations)."
  echo "    3. Have all four cores unmap their own page concurrently, through"
  echo "       the live dispatch seam, repeatedly."
  echo "    4. Assert no core ever resolves an unmapped VA (no stale TLB hit),"
  echo "       no round times out, and every core emits its completion banner."
  echo "    5. Assert '[smp-test] tlb-shootdown-stress: all cores completed'."
  echo ""
  echo "  Formal coverage at SM7.E (already passing):"
  echo "    lake exe smp_tlb_shootdown_suite"
  exit 0
fi

# --------------------------------------------------------------------------
# Run the test (only reached if the stress driver is wired)
# --------------------------------------------------------------------------
LOG="$(mktemp -t sele4n-smp-shootdown-stress.XXXXXX.log)"
# shellcheck disable=SC2064
trap "rm -f '${LOG}'" EXIT

TIMEOUT_SECS="${SELE4N_QEMU_TIMEOUT_SECS:-120}"

echo "[META] WS-SM SM7.E.3: booting QEMU virt -smp 4 for the concurrent-unmap stress"
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

# A stale-TLB regression surfaces as the driver's own probe failure; a
# serialisation or lock regression surfaces as the SM7.B.6 fail-closed timeout
# panic or as a hang (no banner).  Check the loud failures first so the
# diagnostic names the actual mode.
if grep -q "shootdown round timed out" "${LOG}"; then
  echo "[FAIL] WS-SM SM7.E.3: a round hit the SM7.B.6 bounded-wait timeout" >&2
  tail -n 80 "${LOG}" >&2
  exit 1
fi

if grep -q "tlb-shootdown-stress: stale translation" "${LOG}"; then
  echo "[FAIL] WS-SM SM7.E.3: a core resolved an unmapped VA (stale TLB — SMP-C4)" >&2
  tail -n 80 "${LOG}" >&2
  exit 1
fi

if ! grep -qE "${TEST_BANNER}" "${LOG}"; then
  echo "[FAIL] WS-SM SM7.E.3: completion banner missing (possible hang)" >&2
  echo "       QEMU exit code: ${QEMU_EXIT}" >&2
  tail -n 80 "${LOG}" >&2
  exit 1
fi

case "${QEMU_EXIT}" in
  0|124) ;;
  *)
    echo "[FAIL] WS-SM SM7.E.3: QEMU exited with code ${QEMU_EXIT}" >&2
    tail -n 40 "${LOG}" >&2
    exit 1
    ;;
esac

echo "[PASS] WS-SM SM7.E.3: concurrent-unmap stress completed (no stale hit, no timeout)"
exit 0
