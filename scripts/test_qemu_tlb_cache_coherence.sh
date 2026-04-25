#!/usr/bin/env bash
# AN9-A (DEF-A-M04) — QEMU TLB+Cache coherency validation harness.
#
# Boots the seLe4n kernel under QEMU virt and exercises a page-table
# update + executable-page flush.  Verifies no stale-I-cache fetch.
#
# See docs/HARDWARE_TESTING.md §4.1 for the procedure.
#
# Skips with status 0 if QEMU is not available so CI runners without
# emulation can still complete the smoke gate.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

if ! command -v qemu-system-aarch64 &>/dev/null; then
  echo "[SKIP] qemu-system-aarch64 not found — AN9-A hardware test SKIPPED"
  echo "       Install with: sudo apt install qemu-system-arm"
  exit 0
fi

# This harness is a STUB awaiting the full RPi 5 image build pipeline
# (tracked under post-AN9 hardware validation per
# docs/HARDWARE_TESTING.md §3.3).  Until the image build is wired,
# this script reports its skip status and the placeholder text the
# documentation references.
echo "[SKIP] AN9-A QEMU TLB+Cache coherency test not yet wired"
echo ""
echo "  Reason: requires the full kernel8.img + config.txt build"
echo "          pipeline (post-AN9 follow-up, tracked in"
echo "          docs/HARDWARE_TESTING.md §3.3)."
echo ""
echo "  When wired, this script will:"
echo "    1. Boot the kernel with QEMU virt machine (8 GB RAM)."
echo "    2. Map a 4 KiB page R+W at VA 0x10_0000_0000."
echo "    3. Write 0xDEADBEEF to the page."
echo "    4. Re-map the same VA as R+X (changes permissions)."
echo "    5. Branch to VA 0x10_0000_0000."
echo "    6. Confirm the I-cache fetched the new mapping."
echo ""
echo "  AN9-A static guarantees ARE verified at every commit:"
echo "    - lake build SeLe4n.Kernel.Architecture.TlbCacheComposition"
echo "    - lake exe an9_hardware_binding_suite (15 tests)"
echo ""

exit 0
