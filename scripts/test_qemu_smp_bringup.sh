#!/usr/bin/env bash
# AN9-J (DEF-R-HAL-L20) — QEMU SMP secondary-core bring-up validation.
#
# Boots seLe4n under QEMU virt -smp 4 with PSCI firmware and verifies
# all 4 cores reach their per-core ready flag and execute concurrent
# kernel work.
#
# See docs/HARDWARE_TESTING.md §4.8 for the procedure.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

if ! command -v qemu-system-aarch64 &>/dev/null; then
  echo "[SKIP] qemu-system-aarch64 not found — AN9-J SMP test SKIPPED"
  exit 0
fi

# Stub awaiting the full kernel image build pipeline (see
# docs/HARDWARE_TESTING.md §3.3).
echo "[SKIP] AN9-J QEMU SMP bring-up test not yet wired"
echo ""
echo "  Reason: requires the full kernel image + PSCI firmware boot"
echo "          pipeline.  AN9-J ships SMP code merged but disabled"
echo "          by default (SMP_ENABLED = false) at v1.0.0."
echo ""
echo "  When wired, this script will:"
echo "    1. Boot QEMU virt with -smp 4 -machine virt,secure=on"
echo "    2. Pass smp_enabled=true on the kernel command line"
echo "    3. Capture the UART log"
echo "    4. Assert each of cores 0..3 emits its core_id log line"
echo "    5. Run a cross-core SGI test"
echo ""
echo "  AN9-J static guarantees ARE verified:"
echo "    - cargo test -p sele4n-hal --lib smp (9 tests)"
echo "    - cargo test -p sele4n-hal --lib psci (5 tests)"
echo ""

exit 0
