#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# AN7-B (H-15): repo-wide audit of `physicalAddressWidth` values.
#
# Per the target-platform contract:
#   - RPi5 / BCM2712     : 44 bits (hardware limit)
#   - Sim platform        : 52 bits (ARMv8 LPA max)
#   - Generic / abstract  : 52 bits (matches ARMv8 max)
#   - Test probes         : explicit per-test value (0, 64, etc.) for bounds tests
#
# The audit enforces:
#   1. The RPi5 board definition supplies exactly 44.
#   2. The Sim platform contract supplies exactly 52.
#   3. The `defaultMachineConfig` supplies exactly 52.
#   4. No source file contains `physicalAddressWidth := 48` (a common ARMv8
#      misconfiguration confusing VA width and PA width).
#
# Exits 0 when every expected value matches and no forbidden value appears,
# otherwise 1 with a diagnostic.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${REPO_ROOT}"

fail() {
  echo "AN7-B FAIL: $*" >&2
  exit 1
}

# 1. RPi5 Board.lean must bind 44.
if ! grep -q 'physicalAddressWidth := 44' SeLe4n/Platform/RPi5/Board.lean; then
  fail "RPi5/Board.lean must declare physicalAddressWidth := 44 (BCM2712 hardware limit)."
fi

# 2. Sim Contract.lean must bind 52.
if ! grep -q 'physicalAddressWidth := 52' SeLe4n/Platform/Sim/Contract.lean; then
  fail "Sim/Contract.lean must declare physicalAddressWidth := 52 (ARMv8 LPA max)."
fi

# 3. defaultMachineConfig must bind 52.
if ! grep -q 'physicalAddressWidth := 52' SeLe4n/Machine.lean; then
  fail "Machine.lean::defaultMachineConfig must declare physicalAddressWidth := 52."
fi

# 4. No file may declare `physicalAddressWidth := 48`.  48 is the ARMv8 VA
#    width; using it for PA is a known misconfiguration on BCM2712 (AJ3-B / M-18).
if command -v rg >/dev/null 2>&1; then
  if rg -n 'physicalAddressWidth\s*:=\s*48\b' \
       --type-add 'source:*.{lean,rs,toml}' -tsource . 2>/dev/null; then
    fail "physicalAddressWidth := 48 is forbidden (VA-width confusion; see AJ3-B / M-18)."
  fi
else
  if (find SeLe4n tests rust -name '*.lean' -o -name '*.rs' -o -name '*.toml' 2>/dev/null) \
      | xargs grep -nE 'physicalAddressWidth[[:space:]]*:=[[:space:]]*48\b' 2>/dev/null; then
    fail "physicalAddressWidth := 48 is forbidden (VA-width confusion; see AJ3-B / M-18)."
  fi
fi

echo "AN7-B: physicalAddressWidth audit clean (RPi5=44, Sim=52, default=52; no ':= 48' anywhere)."
exit 0
