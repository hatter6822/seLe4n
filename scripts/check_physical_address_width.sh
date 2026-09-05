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

# ---------------------------------------------------------------------------
# WS-RR RR7.1: the boot identity map's window
#
# The remediation for register §4 finding 4 asks for the resulting bound to be
# in this script's remit "so it cannot drift again".  Three declarations state
# the same physical memory map and must agree:
#
#   1. `rpi5MemoryMapForConfig` in `SeLe4n/Platform/RPi5/Board.lean` — the
#      project's canonical BCM2712 map.
#   2. `mmu::boot_mapping_for`'s constants in `rust/sele4n-hal/src/mmu.rs` —
#      what the boot translation tables actually install.
#   3. `link.ld`'s `RAM` region — what the linker may hand out.
#
# Read over the Rust *code view* (comments blanked) so a boundary that survives
# only in a doc comment cannot satisfy the check.
# ---------------------------------------------------------------------------

MMU_SRC="rust/sele4n-hal/src/mmu.rs"
MMU_VIEW_FILE="$(mktemp)"
# The view goes to a file rather than a shell variable piped into `grep`: under
# `pipefail`, `grep -q` closes the pipe on its first match and the writer takes
# SIGPIPE, so the pipeline's status is 141 exactly when the pattern *is* found.
# That reads as "absent" and made this gate fail on a tree that satisfies it.
trap 'rm -f "${MMU_VIEW_FILE}"' EXIT
python3 scripts/rust_code_view.py --no-strings "${MMU_SRC}" > "${MMU_VIEW_FILE}"

expect_mmu_const() {
  local name="$1" value="$2"
  if ! grep -qE "^pub const ${name}: u64 = ${value};$" "${MMU_VIEW_FILE}"; then
    fail "${MMU_SRC} must declare \`pub const ${name}: u64 = ${value};\` (WS-RR RR7.1 boot map)."
  fi
}

expect_mmu_const LOW_RAM_TOP '0xFC00_0000'
expect_mmu_const DEVICE_WINDOW_BASE '0xFE00_0000'
expect_mmu_const DEVICE_WINDOW_TOP '0xFFA0_0000'
expect_mmu_const HIGH_RAM_BASE '0x1_0000_0000'

# The Lean map's own boundaries.  `peripheralBoundary` caps the low RAM region;
# the device region starts at 0xFE000000; the second RAM region starts at the
# 4 GiB boundary.
if ! grep -q 'let peripheralBoundary := 0xFC000000' SeLe4n/Platform/RPi5/Board.lean; then
  fail "Board.lean's rpi5MemoryMapForConfig must cap low RAM at 0xFC000000 (matches mmu.rs LOW_RAM_TOP)."
fi
if ! grep -q 'base := (SeLe4n.PAddr.ofNat 0xFE000000)' SeLe4n/Platform/RPi5/Board.lean; then
  fail "Board.lean's rpi5MemoryMapForConfig must place the device window at 0xFE000000 (matches mmu.rs DEVICE_WINDOW_BASE)."
fi
if ! grep -q 'base := (SeLe4n.PAddr.ofNat 0x100000000)' SeLe4n/Platform/RPi5/Board.lean; then
  fail "Board.lean's rpi5MemoryMapForConfig must place high RAM at 0x100000000 (matches mmu.rs HIGH_RAM_BASE)."
fi

# link.ld's RAM region must end exactly at LOW_RAM_TOP: ORIGIN + LENGTH.
LINK_LD="rust/sele4n-hal/link.ld"
LD_ORIGIN="$(grep -oE 'ORIGIN[[:space:]]*=[[:space:]]*0x[0-9A-Fa-f]+' "${LINK_LD}" | head -1 | grep -oE '0x[0-9A-Fa-f]+')"
LD_LENGTH="$(grep -oE 'LENGTH[[:space:]]*=[[:space:]]*0x[0-9A-Fa-f]+' "${LINK_LD}" | head -1 | grep -oE '0x[0-9A-Fa-f]+')"
if [ -z "${LD_ORIGIN}" ] || [ -z "${LD_LENGTH}" ]; then
  fail "${LINK_LD} must declare a RAM region with hexadecimal ORIGIN and LENGTH."
fi
LD_END="$(printf '0x%X' "$(( LD_ORIGIN + LD_LENGTH ))")"
if [ "${LD_END}" != "0xFC000000" ]; then
  fail "${LINK_LD}'s RAM region ends at ${LD_END}, not at mmu.rs's LOW_RAM_TOP (0xFC000000): the linker would hand out addresses the boot tables do not map as RAM."
fi

echo "AN7-B: physicalAddressWidth audit clean (RPi5=44, Sim=52, default=52; no ':= 48' anywhere)."
echo "WS-RR RR7.1: boot identity-map window agrees across mmu.rs, Board.lean and link.ld."
exit 0
