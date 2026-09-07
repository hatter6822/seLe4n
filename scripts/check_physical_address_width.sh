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
# WS-RR RR7.1 added the boot identity map's window (below), and the RR7 audit
# round (v0.34.109) made the window a RELATION to the Lean memory map rather
# than a literal pinned beside it: the device window's top must be the 2 MiB
# round-up of the `.device` region `rpi5MemoryMapForConfig` declares, computed
# from the Lean source, and the Rust test that states the same fact must state
# it about the same number.  That block carries its own self-test, run first on
# every invocation (`--self-test` runs it alone): each relation is broken with
# every token kept in place, and the parse is exercised on a fixture whose raw
# text would mislead it.
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

# ---------------------------------------------------------------------------
# WS-RR RR7 audit round: the device window as a relation to the Lean map.
#
# `DEVICE_WINDOW_TOP` is pinned as a literal below, and `mmu.rs`'s own boot-map
# test relates it to `LEAN_DEVICE_EXTENT_TOP` — a SECOND literal, hand-copied
# from `Board.lean`.  Neither reads the Lean map, so a change to the peripheral
# window in `rpi5MemoryMapForConfig` (the one place the project declares the
# BCM2712 map) would leave the boot tables mapping the old window with every
# gate green.  The functions here compute the extent from the Lean source and
# decide the relation:
#   * the window covers the extent          (extent_top <= DEVICE_WINDOW_TOP),
#   * it is 2 MiB aligned and the round-up   (DEVICE_WINDOW_TOP - extent_top < 2 MiB),
#     because the fourth GiB is described at level-2 block granularity and a
#     second block above the extent would map space the Lean map reserves,
#   * the Rust literal IS the Lean extent, so that test is about the same fact
#     and not about a stale copy of it.
# The Lean side is read over the Lean code view (comments blanked), so a figure
# that survives only in a comment can neither satisfy nor confuse the parse.
# ---------------------------------------------------------------------------

L2_BLOCK=$(( 0x200000 ))

# The relation, as a function of the three numbers it is about, so the self-test
# can break each clause while keeping every token in place.  Prints the reason
# on failure.  Arguments are decimal (bash arithmetic accepts `0x…` too).
device_window_relation_verdict() {
  local extent_top="$1" window_top="$2" rust_literal="$3"
  if (( extent_top > window_top )); then
    printf 'the boot device window (top 0x%X) does not cover the Lean device extent (top 0x%X)' \
      "${window_top}" "${extent_top}"
    return 1
  fi
  if (( window_top % L2_BLOCK != 0 )); then
    printf 'DEVICE_WINDOW_TOP 0x%X is not 2 MiB aligned' "${window_top}"
    return 1
  fi
  if (( window_top - extent_top >= L2_BLOCK )); then
    printf 'DEVICE_WINDOW_TOP 0x%X is more than one 2 MiB block above the Lean device extent (top 0x%X): the window maps space the Lean map reserves' \
      "${window_top}" "${extent_top}"
    return 1
  fi
  if (( rust_literal != extent_top )); then
    printf "mmu.rs's LEAN_DEVICE_EXTENT_TOP (0x%X) is not the Lean map's device extent (top 0x%X): the Rust boot-map test relates the window to a stale copy" \
      "${rust_literal}" "${extent_top}"
    return 1
  fi
  return 0
}

# The `.device` region of a memory-map view: prints `<base> <size>` (both hex)
# for the ONE region whose kind is `.device`, reading the `{ base := (…0x…)
# / size := 0x… / kind := .device }` shape with blank (comment-blanked) lines
# skipped between the three.  Exits 1 unless exactly one such region exists —
# two is an ambiguity the gate refuses rather than resolving first-wins, and
# zero is a map with no device window to relate.
lean_device_region() {
  awk '
    function next_nonblank(    l) {
      while ((getline l) > 0) { if (l !~ /^[[:space:]]*$/) return l }
      return ""
    }
    /base := \(SeLe4n\.PAddr\.ofNat 0x[0-9A-Fa-f]+\)/ {
      match($0, /0x[0-9A-Fa-f]+/); base = substr($0, RSTART, RLENGTH)
      sizeline = next_nonblank()
      if (match(sizeline, /size := 0x[0-9A-Fa-f]+/)) {
        size = substr(sizeline, RSTART + 8, RLENGTH - 8)
        kindline = next_nonblank()
        if (kindline ~ /kind := \.device/) { print base, size; n++ }
      }
    }
    END { exit (n == 1) ? 0 : 1 }' "$1"
}

# Numeric value of `pub const NAME: u64 = 0x…;` in a Rust code view, with the
# digit-group underscores dropped.  Empty when the constant is absent.
rust_const_value() {
  grep -oE "^pub const $1: u64 = 0x[0-9A-Fa-f_]+;\$" "$2" \
    | grep -oE '0x[0-9A-Fa-f_]+' | tr -d _
}

self_test() {
  local failures=0 got
  expect_verdict() {
    local want="$1" label="$2"
    shift 2
    if device_window_relation_verdict "$@" >/dev/null; then got=accept; else got=reject; fi
    if [ "${got}" != "${want}" ]; then
      echo "self-test FAIL: ${label}: wanted ${want}, got ${got}" >&2
      failures=$((failures + 1))
    fi
  }
  # The tree's own numbers, and each clause broken with the others intact.
  expect_verdict accept "the tree's own numbers" \
    $((0xFF850000)) $((0xFFA00000)) $((0xFF850000))
  expect_verdict reject "extent grown past the window (window kept, literal follows the extent)" \
    $((0xFFA50000)) $((0xFFA00000)) $((0xFFA50000))
  expect_verdict reject "window a second block above the extent" \
    $((0xFF850000)) $((0xFFC00000)) $((0xFF850000))
  expect_verdict reject "window equal to an unaligned extent" \
    $((0xFF850000)) $((0xFF850000)) $((0xFF850000))
  expect_verdict reject "Rust literal drifted from the Lean extent" \
    $((0xFF850000)) $((0xFFA00000)) $((0xFF800000))
  expect_verdict accept "extent exactly on a block boundary, window equal to it" \
    $((0xFFA00000)) $((0xFFA00000)) $((0xFFA00000))

  # The parse.  Three things the fixture pins: the region is selected by its
  # KIND, not by the size token (`0x01850000` sits on a reserved region and must
  # not be read); a comment between `base` and `size` must be invisible (over
  # the raw text it reads as the size, and the real size line then reads as
  # the kind, so a raw-text parse finds no device region at all); and a second
  # `.device` region is a refusal.
  local fx view
  fx="$(mktemp)"; view="$(mktemp)"
  cat > "${fx}" <<'LEANEOF'
-- A fixture, written and deleted by scripts/check_physical_address_width.sh.
def fixtureRegions :=
    [ { base := (SeLe4n.PAddr.ofNat 0xFC000000)
        size := 0x01850000  -- the tree's device size, on a RESERVED region
        kind := .reserved }
    , { base := (SeLe4n.PAddr.ofNat 0xFE000000)
        -- size := 0x02000000
        size := 0x00400000
        kind := .device }
    ]
LEANEOF
  python3 scripts/lean_code_view.py "${fx}" > "${view}"
  if got="$(lean_device_region "${view}")"; then
    if [ "${got}" != "0xFE000000 0x00400000" ]; then
      echo "self-test FAIL: parse: wanted the .device region '0xFE000000 0x00400000', got '${got}'" >&2
      failures=$((failures + 1))
    fi
  else
    echo "self-test FAIL: parse: the code-view read found no unique .device region" >&2
    failures=$((failures + 1))
  fi
  if lean_device_region "${fx}" >/dev/null 2>&1; then
    echo "self-test FAIL: parse: the RAW text must not parse (the fixture's comment is designed to mislead a raw read)" >&2
    failures=$((failures + 1))
  fi
  cat > "${fx}" <<'LEANEOF'
def fixtureRegions :=
    [ { base := (SeLe4n.PAddr.ofNat 0xFE000000)
        size := 0x00400000
        kind := .device }
    , { base := (SeLe4n.PAddr.ofNat 0xFF000000)
        size := 0x00200000
        kind := .device }
    ]
LEANEOF
  python3 scripts/lean_code_view.py "${fx}" > "${view}"
  if lean_device_region "${view}" >/dev/null 2>&1; then
    echo "self-test FAIL: parse: two .device regions must be refused, not resolved first-wins" >&2
    failures=$((failures + 1))
  fi
  rm -f "${fx}" "${view}"

  if [ "${failures}" -ne 0 ]; then
    fail "device-window relation self-test: ${failures} case(s) failed"
  fi
  echo "device-window relation self-test passed (6 verdict cases, 3 parse cases)."
}

# The self-test runs first on every invocation: a relation check that has
# stopped deciding is indistinguishable from a tree that satisfies it.
self_test
if [ "${1:-}" = "--self-test" ]; then
  exit 0
fi

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

# ---------------------------------------------------------------------------
# WS-RR RR7 audit round: the device window, derived from the Lean map.
# ---------------------------------------------------------------------------

BOARD_SRC="SeLe4n/Platform/RPi5/Board.lean"
BOARD_VIEW_FILE="$(mktemp)"
trap 'rm -f "${MMU_VIEW_FILE}" "${BOARD_VIEW_FILE}"' EXIT
python3 scripts/lean_code_view.py "${BOARD_SRC}" > "${BOARD_VIEW_FILE}"

if ! DEV_REGION="$(lean_device_region "${BOARD_VIEW_FILE}")"; then
  fail "${BOARD_SRC}'s rpi5MemoryMapForConfig must declare exactly one \`kind := .device\` region with a literal hexadecimal base and size."
fi
read -r LEAN_DEV_BASE LEAN_DEV_SIZE <<<"${DEV_REGION}"
LEAN_DEV_TOP=$(( LEAN_DEV_BASE + LEAN_DEV_SIZE ))

WINDOW_BASE="$(rust_const_value DEVICE_WINDOW_BASE "${MMU_VIEW_FILE}")"
WINDOW_TOP="$(rust_const_value DEVICE_WINDOW_TOP "${MMU_VIEW_FILE}")"
if [ -z "${WINDOW_BASE}" ] || [ -z "${WINDOW_TOP}" ]; then
  fail "${MMU_SRC} must declare DEVICE_WINDOW_BASE and DEVICE_WINDOW_TOP as hexadecimal u64 constants."
fi
if (( LEAN_DEV_BASE != WINDOW_BASE )); then
  fail "$(printf 'the Lean device region starts at 0x%X but mmu.rs maps the device window from 0x%X' "${LEAN_DEV_BASE}" "${WINDOW_BASE}")"
fi

RUST_LITERAL="$(grep -oE 'const LEAN_DEVICE_EXTENT_TOP: u64 = 0x[0-9A-Fa-f_]+;' "${MMU_VIEW_FILE}" \
  | grep -oE '0x[0-9A-Fa-f_]+' | tr -d _)"
if [ -z "${RUST_LITERAL}" ]; then
  fail "${MMU_SRC}'s boot-map test must relate DEVICE_WINDOW_TOP to a \`const LEAN_DEVICE_EXTENT_TOP: u64 = 0x…;\` literal."
fi

if ! VERDICT="$(device_window_relation_verdict "${LEAN_DEV_TOP}" "$(( WINDOW_TOP ))" "$(( RUST_LITERAL ))")"; then
  fail "${VERDICT}"
fi

echo "AN7-B: physicalAddressWidth audit clean (RPi5=44, Sim=52, default=52; no ':= 48' anywhere)."
echo "WS-RR RR7.1: boot identity-map window agrees across mmu.rs, Board.lean and link.ld."
printf 'device window: DEVICE_WINDOW_TOP 0x%X is the 2 MiB round-up of the Lean device extent 0x%X, and mmu.rs tests against that extent.\n' \
  "${WINDOW_TOP}" "${LEAN_DEV_TOP}"
exit 0
