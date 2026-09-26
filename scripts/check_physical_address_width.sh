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
#   - RPi5 / BCM2712     : 40 bits (Cortex-A76 `ID_AA64MMFR0_EL1.PARange = 0b0010`;
#                          TRM r4p1 §B2.58 — the v0.36.2 audit corrected the `44`
#                          AJ3-B had carried, which no Cortex-A76 implements)
#   - Sim platform        : 52 bits (ARMv8 LPA max)
#   - Generic / abstract  : 52 bits (matches ARMv8 max)
#   - Test probes         : explicit per-test value (0, 64, etc.) for bounds tests
#
# The audit enforces:
#   1. The RPi5 board definition supplies exactly 40.
#   2. The Sim platform contract supplies exactly 52.
#   3. The `defaultMachineConfig` supplies exactly 52.
#   4. No source file contains `physicalAddressWidth := 48` (a common ARMv8
#      misconfiguration confusing VA width and PA width).
#
# WS-RR RR7.1 added the boot identity map's window to this script's remit, and
# the RR7 audit round made the device window a relation to the Lean memory map
# computed by parsing `Board.lean` with a regular expression.  WS-BP BP0.4
# retired that parse: the boot map is now DRIVEN through the Lean map rather
# than compared against its text — `tests/Ak9PlatformSuite.lean` emits
# `rpi5MemoryMapForConfig`'s regions and its kind at every boundary probe into
# `tests/fixtures/boot_map.expected`, and `mmu.rs`'s
# `the_boot_map_agrees_with_the_lean_map` pushes the same probes (and its own
# boundary constants) through `boot_mapping_for` and a walk of the tables.  A
# Lean question goes to Lean.  What stays here is the linker's half, which no
# Lean definition states: `link.ld`'s RAM region ends at `KERNEL_RESERVED_END`,
# the only RAM the boot map covers before the verified parse (WS-BP BP2.6;
# BP7.10 retired `GUARANTEED_RAM_TOP`, the first gigabyte, which no board's
# firmware reports whole), so the linker cannot place the image where the boot
# does not map it.
#
# The width scans carry their own self-test, run first on every invocation
# (`--self-test` runs it alone): each keeps the token and changes only whether
# it is code.
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

self_test() {
  local failures=0
  # PR #892 review round 8: the width scans read the code view too, and both
  # directions of that need a witness — a *presence* case (prose must not
  # satisfy a positive) and an *absence* case (prose must not trip the
  # negative).  Both mutations keep the token and change only whether it is
  # code, which is the mutation shape this project requires.
  local wfx wview
  wfx="$(mktemp)"; wview="$(mktemp)"
  cat > "${wfx}" <<'LEANEOF'
-- A fixture, written and deleted by scripts/check_physical_address_width.sh.
-- The binding below has been changed; the old one survives only in this
-- comment: physicalAddressWidth := 44
def fixtureConfig :=
  { physicalAddressWidth := 40 }
LEANEOF
  python3 scripts/lean_code_view.py "${wfx}" > "${wview}"
  if grep -q 'physicalAddressWidth := 44' "${wview}"; then
    echo "self-test FAIL: width: a commented-out binding satisfied the positive scan" >&2
    failures=$((failures + 1))
  fi
  cat > "${wfx}" <<'LEANEOF'
-- A fixture, written and deleted by scripts/check_physical_address_width.sh.
/-- Never `physicalAddressWidth := 48`: 48 is the ARMv8 *virtual* address
    width, and using it for a physical one is the misconfiguration this gate
    refuses.  (A heredoc body is lexed as a document of its own, so an audit
    identifier written here would be read as code by the naming gate; the
    reference lives in the shell comment above.) -/
def fixtureDoc := 0
LEANEOF
  python3 scripts/lean_code_view.py "${wfx}" > "${wview}"
  if grep -qE 'physicalAddressWidth[[:space:]]*:=[[:space:]]*48([^0-9]|$)' "${wview}"; then
    echo "self-test FAIL: width: prose describing the forbidden binding tripped the negative" >&2
    failures=$((failures + 1))
  fi
  rm -f "${wfx}" "${wview}"

  if [ "${failures}" -ne 0 ]; then
    fail "width self-test: ${failures} case(s) failed"
  fi
  echo "width self-test passed (2 width-view cases)."
}

# The self-test runs first on every invocation: a relation check that has
# stopped deciding is indistinguishable from a tree that satisfies it.
self_test
if [ "${1:-}" = "--self-test" ]; then
  exit 0
fi

# PR #892 review round 8: all four width scans read the **code view**, not the
# raw file.  Raw text is wrong in both directions here, and the gate was wrong
# in both: a width changed while the old assignment survived in a docstring
# satisfied the three positives, and a comment explaining what `48` means for
# virtual addresses tripped the negative — the very shape this project's
# conventions forbid (*never contort prose to satisfy a scanner*).
#
# Views are read from the shared overlay (`lean_code_view.py --overlay`),
# refreshed once here and read in place, rather than emitted by one `python3`
# invocation per file: the per-file form was five hundred interpreter
# start-ups, twenty-three seconds of a gate whose scans take a fraction of one
# (test-performance audit, v0.35.159).  The overlay's `.lean` entries are
# `lean_code_view.strip` of the source and its `.rs` entries are
# `rust_code_view.code` -- the two functions the per-file calls ran -- and a
# suffix its table does not name is linked whole, which is the raw read the
# `.toml` arm below wants.  Reading the overlay also keeps `grep -q` off a
# pipeline: under `pipefail` it closes the pipe on its first match and a
# writer takes SIGPIPE, so a piped status is 141 exactly when the pattern *is*
# present.
CODE_VIEW="$(python3 scripts/lean_code_view.py --overlay .lake/build/leancodeview)"
WIDTH_VIEW_DIR="$(mktemp -d)"
trap 'rm -rf "${WIDTH_VIEW_DIR}"' EXIT

# The comment-free view of a Lean file: its overlay entry.
lean_view_of() {
  local src="$1"
  echo "${CODE_VIEW}/${src}"
}

require_width_binding() {
  local src="$1" width="$2" message="$3"
  local view
  view="$(lean_view_of "${src}")"
  if ! grep -q "physicalAddressWidth := ${width}" "${view}"; then
    fail "${message}"
  fi
}

# 1. RPi5 Board.lean must bind 40.
require_width_binding SeLe4n/Platform/RPi5/Board.lean 40 \
  "RPi5/Board.lean must declare physicalAddressWidth := 40 (the Cortex-A76's PARange; BCM2712)."

# 2. Sim Contract.lean must bind 52.
require_width_binding SeLe4n/Platform/Sim/Contract.lean 52 \
  "Sim/Contract.lean must declare physicalAddressWidth := 52 (ARMv8 LPA max)."

# 3. defaultMachineConfig must bind 52.
require_width_binding SeLe4n/Machine.lean 52 \
  "Machine.lean::defaultMachineConfig must declare physicalAddressWidth := 52."

# 4. No file may declare `physicalAddressWidth := 48`.  48 is the ARMv8 VA
#    width; using it for PA is a known misconfiguration on BCM2712 (AJ3-B / M-18).
#    Scanned over each file's own code view, so prose that *discusses* the
#    forbidden binding is not the forbidden binding.
width_48_hits="${WIDTH_VIEW_DIR}/forbidden_48"
: > "${width_48_hits}"
while IFS= read -r src; do
  case "${src}" in
    *.lean) view="$(lean_view_of "${src}")" ;;
    # The overlay's `.rs` entry is `rust_code_view.code`: comments blanked,
    # string contents kept, byte-aligned.
    *.rs) view="${CODE_VIEW}/${src}" ;;
    # A language with no stripper in the table is read raw, deliberately: this
    # scan builds a set of REFUSALS, and a refusal it drops is a check nobody
    # runs, so the fail-closed direction is to over-report.
    *) view="${src}" ;;
  esac
  if grep -nE 'physicalAddressWidth[[:space:]]*:=[[:space:]]*48([^0-9]|$)' "${view}" \
      | sed "s|^|${src}:|" >> "${width_48_hits}"; then
    :
  fi
done < <(find SeLe4n tests rust -name '*.lean' -o -name '*.rs' -o -name '*.toml' 2>/dev/null)

if [ -s "${width_48_hits}" ]; then
  cat "${width_48_hits}"
  fail "physicalAddressWidth := 48 is forbidden (VA-width confusion; see AJ3-B / M-18)."
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
# One trap for every temporary this script makes: a second `trap … EXIT`
# replaces the first rather than adding to it.
trap 'rm -rf "${WIDTH_VIEW_DIR}" "${MMU_VIEW_FILE}"' EXIT
python3 scripts/rust_code_view.py --no-strings "${MMU_SRC}" > "${MMU_VIEW_FILE}"

expect_mmu_const() {
  local name="$1" value="$2"
  if ! grep -qE "^pub const ${name}: u64 = ${value};$" "${MMU_VIEW_FILE}"; then
    fail "${MMU_SRC} must declare \`pub const ${name}: u64 = ${value};\` (WS-RR RR7.1 boot map)."
  fi
}

# WS-BP BP0.4: the boundary pins against `Board.lean`'s text are retired — the
# driven comparison (see the header) decides every boundary against the Lean
# map itself.  `KERNEL_RESERVED_END` stays pinned because the linker check below
# needs its value and `link.ld` is not something Lean states.
expect_mmu_const KERNEL_RESERVED_END '0x1000_0000'

# link.ld's RAM region must end exactly at KERNEL_RESERVED_END: ORIGIN + LENGTH.
LINK_LD="rust/sele4n-hal/link.ld"
LD_ORIGIN="$(grep -oE 'ORIGIN[[:space:]]*=[[:space:]]*0x[0-9A-Fa-f]+' "${LINK_LD}" | head -1 | grep -oE '0x[0-9A-Fa-f]+')"
LD_LENGTH="$(grep -oE 'LENGTH[[:space:]]*=[[:space:]]*0x[0-9A-Fa-f]+' "${LINK_LD}" | head -1 | grep -oE '0x[0-9A-Fa-f]+')"
if [ -z "${LD_ORIGIN}" ] || [ -z "${LD_LENGTH}" ]; then
  fail "${LINK_LD} must declare a RAM region with hexadecimal ORIGIN and LENGTH."
fi
LD_END="$(printf '0x%X' "$(( LD_ORIGIN + LD_LENGTH ))")"
if [ "${LD_END}" != "0x10000000" ]; then
  fail "${LINK_LD}'s RAM region ends at ${LD_END}, not at mmu.rs's KERNEL_RESERVED_END (0x10000000): the linker would place the image where the boot map does not cover it."
fi

echo "AN7-B: physicalAddressWidth audit clean (RPi5=40, Sim=52, default=52; no ':= 48' anywhere)."
echo "WS-BP BP2.6, BP7.10: link.ld's RAM region ends at mmu.rs's KERNEL_RESERVED_END (the boot map itself is driven through the Lean map: WS-BP BP0.4)."
exit 0
