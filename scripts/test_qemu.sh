#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# AG9-A: QEMU Integration Testing for seLe4n on Raspberry Pi 5
#
# Validates the kernel image boots correctly in QEMU, exercising:
# 1. UART boot banner output
# 2. Exception vector table setup (VBAR_EL1)
# 3. GIC-400 interrupt controller initialization
# 4. ARM Generic Timer interrupt delivery
# 5. Syscall dispatch (SVC instruction handling)
#
# Prerequisites:
#   - qemu-system-aarch64 installed (QEMU >= 8.0)
#   - Rust toolchain with aarch64-unknown-none-softfloat target
#   - cargo build --release --target aarch64-unknown-none-softfloat
#     --features kernel_image,board_qemu_virt --bin sele4n-kernel completes
#     (WS-BP BP8.1: the image built for QEMU's `virt` machine -- QEMU models no
#     BCM2712, so the Raspberry Pi 5 image meets no device under it; the Rust
#     half boots on its own, and KERNEL_BIN may name another image instead)
#
# Usage:
#   ./scripts/test_qemu.sh              # Build the virt image; boot it at EL1 and at EL2
#   ./scripts/test_qemu.sh --lean-kernel  # Build the Lean-linked virt image; boot it on
#                                         # four PEs to every core's first idle dispatch
#   KERNEL_BIN=… QEMU_MACHINE=… ./scripts/test_qemu.sh   # Boot a named image on a named machine
#   QEMU_TIMEOUT=30 ./scripts/test_qemu.sh  # Custom per-boot timeout (seconds)
#
# CI Integration:
#   A gate that cannot run certifies nothing, so an unavailable prerequisite
#   (no QEMU, no cargo, no cross target, no kernel image, no machine) exits
#   SELE4N_SKIP_EXIT (77) — NOT 0.  Callers must invoke this through
#   `run_gate_check`, which records the gate as NOT RUN; a plain `run_check`,
#   or a direct call under `set -e`, will treat 77 as a failure.  Set
#   REQUIRE_QEMU=1 to fail outright instead of skipping.

set -euo pipefail

# WS-BP BP8.1 slice 3: `--lean-kernel` boots the image that links the Lean
# kernel (`hw_target`) instead of the HAL alone.  It needs the Lean archive
# `scripts/test_lean_aarch64_archive.sh` builds, and that lane runs this mode as
# its last step.
LEAN_KERNEL=0
for arg in "$@"; do
    case "${arg}" in
        --lean-kernel) LEAN_KERNEL=1 ;;
        *) echo "test_qemu.sh: unknown argument: ${arg}" >&2; exit 2 ;;
    esac
done

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

cd "${REPO_ROOT}"

# ── Configuration ──────────────────────────────────────────────────────────
# WS-BP BP8.2: the image build, the raw cut and the run are
# `scripts/qemu_boot_lib.sh`'s, shared with the four-PE bring-up gate.
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/qemu_boot_lib.sh"
# The HAL-only boot never stops printing, so it runs for a fixed window; the
# Lean-linked boot stops at the fourth first idle dispatch and this is only its
# deadline (measured: about two seconds on either entry level).
if [[ "${LEAN_KERNEL}" -eq 1 ]]; then
    QEMU_TIMEOUT="${QEMU_TIMEOUT:-120}"
else
    QEMU_TIMEOUT="${QEMU_TIMEOUT:-10}"
fi
QEMU_MACHINE="${QEMU_MACHINE:-}"

log_section "META" "=== AG9-A: QEMU Integration Testing ==="
qemu_require_tools
qemu_temp_file QEMU_LOG qemu_boot

# ── Build the kernel image ────────────────────────────────────────────────
qemu_build_image "${LEAN_KERNEL}"

# ── WS-BP BP8.1: QEMU's `virt`, at both entry levels ───────────────────────
# QEMU models no BCM2712, so the lane boots the image built for `virt`
# (`board_qemu_virt`, rust/sele4n-hal/src/board.rs): `virt`'s device map and
# RAM base, the same kernel otherwise.  It runs twice — at QEMU's default EL1
# entry, and with `virtualization=on`, where QEMU enters at EL2 as the
# Raspberry Pi firmware does, so the drop to EL1 and the SMC conduit execute
# before the board is the first thing to run them.  An image named by
# KERNEL_BIN runs on the machine named by QEMU_MACHINE instead, once.
qemu_cut_image

FIXTURE="${REPO_ROOT}/tests/fixtures/qemu_boot_expected.txt"
if [[ "${LEAN_KERNEL}" -eq 1 ]]; then
    FIXTURE="${REPO_ROOT}/tests/fixtures/qemu_lean_boot_expected.txt"
fi
BOOT_PASS=true

# How each boot runs.  The HAL-only image boots one PE for a fixed window.  The
# Lean-linked image boots the four its binding declares -- the boot halts at
# Phase 7 unless every one serves the kernel -- until `UNTIL_COUNT` lines carry
# `UNTIL_FRAGMENT`, and under `-icount`: with QEMU's multi-threaded TCG the
# virtual clock follows host time, one Lean scheduler tick emulated takes longer
# than the 1 ms tick period, and four PEs' ticks then hold the kernel-entry lock
# end to end so the boot core never leaves its bring-up (measured, at both entry
# levels).  `-icount shift=0` advances the clock one nanosecond per executed
# instruction -- a 1 GHz PE, slower than a Cortex-A76 -- so a tick costs its
# instruction count, and `sleep=off` skips the idle waits.  That is the kernel's
# own cost measured in instructions, not a longer tick.
BOOT_SMP=1
BOOT_EXTRA=()
UNTIL_FRAGMENT=""
UNTIL_COUNT=0
if [[ "${LEAN_KERNEL}" -eq 1 ]]; then
    BOOT_SMP=4
    BOOT_EXTRA=(-icount "shift=0,sleep=off")
    UNTIL_FRAGMENT="first idle dispatch"
    UNTIL_COUNT=4
fi

# boot_once LABEL MACHINE [FRAGMENT...]: boot the image on MACHINE and require
# the fixture's fragments IN ORDER, then each extra FRAGMENT anywhere.
boot_once() {
    local label="$1" machine="$2"
    shift 2
    log_section "TRACE" "RUN: ${label} — -machine ${machine} (timeout: ${QEMU_TIMEOUT}s)"
    qemu_run "${label}" "${QEMU_LOG}" "${machine}" "${BOOT_SMP}" "${QEMU_TIMEOUT}" \
        "${UNTIL_FRAGMENT}" "${UNTIL_COUNT}" "${BOOT_EXTRA[@]}" || BOOT_PASS=false
    if [[ ! -s "${QEMU_LOG}" ]]; then
        record_failure "TRACE" "${label}: QEMU produced no output (hung or dead kernel)"
        BOOT_PASS=false
        return
    fi
    if grep -qi "fatal\|panic\|unhandled.*exception\|SError" "${QEMU_LOG}"; then
        record_failure "TRACE" "${label}: fatal exception in boot output: $(grep -i -m1 'fatal\|panic\|unhandled.*exception\|SError' "${QEMU_LOG}")"
        BOOT_PASS=false
    fi
    # The fixture's fragments in the order the fixture lists them: each must
    # occur on a line after the previous fragment's line.
    local after=0 check_name fragment line
    while IFS='|' read -r check_name fragment; do
        [[ "${check_name}" =~ ^[[:space:]]*# ]] && continue
        [[ -z "${check_name// /}" ]] && continue
        check_name=$(echo "${check_name}" | xargs)
        fragment=$(echo "${fragment}" | xargs)
        # No match is grep's status 1, which `set -e -o pipefail` would turn
        # into a silent exit; it is a missing fragment, and is reported.
        line=$(tail -n "+$((after + 1))" "${QEMU_LOG}" | grep -n -F -m1 -- "${fragment}" | cut -d: -f1) || line=""
        if [[ -n "${line}" ]]; then
            after=$((after + line))
            log_section "TRACE" "PASS: ${label}: ${check_name} — '${fragment}' at line ${after}"
        else
            record_failure "TRACE" "${label}: ${check_name} — '${fragment}' missing after line ${after}"
            BOOT_PASS=false
        fi
    done < "${FIXTURE}"
    for fragment in "$@"; do
        if grep -q -F -- "${fragment}" "${QEMU_LOG}"; then
            log_section "TRACE" "PASS: ${label}: '${fragment}'"
        else
            record_failure "TRACE" "${label}: '${fragment}' missing from boot log"
            BOOT_PASS=false
        fi
    done
    if [[ "${LEAN_KERNEL}" -eq 1 ]]; then
        lean_boot_relations "${label}"
    fi
    log_section "TRACE" "${label}: $(wc -l < "${QEMU_LOG}") lines of boot output"
}

# lean_boot_relations LABEL (v0.36.31): what the ordered fragments cannot
# state.  WS-BP BP4.2 -- the install precedes the release, and the release
# precedes every secondary's first line, so no secondary ran while the
# unbracketed install wrote the kernel state.  WS-BP BP2.5 -- the census after
# the install counts more live allocations than the one after the library
# initializer: the Lean kernel's own `IO` action allocated on the target and
# completed, with the heap's invariants intact at both points.
lean_boot_relations() {
    local label="$1" verdict
    verdict=$(python3 - "${QEMU_LOG}" <<'PY'
import re
import sys

with open(sys.argv[1], encoding="utf-8", errors="replace") as handle:
    lines = handle.read().split("\n")
failures = []

def indices(predicate):
    return [i for i, line in enumerate(lines) if predicate(line)]

install = indices(lambda l: l == "[boot] Phase 5: kernel state installed")
release = indices(lambda l: l == "[smp] releasing the secondaries under the install permit")
secondary = indices(lambda l: re.match(r"\[(smp|sched|tick)\] core [1-9]", l) is not None)
if len(install) != 1 or len(release) != 1:
    failures.append(f"expected one install line and one release line, found {len(install)} and {len(release)}")
elif not secondary:
    failures.append("no secondary line at all: the release was not followed by a bring-up")
else:
    if not install[0] < release[0]:
        failures.append("the release precedes the install")
    if not release[0] < secondary[0]:
        failures.append(f"a secondary ran before the release: {lines[secondary[0]]!r}")

census = re.compile(
    r"\[boot\] Lean heap after (the library initializer|the install): (\d+) live "
    r"allocation\(s\), (\d+) of (\d+) page\(s\) in use, invariants hold$")
found = {}
for i, line in enumerate(lines):
    match = census.match(line)
    if match:
        if match.group(1) in found:
            failures.append(f"a second census after {match.group(1)}")
        found[match.group(1)] = (i, int(match.group(2)), int(match.group(3)), int(match.group(4)))
if set(found) != {"the library initializer", "the install"}:
    failures.append(f"expected a census after the library initializer and after the install, found {sorted(found)}")
else:
    (i_init, live_init, used_init, pages_init) = found["the library initializer"]
    (i_boot, live_boot, used_boot, pages_boot) = found["the install"]
    if install and not i_init < install[0] < i_boot:
        failures.append("the censuses do not bracket the install")
    if not 0 < live_init < live_boot:
        failures.append(f"the install did not allocate: {live_init} then {live_boot} live allocation(s)")
    if pages_init != pages_boot or not 0 < used_init <= used_boot <= pages_boot:
        failures.append(f"the page counts are not a heap's: {used_init}/{pages_init} then {used_boot}/{pages_boot}")
for failure in failures:
    print(failure)
PY
) || { record_failure "TRACE" "${label}: the relation check could not run"; BOOT_PASS=false; return; }
    if [[ -n "${verdict}" ]]; then
        BOOT_PASS=false
        while IFS= read -r failure; do
            record_failure "TRACE" "${label}: ${failure}"
        done <<< "${verdict}"
    else
        log_section "TRACE" "PASS: ${label}: install, release, then the secondaries; the install allocated, with the heap's invariants intact"
    fi
}

if [[ ! -f "${FIXTURE}" ]]; then
    record_failure "TRACE" "Boot fixture missing: ${FIXTURE}"
    finalize_report
fi
# The fixture's `.sha256` companion (WS-BP BP8.1: it landed with the boot path
# this lane now runs): a fixture edit must be paired with a hash refresh in the
# same commit, as Tier 2 requires of every `.expected` fixture.  Tier 2's sweep
# reads `*.expected.sha256` only, so this lane checks its own.
if ! (cd "$(dirname "${FIXTURE}")" && sha256sum -c "$(basename "${FIXTURE}").sha256" > /dev/null 2>&1); then
    record_failure "TRACE" "${FIXTURE##*/} does not match its .sha256 companion (cd tests/fixtures && sha256sum ${FIXTURE##*/} > ${FIXTURE##*/}.sha256)"
    finalize_report
fi

# WS-BP BP8.1: the Lean board check is driven against a checked-in `virt`
# device tree; this QEMU is asked for its own and the two must agree, so the
# fixture cannot drift from the machine the image boots on.
if ! QEMU_BIN="${QEMU_BIN}" python3 "${REPO_ROOT}/scripts/qemu_virt_dtb_fixture.py" --check; then
    record_failure "TRACE" "tests/fixtures/qemu_virt_dtb.hex is not this QEMU's virt device tree (scripts/qemu_virt_dtb_fixture.py)"
    finalize_report
fi

if [[ -n "${QEMU_MACHINE}" ]]; then
    boot_once "the image on ${QEMU_MACHINE}" "${QEMU_MACHINE}"
elif [[ "${LEAN_KERNEL}" -eq 1 ]]; then
    # Every core's first idle dispatch, and every secondary's IRQ readiness,
    # which the boot core's Phase 7 counts; the fixture orders the boot core's.
    LEAN_PER_CORE=(
        "[smp] core 1: IRQ-serviceable" "[smp] core 2: IRQ-serviceable" "[smp] core 3: IRQ-serviceable"
        "[sched] core 0: first idle dispatch" "[sched] core 1: first idle dispatch"
        "[sched] core 2: first idle dispatch" "[sched] core 3: first idle dispatch"
    )
    boot_once "Lean kernel, virt, EL1 entry" "virt,gic-version=2" \
        "Entered at EL1, running at EL1" "PSCI conduit: Hvc" "${LEAN_PER_CORE[@]}"
    boot_once "Lean kernel, virt, EL2 entry" "virt,gic-version=2,virtualization=on" \
        "Entered at EL2, running at EL1" "PSCI conduit: Smc" "${LEAN_PER_CORE[@]}"
else
    boot_once "virt, EL1 entry" "virt,gic-version=2" \
        "booting on QEMU virt" "Entered at EL1, running at EL1" "PSCI conduit: Hvc"
    boot_once "virt, EL2 entry" "virt,gic-version=2,virtualization=on" \
        "booting on QEMU virt" "Entered at EL2, running at EL1" "PSCI conduit: Smc"
fi

# ── Summary ────────────────────────────────────────────────────────────────
if [[ "${BOOT_PASS}" = true ]]; then
    log_section "META" "PASS: QEMU boot"
else
    log_section "META" "FAIL: QEMU boot"
fi

finalize_report
