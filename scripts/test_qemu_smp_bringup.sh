#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM1.H.1 / WS-BP BP8.2 — the four-PE bring-up gate.
#
# Boots the kernel image built for QEMU's `virt` machine on four PEs, at EL1
# and again at EL2 (`virtualization=on`, the firmware's entry level on the
# Raspberry Pi 5), and requires the whole bring-up trace
# `tests/fixtures/qemu_smp_bringup_expected.txt` names: every secondary core's
# per-core init in order, the boot core's Phase 6 count of three secondaries,
# and — with `--lean-kernel` — the Phase 7 topology check and every core's
# first idle dispatch.
#
# Until WS-BP BP8.2 this script SKIPped on every run: it asked the caller for
# a pre-built kernel ELF that no target built, so it had executed no line
# of SMP HAL code, and WS-RR RR7.16 unchecked the two SM1.H acceptance boxes
# that claimed it.  It builds its own image now, through the same
# `scripts/qemu_boot_lib.sh` the boot lane `scripts/test_qemu.sh` uses.
#
# **A banner is a line.**  Every row matches a line that BEGINS with it, and no
# line may carry a console tag (`[smp]`, `[boot]`, `[sched]`, `[tick]`)
# anywhere but at its start.  A gate that searched for substrings, as the
# SM1.H draft did, would have passed the first four-PE boot, whose log tore
# banners together character by character: the secondaries printed before
# their MMU was on, where the console cannot take its lock, and `kprintln!`
# took the lock twice per line (both fixed in the cut that made this gate run).
#
# Usage:
#   ./scripts/test_qemu_smp_bringup.sh                 # HAL-only virt image
#   ./scripts/test_qemu_smp_bringup.sh --lean-kernel   # the Lean-linked image
#
# Exit codes:
#   0   PASS
#   77  SKIP / NOT RUN (SELE4N_SKIP_EXIT) — QEMU, cargo or the cross target is
#       missing, so this gate certified nothing; `run_gate_check` records it
#       as NOT RUN.  REQUIRE_QEMU=1 makes an absent QEMU a failure.
#   1   FAIL

set -euo pipefail

LEAN_KERNEL=0
for arg in "$@"; do
    case "${arg}" in
        --lean-kernel) LEAN_KERNEL=1 ;;
        *) echo "test_qemu_smp_bringup.sh: unknown argument: ${arg}" >&2; exit 2 ;;
    esac
done

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"
cd "${REPO_ROOT}"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/qemu_boot_lib.sh"

log_section "META" "=== WS-BP BP8.2: four-PE bring-up under QEMU virt ==="

FIXTURE="${REPO_ROOT}/tests/fixtures/qemu_smp_bringup_expected.txt"
if [[ ! -f "${FIXTURE}" ]]; then
    record_failure "TRACE" "bring-up fixture missing: ${FIXTURE}"
    finalize_report
fi
# The fixture's `.sha256` companion: a fixture edit must be paired with a hash
# refresh in the same commit, as Tier 2 requires of every `.expected` fixture.
if ! (cd "$(dirname "${FIXTURE}")" && sha256sum -c "$(basename "${FIXTURE}").sha256" > /dev/null 2>&1); then
    record_failure "TRACE" "${FIXTURE##*/} does not match its .sha256 companion"
    finalize_report
fi

qemu_require_tools
qemu_build_image "${LEAN_KERNEL}"
qemu_cut_image
qemu_temp_file BRINGUP_LOG qemu_bringup

# The HAL-only image stops being interesting once the third secondary is ready;
# the Lean-linked one once every core has dispatched its idle thread, and it
# runs under `-icount` for the reason `scripts/test_qemu.sh` states (a Lean tick
# emulated under host-timed TCG outlasts the tick period on four PEs).  These
# are deadlines, not windows: each boot stops as soon as its condition holds.
UNTIL_FRAGMENT="ready, entering kernel"
UNTIL_COUNT=3
DEADLINE="${QEMU_TIMEOUT:-60}"
BOOT_EXTRA=()
if [[ "${LEAN_KERNEL}" -eq 1 ]]; then
    UNTIL_FRAGMENT="first idle dispatch"
    UNTIL_COUNT=4
    DEADLINE="${QEMU_TIMEOUT:-120}"
    BOOT_EXTRA=(-icount "shift=0,sleep=off")
fi

BRINGUP_PASS=true

# bringup_once LABEL MACHINE: boot four PEs on MACHINE and hold the log to the
# fixture.  The check is Python so a row is matched against a whole line, and a
# line is attributed to the core it names, rather than grepped for a substring.
bringup_once() {
    local label="$1" machine="$2" verdict
    log_section "TRACE" "RUN: ${label} — -machine ${machine} -smp 4 (deadline: ${DEADLINE}s)"
    qemu_run "${label}" "${BRINGUP_LOG}" "${machine}" 4 "${DEADLINE}" \
        "${UNTIL_FRAGMENT}" "${UNTIL_COUNT}" "${BOOT_EXTRA[@]}" || BRINGUP_PASS=false
    verdict=$(python3 - "${BRINGUP_LOG}" "${FIXTURE}" "${LEAN_KERNEL}" <<'PY'
import re
import sys

log_path, fixture_path, lean = sys.argv[1], sys.argv[2], sys.argv[3] == "1"
with open(log_path, encoding="utf-8", errors="replace") as handle:
    lines = handle.read().split("\n")
rows = []
with open(fixture_path, encoding="utf-8") as handle:
    for raw in handle:
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        scope, _, prefix = raw.rstrip("\n").partition("|")
        rows.append((scope.strip(), prefix.strip()))

failures = []
if not any(lines):
    failures.append("QEMU produced no output (hung or dead kernel)")
for number, line in enumerate(lines, 1):
    # A torn line: a console tag anywhere but at the start.
    if re.search(r".\[(smp|boot|sched|tick)\] ", line):
        failures.append(f"line {number} is torn: {line!r}")
    if re.search(r"(?i)fatal|panic|unhandled.*exception|serror", line):
        failures.append(f"line {number} reports a fatal condition: {line!r}")

def in_order(stream, prefixes, what):
    at = 0
    for prefix in prefixes:
        while at < len(stream) and not stream[at].startswith(prefix):
            at += 1
        if at == len(stream):
            failures.append(f"{what}: {prefix!r} missing, or out of order")
            return
        at += 1

secondary = [p for s, p in rows if s == "secondary"]
for core in (1, 2, 3):
    tag = f"[smp] core {core}: "
    stream = [line for line in lines if line.startswith(tag)]
    in_order(stream, [p.replace("{N}", str(core)) for p in secondary], f"core {core}")
in_order(lines, [p for s, p in rows if s == "boot"], "boot core")
if lean:
    for _, prefix in (r for r in rows if r[0] == "lean"):
        cores = range(4) if "{N}" in prefix else (None,)
        for core in cores:
            wanted = prefix if core is None else prefix.replace("{N}", str(core))
            if not any(line.startswith(wanted) for line in lines):
                failures.append(f"{wanted!r} missing")
unknown = {s for s, _ in rows} - {"secondary", "boot", "lean"}
if unknown:
    failures.append(f"fixture scope(s) {sorted(unknown)} are not ones this gate reads")
for failure in failures:
    print(failure)
PY
) || { record_failure "TRACE" "${label}: the bring-up check could not run"; BRINGUP_PASS=false; return; }
    if [[ -n "${verdict}" ]]; then
        while IFS= read -r failure; do
            record_failure "TRACE" "${label}: ${failure}"
        done <<< "${verdict}"
        BRINGUP_PASS=false
        log_section "TRACE" "${label}: last 40 lines of the log:"
        tail -n 40 "${BRINGUP_LOG}"
    else
        log_section "TRACE" "PASS: ${label}: four PEs, every banner a whole line, in order ($(wc -l < "${BRINGUP_LOG}") lines)"
    fi
}

bringup_once "four PEs, virt, EL1 entry" "virt,gic-version=2"
bringup_once "four PEs, virt, EL2 entry" "virt,gic-version=2,virtualization=on"

if [[ "${BRINGUP_PASS}" = true ]]; then
    log_section "META" "PASS: four-PE bring-up"
else
    log_section "META" "FAIL: four-PE bring-up"
fi
finalize_report
