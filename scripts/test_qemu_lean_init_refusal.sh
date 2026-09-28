#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-BP BP2.4 — a refused Lean library initialization halts the system, on the
# target (v0.36.31).
#
# BP2.4's refusal path — an `IO` error, a malformed result, a second run — was
# host-tested and had never executed on a PE.  This gate builds the
# Lean-linked `virt` image with the refusal probe (`lean_init_refusal_probe`,
# `rust/sele4n-hal/src/lean_entry.rs`'s `refusal_probe`), a TEST image no board
# boots, and boots it on four PEs at the board's EL2 entry once per mode named
# on the kernel command line.  Every mode drives the same report-and-halt code
# a real refusal runs (`lean_entry::initialise_or_halt`).
#
# The claim is that the boot HALTS rather than continues, so each run is a
# fixed window rather than stopping at the refusal: the refusal must be the
# last line of the log, and nothing of what follows a successful
# initialization -- the heap census, the install, the release of a secondary,
# a secondary's first line, any dispatch -- may appear.  A fourth run with no
# mode holds the probe image to refusing to boot the kernel at all.
#
# Exit codes:
#   0   PASS
#   77  SKIP (SELE4N_SKIP_EXIT) — QEMU, cargo or the cross target is missing;
#       REQUIRE_QEMU=1 makes an absent QEMU a failure.
#   1   FAIL

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"
cd "${REPO_ROOT}"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/qemu_boot_lib.sh"

log_section "META" "=== WS-BP BP2.4: a refused Lean initialization halts the system (QEMU virt, four PEs) ==="

qemu_require_tools
qemu_build_image 1 0 1
qemu_cut_image
qemu_temp_file PROBE_LOG qemu_init_probe

# The window each run is given.  A boot reaches Phase 5 in about two seconds
# under `-icount`, so the rest of the window is silence the halt must keep.
WINDOW="${QEMU_PROBE_WINDOW:-20}"
MACHINE="virt,gic-version=2,virtualization=on"

# mode | the refusal line that must end the log
CASES=(
    "error|[boot] FATAL: Lean library initialization refused: Error"
    "malformed|[boot] FATAL: Lean library initialization refused: Malformed { tag: None }"
    "twice|[boot] FATAL: Lean library initialization refused: AlreadyRan"
    "|[probe] FATAL: no lean_init_probe=<error|malformed|twice> on the command line; the probe image does not boot the kernel"
)

PASS=true
for case in "${CASES[@]}"; do
    mode="${case%%|*}"
    refusal="${case#*|}"
    label="refusal probe, mode '${mode:-none}', EL2 entry, four PEs"
    append=()
    if [[ -n "${mode}" ]]; then
        append=(-append "lean_init_probe=${mode}")
    fi
    log_section "TRACE" "RUN: ${label} — ${WINDOW}s window"
    qemu_run "${label}" "${PROBE_LOG}" "${MACHINE}" 4 "${WINDOW}" "" 0 \
        -icount "shift=0,sleep=off" "${append[@]}" || PASS=false
    verdict=$(python3 - "${PROBE_LOG}" "${mode}" "${refusal}" <<'PY'
import re
import sys

log_path, mode, refusal = sys.argv[1:4]
with open(log_path, encoding="utf-8", errors="replace") as handle:
    lines = [line for line in handle.read().split("\n") if line.strip()]
failures = []
if not lines:
    failures.append("QEMU produced no output (hung or dead kernel)")
else:
    # The refusal ends the log: nothing runs after the halt.
    if lines[-1] != refusal:
        failures.append(f"the log does not end with the refusal {refusal!r}; it ends with {lines[-1]!r}")
    if sum(1 for line in lines if "FATAL" in line) != 1:
        failures.append(f"expected exactly one FATAL line: {[l for l in lines if 'FATAL' in l]!r}")
for number, line in enumerate(lines, 1):
    if re.search(r".\[(smp|boot|sched|probe|lean_heap)\] ", line):
        failures.append(f"line {number} is torn: {line!r}")
    # What a successful initialization is followed by, none of which may run.
    for forbidden in ("[boot] Lean heap after", "[boot] Phase 5", "[smp] releasing the secondaries",
                      "[boot] Phase 6", "[sched] core"):
        if line.startswith(forbidden):
            failures.append(f"line {number}: the boot continued past the refusal: {line!r}")
    if re.match(r"\[smp\] core [1-9]:", line):
        failures.append(f"line {number}: a secondary ran: {line!r}")
if mode:
    expected = f"[probe] Lean initialization refusal probe: mode {mode.capitalize()}"
    if expected not in lines:
        failures.append(f"{expected!r} missing: the probe did not drive the mode named")
if mode == "twice":
    first = "[probe] the real initializer succeeded; asking for a second run"
    if first not in lines:
        failures.append(f"{first!r} missing: the second run was not asked for after a real one")
    elif lines.index(first) > len(lines) - 2:
        failures.append("the real initializer's success is not before the refusal")
for failure in failures:
    print(failure)
PY
) || { record_failure "TRACE" "${label}: the check could not run"; finalize_report; }
    if [[ -n "${verdict}" ]]; then
        PASS=false
        while IFS= read -r failure; do
            record_failure "TRACE" "${label}: ${failure}"
        done <<< "${verdict}"
        log_section "TRACE" "${label}: last 20 lines of the log:"
        tail -n 20 "${PROBE_LOG}"
    else
        log_section "TRACE" "PASS: ${label}: refused, and nothing ran after the refusal ($(wc -l < "${PROBE_LOG}") lines)"
    fi
done

if [[ "${PASS}" = true ]]; then
    log_section "META" "PASS: a refused Lean initialization halts the system"
else
    log_section "META" "FAIL: a refused Lean initialization halts the system"
fi
finalize_report
