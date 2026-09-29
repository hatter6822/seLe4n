#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM1.H.3 / WS-BP BP6.3 / WS-BP BP8.4 — the PE-withheld boot.
#
# Boots the `virt` image on TWO PEs, where the kernel expects four, and holds
# each image to what it must do with a machine narrower than it was built for:
#
# * The HAL-only image boots: one secondary comes up, Phase 6 counts exactly
#   one, and no line names a core that does not exist.  (SM1.H.3's minimal
#   bring-up, which used to ask for a kernel ELF no target built.)
# * The Lean-linked image REFUSES: the linked kernel declares four PEs, so
#   Phase 7 waits its bounded window for the two that never publish, names
#   each of them with the half of readiness it lacks, and halts the system
#   before the boot core hands itself to the idle wait — so the boot core,
#   whose run queues hold every started thread of the deployment, never
#   dispatches, and nothing is served to user space on a machine one core
#   cannot serve.  The secondary that DID come up serves the kernel while the
#   boot core waits: a tick there dispatches that core's own idle thread,
#   which the log reports (`[sched] core 1: first idle dispatch`) and which
#   is the kernel idling on a PE that serves it, not a thread being served.
#   The check therefore forbids the boot core's dispatch and any dispatch on
#   a PE the machine does not have, and admits the serving secondary's.
#   That is WS-BP BP6.3's second acceptance box, decided by this run rather
#   than asserted.
#
# Usage:
#   ./scripts/test_qemu_smp_minimal.sh                 # HAL-only: boots on two PEs
#   ./scripts/test_qemu_smp_minimal.sh --lean-kernel   # Lean-linked: refuses two PEs
#
# Exit codes:
#   0   PASS
#   77  SKIP / NOT RUN (SELE4N_SKIP_EXIT) — QEMU, cargo or the cross target is
#       missing.  REQUIRE_QEMU=1 makes an absent QEMU a failure.
#   1   FAIL

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"
cd "${REPO_ROOT}"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/qemu_boot_lib.sh"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/qemu_exerciser_lib.sh"

exerciser_parse_args "$@"
log_section "META" "=== WS-SM SM1.H.3 / WS-BP BP6.3: the PE-withheld boot under QEMU virt (-smp 2) ==="

qemu_require_tools
qemu_build_image "${LEAN_KERNEL}" 0
qemu_cut_image
qemu_temp_file MINIMAL_LOG qemu_minimal

# The HAL-only image is done once its one secondary is ready; the Lean-linked
# one once it has refused (its FATAL line), under `-icount` for the reason
# `scripts/test_qemu.sh` states.
UNTIL_FRAGMENT="[smp] core 1: ready, entering kernel"
DEADLINE="${QEMU_TIMEOUT:-120}"
BOOT_EXTRA=()
LABEL="two PEs, HAL-only image, virt, EL2 entry"
if [[ "${LEAN_KERNEL}" -eq 1 ]]; then
    UNTIL_FRAGMENT="[boot] FATAL:"
    DEADLINE="${QEMU_TIMEOUT:-300}"
    BOOT_EXTRA=(-icount "shift=0,sleep=off")
    LABEL="two PEs, Lean-linked image, virt, EL2 entry"
fi

log_section "TRACE" "RUN: ${LABEL} — -machine ${EXERCISER_MACHINE} -smp 2 (deadline: ${DEADLINE}s)"
qemu_run "${LABEL}" "${MINIMAL_LOG}" "${EXERCISER_MACHINE}" 2 "${DEADLINE}" \
    "${UNTIL_FRAGMENT}" 1 "${BOOT_EXTRA[@]}" || true

verdict=$(python3 - "${MINIMAL_LOG}" "${LEAN_KERNEL}" <<'PY'
import re
import sys

log_path, lean = sys.argv[1], sys.argv[2] == "1"
with open(log_path, encoding="utf-8", errors="replace") as handle:
    lines = handle.read().split("\n")
failures = []
if not any(lines):
    failures.append("QEMU produced no output (hung or dead kernel)")

def require(text):
    if text not in lines:
        failures.append(f"{text!r} missing")

def require_prefix(prefix):
    if not any(line.startswith(prefix) for line in lines):
        failures.append(f"no line starts with {prefix!r}")

for number, line in enumerate(lines, 1):
    if re.search(r".\[(smp|boot|sched|tick|smp-test|gic|kernel-entry)\] ", line):
        failures.append(f"line {number} is torn: {line!r}")
    if re.search(r"(?i)panic|unhandled.*exception|serror", line):
        failures.append(f"line {number} reports a fatal condition: {line!r}")
    if re.match(r"\[smp\] core [23]:", line):
        failures.append(f"line {number} names a PE the machine does not have: {line!r}")
require("[smp] core 1: ready, entering kernel")
fatal = [line for line in lines if line.startswith("[boot] FATAL:")]
if lean:
    # The refusal, naming the count it found and the count the kernel declares.
    require_prefix("[boot] FATAL: 2 PE(s) serving the kernel but the linked Lean kernel declares 4")
    for core in (2, 3):
        require(f"[boot]   PE {core}: IRQ-ready false, Lean-ready false")
    if any(line.startswith("[boot] FATAL:") and "serving the kernel" not in line for line in lines):
        failures.append(f"a fatal condition other than the topology refusal: {fatal!r}")
    # The refusal halts the system before the boot core hands itself to the
    # idle wait, so the boot core never dispatches; a serving secondary may
    # dispatch its own idle thread while the boot core waits its window.
    for line in lines:
        if line.startswith("[sched] core 0:"):
            failures.append(f"the boot core dispatched before the refusal: {line!r}")
        if re.match(r"\[sched\] core [23]:", line):
            failures.append(f"a PE the machine does not have dispatched: {line!r}")
else:
    require("[boot] Phase 6: 1 secondary core(s) online (max requested: 4)")
    require("[boot] Boot complete")
    if fatal:
        failures.append(f"the HAL-only image refused a two-PE machine: {fatal!r}")
for failure in failures:
    print(failure)
PY
) || { record_failure "TRACE" "${LABEL}: the check could not run"; finalize_report; }
if [[ -n "${verdict}" ]]; then
    while IFS= read -r failure; do
        record_failure "TRACE" "${LABEL}: ${failure}"
    done <<< "${verdict}"
    log_section "TRACE" "${LABEL}: last 40 lines of the log:"
    tail -n 40 "${MINIMAL_LOG}"
    log_section "META" "FAIL: the PE-withheld boot"
else
    log_section "TRACE" "PASS: ${LABEL} ($(wc -l < "${MINIMAL_LOG}") lines)"
    log_section "META" "PASS: the PE-withheld boot"
fi
finalize_report
