#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-BP BP8.4: the one way the Tier-4 exerciser gates boot the test image and
# read its console.  Sourced after `test_lib.sh` and `qemu_boot_lib.sh`; never
# executed.
#
# Every exerciser gate boots the same image — the `virt` image with the
# in-image drivers (`smp_exercisers`, `rust/sele4n-hal/src/smp_exercisers.rs`)
# — on four PEs at EL2, the Raspberry Pi 5 firmware's entry level, HAL-only
# or, with `--lean-kernel`, Lean-linked, and holds the log to the banners its
# driver prints.  The four drivers run in one boot, so a gate that reads one
# driver's banners still boots all four; `scripts/test_qemu_smp_exercisers.sh`
# reads all of them from one boot, which is what the Lean archive lane runs.
#
# Until WS-BP BP8.4 every one of these gates SKIPped on every run: each asked
# for a kernel ELF no target built and looked for its driver's banner in that
# image with `strings`.  The drivers exist now, in a test image no board boots.
#
# A banner is a line (WS-BP BP8.2's rule): a driver's lines are matched whole,
# and a console tag anywhere but at a line's start is a torn line and a
# failure.  What each driver's lines must say is a relation, not a token: the
# acknowledged generations must reach the round's, every core's stress lines
# must be exactly the iterations 0..31 once each, and the stress rounds must
# carry 32 distinct generations — one per round, which is what the round lock
# serialising them means.

EXERCISER_MACHINE="virt,gic-version=2,virtualization=on"
EXERCISER_SUMMARY="[smp-test] exercisers: "
EXERCISER_DRIVERS=(sgi-round-trip kprintln-stress tlb-shootdown tlb-shootdown-stress per-core-stats)

# exerciser_parse_args "$@": `--lean-kernel` selects the Lean-linked image
# (LEAN_KERNEL=1); any other argument is an error.
exerciser_parse_args() {
    LEAN_KERNEL=0
    local arg
    for arg in "$@"; do
        case "${arg}" in
            --lean-kernel) LEAN_KERNEL=1 ;;
            *) echo "${0##*/}: unknown argument: ${arg}" >&2; exit 2 ;;
        esac
    done
}

# exerciser_boot LABEL: build the exerciser image (Lean-linked when LEAN_KERNEL
# is 1), boot it on four PEs until its summary line, and name the log in
# EXERCISER_LOG.  The Lean-linked image runs under `-icount` for the reason
# `scripts/test_qemu.sh` states.
exerciser_boot() {
    local label="$1" deadline extra=()
    qemu_require_tools
    qemu_build_image "${LEAN_KERNEL}" 1
    qemu_cut_image
    qemu_temp_file EXERCISER_LOG qemu_exercisers
    deadline="${QEMU_TIMEOUT:-120}"
    if [[ "${LEAN_KERNEL}" -eq 1 ]]; then
        deadline="${QEMU_TIMEOUT:-300}"
        extra=(-icount "shift=0,sleep=off")
    fi
    log_section "TRACE" "RUN: ${label} — -machine ${EXERCISER_MACHINE} -smp 4 (deadline: ${deadline}s)"
    # The summary is the third `[smp-test] exercisers: ` line — the
    # announcement, the window, the tally.  A run that never prints it runs to
    # the deadline and fails the check below.
    qemu_run "${label}" "${EXERCISER_LOG}" "${EXERCISER_MACHINE}" 4 "${deadline}" \
        "${EXERCISER_SUMMARY}" 3 "${extra[@]}"
}

# exerciser_check LABEL DRIVER...: hold EXERCISER_LOG to the named drivers'
# banners — each of `sgi-round-trip`, `kprintln-stress`, `tlb-shootdown`,
# `tlb-shootdown-stress`, `per-core-stats` (WS-BP BP8.5; the Lean-linked image
# only, since the reader and the verdict are the kernel's), or `all` for every
# driver the image runs and the summary tally.  Records a failure per finding;
# returns 1 on any.
exerciser_check() {
    local label="$1" verdict
    shift
    verdict=$(python3 - "${EXERCISER_LOG}" "${LEAN_KERNEL}" "$@" <<'PY'
import re
import sys

log_path, lean, drivers = sys.argv[1], sys.argv[2] == "1", sys.argv[3:]
with open(log_path, encoding="utf-8", errors="replace") as handle:
    lines = handle.read().split("\n")
failures = []
if not any(lines):
    failures.append("QEMU produced no output (hung or dead kernel)")
for number, line in enumerate(lines, 1):
    # A torn line: a console tag anywhere but at the start.
    if re.search(r".\[(smp|boot|sched|tick|smp-test|gic|kernel-entry|core \d)\] ", line):
        failures.append(f"line {number} is torn: {line!r}")
    if re.search(r"(?i)fatal|panic|unhandled.*exception|serror", line):
        failures.append(f"line {number} reports a fatal condition: {line!r}")

def require(text):
    if text not in lines:
        failures.append(f"{text!r} missing")

def matches(pattern):
    return [m for m in (re.fullmatch(pattern, line) for line in lines) if m]

require("[smp-test] exercisers: test image; the Tier-4 in-image drivers follow")
for line in lines:
    if line.startswith("[smp-test] exercisers: not run"):
        failures.append(f"the drivers did not run: {line!r}")
if not any(line.startswith("[smp-test] exercisers: window installed at ") for line in lines):
    failures.append("the exercisers' window was not installed")
every = ["sgi-round-trip", "kprintln-stress", "tlb-shootdown", "tlb-shootdown-stress"]
if lean:
    every.append("per-core-stats")
if "all" in drivers:
    drivers = every
    require(f"[smp-test] exercisers: {len(every)} passed, 0 failed")
for driver in drivers:
    for line in lines:
        if line == f"[smp-test] FAIL: {driver}" or line.startswith(f"[smp-test] FAIL: {driver}:"):
            failures.append(f"the driver reported a failure: {line!r}")
    if driver == "sgi-round-trip":
        require("[smp-test] SGI round-trip complete")
        for core in (1, 2, 3):
            require(f"[smp-test] sgi-round-trip: core 0 sending SGI 15 to core {core}")
            require(f"[smp-test] core {core}: received SGI 15 from core 0, sending ack")
            require(f"[smp-test] core 0: ack received from core {core} (SGI source {core})")
            counts = matches(rf"\[smp-test\] sgi-round-trip: core {core} SGI count \+(\d+), core 0 SGI count \+(\d+)")
            if len(counts) != 1:
                failures.append(f"sgi-round-trip: core {core}: expected one SGI count line, found {len(counts)}")
            elif int(counts[0].group(1)) < 1 or int(counts[0].group(2)) < 1:
                failures.append(f"sgi-round-trip: core {core}: an SGI counter did not move: {counts[0].group(0)!r}")
    elif driver == "kprintln-stress":
        require("[smp-test] kprintln-stress: every core printed 32 lines")
        for core in range(4):
            iterations = sorted(int(m.group(1)) for m in matches(rf"\[core {core}\] stress iter (\d+)"))
            if iterations != list(range(32)):
                failures.append(f"kprintln-stress: core {core} printed iterations {iterations}, expected 0..31 once each")
    elif driver == "tlb-shootdown":
        require("[smp-test] tlb-shootdown: stale translation removed")
        if len(matches(r"\[smp-test\] tlb-shootdown: core 0 generation 1: round (\d+) complete")) != 1:
            failures.append("tlb-shootdown: expected one completed round from core 0")
        acknowledged = matches(r"\[smp-test\] tlb-shootdown: round generation (\d+) acknowledged: core 1 at (\d+), core 2 at (\d+), core 3 at (\d+)")
        if len(acknowledged) != 1:
            failures.append(f"tlb-shootdown: expected one acknowledgment line, found {len(acknowledged)}")
        else:
            generation = int(acknowledged[0].group(1))
            for core in (1, 2, 3):
                acked = int(acknowledged[0].group(core + 1))
                if acked < generation:
                    failures.append(f"tlb-shootdown: core {core} acknowledged generation {acked}, below the round's {generation}")
    elif driver == "tlb-shootdown-stress":
        require("[smp-test] tlb-shootdown-stress: all cores completed (8 generations, 32 rounds)")
        rounds = [(int(m.group(1)), int(m.group(2)), int(m.group(3)))
                  for m in matches(r"\[smp-test\] tlb-shootdown-stress: core (\d) generation (\d+): round (\d+) complete")]
        expected = {(core, generation) for core in range(4) for generation in range(2, 10)}
        if len(rounds) != 32 or {(core, generation) for core, generation, _ in rounds} != expected:
            failures.append(f"tlb-shootdown-stress: expected every core to complete generations 2..9 once (32 rounds), found {len(rounds)}")
        generations = [generation for _, _, generation in rounds]
        if len(set(generations)) != len(generations):
            failures.append("tlb-shootdown-stress: two rounds carry one generation, so the round lock did not serialise them")
        for line in lines:
            if line.startswith("[smp-test] tlb-shootdown-stress: stale translation"):
                failures.append(f"a stale translation survived a round: {line!r}")
    elif driver == "per-core-stats":
        # WS-BP BP8.5: the relations, re-derived from the words the seam
        # reported rather than taken from the driver's own verdict -- the
        # verdict `1` beside words that refute it is a seam answering `1`
        # unconditionally, which the driver alone could not see.
        require("[smp-test] per-core-stats: every core's snapshot is plausible, ticked, and inside its own slot's bracket")
        sgis_by_core = {}
        for core in range(4):
            lean_lines = matches(rf"\[smp-test\] per-core-stats: core {core}: lean irqs=(\d+) timer-ticks=(\d+) sgis=(\d+) syscalls=(\d+) plausible=(\d+)")
            rust_lines = matches(rf"\[smp-test\] per-core-stats: core {core}: rust before irqs=(\d+) timer-ticks=(\d+) sgis=(\d+) syscalls=(\d+) after irqs=(\d+) timer-ticks=(\d+) sgis=(\d+) syscalls=(\d+)")
            if len(lean_lines) != 1 or len(rust_lines) != 1:
                failures.append(f"per-core-stats: core {core}: expected one Lean line and one Rust line, found {len(lean_lines)} and {len(rust_lines)}")
                continue
            irqs, ticks, sgis, syscalls, plausible = (int(g) for g in lean_lines[0].groups())
            before = tuple(int(g) for g in rust_lines[0].groups()[:4])
            after = tuple(int(g) for g in rust_lines[0].groups()[4:])
            words = (irqs, ticks, sgis, syscalls)
            if plausible != 1:
                failures.append(f"per-core-stats: core {core}: the verdict is {plausible}, not 1")
            if ticks + sgis > irqs:
                failures.append(f"per-core-stats: core {core}: the words refute the verdict: {ticks} + {sgis} > {irqs}")
            if irqs == 0 or ticks == 0:
                failures.append(f"per-core-stats: core {core}: a serving core reports irqs={irqs} timer-ticks={ticks}")
            if not all(b <= w <= a for b, w, a in zip(before, words, after)):
                failures.append(f"per-core-stats: core {core}: a word is outside its slot's bracket: before {before}, lean {words}, after {after}")
            sgis_by_core[core] = sgis
        if len(set(sgis_by_core.values())) != len(sgis_by_core):
            failures.append(f"per-core-stats: two cores report one SGI count ({sgis_by_core}), so a wrong slot could not be told from the right one")
    else:
        failures.append(f"unknown driver {driver!r}")
for failure in failures:
    print(failure)
PY
    ) || { record_failure "TRACE" "${label}: the exerciser check could not run"; return 1; }
    if [[ -n "${verdict}" ]]; then
        while IFS= read -r failure; do
            record_failure "TRACE" "${label}: ${failure}"
        done <<< "${verdict}"
        log_section "TRACE" "${label}: last 60 lines of the log:"
        tail -n 60 "${EXERCISER_LOG}"
        return 1
    fi
    log_section "TRACE" "PASS: ${label} ($(wc -l < "${EXERCISER_LOG}") lines, every banner a whole line)"
    return 0
}

# exerciser_gate ID SUBJECT DRIVER... [-- "$@"]: the whole of a single-driver
# gate — parse the arguments, boot, check, report.
exerciser_gate() {
    local id="$1" subject="$2" driver="$3" known candidate
    shift 3
    exerciser_parse_args "$@"
    # A gate names a driver the library checks, or `all`; a driver nobody
    # checks would boot the image and decide nothing.
    known=0
    for candidate in "${EXERCISER_DRIVERS[@]}" all; do
        [[ "${driver}" == "${candidate}" ]] && known=1
    done
    if [[ "${known}" -ne 1 ]]; then
        echo "${0##*/}: unknown exerciser driver: ${driver}" >&2
        exit 2
    fi
    log_section "META" "=== ${id}: ${subject} under QEMU virt ==="
    local image="HAL-only"
    [[ "${LEAN_KERNEL}" -eq 1 ]] && image="Lean-linked"
    exerciser_boot "${subject}, ${image} image, four PEs, EL2 entry" || true
    if exerciser_check "${subject}" "${driver}"; then
        log_section "META" "PASS: ${subject}"
    else
        log_section "META" "FAIL: ${subject}"
    fi
    finalize_report
}

# exerciser_user_program_gate ID SUBJECT SUITE BANNER: a Tier-4 gate that needs
# a user-level driver program, which the image does not carry.  Reports NOT RUN
# with the reason and the banner the gate will require once it can run, and
# exits SELE4N_SKIP_EXIT; `run_gate_check` records it, and
# `SELE4N_REQUIRE_GATES=1` makes it a failure.
exerciser_user_program_gate() {
    local id="$1" subject="$2" suite="$3" banner="$4"
    echo "[SKIP] ${id}: ${subject} — NOT RUN: needs a user program"
    echo ""
    echo "  This gate drives kernel transitions from user space — a thread issuing the"
    echo "  syscalls on one core while a thread on another core observes the effect — so"
    echo "  it needs a user-level driver program.  The kernel image carries none: the"
    echo "  two initial threads WS-BP BP7.11 starts run no code, and a user program is"
    echo "  SM10's root task.  Until it exists this gate cannot run, and says so rather"
    echo "  than looking for its banner in an image with 'strings', which is what it"
    echo "  did until WS-BP BP8.4.  Registered: docs/REGISTERED_DEBT.md (WS-BP)."
    echo ""
    echo "  The property is established for every execution, machine-checked, by"
    echo "  ${suite}; this gate is its runtime spot-check on emulated cores."
    echo "  Once the driver program exists it must print, as a whole line:"
    echo "    ${banner}"
    exit "${SELE4N_SKIP_EXIT:-77}"
}
