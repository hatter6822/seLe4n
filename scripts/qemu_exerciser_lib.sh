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
EXERCISER_DRIVERS=(sgi-round-trip kprintln-stress tlb-shootdown tlb-shootdown-stress per-core-stats heap-allocations-per-syscall remote-stall)

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
# EXERCISER_LOG.
#
# Both images run under `-icount shift=0,sleep=off`, the HAL-only one included,
# because the drivers' verdicts are **bounded waits** — a round's acknowledgment
# wait (`ROUND_WAIT_TIMEOUT_TICKS`, 540000 ticks, the seam's own budget), the
# round lock's acquisition fuel and every command's two-second timeout — and
# under multi-threaded TCG the guest's counter is the host's wall clock.  A vCPU
# thread the host preempts for longer than a round's 8.6 ms budget then misses
# the round, which halts the system as the seam does on hardware: measured, the
# HAL-only stress passed on an idle 4-CPU host and failed with exactly that
# signature — a round timed out with one core's acknowledgment lagging and the
# other initiators out of lock fuel — with two CPU hogs beside it.  That is a
# verdict about the host's scheduler, not the protocol.  Under `-icount` the
# clock counts guest instructions, so every wait is decided by what the guest
# does.  (The Lean-linked image needed it first for the reason
# `scripts/test_qemu.sh` states: one emulated Lean tick outlasts the 1 ms
# period.)
exerciser_boot() {
    local label="$1" deadline extra=(-icount "shift=0,sleep=off")
    qemu_require_tools
    qemu_build_image "${LEAN_KERNEL}" 1
    qemu_cut_image
    qemu_temp_file EXERCISER_LOG qemu_exercisers
    deadline="${QEMU_TIMEOUT:-300}"
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
# only, since the reader and the verdict are the kernel's),
# `heap-allocations-per-syscall` (WS-CV CV0.1; Lean-linked only, it measures a
# syscall through the Lean kernel), `remote-stall` (the remote-core stall's
# protocol between the boot core and each secondary), or `all` for every
# driver the image runs and the summary tally.  Records a failure per finding;
# returns 1 on any.
exerciser_check() {
    local label="$1" verdict kinds="" kinds_status=0
    shift
    # WS-UC UC1: the object kinds an untyped retype can name, derived from the
    # retype's own decode (`scripts/retype_object_kinds.lean`, run by Lean) and
    # not listed here: the allocation gate holds each to a carve scenario and
    # to a delete of the carved capability.  A derivation that fails, or
    # answers nothing, fails the gate; it is never read as no kinds.
    if [[ "${LEAN_KERNEL}" -eq 1 ]]; then
        ensure_lake_available || kinds_status=$?
        if [[ "${kinds_status}" -eq 0 ]]; then
            kinds=$(cd "${REPO_ROOT}" && lake env lean --run scripts/retype_object_kinds.lean 2>&1) \
                || kinds_status=$?
        fi
    fi
    verdict=$(RETYPE_OBJECT_KINDS="${kinds}" RETYPE_OBJECT_KINDS_STATUS="${kinds_status}" \
        EXERCISER_REPO_ROOT="${REPO_ROOT}" python3 - "${EXERCISER_LOG}" "${LEAN_KERNEL}" "$@" <<'PY'
import os
import re
import subprocess
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
    every.append("heap-allocations-per-syscall")
every.append("remote-stall")
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
    elif driver == "remote-stall":
        # The remote-core stall (seL4's remoteTCBStall): per secondary, the
        # poke ended a wait on a core at user, and a core in the kernel was
        # requested and its exit gate refused the return; on the Lean-linked
        # image its next kernel entry also met the request.
        require("[smp-test] remote-stall: every core left user mode before the stall returned")
        for core in (1, 2, 3):
            require(f"[smp-test] remote-stall: core {core}: at user, poked, entered the kernel before the stall returned")
            require(f"[smp-test] remote-stall: core {core}: in the kernel, requested; its exit gate refused the return to user")
            if lean:
                require(f"[smp-test] remote-stall: core {core}: its next kernel entry met the request")
    elif driver == "heap-allocations-per-syscall":
        # A kernel entry allocates nothing (CLAUDE.md; WS-CV CV0.1, WS-ZA
        # ZA4.1 to ZA6.35).  Each round trip runs twice on the boot core, its
        # first call and its steady state, and every other kernel entry (the
        # timer tick, the reschedule SGI, the fault and interrupt entries) is
        # measured the same way.  The gate holds that each run's reading
        # happened once, after the round trip returned a frame or blocked as it
        # should, is a delta, and is zero, except a retype's: a retype that
        # succeeded names the object it carved (`carved <kind>/<size bits>`),
        # and its reading must be exactly that object's own cells.  Each
        # reading also prints the bytes of the cells it counted, by size
        # (WS-UC UC1): the sizes must account for exactly the counted cells
        # and the bytes for exactly the sizes, and the bytes are pinned beside
        # the cells.
        readings = [m for m in matches(r"\[smp-test\] heap-allocations-per-syscall: ([a-z0-9-]+): core 0( \(first call\))?: before=(\d+) after=(\d+) delta=(\d+) bytes=(\d+|unrecorded) sizes=(none|unrecorded|\d+x\d+(?:,\d+x\d+)*)$") if m.group(1) != "secondary-entry"]
        unparsed = [m for m in matches(r"\[smp-test\] heap-allocations-per-syscall: ([a-z0-9-]+): core 0( \(first call\))?: before=.*$") if m.group(1) != "secondary-entry" and not re.fullmatch(r".*: before=\d+ after=\d+ delta=\d+ bytes=(\d+|unrecorded) sizes=(none|unrecorded|\d+x\d+(?:,\d+x\d+)*)", m.group(0))]
        for m in unparsed:
            failures.append(f"heap-allocations-per-syscall: a reading whose bytes could not be read: {m.group(0)!r}")
        returned = matches(r"\[smp-test\] heap-allocations-per-syscall: ([a-z0-9-]+): core 0( \(first call\))?: (?:returned x0=0x[0-9a-f]+ x1=0x[0-9a-f]+|blocked, the other thread restored|entered, a thread restored)$")
        carves = matches(r"\[smp-test\] heap-allocations-per-syscall: ([a-z0-9-]+): core 0( \(first call\))?: carved ([a-z-]+/\d+) at (\d+) into (0x[0-9a-f]+/\d+)$")
        names = [m.group(1) for m in readings]
        # The cells of the object a carve makes, by kind and size bits, and
        # their bytes: the object's record and the cells it is built of, its
        # entry in the object table (the index, index set and type table are
        # proof-only ghosts since WS-UC UC2, and build no cells), and its child
        # record in the untyped.  Nothing
        # else a retype does may allocate: not its decode, not its carve
        # request, not the capability it writes.  Pinned here, cells then
        # bytes: a kind whose object changes shape changes its pins, and a
        # kind the exerciser carves that has no pin fails.  The breakdown of
        # each pin is the table in docs/planning/UNTYPED_BACKED_CELLS_PLAN.md.
        carve_cells = {
            "endpoint/0": (6, 248), "notification/0": (6, 240), "reply/0": (10, 256),
            "tcb/0": (19, 2040), "sched-context/7": (8, 440), "cnode/2": (23, 1128),
            "frame/0": (6, 152), "page-table/0": (8, 232), "vspace-root/0": (101, 3568),
            "untyped/12": (7, 184),
        }
        # The scenario set is pinned: a round trip renamed or dropped from
        # the exerciser (smp_exercisers.rs) must change this set too, so the
        # evidence cannot disappear while the gate stays green.
        expected = {
            "audit-drain", "audit-drain-first", "audit-read-basis-chunk",
            "audit-read-basis-count", "audit-read-chain-archived", "audit-read-chain-entry",
            "audit-read-chain-predecessor", "audit-read-entry", "audit-read-refusal-counters",
            "audit-read-refusal-domain", "audit-read-refusal-domain-count",
            "audit-read-refusal-receiver", "audit-read-refusal-receiver-count",
            "audit-read-refusal-status",
            "audit-read-refusal-subject", "audit-read-refusal-subject-count",
            "audit-read-refusal-tags", "audit-read-refusal-target",
            "audit-read-refusal-target-count", "audit-read-status", "badged-call",
            "badged-send-blocks", "badged-send-to-receiver", "bind-carved-notification",
            "bind-carved-sched-context", "bind-carved-tcb", "bound-notification-delete",
            "bound-sched-context-delete", "bound-tcb-delete", "busy-endpoint-delete",
            "busy-notification-delete", "busy-reply-cap-delete", "busy-reply-delete", "call",
            "child-untyped-delete",
            "call-to-carved-reply", "call-to-reply-receiver", "cap-fault-delivered",
            "cap-fault-delivered-to-reply", "cap-fault-plain-reply",
            "cap-fault-reply", "cap-fault-resume", "cap-fault-suspends", "chain-bind-partner",
            "chain-configure", "chain-reply-cap-delete", "chain-reply-cap-mint",
            "chain-reply-delete", "chain-resume-partner", "chain-resume-root",
            "chain-resume-server", "chain-root-calls-server", "chain-root-receives",
            "chain-root-replies", "chain-server-receives", "chain-server-reply-recv",
            "chain-suspend-partner", "chain-suspend-root", "chain-suspend-server",
            "chain-tcb-delete", "chain-tcb-set-priority", "chain-tcb-set-space",
            "chain-unbind", "cnode-delete", "contextless-context-delete",
            "contextless-partner-calls", "contextless-resume-server", "contextless-root-waits",
            "contextless-server-calls", "contextless-server-receives",
            "contextless-server-resumes-top", "contextless-suspend-partner",
            "contextless-suspend-top", "contextless-top-cap-delete", "contextless-top-delete",
            "contextless-top-receives", "contextless-top-resumes-partner",
            "contextless-top-waits", "contextless-top-wakes-root", "cross-core-home-root",
            "cross-core-home-root-back", "cross-core-partner-calls", "cspace-copy",
            "cspace-delete", "cspace-mint", "cspace-move", "cspace-revoke",
            "declassified-signal", "declassified-signal-bound", "declassified-signal-two-hop",
            "declassified-signal-wakes", "declassified-wait-blocks",
            "declassified-wait-pending",
            "declassify", "declassify-refused", "declassified-signal-refused-at-receiver",
            "endpoint-delete", "exhaust-drain-tick",
            "exhaust-tick", "failed-lookup-depth-mismatch", "failed-lookup-guard-mismatch",
            "failed-lookup-missing-source", "fp-access", "fp-access-partner", "fp-owner-blocks",
            "fp-owner-wakes-root", "frame-copy-delete", "frame-copy-for-revoke",
            "frame-copy-mapped", "frame-delete", "frame-revoke", "head-partner-calls",
            "head-reply-cap-delete", "head-reply-delete", "head-server-receives",
            "head-server-resumes-partner", "head-server-waits", "head-server-wakes-root",
            "inactive-tcb-delete", "irq-control-copy", "irq-control-copy-delete", "irq-control-get",
            "irq-control-mint",
            "irq-control-mint-attenuated", "irq-control-mint-attenuated-delete",
            "irq-control-mint-badged", "irq-control-mint-badged-delete", "irq-control-mint-delete", "irq-handler-ack", "irq-handler-clear",
            "irq-handler-delete", "irq-handler-set-notification", "irq-notification-revoke",
            "irq-revoked-line", "irq-signal-bound", "irq-signal-no-waiter", "irq-signal-waiter",
            "irq-spurious",
            "irq-unbound", "long-send-bind-partner", "long-send-configure",
            "long-send-partner-yield", "long-send-resume-partner", "long-send-root-receives",
            "long-send-suspend", "long-send-to-receiver", "long-send-unbind",
            "middle-reply-cap-delete", "middle-reply-delete",
            "mint-busy-reply-cap", "mint-stashed-reply-cap", "notification-delete",
            "orphan-head-reply-delete", "orphan-holder-delete",
            "orphan-middle-reply-cap-delete", "orphan-middle-reply-delete",
            "orphan-partner-calls", "orphan-recv-partner-calls", "orphan-recv-partner-waits",
            "orphan-recv-partner-wakes-root", "orphan-recv-reply-cap-delete",
            "orphan-recv-reply-cap-mint", "orphan-recv-reply-delete",
            "orphan-recv-resume-server", "orphan-recv-root-waits", "orphan-recv-server-delete",
            "orphan-recv-server-receives", "orphan-recv-server-resumes-partner",
            "orphan-recv-server-set-priority", "orphan-recv-server-set-space",
            "orphan-recv-server-waits", "orphan-recv-server-wakes-root",
            "orphan-recv-suspend-partner", "orphan-reply-cap-delete", "orphan-reply-recv",
            "orphan-resume-server", "orphan-root-answers-server", "orphan-root-waits",
            "orphan-root-waits-server", "orphan-server-calls", "orphan-server-receives",
            "orphan-server-reply-cap-mint", "orphan-server-resumes-top", "orphan-server-waits",
            "orphan-server-wakes-root", "orphan-stack-bind-partner", "orphan-stack-configure",
            "orphan-stack-unbind", "orphan-suspend-server", "orphan-top-receives",
            "orphan-top-reply-cap-delete", "orphan-top-reply-cap-mint",
            "orphan-top-reply-delete", "orphan-top-resumes-partner", "orphan-top-set-priority",
            "orphan-top-set-space", "orphan-top-waits", "orphan-top-wakes-root",
            "page-table-delete-1", "page-table-delete-2", "page-table-delete-3",
            "page-table-map-1", "page-table-map-2", "page-table-map-3", "page-table-unmap-1",
            "page-table-unmap-2", "page-table-unmap-3", "populated-cnode-delete",
            "postpone-bind-partner", "postpone-configure", "postpone-partner-yield",
            "postpone-resume-partner", "postpone-root-receives", "postpone-suspend",
            "postpone-unbind", "postpone-wake-root", "queue-endpoint-delete",
            "queue-partner-receives", "queue-partner-wakes-root", "queue-resume-top",
            "queue-root-waits", "queue-suspend-partner", "queue-suspend-top",
            "queue-top-receives", "queue-top-resumes-partner", "queued-tcb-delete",
            "receive-blocks", "receive-for-badged-call", "receive-for-badged-send",
            "receive-for-call", "receive-from-badged-sender", "receive-from-sender",
            "receive-on-carved", "receive-queued-fault", "receive-stashing-reply",
            "range-error-payload",
            # Argument words at or above 2^63, each refused on the word, and
            # the measured mint of a badge at 2^63.
            "vspace-map-wide-asid", "vspace-map-wide-vaddr", "vspace-map-wide-perms",
            "vspace-unmap-wide-vaddr", "tcb-set-affinity-wide",
            "mint-wide-badged-notification",
            "receive-tainted", "receive-with-carved-reply", "refill-bind-root",
            "refill-configure", "refill-drain-tick", "refill-unbind-root", "refill-wait-tick",
            "refill-yield", "reply", "reply-cap-delete", "reply-cap-mint",
            "reply-cap-mint-over-copy", "reply-cap-over-copy-delete", "reply-delete",
            "reply-queued-fault", "reply-recv", "reply-to-badged-call", "reschedule-sgi",
            "resume-carved-tcb", "resume-shared-tcb", "root-ipc-buffer-back", "root-set-ipc-buffer",
            "sched-context-bind", "sched-context-configure", "sched-context-consumed",
            "sched-context-consumed-reset", "sched-context-rebind", "sched-context-unbind",
            "sched-context-unbind-suspended", "sched-context-unbind-waiting",
            "sched-context-yield-to", "sched-context-yield-to-linked",
            "sched-context-yield-to-requeue", "send-blocks", "send-tainted-blocks",
            "send-to-receiver", "send-to-unstashed-receiver", "service-query",
            "service-register", "service-revoke", "set-carved-tcb-space", "signal",
            "signal-bound",
            "signal-to-waiter", "signal-wide-badge", "space-cnode-cap-delete",
            "spaced-tcb-delete", "stack-bind-partner", "stack-configure",
            "stack-context-bind-partner", "stack-context-configure", "stack-partner-calls",
            "stack-resume-server", "stack-root-calls", "stack-root-receives",
            "stack-server-calls", "stack-server-delete", "stack-server-receives",
            "stack-server-reply-cap-mint", "stack-server-resumes-top",
            "stack-server-set-priority", "stack-server-set-space", "stack-suspend-partner",
            "stack-suspend-server", "stack-suspend-top", "stack-top-delete",
            "stack-top-receives", "stack-top-reply-cap-mint", "stack-top-resumes-partner",
            "stack-top-resumes-root", "stack-top-set-priority", "stack-top-set-space",
            "stack-top-waits", "stack-unbind", "stashed-reply-cap-delete",
            "stashed-reply-delete", "suspend-donated-bind-partner",
            "suspend-donated-configure", "suspend-donated-partner-calls",
            "suspend-donated-resume", "suspend-donated-root-receives",
            "suspend-donated-unbind", "suspend-queued-tcb", "suspend-recv-partner-receives",
            "suspend-recv-resume", "suspend-recv-root-receives", "suspend-recv-wake-root",
            "suspend-reply-partner-calls", "suspend-reply-resume",
            "suspend-reply-root-receives", "suspend-send-partner-sends", "suspend-send-resume",
            "suspend-send-root-receives", "suspend-send-wake-root",
            "suspend-wait-partner-waits", "suspend-wait-resume", "suspend-wait-root-receives",
            "suspend-wait-wake-root", "suspended-tcb-delete", "tcb-bind-notification",
            "tcb-resume", "tcb-resume-bound", "tcb-resume-postpone", "tcb-set-affinity",
            "tcb-set-affinity-running", "tcb-set-fault-handler", "tcb-set-ipc-buffer",
            "tcb-set-mc-priority", "tcb-set-priority", "tcb-set-space", "tcb-suspend",
            "tcb-suspend-bound", "tcb-suspend-receive-blocked", "tcb-suspend-release-queued",
            "tcb-suspend-reply-blocked", "tcb-suspend-reply-donated",
            "tcb-suspend-send-blocked", "tcb-suspend-wait-blocked", "tcb-suspend-waiting",
            "tcb-unbind-notification", "third-bind-partner", "third-configure",
            "third-reply-cap-mint", "third-resume-server", "third-root-waits",
            "third-tcb-set-priority", "third-tcb-set-space", "third-unbind", "timer-tick",
            "unbound-tcb-delete", "unknown-syscall-delivered",
            "unknown-syscall-delivered-to-reply", "unknown-syscall-plain-reply", "unknown-syscall-reply",
            "unknown-syscall-resume", "unknown-syscall-suspends", "untyped-reset",
            "untyped-retype-bound-notification", "untyped-retype-bound-tcb",
            "untyped-retype-busy-endpoint", "untyped-retype-busy-notification",
            "untyped-retype-busy-reply", "untyped-retype-chain-reply",
            "untyped-retype-chain-tcb", "untyped-retype-cnode", "untyped-retype-endpoint",
            "untyped-retype-frame", "untyped-retype-heap-refused", "untyped-retype-into-cnode",
            "untyped-retype-notification", "untyped-retype-orphan-recv-reply",
            "untyped-retype-orphan-recv-server", "untyped-retype-orphan-server-reply",
            "untyped-retype-orphan-top", "untyped-retype-orphan-top-reply",
            "untyped-retype-page-table-1", "untyped-retype-page-table-2",
            "untyped-retype-page-table-3", "untyped-retype-populated-cnode",
            "untyped-retype-queue-endpoint", "untyped-retype-queued-tcb",
            "untyped-retype-region-exhausted",
            "untyped-retype-reply", "untyped-retype-sc-thread", "untyped-retype-sched-context",
            "untyped-retype-shared-tcb", "untyped-retype-slot-occupied",
            "untyped-retype-space-cnode",
            "untyped-retype-spaced-tcb", "untyped-retype-stack-context",
            "untyped-retype-stack-server", "untyped-retype-stack-server-reply",
            "untyped-retype-stack-top", "untyped-retype-stack-top-reply",
            "untyped-retype-stashed-reply", "untyped-retype-tcb", "untyped-retype-third-reply",
            "untyped-retype-third-tcb", "untyped-retype-untyped",
            "untyped-retype-vspace-root", "untyped-retype-waited-reply",
            "upper-notification-delete", "user-exception-delivered",
            "user-exception-delivered-to-reply", "user-exception-plain-reply", "user-exception-reply",
            "user-exception-resume", "user-exception-suspends", "vm-fault-data-delivered",
            "vm-fault-data-delivered-to-reply", "vm-fault-data-plain-reply",
            "vm-fault-data-reply", "vm-fault-data-resume", "vm-fault-data-suspends",
            "vm-fault-instruction-delivered", "vm-fault-instruction-delivered-to-reply",
            "vm-fault-instruction-plain-reply", "vm-fault-instruction-reply",
            "vm-fault-instruction-resume", "vm-fault-instruction-suspends", "vm-fault-queued",
            "vspace-map", "vspace-map-again", "vspace-map-copy", "vspace-map-moved",
            "vspace-unify-instruction", "vspace-unmap", "vspace-unmap-first",
            "vspace-root-delete", "vspace-unmap-moved", "wait-blocks", "wait-on-carved", "wait-pending",
            "waited-partner-calls", "waited-reply-cap-mint", "waited-root-waits",
            "waited-server-delete", "waited-server-receives", "waited-server-resumes-partner",
            "waited-server-waits", "waited-server-wakes-root", "waited-wake-server", "yield",
            # The long, short-argument and refused forms the register file
            # routes past the named syscalls.
            "bad-message-info", "high-message-info", "invocation-long-message",
            "sched-context-configure-long", "service-register-short", "signal-long-message",
            "wait-long-message", "yield-long-message",
            # The IPC buffer the validator refuses for crossing its page, and the
            # full-length forms with the buffer in its frame's last 1024 bytes.
            "half-aligned-ipc-buffer",
            "tail-partner-ipc-buffer", "tail-partner-ipc-buffer-back",
            "tail-root-ipc-buffer", "tail-root-ipc-buffer-back",
            "tail-send-bind-partner", "tail-send-configure",
            "tail-send-partner-yield", "tail-send-resume-partner",
            "tail-send-root-receives", "tail-send-suspend", "tail-send-to-receiver",
            "tail-send-unbind", "signal-tail-buffer", "wait-tail-buffer",
            "tail-call-resume", "tail-call-root-receives", "tail-call-to-receiver",
            "tail-call-suspend", "tail-call-resume-again", "tail-call-blocks",
            "tail-call-partner-takes", "tail-call-partner-replies", "tail-call-partner-yield",
            "tail-call-suspend-again", "tail-send-blocks-resume", "tail-send-blocks",
            "short-call-take-resume", "short-call-blocks", "short-call-partner-takes",
            "short-call-partner-replies", "short-call-partner-yield", "short-call-take-suspend",
            "tail-send-partner-takes", "tail-send-blocks-partner-yield",
            "tail-send-blocks-suspend", "tail-reply-recv-resume",
            "tail-reply-recv-call", "tail-reply-recv-takes", "tail-reply-recv-blocks",
            "tail-reply-recv-suspend",
            # Capability-carrying sends and calls that block.
            "caps-send-blocks-resume", "caps-send-blocks", "caps-send-blocks-suspend-root",
            "caps-send-blocks-resume-root", "caps-send-blocks-suspend",
            "caps-long-send-blocks-resume", "caps-long-send-blocks",
            "caps-long-send-blocks-suspend-root", "caps-long-send-blocks-resume-root",
            "caps-long-send-blocks-suspend", "caps-call-blocks-resume", "caps-call-blocks",
            "caps-call-blocks-suspend-root", "caps-call-blocks-resume-root",
            "caps-call-blocks-suspend", "caps-long-call-blocks-resume",
            "caps-long-call-blocks", "caps-long-call-blocks-suspend-root",
            "caps-long-call-blocks-resume-root", "caps-long-call-blocks-suspend",
            # Capability-carrying rendezvous into a closed receive window.
            "caps-send-rendezvous-resume", "caps-send-rendezvous-root-receives",
            "caps-send-rendezvous-to-receiver", "caps-send-rendezvous-yield",
            "caps-send-rendezvous-suspend", "caps-three-send-rendezvous-resume",
            "caps-three-send-rendezvous-root-receives",
            "caps-three-send-rendezvous-to-receiver", "caps-three-send-rendezvous-yield",
            "caps-three-send-rendezvous-suspend", "caps-call-rendezvous-resume",
            "caps-call-rendezvous-root-receives", "caps-call-rendezvous-to-receiver",
            "caps-call-rendezvous-suspend", "caps-three-call-rendezvous-resume",
            "caps-three-call-rendezvous-root-receives",
            "caps-three-call-rendezvous-to-receiver", "caps-three-call-rendezvous-suspend",
            "caps-install-send-resume", "caps-install-send-root-receives",
            "caps-install-send-to-receiver", "caps-install-send-yield",
            "caps-install-send-suspend", "caps-install-send-delete", "caps-unwrap-send-resume",
            "caps-unwrap-send-root-receives", "caps-unwrap-send-to-receiver",
            "caps-unwrap-send-yield", "caps-unwrap-send-suspend",
            "caps-three-install-send-resume", "caps-three-install-send-root-receives",
            "caps-three-install-send-to-receiver", "caps-three-install-send-yield",
            "caps-three-install-send-suspend", "caps-three-install-send-delete",
            "caps-occupied-slot-send-resume", "caps-occupied-slot-send-root-receives",
            "caps-occupied-slot-send-to-receiver", "caps-occupied-slot-send-yield",
            "caps-occupied-slot-send-suspend", "caps-invalid-path-send-resume",
            "caps-invalid-path-send-root-receives", "caps-invalid-path-send-to-receiver",
            "caps-invalid-path-send-yield", "caps-invalid-path-send-suspend",
            "caps-no-grant-send-mint", "caps-no-grant-send-resume",
            "caps-no-grant-send-root-receives", "caps-no-grant-send-to-receiver",
            "caps-no-grant-send-yield", "caps-no-grant-send-suspend",
            "caps-no-grant-send-delete",
            "caps-install-call-resume", "caps-install-call-root-receives",
            "caps-install-call-to-receiver", "caps-install-call-suspend",
            "caps-install-call-delete", "caps-unwrap-call-resume",
            "caps-unwrap-call-root-receives", "caps-unwrap-call-to-receiver",
            "caps-unwrap-call-suspend", "caps-occupied-slot-call-resume",
            "caps-occupied-slot-call-root-receives", "caps-occupied-slot-call-to-receiver",
            "caps-occupied-slot-call-suspend", "caps-install-take-resume",
            "caps-install-take-send-blocks", "caps-install-take-partner-takes",
            "caps-install-take-partner-yield", "caps-install-take-suspend",
            "caps-install-take-delete", "caps-unwrap-take-resume",
            "caps-unwrap-take-send-blocks", "caps-unwrap-take-partner-takes",
            "caps-unwrap-take-partner-yield", "caps-unwrap-take-suspend",
            "caps-install-call-take-resume", "caps-install-call-take-blocks",
            "caps-install-call-take-partner-takes",
            "caps-install-call-take-partner-replies",
            "caps-install-call-take-partner-yield",
            "caps-install-call-take-suspend", "caps-install-call-take-delete",
            "caps-unwrap-call-take-resume", "caps-unwrap-call-take-blocks",
            "caps-unwrap-call-take-partner-takes",
            "caps-unwrap-call-take-partner-replies",
            "caps-unwrap-call-take-partner-yield",
            "caps-unwrap-call-take-suspend",
            "caps-take-resume", "caps-take-send-blocks", "caps-take-partner-takes",
            "caps-take-partner-yield", "caps-take-suspend",
            # Granting replies to a caller whose buffer names an empty receive slot.
            "grant-reply-resume", "grant-reply-root-receives", "grant-reply-partner-calls",
            "grant-reply-recv", "grant-reply-partner-calls-again", "grant-reply",
            "grant-reply-cap-root-receives", "grant-reply-cap-partner-calls",
            "grant-reply-installs-cap",
            "grant-reply-installed-signal", "grant-reply-installed-wait",
            "grant-reply-installed-delete", "grant-reply-suspend",
            # The install and unwrap forms at the longest message.
            "caps-long-install-send-resume", "caps-long-install-send-root-receives",
            "caps-long-install-send-to-receiver", "caps-long-install-send-yield",
            "caps-long-install-send-suspend", "caps-long-install-send-delete",
            "caps-long-unwrap-send-resume", "caps-long-unwrap-send-root-receives",
            "caps-long-unwrap-send-to-receiver", "caps-long-unwrap-send-yield",
            "caps-long-unwrap-send-suspend", "caps-long-install-call-resume",
            "caps-long-install-call-root-receives", "caps-long-install-call-to-receiver",
            "caps-long-install-call-suspend", "caps-long-install-call-delete",
            "caps-long-unwrap-call-resume", "caps-long-unwrap-call-root-receives",
            "caps-long-unwrap-call-to-receiver", "caps-long-unwrap-call-suspend",
            "caps-long-install-take-resume", "caps-long-install-take-send-blocks",
            "caps-long-install-take-partner-takes", "caps-long-install-take-partner-yield",
            "caps-long-install-take-suspend", "caps-long-install-take-delete",
            "caps-long-unwrap-take-resume", "caps-long-unwrap-take-send-blocks",
            "caps-long-unwrap-take-partner-takes", "caps-long-unwrap-take-partner-yield",
            "caps-long-unwrap-take-suspend", "caps-long-install-call-take-resume",
            "caps-long-install-call-take-blocks", "caps-long-install-call-take-partner-takes",
            "caps-long-install-call-take-partner-replies",
            "caps-long-install-call-take-partner-yield", "caps-long-install-call-take-suspend",
            "caps-long-install-call-take-delete", "caps-long-unwrap-call-take-resume",
            "caps-long-unwrap-call-take-blocks", "caps-long-unwrap-call-take-partner-takes",
            "caps-long-unwrap-call-take-partner-replies",
            "caps-long-unwrap-call-take-partner-yield", "caps-long-unwrap-call-take-suspend",
            # Installing replies at the longest message, on a donated reply object
            # and to a caller recording no server.
            "grant-long-reply-root-receives", "grant-long-reply-partner-calls",
            "grant-long-reply-installs-cap", "grant-long-reply-installed-signal",
            "grant-long-reply-installed-wait", "grant-long-reply-installed-delete",
            "donated-reply-caps-configure", "donated-reply-caps-bind-partner",
            "donated-reply-caps-resume", "donated-reply-caps-root-receives",
            "donated-reply-caps-partner-calls", "donated-reply-installs-cap",
            "donated-reply-installed-signal", "donated-reply-installed-wait",
            "donated-reply-installed-delete", "donated-reply-caps-suspend-root",
            "donated-reply-caps-resume-root", "donated-reply-caps-suspend",
            "donated-reply-caps-unbind", "untyped-retype-unheld-caps-server",
            "unheld-caps-server-set-space", "unheld-caps-server-set-priority",
            "untyped-retype-unheld-caps-reply", "unheld-caps-reply-cap-mint",
            "unheld-caps-resume-server", "unheld-caps-root-waits",
            "unheld-caps-server-resumes-partner", "unheld-caps-server-receives",
            "unheld-caps-partner-calls", "unheld-caps-server-wakes-root",
            "unheld-caps-server-waits", "unheld-caps-server-delete",
            "unheld-reply-installs-cap", "unheld-reply-installed-signal",
            "unheld-reply-installed-wait", "unheld-reply-installed-delete",
            "unheld-caps-suspend-partner", "unheld-caps-reply-cap-delete",
            "unheld-caps-reply-delete",
            # Granting reply-receives whose reply leg installs: blocking, at the
            # longest message, on a donated reply object and to a caller
            # recording no server.
            "grant-reply-recv-cap-root-receives", "grant-reply-recv-cap-partner-calls",
            "grant-reply-recv-cap-installs-cap", "grant-reply-recv-cap-installed-signal",
            "grant-reply-recv-cap-installed-wait", "grant-reply-recv-cap-installed-delete",
            "grant-reply-recv-cap-partner-calls-again", "grant-reply-recv-cap-root-replies",
            "grant-long-reply-recv-cap-root-receives",
            "grant-long-reply-recv-cap-partner-calls", "grant-long-reply-recv-cap-installs-cap",
            "grant-long-reply-recv-cap-installed-signal",
            "grant-long-reply-recv-cap-installed-wait",
            "grant-long-reply-recv-cap-installed-delete",
            "grant-long-reply-recv-cap-partner-calls-again",
            "grant-long-reply-recv-cap-root-replies", "chain-caps-server-ipc-buffer",
            "chain-caps-root-calls-server", "chain-server-reply-recv-installs-cap",
            "chain-reply-recv-installed-signal", "chain-reply-recv-installed-wait",
            "chain-reply-recv-installed-delete", "untyped-retype-unheld-recv-caps-server",
            "unheld-recv-caps-server-set-space", "unheld-recv-caps-server-set-priority",
            "untyped-retype-unheld-recv-caps-reply", "unheld-recv-caps-reply-cap-mint",
            "unheld-recv-caps-resume-server", "unheld-recv-caps-root-waits",
            "unheld-recv-caps-server-resumes-partner", "unheld-recv-caps-server-receives",
            "unheld-recv-caps-partner-calls", "unheld-recv-caps-server-wakes-root",
            "unheld-recv-caps-server-waits", "unheld-recv-caps-server-delete",
            "unheld-reply-recv-installs-cap", "unheld-reply-recv-installed-signal",
            "unheld-reply-recv-installed-wait", "unheld-reply-recv-installed-delete",
            "unheld-recv-caps-partner-wakes-root", "unheld-recv-caps-partner-waits",
            "unheld-recv-caps-suspend-partner", "unheld-recv-caps-reply-cap-delete",
            "unheld-recv-caps-reply-delete",
            # A reply-receive whose receive leg meets a queued sender, the long
            # donated and unheld reply-receives, and a capability fault answered
            # by a long reply and a long reply-receive.
            "cap-fault-delivered-to-long-reply", "cap-fault-delivered-to-long-reply-recv",
            "cap-fault-long-reply", "cap-fault-long-reply-recv",
            "chain-long-caps-root-calls-server", "chain-long-reply-recv-installed-delete",
            "chain-long-reply-recv-installed-signal", "chain-long-reply-recv-installed-wait",
            "chain-long-root-calls-server", "chain-server-long-reply-recv",
            "chain-server-long-reply-recv-installs-cap", "queued-sender-caps-installed-delete",
            "queued-sender-caps-installed-signal", "queued-sender-caps-installed-wait",
            "queued-sender-caps-partner-calls", "queued-sender-caps-reply-recv-installs-cap",
            "queued-sender-caps-resume-partner", "queued-sender-caps-resume-sender",
            "queued-sender-caps-root-receives", "queued-sender-caps-root-waits",
            "queued-sender-caps-sender-sends", "queued-sender-caps-sender-wakes-root",
            "queued-sender-caps-suspend-partner", "queued-sender-caps-suspend-sender",
            "queued-sender-delete", "queued-sender-partner-calls", "queued-sender-reply-recv",
            "queued-sender-resume-partner", "queued-sender-resume-sender",
            "queued-sender-root-receives", "queued-sender-root-waits",
            "queued-sender-sender-sends", "queued-sender-sender-wakes-root",
            "queued-sender-set-priority", "queued-sender-set-space",
            "queued-sender-suspend-partner", "queued-sender-suspend-sender",
            "unheld-long-recv-caps-installed-delete", "unheld-long-recv-caps-installed-signal",
            "unheld-long-recv-caps-installed-wait", "unheld-long-recv-caps-partner-calls",
            "unheld-long-recv-caps-partner-waits", "unheld-long-recv-caps-partner-wakes-root",
            "unheld-long-recv-caps-reply-cap-delete", "unheld-long-recv-caps-reply-cap-mint",
            "unheld-long-recv-caps-reply-delete", "unheld-long-recv-caps-resume-server",
            "unheld-long-recv-caps-root-waits", "unheld-long-recv-caps-server-delete",
            "unheld-long-recv-caps-server-receives",
            "unheld-long-recv-caps-server-resumes-partner",
            "unheld-long-recv-caps-server-set-priority",
            "unheld-long-recv-caps-server-set-space", "unheld-long-recv-caps-server-waits",
            "unheld-long-recv-caps-server-wakes-root", "unheld-long-recv-caps-suspend-partner",
            "unheld-long-recv-partner-calls", "unheld-long-recv-partner-waits",
            "unheld-long-recv-partner-wakes-root", "unheld-long-recv-reply-cap-delete",
            "unheld-long-recv-reply-cap-mint", "unheld-long-recv-reply-delete",
            "unheld-long-recv-resume-server", "unheld-long-recv-root-waits",
            "unheld-long-recv-server-delete", "unheld-long-recv-server-receives",
            "unheld-long-recv-server-resumes-partner", "unheld-long-recv-server-set-priority",
            "unheld-long-recv-server-set-space", "unheld-long-recv-server-waits",
            "unheld-long-recv-server-wakes-root", "unheld-long-recv-suspend-partner",
            "unheld-long-reply-recv", "unheld-long-reply-recv-installs-cap",
            "untyped-retype-queued-sender", "untyped-retype-unheld-long-recv-caps-reply",
            "untyped-retype-unheld-long-recv-caps-server",
            "untyped-retype-unheld-long-recv-reply", "untyped-retype-unheld-long-recv-server",
            # The lifecycle branches: final deletes of untypeds with live
            # children, moved parents, bound and running threads, threads'
            # space slots, installed tables, mapped frames, tabled VSpace
            # roots, registered endpoints, endpoints with blocked senders and
            # callers, and notifications whose last capability is a handler's;
            # the refusals and the empty unmaps beside them.
            "untyped-retype-parent-untyped", "child-retype-endpoint",
            "child-untyped-reset-refused", "child-untyped-revoke",
            "child-retype-notification", "childless-revoke", "parent-untyped-delete",
            "adopted-notification-delete", "untyped-retype-moved-parent",
            "moved-parent-copy", "parent-cap-move", "moved-parent-child-delete",
            "moved-parent-delete", "untyped-retype-bound-context",
            "untyped-retype-context-thread", "bind-context-thread",
            "context-bound-tcb-delete", "released-context-delete",
            "untyped-retype-space-tcb", "untyped-retype-space-root",
            "space-root-set-space", "space-root-cap-delete", "space-root-replaced",
            "untyped-retype-replaced-cnode", "replaced-cnode-set-space",
            "replaced-cnode-cap-delete", "replaced-cnode-retired",
            "untyped-retype-zombie-cnode", "untyped-retype-zombie-endpoint",
            "zombie-cnode-set-space", "zombie-cnode-cap-delete",
            "zombie-cnode-replaced", "untyped-retype-nested-cnode",
            "untyped-retype-nested-endpoint", "nested-cnode-set-space",
            "nested-cnode-cap-delete", "nested-space-tcb-delete",
            "untyped-retype-rooted-tcb", "untyped-retype-thread-root",
            "thread-root-set-space", "thread-root-cap-delete", "rooted-tcb-delete",
            "untyped-retype-installed-table-1", "installed-table-map-1",
            "untyped-retype-installed-table-2", "installed-table-map-2",
            "untyped-retype-installed-table-3", "installed-table-map-3",
            "installed-table-unmap-refused", "untyped-retype-mapped-frame",
            "mapped-frame-map", "mapped-frame-remap", "mapped-frame-remap-other-vaddr",
            "mapped-frame-unify", "mapped-frame-unmap-code", "mapped-frame-map-again",
            "unmap-nothing",
            "mapped-frame-delete", "installed-table-delete-1", "stale-table-unmap-2",
            "stale-table-delete-2", "stale-table-delete-3",
            "untyped-retype-uninstalled-table", "uninstalled-table-unmap",
            "uninstalled-table-delete", "untyped-retype-tabled-root",
            "untyped-retype-tabled-root-table-1", "tabled-root-table-map-1",
            "untyped-retype-tabled-root-table-2", "tabled-root-table-map-2",
            "untyped-retype-tabled-root-table-3", "tabled-root-table-map-3",
            "untyped-retype-tabled-root-frame", "tabled-root-map",
            "tabled-root-frame-other-asid", "tabled-root-delete",
            "orphaned-table-unmap-3", "orphaned-table-delete-3",
            "orphaned-table-delete-2", "orphaned-table-delete-1",
            "orphaned-frame-delete", "lifecycle-untyped-reset",
            "untyped-retype-send-endpoint", "send-on-carved", "sender-endpoint-delete",
            "untyped-retype-call-endpoint", "call-on-carved", "caller-endpoint-delete",
            "untyped-retype-registered-endpoint", "registered-endpoint-register",
            "registered-endpoint-delete", "untyped-retype-irq-notification",
            "irq-handler-set-carved-notification", "irq-notification-cap-delete",
            "irq-handler-set-notification-over-last",
            "untyped-retype-irq-cleared-notification",
            "irq-handler-set-notification-over-copy",
            "irq-cleared-notification-cap-delete", "irq-handler-clear-last",
            "self-tcb-delete", "remote-running-tcb-delete",
            # The call queued with no receiver and the receive and the
            # reply-receive that take it, the priority of a ready thread and of
            # the caller itself set, the one-page long send that blocks.
            "untyped-retype-queued-caller", "queued-caller-set-space",
            "queued-caller-set-priority", "queued-caller-bind",
            "queued-caller-resume-caller", "queued-caller-root-waits",
            "queued-caller-caller-wakes-root", "queued-caller-calls",
            "queued-caller-root-receives", "queued-caller-root-replies",
            "queued-caller-suspend-root", "queued-caller-resume-root",
            "queued-caller-suspend-caller", "queued-caller-resume-partner",
            "queued-caller-root-takes-partner", "queued-caller-partner-calls",
            "queued-caller-resume-caller-again", "queued-caller-lower-ready",
            "queued-caller-raise-ready", "queued-caller-root-lowers-self",
            "queued-caller-calls-again", "queued-caller-root-raises-self",
            "queued-caller-resume-lowered", "queued-caller-caller-waits",
            "queued-caller-root-wakes-caller", "queued-caller-suspend-lowered",
            "queued-caller-root-waits-again", "queued-caller-caller-wakes-root-again",
            "queued-caller-reply-recv", "queued-caller-root-replies-again",
            "queued-caller-suspend-caller-again", "queued-caller-suspend-partner",
            "queued-caller-suspend-root-again", "queued-caller-resume-root-again",
            "queued-caller-unbind", "queued-caller-delete",
            "long-send-blocks-resume", "long-send-blocks", "long-send-partner-takes",
            "long-send-blocks-partner-yield", "long-send-blocks-suspend",
            "yield-to-lower-partner", "yield-to-resume-partner", "yield-to-raise-partner",
            # Every fault kind queued on a handler with no receiver, and the
            # refusals the entry turns into capability faults on either side
            # of the IPC buffer's TLB fill.
            "vm-fault-instruction-queued", "cap-fault-queued", "unknown-syscall-queued",
            "user-exception-queued", "receive-queued-instruction-fault",
            "receive-queued-cap-fault", "receive-queued-unknown-syscall",
            "receive-queued-user-exception", "reply-queued-instruction-fault",
            "reply-queued-cap-fault", "reply-queued-unknown-syscall",
            "reply-queued-user-exception",
            "configure-refused-fills", "configure-cap-fault-fills",
            "receive-configure-cap-fault", "reply-configure-cap-fault",
            "configure-fills-ipc-buffer", "configure-cap-fault-held",
            "receive-configure-cap-fault-held", "reply-configure-cap-fault-held",
            "configure-refused-held", "configure-zero-budget-max-period",
            "configure-budget-over-wide-period", "configure-wide-budget-and-period",
            "configure-wide-deadline", "configure-held-ipc-buffer",
            "service-register-cap-fault", "receive-service-register-cap-fault",
            "reply-service-register-cap-fault", "long-send-cap-fault",
            "receive-long-send-cap-fault", "reply-long-send-cap-fault",
            # The buffer's page unmapped: the messages past the inline words
            # clamped to them, as seL4's handleInvocation clamps a message with
            # no IPC buffer, and a long receive reading no overflow word.
            "configure-one-word-unmapped-buffer", "configure-long-unmapped-buffer",
            "long-send-unmapped-buffer-cap-fault",
            "receive-long-send-unmapped-buffer-cap-fault",
            "reply-long-send-unmapped-buffer-cap-fault",
            "long-call-unmapped-buffer-cap-fault",
            "receive-long-call-unmapped-buffer-cap-fault",
            "reply-long-call-unmapped-buffer-cap-fault",
            "long-receive-unmapped-buffer-cap-fault",
            "receive-long-receive-unmapped-buffer-cap-fault",
            "reply-long-receive-unmapped-buffer-cap-fault",
            # The receive phase's capability faults (seL4's `handleRecv`): a
            # capability of the wrong type, or without the right to receive,
            # faults as a failed lookup does.
            "overflowed-receive-cap-fault", "receive-overflowed-receive-cap-fault",
            "reply-overflowed-receive-cap-fault",
            "receive-wrong-type-cap-fault", "receive-receive-wrong-type-cap-fault",
            "reply-receive-wrong-type-cap-fault",
            "wait-wrong-type-cap-fault", "receive-wait-wrong-type-cap-fault",
            "reply-wait-wrong-type-cap-fault",
            "reply-recv-wrong-type-cap-fault", "receive-reply-recv-wrong-type-cap-fault",
            "reply-reply-recv-wrong-type-cap-fault",
            "receive-no-right-mint", "receive-no-right-cap-fault",
            "receive-receive-no-right-cap-fault", "reply-receive-no-right-cap-fault",
            "receive-no-right-delete",
            # The unbound line's handler issued and acknowledged, the
            # notification bound again after the revoke.
            "irq-control-get-unbound", "irq-unbound-ack", "irq-handler-set-notification-again",
            # A remote core's work: a shootdown with a remote target, a
            # syscall on a core another core vacated and the reschedule that
            # ends it, a thread homed back while another core still holds it
            # (deferred, an FP/SIMD access there loads nothing), and the
            # reschedule and access once that core has released it.
            "remote-asid-map", "remote-asid-unmap", "vacated-core-syscall",
            "vacated-core-reschedule", "fp-deferred-home-back", "fp-deferred-root-receives",
            "fp-access-deferred", "fp-released-reschedule", "fp-access-released",
            # Every syscall with a message past its inline words, refused: only
            # an IPC transfer and a five-word invocation read the overflow words.
            "overflowed-cspace-mint", "overflowed-cspace-copy",
            "overflowed-cspace-move", "overflowed-cspace-delete", "overflowed-cspace-revoke",
            "overflowed-vspace-map", "overflowed-vspace-unmap",
            "overflowed-vspace-unify-instruction", "overflowed-service-revoke",
            "overflowed-service-query", "overflowed-sched-context-bind",
            "overflowed-sched-context-unbind", "overflowed-sched-context-consumed",
            "overflowed-sched-context-yield-to", "overflowed-tcb-suspend", "overflowed-tcb-resume",
            "overflowed-tcb-set-priority", "overflowed-tcb-set-ipc-buffer",
            "overflowed-tcb-set-affinity", "overflowed-tcb-bind-notification",
            "overflowed-tcb-unbind-notification", "overflowed-tcb-set-fault-handler",
            "overflowed-tcb-set-space", "overflowed-mint-reply-cap", "overflowed-irq-handler-ack",
            "overflowed-irq-control-get", "overflowed-irq-handler-set-notification",
            "overflowed-irq-handler-clear", "overflowed-page-table-map",
            "overflowed-page-table-unmap", "overflowed-audit-read", "overflowed-audit-drain",
            "overflowed-service-register", "overflowed-untyped-reset", "overflowed-declassify",
            "long-declassify-signal", "overflowed-untyped-retype",
            # Every invocation with a truncation minimum, one word short of
            # its arguments: refused TruncatedMessage before any argument read.
            "cspace-mint-short", "cspace-copy-short", "cspace-move-short",
            "cspace-delete-short", "cspace-revoke-short", "mint-reply-cap-short",
            "untyped-retype-short", "vspace-map-short", "vspace-unmap-short",
            "vspace-unify-instruction-short", "page-table-map-short",
            "sched-context-configure-short", "sched-context-bind-short",
            "tcb-bind-notification-short", "tcb-set-priority-short",
            "tcb-set-mc-priority-short", "tcb-set-ipc-buffer-short",
            "tcb-set-affinity-short", "tcb-set-fault-handler-short", "tcb-set-space-short",
            "irq-control-get-short", "irq-handler-set-notification-short",
            "audit-drain-short", "audit-read-short",
            # WS-UC UC4: a capability copied into a carved CNode and out of
            # it, the CNode retired while the copy lives on.
            "untyped-retype-owned-cnode", "owned-cnode-fill", "owned-cnode-copy-out",
            "owned-cnode-slot-delete", "owned-cnode-delete", "owned-cnode-escaped-move",
            "owned-cnode-escaped-delete", "owned-cnode-untyped-reset",
        }
        observed = set(names) | {m.group(1) for m in returned}
        if observed != expected:
            failures.append(f"heap-allocations-per-syscall: scenarios {sorted(observed ^ expected)} differ from the pinned set")
        runs = [(m.group(1), m.group(2) is not None) for m in readings]
        trips = [(m.group(1), m.group(2) is not None) for m in returned]
        carved = {}
        for m in carves:
            key = (m.group(1), m.group(2) is not None)
            if key in carved:
                failures.append(f"heap-allocations-per-syscall: {m.group(1)}: named two carves in one run")
            carved[key] = m.group(3)
        for name in sorted(observed | expected):
            for first in (True, False):
                which = "first call" if first else "steady state"
                if runs.count((name, first)) != 1 or trips.count((name, first)) != 1:
                    failures.append(f"heap-allocations-per-syscall: {name} ({which}): expected one reading and one returned or blocked round trip on core 0")
        for key in carved:
            if key not in trips:
                failures.append(f"heap-allocations-per-syscall: {key[0]}: a carve named with no returned round trip")
        # Every arm the kernel's router routes a syscall to has a measured
        # round trip.  The arms are derived by the router itself
        # (`scripts/exerciser_route_coverage.lean`, run by Lean, which routes
        # every syscall number and message-info shape the ABI decodes); the
        # evidence is each pinned scenario's routed words and answer, as the
        # exerciser printed them beside its reading, routed by the same
        # router.  A tool that cannot run, or answers nonzero, fails the gate.
        routed_re = re.compile(r"\[smp-test\] heap-allocations-per-syscall: ([a-z0-9-]+): core 0( \(first call\))?: routed x7=(0x[0-9a-f]+) x1=(0x[0-9a-f]+) answered (0x[0-9a-f]+|blocked)")
        # A round trip is evidence for its arm only if its reading's window
        # entered the kernel through the syscall entry: a trip the HAL refused
        # before the kernel ran measured no arm.
        svc_entry_re = re.compile(r"\[smp-test\] heap-allocations-per-syscall: ([a-z0-9-]+): core 0( \(first call\))?: entered (\S+)")
        svc_entered = set()
        for line in lines:
            m = svc_entry_re.fullmatch(line)
            if m and "src/svc_dispatch.rs:" in m.group(3):
                svc_entered.add((m.group(1), m.group(2) is not None))
        evidence = []
        for line in lines:
            m = routed_re.fullmatch(line)
            key = (m.group(1), m.group(2) is not None) if m else None
            if m and m.group(1) in expected and key in runs and key in svc_entered:
                evidence.append(f"{m.group(1)}{'/first' if m.group(2) else ''} {m.group(3)} {m.group(4)} {m.group(5)}")
        try:
            coverage = subprocess.run(
                ["lake", "env", "lean", "--run", "scripts/exerciser_route_coverage.lean"],
                cwd=os.environ["EXERCISER_REPO_ROOT"], input="\n".join(evidence) + "\n",
                capture_output=True, text=True, timeout=600)
        except (OSError, KeyError, subprocess.SubprocessError) as error:
            failures.append(f"heap-allocations-per-syscall: the route coverage could not run: {error}")
        else:
            reported = [l[len("FAIL: "):] for l in coverage.stderr.split("\n") if l.startswith("FAIL: ")]
            for finding in reported:
                failures.append(f"heap-allocations-per-syscall: route coverage: {finding}")
            if coverage.returncode != 0 and not reported:
                failures.append(f"heap-allocations-per-syscall: the route coverage answered {coverage.returncode}: {coverage.stderr.strip()!r}")
            if coverage.returncode == 0 and reported:
                failures.append("heap-allocations-per-syscall: the route coverage reported findings and answered 0")
        # Every kernel-entry site has a measured reading that entered it.  The
        # sites are the HAL's own `crate::kernel_entry::with_kernel_entry(`
        # calls, derived from the code by its `build.rs` and printed by the
        # image; each reading names the sites its window entered, tallied by
        # the bracket's caller.  The exerciser's own brackets (its file) are
        # not kernel entries a thread or device takes, the one exclusion.  An
        # entry the table does not name, or a window the image could not
        # attribute, fails the gate.
        site_re = re.compile(r"\[smp-test\] heap-allocations-per-syscall: kernel-entry site (src/[a-z0-9_/]+\.rs:\d+)")
        entered_re = re.compile(r"\[smp-test\] heap-allocations-per-syscall: ([a-z0-9-]+): core \d+( \(first call\))?: entered (\S+)")
        sites = [m.group(1) for m in (site_re.fullmatch(line) for line in lines) if m]
        if not sites:
            failures.append("heap-allocations-per-syscall: the image printed no kernel-entry site")
        if len(set(sites)) != len(sites):
            failures.append(f"heap-allocations-per-syscall: the kernel-entry sites repeat: {sites}")
        entered_sites = set()
        windows = {"secondary-ticks", "secondary-reschedule", "secondary-entry"}
        for line in lines:
            m = entered_re.fullmatch(line)
            if m is None:
                continue
            if m.group(1) not in expected and m.group(1) not in windows:
                failures.append(f"heap-allocations-per-syscall: entered sites named for {m.group(1)}, not a pinned reading: {line!r}")
                continue
            if m.group(3) == "none":
                continue
            for site in m.group(3).split(","):
                if site not in sites:
                    failures.append(f"heap-allocations-per-syscall: {m.group(1)} entered {site}, which is not a kernel-entry site: {line!r}")
                else:
                    entered_sites.add(site)
        for site in sites:
            if not site.startswith("src/smp_exercisers.rs:") and site not in entered_sites:
                failures.append(f"heap-allocations-per-syscall: the kernel-entry site {site} has no measured reading that entered it")
        for m in readings:
            before, after, delta = (int(g) for g in m.groups()[2:5])
            kind = carved.get((m.group(1), m.group(2) is not None))
            if kind is not None and kind not in carve_cells:
                failures.append(f"heap-allocations-per-syscall: {m.group(1)} carved {kind}, whose cells the gate does not know: {m.group(0)!r}")
                continue
            pin, byte_pin = carve_cells[kind] if kind is not None else (0, 0)
            if after < before or delta != after - before:
                failures.append(f"heap-allocations-per-syscall: the reading is not a delta: {m.group(0)!r}")
                continue
            if m.group(6) == "unrecorded" or m.group(7) == "unrecorded":
                failures.append(f"heap-allocations-per-syscall: the heap no longer recorded the reading's sizes: {m.group(0)!r}")
                continue
            groups = [] if m.group(7) == "none" else [tuple(int(x) for x in g.split("x")) for g in m.group(7).split(",")]
            sizes = [size for size, _ in groups]
            if sizes != sorted(set(sizes)) or any(count == 0 for _, count in groups):
                failures.append(f"heap-allocations-per-syscall: the sizes are not ascending distinct groups: {m.group(0)!r}")
            elif sum(count for _, count in groups) != delta:
                failures.append(f"heap-allocations-per-syscall: the sizes account for {sum(count for _, count in groups)} cells, the reading counted {delta}: {m.group(0)!r}")
            elif sum(size * count for size, count in groups) != int(m.group(6)):
                failures.append(f"heap-allocations-per-syscall: the bytes are not the sizes' total: {m.group(0)!r}")
            elif delta != pin and kind is not None:
                failures.append(f"heap-allocations-per-syscall: a retype carving {kind} read {delta}, the object's own cells are {pin}: {m.group(0)!r}")
            elif int(m.group(6)) != byte_pin and kind is not None:
                failures.append(f"heap-allocations-per-syscall: a retype carving {kind} read {m.group(6)} bytes, the object's own cells' bytes are {byte_pin}: {m.group(0)!r}")
            elif delta != pin:
                failures.append(f"heap-allocations-per-syscall: a kernel entry read {delta}, not 0: {m.group(0)!r}")
        # WS-UC UC1: every kind the retype's decode accepts has a carve
        # scenario and a delete of the carved capability, both pinned.  The
        # kinds come from the decode (`retype_object_kinds.lean`), each
        # constructor's name in kebab case, as the driver names a carve.  The
        # relation is read off the log in order: a first-call carve of the kind
        # names its object id and its capability's slot; the first delete of
        # that slot after it, with no other carve into the slot between, is
        # its delete; and the steady-state run of the same carve succeeded at
        # the same id afterwards, which a store still holding the object would
        # have refused, so the delete retired it.
        kinds = []
        derived = os.environ.get("RETYPE_OBJECT_KINDS", "")
        if os.environ.get("RETYPE_OBJECT_KINDS_STATUS", "1") != "0":
            failures.append(f"heap-allocations-per-syscall: the retype's object kinds could not be derived: {derived!r}")
        else:
            for line in derived.split("\n"):
                if not line.strip():
                    continue
                m = re.fullmatch(r"(\d+) SeLe4n\.Model\.KernelObjectType\.([a-zA-Z]+)", line.strip())
                if m is None:
                    failures.append(f"heap-allocations-per-syscall: an object kind line the gate cannot read: {line!r}")
                    continue
                kinds.append(re.sub(r"([A-Z])", lambda c: "-" + c.group(1).lower(), m.group(2)))
            if not kinds:
                failures.append("heap-allocations-per-syscall: the retype's decode answered no object kind")
        carve_re = re.compile(r"\[smp-test\] heap-allocations-per-syscall: ([a-z0-9-]+): core 0( \(first call\))?: carved ([a-z-]+)/\d+ at (\d+) into (0x[0-9a-f]+/\d+)$")
        delete_re = re.compile(r"\[smp-test\] heap-allocations-per-syscall: ([a-z0-9-]+): core 0( \(first call\))?: deleted (0x[0-9a-f]+/\d+)$")
        events = []
        for line in lines:
            m = carve_re.fullmatch(line)
            if m:
                events.append(("carve", m.group(1), m.group(2) is not None, m.group(3), m.group(4), m.group(5)))
                continue
            m = delete_re.fullmatch(line)
            if m:
                events.append(("delete", m.group(1), m.group(2) is not None, None, None, m.group(3)))
        for kind in kinds:
            carved_by = []
            deleted_by = []
            for i, (what, name, first, k, oid, slot) in enumerate(events):
                if what != "carve" or k != kind or not first or name not in expected:
                    continue
                steady = next((j for j in range(i + 1, len(events))
                               if events[j][:3] == ("carve", name, False) and events[j][4] == oid), None)
                if steady is None:
                    continue
                carved_by.append(name)
                for j in range(i + 1, steady):
                    e = events[j]
                    if e[0] == "carve" and e[5] == slot:
                        break
                    if e[0] == "delete" and e[5] == slot:
                        if e[2] and e[1] in expected:
                            deleted_by.append(e[1])
                        break
            if not carved_by:
                failures.append(f"heap-allocations-per-syscall: the retype can carve {kind}, and no pinned scenario carves it in both runs")
            elif not deleted_by:
                failures.append(f"heap-allocations-per-syscall: no pinned scenario deletes a carved {kind}'s capability before its carve runs again")

        # WS-UC UC4: a carve owns its cells, and its retire returns them.  The
        # owned-CNode window runs a CNode's carve, a capability copied into
        # one of its slots and out of it into a root slot, the carved slot's
        # delete and the carved capability's delete (the copy out lives on),
        # and reads this core's allocations and frees across all five: once
        # in each run, the cells allocated and the cells freed are each the
        # CNode's carve pin.  A cell the carve shares with another object, one
        # the escaped copy keeps, or one the retire leaves behind or takes
        # from another object, moves the frees off it.
        owned_re = re.compile(r"\[smp-test\] heap-allocations-per-syscall: owned-cnode-retire: core 0( \(first call\))?: allocated (\d+) freed (\d+)$")
        owned = [m for m in (owned_re.fullmatch(line) for line in lines) if m]
        owned_cnode = [carved.get(("untyped-retype-owned-cnode", first)) for first in (True, False)]
        if owned_cnode[0] is None or owned_cnode[0] != owned_cnode[1] or owned_cnode[0] not in carve_cells:
            failures.append(f"heap-allocations-per-syscall: owned-cnode-retire: the carve named {owned_cnode}, not one pinned CNode kind in both runs")
        elif not owned_cnode[0].startswith("cnode/"):
            failures.append(f"heap-allocations-per-syscall: owned-cnode-retire: the carve made {owned_cnode[0]}, not a CNode")
        else:
            owned_pin = carve_cells[owned_cnode[0]][0]
            for first in (True, False):
                window = [m for m in owned if (m.group(1) is not None) == first]
                which = "first call" if first else "steady state"
                if len(window) != 1:
                    failures.append(f"heap-allocations-per-syscall: owned-cnode-retire ({which}): expected one window, found {len(window)}")
                    continue
                allocated, freed = int(window[0].group(2)), int(window[0].group(3))
                if allocated != owned_pin or freed != owned_pin:
                    failures.append(f"heap-allocations-per-syscall: owned-cnode-retire ({which}): allocated {allocated} and freed {freed}, the CNode's carve pin is {owned_pin}: {window[0].group(0)!r}")

        # WS-ZA ZA6.1: each core's first entry, its bring-up reschedule, read
        # once per core (the boot core's after boot, each secondary's as it
        # comes up), each a delta of zero.
        # Each secondary's timer ticks and `.reschedule` SGI once it is up,
        # read on that core's own counter at the driver's start and its end:
        # one reading of each per core and run, with the line that says the
        # window took them, and each 0.
        for kind, took in (("secondary-ticks", r"took \d+ ticks"), ("secondary-reschedule", r"took the SGI")):
            for which in (" (first call)", ""):
                for core in (1, 2, 3):
                    prefix = f"[smp-test] heap-allocations-per-syscall: {kind}: core {core}{which}: "
                    window = [l for l in lines if l.startswith(prefix + "before=")]
                    taken = [l for l in lines if l.startswith(prefix) and re.fullmatch(took, l[len(prefix):])]
                    if len(window) != 1 or len(taken) != 1:
                        failures.append(f"heap-allocations-per-syscall: {kind}: core {core}{which}: expected one reading and one taken line, found {len(window)} and {len(taken)}")
                        continue
                    m = re.fullmatch(r"before=(\d+) after=(\d+) delta=(\d+) bytes=(\d+) sizes=(none|\d+x\d+(?:,\d+x\d+)*)", window[0][len(prefix):])
                    if m is None:
                        failures.append(f"heap-allocations-per-syscall: a reading the gate cannot read: {window[0]!r}")
                        continue
                    before, after, delta = int(m.group(1)), int(m.group(2)), int(m.group(3))
                    if after < before or delta != after - before:
                        failures.append(f"heap-allocations-per-syscall: the reading is not a delta: {window[0]!r}")
                    elif delta != 0:
                        failures.append(f"heap-allocations-per-syscall: a secondary's kernel entries read {delta}, not 0: {window[0]!r}")
        secondary = matches(r"\[smp-test\] heap-allocations-per-syscall: secondary-entry: core (\d+) \(first call\): before=(\d+) after=(\d+) delta=(\d+)$")
        cores = sorted(int(m.group(1)) for m in secondary)
        if cores != [0, 1, 2, 3]:
            failures.append(f"heap-allocations-per-syscall: secondary-entry: readings on cores {cores}, expected one on each of cores [0, 1, 2, 3]")
        for m in secondary:
            before, after, delta = (int(g) for g in m.groups()[1:])
            if after < before or delta != after - before:
                failures.append(f"heap-allocations-per-syscall: the reading is not a delta: {m.group(0)!r}")
            elif delta != 0:
                failures.append(f"heap-allocations-per-syscall: a core's first entry read {delta}, pinned at 0: {m.group(0)!r}")
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
