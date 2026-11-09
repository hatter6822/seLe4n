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
        python3 - "${EXERCISER_LOG}" "${LEAN_KERNEL}" "$@" <<'PY'
import os
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
        # entries in the object store (the object, index-set and type tables
        # and the index row), and its child record in the untyped.  Nothing
        # else a retype does may allocate: not its decode, not its carve
        # request, not the capability it writes.  Pinned here, cells then
        # bytes: a kind whose object changes shape changes its pins, and a
        # kind the exerciser carves that has no pin fails.  The breakdown of
        # each pin is the table in docs/planning/UNTYPED_BACKED_CELLS_PLAN.md.
        carve_cells = {
            "endpoint/0": (11, 368), "notification/0": (11, 360), "reply/0": (15, 376),
            "tcb/0": (24, 2160), "sched-context/7": (13, 560), "cnode/2": (28, 1248),
            "frame/0": (11, 272), "page-table/0": (13, 352), "vspace-root/0": (14, 376),
            "untyped/12": (12, 304),
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
            "declassify", "endpoint-delete", "exhaust-drain-tick",
            "exhaust-tick", "fp-access", "fp-access-partner", "fp-owner-blocks",
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
            "receive-tainted", "receive-with-carved-reply", "refill-bind-root",
            "refill-configure", "refill-drain-tick", "refill-unbind-root", "refill-wait-tick",
            "refill-yield", "reply", "reply-cap-delete", "reply-cap-mint",
            "reply-cap-mint-over-copy", "reply-cap-over-copy-delete", "reply-delete",
            "reply-queued-fault", "reply-recv", "reply-to-badged-call", "reschedule-sgi",
            "resume-carved-tcb", "resume-shared-tcb", "root-set-ipc-buffer",
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
            "untyped-retype-reply", "untyped-retype-sc-thread", "untyped-retype-sched-context",
            "untyped-retype-shared-tcb", "untyped-retype-space-cnode",
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
            "caps-take-resume", "caps-take-send-blocks", "caps-take-partner-takes",
            "caps-take-partner-yield", "caps-take-suspend",
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

        # WS-ZA ZA6.1: each core's first entry, its bring-up reschedule, read
        # once per core (the boot core's after boot, each secondary's as it
        # comes up), each a delta of zero.
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
