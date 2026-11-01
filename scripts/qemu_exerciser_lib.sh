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
        # WS-CV CV0.1, WS-ZA ZA4.1: a syscall allocates nothing.  Each round
        # trip runs twice on the boot core, its first call and its steady
        # state; the gate holds that each run's reading happened once, after
        # the round trip returned a frame or blocked as it should, is a delta,
        # and is its pinned reading: zero, or (WS-ZA ZA5.1) for a capability
        # invocation a later row brings to zero, the reading it has today, so
        # a change either way has to move the pin.
        # WS-ZA ZA6.1: a kernel entry other than a syscall (the timer tick, the
        # reschedule SGI) is measured the same way and reports that it was
        # entered and restored a thread; the secondary core's entry is
        # measured once per core, below.
        readings = [m for m in matches(r"\[smp-test\] heap-allocations-per-syscall: ([a-z0-9-]+): core 0( \(first call\))?: before=(\d+) after=(\d+) delta=(\d+)") if m.group(1) != "secondary-entry"]
        returned = matches(r"\[smp-test\] heap-allocations-per-syscall: ([a-z0-9-]+): core 0( \(first call\))?: (?:returned x0=0x[0-9a-f]+ x1=0x[0-9a-f]+|blocked, the other thread restored|entered, a thread restored)$")
        names = [m.group(1) for m in readings]
        # The scenario set is pinned: a round trip renamed or dropped from
        # `ROUND_TRIPS`, `PARTNER_SCENARIOS` or `INVOCATION_SCENARIOS`
        # (smp_exercisers.rs) must change this pin too, so the evidence cannot
        # disappear while the gate stays green.
        # Each scenario's pinned reading, (first call, steady state).
        pinned = {name: (0, 0) for name in (
            "signal", "signal-wide-badge", "wait-pending", "yield",
            "receive-blocks", "send-to-receiver", "wait-blocks", "signal-to-waiter",
            "receive-for-call", "call", "reply-recv", "call-to-reply-receiver", "reply",
            "send-blocks", "receive-from-sender",
            # WS-ZA ZA5.3: the same through a badged endpoint capability.
            "receive-for-badged-send", "badged-send-to-receiver",
            "badged-send-blocks", "receive-from-badged-sender",
            "receive-for-badged-call", "badged-call", "reply-to-badged-call",
            # WS-ZA ZA5.4 part 23: a receive and a wait blocked on a carved
            # endpoint and notification, the notification bound to the
            # partner, and each one's only capability deleted: the
            # finalisation cancels the waiter in place (the waiters are linked
            # through their TCBs) or unbinds the thread, then the retire.
            "receive-on-carved", "busy-endpoint-delete",
            "wait-on-carved", "busy-notification-delete",
            "bind-carved-notification", "bound-notification-delete",
            # WS-ZA ZA5.2: the thread and notification arms change their
            # objects in place.
            "tcb-set-priority", "tcb-set-mc-priority", "tcb-set-affinity",
            "tcb-set-fault-handler", "tcb-bind-notification", "tcb-unbind-notification",
            "tcb-set-space", "tcb-resume", "tcb-suspend", "tcb-set-ipc-buffer",
            # and the scheduling-context arms (the partner resumed and
            # suspended while it holds the context, the suspend releasing it),
            # behind the root task's own IPC-buffer set that the configure's
            # fifth word is read through.
            "root-set-ipc-buffer", "sched-context-configure", "sched-context-bind",
            "sched-context-unbind", "sched-context-consumed", "sched-context-rebind",
            "tcb-resume-bound",
            "tcb-suspend-bound",
            # WS-ZA ZA5.5: a service query reads the code its endpoint records,
            # and a revoke clears it and erases the registry entry in place.
            "service-query", "service-revoke",
            # WS-ZA ZA5.3: the capability operations write each slot's own
            # record in place and the derivation links in the slots.
            "cspace-copy", "cspace-move", "cspace-delete", "cspace-mint",
            "cspace-revoke", "reply-cap-delete", "reply-cap-mint",
            # a mapped capability copied, and a reply capability minted over
            # a record whose target another capability shares.
            "frame-copy-mapped", "frame-copy-delete", "reply-cap-mint-over-copy",
            "reply-cap-over-copy-delete", "frame-copy-for-revoke",
            # WS-ZA ZA5.4: a mapped frame's capability deleted, its record
            # read as words and its page unmapped in place.
            "frame-delete",
            # a page table installed over the slot cell it carries, removed
            # with that cell handed back, and its capability deleted.
            "page-table-map-1", "page-table-map-2", "page-table-map-3",
            "page-table-unmap-3", "page-table-unmap-2", "page-table-unmap-1",
            "page-table-delete-3", "page-table-delete-2", "page-table-delete-1",
            # WS-ZA ZA5.4 part 22: a quiescent endpoint, notification, reply
            # and CNode retired by their only capability's delete.
            "endpoint-delete", "notification-delete", "reply-delete", "cnode-delete",
            # WS-ZA ZA5.4 part 24: a carved thread's only capability deleted
            # while it is inactive and while it is bound to the boot
            # notification, a carved scheduling context's while it is bound
            # to a carved thread, then that thread's: each finalised in place
            # (the unbinds and the suspend write the objects' own cells) and
            # retired.  Two carved threads resumed onto one run queue, the
            # first suspended and its only capability deleted, then the
            # second's: the suspends unlink each from the queue in place (the
            # run links live in the TCBs).
            "inactive-tcb-delete", "bind-carved-tcb", "bound-tcb-delete",
            "bind-carved-sched-context", "bound-sched-context-delete",
            "unbound-tcb-delete", "resume-shared-tcb", "suspend-queued-tcb",
            "suspended-tcb-delete", "queued-tcb-delete",
            # WS-ZA ZA5.4 part 25: a carved reply's minted capability received
            # through and the partner's call that blocks on it, the minted
            # capability's delete; and a carved reply stashed by a blocked
            # receive, both its capabilities deleted by the partner: the final
            # delete clears the receiver's stash in its own TCB and retires
            # the reply, and the partner's send then finds the receiver waiting.
            # The busy reply's final delete cancels its caller in place: the
            # finalise reads the caller's codes before any write and stores
            # the splice, the consumed reply and the caller's cleared link in
            # their slots (`finaliseReply_eq_impl`, an @[csimp] over the
            # specification's `cancelIpcBlocking` reply arm).
            "mint-busy-reply-cap", "receive-with-carved-reply", "call-to-carved-reply",
            "busy-reply-cap-delete", "busy-reply-delete",
            "mint-stashed-reply-cap", "receive-stashing-reply", "stashed-reply-cap-delete",
            "stashed-reply-delete", "send-to-unstashed-receiver",
            # WS-ZA ZA5.4 part 26: a carved CNode holding an endpoint's only
            # capability, deleted: the loop deletes the endpoint's slot, which
            # retires it, and then retires the CNode; a carved thread holding
            # the last capability to its CNode root, deleted: the loop deletes
            # its space slots after the finalisation, retiring the CNode, and
            # retires the thread.  Each delete writes in place, and so does
            # the carved thread's first space set, over the space-slot records
            # its carve made (`TCB.spaceCellFilled`).
            "populated-cnode-delete", "space-cnode-cap-delete", "spaced-tcb-delete",
            "set-carved-tcb-space",
            # WS-ZA ZA5.13: on the exerciser image's labeling, an upper-domain
            # notification declassified and signalled through the declassifying
            # signal (each writes its audit record in its ring slot and tags the
            # caller), the tainted path — a blocked send carrying the caller's
            # tags and the receive that takes them — the audit monitor's two
            # reads and its drain, and the notification's delete.
            "declassify", "declassified-signal", "send-tainted-blocks",
            "receive-tainted", "audit-read-status", "audit-read-entry",
            "audit-drain", "upper-notification-delete",
            # WS-ZA ZA6.1: the timer tick and the reschedule SGI, each entered
            # over an EL0 frame on the boot core.
            "timer-tick", "reschedule-sgi",
            # WS-ZA ZA6.2: the refill scenario: the context configured and
            # bound to the root task, the tick that finds no refill due, the
            # tick that drains the yield's refill and switches back to the root
            # task, and the unbind.
            "refill-configure", "refill-bind-root", "refill-wait-tick",
            "refill-drain-tick", "refill-unbind-root",
            # WS-ZA ZA6.3: the bound yield's forfeit and an exhausting tick
            # link the context into the release queue in place and write its
            # refill in its own fields; the next tick drains it (ZA6.4: seL4's
            # used refill is due one period on, which is that tick).
            "refill-yield", "exhaust-tick", "exhaust-drain-tick")}
        # WS-ZA ZA5.1: the memory invocations' readings today, each the
        # operation's own cells (object writes, the store's copy); the rows
        # that bring them to zero lower these pins.
        pinned.update({
            # WS-ZA ZA5.4: a retype reads its new object's own cells in
            # steady state (a table 13, a frame 11: the object, its store,
            # index and type entries, the untyped's child record); the first
            # call of the first table also builds the destination slot's
            # capability record.  Since part 26 a boot CNode's spare records
            # own their object targets (`unshareSpareCell`), so neither first
            # call builds the record's target (`CapTarget.objectOver`).
            "untyped-retype-page-table-1": (15, 13),
            "untyped-retype-page-table-2": (13, 13),
            "untyped-retype-page-table-3": (14, 13),
            # The first carve after boot takes one cell more than its steady
            # state; since v0.36.134 that is the busy-endpoint carve, which
            # now runs first, so the frame carve reads 11 both times.
            "untyped-retype-frame": (11, 11), "vspace-map": (9, 0),
            # WS-ZA ZA5.4 part 22: each passive kind's carve, read at its own
            # cells (attributed by a QEMU trace of lean_alloc_small's callers).
            # 9 are the store's: the untyped's record and child cell written
            # in place (2), the object, index-set and type-table inserts (2
            # each) and the index row (1).  An endpoint and a notification
            # add their own record and object cell (2): since v0.36.134 the
            # carve rebuilds the shared constant it is built from
            # (`CarveRequest.object_eq_impl`, `KernelObject.unshareFresh`), so
            # the first receive or wait on it writes in place.  A reply adds its
            # record (2) and the carve request (1); a CNode adds the carve
            # request and its decode (3), its spare slot cells (12) and the
            # CNode record (1), and 4 larger cells the heap serves as page
            # runs, which the small-object trace does not see.
            "untyped-retype-endpoint": (11, 11), "untyped-retype-notification": (11, 11),
            # WS-ZA ZA5.4 part 23: the same carves at the finalising deletes'
            # own ids; the busy endpoint's is the run's first carve, which
            # since part 26 writes over its slot's boot record and that
            # record's own target as later carves do (11).
            "untyped-retype-busy-endpoint": (11, 11),
            "untyped-retype-busy-notification": (11, 11),
            "untyped-retype-bound-notification": (11, 11),
            # Since v0.36.139 a CNode carries its occupancy link array
            # (`CNode.occ`), one cell of its own: 30.
            "untyped-retype-reply": (12, 12), "untyped-retype-cnode": (30, 30),
            # WS-ZA ZA5.4 part 25: the busy and the stashed reply's carves,
            # at the passive reply's id once that reply is retired.
            "untyped-retype-busy-reply": (12, 12), "untyped-retype-stashed-reply": (12, 12),
            # WS-ZA ZA5.4 part 24: a thread's and a scheduling context's carve
            # (same trace).  Past the store's 9, a thread adds its TCB cell and
            # two 16-byte cells built with it (`CarveRequest.objectImpl`, 3)
            # and the carve request and its decode (`carveRequestOf?`, 2): 14.
            # Part 26 makes the thread's space-slot cells at the carve, as
            # seL4 makes a TCB's CTEs at the retype (QEMU trace of
            # lean_alloc_small's callers, `KernelObject.unshareFresh`): a
            # spare record, its `some` cell and its object target for each of
            # the two space slots (6), the thread's own slot, link and spare
            # arrays (3) and its own register file (1): 24.  Each is the new
            # thread's own; its first space set then writes over them.
            # A scheduling context adds its record (`SchedContext.empty`), its
            # object cell and the request and decode (4): 13, and 14 on its
            # first call, which also builds the capability's target record
            # (`CapTarget.objectOver`).
            "untyped-retype-tcb": (24, 24), "untyped-retype-bound-tcb": (24, 24),
            "untyped-retype-queued-tcb": (24, 24), "untyped-retype-shared-tcb": (24, 24),
            # The first resume of a carved thread enqueues a run-queue key no
            # thread has held (a QEMU trace of lean_alloc_small's callers):
            # the run queue's membership table builds the new key's entry
            # (`RHTable.insertNoResizeImpl` under `RunQueue.insert`, 2) and
            # the queue's ends record its new priority bucket
            # (`RunQueueEnds.appendImpl`, 1).  The steady state reuses both.
            "resume-carved-tcb": (3, 0),
            "untyped-retype-sched-context": (14, 13), "untyped-retype-sc-thread": (24, 24),
            "vspace-unmap-first": (0, 0), "vspace-map-again": (0, 0),
            "vspace-unify-instruction": (4, 3),
            "vspace-map-copy": (7, 5), "frame-revoke": (0, 0),
            "vspace-unmap": (0, 0),
            # a map at a second address after an unmap: the root's retained
            # mapping and epoch cells take the new address.
            "vspace-map-moved": (0, 0), "vspace-unmap-moved": (0, 0),
            # WS-ZA ZA5.4 part 26: the populated CNode's carve (a CNode's 30)
            # and the endpoint's into its slot (an endpoint's 11), the spaced
            # thread's carve (a thread's 24) and its CNode root's into the
            # move slot (a CNode's 30, and the capability's target cell, 31:
            # traced, the slot's spare record last held a reply capability
            # whose target is the boot reply object's own (`replyCapTargetIn`
            # shares it), so `CapTarget.objectOver` builds the new one).  The
            # carved thread's first space set writes over the records the
            # carve made, and the thread's cell in place (0).
            "untyped-retype-populated-cnode": (30, 30), "untyped-retype-into-cnode": (11, 11),
            "untyped-retype-spaced-tcb": (24, 24), "untyped-retype-space-cnode": (31, 31),
            # The reset is seL4's (WS-ZA ZA5.4 part 36, `v0.36.149`; 30 before):
            # every refusal precedes its one write, the in-place rewind of the
            # invoked capability's free index, so its dispatch runs through
            # `RefusalCarrying.ofChecked` and keeps no pre-state.
            "untyped-reset": (0, 0),
            # WS-ZA ZA5.9 (`v0.36.159`; 6 and 4 before, 9 and 7 before
            # ZA5.5): the registry table is retired, so a register's one write
            # is its endpoint's record, set in its slot from the decoded words
            # (`registerServiceWordsPerform`), and its compiled arm builds no
            # registration (`dispatchServiceRegisterByR_eq_impl`).
            "service-register": (0, 0),
        })
        expected = set(pinned)
        observed = set(names) | {m.group(1) for m in returned}
        if observed != expected:
            failures.append(f"heap-allocations-per-syscall: scenarios {sorted(observed)} are not the pinned set {sorted(expected)}")
        runs = [(m.group(1), m.group(2) is not None) for m in readings]
        trips = [(m.group(1), m.group(2) is not None) for m in returned]
        for name in sorted(observed | expected):
            for first in (True, False):
                which = "first call" if first else "steady state"
                if runs.count((name, first)) != 1 or trips.count((name, first)) != 1:
                    failures.append(f"heap-allocations-per-syscall: {name} ({which}): expected one reading and one returned or blocked round trip on core 0")
        for m in readings:
            before, after, delta = (int(g) for g in m.groups()[2:])
            pin = pinned.get(m.group(1), (0, 0))[0 if m.group(2) else 1]
            if after < before or delta != after - before:
                failures.append(f"heap-allocations-per-syscall: the reading is not a delta: {m.group(0)!r}")
            elif delta != pin:
                failures.append(f"heap-allocations-per-syscall: a syscall read {delta}, pinned at {pin}: {m.group(0)!r}")
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
