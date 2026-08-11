#!/usr/bin/env python3
"""Fail if a live syscall arm can reach a boot-pinned scheduler primitive.

WS-SM SM8.B, PR #861 review rounds 10 and 12 found the same defect three times,
one syscall per round: a live dispatch arm whose *scheduling* effects target
`bootCoreId` unconditionally.  `.tcbResume` enqueued on the boot core,
`.send` woke a rendezvous receiver there and descheduled a blocking sender
there, and `.tcbSetPriority` / `.tcbSetMCPriority` re-bucketed and preempted
there.  Each was fixed on discovery; none was found by a gate.

A grep over the dispatch arms would have caught none of them.  Every one was
**one level down**: the arm named `setPriorityOp`, and `setPriorityOp` called
`migrateRunQueueBucket`.  So the property to check is transitive — the
operation an arm reaches, and everything *it* reaches, must not hardcode the
boot core in a scheduler effect.

This script checks that.  It starts from `syscallIdToEnforcementNamePerCore`
(the total `SyscallId → String` map recording which operation each syscall
actually reaches under SMP), walks the call graph of Lean definitions to a
bounded depth, and fails on any boot-pinned primitive reached along the way.
Exceptions live in `scripts/per_core_routing_allowlist.json`, one entry per
(syscall, symbol) with a written reason, so a deliberate boot-pinning is a
counted, justified fact rather than an oversight waiting for a reviewer.

**Reach, stated honestly.**  The call graph is extracted from source text, so a
followed name is any identifier token appearing in a definition's body.  That is
sound at short range and useless at long range: by three hops the closure is
near-total and reports definitions the arm cannot reach.  The gate therefore
walks **two hops** from the named operation — arm -> operation -> helper — which
is where every defect found so far lived (`setPriorityOp` -> `migrateRunQueueBucket`
was the deepest).  `--self-test` is the check that this reach is not vacuous: it
re-runs the walk over the *canonical* pre-SMP map, which still names the
boot-pinned operations, and fails if the gate does not flag them.

Usage:  scripts/check_live_arm_per_core_routing.py [--depth N] [--list] [--self-test]
"""

from __future__ import annotations

import json
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(REPO, "SeLe4n")
MAPFILE = os.path.join(SRC, "Kernel", "InformationFlow", "CovertChannelPerCore.lean")
API = os.path.join(SRC, "Kernel", "API.lean")
NIFILE = os.path.join(SRC, "Kernel", "InformationFlow", "NonInterferenceCrossCore.lean")
CANON = os.path.join(SRC, "Kernel", "InformationFlow", "Enforcement", "Wrappers.lean")
ALLOWLIST = os.path.join(REPO, "scripts", "per_core_routing_allowlist.json")
ALIASES = os.path.join(REPO, "scripts", "per_core_routing_aliases.json")

# Scheduler effects that name the boot core rather than a supplied `CoreId`.
# Each is the *single-core* member of a per-core pair; its sibling takes a core.
BOOT_PINNED = {
    "ensureRunnable":            "enqueues on bootCoreId; per-core form is enqueueRunnableOnCore",
    "removeRunnable":            "clears bootCoreId's slots; per-core form is removeRunnableOnCore",
    "resumeThread":              "boot-core resume; per-core form is resumeThreadOnCore",
    "suspendThread":             "boot-core suspend; per-core form is suspendThreadOnCore",
    "migrateRunQueueBucket":     "re-buckets runQueueOnCore bootCoreId; per-core form is migrateRunQueueBucketOnCore",
    "propagatePriorityInheritance": "boot-core chain walk; per-core form is propagatePipChainCrossCore",
    "updatePipBoost":            "boot-core re-bucket; per-core form is updatePipBoostOnCore",
    "handleRescheduleSgi":       "boot-core reschedule; per-core form is handleRescheduleSgiOnCore",
}
# A raw read of the boot core's scheduler slots inside a live operation.
#
# PR #861 review round 17: `replenishQueueOnCore` joined the list because it is
# the third per-core scheduler slot and the gate could not see it.  A
# replenishment is enqueued on the bound thread's home core (`replenishOnCore`)
# and drained by that core's tick, so a purge keyed on `bootCoreId` is a silent
# no-op for any SC bound to a thread homed elsewhere.  Three live sites had it —
# `schedContextConfigure` and both arms of `schedContextUnbind` — after
# round 13 had routed the *run-queue* half of the very same operations per-core.
# Two slots checked out of three is how that survived.
STATE = os.path.join(SRC, "Model", "State.lean")


def per_core_scheduler_fields() -> list[str]:
    """The `SchedulerState` fields that are per-core `Vector`s.

    PR #861 review round 25: the read and write inventories were hand-written,
    and a hand-written inventory is how three of the seven per-core slots came
    to be unchecked — `activeDomain`, `domainScheduleIndex`,
    `domainTimeRemaining` and `lastTimeoutErrors` were all absent, so a live
    helper selecting against `activeDomainOnCore bootCoreId` passed the gate
    and its self-test alike.  Deriving the list from the structure means a
    field added to `SchedulerState` is covered the day it lands, which is the
    same reason the axiom sweep enumerates the elaborated environment and this
    gate's roots come from the enforcement map.

    Fails closed: a parse that finds nothing raises rather than returning an
    empty inventory, which would silently disable every pattern below.
    """
    src = open(STATE, encoding="utf-8").read()
    m = re.search(r"^structure SchedulerState where$(.*?)^\S", src, re.M | re.S)
    if not m:
        raise SystemExit("[per-core-routing] cannot locate `structure SchedulerState`")
    fields = re.findall(r"^\s{2}([a-z][A-Za-z0-9_']*)\s*:\s*Vector\b[^\n]*\bnumCores\b",
                        m.group(1), re.M)
    if not fields:
        raise SystemExit("[per-core-routing] no per-core Vector fields parsed from "
                         "SchedulerState -- the gate would check nothing")
    return fields


PER_CORE_FIELDS = per_core_scheduler_fields()

# PR #861 review round 26: these first shipped as `<accessor>\s+bootCoreId`,
# which matches only the dot-notation spelling (`st.scheduler.currentOnCore
# bootCoreId`), because there the receiver precedes the name.  The accessors
# take the scheduler state explicitly, so `currentOnCore st.scheduler
# bootCoreId` is an equally ordinary Lean call and went unmatched -- half the
# spellings of every boot-pinned read.  The literal defects this gate caught
# earlier all happened to be written the first way, which is why the gap
# survived.  Reads now use the same bounded-gap shape as the writes below,
# against the same normalized body, so the two halves cannot drift apart.
# The core is the accessor's LAST argument, so at most one argument may sit
# between the two: none in dot notation (`sched.currentOnCore bootCoreId`), one
# under explicit application (`currentOnCore st.scheduler bootCoreId`).  A
# bounded any-character gap was tried first and over-matched
# `determineExecutingCore`, where `currentOnCore c` is a read of the *searched*
# core and `bootCoreId` is the `find?.getD` fallback one line later -- a
# legitimate default, not a pinned read.  Matching the argument shape rather
# than a character budget tells the two apart.
# One argument: a (dotted) identifier, or a parenthesized expression with an
# optional field selection after it -- `(prepare st).scheduler`.  Round 27:
# the identifier-only form missed every computed receiver, which is the same
# under-reach as the dot-notation-only form it replaced, one spelling further
# out.  Nesting is bounded at two levels, which covers the receivers a call of
# this shape actually has; a deeper one would need a real parser, and the
# self-test's negatives are what keep the bound from silently widening.
_PAREN = r"\((?:[^()]|\((?:[^()]|\([^()]*\))*\))*\)"
_ARG = rf"(?:\s+(?:{_PAREN}|[A-Za-z_][A-Za-z0-9_.']*)(?:\.[A-Za-z_][A-Za-z0-9_.']*)?)?"
_BOOT = r"(?:[A-Za-z_][A-Za-z0-9_.']*\.)?bootCoreId"
BOOT_READS = [
    re.compile(rf"\b{f}OnCore\b{_ARG}\s+{_BOOT}\b")
    for f in PER_CORE_FIELDS
]

# PR #861 review round 23: the three patterns above are *accessor reads*, and a
# gate that sees only reads is half a gate.  The per-core scheduler *mutators*
# take their core as a positional argument, so `removeRunnableOnCore st tid
# bootCoreId` pins the write to the boot core just as surely as
# `runQueueOnCore bootCoreId` pinned the read — and recreates precisely the
# secondary-core defect this gate exists to close, while staying green.  The
# asymmetry was invisible because every defect found so far happened to be
# spelled as a read.
#
# The core argument is not adjacent to the callee, so each pattern spans the
# intervening arguments on one line.  Over-matching is the safe direction here:
# a false positive is one allowlist line, a false negative is a wedged core.
BOOT_WRITE_CALLEES = [
    # Per-core operations that are not plain field setters.
    "removeRunnableOnCore",
    "enqueueRunnableOnCore",
    "handleRescheduleSgiOnCore",
    "migrateRunQueueBucketOnCore",
    "switchToThreadOnCore",
    "preemptCurrentOnCore",
    "removeReplenishmentsOnCore",
    "advanceDomainOnCore",
    "decrementDomainTimeOnCore",
] + [
    # ... plus one setter per per-core field, derived for the reason above:
    # `setActiveDomainOnCore bootCoreId` pins a secondary core's domain
    # selection to the boot core's just as surely as `setCurrentOnCore` pins
    # its current thread.
    f"set{f[0].upper()}{f[1:]}OnCore" for f in PER_CORE_FIELDS
]
BOOT_WRITES = [
    re.compile(rf"\b{callee}\b.{{0,100}}?\bbootCoreId\b")
    for callee in BOOT_WRITE_CALLEES
]

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|partial\s+|noncomputable\s+)*"
                  r"(?:def|abbrev)\s+([A-Za-z_][A-Za-z0-9_.'?!]*)", re.M)
TOP = re.compile(r"^(?:@\[|/--|/-!|private\s|protected\s|partial\s|noncomputable\s|def\s|abbrev\s|"
                 r"theorem\s|lemma\s|instance\s|structure\s|inductive\s|end\s|namespace\s|section\s|"
                 r"open\s|import\s|example\s|macro\s|syntax\s|deriving\s)", re.M)


def lean_files() -> list[str]:
    out = []
    for root, _dirs, files in os.walk(SRC):
        for f in files:
            if f.endswith(".lean"):
                out.append(os.path.join(root, f))
    return out


def index_definitions() -> dict[str, str]:
    """Map a definition's *short* name to its body text (declaration to next top-level).

    PR #861 review round 15: the scan for "where does this declaration end" must
    start below the `def`/`abbrev` **keyword** line, not below the declaration's
    first line.  `DECL` deliberately matches Lean's two-line
    `@[attribute]` / `def name` form, so for those the match begins on the
    attribute line — and `TOP` matches `def `, so a scan starting one line later
    hit the declaration's own keyword and stopped immediately, recording the
    attribute alone as the body.  Every `@[export ...] def` in the tree was
    therefore indexed as an empty definition: `suspendThreadInner`
    (`Platform/FFI.lean`) came out as the literal string
    `@[export suspend_thread_inner]`.  A boot-pinned primitive inside any such
    body was invisible and the gate reported PASS — the fail-open mode this
    gate exists to eliminate, in the gate itself.
    """
    bodies: dict[str, str] = {}
    for path in lean_files():
        text = open(path).read()
        lines = text.split("\n")
        starts = []
        for m in DECL.finditer(text):
            # `m.start()` is the attribute (or modifier) line; `m.end()` sits just
            # past the declared name and so is always on the `def`/`abbrev` line.
            starts.append((text[:m.start()].count("\n"),
                           text[:m.end()].count("\n"),
                           m.group(1)))
        for ln, kw_ln, name in starts:
            end = len(lines)
            for j in range(kw_ln + 1, len(lines)):
                if TOP.match(lines[j]):
                    end = j
                    break
            body = "\n".join(lines[ln:end])
            # A short name can be defined in several namespaces; concatenating the
            # bodies is the conservative direction for a "can this reach X" gate.
            bodies[name] = bodies.get(name, "") + "\n" + body
    return bodies


ARM = re.compile(r"^([ \t]*)\|\s*\.([A-Za-z][A-Za-z0-9]*)\s*=>", re.M)
COL0 = re.compile(r"^[A-Za-z@/]")
# The definitions whose `SyscallId` arms are live dispatch paths.  Anything else
# matching on `SyscallId` in `API.lean` — the authority table, the lock-set
# table, delegation-theorem statements — is not a code path and must not be
# walked (round 20).
DISPATCH_DEFS = re.compile(r"^dispatch(WithCap|CapabilityOnly|Syscall)")


def dispatch_arm_bodies(path: str) -> dict[str, list[str]]:
    """Map a `SyscallId` constructor to the text of each dispatch arm matching it.

    PR #861 review round 20: **one entry per arm, not one concatenated blob.**
    A syscall commonly has two production roots — the unchecked arm and the
    information-flow-checked one — and `.send` is the case in point
    (`endpointSendDualWithCapsOnCore` vs `endpointSendCrossCoreDispatchChecked`).
    Concatenating them let the checked arm satisfy root verification while the
    unchecked arm was never walked, so a boot-pinned regression confined to it
    would have left this gate green.

    PR #861 review round 15: the label -> definition translation must be
    *verified against the dispatch*, not assumed.  An enforcement-boundary label
    that happens to be some Lean definition's name was accepted even when the
    live arm called a different operation — `.tcbSetAffinity` resolved to
    `setThreadCpuAffinity` while `dispatchCapabilityOnly` calls
    `setThreadCpuAffinityOp`, so the scheduling-relevant body was never walked
    and the advertised fail-closed check passed by coincidence.

    An arm runs to the next `| .ctor =>` at the same or shallower indent, or to
    the next column-0 top-level, whichever comes first.  Arms for one
    constructor across several dispatch functions are concatenated.
    """
    text = open(path).read()
    lines = text.split("\n")
    marks = [(text[:m.start()].count("\n"), len(m.group(1)), m.group(2))
             for m in ARM.finditer(text)]
    # Round 20: an arm counts only if it sits inside a *dispatch* definition.
    # `API.lean` also matches on `SyscallId` for the authority table
    # (`| .send => .write`) and inside delegation-theorem statements, and those
    # are not code paths.  Walking them produced spurious reach — a theorem
    # statement's `∀`-bound names resolve to unrelated definitions.
    def_at: list[tuple[int, str]] = []
    for m in DECL.finditer(text):
        def_at.append((text[:m.start()].count("\n"), m.group(1)))

    def enclosing(line: int) -> str:
        name = ""
        for ln, nm in def_at:
            if ln <= line:
                name = nm
            else:
                break
        return name

    out: dict[str, list[str]] = {}
    for i, (ln, indent, sid) in enumerate(marks):
        if not DISPATCH_DEFS.match(enclosing(ln)):
            continue
        end = len(lines)
        for j in range(i + 1, len(marks)):
            if marks[j][1] <= indent:
                end = marks[j][0]
                break
        for j in range(ln + 1, end):
            if COL0.match(lines[j]):
                end = j
                break
        out.setdefault(sid, []).append("\n".join(lines[ln:end]))
    return out


def parse_map(path: str, fn: str) -> dict[str, str]:
    text = open(path).read()
    i = text.index(f"def {fn} : SyscallId → String")
    j = TOP.search(text, text.index("\n", i) + 1)
    seg = text[i: j.start() if j else len(text)]
    out = {}
    for m in re.finditer(r"^\s*\|\s*\.([A-Za-z][A-Za-z0-9]*)\s*=>\s*\"([^\"]+)\"", seg, re.M):
        out[m.group(1)] = m.group(2)
    return out


def parse_live_arm_syscalls(path: str) -> set[str]:
    """The `SyscallId`s the cross-core NI inventory claims as live arms.

    Read from `crossCoreLiveArmSyscall`'s `=> some .<syscall>` arms.
    """
    text = open(path).read()
    i = text.index("def crossCoreLiveArmSyscall : CrossCoreTransition → Option SyscallId")
    j = TOP.search(text, text.index("\n", i) + 1)
    seg = text[i: j.start() if j else len(text)]
    return set(re.findall(r"=>\s*some\s+\.([A-Za-z][A-Za-z0-9]*)", seg))


def takes_a_core(body: str) -> bool:
    """Does this definition's *signature* take a `CoreId`?

    The signature is everything before the first `:=`.  A live arm's operation
    taking a core is the mechanical signal that it was re-routed to a per-core
    form and can therefore write a core other than the executing one.
    """
    head = body.split(":=", 1)[0]
    return re.search(r"(?<![A-Za-z0-9_'])CoreId(?![A-Za-z0-9_'])", head) is not None


# A *leading-dot* term — a dot not preceded by an identifier character.  In Lean
# that is anonymous-constructor notation (`.ok`, `.error`, `.schedContextUnbind`),
# never a call by short name.  A qualified call keeps its dot preceded by an
# identifier (`SchedContextOps.schedContextUnbindOnCore`) and so is left alone.
LEADING_DOT_CTOR = re.compile(r"(?<![A-Za-z0-9_'])\.[A-Za-z][A-Za-z0-9_']*")


def strip_arm_patterns(body: str) -> str:
    """Remove constructor references so only genuine call sites remain.

    PR #861 review round 16: the dispatch-verification check tokenized the whole
    arm, so the arm header `| .schedContextUnbind =>` made the *label*
    `schedContextUnbind` look like a call.  The live arm calls
    `schedContextUnbindOnCore`; the check passed on the header alone, and the
    walk then started from the single-core body — missing the wrapper's
    `priorityRescheduleOnCore` path entirely.  Same fail-open shape as the two
    round-15 gate defects.

    Stripping only `|`-prefixed patterns is not enough, which the fix's own first
    attempt proved: `decoded.syscallId = .schedContextUnbind` in the
    `syscallDelegates` arm reintroduced the bare name with no `|` in sight.  The
    boundary that actually separates the two is the *leading dot*.
    """
    return LEADING_DOT_CTOR.sub(" ", body)


def strip_comments(body: str) -> str:
    body = re.sub(r"/-.*?-/", " ", body, flags=re.S)
    return "\n".join(l for l in body.split("\n") if not l.strip().startswith("--"))


def collapse_whitespace(body: str) -> str:
    """Collapse every whitespace run to one space.

    PR #861 review round 24: the boot-*write* patterns first shipped with
    `[^\\n]{0,100}`, so a call whose arguments wrap — which in Lean is simply a
    call longer than the line budget — slipped past them, and the self-test's
    probes were all single-line so it passed with the gap.  Matching against a
    normalized body makes the `{0,100}` budget a distance in tokens rather than
    in source characters, so indentation and line breaks cannot hide a literal
    boot core.  The `BOOT_READS` patterns were never affected (`\\s` matches a
    newline); this is the newer patterns' own regression.
    """
    return re.sub(r"\s+", " ", body)


def called_names(body: str) -> set[str]:
    return set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", body))


def scan(percore: dict[str, str], bodies: dict[str, str], depth: int,
         allow: dict[tuple[str, str], str]) -> list[tuple[str, str, str, str]]:
    findings: list[tuple[str, str, str, str]] = []
    for sid, op in sorted(percore.items()):
        seen: set[str] = set()
        frontier = [op]
        for _ in range(depth):
            nxt: list[str] = []
            for name in frontier:
                if name in seen or name not in bodies:
                    continue
                seen.add(name)
                body = strip_comments(bodies[name])
                for sym, why in BOOT_PINNED.items():
                    if re.search(rf"(?<![A-Za-z0-9_']){sym}(?![A-Za-z0-9_'])", body):
                        if (sid, sym) in allow:
                            continue
                        findings.append((sid, name, sym, why))
                flat = collapse_whitespace(body)
                for pat in BOOT_READS:
                    if pat.search(flat):
                        if (sid, pat.pattern) in allow:
                            continue
                        findings.append((sid, name, pat.pattern,
                                         "reads the boot core's scheduler slot directly"))
                for pat in BOOT_WRITES:
                    if pat.search(flat):
                        if (sid, pat.pattern) in allow:
                            continue
                        findings.append((sid, name, pat.pattern,
                                         "writes a per-core scheduler slot at a literal "
                                         "bootCoreId; pass the operation's own core"))
                nxt.extend(called_names(body) & bodies.keys())
            frontier = nxt
    return findings


def main() -> int:
    depth = 2
    listing = "--list" in sys.argv
    if "--depth" in sys.argv:
        depth = int(sys.argv[sys.argv.index("--depth") + 1])

    bodies = index_definitions()
    canonical = parse_map(CANON, "syscallIdToEnforcementName")
    percore = dict(canonical)
    percore.update(parse_map(MAPFILE, "syscallIdToEnforcementNamePerCore"))
    # Enforcement-boundary labels and Lean definition names are two namespaces;
    # where they differ, an alias names the definition the arm reaches.  Missing
    # aliases are rejected below rather than skipped, and every resolution —
    # aliased or not — is verified against the dispatch arm (round 15).
    try:
        aliases = {k: v for k, v in json.load(open(ALIASES)).items()
                   if not k.startswith("_")}
    except (OSError, ValueError):
        aliases = {}
    labels = dict(percore)
    percore = {sid: aliases.get(op, op) for sid, op in percore.items()}

    try:
        allow = {(e["syscall"], e["symbol"]): e["reason"] for e in json.load(open(ALLOWLIST))}
    except (OSError, ValueError):
        allow = {}

    if "--self-test" in sys.argv:
        # The gate must FLAG the operations these arms called *before* this cut.
        # Probed by definition name rather than through the canonical map, because
        # that map's strings are enforcement-boundary labels and several
        # (`setPriority`, `setMCPriority`) are not Lean definitions at all —
        # which is the fail-open `unresolved` below now rejects.
        pre_smp = {"tcbResume": "resumeThread",
                   "tcbSetPriority": "setPriorityOp",
                   "tcbSetMCPriority": "setMCPriorityOp",
                   "send": "endpointSendDualWithCaps"}
        detected = {f[0] for f in scan(pre_smp, bodies, depth, {})}
        expected = set(pre_smp)
        missing = expected - detected
        if missing:
            print(f"[per-core-routing] SELF-TEST FAIL: reach {depth} does not detect "
                  f"the known boot-pinned arms: {sorted(missing)}")
            return 1
        # Round 23: the boot-*write* patterns must actually match.  They were
        # added to a tree that has no violation of that shape, so the scan went
        # green the moment they landed — which is equally what a broken regex
        # looks like.  These synthetic spellings are the difference between the
        # two, and the last one pins that a genuine per-core call (core taken
        # from `determineTargetCore`, not a literal) is NOT flagged, so the
        # patterns cannot be "fixed" into rejecting correct code.
        write_probes = [
            ("removeRunnableOnCore st tid bootCoreId", True),
            ("setCurrentOnCore bootCoreId none", True),
            ("handleRescheduleSgiOnCore st bootCoreId", True),
            ("let st2 := enqueueRunnableOnCore st1 tid bootCoreId", True),
            ("switchToThreadOnCore st tid (determineTargetCore st tid)", False),
            # Round 24: the same violations with their arguments wrapped, which
            # is how a real call of this length is written.  These are the
            # probes whose absence let the single-line gap ship.
            ("removeRunnableOnCore st tid\n            bootCoreId", True),
            ("let st2 :=\n  setCurrentOnCore\n    bootCoreId\n    none", True),
            ("switchToThreadOnCore st tid\n  (determineTargetCore st tid)", False),
            # Round 25: the derived slots.  Each of these passed the gate
            # before the inventory came from `SchedulerState` itself.
            ("setActiveDomainOnCore bootCoreId d", True),
            ("setDomainScheduleIndexOnCore bootCoreId 0", True),
            ("setDomainTimeRemainingOnCore bootCoreId n", True),
            ("setLastTimeoutErrorsOnCore bootCoreId []", True),
        ]
        # Round 25: the derivation must see every per-core slot.  A parse that
        # silently returns a subset is the failure mode the hand-written list
        # already demonstrated, so the count is pinned rather than trusted.
        want_fields = {"runQueue", "current", "activeDomain", "domainTimeRemaining",
                       "domainScheduleIndex", "replenishQueue", "lastTimeoutErrors"}
        if set(PER_CORE_FIELDS) != want_fields:
            print(f"[per-core-routing] SELF-TEST FAIL: per-core field derivation gives "
                  f"{sorted(PER_CORE_FIELDS)}, expected {sorted(want_fields)}.  If a field "
                  f"was added to SchedulerState, extend this set in the same commit.")
            return 1
        # Round 26: probe BOTH spellings per field -- dot-notation (receiver
        # before the name) and explicit application (receiver between the name
        # and the core), wrapped as well.  Probing only the first is what let
        # the explicit form go unmatched for every field.
        for f in PER_CORE_FIELDS:
            for spelling in (f"{f}OnCore bootCoreId",
                             f"{f}OnCore st.scheduler bootCoreId",
                             f"{f}OnCore\n  sched\n  bootCoreId",
                             # Round 27: computed receivers.
                             f"{f}OnCore (prepare st).scheduler bootCoreId",
                             f"{f}OnCore (mk (f x) y).scheduler Concurrency.bootCoreId"):
                if not any(pat.search(collapse_whitespace(spelling))
                           for pat in BOOT_READS):
                    print(f"[per-core-routing] SELF-TEST FAIL: no read pattern covers "
                          f"{spelling!r}")
                    return 1
        # Two negatives, both real: a read at a computed core, and the
        # `find?`-with-boot-fallback shape in `determineExecutingCore`, which a
        # bounded any-character gap did flag.
        for benign in ("currentOnCore st.scheduler (determineTargetCore st tid)",
                       "(Concurrency.allCores.find? (fun c => "
                       "st.scheduler.currentOnCore c == some tid)).getD\n"
                       "    Concurrency.bootCoreId"):
            if any(pat.search(collapse_whitespace(benign)) for pat in BOOT_READS):
                print(f"[per-core-routing] SELF-TEST FAIL: read patterns flag a "
                      f"genuine per-core read: {benign!r}")
                return 1
        for probe, want in write_probes:
            got = any(pat.search(collapse_whitespace(probe)) for pat in BOOT_WRITES)
            if got != want:
                verb = "missed" if want else "false-positived on"
                print(f"[per-core-routing] SELF-TEST FAIL: boot-write patterns "
                      f"{verb}: {probe!r}")
                return 1
        # Round 15: the `@[attribute]` / `def` form must index its real body.
        # Checked structurally rather than by naming one definition, so a rename
        # cannot quietly retire the check: no indexed body may consist solely of
        # attribute lines.  Before the fix EVERY attributed declaration in the
        # tree indexed that way — `suspendThreadInner` came out as the single
        # line `@[export suspend_thread_inner]` — so a boot-pinned call inside
        # any of them was invisible and the gate passed vacuously.
        # A correctly indexed body always contains its own `def`/`abbrev`
        # keyword; a truncated one stops above it.  That is the exact test —
        # "consists only of attribute lines" would misread the same-line
        # `@[inline] def foo := bar` form, whose one line is the whole body.
        attributed = [n for n, b in bodies.items()
                      if any(ln.lstrip().startswith("@[") for ln in b.split("\n"))]
        attr_only = sorted(n for n in attributed
                           if not re.search(r"(?<![A-Za-z0-9_'])(?:def|abbrev)"
                                            r"(?![A-Za-z0-9_'])", bodies[n]))
        if attr_only:
            print("[per-core-routing] SELF-TEST FAIL: these declarations indexed to "
                  "their attribute line alone, so their bodies are never scanned:")
            for n in attr_only[:10]:
                print(f"  {n}")
            return 1
        if not attributed:
            print("[per-core-routing] SELF-TEST FAIL: no attributed declaration found "
                  "at all — the attribute-form probe is vacuous.")
            return 1
        print(f"[per-core-routing] SELF-TEST PASS: {len(attributed)} attributed "
              f"declaration(s) index a body beyond their attribute line.")
        print(f"[per-core-routing] SELF-TEST PASS: reach {depth} detects all of "
              f"{sorted(expected)} in the pre-SMP map "
              f"({len(detected)} arm(s) flagged there in total).")
        return 0

    # FAIL-CLOSED: a mapped operation that is not a definition means the walk
    # starts nowhere and the syscall is silently unchecked.  The self-test found
    # this: the canonical map's `.tcbSetPriority => "setPriority"` resolves to no
    # Lean definition, so that arm was passing by vacuity, not by correctness.
    unresolved = sorted({(sid, op) for sid, op in percore.items() if op not in bodies})
    if unresolved:
        print("[per-core-routing] FAIL: a mapped operation does not resolve to a "
              "definition, so its arm is unchecked rather than clean:")
        for sid, op in unresolved:
            print(f"  .{sid} -> `{op}` (no `def`/`abbrev` of that name in SeLe4n/)")
        return 1

    # FAIL-CLOSED (round 15): resolving to *a* definition is not enough — it must
    # be the definition the live arm actually calls.  A label that coincidentally
    # names some unrelated `def` walked the wrong body and passed by accident.
    arms = dispatch_arm_bodies(API)
    unverified = []
    # Round 20: every arm is verified and walked, not just the one that happens
    # to name the mapped root.  `.send` has two production arms — the unchecked
    # one calls `endpointSendDualWithCapsOnCore`, the checked one
    # `endpointSendCrossCoreDispatchChecked` — so requiring only that *some* arm
    # mentions the mapped operation let a boot-pinned regression hide in the
    # other.  `extra_roots` carries each arm's own callees into the scan below.
    extra_roots: dict[str, set[str]] = {}
    for sid, root in sorted(percore.items()):
        armlist = arms.get(sid)
        if not armlist:
            unverified.append((sid, root, "no `| .<syscall> =>` arm in API.lean"))
            continue
        called_per_arm = [called_names(strip_arm_patterns(strip_comments(a))) for a in armlist]
        # Every root this syscall is declared to have: the mapped one, plus any
        # siblings named in the aliases file under `<label>#alt`.  Declared
        # rather than inferred — taking each arm's callees as roots would walk
        # names an arm merely mentions, and over-approximating a *reach* gate
        # produces findings against code the arm cannot run.
        declared = {root}
        alt = aliases.get(labels[sid] + "#alt")
        if isinstance(alt, str):
            declared.add(alt)
        elif isinstance(alt, list):
            declared.update(alt)
        uncovered = [i for i, c in enumerate(called_per_arm)
                     if not (declared & c)]
        if uncovered:
            unverified.append((sid, root,
                               f"dispatch arm #{uncovered[0]} calls none of "
                               f"{sorted(declared)} — declare it as "
                               f"`\"{labels[sid]}#alt\"` in the aliases file"))
            continue
        extra_roots.setdefault(sid, set()).update(d for d in declared
                                                  if d != root and d in bodies)
    if unverified:
        print("[per-core-routing] FAIL: a mapped operation is not the one its live "
              "dispatch arm calls, so the walk starts from the wrong body:")
        for sid, root, why in unverified:
            print(f"  .{sid} -> `{root}` — {why}")
        print("[per-core-routing] Add a verified entry to "
              "scripts/per_core_routing_aliases.json naming the operation the arm")
        print("[per-core-routing] really calls.")
        return 1

    # FAIL-CLOSED (round 15): the *other* half of the per-core obligation.
    #
    # Re-routing an arm to a per-core operation is only half the work — the
    # operation can now write a core it is not executing on, which is exactly
    # what the cross-core non-interference inventory exists to bound.  Rounds 12
    # and 14 rerouted five arms and gave three of them inventory entries; the
    # miss was found by a reviewer, one arm at a time, because nothing checked
    # the pairing.  This does: an operation whose signature takes a `CoreId` is
    # a per-core form, and its syscall must appear in `crossCoreLiveArmSyscall`.
    inventory = parse_live_arm_syscalls(NIFILE)
    missing_entry = []
    for sid, root in sorted(percore.items()):
        if not takes_a_core(bodies[root]):
            continue
        if sid in inventory or (sid, "cross-core-inventory") in allow:
            continue
        missing_entry.append((sid, root))
    if missing_entry:
        print("[per-core-routing] FAIL: a per-core-routed arm has no cross-core "
              "non-interference entry, so nothing bounds what it writes remotely:")
        for sid, root in missing_entry:
            print(f"  .{sid} -> `{root}` (takes a CoreId; absent from "
                  f"crossCoreLiveArmSyscall)")
        print("[per-core-routing] Add the entry with its write set and confinement")
        print("[per-core-routing] proof, or allowlist (syscall, \"cross-core-inventory\")")
        print("[per-core-routing] with the reason its per-core writes are unobservable.")
        return 1

    # Round 20: scan the mapped root AND every second-arm root discovered above,
    # so both production paths of a two-arm syscall are walked.
    scan_roots = dict(percore)
    for sid, roots in extra_roots.items():
        for i, extra in enumerate(sorted(roots)):
            scan_roots[f"{sid}#{i}"] = extra
    findings = scan(scan_roots, bodies, depth, allow)
    # Report a second-arm finding against the syscall, not the synthetic key.
    findings = [(sid.split("#", 1)[0], *rest) for sid, *rest in findings]

    if listing:
        for sid, op in sorted(percore.items()):
            print(f"  {sid:24s} -> {op}")

    print(f"[per-core-routing] {len(percore)} syscalls, reach depth {depth} "
          f"(two hops: arm -> operation -> helper), "
          f"{len(allow)} allowlisted exception(s)")
    if findings:
        print("[per-core-routing] FAIL: a live syscall arm can reach a boot-pinned "
              "scheduler primitive.")
        for sid, via, sym, why in sorted(set(findings)):
            print(f"  .{sid}: reaches `{sym}` via `{via}` — {why}")
        print("[per-core-routing] Route the arm through the per-core form, or add a")
        print("[per-core-routing] justified entry to scripts/per_core_routing_allowlist.json.")
        return 1
    print("[per-core-routing] PASS: no live arm reaches a boot-pinned scheduler primitive.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
