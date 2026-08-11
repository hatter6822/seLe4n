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
BOOT_READS = [
    re.compile(r"currentOnCore\s+bootCoreId"),
    re.compile(r"runQueueOnCore\s+bootCoreId"),
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


def dispatch_arm_bodies(path: str) -> dict[str, str]:
    """Map a `SyscallId` constructor to the text of every dispatch arm matching it.

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
    out: dict[str, str] = {}
    for i, (ln, indent, sid) in enumerate(marks):
        end = len(lines)
        for j in range(i + 1, len(marks)):
            if marks[j][1] <= indent:
                end = marks[j][0]
                break
        for j in range(ln + 1, end):
            if COL0.match(lines[j]):
                end = j
                break
        out[sid] = out.get(sid, "") + "\n" + "\n".join(lines[ln:end])
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


def strip_comments(body: str) -> str:
    body = re.sub(r"/-.*?-/", " ", body, flags=re.S)
    return "\n".join(l for l in body.split("\n") if not l.strip().startswith("--"))


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
                for pat in BOOT_READS:
                    if pat.search(body):
                        if (sid, pat.pattern) in allow:
                            continue
                        findings.append((sid, name, pat.pattern,
                                         "reads the boot core's scheduler slot directly"))
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
    for sid, root in sorted(percore.items()):
        arm = arms.get(sid)
        if arm is None:
            unverified.append((sid, root, "no `| .<syscall> =>` arm in API.lean"))
        elif root not in called_names(strip_comments(arm)):
            unverified.append((sid, root,
                               f"the dispatch arm never mentions `{root}`"
                               + (f" (label `{labels[sid]}`)" if labels[sid] != root else "")))
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

    findings = scan(percore, bodies, depth, allow)

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
