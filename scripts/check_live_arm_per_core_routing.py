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
    """Map a definition's *short* name to its body text (declaration to next top-level)."""
    bodies: dict[str, str] = {}
    for path in lean_files():
        text = open(path).read()
        lines = text.split("\n")
        starts = []
        for m in DECL.finditer(text):
            starts.append((text[:m.start()].count("\n"), m.group(1)))
        for idx, (ln, name) in enumerate(starts):
            end = len(lines)
            for j in range(ln + 1, len(lines)):
                if TOP.match(lines[j]):
                    end = j
                    break
            body = "\n".join(lines[ln:end])
            # A short name can be defined in several namespaces; concatenating the
            # bodies is the conservative direction for a "can this reach X" gate.
            bodies[name] = bodies.get(name, "") + "\n" + body
    return bodies


def parse_map(path: str, fn: str) -> dict[str, str]:
    text = open(path).read()
    i = text.index(f"def {fn} : SyscallId → String")
    j = TOP.search(text, text.index("\n", i) + 1)
    seg = text[i: j.start() if j else len(text)]
    out = {}
    for m in re.finditer(r"^\s*\|\s*\.([A-Za-z][A-Za-z0-9]*)\s*=>\s*\"([^\"]+)\"", seg, re.M):
        out[m.group(1)] = m.group(2)
    return out


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
    # aliases are rejected below rather than skipped.
    try:
        aliases = {k: v for k, v in json.load(open(ALIASES)).items()
                   if not k.startswith("_")}
    except (OSError, ValueError):
        aliases = {}
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
