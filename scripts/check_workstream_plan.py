#!/usr/bin/env python3
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
"""Structural gate over workstream planning documents.

A plan under `docs/planning/` is relational data wearing prose: sub-task IDs
are keys, the phase map is an aggregate over them, the declared total is an
aggregate over that, and cross-references are foreign keys.  Those invariants
were maintained by hand and drifted in five consecutive cuts -- declared totals
of 126/143/145/146/149 against actual row counts, cross-references to rows that
renumbering had moved, and a phase whose own arithmetic (46 + 4 = 49) could not
be satisfied.  Each was found by review and fixed by re-running an ad-hoc
script that was never committed, so the next edit reintroduced the class.

This project already machine-checks the same shape of invariant for code --
`check_version_sync.sh` exists because one version spread across 36 sites
drifted the same way.  A plan is no different, so it gets the same treatment.

Checks, per plan that declares a `Sub-task count` header:

  1. Sub-task numbers run 1..N within each phase, no gaps, no duplicates.
  2. The phase map's per-phase count equals the number of rows for that phase.
  3. The declared total equals the sum of the phase map.
  4. Every `<PREFIX><phase>.<sub>` reference -- in the plan and in the
     companion documents that cite it -- resolves to a defined row.
  5. No sub-task row references itself or a later one (a backward dependency
     in execution order), which is the numbering rule stated in CLAUDE.md.
  6. Where a phase's table carries a per-row findings count, the column sums
     to the total the phase's acceptance text declares.

Run `--self-test` to check the checker: a scanner that under-reaches fails
silently, which is how the drift survived review in the first place.
"""

from __future__ import annotations

import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# Documents that cite plan sub-task IDs and must not cite a stale one.
COMPANIONS = [
    "docs/planning/UNFINISHED_SMP_WORK.md",
    "docs/WORKSTREAM_HISTORY.md",
    "CLAUDE.md",
    "AGENTS.md",
]

HEADER_TOTAL = re.compile(r"^>\s*\*\*Sub-task count\*\*:\s*(\d+)(?![\d\s]*[-\u2013])", re.M)
# Plans predating the flat-numbering rule use letter groups (`SM6.A.1`).  Those
# workstreams are closed, and CLAUDE.md grandfathers historical identifiers, so
# demanding a renumber of landed work would be the wrong remedy.  They are
# reported as legacy rather than skipped silently -- an unchecked document
# nobody can see is how this class survived in the first place.
LEGACY_ROW = re.compile(r"^\|\s*[A-Z]{2,}\d*\.[A-Z]\.\d+\s*\|", re.M)
SUBTASK_ROW = re.compile(r"^\|\s*([A-Z]{2,})(\d+)\.(\d+)\s*\|(.*)$", re.M)
FINDINGS_ROW = re.compile(r"^\|\s*[A-Z]{2,}\d+\.\d+\s*\|[^|]*\|\s*(\d+)\s*\|", re.M)
ACCEPT_TOTAL = re.compile(r"\*\*Acceptance\*\*:\s*all\s*\*\*(\d+)\*\*\s*findings", re.M)


def phase_map_rows(text: str, prefix: str) -> dict[int, int]:
    """`| RR0 | scope | 11 | S-M |` -> {0: 11}.  Sub-task rows are excluded by
    the absence of a dot, so the two table shapes cannot be confused."""
    out = {}
    pat = re.compile(r"^\|\s*" + prefix + r"(\d+)\s*\|[^|]*\|\s*(\d+)\s*\|", re.M)
    for m in pat.finditer(text):
        out[int(m.group(1))] = int(m.group(2))
    return out


def read_indexed(rel: str) -> str | None:
    """Read from the git index, not the working tree: the gate must check what
    is being committed.  Validating the tree while the gate reads the index is
    how a local run passed over content that no longer existed."""
    try:
        return subprocess.run(
            ["git", "show", f":{rel}"], cwd=REPO,
            capture_output=True, text=True, check=True).stdout
    except subprocess.CalledProcessError:
        p = REPO / rel
        return p.read_text(encoding="utf-8") if p.exists() else None


def check_plan(rel: str, text: str, companions: dict[str, str]) -> list[str]:
    errors: list[str] = []
    rows = list(SUBTASK_ROW.finditer(text))
    if not rows:
        return [f"{rel}: declares a sub-task count but has no sub-task rows"]

    prefix = rows[0].group(1)
    by_phase: dict[int, list[tuple[int, str]]] = defaultdict(list)
    for m in rows:
        if m.group(1) != prefix:
            errors.append(f"{rel}: mixed ID prefixes {prefix} and {m.group(1)}")
            continue
        by_phase[int(m.group(2))].append((int(m.group(3)), m.group(4)))

    defined = {f"{prefix}{ph}.{n}" for ph, subs in by_phase.items() for n, _ in subs}

    # 1. sequential within each phase
    for ph in sorted(by_phase):
        nums = sorted(n for n, _ in by_phase[ph])
        if nums != list(range(1, len(nums) + 1)):
            errors.append(
                f"{rel}: {prefix}{ph} sub-task numbers are not 1..{len(nums)}: {nums}")

    # 2 + 3. phase map and declared total
    declared = phase_map_rows(text, prefix)
    for ph in sorted(set(declared) | set(by_phase)):
        want, have = declared.get(ph), len(by_phase.get(ph, []))
        if ph not in declared:
            errors.append(f"{rel}: {prefix}{ph} has {have} rows but no phase-map entry")
        elif want != have:
            errors.append(
                f"{rel}: phase map says {prefix}{ph} has {want} sub-tasks, table has {have}")
    m = HEADER_TOTAL.search(text)
    if m and declared:
        total, summed = int(m.group(1)), sum(declared.values())
        if total != summed:
            errors.append(
                f"{rel}: declared total {total} != phase-map sum {summed}")

    # 4. every reference resolves, here and in the companions
    ref = re.compile(r"\b" + prefix + r"(\d+)\.(\d+)\b")
    for where, body in [(rel, text)] + list(companions.items()):
        for r in sorted({f"{prefix}{a}.{b}" for a, b in ref.findall(body)}):
            if r not in defined:
                errors.append(f"{where}: reference to {r}, which is not a sub-task in {rel}")

    # 5. no self- or forward-reference inside a sub-task row
    for ph in sorted(by_phase):
        for n, body in sorted(by_phase[ph]):
            for a, b in ref.findall(body):
                a, b = int(a), int(b)
                if a > ph or (a == ph and b >= n):
                    kind = "itself" if (a, b) == (ph, n) else f"the later {prefix}{a}.{b}"
                    errors.append(
                        f"{rel}: {prefix}{ph}.{n} depends on {kind}; "
                        "a sub-task may only consume a lower-numbered one")

    # 6. per-row findings counts sum to the declared acceptance total
    for sec in re.split(r"^### ", text, flags=re.M)[1:]:
        acc = ACCEPT_TOTAL.search(sec)
        counts = [int(x) for x in FINDINGS_ROW.findall(sec)]
        if acc and counts:
            want, have = int(acc.group(1)), sum(counts)
            if want != have:
                errors.append(
                    f"{rel}: {sec.split(chr(10))[0].strip()} acceptance claims "
                    f"{want} findings, its rows sum to {have}")
    return errors


# A plan may declare an estimate range ("60-80 across ~12-15 PRs") rather than
# an exact count.  A range is a forecast, not a claim of record, so there is no
# total-to-sum invariant to hold it to; it is counted in the summary so the
# gate's coverage is visible rather than assumed.
HEADER_RANGE = re.compile(r"^>\s*\*\*Sub-task count\*\*:", re.M)


def collect(paths: list[str]) -> tuple[list[str], dict[str, str], int]:
    plans, ranged = [], 0
    for p in sorted((REPO / "docs" / "planning").glob("*.md")) if not paths else [REPO / x for x in paths]:
        rel = str(p.relative_to(REPO))
        body = read_indexed(rel)
        if not body or not HEADER_RANGE.search(body):
            continue
        if HEADER_TOTAL.search(body):
            plans.append(rel)
        else:
            ranged += 1
    companions = {}
    for c in COMPANIONS:
        body = read_indexed(c)
        if body is not None:
            companions[c] = body
    return plans, companions, ranged


def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        return self_test()
    plans, companions, ranged = collect([a for a in argv if not a.startswith("-")])
    if not plans:
        print("check_workstream_plan: no plan declares a 'Sub-task count' header.")
        return 0
    errors, legacy, checked = [], [], []
    for rel in plans:
        body = read_indexed(rel)
        assert body is not None
        if LEGACY_ROW.search(body):
            legacy.append(rel)
            continue
        checked.append(rel)
        errors += check_plan(rel, body, {k: v for k, v in companions.items() if k != rel})
    if errors:
        print(f"FAIL: {len(errors)} workstream-plan structure error(s):")
        for e in errors:
            print(f"  {e}")
        print("\nA plan's numbering, counts and cross-references are data, not prose.")
        return 1
    print(f"PASS: {len(checked)} workstream plan(s) structurally consistent "
          f"(sequential IDs, phase counts, declared totals, cross-references, "
          f"no forward dependencies); "
          f"{len(legacy)} legacy letter-group plan(s) and {ranged} declaring an "
          f"estimate range are not held to flat numbering.")
    return 0


# ---------------------------------------------------------------------------
# Witness suite.  Each case plants exactly one real defect from this project's
# own history and asserts the checker reports it -- and a clean plan asserts it
# stays quiet, since a gate that fires on everything is as useless as one that
# fires on nothing.

CLEAN = """
> **Sub-task count**: 5 across 2 phases (XX0..XX1)

| Phase | Scope | Subs | Est |
|-------|-------|------|-----|
| XX0 | first | 3 | S |
| XX1 | second | 2 | M |

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| XX0.1 | groundwork | a | S |
| XX0.2 | builds on XX0.1 | a | S |
| XX0.3 | third | a | S |
| XX1.1 | consumes XX0.2 | b | M |
| XX1.2 | last | b | M |
"""


def _case(name, mutate, expect):
    text = mutate(CLEAN)
    errs = check_plan("plan.md", text, {})
    hit = any(expect in e for e in errs)
    return (name, hit, errs)


def self_test() -> int:
    cases = []

    cases.append(("a clean plan reports nothing",
                  not check_plan("plan.md", CLEAN, {}),
                  check_plan("plan.md", CLEAN, {})))

    # The 143 -> 145 class: header total stops matching the phase map.
    cases.append(_case("declared total drift",
                       lambda t: t.replace("**Sub-task count**: 5", "**Sub-task count**: 7"),
                       "declared total 7 != phase-map sum 5"))

    # The RR7 22 -> 23 class: phase map stops matching its own rows.
    cases.append(_case("phase-map count drift",
                       lambda t: t.replace("| XX1 | second | 2 |", "| XX1 | second | 4 |"),
                       "phase map says XX1 has 4 sub-tasks, table has 2"))

    # The renumbering class: a gap left by an inserted or removed row.
    cases.append(_case("non-sequential sub-task numbers",
                       lambda t: t.replace("| XX0.3 |", "| XX0.5 |"),
                       "not 1..3"))

    # The RR3.16 / RR7.15 / RR5.11 class: a citation renumbering left behind.
    cases.append(_case("dangling cross-reference",
                       lambda t: t.replace("consumes XX0.2", "consumes XX0.9"),
                       "reference to XX0.9"))

    # The RR2 / RR4 / RR5 class, in its numeric half: a row consuming a later one.
    cases.append(_case("forward dependency",
                       lambda t: t.replace("| XX0.1 | groundwork", "| XX0.1 | needs XX0.3"),
                       "depends on the later XX0.3"))

    # The RR6.4 class: a row naming itself as the task that does the thing.
    cases.append(_case("self-reference",
                       lambda t: t.replace("| XX0.2 | builds on XX0.1", "| XX0.2 | builds on XX0.2"),
                       "depends on itself"))

    # A stale citation in a companion document, not in the plan itself.
    companion_errs = check_plan("plan.md", CLEAN, {"CLAUDE.md": "see XX1.7 for detail"})
    cases.append(("stale reference in a companion document",
                  any("CLAUDE.md: reference to XX1.7" in e for e in companion_errs),
                  companion_errs))

    # The 46 + 4 = 49 class: a findings column that cannot reach its own total.
    findings = CLEAN + """
### XX2 - sweep

| Sub | Description | Findings | Est |
|-----|-------------|----------|-----|
| XX2.1 | batch one | 2 | S |
| XX2.2 | batch two | 1 | S |

**Acceptance**: all **5** findings this phase owns are closed.
"""
    ferrs = check_plan("plan.md", findings, {})
    cases.append(("findings column does not sum to the acceptance total",
                  any("acceptance claims 5 findings, its rows sum to 3" in e for e in ferrs),
                  ferrs))

    failed = 0
    for name, ok, detail in cases:
        if ok:
            print(f"  PASS: {name}")
        else:
            failed += 1
            print(f"  FAIL: {name} -- got {detail}")
    if failed:
        print(f"SELF-TEST FAILED: {failed} case(s)")
        return 1
    print(f"check_workstream_plan self-test: {len(cases)} cases, all correct.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
