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

import os
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
    out: dict[int, int] = {}
    dupes: list[str] = []
    pat = re.compile(r"^\|\s*" + prefix + r"(\d+)\s*\|[^|]*\|\s*(\d+)\s*\|", re.M)
    for m in pat.finditer(text):
        ph, n = int(m.group(1)), int(m.group(2))
        if ph in out:
            # Assigning over the earlier row would de-duplicate the map before
            # any comparison ran, so a plan listing a phase twice -- with two
            # different counts -- would pass on whichever row came last.
            dupes.append(f"{prefix}{ph} appears twice in the phase map "
                         f"(counts {out[ph]} and {n}); one of them is wrong")
        out[ph] = n
    return out, dupes


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
    text = prose_view(text)
    companions = {k: prose_view(v) for k, v in companions.items()}
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
    declared, dupes = phase_map_rows(text, prefix)
    errors += [f"{rel}: {d}" for d in dupes]
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


def list_tracked(ref: str) -> list[str]:
    """Plans as `ref` sees them.  Enumerating the working tree instead would
    make a plan staged for deletion invisible: the glob would not find it, so
    its prefix would never be checked and a companion still citing its
    sub-tasks would pass.  The gate reads the index for content, so it must
    enumerate from the index too."""
    paths = ["docs/planning/", "docs/dev_history/planning/"]
    cmd = (["git", "ls-files", "--", *[x + "*.md" for x in paths]] if ref == ":"
           else ["git", "ls-tree", "-r", "--name-only", ref, "--", *paths])
    try:
        out = subprocess.run(cmd, cwd=REPO, capture_output=True, text=True,
                             check=True).stdout
    except subprocess.CalledProcessError:
        return []
    return sorted(x for x in out.splitlines() if x.endswith(".md"))


def read_at(ref: str, rel: str) -> str | None:
    try:
        return subprocess.run(["git", "show", f"{ref}{rel}" if ref == ":" else f"{ref}:{rel}"],
                              cwd=REPO, capture_output=True, text=True, check=True).stdout
    except subprocess.CalledProcessError:
        return None


FENCE = re.compile(r"^```.*?^```", re.M | re.S)


def prose_view(text: str) -> str:
    """The document with fenced blocks blanked out, line count preserved.

    A plan illustrating a row shape or citing an example ID inside a fence is
    showing the reader what one looks like, not declaring one.  Parsing those
    as data made the gate fail legitimate documents — a phantom phase from a
    fenced table, a dangling citation from an example ID — which is the mirror
    of a bypass: it pushes authors to contort prose to satisfy the scanner,
    which this project forbids in as many words.  Lines are replaced rather
    than removed so any position the caller reports still lines up.
    """
    return FENCE.sub(lambda m: "\n" * m.group(0).count("\n"), text)


def global_definitions(clashes: list | None = None) -> dict[str, tuple[str, set[str]]]:
    """Every sub-task ID the indexed tree defines, keyed by prefix.

    Built across `docs/planning/` **and** `docs/dev_history/planning/`, because
    checking a companion's citation against one plan at a time cannot see two
    things: a plan archived on close still defines its IDs (SM10.6.4 moves this
    very plan), and a plan whose rows are re-prefixed wholesale leaves the old
    prefix cited nowhere the per-plan scan looks.  A map keyed by prefix
    answers both.
    """
    out: dict[str, tuple[str, set[str]]] = {}
    clashes = clashes if clashes is not None else []
    for rel in list_tracked(":"):
        body = read_indexed(rel)
        if not body:
            continue
        body = prose_view(body)
        rows = list(SUBTASK_ROW.finditer(body))
        if not rows:
            continue
        prefix = rows[0].group(1)
        ids = {f"{prefix}{m.group(2)}.{m.group(3)}" for m in rows
               if m.group(1) == prefix}
        if prefix in out and out[prefix][0] != rel:
            # Unioning two plans' IDs under one prefix makes every citation
            # ambiguous and hides duplicate definitions; record the clash so
            # the caller can report it rather than silently merging.
            clashes.append((prefix, out[prefix][0], rel))
            continue
        where, known = out.get(prefix, (rel, set()))
        out[prefix] = (where, known | ids)
    return out


def companion_citation_errors(companions: dict[str, str]) -> list[str]:
    """Hold every companion citation against the global map.

    A prefix the tree no longer defines anywhere is reported wholesale: that is
    a plan deleted, or renamed out from under its citations.  A prefix that is
    still defined has each citation checked individually.
    """
    errors: list[str] = []
    clashes: list[tuple[str, str, str]] = []
    defined = global_definitions(clashes)
    for prefix, first, second in clashes:
        errors.append(f"prefix {prefix} is defined by two plans, {first} and "
                      f"{second}; a citation to it cannot be resolved")
    # Plans cite one another's rows, so every tracked plan is scanned too, not
    # just the four companion documents: a cross-plan citation was invisible to
    # both passes — the global one never looked at plan bodies, and the
    # per-plan one searched each plan only for its own prefix.
    sources = dict(companions)
    for rel in list_tracked(":"):
        body = read_indexed(rel)
        if body:
            sources.setdefault(rel, prose_view(body))
    baseline_prefixes: dict[str, str] = {}
    for base in baseline_refs():
        for rel in list_tracked(base):
            body = read_at(base, rel)
            rows = list(SUBTASK_ROW.finditer(body)) if body else []
            if rows:
                baseline_prefixes.setdefault(rows[0].group(1), rel)

    sources = {k: prose_view(v) for k, v in sources.items()}
    for where, text in sources.items():
        for m in sorted({(a, b, c) for a, b, c in
                         re.findall(r"\b([A-Z]{2,})(\d+)\.(\d+)\b", text)}):
            prefix, cite = m[0], f"{m[0]}{m[1]}.{m[2]}"
            if prefix in defined:
                if cite not in defined[prefix][1]:
                    errors.append(f"{where}: reference to {cite}, which is not a "
                                  f"sub-task in {defined[prefix][0]}")
            elif prefix in baseline_prefixes:
                errors.append(
                    f"{where}: cites {cite}, but nothing in the tree defines "
                    f"{prefix} any more — {baseline_prefixes[prefix]} defined it "
                    f"before this change (deleted, or its rows re-prefixed)")
    return errors


def baseline_refs() -> list[str]:
    """Revisions a plan may have existed in but the index no longer carries.

    `HEAD` alone covers only a *staged* deletion.  In CI the deletion is
    already committed, so HEAD and the index name the same tree and the
    difference is always empty -- the check would be dead exactly where it is
    meant to run.  The integration base is therefore consulted too, so a
    committed deletion on the branch is still compared against a revision that
    predates it.
    """
    refs = ["HEAD"]
    override = os.environ.get("SELE4N_PLAN_BASE_REF")
    for cand in ([override] if override else ["origin/main", "main"]):
        if cand and subprocess.run(["git", "rev-parse", "--verify", "-q", cand],
                                   cwd=REPO, capture_output=True).returncode == 0:
            refs.append(cand)
            break
    return refs


def baseline_is_complete() -> bool:
    """Whether an integration base was available.  A shallow clone with no
    base is reported rather than silently narrowing the check."""
    return len(baseline_refs()) > 1


def deleted_plan_errors(companions: dict[str, str]) -> list[str]:
    """A plan may not be deleted while its sub-tasks are still cited.  Removing
    the plan removes the only definition of those IDs, so every citation to it
    becomes dangling in the same commit that hides it from the gate."""
    errors = []
    # Remember which revision still holds each departing plan: on a branch
    # where the deletion is already committed, HEAD no longer has the file, so
    # reading its body from HEAD would find nothing and the check would pass.
    present: dict[str, str] = {}
    for base in baseline_refs():
        for rel in list_tracked(base):
            present.setdefault(rel, base)
    gone = set(present) - set(list_tracked(":"))
    for rel in sorted(gone):
        body = read_at(present[rel], rel)
        if not body or not HEADER_TOTAL.search(body):
            continue
        rows = list(SUBTASK_ROW.finditer(body))
        if not rows:
            continue
        prefix = rows[0].group(1)
        ref = re.compile(r"\b" + prefix + r"(\d+)\.(\d+)\b")
        for where, text in companions.items():
            for a, b in sorted({(x, y) for x, y in ref.findall(text)}):
                errors.append(
                    f"{where}: cites {prefix}{a}.{b}, but this change deletes "
                    f"{rel}, which is where that sub-task is defined")
    return errors


def collect(paths: list[str]) -> tuple[list[str], dict[str, str], int]:
    plans, ranged, legacy_only = [], 0, []
    for rel in (list_tracked(":") if not paths else paths):
        body = read_indexed(rel)
        if not body:
            continue
        # Structural checking follows the *rows*, not the header.  Keying off
        # the `Sub-task count` line made the gate opt-in: a plan with
        # non-sequential numbering and a forward dependency passed simply by
        # omitting one line, which is the easiest bypass to trip by accident.
        # The declared-total comparison still needs an exact count; everything
        # else needs only flat rows.
        if not SUBTASK_ROW.search(body):
            # No flat rows: either a genuinely legacy letter-group plan, or a
            # document with no sub-task table to check at all.
            if LEGACY_ROW.search(body):
                legacy_only.append(rel)
            elif HEADER_RANGE.search(body):
                ranged += 1
            continue
        plans.append(rel)
        if not HEADER_TOTAL.search(body):
            ranged += 1
    companions = {}
    for c in COMPANIONS:
        body = read_indexed(c)
        if body is not None:
            companions[c] = body
    return plans, companions, ranged, legacy_only


def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        return self_test()
    plans, companions, ranged, legacy_only = collect([a for a in argv if not a.startswith("-")])
    # Deliberately before the "nothing to validate" exit: deleting the last
    # exact-count plan while a companion still cites it left `plans` empty, so
    # returning here skipped the very check that deletion is supposed to trip.
    orphan_errors = companion_citation_errors(companions)
    if not plans:
        if orphan_errors:
            print(f"FAIL: {len(orphan_errors)} workstream-plan structure error(s):")
            for e in orphan_errors:
                print(f"  {e}")
            return 1
        print("check_workstream_plan: no plan declares a 'Sub-task count' header.")
        return 0
    errors, legacy, checked = list(orphan_errors), list(legacy_only), []
    for rel in plans:
        body = read_indexed(rel)
        assert body is not None
        flat = list(SUBTASK_ROW.finditer(body))
        letter = list(LEGACY_ROW.finditer(body))
        if letter and not flat:
            # Genuinely legacy: the whole plan predates flat numbering.
            legacy.append(rel)
            continue
        if letter:
            # A flat plan with one letter-group row is not a legacy plan; it is
            # a flat plan with a malformed row.  Treating it as legacy skipped
            # every sequential-ID, phase-count, total and dependency check for
            # the entire file, which is a bypass rather than a grandfather.
            errors.append(
                f"{rel}: mixes {len(letter)} letter-group row(s) into a flat "
                f"plan (first: {letter[0].group(0).strip()}); flat plans use "
                f"<PREFIX><phase>.<sub> throughout")
        checked.append(rel)
        errors += check_plan(rel, body, {k: v for k, v in companions.items() if k != rel})
    seen, deduped = set(), []
    for e in errors:
        if e not in seen:
            seen.add(e)
            deduped.append(e)
    errors = deduped
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
    if not baseline_is_complete():
        # Narrower coverage is said out loud rather than inferred from a pass.
        print("  NOTE: no integration base resolved (shallow clone?), so a plan "
              "deletion committed on this branch was not compared against a "
              "revision predating it; set SELE4N_PLAN_BASE_REF to restore it.")
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


def _cli_cases():
    """Drive the command, not the helpers.

    Every earlier witness called a function directly, so none of them could see
    a defect in `main`'s control flow — and two lived there: deleting the last
    exact-count plan returned before the citation check ran, and one
    letter-group row grandfathered an entire flat plan past every check.  Both
    reported exit 0.  These cases run the CLI in a throwaway repository and
    assert on its exit status, which is the only thing CI actually reads.
    """
    import shutil
    import tempfile
    out = []
    src = Path(__file__).resolve()

    def build(td, mutate):
        root = Path(td)
        (root / "docs" / "planning").mkdir(parents=True)
        (root / "scripts").mkdir()
        shutil.copy(src, root / "scripts" / src.name)
        (root / "docs" / "planning" / "XX_PLAN.md").write_text(CLEAN, encoding="utf-8")
        (root / "CLAUDE.md").write_text("cites XX0.1\n", encoding="utf-8")
        git = lambda *a: subprocess.run(["git", *a], cwd=root, capture_output=True, check=True)
        git("init", "-q", "-b", "main")
        git("config", "user.email", "gate@example.invalid")
        git("config", "user.name", "gate")
        git("add", "-A"); git("commit", "-qm", "base")
        mutate(root, git)
        env = {**os.environ, "SELE4N_PLAN_BASE_REF": "main"}
        return subprocess.run([sys.executable, "scripts/" + src.name],
                              cwd=root, capture_output=True, text=True, env=env)

    def drop_sole_plan(root, git):
        git("checkout", "-q", "-b", "topic")
        git("rm", "-q", "docs/planning/XX_PLAN.md")
        git("commit", "-qm", "delete the sole plan")

    def headerless_plan(root, git):
        # Found by probing the gate rather than by review: keying coverage off
        # the `Sub-task count` line made it opt-in, so omitting one line took a
        # plan with non-sequential numbering AND a forward dependency to exit 0.
        p2 = root / "docs" / "planning" / "XX_PLAN.md"
        p2.write_text(
            CLEAN.replace("> **Sub-task count**: 5 across 2 phases (XX0..XX1)\n", "")
                 .replace("| XX0.3 | third | a | S |", "| XX0.7 | third | a | S |"),
            encoding="utf-8")
        git("add", "-A")

    def cross_plan_and_duplicate_prefix(root, git):
        d = root / "docs" / "planning"
        (d / "AA_PLAN.md").write_text(
            CLEAN.replace("XX", "AA").replace("| AA0.1 | groundwork",
                                              "| AA0.1 | consumes BB0.9"),
            encoding="utf-8")
        (d / "BB_PLAN.md").write_text(CLEAN.replace("XX", "BB"), encoding="utf-8")
        (d / "CC_ONE.md").write_text(CLEAN.replace("XX", "CC"), encoding="utf-8")
        (d / "CC_TWO.md").write_text(CLEAN.replace("XX", "CC"), encoding="utf-8")
        git("add", "-A")

    def stray_letter_row(root, git):
        p2 = root / "docs" / "planning" / "XX_PLAN.md"
        p2.write_text(CLEAN.replace("| XX0 | first | 3 |", "| XX0 | first | 99 |")
                      .replace("| XX1.2 | last | b | M |",
                               "| XX1.2 | last | b | M |\n| XX2.A.1 | stray | c | S |"),
                      encoding="utf-8")
        git("add", "-A")

    with tempfile.TemporaryDirectory() as td:
        r = build(td, drop_sole_plan)
        out.append(("CLI: deleting the last plan with a live citation exits non-zero",
                    r.returncode != 0 and "nothing in the tree defines XX" in r.stdout,
                    (r.returncode, r.stdout.strip()[:110])))
    with tempfile.TemporaryDirectory() as td:
        r = build(td, cross_plan_and_duplicate_prefix)
        out.append(("CLI: a plan citing another plan's missing row is caught",
                    r.returncode != 0 and "reference to BB0.9" in r.stdout,
                    (r.returncode, r.stdout.strip()[:110])))
        out.append(("CLI: two plans claiming one prefix are rejected",
                    r.returncode != 0 and "defined by two plans" in r.stdout,
                    (r.returncode, r.stdout.strip()[:110])))
    with tempfile.TemporaryDirectory() as td:
        r = build(td, headerless_plan)
        out.append(("CLI: a plan without a count header is still checked",
                    r.returncode != 0 and "not 1..3" in r.stdout,
                    (r.returncode, r.stdout.strip()[:110])))
    with tempfile.TemporaryDirectory() as td:
        r = build(td, stray_letter_row)
        out.append(("CLI: a stray letter-group row does not grandfather a flat plan",
                    r.returncode != 0 and "phase map says XX0" in r.stdout,
                    (r.returncode, r.stdout.strip()[:110])))
    return out


def _archive_and_reprefix_cases():
    """Two moves that look identical to a naive set difference but are not:
    archiving a closed plan keeps its IDs defined, re-prefixing its rows does
    not."""
    import tempfile
    global REPO
    saved, out = REPO, []
    try:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            plan = root / "docs" / "planning" / "XX_PLAN.md"
            plan.parent.mkdir(parents=True)
            (root / "docs" / "dev_history" / "planning").mkdir(parents=True)
            plan.write_text(CLEAN, encoding="utf-8")
            (root / "CLAUDE.md").write_text("scheduled at XX0.2\n", encoding="utf-8")
            git = lambda *a: subprocess.run(["git", *a], cwd=root, capture_output=True, check=True)
            git("init", "-q", "-b", "main")
            git("config", "user.email", "gate@example.invalid")
            git("config", "user.name", "gate")
            git("add", "-A"); git("commit", "-qm", "plan and citation")
            REPO = root
            os.environ["SELE4N_PLAN_BASE_REF"] = "main"
            companions = {"CLAUDE.md": (root / "CLAUDE.md").read_text()}

            # Archiving on close: SM10.6.4 does exactly this to the live plan.
            git("mv", "docs/planning/XX_PLAN.md",
                "docs/dev_history/planning/XX_PLAN.md")
            out.append(("archiving a closed plan does not orphan its citations",
                        companion_citation_errors(companions) == [],
                        companion_citation_errors(companions)))

            # Re-prefixing every row: the IDs the companion cites cease to exist.
            git("mv", "docs/dev_history/planning/XX_PLAN.md",
                "docs/planning/XX_PLAN.md")
            plan.write_text(CLEAN.replace("XX", "YY"), encoding="utf-8")
            git("add", "-A")
            errs = companion_citation_errors(companions)
            out.append(("re-prefixing a plan's rows is caught, not bypassed",
                        any("nothing in the tree defines XX" in e for e in errs),
                        errs))
            return out
    finally:
        REPO = saved
        os.environ.pop("SELE4N_PLAN_BASE_REF", None)


def _committed_deletion_case():
    """The CI path.  The staged-deletion witness passed while this was dead:
    once the deletion is committed, HEAD and the index agree, so a HEAD-only
    comparison sees nothing.  Here the deletion is committed on a branch and
    the check must still find it by consulting the integration base."""
    import tempfile
    global REPO
    saved = REPO
    try:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "docs" / "planning").mkdir(parents=True)
            (root / "docs" / "planning" / "XX_PLAN.md").write_text(CLEAN, encoding="utf-8")
            (root / "CLAUDE.md").write_text("scheduled at XX0.2\n", encoding="utf-8")
            git = lambda *a: subprocess.run(["git", *a], cwd=root, capture_output=True, check=True)
            git("init", "-q", "-b", "main")
            git("config", "user.email", "gate@example.invalid")
            git("config", "user.name", "gate")
            git("add", "-A"); git("commit", "-qm", "plan and citation")
            git("checkout", "-q", "-b", "topic")
            git("rm", "-q", "docs/planning/XX_PLAN.md")
            git("commit", "-qm", "delete the plan, keep the citation")
            REPO = root
            os.environ["SELE4N_PLAN_BASE_REF"] = "main"
            errs = deleted_plan_errors({"CLAUDE.md": (root / "CLAUDE.md").read_text()})
            hit = any("cites XX0.2" in e for e in errs)
            return ("a COMMITTED plan deletion is caught, not just a staged one",
                    hit, errs)
    finally:
        REPO = saved
        os.environ.pop("SELE4N_PLAN_BASE_REF", None)


def _deleted_plan_case():
    """Build a real repository, stage the plan's deletion, and require the
    outstanding citation to be reported."""
    import tempfile
    global REPO
    saved = REPO
    try:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "docs" / "planning").mkdir(parents=True)
            (root / "docs" / "planning" / "XX_PLAN.md").write_text(CLEAN, encoding="utf-8")
            (root / "CLAUDE.md").write_text("the work is scheduled at XX0.2\n", encoding="utf-8")
            git = lambda *a: subprocess.run(["git", *a], cwd=root, capture_output=True, check=True)
            git("init", "-q")
            git("config", "user.email", "gate@example.invalid")
            git("config", "user.name", "gate")
            git("add", "-A")
            git("commit", "-qm", "plan and a citation of it")
            git("rm", "-q", "--cached", "docs/planning/XX_PLAN.md")
            REPO = root
            errs = deleted_plan_errors({"CLAUDE.md": (root / "CLAUDE.md").read_text()})
            hit = any("cites XX0.2" in e and "deletes docs/planning/XX_PLAN.md" in e
                      for e in errs)
            return ("deleting a plan that is still cited is rejected", hit, errs)
    finally:
        REPO = saved


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

    # The deleted-plan case, which the first version of this gate missed: it
    # globbed the working tree, so a plan staged for deletion vanished from
    # discovery and every citation to it passed unchecked.  Witnessed against a
    # throwaway repository, because the defect was in how plans are
    # *enumerated* -- a fixture string cannot exercise that.
    cases.append(_deleted_plan_case())
    cases.append(_committed_deletion_case())
    cases.extend(_archive_and_reprefix_cases())
    cases.extend(_cli_cases())

    # Fenced blocks illustrate; they do not declare.  Both directions matter:
    # an example must not fail a legitimate plan, and blanking fences must not
    # blind the gate to a real defect sitting outside one.
    fenced = CLEAN + "\n```\nsee XX9.9, and a row like\n| XX3.1 | fenced | a | S |\n```\n"
    ferrs = check_plan("plan.md", fenced, {})
    cases.append(("an example inside a code fence is not parsed as data",
                  ferrs == [], ferrs))
    still = check_plan("plan.md",
                       fenced.replace("| XX0 | first | 3 |", "| XX0 | first | 42 |"), {})
    cases.append(("a real defect outside a fence is still caught",
                  any("phase map says XX0 has 42" in e for e in still), still))

    # A phase listed twice must be reported, not collapsed by the assignment.
    dup = CLEAN.replace("| XX1 | second | 2 |", "| XX1 | second | 2 |\n| XX1 | second again | 9 |")
    derrs = check_plan("plan.md", dup, {})
    cases.append(("a duplicated phase-map row is rejected",
                  any("appears twice in the phase map" in e for e in derrs), derrs))

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
