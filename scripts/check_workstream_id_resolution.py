#!/usr/bin/env python3
"""Every workstream that kernel code cites resolves to a plan a reader can open.

`SeLe4n/`, `Main.lean`, `tests/` and `rust/` may not name `docs/dev_history/`
(Tier 0), so they cite a closed plan by its workstream ID (`WS-OD`,
`WS-SM SM6.C`, `WS-H12b`).  That holds only while something live maps the ID
back to a file.  The *Archived plans by ID* section of
`docs/agent_guide/WORKSTREAM_CONTEXT.md` is that map, and a plan archived
without a row there turns every citation of it into a dead end.  This gate
derives the cited workstreams from those trees and fails when one resolves to
none of:

* a row of the *Archived plans by ID* section whose linked plan exists;
* the `# ` title of a live plan in `docs/planning/` or `docs/audits/`;
* a `## WS-` section of `docs/REGISTERED_DEBT.md` (WS-SL, WS-IN, WS-AP and
  WS-XV keep their plan there).

**The unit is the workstream family, not the phase.**  A family is the capital
run after `WS-`: `WS-H12b` is H, `WS-J1-D` is J, `WS-K-F5` is K, and
`WS-SM SM6.C` is SM.  A phase-level answer is not well defined: WS-SM and
WS-RC each have a live plan that covers every phase, beside archived plans for
single phases, so whether `WS-RC R4` "resolves" would depend on which of the
two counts.  The family-level question has one answer.

The trees are the ones Tier 0 forbids `docs/dev_history/` in, for the reason
that gate gives: they must cite by ID.  `scripts/` and `docs/` may cite a path,
and `scripts/` also holds gate fixtures and placeholders (`WS-XX`) that name no
workstream.

Everything is read from the git index, as every Tier 0 scanner reads it.  A
derivation that finds no citation, no lookup section or no lookup row fails
instead of passing over an empty domain.
"""

from __future__ import annotations

import os
import posixpath
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from indexed_source import (  # noqa: E402  (needs the path insert above)
    DerivationFailed,
    indexed_contents,
    listed_at,
)

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CODE_TREES = ("SeLe4n", "Main.lean", "tests", "rust")
LOOKUP_DOC = "docs/agent_guide/WORKSTREAM_CONTEXT.md"
LOOKUP_HEADING = "Archived plans by ID"
REGISTER = "docs/REGISTERED_DEBT.md"
LIVE_PLAN_DIRS = ("docs/planning", "docs/audits")

FAMILY_RE = re.compile(r"\bWS-([A-Z]+)")
HEADING_RE = re.compile(r"^(#{1,6})\s+(.*?)\s*$")
LINK_RE = re.compile(r"\]\(([^)#\s]+)(?:#[^)]*)?\)")
SEPARATOR_RE = re.compile(r"^\|[\s:|-]+\|$")
REGISTER_SECTION_RE = re.compile(r"^##\s+WS-([A-Z]+)\b", re.M)


class GateError(Exception):
    """The derivation produced no answer, so the gate fails instead of passing."""


def cited_families(texts: dict[str, str]) -> dict[str, list[str]]:
    """Each cited family, with its citation sites as `path:line`."""
    sites: dict[str, list[str]] = {}
    for path in sorted(texts):
        for lineno, line in enumerate(texts[path].splitlines(), 1):
            for family in sorted(set(FAMILY_RE.findall(line))):
                sites.setdefault(family, []).append(f"{path}:{lineno}")
    return sites


def lookup_section(text: str) -> list[str]:
    """The section's lines, up to the next heading at its own level or above."""
    lines = text.splitlines()
    start = level = None
    for i, line in enumerate(lines):
        match = HEADING_RE.match(line)
        if not match:
            continue
        if start is None:
            if match.group(2) == LOOKUP_HEADING:
                start, level = i + 1, len(match.group(1))
        elif len(match.group(1)) <= level:
            return lines[start:i]
    if start is None:
        raise GateError(f"{LOOKUP_DOC}: no '{LOOKUP_HEADING}' heading")
    return lines[start:]


def lookup_families(text: str, indexed: set[str]) -> tuple[set[str], list[str]]:
    """Families named by a lookup row whose plan exists, and the broken rows."""
    families: set[str] = set()
    problems: list[str] = []
    rows = 0
    for line in lookup_section(text):
        row = line.strip()
        if not row.startswith("|") or SEPARATOR_RE.match(row):
            continue
        first = row.strip("|").split("|", 1)[0].strip()
        if first == "ID":
            continue
        rows += 1
        ids = FAMILY_RE.findall(first)
        targets = {
            posixpath.normpath(posixpath.join(posixpath.dirname(LOOKUP_DOC), t))
            for t in LINK_RE.findall(row)
        }
        if not ids:
            problems.append(f"lookup row names no workstream: {row[:90]}")
        elif not targets & indexed:
            problems.append(f"lookup row for {first} links no plan the index holds")
        else:
            families.update(ids)
    if rows == 0:
        raise GateError(f"{LOOKUP_DOC}: '{LOOKUP_HEADING}' has no table rows")
    return families, problems


def live_families(texts: dict[str, str], plan_paths: list[str]) -> set[str]:
    """Families named by a live plan's title or by a register section."""
    families: set[str] = set()
    for path in plan_paths:
        for line in texts.get(path, "").splitlines():
            if line.startswith("# "):
                families.update(FAMILY_RE.findall(line))
                break
    if REGISTER not in texts:
        raise GateError(f"{REGISTER}: not in the index")
    families.update(REGISTER_SECTION_RE.findall(texts[REGISTER]))
    return families


def check(repo: str) -> int:
    """0 when every cited family resolves, 1 otherwise."""
    code_paths = listed_at(repo, ":", *CODE_TREES)
    code = indexed_contents(repo, code_paths)
    cited = cited_families(code)
    if not cited:
        raise GateError(f"no WS- citation in {', '.join(CODE_TREES)}")

    indexed = set(listed_at(repo, ":", "docs"))
    plan_paths = sorted(
        p for p in indexed
        if posixpath.dirname(p) in LIVE_PLAN_DIRS and p.endswith(".md")
    )
    docs = indexed_contents(repo, [LOOKUP_DOC, REGISTER, *plan_paths])
    if LOOKUP_DOC not in docs:
        raise GateError(f"{LOOKUP_DOC}: not in the index")
    archived, problems = lookup_families(docs[LOOKUP_DOC], indexed)
    live = live_families(docs, plan_paths)

    unresolved = sorted(set(cited) - archived - live)
    for problem in problems:
        print(f"FAIL: {LOOKUP_DOC}: {problem}")
    for family in unresolved:
        sites = cited[family]
        more = f" (+{len(sites) - 3} more)" if len(sites) > 3 else ""
        print(f"FAIL: WS-{family}, cited at {', '.join(sites[:3])}{more}, "
              "resolves to no lookup row, live plan title or register section")
    if problems or unresolved:
        print(f"Add the plan to '{LOOKUP_HEADING}' in {LOOKUP_DOC}.")
        return 1
    print(f"PASS: {len(cited)} workstream families cited in "
          f"{', '.join(CODE_TREES)}; each resolves "
          f"({len(set(cited) & archived)} through the archived-plan lookup)")
    return 0


_FIXTURE_CONTEXT = """# Context

#### Archived plans by ID

| ID | Archived plan |
|----|---------------|
| WS-QA | [`QA.md`](../dev_history/planning/QA.md) |

##### Audit-era workstreams

| ID | Archived plan |
|----|---------------|
| WS-QE | [`QE.md`](../dev_history/audits/QE.md) |

### WS-QF, the next section

| WS-QG | [`QG.md`](../dev_history/planning/QG.md) |
"""

_FIXTURE = {
    LOOKUP_DOC: _FIXTURE_CONTEXT,
    "docs/dev_history/planning/QA.md": "# QA\n",
    "docs/dev_history/audits/QE.md": "# QE\n",
    "docs/dev_history/planning/QG.md": "# QG\n",
    "docs/planning/LIVE.md": "# WS-QB — a live plan\n",
    REGISTER: "# Register\n\n## WS-QC — a register section\n",
    "SeLe4n/A.lean": "-- WS-QA, WS-QB QB2.C, WS-QC, WS-QE12b-x\n",
    "scripts/x.sh": "# WS-ZZ: scripts/ is outside the scope\n",
}


def _run_fixture(files: dict[str, str | None]) -> int:
    import contextlib
    import io
    import tempfile

    with tempfile.TemporaryDirectory() as td:
        for path, text in files.items():
            if text is None:
                continue
            full = os.path.join(td, path)
            os.makedirs(os.path.dirname(full), exist_ok=True)
            with open(full, "w", encoding="utf-8") as handle:
                handle.write(text)
        subprocess.run(["git", "init", "-q", td], check=True)
        subprocess.run(["git", "-C", td, "add", "-A"], check=True)
        with contextlib.redirect_stdout(io.StringIO()):
            try:
                return check(td)
            except GateError:
                return 2


def _self_test() -> int:
    """Break each relation the gate stands for, keeping the tokens in place."""
    in_section_row = "| WS-QA | [`QA.md`](../dev_history/planning/QA.md) |\n"
    cases = [
        ("baseline: lookup row, live title, register section", {}, 0),
        ("an unlisted family", {"SeLe4n/A.lean": "-- WS-QA, WS-QD\n"}, 1),
        ("a row below the section's end", {"SeLe4n/A.lean": "-- WS-QG\n"}, 1),
        ("a row whose plan the index lacks",
         {"docs/dev_history/planning/QA.md": None}, 1),
        ("a row naming no workstream",
         {LOOKUP_DOC: _FIXTURE_CONTEXT.replace(
             in_section_row, in_section_row + in_section_row.replace("WS-QA", "QA"))}, 1),
        ("a family named in a live plan's body, not its title",
         {"docs/planning/LIVE.md": "# A live plan\n\nWS-QB\n"}, 1),
        ("a register mention that is not a section",
         {REGISTER: "# Register\n\n| **WS-QC** | v1 |\n"}, 1),
        ("no citation at all", {"SeLe4n/A.lean": "-- none\n"}, 2),
        ("no lookup heading",
         {LOOKUP_DOC: _FIXTURE_CONTEXT.replace("Archived plans by ID", "Plans")}, 2),
    ]
    failed = 0
    for name, edits, want in cases:
        got = _run_fixture({**_FIXTURE, **edits})
        ok = got == want
        failed += not ok
        print(f"{'ok  ' if ok else 'FAIL'} {name}: exit {got}, want {want}")
    return 1 if failed else 0


def main(argv: list[str]) -> int:
    if argv[1:] == ["--self-test"]:
        return _self_test()
    if argv[1:]:
        print(f"usage: {argv[0]} [--self-test]", file=sys.stderr)
        return 2
    try:
        return check(REPO_ROOT)
    except (GateError, DerivationFailed) as err:
        print(f"FAIL: {err}")
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
