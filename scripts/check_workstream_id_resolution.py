#!/usr/bin/env python3
"""Every workstream ID that kernel code cites resolves to the plan defining it.

`SeLe4n/`, `Main.lean`, `tests/` and `rust/` may not name `docs/dev_history/`
(Tier 0), so they cite a closed plan by its workstream ID (`WS-OD`,
`WS-SM SM6.C`, `WS-H12b`).  That holds only while something live maps the ID
back to a file.  The *Archived plans by ID* section of
`docs/agent_guide/WORKSTREAM_CONTEXT.md` is that map, and a plan archived
without a row there turns every citation of it into a dead end.

**A citation resolves at the level it is written.**

* `WS-RA`, with no phase, resolves when a lookup row, the `# ` title of a live
  plan in `docs/planning/` or `docs/audits/`, or a `## WS-` section of
  `docs/REGISTERED_DEBT.md` names the workstream.
* `WS-SM SM6.C`, with a phase token, first picks its plan.  The lookup row
  whose ID is the longest prefix of the token wins (`WS-SM SM6`; never
  `WS-SM SM1` for `SM10`), so where a workstream's rows split by phase the
  phase picks the row.  With no such row, the candidates are the workstream's
  phase-free rows and the live plans titled with it.  The token's **phase key**
  (`SM6`, `R4`, `RA.B`) must be defined by a candidate.  Where that plan
  numbers the phase's sub-tasks in the flat form `check_workstream_plan.py`
  reads (`| HP1.2 |`), a flat token (`HP1.4`), or each end of a flat range
  (`RR6.12-RR6.14`), must be one of them as well.
* `WS-H12b`, `WS-J1-D`, `WS-K-F5`, with a suffix on the code, must be defined
  whole by a plan its row picks, by the same longest-prefix rule.
* A lookup row's own phase or suffix is held to the same rule against the
  plans that row links.  A row is a claim about its plan, not a definition, so
  `WS-QA QA99` linking a plan that defines only `QA1` fails, and so does every
  citation it would have vouched for.  A family-only row claims no phase.

"Defined" is structural: a token of a heading, a token of a table row's first
cell, a flat sub-task row, or an ancestor of one (`SM9.A` of `SM9.A.1`).  It is
read with fenced blocks blanked by `check_workstream_plan.prose_view`, which
follows CommonMark's fence rules (indented, tilde and longer-closer fences
included), and it uses that gate's `SUBTASK_ROW`, so the two gates read a row
the same way.  A mention in prose or an example in a fence does not define.

Letter-group plans (`SM9.A.1`) are held to the phase key, not the whole token.
They define sub-tasks through ranges (`SM9.A.6-.A.13`), `(a–f)` suffixes and
prose, which no structural reading enumerates.

A citation the gate cannot place fails; nothing defaults to a pass.  A phase
token wrapped onto the next comment line is read with its citation.  The trees
are the ones Tier 0 forbids `docs/dev_history/` in: they must cite by ID.
`scripts/` and `docs/` may cite a path, and `scripts/` also holds gate fixtures
and placeholders (`WS-XX`) that name no workstream.

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
from check_workstream_plan import SUBTASK_ROW, prose_view  # noqa: E402
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

_PHASE_TOKEN = (r"[A-Z]+(?:\d+|\.[A-Z])(?:[.\-][A-Za-z0-9]+)*"
                r"(?:\.\.[A-Z]+\d+(?:\.\d+)*)?")
CITE_RE = re.compile(
    r"\bWS-(?P<fam>[A-Z]+)"
    r"(?P<att>(?:\d+[a-z]?)?(?:-[A-Z]+\d*[a-z]?|-\d+)*)"
    r"(?:[ \t]+(?P<tok>" + _PHASE_TOKEN + r"))?")
# The line a wrapped phase token continues on, after its comment leader.
CONTINUATION_RE = re.compile(
    r"^\s*(?:--|//[/!]?|#|\*|/--?|/-!)?\s*(?P<tok>" + _PHASE_TOKEN + r")")
FAMILY_RE = re.compile(r"\bWS-([A-Z]+)")
PHASE_KEY_RE = re.compile(r"[A-Z]+(?:\d+|\.[A-Z]+)")
FLAT_ID_RE = re.compile(r"[A-Z]+\d+(?:\.\d+)+")
RANGE_RE = re.compile(r"([A-Z]+\d+(?:\.\d+)+)(?:-|\.\.)([A-Z]+\d+(?:\.\d+)+)")
TOKEN_RE = re.compile(r"[A-Za-z0-9](?:[A-Za-z0-9.\-]*[A-Za-z0-9])?")
HEADING_RE = re.compile(r"^(#{1,6})\s+(.*?)\s*$")
FIRST_CELL_RE = re.compile(r"^\|([^|]*)\|")
LINK_RE = re.compile(r"\]\(([^)#\s]+)(?:#[^)]*)?\)")
SEPARATOR_RE = re.compile(r"^\|[\s:|-]+\|$")
REGISTER_SECTION_RE = re.compile(r"^##\s+WS-([A-Z]+)\b", re.M)


class GateError(Exception):
    """The derivation produced no answer, so the gate fails instead of passing."""


def citations_in(line: str, next_line: str = "") -> list[tuple[str, str, str]]:
    """`(family, key, kind)` for each citation on `line`.

    `kind` is `family` (`WS-RA`, key empty), `phase` (`WS-SM SM6.C`, key the
    token) or `suffix` (`WS-H12b`, key `H12b`).  A citation ending the line
    takes its phase token from the start of `next_line`, after a comment leader.
    """
    out = []
    for m in CITE_RE.finditer(line):
        fam, att, tok = m.group("fam"), m.group("att"), m.group("tok")
        if not att and not tok and not line[m.end():].strip():
            cont = CONTINUATION_RE.match(next_line)
            tok = cont.group("tok") if cont else None
        if att:
            out.append((fam, fam + att, "suffix"))
        elif tok:
            out.append((fam, tok.rstrip(".-"), "phase"))
        else:
            out.append((fam, "", "family"))
    return out


def cited(texts: dict[str, str]) -> dict[tuple[str, str, str], list[str]]:
    """Each distinct citation, with its sites as `path:line`."""
    sites: dict[tuple[str, str, str], list[str]] = {}
    for path in sorted(texts):
        lines = texts[path].splitlines()
        for i, line in enumerate(lines):
            following = lines[i + 1] if i + 1 < len(lines) else ""
            for cite in dict.fromkeys(citations_in(line, following)):
                sites.setdefault(cite, []).append(f"{path}:{i + 1}")
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


def lookup_rows(text: str, indexed: set[str]):
    """`(ids, plans)` per lookup row whose plan exists, and the broken rows.

    `ids` are the row's first-cell citations, parsed as source is parsed, so a
    row and a citation compare on the same key.
    """
    rows: list[tuple[list[tuple[str, str, str]], list[str]]] = []
    problems: list[str] = []
    for line in lookup_section(text):
        row = line.strip()
        if not row.startswith("|") or SEPARATOR_RE.match(row):
            continue
        first = row.strip("|").split("|", 1)[0].strip()
        if first == "ID":
            continue
        ids = citations_in(first)
        plans = [
            posixpath.normpath(posixpath.join(posixpath.dirname(LOOKUP_DOC), t))
            for t in LINK_RE.findall(row)
        ]
        plans = [p for p in plans if p in indexed]
        if not ids:
            problems.append(f"lookup row names no workstream: {row[:90]}")
        elif not plans:
            problems.append(f"lookup row for {first} links no plan the index holds")
        else:
            rows.append((ids, plans))
    if not rows and not problems:
        raise GateError(f"{LOOKUP_DOC}: '{LOOKUP_HEADING}' has no table rows")
    return rows, problems


def live_titles(texts: dict[str, str], plan_paths: list[str]) -> dict[str, list[str]]:
    """Each workstream named by a live plan's `# ` title, with those plans."""
    titled: dict[str, list[str]] = {}
    for path in plan_paths:
        for line in texts.get(path, "").splitlines():
            if line.startswith("# "):
                for fam in dict.fromkeys(FAMILY_RE.findall(line)):
                    titled.setdefault(fam, []).append(path)
                break
    return titled


def defined_ids(text: str) -> tuple[set[str], set[str]]:
    """The IDs a plan defines structurally, and its flat sub-task rows."""
    view = prose_view(text)
    found: set[str] = set()
    for line in view.splitlines():
        heading = HEADING_RE.match(line)
        cell = FIRST_CELL_RE.match(line) if not heading else None
        source = heading.group(2) if heading else cell.group(1) if cell else None
        if source is None:
            continue
        for token in TOKEN_RE.findall(source):
            found.add(token)
            if token.startswith("WS-"):
                found.add(token[3:])
    rows = {f"{m.group(1)}.{m.group(2)}" for m in SUBTASK_ROW.finditer(view)}
    found |= rows
    for token in list(found):
        parts = token.split(".")
        found.update(".".join(parts[:k]) for k in range(1, len(parts)))
    return found, rows


def _within(prefix: str, key: str) -> bool:
    """`key` is `prefix` or extends it past a non-alphanumeric boundary."""
    return key == prefix or (key.startswith(prefix) and not key[len(prefix)].isalnum())


class Resolver:
    """Answers one citation against the lookup rows, live titles and register."""

    def __init__(self, rows, titled, sections, texts):
        self.rows, self.titled, self.sections, self.texts = rows, titled, sections, texts
        self._defined: dict[str, tuple[set[str], set[str]]] = {}

    def defined(self, path: str) -> tuple[set[str], set[str]]:
        if path not in self._defined:
            self._defined[path] = defined_ids(self.texts[path])
        return self._defined[path]

    def candidates(self, fam: str, key: str) -> list[str]:
        """The plans a citation reads: its longest-prefix row, else the rest."""
        best, best_len = None, -1
        for ids, plans in self.rows:
            for row_fam, row_key, _ in ids:
                if row_fam == fam and row_key and key and _within(row_key, key):
                    if len(row_key) > best_len:
                        best, best_len = plans, len(row_key)
        if best is not None:
            return best
        free = [p for ids, plans in self.rows
                for row_fam, row_key, _ in ids if row_fam == fam and not row_key
                for p in plans]
        return list(dict.fromkeys(free + self.titled.get(fam, [])))

    def error(self, fam: str, key: str, kind: str) -> str | None:
        """Why the citation does not resolve, or None when it does."""
        named = any(row_fam == fam for ids, _ in self.rows for row_fam, _, _ in ids)
        if kind == "family":
            if named or fam in self.titled or fam in self.sections:
                return None
            return "names no lookup row, live plan title or register section"
        plans = self.candidates(fam, key)
        if not plans:
            return "resolves to no plan: no lookup row and no live plan title"
        return self.undefined(key, kind, plans)

    def row_errors(self) -> list[str]:
        """Each lookup row ID that the plans its row links do not define.

        A row is a claim about its plan, not a definition: `WS-QA QA99` linking
        a plan that numbers only `QA1` is as dead as the citation it would
        otherwise vouch for.  A family-only row (`WS-OD`) claims no phase.
        """
        out = []
        for ids, plans in self.rows:
            for fam, key, kind in ids:
                why = self.undefined(key, kind, plans) if key else None
                if why:
                    shown = f"WS-{fam} {key}" if kind == "phase" else f"WS-{key}"
                    out.append(f"lookup row {shown}: {why}")
        return out

    def undefined(self, key: str, kind: str, plans: list[str]) -> str | None:
        """Why none of `plans` defines `key` at its level, or None when one does."""
        names = ", ".join(posixpath.basename(p) for p in plans)
        if kind == "suffix":
            if any(key in self.defined(p)[0] for p in plans):
                return None
            return f"{key} is defined by none of {names}"
        phase = PHASE_KEY_RE.match(key)
        holders = [p for p in plans if phase and phase.group(0) in self.defined(p)[0]]
        if not holders:
            return f"phase {phase.group(0) if phase else key} is defined by none of {names}"
        ends = RANGE_RE.fullmatch(key)
        flat = [e for e in (ends.groups() if ends else (key,)) if FLAT_ID_RE.fullmatch(e)]
        for end in flat:
            enumerating = [p for p in holders
                           if any(r.startswith(phase.group(0) + ".")
                                  for r in self.defined(p)[1])]
            if enumerating and not any(end in self.defined(p)[0] for p in enumerating):
                return (f"{end} is not a sub-task row of "
                        f"{', '.join(posixpath.basename(p) for p in enumerating)}")
        return None


def check(repo: str) -> int:
    """0 when every citation resolves at its own level, 1 otherwise."""
    code = indexed_contents(repo, listed_at(repo, ":", *CODE_TREES))
    sites = cited(code)
    if not sites:
        raise GateError(f"no WS- citation in {', '.join(CODE_TREES)}")

    indexed = set(listed_at(repo, ":"))
    lookup = indexed_contents(repo, [LOOKUP_DOC, REGISTER])
    if LOOKUP_DOC not in lookup:
        raise GateError(f"{LOOKUP_DOC}: not in the index")
    if REGISTER not in lookup:
        raise GateError(f"{REGISTER}: not in the index")
    rows, problems = lookup_rows(lookup[LOOKUP_DOC], indexed)
    plan_paths = sorted(p for p in indexed
                        if posixpath.dirname(p) in LIVE_PLAN_DIRS and p.endswith(".md"))
    linked = sorted({p for _, plans in rows for p in plans})
    texts = indexed_contents(repo, sorted(set(plan_paths) | set(linked)))
    missing = [p for p in linked if p not in texts]
    if missing:
        raise GateError(f"linked plan(s) not readable from the index: {', '.join(missing)}")
    resolver = Resolver(rows, live_titles(texts, plan_paths),
                        set(REGISTER_SECTION_RE.findall(lookup[REGISTER])), texts)
    problems += resolver.row_errors()

    failures = []
    for (fam, key, kind), where in sorted(sites.items()):
        why = resolver.error(fam, key, kind)
        if why:
            more = f" (+{len(where) - 3} more)" if len(where) > 3 else ""
            shown = f"WS-{fam} {key}" if kind == "phase" else f"WS-{key or fam}"
            failures.append(f"FAIL: {shown}, cited at {', '.join(where[:3])}{more}: {why}")
    for problem in problems:
        print(f"FAIL: {LOOKUP_DOC}: {problem}")
    for failure in failures:
        print(failure)
    if problems or failures:
        print(f"Fix the citation, or give its plan a row in '{LOOKUP_HEADING}' "
              f"({LOOKUP_DOC}).")
        return 1
    with_id = sum(1 for _, key, _ in sites if key)
    families = len({fam for fam, _, _ in sites})
    keyed = sum(1 for ids, _ in rows for _, key, _ in ids if key)
    print(f"PASS: {len(sites)} distinct workstream citations ({families} workstreams) "
          f"in {', '.join(CODE_TREES)} resolve; {with_id} carry a phase or suffix "
          f"and resolve at that level; the {keyed} lookup row IDs with one are "
          "defined by the plans their rows link")
    return 0


_ROW_QA1 = "| WS-QA QA1 | [`QA1.md`](../dev_history/planning/QA1.md) |\n"
_ROW_QA2 = "| WS-QA QA2 | [`QA2.md`](../dev_history/planning/QA2.md) |\n"
_FIXTURE_CONTEXT = (
    "# Context\n\n#### Archived plans by ID\n\n| ID | Archived plan |\n"
    "|----|---------------|\n" + _ROW_QA1 + _ROW_QA2 +
    "| WS-QH | [`QH.md`](../dev_history/audits/QH.md) |\n"
    "| WS-QJ1 | [`QJ.md`](../dev_history/audits/QJ.md) |\n\n"
    "##### Audit-era workstreams\n\n| ID | Archived plan |\n|----|----|\n"
    "| WS-QE | [`QE.md`](../dev_history/audits/QE.md) |\n\n"
    "### WS-QF, the next section\n\n"
    "| WS-QG | [`QG.md`](../dev_history/planning/QG.md) |\n")
_CITES = ("-- WS-QA QA1.2, WS-QA QA2.C, WS-QB QB1.2, WS-QC, WS-QE, WS-QH12b\n"
          "-- WS-QJ1-D, and RR-style ranges: WS-QA QA1.1-QA1.2; wrapped: WS-QA\n"
          "-- QA2.C.4 continues here\n")
_FIXTURE = {
    LOOKUP_DOC: _FIXTURE_CONTEXT,
    "docs/dev_history/planning/QA1.md": "# QA one\n\n## QA1\n\n| QA1.1 | a |\n| QA1.2 | b |\n",
    "docs/dev_history/planning/QA2.md": "# QA two\n\n## QA2\n\n| QA2.C.4 | legacy |\n",
    "docs/dev_history/audits/QH.md": "# QH\n\n### WS-QH12b — a sub-workstream\n",
    "docs/dev_history/audits/QJ.md": ("# QJ\n\n## WS-QJ1 — a workstream\n\n"
                                      "### WS-QJ1-D — a sub-workstream\n"),
    "docs/dev_history/audits/QE.md": "# QE\n",
    "docs/dev_history/planning/QG.md": "# QG\n",
    "docs/planning/LIVE.md": ("# WS-QB — a live plan\n\nQB7 is named in prose.\n\n"
                              "```\n## QB5\n```\n\n| QB1.1 | x |\n| QB1.2 | y |\n"),
    REGISTER: "# Register\n\n## WS-QC — a register section\n",
    "SeLe4n/A.lean": _CITES,
    "scripts/x.sh": "# WS-ZZ, WS-QA QA99: scripts/ is outside the scope\n",
}


def _with_cite(extra: str) -> dict[str, str]:
    return {"SeLe4n/A.lean": _CITES + extra}


def _with_row(row: str, extra: str = "") -> dict[str, str]:
    """The fixture with one more lookup row, and `extra` cited."""
    return {LOOKUP_DOC: _FIXTURE_CONTEXT.replace(_ROW_QA2, _ROW_QA2 + row),
            **(_with_cite(extra) if extra else {})}


_ROW_QA99 = "| WS-QA QA99 | [`QA99.md`](../dev_history/planning/QA99.md) |\n"
_FAKE_QA99 = "## QA99\n\n| QA99.1 | a |\n"


def _qa99_plan(body: str) -> dict[str, str]:
    """A `WS-QA QA99` row whose plan is `body`, cited as a phase and a sub-task."""
    return {**_with_row(_ROW_QA99, "-- WS-QA QA99, WS-QA QA99.1\n"),
            "docs/dev_history/planning/QA99.md": "# QA ninety-nine\n\n" + body}


def _run_fixture(files: dict[str, str | None]) -> tuple[int, str]:
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
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            try:
                return check(td), out.getvalue()
            except GateError as err:
                return 2, str(err)


def _self_test() -> int:
    """Break each relation the gate stands for, keeping the tokens in place.

    Each case asserts the verdict and the message: a case that fails for an
    unrelated reason would otherwise pass as a witness.
    """
    swapped = (_FIXTURE_CONTEXT.replace(_ROW_QA1, "@1").replace(_ROW_QA2, "@2")
               .replace("@1", _ROW_QA1.replace("QA1.md", "QA2.md"))
               .replace("@2", _ROW_QA2.replace("QA2.md", "QA1.md")))
    cases = [
        ("baseline: rows, phases, suffixes, ranges, a wrap, a live plan", {}, 0,
         "PASS: 9 distinct"),
        ("a phase the workstream does not have (WS-QA QA99)",
         _with_cite("-- WS-QA QA99\n"), 1, "WS-QA QA99, cited at SeLe4n/A.lean:4: resolves to no plan"),
        ("a numeric suffix no row covers (WS-QJ999)", _with_cite("-- WS-QJ999\n"), 1,
         "WS-QJ999, cited at SeLe4n/A.lean:4: resolves to no plan"),
        ("a letter suffix the plan does not define (WS-QH12z)",
         _with_cite("-- WS-QH12z\n"), 1, "QH12z is defined by none of QH.md"),
        ("a flat sub-task the archived plan does not number (QA1.9)",
         _with_cite("-- WS-QA QA1.9\n"), 1, "QA1.9 is not a sub-task row of QA1.md"),
        ("a flat sub-task the live plan does not number (QB1.9)",
         _with_cite("-- WS-QB QB1.9\n"), 1, "QB1.9 is not a sub-task row of LIVE.md"),
        ("a range whose far end is not a row", _with_cite("-- WS-QA QA1.1-QA1.9\n"), 1,
         "QA1.9 is not a sub-task row of QA1.md"),
        ("each phase resolved in the other row's plan", {LOOKUP_DOC: swapped}, 1,
         "WS-QA QA1.2, cited at SeLe4n/A.lean:1: phase QA1 is defined by none of QA2.md"),
        ("a phase named only in prose", _with_cite("-- WS-QB QB7\n"), 1, "phase QB7 is defined by none"),
        ("a phase named only inside a fence", _with_cite("-- WS-QB QB5\n"), 1, "phase QB5 is defined by none"),
        ("a bad phase wrapped onto the next line",
         _with_cite("-- see WS-QA\n-- QA99 here\n"), 1, "WS-QA QA99, cited at SeLe4n/A.lean:4"),
        ("a row naming a phase its plan lacks (WS-QA QA99 linking QA1.md)",
         _with_row(_ROW_QA1.replace("WS-QA QA1", "WS-QA QA99"), "-- WS-QA QA99\n"), 1,
         "WS-QA QA99, cited at SeLe4n/A.lean:4: phase QA99 is defined by none of QA1.md"),
        ("that row fails with nothing cited through it",
         _with_row(_ROW_QA1.replace("WS-QA QA1", "WS-QA QA99")), 1,
         "lookup row WS-QA QA99: phase QA99 is defined by none of QA1.md"),
        ("a row naming a suffix its plan lacks (WS-QJ999 linking QJ.md)",
         _with_row("| WS-QJ999 | [`QJ.md`](../dev_history/audits/QJ.md) |\n", "-- WS-QJ999\n"),
         1, "WS-QJ999, cited at SeLe4n/A.lean:4: QJ999 is defined by none of QJ.md"),
        ("control: the QA99 plan defining QA99 and QA99.1 in the open",
         _qa99_plan(_FAKE_QA99), 0, "PASS: 11 distinct"),
        ("QA99 defined only inside an indented fence",
         _qa99_plan("  ```\n" + _FAKE_QA99 + "  ```\n"), 1,
         "WS-QA QA99, cited at SeLe4n/A.lean:4: phase QA99 is defined by none of QA99.md"),
        ("QA99 defined only inside a tilde fence",
         _qa99_plan("~~~\n" + _FAKE_QA99 + "~~~\n"), 1,
         "WS-QA QA99, cited at SeLe4n/A.lean:4: phase QA99 is defined by none of QA99.md"),
        ("QA99 defined only past a shorter run, inside a fence a longer run closes",
         _qa99_plan("````\n```\n" + _FAKE_QA99 + "`````\n"), 1,
         "WS-QA QA99, cited at SeLe4n/A.lean:4: phase QA99 is defined by none of QA99.md"),
        ("control: QA99 defined after that longer closer",
         _qa99_plan("````\n```\n`````\n" + _FAKE_QA99), 0, "PASS: 11 distinct"),
        ("an unlisted workstream", _with_cite("-- WS-QD\n"), 1, "WS-QD, cited at"),
        ("a row below the section's end", _with_cite("-- WS-QG\n"), 1, "WS-QG, cited at"),
        ("a row whose plan the index lacks",
         {"docs/dev_history/planning/QA1.md": None}, 1,
         "lookup row for WS-QA QA1 links no plan the index holds"),
        ("a row naming no workstream",
         {LOOKUP_DOC: _FIXTURE_CONTEXT.replace(
             _ROW_QA1, _ROW_QA1 + _ROW_QA1.replace("WS-QA QA1", "QA1"))}, 1,
         "lookup row names no workstream"),
        ("a live plan naming the workstream in its body, not its title",
         {"docs/planning/LIVE.md": "# A live plan\n\nWS-QB\n\n| QB1.2 | y |\n"}, 1,
         "WS-QB QB1.2, cited at SeLe4n/A.lean:1: resolves to no plan"),
        ("a register mention that is not a section",
         {REGISTER: "# Register\n\n| **WS-QC** | v1 |\n"}, 1,
         "WS-QC, cited at SeLe4n/A.lean:1: names no lookup row"),
        ("no citation at all", {"SeLe4n/A.lean": "-- none\n"}, 2, "no WS- citation"),
        ("no lookup heading",
         {LOOKUP_DOC: _FIXTURE_CONTEXT.replace("Archived plans by ID", "Plans")}, 2,
         "no 'Archived plans by ID' heading"),
    ]
    failed = 0
    for name, edits, want, message in cases:
        got, out = _run_fixture({**_FIXTURE, **edits})
        ok = got == want and message in out
        failed += not ok
        print(f"{'ok  ' if ok else 'FAIL'} {name}: exit {got}, want {want}")
        if not ok:
            print(f"     wanted message {message!r}; got:\n{out}")
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
