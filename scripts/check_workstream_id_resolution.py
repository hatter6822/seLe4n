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
  (`SM6`, `R4`, `RA.B`) must be defined by a candidate.  Then the token is read
  as a path (`SM5.H.4` is `SM5`, `SM5.H`, `SM5.H.4`; `Z6-A` is `Z6`, `Z6-A`;
  `SM3.D.5b` ends a level below `SM3.D.5`), and at each level the plan
  numbers, the next ID must be one it defines: `SM6.Z` fails where the plan
  numbers SM6's groups, `SM5.H.99` where it numbers SM5.H's sub-tasks.  Each
  end of a range (`RR6.12-RR6.14`, `SM9.A.6-.A.13`, `SM0..SM10`) is read so.
* `WS-H12b`, `WS-J1-D`, `WS-K-F5`, with a suffix on the code, must be defined
  whole by a plan its row picks, by the same longest-prefix rule.
* A lookup row's own phase or suffix is held to the same rule against the
  plans that row links.  A row is a claim about its plan, not a definition, so
  `WS-QA QA99` linking a plan that defines only `QA1` fails, and so does every
  citation it would have vouched for.  A family-only row claims no phase.

* A phase written any other way (`(WS-SM, SM5.H.4)`, `WS-Z/Z6`,
  `WS-SM (SM0.C`, `WS-AB.D2`, `WS-SM phase SM0`, or with the token wrapped
  after the separator) fails as written, because it would otherwise read as the
  bare workstream.  One form is canonical: `WS-SM SM5.H.4`.  A separator that
  ends the citation instead (a closing bracket, a sentence's full stop, the end
  of a comment) leaves the token outside it.

"Defined" is structural: a token of a heading, a token of a table row's first
cell, a sub-task row, any ID on the path of one (`SM9.A` of `SM9.A.1`), or an
ID a range spans.  "Numbered" is narrower: the sub-task rows, and the first ID
of each heading or table row.  A heading that opens on a range or on a
qualified name (`AL6-C.hygiene`) points at rows elsewhere and numbers nothing.

**Depth, by family.**  Every family is checked to the last ID of every
citation, except below a level no plan numbers: a landed plan that folded its
sub-tasks into prose (`SM9.A — 15 sub-tasks — LANDED`) says nothing
structural about which belong there, so `SM9.A.10` is held to `SM9.A`.  Each
such level is pinned in `UNNUMBERED_LEVELS`, so a citation held short of its
last ID at a level not pinned there fails, and so does a pin no citation is
held to.  The pins are WS-SM's SM0 (its letter groups), SM1.F, SM1.G,
SM3.D.5 and SM3.D.6 (their letter parts), SM9.A and SM9.B; WS-RC's R5 (its
letter groups); and WS-AL's AL2, AL6 and AL7 and WS-AM's AM1 and AM4, whose
dash sub-tasks only `CHANGELOG.md` prose records.  Every other phase citation
is checked to its last ID; a suffix citation (`WS-H12b`) is checked whole; a
bare family (`WS-RA`) is checked for a row, a live title or a register section.

Plans are read with fenced blocks blanked by `markdown_prose_view.prose_view`
(CommonMark's fence rules), and with `check_workstream_plan.SUBTASK_ROW`, so
the gates read a row the same way.  A mention in prose or an example in a
fence does not define.

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
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_workstream_plan import SUBTASK_ROW  # noqa: E402
from markdown_prose_view import prose_view  # noqa: E402
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
# The levels a citation may be held to short of its last ID, as `(family,
# level)`: no plan numbers what lies below them.  A pin, not a domain -- the gate
# derives the held levels from the plans and fails on any difference, so a plan
# that drops its sub-task rows, or a citation reaching below a new prose-only
# level, is a failure rather than a quieter check.
UNNUMBERED_LEVELS = frozenset({
    ("SM", "SM0"), ("SM", "SM1.F"), ("SM", "SM1.G"), ("SM", "SM3.D.5"),
    ("SM", "SM3.D.6"), ("SM", "SM9.A"), ("SM", "SM9.B"), ("RC", "R5"),
    ("AL", "AL2"), ("AL", "AL6"), ("AL", "AL7"), ("AM", "AM1"), ("AM", "AM4"),
})

_PHASE_TOKEN = (r"[A-Z]+(?:\d+|\.[A-Z])(?:[.\-][A-Za-z0-9]+)*"
                r"(?:\.\.[A-Z]+\d+(?:\.\d+)*)?")
CITE_RE = re.compile(
    r"\bWS-(?P<fam>[A-Z]+)"
    r"(?P<att>(?:\d+[a-z]?)?(?:-[A-Z]+\d*[a-z]?|-\d+)*)"
    r"(?:[ \t]+(?P<tok>" + _PHASE_TOKEN + r"))?")
# The line a wrapped phase token continues on, after its comment leader.
CONTINUATION_RE = re.compile(
    r"^\s*(?:--|//[/!]?|#|\*|/--?|/-!)?\s*(?P<tok>" + _PHASE_TOKEN + r")")
# A family tag parted from a phase-like token by anything but spaces:
# punctuation (`(WS-SM, SM5.H.4)`, `WS-Z/Z6`, `WS-SM (SM0.C`, `WS-AB.D2`,
# `WS-BP `BP2.6``) or the word `phase` (`WS-SM phase SM0`).  `CITE_RE` would read
# the family alone; this reads the form, so the gate can refuse it.
_SEPARATOR = r"(?:[^\w\s]+|phases?\b)"
PUNCTUATED_RE = re.compile(
    r"\bWS-(?P<fam>[A-Z]+)(?![\w-])"
    r"(?P<sep>[ \t]*" + _SEPARATOR + r"(?:[ \t]*" + _SEPARATOR + r")*[ \t]*)"
    r"(?P<tok>" + _PHASE_TOKEN + r")")
# The same form with the token wrapped onto the next line.
PUNCTUATED_EOL_RE = re.compile(
    r"\bWS-(?P<fam>[A-Z]+)(?![\w-])"
    r"(?P<sep>[ \t]*" + _SEPARATOR + r"(?:[ \t]*" + _SEPARATOR + r")*)[ \t]*$")
# A separator that ends the citation instead: a closing bracket, a full stop
# that ends the sentence, or the end of the comment.  `(see WS-RA) R2.A.1` and
# `deferred to WS-U. -/` then a heading are not the workstream's phases.
CLOSING_RE = re.compile(r"[)\]}]|\.\s|-/|\*/")
FAMILY_RE = re.compile(r"\bWS-([A-Z]+)")
PHASE_KEY_RE = re.compile(r"[A-Z]+(?:\d+|\.[A-Z]+)")
# A range whose far end may be abbreviated: `RR6.12-RR6.14`, `SM9.A.6-.A.13`,
# `SM5.F.1-14`.  Its members are every number between the ends.
SPAN_RE = re.compile(r"(?P<head>[A-Z]+(?:\d+|\.[A-Z]+)(?:\.[A-Z0-9]+)*\.)(?P<lo>\d+)(?:-|\.\.)"
                     r"(?:\.?[A-Z]+\d*(?:\.[A-Z0-9]+)*\.)?(?P<hi>\d+)")
# One step down a path: `.A`, `.4`, `-A`; and a letter after a number (`5b`).
SEGMENT_RE = re.compile(r"\.(?:[A-Z]+(?![a-z])|\d+)|-(?:[A-Z]+|\d+)(?![A-Za-z0-9]|\.[A-Z0-9])")
LETTER_LEVEL_RE = re.compile(r"[a-z](?![A-Za-z])")
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
    token), `suffix` (`WS-H12b`, key `H12b`) or `punctuated` (`(WS-SM, SM5.H.4)`,
    key the text as written).  A citation ending the line takes its phase token
    from the start of `next_line`, after a comment leader.
    """
    out = []
    punctuated = {}
    for m in PUNCTUATED_RE.finditer(line):
        if not CLOSING_RE.search(m.group("sep")):
            punctuated[m.start()] = m.group(0)
    tail = PUNCTUATED_EOL_RE.search(line)
    cont = CONTINUATION_RE.match(next_line)
    if (tail and cont and tail.start() not in punctuated
            and not CLOSING_RE.search(tail.group("sep") + "\n")):
        punctuated[tail.start()] = tail.group(0).rstrip() + " " + cont.group("tok")
    for m in CITE_RE.finditer(line):
        fam, att, tok = m.group("fam"), m.group("att"), m.group("tok")
        if m.start() in punctuated and not att and not tok:
            out.append((fam, punctuated[m.start()], "punctuated"))
            continue
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


def levels(token: str) -> list[str]:
    """The IDs a token names, coarse to fine.

    `SM9.A.4a` is `SM9`, `SM9.A`, `SM9.A.4`, `SM9.A.4a`: a letter after a number
    is one level down (`SM3.D.5b` under `SM3.D.5`).  A lower-case word ends the
    path, so `SM2.C-defer` and `AK7-E.cascade` are qualified, not deeper.
    """
    key = PHASE_KEY_RE.match(token)
    if not key:
        return []
    path, pos = [key.group(0)], key.end()
    while pos < len(token):
        step = ((LETTER_LEVEL_RE.match(token, pos) if path[-1][-1].isdigit() else None)
                or SEGMENT_RE.match(token, pos))
        if not step:
            break
        path.append(path[-1] + step.group(0))
        pos = step.end()
    return path


def span(token: str) -> list[str] | None:
    """Every ID a range token covers (`SM9.A.6-.A.8`), or None for one ID."""
    m = SPAN_RE.fullmatch(token)
    if not m or not 0 <= int(m.group("hi")) - int(m.group("lo")) <= 200:
        return None
    return [m.group("head") + str(n) for n in range(int(m.group("lo")), int(m.group("hi")) + 1)]


def ends(token: str) -> list[str]:
    """The IDs a cited token must each resolve: both ends of a range, else itself."""
    if ".." in token:
        return token.split("..", 1)
    members = span(token)
    return [members[0], members[-1]] if members else [token]


def defined_ids(text: str) -> tuple[set[str], dict[str, set[str]]]:
    """What a plan defines, and the children it numbers under each ID.

    Defined: every token of a heading or of a table row's first cell, each with
    the path of IDs it names (`SM9.A` of `SM9.A.1`) and every ID a range spans;
    and every sub-task row `SUBTASK_ROW` reads.  Numbered: the sub-task rows,
    and the first ID of each heading or table row, or each ID a row's range
    spans.  A heading that opens on a range (`The ABI slice (SM9.A.6-.A.8)`)
    or on a qualified name (`AL6-C.hygiene closure`) points at rows elsewhere
    rather than being a section of its own, so it numbers nothing; nor does a
    qualified name in a row.
    """
    view = prose_view(text)
    found: set[str] = set()
    numbered: dict[str, set[str]] = defaultdict(set)

    def number(child: str) -> None:
        path = levels(child)
        if len(path) > 1:
            numbered[path[-2]].add(path[-1])

    for line in view.splitlines():
        heading = HEADING_RE.match(line)
        cell = FIRST_CELL_RE.match(line) if not heading else None
        source = heading.group(2) if heading else cell.group(1) if cell else None
        if source is None:
            continue
        first = True
        for token in TOKEN_RE.findall(source):
            bare = token[3:] if token.startswith("WS-") else token
            found.update((token, bare))
            members = span(bare)
            for member in members or [bare]:
                found.update(levels(member))
            if first and PHASE_KEY_RE.match(bare):
                first = False
                if members and not heading:
                    for member in members:
                        number(member)
                elif not members and levels(bare)[-1] == bare:
                    number(bare)
    for m in SUBTASK_ROW.finditer(view):
        row = f"{m.group(1)}.{m.group(2)}"
        found.update(levels(row))
        number(row)
    for token in list(found):
        parts = token.split(".")
        found.update(".".join(parts[:k]) for k in range(1, len(parts)))
    return found, numbered


def _within(prefix: str, key: str) -> bool:
    """`key` is `prefix` or extends it past a non-alphanumeric boundary."""
    return key == prefix or (key.startswith(prefix) and not key[len(prefix)].isalnum())


class Resolver:
    """Answers one citation against the lookup rows, live titles and register."""

    def __init__(self, rows, titled, sections, texts, pinned=UNNUMBERED_LEVELS):
        self.rows, self.titled, self.sections, self.texts = rows, titled, sections, texts
        self.pinned = pinned
        # `(family, level)` for each citation held short of its last ID.
        self.held: set[tuple[str, str]] = set()
        self._defined: dict[str, tuple[set[str], dict[str, set[str]]]] = {}

    def defined(self, path: str) -> tuple[set[str], dict[str, set[str]]]:
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
        if kind == "punctuated":
            form = PUNCTUATED_RE.match(key)
            return (f"a phase parted from its workstream by {form.group('sep').strip()!r}, "
                    f"which reads as the bare workstream; write `WS-{fam} {form.group('tok')}`")
        for end in (ends(key) if kind == "phase" else [key]):
            plans = self.candidates(fam, end)
            if not plans:
                return "resolves to no plan: no lookup row and no live plan title"
            why = self.undefined(fam, end, kind, plans)
            if why:
                return why
        return None

    def row_errors(self) -> list[str]:
        """Each lookup row ID that the plans its row links do not define.

        A row is a claim about its plan, not a definition: `WS-QA QA99` linking
        a plan that numbers only `QA1` is as dead as the citation it would
        otherwise vouch for.  A family-only row (`WS-OD`) claims no phase.
        """
        out = []
        for ids, plans in self.rows:
            for fam, key, kind in ids:
                if kind == "punctuated":
                    why = self.error(fam, key, kind)
                else:
                    why = next(filter(None, (self.undefined(fam, end, kind, plans)
                                             for end in (ends(key) if kind == "phase" else [key])
                                             if key)), None)
                if why:
                    shown = (key if kind == "punctuated" else f"WS-{fam} {key}"
                             if kind == "phase" else f"WS-{key}")
                    out.append(f"lookup row {shown}: {why}")
        return out

    def undefined(self, fam: str, key: str, kind: str, plans: list[str]) -> str | None:
        """Why none of `plans` defines `key` at its level, or None when one does."""
        names = ", ".join(posixpath.basename(p) for p in plans)
        if kind == "suffix":
            if any(key in self.defined(p)[0] for p in plans):
                return None
            return f"{key} is defined by none of {names}"
        path = levels(key)
        holders = [p for p in plans if path and path[0] in self.defined(p)[0]]
        if not holders:
            return f"phase {path[0] if path else key} is defined by none of {names}"
        # Down the path, each level the plan numbers must hold the next ID.
        # A level it does not number (sub-tasks a landed plan folded into
        # prose) is not read: nothing structural says what belongs there.
        for parent, child in zip(path, path[1:]):
            numbering = [p for p in holders if self.defined(p)[1].get(parent)]
            if numbering and not any(child in self.defined(p)[0] for p in holders):
                return (f"{child} is not among the {parent} sub-tasks numbered by "
                        f"{', '.join(posixpath.basename(p) for p in numbering)}")
        if any(path[-1] in self.defined(p)[0] for p in holders):
            return None
        # Held short of its last ID: only a pinned level may hold a citation.
        held = next(level for level in reversed(path)
                    if any(level in self.defined(p)[0] for p in holders))
        self.held.add((fam, held))
        if (fam, held) in self.pinned:
            return None
        return (f"{path[-1]} is held to {held}, which no plan numbers below, and "
                f"WS-{fam} {held} is not pinned in UNNUMBERED_LEVELS: cite {held}, "
                "number its sub-tasks in the plan, or pin a level a landed plan "
                "folded into prose")


def check(repo: str, pinned: frozenset = UNNUMBERED_LEVELS) -> int:
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
                        set(REGISTER_SECTION_RE.findall(lookup[REGISTER])), texts, pinned)
    problems += resolver.row_errors()

    failures = []
    for (fam, key, kind), where in sorted(sites.items()):
        why = resolver.error(fam, key, kind)
        if why:
            more = f" (+{len(where) - 3} more)" if len(where) > 3 else ""
            shown = (key if kind == "punctuated" else f"WS-{fam} {key}"
                     if kind == "phase" else f"WS-{key or fam}")
            failures.append(f"FAIL: {shown}, cited at {', '.join(where[:3])}{more}: {why}")
    for problem in problems:
        print(f"FAIL: {LOOKUP_DOC}: {problem}")
    for failure in failures:
        print(failure)
    if problems or failures:
        print(f"Fix the citation, or give its plan a row in '{LOOKUP_HEADING}' "
              f"({LOOKUP_DOC}).")
        return 1
    # Only a clean run has read every citation, so only it can call a pin stale.
    stale = sorted(pinned - resolver.held)
    for fam, level in stale:
        print(f"FAIL: UNNUMBERED_LEVELS pins WS-{fam} {level}, but no citation or "
              "lookup row is held to it: its plan numbers the level now, or nothing "
              "cites below it.  Drop the pin.")
    if stale:
        return 1
    with_id = sum(1 for _, key, _ in sites if key)
    families = len({fam for fam, _, _ in sites})
    keyed = sum(1 for ids, _ in rows for _, key, _ in ids if key)
    print(f"PASS: {len(sites)} distinct workstream citations ({families} workstreams) "
          f"in {', '.join(CODE_TREES)} resolve; {with_id} carry a phase or suffix "
          f"and resolve at that level, held short only at the {len(pinned)} pinned "
          f"levels no plan numbers below; the {keyed} lookup row IDs with one are "
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
    "docs/dev_history/planning/QA2.md": (
        "# QA two\n\n## QA2\n\n### QA2.C — a group\n\n| QA2.C.4 | legacy |\n\n"
        "### QA2.D — another group\n\n| QA2.D.1 | x |\n\n"
        "## An ABI slice (QA2.E.6-.E.8)\n\n## QA2.G.1.hygiene sweep\n"),
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


def _qa2_plan(old: str, new: str) -> dict[str, str]:
    """The fixture with one line of `QA2.md` rewritten."""
    path = "docs/dev_history/planning/QA2.md"
    assert old in _FIXTURE[path]
    return {path: _FIXTURE[path].replace(old, new)}


def _qa99_plan(body: str) -> dict[str, str]:
    """A `WS-QA QA99` row whose plan is `body`, cited as a phase and a sub-task."""
    return {**_with_row(_ROW_QA99, "-- WS-QA QA99, WS-QA QA99.1\n"),
            "docs/dev_history/planning/QA99.md": "# QA ninety-nine\n\n" + body}


def _qa_pins(*held: str) -> frozenset:
    """`UNNUMBERED_LEVELS` for the fixture: each level pinned under `WS-QA`."""
    return frozenset(("QA", level) for level in held)


def _run_fixture(files: dict[str, str | None],
                 pinned: frozenset = frozenset()) -> tuple[int, str]:
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
                return check(td, pinned), out.getvalue()
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
         _with_cite("-- WS-QA QA1.9\n"), 1, "QA1.9 is not among the QA1 sub-tasks numbered by QA1.md"),
        ("a flat sub-task the live plan does not number (QB1.9)",
         _with_cite("-- WS-QB QB1.9\n"), 1, "QB1.9 is not among the QB1 sub-tasks numbered by LIVE.md"),
        ("a range whose far end is not a row", _with_cite("-- WS-QA QA1.1-QA1.9\n"), 1,
         "QA1.9 is not among the QA1 sub-tasks numbered by QA1.md"),
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
        ("a row written as (WS-QA, QA1)",
         _with_row("| (WS-QA, QA1) | [`QA1.md`](../dev_history/planning/QA1.md) |\n"), 1,
         "lookup row WS-QA, QA1: a phase parted from its workstream by ','"),
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
        ("a letter group the plan does not number (WS-QA QA2.Z)",
         _with_cite("-- WS-QA QA2.Z\n"), 1,
         "QA2.Z is not among the QA2 sub-tasks numbered by QA2.md"),
        ("a sub-task the group does not number (WS-QA QA2.C.99)",
         _with_cite("-- WS-QA QA2.C.99\n"), 1,
         "QA2.C.99 is not among the QA2.C sub-tasks numbered by QA2.md"),
        ("control: a letter part of a sub-task the plan does not split (QA2.C.4b), "
         "its level pinned", _with_cite("-- WS-QA QA2.C.4b\n"), 0, "PASS: 10 distinct",
         _qa_pins("QA2.C.4")),
        ("that letter part with its level not pinned", _with_cite("-- WS-QA QA2.C.4b\n"), 1,
         "QA2.C.4b is held to QA2.C.4, which no plan numbers below, and "
         "WS-QA QA2.C.4 is not pinned"),
        ("that letter part with its level pinned under another workstream",
         _with_cite("-- WS-QA QA2.C.4b\n"), 1, "WS-QA QA2.C.4 is not pinned",
         frozenset({("QB", "QA2.C.4")})),
        ("a plan that folds its rows into prose holds its citations short",
         {"docs/dev_history/planning/QA1.md": "# QA one\n\n## QA1\n\nQA1.1 and QA1.2 landed.\n"},
         1, "QA1.2 is held to QA1, which no plan numbers below"),
        ("a pin no citation is held to", {}, 1,
         "UNNUMBERED_LEVELS pins WS-QA QA2.E, but no citation or lookup row is held to it",
         _qa_pins("QA2.E")),
        ("control: a heading opening on a range numbers nothing (QA2.E.2), its level "
         "pinned", _with_cite("-- WS-QA QA2.E.2\n"), 0, "PASS: 10 distinct", _qa_pins("QA2.E")),
        ("that citation with its level not pinned", _with_cite("-- WS-QA QA2.E.2\n"), 1,
         "QA2.E.2 is held to QA2.E, which no plan numbers below"),
        ("the same range as a row numbers the level",
         {**_with_cite("-- WS-QA QA2.E.2\n"),
          **_qa2_plan("## An ABI slice (QA2.E.6-.E.8)", "| QA2.E.6-.E.8 | the ABI slice |")},
         1, "QA2.E.2 is not among the QA2.E sub-tasks numbered by QA2.md"),
        ("control: a qualified heading name numbers nothing (QA2.G.2), its level pinned",
         _with_cite("-- WS-QA QA2.G.2\n"), 0, "PASS: 10 distinct", _qa_pins("QA2.G")),
        ("the same heading unqualified numbers the level",
         {**_with_cite("-- WS-QA QA2.G.2\n"),
          **_qa2_plan("## QA2.G.1.hygiene sweep", "## QA2.G.1 sweep")},
         1, "QA2.G.2 is not among the QA2.G sub-tasks numbered by QA2.md"),
        ("a phase range whose far end is no phase (WS-QA QA1..QA99)",
         _with_cite("-- WS-QA QA1..QA99\n"), 1,
         "WS-QA QA1..QA99, cited at SeLe4n/A.lean:4: resolves to no plan"),
        ("a comma between the workstream and a phase it lacks: (WS-QA, QA99)",
         _with_cite("-- (WS-QA, QA99)\n"), 1,
         "WS-QA, QA99, cited at SeLe4n/A.lean:4: a phase parted from its workstream by ','"),
    ] + [
        (f"a phase it has, parted by {shape!r}", _with_cite(f"-- {text}\n"), 1,
         f"{shown}, cited at SeLe4n/A.lean:4: a phase parted from its workstream by {shape!r}")
        for shape, text, shown in (
            (",", "(WS-QA, QA1.2)", "WS-QA, QA1.2"), ("/", "WS-QA/QA1.2", "WS-QA/QA1.2"),
            ("(", "WS-QA (QA1.2 note)", "WS-QA (QA1.2"), (".", "WS-QA.QA1", "WS-QA.QA1"),
            ("`", "WS-QA `QA1.2`", "WS-QA `QA1.2"), ("**", "WS-QA **QA1.2**", "WS-QA **QA1.2"),
            ("+", "WS-QA + QA1.2", "WS-QA + QA1.2"), ("phase", "WS-QA phase QA1", "WS-QA phase QA1"),
            ("phases (", "WS-QA phases (QA1 note)", "WS-QA phases (QA1"),
            (":", "WS-QA: QA1.2", "WS-QA: QA1.2"),
        )
    ] + [
        ("a separator wrapped onto the next line", _with_cite("-- see WS-QA —\n-- QA1.2\n"), 1,
         "WS-QA — QA1.2, cited at SeLe4n/A.lean:4: a phase parted from its workstream by '—'"),
        ("control: a closing bracket or a full stop ends the citation",
         _with_cite("-- (see WS-QA) QA1.2 and WS-QA. QA1 opens a sentence\n"), 0,
         "PASS: 10 distinct"),
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
    for name, edits, want, message, *pin in cases:
        got, out = _run_fixture({**_FIXTURE, **edits}, pin[0] if pin else frozenset())
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
