#!/usr/bin/env python3
"""Fail when a source file declares its own deferral untracked.

The project keeps one debt register — the *Registered debt index* in
`docs/WORKSTREAM_HISTORY.md`.  A comment that says "no currently-active plan
file tracks it" is a deferral that has opted out of it: self-describing and
unfindable at once, because a reader can only meet it by opening the file it
lives in.  The register enumerates them instead, and each source comment
points there.

Keeping that true by hand does not work.  Three separate review rounds on the
cut that built the register found the sweep incomplete — first a deferral
living in a documentation file rather than in Lean, then two more in one Lean
file, then five others — every time because the sweep matched one phrasing and
the tree used another.  A person grepping one string is the wrong mechanism,
so this gate is the mechanism instead.

**Compliance is citing the register, not avoiding the words.**  A site may
discuss being untracked as long as the surrounding lines name the register;
what fails is a deferral that declares itself untracked and points nowhere.
That way the narrative files which *describe* the problem keep working, and a
new comment that quietly opts out does not.
"""

from __future__ import annotations

import pathlib
import re
import sys

REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent

# Where a self-declared deferral would live.  Documentation is included: the
# first miss this gate would have caught was in `docs/AUDIT_NOTES.md`, not in
# Lean.
SCAN_ROOTS = ("SeLe4n", "tests", "rust", "scripts", "docs")
SCAN_SUFFIXES = (".lean", ".rs", ".py", ".sh", ".md", ".toml", ".json")

# Files whose subject *is* the register or the audit that found it, so they
# necessarily quote the phrasing while describing it.  This list is
# deliberately short and each entry is a narrative, never a deferral site.
NARRATIVE_EXEMPT = {
    "docs/WORKSTREAM_HISTORY.md",       # the register itself
    "CHANGELOG.md",                     # historical per-version narrative
    "docs/planning/UNFINISHED_SMP_WORK.md",  # the audit that reported the gap
    "scripts/check_deferral_registration.py",  # this file's own docstring
}

EXEMPT_PREFIXES = ("docs/dev_history/",)

# "no currently-active plan file tracks it" and its observed variants.  Keyed
# on the *claim* — a plan/workstream not tracking something — rather than on
# any one sentence, since matching one sentence is what kept failing.
UNTRACKED_RE = re.compile(
    # The claim, in both orders it is written:
    #
    #   A. "no <modifiers> plan|workstream <noun> tracks it"
    #        no currently-active plan file tracks it
    #        no concrete plan file tracks it yet
    #        No currently-active workstream plan tracks it
    #   B. "not|never tracked in any <modifiers> plan|workstream"
    #        not tracked in any currently-active workstream plan
    #        is NOT tracked in any currently-active WS-AK plan file
    #
    # The modifier is free text and NOT part of the pattern: keying on
    # `currently-active` made the gate miss `no concrete plan file tracks it`,
    # the sixth phrasing this tree turned out to use.  What makes a deferral
    # untracked is the *relationship* — a negation, a plan or workstream, and
    # a tracking verb — so that is what is matched.
    #
    # The spans are short on purpose.  Text is flattened before matching, and
    # code contains few periods, so a wide `[^.]` bound wanders across
    # unrelated statements: a first attempt at this generalisation matched
    # "runs no unwrap at all (… tracked debt, see the plan …)" in a docstring
    # and "does not declare it tracked" in a Python f-string.  Binding the
    # negation tightly to the noun it negates is what separates the claim from
    # prose that merely contains the same words.
    r"\bno\b\s+(?:[\w'-]+\s+){0,3}(?:plan|workstream)[^.]{0,40}?track"
    r"|\b(?:not|never)\s+tracked\b[^.]{0,60}?(?:plan|workstream)",
    re.I,
)

# A site is compliant when the register is cited near the claim.
REGISTER_RE = re.compile(
    r"Registered debt index|WORKSTREAM_HISTORY", re.I
)

# `row 29`, `rows 24-26` — the citation form every re-pointed site uses.
ROW_CITE_RE = re.compile(r"\brows?\s+(\d+)", re.I)

REGISTER_PATH = "docs/WORKSTREAM_HISTORY.md"
_REGISTER_ROW_RE = re.compile(r"^\|\s*(\d+)\s*\|\s*`([^`]+)`", re.M)


class RegisterIndex:
    """The enumerated debt table, parsed from the register.

    Correlation is deliberately shallow and says so: it confirms that a cited
    row *exists* and that each row's file *exists*.  It cannot confirm the row
    describes the deferral beside it — no scanner can — and the diagnostic no
    longer implies otherwise.
    """

    def __init__(self, text: str) -> None:
        self.rows: dict[int, str] = {}
        for m in _REGISTER_ROW_RE.finditer(text):
            self.rows[int(m.group(1))] = m.group(2)

    @classmethod
    def load(cls, root: pathlib.Path) -> "RegisterIndex":
        p = root / REGISTER_PATH
        return cls(p.read_text(encoding="utf-8") if p.is_file() else "")


CONTEXT_LINES = 6


# Comment punctuation, stripped before joining so a wrapped claim reads as one
# sentence.
_COMMENT_LEAD_RE = re.compile(r"^\s*(?:--+|//+|/\*+|\*+/?|#+|>+)?\s*")


def _flatten(lines: list[str]) -> tuple[str, list[int]]:
    """Join comment lines into one string, with an offset -> line-number map.

    A line-based scan missed a claim wrapped across two lines; widening to a
    two-line window then missed one wrapped across three.  Guessing a window
    size is the same mistake as guessing a prefix list, so there is no window:
    the file is flattened and the *sentence* is the unit, bounded by the period
    the patterns already refuse to cross.
    """
    parts: list[str] = []
    line_of: list[int] = []
    for i, ln in enumerate(lines):
        text = _COMMENT_LEAD_RE.sub("", ln)
        parts.append(text)
        line_of.extend([i] * (len(text) + 1))   # +1 for the joining space
    return " ".join(parts), line_of


def scan_text(rel: str, text: str, register: RegisterIndex | None = None) -> list[str]:
    """Return one finding per untracked claim that is not properly registered.

    A claim is compliant when it cites the register **and**, if it names a
    `row N`, that row exists in the register's enumerated table.  Citing the
    register while naming a row that does not exist is the failure this
    correlation closes: the diagnostic always said a deferral must be both
    cited and listed, and only the citation was ever checked.
    """
    lines = text.splitlines()
    flat, line_of = _flatten(lines)
    out: list[str] = []
    for m in UNTRACKED_RE.finditer(flat):
        idx = min(m.start(), len(line_of) - 1) if line_of else 0
        i = line_of[idx] if line_of else 0
        lo = max(0, i - CONTEXT_LINES)
        hi = min(len(lines), i + CONTEXT_LINES + 1)
        context = "\n".join(lines[lo:hi])
        if not REGISTER_RE.search(context):
            out.append(f"{rel}:{i + 1}: cites no register -- {lines[i].strip()}")
            continue
        if register is not None:
            for row in ROW_CITE_RE.findall(context):
                if int(row) not in register.rows:
                    out.append(
                        f"{rel}:{i + 1}: cites row {row}, which the register's "
                        f"enumerated table does not contain -- {lines[i].strip()}"
                    )
                    break
    return out


def files_to_scan() -> list[pathlib.Path]:
    out: list[pathlib.Path] = []
    for root in SCAN_ROOTS:
        base = REPO_ROOT / root
        if not base.is_dir():
            continue
        for p in sorted(base.rglob("*")):
            if not p.is_file() or p.suffix not in SCAN_SUFFIXES:
                continue
            rel = str(p.relative_to(REPO_ROOT))
            if rel in NARRATIVE_EXEMPT:
                continue
            if any(rel.startswith(pre) for pre in EXEMPT_PREFIXES):
                continue
            out.append(p)
    return out


def _self_test() -> int:
    cases: list[tuple[str, bool, str]] = []

    def check(name: str, ok: bool, detail: str = "") -> None:
        cases.append((name, ok, detail))

    # Every phrasing the hand sweep missed must be caught.
    for label, text in [
        ("the phrasing the sweep did match",
         "-- post-1.0 candidate; no currently-active plan file tracks it.\n"),
        ("`not tracked in any currently-active workstream plan`",
         "-- work (not tracked in any currently-active workstream plan).\n"),
        ("`No currently-active workstream plan tracks it`",
         "-- work (DS-M04). No currently-active workstream plan tracks it.\n"),
        ("`NOT tracked in any currently-active WS-AK plan file`",
         "-- scope and is NOT tracked in any currently-active WS-AK plan file.\n"),
        ("a claim split with the register absent",
         "-- recorded as a post-1.0 hardening candidate; no currently-active\n"
         "-- plan file tracks it.\n"),
    ]:
        check(f"caught: {label}", bool(scan_text("X.lean", text)), repr(text))

    # Citing the register is what compliance means.
    check("a site citing the register passes",
          not scan_text("X.lean",
                        "-- no currently-active plan file tracks it, so it is\n"
                        "-- registered in the Registered debt index instead.\n"),
          "should not fire")
    check("a citation within the context window passes",
          not scan_text("X.lean",
                        "-- see docs/WORKSTREAM_HISTORY.md\n" + "-- filler\n" * 4 +
                        "-- no currently-active plan file tracks it.\n"),
          "should not fire")
    check("a citation beyond the context window still fires",
          bool(scan_text("X.lean",
                         "-- see docs/WORKSTREAM_HISTORY.md\n" + "-- filler\n" * 12 +
                         "-- no currently-active plan file tracks it.\n")),
          "should fire")

    # The one real false positive the tree contains must stay quiet.
    check("`currently-active ASID` is not a deferral",
          not scan_text("A.lean",
                        "  rollover never returns a currently-active ASID.\n"),
          "should not fire")
    check("ordinary prose is not a deferral",
          not scan_text("A.lean", "-- The active plan is to ship this.\n"),
          "should not fire")

    # A sentence wrapped across three lines is one sentence.  The first fix
    # here scanned single lines and missed a two-line wrap; the second used a
    # two-line window and missed a three-line one.  Guessing a window size is
    # the same mistake as guessing a prefix list, so there is no window.
    # (Codex review round 8, PR #882 — the reviewer's own three-line split.)
    check("a three-line wrapped claim is caught",
          bool(scan_text("X.lean",
                         "-- This debt is not tracked\n"
                         "-- in any currently-active\n"
                         "-- workstream plan.\n")),
          "should fire")
    check("a four-line wrapped claim is caught",
          bool(scan_text("X.lean",
                         "-- This debt\n-- is not tracked\n"
                         "-- in any currently-active\n-- workstream plan.\n")),
          "should fire")
    check("a period still bounds the claim",
          not scan_text("X.lean",
                        "-- Nothing here is not. The active plan tracks everything.\n"),
          "should not fire")

    # Citing the register is necessary but was also *sufficient* — a site could
    # name a row that does not exist and the gate passed, while its own
    # diagnostic claimed the deferral must be listed there.
    reg = RegisterIndex("| 29 | `scripts/check_deferral_registration.py` | thing |\n")
    check("a citation naming a nonexistent row is caught",
          any("does not contain" in f for f in scan_text(
              "X.lean",
              "-- no currently-active plan tracks it; see WORKSTREAM_HISTORY.md row 99.\n",
              reg)),
          "should fire")
    check("a citation naming a real row passes",
          not scan_text(
              "X.lean",
              "-- no currently-active plan tracks it; see WORKSTREAM_HISTORY.md row 29.\n",
              reg),
          "should not fire")
    check("the register table is parsed into rows",
          reg.rows == {29: "scripts/check_deferral_registration.py"}, repr(reg.rows))

    failed = [c for c in cases if not c[1]]
    for name, ok, detail in cases:
        print(f"  {'PASS' if ok else 'FAIL'}: {name}" + (f" -- {detail}" if not ok else ""))
    print(f"deferral-registration gate self-test: {len(cases)} cases, "
          f"{len(cases) - len(failed)} correct.")
    return 1 if failed else 0


def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        return _self_test()
    register = RegisterIndex.load(REPO_ROOT)
    findings: list[str] = []
    # Every enumerated row must name a file that still exists; a row pointing
    # at a deleted path is a deferral that has quietly lost its site.
    for row, path in sorted(register.rows.items()):
        if not (REPO_ROOT / path).is_file():
            findings.append(
                f"{REGISTER_PATH}: row {row} cites `{path}`, which does not exist"
            )
    for p in files_to_scan():
        try:
            text = p.read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue
        findings.extend(scan_text(str(p.relative_to(REPO_ROOT)), text, register))
    if findings:
        print("FAIL: deferral registration is incomplete.")
        print("Each deferral must cite the *Registered debt index* in "
              "docs/WORKSTREAM_HISTORY.md; a cited `row N` must exist in its "
              "enumerated table, and each row must name a file that exists. "
              "(Whether a row *describes* the deferral beside it is a reader's "
              "judgement, not this gate's.)")
        for f in findings:
            print(f"  {f}")
        return 1
    print(f"PASS: every deferral cites the register; all cited rows exist "
          f"among the {len(register.rows)} enumerated, and every row's file is present.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
