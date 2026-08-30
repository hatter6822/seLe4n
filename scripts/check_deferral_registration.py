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
    r"(?:no|not)\b[^.\n]{0,80}?"
    r"(?:currently[- ]active|active)\b[^.\n]{0,80}?"
    r"(?:plan|workstream)"
    r"|(?:plan|workstream)[^.\n]{0,80}?(?:does not|doesn't|do not|don't)\s+track"
    r"|(?:not|never)\s+tracked\s+(?:by|in)\s+(?:any|an?)\b[^.\n]{0,60}"
    r"(?:plan|workstream|register)",
    re.I,
)

# A site is compliant when the register is cited near the claim.
REGISTER_RE = re.compile(
    r"Registered debt index|WORKSTREAM_HISTORY", re.I
)

CONTEXT_LINES = 6


# Comment punctuation, stripped before joining so a claim wrapped across two
# lines still reads as one sentence.  A line-based scan missed exactly that —
# and one of the real sites this gate was built for is wrapped.
_COMMENT_LEAD_RE = re.compile(r"^\s*(?:--+|//+|/\*+|\*+/?|#+|>+)?\s*")


def scan_text(rel: str, text: str) -> list[str]:
    """Return one finding per untracked claim that cites no register.

    Claims are matched over a two-line window, because prose wraps and a
    sentence split across a newline is the same sentence.  Findings are
    reported once per claim, not once per window that contains it.
    """
    lines = text.splitlines()
    out: list[str] = []
    reported: set[int] = set()
    for i in range(len(lines)):
        window = " ".join(
            _COMMENT_LEAD_RE.sub("", ln) for ln in lines[i:i + 2]
        )
        if not UNTRACKED_RE.search(window):
            continue
        if i in reported or (i - 1) in reported:
            continue
        lo = max(0, i - CONTEXT_LINES)
        hi = min(len(lines), i + CONTEXT_LINES + 2)
        if REGISTER_RE.search("\n".join(lines[lo:hi])):
            continue
        reported.add(i)
        out.append(f"{rel}:{i + 1}: {lines[i].strip()}")
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

    failed = [c for c in cases if not c[1]]
    for name, ok, detail in cases:
        print(f"  {'PASS' if ok else 'FAIL'}: {name}" + (f" -- {detail}" if not ok else ""))
    print(f"deferral-registration gate self-test: {len(cases)} cases, "
          f"{len(cases) - len(failed)} correct.")
    return 1 if failed else 0


def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        return _self_test()
    findings: list[str] = []
    for p in files_to_scan():
        try:
            text = p.read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue
        findings.extend(scan_text(str(p.relative_to(REPO_ROOT)), text))
    if findings:
        print("FAIL: deferral(s) declare themselves untracked and cite no register.")
        print("Each must point at the *Registered debt index* in "
              "docs/WORKSTREAM_HISTORY.md, and be listed there:")
        for f in findings:
            print(f"  {f}")
        return 1
    print("PASS: no source declares a deferral untracked without citing the register.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
