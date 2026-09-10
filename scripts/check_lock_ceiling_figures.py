#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
#
#   seLe4n  - A Lean Microkernel
#   Copyright (C) 2026  Adam Hall
#   This program comes with ABSOLUTELY NO WARRANTY.
#   This is free software, and you are welcome to redistribute it
#   under certain conditions. See:
#   https://github.com/hatter6822/seLe4n/blob/main/LICENSE
"""Hold every prose claim about the lock-set ceiling to the value Lean derives.

**Why this gate exists.**  `maxLockSetSize` is the first factor of the WCRT
headline, and two further figures are functions of it: the per-lock critical
section the RPi5 tick admits (`admissibleCriticalSection`), and the contention
envelope at an illustrative uniform cost.  Every time the constant moved --
WS-RR RR7.11, then WS-OD OD3.5, OD3.7 and OD3.13 -- a hand-maintained copy of
one of those figures was left behind somewhere in the prose, and four
consecutive review rounds each found one that the previous round's sweep had
missed.  A hand-maintained copy of a derived figure is the
enumeration-standing-in-for-a-derivation shape this project warns about, and
the remedy it already uses elsewhere is a gate: WS-RR RR7.28 holds the
de-threading bundle count to its census, and that gate caught the family moving
170 -> 172 on the cut that made it stale rather than on the cut that noticed.
This is the same mechanism for the ceiling.

**Both axes are derived.**  The numbers come from the Lean sources -- the three
constants and the *shape* of the formula that combines them -- never from a
literal in this file; the sites are every tracked Markdown and Lean file outside
the historical set, never a list, so a prose site is covered the day it is
written.

**The claims are canonical, by contract.**  A regex cannot tell a live assertion
("the ceiling is 14") from narrative that legitimately names an old value ("OD3.5
raised the ceiling to 11", "against a ceiling of nine") -- the set of spellings
is unbounded, and this project's rule for that case is to require a canonical
form and refuse the rest rather than to keep teaching a scanner one more.  So a
*live* claim about any of the three figures is written in one of the three forms
below, and every occurrence of one is held to the derived value.  Narrative is
free to say anything, because it does not use those forms.

    the declared lock-set ceiling is **N**
    the RPi5 tick admits **N µs** per lock
    the uniform C µs envelope is **N µs**

**The gate fails closed on what it cannot read.**  It builds a set of
*requirements* -- prose claims to hold to the measurement -- so a near-miss (the
locator phrase present, the strict claim absent) is a gate defect reported as a
failure, not an input silently skipped.  The one input for which silence is the
right answer is a file carrying no claim at all.

**The required set is a pin, not a derivation.**  Which documents *must* carry
the canonical statement is an editorial decision with nothing in the code to
derive it from; it is listed, and the listing fails when a canonical document
drops the claim -- so the gate cannot be silenced by deleting the sentence it
checks.
"""

from __future__ import annotations

import argparse
import importlib.util
import os
import re
import subprocess
import sys
import tempfile

# **Gates read code, prose reads prose — and this gate does both** (PR #893
# review round 5).  The *claims* it holds to the derivation live in Markdown and
# in Lean docstrings, so they are read from the real text.  The *constants and
# the formula* are a question about code, so they are read through the shared
# comment-free view: without it a docstring shaped like the canonical
# declaration — `def maxLockSetSize : Nat := 13` quoted in historical prose —
# would either be reported as a duplicate definition or, if the live
# declaration were ever reformatted, supply the value itself.  A comment
# deciding whether a Tier 0 gate passes is precisely what that rule forbids, and
# writing a new scanner that reads Lean raw is how the rule gets broken again.
_VIEW_SPEC = importlib.util.spec_from_file_location(
    "lean_code_view", os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                   "lean_code_view.py"))
_VIEW = importlib.util.module_from_spec(_VIEW_SPEC)
_VIEW_SPEC.loader.exec_module(_VIEW)

# --------------------------------------------------------------------------
# The derived values: three constants and the shape that combines them.
# --------------------------------------------------------------------------

CEILING_SOURCE = "SeLe4n/Kernel/Concurrency/Locks/LockSet.lean"
CORES_SOURCE = "SeLe4n/Kernel/Concurrency/Types.lean"
BUDGET_SOURCE = "SeLe4n/Kernel/Scheduler/Operations/PerCoreWcrt.lean"

CEILING_DEF = re.compile(r"^def\s+maxLockSetSize\s*:\s*Nat\s*:=\s*(\d+)\s*$", re.MULTILINE)
CORES_DEF = re.compile(r"^def\s+numCores\s*:\s*Nat\s*:=\s*(\d+)\s*$", re.MULTILINE)
BUDGET_DEF = re.compile(r"^def\s+rpi5TickBudgetMicros\s*:\s*Nat\s*:=\s*(\d+)\s*$", re.MULTILINE)

# The formula is pinned rather than assumed.  Deriving `admissible` from the
# three constants is only sound while `admissibleCriticalSection` divides the
# budget by `maxLockSetSize * (numCores - 1)`; if that body changes, this gate
# would compute a figure the kernel does not, which is worse than not checking.
#
# **Anchored at the end of the body** (PR #893 review round 5).  Without the
# trailing anchor the pattern matched a *prefix*: `budget / (maxLockSetSize *
# (numCores - 1)) + 1` satisfied it, so the gate would derive 23 while Lean
# computed 24 and every stale prose figure would pass.  That is this project's
# oldest rule — a presence check is not a relation check — inside the pin
# written to enforce a relation, which is why the mutation is in the self-test.
ADMISSIBLE_BODY = re.compile(
    r"def\s+admissibleCriticalSection\s*\(budget\s*:\s*Nat\)\s*:\s*Nat\s*:=\s*\n"
    r"\s*budget\s*/\s*\(maxLockSetSize\s*\*\s*\(numCores\s*-\s*1\)\)[ \t]*(?:\r?\n|\Z)"
)

# --------------------------------------------------------------------------
# The canonical claim forms, and the looser locators that fail closed.
# --------------------------------------------------------------------------

CEILING_LOCATOR = re.compile(r"declared lock-set ceiling")
CEILING_CLAIM = re.compile(r"declared lock-set ceiling is \*\*(\d+)\*\*")

ADMISSIBLE_LOCATOR = re.compile(r"RPi5 tick admits")
ADMISSIBLE_CLAIM = re.compile(r"RPi5 tick admits \*\*(\d+) µs\*\* per lock")

ENVELOPE_LOCATOR = re.compile(r"µs envelope is")
ENVELOPE_CLAIM = re.compile(r"the uniform (\d+) µs envelope is \*\*(\d+) µs\*\*")

# Where a figure is *history* rather than a claim about HEAD.  Rewriting a
# CHANGELOG entry or a retired plan to today's value would be the falsification,
# not the fix -- the same rule that keeps CHANGELOG headers off the version-bump
# list.
HISTORICAL_PROSE = ("docs/dev_history/", "CHANGELOG.md")

# The pin: documents whose readers act on these figures, so a missing canonical
# statement is itself a failure.
REQUIRED_SITES = (
    "CLAUDE.md",
    "AGENTS.md",
    "docs/spec/SELE4N_SPEC.md",
    "docs/gitbook/12-proof-and-invariant-map.md",
    "SeLe4n/Kernel/Concurrency/Locks/LockSet.lean",
)

CHECKS = ("derived_constants", "ceiling_figure", "admissible_figure", "envelope_figure",
          "required_sites")


def prose_sources(root: str) -> list[str]:
    """Every tracked `.md` and `.lean` file, or a filesystem walk when git is absent.

    The tracked set is the honest one for a gate that runs pre-commit; the walk
    is what the self-test's temporary trees need.  Lean files are in scope
    because the ceiling's own docstring and three module overviews carried
    copies of these figures, and two of the four stale ones were there.
    """
    try:
        listed = subprocess.run(
            ["git", "-C", root, "ls-files", "*.md", "*.lean"],
            capture_output=True, text=True, check=True,
        ).stdout.split()
        if listed:
            return sorted(listed)
    except (OSError, subprocess.CalledProcessError):
        pass
    found = []
    for base, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if d not in (".git", ".lake")]
        for name in files:
            if name.endswith((".md", ".lean")):
                found.append(os.path.relpath(os.path.join(base, name), root))
    return sorted(found)


def read(root: str, relative: str) -> str | None:
    """The file's real text — what a *prose* claim is written in."""
    try:
        with open(os.path.join(root, relative), "r", encoding="utf-8") as handle:
            return handle.read()
    except (OSError, UnicodeDecodeError):
        return None


def read_code(root: str, relative: str) -> str | None:
    """The file's comment-free view — what a question about *code* must read.

    Byte-aligned with the original, so line numbers still mean what they say.
    An unterminated comment is unreadable rather than empty: returning `None`
    makes the caller report a derivation it could not perform, which is the
    fail-closed direction for a scanner building requirements.
    """
    text = read(root, relative)
    if text is None:
        return None
    try:
        return _VIEW.strip(text)
    except Exception:
        return None


def derived_figures(root: str) -> tuple[dict[str, int], list[str]]:
    """The three constants and the two figures derived from them.

    Returns `({}, problems)` when a source cannot be read or the formula has
    moved: a gate that cannot derive its own measurement must say so rather
    than check prose against a guess.
    """
    problems: list[str] = []
    values: dict[str, int] = {}
    for name, relative, pattern in (
        ("ceiling", CEILING_SOURCE, CEILING_DEF),
        ("cores", CORES_SOURCE, CORES_DEF),
        ("budget", BUDGET_SOURCE, BUDGET_DEF),
    ):
        text = read_code(root, relative)
        if text is None:
            problems.append(
                f"derived_constants: {relative}: cannot be read as Lean code, so "
                f"the {name} this gate measures prose against cannot be derived"
            )
            continue
        found = pattern.findall(text)
        if len(found) != 1:
            problems.append(
                f"derived_constants: {relative}: expected exactly one definition "
                f"of the {name} constant in the canonical form this gate reads; "
                f"found {len(found)}"
            )
            continue
        values[name] = int(found[0])

    body = read_code(root, BUDGET_SOURCE)
    if body is not None and not ADMISSIBLE_BODY.search(body):
        problems.append(
            f"derived_constants: {BUDGET_SOURCE}: `admissibleCriticalSection` no "
            f"longer divides the budget by `maxLockSetSize * (numCores - 1)`, so "
            f"the figure this gate derives is not the one the kernel computes -- "
            f"update the derivation here in the same cut that changes the formula"
        )

    if problems or len(values) != 3:
        return {}, problems

    divisor = values["ceiling"] * (values["cores"] - 1)
    if divisor == 0:
        problems.append(
            "derived_constants: the ceiling times one less than the core count is "
            "zero, so the admissible per-lock cost is undefined"
        )
        return {}, problems
    values["admissible"] = values["budget"] // divisor
    return values, problems


def figure_claims(root: str, values: dict[str, int]) -> list[str]:
    """Violations for prose stating a figure that is not the derived one."""
    problems: list[str] = []
    for relative in prose_sources(root):
        if any(relative.startswith(prefix) for prefix in HISTORICAL_PROSE):
            continue
        text = read(root, relative)
        if text is None:
            problems.append(
                f"ceiling_figure: {relative}: cannot be read, so any ceiling "
                f"claim it carries goes unchecked"
            )
            continue

        def line_of(offset: int) -> int:
            return text.count("\n", 0, offset) + 1

        for check, locator, claim in (
            ("ceiling_figure", CEILING_LOCATOR, CEILING_CLAIM),
            ("admissible_figure", ADMISSIBLE_LOCATOR, ADMISSIBLE_CLAIM),
            ("envelope_figure", ENVELOPE_LOCATOR, ENVELOPE_CLAIM),
        ):
            # Containment, not offset equality: a claim's match begins before
            # its locator's does (the envelope claim opens at `the uniform`
            # while its locator sits at `µs envelope is`), so comparing start
            # offsets would report every well-formed claim as unreadable.
            readable = [(m.start(), m.end()) for m in claim.finditer(text)]
            for match in locator.finditer(text):
                if not any(s <= match.start() and match.end() <= e for s, e in readable):
                    problems.append(
                        f"{check}: {relative}:{line_of(match.start())}: names this "
                        f"figure in a form the gate cannot read.  A live claim is "
                        f"written in the canonical form (see this gate's module "
                        f"docstring), so a figure that drifts is a build failure "
                        f"rather than a sentence nobody re-measured"
                    )

        for match in CEILING_CLAIM.finditer(text):
            claimed = int(match.group(1))
            if claimed != values["ceiling"]:
                problems.append(
                    f"ceiling_figure: {relative}:{line_of(match.start())}: claims "
                    f"the declared lock-set ceiling is {claimed}; "
                    f"`maxLockSetSize` is {values['ceiling']}"
                )
        for match in ADMISSIBLE_CLAIM.finditer(text):
            claimed = int(match.group(1))
            if claimed != values["admissible"]:
                problems.append(
                    f"admissible_figure: {relative}:{line_of(match.start())}: "
                    f"claims the RPi5 tick admits {claimed} µs per lock; "
                    f"`admissibleCriticalSection {values['budget']}` is "
                    f"{values['admissible']} at a ceiling of {values['ceiling']}"
                )
        for match in ENVELOPE_CLAIM.finditer(text):
            cost = int(match.group(1))
            claimed = int(match.group(2))
            expected = values["ceiling"] * (values["cores"] - 1) * cost
            if claimed != expected:
                problems.append(
                    f"envelope_figure: {relative}:{line_of(match.start())}: claims "
                    f"the uniform {cost} µs envelope is {claimed} µs; at a ceiling "
                    f"of {values['ceiling']} over {values['cores'] - 1} contending "
                    f"cores it is {expected} µs"
                )
    return problems


def required_sites(root: str) -> list[str]:
    """Violations for a canonical document that carries no such claim at all."""
    problems: list[str] = []
    for relative in REQUIRED_SITES:
        text = read(root, relative)
        if text is None:
            problems.append(
                f"required_sites: {relative}: cannot be read, so the canonical "
                f"statement this gate pins cannot be found"
            )
            continue
        for label, claim in (
            ("the declared lock-set ceiling", CEILING_CLAIM),
            ("the RPi5 tick's admissible per-lock cost", ADMISSIBLE_CLAIM),
            ("the uniform-cost contention envelope", ENVELOPE_CLAIM),
        ):
            if not claim.search(text):
                problems.append(
                    f"required_sites: {relative}: carries no canonical statement "
                    f"of {label}.  This document is pinned because its readers act "
                    f"on the figure, so deleting the sentence is not a way to "
                    f"satisfy the gate"
                )
    return problems


def run(root: str) -> list[str]:
    values, problems = derived_figures(root)
    if not values:
        return problems
    problems.extend(figure_claims(root, values))
    problems.extend(required_sites(root))
    return problems


# ==========================================================================
# Self-test
# ==========================================================================
#
# Every case mutates a *complete* fixture tree -- one that passes clean -- so
# a rejecting case demonstrates the check it names and nothing else.  Each
# declares whether its mutation is `preserving` (keeps the tokens, breaks the
# relation) or `deleting`, and the harness fails when any check has no
# preserving case: a fixture family that only ever removes things exercises a
# presence check, which is exactly the defect this gate exists to replace.

CLEAN_CEILING = "def maxLockSetSize : Nat := 14\n"
CLEAN_CORES = "def numCores : Nat := 4\n"
CLEAN_BUDGET = (
    "def rpi5TickBudgetMicros : Nat := 1000\n"
    "\n"
    "def admissibleCriticalSection (budget : Nat) : Nat :=\n"
    "  budget / (maxLockSetSize * (numCores - 1))\n"
)
CLEAN_CLAIMS = (
    "the declared lock-set ceiling is **14**, the RPi5 tick admits **23 µs** per "
    "lock, and the uniform 60 µs envelope is **2520 µs**.\n"
)


def _write(root: str, relative: str, text: str) -> None:
    path = os.path.join(root, relative)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as handle:
        handle.write(text)


def _build_tree(root: str, overrides: dict[str, str]) -> None:
    files = {
        CEILING_SOURCE: CLEAN_CEILING + "-- " + CLEAN_CLAIMS,
        CORES_SOURCE: CLEAN_CORES,
        BUDGET_SOURCE: CLEAN_BUDGET,
        "CLAUDE.md": CLEAN_CLAIMS,
        "AGENTS.md": CLEAN_CLAIMS,
        "docs/spec/SELE4N_SPEC.md": CLEAN_CLAIMS,
        "docs/gitbook/12-proof-and-invariant-map.md": CLEAN_CLAIMS,
        "CHANGELOG.md": "the declared lock-set ceiling is **9**\n",
        "docs/dev_history/old.md": "the declared lock-set ceiling is **8**\n",
        "docs/narrative.md": "OD3.5 raised the ceiling to 11, against a ceiling of nine.\n",
    }
    files.update(overrides)
    for relative, text in files.items():
        if text is None:
            continue
        _write(root, relative, text)


SELF_TESTS: tuple[tuple[str, str, str, dict[str, str], bool], ...] = (
    # (name, check, mutation kind, overrides, expect_problem)
    ("a clean tree passes", "-", "none", {}, False),
    ("history is not held to HEAD's value", "-", "none", {}, False),
    ("narrative naming an old ceiling is not a claim", "-", "none", {}, False),
    (
        "a ceiling claim that does not match the constant is caught",
        "ceiling_figure", "preserving",
        {"CLAUDE.md": "the declared lock-set ceiling is **13**, the RPi5 tick admits "
                      "**23 µs** per lock, and the uniform 60 µs envelope is **2520 µs**.\n"},
        True,
    ),
    (
        "an admissible claim that does not match the derivation is caught",
        "admissible_figure", "preserving",
        {"CLAUDE.md": "the declared lock-set ceiling is **14**, the RPi5 tick admits "
                      "**25 µs** per lock, and the uniform 60 µs envelope is **2520 µs**.\n"},
        True,
    ),
    (
        "an envelope claim that does not match the derivation is caught",
        "envelope_figure", "preserving",
        {"CLAUDE.md": "the declared lock-set ceiling is **14**, the RPi5 tick admits "
                      "**23 µs** per lock, and the uniform 60 µs envelope is **2340 µs**.\n"},
        True,
    ),
    (
        "an envelope claim at another cost is checked at THAT cost",
        "-", "preserving",
        {"CLAUDE.md": "the declared lock-set ceiling is **14**, the RPi5 tick admits "
                      "**23 µs** per lock, and the uniform 60 µs envelope is **2520 µs**; "
                      "the uniform 10 µs envelope is **420 µs**.\n"},
        False,
    ),
    (
        "an envelope claim at another cost with the WRONG product is caught",
        "envelope_figure", "preserving",
        {"CLAUDE.md": "the declared lock-set ceiling is **14**, the RPi5 tick admits "
                      "**23 µs** per lock, and the uniform 60 µs envelope is **2520 µs**; "
                      "the uniform 10 µs envelope is **2520 µs**.\n"},
        True,
    ),
    (
        "a locator without a readable claim is a gate defect, not a skip",
        "ceiling_figure", "preserving",
        {"CLAUDE.md": CLEAN_CLAIMS + "the declared lock-set ceiling is fourteen.\n"},
        True,
    ),
    (
        "a required document that drops the claim is caught",
        "required_sites", "deleting",
        {"docs/gitbook/12-proof-and-invariant-map.md": "no figure here.\n"},
        True,
    ),
    (
        "...and one that states every figure correctly but uncheckably is caught too",
        "required_sites", "preserving",
        {"docs/gitbook/12-proof-and-invariant-map.md":
            "The lock-set ceiling is fourteen; the RPi5 timer tick allows "
            "twenty-three µs per lock; and at a uniform 60 µs cost the envelope "
            "comes to 2520 µs.\n"},
        True,
    ),
    (
        "the ceiling moving without the prose is caught",
        "ceiling_figure", "preserving",
        {CEILING_SOURCE: "def maxLockSetSize : Nat := 15\n-- " + CLEAN_CLAIMS},
        True,
    ),
    (
        "a changed admissible formula stops the derivation rather than guessing",
        "derived_constants", "preserving",
        {BUDGET_SOURCE: "def rpi5TickBudgetMicros : Nat := 1000\n\n"
                        "def admissibleCriticalSection (budget : Nat) : Nat :=\n"
                        "  budget / (maxLockSetSize * numCores)\n"},
        True,
    ),
    (
        "...and so does a formula EXTENDED after the pinned expression",
        "derived_constants", "preserving",
        {BUDGET_SOURCE: "def rpi5TickBudgetMicros : Nat := 1000\n\n"
                        "def admissibleCriticalSection (budget : Nat) : Nat :=\n"
                        "  budget / (maxLockSetSize * (numCores - 1)) + 1\n"},
        True,
    ),
    (
        "a commented-out definition cannot supply the constant",
        "-", "preserving",
        {CEILING_SOURCE: "-- def maxLockSetSize : Nat := 13\n"
                        + CLEAN_CEILING + "-- " + CLEAN_CLAIMS},
        False,
    ),
    (
        "...and a commented-out definition ALONE supplies nothing",
        "derived_constants", "preserving",
        {CEILING_SOURCE: "/- historical: def maxLockSetSize : Nat := 13 -/\n"
                        "-- " + CLEAN_CLAIMS},
        True,
    ),
    (
        "a ceiling constant the gate cannot read stops the derivation",
        "derived_constants", "preserving",
        {CEILING_SOURCE: "def maxLockSetSize : Nat := 7 + 7\n-- " + CLEAN_CLAIMS},
        True,
    ),
    (
        "a core count that makes the divisor zero is refused",
        "derived_constants", "preserving",
        {CORES_SOURCE: "def numCores : Nat := 1\n"},
        True,
    ),
)


def self_test() -> int:
    correct = 0
    failures: list[str] = []
    preserving_for: dict[str, int] = {check: 0 for check in CHECKS}
    for name, check, kind, overrides, expect_problem in SELF_TESTS:
        with tempfile.TemporaryDirectory() as root:
            _build_tree(root, {})
            baseline = dict()
            for relative in overrides:
                baseline[relative] = read(root, relative)
            _build_tree(root, overrides)
            # An inert mutation reads as coverage while asserting nothing.
            if overrides and all(read(root, r) == baseline.get(r) for r in overrides):
                failures.append(f"  INERT: {name}: the mutation changed no fixture")
                continue
            problems = run(root)
            got = bool(problems)
            if got != expect_problem:
                failures.append(
                    f"  {name}: expected {'a problem' if expect_problem else 'no problem'}, "
                    f"got {problems if problems else 'none'}"
                )
                continue
            if expect_problem and check != "-":
                if not any(p.startswith(check + ":") for p in problems):
                    failures.append(
                        f"  {name}: expected a `{check}` problem, got {problems}"
                    )
                    continue
                if kind == "preserving":
                    preserving_for[check] = preserving_for.get(check, 0) + 1
            correct += 1
            print(f"[SELF-TEST OK]   {name} [{kind}]")
    for check in CHECKS:
        if preserving_for.get(check, 0) == 0:
            failures.append(
                f"  check `{check}` has no token-preserving rejecting case -- a "
                f"family that only ever deletes exercises a presence check"
            )
    if failures:
        print(f"lock-ceiling figure gate self-test: {len(failures)} problem(s):")
        for line in failures:
            print(line)
        return 1
    print(
        f"lock-ceiling figure gate self-test: {correct} cases, {correct} correct; "
        f"every check has a token-preserving case."
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Hold prose claims about the lock-set ceiling to the value Lean derives."
    )
    parser.add_argument("--root", default=os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    parser.add_argument("--self-test", action="store_true",
                        help="run the gate's own mutation fixtures and exit")
    parser.add_argument("--report", action="store_true",
                        help="print the derived figures and exit")
    args = parser.parse_args()

    if args.self_test:
        return self_test()

    values, problems = derived_figures(args.root)
    if args.report:
        if problems:
            for line in problems:
                print(f"  - {line}")
            return 1
        print(f"maxLockSetSize        = {values['ceiling']}")
        print(f"numCores              = {values['cores']}")
        print(f"rpi5TickBudgetMicros  = {values['budget']}")
        print(f"admissible per lock   = {values['admissible']} µs")
        print(f"uniform 60 µs envelope = "
              f"{values['ceiling'] * (values['cores'] - 1) * 60} µs")
        return 0

    problems = run(args.root)
    if problems:
        print("[FAIL] lock-ceiling figures (WS-OD OD3.15):")
        for line in problems:
            print(f"  - {line}")
        return 1
    print("[PASS] every prose claim about the lock-set ceiling matches the derivation")
    return 0


if __name__ == "__main__":
    sys.exit(main())
