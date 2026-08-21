#!/usr/bin/env python3
"""Anchor-set satisfiability gate.

The tiered suites pin the invariant surface with two opposed helpers:
`run_check` (and `run_prose_check`) assert a pattern is PRESENT, while
`run_negative_check` (and `run_prose_negative_check`) assert it is ABSENT.
Nothing previously checked that the two sets are consistent, so a cut that
deleted a theorem, added the negative pin forbidding its return, and left the
original positive anchor in place produced an anchor set no tree can satisfy.

That is a silent failure in the worst place: the contradiction only surfaces in
the Full lane, several commits after the cut that introduced it, and it reads as
"the invariant surface regressed" rather than "two anchors disagree".

This gate is deliberately STATIC — it reads the anchor declarations rather than
running them — so it belongs in the fast hygiene lane and fires on the PR that
introduces the contradiction.

Exit status: 0 when the anchor set is satisfiable, 1 otherwise.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import subprocess
import sys
import tempfile

REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent

# Scripts whose anchors are checked — **discovered, not listed**.
#
# The hand-written list this replaces had gone stale in the way a hand-written
# list does: it named `test_tier2_smoke.sh`, which does not exist, and omitted
# `test_tier2_{trace,determinism,negative}.sh`, both Tier 4 suites and Tier 5.
# Five live suites were therefore unchecked, and because a missing path was
# skipped in silence the gate reported PASS over them just as confidently as
# over the four it actually read.  A satisfiability gate that quietly covers
# less than it claims is worse than none: it converts "unverified" into
# "verified", which is the reading its PASS line invites.
#
# Discovery keeps it honest — a tier script added tomorrow is covered the day it
# lands, and one renamed cannot silently drop out.
TIER_SCRIPT_GLOB = "test_tier*.sh"


def discover_anchor_scripts() -> list[str]:
    """Every tiered suite, by discovery.

    Sorted for a stable report order.  An empty result is a hard error rather
    than an empty pass: it means the glob has stopped matching the tree, which
    is the same fail-open this function exists to remove.
    """
    scripts = sorted(
        str(p.relative_to(REPO_ROOT))
        for p in (REPO_ROOT / "scripts").glob(TIER_SCRIPT_GLOB)
        if p.is_file()
    )
    if not scripts:
        raise SystemExit(
            f"FAIL: anchor-set satisfiability — no tier suites matched "
            f"scripts/{TIER_SCRIPT_GLOB}; the gate would have checked nothing "
            f"and reported PASS."
        )
    return scripts

ANCHOR_RE = re.compile(
    r"""run_(?P<prose>prose_)?(?P<neg>negative_)?check\s+   # helper
        "(?P<label>[A-Z-]+)"\s+                             # label
        rg\s+(?:-\S+\s+)*                                   # rg flags
        (?:'(?P<sq>[^']*)'                                  # '…' pattern
          |"(?P<dq>(?:[^"\\]|\\.)*)")\s+                    # or "…" pattern
        (?P<target>\S+)                                     # the file it reads
    """,
    re.VERBOSE,
)

# Bash keeps a backslash inside double quotes unless it precedes one of these,
# so `"\s"` reaches `rg` as `\s` while `"\\."` reaches it as `\.`.  Both forms
# are live in the suites, and a parser that skipped the unescaping would file
# the same pattern under two spellings and see no contradiction between them.
_DQ_SPECIAL = set('$`"\\\n')


def _unescape_double_quoted(s: str) -> str:
    """The string bash hands the command for a double-quoted word."""
    out, i = [], 0
    while i < len(s):
        c = s[i]
        if c == "\\" and i + 1 < len(s) and s[i + 1] in _DQ_SPECIAL:
            out.append(s[i + 1])
            i += 2
            continue
        out.append(c)
        i += 1
    return "".join(out)


def parse_anchors(text: str):
    """Yield (line_no, is_negative, pattern, target) for each anchor."""
    for line_no, raw in enumerate(text.splitlines(), 1):
        line = raw.strip()
        if line.startswith("#"):
            continue
        m = ANCHOR_RE.search(line)
        if not m:
            continue
        # Both quoting styles appear in the suites, and an anchor is no less
        # live for being double-quoted — reduce each to the pattern `rg`
        # actually receives so the two are comparable.
        sq = m.group("sq")
        pattern = sq if sq is not None else _unescape_double_quoted(m.group("dq"))
        # `^` is an anchoring detail of the regex, not part of the symbol the
        # two helpers are talking about, so normalise it away before comparing.
        pattern = pattern.lstrip("^")
        yield line_no, bool(m.group("neg")), pattern, m.group("target")


def _literal_core(pattern: str) -> str | None:
    """The literal text `pattern` pins, or `None` if it pins no single string.

    `.` and `\\.` both reduce to a literal dot.  Unescaped `.` *is* a wildcard,
    but in these suites it is overwhelmingly a module separator written without
    the escape (`SeLe4n.ObjId`), and the two helpers routinely spell the same
    symbol one way in the positive anchor and the other way in the negative —
    which is precisely the pair that has to be comparable.  Treating them alike
    is what makes the containment test below able to see them as the same text.

    A pattern carrying a genuine wildcard — a quantifier, class, group or
    alternation — pins a *set* of strings rather than one, so no single string
    stands for it and the honest answer is "no verdict" rather than a guess.
    """
    out, i = [], 0
    while i < len(pattern):
        c = pattern[i]
        if c == "\\" and i + 1 < len(pattern):
            nxt = pattern[i + 1]
            # `\.`, `\(`, … are escaped literals; `\s`, `\b`, `\d` are classes.
            if nxt.isalnum():
                return None
            out.append(nxt)
            i += 2
            continue
        if c == ".":
            out.append(".")
            i += 1
            continue
        if c in "*+?[]()|{}^$":
            return None
        out.append(c)
        i += 1
    return "".join(out)


def find_contradictions(paths):
    positive: dict[tuple[str, str], list[str]] = {}
    negative: dict[tuple[str, str], list[str]] = {}
    total_pos = total_neg = 0
    for path in paths:
        p = pathlib.Path(path)
        if not p.is_absolute():
            p = REPO_ROOT / p
        if not p.exists():
            # Never silently.  A path that cannot be read is a tier whose
            # anchors are unchecked, and reporting PASS over it is the failure
            # this gate is for.
            raise SystemExit(
                f"FAIL: anchor-set satisfiability — {path} does not exist, so "
                f"its anchors would go unchecked while the gate reported PASS."
            )
        for line_no, is_neg, pattern, target in parse_anchors(p.read_text()):
            key = (pattern, target)
            where = f"{p.relative_to(REPO_ROOT) if p.is_relative_to(REPO_ROOT) else p}:{line_no}"
            if is_neg:
                negative.setdefault(key, []).append(where)
                total_neg += 1
            else:
                positive.setdefault(key, []).append(where)
                total_pos += 1
    both = sorted(set(positive) & set(negative))

    # …and the contradictions that are not textually identical.
    #
    # Exact-key matching sees `^theorem foo` against `theorem foo` (the `^` is
    # normalised away) but not a negative anchor whose regex matches a *part* of
    # what a positive anchor requires.  That is the shape that actually shipped:
    # `run_check` required `^abbrev TaintTable := SeLe4n.ObjId → Declassification…`
    # while `run_negative_check` forbade `abbrev TaintTable := SeLe4n\.ObjId`.
    # Different strings, same file, and unsatisfiable together — Tier 3 was red
    # for four commits before anyone read the two lines side by side.
    #
    # A positive anchor asserts that some line matching P exists.  When the text
    # a negative anchor forbids is *literally contained* in the text P requires,
    # that line necessarily contains the forbidden text too, so the two cannot
    # both hold — no regex reasoning needed, just string containment over the
    # literal cores.  Restricting to literal cores is what keeps this free of
    # false positives: a pattern with a real wildcard yields no core and is
    # skipped rather than guessed at.
    for (p_pat, p_target), p_where in positive.items():
        p_core = _literal_core(p_pat)
        if p_core is None:
            continue
        for (n_pat, n_target), n_where in negative.items():
            if n_target != p_target or (p_pat, p_target) in both:
                continue
            n_core = _literal_core(n_pat)
            if n_core and n_core in p_core:
                both.append((p_pat, p_target))
                # Report against the negative anchor that actually fires.
                negative[(p_pat, p_target)] = n_where
                positive[(p_pat, p_target)] = p_where
                break
    both = sorted(set(both))
    return both, positive, negative, total_pos, total_neg


def report(both, positive, negative, total_pos, total_neg) -> int:
    if not both:
        print(
            f"PASS: anchor-set satisfiability — {total_pos} positive and "
            f"{total_neg} negative anchors, no pattern pinned both ways."
        )
        return 0
    print(
        f"FAIL: anchor-set satisfiability — {len(both)} pattern(s) are pinned "
        f"BOTH present and absent, so no tree can satisfy the suite:",
        file=sys.stderr,
    )
    for key in both:
        pattern, target = key
        print(f"\n  pattern: {pattern!r}", file=sys.stderr)
        print(f"  target:  {target}", file=sys.stderr)
        print(f"    asserted PRESENT at: {', '.join(positive[key])}", file=sys.stderr)
        print(f"    asserted ABSENT  at: {', '.join(negative[key])}", file=sys.stderr)
    print(
        "\nA symbol that was deleted keeps only its negative pin; a symbol that "
        "was kept keeps only its positive anchor.  Delete whichever no longer "
        "describes the tree.",
        file=sys.stderr,
    )
    return 1


def self_test() -> int:
    """Pin the mechanism: a gate that stops detecting fails silently.

    Drives the real entry point over two synthetic scripts — one clean, one
    carrying a planted contradiction — and asserts the verdict flips.  The
    planted pair uses the exact shape the live suites use, including the `^`
    the two helpers spell differently, since normalising that is the step a
    naive implementation omits.
    """
    clean = (
        "run_check \"INVARIANT\" rg -n '^theorem alpha_present' Some/File.lean\n"
        "run_negative_check \"INVARIANT\" rg -n 'theorem beta_removed' Some/File.lean\n"
    )
    planted = clean + (
        "run_check \"INVARIANT\" rg -n '^theorem beta_removed' Some/File.lean\n"
    )
    # A contradiction that differs only by the leading `^` — the live failure.
    with tempfile.TemporaryDirectory() as td:
        d = pathlib.Path(td)
        clean_p = d / "clean.sh"
        planted_p = d / "planted.sh"
        clean_p.write_text(clean)
        planted_p.write_text(planted)

        both, *_ = find_contradictions([str(clean_p)])
        if both:
            print(
                f"FAIL: --self-test — the clean anchor set was reported as "
                f"contradictory ({both}).",
                file=sys.stderr,
            )
            return 1

        both, pos, neg, _, _ = find_contradictions([str(planted_p)])
        if not both:
            print(
                "FAIL: --self-test — the planted contradiction was NOT detected; "
                "the gate no longer protects the suites.",
                file=sys.stderr,
            )
            return 1
        if both != [("theorem beta_removed", "Some/File.lean")]:
            print(
                f"FAIL: --self-test — detected the wrong pattern: {both}.",
                file=sys.stderr,
            )
            return 1

        # THE HISTORICAL PAIR.  Exact-key matching could not see this: the
        # positive spells the module separator `.` and the negative spells it
        # `\.`, and the negative names only a prefix of what the positive
        # requires.  Different strings, same file, unsatisfiable together —
        # this is the contradiction that kept Tier 3 red for four commits, and
        # it is planted verbatim so a future simplification of the containment
        # test cannot quietly stop catching it.
        historical = (
            "run_check \"INVARIANT\" rg -n "
            "'^abbrev TaintTable := SeLe4n.ObjId → DeclassificationTaint' "
            "SeLe4n/Kernel/InformationFlow/Taint.lean\n"
            "run_negative_check \"INVARIANT\" rg -n "
            "'abbrev TaintTable := SeLe4n\\.ObjId' "
            "SeLe4n/Kernel/InformationFlow/Taint.lean\n"
        )
        historical_p = d / "historical.sh"
        historical_p.write_text(historical)
        both, *_ = find_contradictions([str(historical_p)])
        if not both:
            print(
                "FAIL: --self-test — the substring/escape-spelling "
                "contradiction was NOT detected; a positive anchor whose "
                "required text contains a negative anchor's forbidden text is "
                "the shape that shipped, and it would ship again.",
                file=sys.stderr,
            )
            return 1

        # A path that cannot be read must FAIL rather than be skipped: a
        # silently-skipped tier is one the PASS line covers without checking.
        try:
            find_contradictions([str(d / "does_not_exist.sh")])
        except SystemExit:
            pass
        else:
            print(
                "FAIL: --self-test — a missing anchor script was skipped "
                "silently instead of failing the gate.",
                file=sys.stderr,
            )
            return 1

        # Discovery must actually find the tiered suites.  A glob that stops
        # matching would check nothing and report PASS over everything.
        discovered = discover_anchor_scripts()
        if len(discovered) < 5 or not any("tier3" in s for s in discovered):
            print(
                f"FAIL: --self-test — discovery returned {discovered}, which "
                f"does not look like the tiered suites.",
                file=sys.stderr,
            )
            return 1

        # The parser must not be fooled by a commented-out anchor.
        commented = clean + "# run_check \"INVARIANT\" rg -n '^theorem beta_removed' Some/File.lean\n"
        commented_p = d / "commented.sh"
        commented_p.write_text(commented)
        both, *_ = find_contradictions([str(commented_p)])
        if both:
            print(
                "FAIL: --self-test — a commented-out anchor was counted as live.",
                file=sys.stderr,
            )
            return 1

        # ... nor by the other quoting style.  The suites use double quotes
        # wherever the pattern itself contains a single quote or an escaped
        # dot, so a single-quote-only parser silently drops those anchors and
        # reports PASS on a tier that cannot be satisfied.  Both halves of this
        # pair are double-quoted, and the escape spellings differ between them
        # (`"\\."` vs `"\."`) — bash reduces both to `\.`, so the two must
        # collide.
        quoted = (
            'run_negative_check "INVARIANT" rg -n "^theorem gamma\\\\.removed" Some/File.lean\n'
            'run_check "INVARIANT" rg -n "theorem gamma\\.removed" Some/File.lean\n'
        )
        quoted_p = d / "quoted.sh"
        quoted_p.write_text(quoted)
        both, *_ = find_contradictions([str(quoted_p)])
        if both != [("theorem gamma\\.removed", "Some/File.lean")]:
            print(
                f"FAIL: --self-test — a double-quoted contradiction was not "
                f"detected (got {both}); double-quoted anchors are invisible "
                f"to the parser.",
                file=sys.stderr,
            )
            return 1

    print(
        "PASS: --self-test — planted contradictions were detected in both "
        "quoting styles, the clean set passed, and a commented-out anchor was "
        "not counted."
    )
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--self-test",
        action="store_true",
        help="drive the checker over a planted contradiction and assert detection",
    )
    ap.add_argument(
        "scripts",
        nargs="*",
        help="anchor-declaring scripts to check (default: the tiered suites)",
    )
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    return report(*find_contradictions(args.scripts or discover_anchor_scripts()))


if __name__ == "__main__":
    sys.exit(main())
