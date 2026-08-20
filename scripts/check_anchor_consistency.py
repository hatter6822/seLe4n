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

# Scripts whose anchors are checked.  A tiered suite that starts declaring
# anchors must be added here; the self-test pins the parser, not this list.
ANCHOR_SCRIPTS = [
    "scripts/test_tier3_invariant_surface.sh",
    "scripts/test_tier2_smoke.sh",
    "scripts/test_tier1_build.sh",
    "scripts/test_tier0_hygiene.sh",
]

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


def find_contradictions(paths):
    positive: dict[tuple[str, str], list[str]] = {}
    negative: dict[tuple[str, str], list[str]] = {}
    total_pos = total_neg = 0
    for path in paths:
        p = pathlib.Path(path)
        if not p.is_absolute():
            p = REPO_ROOT / p
        if not p.exists():
            continue
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

    return report(*find_contradictions(args.scripts or ANCHOR_SCRIPTS))


if __name__ == "__main__":
    sys.exit(main())
