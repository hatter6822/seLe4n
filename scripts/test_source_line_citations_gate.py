#!/usr/bin/env python3
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
"""Self-test for the source-line-citation gate.

`check_source_line_citations.py` prints a PASS line claiming there are
no line-number citations in active documentation, and it has now been
found narrower than that claim twice in consecutive review rounds: it
matched neither the orphaned `:NNN` its own cleanup sweep produced, nor
the GitHub `#L123` anchor spelling.  Both times it reported PASS over
documents that held exactly what it forbids.

A gate whose failure mode is silence needs regression witnesses, the
same reasoning that gave the naming gate its self-test.  Each check
below pins one spelling the matcher must catch, or one it must leave
alone -- and the negatives matter as much as the positives here, since
a colon before digits is common in prose and an over-broad matcher
would make the gate unusable rather than merely weak.

Run directly, or as part of the documentation-sync tier.
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import check_source_line_citations as gate  # noqa: E402

failures: list[str] = []
performed = 0


def check(label: str, got: object, want: object) -> None:
    global performed
    performed += 1
    if got != want:
        failures.append(f"{label}: got {got!r}, want {want!r}")


CITE = gate.build_citation_re({"rs", "lean", "md", "sh", "py", "yml"})


def cited(text: str) -> bool:
    return bool(CITE.search(text)
                or gate.TEXTUAL_CITATION_RE.search(text)
                or gate.ORPHAN_CITATION_RE.search(text))


# --- The compact form, and the anchor spelling of the same citation ---
# `foo.rs#L123` renders as a live link and goes stale on exactly the
# edit `foo.rs:123` does -- an insertion above line 123 -- but silently,
# because the link still resolves.
check("a compact citation is caught", cited("see Boot.lean:551 for this"), True)
check("a line anchor is caught", cited("see Boot.lean#L551"), True)
check("an anchor RANGE is caught", cited("see Boot.lean#L551-L560"), True)
check("the Markdown-link spelling is caught",
      cited("[source](https://github.com/o/r/blob/abc123/AGENTS.md#L521-L527)"),
      True)
check("a path without a line number passes",
      cited("see SeLe4n/Platform/Boot.lean and its builder"), False)
check("a bare anchor-looking word passes", cited("issue #L in the tracker"),
      False)

# --- The prose spelling ----------------------------------------------
check("a verb-introduced line citation is caught",
      cited("defined at line 471 of the builder"), True)
check("a bare parenthetical line citation is caught",
      cited("the guard (line 530) rejects it"), True)
check("a single-digit line passes", cited("line 5 of the table"), False)

# --- The ORPHANED half a cleanup leaves behind ------------------------
# The v0.32.109 sweep rewrote the first citation of a pair and left the
# second as a bare `:NNN`: stale AND no longer naming a file.
check("an orphaned citation is caught", cited("(`API.lean`, `:303`)"), True)
check("a slash-separated orphan is caught", cited("`Defs.lean` / :237"), True)
# ...and the narrowness that keeps the gate usable. A colon before digits
# is ordinary prose; an over-broad rule here would flag clock times,
# ports and every bolded lead-in.
check("a clock time passes", cited("at 12:30 the round opens"), False)
check("a host:port passes", cited("bound to host:8080 locally"), False)
check("a bolded lead-in passes", cited("**Note**: 42 cores"), False)

# --- Scope is derived, not hand-listed --------------------------------
# A hard-coded extension list silently omitted `.yml`, `.ld` and `.json`,
# so citations into those formats sailed past the gate.
check("extensions are derived from the tree",
      gate.REQUIRED_EXTENSIONS <= gate.cited_extensions(), True)
check("a derived extension is matched",
      cited("in .github/workflows/lean_action_ci.yml:213"), True)
# ...and derivation must not then filter by NAME LENGTH.  An earlier
# `{0,7}` bound was justified as excluding numeric suffixes, but the
# leading-letter requirement already does that, so the bound's only
# effect was dropping real formats for being long -- `gitignore` is
# nine characters, and both tracked `.gitignore` files went uncited.
# A derived set that post-filters on length is a hand-list in
# derivation's clothing.
check("a nine-character extension is derived",
      "gitignore" in gate.cited_extensions(), True)
# These two run against the LIVE derived set rather than the fixed one
# the other checks use.  The claim under test is that derivation reaches
# this format at all, so a hand-written extension set here would test
# the opposite of the property.
_live = gate.build_citation_re(gate.cited_extensions())
check("a long-extension citation is matched",
      bool(_live.search("see rust/.gitignore:12 for the rule")), True)
check("its GitHub-anchor spelling is matched too",
      bool(_live.search(
          "see [x](https://github.com/a/b/blob/c/rust/.gitignore#L12)")), True)
# The exclusion that the length bound was wrongly credited with: a
# numeric suffix must still not read as an extension, or every dotted
# version in the prose becomes a citation.
check("a numeric suffix is still not an extension",
      cited("the version v0.32.1:5 shipped that"), False)
# A DOTFILE has no part before its extension -- the leading dot IS the
# separator -- so requiring at least one character matched
# `rust/.gitignore:12` and missed the bare spelling. A citation is not
# less stale for being written without its directory.
check("a bare dotfile citation is matched",
      bool(_live.search("see .gitignore:12 for the rule")), True)
check("its anchor spelling is matched too",
      bool(_live.search("see .gitignore#L12 for the rule")), True)
# The negative that keeps the optional prefix honest: a dotted version
# must not complete the pattern, which rests on the extension set
# requiring a leading letter rather than on the prefix being mandatory.
check("a dotted version is still not a citation",
      bool(_live.search("bumped to 0.32.138 today")), False)

# --- Fenced blocks are verbatim output, not citations ------------------
# A bare '```' toggle got both tilde fences and nested fences wrong,
# subjecting real transcripts to the prose rule.
check("a tilde fence is a fence", bool(gate.FENCE_RE.match("~~~text")), True)
check("an indented fence is a fence", bool(gate.FENCE_RE.match("   ```sh")), True)
check("a fence records its run length",
      len(gate.FENCE_RE.match("````").group("delim")), 4)


def main() -> int:
    if failures:
        print("FAIL: the citation gate lost a mechanism it is supposed to have:",
              file=sys.stderr)
        for f in failures:
            print("  " + f, file=sys.stderr)
        return 1
    print(f"PASS: citation gate self-test ({performed} checks).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
