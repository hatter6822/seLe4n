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

**Every helper invocation is classified, and the classification is exhaustive.**
An absence pin is not always spelled `run_negative_check`: a couple of dozen live
anchors say it with `run_check "…" bash -c "! rg …"` or
`run_check "…" bash -c "if rg …; then …; exit 1; fi"`, and a parser that expected
`rg` immediately after the label filed none of them — so a positive anchor could
contradict one and this gate would still report PASS.  Reading the shell wrapper
is half the fix; the other half is that an invocation which searches but cannot
be reduced to a single (pattern, target) is a **hard failure** rather than a
skip, because "the gate could not read it" and "the gate checked it" must never
produce the same PASS line.  The one tolerated middle case is a search whose
result is *composed* — piped through a filter, conjoined, or read out of a
process substitution.  Those pin a property of the composition rather than of a
pattern, so they have no counterpart to contradict; they are counted and named
(`--list`) instead of being silently dropped.

Exit status: 0 when the anchor set is satisfiable, 1 otherwise.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import shlex
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

# A helper invocation, split at the label.  Everything after it is a command,
# and *which* command decides whether the line is an anchor at all — which is
# why the rest is handed to a shell-aware splitter rather than matched by a
# regex that assumed `rg` came next.
HELPER_RE = re.compile(
    r"""^run_(?P<prose>prose_)?(?P<neg>negative_)?check(?:_with_timeout)?\s+
        "(?P<label>[A-Z-]+)"\s+
        (?P<rest>.+)$
    """,
    re.VERBOSE,
)

# Helper *detection*, deliberately weaker than `HELPER_RE`: the name alone.
# Whether the rest parses decides `anchor` vs `unparsed`; it must not decide
# whether the line is an anchor at all, or a label spelling nobody anticipated
# silently removes a pin from the comparison.
HELPER_NAME_RE = re.compile(r"^run_(?:prose_)?(?:negative_)?check(?:_with_timeout)?\s")

# The tools an anchor can be built out of.  Word-bounded so a path like
# `check_bcm2712_freshness.sh` is not read as naming one.
SEARCH_TOOLS = ("rg", "grep", "egrep", "fgrep")
SEARCH_TOOL_RE = re.compile(
    r"(?<![\w./-])(?:" + "|".join(SEARCH_TOOLS) + r")(?![\w-])")

# Anything that composes a command with another one, or derives its input.  A
# search whose result is piped, conjoined, or read out of a process substitution
# does not pin "this pattern is absent from this file" — it pins something about
# the composition — so these mark the boundary of what can be compared.
#
# Tested against *tokens*, never against the raw text.  Half the suites' patterns
# are alternations — `rg "SeLe4n\.Testing\.rc(AcceptAll|DenyAll)" …` — so a
# substring test for `|` or `(` reads the regex as a pipeline and files a live
# absence pin as uncomparable.  `shlex` with `punctuation_chars` splits an
# *unquoted* operator into its own token and leaves a quoted one inside the word,
# which is exactly the distinction that matters here.
_OPERATOR_CHARS = set("();<>|&")
_OPERATOR_WORDS = {"[[", "]]", "!", "{", "}"}


def _shell_tokens(s: str) -> list[str]:
    """Bash's words for `s`, with unquoted operators as separate tokens."""
    lexer = shlex.shlex(s, posix=True, punctuation_chars=True)
    lexer.whitespace_split = True
    return list(lexer)


def _is_composed(tokens: list[str]) -> bool:
    """Does this token stream join commands, or derive one's input?"""
    return any(
        tok in _OPERATOR_WORDS or (tok != "" and set(tok) <= _OPERATOR_CHARS)
        for tok in tokens)


# Option arity, **per tool**.  The word after an option is its value or the
# pattern depending on the option, and skipping the flag alone made
# `rg -g '*.lean' forbidden SeLe4n` parse as pattern `*.lean` with `forbidden` as
# a target — filed under a key nothing could contradict, so the gate passed over
# it.
#
# Per tool because the two disagree on a letter the suites actually use: `-E` is
# `--extended-regexp` in `grep` (a bare switch, live here as `grep -nwE`) and
# `--encoding` in `rg` (which takes a value).  One shared table would either
# refuse `grep -nwE` or swallow rg's encoding argument.
#
# `-e`/`--regexp` is the special one in both: its value IS the pattern.
_RG_VALUE = {
    "-e", "--regexp", "-f", "--file", "-g", "--glob", "--iglob",
    "-t", "--type", "-T", "--type-not", "--type-add", "--type-clear",
    "-m", "--max-count", "-A", "--after-context", "-B", "--before-context",
    "-C", "--context", "-M", "--max-columns", "-d", "--max-depth",
    "-r", "--replace", "--sort", "--sortr", "--color", "--colors",
    "-E", "--encoding", "--pre", "--ignore-file", "--context-separator",
    "--field-context-separator", "--field-match-separator",
    "--path-separator", "-j", "--threads", "--engine", "--stats-format",
}
_RG_BARE = {
    "-n", "--line-number", "-N", "--no-line-number", "-q", "--quiet",
    "-w", "--word-regexp", "-x", "--line-regexp", "-i", "--ignore-case",
    "-s", "--case-sensitive", "-S", "--smart-case", "-F", "--fixed-strings",
    "-U", "--multiline", "--multiline-dotall", "-o", "--only-matching",
    "-c", "--count", "--count-matches", "-l", "--files-with-matches",
    "--files-without-match", "-H", "--with-filename", "-I", "--no-filename",
    "--hidden", "--no-ignore", "-u", "--unrestricted", "-a", "--text",
    "-z", "--search-zip", "--no-heading", "--heading", "--vimgrep",
    "--json", "--null", "-0", "--no-config", "--pcre2", "-P",
    "--no-messages", "--binary", "-p", "--pretty", "--trim", "--invert-match",
    "-v", "-L", "--follow", "--one-file-system", "--crlf", "--debug",
}
_GREP_VALUE = {
    "-e", "--regexp", "-f", "--file", "-m", "--max-count",
    "-A", "--after-context", "-B", "--before-context", "-C", "--context",
    "-d", "--directories", "-D", "--devices", "--include", "--exclude",
    "--exclude-dir", "--exclude-from", "--label", "--binary-files",
    "--color", "--colour", "--group-separator", "--NUM",
}
_GREP_BARE = {
    "-E", "--extended-regexp", "-F", "--fixed-strings", "-G", "--basic-regexp",
    "-P", "--perl-regexp", "-i", "--ignore-case", "-y", "-v", "--invert-match",
    "-w", "--word-regexp", "-x", "--line-regexp", "-c", "--count",
    "-l", "--files-with-matches", "-L", "--files-without-match",
    "-o", "--only-matching", "-q", "--quiet", "--silent", "-s", "--no-messages",
    "-n", "--line-number", "-H", "--with-filename", "-h", "--no-filename",
    "-b", "--byte-offset", "-u", "--unix-byte-offsets", "-Z", "--null",
    "-z", "--null-data", "-a", "--text", "-I", "-r", "--recursive",
    "-R", "--dereference-recursive", "-U", "--binary", "--line-buffered",
    "-T", "--initial-tab", "--no-group-separator",
}

# `egrep`/`fgrep` are `grep` with a preset pattern mode.
_OPTION_TABLES = {
    "rg": (_RG_VALUE, _RG_BARE),
    "grep": (_GREP_VALUE, _GREP_BARE),
    "egrep": (_GREP_VALUE, _GREP_BARE),
    "fgrep": (_GREP_VALUE, _GREP_BARE),
}
_PATTERN_OPTIONS = {"-e", "--regexp"}

# PR #873 round 10: the flags that change the **match language**, not just the
# output.  They were parsed and thrown away, so `rg -i foo F` and `rg foo F`
# collapsed to one `(pattern, target)` key and a file containing only `FOO` —
# which satisfies the first and not the second — was reported as a contradiction.
# Retaining them lets `_mode_allows` compare only languages that can contradict.
_MODE_FLAGS: dict[str, set[str]] = {
    "-i": {"i"}, "--ignore-case": {"i"},
    "-s": {"s"}, "--case-sensitive": {"s"},
    "-S": {"S"}, "--smart-case": {"S"},
    "-F": {"F"}, "--fixed-strings": {"F"},
    "-w": {"w"}, "--word-regexp": {"w"},
    "-x": {"x"}, "--line-regexp": {"x"},
    "-G": set(), "--basic-regexp": set(),
    "-E": set(), "--extended-regexp": set(),
    "-P": set(), "--perl-regexp": set(),
}


def _mode_allows(p_mode: frozenset, n_mode: frozenset) -> bool:
    """May a negative anchor in `n_mode` contradict a positive one in `p_mode`?

    A contradiction says *every* line the positive requires also contains what
    the negative forbids.  That needs the negative's match language to be **no
    stricter** than the positive's:

    * a negative anchored at a word or line boundary (`-w`, `-x`) does not match
      the same text found mid-token, so containment inside the positive's
      literal run implies nothing;
    * a case-sensitive negative against a case-insensitive positive is escaped
      by any line whose case differs — the reviewer's `rg -i foo` / `rg foo`
      pair, satisfied together by a file holding only `FOO`;
    * `-S` (smart case) is case-sensitivity that depends on the pattern's own
      spelling, which this gate does not model, so it refuses rather than guess.

    The converse directions are all sound: a *more* permissive negative, or a
    boundary-anchored positive, only narrows what the positive can be satisfied
    by."""
    if {"w", "x"} & n_mode:
        return False
    if "S" in p_mode or "S" in n_mode:
        return False
    if "i" in p_mode and "i" not in n_mode:
        return False
    return True


def _scope_contains(outer: str, inner: str) -> bool:
    """Does search scope `outer` cover everything scope `inner` covers?

    `rg` positional arguments are files **or directories**, and the suites use
    both — so comparing the target strings for equality (PR #873 round 10's
    finding) skipped a negative anchor over `SeLe4n/` against a positive over
    `SeLe4n/Foo.lean`, which is a real contradiction: the positive requires a
    match in a file the negative forbids it in.

    Directional on purpose.  The reverse — a positive over a *directory* and a
    negative over one file in it — is satisfiable, because the positive can be
    met by a different file, so it must not be reported."""
    o, i = outer.rstrip("/"), inner.rstrip("/")
    return o == i or i.startswith(o + "/")


def _split_short_cluster(tok: str, valued: set[str], bare: set[str]) -> bool:
    """Is `-nwE` a cluster of *bare* short flags for this tool?

    Clustered short flags are live in the suites (`grep -nwE`, `rg -Un`), and a
    cluster is only safe to skip when every letter is a bare switch: a valued one
    hiding inside (`-nge`) would swallow the next word as its argument while the
    parser went looking for the pattern.
    """
    if len(tok) < 2 or tok.startswith("--"):
        return False
    for ch in tok[1:]:
        flag = "-" + ch
        if flag in valued or flag not in bare:
            return False
    return True


def _search_invocation(argv: list[str]):
    """`(pattern, targets)` if `argv` is a plain search, else `None`.

    Option arity is read from a table rather than guessed from shape.  The
    previous version skipped any word starting with `-` and took the next word as
    the pattern, which is right for a bare switch and wrong for every option that
    takes a separate value — `rg -g '*.lean' forbidden SeLe4n` was parsed as
    pattern `*.lean`.  An option in neither table is refused (`None` → the caller
    reports it as unparsed, which is a hard failure) rather than parsed on a
    guess: an unknown flag has unknown arity.

    A search with no target reads stdin and pins nothing about the tree, so it is
    not an anchor.
    """
    if not argv or argv[0] not in _OPTION_TABLES:
        return None
    valued, bare = _OPTION_TABLES[argv[0]]
    i, pattern = 1, None
    mode: set[str] = set()
    while i < len(argv) and argv[i].startswith("-") and argv[i] != "--":
        tok = argv[i]
        # `-v` inverts the match, so the invocation succeeds on the lines that do
        # NOT contain the pattern — the opposite of what a positive anchor
        # claims.  Reading it as a plain pin would invert the polarity silently.
        if tok == "--invert-match" or (
                not tok.startswith("--") and "v" in tok[1:]):
            return None
        if tok.startswith("--") and "=" in tok:
            # `--glob=…` carries its value; nothing to consume.
            name = tok.split("=", 1)[0]
            if name not in valued and name not in bare:
                return None
            if name in _PATTERN_OPTIONS:
                if pattern is not None:
                    return None          # two patterns: not one pinned string
                pattern = tok.split("=", 1)[1]
            i += 1
            continue
        if tok in valued:
            if i + 1 >= len(argv):
                return None
            if tok in _PATTERN_OPTIONS:
                if pattern is not None:
                    return None
                pattern = argv[i + 1]
            i += 2
            continue
        if tok in bare:
            mode |= _MODE_FLAGS.get(tok, set())
            i += 1
            continue
        if _split_short_cluster(tok, valued, bare):
            for ch in tok[1:]:
                mode |= _MODE_FLAGS.get("-" + ch, set())
            i += 1
            continue
        return None                       # unknown flag, unknown arity
    if i < len(argv) and argv[i] == "--":
        i += 1
    if pattern is None:
        if i >= len(argv):
            return None
        pattern, targets = argv[i], argv[i + 1:]
    else:
        targets = argv[i:]
    if not targets:
        return None
    # `-s` is an explicit case-sensitive override, so it cancels a preceding `-i`.
    if "s" in mode:
        mode.discard("i")
        mode.discard("s")
    return pattern, targets, frozenset(mode)


def _wrapped_search(script: str):
    """`(tokens, asserts_absent)` for a shell-wrapped search, or `None`.

    Three shapes, and the third is why this returns a polarity instead of just
    the argv:

        ! rg 'P' F                                   → P must be ABSENT
        if rg 'P' F; then echo …; exit 1; fi         → P must be ABSENT
        if rg 'P' F; then echo ok; else exit 1; fi   → P must be PRESENT

    The earlier version looked for `exit 1` anywhere after `then` and called every
    match an absence assertion.  That reads the third shape backwards: the failing
    exit is in the **else** branch, so the check fails when the search finds
    *nothing*.  Pairing such a line with an ordinary positive anchor for the same
    pattern would have produced a false contradiction and blocked CI on a
    perfectly satisfiable suite — a gate that invents failures is as bad as one
    that misses them.

    So the branches are separated and the polarity comes from *which* branch
    exits: then-only → absent, else-only → present, both or neither → `None`, and
    the caller reports it as unparsed rather than guessing.

    Composition disqualifies: `rg … | grep -v …` asserts that nothing *survives
    the filter*, which is a weaker claim than absence and would be a false
    contradiction if compared as one.  Those are reported as uncompared rather
    than guessed at.
    """
    s = script.strip()
    m = re.match(r"^!\s+(.*)$", s, re.S)
    if m:
        body, asserts_absent = m.group(1), True
    else:
        m = re.match(r"^if\s+(.*?);\s*then\b(.*)\bfi$", s, re.S)
        if not m:
            return None
        body, tail = m.group(1), m.group(2)
        # Split the two branches at a top-level `else`.  `elif` is a third
        # branch this cannot reason about, so it is refused outright.
        if re.search(r"(^|[;\s])elif(\s|$)", tail):
            return None
        parts = re.split(r"(?:^|[;\s])else(?:\s|$)", tail, maxsplit=1)
        then_part = parts[0]
        else_part = parts[1] if len(parts) > 1 else ""
        exits_on_found = bool(re.search(r"\bexit\s+1\b", then_part))
        exits_on_missing = bool(re.search(r"\bexit\s+1\b", else_part))
        if exits_on_found == exits_on_missing:
            # Neither branch fails (a report, not an assertion), or both do
            # (asserts nothing about the pattern either way).
            return None
        asserts_absent = exits_on_found
    try:
        tokens = _shell_tokens(body)
    except ValueError:
        return None
    if _is_composed(tokens):
        return None
    return tokens, asserts_absent


def _bash_script(argv: list[str]):
    """The script `bash -c` / `bash -lc` was handed, if this is such a call."""
    if not argv or argv[0] != "bash":
        return None
    for i, tok in enumerate(argv[1:], 1):
        if tok.startswith("-") and "c" in tok[1:]:
            return argv[i + 1] if i + 1 < len(argv) else None
    return None


def classify_line(line: str):
    """`(kind, is_negative, pattern, targets)` for one helper invocation.

    `kind` is one of:

    * `anchor` — a single pattern pinned present or absent in named files.
    * `plain` — the command names no search tool, so it is not an anchor at all
      (a build, a python gate, a `test -x`).  Decided by evidence, not by the
      regex failing to match.
    * `filtered` — it *does* search, but composes the result, so no single
      (pattern, target) is pinned.  Counted and reportable, never silently
      dropped.
    * `unparsed` — it searches and this parser cannot say what it pins.  A hard
      failure: an anchor the gate cannot read is an anchor it cannot compare,
      and reporting PASS over it is the fail-open this gate exists to remove.
    """
    m = HELPER_RE.match(line)
    if not m:
        # PR #873 round 14: **a helper line this cannot parse is `unparsed`, not
        # absent.**  `HELPER_RE` demands a `[A-Z-]+` label, but `test_lib.sh`
        # accepts any category string through its default `category_color` arm.
        # An anchor labelled `"SM9_D"` or `"Tier1"` therefore failed the regex,
        # returned `None`, and the caller read that as "not a helper line" --
        # the anchor vanished from the comparison while the gate reported PASS.
        # That is the fail-open the `unparsed` kind exists to remove, reaching
        # the gate one step earlier than the kind could see: at detection rather
        # than at parsing.  Detection is now by helper NAME alone, so a label
        # grammar can no longer decide whether an anchor is counted.
        if HELPER_NAME_RE.match(line):
            return ("unparsed", False, None, [], frozenset())
        return None
    rest = m.group("rest")
    searches = bool(SEARCH_TOOL_RE.search(rest))
    try:
        argv = _shell_tokens(rest)
    except ValueError:
        # An unbalanced quote — a form this cannot read.
        return ("unparsed" if searches else "plain", False, None, [], frozenset())

    inv = None if _is_composed(argv) else _search_invocation(argv)
    if inv is not None:
        return ("anchor", bool(m.group("neg")), inv[0], inv[1], inv[2])
    if argv and argv[0] in SEARCH_TOOLS:
        return ("unparsed", False, None, [], frozenset())

    script = _bash_script(argv)
    if script is not None:
        wrapped = _wrapped_search(script)
        if wrapped is not None:
            inner, asserts_absent = wrapped
            inv = _search_invocation(inner)
            if inv is not None:
                # The wrapper's own polarity composes with the helper's.  A script
                # that asserts ABSENCE under `run_check` is a negative anchor; one
                # that asserts PRESENCE under `run_check` is a positive one, and
                # under `run_negative_check` each flips again.
                is_neg = asserts_absent != bool(m.group("neg"))
                return ("anchor", is_neg, inv[0], inv[1], inv[2])
        return ("filtered" if SEARCH_TOOL_RE.search(script) else "plain",
                False, None, [], frozenset())

    return ("unparsed" if searches else "plain", False, None, [], frozenset())


def logical_lines(text: str):
    """Yield `(first_line_no, joined)` with backslash continuations folded in.

    Six live Tier-3 anchors put the file on the continuation line, and reading
    the physical line stopped at the trailing `\\` — which `\\S+` happily matched,
    so those six were filed under the target `'\\'` and could never collide with
    the anchor they were opposite to.  Bash joins the lines before the helper
    ever sees them; so must this.
    """
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        start = i + 1
        buf = lines[i]
        while buf.rstrip().endswith("\\") and i + 1 < len(lines):
            buf = buf.rstrip()[:-1] + " " + lines[i + 1]
            i += 1
        yield start, buf
        i += 1


def parse_anchors(text: str):
    """Yield `(line_no, kind, is_negative, pattern, target)` per anchor/target.

    One record per *target*: `rg -q 'X' a.rs b.rs` pins `X` absent in both files,
    and reading only the first left the second uncompared.
    """
    for line_no, raw in logical_lines(text):
        line = raw.strip()
        if line.startswith("#"):
            continue
        got = classify_line(line)
        if got is None:
            continue
        kind, is_neg, pattern, targets, mode = got
        if kind != "anchor":
            yield line_no, kind, False, None, None, frozenset()
            continue
        # `^` is an anchoring detail of the regex, not part of the symbol the
        # two helpers are talking about, so normalise it away before comparing.
        # Under `-F` there is no regex, so `^` is a literal character and stays.
        if "F" not in mode:
            pattern = pattern.lstrip("^")
        for target in targets:
            yield line_no, "anchor", is_neg, pattern, target, mode


def _literal_runs(pattern: str, fixed: bool = False) -> list[str] | None:
    """The maximal literal runs of `pattern`, or `None` if it is not decomposable.

    The soundness primitive.  **Every** string matching `pattern` contains each
    returned run as a substring, which is what lets the containment test below
    conclude something about the whole match language from one run.

    An unescaped `.` is a wildcard — `rg` documents `PATTERN` as a regular
    expression and `-F` as what makes metacharacters literal — so it *ends* a run
    rather than contributing a dot to it.  A quantifier, class, group or
    alternation makes even run-decomposition unsound (`a*` does not require an
    `a` at all), so those refuse outright.

    Under `-F` (`fixed`) there is no regex at all: `rg` documents it as what
    makes metacharacters literal, so the pattern is one run of its own text.
    """
    if fixed:
        return [pattern] if pattern else []
    runs, cur, i = [], [], 0
    while i < len(pattern):
        c = pattern[i]
        if c == "\\" and i + 1 < len(pattern):
            nxt = pattern[i + 1]
            # `\.`, `\(`, … are escaped literals; `\s`, `\b`, `\d` are classes.
            if nxt.isalnum():
                return None
            cur.append(nxt)
            i += 2
            continue
        if c == ".":
            if cur:
                runs.append("".join(cur))
                cur = []
            i += 1
            continue
        if c in "*+?[]()|{}^$":
            return None
        cur.append(c)
        i += 1
    if cur:
        runs.append("".join(cur))
    return runs


def _literal_core(pattern: str, fixed: bool = False) -> str | None:
    """The single literal string `pattern` pins, or `None` if it pins a set.

    A pattern with no wildcard at all decomposes into exactly one run, and that
    run *is* the pattern's text.  Anything else — an unescaped `.` included —
    pins a set, and the honest answer is "no verdict" rather than a guess.

    PR #873 round 8 made the unescaped dot a wildcard here.  It used to be folded
    to a literal dot on the grounds that the suites overwhelmingly write module
    separators unescaped, which is true but not a licence to *decide* on: a
    positive `foo.bar` and a negative `foo\.bar` are both satisfied by a tree
    containing only `fooXbar`, and the gate was reporting that satisfiable pair
    as a contradiction — failing CI over a suite that is fine.  A gate that
    invents failures is as bad as one that misses them.  What the fold was
    really catching is preserved, honestly, as `_dot_ambiguous` below.
    """
    runs = _literal_runs(pattern, fixed=fixed)
    if runs is None or len(runs) != 1:
        return None
    return runs[0]


def _regex_matches_literal(pattern: str, literal: str, mode: frozenset) -> bool:
    """Does `pattern`, read as a regex, match the text `literal` anywhere?

    Used only in the one direction where it is sound: a fixed-string positive
    obliges an exact substring, so the negative's regex can be run against that
    exact text.  An uncompilable pattern answers `False` -- this is a
    contradiction detector, and reporting one from a pattern `rg` itself would
    reject would fail CI on an anchor that never runs.
    """
    flags = re.IGNORECASE if "i" in mode else 0
    body = pattern
    if "w" in mode:
        body = r"\b(?:" + body + r")\b"
    if "x" in mode:
        body = r"\A(?:" + body + r")\Z"
    try:
        return re.search(body, literal, flags) is not None
    except re.error:
        return False


def _dot_literal(pattern: str) -> str | None:
    """`pattern` with every unescaped `.` read as a literal dot, or `None`.

    Not a claim about the regex — the *other* reading, the one the suites
    actually intend when they write `SeLe4n.ObjId` for a module separator.  Used
    only to tell an author that two anchors disagree about escaping, never to
    conclude that a tree cannot exist.
    """
    if _literal_runs(pattern) is None:
        # A quantifier, class, group or alternation is a wildcard under *both*
        # readings, so there is no "intended literal" to compare.
        return None
    out, i = [], 0
    while i < len(pattern):
        c = pattern[i]
        if c == "\\" and i + 1 < len(pattern):
            out.append(pattern[i + 1])
            i += 2
            continue
        out.append(c)
        i += 1
    return "".join(out)


def find_contradictions(paths):
    positive: dict[tuple[str, str], list[str]] = {}
    negative: dict[tuple[str, str], list[str]] = {}
    # PR #873 round 10: the dicts above key on `(pattern, target)` for *reporting*
    # only.  Comparison runs over these records, because two anchors sharing a key
    # can still have different search modes — and two with different targets can
    # still overlap when one names a directory.
    pos_records: list[tuple[str, str, frozenset, str]] = []
    neg_records: list[tuple[str, str, frozenset, str]] = []
    filtered: list[str] = []
    unparsed: list[str] = []
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
        rel = p.relative_to(REPO_ROOT) if p.is_relative_to(REPO_ROOT) else p
        for line_no, kind, is_neg, pattern, target, mode in parse_anchors(p.read_text()):
            where = f"{rel}:{line_no}"
            if kind == "plain":
                continue
            if kind == "filtered":
                filtered.append(where)
                continue
            if kind == "unparsed":
                unparsed.append(where)
                continue
            key = (pattern, target)
            if is_neg:
                negative.setdefault(key, []).append(where)
                neg_records.append((pattern, target, mode, where))
                total_neg += 1
            else:
                positive.setdefault(key, []).append(where)
                pos_records.append((pattern, target, mode, where))
                total_pos += 1
    if unparsed:
        # The reviewer's second half, and the one that keeps this honest: a form
        # the parser cannot read is not evidence of consistency.  Better to fail
        # on a shape nobody anticipated than to report PASS over it.
        raise SystemExit(
            "FAIL: anchor-set satisfiability — "
            f"{len(unparsed)} helper invocation(s) run a search this gate cannot "
            "read, so what they pin is uncompared:\n  "
            + "\n  ".join(unparsed)
            + "\n\nWrite the anchor as `run_check`/`run_negative_check` with a "
              "direct `rg PATTERN FILE`, or as `bash -c \"! rg PATTERN FILE\"`, "
              "so the gate can compare it."
        )
    both: list[tuple[str, str]] = []

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
    #
    # PR #873 round 8: the containment is over the positive's literal **runs**,
    # not over a dot-literalised core.  An unescaped `.` is a wildcard, so the
    # only text every match is guaranteed to contain is each run — and a
    # negative whose forbidden literal sits inside one run is forbidden by every
    # match, which is a real contradiction.  A negative that spans a wildcard is
    # not implied at all, and reporting it was the round-8 finding: `foo.bar`
    # positive against `foo\.bar` negative is satisfied by `fooXbar`.
    #
    # That reading is not simply dropped.  When the two contradict under the
    # *module-separator* reading the suites use everywhere — the pair that kept
    # Tier 3 red — the disagreement is about **escaping**, and the gate says so
    # separately instead of claiming unsatisfiability it cannot show.
    #
    # PR #873 round 10, two more soundness corrections in the same comparison:
    #
    # * **Scope.** `rg`'s positional arguments are files *or directories*, and the
    #   suites use both, so `n_target == p_target` skipped a negative over
    #   `SeLe4n/` against a positive over `SeLe4n/Foo.lean` — a real
    #   contradiction, since the positive requires a match in a file the negative
    #   forbids it in.  `_scope_contains` is directional: the reverse pair is
    #   satisfiable by a different file and must not be reported.
    # * **Match language.**  `-i`, `-F`, `-w`, `-x` were parsed and discarded, so
    #   `rg -i foo F` and `rg foo F` collapsed to one key and a file holding only
    #   `FOO` — which satisfies both — was reported contradictory.
    #   `_mode_allows` compares only languages where the negative is no stricter
    #   than the positive; an identical search asserted both ways is a
    #   contradiction whatever its flags, which is the rule stated first.
    ambiguous: list[tuple[str, str]] = []
    for p_pat, p_target, p_mode, p_where in pos_records:
        p_runs = _literal_runs(p_pat, fixed="F" in p_mode)
        p_dotted = _dot_literal(p_pat)
        for n_pat, n_target, n_mode, n_where in neg_records:
            key = (p_pat, p_target)
            if key in both or not _scope_contains(n_target, p_target):
                continue
            # The same search asserted both ways: no language reasoning needed.
            if p_pat == n_pat and p_mode == n_mode:
                both.append(key)
                negative[key] = [n_where]
                break
            if not _mode_allows(p_mode, n_mode):
                continue
            # PR #873 round 14: **a fixed-string positive against a regex
            # negative.**  `-F` makes the positive require a LITERAL in the
            # file; the negative is then a regex forbidding whatever matches it.
            # `rg -F 'foo.bar'` and `rg 'foo.bar'` over one file are
            # unsatisfiable -- the literal the positive demands is itself
            # matched by the negative's wildcard -- but `_literal_core` answers
            # `None` for a regex carrying a metacharacter, and a `None` core was
            # read as "no contradiction".  The asymmetry is the point: the
            # positive's obligation is a concrete string, so it can be tested
            # against the negative's pattern directly rather than by comparing
            # two literal cores.
            if "F" in p_mode and "F" not in n_mode:
                if _regex_matches_literal(n_pat, p_pat, n_mode):
                    both.append(key)
                    negative[key] = [n_where]
                    positive.setdefault(key, [p_where])
                    break
            if p_runs is None:
                continue
            n_core = _literal_core(n_pat, fixed="F" in n_mode)
            if n_core and any(n_core in run for run in p_runs):
                both.append(key)
                # Report against the negative anchor that actually fires.
                negative[key] = [n_where]
                positive.setdefault(key, [p_where])
                break
            # Same text under the reading the suites intend, different under the
            # regex one — an authoring ambiguity, not a proven contradiction.
            n_dotted = _dot_literal(n_pat)
            if (n_core and p_dotted and n_dotted and n_dotted in p_dotted
                    and key not in ambiguous):
                ambiguous.append(key)
                negative[key] = [n_where]
                positive.setdefault(key, [p_where])
    both = sorted(set(both))
    ambiguous = sorted({a for a in ambiguous if a not in set(both)})
    return both, positive, negative, total_pos, total_neg, filtered, ambiguous


def report(both, positive, negative, total_pos, total_neg, filtered, ambiguous=()) -> int:
    # Say what was NOT compared as plainly as what was.  A filtered invocation
    # pins something about a composition rather than about a pattern, so it has
    # no counterpart to contradict — but a PASS line that omits it would read as
    # coverage the gate does not have.
    note = (f"; {len(filtered)} filtered invocation(s) pin a composed result "
            f"and are not compared (--list names them)" if filtered else "")
    if not both and not ambiguous:
        print(
            f"PASS: anchor-set satisfiability — {total_pos} positive and "
            f"{total_neg} negative anchors, no pattern pinned both ways{note}."
        )
        return 0
    if not both:
        # Not a proven contradiction — an ambiguity the gate refuses to guess at.
        print(
            f"FAIL: anchor escaping is ambiguous — {len(ambiguous)} pattern(s) "
            f"contradict a negative anchor under the module-separator reading "
            f"these suites use, but not under the regex one, because an "
            f"unescaped `.` is a wildcard:",
            file=sys.stderr,
        )
        for key in ambiguous:
            pattern, target = key
            print(f"\n  pattern: {pattern!r}", file=sys.stderr)
            print(f"  target:  {target}", file=sys.stderr)
            print(f"    asserted PRESENT at: {', '.join(positive[key])}", file=sys.stderr)
            print(f"    asserted ABSENT  at: {', '.join(negative[key])}", file=sys.stderr)
        print(
            "\nEscape the dot in BOTH anchors (`SeLe4n\\.ObjId`) so the pair is "
            "comparable — then a real contradiction is reported as one, and a "
            "deliberate wildcard is spelled as a wildcard and left alone.",
            file=sys.stderr,
        )
        return 1
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

        both, *_ = find_contradictions([str(planted_p)])
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
        both, _, _, _, _, _, ambiguous = find_contradictions([str(historical_p)])
        # PR #873 round 8: still caught, and now correctly *labelled*.  The two
        # spell the module separator differently, so under the regex reading a
        # tree containing `SeLe4nXObjId` satisfies both — the pair is not
        # provably unsatisfiable, and saying it was is what the round-8 finding
        # objected to.  It IS an escaping ambiguity, which the gate reports as
        # such and still fails on, because an anchor set it cannot compare is
        # one it cannot protect.
        if both:
            print(
                f"FAIL: --self-test — the escape-spelling pair was reported as "
                f"a proven contradiction ({both}); it is satisfiable under the "
                f"regex reading and must be reported as ambiguous instead.",
                file=sys.stderr,
            )
            return 1
        if not ambiguous:
            print(
                "FAIL: --self-test — the substring/escape-spelling pair was "
                "NOT detected at all; a positive anchor whose required text "
                "contains a negative anchor's forbidden text is the shape that "
                "shipped, and it would ship again.",
                file=sys.stderr,
            )
            return 1

        # A wildcard the author MEANT is satisfiable, and must not be reported
        # as a contradiction: `foo.bar` present and `foo\.bar` absent are both
        # true of a tree containing only `fooXbar`.  The old dot-literalising
        # core failed CI on exactly this.
        wildcard_p = d / "wildcard.sh"
        wildcard_p.write_text(
            "run_check \"INVARIANT\" rg -n 'zeta.omega' Some/File.lean\n"
            "run_negative_check \"INVARIANT\" rg -n 'zeta\\.omega' Some/File.lean\n")
        both, *_ = find_contradictions([str(wildcard_p)])
        if both:
            print(
                f"FAIL: --self-test — a satisfiable wildcard/escaped pair was "
                f"reported as a contradiction ({both}).",
                file=sys.stderr,
            )
            return 1

        # …while a contradiction whose overlap lies INSIDE one literal run is
        # still proven, wildcard elsewhere in the pattern or not.  This is what
        # keeps the run decomposition from being a way to stop checking.
        run_p = d / "run.sh"
        run_p.write_text(
            "run_check \"INVARIANT\" rg -n 'alpha.theorem gamma_kept' Some/File.lean\n"
            "run_negative_check \"INVARIANT\" rg -n 'theorem gamma_kept' Some/File.lean\n")
        both, *_ = find_contradictions([str(run_p)])
        if both != [("alpha.theorem gamma_kept", "Some/File.lean")]:
            print(
                f"FAIL: --self-test — a contradiction contained in one literal "
                f"run of a wildcard-carrying positive anchor was missed "
                f"(got {both}).",
                file=sys.stderr,
            )
            return 1

        # PR #873 round 10: a negative anchor over a DIRECTORY contradicts a
        # positive over a file beneath it.  Exact target-string comparison
        # skipped the pair, and the suites really do search directories.
        scope_p = d / "scope.sh"
        scope_p.write_text(
            "run_check \"INVARIANT\" rg -n 'theorem overlap_kept' SeLe4n/Foo.lean\n"
            "run_negative_check \"INVARIANT\" rg -n 'theorem overlap_kept' SeLe4n\n")
        both, *_ = find_contradictions([str(scope_p)])
        if both != [("theorem overlap_kept", "SeLe4n/Foo.lean")]:
            print(
                f"FAIL: --self-test — a negative anchor over a directory did not "
                f"contradict a positive anchor over a file inside it (got {both}).",
                file=sys.stderr,
            )
            return 1

        # …and the reverse is SATISFIABLE: a positive over a directory can be met
        # by a different file than the one the negative forbids.  Reporting it
        # would be the round-8 mistake in a new place.
        scope_rev_p = d / "scope_rev.sh"
        scope_rev_p.write_text(
            "run_check \"INVARIANT\" rg -n 'theorem elsewhere_ok' SeLe4n\n"
            "run_negative_check \"INVARIANT\" rg -n 'theorem elsewhere_ok' SeLe4n/Foo.lean\n")
        both, *_ = find_contradictions([str(scope_rev_p)])
        if both:
            print(
                f"FAIL: --self-test — a positive anchor over a directory was "
                f"reported as contradicted by a negative over one file in it "
                f"({both}); that pair is satisfiable elsewhere in the tree.",
                file=sys.stderr,
            )
            return 1

        # PR #873 round 10: the search MODE is part of what an anchor pins.  A
        # case-insensitive positive and a case-sensitive negative are satisfied
        # together by a file holding only `FOO`, and flagging that failed CI over
        # a fine suite.
        mode_p = d / "mode.sh"
        mode_p.write_text(
            "run_check \"INVARIANT\" rg -n -i 'theorem case_free' Some/File.lean\n"
            "run_negative_check \"INVARIANT\" rg -n 'theorem case_free' Some/File.lean\n")
        both, *_ = find_contradictions([str(mode_p)])
        if both:
            print(
                f"FAIL: --self-test — a case-insensitive positive and a "
                f"case-sensitive negative were reported as contradictory "
                f"({both}); a differently-cased line satisfies both.",
                file=sys.stderr,
            )
            return 1

        # …and the OTHER direction is a real contradiction: a case-insensitive
        # negative forbids every spelling the case-sensitive positive requires.
        # Without this the mode check would just be a way to stop checking.
        mode_rev_p = d / "mode_rev.sh"
        mode_rev_p.write_text(
            "run_check \"INVARIANT\" rg -n 'theorem case_pinned' Some/File.lean\n"
            "run_negative_check \"INVARIANT\" rg -n -i 'theorem case_pinned' Some/File.lean\n")
        both, *_ = find_contradictions([str(mode_rev_p)])
        if both != [("theorem case_pinned", "Some/File.lean")]:
            print(
                f"FAIL: --self-test — a case-INsensitive negative did not "
                f"contradict a case-sensitive positive (got {both}); it forbids "
                f"every spelling the positive requires.",
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

        # THE SHELL-WRAPPED NEGATIVE.  Tier 3 spells roughly a dozen of its
        # absence pins as `run_check "…" bash -c "! rg …"` rather than through
        # `run_negative_check`, and a parser that required `rg` immediately after
        # the label filed none of them — so an opposing positive anchor could
        # make the tier unsatisfiable while this gate reported PASS.  Both live
        # spellings are planted: the bare negation and the `if …; then exit 1`
        # form.
        for name, wrapped in (
            ("bang", "run_check \"INVARIANT\" bash -c "
                     "\"! rg -q 'theorem delta_removed' Some/File.lean\"\n"),
            ("if-exit", "run_check \"INVARIANT\" bash -lc "
                        "\"if rg -n 'theorem delta_removed' Some/File.lean; "
                        "then echo 'back' >&2; exit 1; fi\"\n"),
        ):
            wrapped_p = d / f"wrapped_{name}.sh"
            wrapped_p.write_text(
                "run_check \"INVARIANT\" rg -n '^theorem delta_removed' "
                "Some/File.lean\n" + wrapped)
            both, *_ = find_contradictions([str(wrapped_p)])
            if both != [("theorem delta_removed", "Some/File.lean")]:
                print(
                    f"FAIL: --self-test — the shell-wrapped negative anchor "
                    f"({name} form) was not compared (got {both}).  Those pins "
                    f"are live in Tier 3, and a gate blind to them reports PASS "
                    f"over an unsatisfiable suite.",
                    file=sys.stderr,
                )
                return 1

        # THE ELSE-BRANCH FORM.  `if rg P F; then echo ok; else exit 1; fi`
        # asserts that P is PRESENT — the failing exit is in the else branch.
        # Reading any `exit 1` after `then` as an absence claim turned this into a
        # negative anchor, so pairing it with an ordinary positive anchor for the
        # same pattern produced a FALSE contradiction and would have blocked CI on
        # a perfectly satisfiable suite.  A gate that invents failures is as bad as
        # one that misses them, so both directions are planted.
        else_form_p = d / "else_form.sh"
        else_form_p.write_text(
            "run_check \"INVARIANT\" rg -n '^theorem eta_present' Some/File.lean\n"
            "run_check \"INVARIANT\" bash -lc "
            "\"if rg -n 'theorem eta_present' Some/File.lean; then echo ok; "
            "else exit 1; fi\"\n")
        both, *_ = find_contradictions([str(else_form_p)])
        if both:
            print(
                f"FAIL: --self-test — an `else exit 1` check (which asserts the "
                f"pattern is PRESENT) was read as an absence claim and reported "
                f"as contradicting a positive anchor ({both}).",
                file=sys.stderr,
            )
            return 1
        # …and it really is compared, as a POSITIVE anchor: a negative anchor for
        # the same pattern must contradict it.  Without this the check above would
        # pass just as well if the form were dropped on the floor.
        else_form_neg_p = d / "else_form_neg.sh"
        else_form_neg_p.write_text(
            "run_negative_check \"INVARIANT\" rg -n 'theorem eta_present' Some/File.lean\n"
            "run_check \"INVARIANT\" bash -lc "
            "\"if rg -n 'theorem eta_present' Some/File.lean; then echo ok; "
            "else exit 1; fi\"\n")
        both, *_ = find_contradictions([str(else_form_neg_p)])
        if both != [("theorem eta_present", "Some/File.lean")]:
            print(
                f"FAIL: --self-test — an `else exit 1` check was not compared as a "
                f"POSITIVE anchor (got {both}); tolerating the form is not the "
                f"same as reading it.",
                file=sys.stderr,
            )
            return 1

        # A VALUE-TAKING OPTION.  `rg -g '*.lean' P dir` puts the option's value
        # where a bare-switch parser expects the pattern, so the anchor was filed
        # under `*.lean` — a key nothing could ever contradict.  Planted with an
        # opposing negative anchor, which must now collide.
        glob_p = d / "glob_option.sh"
        glob_p.write_text(
            "run_check \"INVARIANT\" rg -n -g '*.lean' 'theorem theta_kept' SeLe4n\n"
            "run_negative_check \"INVARIANT\" rg -n 'theorem theta_kept' SeLe4n\n")
        both, *_ = find_contradictions([str(glob_p)])
        if both != [("theorem theta_kept", "SeLe4n")]:
            print(
                f"FAIL: --self-test — a value-taking search option was not "
                f"consumed (got {both}); its value was taken as the pattern, so "
                f"the anchor could never collide with anything.",
                file=sys.stderr,
            )
            return 1
        # An option whose arity this parser does not know must FAIL rather than be
        # parsed on a guess — the same fail-closed rule as an unreadable command.
        unknown_opt_p = d / "unknown_option.sh"
        unknown_opt_p.write_text(
            "run_check \"INVARIANT\" rg --frobnicate xyz 'theorem iota' F.lean\n")
        try:
            find_contradictions([str(unknown_opt_p)])
        except SystemExit:
            pass
        else:
            print(
                "FAIL: --self-test — a search with an unknown option was parsed "
                "on a guess instead of failing the gate; an unknown flag has "
                "unknown arity, so the pattern's position is unknown too.",
                file=sys.stderr,
            )
            return 1
        # `grep -nwE` is a cluster of BARE switches even though rg spells `-E`
        # with a value.  Per-tool tables are what keep both readable.
        grep_cluster_p = d / "grep_cluster.sh"
        grep_cluster_p.write_text(
            "run_check \"INVARIANT\" grep -nwE 'theorem kappa' F.lean\n"
            "run_negative_check \"INVARIANT\" grep -n 'theorem kappa' F.lean\n")
        both, *_ = find_contradictions([str(grep_cluster_p)])
        if both != [("theorem kappa", "F.lean")]:
            print(
                f"FAIL: --self-test — `grep -nwE` was not read as a cluster of "
                f"bare switches (got {both}); `-E` is valued in rg and bare in "
                f"grep, which is why the tables are per-tool.",
                file=sys.stderr,
            )
            return 1

        # A composed search pins the composition, not the pattern — comparing it
        # as an absence claim would be a false contradiction.  It must be
        # tolerated and counted, never treated as an anchor.
        composed_p = d / "composed.sh"
        composed_p.write_text(
            "run_check \"INVARIANT\" rg -n '^theorem eps_kept' Some/File.lean\n"
            "run_check \"HYGIENE\" bash -lc "
            "\"if rg -n 'theorem eps_kept' Some/File.lean | grep -v OK; "
            "then exit 1; fi\"\n")
        both, _, _, _, _, filtered, _ = find_contradictions([str(composed_p)])
        if both:
            print(
                f"FAIL: --self-test — a filtered search was compared as a plain "
                f"absence claim ({both}); `rg … | grep -v …` pins that nothing "
                f"survives the filter, which a positive anchor does not "
                f"contradict.",
                file=sys.stderr,
            )
            return 1
        if len(filtered) != 1:
            print(
                f"FAIL: --self-test — the filtered search was not counted "
                f"(got {filtered}); an uncompared invocation that goes "
                f"unreported is the silent skip this gate exists to remove.",
                file=sys.stderr,
            )
            return 1

        # …and a search shape the parser cannot read at all must FAIL, not be
        # skipped.  This is what stops the blind spot from reopening the next
        # time someone writes an anchor in a form nobody anticipated.
        opaque_p = d / "opaque.sh"
        opaque_p.write_text(
            "run_check \"INVARIANT\" xargs rg -q 'theorem zeta' Some/File.lean\n")
        try:
            find_contradictions([str(opaque_p)])
        except SystemExit:
            pass
        else:
            print(
                "FAIL: --self-test — a helper invocation running an unreadable "
                "search was skipped instead of failing the gate; an anchor the "
                "gate cannot read is one it cannot compare.",
                file=sys.stderr,
            )
            return 1

        # PR #873 round 14: a helper line whose CATEGORY LABEL the parser does
        # not recognise must fail, not vanish.  `test_lib.sh` accepts any
        # category string, so a label outside `[A-Z-]+` used to make `HELPER_RE`
        # miss the line entirely and the anchor drop out of the comparison
        # while the gate reported PASS.
        label_p = d / "label.sh"
        label_p.write_text(
            "run_check \"SM9_D\" rg -n 'theorem eta' Some/File.lean\n")
        try:
            find_contradictions([str(label_p)])
        except SystemExit:
            pass
        else:
            print(
                "FAIL: --self-test — an anchor with an unrecognised category "
                "label was skipped instead of failing the gate; a label "
                "spelling must not decide whether a pin is compared.",
                file=sys.stderr,
            )
            return 1

        # …and a fixed-string positive is unsatisfiable against a regex negative
        # whose wildcard matches the literal the positive demands.
        fixed_p = d / "fixed.sh"
        fixed_p.write_text(
            "run_check \"INVARIANT\" rg -F 'foo.bar' F.lean\n"
            "run_negative_check \"INVARIANT\" rg -n 'foo.bar' F.lean\n")
        both, *_ = find_contradictions([str(fixed_p)])
        if both != [("foo.bar", "F.lean")]:
            print(
                f"FAIL: --self-test — a fixed-string positive was not compared "
                f"against a regex negative that matches its literal (got "
                f"{both}); `-F` makes the positive demand an exact string, which "
                f"the negative's wildcard forbids.",
                file=sys.stderr,
            )
            return 1

        # The reverse pairing stays satisfiable: a regex positive can be met by
        # `fooXbar`, which the fixed-string negative does not forbid.
        fixed_rev_p = d / "fixed_rev.sh"
        fixed_rev_p.write_text(
            "run_check \"INVARIANT\" rg -n 'foo.bar' G.lean\n"
            "run_negative_check \"INVARIANT\" rg -F 'foo.bar' G.lean\n")
        both, _, _, _, _, _, amb = find_contradictions([str(fixed_rev_p)])
        if both:
            print(
                f"FAIL: --self-test — a regex positive against a fixed-string "
                f"negative was reported contradictory (got {both}), but "
                f"`fooXbar` satisfies both.",
                file=sys.stderr,
            )
            return 1

        # Every target of a multi-file search is pinned, not just the first.
        multi_p = d / "multi.sh"
        multi_p.write_text(
            "run_negative_check \"INVARIANT\" rg -q 'Sym' a.rs b.rs\n"
            "run_check \"INVARIANT\" rg -n 'Sym' b.rs\n")
        both, *_ = find_contradictions([str(multi_p)])
        if both != [("Sym", "b.rs")]:
            print(
                f"FAIL: --self-test — a contradiction on the SECOND target of a "
                f"multi-file search was missed (got {both}).",
                file=sys.stderr,
            )
            return 1

    print(
        "PASS: --self-test — planted contradictions were detected in both "
        "quoting styles, in both shell-wrapped spellings, on a second search "
        "target, through an `else exit 1` presence check and past a "
        "value-taking option; a filtered search was counted rather than "
        "compared, an unreadable command and an unknown option each failed the "
        "gate, an unrecognised category label failed rather than vanishing, a "
        "fixed-string positive was compared against a regex negative that "
        "matches its literal while the reverse pairing stayed satisfiable, "
        "`grep -nwE` was read as bare switches, an unescaped `.` was read "
        "as the wildcard it is (satisfiable pair not flagged, escape-spelling "
        "pair reported as ambiguous, in-run overlap still proven), a negative "
        "over a directory contradicted a positive over a file inside it while "
        "the reverse did not, case-insensitivity was compared in the direction "
        "that implies and skipped in the one that does not, the clean "
        "set passed, and a commented-out anchor was not counted."
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
        "--list",
        action="store_true",
        help="name the invocations whose composed result is not compared",
    )
    ap.add_argument(
        "scripts",
        nargs="*",
        help="anchor-declaring scripts to check (default: the tiered suites)",
    )
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    result = find_contradictions(args.scripts or discover_anchor_scripts())
    if args.list:
        for where in result[5]:
            print(f"  filtered (not compared): {where}")
    return report(*result)


if __name__ == "__main__":
    sys.exit(main())
