#!/usr/bin/env python3
"""A comment-free *view* of the Lean tree, so prose cannot decide a gate.

WS-SM SM8.B (PR #861 review round 43).

Every source-scanning gate in this repository — the 1500-odd Tier 3 surface
anchors, the AK7 cascade counters, the `sorry`/`axiom` floors — matched raw
file text.  Raw text includes docstrings and comments, so prose could both
*satisfy* a check and *break* one:

  * a positive anchor `rg 'fooTheorem' F.lean` passes when the theorem has been
    deleted and a comment still mentions it — the gate reads as coverage and
    checks nothing;
  * a negative anchor `rg 'forbiddenSymbol'` fires on the docstring that
    explains why the symbol is forbidden;
  * `RAW_MATCH_TOTAL` counts a docstring that *quotes* `st.objects[oid]?` while
    discussing it, so writing about the pattern regresses a monotonicity floor;
  * `SORRY_COUNT` greps `\\bsorry\\b` over the kernel, so a docstring saying
    "this proof carries no sorry" fails the project's most load-bearing gate.

The mitigations in place were conventions ("match a definition, not a mention",
`grep -v '^…--'`), and a convention is not a mechanism: it holds until someone
writes an ordinary sentence.  There is evidence of the cost in the tree — a
comment in `PriorityInheritance/PerCore.lean` was deliberately broken across
two lines so the AK7 line-oriented counter would not see the pattern it was
describing.  Contorting the prose to appease the scanner is the tell that the
scanner is reading the wrong thing.

This module supplies the right thing to read.  `strip` blanks every comment
character and leaves everything else exactly where it was, so a gate matching
the view sees code and only code, with the line and column geometry of the
original — `rg -n` line numbers over the view point at real lines of the real
file, and diagnostics stay usable.

Deliberately a *view*, not a rewrite: nothing here edits a source file, so a
docstring may say whatever is true without regard to what any pattern happens
to match.

Usage:
  lean_code_view.py FILE...            strip to stdout (single file)
  lean_code_view.py --overlay DIR      build/refresh the whole-repo overlay
  lean_code_view.py --self-test        run the witness suite
"""

from __future__ import annotations

import os
import shutil
import sys

_IDENT_TAIL = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'?!")


class UnterminatedComment(Exception):
    """A block comment ran to end of file.

    Raised rather than tolerated.  Silently blanking the remainder would hand
    every positive anchor an empty file (loudly wrong) and every negative
    anchor a clean bill of health (quietly wrong) — and the quiet direction is
    the one that matters, since a fail-open gate is the defect this module
    exists to remove.
    """


def strip(src: str, blank_strings: bool = False) -> str:
    """Blank Lean comments, preserving length, line count and column offsets.

    Handles `--` line comments, `/- -/` block comments *with nesting* (so `/--`
    docstrings, which are block comments, close correctly even when they quote
    another comment), string literals with backslash escapes, and char
    literals.

    With `blank_strings`, the *contents* of string literals are blanked too —
    the delimiting quotes stay, so a scanner asking "does this declaration call
    `f`" cannot be satisfied by `IO.println "f"` (PR #889 review round 5: the
    boot-entry gate asked exactly that and a string literal answered it).  The
    default keeps string contents, because some gates read them — a `.file(…)`
    path, an `#[export_name = "…"]` — and an anchor over such a string must
    keep seeing it.

    Char literals need the identifier check: `'` is both a char delimiter and a
    legal identifier suffix, so `foo'` must not open one.  Getting this wrong
    would desynchronise the string state on any file containing a primed name,
    which is most of them.
    """
    out = list(src)
    n = len(src)
    i = 0
    depth = 0
    in_line = False
    in_string = False

    def blank(j: int) -> None:
        if out[j] != "\n":
            out[j] = " "

    while i < n:
        c = src[i]
        nxt = src[i + 1] if i + 1 < n else ""

        if in_line:
            if c == "\n":
                in_line = False
            else:
                blank(i)
            i += 1
            continue

        if depth:
            if c == "/" and nxt == "-":
                depth += 1
                blank(i), blank(i + 1)
                i += 2
                continue
            if c == "-" and nxt == "/":
                depth -= 1
                blank(i), blank(i + 1)
                i += 2
                continue
            blank(i)
            i += 1
            continue

        if in_string:
            if c == "\\":
                if blank_strings:
                    blank(i)
                    if i + 1 < n:
                        blank(i + 1)
                i += 2
                continue
            if c == '"':
                in_string = False
            elif blank_strings:
                blank(i)
            i += 1
            continue

        # A **raw** string literal: `r"…"`, `r#"…"#`, `r##"…"##` (PR #889
        # review round 15).  Its body ends at a `"` followed by exactly the
        # opening run of `#`s, and an ordinary `"` inside it is text — so a
        # scanner that treats every quote as a delimiter closes the literal
        # early, reads the real terminator as an *opening* quote, and blanks
        # the live code that follows.  With `def s := r#"hello " raw"#` above
        # it, an `@[export lean_kernel_main]` disappeared from the view.
        if c == "r" and (i == 0 or src[i - 1] not in _IDENT_TAIL):
            hashes = 0
            j = i + 1
            while j < n and src[j] == "#":
                hashes += 1
                j += 1
            if j < n and src[j] == '"':
                terminator = '"' + "#" * hashes
                close = src.find(terminator, j + 1)
                end = n if close == -1 else close + len(terminator)
                if blank_strings:
                    for k in range(j + 1, min(end - len(terminator), n) if close != -1 else n):
                        blank(k)
                i = end
                continue

        if c == '"':
            in_string = True
            i += 1
            continue

        # A char literal, but only where `'` cannot be an identifier's prime.
        if c == "'" and (i == 0 or src[i - 1] not in _IDENT_TAIL):
            if nxt == "\\" and i + 3 < n and src[i + 3] == "'":
                i += 4
                continue
            if i + 2 < n and src[i + 2] == "'":
                i += 3
                continue

        # A guillemet-quoted identifier is a single token: `--` or `/-`
        # inside `«a--b»` is identifier text, not a comment opener, and a
        # stripper blind to the quoting truncates the line (or raises on a
        # quoted `/-` with no close) while Lean compiles it happily
        # (PR #886 review).  Bounded to one line — Lean's quoted
        # identifiers cannot span lines — so a stray unpaired `«` changes
        # nothing.
        if c == "«":
            close = src.find("»", i + 1)
            newline = src.find("\n", i + 1)
            if close != -1 and (newline == -1 or close < newline):
                i = close + 1
                continue

        if c == "-" and nxt == "-":
            in_line = True
            blank(i), blank(i + 1)
            i += 2
            continue

        if c == "/" and nxt == "-":
            depth = 1
            blank(i), blank(i + 1)
            i += 2
            continue

        i += 1

    if depth:
        raise UnterminatedComment(f"block comment still open at end of input (depth {depth})")

    return "".join(out)


def code_no_strings(src: str) -> str:
    """The comment-free view with string contents blanked as well — for a
    scanner whose question is about identifiers and calls, never about text.
    Named after `rust_code_view.code_no_strings`, its Rust counterpart."""
    return strip(src, blank_strings=True)


def attribute_arguments(view: str, keyword: str) -> list[str]:
    """Every `@[… , <keyword> <name>, …]` argument in a Lean **code view**, in
    order of first occurrence, without duplicates.

    Lean's attribute syntax is a bracketed, comma-separated list, so the
    argument of one attribute is not the whole bracket: `@[inline, export
    lean_kernel_main]` carries the export just as `@[export lean_kernel_main]`
    does, and a line break after `export` is whitespace like any other.  A
    scanner that greps for the literal `@[export ` sees neither — which is how
    `check_kernel_entry_exports.py` came to have an export inventory and a
    boot-entry locator that `build.rs`'s parser (which has split the list
    since PR #889 review round 2) disagreed with.  This is that parser, shared,
    so the two cannot drift again.

    Brackets nest (`@[simp, foo[bar]]`), so the list ends at the *matching*
    `]`.  A quoted argument (`@[extern "ffi_fatal_halt"]`) is read as the
    string's contents, so the same parser answers "which Rust symbol does this
    `opaque` bind to?".  The caller passes a view — `strip`ped where a quoted
    argument must be readable, `code_no_strings` where a quoted *attribute*
    must not count.
    """
    names: list[str] = []
    search = 0
    while True:
        hit = view.find("@[", search)
        if hit < 0:
            return names
        open_at = hit + 2
        depth = 1
        close = None
        for index in range(open_at, len(view)):
            if view[index] == "[":
                depth += 1
            elif view[index] == "]":
                depth -= 1
                if depth == 0:
                    close = index
                    break
        if close is None:
            return names
        for attr in view[open_at:close].split(","):
            attr = attr.strip()
            if not attr.startswith(keyword):
                continue
            rest = attr[len(keyword):]
            if not rest[:1].isspace():
                continue
            argument = rest.strip()
            if argument.startswith('"'):
                # A quoted argument — `@[extern "ffi_fatal_halt"]`.  Read it
                # only where the caller kept string contents; over
                # `code_no_strings` the quotes survive and the name does not,
                # which is the right answer there (a blanked string names
                # nothing).
                name = argument[1:].split('"', 1)[0].strip()
            else:
                name = ""
                for ch in argument:
                    if ch.isascii() and (ch.isalnum() or ch == "_"):
                        name += ch
                    else:
                        break
            if name and name not in names:
                names.append(name)
        search = close + 1


# ---------------------------------------------------------------------------
# The witness suite.
#
# A scanner that under-reaches fails silently, which is the whole complaint
# this module answers, so its own mechanisms are pinned here rather than
# assumed — the same discipline `test_identifier_naming_gate.py` and
# `test_source_line_citations_gate.py` apply to theirs.
# ---------------------------------------------------------------------------

# Each case states the *code* that must survive, whitespace-normalised, and the
# prose token that must not.  Written this way on purpose: an expectation
# spelled as an exact output string means hand-counting blanked columns, which
# is how the first draft of this suite shipped two wrong expectations — one of
# them wrong about Lean itself (`/-- a /- b -/` nests, so it stays *open*).
# Geometry is checked separately, over the real tree, where it matters.
_CASES: list[tuple[str, str, str]] = [
    ("line comment",
     "def f := 1 -- sorry\n", "def f := 1"),
    ("docstring is a block comment",
     "/-- has sorry in it -/\ndef f := 1\n", "def f := 1"),
    ("multi-line docstring",
     "/-- one\nsorry\n-/\ndef f := 1\n", "def f := 1"),
    ("nested block comment closes at the right depth",
     "/- a /- b sorry -/ c -/ def f := 1\n", "def f := 1"),
    ("trailing comment after code on the same line",
     "theorem t : P := by simp -- no sorry needed\n", "theorem t : P := by simp"),
    ("a primed identifier does not open a char literal",
     "def f' := 1 -- sorry\n", "def f' := 1"),
    ("char literal containing a quote keeps string state sane",
     "def q := '\"'\ndef g := 1 -- sorry\n", "def q := '\"' def g := 1"),
    ("comment lookalike inside a guillemet identifier stays code",
     "def «a--b» := 1 -- sorry\n", "def «a--b» := 1"),
]

# Code that must survive *verbatim*, because a stripper that ate it would make
# every positive anchor over that construct silently unsatisfiable.
_PRESERVED: list[tuple[str, str]] = [
    ("string literals are code, not prose",
     'def f := "-- not a comment"\n'),
    ("an escaped quote does not end the string",
     'def f := "a \\" -- still string"\n'),
    ("a raw object-store match is code",
     "match st.objects[oid]? with\n"),
    ("a guillemet identifier quoting a block-comment opener is code",
     "def «x/-y» := 1\n"),
]


# PR #889 review round 5: what `blank_strings` must and must not do.  Each
# case is (name, source, code that must survive, token that must not).
# Blanking is length-preserving, so a blanked literal normalises to `" "`.
_STRING_BLANKED: list[tuple[str, str, str, str]] = [
    ("a string literal's contents are blanked, its quotes kept",
     'def f := IO.println "bootAndInitialisePlatform"\n',
     'def f := IO.println " "', "bootAndInitialisePlatform"),
    ("an escaped quote inside the string is blanked with the rest",
     'def f := "a \\" sorry"\n', 'def f := " "', "sorry"),
    ("a char literal is not a string and survives",
     "def q := '\"'\ndef g := \"sorry\"\n", "def q := '\"' def g := \" \"", "sorry"),
    ("a comment after a blanked string is still a comment",
     'def f := "sorry" -- sorry\n', 'def f := " "', "sorry"),
]


#: Witnesses for `attribute_arguments`: `(name, source, keyword, expected)`.
#: The mutations that matter here **keep** the attribute text and change its
#: structure — a second attribute beside it, a line break after the keyword, a
#: nested bracket, the whole list quoted — because a `find("@[export ")`
#: scanner reads all four wrongly while the token is plainly present.
_ATTRIBUTE_ARGUMENTS: list[tuple[str, str, str, list[str]]] = [
    ("a lone attribute", "@[export lean_alpha]\ndef a := 0\n", "export", ["lean_alpha"]),
    ("a combined attribute list", "@[inline, export lean_alpha]\ndef a := 0\n",
     "export", ["lean_alpha"]),
    ("the keyword last in the list", "@[export lean_alpha, inline]\ndef a := 0\n",
     "export", ["lean_alpha"]),
    ("a line break after the keyword", "@[export\n  lean_alpha]\ndef a := 0\n",
     "export", ["lean_alpha"]),
    ("a nested bracket does not end the list",
     "@[simp, foo[bar], export lean_alpha]\ndef a := 0\n", "export", ["lean_alpha"]),
    ("two attribute lists in one source",
     "@[export lean_alpha]\ndef a := 0\n@[inline, export lean_beta]\ndef b := 1\n",
     "export", ["lean_alpha", "lean_beta"]),
    ("the same name twice is one symbol",
     "@[export lean_alpha]\ndef a := 0\n@[export lean_alpha]\ndef b := 1\n",
     "export", ["lean_alpha"]),
    ("a keyword prefix is not the keyword",
     "@[exported lean_alpha]\ndef a := 0\n", "export", []),
    ("the keyword with no separator is not an attribute",
     "@[exportlean_alpha]\ndef a := 0\n", "export", []),
    ("another attribute's argument is not this one's",
     "@[extern \"ffi_fatal_halt\"]\nopaque h : Unit\n", "export", []),
    ("an `extern` argument is blanked with its string, over a strings-free view",
     "@[extern \"ffi_fatal_halt\"]\nopaque h : Unit\n", "extern", []),
    ("a raw string's body is blanked and its quote is not a delimiter",
     'def s := r#"hi " raw"#\n@[export lean_alpha]\ndef a := 0\n', "export", ["lean_alpha"]),
    ("an attribute quoted inside a raw string is not a live one",
     'def s := r#"@[export lean_beta]"#\n@[export lean_alpha]\ndef a := 0\n',
     "export", ["lean_alpha"]),
    ("a simple raw string still closes at its own quote",
     'def s := r"plain"\n@[export lean_alpha]\ndef a := 0\n', "export", ["lean_alpha"]),
]

#: The same parser over the **strings-kept** view, where a quoted argument is
#: readable: `(name, source, keyword, expected)`.
_ATTRIBUTE_ARGUMENTS_KEPT: list[tuple[str, str, str, list[str]]] = [
    ("a quoted argument is the string's contents",
     '@[extern "ffi_fatal_halt"]\nopaque h : Unit\n', "extern", ["ffi_fatal_halt"]),
    ("a quoted argument in a combined list",
     '@[inline, extern "ffi_fatal_halt_all"]\nopaque h : Unit\n', "extern",
     ["ffi_fatal_halt_all"]),
    ("a commented-out quoted argument is not one",
     '-- @[extern "ffi_fatal_halt"]\nopaque h : Unit\n', "extern", []),
]


def _self_test() -> int:
    failures = 0
    for name, source, keyword, want in _ATTRIBUTE_ARGUMENTS:
        got = attribute_arguments(code_no_strings(source), keyword)
        if got != want:
            failures += 1
            print(f"[lean-code-view] FAIL attribute_arguments {name}: "
                  f"want {want!r}, got {got!r}")
    for name, source, keyword, want in _ATTRIBUTE_ARGUMENTS_KEPT:
        got = attribute_arguments(strip(source), keyword)
        if got != want:
            failures += 1
            print(f"[lean-code-view] FAIL attribute_arguments (strings kept) {name}: "
                  f"want {want!r}, got {got!r}")
    quoted = 'def doc : String := "@[export lean_alpha]"\n'
    if attribute_arguments(code_no_strings(quoted), "export"):
        failures += 1
        print("[lean-code-view] FAIL attribute_arguments: an attribute quoted in a "
              "string literal was read as a live one")
    commented = "-- @[inline, export lean_alpha]\ndef a := 0\n"
    if attribute_arguments(code_no_strings(commented), "export"):
        failures += 1
        print("[lean-code-view] FAIL attribute_arguments: a commented-out attribute "
              "was read as a live one")
    for name, src, want_code, token in _STRING_BLANKED:
        got = code_no_strings(src)
        if " ".join(got.split()) != want_code:
            failures += 1
            print(f"[lean-code-view] FAIL {name}: code\n  want {want_code!r}\n"
                  f"  got  {' '.join(got.split())!r}")
        if token in got:
            failures += 1
            print(f"[lean-code-view] FAIL {name}: string token survived blanking")
        if len(got) != len(src):
            failures += 1
            print(f"[lean-code-view] FAIL {name}: geometry changed under string blanking")
        if token not in strip(src) and "--" not in src:
            failures += 1
            print(f"[lean-code-view] FAIL {name}: string contents blanked by default")
    for name, src, want_code in _CASES:
        got = strip(src)
        if " ".join(got.split()) != want_code:
            failures += 1
            print(f"[lean-code-view] FAIL {name}: code\n  want {want_code!r}\n"
                  f"  got  {' '.join(got.split())!r}")
        if "sorry" in got:
            failures += 1
            print(f"[lean-code-view] FAIL {name}: prose token survived stripping")
        if len(got) != len(src):
            failures += 1
            print(f"[lean-code-view] FAIL {name}: geometry changed")

    for name, src in _PRESERVED:
        got = strip(src)
        if got != src:
            failures += 1
            print(f"[lean-code-view] FAIL {name}: code was altered\n"
                  f"  want {src!r}\n  got  {got!r}")

    # Unterminated block comments must raise, not silently blank the rest.
    try:
        strip("/- open forever\ndef f := 1\n")
    except UnterminatedComment:
        pass
    else:
        failures += 1
        print("[lean-code-view] FAIL: unterminated block comment did not raise")

    # The property the gates rely on, checked over the real tree rather than
    # over fixtures: stripping never moves a byte, so `rg -n` line numbers on
    # the view are line numbers in the source.
    checked = 0
    for path in _lean_files(["SeLe4n", "tests"]):
        src = open(path, encoding="utf-8").read()
        got = strip(src)
        checked += 1
        if len(got) != len(src) or got.count("\n") != src.count("\n"):
            failures += 1
            print(f"[lean-code-view] FAIL: geometry changed for {path}")
        if any(a != b and b != " " for a, b in zip(src, got)):
            failures += 1
            print(f"[lean-code-view] FAIL: {path} changed a character to something other than a space")
    if checked < 100:
        failures += 1
        print(f"[lean-code-view] FAIL: only {checked} files walked; the tree scan is not running")

    # The overlay lifecycle, on a throwaway source tree (never the real repo):
    # build mirrors a .lean, refresh PRUNES a deleted source's mirror — file
    # and directory both.  Without the prune, a deleted file's stale mirror
    # keeps satisfying positive anchors locally while a fresh CI checkout
    # fails them; a witness that only checked the build half would attest to
    # nothing about that.
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        srcdir = os.path.join(tmp, "repo")
        os.makedirs(os.path.join(srcdir, "Sub"))
        keep = os.path.join(srcdir, "Keep.lean")
        gone = os.path.join(srcdir, "Sub", "Gone.lean")
        with open(keep, "w", encoding="utf-8") as fh:
            fh.write("def keep := 1 -- comment\n")
        with open(gone, "w", encoding="utf-8") as fh:
            fh.write("def gone := 2\n")
        out = os.path.join(tmp, "view")
        overlay(out, repo=srcdir)
        mirror_keep = os.path.join(out, "Keep.lean")
        mirror_gone = os.path.join(out, "Sub", "Gone.lean")
        if not (os.path.isfile(mirror_keep) and os.path.isfile(mirror_gone)):
            failures += 1
            print("[lean-code-view] FAIL: overlay did not mirror the throwaway tree")
        elif "comment" in open(mirror_keep, encoding="utf-8").read():
            failures += 1
            print("[lean-code-view] FAIL: overlay mirror kept a comment")
        os.unlink(gone)
        os.rmdir(os.path.dirname(gone))
        overlay(out, repo=srcdir)
        if os.path.exists(mirror_gone) or os.path.isdir(os.path.dirname(mirror_gone)):
            failures += 1
            print("[lean-code-view] FAIL: a deleted source's stale mirror survived the "
                  "refresh — the prune is not running, and a positive anchor for a "
                  "deleted symbol would still pass locally")
        if not os.path.isfile(mirror_keep):
            failures += 1
            print("[lean-code-view] FAIL: the prune removed a mirror whose source exists")

    if failures:
        print(f"[lean-code-view] SELF-TEST FAILED ({failures})")
        return 1
    cases = (len(_CASES) + len(_PRESERVED) + len(_STRING_BLANKED)
             + len(_ATTRIBUTE_ARGUMENTS)
             + len(_ATTRIBUTE_ARGUMENTS_KEPT) + 2)
    print(f"[lean-code-view] SELF-TEST PASS ({cases} cases, "
          f"{checked} tree files, overlay prune witnessed)")
    return 0


def _lean_files(roots: list[str]) -> list[str]:
    repo = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    found = []
    for root in roots:
        base = os.path.join(repo, root)
        if os.path.isfile(base):
            if base.endswith(".lean"):
                found.append(base)
            continue
        for dirpath, _dirs, files in os.walk(base):
            for f in files:
                if f.endswith(".lean"):
                    found.append(os.path.join(dirpath, f))
    return sorted(found)


def overlay(outdir: str, repo: str | None = None) -> str:
    """Build a whole-repo overlay whose `.lean` files are comment-free.

    Every `.lean` file is a real, stripped file; everything else — fixtures,
    Rust, scripts, docs, the lakefile — is a symlink to the original.  A text
    scan then needs no argument rewriting at all: run it with this directory as
    the working directory and every relative path in the check resolves, with
    `.lean` reads seeing code and only code.

    That matters more than the convenience.  Argument rewriting would have to
    understand each check's shape, and 40 of this repo's anchors are inline
    shell (`bash -lc "! rg … F.lean"`) where the path is inside a string.  A
    mechanism that covers the easy 1594 and quietly skips the awkward 40 is the
    partial-coverage failure this whole change is about.

    `.git` and `.lake` are linked whole rather than walked: they are large, and
    neither holds a `.lean` file any gate reads.

    Refreshing also **prunes**: an overlay entry whose source file no longer
    exists is removed, directories included.  Without this the overlay only
    ever grows, and a `.lean` file deleted from the repo leaves a stale
    stripped mirror behind — which a positive anchor for a deleted symbol
    would still match, locally, while a fresh CI checkout (empty overlay)
    failed it.  Local-green-CI-red divergence is the exact failure shape the
    shellcheck gap produced twice in this PR, so the overlay must not be able
    to manufacture a third instance.

    `repo` defaults to this repository; the parameter exists so the self-test
    can exercise build/refresh/prune against a throwaway source tree without
    touching the real one.
    """
    if repo is None:
        repo = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    os.makedirs(outdir, exist_ok=True)

    def prune(dirpath: str) -> None:
        rel = os.path.relpath(dirpath, outdir)
        src_dir = repo if rel == "." else os.path.join(repo, rel)
        for entry in os.scandir(dirpath):
            src = os.path.join(src_dir, entry.name)
            if entry.is_symlink() or entry.is_file(follow_symlinks=False):
                # lexists, not exists: a symlink whose target moved still has a
                # live source entry and is repaired by link(), not pruned.
                if not os.path.lexists(src):
                    os.unlink(entry.path)
            elif entry.is_dir(follow_symlinks=False):
                if not os.path.isdir(src):
                    shutil.rmtree(entry.path)
                else:
                    prune(entry.path)

    prune(outdir)

    def link(src: str, dest: str) -> None:
        if os.path.islink(dest):
            if os.readlink(dest) == src:
                return
            os.unlink(dest)
        elif os.path.exists(dest):
            return
        os.symlink(src, dest)

    for dirpath, dirs, files in os.walk(repo):
        rel = os.path.relpath(dirpath, repo)
        if rel == ".":
            rel = ""
        # Do not descend into these; link them whole.
        for opaque in (".git", ".lake"):
            if opaque in dirs:
                dirs.remove(opaque)
                link(os.path.join(dirpath, opaque), os.path.join(outdir, rel, opaque))
        if outdir.startswith(dirpath + os.sep):
            # Never mirror the overlay into itself.
            skip = os.path.relpath(outdir, dirpath).split(os.sep)[0]
            if skip in dirs:
                dirs.remove(skip)
        os.makedirs(os.path.join(outdir, rel), exist_ok=True)
        for f in files:
            src = os.path.join(dirpath, f)
            dest = os.path.join(outdir, rel, f)
            if not f.endswith(".lean"):
                link(src, dest)
                continue
            if (os.path.exists(dest) and not os.path.islink(dest)
                    and os.path.getmtime(dest) >= os.path.getmtime(src)):
                continue
            if os.path.islink(dest):
                os.unlink(dest)
            with open(dest, "w", encoding="utf-8") as fh:
                fh.write(strip(open(src, encoding="utf-8").read()))
    return outdir


def main(argv: list[str]) -> int:
    if not argv:
        print(__doc__)
        return 2
    if argv[0] == "--self-test":
        return _self_test()
    if argv[0] == "--overlay":
        if len(argv) != 2:
            print("usage: lean_code_view.py --overlay DIR", file=sys.stderr)
            return 2
        print(overlay(argv[1]))
        return 0
    for path in argv:
        sys.stdout.write(strip(open(path, encoding="utf-8").read()))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
