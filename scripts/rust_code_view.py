#!/usr/bin/env python3
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
"""A structural *view* of Rust source, so gates read programs and not lines.

WS-RR RR1.12 (PR #883 review round 3).

The repository's Rust-scanning gates -- the TLBI broadcast discipline, the
cross-target configuration gate, `build.rs`'s own guard scanners -- each
carried a private four-line stripper of the form ``line[:line.find("//")]``
and answered scope questions with "the last ``fn`` declared before this
offset".  Both proxies are wrong in ways that are invisible until someone
writes the code that exposes them:

  * ``asm!("// note", "tlbi vmalle1")`` is two template lines joined with a
    newline.  The ``//`` opens a comment *for the assembler*, on its own
    line; the ``tlbi`` on the next line is emitted.  A line-based stripper
    truncates at the ``//`` -- inside a string literal -- and deletes the
    instruction from the view.  The containment gate then reports no
    emission where the assembler emits one.
  * ``static BAD: fn() = crate::tlb::tlbi_vmalle1;`` at module scope, placed
    after an allowlisted function, is attributed to that function by a
    last-declaration-wins scan, so it inherits an exemption written for
    somebody else's body.

Both are the same defect: *a presence check is not a relation check*
(CLAUDE.md).  The relations here are "is this text inside a string literal"
and "is this offset inside that function's body", and neither can be
recovered from a line once the line has been sliced.  So this module
supplies the structure instead, once, for every Rust gate to share --
exactly as `lean_code_view` does for the Lean tree.

Three views, all byte-aligned with the original so `offset` and line
numbers computed over a view point at real positions in the real file:

  * `code(text)` blanks comments and KEEPS string contents.  A string
    literal is not prose: it is data the compiler or the assembler consumes.
    This is the view for "what instruction does this `asm!` emit".
  * `code_no_strings(text)` blanks comments AND string interiors, keeping
    the delimiters.  This is the view for "is this identifier referenced",
    where a name inside a string is a mention rather than a reference.
  * `fn_bodies(text)` brace-matches every `fn` body over the
    `code_no_strings` view, so a brace inside a literal cannot desynchronise
    the nesting, and `enclosing_fn` answers with the INNERMOST body
    containing an offset -- or `<file scope>`, which is the honest answer
    for a module-level item and the one that fails a gate closed.

Deliberately a *view*, not a rewrite: nothing here edits a source file.

Usage:
  rust_code_view.py FILE...        print the code view of each file
  rust_code_view.py --no-strings FILE...
  rust_code_view.py --self-test    run the witness suite

Exits 0 when clean, 1 on a self-test failure.
"""

from __future__ import annotations

import functools
import re
import ast
import io
import tokenize
from pathlib import Path
import sys

FILE_SCOPE = "<file scope>"


class UnterminatedLiteral(Exception):
    """A comment or string literal ran to end of file.

    Raised rather than tolerated, for `lean_code_view`'s reason: silently
    blanking the remainder hands every positive check an empty file (loudly
    wrong) and every negative check a clean bill of health (quietly wrong),
    and the quiet direction is the one that lets a defect ship.
    """


def _blank(text: str) -> str:
    """Replace every character with a space, keeping newlines in place."""
    return "".join("\n" if ch == "\n" else " " for ch in text)


# Memoised (the four public views and the scanner beneath them): each is a pure
# function of its text, and the Tier 0 gates ask for the same few dozen sources
# many times over -- `fn_bodies` alone scanned each file three times per call
# (once for `code`, again for `code_no_strings`, again itself), and the TLBI
# gate called it per pass.  The cache is keyed on the text, so a fixture that
# is edited between calls is re-scanned; only identical text is reused.
@functools.lru_cache(maxsize=None)
def _scan(src: str) -> list[tuple[str, int, int]]:
    """Classify `src` into ``(kind, start, end)`` spans.

    `kind` is one of ``code``, ``comment``, ``string`` (the literal
    including its delimiters) or ``string_body`` (its interior only).
    Spans of kind ``string`` and ``string_body`` overlap by construction:
    the body is reported as a separate span nested in the literal, so a
    caller can blank the interior while keeping the quotes.
    """
    spans: list[tuple[str, int, int]] = []
    i, n = 0, len(src)
    code_start = 0

    def close_code(at: int) -> None:
        if at > code_start:
            spans.append(("code", code_start, at))

    while i < n:
        ch = src[i]
        # --- comments -----------------------------------------------------
        if ch == "/" and i + 1 < n and src[i + 1] == "/":
            close_code(i)
            end = src.find("\n", i)
            end = n if end < 0 else end
            spans.append(("comment", i, end))
            i = code_start = end
            continue
        if ch == "/" and i + 1 < n and src[i + 1] == "*":
            close_code(i)
            start, depth, i = i, 0, i
            while i < n:
                if src.startswith("/*", i):
                    depth += 1
                    i += 2
                elif src.startswith("*/", i):
                    depth -= 1
                    i += 2
                    if depth == 0:
                        break
                else:
                    i += 1
            else:
                raise UnterminatedLiteral(
                    f"block comment opened at offset {start} is unterminated"
                )
            if depth != 0:
                raise UnterminatedLiteral(
                    f"block comment opened at offset {start} is unterminated"
                )
            spans.append(("comment", start, i))
            code_start = i
            continue
        # --- raw strings: r"..", r#".."#, br#".."#, cr#".."# ---------------
        raw = re.match(r'(?:b|c)?r(#*)"', src[i:])
        if raw and (i == 0 or not _is_ident_char(src[i - 1])):
            close_code(i)
            hashes = raw.group(1)
            body_start = i + raw.end()
            terminator = '"' + hashes
            end = src.find(terminator, body_start)
            if end < 0:
                raise UnterminatedLiteral(
                    f"raw string opened at offset {i} is unterminated"
                )
            stop = end + len(terminator)
            spans.append(("string", i, stop))
            spans.append(("string_body", body_start, end))
            i = code_start = stop
            continue
        # --- ordinary and byte/C strings ----------------------------------
        if ch == '"' or (
            ch in "bc"
            and i + 1 < n
            and src[i + 1] == '"'
            and (i == 0 or not _is_ident_char(src[i - 1]))
        ):
            close_code(i)
            quote_at = i if ch == '"' else i + 1
            body_start = quote_at + 1
            j = body_start
            while j < n:
                if src[j] == "\\":
                    j += 2
                    continue
                if src[j] == '"':
                    break
                j += 1
            else:
                raise UnterminatedLiteral(
                    f"string opened at offset {i} is unterminated"
                )
            if j >= n:
                raise UnterminatedLiteral(
                    f"string opened at offset {i} is unterminated"
                )
            spans.append(("string", i, j + 1))
            # An `extern "C"` ABI string is SYNTAX, not data: blanking it
            # turns `pub extern "C" fn f` into `pub extern " " fn f` and a
            # scanner looking for the signature stops finding it -- which
            # is fail-open for any check that a required export still
            # exists.  So ABI strings stay in both views.
            if not _preceded_by_keyword(src, i, "extern"):
                spans.append(("string_body", body_start, j))
            i = code_start = j + 1
            continue
        # --- char literal vs lifetime -------------------------------------
        if ch == "'":
            end = _char_literal_end(src, i)
            if end is not None:
                close_code(i)
                spans.append(("string", i, end))
                spans.append(("string_body", i + 1, end - 1))
                i = code_start = end
                continue
            # A lifetime or a loop label: ordinary code.
        i += 1
    close_code(n)
    return spans


def _preceded_by_keyword(src: str, at: int, keyword: str) -> bool:
    """Is the token immediately before `at` exactly `keyword`?"""
    head = src[:at].rstrip()
    return head.endswith(keyword) and (
        len(head) == len(keyword) or not _is_ident_char(head[-len(keyword) - 1])
    )


def _is_ident_char(ch: str) -> bool:
    return ch.isalnum() or ch == "_"


def _char_literal_end(src: str, start: int) -> int | None:
    """End offset of the char literal at `start`, or None for a lifetime.

    ``'a'`` is a literal; ``'a`` in ``&'a str`` or ``'outer: loop`` is not.
    The distinguishing rule is that a literal closes on a ``'`` after one
    character (or one escape sequence), and a lifetime never does.
    """
    n = len(src)
    j = start + 1
    if j >= n:
        return None
    if src[j] == "\\":
        j += 2
        # `\u{...}` and friends: run to the closing quote.
        while j < n and src[j] != "'":
            j += 1
        return j + 1 if j < n and src[j] == "'" else None
    # A single (possibly multi-byte) character followed by a quote.
    j += 1
    return j + 1 if j < n and src[j] == "'" else None


@functools.lru_cache(maxsize=None)
def code(text: str) -> str:
    """Comments blanked; string contents preserved, byte-aligned."""
    out = list(text)
    for kind, start, end in _scan(text):
        if kind == "comment":
            out[start:end] = _blank(text[start:end])
    return "".join(out)


@functools.lru_cache(maxsize=None)
def code_no_strings(text: str) -> str:
    """Comments and string interiors blanked; delimiters kept, byte-aligned."""
    out = list(code(text))
    for kind, start, end in _scan(text):
        if kind == "string_body":
            out[start:end] = _blank(text[start:end])
    return "".join(out)


def keyword(word: str) -> str:
    """The regex fragment matching the Rust keyword `word`, and not an
    identifier that merely spells it.

    **One spelling, because three review rounds proved that two diverge.**
    `r#unsafe`, `r#extern` and `r#fn` are ordinary identifiers -- Rust's raw
    escape lets any keyword name an item -- and a bare word-boundary spelling
    matches inside one, because `#` is a non-word character and the boundary
    falls between it and the letter.  A scanner using the bare form therefore
    reads `struct r#extern { … }` as a foreign block and `struct r#unsafe { … }`
    as an unsafe block: it invents an obligation against safe code, and Tier 0
    refuses valid Rust.

    The rule itself was never in doubt.  What kept failing is that each gate
    spelled the question again: `v0.35.17` put the exclusion on the unsafe
    gate's keyword scan for `r#unsafe`, `v0.35.21` put the identical exclusion
    on this module's `extern` scan for `r#extern`, and the review round after
    *that* found six more bare spellings in the same file as the one carrying
    the rule -- one of them ten lines below the comment explaining it.

    That is this project's enumeration-versus-derivation rule at the level of a
    regex fragment, and it does not close by patching a sixth site.  It closes
    by there being one fragment to compose and a check that refuses a new bare
    one: `bare_keyword_literals` reads the gate sources and reports any
    word-boundary keyword spelling written outside this helper, so the next
    pattern cannot be written without the rule rather than merely being
    reviewed for it.
    """
    return r"(?<!r#)\b" + word + r"\b"


#: The keywords a scanner in this tree matches, and therefore the ones
#: `bare_keyword_literals` refuses to see spelled bare.  Deliberately the set
#: the gates actually ask about rather than Rust's whole reserved list: a
#: keyword nothing scans for needs no fragment, and listing it would be an
#: enumeration with no consumer.
SCANNED_KEYWORDS = ("unsafe", "extern", "impl", "trait", "mod", "struct", "fn")


def _gate_sources() -> list[Path]:
    """The gate sources the keyword discipline governs.

    Derived from the directory rather than listed, so a gate added later is
    scanned the day it lands -- the enumeration-versus-derivation rule applied
    to this check's own domain, since a hand-written file list is exactly what
    would let the eighth bare spelling in.
    """
    here = Path(__file__).resolve().parent
    return sorted(
        path for path in here.glob("*.py")
        if path.name.startswith(("check_", "rust_code_view", "lean_code_view"))
    )


#: A word-boundary spelling of a Rust keyword, which `keyword()` exists to
#: replace.  Built from `SCANNED_KEYWORDS` so the two cannot drift, and spelled
#: through `chr(92)` so this pattern is not itself an instance of what it
#: forbids -- a scanner that trips on its own definition is the kind of
#: self-reference that gets "fixed" by weakening the check.
_BARE_KEYWORD_LITERAL = re.compile(
    chr(92) * 2 + "b(?:" + "|".join(SCANNED_KEYWORDS) + ")" + chr(92) * 2 + "b")


def _python_code_view(text: str) -> str:
    """`text` with comments and docstrings blanked, byte-aligned, code kept.

    **Gates read code, prose reads prose**, applied to this project's own
    scanners.  The subject here is a regex *fragment* -- a string literal that
    is evaluated -- so a `#` comment and a docstring are both prose, and both
    are blanked.  That is not a convenience: `keyword`'s own docstring quotes
    the bad spelling precisely in order to say why it is wrong, and a check that
    counted it would force this file to stop explaining itself, which is this
    project's rule against contorting prose to satisfy a scanner.

    The docstring spans come from `ast`, not from a quote-state walk, because
    which string literals are documentation is a question about Python's grammar
    and Python answers it exactly: a bare string expression statement is a
    docstring wherever it appears, while an f-string, a concatenation or a
    string in argument position is not.  Byte alignment is preserved so the line
    numbers reported are the file's own.
    """
    out = list(text)

    def blank(lo: int, hi: int) -> None:
        for index in range(lo, min(hi, len(out))):
            if out[index] != "\n":
                out[index] = " "

    line_starts = [0]
    for line in text.splitlines(keepends=True):
        line_starts.append(line_starts[-1] + len(line))

    def offset(lineno: int, col: int) -> int:
        return line_starts[lineno - 1] + col

    try:
        tree = ast.parse(text)
    except SyntaxError:
        # A file that does not parse is not one this check can read.  Leaving
        # the text unscrubbed is the fail-CLOSED direction here, because this
        # scanner produces a set of *violations*: reading too much reports a
        # spurious one and stops the build, where reading too little passes
        # silently.
        tree = None

    if tree is not None:
        for node in ast.walk(tree):
            if not isinstance(node, ast.Expr):
                continue
            value = node.value
            if isinstance(value, ast.Constant) and isinstance(value.value, str):
                blank(offset(value.lineno, value.col_offset),
                      offset(value.end_lineno, value.end_col_offset))

    try:
        tokens = list(tokenize.generate_tokens(io.StringIO(text).readline))
    except (tokenize.TokenError, IndentationError):
        tokens = []
    for token in tokens:
        if token.type == tokenize.COMMENT:
            blank(offset(*token.start), offset(*token.end))

    return "".join(out)


def bare_keyword_literals() -> list[str]:
    """Every word-boundary Rust-keyword spelling written outside `keyword()`.

    **The mechanism, rather than a sixth patch.**  Three review rounds in a row
    found a keyword pattern missing the raw-identifier exclusion that a sibling
    pattern -- once ten lines away, in the same file, under a comment explaining
    the rule -- already carried.  Each round's remedy was correct and none of
    them stopped the next one: fixing a site does not reach the site nobody has
    written yet, and sharing a walk does not make a *new* regex inherit what the
    old one learned.

    So the rule is enforced where it can fail closed.  A contributor who writes
    the bare spelling in a gate gets a self-test failure naming the file and the
    line, on the day they write it, instead of a review round finding it two
    cuts later.
    """
    out: list[str] = []
    for path in _gate_sources():
        text = path.read_text(encoding="utf-8")
        scrubbed = _python_code_view(text)
        for match in _BARE_KEYWORD_LITERAL.finditer(scrubbed):
            line = scrubbed.count("\n", 0, match.start()) + 1
            out.append(f"{path.name}:{line}: {match.group(0)} "
                       f"-- compose rust_code_view.keyword(...) instead")
    return out


#: A `fn` and its name.  `r#` is Rust's raw-identifier escape and is part of
#: the *spelling*, not the name — `fn r#lean_real()` is the function
#: `lean_real` and links under that symbol (PR #889 review round 25, swept
#: from the sibling finding against `check_kernel_entry_exports.py`).  Without
#: it the name read as `r`, so every allowlist entry, exemption and dominance
#: attribution keyed on the enclosing function's name looked at the wrong one.
_FN_RE = re.compile(keyword("fn") + r"\s+(?:r#)?([A-Za-z_][A-Za-z0-9_]*)")


@functools.lru_cache(maxsize=None)
def fn_bodies(text: str) -> list[tuple[str, int, int]]:
    """Every ``fn`` body as ``(name, body_start, body_end)``, outermost first.

    Brace-matched over `code_no_strings`, so a brace inside a literal cannot
    desynchronise the nesting.  Bodies are reported for nested functions too;
    `enclosing_fn` picks the innermost.

    A `fn` whose signature is followed by ``;`` before any ``{`` -- a trait
    method declaration or an ``extern`` block entry -- has no body and is
    skipped, rather than being given the *next* item's braces.
    """
    view = code_no_strings(text)
    bodies: list[tuple[str, int, int]] = []
    for match in _FN_RE.finditer(view):
        opened = _body_open_brace(view, match.end())
        if opened is None:
            continue
        end = _matching_brace(view, opened)
        if end is None:
            continue
        bodies.append((match.group(1), opened + 1, end))
    return bodies


def _body_open_brace(view: str, after_name: int) -> int | None:
    """Offset of the ``{`` opening the body of the `fn` named just before.

    Skips the parameter list by paren-matching, then takes the first ``{``
    that follows -- which is the body's, since a return type or ``where``
    clause introduces none in any form this tree uses.  A ``;`` reached
    first means the `fn` is a declaration without a body.
    """
    i = view.find("(", after_name)
    if i < 0:
        return None
    depth = 0
    while i < len(view):
        if view[i] == "(":
            depth += 1
        elif view[i] == ")":
            depth -= 1
            if depth == 0:
                i += 1
                break
        i += 1
    else:
        return None
    while i < len(view):
        if view[i] == "{":
            return i
        if view[i] == ";":
            return None
        i += 1
    return None


def _matching_brace(view: str, opened: int) -> int | None:
    depth = 0
    for offset in range(opened, len(view)):
        if view[offset] == "{":
            depth += 1
        elif view[offset] == "}":
            depth -= 1
            if depth == 0:
                return offset
    return None


def enclosing_fn(text: str, offset: int, bodies=None) -> str:
    """Name of the INNERMOST `fn` whose body contains `offset`.

    Returns `FILE_SCOPE` for a module-level item.  That is the honest answer
    -- a `static` between two functions belongs to neither -- and it is the
    fail-closed one: an allowlist keyed on function names cannot match it,
    so a module-scope reference is reported rather than silently inheriting
    the exemption of whichever function happens to precede it.
    """
    if bodies is None:
        bodies = fn_bodies(text)
    best: tuple[str, int] | None = None
    for name, start, end in bodies:
        if start <= offset < end and (best is None or start > best[1]):
            best = (name, start)
    return best[0] if best else FILE_SCOPE


def top_level_statements(view: str, start: int, end: int) -> list[tuple[int, int]]:
    """The top-level statements of a Rust block interior ``[start, end)`` as
    ``(lo, hi)`` spans over a string-free view: a statement ends at a ``;``
    at brace depth zero, or at the ``}`` that closes a depth-zero block not
    followed by ``else``.  The Python twin of ``build.rs``'s
    ``top_level_statements_in``, shared here (PR #889 review round 8) so
    every gate that asks a question of a function's statements asks it of
    the same shape.
    """
    out: list[tuple[int, int]] = []
    depth = 0
    paren = 0
    stmt_start = start
    i = start
    while i < end:
        c = view[i]
        if c in "([":
            paren += 1
        elif c in ")]":
            paren -= 1
        elif c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0 and paren == 0:
                nxt = i + 1
                while nxt < end and view[nxt].isspace():
                    nxt += 1
                if not view[nxt:end].startswith("else"):
                    stmt_end = nxt + 1 if nxt < end and view[nxt] == ";" else i + 1
                    out.append((stmt_start, stmt_end))
                    stmt_start = stmt_end
                    i = stmt_end
                    continue
        elif c == ";" and depth == 0 and paren == 0:
            out.append((stmt_start, i + 1))
            stmt_start = i + 1
        i += 1
    if view[stmt_start:end].strip():
        out.append((stmt_start, end))
    return out


def statement_containing(
    statements: list[tuple[int, int]], offset: int
) -> tuple[int, int] | None:
    """The ``(lo, hi)`` statement span holding ``offset``, if any."""
    return next(((lo, hi) for lo, hi in statements if lo <= offset < hi), None)


def binding_statement_before(
    view: str, statements: list[tuple[int, int]], name: str, upto: tuple[int, int]
) -> tuple[int, int] | None:
    """The LAST top-level statement strictly before ``upto`` that gives
    ``name`` a new value — a ``let [mut] <name>`` binding **or** an
    assignment ``<name> = …`` (PR #889 review rounds 8 and 9).

    A receiver's *spelling* does not identify a value: ``let mut asm = …;
    asm.file("ghost.S"); let mut asm = …; asm.file("real.S").compile(…)`` is
    valid Rust in which the first ``.file`` reaches nothing the compile
    sees.  Rust resolves a name to its most recent binding in scope, so the
    gates do the same: a use belongs to the last binding of that name before
    the use.

    Round 9: a ``mut`` receiver is rebound by **assignment** as well, with no
    second ``let`` — ``let mut asm = …; asm.file("ghost.S"); asm =
    cc::Build::new(); asm.file("real.S").compile(…)`` discards the first
    builder just as the shadowing form does, and a ``let``-only rule left the
    window open at the original binding.  An assignment is therefore a
    binding boundary too; a compound assignment (``+=``) is not, since it
    keeps the value, and ``==`` is a comparison.

    Returns ``None`` when the block gives ``name`` no value — a parameter, a
    captured variable or a temporary — which the callers treat as fail-closed
    (nothing before the using statement counts).
    """
    pattern = re.compile(
        r"^\s*(?:let\s+(?:mut\s+)?" + re.escape(name) + r"\b"
        r"|" + re.escape(name) + r"\s*=(?!=))"
    )
    found: tuple[int, int] | None = None
    for lo, hi in statements:
        # A `let` binds from the statement AFTER it: a use inside the binding
        # statement's own initialiser refers to the previous binding, so the
        # using statement itself is never its own instance.
        if lo >= upto[0]:
            break
        if pattern.match(view[lo:hi]):
            found = (lo, hi)
    return found


# ---------------------------------------------------------------------------
# `extern` blocks.
#
# **One question, one answer.**  Two gates parse foreign blocks — the kernel
# entry gate, which derives link requirements from them, and the unsafe-site
# gate, which derives justification requirements — and they diverged exactly the
# way this project keeps paying for: PR #889 review round 21 taught the first to
# refuse an item macro, round 25 taught it to refuse every other unreadable
# item, and PR #895 review round 7 found the second still scanning for `fn` and
# silently examining nothing else.  The remedy for a question answered in two
# places is not to answer it correctly twice; it is to answer it here.
#
# Extraction stays with the caller: what a `fn` item *means* differs between the
# two (a linker symbol with `#[link_name]` applied, versus an unsafe obligation
# with the edition-2024 `safe` opt-out).  Only the CLASSIFICATION is shared.
# ---------------------------------------------------------------------------

#: The `extern` keyword.  Whether it opens a block is decided structurally by
#: `extern_blocks`, never by a spelling: `extern r"C" {`, `extern {` and
#: `extern "C-unwind" {` are all foreign blocks, and the ABI names a calling
#: convention rather than changing what the block declares.
#:
#: **A raw identifier is not the keyword** (PR #895 review round 8).  Rust
#: permits an ordinary item named `r#extern` — `mod r#extern { … }`,
#: `struct r#extern { … }` — and `\bextern\b` matches inside it, so the item's
#: own body was read as a foreign block: the unsafe gate then invented
#: obligations for safe module functions and the entry gate rejected valid Rust
#: as an unknown foreign item.  The identical exclusion sits on
#: `UNSAFE_KEYWORD` in `check_unsafe_block_justifications.py`, added for
#: `r#unsafe` one review round earlier and not swept here — which is this
#: project's sweep rule failing inside the cut that moved this scanner.
_EXTERN_KEYWORD = re.compile(keyword("extern"))
#: An item macro at item position — `name!(`, `name![` or `name!{`, the three
#: bracket forms Rust accepts.  Matched on a string-free view, so a `!` inside a
#: literal is not one.
_MACRO_INVOCATION = re.compile(r"\b[A-Za-z_][A-Za-z0-9_]*\s*!\s*[(\[{]")
#: A `fn` item.  `r#` is Rust's raw-identifier escape and part of the spelling,
#: not the name.
_EXTERN_FN_ITEM = re.compile(keyword("fn") + r"\s+(?:r#)?[A-Za-z_][A-Za-z0-9_]*\s*\(")
#: An item a foreign block may hold that declares no function: a `static`, a
#: type alias, or a `use`.
_EXTERN_NON_FN_ITEM = re.compile(
    r"|".join(keyword(w) for w in ("static", "type", "use")))


#: **One attribute opener, and every scanner composes it** (PR #895 review
#: round 12).
#:
#: Rust treats a comment as whitespace *between tokens*, so
#: `#/* explanation */[doc = "# Safety"]` is a valid attribute that rustfmt
#: accepts and rustdoc publishes — and on a code view a comment is blanked to
#: spaces, so the `#` and the `[` are simply not adjacent.  Seven scanners in
#: this tree asked "is this an attribute" with a literal `#[`, which made the
#: correctly documented item below that line read as undocumented.
#:
#: The fragment is shared rather than corrected seven times, because this
#: project has now measured twice that stating the sweep rule does not make a
#: new pattern inherit what the old ones learned.  `ATTRIBUTE_OPEN` accepts the
#: inner form too; `OUTER_ATTRIBUTE_OPEN` is the one for a question about the
#: item *below* the line, since `#![…]` documents the enclosing module.
ATTRIBUTE_OPEN = r"#\s*(?:!\s*)?\["
OUTER_ATTRIBUTE_OPEN = r"#\s*(?!!)\["

_ATTRIBUTE_OPEN_RE = re.compile(ATTRIBUTE_OPEN)


def attribute_opens_at(view: str, at: int = 0):
    """End offset of the attribute opener starting at `at`, or `None`.

    The opener is `#`, an optional `!`, and `[`, with token-separating
    whitespace — which is what a blanked comment becomes — permitted between.
    """
    match = _ATTRIBUTE_OPEN_RE.match(view, at)
    return None if match is None else match.end()


def attribute_spans(view: str) -> list[tuple[int, int]]:
    """Byte spans of every `#[…]` / `#![…]` attribute in a STRING-FREE view.

    **Structure from the string-free view; the text a predicate is about from
    the aligned kept one.**  That rule is written down in this project and round
    10 did not follow it: moving doc-attribute recognition onto
    `rust_code_view.code` fixed the commented-out case and left the view's
    *strings* intact, so attribute-shaped text inside an unrelated literal —
    `#[allow(unused, reason = r##"#[doc = "# Safety"]"##)]` — was read as a real
    attached attribute and justified an undocumented `unsafe fn`
    (PR #895 review round 11).

    Pass `code_no_strings` here to find where the attributes *are*, then read
    their values out of the byte-aligned `code` view.  Brackets are matched, so
    a nested `#[…]` inside an attribute's own arguments does not end it early.
    """
    spans: list[tuple[int, int]] = []
    i, n = 0, len(view)
    while i < n:
        if view[i] != "#":
            i += 1
            continue
        opened = attribute_opens_at(view, i)
        if opened is None:
            i += 1
            continue
        j = opened - 1
        if j >= n or view[j] != "[":
            i += 1
            continue
        depth, k = 0, j
        while k < n:
            if view[k] == "[":
                depth += 1
            elif view[k] == "]":
                depth -= 1
                if depth == 0:
                    spans.append((i, k + 1))
                    break
            k += 1
        else:
            # Unterminated: the scanner cannot say where this attribute ends, so
            # it reports nothing rather than guessing an extent.  Callers that
            # build justifications treat a missing attribute as undocumented,
            # which is the fail-closed direction for them.
            break
        i = k + 1
    return spans


def skip_rust_space(view: str, at: int) -> int:
    """Past the whitespace at `at`.  Comments are already blanked in the view,
    so whitespace is all there is to skip."""
    while at < len(view) and view[at].isspace():
        at += 1
    return at


def string_literal_end(view: str, at: int) -> int | None:
    """Just past the string literal starting at `at`, or `None` when there is
    none there.

    Handles the raw forms: `r"…"`, `r#"…"#`, `r##"…"##`.  On the string-free
    view an interior holds no `"` at all (it is blanked to spaces), and on the
    aligned view an ABI string is kept verbatim because it is syntax; both read
    correctly here, since the closer is the first `"` followed by the opener's
    own run of `#`.
    """
    index = at
    hashes = 0
    if index < len(view) and view[index] == "r":
        index += 1
        while index < len(view) and view[index] == "#":
            hashes += 1
            index += 1
    if index >= len(view) or view[index] != '"':
        return None
    index += 1
    closer = '"' + "#" * hashes
    while index < len(view):
        if view[index] == "\\" and hashes == 0:
            index += 2
            continue
        if view.startswith(closer, index):
            return index + len(closer)
        index += 1
    return None


class UnbalancedExternBlock(Exception):
    """An `extern` block whose extent cannot be determined."""

    def __init__(self, offset: int) -> None:
        super().__init__(f"unbalanced `extern` block at offset {offset}")
        self.offset = offset


def extern_blocks(view: str) -> list[tuple[int, int, int]]:
    """Every `extern <abi>? { … }` block, as `(keyword, open brace, close brace)`.

    Brace-matched rather than line-scanned, so a brace in a signature cannot end
    a block early.  An unbalanced block raises: both callers derive
    REQUIREMENTS from these blocks, and a requirement dropped is a check nobody
    runs, so the fail-closed direction here is refusal rather than omission.
    """
    blocks: list[tuple[int, int, int]] = []
    for m in _EXTERN_KEYWORD.finditer(view):
        # Rust's grammar after `extern` is closed: `crate`, an optional ABI
        # **string literal** then `fn`, or an optional ABI literal then `{`.
        # Only the last opens a block, and resolving the literal is what makes
        # the answer independent of how it is spelled — `"C"`, `r"C"`,
        # `r#"C"#`, any convention (PR #889 review round 17, whose check this
        # is; PR #895 review round 7 moved it here so the second gate that asks
        # the question reads the same answer).
        index = skip_rust_space(view, m.end())
        past = string_literal_end(view, index)
        if past is not None:
            index = skip_rust_space(view, past)
        if index >= len(view) or view[index] != "{":
            continue        # `extern "C" fn f()`, an `extern crate`: not a block
        depth, end = 0, None
        for i in range(index, len(view)):
            if view[i] == "{":
                depth += 1
            elif view[i] == "}":
                depth -= 1
                if depth == 0:
                    end = i
                    break
        if end is None:
            raise UnbalancedExternBlock(m.start())
        blocks.append((m.start(), index, end))
    return blocks


def extern_block_items(view: str, start: int, end: int) -> list[tuple[int, int]]:
    """The `;`-terminated items of a foreign block, as spans.

    Each span begins after the previous item's `;` — so it carries that item's
    own attributes — and ends at its own `;`.  Semicolons inside brackets (a
    `[u8; 4]` type) do not terminate an item.

    **Angle brackets are not nesting here** (PR #895 review round 14).  Counting
    `<` and `>` as a bracket pair is wrong in the direction that hides items: a
    valid foreign signature may contain a *shift* — `pub fn f(x: *const [u8; 1 <<
    2]);` — which raises the depth twice with nothing to lower it, so that item's
    own `;` stops terminating and **every following declaration merges into it**.
    Measured: the block then reports one item, the undocumented declaration after
    it is absent from the site count, the unjustified inventory and the empty
    baseline alike, and the gate reports green.  Fail-OPEN, and invisible.

    Dropping them is not a narrowing: a `;` can only appear inside a generic
    position by way of an array type or a const-generic block, and `[` and `{`
    already cover both, so no `;` that must be hidden sits at angle-bracket depth
    alone.  The docstring above always said *brackets*; the code over-reached.
    """
    items: list[tuple[int, int]] = []
    at = start
    depth = 0
    index = start
    while index < end:
        character = view[index]
        if character in "([{":
            depth += 1
        elif character in ")]}":
            depth = max(0, depth - 1)
        elif character == ";" and depth == 0:
            items.append((at, index))
            at = index + 1
        index += 1
    if view[at:end].strip():
        items.append((at, end))
    return items


def classify_extern_item(view: str, start: int, end: int) -> str:
    """What kind of item a foreign block holds: `fn`, `macro`, `non-fn`, `unknown`.

    A `fn` is a function declaration the caller may then read for whatever it
    needs.  A `macro` expands into declarations no `fn`-shaped search can see.
    A `non-fn` is a `static`, a type alias or a `use` — items that genuinely
    declare no function, and the ONLY ones a caller may skip.  Anything else is
    `unknown`, which is a decision rather than a default: an item form no
    scanner here knows is refused by both callers, so a spelling Rust accepts
    and this view does not becomes a build failure on the day it is written
    rather than a silently smaller set of requirements.

    The `fn` test precedes the macro test because a macro *name* may contain the
    letters `fn` only as an identifier, while `_EXTERN_FN_ITEM` requires the
    keyword followed by a name and `(`; an item matching both — `fn f(x: m!());`
    — is a function declaration with a macro in its type, and it is the `fn`
    that declares the symbol.
    """
    if _EXTERN_FN_ITEM.search(view, start, end):
        return "fn"
    if _MACRO_INVOCATION.search(view, start, end):
        return "macro"
    if _EXTERN_NON_FN_ITEM.search(view, start, end):
        return "non-fn"
    return "unknown"


# ---------------------------------------------------------------------------
# Self-test.
#
# A stripper that stops stripping, or one that strips too much, both fail
# silently: the gates reading the view keep reporting PASS.  So every
# distinction this module draws is pinned by a witness, and each witness
# KEEPS the token it is about and changes only the relation -- a `//` moved
# inside a string, a brace moved inside a literal, an item moved outside a
# body -- because a witness that deletes the token is passed by the
# line-based stripper this module replaces.
# ---------------------------------------------------------------------------

_ASM_WITH_COMMENT_LINE = (
    'fn f() {\n'
    '    unsafe { core::arch::asm!("// note", "tlbi vmalle1"); }\n'
    '}\n'
)

_MODULE_SCOPE_ITEM = (
    "fn allowed() {\n"
    "    let _ = 1;\n"
    "}\n"
    "static BAD: fn() = crate::tlb::tlbi_vmalle1;\n"
    "fn other() {\n"
    "    let _ = 2;\n"
    "}\n"
)


def _self_test() -> int:
    failures: list[str] = []

    def check(name: str, condition: bool, detail: str = "") -> None:
        if not condition:
            failures.append(f"{name}: {detail}" if detail else name)

    # --- comments are blanked, byte-aligned ------------------------------
    src = "let a = 1; // trailing\nlet b = 2;\n"
    view = code(src)
    check("line comment blanked", "trailing" not in view)
    check("line comment keeps length", len(view) == len(src))
    check("code survives", "let b = 2;" in view)

    nested = "/* outer /* inner */ still comment */ let a = 1;\n"
    check("nested block comment", "still comment" not in code(nested))
    check("nested block comment ends", "let a = 1;" in code(nested))

    # --- string contents survive `code` ----------------------------------
    # THE relation-breaking witness: the token `tlbi vmalle1` is present in
    # both views; what changes is that a `//` precedes it *inside a string*.
    # A line-based stripper deletes the instruction here.
    check(
        "asm template survives a `//` in a sibling template line",
        "tlbi vmalle1" in code(_ASM_WITH_COMMENT_LINE),
        code(_ASM_WITH_COMMENT_LINE),
    )
    check(
        "a real comment on the same line is still blanked",
        "gone" not in code('let s = "keep"; // gone\n'),
    )
    check("string kept in `code`", "keep" in code('let s = "keep";\n'))

    # --- string contents are blanked by `code_no_strings` ----------------
    stripped = code_no_strings('let s = "tlbi_vae1";\nlet t = 1;\n')
    check("string body blanked", "tlbi_vae1" not in stripped)
    check("delimiters kept", stripped.count('"') == 2)
    check("code after string survives", "let t = 1;" in stripped)

    # --- raw, byte and C strings -----------------------------------------
    for label, text, needle in (
        ("raw string", 'let s = r"a\\b//c";\n', "a\\b//c"),
        ("hashed raw", 'let s = r#"quote " and // here"#;\n', 'quote " and // here'),
        ("byte string", 'let s = b"by//te";\n', "by//te"),
        ("c string", 'let s = c"c//str";\n', "c//str"),
    ):
        check(f"{label} preserved in `code`", needle in code(text), code(text))
        check(f"{label} blanked in `code_no_strings`", needle not in code_no_strings(text))

    # --- escapes ---------------------------------------------------------
    escaped = 'let s = "a\\"// still string"; let t = 1;\n'
    check("escaped quote does not end the string", "still string" in code(escaped))
    check("code after escaped quote survives", "let t = 1;" in code(escaped))

    # --- lifetimes are not char literals ---------------------------------
    life = "fn f<'a>(x: &'a str) -> &'a str { x }\n"
    check("lifetime is code", code_no_strings(life).count("'") == 3, code_no_strings(life))
    check("lifetime body intact", "-> &'a str" in code_no_strings(life))
    chr_lit = "let c = '}'; let d = 1;\n"
    check("char literal blanked", "'}'" not in code_no_strings(chr_lit))
    check("code after char literal survives", "let d = 1;" in code_no_strings(chr_lit))
    esc_chr = "let c = '\\''; let d = 1;\n"
    check("escaped char literal", "let d = 1;" in code_no_strings(esc_chr))

    # --- function bodies --------------------------------------------------
    bodies = dict((n, (s, e)) for n, s, e in fn_bodies(_MODULE_SCOPE_ITEM))
    check("both fns found", set(bodies) == {"allowed", "other"}, str(sorted(bodies)))
    at = _MODULE_SCOPE_ITEM.index("crate::tlb::tlbi_vmalle1")
    # THE relation-breaking witness for scope: the reference is present and
    # `allowed` is present; only the reference's POSITION relative to the
    # body changes.  Last-declaration-wins answers `allowed`.
    check(
        "module-scope item is file scope, not the preceding fn",
        enclosing_fn(_MODULE_SCOPE_ITEM, at) == FILE_SCOPE,
        enclosing_fn(_MODULE_SCOPE_ITEM, at),
    )
    inside = "fn a() {\n    let x = TOKEN;\n}\n"
    check(
        "a reference inside a body is attributed to it",
        enclosing_fn(inside, inside.index("TOKEN")) == "a",
    )

    nested_fn = "fn outer() {\n    fn inner() {\n        TOKEN;\n    }\n}\n"
    check(
        "innermost body wins",
        enclosing_fn(nested_fn, nested_fn.index("TOKEN")) == "inner",
        enclosing_fn(nested_fn, nested_fn.index("TOKEN")),
    )

    # PR #889 review round 25: `r#` is part of the spelling, not the name.
    # The mutation KEEPS the `fn`, the body and the name and only escapes it —
    # which read `r`, so every lookup keyed on the enclosing function's name
    # (an allowlist entry, an exemption, a gate attribution) missed.
    raw_fn = "fn r#lean_raw() {\n    TOKEN;\n}\n"
    check(
        "a raw-identifier `fn` is named without its escape",
        enclosing_fn(raw_fn, raw_fn.index("TOKEN")) == "lean_raw",
        enclosing_fn(raw_fn, raw_fn.index("TOKEN")),
    )

    brace_in_string = 'fn a() {\n    let s = "}";\n    TOKEN;\n}\nstatic S: u8 = 0;\n'
    check(
        "a brace inside a literal does not close the body",
        enclosing_fn(brace_in_string, brace_in_string.index("TOKEN")) == "a",
        enclosing_fn(brace_in_string, brace_in_string.index("TOKEN")),
    )
    after = brace_in_string.index("static S")
    check(
        "and the item after the body is still file scope",
        enclosing_fn(brace_in_string, after) == FILE_SCOPE,
    )

    abi = 'pub extern "C" fn handle_irq() { let s = "data"; }\n'
    check(
        "an `extern` ABI string is syntax and survives both views",
        'extern "C" fn handle_irq' in code_no_strings(abi),
        code_no_strings(abi),
    )
    check(
        "... while an ordinary string in the same fn is still blanked",
        "data" not in code_no_strings(abi),
    )

    decl_only = "trait T {\n    fn declared(&self);\n}\nfn real() {\n    TOKEN;\n}\n"
    check(
        "a bodyless declaration does not claim the next item's braces",
        enclosing_fn(decl_only, decl_only.index("TOKEN")) == "real",
        enclosing_fn(decl_only, decl_only.index("TOKEN")),
    )

    # --- statements and binding instances (PR #889 review round 8) ----------
    block = (
        "fn assemble() {\n"
        "    let mut asm = cc::Build::new();\n"
        '    asm.file("src/ghost.S");\n'
        "    let mut asm = cc::Build::new();\n"
        "    if false {\n"
        '        asm.file("src/dead.S");\n'
        "    }\n"
        '    asm.file("src/real.S")\n'
        '        .compile("sele4n_hal_asm");\n'
        "}\n"
    )
    view = code_no_strings(block)
    (_, b_start, b_end), = fn_bodies(block)
    stmts = top_level_statements(view, b_start, b_end)
    check("five top-level statements", len(stmts) == 5, str(len(stmts)))
    compile_at = block.index(".compile(")
    holder = statement_containing(stmts, compile_at)
    check("the compile sits in the last statement", holder == stmts[-1], str(holder))
    binding = binding_statement_before(view, stmts, "asm", holder)
    # THE relation-breaking witness: both `let mut asm` statements are
    # present; the one a use of `asm` refers to is the LAST before the use.
    check(
        "the binding instance is the last `let` before the use",
        binding == stmts[2],
        str(binding),
    )
    ghost_at = block.index('.file("src/ghost.S")')
    check(
        "a use before the rebinding precedes the instance the compile sees",
        binding is not None and ghost_at < binding[0],
    )
    check(
        "an unbound name has no binding instance",
        binding_statement_before(view, stmts, "other", holder) is None,
    )
    check(
        "a `let` after the use is not its binding",
        binding_statement_before(view, stmts, "asm", stmts[0]) is None,
    )

    # PR #889 review round 9: a `mut` receiver rebound by ASSIGNMENT, with no
    # second `let`.  Every token of the round-8 fixture survives — one `let`,
    # the same name, the same order — and only the second value's origin
    # differs.
    assigned = (
        "fn assemble() {\n"
        "    let mut asm = cc::Build::new();\n"
        '    asm.file("src/ghost.S");\n'
        "    asm = cc::Build::new();\n"
        '    asm.file("src/real.S")\n'
        '        .compile("sele4n_hal_asm");\n'
        "}\n"
    )
    a_view = code_no_strings(assigned)
    (_, a_start, a_end), = fn_bodies(assigned)
    a_stmts = top_level_statements(a_view, a_start, a_end)
    a_holder = statement_containing(a_stmts, assigned.index(".compile("))
    a_binding = binding_statement_before(a_view, a_stmts, "asm", a_holder)
    check(
        "an assignment is a binding boundary",
        a_binding == a_stmts[2],
        str(a_binding),
    )
    check(
        "...so the discarded builder's use precedes the live instance",
        a_binding is not None and assigned.index('.file("src/ghost.S")') < a_binding[0],
    )
    # ...while a compound assignment keeps the value and is not a boundary,
    # and `==` is a comparison.
    for label, statement in (
        ("compound assignment", "    asm += other;\n"),
        ("comparison", "    if asm == other {}\n"),
    ):
        kept = assigned.replace("    asm = cc::Build::new();\n", statement)
        k_view = code_no_strings(kept)
        (_, k_start, k_end), = fn_bodies(kept)
        k_stmts = top_level_statements(k_view, k_start, k_end)
        k_holder = statement_containing(k_stmts, kept.index(".compile("))
        check(
            f"a {label} is not a binding boundary",
            binding_statement_before(k_view, k_stmts, "asm", k_holder) == k_stmts[0],
            f"{label}: {binding_statement_before(k_view, k_stmts, 'asm', k_holder)}",
        )

    # --- unterminated literals raise rather than truncate ------------------
    for label, text in (
        ("block comment", "/* never closed\nlet a = 1;\n"),
        ("string", 'let s = "never closed\n'),
        ("raw string", 'let s = r#"never closed\n'),
    ):
        try:
            code(text)
        except UnterminatedLiteral:
            pass
        else:
            failures.append(f"unterminated {label} did not raise")

    # --- foreign blocks ---------------------------------------------------
    # Shared by two gates since PR #895 review round 7, so a defect here is a
    # defect in both.  Each witness KEEPS the tokens and changes the relation.
    def blocks_of(text: str):
        return extern_blocks(code_no_strings(text))

    check("an extern block is found", len(blocks_of('extern "C" { fn f(); }')) == 1)
    # Token-preserving: `extern`, the ABI and `fn` all survive; only what
    # follows the ABI changes, and `extern "C" fn` opens no block.
    check("`extern \"C\" fn` opens no block", blocks_of('extern "C" fn f() { }') == [])
    check("a raw-hashed ABI still opens a block",
          len(blocks_of('extern r#"C"# { fn f(); }')) == 1)
    check("a default-ABI block opens", len(blocks_of("extern { fn f(); }")) == 1)
    # A raw identifier NAMES an item `extern`; Rust accepts the item and its
    # body is ordinary code.  Token-preserving against the accepted blocks above:
    # the keyword letters and the `{` both stay, and only the `r#` is added.
    check("`mod r#extern { … }` opens no block",
          blocks_of("mod r#extern { fn f() {} }") == [])
    check("`struct r#extern { … }` opens no block",
          blocks_of("struct r#extern { x: u32 }") == [])
    # The brace is inside a string literal, so it opens nothing — the relation
    # the string-free view exists to get right.
    check("a brace inside a literal opens no block",
          blocks_of('let s = "extern \\"C\\" {";\n') == [])
    try:
        blocks_of('extern "C" { fn f();\n')
    except UnbalancedExternBlock:
        pass
    else:
        failures.append("an unbalanced extern block did not raise")

    def kinds_of(text: str) -> list[str]:
        view = code_no_strings(text)
        (_k, open_at, end), = extern_blocks(view)
        return [classify_extern_item(view, a, b)
                for a, b in extern_block_items(view, open_at + 1, end)]

    check("a fn, a static and a macro classify apart",
          kinds_of('unsafe extern "C" { fn a(); static B: u8; decl!(); }')
          == ["fn", "non-fn", "macro"],
          str(kinds_of('unsafe extern "C" { fn a(); static B: u8; decl!(); }')))
    # A macro in a function's TYPE does not make the item a macro: it is the
    # `fn` that declares the symbol.  Token-preserving against the macro case —
    # the `!` and the brackets are both still there.
    check("a macro inside a fn signature is still a fn",
          kinds_of('extern "C" { fn a(x: m!()); }') == ["fn"])
    # An item form the view does not know is `unknown`, never silently skipped.
    check("an unknown item form is named", kinds_of('extern "C" { const K: u32; }')
          == ["unknown"])
    # **A shift operator is not nesting** (PR #895 review round 14).  Counting
    # `<`/`>` as a bracket pair raised the depth twice on `1 << 2` with nothing
    # to lower it, so the item's own `;` stopped terminating and every following
    # declaration merged into it — the undocumented one then existed for no
    # count, no inventory and no baseline.  Token-preserving against its control:
    # both fixtures hold the same two declarations and the same `[u8; …]` type;
    # only the array length differs.
    check("a shift in a signature does not swallow the next item",
          kinds_of('extern "C" { fn a(x: *const [u8; 1 << 2]); fn b(); }')
          == ["fn", "fn"],
          str(kinds_of('extern "C" { fn a(x: *const [u8; 1 << 2]); fn b(); }')))
    check("its control, with no shift, splits the same way",
          kinds_of('extern "C" { fn a(x: *const [u8; 4]); fn b(); }') == ["fn", "fn"])
    # ...and a `;` that genuinely IS nested still does not terminate, which is
    # what the bracket depth is for and what dropping the angle brackets must
    # not cost.
    check("a `;` inside an array type still does not terminate",
          kinds_of('extern "C" { fn a(x: *const [u8; 4]); }') == ["fn"])
    check("a `;` inside a const-generic block still does not terminate",
          kinds_of('extern "C" { fn a(x: *const Foo<{ 1 }>); fn b(); }') == ["fn", "fn"])

    # --- the keyword fragment, and the discipline that keeps it one ------
    # Token-preserving in the way this class demands: the keyword letters and
    # the following brace both survive; only the `r#` escape is added.
    check("a raw identifier is not the keyword",
          re.search(keyword("unsafe"), "struct r#unsafe { x: u32 }") is None)
    check("the keyword is still the keyword",
          re.search(keyword("unsafe"), "unsafe { f(); }") is not None)
    check("a raw identifier is not `extern`",
          re.search(keyword("extern"), "mod r#extern { }") is None)
    # A longer identifier merely CONTAINING the keyword is not it either, which
    # is what the trailing boundary is for.
    check("a longer identifier is not the keyword",
          re.search(keyword("fn"), "let fnord = 1;") is None)
    # The discipline itself: no gate may spell a keyword bare.  This is the
    # check that reaches the pattern nobody has written yet, which is the one
    # thing three rounds of site-by-site fixes could not do.
    bare = bare_keyword_literals()
    check("no gate spells a Rust keyword bare", not bare, "; ".join(bare))

    for problem in failures:
        print(f"FAIL  {problem}")
    if failures:
        print(f"\nrust_code_view self-test: {len(failures)} failure(s)")
        return 1
    print("rust_code_view self-test: all witnesses hold")
    return 0


def main(argv: list[str]) -> int:
    if argv and argv[0] == "--self-test":
        return _self_test()
    no_strings = bool(argv) and argv[0] == "--no-strings"
    paths = argv[1:] if no_strings else argv
    if not paths:
        print(__doc__)
        return 0
    view = code_no_strings if no_strings else code
    for path in paths:
        with open(path, encoding="utf-8") as handle:
            sys.stdout.write(view(handle.read()))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
