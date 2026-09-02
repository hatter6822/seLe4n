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


_FN_RE = re.compile(r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)")


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
