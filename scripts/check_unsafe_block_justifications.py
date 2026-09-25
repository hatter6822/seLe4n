#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Every `unsafe` site in the Rust tree carries a justification a reviewer reads.

`CLAUDE.md` states the HAL's discipline as *every unsafe block carries a
`// SAFETY:` comment*, and attributed its enforcement to
`scripts/check_arm_arm_citations.sh` — a gate the v0.30.11 audit planned as
R12.C, recorded in `docs/audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md` row F.3 as
the discharge mechanism for DEEP-RUST-01/02, and **never written**: no commit on
any branch contains it and Tier 0 never ran it.  So the discipline was stated,
relied on by a discharge row, and checked by nothing.  This is that gate, written
against what the tree actually is.

## The relation, not a window

The audit plan specified "the preceding 5 lines contain the citation", and a
fixed window is a presence check: an unrelated comment five lines up satisfies
it, and a justification separated from its block by an intervening statement
does not fail it.  What a reviewer actually reads is the **contiguous comment run
immediately above the site** — comments and attributes only, no code between — so
that is the relation this gate asks.  A `SAFETY:` comment moved below the block,
or separated from it by a statement, is refused.

## Two disciplines, one enforced

`SAFETY` is required of every site: a justification is something a human writes
about any unsafe operation, and demanding it costs nothing correct.

`(ARM ARM <section>)` is **reported, not enforced**.  Requiring it everywhere
would demand an architecture-manual citation of a raw-pointer dereference that
touches no hardware, and deciding *which* sites touch hardware needs the body —
the analysis-instead-of-a-contract shape this project has retired twice.  So the
citation count is a diagnostic beside the enforced figure, exactly as
`STORE_READ_SPEC` sits beside `STORE_READ_CODE`.

## The floor is an inventory

`scripts/unsafe_justification_baseline.json` pins the unjustified sites per
`(file, enclosing declaration)` **with counts**, reconciled in both directions: a
key the baseline does not name fails outright, a key it names may only fall, and
a key that has gone to zero and stayed in the baseline is reported as stale.  A
set of keys alone cannot see a second unjustified site in a file that already has
one, and a count alone cannot see the first in a file that had none, so the floor
has to be both — the shape `scripts/identifier_naming_baseline.json` and
`scripts/store_reader_hygiene_baseline.txt` already use.

## Which view answers which question

Site *positions* come from the comment-blanked, string-blanked view
(`rust_code_view.code_no_strings`), so an `unsafe {` inside a string literal or a
comment is not a site.  The justification *text* is read from the raw file at the
same byte offsets, because the subject there genuinely is the comment.  Both
views are byte-aligned, which is what lets one walk use both.

    scripts/check_unsafe_block_justifications.py            # check
    scripts/check_unsafe_block_justifications.py --rows     # the inventory
    scripts/check_unsafe_block_justifications.py --update   # re-anchor
    scripts/check_unsafe_block_justifications.py --self-test
"""
from __future__ import annotations

import json
import os
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import rust_code_view  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
BASELINE = REPO / "scripts" / "unsafe_justification_baseline.json"

# An `unsafe` block, or an `unsafe fn` DECLARATION — `unsafe fn` followed by a
# name.  `unsafe impl` and `unsafe trait` are not operations and carry their own
# review story, and neither is `unsafe fn(u8) -> T`: that is a function-pointer
# **type**, which `tests::register_signature_pinned` uses to pin an ABI.  A type
# performs nothing, so demanding a justification of one is a scanner matching a
# keyword rather than asking about an operation.
# **The ABI is a string literal, and Rust's string literals include raw ones.**
# `extern r"C" fn f()` compiles; the four patterns below each carried their own
# copy of `"[^"]*"`, so widening three of them left the fourth behind and a valid
# declaration yielded no site while the keyword scan rejected the file
# (PR #895 review round 5).  One question, one spelling, four readers.
#
# **A raw string's hashes are balanced, and half of them is not a literal.**
# `r#*\"[^\"]*\"` consumed the OPENING hashes of `r#\"C\"#` and stopped at the
# closing quote, leaving the trailing `#` exactly where every surrounding
# pattern requires whitespace — so `pub unsafe extern r#\"C\"# fn f() {}`, which
# rustc accepts, yielded no site AND was reported as an unrecognised `unsafe`
# form, failing Tier 0 on valid Rust (PR #895 review round 6).  The count of
# closing hashes must equal the opening count, which is a backreference, not a
# repetition.  Each pattern below embeds `ABI` exactly once, so one named group
# is safe; embedding it twice in a single pattern would not compile, which is a
# loud failure rather than a silent one.
ABI = r'(?:r(?P<rawhash>\#*)\"[^\"]*\"(?P=rawhash)|\"[^\"]*\")'

#: **Every keyword below is `rust_code_view.keyword(...)`, never `\bword\b`.**
#: A raw identifier such as `r#unsafe` spells the keyword and is not it, and a
#: bare `\bunsafe\b` matches inside one -- so `struct r#unsafe { x: u32 }` was
#: read as an unsafe block and Tier 0 demanded a justification of safe Rust
#: (PR #895 review round 9).  The exclusion had been on `UNSAFE_KEYWORD` since
#: `v0.35.17`, ten lines below, with a comment explaining it; six sibling
#: patterns in this file were written without it anyway.  The helper is what
#: makes that unrepeatable, and `verify_keyword_discipline` is what refuses the
#: next bare spelling rather than trusting review to catch it.
KW_UNSAFE = rust_code_view.keyword("unsafe")
KW_EXTERN = rust_code_view.keyword("extern")
KW_FN = rust_code_view.keyword("fn")

#: A Rust identifier's first character, and a whole one.
#:
#: **PR #895 review round 18.**  Round 12 widened this from ASCII to `[^\W\d]`
#: after `pub unsafe fn \u03bb()` proved to be no site at all -- and `[^\W\d]`
#: is Python's *word* class, not `XID_Start`.  The gap is live: rustc 1.94.1
#: accepts `pub unsafe fn \u2118()`, `\u212e()` and `\u1885()` (measured), and
#: `\w` matches none of the three, so a declaration spelled with one raised no
#: obligation and then failed the file as an unrecognised form.
#:
#: Widening it a third time would be the same move that has now failed twice.
#: The class is derived from CPython's own UAX#31 tables instead --
#: `rust_code_view.ident()`, which is measured to agree with rustc -- and
#: `rust_code_view.bare_ident_literals` refuses the next ASCII spelling written
#: in a source that asks this question.
IDENT_START = rust_code_view.ident_start()
IDENT = rust_code_view.ident()

# **A `macro_rules!` template declaring `unsafe … fn $name` is a declaration
# site, keyed by its metavariable** (the `v0.36.2` audit).  The Lean runtime's
# C-ABI exports are minted by four templates (`export_apply`, `borrowed2`,
# `compare`, `narrow`); each expansion is a `pub unsafe extern "C" fn` whose
# documentation is the template's own `///` lines, so the template is where the
# `# Safety` section lives and where the obligation is decided once for every
# name it mints.  A metavariable is not an identifier, so before this the
# keyword scan found the token, no known form accepted the position, and the
# gate failed the file — the fail-CLOSED branch, so nothing was silently passed,
# but a decision was missing.  `MACRO_NAME` is the `$` the template spells its
# name with; every form below admits it exactly where an identifier may start.
MACRO_NAME = r"(?:\$)?"

UNSAFE_SITE = re.compile(
    KW_UNSAFE + r"\s*\{"                                       # a block
    r"|" + KW_UNSAFE + r"\s+(?:" + KW_EXTERN + r"\s+" + ABI + r"\s+)?"
    + KW_FN + r"\s+(?:r#)?" + MACRO_NAME + IDENT_START,         # a declaration
    re.UNICODE,
)

# **Every form of the keyword this scanner knows, and nothing else passes.**
#
# An earlier cut matched `unsafe` followed immediately by `fn`, so the ordinary
# FFI spelling `pub unsafe extern "C" fn f()` was not a site *at all* — absent
# from the count and from the unjustified inventory alike, with an empty
# baseline still reporting PASS.  That is the fail-OPEN direction: a scanner
# that builds a set of obligations and does not recognise an input has dropped
# an obligation, silently.
#
# So the default branch is explicit.  Each pattern below is a form the scanner
# has a decision for; an `unsafe` matching none of them stops the gate with a
# diagnostic, because a spelling Rust accepts and this gate does not is a gate
# defect and should say so on the day it appears rather than quietly checking
# less.
UNSAFE_KNOWN_FORMS = [
    (re.compile(KW_UNSAFE + r"\s*\{"), "block"),
    (re.compile(KW_UNSAFE + r"\s+(?:" + KW_EXTERN + r"\s+" + ABI + r"\s+)?"
                 + KW_FN + r"\s+(?:r#)?" + MACRO_NAME + IDENT_START, re.UNICODE),
     "declaration"),
    # `unsafe impl` / `unsafe trait` are not operations: they assert a trait
    # contract, which carries its own review story and no per-site obligation.
    (re.compile(KW_UNSAFE + r"\s+(?:" + rust_code_view.keyword("impl")
                 + r"|" + rust_code_view.keyword("trait") + r")"),
     "trait contract"),
    # Rust 2024's `unsafe extern { … }` block header.  The items inside are
    # declarations and are matched as such; the header itself performs nothing.
    (re.compile(KW_UNSAFE + r"\s+" + KW_EXTERN + r"\s*(?:" + ABI + r"\s*)?\{"),
     "extern block header"),
    # A function-pointer TYPE — `unsafe fn(u8, T) -> R`, which
    # `tests::register_signature_pinned` uses to pin an ABI.  A type performs
    # nothing, so demanding a justification of one is a scanner matching a
    # keyword rather than asking about an operation.
    (re.compile(KW_UNSAFE + r"\s+(?:" + KW_EXTERN + r"\s+" + ABI + r"\s+)?"
                 + KW_FN + r"\s*\("),
     "function-pointer type"),
    # **Rust 2024's unsafe ATTRIBUTE** — `#[unsafe(no_mangle)]`,
    # `#[unsafe(export_name = "…")]`, `#[unsafe(link_section = "…")]`.  The
    # 2024 edition requires the wrapper on the attributes that can make a
    # symbol collide, so this is the *only* spelling a 2024 crate may use, and
    # the gate rejected the whole file for it: `UNSAFE_KEYWORD` found the token
    # and no form accepted the position, which is the fail-CLOSED branch of the
    # explicit default above.
    #
    # **It carries no per-site obligation, and that is a decision.**  The
    # attribute attaches to an ITEM and asserts something about the linker
    # namespace, not about an operation — the same shape as `unsafe impl` two
    # entries up, whose review story is the trait's contract rather than a
    # comment at a call site.  Here the story is the one this tree already
    # enforces on exported symbols: `check_kernel_entry_exports.py` reconciles
    # every exported name against the archive, and `check_identifier_naming.py`
    # reads `#[export_name = "…"]` as a linker-visible name.  Demanding a
    # `// SAFETY:` here would put the justification in a third place and check
    # it in none.
    # Anchored at the keyword, because `unrecognised_unsafe_forms` matches each
    # form at the token's own offset -- a pattern opening with `#[` would never
    # fire.  `unsafe` followed by `(` is unambiguous in Rust's grammar: the
    # keyword otherwise takes `{`, `fn`, `impl`, `trait` or `extern`, and there
    # is no parenthesised `unsafe` expression, so the attribute wrapper is the
    # only thing this can be -- which also means an inner `#![unsafe(...)]` and
    # a whitespace-separated `#[ unsafe(...) ]` are both covered, where a
    # lookbehind on the bracket would have refused the second.
    (re.compile(KW_UNSAFE + r"\s*\("), "unsafe attribute"),
]

# **A raw identifier is not the keyword.**  `r#unsafe` names an ordinary item
# called `unsafe`; Rust accepts the declaration and the call, and `\bunsafe\b`
# matches inside it because `#` is a non-word character.  No entry of
# `UNSAFE_KNOWN_FORMS` then accepts the position, so the gate *failed the file*
# — the fail-CLOSED direction, which costs a contributor rather than a reviewer,
# and is still a gate defect.
#
# The same relation was already swept onto the declaration pattern in
# `v0.35.13` (`fn\s+(?:r#)?[A-Za-z_]`, for `r#lean_real`) and not onto the
# keyword scan beside it, which is this project's sweep rule failing in the way
# it describes.
UNSAFE_KEYWORD = re.compile(KW_UNSAFE)


def unrecognised_unsafe_forms(path: Path, view: str) -> list[str]:
    """Occurrences of `unsafe` this scanner has no decision for."""
    out = []
    for m in UNSAFE_KEYWORD.finditer(view):
        if any(pat.match(view, m.start()) for pat, _ in UNSAFE_KNOWN_FORMS):
            continue
        line = view.count("\n", 0, m.start()) + 1
        snippet = " ".join(view[m.start():m.start() + 48].split())
        out.append(f"{path}:{line}: unrecognised `unsafe` form: {snippet!r}")
    return out

# **The two kinds ask different questions, so the gate asks each its own.**
#
# An `unsafe` BLOCK *discharges* an obligation locally, and Rust's idiom for
# that — the one `clippy::undocumented_unsafe_blocks` reads — is a `// SAFETY:`
# comment on the block.  An `unsafe fn` DECLARATION *publishes* one to its
# callers, and Rust's idiom for that is a `# Safety` doc section.  A gate that
# demanded `// SAFETY:` of a declaration would report every correctly documented
# `unsafe fn` in the tree, which is a scanner asking the wrong question rather
# than a discipline the code fails.
# **The marker is `SAFETY:`, and the colon is part of it** (PR #895 review
# round 9).  Requiring only a word boundary let a comment that explicitly
# DISCLAIMS the obligation satisfy it: `// SAFETY is not established.` and
# `/* SAFETY unknown */` both justified an unsafe block and kept the empty
# baseline green.  That is the fail-OPEN direction, and it is a presence check
# standing in for the contract -- the convention this gate enforces, the one
# `clippy::undocumented_unsafe_blocks` reads, and the one every docstring here
# names, is `// SAFETY:`.  Measured before changing it: all 138 markers in the
# tree already carry the colon, so the tightening refuses the next disclaimer
# without touching a single live site.
# **...and a block comment's body lines carry decoration** (PR #895 review
# round 11).  The conventional multiline form
#
#     /*
#      * SAFETY: the pointer is valid …
#      */
#
# puts a `*` between the opening delimiter and the marker, and requiring only
# whitespace there rejected a genuinely documented block — Tier 0 refusing the
# very spelling the gate says it supports.  The marker may therefore be preceded
# on its line by comment decoration and nothing else: slashes, asterisks and
# whitespace.  It is still anchored to a line start, so `let x = 1; // SAFETY:`
# after real code does not qualify, and it is still read over `comment_text_of`,
# so nothing inside a string can supply it.
SAFETY_BLOCK = re.compile(r"^[ \t]*(?:(?://[/!]?|/?\*+)[ \t*]*)?SAFETY\s*:",
                          re.IGNORECASE | re.MULTILINE)
# **Rustdoc, and only rustdoc.**  The heading has to reach the *caller*, so the
# line carrying it must be a doc comment (`///`, `//!`) or a line inside a doc
# BLOCK (`/**`, `/*!`) -- an ordinary `/* … * # Safety … */` publishes nothing
# and used to pass on the bare `\*` alternative.  Rust's attribute spelling
# `#[doc = "# Safety"]` publishes the same section and is accepted too, since
# refusing it would reject correctly documented code.
#
# **Outer rustdoc, because inner rustdoc documents something else.**  `///`,
# `/**` and `#[doc = …]` attach to the item that FOLLOWS them; `//!`, `/*!` and
# `#![doc = …]` attach to the item that ENCLOSES them — the module or crate.  A
# module opening with `//! # Safety` immediately above the first `unsafe fn`
# therefore published a section about the module while the function itself
# exposed no contract at all, and the gate read it as justification.  That is
# the same substitution as the two findings above it, one level in: *is a doc
# comment* is not *is a doc comment ON THIS ITEM*.
#
# `////` and `/***` are regular comments in Rust, not doc comments (the
# reference excludes a fourth `/` and a third `*`), so neither publishes
# anything either.  The `(?!/)` and `(?![*/])` state that rather than leaning on
# it: a `////` heading was already refused incidentally, because the fourth
# slash is not the whitespace the pattern expects next, while a `/***` block WAS
# accepted -- its interior line matches the doc-block body pattern like any
# other.  Both are now refused for the reason, not by accident.
# **The attribute form is no longer a pattern over the spelling.**  Two rounds
# narrowed a regex that asked whether `# Safety` followed an escaped newline
# inside the literal -- round 5 stopped arbitrary prose preceding the `#`, round
# 8 required the whitespace after it -- and round 9 showed the question itself
# was wrong: in a RAW literal `\n` is two characters and starts no line, so the
# pattern could not be narrowed into correctness.  `_doc_attribute_values`
# DECODES each literal and `publishes_safety_heading` asks a real markdown question
# of the result.  The superseded `SAFETY_DECL_ATTR` is deleted rather than left
# beside its replacement: a retired pattern that once decided this question is
# what a later cut reaches for by name.
# **A heading marker needs whitespace after it** (PR #895 review round 8).  The
# three patterns above and below spelled the gap `\s*`, which is satisfied by
# NOTHING — so `/// #Safety` passed while CommonMark (and therefore rustdoc)
# requires a space or tab after the `#` run and renders that text as an ordinary
# paragraph.  An `unsafe fn` could publish no caller-facing section at all and
# still clear Tier 0, which is the fail-OPEN direction on the one gate whose
# whole subject is what a caller is told.  `[ \t]+` is the Markdown rule, and it
# is applied to all three spellings at once rather than to the one a review
# names, since they answer the same question in three syntaxes.
DOC_BLOCK_OPEN = re.compile(r"/\*\*(?![*/])")


def block_comment_spans(raw: str, view: str) -> list[tuple[int, int, bool]]:
    """`(start, end, is_doc)` for each real block comment in `raw`.

    **Rust block comments nest, and a marker nested inside one publishes
    nothing.**  `/* … /** # Safety … */ … */` is a single ordinary comment as
    far as rustdoc is concerned, so the declaration below it exposes no
    caller-facing contract — yet scanning the run for `/**` anywhere treated the
    inner marker as an independently attached doc block and accepted the
    `unsafe fn` (PR #895 review round 6).

    **And a `/*` opens a comment only where the view says a comment begins**
    (PR #895 review round 11).  The nesting walk answers *extent* and says
    nothing about whether the text is code: `let m = "/** # Safety */";` opens
    nothing, and neither does a `/**` written inside a `//` line.  So an opener
    is a `/` the code view blanked — which is this file's one derivation of
    "that byte is comment text" — and the walk only measures how far it
    reaches.  A line comment's extent is its line, so scanning resumes at the
    newline and a `/*` inside it is never examined; a nested `/*` is consumed
    by the walk.  Reading the question off one walk and the enclosure off
    another is what left three fail-OPEN cells for the form matrix to find.
    """
    spans: list[tuple[int, int, bool]] = []
    i, n = 0, len(raw)
    while i < n:
        if view[i] != " " or raw[i] != "/":
            i += 1
            continue
        if raw.startswith("//", i):
            newline = raw.find("\n", i)
            i = n if newline < 0 else newline
            continue
        if not raw.startswith("/*", i):
            i += 1
            continue
        is_doc = DOC_BLOCK_OPEN.match(raw, i) is not None
        depth, j = 1, i + 2
        while j < n and depth:
            if raw.startswith("/*", j):
                depth += 1
                j += 2
            elif raw.startswith("*/", j):
                depth -= 1
                j += 2
            else:
                j += 1
        spans.append((i, j, is_doc))
        i = j
    return spans


def blank_block_comments(raw: str, spans: list[tuple[int, int, bool]]) -> str:
    """`raw` with every block comment's extent blanked, newlines kept.

    A `///` line or a `#[doc = …]` attribute *spelled inside* an ordinary block
    comment is attached to nothing, so the line-anchored scans must not see it;
    keeping the newlines leaves their geometry intact.

    Deliberately not applied to `SAFETY_BLOCK`: a `// SAFETY:` comment is for
    the reviewer reading this file, who sees a nested one as readily as a
    top-level one.  The relation here is *rustdoc publication*, which is a
    property of declarations alone.
    """
    out = list(raw)
    for start, end, _ in spans:
        for j in range(start, min(end, len(out))):
            if out[j] != "\n":
                out[j] = " "
    return "".join(out)


#: An OUTER rustdoc `#[doc = "…"]` attribute, up to the opening quote of its
#: value.  The value itself is NOT matched here: deciding where a Rust string
#: literal ends is a question about its own kind, which `_doc_attribute_values`
#: answers by reading the literal rather than by a pattern over it.
#:
#: **Outer only, deliberately.**  `#![doc = …]` documents the ENCLOSING module,
#: not the item below it, so a module opening with an inner Safety section
#: publishes nothing about the first `unsafe fn` under it -- round 4's finding,
#: which this pattern reopened when it was first written `#!?\[` and which the
#: witness for that round caught on the spot.  The sibling classification of
#: `#![unsafe(…)]` is correctly inner-tolerant, because *which item is an unsafe
#: attribute attached to* is not a question that scan asks.
#: An OUTER doc attribute's HEAD, matched at the start of an attribute span on
#: the string-free view.  This is what decides *whether a span is a doc
#: attribute at all*; `DOC_ATTR_OPEN` then locates its value inside.  Splitting
#: the two is the round-11 fix: searching for the opener anywhere let an
#: unrelated attribute's string literal supply one.
DOC_ATTR_HEAD = re.compile(rust_code_view.ATTRIBUTE_OPEN + r"\s*doc\s*=")

DOC_ATTR_OPEN = re.compile(rust_code_view.OUTER_ATTRIBUTE_OPEN
                           + r"\s*doc\s*=\s*(?P<raw>r(?P<hashes>\#*))?\"")

#: A `#[doc = …]` whose value is NOT a plain string literal.  Matched so the
#: scanner can DECIDE about it rather than skip it -- see `_doc_attribute_values`.
DOC_ATTR_NONLITERAL = re.compile(
    rust_code_view.OUTER_ATTRIBUTE_OPEN
    + r"\s*doc\s*=\s*(?P<value>" + IDENT + r"\s*!)")
#: `concat!(…)`, whose arguments this scanner can expand exactly when they are
#: all string literals -- which is what rustdoc renders.
CONCAT_OPEN = re.compile(r"\bconcat\s*!\s*\(")


class UnreadableDocAttribute(Exception):
    """A `#[doc = …]` whose rendered text this scanner cannot determine.

    **"Undocumented" and "unreadable" are different claims** (PR #895 review
    round 10).  `#[doc = include_str!("x.md")]` publishes a section this gate
    cannot see without reading another file, and reporting the declaration
    *unjustified* says something false about the code: Tier 0 refusing valid
    Rust, with a diagnostic that sends a contributor looking for documentation
    that is already there.  Refusing the input names the gate's own limit
    instead, which is this project's rule that a scanner's default branch is a
    decision.
    """

    def __init__(self, snippet: str) -> None:
        super().__init__(f"unreadable `#[doc = …]` value: {snippet!r} — this gate "
                         f"expands string literals and `concat!` of string "
                         f"literals; teach it this form or spell the section "
                         f"with `///`")


def _decode_rust_string(body: str, is_raw: bool) -> str:
    """A Rust string literal's body as the text it denotes.

    **A spelling is not the text** (PR #895 review round 9).  In a RAW literal
    there are no escapes, so `r"a\\nb"` is eleven characters with a backslash in
    the middle and renders as one markdown line; in an ordinary literal the same
    two characters are a newline and the text has two lines.  Asking a regex
    whether `# Safety` follows a `\\n` conflates them, and it conflates them in
    the fail-OPEN direction: an `unsafe fn` documented `#[doc = r"not a heading
    \\n# Safety"]` published no heading at all and satisfied the gate.

    So the value is decoded before it is read, which is this project's own
    instruction to resolve the text into the structure it stands for -- here,
    the markdown a caller is actually shown.  Only the escapes that can produce
    a line start or hide one need to be exact; every other escape is passed
    through as its own character, since the question asked of the result is
    whether any LINE begins a `# Safety` heading.
    """
    if is_raw:
        return body
    out: list[str] = []
    i, n = 0, len(body)
    simple = {"n": "\n", "r": "\r", "t": "\t", "0": "\0",
              "\\": "\\", "'": "'", '"': '"'}
    while i < n:
        ch = body[i]
        if ch != "\\" or i + 1 >= n:
            out.append(ch)
            i += 1
            continue
        nxt = body[i + 1]
        if nxt in simple:
            out.append(simple[nxt])
            i += 2
            continue
        if nxt == "x" and i + 3 < n:
            try:
                out.append(chr(int(body[i + 2:i + 4], 16)))
                i += 4
                continue
            except ValueError:
                pass
        if nxt == "u" and body[i + 2:i + 3] == "{":
            close = body.find("}", i + 3)
            if close != -1:
                try:
                    out.append(chr(int(body[i + 3:close], 16)))
                    i = close + 1
                    continue
                except ValueError:
                    pass
        if nxt == "\n":
            # A line continuation: the newline and the leading whitespace of the
            # next line are both consumed, so it produces NO line start.
            i += 2
            while i < n and body[i] in " \t\r\n":
                i += 1
            continue
        # An escape this decoder does not know.  Dropping the backslash is the
        # fail-CLOSED choice: it can only merge text onto one line, never invent
        # the line start a heading needs.
        out.append(nxt)
        i += 2
    return "".join(out)


def _concat_literals(text: str, at: int) -> str | None:
    """`concat!(…)`'s value when every argument is a string literal, else `None`.

    Expanded rather than refused because `concat!` of literals is exactly what
    rustdoc renders and a contributor splitting a long section across lines with
    it is writing correct, published documentation.  A `None` return means an
    argument this scanner cannot evaluate -- a nested macro, a constant, a
    numeric literal -- and the caller refuses the attribute rather than guessing.
    """
    i = text.find("(", at - 1)
    if i == -1:
        return None
    i += 1
    parts: list[str] = []
    n = len(text)
    while i < n:
        while i < n and text[i] in " \t\r\n,":
            i += 1
        if i < n and text[i] == ")":
            return "".join(parts)
        raw_match = re.compile(r"r(#*)\"").match(text, i)
        if raw_match:
            terminator = '"' + raw_match.group(1)
            end = text.find(terminator, raw_match.end())
            if end == -1:
                return None
            parts.append(_decode_rust_string(text[raw_match.end():end], True))
            i = end + len(terminator)
            continue
        if i < n and text[i] == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == '"':
                    break
                j += 1
            else:
                return None
            parts.append(_decode_rust_string(text[i + 1:j], False))
            i = j + 1
            continue
        return None
    return None


def _doc_attribute_values(text: str) -> list[str]:
    """The decoded value of every `#[doc = "…"]` attribute in `text`.

    Reads each literal by its own kind so the terminator is right: a raw literal
    ends at a quote followed by exactly its opening hash count, an ordinary one
    at the first unescaped quote.  An unterminated literal yields nothing --
    this scanner produces a set of JUSTIFICATIONS, so dropping what it cannot
    read refuses the declaration rather than passing it.
    """
    out: list[str] = []
    # **A macro-valued doc attribute is decided, not skipped.**  `concat!` of
    # string literals is what rustdoc renders, so it is expanded; anything else
    # (`include_str!`, a user macro) is refused by name rather than reported as
    # missing documentation, because those are different claims (round 10).
    for match in DOC_ATTR_NONLITERAL.finditer(text):
        head = match.group("value")
        if CONCAT_OPEN.match(head + "(") or head.replace(" ", "") == "concat!":
            expanded = _concat_literals(text, match.end())
            if expanded is None:
                raise UnreadableDocAttribute(text[match.start():match.start() + 60])
            out.append(expanded)
            continue
        raise UnreadableDocAttribute(text[match.start():match.start() + 60])
    for match in DOC_ATTR_OPEN.finditer(text):
        is_raw = match.group("raw") is not None
        start = match.end()
        if is_raw:
            terminator = '"' + (match.group("hashes") or "")
            end = text.find(terminator, start)
            if end == -1:
                continue
            out.append(_decode_rust_string(text[start:end], True))
            continue
        i, n = start, len(text)
        while i < n:
            if text[i] == "\\":
                i += 2
                continue
            if text[i] == '"':
                out.append(_decode_rust_string(text[start:i], False))
                break
            i += 1
    return out


#: A `# Safety` ATX heading occupying a line of already-decoded markdown.
#: CommonMark requires whitespace after the `#` run, which is why `#Safety`
#: renders as a paragraph and must not count (PR #895 review round 8).


def declaration_documents_safety(run: str) -> bool:
    """Does this run publish a rustdoc `# Safety` section?

    **One document, one question** (PR #895 review round 12).  This used to be
    three line-oriented searches — a `///` scan, a decoded-attribute scan and a
    doc-block scan — each deciding independently whether a `# Safety` line
    occurred.  All three accepted a heading inside a fenced code block, which
    rustdoc renders as literal text, so a declaration could publish no
    caller-facing contract at all and still clear an empty baseline.  The
    enclosure is a property of the rendered *document*, so the document is what
    is built (`rendered_doc_markdown`) and what is asked
    (`publishes_safety_heading`).

    That also retires the three patterns' disagreements by construction: every
    rule about which markers attach to the item below — `//!` and `#![doc]`
    document the enclosing module, a marker inside a string or nested in
    another comment publishes nothing, an attribute value is decoded by its
    literal kind — now lives at the one place that builds the document.
    """
    return publishes_safety_heading(rendered_doc_markdown(run))

ARM_ARM = re.compile(r"\(ARM ARM [A-Z][0-9]+(?:\.[0-9]+)*\)")


#: An outer line doc comment, and the text it contributes.  `//!` documents the
#: ENCLOSING module (round 4) and `////` is an ordinary comment, so neither is a
#: source for the item below.  rustdoc strips the marker and at most ONE space.
LINE_DOC = re.compile(r"^[ \t]*///(?!/)[ \t]?(?P<text>.*)$")


def rendered_doc_markdown(run: str) -> str:
    """The markdown rustdoc renders for the item below this run.

    **One document, because rustdoc renders one document.**  A `///` line, a
    `/** … */` block and a `#[doc = "…"]` attribute are three spellings of the
    same `#[doc]` attribute, and rustdoc concatenates every one attached to an
    item, in source order, before parsing the result as markdown.  Asking three
    separate line patterns whether a heading occurs therefore answered a
    question about lines when the property — *is this heading inside a code
    block* — is a property of the document (PR #895 review round 12): a fence
    opened in one source encloses what follows it in the next.

    Fragments are ordered by their byte offset in the run, which is the source
    order rustdoc uses, and each is de-decorated the way rustdoc de-decorates
    it.  Every offset comes from a code view, so a doc marker written inside a
    string or nested in another comment contributes nothing.
    """
    view = rust_code_view.code(run)
    fragments: list[tuple[int, str]] = []

    # Doc BLOCKS, from the shared view-gated walk.
    for start, end, is_doc in block_comment_spans(run, view):
        if not is_doc:
            continue
        closed = run[end - 2:end] == "*/"
        fragments.append((start, _undecorate_block(run[start + 3:end - 2 if closed else end])))

    # LINE docs, from comment text with the block comments already blanked, so
    # a `///` written inside a `/* … */` contributes nothing.
    attached = blank_block_comments(run, block_comment_spans(run, view))
    comments = comment_text_of(attached, rust_code_view.code(attached))
    offset = 0
    for line in comments.split("\n"):
        hit = LINE_DOC.match(line)
        if hit is not None:
            fragments.append((offset, hit.group("text")))
        offset += len(line) + 1

    # Doc ATTRIBUTES: extents from the string-free view, values from the
    # byte-aligned kept one, decoded by literal kind.
    kept = rust_code_view.code(attached)
    bare = rust_code_view.code_no_strings(attached)
    for lo, hi in rust_code_view.attribute_spans(bare):
        if DOC_ATTR_HEAD.match(bare, lo) is None:
            continue
        for value in _doc_attribute_values(kept[lo:hi]):
            fragments.append((lo, value))

    fragments.sort(key=lambda f: f[0])
    return "\n".join(text for _offset, text in fragments)


def _undecorate_block(body: str) -> str:
    """A doc block's body with its `*` gutter removed, if it has one.

    Conditional, as rustdoc is: the gutter is stripped only when *every*
    non-empty line carries it, so a markdown bullet list written `* item` in a
    block that has no gutter survives intact.
    """
    lines = body.split("\n")
    rest = [ln for ln in lines[1:] if ln.strip()]
    if rest and all(re.match(r"^[ \t]*\*", ln) for ln in rest):
        lines = [lines[0]] + [re.sub(r"^[ \t]*\*[ \t]?", "", ln) for ln in lines[1:]]
    return "\n".join(lines)


#: A fenced code block's delimiter line (CommonMark 4.5): three or more
#: backticks or tildes, indented at most three spaces.
MD_FENCE = re.compile(r"^ {0,3}(`{3,}|~{3,})(.*)$")


def _opens_fence(delim: "re.Match[str]") -> bool:
    """Does this delimiter line OPEN a fenced code block?

    **A backtick fence's info string may not contain a backtick** (CommonMark
    4.5), and the specification gives the reason: otherwise ordinary inline code
    would read as the start of a fence.  So ```` ```rust`x ```` opens nothing,
    and a `# Safety` heading below it is published — while this gate treated the
    line as a fence and reported the declaration undocumented.  Fail-CLOSED,
    refusing correct documentation, which round 6 recorded as a defect in its
    own right.

    A **tilde** fence carries no such restriction: `~~~rust`x` is a fence, and
    the asymmetry is the whole content of this predicate.  Closing is unaffected
    — a closer may carry no info string at all, which the caller already
    requires — so this is asked only where a fence is opened.
    """
    return not (delim.group(1)[0] == "`" and "`" in delim.group(2))

#: **The heading titles `clippy::missing_safety_doc` accepts**, measured against
#: the workspace's own clippy rather than recalled (PR #895 review round 17).
#:
#: A probe crate with one `pub unsafe fn` per spelling gives the exact set:
#: `Safety` and `SAFETY` are accepted, `Implementation safety` and
#: `Implementation Safety` are accepted, and `safety`, `SaFeTy`, `Safety:` and
#: `Safety Requirements` are **rejected**.  Matching case-insensitively on a
#: word boundary accepted all four of the rejected forms — and clippy does not
#: examine a *private* `unsafe fn` at all, so for those this scanner is the only
#: enforcement and a heading it alone accepts publishes no caller contract.
#:
#: Measuring mattered in both directions: the review proposed `Safety` or
#: `SAFETY`, and restricting to those two would have refused the two
#: `Implementation …` spellings clippy accepts — the fail-CLOSED direction,
#: which round 6 recorded as a defect in its own right.
#:
#: One alternation, composed by both the ATX and the Setext matcher, because a
#: second spelling of one question is what this project keeps paying for.
SAFETY_HEADING_TITLES = frozenset(
    {"Safety", "SAFETY", "Implementation safety", "Implementation Safety"})

#: An ATX heading (CommonMark 4.2) and its inline content.  Up to three leading
#: spaces; a fourth makes the line an indented code block.  The whitespace after
#: the `#` run is required -- `#Safety` renders as a paragraph (round 8).
_MD_ATX_CONTENT = re.compile(r"^ {0,3}#{1,6}[ \t]+(?P<content>.*?)[ \t]*$")

#: CommonMark's optional closing hash sequence, which must be preceded by
#: whitespace and renders as nothing.
_MD_CLOSING_HASHES = re.compile(r"[ \t]+#+$")

def heading_publishes_safety(inline: str) -> bool:
    """Does a heading with this inline content publish a Safety section?

    **The content must BE the title.**  Inline markup is refused, not rendered.

    **PR #895 review round 20, and the correction to round 19.**  Round 19
    asked round 18's question — *is an exact oracle in reach?* — answered
    **no** (this gate runs at Tier 0, before any build, with no CommonMark
    implementation available), and then wrote down the right rule: the reader
    is bounded and *refuses what it cannot render*.  What it actually shipped
    was a partial CommonMark renderer — hand-written emphasis peeling and
    link-label extraction — and two P1 fail-opens fell straight out of the gap
    between the stated rule and the implementation:

    * `# ** Safety **` — an opening delimiter run followed by whitespace is not
      left-flanking, so CommonMark leaves it inactive and rustdoc renders the
      literal `** Safety **`; the peel loop returned `Safety`.
    * `# [Safety](url)junk)` — a link destination is balanced, so rustdoc closes
      it at the first `)` and renders `Safetyjunk)`; a greedy `\S+` swallowed
      `url)junk` and the label was returned as the title.

    Both would have let a **private** `unsafe fn` — which clippy does not
    examine, so this scanner is the only enforcement — pass Tier 0 while
    publishing no caller-facing contract.

    So the implementation is made to match the rule round 19 stated, which is
    also round 16's exit: **where the subject is code this project writes,
    require a canonical spelling and refuse the rest.**  These doc comments are
    this project's own, and the spelling costs nothing — every one of the tree's
    Safety headings is already written plainly, measured.  A contributor who
    writes `# **Safety**` gets a Tier 0 failure naming the heading and asking
    for `# Safety`, which is a stated convention rather than a mystery
    rejection; rendering it correctly would mean implementing CommonMark inline
    parsing here, which is the class this whole section exists to end.
    """
    return inline.strip() in SAFETY_HEADING_TITLES


def atx_heading_content(line: str) -> "str | None":
    """The inline content of an ATX heading line, or `None` if it is not one."""
    match = _MD_ATX_CONTENT.match(line)
    if match is None:
        return None
    return _MD_CLOSING_HASHES.sub("", match.group("content")).strip()


#: A Setext heading underline (CommonMark 4.3): a run of `=` or `-` alone on a
#: line, under up to three spaces of indent.  `=` makes an h1 and `-` an h2, and
#: the heading's text is the paragraph line above it — so `Safety` followed by
#: `======` publishes exactly the `<h2 id="safety">` an ATX `# Safety` does, and
#: refusing it made Tier 0 reject a declaration whose caller-facing contract
#: rustdoc had already published (PR #895 review round 14).  This is the
#: fail-CLOSED direction, which round 6 recorded as a defect in its own right.
MD_SETEXT_UNDERLINE = re.compile(r"^ {0,3}(?:=+|-+)[ \t]*$")

#: The **first** line of the paragraph a Setext underline turns into a heading.
#: Anchored like the ATX pattern so `Safety Requirements` counts the same way
#: there -- and asked of the paragraph's first line, because a Setext heading's
#: content is the WHOLE preceding paragraph, which CommonMark 4.3 permits to
#: span lines.  Reading only the line above the underline accepted
#: `This is not a contract` / `Safety` / `===`, which rustdoc titles
#: "This is not a contract Safety" and which is no Safety section at all
#: (PR #895 review round 15).  Fail-OPEN, on a gate with an empty baseline.
#: A Setext heading's content is its paragraph, whose leading indent (up to
#: three spaces) is stripped before the inlines are read.
_MD_SETEXT_CONTENT = re.compile(r"^ {0,3}(?P<content>.*?)[ \t]*$")


def setext_publishes_safety(opening: str) -> bool:
    """Does this one-line paragraph, under an underline, publish Safety?

    Reads the RENDERED title exactly as the ATX side does (round 19), so
    `**Safety**` over `======` is the section rustdoc publishes for it and
    the two heading syntaxes cannot disagree about one question.
    """
    match = _MD_SETEXT_CONTENT.match(opening)
    return match is not None and heading_publishes_safety(match.group("content"))

#: A thematic break (CommonMark 4.1): three or more `-`, `*` or `_`, optionally
#: separated by spaces or tabs, alone on a line.  It is a leaf block, so it
#: CLOSES an open paragraph -- which is why it has to be recognised here: with
#: the paragraph's first line carried rather than its last, `Safety` / `***` /
#: `===` would otherwise read the paragraph across a break that ended it.
#: A `-` run is tested for a Setext underline FIRST, since a Setext heading
#: takes precedence over a thematic break under an open paragraph (4.3).
MD_THEMATIC_BREAK = re.compile(r"^ {0,3}([-*_])(?:[ \t]*\1){2,}[ \t]*$")

#: An ATX heading (CommonMark 4.2): one to six `#` followed by a space, a tab or
#: the end of the line.  Also a leaf block that closes a paragraph, and for the
#: opposite reason: `# Overview` / `Safety` / `===` publishes a real Safety
#: heading, and carrying the ATX line as the paragraph's first would refuse it.
#: Round 6's rule -- the safe direction is still a direction.
MD_ATX_HEADING = re.compile(r"^ {0,3}#{1,6}(?:[ \t]|$)")

#: CommonMark 4.6 block-level tag names — the start condition of an HTML block
#: of type 6.  Fixed by the specification, so this is the grammar's own list and
#: not a resemblance: a name absent from it opens no type-6 block.
MD_HTML_BLOCK_TAGS = frozenset("""
address article aside base basefont blockquote body caption center col colgroup
dd details dialog dir div dl dt fieldset figcaption figure footer form frame
frameset h1 h2 h3 h4 h5 h6 head header hr html iframe legend li link main menu
menuitem nav noframes ol optgroup option p param search section summary table
tbody td tfoot th thead title tr track ul
""".split())

#: The five HTML block types whose end condition is a *string on a line* rather
#: than a blank line (CommonMark 4.6 types 1-5), as `(start, end)` pairs.  Each
#: holds raw text: no markdown is parsed inside one, so a heading written there
#: is never published.
MD_HTML_RAW_BLOCKS = (
    (re.compile(r"^ {0,3}<(?:pre|script|style|textarea)(?:[ \t>]|$)", re.IGNORECASE),
     re.compile(r"</(?:pre|script|style|textarea)>", re.IGNORECASE)),
    (re.compile(r"^ {0,3}<!--"), re.compile(r"-->")),
    (re.compile(r"^ {0,3}<\?"), re.compile(r"\?>")),
    (re.compile(r"^ {0,3}<![A-Za-z]"), re.compile(r">")),
    (re.compile(r"^ {0,3}<!\[CDATA\["), re.compile(r"\]\]>")),
)

#: Type 6: an open or closing tag whose name is block-level.  Ends at a blank
#: line.
MD_HTML_BLOCK_6 = re.compile(r"^ {0,3}</?([A-Za-z][A-Za-z0-9-]*)(?:[ \t/>]|$)")

#: An attribute of a complete tag (CommonMark 4.6 type 7's start condition).
_MD_ATTR = r"""[ \t]+[A-Za-z_:][A-Za-z0-9_.:-]*(?:[ \t]*=[ \t]*(?:[^ \t"'=<>`]+|'[^']*'|"[^"]*"))?"""

#: Type 7: a *complete* open or closing tag alone on its line.  Ends at a blank
#: line, and — unlike every other type — may not interrupt a paragraph.
MD_HTML_BLOCK_7 = re.compile(
    r"^ {0,3}(?:<[A-Za-z][A-Za-z0-9-]*(?:" + _MD_ATTR + r")*[ \t]*/?>"
    r"|</[A-Za-z][A-Za-z0-9-]*[ \t]*>)[ \t]*$")


def publishes_safety_heading(markdown: str) -> bool:
    """Does this rendered markdown publish a `# Safety` **heading**?

    **A line that looks like a heading is not a heading** (PR #895 review
    round 12).  Inside a fenced or indented code block rustdoc renders
    `# Safety` as literal text, so an `unsafe fn` documented as

    ```rust
    /// ```text
    /// # Safety
    /// ```
    ```

    publishes no caller-facing section at all — and three separate
    line-oriented patterns in this gate accepted it, on all three doc forms.
    Fail-OPEN, on the gate whose whole subject is what a caller is told.

    The three patterns are now one question asked of the **document**, because
    the enclosure is a property of the document and not of the line: a fence
    opened in one `///` line encloses the next, and rustdoc concatenates every
    doc source on an item into one markdown input (see `rendered_doc_markdown`).
    """
    fence = None          # (delimiter char, run length) while a fence is open
    html_end = None       # the end-condition pattern while a raw HTML block is open
    html_blank = False    # a type-6/7 HTML block, which ends at a blank line
    paragraph = False     # an indented code block may not interrupt a paragraph
    opening = None        # the FIRST line of the open paragraph (Setext title)
    opening_alone = False  # ...and whether that paragraph is still ONE line
    for line in markdown.split("\n"):
        # **An HTML block holds raw text** (CommonMark 4.6): no markdown is
        # parsed inside one, so a heading written there is never published --
        # which `/// <!--`, `/// # Safety`, `/// -->` exploited to satisfy this
        # gate while telling the caller nothing (PR #895 review round 13).
        # Types 1-5 end at a string on a line, types 6-7 at a blank line; an
        # unterminated block runs to the end of the document, which is why the
        # state is carried rather than reset per line.
        if html_end is not None:
            if html_end.search(line):
                html_end = None
            continue
        if html_blank:
            if not line.strip():
                html_blank = False
                paragraph = False
                opening = None
            continue
        if fence is None:
            opened = False
            for start, end in MD_HTML_RAW_BLOCKS:
                if start.match(line):
                    # The end condition may be met on the start line itself.
                    html_end = None if end.search(line) else end
                    opened = True
                    break
            if not opened:
                m6 = MD_HTML_BLOCK_6.match(line)
                if m6 is not None and m6.group(1).lower() in MD_HTML_BLOCK_TAGS:
                    html_blank = True
                    opened = True
                elif not paragraph and MD_HTML_BLOCK_7.match(line):
                    # Type 7 alone may not interrupt a paragraph.
                    html_blank = True
                    opened = True
            if opened:
                paragraph = False
                opening = None
                continue
        delim = MD_FENCE.match(line)
        if fence is not None:
            # Only a matching, longer-or-equal run with no info string closes.
            if (delim is not None and delim.group(1)[0] == fence[0]
                    and len(delim.group(1)) >= fence[1]
                    and not delim.group(2).strip()):
                fence = None
            continue
        if delim is not None and _opens_fence(delim):
            fence = (delim.group(1)[0], len(delim.group(1)))
            paragraph = False
            opening = None
            continue
        if not line.strip():
            paragraph = False
            opening = None
            continue
        if not paragraph and re.match(r"^(?: {4}|\t)", line):
            continue          # an indented code block, and still open
        # A Setext underline turns the paragraph ABOVE it into a heading, and
        # that paragraph may span lines -- so the verdict is about `opening`,
        # the paragraph's FIRST line, since the heading's content is the lines
        # concatenated and therefore BEGINS there.  It counts only directly
        # under paragraph content: after a blank line a `---` run is a thematic
        # break, and inside a fence, an HTML block or indented code `opening`
        # was never set.
        if paragraph and opening is not None and MD_SETEXT_UNDERLINE.match(line):
            # A Setext heading's text is the whole paragraph, concatenated -- so
            # a paragraph of two or more lines can never render as exactly an
            # accepted title, whatever its first line says.  Round 15 carried the
            # first line because the verdict was a prefix match; with the title
            # required WHOLE (round 17) the paragraph must also be one line.
            if opening_alone and setext_publishes_safety(opening):
                return True
            paragraph = False
            opening = None
            continue
        # Two leaf blocks that end a paragraph, checked AFTER the underline so
        # a `---` under paragraph content is still the heading CommonMark makes
        # it.  Both matter only because the paragraph's first line is carried:
        # a break would otherwise be read through, and an ATX heading would be
        # mistaken for the content of the paragraph that follows it.
        if MD_THEMATIC_BREAK.match(line):
            paragraph = False
            opening = None
            continue
        atx = atx_heading_content(line)
        if atx is not None and heading_publishes_safety(atx):
            return True
        if MD_ATX_HEADING.match(line):
            paragraph = False
            opening = None
            continue
        if not paragraph:
            opening = line
            opening_alone = True
        else:
            opening_alone = False
        paragraph = True
    return False


def comment_text_of(raw: str, view: str) -> str:
    """`raw` with everything that is NOT comment text blanked, byte-aligned.

    **The view you read depends on the question** (PR #895 review round 10).
    The justification run is deliberately RAW -- what matters is what a reviewer
    reads, so the answer comes from the real file -- and that reasoning is right
    for *reading* a comment and wrong for *deciding whether something is one*.
    Asking `SAFETY_BLOCK` of the raw run let a string literal inside an ordinary
    attribute supply the marker: `#[allow(unused, reason = "// SAFETY: not a
    comment")]` compiles, publishes nothing, and justified the unsafe block
    below it.  Fail-OPEN, on a gate with an empty baseline.

    Derived from the code view rather than re-lexed, because a second Rust lexer
    is this project's one-question-two-answers hazard: `rust_code_view.code`
    blanks comments to spaces and is byte-aligned, so a maximal run of blanked
    bytes that holds at least one byte the raw text did not blank IS a comment,
    and nothing else is.  Ordinary whitespace between code tokens blanks to
    itself and so is never mistaken for one.
    """
    out = [" "] * len(raw)
    for start, end in comment_spans(raw, view):
        for j in range(start, end):
            out[j] = raw[j]
    for j, ch in enumerate(view):
        if ch == "\n":
            out[j] = "\n"
    return "".join(out)


def comment_spans(raw: str, view: str) -> list[tuple[int, int]]:
    """Byte spans of the comments in `raw`, derived from its code `view`.

    A maximal run of bytes the view blanked, holding at least one byte the raw
    text did not blank, is a comment; ordinary whitespace between code tokens
    blanks to itself and never qualifies.  Exposed separately from
    `comment_text_of` because *which kind* of comment a span is decides what it
    can publish: a `/**` sitting inside a `//` line is text, not a doc block
    (PR #895 review round 11).
    """
    spans: list[tuple[int, int]] = []
    i, n = 0, len(raw)
    while i < n:
        if view[i] != " ":
            i += 1
            continue
        start = i
        while i < n and view[i] == " ":
            i += 1
        if any(raw[j] not in " \n" for j in range(start, i)):
            spans.append((start, i))
    return spans


def justified(run: str, is_declaration: bool) -> bool:
    """Does this run carry the justification its site kind calls for?

    **Each kind, its own idiom, and no fallback between them.**  An earlier cut
    let a declaration pass on a `// SAFETY:` comment as well, which reads like
    leniency and is not: the two idioms publish to different audiences.  A
    `// SAFETY:` comment is *inside* the file, for the reviewer reading the next
    line; a `# Safety` doc section is rustdoc, for the **caller** who will have
    to discharge the obligation and never opens this file.  Accepting the first
    in place of the second passes an `unsafe fn` that exposes no contract at all
    to the people bound by it — which is why this file's own comment above, and
    `CLAUDE.md`, both say the two are *not interchangeable*.  The gate now says
    so too.

    The tree relies on the fallback nowhere: all twelve `unsafe fn`
    declarations carry a `# Safety` section, so removing it fails nothing
    today and refuses the next declaration documented the wrong way."""
    if is_declaration:
        return declaration_documents_safety(run)
    # Comment text only: a `// SAFETY:` inside a string literal is a string, and
    # the marker has to be something a compiler would discard (round 10).
    return bool(SAFETY_BLOCK.search(comment_text_of(run, rust_code_view.code(run))))


def is_attribute_only(code_line: str) -> bool:
    """Is this code-view line *nothing but* attributes?

    **A line that starts as an attribute is not a line that is one.**  Testing
    `startswith("#[")` let `#[allow(unused)] let x = compute();` extend a
    justification run, so a `// SAFETY:` comment carried across a real statement
    and marked the block below it justified (PR #895 review round 5) — while the
    run's own contract, written directly beneath it, is that *nothing may execute
    between the justification and the operation it justifies*.

    The attribute's extent is bracket-matched rather than assumed: an attribute
    left open at end of line continues onto the next, and the rest of the line is
    inside it, so the line carries no code.
    """
    rest = code_line.strip()
    while rust_code_view.attribute_opens_at(rest) is not None:
        open_at = rest.index("[")
        depth = 0
        close_at = None
        for i in range(open_at, len(rest)):
            if rest[i] == "[":
                depth += 1
            elif rest[i] == "]":
                depth -= 1
                if depth == 0:
                    close_at = i
                    break
        if close_at is None:
            # Unterminated on this line: the remainder is attribute interior.
            return True
        rest = rest[close_at + 1:].strip()
    return rest == ""


#: Keywords that may sit between an item's real start and the token this gate
#: matches it at (`unsafe` for a declaration, `fn` for a foreign item).  They
#: belong to the item, so they are transparent to the justification run.
ITEM_MODIFIERS = frozenset({"pub", "const", "async", "default", "unsafe", "extern"})


#: A completed statement on the site's own line.  For a BLOCK this is what
#: "something executed in between" looks like — a bare binding prefix
#: (`let inner = `) is not, since the block is evaluated to produce its value.
STATEMENT_BREAK = re.compile(r"[;{}]")


def _same_line_prefix(raw: str, view: str, line_start: int, at: int,
                      is_declaration: bool) -> tuple[str, bool]:
    """`(the site's own-line prefix trimmed to its trailing justification, code?)`.

    **The two site kinds ask different questions of the same line.**

    For a BLOCK, the prefix is the statement the block is evaluated *within*:
    `let inner = unsafe { … };` runs the block first and binds its value, so
    nothing has executed between the comment above and the operation — and
    Rust's own convention, the one `clippy::undocumented_unsafe_blocks` reads,
    puts the `// SAFETY:` above that statement.  What genuinely intervenes is a
    *completed* statement, so the run stops at a `;` / `{` / `}` and not at any
    code at all.

    For a DECLARATION it is the opposite: code before it on its own line is a
    different ITEM, whose documentation does not carry.  That is the round-6
    finding.

    **The prefix is not automatically a justification.**  Taking the site's whole
    same-line prefix let a *preceding item on that line* donate its
    documentation: in
    `unsafe extern "C" { #[doc = "# Safety"] fn documented(); fn undocumented(); }`
    the second foreign function inherited the first's doc attribute and passed,
    while rustdoc leaves it undocumented (PR #895 review round 6).  It is the
    same relation the upward walk already enforces line by line — *nothing may
    execute between the justification and the operation* — asked of the one line
    the walk never examined.

    So the prefix is trimmed, right to left, over whitespace, block comments and
    complete attributes, and stops at the first CODE.  Comment interiors are
    blanked to spaces in the code view, so whitespace and comments need no
    distinction here: both are transparent, and anything else is not.  The
    second element reports whether code was found, because a site with code
    before it on its own line cannot be justified from further up either.
    """
    if not is_declaration:
        last = None
        for m in STATEMENT_BREAK.finditer(view, line_start, at):
            last = m
        if last is not None:
            return raw[last.end():at], True
        return raw[line_start:at], False
    end = at
    while end > line_start:
        if view[end - 1].isspace():          # whitespace, or a blanked comment
            end -= 1
            continue
        # An item's own MODIFIERS are not code preceding it.  A declaration site
        # is matched at its `unsafe` token and a foreign item at its `fn`, so
        # `pub`, `pub(crate)`, `const`, `async` and friends sit between the item's
        # real start and the offset — treating them as code cut the run off from
        # the doc comment directly above `pub unsafe fn f()`.  The set is Rust's
        # and is closed; a modifier missing from it reads as code, which stops
        # the run and fails the site CLOSED rather than silently widening it.
        if view[end - 1] == ")":             # a `pub(crate)` / `pub(in …)` group
            depth, k = 0, end
            while k > line_start:
                k -= 1
                if view[k] == ")":
                    depth += 1
                elif view[k] == "(":
                    depth -= 1
                    if depth == 0:
                        break
            word = re.search(r"(" + IDENT + r")\s*$", view[line_start:k])
            if depth == 0 and word and word.group(1) == "pub":
                end = line_start + word.start(1)
                continue
        word = re.search(r"(" + IDENT + r")\s*$", view[line_start:end])
        if word and word.group(1) in ITEM_MODIFIERS:
            end = line_start + word.start(1)
            continue
        if view[end - 1] == "]":             # a complete `#[ … ]` / `#![ … ]`?
            depth, k = 0, end
            while k > line_start:
                k -= 1
                if view[k] == "]":
                    depth += 1
                elif view[k] == "[":
                    depth -= 1
                    if depth == 0:
                        break
            if depth == 0 and view[k] == "[":
                open_at = k
                if open_at - 1 >= line_start and view[open_at - 1] == "!":
                    open_at -= 1
                if open_at - 1 >= line_start and view[open_at - 1] == "#":
                    end = open_at - 1
                    continue
        break
    return raw[end:at], end > line_start


def justification_run(raw: str, view: str, at: int, is_declaration: bool,
                      bare: str | None = None) -> str:
    """The contiguous comment-and-attribute run immediately above `at`.

    Walks upward line by line while each line is blank in the code view (a
    whole-line comment), is blank outright, or is an attribute, and stops at the
    first line carrying code.  Returns the RAW text of that run — the question is
    what a reviewer reads, so the answer comes from the real file.

    **An attribute is one item, not one line** (PR #895 review round 8).  Deciding
    each physical line independently meets a multi-line `#[cfg(all( … ))]` at its
    closing `))]`, which starts with neither `#[` nor a comment, so the walk
    stopped *below* the documentation and a correctly written declaration was
    reported unjustified — Tier 0 refusing valid Rust, the fail-STRICT direction.
    So an unbalanced closer opens a pending run that is consumed until its
    brackets balance, and the line that balances it must itself open an attribute:
    a multi-line *expression* ending in `]` is code, and extending the run across
    it would carry a justification over something that executes, which is the
    fail-OPEN direction this run's whole contract forbids.

    `bare` is the string-free view, used for the bracket arithmetic only — a `]`
    inside a string literal is text, not structure.  It defaults to `view` so the
    self-test may pass one argument, and every live caller passes both.
    """
    counted = bare if bare is not None else view
    line_start = raw.rfind("\n", 0, at) + 1
    # A trailing comment on the site's own line counts: `unsafe { … } // SAFETY: …`
    # does not, but `// SAFETY: …` before it on the same line does — provided
    # nothing executes in between, which is what the trim below establishes.
    prefix, prefix_has_code = _same_line_prefix(raw, view, line_start, at, is_declaration)
    run = [prefix]
    if prefix_has_code:
        return prefix
    idx = line_start
    # Lines held while a multi-line attribute is being closed from below.  They
    # join the run only once the brackets balance AND the balancing line opens an
    # attribute; otherwise they are code and the run ended beneath them.
    pending_raw: list[str] = []
    pending_code: list[str] = []
    depth = 0
    while idx > 0:
        prev_end = idx - 1
        prev_start = raw.rfind("\n", 0, prev_end) + 1
        raw_line = raw[prev_start:prev_end]
        view_line = view[prev_start:prev_end]
        counted_line = counted[prev_start:prev_end]
        stripped_code = view_line.strip()
        stripped_raw = raw_line.strip()
        opens = sum(counted_line.count(ch) for ch in "([{")
        closes = sum(counted_line.count(ch) for ch in ")]}")
        if depth > 0:
            depth += closes - opens
            pending_raw.append(raw_line)
            pending_code.append(stripped_code)
            idx = prev_start
            if depth <= 0:
                joined = " ".join(reversed(pending_code)).strip()
                if (rust_code_view.attribute_opens_at(joined) is not None
                        and is_attribute_only(joined)):
                    run.extend(pending_raw)
                    pending_raw, pending_code, depth = [], [], 0
                    continue
                break
            continue
        is_comment_only = stripped_raw != "" and stripped_code == ""
        is_attribute = (rust_code_view.attribute_opens_at(stripped_code) is not None
                        and is_attribute_only(stripped_code))
        # A blank line is TRANSPARENT: a doc block separated from its attribute
        # list by one is ordinary formatting, and treating it as a break would
        # refuse the tree's own convention.  What breaks the run is a line
        # carrying CODE — that is the relation, since nothing may execute
        # between the justification and the operation it justifies.
        is_blank = stripped_raw == ""
        if is_comment_only or is_attribute or is_blank:
            run.append(raw_line)
            idx = prev_start
            continue
        if closes > opens and stripped_code.endswith(("]", ")", "}")):
            # Possibly the tail of a multi-line attribute; the line that balances
            # it decides.
            depth = closes - opens
            pending_raw = [raw_line]
            pending_code = [stripped_code]
            idx = prev_start
            continue
        # **The line that ends the run may still carry documentation for us.**
        # A `///` attaches to the item that FOLLOWS it, so on
        # `pub mod m { /// # Safety` the comment documents the first item inside
        # the module -- our site -- while only `pub mod m {` intervenes.  The
        # walk stopped at the whole line and lost the section, reporting a
        # correctly documented `unsafe fn` as unjustified: Tier 0 refusing valid
        # Rust (PR #895 review round 9).
        #
        # Taking the trailing portion is not a widening of round 6's rule but the
        # other side of it.  That finding was documentation sitting BEFORE an
        # intervening item on the line (`#[doc = "…"] fn documented(); fn us();`),
        # which is consumed by that item and stays inside the code region here.
        # What this adds is documentation sitting AFTER the code, which no item
        # has consumed and which rustdoc gives to the next one.  The distinction
        # is the byte offset of the last code character, so both hold at once.
        trailing = raw_line[len(view_line.rstrip()):]
        if trailing.strip():
            run.append(trailing)
        break
    return "\n".join(reversed(run))


UNSAFE_FN_NAME = re.compile(
    KW_UNSAFE + r"\s+(?:" + KW_EXTERN + r"\s+" + ABI + r"\s+)?"
    + KW_FN + r"\s+(?:r#)?(?P<name>" + MACRO_NAME + IDENT + r")", re.UNICODE)


#: A foreign function item inside a foreign block, and the `safe` opt-out.
FOREIGN_FN = re.compile(
    r"(?P<safe>" + rust_code_view.keyword("safe") + r"\s+)?"
    + KW_FN + r"\s+(?:r#)?(?P<name>" + IDENT + r")\s*\(", re.UNICODE)


def foreign_fn_items(view: str):
    """Yield `(offset, name)` for every non-`safe` foreign function declared.

    **A domain the gate never examined.**  `UNSAFE_SITE` looks for the `unsafe`
    keyword, and a foreign item carries none — the block header does, and only in
    edition 2024.  So every `extern "C" { fn … }` in the tree declared a
    caller-facing unsafe obligation that no count, no inventory and no baseline
    could see (PR #895 review round 5).  That is this project's *a recognised set
    is not a derived set* on the one gate written after the rule: the items are
    never inspected, so the empty baseline stays green over them.

    **...and scanning the block for `fn` was the same defect one level in**
    (PR #895 review round 7).  A foreign block may hold an item MACRO, which
    Rust expands into real declarations: `unsafe extern "C" { decl!(); }` where
    `decl!` expands to `fn undocumented();` declares an unsafe obligation that
    a `fn`-shaped search cannot see, so the site never existed and the empty
    baseline stayed green over it.  The sibling gate
    `scripts/check_kernel_entry_exports.py` had refused exactly this since
    PR #889 review round 21 and every other unrecognised item since round 25 —
    and `CLAUDE.md` recorded the rule as implemented, of a tree in which one of
    the two gates that parse foreign blocks did it.

    So the block is walked as ITEMS through `rust_code_view`, which is now where
    that question is answered once: an item macro or a form the view does not
    know is REFUSED, and only a `static`, a type alias or a `use` — items that
    genuinely declare no function — may be skipped.  This gate derives
    REQUIREMENTS (sites that must carry a justification), so refusal is its
    fail-closed direction: a requirement dropped is a check nobody runs.
    """
    for _keyword, open_at, end in rust_code_view.extern_blocks(view):
        for item_at, item_end in rust_code_view.extern_block_items(view, open_at + 1, end):
            kind = rust_code_view.classify_extern_item(view, item_at, item_end)
            if kind == "non-fn":
                continue
            if kind != "fn":
                raise UnreadableExternItem(view[item_at:item_end].strip()[:60], kind)
            f = FOREIGN_FN.search(view, item_at, item_end)
            if f is None:
                # The shared view calls it a function and this gate's own
                # pattern cannot read it — two answers to one question, which is
                # the shape this move exists to remove.  Refuse rather than
                # letting the disagreement silently drop a site.
                raise UnreadableExternItem(view[item_at:item_end].strip()[:60], "fn")
            if f.group("safe"):     # `safe fn` — the edition-2024 opt-out
                continue
            # The ITEM's offset, not the name's: the justification run is the
            # text immediately before the item, and `fn ` sits between the two.
            # Keying it on the name made that keyword read as code preceding the
            # site, so a correctly documented foreign function found an empty run.
            yield (f.start(), f.group("name"))


class UnreadableExternItem(Exception):
    """An item inside a foreign block whose form this scanner cannot read."""

    def __init__(self, snippet: str, kind: str) -> None:
        super().__init__(
            f"an item inside an `extern` block ({snippet!r}) is a {kind}, not a `fn` "
            f"declaration this gate can read.  If it declares a function symbol its "
            f"unsafe obligation is missing; write the declaration out, or teach "
            f"`rust_code_view.classify_extern_item` the form.")
        self.snippet = snippet
        self.kind = kind


#: What "this gate cannot read its input" looks like, in ONE place.
#:
#: Three sites answered this question with three hand-written tuples — the
#: scanner, the refusal harness and the form matrix — so `UnterminatedLiteral`
#: could be, and was, absent from two of them while the third looked complete
#: (PR #895 review round 11).  A shared refusal set also makes the omission
#: *detectable*: drop a member and the refusal cases stop being caught anywhere,
#: where before the harness's own copy silently absorbed what the gate would
#: have tracebacked on.
#:
#: Membership is a decision, not a catch-all: every entry is a refusal this gate
#: reports by name.  An exception that is not one of these is a defect in the
#: gate and must reach the operator as a traceback.
REFUSALS = (UnreadableExternItem, UnreadableDocAttribute,
            rust_code_view.UnbalancedExternBlock,
            rust_code_view.UnterminatedLiteral)


def sites(path: Path):
    """Yield (offset, enclosing declaration, justification run) per unsafe site.

    An `unsafe fn` DECLARATION is keyed by its own name, not by the scope it sits
    in: its `unsafe` token is outside every function body, so keying it by the
    enclosing scope would collapse every `unsafe fn` of a file onto one key — a
    cardinality one level up, which cannot see one declaration gaining a site
    while another gives one up.

    **The interior of a foreign block belongs to exactly one pass** (PR #895
    review round 22).  Two passes run here — the `unsafe` KEYWORD scan and the
    foreign-ITEM walk — and inside an `unsafe extern` block a declaration may
    carry the keyword explicitly (`unsafe fn f();`, RFC 3484's per-item marker,
    whose `safe fn` opt-out this gate already reads).  Both passes then yielded
    it, at two offsets seven bytes apart, so ONE declaration became TWO rows:
    `UNSAFE_SITES_TOTAL`, `UNSAFE_FN_DECLARATIONS`, the ARM citation ratio and
    any baseline all counted it twice, and an *undocumented* one produced two
    violations a single baseline entry could not account for.  Latent only
    because no declaration in this tree is spelled that way — which is round 5's
    defect in this same gate, one pass over: a domain nobody measured.

    The foreign pass owns that region, and the direction is the one this gate's
    domain rule requires.  It is DERIVED from the item structure rather than
    from a token — it splits the block into items, classifies each, and refuses
    a form it cannot read — so nothing inside the braces escapes it, and
    skipping the region in the keyword pass drops no requirement.  The reverse
    assignment would: the keyword pass sees only what carries the token, so a
    `fn` with no marker (the block-level default) has no site there at all.
    """
    raw = path.read_text(encoding="utf-8")
    view = rust_code_view.code_no_strings(raw)
    aligned = rust_code_view.code(raw)
    bodies = rust_code_view.fn_bodies(raw)
    # **The run is the lines immediately above the site, and a line carrying
    # CODE ends it.**  An earlier cut anchored the run to the enclosing
    # top-level statement instead, on the reasoning that `let x =\n    unsafe
    # { … };` puts the justification above the statement rather than above the
    # token.  That is true, and it is the *code* that should move: Rust's own
    # convention — and the one `clippy::undocumented_unsafe_blocks` reads — puts
    # the `// SAFETY:` on the block.  Resolving it in the scanner instead buys
    # four sites and costs the relation its sharpness, since a statement can be
    # long and its run then sits arbitrarily far from the operation.
    # The half-open interiors the foreign-item pass owns, so the keyword pass
    # below does not also report a declaration that marks itself `unsafe`.
    foreign_interiors = [(open_at, end)
                         for _kw, open_at, end in rust_code_view.extern_blocks(view)]
    for m in UNSAFE_SITE.finditer(view):
        if any(open_at < m.start() < end for open_at, end in foreign_interiors):
            continue
        named = UNSAFE_FN_NAME.match(view, m.start())
        if named:
            decl = named.group("name")
        else:
            decl = rust_code_view.enclosing_fn(raw, m.start(), bodies) or "<module scope>"
        yield (m.start(), decl,
               justification_run(raw, aligned, m.start(), named is not None, view),
               named is not None)
    # Foreign function declarations, which carry no `unsafe` token of their own.
    for offset, name in foreign_fn_items(view):
        yield (offset, name, justification_run(raw, aligned, offset, True, view), True)


def compiled_rust_sources(root: Path) -> list[Path]:
    """Every Rust source the workspace compiles, derived rather than filtered.

    **The domain was an exclusion wearing a glob.**  `*/src/**/*.rs` names the
    crate libraries and silently omits everything else cargo builds --
    integration tests, `build.rs`, examples, benches.  That is this project's
    "a recognised set is not a derived set" one level up from the predicate: the
    omitted files are never examined, so the count reads as a measurement of the
    tree while describing a subset of it, and the empty baseline stays green
    over an unjustified `unsafe` in any of them.  Not hypothetical --
    `rust/sele4n-hal/tests/readiness_gate_after_mark.rs` carries a real block.

    So the set is every `.rs` file under the workspace that is not build output.
    `target/` is cargo's own, and `.rs` files there are generated rather than
    written; everything else a contributor can put an `unsafe` in is in scope.
    Over-approximating is the safe direction here: this scanner produces
    *requirements*, and a requirement it drops is a check nobody runs.

    **And the exclusion names cargo's output ROOT, not the directory name**
    (PR #895 review round 10).  Testing every path component dropped any source
    under a nested directory that happens to be called `target` --
    `rust/sele4n-hal/src/target/aarch64.rs` is an ordinary module a contributor
    would plausibly write on this project, since the tree is organised by
    hardware target -- so an unjustified site there was absent from the count,
    the inventory and the baseline alike.  That is the same domain defect the
    glob above was fixed for, reintroduced by the filter written to fix it: the
    remedy for an over-broad exclusion is a narrower one only when the narrower
    one names the actual thing.  Cargo's output root is `<workspace>/target`,
    one directory, and `CARGO_TARGET_DIR` is honoured because a caller may have
    moved it.

    **A relative `CARGO_TARGET_DIR` is cargo's, so it resolves where cargo
    resolves it** (PR #895 review round 21): from the *invocation* directory,
    not from whatever root this scan happens to have narrowed to.  Launched at
    the repository root with the setting a contributor would actually write,
    `CARGO_TARGET_DIR=rust/target`, the previous line excluded
    `<root>/rust/rust/target` -- a path that does not exist -- while cargo wrote
    to `<root>/rust/target`, which was therefore scanned.  Generated `.rs` under
    a build script's `OUT_DIR` is code nobody in this tree wrote, so an unsafe
    site there would have failed Tier 0 against a file the contributor cannot
    edit.  The unset default stays `root / "target"`, which is the one case
    where the scan root really is the workspace cargo would use.
    """
    setting = os.environ.get("CARGO_TARGET_DIR")
    if setting:
        # `Path.cwd()` is the invocation directory, which is what cargo joins a
        # relative setting onto; an absolute setting is already resolved.
        build_output = (Path.cwd() / Path(setting)).resolve()
    else:
        build_output = (root / "target").resolve()
    return [
        path
        for path in sorted(root.rglob("*.rs"))
        if not path.resolve().is_relative_to(build_output)
    ]


def census(root: Path):
    """(unjustified inventory, sites, ARM-ARM-citing sites, declarations, unreadable).

    The declaration count is reported because the two kinds are documented
    differently and prose cites the number: a figure nothing emits is a figure
    that goes stale, and this one had — `CLAUDE.md` said thirteen where the
    tree has ten in the HAL.
    """
    inventory: dict[str, int] = {}
    total = 0
    cited = 0
    declarations = 0
    unreadable: list[str] = []
    for path in sorted(compiled_rust_sources(root)):
        rel = str(path.relative_to(REPO))
        try:
            # Inside the try with everything else: this call builds a code view
            # too, so it raises on exactly the input the handler below exists
            # for, and sitting above it was a second escape route out of the
            # "one failure channel" (PR #895 review round 11).
            unreadable += unrecognised_unsafe_forms(
                path.relative_to(REPO), rust_code_view.code_no_strings(
                    path.read_text(encoding="utf-8")))
            file_sites = list(sites(path))
            # The verdicts are computed INSIDE the try: a refusal can come from
            # reading a site's documentation as well as from finding the site,
            # and `UnreadableDocAttribute` is raised by `justified`.  Catching
            # only around `sites` left that one escaping as a traceback -- the
            # same "one failure channel" this block exists for, missed at the
            # half of the work it did not wrap.
            verdicts = [(decl, is_decl, run, justified(run, is_decl))
                        for _off, decl, run, is_decl in file_sites]
        except REFUSALS as refusal:
            # One failure channel, so a refusal reads like every other gate
            # defect instead of leaving a traceback.  `UnreadableExternBlock`
            # used to be raised and caught nowhere at all.
            unreadable.append(f"{rel}: {refusal}")
            continue
        for decl, is_decl, run, ok in verdicts:
            total += 1
            if is_decl:
                declarations += 1
            if ARM_ARM.search(run):
                cited += 1
            if not ok:
                inventory[f"{rel}|{decl}"] = inventory.get(f"{rel}|{decl}", 0) + 1
    return inventory, total, cited, declarations, unreadable


def reconcile(current: dict[str, int], baseline: dict[str, int]) -> list[str]:
    """Where the inventory and the floor disagree; `[]` when the floor holds."""
    problems = []
    for key, count in sorted(current.items()):
        if key not in baseline:
            problems.append(
                f"NEW unjustified unsafe site: {key} ({count}).  An `unsafe` BLOCK needs a "
                f"`// SAFETY:` comment in the contiguous comment run immediately above it — "
                f"what a reviewer reads before the operation.  An `unsafe fn` DECLARATION "
                f"needs a `# Safety` doc section, which is what its CALLERS read; the two "
                f"idioms are not interchangeable."
            )
        elif count > baseline[key]:
            problems.append(
                f"GREW: {key} has {count} unjustified unsafe site(s), baseline {baseline[key]}"
            )
    for key, count in sorted(baseline.items()):
        if current.get(key, 0) > count:
            continue
        if current.get(key, 0) == 0 and count > 0:
            problems.append(
                f"STALE floor entry: {key} is fully justified now (baseline {count}).  "
                f"Re-anchor with --update; a floor above the tree reads like coverage."
            )
    return problems


# ---------------------------------------------------------------------------
# Self-test.  Every mutation is TOKEN-PRESERVING: it keeps the `SAFETY` comment
# the tree has and breaks the RELATION the gate asserts, because a fixture that
# mutated by deletion is satisfied by any presence check — which is precisely
# what the five-line window this gate replaces would have been.
# ---------------------------------------------------------------------------
_CASES = [
    ("justified", True, """
fn f() {
    // SAFETY: the pointer is valid for the lifetime of the call.
    unsafe { g() }
}
"""),
    ("the comment is BELOW the block", False, """
fn f() {
    unsafe { g() }
    // SAFETY: the pointer is valid for the lifetime of the call.
}
"""),
    ("a statement separates the comment from the block", False, """
fn f() {
    // SAFETY: the pointer is valid for the lifetime of the call.
    let x = h();
    unsafe { g(x) }
}
"""),
    ("the token is inside a string literal", False, """
fn f() {
    let msg = "SAFETY: not a justification";
    unsafe { g(msg) }
}
"""),
    ("an attribute between the comment and the block is fine", True, """
fn f() {
    // SAFETY: the pointer is valid for the lifetime of the call.
    #[allow(clippy::undocumented_unsafe_blocks)]
    unsafe { g() }
}
"""),
    ("an `unsafe fn` needs one too", False, """
// A declaration with no justification at all.
unsafe fn f() {}
"""),
    ("a justified `unsafe fn`", True, """
/// # Safety
///
/// The caller holds the lock this reads.
unsafe fn f() {}
"""),
    # A `macro_rules!` template is one declaration site for every name it
    # mints (the v0.36.2 audit): its `///` lines are the expansions' docs.
    ("a macro template's `unsafe fn $name` needs a `# Safety` section too", False, """
macro_rules! exports {
    ($($name:ident;)+) => {$(
        #[no_mangle]
        pub unsafe extern "C" fn $name(o: Obj) {
            // SAFETY: the caller passes a live object.
            unsafe { g(o) }
        }
    )+};
}
"""),
    ("a justified macro-template declaration", True, """
macro_rules! exports {
    ($($name:ident;)+) => {$(
        /// An export minted by `exports`.
        ///
        /// # Safety
        ///
        /// The caller passes a live object.
        #[no_mangle]
        pub unsafe extern "C" fn $name(o: Obj) {
            // SAFETY: the caller passes a live object.
            unsafe { g(o) }
        }
    )+};
}
"""),
    # THE ABI-QUALIFIER CASE.  `pub unsafe extern "C" fn` is the ordinary FFI
    # spelling, and requiring `fn` immediately after `unsafe` made it not a site
    # at all -- absent from the count and from the inventory alike, with an
    # empty baseline still reporting PASS.  That is fail-OPEN: a dropped
    # obligation, silently.
    ("an undocumented `unsafe extern \"C\" fn`", False, """
pub unsafe extern "C" fn f() {}
"""),
    ("a justified `unsafe extern \"C\" fn`", True, """
/// # Safety
///
/// The caller upholds the C ABI contract.
pub unsafe extern "C" fn f() {}
"""),
    # TOKEN-PRESERVING: the justification is there, in the idiom the *other*
    # site kind uses.  A declaration publishes its obligation to callers who
    # never open this file, so a comment they cannot see is not that contract —
    # and this is the case the retired `SAFETY_BLOCK` fallback accepted.
    ("an `unsafe fn` documented in the BLOCK idiom", False, """
// SAFETY: the caller holds the lock this reads.
unsafe fn f() {}
"""),
    # TOKEN-PRESERVING, and the defect the `\*` alternative shipped: the
    # heading is present, spelled inside an ORDINARY block comment.  Rustdoc
    # publishes nothing from it, so the caller bound by the obligation never
    # sees a contract.  The mutation keeps every token and changes only which
    # comment carries it.
    ("an `unsafe fn` whose `# Safety` is in a plain block comment", False, """
/*
 * # Safety
 * The caller must hold the lock.
 */
unsafe fn f() {}
"""),
    # ...and the same heading inside a DOC block is the real contract.
    ("an `unsafe fn` whose `# Safety` is in a doc block", True, """
/**
 * # Safety
 * The caller must hold the lock.
 */
unsafe fn f() {}
"""),
    # Rust's attribute spelling publishes the identical section, so refusing it
    # would reject correctly documented code — the fail-closed direction, but
    # still wrong.
    ("an `unsafe fn` documented with `#[doc = \"# Safety\"]`", True, """
#[doc = "# Safety"]
#[doc = "The caller must hold the lock."]
unsafe fn f() {}
"""),
    # ...and the converse still holds: a block wants the comment, not a doc
    # section, so the two cases together pin the separation in both directions.
    ("an `unsafe` block documented in the DECLARATION idiom", False, """
fn f() {
    /// # Safety
    ///
    /// The pointer is valid for the lifetime of the call.
    unsafe { g() }
}
"""),
    ("an `unsafe {` inside a comment is not a site", True, """
fn f() {
    // Historically this was `unsafe { g() }`; it no longer is.
    h()
}
"""),
    ("a doc-comment justification counts", True, """
fn f() {
    /// SAFETY: the pointer is valid for the lifetime of the call.
    unsafe { g() }
}
"""),
    ("a block-comment justification counts", True, """
fn f() {
    /* SAFETY: the pointer is valid for the lifetime of the call. */
    unsafe { g() }
}
"""),
    # The two kinds, and their two idioms.
    ("an `unsafe fn` documented with a `# Safety` section", True, """
/// Reads the register bank.
///
/// # Safety
///
/// The caller holds the per-core lock.
#[inline]
unsafe fn f() {}
"""),
    ("...and a `# Safety` section does NOT justify a block", False, """
fn f() {
    // # Safety
    // The caller holds the per-core lock.
    unsafe { g() }
}
"""),
    ("a blank line between the doc block and the attributes is transparent", True, """
/// # Safety
///
/// The caller holds the per-core lock.

#[inline]
unsafe fn f() {}
"""),
    # INNER rustdoc documents the enclosing module, not the following item, so
    # the function it precedes publishes no contract.  Token-preserving against
    # the accepted cases above: same declaration, same `# Safety` text, only the
    # comment's DIRECTION changes.
    ("an `unsafe fn` preceded by INNER line rustdoc (`//!`)", False, """
//! # Safety
//! The caller holds the per-core lock.
unsafe fn f() {}
"""),
    ("an `unsafe fn` preceded by an INNER doc block (`/*!`)", False, """
/*! # Safety
 * The caller holds the per-core lock.
 */
unsafe fn f() {}
"""),
    ("an `unsafe fn` with an INNER `#![doc]` attribute", False, """
#![doc = "# Safety: the caller holds the per-core lock."]
unsafe fn f() {}
"""),
    # `////` and `/***` are regular comments in Rust, not doc comments -- the
    # reference excludes a fourth `/` and a third `*` -- so neither publishes
    # anything.  Each is ONE character from an accepted case above.
    ("an `unsafe fn` whose `# Safety` is in a `////` comment", False, """
//// # Safety
//// The caller holds the per-core lock.
unsafe fn f() {}
"""),
    ("an `unsafe fn` whose `# Safety` is in a `/***` comment", False, """
/*** # Safety
 * The caller holds the per-core lock.
 */
unsafe fn f() {}
"""),
    ("an `unsafe fn` with a doc comment that never mentions safety", False, """
/// Reads the register bank.  Fast.
#[inline]
unsafe fn f() {}
"""),
    # A keyword in a TYPE performs nothing.
    ("an `unsafe fn` POINTER TYPE is not a site", True, """
fn pin_the_abi() {
    let _: unsafe fn(u8, Handler) = register;
}
"""),
    ("`unsafe impl` is not a site", True, """
unsafe impl Send for T {}
"""),
    # THE ABI IS A STRING LITERAL, and a raw string is one.  Token-preserving
    # against the accepted `extern "C"` cases: same declaration, same section,
    # the ABI respelled.
    ("a raw-string ABI declaration, documented", True, """
/// # Safety
/// The caller holds the per-core lock.
pub unsafe extern r"C" fn f() {}
"""),
    ("a raw-string ABI declaration, undocumented", False, """
pub unsafe extern r"C" fn f() {}
"""),
    # A HEADING BEGINS A LINE.  Markdown renders a mid-line `# Safety` as
    # ordinary prose, so it publishes nothing; these two keep the text and move
    # it.
    ("`#[doc]` whose `# Safety` is mid-line", False, """
#[doc = "This function has no # Safety section."]
pub unsafe fn f() {}
"""),
    ("`#[doc]` whose `# Safety` opens a line", True, """
#[doc = "intro\\n# Safety\\nThe caller holds the per-core lock."]
pub unsafe fn f() {}
"""),
    # AN ATTRIBUTE LINE MUST BE ONLY AN ATTRIBUTE.  A statement between the
    # justification and the operation breaks the relation the run asserts;
    # token-preserving against the accepted bare-attribute case below it.
    ("an attribute line that also carries a statement", False, """
fn g() {
    // SAFETY: pinned by the caller.
    #[allow(unused)] let x = compute();
    unsafe { h() }
}
"""),
    ("a bare attribute line is still transparent", True, """
fn g() {
    // SAFETY: pinned by the caller.
    #[allow(unused)]
    unsafe { h() }
}
"""),
    # A FOREIGN ITEM IS A DECLARATION SITE: it carries no `unsafe` token of its
    # own, and calling it is unsafe all the same.
    ("a foreign fn with no `# Safety` section", False, """
extern "C" {
    fn foreign(x: u64) -> u32;
}
"""),
    ("a foreign fn with a `# Safety` section", True, """
extern "C" {
    /// # Safety
    /// Only on a ready core.
    fn foreign(x: u64) -> u32;
}
"""),
    ("a Rust-2024 `safe fn` in an extern block is not a site", True, """
unsafe extern "C" {
    safe fn harmless(x: u64) -> u32;
}
"""),
    # A MARKER NESTED IN ANOTHER COMMENT PUBLISHES NOTHING.  Rust block comments
    # nest, and rustdoc takes nothing from the inner one, so the declaration
    # below exposes no caller-facing contract.  Token-preserving against the
    # accepted doc-block case above: the same `/** # Safety */`, wrapped.
    ("an `unsafe fn` whose doc block is NESTED in a plain comment", False, """
/* outer plain comment
   /** # Safety
       The caller must hold the lock. */
   still the outer comment */
pub unsafe fn f() {}
"""),
    # ...and the same relation for the sibling markers, which are `re.MULTILINE`
    # searches and so matched a `///` line spelled inside a block comment.
    ("an `unsafe fn` whose `///` heading is inside a block comment", False, """
/* outer plain comment
   /// # Safety
   The caller must hold the lock. */
pub unsafe fn f() {}
"""),
    # A RAW STRING'S HASHES ARE BALANCED.  `r#"C"#` is a legal ABI spelling that
    # rustc accepts; consuming only the opening hashes left the closing `#`
    # where the pattern wanted whitespace, so the site vanished AND the file was
    # rejected as an unrecognised form.  Token-preserving against the accepted
    # `extern r"C"` case: one more hash on each side.
    ("a hashed raw-string ABI declaration, documented", True, """
/// # Safety
/// The caller upholds the C ABI contract.
pub unsafe extern r#"C"# fn f() {}
"""),
    ("a hashed raw-string ABI declaration, undocumented", False, """
pub unsafe extern r#"C"# fn f() {}
"""),
    # A PRECEDING ITEM ON THE SAME LINE DOES NOT DONATE ITS DOCS.  Rustdoc
    # attaches the attribute to `documented` alone, so `undocumented` publishes
    # nothing.  Token-preserving: the heading is present, on the wrong item.
    ("a foreign fn inheriting the previous item's doc on one line", False, """
unsafe extern "C" { #[doc = "# Safety\\nreal contract"] fn documented(); fn undocumented(); }
"""),
    # ...and the BLOCK rule is the opposite, deliberately: a block is evaluated
    # inside the statement it sits in, so a binding prefix is not something that
    # executed in between — Rust's convention, and clippy's, puts the comment
    # above that statement.  `uart.rs::with_guard` is the live instance.
    ("a `let` binding prefix does not break a block's run", True, """
fn f() {
    // SAFETY: `acquire` established exclusive access for the guard's lifetime.
    let inner = unsafe { &mut *PTR.0.get() };
    drop(inner);
}
"""),
    # ...while a COMPLETED statement on the site's own line does break it.
    ("a completed statement on the site's own line breaks the run", False, """
fn f() {
    // SAFETY: pinned by the caller.
    let x = compute(); unsafe { g(x) }
}
"""),
    # **An attribute is one item, not one line** (PR #895 review round 8).  The
    # upward walk met the closing `))]` first and stopped below the docs, so a
    # correctly written declaration was reported unjustified — Tier 0 refusing
    # valid Rust.  Token-preserving against the single-line case below: the same
    # docs, the same attribute, written across lines.
    ("a multi-line attribute does not break a declaration's run", True, """
/// # Safety
/// The caller must hold the entry lock.
#[cfg(all(
    target_arch = "aarch64",
))]
pub unsafe fn documented() {}
"""),
    ("...and the single-line spelling still justifies", True, """
/// # Safety
/// The caller must hold the entry lock.
#[cfg(target_arch = "aarch64")]
pub unsafe fn documented() {}
"""),
    # ...while a multi-line EXPRESSION ending in `]` is code, and extending the
    # run across it would carry a justification over something that executes.
    # Same shape as the attribute above, and the opposite verdict.
    ("a multi-line expression ending in `]` still breaks the run", False, """
fn f() {
    // SAFETY: pinned by the caller.
    let v = compute(&[
        1, 2, 3,
    ]);
    unsafe { g(v) }
}
"""),
    # **A heading marker needs whitespace** (PR #895 review round 8).  CommonMark
    # renders `#Safety` as a paragraph, so rustdoc publishes no section and the
    # caller is told nothing — the fail-OPEN direction.  Token-preserving against
    # the accepted cases: the `#`, the word and the `///` all stay.
    ("`#Safety` without whitespace publishes no section", False, """
/// #Safety
/// The caller must hold the entry lock.
pub unsafe fn undocumented() {}
"""),
    ("...and the doc-attribute spelling is held to the same rule", False, """
#[doc = "#Safety"]
#[doc = "The caller must hold the entry lock."]
pub unsafe fn undocumented() {}
"""),
    ("...and so is a doc BLOCK", False, """
/** #Safety
 * The caller must hold the entry lock.
 */
pub unsafe fn undocumented() {}
"""),
    # A `static` in a foreign block declares no function, so it must NOT be
    # refused — the direction that keeps the refusal below from firing on
    # correct input.  Token-preserving against the macro case: same block, same
    # documented neighbour, one item swapped for another form.
    ("a `static` in an extern block is skipped, not refused", True, """
unsafe extern "C" {
    static COUNTER: u32;
    /// # Safety
    /// The caller must hold the entry lock.
    fn documented();
}
"""),
    # --- PR #895 review round 9 ------------------------------------------
    # **A raw identifier is not the keyword**, at the SITE scan this time.  The
    # rule had been on `UNSAFE_KEYWORD` since `v0.35.17` and on the view's
    # `extern` scan since `v0.35.21`; six sibling patterns in this file were
    # written without it, so Tier 0 demanded a justification of safe Rust.
    # Token-preserving against the justified block above: the keyword letters
    # and the brace both survive, only `r#` is added.
    ("a raw identifier is not an unsafe block", True, """
struct r#unsafe { x: u32 }
"""),
    ("a raw-identifier literal is not an unsafe block", True, """
fn f() { let _ = r#unsafe { x: 0 }; }
"""),
    # **The line that ends the run may still carry OUR documentation.**  A `///`
    # attaches to the item that follows, so the comment after a scope opener
    # documents the first item inside it.  The mirror case -- documentation
    # sitting BEFORE an intervening item -- is round 6's, two cases below, and
    # both hold at once because the distinction is the last code character's
    # offset.
    ("rustdoc after a scope opener documents the item inside", True, """
pub mod m { /// # Safety
    /// The caller must hold the entry lock.
    pub unsafe fn f() {}
}
"""),
    ("rustdoc after a closing brace documents the next item", True, """
fn a() {} /// # Safety
/// The caller must hold the entry lock.
pub unsafe fn f() {}
"""),
    # **A spelling is not the text.**  In a RAW literal `\\n` is two characters
    # and starts no line, so rustdoc publishes no heading.  Token-preserving
    # against the accepted escaped form below: every character of `# Safety` is
    # present and only the `r` prefix differs.
    ("a raw doc literal publishes no heading from a literal backslash-n",
     False, r'''
#[doc = r"not a heading\n# Safety"]
pub unsafe fn f() {}
'''),
    ("an escaped newline in an ordinary doc literal does publish one",
     True, '''
#[doc = "intro\\n# Safety\\nThe caller must hold the entry lock."]
pub unsafe fn f() {}
'''),
    ("a raw doc literal with a real newline publishes one", True, '''
#[doc = r"
# Safety
The caller must hold the entry lock."]
pub unsafe fn f() {}
'''),
    # **The marker is `SAFETY:`.**  A comment DISCLAIMING the obligation
    # satisfied a word-boundary test -- the fail-OPEN direction, and a presence
    # check standing in for the contract.  Token-preserving: the word `SAFETY`
    # and the comment marker both stay, only the colon goes.
    ("a comment disclaiming safety is not a justification", False, """
fn f() {
    // SAFETY is not established for this call.
    unsafe { g() }
}
"""),
    ("a block comment disclaiming safety is not a justification", False, """
fn f() {
    /* SAFETY unknown */
    unsafe { g() }
}
"""),
    # --- PR #895 review round 10 -----------------------------------------
    # **The view you read depends on the question.**  The run is raw because
    # what matters is what a reviewer reads -- right for READING a comment,
    # wrong for DECIDING whether something is one.  Both halves are
    # token-preserving against the accepted cases: every character of the
    # marker and of `# Safety` survives, only its enclosure changes.
    ("a commented-out doc attribute publishes nothing", False, """
// #[doc = "# Safety"]
pub unsafe fn f() {}
"""),
    ("a safety marker inside an attribute string is a string", False, """
fn f() {
    #[allow(unused, reason = "// SAFETY: not a comment")]
    let _ = unsafe { g() };
}
"""),
    ("...while a real comment beside that attribute still counts", True, """
fn f() {
    #[allow(unused, reason = "x")]
    // SAFETY: the pointer is valid for the lifetime of the call.
    let _ = unsafe { g() };
}
"""),
    # **A macro-valued doc attribute is decided, not skipped.**  `concat!` of
    # string literals is what rustdoc renders, so it is expanded; a form this
    # scanner cannot evaluate is REFUSED by name (the `_REFUSED_DOC_CASES`
    # below), because "undocumented" and "unreadable" are different claims.
    ("a concat! doc attribute publishes its heading", True, """
#[doc = concat!("# Safety\\n", "The caller must hold the entry lock.")]
pub unsafe fn f() {}
"""),
    ("a concat! doc attribute with no heading does not", False, """
#[doc = concat!("intro ", "text")]
pub unsafe fn f() {}
"""),
]


#: Foreign-block items this gate must REFUSE rather than read past, each with the
#: word its failure must name.  A separate list because the assertion differs:
#: these cases have no site to judge — the point is that the gate stops instead
#: of reporting a clean count over input it never examined.
#: `#[doc = …]` values this gate must REFUSE rather than report as missing
#: documentation.  "Undocumented" and "unreadable" are different claims, and
#: only one of them is true of a declaration whose section this scanner simply
#: cannot evaluate (PR #895 review round 10).
_REFUSED_DOC_CASES = [
    ("an include_str! doc attribute is refused, not called undocumented",
     "include_str", '#[doc = include_str!("safety.md")]\npub unsafe fn f() {}\n'),
    ("a user-macro doc attribute is refused", "mydoc",
     '#[doc = mydoc!(x)]\npub unsafe fn f() {}\n'),
    ("a concat! with a non-literal argument is refused", "concat",
     '#[doc = concat!("# Safety", SUFFIX)]\npub unsafe fn f() {}\n'),
]

_REFUSED_EXTERN_CASES = [
    # THE SHAPE (PR #895 review round 7): a macro expands to declarations no
    # `fn`-shaped search can see, so the site never existed and the empty
    # baseline stayed green.  Token-preserving against the `static` case above:
    # the block, the documented neighbour and the `;` are unchanged.
    ("an item macro in an extern block is refused", "macro", """
macro_rules! declare_it { () => { fn undocumented(); } }
unsafe extern "C" {
    declare_it!();
}
"""),
    # ...and the default branch beneath it: a form the shared view does not
    # know is refused too, which is round 25's rule rather than one case of it.
    ("an unknown item form in an extern block is refused", "unknown", """
unsafe extern "C" {
    const THING: u32;
}
"""),
    # An unbalanced block: the extent cannot be determined, so the items cannot
    # be enumerated at all.  This used to raise an exception nothing caught.
    ("an unbalanced extern block is refused", "unbalanced", """
unsafe extern "C" {
    fn documented();
"""),
    # ...and the shared VIEW's own refusal, which reached the gate as a
    # traceback rather than as a refusal until PR #895 review round 11: a file
    # the lexer cannot finish is exactly the input the "one failure channel"
    # exists for, and `UnterminatedLiteral` was in neither handler.  Found by
    # the form matrix, whose `commented-out` enclosure leaves a real one.
    ("a source with an unterminated literal is refused", "unterminated", """
// #[doc = r"
# Safety
The caller must hold the entry lock."]
pub unsafe fn f() {}
"""),
]


#: **What the site inventory IS, with multiplicity** — the shape a "every site is
#: justified" case cannot assert.
#:
#: `_CASES` above asks whether each site found carries a justification, so a
#: declaration reported TWICE with a good justification passes both rows and the
#: harness prints two `OK`s.  That is a cardinality defect, and the rule this
#: project states for it is that a set of keys and a count are different claims:
#: here the claim is *this fixture has exactly these declaration sites*, so the
#: expectation is the sorted list of names and a repeat is a failure.
#:
#: Round 22's finding is the first entry: inside an `unsafe extern` block a
#: declaration may mark itself `unsafe` (RFC 3484's per-item marker, whose `safe`
#: opt-out this gate already reads), and both the keyword pass and the
#: foreign-item pass then yielded it.  The mutation for it is token-preserving in
#: the way this class demands — the marker stays and only the region assignment
#: moves — and the two controls below it keep the fix known to NARROW rather than
#: to disable, since dropping the foreign interior from the keyword pass must not
#: cost the unmarked declaration or the ordinary `unsafe fn` outside a block.
_SITE_INVENTORY_CASES = [
    ("an explicitly-`unsafe` foreign declaration is ONE site", """
unsafe extern "C" {
    /// # Safety
    /// Documented.
    unsafe fn explicit();
}
""", ["explicit"]),
    ("...and so is an unmarked one, in the same block", """
unsafe extern "C" {
    /// # Safety
    /// Documented.
    unsafe fn explicit();
    /// # Safety
    /// Documented.
    fn implicit();
    safe fn opted_out();
}
""", ["explicit", "implicit"]),
    ("an `unsafe fn` OUTSIDE a foreign block is still a site", """
/// # Safety
/// Documented.
pub unsafe fn standalone() {}
""", ["standalone"]),
    ("...and a block inside a fn body is keyed by that fn, once", """
fn holder() {
    // SAFETY: documented.
    unsafe { f() }
}
""", ["holder"]),
]


#: **The justification predicates, as a cross-product of forms rather than a
#: list of cases** (PR #895 review round 11).
#:
#: Three rounds running, the witnesses here were drawn from the *findings* —
#: each round added cases for exactly the defect reported plus a control or
#: two, and the next round supplied a spelling nobody had enumerated: a raw
#: doc literal, a `#[unsafe(…)]` attribute, a scope opener, a `*`-decorated
#: block comment, attribute-shaped text inside a string.  That is this
#: project's own *a recognised set is not a derived set*, applied to its own
#: test cases.
#:
#: So the space is enumerated instead.  Every MARKER form crossed with every
#: ENCLOSURE, and the expected verdict is a property of the enclosure alone:
#: a real comment justifies, and a literal or a commented-out spelling never
#: does.  A spelling this gate has not considered is then a missing ROW —
#: visible, and addable without waiting for a review round to supply it.
#:
#: `rust/` is the authority for which marker forms occur; the enclosures are
#: the ways Rust lets the same bytes mean something else.
_BLOCK_MARKER_FORMS = {
    "line": "// SAFETY: the pointer is valid for the lifetime of the call.",
    "doc-line": "/// SAFETY: the pointer is valid for the lifetime of the call.",
    "inner-doc-line": "//! SAFETY: the pointer is valid for the lifetime of the call.",
    "block-one-line": "/* SAFETY: the pointer is valid. */",
    "block-decorated": "/*\n * SAFETY: the pointer is valid.\n */",
    "block-undecorated": "/*\nSAFETY: the pointer is valid.\n*/",
    "spaced-colon": "// SAFETY : the pointer is valid.",
}

#: How a marker can be *enclosed*, and whether that enclosure publishes it.
#: `{}` is the marker form.  A justification must be something the compiler
#: discards; anything a compiler keeps is data.
_BLOCK_ENCLOSURES = {
    "bare": ("{}", True),
    "in-attribute-string": ('#[allow(unused, reason = "{}")]', False),
    "in-raw-attribute-string": ('#[allow(unused, reason = r##"{}"##)]', False),
    "in-let-binding-string": ('let _m = "{}";', False),
}

#: The declaration side: every way a `# Safety` section can be spelled, crossed
#: with the enclosures that decide whether rustdoc publishes it.
_DECL_SECTION_FORMS = {
    "triple-slash": "/// # Safety\n/// The caller must hold the entry lock.",
    "doc-block": "/** # Safety\n * The caller must hold the entry lock.\n */",
    "attr-escaped": '#[doc = "# Safety\\nThe caller must hold the entry lock."]',
    "attr-raw-real-newline": '#[doc = r"\n# Safety\nThe caller must hold the entry lock."]',
    "attr-concat": '#[doc = concat!("# Safety\\n", "The caller must hold the entry lock.")]',
    # Rust treats a comment as whitespace BETWEEN TOKENS, so this is one
    # attribute (PR #895 review round 12).  Seven scanners required a literal
    # `#[`; they compose `rust_code_view.ATTRIBUTE_OPEN` now.
    "attr-comment-punctuated":
        '#/* why */[doc = "# Safety\\nThe caller must hold the entry lock."]',
}

#: The enclosure tables are deliberately the SAME shape on both sides.  They
#: were not: the declaration side omitted the plain string-literal enclosures
#: the block side had carried since round 10, which is this project's
#: *a recognised set is not a derived set* applied to the test matrix itself —
#: and it hid a live fail-OPEN cell, a `///` at the start of a line *inside* a
#: string literal satisfying the line-anchored `///` scan.
_DECL_ENCLOSURES = {
    "bare": ("{}", True),
    "commented-out": ("// {}", False),
    "inner-doc": ("#![doc = \"# Safety\"]\n// {}", False),
    "in-attribute-string": ('#[allow(unused, reason = r##"{}"##)]', False),
    "in-let-binding-string": ('let _m = r##"\n{}"##;', False),
}

#: **The markdown dimension** (PR #895 review round 12).
#:
#: A `# Safety` line inside a fenced code block renders as literal text, so the
#: declaration publishes no caller-facing section — and all three of this gate's
#: former line patterns accepted it.  This is not an ENCLOSURE in the sense of
#: the table above: a fence has to be written in the doc form's own syntax, so
#: it crosses the forms rather than composing with them, and each row carries
#: its own control in which the fence is CLOSED before the heading.  The
#: control is the half that decides: a gate that rejected every fenced document
#: by rejecting every document with a fence in it would pass the first column
#: and fail nobody's real documentation.
_DOC_MARKDOWN_FORMS = {
    "line-fenced": ("/// ```text\n/// # Safety\n/// ```", False),
    "line-fence-closed": ("/// ```\n/// let x = 1;\n/// ```\n/// # Safety\n/// text", True),
    "block-fenced": ("/** ```text\n * # Safety\n * ```\n */", False),
    "block-fence-closed": ("/** ```\n * let x = 1;\n * ```\n * # Safety\n * text\n */", True),
    "attr-fenced": ('#[doc = "```text\\n# Safety\\ntext"]', False),
    "attr-fence-closed": ('#[doc = "```\\nlet x = 1;\\n```\\n# Safety\\ntext"]', True),
    # rustdoc concatenates every doc source on an item into ONE markdown input,
    # so a fence opened in one source encloses the next.  Three independent
    # per-form scans structurally could not see this.
    "cross-form-fence": ('/// ```text\n#[doc = "# Safety"]\n/// ```', False),
    # ...and the same pair with the fence closed, so the row above is known to
    # fail on the ENCLOSURE rather than on the concatenation.
    "cross-form-closed": ('/// ```\n/// x\n/// ```\n#[doc = "# Safety"]', True),
    "tilde-fenced": ("/// ~~~\n/// # Safety\n/// ~~~", False),
    # A backtick run does not close a tilde fence, and vice versa.
    "mismatched-fence": ("/// ~~~\n/// ```\n/// # Safety\n/// ```", False),
    "indented-code": ("/// text\n///\n///     # Safety\n", False),
    # **The HTML-block enclosure** (PR #895 review round 13).  A fence is not
    # the only thing in the rendered document that suppresses heading parsing:
    # CommonMark 4.6 HTML blocks hold RAW TEXT, so rustdoc publishes no heading
    # for anything written inside one.  `<!-- ... -->` was the reported form;
    # the rows below are the grammar's own types, because taking the axis from
    # the finding is what round 11 already paid for.  Each hidden row is paired
    # with a control that ENDS the block, so the row is known to fail on the
    # enclosure rather than on the marker.
    "html-comment": ("/// <!--\n/// # Safety\n/// -->", False),
    "html-comment-closed": ("/// <!-- note -->\n/// # Safety\n/// text", True),
    # An unterminated HTML block runs to the end of the document, so the
    # heading is still never published — the state is carried, not reset.
    "html-comment-unterminated": ("/// <!--\n/// # Safety", False),
    "html-raw-text": ("/// <script>\n/// # Safety\n/// </script>", False),
    "html-raw-text-closed": ("/// <script>x</script>\n/// # Safety\n/// text", True),
    "html-cdata": ("/// <![CDATA[\n/// # Safety\n/// ]]>", False),
    "html-processing": ("/// <?x\n/// # Safety\n/// ?>", False),
    # A type-4 declaration ends on its own line, so the heading after it IS
    # published — the fail-CLOSED direction has a row too.
    "html-declaration-ends": ("/// <!DOCTYPE html>\n/// # Safety\n/// text", True),
    # Types 6 and 7 end at a BLANK line rather than at a string.
    "html-block-tag": ("/// <div>\n/// # Safety\n/// </div>", False),
    "html-block-tag-closed": ("/// <div>\n/// </div>\n///\n/// # Safety\n/// text", True),
    "html-complete-tag": ("/// <custom-tag>\n/// # Safety", False),
    "html-complete-tag-closed": ("/// <custom-tag>\n///\n/// # Safety\n/// text", True),
    # ...and type 7 alone may not interrupt a paragraph, so a complete tag
    # after text opens nothing and the heading below it is published.
    "html-complete-tag-in-paragraph":
        ("/// text\n/// <custom-tag>\n/// # Safety\n/// more", True),
    # The enclosure crosses doc forms, exactly as a fence does.
    "html-cross-form": ('/// <!--\n#[doc = "# Safety"]\n/// -->', False),
    # **The heading FORM axis** (PR #895 review round 14).  CommonMark has two
    # heading syntaxes and this gate knew one, so a declaration documented the
    # Setext way was refused though rustdoc had published its `<h2 id="safety">`
    # — the fail-CLOSED direction, which round 6 recorded as a defect too.  The
    # rows below are that axis at all of its values, each accepting row paired
    # with a control that changes only what the underline titles or what
    # encloses it.
    "setext-equals": ("/// Safety\n/// ======\n/// text", True),
    "setext-dashes": ("/// Safety\n/// ------\n/// text", True),
    # Both authorities reject this: clippy compares the heading's text to an
    # accepted title, and rustdoc renders `id="safety-requirements"`.  The `True`
    # here was written under the superseded `\bSafety\b` prefix match, which is
    # the round-17 finding in its Setext form.
    "setext-trailing-words": ("/// Safety Requirements\n/// ===\n/// text", False),
    # The underline titles the line above it, so a different line is a
    # different heading.
    "setext-titles-other-text": ("/// Notes\n/// =====\n/// text", False),
    # After a blank line a `-` run is a thematic break, not an underline.
    "setext-needs-a-paragraph": ("/// text\n///\n/// ---\n/// Safety", False),
    # ...and every enclosure that hides an ATX heading hides a Setext one.
    "setext-fenced": ("/// ```\n/// Safety\n/// ======\n/// ```", False),
    "setext-html-block": ("/// <!--\n/// Safety\n/// ======\n/// -->", False),
    "setext-indented-code": ("/// text\n///\n///     Safety\n///     ======", False),
    # **A Setext heading's content is the WHOLE paragraph** (CommonMark 4.3,
    # PR #895 review round 15).  Reading only the line above the underline made
    # the first row below accept a heading rustdoc titles "This is not a
    # contract Safety" -- fail-OPEN.  The second is its control: it keeps a
    # multi-line paragraph and moves `Safety` to the front, where the heading
    # really does begin with it, as `# Safety Requirements` does for ATX.  The
    # pair decides in both directions, since the superseded code answers each
    # of them the other way round.
    #
    # **Round 17 measured both against the real tools, and they disagree.**
    # `cargo doc` renders `id="this-is-not-a-contractsafety"` and
    # `id="safetyand-more-text"`: NEITHER multi-line form publishes a Safety
    # section.  `clippy::missing_safety_doc` accepts both, because it compares
    # each Text event of the heading rather than the heading's text -- so on
    # this shape the lint is the LENIENT one.  The gate follows rustdoc, which
    # is what a caller actually reads, so `safety-first` flips to False: round
    # 15 was right about the rendering and its control's expectation was set by
    # the first-line rule it had just introduced rather than by measurement.
    # This is *a proxy is not the fact* with the proxy on the other side.
    "setext-multiline-paragraph":
        ("/// This is not a contract\n/// Safety\n/// ===", False),
    "setext-multiline-safety-first":
        ("/// Safety\n/// and more text\n/// ===", False),
    # A thematic break is a leaf block, so it ends the paragraph the underline
    # below it could otherwise have titled.
    "setext-after-thematic-break":
        ("/// Safety\n/// ***\n/// ===", False),
    # ...and so is an ATX heading -- in the other direction: the paragraph the
    # underline titles STARTS after it, so this one really is a Safety heading.
    "setext-after-atx-heading":
        ("/// # Overview\n/// Safety\n/// ===", True),
    # **A backtick fence's info string may not contain a backtick**
    # (CommonMark 4.5, PR #895 review round 16) -- so the first row opens no
    # fence and its heading IS published, where this gate read a fence and
    # refused correct documentation.  The asymmetry is the point, so the two
    # controls keep the backtick and change only what carries it: a real
    # backtick fence still hides a heading, and a TILDE fence carries no such
    # restriction and hides one even with a backtick in its info string.
    "fence-backtick-in-backtick-info":
        ("/// ```rust`x\n/// # Safety\n/// contract", True),
    "fence-backtick-plain-info":
        ("/// ```rust\n/// # Safety\n/// ```", False),
    "fence-tilde-allows-backtick-info":
        ("/// ~~~rust`x\n/// # Safety\n/// ~~~", False),
    # **The TITLE axis** (PR #895 review round 17).  Its values are not guessed:
    # a probe crate with one `pub unsafe fn` per spelling was compiled under the
    # workspace's own `clippy::missing_safety_doc`, and these rows are its
    # verdicts.  Matching case-insensitively on a word boundary accepted all
    # four of the rejected forms -- and clippy does not examine a PRIVATE
    # `unsafe fn` at all, so for those this scanner is the only enforcement.
    "title-exact-safety":        ("/// # Safety\n///\n/// contract", True),
    "title-upper-safety":        ("/// # SAFETY\n///\n/// contract", True),
    "title-implementation-lower": ("/// # Implementation safety\n///\n/// contract", True),
    "title-implementation-upper": ("/// # Implementation Safety\n///\n/// contract", True),
    "title-closing-hashes":      ("/// # Safety #\n///\n/// contract", True),
    "title-trailing-space":      ("/// # Safety   \n///\n/// contract", True),
    "title-two-spaces-after-hash": ("/// #  Safety\n///\n/// contract", True),
    "title-lower-safety":        ("/// # safety\n///\n/// contract", False),
    "title-mixed-case":          ("/// # SaFeTy\n///\n/// contract", False),
    "title-safety-requirements": ("/// # Safety Requirements\n///\n/// contract", False),
    "title-safety-colon":        ("/// # Safety:\n///\n/// contract", False),
    # ...and the Setext matcher composes the same alternation, so it carries the
    # same verdicts -- plus the single-line requirement a WHOLE-title match
    # implies, since a Setext heading's text is the paragraph concatenated.
    "setext-title-upper":        ("/// SAFETY\n/// ======", True),
    "setext-title-implementation": ("/// Implementation Safety\n/// ======", True),
    "setext-title-lower":        ("/// safety\n/// ======", False),
    "setext-title-requirements": ("/// Safety Requirements\n/// ======", False),
    # --- the INLINE-MARKUP axis (PR #895 review rounds 19 and 20) ---------
    # A heading's content is markup, and deciding what it RENDERS to is a
    # CommonMark question.  Round 19 measured the two authorities (rustdoc and
    # `clippy::missing_safety_doc`, 1.94.1) disagreeing in both directions and
    # stated the right rule -- no CommonMark implementation is available at
    # Tier 0, so the reader refuses every inline form it cannot render -- and
    # then implemented emphasis peeling and link-label extraction by hand.
    # Round 20 is that gap: `# ** Safety **` is INACTIVE emphasis (CommonMark
    # 6.2: a left-flanking run may not be followed by whitespace), which
    # rustdoc renders literally; and `# [Safety](url)junk)` renders
    # `Safetyjunk)`.  Both were read as a bare `Safety`.
    #
    # So the rule round 19 stated is now the rule the code implements, which is
    # also round 16's exit: **where the subject is code this project writes,
    # require a canonical spelling and refuse the rest.**  Measured before
    # taking it -- every Safety heading in this tree is already written plainly
    # (26 `/// # Safety`, 3 `/// ## Safety`, 3 `//! # Safety`, 2 `//! ## Safety`,
    # zero carrying inline markup), so the refusal costs the tree nothing and
    # makes the question decidable.  A contributor who wants emphasis in a
    # Safety heading is asked to drop it; a scanner that guesses at CommonMark
    # is how three consecutive rounds shipped a fail-open cell.
    #
    # Every row below is therefore a REFUSAL, and each is annotated with what
    # the two authorities do, because the refusals are not all the same kind:
    # some forms both authorities accept (the reader is deliberately stricter),
    # some only rustdoc accepts, and some neither does.
    # Both authorities accept these; the reader refuses them anyway, because
    # deciding them needs a renderer it does not have:
    "inline-strong-star":        ("/// # **Safety**\n///\n/// contract", False),
    "inline-strong-underscore":  ("/// # __Safety__\n///\n/// contract", False),
    "inline-emphasis-star":      ("/// # *Safety*\n///\n/// contract", False),
    "inline-emphasis-underscore": ("/// # _Safety_\n///\n/// contract", False),
    "inline-emphasis-nested":    ("/// # ***Safety***\n///\n/// contract", False),
    "inline-html-tag":           ("/// # <b>Safety</b>\n///\n/// contract", False),
    "inline-link-with-dest":     ("/// # [Safety](https://e.invalid)\n///\n/// contract", False),
    # rustdoc renders `Safety` and clippy REFUSES — accepting these would green
    # Tier 0 over a file `-D warnings` then rejects:
    "inline-code-span":          ("/// # `Safety`\n///\n/// contract", False),
    "inline-entity":             ("/// # &#83;afety\n///\n/// contract", False),
    "inline-partial-emphasis":   ("/// # **Saf**ety\n///\n/// contract", False),
    "inline-html-comment-split": ("/// # Saf<!-- c -->ety\n///\n/// contract", False),
    # clippy accepts and rustdoc renders `[Safety]` — a shortcut link, on which
    # rustdoc itself warns `broken_intra_doc_links`:
    "inline-link-shortcut":      ("/// # [Safety]\n///\n/// contract", False),
    # **Round 20's two P1 cells.**  Neither authority publishes a Safety
    # section for these, and round 19's hand-written reader read both as a
    # bare `Safety`.  They are the decisive rows: a reader that peels emphasis
    # or extracts a link label passes them, and one that requires the
    # canonical spelling cannot.
    "inline-inactive-emphasis":  ("/// # ** Safety **\n///\n/// contract", False),
    "inline-link-trailing-junk": ("/// # [Safety](https://e.invalid)junk)\n///\n/// contract", False),
    # ...and the controls that keep the refusal from being read as "headings
    # never publish": the canonical spelling still does, in both heading forms.
    "inline-plain-title-still-passes": ("/// # Safety\n///\n/// contract", True),
    "inline-strong-other-title": ("/// # **Danger**\n///\n/// contract", False),
    "inline-strong-requirements": ("/// # **Safety Requirements**\n///\n/// contract", False),
    "inline-setext-strong":      ("/// **Safety**\n/// ======", False),
    "inline-setext-plain-still-passes": ("/// Safety\n/// ======", True),
}

#: **The site-name dimension.**  A declaration whose name this scanner cannot
#: spell is not a site, so its obligation is never raised at all — and the
#: explicit default branch then fails the whole file, refusing a correctly
#: documented function.  Rust identifiers are UAX#31, not ASCII.
_SITE_NAME_FORMS = {
    "ascii": ("f", "f"),
    "raw-ident": ("r#unsafe", "unsafe"),
    "unicode-start": ("\u03bb", "\u03bb"),
    "unicode-continue": ("na\u00efve_read", "na\u00efve_read"),
}

#: Forms that are NOT markers however they are enclosed — the fail-open
#: direction's own row.  Kept in the matrix rather than beside it so the
#: negative space is enumerated too.
_NON_MARKERS = {
    "no-colon": "// SAFETY is not established for this call.",
    "no-colon-block": "/* SAFETY unknown */",
    "heading-no-space": "/// #Safety\n/// text",
}


def _self_test() -> int:
    import tempfile

    failures = 0
    for name, expect_ok, src in _CASES:
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "fixture.rs"
            p.write_text(src, encoding="utf-8")
            found = list(sites(p))
            has_site = bool(found)
            ok = all(justified(r, d) for _o, _n, r, d in found) if has_site else True
            # A case expecting rejection must HAVE a site; one that has none is
            # inert, and an inert case reads like coverage while asserting
            # nothing.
            if not expect_ok and not has_site:
                print(f"  SELF-TEST BROKEN: '{name}' found no unsafe site to judge")
                failures += 1
                continue
            if ok != expect_ok:
                verdict = "accepted" if ok else "rejected"
                want = "accepted" if expect_ok else "rejected"
                print(f"  SELF-TEST FAIL: '{name}' was {verdict}, want {want}")
                failures += 1
            else:
                print(f"  OK   self-test '{name}' ({'accept' if expect_ok else 'reject'})")
    # **The site inventory, with multiplicity.**  `_CASES` above judges each
    # site it is handed; nothing there notices a site handed over twice, which is
    # exactly round 22's defect.  These rows name the declarations a fixture must
    # produce, so a repeat fails.
    for name, src, expected in _SITE_INVENTORY_CASES:
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "fixture.rs"
            p.write_text(src, encoding="utf-8")
            got = sorted(decl for _o, decl, _r, _d in sites(p))
            if got != sorted(expected):
                print(f"  SELF-TEST FAIL: '{name}' site inventory {got}, "
                      f"want {sorted(expected)}")
                failures += 1
            else:
                print(f"  OK   self-test '{name}' (inventory)")
    # **The form matrix.**  Every marker form crossed with every enclosure, with
    # the verdict a property of the ENCLOSURE alone — a real comment justifies,
    # a literal never does.  A spelling this gate has not considered shows up as
    # a missing row rather than as the next review round's finding.
    matrix_failures = 0
    matrix_cells = 0

    def verdict(run: str, is_decl: bool) -> bool:
        """`justified`, with an unreadable run counting as REFUSED.

        A run the shared view cannot lex reaches the gate as a refusal rather
        than as a verdict (`main`'s one failure channel), so that is the answer
        the matrix must compare against: an expectation of `False` is satisfied
        by either kind of refusal, and an expectation of `True` is satisfied by
        neither.  Swallowing the exception silently would let a cell that CANNOT
        be decided read as a cell that was.
        """
        try:
            return justified(run, is_decl)
        except REFUSALS:
            return False
    for form_name, marker in _BLOCK_MARKER_FORMS.items():
        for enc_name, (shape, expected) in _BLOCK_ENCLOSURES.items():
            matrix_cells += 1
            run = shape.format(marker)
            got = verdict(run, False)
            if got != expected:
                print(f"  SELF-TEST FAIL: matrix block[{form_name}][{enc_name}]: "
                      f"got {got}, want {expected}")
                matrix_failures += 1
    for form_name, section in _DECL_SECTION_FORMS.items():
        for enc_name, (shape, expected) in _DECL_ENCLOSURES.items():
            matrix_cells += 1
            run = shape.format(section)
            got = verdict(run, True)
            if got != expected:
                print(f"  SELF-TEST FAIL: matrix decl[{form_name}][{enc_name}]: "
                      f"got {got}, want {expected}")
                matrix_failures += 1
    # The markdown dimension: each fenced row and its closed-fence control.
    for form_name, entry in _DOC_MARKDOWN_FORMS.items():
        run, expected = entry
        matrix_cells += 1
        got = verdict(run, True)
        if got != expected:
            print(f"  SELF-TEST FAIL: matrix markdown[{form_name}]: "
                  f"got {got}, want {expected}")
            matrix_failures += 1
    # The site-name dimension: the declaration must BE a site, under its own
    # name, and the file must carry no unrecognised form.
    for form_name, (spelling, expected_name) in _SITE_NAME_FORMS.items():
        matrix_cells += 1
        src = ("/// # Safety\n/// The caller must hold the entry lock.\n"
               f"pub unsafe fn {spelling}() {{}}\n")
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "fixture.rs"
            path.write_text(src, encoding="utf-8")
            found = list(sites(path))
            names = [decl for _off, decl, _run, is_decl in found if is_decl]
            unread = unrecognised_unsafe_forms(
                Path("fixture.rs"), rust_code_view.code_no_strings(src))
        if names != [expected_name] or unread:
            print(f"  SELF-TEST FAIL: matrix site-name[{form_name}]: "
                  f"sites {names}, want [{expected_name!r}]"
                  + (f"; unrecognised {unread}" if unread else ""))
            matrix_failures += 1
    for form_name, text in _NON_MARKERS.items():
        for kind, is_decl in (("block", False), ("decl", True)):
            matrix_cells += 1
            if verdict(text, is_decl):
                print(f"  SELF-TEST FAIL: matrix non-marker[{form_name}][{kind}] "
                      f"was accepted")
                matrix_failures += 1
    failures += matrix_failures
    if matrix_failures == 0:
        print(f"  OK   self-test 'form matrix' ({matrix_cells} cells)")

    # **The DOMAIN, on a synthetic tree.**  `compiled_rust_sources` reads the
    # real workspace, so nothing in the case lists above can exercise it -- and
    # round 10's fix to it was initially shipped with no witness at all, caught
    # by the mutation harness reporting MISSED.  A fix whose revert breaks
    # nothing is indistinguishable from no fix.
    with tempfile.TemporaryDirectory() as tmp:
        fake = Path(tmp)
        for rel in ("crate/src/lib.rs", "crate/src/target/aarch64.rs",
                    "crate/tests/it.rs", "crate/build.rs",
                    "target/debug/build/generated.rs"):
            f = fake / rel
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text("fn a() {}\n", encoding="utf-8")
        found = {str(q.relative_to(fake)) for q in compiled_rust_sources(fake)}
        domain_cases = [
            # A module under a nested directory named `target` is a SOURCE; only
            # the workspace build-output root is cargo's.  Testing every path
            # component dropped it, so an unjustified site there was absent from
            # the count, the inventory and the baseline alike.
            ("a nested src/target module is compiled, not build output",
             "crate/src/target/aarch64.rs" in found),
            ("cargo's build-output root is still excluded",
             not any(q.startswith("target/") for q in found)),
            # The round-3 finding, pinned in the same place so the two domains
            # cannot drift apart again.
            ("integration tests, build scripts and libs are all in scope",
             {"crate/src/lib.rs", "crate/tests/it.rs", "crate/build.rs"} <= found),
        ]
    for name, ok in domain_cases:
        if ok:
            print(f"  OK   self-test '{name}'")
        else:
            print(f"  SELF-TEST FAIL: domain '{name}'")
            failures += 1

    # The foreign-block refusals.  A gate that derives REQUIREMENTS must stop on
    # input it cannot read, and until round 7 this one enumerated `fn` and
    # examined nothing else in the block.
    for name, word, src in _REFUSED_DOC_CASES:
        try:
            declaration_documents_safety(src)
        except UnreadableDocAttribute as refusal:
            if word not in str(refusal):
                print(f"  SELF-TEST FAIL: '{name}' refused without naming {word!r}")
                failures += 1
            else:
                print(f"  OK   self-test '{name}' (refuse)")
        else:
            print(f"  SELF-TEST FAIL: '{name}' was read past — the gate would report "
                  f"a correctly documented declaration as undocumented")
            failures += 1
    for name, word, src in _REFUSED_EXTERN_CASES:
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "fixture.rs"
            p.write_text(src, encoding="utf-8")
            try:
                list(sites(p))
            except REFUSALS as refusal:
                if word not in str(refusal):
                    print(f"  SELF-TEST FAIL: '{name}' refused without naming {word!r}: "
                          f"{refusal}")
                    failures += 1
                else:
                    print(f"  OK   self-test '{name}' (refuse)")
            else:
                print(f"  SELF-TEST FAIL: '{name}' was read past — the gate reported a "
                      f"clean count over an item it never examined")
                failures += 1
    # The unrecognised-form scan, which had no coverage: it is the gate's
    # fail-CLOSED default branch, and a default branch nothing exercises is a
    # decision nobody checked.
    form_cases = [
        # A raw identifier NAMES an item `unsafe`; Rust accepts the declaration
        # and the call, and neither is an unsafe operation.
        ("a raw identifier `r#unsafe` is not an unsafe form", """
fn r#unsafe() {}
fn caller() { r#unsafe(); }
""", True),
        # ...while a genuine form with no decision must still stop the gate.
        ("`unsafe auto trait` has no decision and is refused", """
unsafe auto trait Wild {}
""", False),
        ("a plain `unsafe` block is a recognised form", """
fn f() { unsafe { g() } }
""", True),
        # A template's metavariable name is a declaration form (the v0.36.2
        # audit): the gate used to refuse the file, which is fail-closed but is
        # not a decision.
        ("a macro template's `unsafe extern \"C\" fn $name` is a declaration form", """
macro_rules! exports {
    ($($name:ident;)+) => {$(
        /// # Safety
        ///
        /// The caller passes a live object.
        pub unsafe extern "C" fn $name(o: Obj) {}
    )+};
}
""", True),
        # **Rust 2024's unsafe ATTRIBUTE is a form, not an unknown**
        # (PR #895 review round 9).  The keyword scan found the token, no entry
        # accepted the position, and the gate failed the whole file -- the
        # explicit default branch firing on the only spelling a 2024 crate may
        # use for these attributes.
        #
        # These belong here rather than among the site cases, and that is this
        # round's own lesson about witnesses: a file whose only `unsafe` is an
        # attribute produces NO sites, so a site case asserting "everything is
        # justified" passes vacuously whether the classification exists or not.
        # The first version of this witness was exactly that, and the mutation
        # harness caught it by NOT failing.
        ("an outer unsafe attribute is a recognised form", """
#[unsafe(no_mangle)]
pub extern "C" fn exported() {}
""", True),
        ("an inner unsafe attribute is a recognised form", """
#![unsafe(no_mangle)]
""", True),
        ("a whitespace-separated unsafe attribute is a recognised form", """
#[ unsafe(export_name = "x") ]
pub extern "C" fn exported() {}
""", True),
    ]
    for name, src, want_clean in form_cases:
        found = unrecognised_unsafe_forms(Path("fixture.rs"), src)
        if (not found) != want_clean:
            print(f"  SELF-TEST FAIL: form scan '{name}'")
            failures += 1
        else:
            print(f"  OK   self-test '{name}'")
    # The reconciliation, on synthetic inventories.
    checks = [
        ("a clean tree passes", reconcile({"a|f": 1}, {"a|f": 1}), True),
        ("a NEW key fails", reconcile({"a|f": 1, "b|g": 1}, {"a|f": 1}), False),
        ("a GROWN key fails", reconcile({"a|f": 2}, {"a|f": 1}), False),
        ("a key that fell passes", reconcile({"a|f": 1}, {"a|f": 2}), True),
        ("a key gone to zero is reported stale", reconcile({}, {"a|f": 1}), False),
        ("empty and empty agree", reconcile({}, {}), True),
    ]
    for name, problems, want_clean in checks:
        if (not problems) != want_clean:
            print(f"  SELF-TEST FAIL: reconciliation '{name}'")
            failures += 1
        else:
            print(f"  OK   self-test '{name}'")
    if failures:
        print(f"unsafe-justification gate self-test FAILED ({failures})")
        return 1
    print(f"unsafe-justification gate self-test passed "
          f"({len(_CASES)} site cases, {len(_SITE_INVENTORY_CASES)} inventory "
          f"cases, {len(form_cases)} form-scan cases, "
          f"{len(checks)} reconciliation cases).")
    return 0


def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        return _self_test()
    inventory, total, cited, declarations, unreadable = census(REPO / "rust")
    if unreadable:
        # Fail CLOSED: a spelling Rust accepts and this gate does not is a gate
        # defect, and it must say so rather than quietly checking less.
        for u in unreadable:
            print(f"FAIL: {u}", file=sys.stderr)
        print("      Add the form to UNSAFE_KNOWN_FORMS with a decision for it.",
              file=sys.stderr)
        return 1
    if "--rows" in argv:
        for key, count in sorted(inventory.items()):
            print(f"UNJUSTIFIED_UNSAFE_SITE={key}|{count}")
        print(f"UNSAFE_SITES_TOTAL={total}")
        print(f"UNSAFE_SITES_UNJUSTIFIED={sum(inventory.values())}")
        print(f"UNSAFE_SITES_ARM_ARM_CITED={cited}  (diagnostic, not enforced)")
        print(f"UNSAFE_FN_DECLARATIONS={declarations}  (of the total; the rest are blocks)")
        return 0
    if "--update" in argv:
        BASELINE.write_text(json.dumps(inventory, indent=2, sort_keys=True) + "\n",
                            encoding="utf-8")
        print(f"re-anchored: {len(inventory)} key(s), "
              f"{sum(inventory.values())} unjustified site(s) of {total}")
        return 0
    if not BASELINE.exists():
        print(f"FAIL: baseline not found: {BASELINE.relative_to(REPO)}", file=sys.stderr)
        print("      create it with --update", file=sys.stderr)
        return 1
    baseline = json.loads(BASELINE.read_text(encoding="utf-8"))
    problems = reconcile(inventory, baseline)
    if problems:
        for p in problems:
            print(f"FAIL: {p}", file=sys.stderr)
        return 1
    justified = total - sum(inventory.values())
    print(f"PASS: {justified}/{total} unsafe sites carry the justification their kind calls "
          f"for — a `// SAFETY:` comment above each of the {total - declarations} block(s), a "
          f"`# Safety` doc section on each of the {declarations} `unsafe fn` declaration(s); "
          f"{sum(inventory.values())} pinned at or below the floor across {len(baseline)} "
          f"key(s).  {cited}/{total} also cite the ARM ARM (diagnostic).")
    # The claim, beside the number.  `136/136` reads as "every unsafe site in
    # the crates"; what this gate can say is "every site it recognises".  The
    # recognised forms are enumerated in UNSAFE_KNOWN_FORMS and anything else
    # stops the gate, so the gap is bounded and visible -- but it is a gap, and
    # the line says so rather than letting the ratio imply otherwise.
    print(f"      scope: the forms in UNSAFE_KNOWN_FORMS ({len(UNSAFE_KNOWN_FORMS)} of them); "
          f"an `unsafe` matching none of them fails this gate rather than being skipped.")
    # **And this gate is no longer the authority for most of what it counts.**
    # `sele4n-hal` and `sele4n-abi` deny `clippy::undocumented_unsafe_blocks` and
    # `clippy::missing_safety_doc` at their crate roots, so an unjustified block
    # and an undocumented public `unsafe fn` are refused by rustc's own parser
    # and by rustdoc's own markdown renderer -- in the host lane and, for the
    # `#[cfg(target_arch = "aarch64")]` majority of the HAL, in the cross lane.
    # This scanner runs in Tier 0, before any build, so it stays as the fast
    # approximation AND as the only check over the residue the lints structurally
    # cannot reach.  Saying which is which is the point: a number that implies an
    # authority it does not have is the defect this whole file keeps recording.
    print("      authority: rustc (`clippy::undocumented_unsafe_blocks`) and rustdoc "
          "(`clippy::missing_safety_doc`), denied at the `sele4n-hal` / `sele4n-abi` "
          "crate roots and run with `-D warnings` on both the host and "
          "`aarch64-unknown-none-softfloat` lanes.")
    print("      heading verdict: a CANONICAL SPELLING — the heading's content must "
          "BE one of " + ", ".join(sorted(SAFETY_HEADING_TITLES)) + ", and every "
          "inline form is refused rather than rendered.  Deciding what markup "
          "renders to is a CommonMark question and no implementation is available "
          "at Tier 0; the two authorities disagree in both directions on it besides "
          "(clippy refuses a code span, an entity and a split title that rustdoc "
          "renders; rustdoc renders `[Safety]` for a shortcut link clippy accepts). "
          "Measured: every Safety heading in this tree is already written plainly, "
          "so the refusal costs it nothing.")
    print("      residue owned here alone: a non-`pub` `unsafe fn`, an `unsafe fn` "
          "declared inside an `extern` block, and the ARM ARM citation census — "
          "no lint requires a contract of a foreign declaration.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
