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

UNSAFE_SITE = re.compile(
    r"\bunsafe\s*\{"                                         # a block
    r"|\bunsafe\s+(?:extern\s+" + ABI + r"\s+)?fn\s+(?:r#)?[A-Za-z_]"  # a declaration
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
    (re.compile(r"\bunsafe\s*\{"), "block"),
    (re.compile(r"\bunsafe\s+(?:extern\s+" + ABI + r"\s+)?fn\s+(?:r#)?[A-Za-z_]"),
     "declaration"),
    # `unsafe impl` / `unsafe trait` are not operations: they assert a trait
    # contract, which carries its own review story and no per-site obligation.
    (re.compile(r"\bunsafe\s+(?:impl|trait)\b"), "trait contract"),
    # Rust 2024's `unsafe extern { … }` block header.  The items inside are
    # declarations and are matched as such; the header itself performs nothing.
    (re.compile(r"\bunsafe\s+extern\s*(?:" + ABI + r"\s*)?\{"), "extern block header"),
    # A function-pointer TYPE — `unsafe fn(u8, T) -> R`, which
    # `tests::register_signature_pinned` uses to pin an ABI.  A type performs
    # nothing, so demanding a justification of one is a scanner matching a
    # keyword rather than asking about an operation.
    (re.compile(r"\bunsafe\s+(?:extern\s+" + ABI + r"\s+)?fn\s*\("), "function-pointer type"),
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
UNSAFE_KEYWORD = re.compile(r"(?<!r#)\bunsafe\b")


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
SAFETY_BLOCK = re.compile(r"//[/!]?\s*SAFETY\b|/\*+\s*SAFETY\b", re.IGNORECASE)
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
SAFETY_DECL_LINE = re.compile(r"^\s*///(?!/)\s*#+\s*Safety\b", re.IGNORECASE | re.MULTILINE)
# **A heading begins a line.**  `[^"]*` let arbitrary text precede the `#`, so
# `#[doc = "This function has no # Safety section."]` satisfied the pattern while
# Markdown renders that fragment as ordinary prose — an `unsafe fn` passed
# publishing no caller-facing section at all (PR #895 review round 5).  The `#`
# must open the attribute's value or follow an escaped newline, which is how a
# heading is spelled in a single-line doc attribute.
SAFETY_DECL_ATTR = re.compile(
    r"#\[\s*doc\s*=\s*(?:r#*)?\"(?:[^\"]*\\n)?\s*#+\s*Safety\b",
    re.IGNORECASE)
DOC_BLOCK_OPEN = re.compile(r"/\*\*(?![*/])")
DOC_BLOCK_LINE = re.compile(r"^\s*\*?\s*#+\s*Safety\b", re.IGNORECASE | re.MULTILINE)


def _split_block_comments(run: str) -> tuple[str, list[str]]:
    """`(run with every block comment blanked, the TOP-LEVEL doc-block bodies)`.

    **Rust block comments nest, and a marker nested inside one publishes
    nothing.**  `/* … /** # Safety … */ … */` is a single ordinary comment as
    far as rustdoc is concerned, so the declaration below it exposes no
    caller-facing contract — yet scanning the run for `/**` anywhere treated the
    inner marker as an independently attached doc block and accepted the
    `unsafe fn` (PR #895 review round 6).

    One walk settles the same relation for the siblings, which is this
    project's sweep rule rather than an extra: `SAFETY_DECL_LINE` and
    `SAFETY_DECL_ATTR` are `re.MULTILINE` searches over the whole run, so a
    `///` line or a `#[doc = …]` attribute *spelled inside* an ordinary block
    comment matched them too.  Blanking every block comment's extent — newlines
    kept, so line-anchored patterns keep their geometry — leaves exactly the
    markers that are really attached to the item, and the doc blocks are
    returned separately because their bodies genuinely are published.

    Deliberately not applied to `SAFETY_BLOCK`: a `// SAFETY:` comment is for
    the reviewer reading this file, who sees a nested one as readily as a
    top-level one.  The relation here is *rustdoc publication*, which is a
    property of declarations alone.
    """
    out: list[str] = []
    bodies: list[str] = []
    i, n = 0, len(run)
    while i < n:
        if run.startswith("/*", i):
            is_doc = DOC_BLOCK_OPEN.match(run, i) is not None
            depth, j = 1, i + 2
            while j < n and depth:
                if run.startswith("/*", j):
                    depth += 1
                    j += 2
                elif run.startswith("*/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            if is_doc:
                bodies.append(run[i + 3:(j - 2) if depth == 0 else n])
            out.append("".join(c if c == "\n" else " " for c in run[i:j]))
            i = j
        else:
            out.append(run[i])
            i += 1
    return "".join(out), bodies


def declaration_documents_safety(run: str) -> bool:
    """Does this run publish a rustdoc `# Safety` section?"""
    attached, doc_bodies = _split_block_comments(run)
    if SAFETY_DECL_LINE.search(attached) or SAFETY_DECL_ATTR.search(attached):
        return True
    # A `# Safety` inside a doc *block* counts; inside an ordinary block comment
    # -- or nested inside any block comment at all -- it does not.
    return any(DOC_BLOCK_LINE.search(body) for body in doc_bodies)
ARM_ARM = re.compile(r"\(ARM ARM [A-Z][0-9]+(?:\.[0-9]+)*\)")


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
    return bool(SAFETY_BLOCK.search(run))


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
    while rest.startswith("#[") or rest.startswith("#!["):
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
            word = re.search(r"([A-Za-z_][A-Za-z0-9_]*)\s*$", view[line_start:k])
            if depth == 0 and word and word.group(1) == "pub":
                end = line_start + word.start(1)
                continue
        word = re.search(r"([A-Za-z_][A-Za-z0-9_]*)\s*$", view[line_start:end])
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


def justification_run(raw: str, view: str, at: int, is_declaration: bool) -> str:
    """The contiguous comment-and-attribute run immediately above `at`.

    Walks upward line by line while each line is blank in the code view (a
    whole-line comment), is blank outright, or is an attribute, and stops at the
    first line carrying code.  Returns the RAW text of that run — the question is
    what a reviewer reads, so the answer comes from the real file.
    """
    line_start = raw.rfind("\n", 0, at) + 1
    # A trailing comment on the site's own line counts: `unsafe { … } // SAFETY: …`
    # does not, but `// SAFETY: …` before it on the same line does — provided
    # nothing executes in between, which is what the trim below establishes.
    prefix, prefix_has_code = _same_line_prefix(raw, view, line_start, at, is_declaration)
    run = [prefix]
    if prefix_has_code:
        return prefix
    idx = line_start
    while idx > 0:
        prev_end = idx - 1
        prev_start = raw.rfind("\n", 0, prev_end) + 1
        raw_line = raw[prev_start:prev_end]
        view_line = view[prev_start:prev_end]
        stripped_code = view_line.strip()
        stripped_raw = raw_line.strip()
        is_comment_only = stripped_raw != "" and stripped_code == ""
        is_attribute = ((stripped_code.startswith("#[") or stripped_code.startswith("#!["))
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
        break
    return "\n".join(reversed(run))


UNSAFE_FN_NAME = re.compile(
    r"\bunsafe\s+(?:extern\s+" + ABI + r"\s+)?fn\s+(?:r#)?(?P<name>[A-Za-z_][A-Za-z0-9_]*)")


#: A foreign function item inside a foreign block, and the `safe` opt-out.
FOREIGN_FN = re.compile(
    r"(?P<safe>\bsafe\s+)?\bfn\s+(?:r#)?(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*\(")


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


def sites(path: Path):
    """Yield (offset, enclosing declaration, justification run) per unsafe site.

    An `unsafe fn` DECLARATION is keyed by its own name, not by the scope it sits
    in: its `unsafe` token is outside every function body, so keying it by the
    enclosing scope would collapse every `unsafe fn` of a file onto one key — a
    cardinality one level up, which cannot see one declaration gaining a site
    while another gives one up.
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
    for m in UNSAFE_SITE.finditer(view):
        named = UNSAFE_FN_NAME.match(view, m.start())
        if named:
            decl = named.group("name")
        else:
            decl = rust_code_view.enclosing_fn(raw, m.start(), bodies) or "<module scope>"
        yield (m.start(), decl, justification_run(raw, aligned, m.start(), named is not None),
               named is not None)
    # Foreign function declarations, which carry no `unsafe` token of their own.
    for offset, name in foreign_fn_items(view):
        yield (offset, name, justification_run(raw, aligned, offset, True), True)


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
    """
    return [
        path
        for path in sorted(root.rglob("*.rs"))
        if "target" not in path.relative_to(root).parts
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
        unreadable += unrecognised_unsafe_forms(
            path.relative_to(REPO), rust_code_view.code_no_strings(
                path.read_text(encoding="utf-8")))
        try:
            file_sites = list(sites(path))
        except (UnreadableExternItem, rust_code_view.UnbalancedExternBlock) as refusal:
            # One failure channel, so a refusal reads like every other gate
            # defect instead of leaving a traceback.  `UnreadableExternBlock`
            # used to be raised and caught nowhere at all.
            unreadable.append(f"{rel}: {refusal}")
            continue
        for _off, decl, run, is_decl in file_sites:
            total += 1
            if is_decl:
                declarations += 1
            if ARM_ARM.search(run):
                cited += 1
            if not justified(run, is_decl):
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
]

#: Foreign-block items this gate must REFUSE rather than read past, each with the
#: word its failure must name.  A separate list because the assertion differs:
#: these cases have no site to judge — the point is that the gate stops instead
#: of reporting a clean count over input it never examined.
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
]


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
    # The foreign-block refusals.  A gate that derives REQUIREMENTS must stop on
    # input it cannot read, and until round 7 this one enumerated `fn` and
    # examined nothing else in the block.
    for name, word, src in _REFUSED_EXTERN_CASES:
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "fixture.rs"
            p.write_text(src, encoding="utf-8")
            try:
                list(sites(p))
            except (UnreadableExternItem, rust_code_view.UnbalancedExternBlock) as refusal:
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
          f"({len(_CASES)} site cases, {len(form_cases)} form-scan cases, "
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
    # The claim, beside the number.  `125/125` reads as "every unsafe site in
    # the crates"; what this gate can say is "every site it recognises".  The
    # recognised forms are enumerated in UNSAFE_KNOWN_FORMS and anything else
    # stops the gate, so the gap is bounded and visible -- but it is a gap, and
    # the line says so rather than letting the ratio imply otherwise.
    print(f"      scope: the forms in UNSAFE_KNOWN_FORMS ({len(UNSAFE_KNOWN_FORMS)} of them); "
          f"an `unsafe` matching none of them fails this gate rather than being skipped.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
