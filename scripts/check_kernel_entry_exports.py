#!/usr/bin/env python3
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
"""WS-RR RR5.16 — every Lean kernel entry the HAL links against is present in
the built static archive.

**What this closes.**  `rust/sele4n-hal/src/kernel_entry.rs` tabulates the Lean
entries that commit kernel state and every one of them is declared in Rust as a
hard `extern "C"` symbol.  Whether such a symbol *exists* is decided by
`SeLe4n.lean`'s import closure: Lake builds one `[[lean_lib]]` whose closure is
the transitive imports of that file, and an `@[export]` in a module outside it
emits nothing.  Before RR5.15 three of the entries lived in staged-only modules,
so `lake build SeLe4n:static` produced an archive with exactly one `T lean_*`
entry symbol and a linked image would have failed to resolve the other three —
on the seams every secondary core needs.

Nothing detected that.  The staged/production partition gate reports which
modules are staged, not which symbols a linked image would carry; a Tier-3 text
anchor on the `@[export]` line is satisfied by a module nothing imports.  This
gate asks the question of the **object code**: build the library a kernel image
links and read its symbol table.

**The required set is derived, not listed — and it is one-sided on purpose.**
Every symbol the HAL declares inside an `extern "C" { … }` block is a symbol
the linker must resolve, so every one of them is required to be defined by
*something*: the built Lean archive (the `@[export]`s), the HAL's own assembly
(`.global` directives in its `.S` sources), or — reconciled below — a provider
that does not exist yet.  A sixth seam declared by the HAL joins the
requirement automatically, and a hand-written table could not see the seam
that does not exist yet — the mistake this gate exists to avoid making again.

**Why not the intersection of the two sides** (PR #889 review): the first cut
required `exports ∩ externs`, which discards exactly the mismatches a link
would fail on.  Rename a HAL declaration while its Lean `@[export]` keeps the
old name — or the reverse — and *neither* spelling is in the intersection; as
long as one other entry still intersects, the requirement is non-empty and the
gate passes while the eventual image has an unresolved symbol.  Requiring
every HAL declaration instead catches a rename on either side, because the
HAL's spelling is then unresolved.  What the Lean side exports beyond what the
HAL declares is not a link requirement and is not checked here.

**Expected-unresolved symbols are reconciled, not exempted.**  `lean_kernel_main`
is declared by the HAL and provided by nobody until SM10.1 writes the primary's
boot install.  It is listed in `EXPECTED_UNRESOLVED` with its reason, and the
list is held in both directions: a listed symbol the HAL no longer declares, or
one the archive now defines, fails the gate — a stale entry is the exemption
that outlived its reason.

**What this gate does *not* decide, since PR #889 review round 17.**  Whether
the boot entry boots through the checked platform boot, what its failure path
does, and whether anything else installs kernel state are questions about
*elaboration*: which declaration a name denotes, what an expression evaluates,
which values a pattern matches.  This file answered them by matching Lean
source with regular expressions from round 3 to round 16, and every review
round found the same defect wearing different clothes — a name is not a
definition, a nested construct is not a sibling, a prefix is not the
expression, a constructor's head is not its coverage.  The set of Lean
spellings that defeat a regular expression is not finite, so the answer was to
stop asking Lean questions this way: `SeLe4n/Testing/BootEntryContract.lean`
asks the elaborated `Environment` instead, where references are resolved
constants, and fails its own elaboration.

What stays here is the part no elaboration can see: object code, `nm` output,
Rust `extern` declarations, assembly sources, and the Lean **source** inventory
of `@[export]`s — deliberately the source, because a module *outside* the
import closure exports nothing into the environment and is exactly the drift
this gate exists to catch.  That inventory is lexical because the question is
lexical; it is not a stand-in for the elaborator.

Exits 77 (the project's NOT-RUN code) when `nm` is unavailable, so a missing
binutils cannot be scored as a pass.
"""

from __future__ import annotations

import ast
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import NamedTuple

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lean_code_view  # noqa: E402  (the Lean code view; strings blanked on request)
import rust_code_view  # noqa: E402  (comments blanked, string contents kept)
import check_aarch64_cross_target as cross_gate  # noqa: E402  (the live builder chain)

SKIP_EXIT = 77
REPO = Path(__file__).resolve().parent.parent
LEAN_ROOT = REPO / "SeLe4n"
HAL_SRC = REPO / "rust" / "sele4n-hal" / "src"
BUILD_RS = REPO / "rust" / "sele4n-hal" / "build.rs"
# The assembled HAL archive a cross build leaves behind (`cc::Build::compile`).
ASM_ARCHIVE_GLOB = "rust/target/aarch64-unknown-none/*/build/sele4n-hal-*/out/libsele4n_hal_asm.a"
ASM_COMPILE_CALL = '.compile("sele4n_hal_asm")'
# A preprocessor conditional: `.S` sources pass through cpp before the assembler.
CPP_CONDITIONAL_OPEN = re.compile(r"^\s*#\s*(?:if|ifdef|ifndef)\b", re.MULTILINE)
CPP_CONDITIONAL_CLOSE = re.compile(r"^\s*#\s*endif\b", re.MULTILINE)
ARCHIVE = REPO / ".lake" / "build" / "lib" / "libseLe4n_SeLe4n.a"

#: HAL `extern "C"` declarations that no provider defines **yet**, with the
#: reason.  Reconciled in both directions by `classify_link_requirements`: an
#: entry the HAL no longer declares, or one the archive now defines, fails.
EXPECTED_UNRESOLVED: dict[str, str] = {
    "lean_kernel_main": (
        "the primary's boot install; SM10.1 provides it — no `@[export lean_kernel_main]` "
        "exists yet, and the HAL's declaration is the seam waiting for it"
    ),
}

#: The `extern` keyword.  Whether it *opens a block* is decided structurally
#: by `extern_block_openings`, not by a spelling: PR #889 review round 17 found
#: this searched for the literal `extern "C" {`, so `extern r"C" { … }` — which
#: compiles, and declares exactly the same symbols — declared nothing as far as
#: this gate could see, and `extern { … }` (ABI `"C"` by default) and
#: `extern "C-unwind" { … }` were invisible the same way.  The ABI names a
#: calling convention; every `extern` block asks the linker for its items
#: whatever the convention is, so the requirement does not depend on it.
EXTERN_KEYWORD = re.compile(r"\bextern\b")
#: A foreign function declaration.  `r#` is Rust's raw-identifier escape and
#: names the *same* linker symbol as the bare spelling — `fn r#lean_real();`
#: asks for `lean_real` (PR #889 review round 25).  Without the prefix this
#: matched nothing, `extern_declarations_in` skipped the item, and the
#: requirement silently did not exist: a HAL seam written that way could
#: disappear from the derived link requirements and Tier 1 would pass with no
#: provider.
EXTERN_FN = re.compile(r"\bfn\s+(?:r#)?([A-Za-z_][A-Za-z0-9_]*)\s*\(")
#: An item a foreign block may hold that declares no *function* symbol: a
#: `static` (a data object — the archive parsers reject those as function
#: providers anyway), a type alias, or a `use`.  Anything in a block that is
#: none of these and not a `fn` is refused rather than skipped (round 25).
EXTERN_NON_FN_ITEM = re.compile(r"\b(?:static|type|use)\b")
#: The symbol SM10.1's boot entry exports.  Only the link-level reconciliation
#: reads it here — that the archive does not define it yet, and that
#: `EXPECTED_UNRESOLVED` still says so.  What the entry must *do* is
#: `SeLe4n/Testing/BootEntryContract.lean`'s, decided over the elaborated
#: environment (PR #889 review round 17).
BOOT_ENTRY_SYMBOL = "lean_kernel_main"
#: `#[link_name = "…"]` — in both spellings — on an `extern` declaration: the
#: symbol the linker is actually asked for, whatever the Rust item is called.
#: Matched over the string-free view, where the literal's delimiters survive
#: and its interior is blanked, so group 1's *span* locates the value and the
#: byte-aligned strings-kept view supplies its text.  The raw forms (`r"…"`,
#: `r#"…"#`) are literals too and name the same symbol.
LINK_NAME_ATTR = re.compile(
    r'#\[\s*(?:unsafe\s*\(\s*)?link_name\s*=\s*r?#*"([^"]*)"'
)
ASM_GLOBAL = re.compile(r"^\s*\.(?:global|globl)\s+([A-Za-z_.$][A-Za-z0-9_.$]*)", re.MULTILINE)
# The directives that open and close a region the assembler does not emit
# where it is written.  Derived from the directives' shape: every GAS
# conditional opener begins `.if`, every repeat block closes with `.endr`.
ASM_REGION_OPEN = re.compile(r"\.(?:macro|if[a-z]*|rept|irpc?)")
ASM_REGION_CLOSE = re.compile(r"\.(?:endm|endmacro|endif|endr)")
# Labels leading a line, so a directive sharing the line with one is still read.
ASM_LEADING_LABELS = re.compile(r"^\s*(?:[A-Za-z0-9_.$][A-Za-z0-9_.$]*\s*:\s*)+")
# A label definition: the symbol at the start of a line, followed by `:`.
ASM_LABEL = re.compile(r"^\s*([A-Za-z_.$][A-Za-z0-9_.$]*)\s*:", re.MULTILINE)
# A `cc::Build` source registration in `build.rs`, read over the comment-blanked
# view (string contents kept, since the path IS a string).
CC_FILE_CALL = re.compile(r'\.file\(\s*"([^"]+)"\s*\)')


def lean_exports_in_view(view: str) -> set[str]:
    """The `@[export …]` symbols of a Lean **code view**.

    PR #889 review round 12: read with the shared attribute-list parser, so a
    combined list (`@[inline, export lean_kernel_main]`) and a line break after
    the keyword count — both are what Lean emits, and both were invisible to
    the `@\[export\s+…\]` regex this replaces.  The consequences ran in the
    fail-open direction twice over: an export written that way was missing from
    the inventory, so the archive was never required to define it; and the boot
    entry carrying it was not recognised as the boot entry, so the check that
    the hardware boot goes through the checked platform boot passed vacuously.
    `build.rs` has split the list since round 2 — the two inventories now share
    one parser and cannot disagree again.
    """
    return set(lean_code_view.attribute_arguments(view, "export"))


def lean_exports_in(text: str) -> set[str]:
    """The `@[export …]` symbols of one Lean source, read over the shared code
    view with comments — nested block comments included — *and* string
    contents blanked (PR #889 review round 6): a docstring, a `/- … -/` inside
    another, or a string literal quoting the attribute is not a symbol."""
    return lean_exports_in_view(lean_code_view.code_no_strings(text))


LEAN_LIBRARY_ROOT_MODULE = REPO / "SeLe4n.lean"


def lean_sources() -> dict[str, str]:
    """Every Lean source the static library is built from: the tree under
    `SeLe4n/` **and the library root module `SeLe4n.lean`** (PR #889 review
    round 7 — the root compiles into `SeLe4n:static` like any other module, so
    an `@[export]` placed there is in the archive; walking the directory alone
    left it outside the export inventory and the boot-entry check)."""
    sources = {
        str(path.relative_to(REPO)): path.read_text() for path in sorted(LEAN_ROOT.rglob("*.lean"))
    }
    sources[str(LEAN_LIBRARY_ROOT_MODULE.relative_to(REPO))] = LEAN_LIBRARY_ROOT_MODULE.read_text()
    return sources


def extern_declarations_in(text: str, where: str) -> set[str]:
    """The **linker symbols** declared inside an `extern "C" { … }` block.

    Brace-matched rather than line-scanned: a declaration is a `fn` inside the
    block, and the block ends at its matching `}` — a `fn` *after* the block is
    a definition in the crate, not a symbol the crate expects to link against.
    Read over the shared Rust code view with string contents blanked (PR #889
    review round 6): a block quoted in a raw string or in a nested block
    comment declares nothing.

    PR #889 review round 12: the symbol is the **effective linker name**, not
    the Rust name.  `#[link_name = "actual_symbol"] fn local_name();` makes the
    linker demand `actual_symbol` and never `local_name`, so returning the Rust
    name got the requirement wrong in both directions at once — the archive was
    asked to define a symbol nothing references, and the symbol a link would
    actually fail on was not required of anybody.  The attribute's value lives
    in a string, so it is read off the strings-*kept* view at the same offsets:
    the two views are byte-aligned, which is what makes structure and text
    readable from one position.
    """
    view = rust_code_view.code_no_strings(text)
    kept = rust_code_view.code(text)
    if len(view) != len(kept):
        sys.exit(f"[FAIL] {where}: the Rust code views are not byte-aligned")
    found: set[str] = set()
    for _, brace_at in extern_block_openings(view):
        depth = 0
        end = None
        for index in range(brace_at, len(view)):
            if view[index] == "{":
                depth += 1
            elif view[index] == "}":
                depth -= 1
                if depth == 0:
                    end = index
                    break
        if end is None:
            sys.exit(f"[FAIL] {where}: unbalanced `extern` block")
        # PR #889 review round 16: split the block into **items** and read each
        # item's own attributes.  Advancing the attribute window only across
        # `fn` declarations let an intervening `static` donate its
        # `#[link_name]` to the next function — the attribute belongs to the
        # item it decorates, and an `extern` block holds statics and type
        # aliases as well as functions.
        for item_at, item_end in extern_block_items(view, brace_at + 1, end):
            declaration = EXTERN_FN.search(view, item_at, item_end)
            if declaration is None:
                # PR #889 review round 21: a foreign block may hold an **item
                # macro**, and Rust expands it into real declarations.
                # `extern "C" { decl!(); }` where `decl!` expands to
                # `fn lean_generated();` declares a symbol this scanner cannot
                # see, so the requirement would silently not exist and Tier 1
                # would pass with no provider.  Expanding Rust macros is out of
                # this scanner's scope and always will be, so the input is
                # refused rather than read past: the rule this file follows is
                # that where a scanner cannot decide, it fails closed.  The HAL
                # contains no such macro, so this costs nothing today and turns
                # the day one is added into a build failure with a reason.
                if MACRO_INVOCATION.search(view, item_at, item_end):
                    sys.exit(
                        f"[FAIL] {where}: a macro invocation inside an `extern` block "
                        f"({view[item_at:item_end].strip()[:60]!r}) expands to declarations "
                        f"this scanner cannot see.  Write the `fn` declarations out, or "
                        f"teach this gate to read the expansion."
                    )
                # PR #889 review round 25: round 21 refused *macros* and let
                # every other unrecognised item fall through to `continue`,
                # which is the fail-open direction — an item whose form this
                # scanner does not know declares no requirement and signals
                # nothing.  Only the items that genuinely declare no function
                # symbol may be skipped; anything else stops the build.  That
                # is round 21's own rule, applied to the default branch rather
                # than to one case of it.
                if not EXTERN_NON_FN_ITEM.search(view, item_at, item_end):
                    sys.exit(
                        f"[FAIL] {where}: an item inside an `extern` block "
                        f"({view[item_at:item_end].strip()[:60]!r}) is neither a `fn` this "
                        f"scanner can read nor a `static`/`type`/`use`.  If it declares a "
                        f"function symbol the link requirement is missing; teach this gate "
                        f"the form, or write the declaration out."
                    )
                continue  # a `static`, a type alias: not a function requirement
            # PR #889 review round 17: the attribute is **located** on the
            # string-free view and only its value read from the aligned kept
            # one — round 16 fixed exactly this at `halt_definitions` and left
            # its sibling here scanning the kept view, where
            # `#[doc = r#"#[link_name = "lean_kernel_main"]"#]` on an unrelated
            # declaration donated that symbol to it.  Text inside a literal is
            # data; what *is* an attribute is structure.
            renamed = [
                kept[found_at.start(1) : found_at.end(1)]
                for found_at in LINK_NAME_ATTR.finditer(view, item_at, declaration.start())
            ]
            found.add(renamed[-1] if renamed else declaration.group(1))
    return found


# PR #889 review round 21: an item macro inside a foreign block.  `name ! (`,
# `name ! [` or `name ! {` at item position — the three bracket forms Rust
# accepts for an invocation.  Matched on the string-free view, so a `!` inside
# a literal is not one.
MACRO_INVOCATION = re.compile(r"\b[A-Za-z_][A-Za-z0-9_]*\s*!\s*[(\[{]")


def extern_block_openings(view: str) -> list[tuple[int, int]]:
    """Every `extern <abi>? { … }` block in `view`, as `(keyword, brace)`
    offsets.

    Rust's grammar after `extern` is closed: `crate`, an optional ABI **string
    literal** then `fn`, or an optional ABI literal then `{`.  Only the last
    opens a block, and the ABI is a literal in any of its forms — `"C"`,
    `r"C"`, `r#"C"#` — naming any convention.  Resolving the literal is what
    makes the answer independent of how it is spelled (PR #889 review round
    17); the previous check searched for the eleven characters `extern "C" {`.
    """
    openings: list[tuple[int, int]] = []
    for keyword in EXTERN_KEYWORD.finditer(view):
        at = skip_rust_space(view, keyword.end())
        past = string_literal_end(view, at)
        if past is not None:
            at = skip_rust_space(view, past)
        if at < len(view) and view[at] == "{":
            openings.append((keyword.start(), at))
    return openings


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
    view an interior holds no `"` at all (it is blanked to spaces), and an ABI
    string is kept verbatim by `rust_code_view` because it is syntax; both read
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
    closer = '"' + "#" * hashes
    close = view.find(closer, index + 1)
    return None if close < 0 else close + len(closer)


def extern_block_items(view: str, start: int, end: int) -> list[tuple[int, int]]:
    """The `;`-terminated items of an `extern "C" { … }` block, as spans.

    Each span begins after the previous item's `;` — so it carries that item's
    own attributes — and ends at its own `;`.  Semicolons inside brackets
    (a `[u8; 4]` type) do not terminate an item.
    """
    items: list[tuple[int, int]] = []
    at = start
    depth = 0
    index = start
    while index < end:
        character = view[index]
        if character in "([{<":
            depth += 1
        elif character in ")]}>":
            depth = max(0, depth - 1)
        elif character == ";" and depth == 0:
            items.append((at, index))
            at = index + 1
        index += 1
    if view[at:end].strip():
        items.append((at, end))
    return items


def hal_extern_declarations() -> set[str]:
    found: set[str] = set()
    for path in sorted(HAL_SRC.rglob("*.rs")):
        found.update(extern_declarations_in(path.read_text(), str(path)))
    return found


def asm_code_view(text: str) -> str:
    """The assembly code view: `//` line comments, `/* … */` block comments
    (cpp's, which do not nest) and the contents of string literals blanked,
    length-preserving (PR #889 review round 6 — the regex pair it replaces
    read a `.global` inside a string or a comment as a definition).  `#`
    lines are preprocessor directives, not comments, and are kept for
    `strip_cpp_conditionals`."""
    out = list(text)
    n = len(text)
    i = 0

    def blank(j: int) -> None:
        if out[j] != "\n":
            out[j] = " "

    while i < n:
        c = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if c == "/" and nxt == "/":
            while i < n and text[i] != "\n":
                blank(i)
                i += 1
            continue
        if c == "/" and nxt == "*":
            close = text.find("*/", i + 2)
            end = n if close == -1 else close + 2
            for j in range(i, end):
                blank(j)
            i = end
            continue
        if c == '"':
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\" and i + 1 < n:
                    blank(i)
                    i += 1
                blank(i)
                i += 1
            i += 1
            continue
        i += 1
    return "".join(out)


def strip_cpp_conditionals(text: str) -> str:
    """Blank every preprocessor-conditional region of an assembly source,
    nesting-aware, keeping newlines.

    PR #889 review round 4: a `.S` source passes through cpp, so a `.global
    foo` and its `foo:` retained inside `#if 0 … #endif` define nothing for
    the image while a comment-stripped scan still read them.  This does not
    evaluate the conditions — a region under *any* conditional contributes
    nothing, which under-approximates the providers and so fails closed: a
    symbol that is in fact assembled under a true condition is reported as
    missing rather than a symbol that is not being reported as provided.
    """
    out: list[str] = []
    depth = 0
    for line in text.split("\n"):
        if CPP_CONDITIONAL_OPEN.match(line):
            depth += 1
            out.append("")
            continue
        if CPP_CONDITIONAL_CLOSE.match(line):
            depth = max(depth - 1, 0)
            out.append("")
            continue
        out.append("" if depth > 0 else line)
    return "\n".join(out)


# PR #889 review round 22: which section a label lands in.  `.text` and its
# named variants (`.section .text.foo`) hold code; `.data`, `.bss`, `.rodata`
# and their variants hold objects.
#
# PR #889 review round 25: directives are classified by **name first, operand
# second**, and every directive line is recognised as a directive.  The regex
# this replaces required the whole directive *and a readable operand* to match
# before it counted as a section change, so `.section ".data"` — whose operand
# the code view blanks, the quotes being a string literal — matched nothing at
# all and left the scanner in whatever section preceded it.  A directive whose
# name is section-changing but whose operand this scanner cannot read now
# leaves the section **unknown**, which is never executable.
ASM_DIRECTIVE = re.compile(
    r"^\s*\.(?P<directive>[A-Za-z_][A-Za-z0-9_]*)"
    r'(?:\s+"?(?P<operand>[A-Za-z0-9_.$-]+)"?)?'
)
# The shorthands whose own name is the section they select.
ASM_SECTION_SHORTHANDS = frozenset({"text", "data", "bss", "rodata"})
# Section-changing directives whose effect this scanner does not model: GAS's
# `.struct` and `.offset` switch to an absolute section.  `.subsection` is
# deliberately absent — it selects a subsection *of the current section*, so it
# cannot change whether labels after it land in code.
ASM_UNMODELLED_SECTION_CHANGE = frozenset({"struct", "offset"})
# AArch64 GAS separates statements with `;`, so one source line can hold a
# section change and the labels that follow it.  Comments and string contents
# are already blanked by `asm_code_view`, so no `;` here is quoted or commented.
ASM_STATEMENT_SEPARATOR = ";"


def asm_statements(view: str) -> list[str]:
    """The assembler statements of a code view, in source order.

    AArch64 GAS separates statements with `;`, so one source line can hold
    several and a line-per-statement reading loses their order — which is the
    whole content of a section scan.  Comments and string literal contents are
    already blanked by `asm_code_view`, so no separator reaching here is quoted
    or commented out.  Both halves of `asm_definitions_in` read this, since a
    provider is the conjunction of a directive and a label and the two must
    agree on what a statement is.

    A preprocessor line is the exception and is never split: cpp runs a stage
    earlier, so `#define ENTRY(x) .text; .global x; x:` is a template whose
    symbols exist where it is *invoked*, not where it is written.
    """
    statements: list[str] = []
    for line in view.split("\n"):
        # A preprocessor line is not a list of assembler statements.  cpp runs
        # a stage earlier and a `#define ENTRY(x) .text; .global x; x:` is a
        # *template*: its directives and its label exist where the macro is
        # invoked, under whatever name the argument supplies.  Splitting it
        # would set the section from a body that never executes there and
        # register the parameter `x` as a provider — the `.macro` hazard round
        # 16 closed, arriving through the statement split this round added.
        # Left whole, it matches neither the directive nor the label pattern,
        # so it contributes nothing: the fail-closed direction for providers.
        if line.lstrip().startswith("#"):
            statements.append(line)
            continue
        statements.extend(line.split(ASM_STATEMENT_SEPARATOR))
    return statements


def section_name_is_executable(name: str) -> bool:
    """Whether a section *name* holds code: `.text` and its named variants."""
    return name == "text" or name.startswith(".text") or name.startswith("text.")


def executable_label_names(view: str) -> set[str]:
    """The labels an assembly source defines **in executable sections**.

    PR #889 review round 22: `asm_definitions_in` paired `.global X` with a
    label `X:` and asked no more, so

        .section .data
        .global lean_data
        lean_data:

    satisfied an `extern "C" fn` requirement while `nm` classifies the emitted
    symbol `D` — a data object standing in for a missing Lean *function*, which
    the linker resolves and a call then enters as if it were code.  Round 8 had
    already made the archive path reject exactly this (`executable_definitions`
    keeps only global text symbols, `T`); the source fallback is the same
    question at a second site and was left asking less.

    PR #889 review round 25: the current section is not the operand of the last
    `.section`.  GAS keeps a **section stack** (`.pushsection` / `.popsection`)
    and a previous-section slot (`.previous`), so

        .text
        .pushsection .data
        .global lean_data
        lean_data:

    left round 22's scanner reporting `lean_data` as executable while the
    assembler emits `D`, which is the very substitution round 22 closed —
    reintroduced by a spelling it did not enumerate.  Section state is
    therefore modelled as GAS defines it: a current section, a previous
    section, and a stack.

    Executability is tracked as a three-valued fact — executable, not
    executable, or **unknown** — and only `executable` admits a label.  Unknown
    is what an unresolvable section change yields: an operand the code view
    blanked, an unbalanced `.popsection`, a directive whose name is
    section-changing but whose semantics this scanner does not model.  The
    fallback under-approximates the providers, so an unknown section reports a
    symbol as *missing* — the gate fails — rather than reporting a data object
    as a function.
    """
    executable: set[str] = set()
    # `None` is "unknown", which is never executable.  GAS starts in `.text`.
    current: bool | None = True
    previous: bool | None = True
    stack: list[bool | None] = []
    for statement in asm_statements(view):
        directive = ASM_DIRECTIVE.match(statement)
        if directive is not None:
            name = directive.group("directive")
            operand = directive.group("operand")
            if name in ASM_SECTION_SHORTHANDS:
                previous, current = current, section_name_is_executable(name)
                continue
            if name in ("section", "pushsection"):
                if name == "pushsection":
                    stack.append(current)
                resolved = (
                    None if operand is None else section_name_is_executable(operand)
                )
                previous, current = current, resolved
                continue
            if name == "popsection":
                # An unbalanced pop is a source this scanner cannot follow.
                restored = stack.pop() if stack else None
                previous, current = current, restored
                continue
            if name == "previous":
                previous, current = current, previous
                continue
            if name == "subsection":
                # Selects a subsection *of the current section*, so it cannot
                # change whether the labels after it land in code.  Named
                # before the catch-all below, whose shape it otherwise matches.
                continue
            if name.endswith("section") or name in ASM_UNMODELLED_SECTION_CHANGE:
                previous, current = current, None
                continue
        if current:
            label = ASM_LABEL.match(statement)
            if label is not None:
                executable.add(label.group(1))
    return executable


def asm_definitions_in(text: str) -> set[str]:
    """Symbols one assembly source **defines and exports** in code the
    preprocessor keeps: a `.global` / `.globl` directive *and* a label `X:` for
    the same name, both read over the comment-blanked view with every
    preprocessor-conditional region blanked (`strip_cpp_conditionals`).

    PR #889 review round 3: a `.global foo` alone declares binding and defines
    nothing — leave the directive and delete the label and the image still has
    an unresolved `foo`, so a directive-only scan passed exactly the
    token-preserving regression this gate exists to catch.  A provider is the
    conjunction, outside any conditional (round 4), **in an executable
    section** (round 22 — `executable_label_names`; every requirement this gate
    reconciles is an `extern "C" fn`, so a data object under the name resolves
    a call into data).
    """
    view = strip_unassembled_regions(strip_cpp_conditionals(asm_code_view(text)))
    exported = {
        match.group(1)
        for match in (ASM_GLOBAL.match(statement) for statement in asm_statements(view))
        if match is not None
    }
    return exported & executable_label_names(view)


def strip_unassembled_regions(text: str) -> str:
    """Blank every region of an assembly source whose directives and labels the
    assembler does **not** emit where they are written, keeping newlines.

    Three families, matched by the shape of their directives rather than by a
    list of the fifteen-odd spellings GAS accepts:

    * `.macro … .endm` — a template.  Its `.global` and its label exist only
      where the macro is *invoked* (PR #889 review round 16: a `.global
      lean_ghost` and `lean_ghost:` inside an uninvoked macro satisfied the
      provider conjunction while `nm` on the object showed no such symbol).
    * `.if… … .endif` — an assembler conditional.  Every GAS conditional opener
      begins `.if` (`.if`, `.ifdef`, `.ifnotdef`, `.ifeqs`, …), so the shape
      derives the family; the assembler evaluates the condition and this
      scanner cannot, so a region under any of them contributes nothing (PR
      #889 review round 17 — round 4 blanked cpp's `#if 0`, and `.if 0` is the
      assembler's own spelling of the same thing, one preprocessing stage
      later).
    * `.rept` / `.irp` / `.irpc` … `.endr` — a repeat block, whose body is
      emitted a computed number of times, possibly zero.

    All three under-approximate the providers, which is the fail-closed
    direction: a symbol really assembled through a macro invocation or a true
    conditional is reported as *missing* rather than a symbol that is not being
    reported as provided — and it must then show up in the assembled archive,
    which is the evidence this check prefers anyway.
    """
    out = list(text)
    depth = 0
    for match in re.finditer(r"^[^\n]*$", text, re.MULTILINE):
        line = match.group(0)
        token = assembler_directive(line)
        if ASM_REGION_OPEN.fullmatch(token):
            depth += 1
        if depth:
            for index in range(match.start(), match.end()):
                if out[index] != "\n":
                    out[index] = " "
        if ASM_REGION_CLOSE.fullmatch(token) and depth:
            depth -= 1
    return "".join(out)


def assembler_directive(line: str) -> str:
    """The directive an assembly line issues, `""` when it issues none.

    A label may share the line with the directive it precedes (`retry: .if 0`),
    so labels are consumed first — reading the *first* token would otherwise
    take `retry:` and miss the region opener, which keeps every token and
    breaks the relation.
    """
    text = ASM_LEADING_LABELS.sub("", line).strip()
    return text.split()[0] if text else ""


def assembled_sources_in(build_rs: str) -> set[str]:
    """The assembly sources `build.rs` hands to the assembler on the **live**
    builder chain: every `.file("…")` on the `cc::Build` receiver that
    `.compile("sele4n_hal_asm")` is called on, in a function reachable from
    `main` — the cross gate's own resolution (`chain_root`,
    `compiled_builder_name`, `reachable_from_main`), reused rather than
    re-derived.

    PR #889 review round 4: collecting every `.file("…")` token counted a
    source left on a probe builder, an uncompiled builder or an inactive
    branch as assembled; a file is assembled only by the builder that is
    compiled, and only if that builder's function runs.
    """
    code = rust_code_view.code(build_rs)
    structure = rust_code_view.code_no_strings(build_rs)
    bodies = rust_code_view.fn_bodies(build_rs)
    found: set[str] = set()
    for compile_at in cross_gate._occurrences(code, ASM_COMPILE_CALL):
        owner = rust_code_view.enclosing_fn(code, compile_at, bodies)
        if owner == rust_code_view.FILE_SCOPE or not cross_gate.reachable_from_main(code, owner):
            continue
        receiver = cross_gate.compiled_builder_name(code, compile_at)
        if receiver is None:
            continue
        # PR #889 review round 7: the `.file()` calls that reach the assembler
        # are the ones on the compiled builder's *executed* chain — top-level
        # statements of the compile's own function body, at or before the
        # statement holding the compile.  A `.file()` under `if false { … }`
        # in that function, or in another function whose local happens to
        # share the receiver's name, keeps the token and assembles nothing.
        body = innermost_body(bodies, compile_at)
        if body is None:
            continue
        body_start, body_end = body
        statements = rust_code_view.top_level_statements(structure, body_start, body_end)
        compile_statement = rust_code_view.statement_containing(statements, compile_at)
        if compile_statement is None:
            continue
        # PR #889 review rounds 8 and 9: the receiver's SPELLING does not
        # identify the builder.  `let mut asm = …; asm.file("ghost.S"); let
        # mut asm = …; asm.file("real.S").compile(…)` rebinds the name, and
        # the first `.file()` reaches a builder the compile never sees — a
        # symbol from `ghost.S` would then be subtracted as an assembly
        # provider and mask an unresolved HAL extern.  Round 9: a `mut`
        # receiver is rebound by **assignment** too (`asm = cc::Build::new();`),
        # with no second `let`.  So a `.file()` counts only from the
        # receiver's binding instance — the last top-level `let [mut]
        # <receiver>` **or** `<receiver> = …` before the compile statement
        # (`binding_statement_before`).  A receiver the block never binds —
        # a parameter, a captured variable — has no instance to resolve
        # against, and then only the compile statement's own chain counts
        # (fail closed).
        binding = rust_code_view.binding_statement_before(
            structure, statements, receiver, compile_statement
        )
        window_start = binding[0] if binding is not None else compile_statement[0]
        for lo, hi in statements:
            if lo > compile_statement[0] or lo < window_start:
                continue
            for pos in cross_gate._occurrences(code[lo:hi], ".file("):
                at = lo + pos
                if at >= compile_at or cross_gate.chain_root(code, at) != receiver:
                    continue
                # A `.file()` inside a block the statement opens — `if false
                # { asm.file(…); }` — is nested, not executed by the statement.
                if structure[lo:at].count("{") != structure[lo:at].count("}"):
                    continue
                m = CC_FILE_CALL.match(code, at)
                if m:
                    found.add(m.group(1))
    return found


def innermost_body(
    bodies: list[tuple[str, int, int]], offset: int
) -> tuple[int, int] | None:
    """The `(start, end)` of the innermost `fn` body containing `offset`."""
    best: tuple[int, int] | None = None
    for _, start, end in bodies:
        if start <= offset < end and (best is None or start > best[0]):
            best = (start, end)
    return best


def asm_providers_from(sources: dict[str, str], build_rs: str) -> set[str]:
    """The symbols the HAL's assembly provides to the link according to the
    **sources**: defined-and-exported (`asm_definitions_in`) in a source the
    live builder chain assembles (`assembled_sources_in`).  `sources` maps a
    `src/`-relative path to its text."""
    assembled = assembled_sources_in(build_rs)
    found: set[str] = set()
    for rel, text in sources.items():
        if rel in assembled:
            found |= asm_definitions_in(text)
    return found


def executable_definitions(nm_output: str) -> set[str]:
    """The **global text** symbols in `nm --defined-only` output — type letter
    `T` exactly.

    PR #889 review round 8: every requirement this gate reconciles is an
    `extern "C" fn` — `extern_declarations_in` collects `fn` declarations
    and nothing else — and a function requirement is satisfied only by
    executable code.  The earlier parsers accepted `D`/`B` (the archive) and
    any upper-case letter (the assembled archive), so a removed or renamed
    Lean export that left a global *data* object under the old linker name
    reported the function resolved while the call would have jumped into
    data.  `t` (local text) is refused too: a local symbol does not resolve a
    reference from another object, and the archive is read with `-g` anyway.
    The HAL's one non-function extern (`static __exception_vectors`, an
    address the vector-table install takes) is outside this inventory by
    construction; a data requirement is a different question and is not
    answered here.
    """
    found: set[str] = set()
    for line in nm_output.splitlines():
        parts = line.split()
        if len(parts) == 3 and parts[1] == "T":
            found.add(parts[2])
    return found


def assembled_archive() -> Path | None:
    """The newest assembled HAL archive a cross build left behind, if any."""
    candidates = sorted(REPO.glob(ASM_ARCHIVE_GLOB), key=lambda p: p.stat().st_mtime)
    return candidates[-1] if candidates else None


def archive_asm_definitions(archive: Path) -> set[str] | None:
    """The symbols the assembled archive defines, or `None` when `nm` cannot
    read it (no `nm`, or a format this `nm` does not know)."""
    if shutil.which("nm") is None:
        return None
    result = subprocess.run(
        ["nm", "--defined-only", str(archive)], capture_output=True, text=True, check=False
    )
    if result.returncode != 0:
        return None
    return executable_definitions(result.stdout)


def hal_asm_providers() -> tuple[set[str], str]:
    """The HAL's assembly providers, and how they were established.

    The source-derived set (`asm_providers_from`) is always computed.  When a
    cross build's assembled archive is present and readable, the providers are
    the **intersection** of the two — a symbol counts only if the current
    sources define it on the live chain *and* the assembled object code
    defines it (PR #889 review round 4: the object code is the authority on
    what was emitted, the sources on what this tree says; a stale archive
    could carry a symbol since deleted, and a source could carry one the
    assembler drops, so neither alone decides).  Without an archive the
    source-derived set stands, and the report says so.
    """
    sources = {
        path.relative_to(HAL_SRC.parent).as_posix(): path.read_text()
        for path in sorted(HAL_SRC.rglob("*.S"))
    }
    from_sources = asm_providers_from(sources, BUILD_RS.read_text())
    archive = assembled_archive()
    if archive is None:
        return from_sources, "sources on the live builder chain (no assembled archive present)"
    from_objects = archive_asm_definitions(archive)
    if from_objects is None:
        return from_sources, f"sources on the live builder chain (`nm` cannot read {archive})"
    return from_sources & from_objects, f"sources on the live builder chain ∩ {archive.relative_to(REPO)}"


def link_requirements(
    externs: set[str],
    asm_globals: set[str],
    expected_unresolved: dict[str, str],
    exports: set[str],
) -> list[str]:
    """The HAL declarations the archive must define: every `extern "C"` the
    HAL's own assembly does not provide, minus the expected-unresolved entries
    **whose export has not appeared** — an entry the Lean tree exports is a
    requirement again (PR #889 review round 6)."""
    live_exemptions = {s for s in expected_unresolved if s not in exports}
    return sorted(externs - asm_globals - live_exemptions)


def classify_link_requirements(
    externs: set[str],
    asm_globals: set[str],
    expected_unresolved: dict[str, str],
    defined: set[str],
    exports: set[str] = frozenset(),
) -> tuple[list[str], list[str], list[str], list[str]]:
    """Decide the gate from the five derived sets.

    Returns `(missing, stale_undeclared, stale_defined, stale_exported)`:

      * `missing` — HAL declarations no provider defines: not an assembly
        global, not a *live* expected-unresolved entry, and not in the
        archive.  A rename on either side of a kernel entry lands here,
        because the HAL's spelling is then unresolved.
      * `stale_undeclared` — expected-unresolved entries the HAL no longer
        declares (the exemption outlived the declaration).
      * `stale_defined` — expected-unresolved entries the archive now defines
        (the exemption outlived its reason and must be removed).
      * `stale_exported` — expected-unresolved entries the Lean tree now
        **exports** (PR #889 review round 6).  The exemption expires the
        moment the export appears, whether or not the archive defines it: an
        exported entry whose module sits outside `SeLe4n.lean`'s import
        closure is exported and undefined at once, and an exemption keyed on
        the archive alone reported that image as bound and resolved.  Such an
        entry is also a requirement (`link_requirements`), so it lands in
        `missing` too when the archive lacks it.

    All four must be empty for the gate to pass.
    """
    required = link_requirements(externs, asm_globals, expected_unresolved, exports)
    missing = [symbol for symbol in required if symbol not in defined]
    stale_undeclared = sorted(s for s in expected_unresolved if s not in externs)
    stale_defined = sorted(s for s in expected_unresolved if s in defined)
    stale_exported = sorted(s for s in expected_unresolved if s in exports)
    return missing, stale_undeclared, stale_defined, stale_exported


def self_test_case_count() -> int:
    """How many relations `self_test` asserts, **measured** from its own source.

    PR #889 review round 17.  The `[PASS]` line carried a literal that ten
    review rounds bumped by hand, and by round 16 it read one higher than the
    harness's real assertion count — a number maintained beside the thing it
    describes rather than derived from it, which is the shape this file's own
    scanners are held to.  An assertion is a `failures.append` or a
    `check_entry` call; a site inside a `for` over a literal sequence runs once
    per element, which is what makes a loop of token-preserving spellings count
    as the cases it really is.
    """
    tree = ast.parse(Path(__file__).read_text())
    harness = next(
        node for node in tree.body
        if isinstance(node, ast.FunctionDef) and node.name == "self_test"
    )

    def count(node: ast.AST, repeats: int) -> int:
        total = 0
        for child in ast.iter_child_nodes(node):
            inner = repeats
            if isinstance(child, ast.For) and isinstance(child.iter, (ast.Tuple, ast.List)):
                inner = repeats * len(child.iter.elts)
            if isinstance(child, ast.Call):
                called = child.func
                if (
                    isinstance(called, ast.Attribute)
                    and called.attr == "append"
                    and isinstance(called.value, ast.Name)
                    and called.value.id == "failures"
                ) or (isinstance(called, ast.Name) and called.id == "check_entry"):
                    total += inner
            total += count(child, inner)
        return total

    return count(harness, 1)


def self_test() -> int:
    """Token-preserving checks on the two derivations.

    Each case **keeps** the token a presence check would look for and breaks the
    relation: the `@[export]` is present but commented out; the `fn` is present
    but sits outside the `extern "C"` block that would make it a link
    requirement.  A scanner that grepped for the token would pass both.
    """
    failures: list[str] = []

    live_lean = "@[export lean_alpha]\ndef alpha : Nat := 0\n"
    if lean_exports_in(live_lean) != {"lean_alpha"}:
        failures.append("a live `@[export]` was not collected")

    commented_lean = "-- @[export lean_alpha]\ndef alpha : Nat := 0\n"
    if lean_exports_in(commented_lean):
        failures.append("a line-commented `@[export]` was collected as a symbol")

    block_commented_lean = "/- @[export lean_alpha] -/\ndef alpha : Nat := 0\n"
    if lean_exports_in(block_commented_lean):
        failures.append("a block-commented `@[export]` was collected as a symbol")
    # PR #889 review round 6: the token survives in a string literal and in a
    # comment nested inside another; neither is a symbol.
    string_lean = 'def doc : String := "@[export lean_alpha]"\ndef alpha : Nat := 0\n'
    if lean_exports_in(string_lean):
        failures.append("an `@[export]` inside a Lean string literal was collected as a symbol")
    nested_lean = "/- outer /- @[export lean_alpha] -/ still a comment -/\ndef alpha : Nat := 0\n"
    if lean_exports_in(nested_lean):
        failures.append("an `@[export]` inside a nested Lean block comment was collected")
    beside_string_lean = 'def doc : String := "-- not a comment"\n@[export lean_alpha]\ndef alpha : Nat := 0\n'
    if lean_exports_in(beside_string_lean) != {"lean_alpha"}:
        failures.append("a live `@[export]` after a string holding `--` was lost")

    live_rust = 'extern "C" {\n    fn lean_alpha(x: u64) -> u64;\n}\n'
    if extern_declarations_in(live_rust, "fixture") != {"lean_alpha"}:
        failures.append("a declaration inside an `extern \"C\"` block was not collected")

    outside_rust = 'extern "C" {\n    fn lean_beta(x: u64);\n}\nfn lean_alpha(x: u64) -> u64 { 0 }\n'
    collected = extern_declarations_in(outside_rust, "fixture")
    if "lean_alpha" in collected:
        failures.append(
            "a crate-local `fn` outside the block was collected as a link requirement"
        )
    if collected != {"lean_beta"}:
        failures.append("the in-block declaration was lost while excluding the outside one")

    # PR #889 review round 12: `#[link_name]` renames the symbol.  The Rust
    # name is present in every one of these and is never the requirement.
    renamed_rust = (
        'extern "C" {\n'
        '    #[link_name = "actual_symbol"]\n'
        '    fn local_name(x: u64) -> u64;\n'
        '}\n'
    )
    got = extern_declarations_in(renamed_rust, "fixture")
    if got != {"actual_symbol"}:
        failures.append(
            "`#[link_name]` was not honoured: the requirement was derived as "
            f"{sorted(got)} rather than the symbol the linker asks for"
        )
    renamed_unsafe_rust = (
        'extern "C" {\n'
        '    #[unsafe(link_name = "actual_symbol")]\n'
        '    fn local_name(x: u64) -> u64;\n'
        '}\n'
    )
    if extern_declarations_in(renamed_unsafe_rust, "fixture") != {"actual_symbol"}:
        failures.append("`#[unsafe(link_name = …)]` was not honoured")
    renamed_neighbour_rust = (
        'extern "C" {\n'
        '    #[link_name = "actual_symbol"]\n'
        '    fn local_name(x: u64) -> u64;\n'
        '    fn lean_beta(x: u64);\n'
        '}\n'
    )
    got = extern_declarations_in(renamed_neighbour_rust, "fixture")
    if got != {"actual_symbol", "lean_beta"}:
        failures.append(
            "an attribute leaked onto the following declaration or lost its own: "
            f"{sorted(got)}"
        )
    # PR #889 review round 16: an attribute decorates the item that FOLLOWS it,
    # and an `extern` block holds more than functions.  The Rust name and the
    # decoy string are both present in this fixture.
    renamed_static_rust = (
        'extern "C" {\n'
        '    #[link_name = "decoy_symbol"]\n'
        '    static X: u8;\n'
        '    fn lean_real(x: u64) -> u64;\n'
        '}\n'
    )
    got = extern_declarations_in(renamed_static_rust, "fixture")
    if got != {"lean_real"}:
        failures.append(
            "a `#[link_name]` on an intervening `static` was donated to the next function: "
            f"{sorted(got)} (round 16)"
        )
    # ...while the attribute on the function itself still renames it.
    renamed_fn_after_static_rust = (
        'extern "C" {\n'
        '    static X: u8;\n'
        '    #[link_name = "actual_symbol"]\n'
        '    fn lean_real(x: u64) -> u64;\n'
        '}\n'
    )
    if extern_declarations_in(renamed_fn_after_static_rust, "fixture") != {"actual_symbol"}:
        failures.append("an attribute on the function after a `static` was lost (round 16)")
    # PR #889 review round 22: a label in a data section is not a function
    # provider.  The mutation KEEPS the `.global` and the label — every token
    # the round-3 conjunction reads — and moves them into `.data`.
    data_label_asm = (
        "    .section .data\n"
        "    .global lean_data\n"
        "lean_data:\n"
        "    .quad 0\n"
        "    .text\n"
        "    .global lean_real\n"
        "lean_real:\n"
        "    ret\n"
    )
    got = asm_definitions_in(data_label_asm)
    if got != {"lean_real"}:
        failures.append(
            "a `.global` + label pair in `.data` was accepted as a function provider: "
            f"{sorted(got)} (round 22)"
        )
    # ...and a named text section still provides, so the check is a bound on
    # the section rather than a rejection of every directive it has not seen.
    named_text_asm = (
        "    .section .text.boot\n"
        "    .global lean_named\n"
        "lean_named:\n"
        "    ret\n"
    )
    if asm_definitions_in(named_text_asm) != {"lean_named"}:
        failures.append("a label in a named `.text.*` section was refused (round 22)")
    # ...and a source with no section directive at all is `.text` by default,
    # which is what GAS assumes and what every `.S` in this tree relies on.
    default_section_asm = "    .global lean_default\nlean_default:\n    ret\n"
    if asm_definitions_in(default_section_asm) != {"lean_default"}:
        failures.append("a label before any section directive was refused (round 22)")
    # PR #889 review round 25: the current section is not the last `.section`
    # operand.  Each mutation below KEEPS the `.text`, the `.global` and the
    # label — everything round 22's check reads — and changes only the section
    # *state* the assembler is in when the label is emitted.
    pushed_data_asm = (
        "    .text\n"
        "    .pushsection .data\n"
        "    .global lean_pushed\n"
        "lean_pushed:\n"
        "    .quad 0\n"
    )
    if asm_definitions_in(pushed_data_asm):
        failures.append(
            "a label under `.pushsection .data` was accepted as a function "
            "provider (round 25)"
        )
    # ...and the stack is tracked rather than refused wholesale: a balanced
    # push/pop puts the label back in `.text`, where it really does provide.
    popped_text_asm = (
        "    .text\n"
        "    .pushsection .data\n"
        "    .quad 0\n"
        "    .popsection\n"
        "    .global lean_popped\n"
        "lean_popped:\n"
        "    ret\n"
    )
    if asm_definitions_in(popped_text_asm) != {"lean_popped"}:
        failures.append("a label after a balanced `.popsection` was refused (round 25)")
    # ...as is `.previous`, which swaps the current section with the one before.
    previous_text_asm = (
        "    .text\n"
        "    .section .data\n"
        "    .quad 0\n"
        "    .previous\n"
        "    .global lean_previous\n"
        "lean_previous:\n"
        "    ret\n"
    )
    if asm_definitions_in(previous_text_asm) != {"lean_previous"}:
        failures.append("a label after `.previous` restored `.text` was refused (round 25)")
    # ...while a pop with nothing pushed is a source this scanner cannot
    # follow, so the section is unknown and the label provides nothing.
    unbalanced_pop_asm = (
        "    .text\n"
        "    .popsection\n"
        "    .global lean_unbalanced\n"
        "lean_unbalanced:\n"
        "    ret\n"
    )
    if asm_definitions_in(unbalanced_pop_asm):
        failures.append("a label after an unbalanced `.popsection` provided (round 25)")
    # ...as is a section whose name the code view blanks, the quotes making it
    # a string literal.  The mutation KEEPS `.section` and its operand and only
    # quotes it — which the regex this replaced failed to match at all, leaving
    # the scanner in the section that preceded it.
    quoted_section_asm = (
        "    .text\n"
        '    .section ".data"\n'
        "    .global lean_quoted\n"
        "lean_quoted:\n"
        "    .quad 0\n"
    )
    if asm_definitions_in(quoted_section_asm):
        failures.append(
            "a label under a quoted `.section` name was accepted as a function "
            "provider (round 25)"
        )
    # ...and an unmodelled section-changing directive is unknown, not ignored.
    unknown_section_asm = (
        "    .text\n"
        "    .foosection bar\n"
        "    .global lean_unknown\n"
        "lean_unknown:\n"
        "    ret\n"
    )
    if asm_definitions_in(unknown_section_asm):
        failures.append("a label after an unmodelled section change provided (round 25)")
    # ...while `.subsection`, whose shape matches that catch-all, changes the
    # subsection of the current section and so cannot change executability.
    subsection_asm = (
        "    .text\n"
        "    .subsection 2\n"
        "    .global lean_subsection\n"
        "lean_subsection:\n"
        "    ret\n"
    )
    if asm_definitions_in(subsection_asm) != {"lean_subsection"}:
        failures.append("a label after `.subsection` was refused (round 25)")
    # ...and AArch64 GAS separates statements with `;`, so a section change and
    # the labels it governs can share a line.  The mutation KEEPS every token
    # of the accepted form and only joins the lines.
    inline_pushed_asm = (
        "    .text; .pushsection .data; .global lean_inline; lean_inline:; .quad 0\n"
    )
    if asm_definitions_in(inline_pushed_asm):
        failures.append(
            "a `;`-separated `.pushsection .data` was read as `.text` (round 25)"
        )
    inline_text_asm = "    .text; .global lean_joined; lean_joined:; ret\n"
    if asm_definitions_in(inline_text_asm) != {"lean_joined"}:
        failures.append("a `;`-separated provider in `.text` was refused (round 25)")
    # ...but a preprocessor line is not a list of assembler statements.  cpp
    # runs a stage earlier, so a `#define` body is a template whose directives
    # and label exist where it is *invoked* — the `.macro` hazard round 16
    # closed, reachable again through the statement split this round added.
    # The mutation KEEPS every token of a real provider and puts it in a macro
    # definition, which declares nothing where it is written.
    cpp_macro_asm = (
        "#define ENTRY(x) .text; .global lean_templated; lean_templated:\n"
        "    .global lean_real\n"
        "lean_real:\n"
        "    ret\n"
    )
    got = asm_definitions_in(cpp_macro_asm)
    if "lean_templated" in got:
        failures.append(
            "a `.global`/label pair inside a `#define` body counted as an assembly "
            "provider (round 25)"
        )
    if "lean_real" not in got:
        failures.append(
            "a real provider beside a `#define` was lost to the statement split "
            "(round 25)"
        )
    # ...and a `#define` does not change the section either: its body never
    # executes where it is written, so a `.data` in one must not follow through
    # to the labels below it.
    cpp_section_asm = (
        "    .text\n"
        "#define SWITCH .section .data\n"
        "    .global lean_after\n"
        "lean_after:\n"
        "    ret\n"
    )
    if asm_definitions_in(cpp_section_asm) != {"lean_after"}:
        failures.append(
            "a section directive inside a `#define` body changed the section for the "
            "code below it (round 25)"
        )
    # PR #889 review round 21: an item macro inside a foreign block expands to
    # declarations this scanner cannot see, so it is refused rather than read
    # past.  The mutation KEEPS the block and the `extern "C"` and puts the
    # declaration behind a macro, which a `fn`-shaped search silently skips.
    macro_extern_rust = (
        "macro_rules! decl { () => { fn lean_generated(); } }\n"
        'extern "C" {\n'
        "    decl!();\n"
        '    fn lean_real(x: u64) -> u64;\n'
        "}\n"
    )
    refused = False
    try:
        extern_declarations_in(macro_extern_rust, "fixture")
    except SystemExit:
        refused = True
    if not refused:
        failures.append(
            "a macro invocation inside an `extern` block was read past rather than "
            "refused, so its expanded declaration is required of nobody (round 21)"
        )
    # ...and an ordinary block with no macro is still accepted, so the refusal
    # is a bound rather than a blanket rejection of foreign blocks.
    if extern_declarations_in(
        'extern "C" {\n    fn lean_real(x: u64) -> u64;\n}\n', "fixture"
    ) != {"lean_real"}:
        failures.append("the macro refusal rejected an ordinary `extern` block (round 21)")
    # PR #889 review round 25: `r#` is Rust's raw-identifier escape and names
    # the *same* linker symbol as the bare spelling, so `fn r#lean_real();`
    # requires `lean_real` of somebody.  The mutation KEEPS the block, the `fn`
    # and the name and only escapes it — which matched no `fn` pattern at all,
    # so the item declared nothing and Tier 1 passed with no provider.
    raw_ident_rust = 'extern "C" {\n    fn r#lean_real(x: u64) -> u64;\n}\n'
    if extern_declarations_in(raw_ident_rust, "fixture") != {"lean_real"}:
        failures.append(
            "a raw-identifier `fn` declaration required no symbol, so its seam has no "
            "provider (round 25)"
        )
    # ...and the items that legitimately declare no *function* symbol are
    # enumerated rather than implied: a `static`, a type alias and a `use` are
    # skipped, and anything else stops the build.  Round 21 refused macros and
    # let every other unrecognised item fall through, which is the fail-open
    # direction — an item whose form this scanner does not know signals nothing.
    for what, block in (
        ("a `static`", 'extern "C" {\n    static COUNT: u64;\n'
                        '    fn lean_real(x: u64) -> u64;\n}\n'),
        ("a type alias", 'extern "C" {\n    type Opaque;\n'
                         '    fn lean_real(x: u64) -> u64;\n}\n'),
    ):
        try:
            got = extern_declarations_in(block, "fixture")
        except SystemExit:
            failures.append(f"{what} inside an `extern` block was refused (round 25)")
        else:
            if got != {"lean_real"}:
                failures.append(
                    f"{what} beside a live declaration changed the requirement set "
                    f"(round 25): {sorted(got)}"
                )
    unclassified_rust = (
        'extern "C" {\n'
        "    const unsafe fine: u64;\n"
        '    fn lean_real(x: u64) -> u64;\n'
        "}\n"
    )
    refused_unclassified = False
    try:
        extern_declarations_in(unclassified_rust, "fixture")
    except SystemExit:
        refused_unclassified = True
    if not refused_unclassified:
        failures.append(
            "an `extern` item this scanner cannot classify was skipped rather than "
            "refused, so any symbol it declares is required of nobody (round 25)"
        )
    # PR #889 review round 16: an uninvoked `.macro` body emits nothing, so its
    # directive and label are not a provider.  Both tokens stay in the fixture.
    macro_asm = (
        ".macro make_ghost\n"
        "    .global lean_ghost\n"
        "lean_ghost:\n"
        "    ret\n"
        ".endm\n"
        "    .global lean_real\n"
        "lean_real:\n"
        "    ret\n"
    )
    got = asm_definitions_in(macro_asm)
    if "lean_ghost" in got:
        failures.append(
            "a `.global`/label pair inside an uninvoked `.macro` counted as an assembly "
            "provider (round 16)"
        )
    if "lean_real" not in got:
        failures.append("a real assembly provider beside a macro definition was lost (round 16)")

    # PR #889 review round 17: `.if 0` is the assembler's own `#if 0`, one
    # preprocessing stage later, and a repeat block may repeat zero times.
    # Every fixture keeps the `.global` and its label.
    for label, region in (
        ("an assembler conditional", ".if 0\n    .global lean_ghost\nlean_ghost:\n    ret\n.endif\n"),
        ("an `.ifdef` region", ".ifdef SOMETHING\n    .global lean_ghost\nlean_ghost:\n    ret\n.endif\n"),
        ("the `.else` half of a conditional",
         ".ifdef X\n    nop\n.else\n    .global lean_ghost\nlean_ghost:\n    ret\n.endif\n"),
        ("a repeat block", ".rept 0\n    .global lean_ghost\nlean_ghost:\n    ret\n.endr\n"),
        ("a conditional sharing its line with a label",
         "retry: .if 0\n    .global lean_ghost\nlean_ghost:\n    ret\n.endif\n"),
    ):
        got = asm_definitions_in(region + "    .global lean_real\nlean_real:\n    ret\n")
        if "lean_ghost" in got:
            failures.append(
                f"a `.global`/label pair inside {label} counted as an assembly provider "
                "(round 17)"
            )
        if "lean_real" not in got:
            failures.append(
                f"a real assembly provider after {label} was lost (round 17)"
            )

    # PR #889 review round 17: the attribute is **located** on the string-free
    # view.  Both fixtures keep the `link_name` text; in neither is it an
    # attribute of the declaration, so the requirement is the Rust name.
    renamed_in_raw_doc_rust = (
        'extern "C" {\n'
        '    #[doc = r#"#[link_name = \'lean_kernel_main\']"#]\n'
        '    fn lean_beta(x: u64);\n'
        '}\n'
    ).replace("\'", '"')
    if extern_declarations_in(renamed_in_raw_doc_rust, "fixture") != {"lean_beta"}:
        failures.append(
            "a `#[link_name]` quoted inside a raw-string doc attribute renamed the "
            "declaration beside it (round 17)"
        )
    raw_link_name_rust = (
        'extern "C" {\n'
        '    #[link_name = r"actual_symbol"]\n'
        '    fn local_name(x: u64) -> u64;\n'
        '}\n'
    )
    if extern_declarations_in(raw_link_name_rust, "fixture") != {"actual_symbol"}:
        failures.append(
            "a `#[link_name]` written with a raw string literal was not honoured (round 17)"
        )
    # PR #889 review round 17: what opens an `extern` block is the keyword and a
    # brace, not the eleven characters `extern "C" {`.  Every accepted spelling
    # keeps the declaration; the two refused ones keep the keyword.
    for label, spelling, opens in (
        ("a raw ABI literal", 'extern r"C" {\n    fn lean_beta(x: u64);\n}\n', True),
        ("a hashed raw ABI literal", 'extern r#"C"# {\n    fn lean_beta(x: u64);\n}\n', True),
        ("an omitted ABI", "extern {\n    fn lean_beta(x: u64);\n}\n", True),
        ("another ABI", 'extern "C-unwind" {\n    fn lean_beta(x: u64);\n}\n', True),
        ("the 2024 `unsafe extern`", 'unsafe extern "C" {\n    fn lean_beta(x: u64);\n}\n', True),
        ("an `extern fn` definition",
         'pub extern "C" fn lean_beta(x: u64) {\n    let _ = x;\n}\n', False),
        ("an `extern crate`", "extern crate alloc;\nfn lean_beta(x: u64) {}\n", False),
    ):
        collected = "lean_beta" in extern_declarations_in(spelling, "fixture")
        if collected != opens:
            failures.append(
                f"{label} was read as {'no ' if opens else ''}`extern` block, so its "
                f"declaration was {'lost' if opens else 'collected'} (round 17)"
            )

    renamed_in_comment_rust = (
        'extern "C" {\n'
        '    // #[link_name = "actual_symbol"]\n'
        '    fn lean_beta(x: u64);\n'
        '}\n'
    )
    if extern_declarations_in(renamed_in_comment_rust, "fixture") != {"lean_beta"}:
        failures.append("a commented-out `#[link_name]` renamed a declaration")

    commented_rust = '// extern "C" {\n//    fn lean_alpha(x: u64) -> u64;\n// }\n'
    if extern_declarations_in(commented_rust, "fixture"):
        failures.append("a commented-out `extern \"C\"` block was collected")
    # PR #889 review round 6: a block quoted in a raw string or in a nested
    # block comment declares nothing; a live block after either is still seen.
    raw_string_rust = 'const DOC: &str = r#"extern "C" {\n    fn lean_alpha(x: u64) -> u64;\n}"#;\n'
    if extern_declarations_in(raw_string_rust, "fixture"):
        failures.append("an `extern \"C\"` block inside a raw string was collected")
    nested_comment_rust = (
        '/* outer /* extern "C" {\n    fn lean_alpha(x: u64) -> u64;\n} */ tail */\n'
        'extern "C" {\n    fn lean_beta(x: u64);\n}\n'
    )
    if extern_declarations_in(nested_comment_rust, "fixture") != {"lean_beta"}:
        failures.append("a nested Rust block comment was not blanked around the live block")

    # --- PR #889 review: the link requirement is one-sided, and reconciled ---
    live_asm = (
        ".global _start\n.globl secondary_entry\n// .global ghost_entry\n/* .global other */\n"
        "_start:\n    b .\nsecondary_entry:\n    b .\nghost_entry:\nother:\n"
    )
    if asm_definitions_in(live_asm) != {"_start", "secondary_entry"}:
        failures.append("assembly `.global`/`.globl` providers were not collected exactly")
    # PR #889 review round 6: a directive and label quoted in a string or in a
    # block comment that spans lines define nothing.
    quoted_asm = (
        '.asciz "\\n.global ghost_entry\\nghost_entry:"\n/* .global other\nother:\n */\n'
        ".global _start\n_start:\n    b .\n"
    )
    if asm_definitions_in(quoted_asm) != {"_start"}:
        failures.append("an assembly definition quoted in a string or a block comment was collected")

    # --- PR #889 review round 3: a provider is a DEFINED, ASSEMBLED symbol ---
    # The directive stays; the label moves into a comment.  A directive-only
    # scan kept reporting `secondary_entry` as provided.
    directive_only = ".global secondary_entry\n// secondary_entry:\n    b .\n"
    if asm_definitions_in(directive_only):
        failures.append("a `.global` whose label is gone was collected as a provider")
    label_only = "secondary_entry:\n    b .\n"
    if asm_definitions_in(label_only):
        failures.append("a label without `.global` was collected as a provider")
    build_rs = (
        "fn main() {\n    let mut asm = cc::Build::new();\n"
        "    asm.file(\"src/boot.S\").file(\"src/trap.S\")\n"
        "        .compile(\"sele4n_hal_asm\");\n"
        "    // asm.file(\"src/ghost.S\");\n    /* asm.file(\"src/other.S\"); */\n}\n"
    )
    if assembled_sources_in(build_rs) != {"src/boot.S", "src/trap.S"}:
        failures.append("the assembled-source set was not derived from the live `.file()` calls")
    defined_asm = ".global secondary_entry\nsecondary_entry:\n    b .\n"
    ghost_asm = ".global ghost_entry\nghost_entry:\n    b .\n"
    providers = asm_providers_from({"src/boot.S": defined_asm, "src/ghost.S": ghost_asm}, build_rs)
    if providers != {"secondary_entry"}:
        failures.append(
            "a symbol defined in a source build.rs does not assemble was counted as a provider"
        )

    # --- PR #889 review round 4: a provider is emitted code on the compiled chain ---
    # The directive and the label stay; they move under `#if 0`.
    inactive_asm = "#if 0\n.global secondary_entry\nsecondary_entry:\n    b .\n#endif\n"
    if asm_definitions_in(inactive_asm):
        failures.append("a definition inside `#if 0` was collected as a provider")
    nested_asm = (
        "#ifdef FOO\n#if 1\n.global secondary_entry\nsecondary_entry:\n#endif\n#endif\n"
        ".global _start\n_start:\n"
    )
    if asm_definitions_in(nested_asm) != {"_start"}:
        failures.append("a nested conditional region was not excluded, or code outside it was")
    if asm_definitions_in(defined_asm) != {"secondary_entry"}:
        failures.append("an unconditional definition was lost to the conditional filter")
    # A `.file()` on a probe builder, on a builder never compiled, and in a
    # helper `main` never calls all keep the token and assemble nothing.
    live_chain = (
        "fn main() {\n    assemble();\n}\n"
        "fn assemble() {\n    let mut probe = cc::Build::new();\n    probe.file(\"src/probe.S\");\n"
        "    let mut unused = cc::Build::new();\n    unused.file(\"src/ghost.S\");\n"
        "    let mut asm = cc::Build::new();\n    asm.file(\"src/boot.S\").file(\"src/trap.S\")\n"
        "        .compile(\"sele4n_hal_asm\");\n}\n"
        "fn dead() {\n    let mut other = cc::Build::new();\n    other.file(\"src/dead.S\")\n"
        "        .compile(\"sele4n_hal_asm\");\n}\n"
    )
    if assembled_sources_in(live_chain) != {"src/boot.S", "src/trap.S"}:
        failures.append(
            "the assembled-source set was not the compiled builder's live chain "
            f"(got {sorted(assembled_sources_in(live_chain))})"
        )
    # PR #889 review round 7: a `.file()` under a dead branch of the compiling
    # function, and one in an unreachable helper whose local shares the
    # receiver's name, keep the token and assemble nothing; a separate
    # top-level `.file()` statement before the compile does assemble.
    executed_chain = (
        "fn main() {\n    assemble();\n}\n"
        "fn stale() {\n    let mut asm = cc::Build::new();\n    asm.file(\"src/stale.S\");\n}\n"
        "fn assemble() {\n    let mut asm = cc::Build::new();\n"
        "    asm.file(\"src/vectors.S\");\n"
        "    if false {\n        asm.file(\"src/ghost.S\");\n    }\n"
        "    asm.file(\"src/boot.S\").file(\"src/trap.S\")\n"
        "        .compile(\"sele4n_hal_asm\");\n}\n"
    )
    if assembled_sources_in(executed_chain) != {"src/vectors.S", "src/boot.S", "src/trap.S"}:
        failures.append(
            "the assembled-source set was not the executed builder chain "
            f"(got {sorted(assembled_sources_in(executed_chain))})"
        )
    # PR #889 review round 8: the receiver is REBOUND between two `.file()`
    # calls.  Every token of the round-7 fixture survives — the same name,
    # top-level statements, one compile — and only the first `.file()`'s
    # binding instance differs from the compile's.
    shadowed_chain = (
        "fn main() {\n    assemble();\n}\n"
        "fn assemble() {\n    let mut asm = cc::Build::new();\n"
        "    asm.file(\"src/ghost.S\");\n"
        "    let mut asm = cc::Build::new();\n"
        "    asm.file(\"src/real.S\").compile(\"sele4n_hal_asm\");\n}\n"
    )
    if assembled_sources_in(shadowed_chain) != {"src/real.S"}:
        failures.append(
            "a `.file()` on a shadowed, uncompiled builder was counted as assembled "
            f"(got {sorted(assembled_sources_in(shadowed_chain))})"
        )
    # PR #889 review round 9: the receiver is REBOUND BY ASSIGNMENT, with no
    # second `let`.  One `let`, the same name, the same order — only the
    # second value's origin differs, and `ghost.S` is on the discarded builder.
    assigned_chain = (
        "fn main() {\n    assemble();\n}\n"
        "fn assemble() {\n    let mut asm = cc::Build::new();\n"
        "    asm.file(\"src/ghost.S\");\n"
        "    asm = cc::Build::new();\n"
        "    asm.file(\"src/real.S\").compile(\"sele4n_hal_asm\");\n}\n"
    )
    if assembled_sources_in(assigned_chain) != {"src/real.S"}:
        failures.append(
            "a `.file()` on a builder discarded by a later assignment was counted as "
            f"assembled (got {sorted(assembled_sources_in(assigned_chain))})"
        )

    # A receiver the block does not bind — a parameter — has no binding
    # instance in the body, so nothing before the compile statement counts.
    parameter_receiver = (
        "fn main() {\n    let mut asm = cc::Build::new();\n    assemble(&mut asm);\n}\n"
        "fn assemble(asm: &mut cc::Build) {\n"
        "    asm.file(\"src/outer.S\");\n"
        "    asm.compile(\"sele4n_hal_asm\");\n}\n"
    )
    if assembled_sources_in(parameter_receiver) != set():
        failures.append(
            "a receiver bound outside the compile's body resolved to a binding instance "
            f"(got {sorted(assembled_sources_in(parameter_receiver))})"
        )
    # ...and a temporary chain has no receiver identifier at all: the cross
    # gate's `chain_root` answers `None` for it (fail closed), the Tier 0
    # build-script check refuses it, and nothing is counted here either.
    temporary_chain = (
        "fn main() {\n    assemble();\n}\n"
        "fn assemble() {\n"
        "    cc::Build::new().file(\"src/one.S\").file(\"src/two.S\")\n"
        "        .compile(\"sele4n_hal_asm\");\n}\n"
    )
    if assembled_sources_in(temporary_chain) != set():
        failures.append(
            "a temporary builder chain, which the receiver resolver fails closed on, "
            f"counted sources (got {sorted(assembled_sources_in(temporary_chain))})"
        )
    nm_text = (
        "0000000000000000 N $d.1\n0000000000000000 t $x.0\n"
        "0000000000000000 T _start\n000000000000007c T secondary_entry\n"
        "0000000000000010 D table\n0000000000000020 B scratch\n"
        "0000000000000030 t local_helper\n0000000000000040 W weak_fn\n"
    )
    # PR #889 review round 8: a function requirement is satisfied by global
    # TEXT only.  `table` (data), `scratch` (bss), `local_helper` (local
    # text) and `weak_fn` (weak) all keep the symbol name and are not
    # executable global definitions.
    if executable_definitions(nm_text) != {"_start", "secondary_entry"}:
        failures.append(
            "`nm` output was not reduced to its global text definitions "
            f"(got {sorted(executable_definitions(nm_text))})"
        )
    # ...and the classification reads the same set: a Lean export renamed
    # away that leaves a global DATA object under the old name is missing.
    missing, _, _, _ = classify_link_requirements(
        externs={"lean_alpha"},
        asm_globals=set(),
        expected_unresolved={},
        defined=executable_definitions(
            "0000000000000000 D lean_alpha\n0000000000000008 T lean_alpha_renamed\n"
        ),
    )
    if missing != ["lean_alpha"]:
        failures.append("a data object under a function extern's name satisfied the requirement")

    # PR #889 review round 17: the boot entry's contract is no longer decided
    # here.  What that entry *is* — whether it executes the checked boot, what
    # its `.error` arm does, whether a name denotes the declaration it spells —
    # are questions about elaboration, and eleven review rounds of regular
    # expressions answered them wrongly one Lean spelling at a time.  They are
    # answered by the elaborator in `SeLe4n/Testing/BootEntryContract.lean`,
    # over `Environment`, where the references are resolved constants; that
    # module's own witnesses (a compliant entry and three token-preserving
    # deviations) keep it from being vacuous while the entry is still SM10.1's
    # to write.  What remains here is the link-level reconciliation: symbols,
    # archives and Rust declarations, which no Lean elaboration can see.

    # A HAL declaration whose Lean export exists under ANOTHER spelling: the
    # token `lean_alpha` is present on the Lean side, but the HAL's spelling is
    # unresolved.  The intersection passed this; the requirement must not.
    missing, stale_undeclared, stale_defined, _ = classify_link_requirements(
        externs={"lean_alpah", "lean_beta"},
        asm_globals=set(),
        expected_unresolved={},
        defined={"lean_alpha", "lean_beta"},
    )
    if missing != ["lean_alpah"] or stale_undeclared or stale_defined:
        failures.append(
            "a HAL declaration misspelt against its Lean export was not reported as missing"
        )

    # The reverse rename: the Lean export moved and the HAL kept the old name.
    missing, _, _, _ = classify_link_requirements(
        externs={"lean_alpha"}, asm_globals=set(), expected_unresolved={}, defined={"lean_alpha2"}
    )
    if missing != ["lean_alpha"]:
        failures.append("a Lean export renamed away from the HAL's declaration was not reported")

    # An assembly global satisfies a HAL declaration without the archive.
    missing, _, _, _ = classify_link_requirements(
        externs={"secondary_entry", "lean_beta"},
        asm_globals={"secondary_entry"},
        expected_unresolved={},
        defined={"lean_beta"},
    )
    if missing:
        failures.append("an assembly-provided declaration was reported as missing")

    # An expected-unresolved entry is honoured while its reason holds...
    missing, stale_undeclared, stale_defined, stale_exported = classify_link_requirements(
        externs={"lean_kernel_main", "lean_beta"},
        asm_globals=set(),
        expected_unresolved={"lean_kernel_main": "SM10.1"},
        defined={"lean_beta"},
        exports={"lean_beta"},
    )
    if missing or stale_undeclared or stale_defined or stale_exported:
        failures.append("a live expected-unresolved entry was not honoured")

    # ...fails once the archive defines it (the exemption outlived its reason)...
    _, _, stale_defined, _ = classify_link_requirements(
        externs={"lean_kernel_main"},
        asm_globals=set(),
        expected_unresolved={"lean_kernel_main": "SM10.1"},
        defined={"lean_kernel_main"},
    )
    if stale_defined != ["lean_kernel_main"]:
        failures.append("an expected-unresolved entry the archive defines was not reported")

    # PR #889 review round 6: the exemption expires when the EXPORT appears —
    # the token is in the Lean inventory, the archive still lacks it (the
    # module is outside the import closure), and the old classification
    # reported nothing.  Both the expiry and the requirement it restores fire.
    missing, _, _, stale_exported = classify_link_requirements(
        externs={"lean_kernel_main"},
        asm_globals=set(),
        expected_unresolved={"lean_kernel_main": "SM10.1"},
        defined=set(),
        exports={"lean_kernel_main"},
    )
    if stale_exported != ["lean_kernel_main"]:
        failures.append("an expected-unresolved entry the Lean tree exports was not reported stale")
    if missing != ["lean_kernel_main"]:
        failures.append(
            "an exported, undefined expected-unresolved entry was not required of the archive"
        )
    # ...and when the archive defines it too, both expiries fire and nothing is missing.
    missing, _, stale_defined, stale_exported = classify_link_requirements(
        externs={"lean_kernel_main"},
        asm_globals=set(),
        expected_unresolved={"lean_kernel_main": "SM10.1"},
        defined={"lean_kernel_main"},
        exports={"lean_kernel_main"},
    )
    if missing or stale_defined != ["lean_kernel_main"] or stale_exported != ["lean_kernel_main"]:
        failures.append("an exported AND defined expected-unresolved entry was not doubly stale")

    # ...and fails once the HAL no longer declares it (the entry outlived the seam).
    _, stale_undeclared, _, _ = classify_link_requirements(
        externs={"lean_beta"},
        asm_globals=set(),
        expected_unresolved={"lean_kernel_main": "SM10.1"},
        defined={"lean_beta"},
    )
    if stale_undeclared != ["lean_kernel_main"]:
        failures.append("an expected-unresolved entry the HAL no longer declares was not reported")

    if failures:
        print("[FAIL] check_kernel_entry_exports self-test:")
        for line in failures:
            print(f"         {line}")
        return 1
    print(f"[PASS] check_kernel_entry_exports self-test ({self_test_case_count()} cases)")
    return 0


def archive_defined_symbols(archive: Path) -> set[str]:
    out = subprocess.run(
        ["nm", "--defined-only", "-g", str(archive)],
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    # `<addr> <type> <name>`; archive member headers have fewer fields, and
    # only global text (`T`) resolves a function requirement (round 8).
    return executable_definitions(out)


def main() -> int:
    if "--self-test" in sys.argv[1:]:
        return self_test()
    if shutil.which("nm") is None:
        print("[SKIP] `nm` not available — cannot read the archive's symbol table")
        return SKIP_EXIT
    if not ARCHIVE.exists():
        sys.exit(
            f"[FAIL] {ARCHIVE} does not exist. Build it first: `lake build SeLe4n:static`"
        )

    sources = lean_sources()
    if str(LEAN_LIBRARY_ROOT_MODULE.relative_to(REPO)) not in sources:
        sys.exit("[FAIL] the Lean source inventory does not include the library root module")
    exports = set()
    for text in sources.values():
        exports.update(lean_exports_in(text))
    externs = hal_extern_declarations()
    asm_globals, provider_basis = hal_asm_providers()
    if not exports:
        sys.exit("[FAIL] no `@[export …]` found under SeLe4n/ — the derivation is broken")
    if not externs:
        sys.exit(
            '[FAIL] no `extern "C"` declaration found under rust/sele4n-hal/src/ — '
            "the derivation is broken"
        )
    if not asm_globals:
        sys.exit(
            "[FAIL] no defined, exported symbol found in the assembly sources build.rs "
            "assembles — the assembly provider derivation is broken"
        )
    # PR #889 review round 17: the kernel-state installer derivation, the halt
    # derivation, the callee resolution and the boot-entry binding check all
    # lived here and all read Lean source with regular expressions.  They are
    # now `SeLe4n/Testing/BootEntryContract.lean`, which asks the elaborated
    # environment instead — `getExportNameFor?` for the entry,
    # `Expr.getUsedConstants` for what it calls, and a reachability walk for
    # what installs state — and fails its own elaboration, so
    # `scripts/test_tier1_build.sh` runs it on every push.  A spelling cannot
    # defeat it: by the time a declaration is in the environment there are no
    # spellings left, only constants.
    if not (exports & externs):
        sys.exit(
            "[FAIL] the Lean `@[export]` set and the HAL `extern \"C\"` set are disjoint. "
            "Every kernel entry is declared on both sides, so an empty intersection means "
            "one of the two scans stopped matching and this gate would pass vacuously."
        )

    defined = archive_defined_symbols(ARCHIVE)
    missing, stale_undeclared, stale_defined, stale_exported = classify_link_requirements(
        externs, asm_globals, EXPECTED_UNRESOLVED, defined, exports
    )
    failed = False
    if missing:
        failed = True
        print("[FAIL] HAL `extern \"C\"` declarations no provider defines:")
        for symbol in missing:
            side = (
                "the Lean tree exports it, but the archive does not define it — its module is "
                "outside `SeLe4n.lean`'s import closure (add it there and drop it from "
                "`scripts/staged_module_allowlist.txt`)"
                if symbol in exports
                else "nothing exports it — a Lean `@[export]` under another spelling, a renamed "
                "seam, or a declaration with no provider (SM10.1 seams go in "
                "`EXPECTED_UNRESOLVED` with their reason)"
            )
            print(f"         {symbol}: {side}")
    if stale_undeclared:
        failed = True
        print("[FAIL] EXPECTED_UNRESOLVED entries the HAL no longer declares (remove them):")
        for symbol in stale_undeclared:
            print(f"         {symbol}")
    if stale_defined:
        failed = True
        print("[FAIL] EXPECTED_UNRESOLVED entries the archive now defines (remove them):")
        for symbol in stale_defined:
            print(f"         {symbol}")
    if stale_exported:
        failed = True
        print(
            "[FAIL] EXPECTED_UNRESOLVED entries the Lean tree now exports (remove them — the "
            "exemption expired with the export, and the archive must define the symbol):"
        )
        for symbol in stale_exported:
            print(f"         {symbol}")
    if failed:
        return 1

    required = link_requirements(externs, asm_globals, EXPECTED_UNRESOLVED, exports)
    boot_entry = (
        "exported; its contract is checked by `SeLe4n/Testing/BootEntryContract.lean`"
        if BOOT_ENTRY_SYMBOL in exports
        else "not yet exported (SM10.1), reconciled as expected unresolved"
    )
    print(
        f"[PASS] all {len(required)} HAL kernel-entry declarations are defined in the archive "
        f"({len(externs & asm_globals)} resolved by the HAL's assembly — {provider_basis}; "
        f"{len(EXPECTED_UNRESOLVED)} expected unresolved and reconciled); boot entry "
        f"`{BOOT_ENTRY_SYMBOL}`: {boot_entry}"
    )
    for symbol in required:
        print(f"         {symbol}")
    for symbol, reason in sorted(EXPECTED_UNRESOLVED.items()):
        print(f"         {symbol}: expected unresolved — {reason}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
