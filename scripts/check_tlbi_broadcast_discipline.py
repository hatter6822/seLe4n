#!/usr/bin/env python3
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
"""WS-RR RR1.9 -- enforce the TLBI broadcast discipline.

``SMP_RUST_HAL_PLAN.md`` §4.4 states that under SMP every kernel-side TLB
invalidation routes through ``tlbi_for_sharing(domain, op)``, which selects
the IS or OS broadcast per ``PlatformBinding.sharingDomain``, and that "a
``grep`` test in tier-0 ensures no production caller emits ``tlbi vae1``
(non-IS)".  That test did not exist.  The plan's SM1.E.5 sketch --
``grep -rn "tlbi_vae1[^i]" SeLe4n/`` -- would not have been it either: it
scans only the Lean tree, matches only one of the four local variants, has
no notion of the call sites that are legitimately local, and reads raw text
so the sentence describing the rule trips the rule.

Why it matters: a non-broadcast ``tlbi vae1`` invalidates only the calling
PE's TLB.  Under SMP a secondary can go on walking a translation the primary
believes it removed, and then load a page the primary considers unmapped --
or mapped for a different address space.  That is the stale-mapping hazard
the entire SM7 shootdown protocol exists to close, and re-opening it takes
one direct call.

Three invariants are checked:

1. **CONTAINMENT** -- a ``tlbi`` mnemonic may be emitted only from
   ``rust/sele4n-hal/src/tlb.rs``.  Every other emission site, in Rust
   ``asm!`` or in a ``.S`` source, bypasses the wrappers' mandatory
   ``DSB``/``ISB`` bracket as well as the broadcast choice.

2. **ALLOWLIST** -- outside ``tlb.rs``, the local (non-broadcast) wrappers
   ``tlbi_vmalle1`` / ``tlbi_vae1`` / ``tlbi_aside1`` / ``tlbi_vale1`` /
   ``tlbi_local`` may be *referenced* only from sites registered in
   ``scripts/tlbi_local_allowlist.txt``, each with the reason the calling
   PE is the only one whose TLB needs the entry gone.  Reference, not
   call: an aliasing ``use`` or a function-pointer binding reaches the
   same instruction while naming it nowhere at the call site.

3. **LEAN** -- the Lean bindings for the local FFI exports
   (``ffiTlbiAll`` / ``ffiTlbiByAsid`` / ``ffiTlbiByVaddr``) may be
   referenced only from registered production modules.  Everything else
   uses ``ffiTlbiForSharing``.  The declaration sites are exempt per
   occurrence -- the binder line under an ``@[extern "ffi_tlbi_*"]``
   attribute -- never per file, so a module that declares one binding
   still has its other references checked.

The allowlist is checked in both directions: an unregistered call site
fails, and so does a registered site that no longer exists, so the file
cannot accumulate entries for code that is gone.

A presence check is not a relation check.  The allowlist matches any
*reference* rather than call syntax (an aliasing `use` reaches the same
instruction), and the declaration exemption is resolved per occurrence over
the stripped code rather than per file over raw text.  See CLAUDE.md's
"A presence check is not a relation check"; add a check here only with a
negative case that KEEPS its token and breaks its relation.

Gates read code, prose reads prose: Rust and assembly sources are stripped
of ``//`` comments here, the allowlist of its ``#`` comments, and Lean
sources go through ``lean_code_view.strip`` -- the repository's one Lean
stripper -- so a docstring naming ``tlbi_vae1`` neither satisfies nor trips
a check.

Usage:
    check_tlbi_broadcast_discipline.py              # scan the repository
    check_tlbi_broadcast_discipline.py --self-test  # prove the gate bites

Exits 0 when clean, 1 on any violation or self-test failure.
"""

from __future__ import annotations

import os
import re
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lean_code_view  # noqa: E402  (path set up immediately above)
import rust_code_view  # noqa: E402

ALLOWLIST = "scripts/tlbi_local_allowlist.txt"
TLB_MODULE = "rust/sele4n-hal/src/tlb.rs"
RUST_SRC = "rust/sele4n-hal/src"
LEAN_ROOT = "SeLe4n"

# The local, non-broadcast wrappers.  `tlbi_local` dispatches to them, so it
# carries the same obligation as a direct call.
LOCAL_WRAPPERS = (
    "tlbi_vmalle1",
    "tlbi_vae1",
    "tlbi_aside1",
    "tlbi_vale1",
    "tlbi_local",
)

# The Lean bindings of the local FFI exports.  Kept as a pin, NOT as the
# source of truth: `local_ffi_exports` derives which `ffi_tlbi_*` exports
# are local from what their Rust bodies actually reach, and
# `check_lean_binding_inventory` fails when a binding of a local export is
# missing here.  An enumeration cannot see an export that does not exist
# yet -- the same hole a hand-written `LOCAL_WRAPPERS` had (PR #883 review
# round 4), one layer up.
LEAN_LOCAL_BINDINGS = ("ffiTlbiAll", "ffiTlbiByAsid", "ffiTlbiByVaddr")
FFI_MODULE = "rust/sele4n-hal/src/ffi.rs"
_FFI_TLBI_EXPORT_RE = re.compile(
    r'\bpub\s+extern\s+"C"\s+fn\s+(ffi_tlbi_[a-z0-9_]+)\s*\('
)

# Any REFERENCE to a local wrapper, not only a call.  Requiring `name(`
# missed every way of reaching the function without naming it at the call
# site -- `use crate::tlb::tlbi_vae1 as invalidate_local;` then
# `invalidate_local(...)`, or `let f = crate::tlb::tlbi_vae1;` -- each of
# which performs a non-broadcast invalidation while matching nothing (PR
# #883 review).  A reference is the right granularity: the name has to
# appear *somewhere* to reach the function, and that somewhere is what the
# allowlist should register.
#
# `\b` on both sides is exact even though `tlbi_vmalle1` is a prefix of
# `tlbi_vmalle1is`: `1` and `i` are both word characters, so there is no
# boundary between them and the broadcast wrappers cannot match.
LOCAL_WRAPPER_RE = re.compile(r"\b(" + "|".join(LOCAL_WRAPPERS) + r")\b")

# A `tlbi` mnemonic at the head of an assembly statement.  Anchored on a
# statement boundary (start of the template, or after a `;` or a newline)
# so an identifier such as `tlbi_vae1` inside a template cannot match.
TLBI_MNEMONIC_RE = re.compile(r'(?:^|[\s;"])tlbi\s+[a-z]', re.IGNORECASE)

# `re.MULTILINE` is load-bearing: without it `^` anchors only at offset 0, so
# every declaration after the first line is invisible and every reference
# reports `<file scope>`.  The first version of this gate had exactly that
# defect, and the fixture below hid it by putting the declaration on the
# file's first line — which is why the fixture now carries a docstring.
LEAN_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|partial\s+|noncomputable\s+|unsafe\s+)*"
    r"(?:def|abbrev|theorem|lemma|instance|opaque)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.!?]*)",
    re.MULTILINE,
)


def strip_rust(text: str) -> str:
    """The Rust code view: comments blanked, string contents KEPT.

    Delegated to `rust_code_view`, the repository's one Rust stripper, for
    a reason the first version of this gate got backwards.  It reasoned that
    a `//` inside a string literal "can only make the gate *stricter* about
    containment ... since a call site is never inside a string".  A call
    site is not, but an *instruction* is: the containment check's whole
    subject is the text inside an `asm!` template, and

        core::arch::asm!("// note", "tlbi vmalle1")

    is two template lines joined with a newline.  The `//` opens a comment
    for the assembler, on its own line; the `tlbi` on the next line is
    emitted.  A line-based stripper truncates at that `//` and deletes the
    instruction from the view -- fail-open, in the check that matters most
    (PR #883 review round 3).

    So string contents are preserved here, and the allowlist check reads
    the same view: a wrapper name appearing in a literal is then reported
    rather than skipped, which is the direction a gate should err in.
    """
    return rust_code_view.code(text)


def split_top_level(arguments: str) -> list[str]:
    """Split a macro argument list on commas outside brackets and strings."""
    parts, current, depth, quote = [], [], 0, None
    index = 0
    while index < len(arguments):
        char = arguments[index]
        if quote is not None:
            current.append(char)
            if char == "\\":
                if index + 1 < len(arguments):
                    current.append(arguments[index + 1])
                    index += 2
                    continue
            elif char == quote:
                quote = None
        elif char == '"':
            quote = char
            current.append(char)
        elif char in "([{":
            depth += 1
            current.append(char)
        elif char in ")]}":
            depth -= 1
            current.append(char)
        elif char == "," and depth == 0:
            parts.append("".join(current))
            current = []
        else:
            current.append(char)
        index += 1
    if current:
        parts.append("".join(current))
    return [part for part in parts if part.strip()]


# Macros that produce an `asm!` template.  `concat!` joins its arguments;
# `stringify!` turns its raw tokens into a string, so
# `asm!(stringify!(tlbi vmalle1))` emits the instruction with no string
# literal anywhere in the source (PR #883 review round 10).
_TEMPLATE_MACRO_RE = re.compile(r"\b(concat|stringify)!\s*\(")


def resolve_template_macros(code: str) -> tuple[str, list[str]]:
    """Fold `concat!("a", "b")` into `"ab"`, byte-aligned by padding.

    `asm!(concat!("tlbi ", "vmalle1"))` emits the instruction: `concat!`
    produces ONE template line, so the mnemonic and its operand are on the
    same line even though the source shows two literals.  The mnemonic
    regex, reading the literals separately, matched neither (PR #883 review
    round 6).

    Note the asymmetry that makes this specific rather than general: the
    sibling form `asm!("tlbi ", "vmalle1")` is two template LINES, joined
    by `asm!` with a newline, and does NOT emit `tlbi vmalle1`.  So
    adjacent template strings must stay separate and only `concat!` folds.

    The replacement is padded to the original span's length so every
    offset -- and therefore every reported line number -- still points at
    the real file.  A `concat!` whose arguments are not all string
    literals cannot be folded; those are returned as problems rather than
    ignored, since an unresolvable template is exactly where a mnemonic
    could hide.
    """
    problems: list[str] = []
    out = code
    while True:
        match = _TEMPLATE_MACRO_RE.search(out)
        if match is None:
            return out, problems
        open_paren = match.end() - 1
        depth, index = 0, open_paren
        while index < len(out):
            if out[index] == "(":
                depth += 1
            elif out[index] == ")":
                depth -= 1
                if depth == 0:
                    break
            index += 1
        if index >= len(out):
            return out, problems
        span = out[match.start() : index + 1]
        if match.group(1) == "stringify":
            # `stringify!` yields its argument tokens verbatim as a string.
            folded = '"' + out[open_paren + 1 : index].strip() + '"'
            out = out[: match.start()] + folded.ljust(len(span))[: len(span)] + out[index + 1 :]
            continue
        arguments = split_top_level(out[open_paren + 1 : index])

        # A non-literal argument matters only where it could start a NEW
        # assembly statement.  `concat!("mrs {}, ", $reg)` -- the register
        # macros in `registers.rs` -- puts the MNEMONIC in the literal
        # prefix and the operand in the parameter, so the instruction is
        # fully visible and folding the literals is enough.  A non-literal
        # is unresolvable only when the literal text before it is empty or
        # ends at a statement boundary, because only there can it supply a
        # mnemonic this gate would never see.
        text, unresolvable = "", False
        for argument in arguments:
            literal = re.fullmatch(r'\s*"((?:[^"\\]|\\.)*)"\s*', argument)
            if literal:
                text += literal.group(1)
                continue
            # A non-literal is replaced by a PLACEHOLDER token rather than
            # dropped.  `concat!("tlbi ", stringify!(vmalle1))` expands to
            # `"tlbi vmalle1"` and emits; dropping the argument left
            # `"tlbi "` in the view, which the mnemonic regex -- needing a
            # letter after the space -- did not match, so an emission whose
            # OPERAND comes from a macro was invisible (PR #883 review
            # round 8).  The placeholder keeps the statement's token shape,
            # so `tlbi <something>` still reads as a `tlbi` and
            # `concat!("mrs {}, ", $reg)` still reads as an `mrs`.
            text += "x"
            if not text[:-1].rstrip() or text[:-1].rstrip().endswith((";", "\\n", "\n")):
                # ... and where the non-literal could supply the MNEMONIC
                # itself, no placeholder can stand in for it: report.
                unresolvable = True
        if unresolvable:
            lineno = out.count("\n", 0, match.start()) + 1
            problems.append(
                f"line {lineno}: `concat!` whose non-literal argument could "
                f"begin an assembly statement, so this gate cannot see what "
                f"instruction is emitted. Put the mnemonic in a string "
                f"literal, so the containment check reads it."
            )
        folded = '"' + text + '"'
        # Pad so the view stays byte-aligned with the original file.
        out = out[: match.start()] + folded.ljust(len(span)) + out[index + 1 :]


def strip_hash(text: str) -> str:
    """Blank `#` line comments (allowlist file)."""
    return "\n".join(line.split("#", 1)[0] for line in text.splitlines())


def enclosing_rust_fn(code: str, offset: int) -> str:
    """Name of the INNERMOST `fn` whose body contains `offset`.

    Delegated to `rust_code_view.enclosing_fn`, which brace-matches bodies.
    The first version took "the last `fn` declared at or before `offset`",
    which is a presence check standing in for a containment relation: a
    module-scope item such as

        static BAD: fn() = crate::tlb::tlbi_vmalle1;

    placed after an allowlisted function was attributed to that function and
    inherited an exemption written for somebody else's body (PR #883 review
    round 3).  A module-scope reference now reports `<file scope>`, which no
    allowlist entry can match -- the fail-closed answer, and the true one.
    """
    return rust_code_view.enclosing_fn(code, offset)


# Lean has no braces, so a declaration runs to the next top-level opener.
# These are the forms that OPEN one and carry a name this gate can attribute
# a reference to.
LEAN_NAMED_DECL_KEYWORDS = (
    "def", "abbrev", "theorem", "lemma", "instance", "opaque", "axiom",
    "structure", "inductive", "class", "initialize", "builtin_initialize",
    "macro", "elab", "syntax", "notation", "alias",
)
# Column-0 forms that are NOT declarations: they neither open a body nor end
# the previous one for attribution purposes.
# `mutual` is deliberately ABSENT from this tuple: it opens a block of
# indented declarations that the column-0 scan cannot see, so classifying it
# as a non-declaration let everything inside inherit the PRECEDING
# declaration's allowlist entry (PR #883 review round 10).  Falling through
# to the unknown-form branch ends the previous declaration and reports
# `<file scope>` inside the block -- the conservative attribution the review
# asked for, and the one no allowlist entry can match.
LEAN_NON_DECL_KEYWORDS = (
    "import", "open", "namespace", "end", "section", "variable", "variables",
    "set_option", "attribute", "export", "universe", "local", "scoped",
    "deriving", "where", "in", "run_cmd", "example",
    "macro_rules", "elab_rules", "declare_syntax_cat", "binder_predicate",
)
LEAN_MODIFIERS = (
    "private", "protected", "partial", "noncomputable", "unsafe", "nonrec",
    "@",
)
_LEAN_TOP_LEVEL_RE = re.compile(r"^(\S.*)$", re.MULTILINE)
_LEAN_WORD_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.!?]*")


def lean_declaration_boundaries(code: str) -> list[tuple[str | None, int]]:
    """Every top-level declaration opener as ``(name or None, offset)``.

    Lean bodies are delimited by indentation, so a declaration owns every
    offset from its opener until the next one.  `None` marks a boundary
    this scanner cannot name -- and that is the point of returning it: the
    first version enumerated a fixed keyword set and took "the last
    declaration at or before the offset", so a form it did not know simply
    was not a boundary and everything inside it inherited the PRECEDING
    declaration's allowlist entry.  `initialize bad : Unit <- ffiTlbiAll`
    placed after an allowlisted `def` did exactly that (PR #883 review
    round 4) -- the same defect fixed on the Rust side one round earlier
    and left standing here.

    So an unrecognised column-0 word still ENDS the previous declaration,
    and `enclosing_lean_decl` reports `<file scope>` inside it: no
    allowlist entry can match, which is the fail-closed answer and the
    honest one, since the scanner genuinely does not know whose body it is.
    """
    boundaries: list[tuple[str | None, int]] = []
    for line_match in _LEAN_TOP_LEVEL_RE.finditer(code):
        line, start = line_match.group(1), line_match.start()
        words = _LEAN_WORD_RE.findall(line)
        stripped = line.lstrip()
        # Attribute lines (`@[extern "..."]`) and modifiers precede the
        # keyword; skip over them to find it.
        index = 0
        if stripped.startswith("@"):
            close = line.find("]")
            if close < 0:
                continue  # attribute continues on the next line
            remainder = line[close + 1 :].strip()
            if not remainder:
                continue  # keyword is on a following line
            words = _LEAN_WORD_RE.findall(remainder)
        while index < len(words) and words[index] in LEAN_MODIFIERS:
            index += 1
        if index >= len(words):
            continue
        keyword = words[index]
        if keyword in LEAN_NON_DECL_KEYWORDS:
            continue
        if keyword in LEAN_NAMED_DECL_KEYWORDS:
            name = words[index + 1] if index + 1 < len(words) else None
            boundaries.append((name, start))
        else:
            # An unknown column-0 form. It may be a declaration this
            # scanner does not know, so it ends the previous one and is
            # reported unnamed rather than silently extending it.
            boundaries.append((None, start))
    return boundaries


def enclosing_lean_decl(code: str, offset: int) -> str:
    """Name of the Lean declaration whose span contains `offset`."""
    name = None
    for candidate, start in lean_declaration_boundaries(code):
        if start > offset:
            break
        name = candidate
    return name if name else "<file scope>"


def load_allowlist(root: str) -> tuple[set[str], list[str]]:
    path = os.path.join(root, ALLOWLIST)
    try:
        with open(path, encoding="utf-8") as handle:
            raw = handle.read()
    except OSError:
        return set(), [
            f"{ALLOWLIST}: missing. It registers the call sites that are "
            f"legitimately local; without it every local TLBI use is "
            f"unattributable."
        ]
    entries = set()
    problems: list[str] = []
    for lineno, line in enumerate(strip_hash(raw).splitlines(), start=1):
        entry = line.strip()
        if not entry:
            continue
        if "::" not in entry:
            problems.append(
                f"{ALLOWLIST}:{lineno}: `{entry}` is not "
                f"`<path>::<symbol>`."
            )
            continue
        entries.add(entry)
    return entries, problems


def walk(root: str, rel_dir: str, suffixes: tuple[str, ...]) -> list[str]:
    base = os.path.join(root, rel_dir)
    found: list[str] = []
    for dirpath, _dirnames, filenames in os.walk(base):
        for name in sorted(filenames):
            if name.endswith(suffixes):
                full = os.path.join(dirpath, name)
                found.append(os.path.relpath(full, root).replace(os.sep, "/"))
    return sorted(found)


def read(root: str, rel: str) -> str:
    with open(os.path.join(root, rel), encoding="utf-8") as handle:
        return handle.read()


def check_containment(root: str) -> list[str]:
    """Only `tlb.rs` may emit a `tlbi` instruction."""
    problems: list[str] = []
    for rel in walk(root, RUST_SRC, (".rs", ".S")):
        if rel == TLB_MODULE:
            continue
        text = read(root, rel)
        code = strip_rust(text) if rel.endswith(".rs") else strip_asm(text)
        if rel.endswith(".rs"):
            code, concat_problems = resolve_template_macros(code)
            problems += [f"{rel}:{note}" for note in concat_problems]
        for match in TLBI_MNEMONIC_RE.finditer(code):
            lineno = code.count("\n", 0, match.start()) + 1
            problems.append(
                f"{rel}:{lineno}: emits a `tlbi` instruction outside "
                f"`{TLB_MODULE}`. Every TLBI must go through a `tlb.rs` "
                f"wrapper, which chooses the broadcast scope and emits the "
                f"mandatory DSB/ISB bracket (ARM ARM D8.11); a bare "
                f"instruction has neither."
            )
    return problems


def strip_asm(text: str) -> str:
    """Blank `//` AND `/* */` comments in a `.S` source, byte-aligned.

    Deliberately NOT `strip_rust`: in assembly a `//` opens a comment
    wherever it appears, with no Rust string literals to protect, and
    routing `.S` through the quote-aware Rust view would let a stray `"`
    swallow a later real comment -- or make a commented-out `tlbi` read as
    live code.

    But the grammar is the C preprocessor's, not just `//`.  The first
    version of this function asserted that "the `.S` sources use `//`
    exclusively", which is a claim about the tree's current CONTENT, not a
    property of the language -- and the assembler does not share it.
    `tlbi/* maintenance */ vmalle1` preprocesses to `tlbi vmalle1` and is
    emitted, while a `//`-only view keeps the comment and the mnemonic
    regex no longer matches across it (PR #883 review round 4).  Comments
    are blanked to spaces rather than removed, which also splices the
    mnemonic back together for the scanner exactly as `cpp` does for the
    assembler.

    C block comments do not nest, unlike Rust's; an unterminated one runs
    to end of file, which is what the preprocessor does with it too.
    """
    out = list(text)
    index, length = 0, len(text)
    while index < length:
        if text.startswith("//", index):
            end = text.find("\n", index)
            end = length if end < 0 else end
        elif text.startswith("/*", index):
            close = text.find("*/", index + 2)
            end = length if close < 0 else close + 2
        else:
            index += 1
            continue
        for position in range(index, end):
            if out[position] != "\n":
                out[position] = " "
        index = end
    return "".join(out)


# A `tlbi` mnemonic's operation, e.g. `vae1is` in `tlbi vae1is, {0}`.
# The broadcast variants are exactly those whose operation ends in `is`
# (inner shareable) or `os` (outer shareable); everything else invalidates
# only the calling PE.
TLBI_OPERATION_RE = re.compile(
    r'(?:^|[\s;"])tlbi\s+([a-z0-9]+)', re.IGNORECASE
)


def local_emitters_in_tlb_module(root: str) -> tuple[set[str], list[str]]:
    """Functions in `tlb.rs` that emit a NON-broadcast `tlbi`, derived.

    `LOCAL_WRAPPERS` is an enumeration, and an enumeration cannot see a
    wrapper that does not exist yet.  Adding

        pub fn flush_entry(v: u64) {
            unsafe { asm!("tlbi vae1, {0}", in(reg) v); }
        }

    to `tlb.rs` and calling it from `vspace.rs` bypassed the gate entirely:
    the emission was skipped because it is inside the trusted module, and
    the call matched nothing because `flush_entry` is not a name the list
    knows (PR #883 review round 4).  The containment rule and the allowlist
    rule between them assumed the module's local surface was closed, and
    nothing checked that.

    So the set is derived from what the module actually emits, and the
    caller pins it against `LOCAL_WRAPPERS`.  Read from the STRING-KEEPING
    view, since the mnemonic is `asm!` template content.
    """
    text = read(root, TLB_MODULE)
    # The SAME resolver the containment check uses.  Applying it there and
    # not here left `flush_entry` -- a new local emitter written as
    # `asm!(concat!("tlbi ", "vae1"))` -- underivable: containment skips
    # `tlb.rs`, and this inventory read the unresolved fragments, so the
    # emitter was never registered and its callers were never checked (PR
    # #883 review round 10).  Sixth instance of a resolver wired into one
    # of its call sites.
    code, template_problems = resolve_template_macros(rust_code_view.code(text))
    bodies = rust_code_view.fn_bodies(text)
    emitters: set[str] = set()
    problems: list[str] = [f"{TLB_MODULE}:{note}" for note in template_problems]
    for match in TLBI_OPERATION_RE.finditer(code):
        operation = match.group(1).lower()
        if operation.endswith(("is", "os")):
            continue
        owner = rust_code_view.enclosing_fn(text, match.start(), bodies=bodies)
        if owner == rust_code_view.FILE_SCOPE:
            lineno = code.count("\n", 0, match.start()) + 1
            problems.append(
                f"{TLB_MODULE}:{lineno}: emits a non-broadcast `tlbi "
                f"{operation}` outside any function, so this gate cannot "
                f"attribute it to a wrapper. Move the emission into a "
                f"named wrapper."
            )
            continue
        emitters.add(owner)
    return emitters, problems


def check_local_wrapper_inventory(root: str) -> list[str]:
    """Every local emitter in `tlb.rs` must be a registered local wrapper."""
    emitters, problems = local_emitters_in_tlb_module(root)
    unknown = sorted(emitters - set(LOCAL_WRAPPERS))
    if unknown:
        problems.append(
            f"{TLB_MODULE}: {', '.join(unknown)} emit(s) a non-broadcast "
            f"`tlbi` but is not in this gate's LOCAL_WRAPPERS list, so "
            f"callers of it are not checked against {ALLOWLIST}.\n"
            f"      A new local emitter is invisible twice over: the "
            f"emission is skipped because it is inside `{TLB_MODULE}`, and "
            f"the call site matches no known wrapper name. Add it to "
            f"LOCAL_WRAPPERS (and register any legitimate caller), or make "
            f"it broadcast."
        )
    return problems


def local_ffi_exports(root: str) -> set[str]:
    """`ffi_tlbi_*` exports that transitively reach a LOCAL wrapper.

    CRATE-WIDE, not per module.  A previous cut computed the closure inside
    `ffi.rs` only and argued that a call *out* of the module was covered by
    the Rust allowlist check on the callee's module.  That reasoning was
    wrong, and the review was right to press it: the allowlist establishes
    that `helpers::local_flush` may reference a local wrapper -- it says
    nothing about an FFI export that re-exposes that helper to Lean, which
    is a different obligation on a different symbol.  So
    `ffi_tlbi_sneaky -> helpers::local_flush -> tlbi_vmalle1` slipped
    through with its Lean binding unregistered (PR #883 review round 8).

    The call graph now spans every `.rs` file under the HAL's `src/`.
    Edges are resolved by bare callee name, and same-named functions in
    different modules have their bodies UNIONED, so any definition's
    wrapper reference counts for the name.  That over-approximates -- it
    can mark an export local that is not -- which fails closed, the safe
    direction and the one this gate should err in.  Keeping only one of the
    duplicates instead would be an arbitrary choice, not an approximation,
    and a decoy definition displaced the real one when this code tried it.
    """
    # Same-named functions in different modules are UNIONED, not resolved.
    # A previous cut kept "the longer body" and called that an
    # over-approximation; it is not -- it is an arbitrary choice, and a
    # longer unrelated `decoy::local_flush` displaced the short
    # `helpers::local_flush` that actually reached a wrapper (PR #883
    # review round 9).  Concatenating every definition of a name is the
    # over-approximation the docstring claimed: any definition's wrapper
    # reference, and any definition's call edge, counts for the name.
    bodies: dict[str, list[str]] = {}
    signatures_by_file: dict[str, str] = {}
    for rel in walk(root, RUST_SRC, (".rs",)):
        text = read(root, rel)
        code = rust_code_view.code_no_strings(text)
        signatures_by_file[rel] = rust_code_view.code(text)
        for name, start, end in rust_code_view.fn_bodies(text):
            bodies.setdefault(name, []).append(code[start:end])

    merged = {name: "\n".join(parts) for name, parts in bodies.items()}
    direct = {
        name for name, body in merged.items() if LOCAL_WRAPPER_RE.search(body)
    }
    calls = {
        name: {
            callee
            for callee in merged
            if callee != name and re.search(rf"\b{re.escape(callee)}\s*\(", body)
        }
        for name, body in merged.items()
    }

    reaching = set(direct)
    changed = True
    while changed:
        changed = False
        for name, callees in calls.items():
            if name not in reaching and callees & reaching:
                reaching.add(name)
                changed = True

    local: set[str] = set()
    for signatures in signatures_by_file.values():
        for match in _FFI_TLBI_EXPORT_RE.finditer(signatures):
            if match.group(1) in reaching:
                local.add(match.group(1))
    return local


def _lean_binding_name(export: str) -> str:
    """`ffi_tlbi_by_asid` -> `ffiTlbiByAsid`, the Lean binder convention."""
    head, *rest = export.split("_")
    return head + "".join(part.capitalize() for part in rest)


def check_lean_binding_inventory(root: str) -> list[str]:
    """Every local `ffi_tlbi_*` export has its Lean binding registered."""
    expected = {_lean_binding_name(e) for e in local_ffi_exports(root)}
    missing = sorted(expected - set(LEAN_LOCAL_BINDINGS))
    if not missing:
        return []
    return [
        f"{FFI_MODULE}: the local FFI export(s) bound as "
        f"{', '.join(missing)} are not in this gate's LEAN_LOCAL_BINDINGS "
        f"list, so Lean callers of them are not checked against "
        f"{ALLOWLIST}.\n"
        f"      A local export reaches a non-broadcast TLBI; its Lean "
        f"binding must be registered here (and any legitimate caller in "
        f"{ALLOWLIST}), or the export must route through "
        f"`tlbi_for_sharing`."
    ]


def check_rust_allowlist(root: str, allowed: set[str]) -> tuple[list[str], set[str]]:
    """Local-wrapper calls outside `tlb.rs` must be registered."""
    problems: list[str] = []
    used: set[str] = set()
    for rel in walk(root, RUST_SRC, (".rs",)):
        if rel == TLB_MODULE:
            continue
        code = strip_rust(read(root, rel))
        bodies = rust_code_view.fn_bodies(code)
        for match in LOCAL_WRAPPER_RE.finditer(code):
            fn = rust_code_view.enclosing_fn(code, match.start(), bodies=bodies)
            site = f"{rel}::{fn}"
            if site in allowed:
                used.add(site)
                continue
            lineno = code.count("\n", 0, match.start()) + 1
            problems.append(
                f"{rel}:{lineno}: `{match.group(1)}` referenced from `{fn}`, "
                f"which is not in {ALLOWLIST}.\n"
                f"      A non-broadcast TLBI invalidates only the calling "
                f"PE. Under SMP another core keeps walking the translation "
                f"this reference reaches. Route through "
                f"`tlb::tlbi_for_sharing(domain, op)` — or, if the calling "
                f"PE really is the only one whose TLB needs the entry gone, "
                f"register `{site}` in {ALLOWLIST} with the reason."
            )
    return problems, used


LEAN_EXTERN_TLBI = re.compile(r'@\[\s*extern\s+"ffi_tlbi_[a-z_]*"\s*\]')
LEAN_BINDER = re.compile(
    r"^\s*(?:private\s+|protected\s+|partial\s+|noncomputable\s+|unsafe\s+)*"
    r"(?:opaque|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_'.!?]*)"
)


def lean_extern_declaration_lines(code: str) -> set[int]:
    """1-based line numbers that DECLARE an `@[extern "ffi_tlbi_*"]` binding.

    A declaration is an `opaque`/`def` binder on the attribute's own line or
    on one of the lines following it, before any other binder intervenes.
    Returning line numbers rather than a per-file flag keeps the exemption
    to the declaration itself: a *call* elsewhere in the same file is still
    checked, which a whole-file flag could not do.
    """
    lines = code.splitlines()
    declared: set[int] = set()
    for index, line in enumerate(lines):
        if not LEAN_EXTERN_TLBI.search(line):
            continue
        # The binder may sit on the attribute's line or below it; scan a
        # short window so an attribute with no binder cannot exempt the
        # rest of the file.
        for offset in range(0, 4):
            if index + offset >= len(lines):
                break
            if LEAN_BINDER.match(lines[index + offset]):
                declared.add(index + offset + 1)
                break
    return declared


def check_lean_allowlist(root: str, allowed: set[str]) -> tuple[list[str], set[str]]:
    """Lean references to the local FFI bindings must be registered."""
    problems: list[str] = []
    used: set[str] = set()
    binding_re = re.compile(r"\b(" + "|".join(LEAN_LOCAL_BINDINGS) + r")\b")
    for rel in walk(root, LEAN_ROOT, (".lean",)):
        code = lean_code_view.strip(read(root, rel))
        # The declaration sites -- `opaque ffiTlbiAll` and friends under an
        # `@[extern "ffi_tlbi_*"]` attribute -- are what every other
        # module's reference resolves to; declaring a binding is not
        # calling it.  Resolved PER OCCURRENCE and over the comment-free
        # code view, because both looser forms fail open: a whole-file flag
        # exempts every real reference in the file that happens to declare
        # one, and reading raw text lets a docstring quoting the attribute
        # set that flag (PR #883 review) -- in the gate written to enforce
        # "gates read code, prose reads prose".
        declaration_lines = lean_extern_declaration_lines(code)
        for match in binding_re.finditer(code):
            if code.count("\n", 0, match.start()) + 1 in declaration_lines:
                continue
            decl = enclosing_lean_decl(code, match.start())
            site = f"{rel}::{decl}"
            if site in allowed:
                used.add(site)
                continue
            lineno = code.count("\n", 0, match.start()) + 1
            problems.append(
                f"{rel}:{lineno}: `{match.group(1)}` referenced from "
                f"`{decl}`, which is not in {ALLOWLIST}.\n"
                f"      These bindings reach the LOCAL TLBI wrappers. "
                f"Production kernel code invalidates through "
                f"`Architecture.tlbiForSharing`, which routes to the IS or "
                f"OS broadcast per `PlatformBinding.sharingDomain`."
            )
    return problems, used


def check_stale_entries(allowed: set[str], used: set[str]) -> list[str]:
    stale = sorted(allowed - used)
    if not stale:
        return []
    return [
        f"{ALLOWLIST}: {len(stale)} entr{'y' if len(stale) == 1 else 'ies'} "
        f"no longer match{'es' if len(stale) == 1 else ''} a call site: "
        f"{', '.join(stale)}.\n"
        f"      An allowlist that outlives its call sites stops describing "
        f"the tree and starts pre-authorising code nobody reviewed. Remove "
        f"the entr{'y' if len(stale) == 1 else 'ies'}."
    ]


def run_checks(root: str) -> list[str]:
    allowed, problems = load_allowlist(root)
    problems += check_containment(root)
    problems += check_local_wrapper_inventory(root)
    problems += check_lean_binding_inventory(root)
    rust_problems, rust_used = check_rust_allowlist(root, allowed)
    problems += rust_problems
    lean_problems, lean_used = check_lean_allowlist(root, allowed)
    problems += lean_problems
    problems += check_stale_entries(allowed, rust_used | lean_used)
    return problems


# ---------------------------------------------------------------------------
# Self-test.
# ---------------------------------------------------------------------------

BASE_TLB_RS = """
pub fn tlbi_vmalle1() {
    unsafe { core::arch::asm!("tlbi vmalle1", options(nostack)); }
}
pub fn tlbi_vae1(asid: u16, vaddr: u64) {
    unsafe { core::arch::asm!("tlbi vae1, {0}", in(reg) 0u64); }
}
pub fn tlbi_vmalle1is() {
    unsafe { core::arch::asm!("tlbi vmalle1is", options(nostack)); }
}
pub fn tlbi_local(op: u32) { tlbi_vmalle1(); }
pub fn tlbi_for_sharing(d: u32, op: u32) { tlbi_vmalle1is(); }
"""

BASE_MMU_RS = """
fn enable_mmu() {
    crate::tlb::tlbi_vmalle1();
}
"""

BASE_OTHER_RS = """
fn unmap_page(asid: u16, vaddr: u64) {
    crate::tlb::tlbi_for_sharing(0, 1);
}
"""

# The declaration under test is deliberately NOT the first thing in the
# fixture, and what precedes it is deliberately not a comment.  A matcher
# anchored only at offset 0 still reaches a declaration preceded by nothing
# but comments, because `lean_code_view.strip` blanks comments to whitespace
# and `^\s*` walks straight through it — which is exactly how the gate's
# first version passed its own self-test while reporting `<file scope>` for
# every real declaration in the tree.
BASE_LEAN = """import SeLe4n.Platform.FFI

namespace SeLe4n.Kernel.Concurrency

/-- An earlier declaration, so the one under test is not reachable from
    offset 0 by whitespace alone. -/
def unrelatedEarlierDecl : BaseIO Unit :=
  pure ()

/-- SM7.B.7 self-service arm: this core discharges its own outstanding
    shootdown obligation. -/
def tlbiLocalFullFlush : BaseIO Unit :=
  SeLe4n.Platform.FFI.ffiTlbiAll

end SeLe4n.Kernel.Concurrency
"""

BASE_FFI_LEAN = """
@[extern "ffi_tlbi_all"]
opaque ffiTlbiAll : BaseIO Unit
@[extern "ffi_tlbi_for_sharing"]
opaque ffiTlbiForSharing : UInt32 → UInt32 → BaseIO Unit
"""

BASE_ALLOWLIST = """# fixture allowlist
rust/sele4n-hal/src/mmu.rs::enable_mmu
rust/sele4n-hal/src/ffi.rs::ffi_tlbi_all
SeLe4n/Kernel/Concurrency/Runtime.lean::tlbiLocalFullFlush
"""


BASE_FFI_RS = """
#[no_mangle]
pub extern "C" fn ffi_tlbi_all() {
    crate::tlb::tlbi_vmalle1();
}

#[no_mangle]
pub extern "C" fn ffi_tlbi_for_sharing(domain: u32, op: u32) {
    crate::tlb::tlbi_for_sharing(domain, op);
}
"""


def fixture() -> dict[str, str]:
    return {
        TLB_MODULE: BASE_TLB_RS,
        FFI_MODULE: BASE_FFI_RS,
        f"{RUST_SRC}/mmu.rs": BASE_MMU_RS,
        f"{RUST_SRC}/vspace.rs": BASE_OTHER_RS,
        f"{RUST_SRC}/boot.S": "// no tlbi here\n_start:\n    nop\n",
        "SeLe4n/Kernel/Concurrency/Runtime.lean": BASE_LEAN,
        "SeLe4n/Platform/FFI.lean": BASE_FFI_LEAN,
        ALLOWLIST: BASE_ALLOWLIST,
    }


def write_tree(root: str, files: dict[str, str]) -> None:
    for rel, content in files.items():
        path = os.path.join(root, rel)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as handle:
            handle.write(content)


# The checks `run_checks` performs, by id.  Each must be exercised by at
# least one PRESERVING negative case below; the harness enforces it.
CHECKS = (
    "containment",
    "local_wrapper_inventory",
    "lean_binding_inventory",
    "rust_allowlist",
    "lean_allowlist",
    "stale_entries",
)


class Case:
    """One self-test fixture, tagged with what it proves.

    `mutation` records HOW the fixture differs from the clean baseline:

      * ``"deleting"`` removes or omits the token a check searches for.
        Necessary, and passed by every presence check ever written -- which
        is why it cannot be the only kind.
      * ``"preserving"`` KEEPS that token and breaks only the relation it
        is supposed to stand in: the reference stays but moves outside the
        allowlisted body, the `//` stays but moves inside a string literal,
        the allowlist entry stays and names a symbol that still exists but
        no longer calls anything local.  This is the mutation that finds the
        defect class this repository keeps shipping (CLAUDE.md, "Test a gate
        by breaking the relation, not by deleting the token").

    Writing that rule down did not stop three review rounds from finding
    fifteen more instances, so it is enforced here instead of asserted: the
    harness fails when any check id in `CHECKS` has no preserving case.
    """

    def __init__(
        self,
        label: str,
        files: dict[str, str],
        expect: bool,
        check: str | None = None,
        mutation: str = "deleting",
    ) -> None:
        assert check is None or check in CHECKS, check
        assert mutation in ("none", "deleting", "preserving"), mutation
        self.label = label
        self.files = files
        self.expect = expect
        self.check = check
        self.mutation = mutation


def self_test() -> int:
    cases: list[Case] = []

    cases.append(Case("clean baseline", fixture(), False, mutation="none"))

    unregistered = fixture()
    unregistered[f"{RUST_SRC}/vspace.rs"] = (
        "\nfn unmap_page(asid: u16, vaddr: u64) {\n"
        "    crate::tlb::tlbi_vae1(asid, vaddr);\n}\n"
    )
    cases.append(Case("unregistered local call in Rust", unregistered, True, check="rust_allowlist"))

    via_local = fixture()
    via_local[f"{RUST_SRC}/vspace.rs"] = (
        "\nfn unmap_page(asid: u16, vaddr: u64) {\n"
        "    crate::tlb::tlbi_local(1);\n}\n"
    )
    cases.append(Case("unregistered `tlbi_local` call", via_local, True, check="rust_allowlist"))

    prose_only = fixture()
    prose_only[f"{RUST_SRC}/vspace.rs"] = (
        "\nfn unmap_page(asid: u16, vaddr: u64) {\n"
        "    // never call crate::tlb::tlbi_vae1(asid, vaddr) here\n"
        "    crate::tlb::tlbi_for_sharing(0, 1);\n}\n"
    )
    cases.append(Case("a comment naming the wrapper is not a call", prose_only, False, check="rust_allowlist", mutation="none"))

    broadcast_ok = fixture()
    broadcast_ok[f"{RUST_SRC}/vspace.rs"] = (
        "\nfn unmap_page(asid: u16, vaddr: u64) {\n"
        "    crate::tlb::tlbi_vmalle1is();\n}\n"
    )
    cases.append(Case("the IS broadcast wrapper is never flagged", broadcast_ok, False, check="rust_allowlist", mutation="none"))

    raw_asm = fixture()
    raw_asm[f"{RUST_SRC}/vspace.rs"] = (
        "\nfn unmap_page(asid: u16, vaddr: u64) {\n"
        '    unsafe { core::arch::asm!("tlbi vae1is, {0}", in(reg) 0u64); }\n}\n'
    )
    cases.append(Case("raw `tlbi` in Rust outside tlb.rs", raw_asm, True, check="containment"))

    raw_asm_s = fixture()
    raw_asm_s[f"{RUST_SRC}/boot.S"] = "_start:\n    tlbi vmalle1\n    nop\n"
    cases.append(Case("raw `tlbi` in a .S source", raw_asm_s, True, check="containment"))

    asm_prose = fixture()
    asm_prose[f"{RUST_SRC}/boot.S"] = (
        "// the MMU enable path issues tlbi vmalle1 from Rust\n_start:\n    nop\n"
    )
    cases.append(Case("a .S comment naming tlbi is not an emission", asm_prose, False, check="containment", mutation="none"))

    lean_unregistered = fixture()
    lean_unregistered["SeLe4n/Kernel/Architecture/VSpace.lean"] = (
        "import SeLe4n.Platform.FFI\n\n"
        "def unrelatedEarlierDecl : BaseIO Unit := pure ()\n\n"
        "/-- leading docstring, so the declaration is not on line 1 -/\n"
        "def unmapPage : BaseIO Unit :=\n"
        "  SeLe4n.Platform.FFI.ffiTlbiByVaddr\n"
    )
    cases.append(Case("unregistered Lean local-FFI reference", lean_unregistered, True, check="lean_allowlist"))

    lean_prose = fixture()
    lean_prose["SeLe4n/Kernel/Architecture/VSpace.lean"] = (
        "import SeLe4n.Platform.FFI\n\n"
        "-- never call ffiTlbiByVaddr from here\n"
        "def unmapPage : BaseIO Unit :=\n"
        "  SeLe4n.Platform.FFI.ffiTlbiForSharing 0 1\n"
    )
    cases.append(Case("a Lean comment naming the binding is not a call", lean_prose, False, check="lean_allowlist", mutation="none"))

    # --- The mutation class that finds "presence checked, relation not" ---
    #
    # Each case below KEEPS the token a naive check looks for and breaks
    # the relation the check actually means.  Deleting the token is the
    # easy mutation and every presence check survives it; these are the
    # ones that do not.  A new check here needs at least one.

    aliased_use = fixture()
    aliased_use[f"{RUST_SRC}/vspace.rs"] = (
        "\nuse crate::tlb::tlbi_vae1 as invalidate_local;\n\n"
        "fn unmap_page(asid: u16, vaddr: u64) {\n"
        "    invalidate_local(asid, vaddr);\n}\n"
    )
    cases.append(Case("local wrapper reached through an aliasing `use`", aliased_use, True, check="rust_allowlist", mutation="preserving"))

    fn_pointer = fixture()
    fn_pointer[f"{RUST_SRC}/vspace.rs"] = (
        "\nfn unmap_page(asid: u16, vaddr: u64) {\n"
        "    let invalidate_local = crate::tlb::tlbi_vae1;\n"
        "    invalidate_local(asid, vaddr);\n}\n"
    )
    cases.append(
        Case(
            "local wrapper bound to a function pointer, then called",
            fn_pointer,
            True,
            check="rust_allowlist",
            mutation="preserving",
        )
    )

    lean_attr_in_prose = fixture()
    lean_attr_in_prose["SeLe4n/Kernel/Architecture/VSpace.lean"] = (
        "import SeLe4n.Platform.FFI\n\n"
        "/-- Resolves against `@[extern \"ffi_tlbi_by_vaddr\"] ffiTlbiByVaddr`,\n"
        "    quoted here so the docstring cannot exempt this file. -/\n"
        "def unmapPage : BaseIO Unit :=\n"
        "  SeLe4n.Platform.FFI.ffiTlbiByVaddr\n"
    )
    cases.append(
        Case(
            "a docstring quoting the extern attribute does not exempt the file",
            lean_attr_in_prose,
            True,
            check="lean_allowlist",
            mutation="preserving",
        )
    )

    lean_declarer_also_calls = fixture()
    lean_declarer_also_calls["SeLe4n/Platform/FFI.lean"] = (
        BASE_FFI_LEAN
        + "\ndef strayLocalFlush : BaseIO Unit :=\n  ffiTlbiAll\n"
    )
    cases.append(
        Case(
            "the declaring module's own unregistered CALL is still checked",
            lean_declarer_also_calls,
            True,
            check="lean_allowlist",
            mutation="preserving",
        )
    )

    # The reference sits at MODULE scope, after the allowlisted `enable_mmu`.
    # Every token a presence check looks for is still there -- the wrapper
    # name, the allowlisted function, its registration -- and only the
    # containment relation is false: the `static` is in no function's body.
    # A last-declaration-wins scan hands it `enable_mmu`'s exemption.
    module_scope = fixture()
    module_scope[f"{RUST_SRC}/mmu.rs"] = (
        BASE_MMU_RS
        + "\nstatic INVALIDATE_LOCAL: fn() = crate::tlb::tlbi_vmalle1;\n"
    )
    cases.append(
        Case(
            "a module-scope reference does not inherit the preceding fn's entry",
            module_scope,
            True,
            check="rust_allowlist",
            mutation="preserving",
        )
    )

    # The `tlbi` is emitted, and a `//` is present -- inside a sibling
    # template string, where it is an ASSEMBLER comment on its own line and
    # does not reach the next one.  A line-based stripper truncates there
    # and deletes the instruction from the view.
    asm_comment_line = fixture()
    asm_comment_line[f"{RUST_SRC}/vspace.rs"] = (
        "\nfn unmap_page(asid: u16, vaddr: u64) {\n"
        '    unsafe { core::arch::asm!("// invalidate", "tlbi vae1, {0}", '
        "in(reg) 0u64); }\n}\n"
    )
    cases.append(
        Case(
            "a `//` inside an asm template does not hide the next template line",
            asm_comment_line,
            True,
            check="containment",
            mutation="preserving",
        )
    )

    # The entry's path exists and its symbol exists; what is gone is the
    # local reference that made the exemption mean anything.  An entry
    # checked only for "does this file/symbol exist" survives this.
    stale_but_resolvable = fixture()
    stale_but_resolvable[f"{RUST_SRC}/mmu.rs"] = BASE_MMU_RS.replace(
        "crate::tlb::tlbi_vmalle1()", "crate::tlb::tlbi_vmalle1is()"
    )
    cases.append(
        Case(
            "a registered site whose local call became a broadcast is stale",
            stale_but_resolvable,
            True,
            check="stale_entries",
            mutation="preserving",
        )
    )

    # A NEW local emitter inside the trusted module, called under a name
    # the wrapper list does not know.  Both tokens a presence check looks
    # for are intact -- the module is still exempt from containment, and no
    # known wrapper name appears at the call site -- and the emitter is
    # invisible twice over.
    new_emitter = fixture()
    new_emitter[TLB_MODULE] = BASE_TLB_RS + (
        "\npub fn flush_entry(vaddr: u64) {\n"
        '    unsafe { core::arch::asm!("tlbi vae1, {0}", in(reg) vaddr); }\n}\n'
    )
    new_emitter[f"{RUST_SRC}/vspace.rs"] = (
        "\nfn unmap_page(vaddr: u64) {\n"
        "    crate::tlb::flush_entry(vaddr);\n}\n"
    )
    cases.append(
        Case(
            "a new local emitter in tlb.rs is not silently trusted",
            new_emitter,
            True,
            check="local_wrapper_inventory",
            mutation="preserving",
        )
    )

    # A broadcast emitter added the same way must NOT be reported: the
    # inventory check exists to find LOCAL emitters, and a check that only
    # ever tightens ends up rejecting correct code.
    new_broadcast = fixture()
    new_broadcast[TLB_MODULE] = BASE_TLB_RS + (
        "\npub fn flush_entry_broadcast(vaddr: u64) {\n"
        '    unsafe { core::arch::asm!("tlbi vae1is, {0}", in(reg) vaddr); }\n}\n'
    )
    cases.append(
        Case(
            "a new BROADCAST emitter in tlb.rs is accepted",
            new_broadcast,
            False,
            check="local_wrapper_inventory",
            mutation="none",
        )
    )

    # An `initialize` block after the allowlisted definition.  The
    # allowlisted name, its registration and the binding are all present;
    # only the reference's owner changed, and a keyword the scanner does
    # not know must not silently extend the previous declaration.
    lean_unknown_form = fixture()
    lean_unknown_form["SeLe4n/Kernel/Concurrency/Runtime.lean"] = (
        BASE_LEAN
        + "\ninitialize badLocalFlush : Unit \u2190 SeLe4n.Platform.FFI.ffiTlbiAll\n"
    )
    cases.append(
        Case(
            "an `initialize` after an allowlisted def does not inherit its entry",
            lean_unknown_form,
            True,
            check="lean_allowlist",
            mutation="preserving",
        )
    )

    # A `/* */` splitting the mnemonic in a `.S` source.  The mnemonic is
    # present and so is the comment; preprocessing splices them and the
    # assembler emits the instruction.
    asm_block_comment = fixture()
    asm_block_comment[f"{RUST_SRC}/boot.S"] = (
        "_start:\n    tlbi/* maintenance */ vmalle1\n    ret\n"
    )
    cases.append(
        Case(
            "a `/* */` inside a .S mnemonic does not hide the instruction",
            asm_block_comment,
            True,
            check="containment",
            mutation="preserving",
        )
    )

    # A new LOCAL ffi export whose Lean binding is not registered: the
    # export exists, the binding exists, callers exist -- only the gate's
    # knowledge of which bindings are local is stale.
    new_ffi_export = fixture()
    new_ffi_export[FFI_MODULE] = BASE_FFI_RS + (
        '\n#[no_mangle]\npub extern "C" fn ffi_tlbi_by_page(asid: u16, vaddr: u64) {\n'
        "    crate::tlb::tlbi_vale1(asid, vaddr);\n}\n"
    )
    new_ffi_export[ALLOWLIST] = (
        BASE_ALLOWLIST + "rust/sele4n-hal/src/ffi.rs::ffi_tlbi_by_page\n"
    )
    cases.append(
        Case(
            "a new local FFI export must have its Lean binding registered",
            new_ffi_export,
            True,
            check="lean_binding_inventory",
            mutation="preserving",
        )
    )

    # ... and a new BROADCAST export must not be reported.
    new_broadcast_export = fixture()
    new_broadcast_export[FFI_MODULE] = BASE_FFI_RS + (
        '\n#[no_mangle]\npub extern "C" fn ffi_tlbi_by_page(asid: u16, vaddr: u64) {\n'
        "    crate::tlb::tlbi_vale1is(asid, vaddr);\n}\n"
    )
    cases.append(
        Case(
            "a new broadcast FFI export needs no Lean binding entry",
            new_broadcast_export,
            False,
            check="lean_binding_inventory",
            mutation="none",
        )
    )

    # A local FFI export that reaches the wrapper THROUGH a helper: its own
    # body holds no wrapper name, so a one-level scan omits it.
    transitive_ffi = fixture()
    transitive_ffi[FFI_MODULE] = BASE_FFI_RS + (
        "\nfn invalidate_helper(asid: u16, vaddr: u64) {\n"
        "    crate::tlb::tlbi_vale1(asid, vaddr);\n}\n"
        '\n#[no_mangle]\npub extern "C" fn ffi_tlbi_by_page(asid: u16, vaddr: u64) {\n'
        "    invalidate_helper(asid, vaddr);\n}\n"
    )
    transitive_ffi[ALLOWLIST] = (
        BASE_ALLOWLIST + "rust/sele4n-hal/src/ffi.rs::invalidate_helper\n"
    )
    cases.append(
        Case(
            "an FFI export reaching a wrapper through a helper is still local",
            transitive_ffi,
            True,
            check="lean_binding_inventory",
            mutation="preserving",
        )
    )

    # `concat!` composes ONE template line, so the instruction is emitted.
    concat_template = fixture()
    concat_template[f"{RUST_SRC}/vspace.rs"] = (
        "\nfn unmap_page() {\n"
        '    unsafe { core::arch::asm!(concat!("tlbi ", "vmalle1")); }\n}\n'
    )
    cases.append(
        Case(
            "a concat!-composed asm template is still an emission",
            concat_template,
            True,
            check="containment",
            mutation="preserving",
        )
    )

    # ... and the sibling form must NOT be reported: separate template
    # arguments are separate LINES, joined with a newline by `asm!`, so
    # they do not compose one instruction.
    separate_lines = fixture()
    separate_lines[f"{RUST_SRC}/vspace.rs"] = (
        "\nfn unmap_page() {\n"
        '    unsafe { core::arch::asm!("dsb ish", "isb"); }\n}\n'
    )
    cases.append(
        Case(
            "separate asm template lines are not concatenated",
            separate_lines,
            False,
            check="containment",
            mutation="none",
        )
    )

    # A register-macro `concat!` whose non-literal supplies an OPERAND, not
    # a mnemonic, must be accepted -- the instruction is fully visible.
    operand_concat = fixture()
    operand_concat[f"{RUST_SRC}/vspace.rs"] = (
        "\nmacro_rules! read_reg {\n    ($reg:literal) => {\n"
        '        unsafe { core::arch::asm!(concat!("mrs {}, ", $reg), out(reg) v) }\n'
        "    };\n}\n"
    )
    cases.append(
        Case(
            "a concat! supplying only an operand is not unresolvable",
            operand_concat,
            False,
            check="containment",
            mutation="none",
        )
    )

    # An FFI export reaching a wrapper through a helper in ANOTHER module.
    # The helper is registered, so the Rust allowlist is satisfied -- and
    # that says nothing about the export re-exposing it to Lean.
    cross_module_ffi = fixture()
    cross_module_ffi[f"{RUST_SRC}/helpers.rs"] = (
        "pub fn local_flush() {\n    crate::tlb::tlbi_vmalle1();\n}\n"
    )
    cross_module_ffi[FFI_MODULE] = BASE_FFI_RS + (
        '\n#[no_mangle]\npub extern "C" fn ffi_tlbi_sneaky() {\n'
        "    crate::helpers::local_flush();\n}\n"
    )
    cross_module_ffi[ALLOWLIST] = (
        BASE_ALLOWLIST + "rust/sele4n-hal/src/helpers.rs::local_flush\n"
    )
    cases.append(
        Case(
            "an FFI export reaching a wrapper in another module is still local",
            cross_module_ffi,
            True,
            check="lean_binding_inventory",
            mutation="preserving",
        )
    )

    # `concat!("tlbi ", stringify!(vmalle1))` expands to a real
    # instruction; the mnemonic is literal and only the OPERAND is a macro.
    stringify_operand = fixture()
    stringify_operand[f"{RUST_SRC}/vspace.rs"] = (
        "\nfn unmap_page() {\n"
        '    unsafe { core::arch::asm!(concat!("tlbi ", stringify!(vmalle1))); }\n}\n'
    )
    cases.append(
        Case(
            "a concat! whose operand is a macro is still an emission",
            stringify_operand,
            True,
            check="containment",
            mutation="preserving",
        )
    )

    # A DECOY definition of the same name, longer than the real one: with
    # duplicates resolved by picking a single body, the decoy displaces the
    # helper that actually reaches a wrapper.  Both definitions, the
    # export, the call and the registration are all present.
    decoy_duplicate = fixture()
    decoy_duplicate[f"{RUST_SRC}/helpers.rs"] = (
        "pub fn local_flush() {\n    crate::tlb::tlbi_vmalle1();\n}\n"
    )
    decoy_duplicate[f"{RUST_SRC}/decoy.rs"] = (
        "pub fn local_flush() {\n"
        + "    let _padding = 0;\n" * 20
        + "    crate::tlb::tlbi_vmalle1is();\n}\n"
    )
    decoy_duplicate[FFI_MODULE] = BASE_FFI_RS + (
        '\n#[no_mangle]\npub extern "C" fn ffi_tlbi_sneaky() {\n'
        "    crate::helpers::local_flush();\n}\n"
    )
    decoy_duplicate[ALLOWLIST] = (
        BASE_ALLOWLIST + "rust/sele4n-hal/src/helpers.rs::local_flush\n"
    )
    cases.append(
        Case(
            "a decoy definition of the same name does not displace the real one",
            decoy_duplicate,
            True,
            check="lean_binding_inventory",
            mutation="preserving",
        )
    )

    # A new local emitter in `tlb.rs` written with `concat!`: containment
    # skips the module, and the inventory read the unresolved fragments.
    concat_emitter = fixture()
    concat_emitter[TLB_MODULE] = BASE_TLB_RS + (
        "\npub fn flush_entry(vaddr: u64) {\n"
        '    unsafe { core::arch::asm!(concat!("tlbi ", "vae1"), in(reg) vaddr); }\n}\n'
    )
    concat_emitter[f"{RUST_SRC}/vspace.rs"] = (
        "\nfn unmap_page(vaddr: u64) {\n"
        "    crate::tlb::flush_entry(vaddr);\n}\n"
    )
    cases.append(
        Case(
            "a concat!-written local emitter is still derived",
            concat_emitter,
            True,
            check="local_wrapper_inventory",
            mutation="preserving",
        )
    )

    # `stringify!` turns raw tokens into a template with no string literal
    # anywhere in the source.
    stringify_template = fixture()
    stringify_template[f"{RUST_SRC}/vspace.rs"] = (
        "\nfn unmap_page() {\n"
        "    unsafe { core::arch::asm!(stringify!(tlbi vmalle1)); }\n}\n"
    )
    cases.append(
        Case(
            "a stringify!-composed asm template is still an emission",
            stringify_template,
            True,
            check="containment",
            mutation="preserving",
        )
    )

    # A `mutual` block opens indented declarations the column-0 scan cannot
    # see; classifying it as a non-declaration let them inherit the
    # preceding definition's allowlist entry.
    lean_mutual = fixture()
    lean_mutual["SeLe4n/Kernel/Concurrency/Runtime.lean"] = (
        BASE_LEAN
        + "\nmutual\n\ndef hiddenLocalFlush : BaseIO Unit :=\n"
        "  SeLe4n.Platform.FFI.ffiTlbiAll\n\nend\n"
    )
    cases.append(
        Case(
            "a declaration inside `mutual` does not inherit the previous entry",
            lean_mutual,
            True,
            check="lean_allowlist",
            mutation="preserving",
        )
    )

    stale = fixture()
    stale[ALLOWLIST] = BASE_ALLOWLIST + "rust/sele4n-hal/src/gone.rs::gone\n"
    cases.append(Case("allowlist entry with no call site", stale, True, check="stale_entries"))

    no_allowlist = fixture()
    del no_allowlist[ALLOWLIST]
    cases.append(Case("allowlist file missing", no_allowlist, True, check="stale_entries"))

    # A case expected to be CAUGHT must actually differ from the clean
    # fixture.  A mutation that silently no-ops reads as coverage while
    # asserting nothing, so it is checked rather than trusted.
    clean = fixture()
    failures = 0
    for case in cases:
        if case.expect and case.files == clean:
            failures += 1
            print(
                f"[SELF-TEST FAIL] inert mutation, fixture unchanged: "
                f"{case.label}"
            )
            continue
        with tempfile.TemporaryDirectory() as tmp:
            write_tree(tmp, case.files)
            problems = run_checks(tmp)
            if bool(problems) != case.expect:
                failures += 1
                verb = "missed" if case.expect else "false-positived on"
                print(f"[SELF-TEST FAIL] gate {verb}: {case.label}")
                for problem in problems:
                    print(f"                 reported: {problem}")
            else:
                state = "caught" if case.expect else "accepted"
                mark = " [preserving]" if case.mutation == "preserving" else ""
                print(f"[SELF-TEST OK]   {state}: {case.label}{mark}")

    # Every check must be exercised by a mutation that KEEPS its token and
    # breaks only the relation.  Deleting the token is passed by any
    # presence check, so a suite made only of deletions certifies nothing
    # about the property the check is named for -- which is how fifteen
    # fail-open holes reached review across three rounds while every suite
    # reported PASS.  Enforced, not asserted in a comment.
    covered = {
        case.check
        for case in cases
        if case.expect and case.mutation == "preserving" and case.check
    }
    for check in CHECKS:
        if check not in covered:
            failures += 1
            print(
                f"[SELF-TEST FAIL] check `{check}` has no token-preserving "
                f"negative case. Add one that keeps the token the check "
                f"searches for and breaks only its relation (CLAUDE.md, "
                f"\"Test a gate by breaking the relation, not by deleting "
                f"the token\")."
            )

    if failures:
        print(f"\n[FAIL] {failures} self-test case(s) failed")
        return 1
    print(
        f"\n[PASS] {len(cases)} self-test case(s); "
        f"{len(CHECKS)}/{len(CHECKS)} checks have a token-preserving case"
    )
    return 0


def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        return self_test()
    root = os.path.abspath(
        os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
    )
    problems = run_checks(root)
    if problems:
        print("[FAIL] TLBI broadcast discipline (WS-RR RR1.9):")
        for problem in problems:
            print(f"  - {problem}")
        return 1
    print("[PASS] TLBI broadcast discipline intact")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
