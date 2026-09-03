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

Exits 77 (the project's NOT-RUN code) when `nm` is unavailable, so a missing
binutils cannot be scored as a pass.
"""

from __future__ import annotations

import re
import shutil
import subprocess
import sys
from pathlib import Path

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

LEAN_EXPORT = re.compile(r"@\[export\s+([A-Za-z_][A-Za-z0-9_]*)\s*\]")
EXTERN_BLOCK = re.compile(r'extern\s+"C"\s*\{')
EXTERN_FN = re.compile(r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(")
ASM_GLOBAL = re.compile(r"^\s*\.(?:global|globl)\s+([A-Za-z_.$][A-Za-z0-9_.$]*)", re.MULTILINE)
# A label definition: the symbol at the start of a line, followed by `:`.
ASM_LABEL = re.compile(r"^\s*([A-Za-z_.$][A-Za-z0-9_.$]*)\s*:", re.MULTILINE)
# A `cc::Build` source registration in `build.rs`, read over the comment-blanked
# view (string contents kept, since the path IS a string).
CC_FILE_CALL = re.compile(r'\.file\(\s*"([^"]+)"\s*\)')
# The primary's boot install, and the checked platform boot it must call:
# `bootAndInitialiseRPi5`, the generic `bootAndInitialisePlatform` fixed at
# `RPi5Platform` (PR #889 review round 7 — with the generic entry as the callee
# the gate never inspected the platform argument, so an entry booting
# `SimSingleCorePlatform` on the hardware image satisfied it).
BOOT_ENTRY_SYMBOL = "lean_kernel_main"
BOOT_ENTRY_EXPORT = re.compile(r"@\[export\s+lean_kernel_main\s*\]")
BOOT_ENTRY_CALLEE = "bootAndInitialiseRPi5"
# Where a top-level Lean declaration starts, at column 0.
LEAN_DECL_START = re.compile(
    r"^(?:@\[|(?:private |protected |noncomputable |unsafe |partial )*"
    r"(?:def|theorem|abbrev|instance|structure|inductive|class|example|opaque|axiom|"
    r"initialize|builtin_initialize)\b|end\b|namespace\b|section\b|open\b|"
    r"set_option\b|variable\b|universe\b|attribute\b|mutual\b|deriving\b)",
    re.MULTILINE,
)
# A declaration's head — attributes, modifiers, keyword, name — at the start of
# one of the segments `LEAN_DECL_START` delimits.
LEAN_DECL_HEAD = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?P<kw>def|theorem|abbrev|instance|opaque|initialize|builtin_initialize|example)\b"
    r"(?:\s+(?P<name>[^\s:(\[{]+))?"
)
LEAN_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*")
# The kernel-state references, and a mention of one for anything but a read.
KERNEL_STATE_REFS = frozenset({"kernelStateRef", "kernelLabelingContextRef"})
KERNEL_STATE_REF_WRITE = re.compile(
    r"\b(?:kernelStateRef|kernelLabelingContextRef)\b(?!\s*\.\s*get\b)"
)
# A `do` statement after which nothing in the block runs.
LEAN_DIVERGES = re.compile(r"^(?:return|throw|panic!|unreachable!)\b")
# The forms in which a `do` statement *executes* the checked boot: bound with
# `←` (a `let` pattern, or a `match` scrutinee), a bare action, or `discard`.
# `let x := …` binds the action without running it; a call under `if`,
# `match`, `fun` or `=>` on the statement's first line is conditional.
BOOT_ENTRY_EXECUTED = re.compile(
    r"^(?:let\s+(?:(?!:=|\bif\b|\bfun\b|=>|\bmatch\b).)*?←\s*\(?\s*"
    + BOOT_ENTRY_CALLEE + r"\b"
    r"|match\s+←\s*\(?\s*" + BOOT_ENTRY_CALLEE + r"\b"
    r"|\(?\s*" + BOOT_ENTRY_CALLEE + r"\b"
    r"|discard\s*(?:<\|\s*|\(\s*)?" + BOOT_ENTRY_CALLEE + r"\b)"
)
# ...and a term body headed by it.
BOOT_ENTRY_TERM_EXECUTED = re.compile(
    r"^(?:\(?\s*" + BOOT_ENTRY_CALLEE + r"\b"
    r"|discard\s*(?:<\|\s*|\(\s*)?" + BOOT_ENTRY_CALLEE + r"\b)"
)
# The kernel-state installers the derivation must find on the real tree, and
# the readers it must not: a pin, so a rename on either side is loud.
EXPECTED_KERNEL_STATE_WRITERS = frozenset({
    "initialiseKernelState",
    "initialiseKernelLabelingContext",
    "modifyGetKernelState",
    "bootAndInitialiseFromPlatformOn",
    "bootAndInitialiseFromPlatform",
    "bootAndInitialisePlatform",
    BOOT_ENTRY_CALLEE,
})
EXPECTED_KERNEL_STATE_READERS = frozenset({"getKernelState", "getKernelLabelingContext"})


def lean_exports_in(text: str) -> set[str]:
    """The `@[export …]` symbols of one Lean source, read over the shared code
    view with comments — nested block comments included — *and* string
    contents blanked (PR #889 review round 6): a docstring, a `/- … -/` inside
    another, or a string literal quoting the attribute is not a symbol."""
    return set(LEAN_EXPORT.findall(lean_code_view.code_no_strings(text)))


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


def lean_exports() -> set[str]:
    found: set[str] = set()
    for text in lean_sources().values():
        found.update(lean_exports_in(text))
    return found


def lean_declarations(view: str) -> list[tuple[str | None, str | None, str]]:
    """The top-level declarations of a code view, as `(keyword, name, text)`.

    Segments are delimited by `LEAN_DECL_START`; an attribute line standing on
    its own (`@[export …]` above its `def`) is merged into the declaration it
    precedes, so the attribute and the body it governs are one segment.  A
    segment with no declaration head (`namespace`, `open`, …) is kept with
    `None` for both, so its tokens are attributed to nothing.
    """
    starts = [m.start() for m in LEAN_DECL_START.finditer(view)] + [len(view)]
    decls: list[tuple[str | None, str | None, str]] = []
    pending = ""
    for at, nxt in zip(starts, starts[1:]):
        text = pending + view[at:nxt]
        head = LEAN_DECL_HEAD.match(text)
        if head is None and text.lstrip().startswith("@["):
            pending = text
            continue
        pending = ""
        decls.append(
            (head.group("kw") if head else None, head.group("name") if head else None, text)
        )
    return decls


def identifier_tokens(text: str) -> set[str]:
    return set(LEAN_IDENT.findall(text))


def kernel_state_writers(sources: dict[str, str]) -> set[str]:
    """PR #889 review round 5: the declarations that can **install kernel
    state**, derived rather than listed.

    The seeds are the declarations that name a kernel-state reference
    (`kernelStateRef`, `kernelLabelingContextRef`) for anything but a `.get` —
    a `.set`, `.modify`, `.modifyGet`, or the reference passed as a value,
    which is a write a scanner cannot see and so counts as one.  The set is
    then closed under reference: a declaration whose body names a writer is a
    writer.  Theorems are skipped (a theorem executes nothing), and the
    references' own definitions are not writers of themselves.  Names are
    matched by their last component, so a qualified call is seen and two
    declarations sharing a short name are merged — both over-approximations,
    so the derivation fails closed.  `EXPECTED_KERNEL_STATE_WRITERS` and
    `EXPECTED_KERNEL_STATE_READERS` pin it against the real tree.
    """
    bodies: dict[str, set[str]] = {}
    seeds: set[str] = set()
    for text in sources.values():
        view = lean_code_view.code_no_strings(text)
        for kw, name, decl in lean_declarations(view):
            if name is None or kw in ("theorem", "example"):
                continue
            short = name.split(".")[-1]
            if short in KERNEL_STATE_REFS:
                continue
            bodies[short] = bodies.get(short, set()) | (identifier_tokens(decl) - {short})
            if KERNEL_STATE_REF_WRITE.search(decl):
                seeds.add(short)
    writers = set(seeds)
    frontier = set(seeds)
    while frontier:
        frontier = {
            name for name, tokens in bodies.items() if name not in writers and tokens & frontier
        }
        writers |= frontier
    return writers


def declaration_body(decl: str) -> int | None:
    """The offset just past the head's `:=` — the first one at bracket depth 0 —
    or `None` for a declaration with no such body (`where` form, a structure)."""
    depth = 0
    i = 0
    while i < len(decl):
        c = decl[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == ":" and depth == 0 and decl.startswith(":=", i):
            return i + 2
        i += 1
    return None


def do_block_statements(decl: str, body_at: int) -> list[str] | None:
    """The **top-level statements** of the `do` block at `body_at`, or `None`
    when the body is not a `do` block.

    Lean's `do` notation fixes the block's column at its first statement; a
    later line at that column starts a statement, a deeper line continues the
    one above it (a `match` arm, an `if` branch), and a shallower non-blank
    line ends the block.  What a block does unconditionally is what its
    top-level statements say — a statement nested under `if`, `match` or
    `for` is a continuation here, never a statement of its own.
    """
    m = re.match(r"\s*do\b", decl[body_at:])
    if m is None:
        return None
    do_end = body_at + m.end()
    line_start = decl.rfind("\n", 0, do_end) + 1
    inline, _, rest = decl[do_end:].partition("\n")
    statements: list[list] = []
    base: int | None = None
    if inline.strip():
        base = (do_end - line_start) + (len(inline) - len(inline.lstrip()))
        statements.append([base, inline.strip()])
    for line in rest.split("\n"):
        if not line.strip():
            continue
        indent = len(line) - len(line.lstrip())
        if base is None:
            base = indent
        if indent == base:
            statements.append([indent, line.strip()])
        elif indent > base and statements:
            statements[-1][1] += "\n" + line.strip()
        else:
            break
    return [text for _, text in statements]


def boot_entry_binding_failures(sources: dict[str, str]) -> list[str]:
    """PR #889 review rounds 3 and 5: the connection from the boot entry to the
    checked platform boot is repository-enforced from the day the entry exists.

    `lean_kernel_main` is SM10.1's to write (it is the one upcall that cannot
    sit behind the readiness gate, and the gate's `EXPECTED_UNRESOLVED` entry
    reconciles its absence).  This check is vacuous until then and decisive
    after.  Two relations, on the declaration carrying `@[export
    lean_kernel_main]`, over the comment-free, **string-free** view:

    1. It **executes** `bootAndInitialisePlatform` **unconditionally**: a
       top-level statement of its `do` block binds the call with `←` (a `let`
       pattern or a `match` scrutinee), runs it bare, or `discard`s it, with no
       `return`/`throw` above it — or its body is a term headed by the call.
       An identifier occurrence satisfied round 3's check; a string literal,
       a docstring, a `let x := …` that binds the action without running it,
       and a call nested under `if false` all kept the token (round 5).
    2. It installs kernel state through **nothing else**: no other member of
       the derived `kernel_state_writers` set, and no kernel-state reference
       named directly, appears in its body.  Without this an entry could run
       the checked boot and then install `bootFromPlatform`'s raw state over
       it — the token present and executed, the live path routed around it.

    Together: the live boot path *is* the checked boot, so the idle-thread,
    labeling and reservation guarantees are the hardware boot's.
    """
    failures: list[str] = []
    writers = kernel_state_writers(sources)
    for where, text in sources.items():
        view = lean_code_view.code_no_strings(text)
        for kw, name, decl in lean_declarations(view):
            if not BOOT_ENTRY_EXPORT.search(decl):
                continue
            label = f"{where}: the declaration exporting `{BOOT_ENTRY_SYMBOL}`"
            if kw is None or name is None:
                failures.append(f"{label} is not a named declaration")
                continue
            body_at = declaration_body(decl)
            if body_at is None:
                failures.append(f"{label} has no `:=` body to bind the checked boot in")
                continue
            body = decl[body_at:]
            statements = do_block_statements(decl, body_at)
            if statements is None:
                executed = BOOT_ENTRY_TERM_EXECUTED.match(body.strip()) is not None
                reason = "its body is neither a `do` block nor a term headed by the call"
            else:
                executed = False
                reason = (
                    "no top-level statement of its `do` block executes the call "
                    "(`let … ← bootAndInitialisePlatform …`, `match ← … with`, a bare call, "
                    "or `discard`), or a `return`/`throw` precedes it"
                )
                for statement in statements:
                    if LEAN_DIVERGES.match(statement):
                        break
                    if BOOT_ENTRY_EXECUTED.match(statement):
                        executed = True
                        break
            if not executed:
                failures.append(
                    f"{label} does not execute `{BOOT_ENTRY_CALLEE}` unconditionally: {reason} "
                    "— the hardware boot must go through the checked platform boot (idle "
                    "threads, deployment labeling, reserved slots)"
                )
            short = name.split(".")[-1]
            others = sorted((identifier_tokens(body) & writers) - {BOOT_ENTRY_CALLEE, short})
            if KERNEL_STATE_REF_WRITE.search(body):
                others.append("a kernel-state reference itself")
            if others:
                failures.append(
                    f"{label} installs kernel state through something other than the checked "
                    f"platform boot: {', '.join(others)} — every state installer in its body but "
                    f"`{BOOT_ENTRY_CALLEE}` is a path around the checked boot"
                )
    return failures


def extern_declarations_in(text: str, where: str) -> set[str]:
    """Symbols declared inside an `extern "C" { … }` block.

    Brace-matched rather than line-scanned: a declaration is a `fn` inside the
    block, and the block ends at its matching `}` — a `fn` *after* the block is
    a definition in the crate, not a symbol the crate expects to link against.
    Read over the shared Rust code view with string contents blanked (PR #889
    review round 6): a block quoted in a raw string or in a nested block
    comment declares nothing.
    """
    text = rust_code_view.code_no_strings(text)
    found: set[str] = set()
    for match in EXTERN_BLOCK.finditer(text):
        depth = 0
        end = None
        for index in range(match.end() - 1, len(text)):
            if text[index] == "{":
                depth += 1
            elif text[index] == "}":
                depth -= 1
                if depth == 0:
                    end = index
                    break
        if end is None:
            sys.exit(f'[FAIL] {where}: unbalanced `extern "C"` block')
        found.update(EXTERN_FN.findall(text[match.end() : end]))
    return found


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


def asm_definitions_in(text: str) -> set[str]:
    """Symbols one assembly source **defines and exports** in code the
    preprocessor keeps: a `.global` / `.globl` directive *and* a label `X:` for
    the same name, both read over the comment-blanked view with every
    preprocessor-conditional region blanked (`strip_cpp_conditionals`).

    PR #889 review round 3: a `.global foo` alone declares binding and defines
    nothing — leave the directive and delete the label and the image still has
    an unresolved `foo`, so a directive-only scan passed exactly the
    token-preserving regression this gate exists to catch.  A provider is the
    conjunction, outside any conditional (round 4).
    """
    view = strip_cpp_conditionals(asm_code_view(text))
    return set(ASM_GLOBAL.findall(view)) & set(ASM_LABEL.findall(view))


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
        statements = rust_top_level_statements(structure, body_start, body_end)
        compile_statement = next(
            ((lo, hi) for lo, hi in statements if lo <= compile_at < hi), None
        )
        if compile_statement is None:
            continue
        for lo, hi in statements:
            if lo > compile_statement[0]:
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


def rust_top_level_statements(view: str, start: int, end: int) -> list[tuple[int, int]]:
    """The top-level statements of a Rust block interior `[start, end)` as
    `(lo, hi)` spans over the string-free view: a statement ends at a `;` at
    brace depth zero, or at the `}` that closes a depth-zero block not
    followed by `else`.  The Python twin of `build.rs`'s
    `top_level_statements_in`, so the two gates ask the same question of the
    same shape."""
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


def nm_global_definitions(nm_output: str) -> set[str]:
    """The globally-defined symbols in `nm --defined-only` output: a symbol
    whose type letter is upper-case and not `N` (debugging)."""
    found: set[str] = set()
    for line in nm_output.splitlines():
        parts = line.split()
        if len(parts) == 3 and len(parts[1]) == 1 and parts[1].isupper() and parts[1] != "N":
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
    return nm_global_definitions(result.stdout)


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
    nm_text = (
        "0000000000000000 N $d.1\n0000000000000000 t $x.0\n"
        "0000000000000000 T _start\n000000000000007c T secondary_entry\n"
        "0000000000000010 D table\n"
    )
    if nm_global_definitions(nm_text) != {"_start", "secondary_entry", "table"}:
        failures.append("`nm` output was not reduced to its global definitions")

    # --- PR #889 review rounds 3 and 5: the boot entry, once exported, IS the checked boot ---
    # A stand-in for `Platform/FFI.lean`: the two references, one reader, the
    # writers, and the checked wrapper over them.  The self-test's fixture must be
    # no thinner than the file it stands for, so it carries a theorem naming the
    # callee (theorems execute nothing) and a pure boot (`bootFromPlatform`).
    ffi = (
        "initialize kernelStateRef : IO.Ref Nat ← IO.mkRef 0\n"
        "initialize kernelLabelingContextRef : IO.Ref Nat ← IO.mkRef 0\n"
        "def getKernelState : IO Nat :=\n  kernelStateRef.get\n"
        "def initialiseKernelState (st : Nat) : IO Unit :=\n  kernelStateRef.set st\n"
        "def initialiseKernelLabelingContext (ctx : Nat) : IO Unit :=\n"
        "  kernelLabelingContextRef.set ctx\n"
        "def modifyGetKernelState (f : Nat → Nat × Nat) : IO Nat :=\n"
        "  kernelStateRef.modifyGet f\n"
        "def bootFromPlatform (cfg : Nat) : Nat := cfg\n"
        "def bootAndInitialiseFromPlatformOn (cores : Nat) (cfg : Nat) : IO Unit := do\n"
        "  initialiseKernelState (bootFromPlatform cfg)\n"
        "  initialiseKernelLabelingContext 0\n"
        "def bootAndInitialiseFromPlatform (cfg : Nat) (ctx : Nat) : IO Unit :=\n"
        "  bootAndInitialiseFromPlatformOn 4 cfg\n"
        "def bootAndInitialisePlatform (platform : Type) (cfg : Nat) : IO Unit :=\n"
        "  bootAndInitialiseFromPlatformOn 4 cfg\n"
        "def bootAndInitialiseRPi5 (cfg : Nat) : IO Unit :=\n"
        "  bootAndInitialisePlatform RPi5Platform cfg\n"
        "theorem bootAndInitialisePlatform_eq (cfg : Nat) :\n"
        "    bootAndInitialisePlatform Unit cfg = bootAndInitialisePlatform Unit cfg := rfl\n"
    )

    def entry(body: str) -> str:
        return "@[export lean_kernel_main]\ndef leanKernelMain : IO Unit := " + body + "\n"

    def check_entry(name: str, body: str, accept: bool) -> None:
        found = boot_entry_binding_failures({"ffi": ffi, "entry": entry(body)})
        if accept and found:
            failures.append(f"an entry of an accepted shape was refused — {name}: {found}")
        if not accept and not found:
            failures.append(f"a boot entry that keeps the token and breaks the relation was accepted — {name}")

    # The executing shapes, each with the call at the top level of the block.
    check_entry("`let _ ←` binding",
                "do\n  let _ ← bootAndInitialiseRPi5 cfg\n  pure ()", True)
    check_entry("`match ←` scrutinee",
                "do\n  match ← bootAndInitialiseRPi5 cfg with\n"
                "  | .ok _ => pure ()\n  | .error _ => pure ()", True)
    check_entry("bare call as the last statement",
                "do\n  IO.println \"booting\"\n  bootAndInitialiseRPi5 cfg", True)
    check_entry("term body headed by the call",
                "discard <| bootAndInitialiseRPi5 cfg", True)
    check_entry("a reader after the call is not an installer",
                "do\n  let _ ← bootAndInitialiseRPi5 cfg\n"
                "  let st ← getKernelState\n  pure ()", True)
    # Token-preserving mutations: every one keeps `bootAndInitialisePlatform` in
    # the declaration and breaks the relation (round 3's check passed them all).
    check_entry("the callee named only in a string literal",
                "do\n  IO.println \"bootAndInitialiseRPi5\"\n"
                "  initialiseKernelState (bootFromPlatform cfg)", False)
    check_entry("the call nested under a dead branch",
                "do\n  if false then\n    let _ ← bootAndInitialiseRPi5 cfg\n"
                "  initialiseKernelState (bootFromPlatform cfg)", False)
    check_entry("the action bound with `:=` and never run",
                "do\n  let boot := bootAndInitialiseRPi5 cfg\n"
                "  initialiseKernelState (bootFromPlatform cfg)", False)
    check_entry("the call executed, then the live path routed around it",
                "do\n  let _ ← bootAndInitialiseRPi5 cfg\n"
                "  initialiseKernelState (bootFromPlatform cfg)", False)
    check_entry("the generic entry at another platform (round 7)",
                "do\n  let _ ← bootAndInitialisePlatform SimSingleCorePlatform cfg\n  pure ()", False)
    check_entry("the generic entry at the right platform is still not the hardware entry (round 7)",
                "do\n  let _ ← bootAndInitialisePlatform RPi5Platform cfg\n  pure ()", False)
    check_entry("the unchecked wrapper re-run after the checked one",
                "do\n  let _ ← bootAndInitialiseRPi5 cfg\n"
                "  let _ ← bootAndInitialiseFromPlatform cfg ctx\n  pure ()", False)
    check_entry("a `return` above the call",
                "do\n  return ()\n  let _ ← bootAndInitialiseRPi5 cfg", False)
    check_entry("an installer reached through a helper",
                "do\n  let _ ← bootAndInitialiseRPi5 cfg\n  installRaw cfg\n\n"
                "def installRaw (cfg : Nat) : IO Unit :=\n  kernelStateRef.set (bootFromPlatform cfg)",
                False)
    check_entry("the reference written directly",
                "do\n  let _ ← bootAndInitialiseRPi5 cfg\n  kernelStateRef.set 0",
                False)
    check_entry("a `where`-form body with no `:=`", "leanKernelMain where\n  x := 0", False)
    doc_only = (
        "/-- calls bootAndInitialiseRPi5 -/\n@[export lean_kernel_main]\n"
        "def leanKernelMain : IO Unit := pure ()\n"
    )
    if not boot_entry_binding_failures({"ffi": ffi, "f": doc_only}):
        failures.append("a boot entry naming the callee only in its docstring was accepted")
    elsewhere = (
        "@[export lean_kernel_main]\ndef leanKernelMain : IO Unit := pure ()\n\n"
        "def other : IO Unit := do\n  let _ ← bootAndInitialiseRPi5 cfg\n  pure ()\n"
    )
    if not boot_entry_binding_failures({"ffi": ffi, "f": elsewhere}):
        failures.append("a boot entry whose neighbour makes the call was accepted")
    if boot_entry_binding_failures({"ffi": ffi, "f": "def other : Nat := 0\n"}):
        failures.append("the absence of a boot entry was reported as a binding failure")

    # The installer derivation: the writers, closed under reference; the reader
    # and the pure boot outside it; the references and the theorem outside it.
    derived = kernel_state_writers({"ffi": ffi})
    if not EXPECTED_KERNEL_STATE_WRITERS <= derived:
        failures.append(
            f"the installer derivation missed {sorted(EXPECTED_KERNEL_STATE_WRITERS - derived)}"
        )
    for reader in ("getKernelState", "bootFromPlatform", "kernelStateRef",
                   "bootAndInitialisePlatform_eq"):
        if reader in derived:
            failures.append(f"the installer derivation counted `{reader}` as a writer")
    # One token turns the reader into a writer: `.get` → `.modify`.
    mutated = kernel_state_writers({"ffi": ffi.replace("kernelStateRef.get", "kernelStateRef.modify id")})
    if "getKernelState" not in mutated:
        failures.append("a `.modify` of the reference was not counted as a write")

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
    print("[PASS] check_kernel_entry_exports self-test (57 cases)")
    return 0


def archive_defined_symbols(archive: Path) -> set[str]:
    out = subprocess.run(
        ["nm", "--defined-only", "-g", str(archive)],
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    defined: set[str] = set()
    for line in out.splitlines():
        parts = line.split()
        # `<addr> <type> <name>`; archive member headers have fewer fields.
        if len(parts) == 3 and parts[1] in {"T", "t", "D", "B"}:
            defined.add(parts[2])
    return defined


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
    writers = kernel_state_writers(sources)
    missing_writers = sorted(EXPECTED_KERNEL_STATE_WRITERS - writers)
    leaked_readers = sorted(EXPECTED_KERNEL_STATE_READERS & writers)
    if missing_writers or leaked_readers:
        print("[FAIL] the kernel-state installer derivation disagrees with its pin:")
        for name in missing_writers:
            print(f"         `{name}` was not derived as an installer (renamed, or the reference "
                  "it writes moved)")
        for name in leaked_readers:
            print(f"         `{name}` was derived as an installer, but it only reads")
        return 1
    print(f"[PASS] kernel-state installers derived: {len(writers)} declarations, pinned by "
          f"{len(EXPECTED_KERNEL_STATE_WRITERS)} writers and {len(EXPECTED_KERNEL_STATE_READERS)} readers")
    binding_failures = boot_entry_binding_failures(sources)
    if binding_failures:
        print("[FAIL] the boot entry is exported but not bound to the checked platform boot:")
        for line in binding_failures:
            print(f"         {line}")
        return 1
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
        "exported and bound to `bootAndInitialisePlatform`"
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
