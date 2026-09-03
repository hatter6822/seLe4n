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

LINE_COMMENT = re.compile(r"--[^\n]*")
BLOCK_COMMENT = re.compile(r"/-.*?-/", re.DOTALL)
LEAN_EXPORT = re.compile(r"@\[export\s+([A-Za-z_][A-Za-z0-9_]*)\s*\]")
RUST_LINE_COMMENT = re.compile(r"//[^\n]*")
RUST_BLOCK_COMMENT = re.compile(r"/\*.*?\*/", re.DOTALL)
EXTERN_BLOCK = re.compile(r'extern\s+"C"\s*\{')
EXTERN_FN = re.compile(r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(")
ASM_LINE_COMMENT = re.compile(r"//[^\n]*")
ASM_BLOCK_COMMENT = re.compile(r"/\*.*?\*/", re.DOTALL)
ASM_GLOBAL = re.compile(r"^\s*\.(?:global|globl)\s+([A-Za-z_.$][A-Za-z0-9_.$]*)", re.MULTILINE)
# A label definition: the symbol at the start of a line, followed by `:`.
ASM_LABEL = re.compile(r"^\s*([A-Za-z_.$][A-Za-z0-9_.$]*)\s*:", re.MULTILINE)
# A `cc::Build` source registration in `build.rs`, read over the comment-blanked
# view (string contents kept, since the path IS a string).
CC_FILE_CALL = re.compile(r'\.file\(\s*"([^"]+)"\s*\)')
# The primary's boot install, and the checked platform boot it must call.
BOOT_ENTRY_SYMBOL = "lean_kernel_main"
BOOT_ENTRY_EXPORT = re.compile(r"@\[export\s+lean_kernel_main\s*\]")
BOOT_ENTRY_CALLEE = re.compile(r"\bbootAndInitialisePlatform\b")
# Where a top-level Lean declaration starts, at column 0.
LEAN_DECL_START = re.compile(
    r"^(?:@\[|(?:private |protected |noncomputable |unsafe |partial )*"
    r"(?:def|theorem|abbrev|instance|structure|inductive|example)\b|end\b|namespace\b|"
    r"section\b|open\b)",
    re.MULTILINE,
)


def strip_lean_comments(text: str) -> str:
    """Blank Lean comments so a commented-out `@[export]` is not a symbol."""
    return LINE_COMMENT.sub("", BLOCK_COMMENT.sub("", text))


def lean_exports_in(text: str) -> set[str]:
    return set(LEAN_EXPORT.findall(strip_lean_comments(text)))


def lean_sources() -> dict[str, str]:
    return {str(path.relative_to(REPO)): path.read_text() for path in sorted(LEAN_ROOT.rglob("*.lean"))}


def lean_exports() -> set[str]:
    found: set[str] = set()
    for text in lean_sources().values():
        found.update(lean_exports_in(text))
    return found


def boot_entry_binding_failures(sources: dict[str, str]) -> list[str]:
    """PR #889 review round 3: the connection from the boot entry to the checked
    platform boot is repository-enforced from the day the entry exists.

    `lean_kernel_main` is SM10.1's to write (it is the one upcall that cannot
    sit behind the readiness gate, and the gate's `EXPECTED_UNRESOLVED` entry
    reconciles its absence).  This check is vacuous until then and decisive
    after: whichever Lean declaration carries `@[export lean_kernel_main]` must
    call `bootAndInitialisePlatform` in its own body — read over the
    comment-free view, so a docstring that names the callee, or a neighbouring
    declaration that makes the call, does not satisfy it.  Without this, an
    entry that boots through `bootFromPlatform` directly would link and carry
    none of the idle-thread, labeling or reservation guarantees.
    """
    failures: list[str] = []
    for where, text in sources.items():
        view = strip_lean_comments(text)
        for m in BOOT_ENTRY_EXPORT.finditer(view):
            rest = view[m.end():]
            head = LEAN_DECL_START.search(rest)
            while head is not None and rest.startswith("@[", head.start()):
                head = LEAN_DECL_START.search(rest, head.end())
            if head is None:
                failures.append(
                    f"{where}: `@[export {BOOT_ENTRY_SYMBOL}]` is not followed by a declaration"
                )
                continue
            following = LEAN_DECL_START.search(rest, head.end())
            body = rest[head.start(): following.start() if following else len(rest)]
            if not BOOT_ENTRY_CALLEE.search(body):
                failures.append(
                    f"{where}: the declaration exporting `{BOOT_ENTRY_SYMBOL}` does not call "
                    "`bootAndInitialisePlatform` — the hardware boot must go through the "
                    "checked platform boot (idle threads, deployment labeling, reserved slots)"
                )
    return failures


def extern_declarations_in(text: str, where: str) -> set[str]:
    """Symbols declared inside an `extern "C" { … }` block.

    Brace-matched rather than line-scanned: a declaration is a `fn` inside the
    block, and the block ends at its matching `}` — a `fn` *after* the block is
    a definition in the crate, not a symbol the crate expects to link against.
    """
    text = RUST_LINE_COMMENT.sub("", RUST_BLOCK_COMMENT.sub("", text))
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


def strip_asm_comments(text: str) -> str:
    return ASM_LINE_COMMENT.sub("", ASM_BLOCK_COMMENT.sub("", text))


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
    view = strip_cpp_conditionals(strip_asm_comments(text))
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
    found: set[str] = set()
    for compile_at in cross_gate._occurrences(code, ASM_COMPILE_CALL):
        owner = rust_code_view.enclosing_fn(code, compile_at)
        if owner == rust_code_view.FILE_SCOPE or not cross_gate.reachable_from_main(code, owner):
            continue
        receiver = cross_gate.compiled_builder_name(code, compile_at)
        if receiver is None:
            continue
        for pos in cross_gate._occurrences(code, ".file("):
            if pos >= compile_at or cross_gate.chain_root(code, pos) != receiver:
                continue
            m = CC_FILE_CALL.match(code, pos)
            if m:
                found.add(m.group(1))
    return found


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


def classify_link_requirements(
    externs: set[str],
    asm_globals: set[str],
    expected_unresolved: dict[str, str],
    defined: set[str],
) -> tuple[list[str], list[str], list[str]]:
    """Decide the gate from the four derived sets.

    Returns `(missing, stale_undeclared, stale_defined)`:

      * `missing` — HAL declarations no provider defines: not an assembly
        global, not expected-unresolved, and not in the archive.  A rename on
        either side of a kernel entry lands here, because the HAL's spelling
        is then unresolved.
      * `stale_undeclared` — expected-unresolved entries the HAL no longer
        declares (the exemption outlived the declaration).
      * `stale_defined` — expected-unresolved entries the archive now defines
        (the exemption outlived its reason and must be removed).

    All three must be empty for the gate to pass.
    """
    required = sorted(externs - asm_globals - set(expected_unresolved))
    missing = [symbol for symbol in required if symbol not in defined]
    stale_undeclared = sorted(s for s in expected_unresolved if s not in externs)
    stale_defined = sorted(s for s in expected_unresolved if s in defined)
    return missing, stale_undeclared, stale_defined


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

    # --- PR #889 review: the link requirement is one-sided, and reconciled ---
    live_asm = (
        ".global _start\n.globl secondary_entry\n// .global ghost_entry\n/* .global other */\n"
        "_start:\n    b .\nsecondary_entry:\n    b .\nghost_entry:\nother:\n"
    )
    if asm_definitions_in(live_asm) != {"_start", "secondary_entry"}:
        failures.append("assembly `.global`/`.globl` providers were not collected exactly")

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
    nm_text = (
        "0000000000000000 N $d.1\n0000000000000000 t $x.0\n"
        "0000000000000000 T _start\n000000000000007c T secondary_entry\n"
        "0000000000000010 D table\n"
    )
    if nm_global_definitions(nm_text) != {"_start", "secondary_entry", "table"}:
        failures.append("`nm` output was not reduced to its global definitions")

    # --- PR #889 review round 3: the boot entry, once exported, calls the checked boot ---
    bound = (
        "@[export lean_kernel_main]\ndef leanKernelMain : IO Unit := do\n"
        "  let _ ← bootAndInitialisePlatform RPi5Platform cfg\n  pure ()\n\ndef other : Nat := 0\n"
    )
    if boot_entry_binding_failures({"f": bound}):
        failures.append("a boot entry that calls the checked platform boot was refused")
    doc_only = (
        "/-- calls bootAndInitialisePlatform -/\n@[export lean_kernel_main]\n"
        "def leanKernelMain : IO Unit := pure ()\n"
    )
    if not boot_entry_binding_failures({"f": doc_only}):
        failures.append("a boot entry naming the callee only in its docstring was accepted")
    elsewhere = (
        "@[export lean_kernel_main]\ndef leanKernelMain : IO Unit := pure ()\n\n"
        "def other : IO Unit := do\n  let _ ← bootAndInitialisePlatform RPi5Platform cfg\n  pure ()\n"
    )
    if not boot_entry_binding_failures({"f": elsewhere}):
        failures.append("a boot entry whose neighbour makes the call was accepted")
    if boot_entry_binding_failures({"f": "def other : Nat := 0\n"}):
        failures.append("the absence of a boot entry was reported as a binding failure")

    # A HAL declaration whose Lean export exists under ANOTHER spelling: the
    # token `lean_alpha` is present on the Lean side, but the HAL's spelling is
    # unresolved.  The intersection passed this; the requirement must not.
    missing, stale_undeclared, stale_defined = classify_link_requirements(
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
    missing, _, _ = classify_link_requirements(
        externs={"lean_alpha"}, asm_globals=set(), expected_unresolved={}, defined={"lean_alpha2"}
    )
    if missing != ["lean_alpha"]:
        failures.append("a Lean export renamed away from the HAL's declaration was not reported")

    # An assembly global satisfies a HAL declaration without the archive.
    missing, _, _ = classify_link_requirements(
        externs={"secondary_entry", "lean_beta"},
        asm_globals={"secondary_entry"},
        expected_unresolved={},
        defined={"lean_beta"},
    )
    if missing:
        failures.append("an assembly-provided declaration was reported as missing")

    # An expected-unresolved entry is honoured while its reason holds...
    missing, stale_undeclared, stale_defined = classify_link_requirements(
        externs={"lean_kernel_main", "lean_beta"},
        asm_globals=set(),
        expected_unresolved={"lean_kernel_main": "SM10.1"},
        defined={"lean_beta"},
    )
    if missing or stale_undeclared or stale_defined:
        failures.append("a live expected-unresolved entry was not honoured")

    # ...fails once the archive defines it (the exemption outlived its reason)...
    _, _, stale_defined = classify_link_requirements(
        externs={"lean_kernel_main"},
        asm_globals=set(),
        expected_unresolved={"lean_kernel_main": "SM10.1"},
        defined={"lean_kernel_main"},
    )
    if stale_defined != ["lean_kernel_main"]:
        failures.append("an expected-unresolved entry the archive defines was not reported")

    # ...and fails once the HAL no longer declares it (the entry outlived the seam).
    _, stale_undeclared, _ = classify_link_requirements(
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
    print("[PASS] check_kernel_entry_exports self-test (27 cases)")
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
    missing, stale_undeclared, stale_defined = classify_link_requirements(
        externs, asm_globals, EXPECTED_UNRESOLVED, defined
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
    if failed:
        return 1

    required = sorted(externs - asm_globals - set(EXPECTED_UNRESOLVED))
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
