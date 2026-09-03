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

SKIP_EXIT = 77
REPO = Path(__file__).resolve().parent.parent
LEAN_ROOT = REPO / "SeLe4n"
HAL_SRC = REPO / "rust" / "sele4n-hal" / "src"
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


def strip_lean_comments(text: str) -> str:
    """Blank Lean comments so a commented-out `@[export]` is not a symbol."""
    return LINE_COMMENT.sub("", BLOCK_COMMENT.sub("", text))


def lean_exports_in(text: str) -> set[str]:
    return set(LEAN_EXPORT.findall(strip_lean_comments(text)))


def lean_exports() -> set[str]:
    found: set[str] = set()
    for path in sorted(LEAN_ROOT.rglob("*.lean")):
        found.update(lean_exports_in(path.read_text()))
    return found


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


def asm_globals_in(text: str) -> set[str]:
    """Symbols the HAL's own assembly exports (`.global` / `.globl` directives).

    Comments (`//`, `/* */`) are blanked first, so a directive that survives
    only in a comment provides nothing.  A `.global` is a *provider*: a HAL
    `extern "C"` declaration it names (`secondary_entry`, from `boot.S`) is
    resolved by the assembly archive, not by Lean, and is not a requirement on
    the Lean archive.
    """
    text = ASM_LINE_COMMENT.sub("", ASM_BLOCK_COMMENT.sub("", text))
    return set(ASM_GLOBAL.findall(text))


def hal_asm_globals() -> set[str]:
    found: set[str] = set()
    for path in sorted(HAL_SRC.rglob("*.S")):
        found.update(asm_globals_in(path.read_text()))
    return found


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
    live_asm = ".global _start\n.globl secondary_entry\n// .global ghost_entry\n/* .global other */\n"
    if asm_globals_in(live_asm) != {"_start", "secondary_entry"}:
        failures.append("assembly `.global`/`.globl` providers were not collected exactly")

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
    print("[PASS] check_kernel_entry_exports self-test (13 cases)")
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

    exports = lean_exports()
    externs = hal_extern_declarations()
    asm_globals = hal_asm_globals()
    if not exports:
        sys.exit("[FAIL] no `@[export …]` found under SeLe4n/ — the derivation is broken")
    if not externs:
        sys.exit(
            '[FAIL] no `extern "C"` declaration found under rust/sele4n-hal/src/ — '
            "the derivation is broken"
        )
    if not asm_globals:
        sys.exit(
            "[FAIL] no `.global` found under rust/sele4n-hal/src/*.S — the assembly "
            "provider derivation is broken"
        )
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
    print(
        f"[PASS] all {len(required)} HAL kernel-entry declarations are defined in the archive "
        f"({len(externs & asm_globals)} resolved by the HAL's assembly, "
        f"{len(EXPECTED_UNRESOLVED)} expected unresolved and reconciled)"
    )
    for symbol in required:
        print(f"         {symbol}")
    for symbol, reason in sorted(EXPECTED_UNRESOLVED.items()):
        print(f"         {symbol}: expected unresolved — {reason}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
