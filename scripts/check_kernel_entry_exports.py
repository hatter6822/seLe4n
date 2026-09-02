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

**The required set is derived, not listed.**  It is the intersection of

  * the Lean tree's `@[export …]` symbols, and
  * the symbols the HAL declares inside an `extern "C" { … }` block,

so a sixth seam added on either side joins the requirement automatically, and a
symbol dropped from both leaves it without anyone editing this file.  A
hand-written table could not see the seam that does not exist yet — the mistake
this gate exists to avoid making again.

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

LINE_COMMENT = re.compile(r"--[^\n]*")
BLOCK_COMMENT = re.compile(r"/-.*?-/", re.DOTALL)
LEAN_EXPORT = re.compile(r"@\[export\s+([A-Za-z_][A-Za-z0-9_]*)\s*\]")
RUST_LINE_COMMENT = re.compile(r"//[^\n]*")
RUST_BLOCK_COMMENT = re.compile(r"/\*.*?\*/", re.DOTALL)
EXTERN_BLOCK = re.compile(r'extern\s+"C"\s*\{')
EXTERN_FN = re.compile(r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(")


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

    if failures:
        print("[FAIL] check_kernel_entry_exports self-test:")
        for line in failures:
            print(f"         {line}")
        return 1
    print("[PASS] check_kernel_entry_exports self-test (6 cases)")
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
    if not exports:
        sys.exit("[FAIL] no `@[export …]` found under SeLe4n/ — the derivation is broken")
    if not externs:
        sys.exit(
            '[FAIL] no `extern "C"` declaration found under rust/sele4n-hal/src/ — '
            "the derivation is broken"
        )

    required = sorted(exports & externs)
    if not required:
        sys.exit(
            "[FAIL] the Lean `@[export]` set and the HAL `extern \"C\"` set are disjoint. "
            "Every kernel entry is declared on both sides, so an empty intersection means "
            "one of the two scans stopped matching and this gate would pass vacuously."
        )

    defined = archive_defined_symbols(ARCHIVE)
    missing = [symbol for symbol in required if symbol not in defined]
    if missing:
        print("[FAIL] kernel entry symbols missing from the built archive:")
        for symbol in missing:
            print(f"         {symbol}")
        print()
        print(
            "  The HAL declares each of these as `extern \"C\"`, and the Lean tree carries an\n"
            "  `@[export]` for each, but the archive a kernel image links does not define them.\n"
            "  An `@[export]` emits a symbol only when its module is in `SeLe4n.lean`'s import\n"
            "  closure: add the defining module there, and drop it from\n"
            "  `scripts/staged_module_allowlist.txt` in the same change."
        )
        return 1

    print(f"[PASS] all {len(required)} Lean kernel entry symbols are defined in the archive")
    for symbol in required:
        print(f"         {symbol}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
