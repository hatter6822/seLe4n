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

# The Lean bindings of the local FFI exports.
LEAN_LOCAL_BINDINGS = ("ffiTlbiAll", "ffiTlbiByAsid", "ffiTlbiByVaddr")

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

RUST_FN_RE = re.compile(r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)\s*[(<]")
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
    """Blank `//` line comments, preserving line structure.

    Rust block comments are not stripped: none of the sources scanned here
    use them, and a stripper that half-handles nesting is worse than one
    that is explicit about its scope.  A `//` inside a string literal would
    over-strip, which can only make the gate *stricter* about containment
    and cannot let a real call site through, since a call site is never
    inside a string.
    """
    return "\n".join(
        (line if (idx := line.find("//")) < 0 else line[:idx])
        for line in text.splitlines()
    )


def strip_hash(text: str) -> str:
    """Blank `#` line comments (allowlist file)."""
    return "\n".join(line.split("#", 1)[0] for line in text.splitlines())


def enclosing_rust_fn(code: str, offset: int) -> str:
    """Name of the last `fn` declared at or before `offset`."""
    last = "<file scope>"
    for match in RUST_FN_RE.finditer(code, 0, offset):
        last = match.group(1)
    return last


def enclosing_lean_decl(code: str, offset: int) -> str:
    """Name of the last Lean declaration at or before `offset`."""
    last = "<file scope>"
    for match in LEAN_DECL_RE.finditer(code[:offset]):
        last = match.group(1)
    return last


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
    """Blank `//` and `/* */`-free assembly comments, preserving lines.

    The `.S` sources use `//` exclusively (they are preprocessed by a C
    compiler), so the Rust stripper's rule applies unchanged.
    """
    return strip_rust(text)


def check_rust_allowlist(root: str, allowed: set[str]) -> tuple[list[str], set[str]]:
    """Local-wrapper calls outside `tlb.rs` must be registered."""
    problems: list[str] = []
    used: set[str] = set()
    for rel in walk(root, RUST_SRC, (".rs",)):
        if rel == TLB_MODULE:
            continue
        code = strip_rust(read(root, rel))
        for match in LOCAL_WRAPPER_RE.finditer(code):
            fn = enclosing_rust_fn(code, match.start())
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
SeLe4n/Kernel/Concurrency/Runtime.lean::tlbiLocalFullFlush
"""


def fixture() -> dict[str, str]:
    return {
        TLB_MODULE: BASE_TLB_RS,
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


def self_test() -> int:
    cases: list[tuple[str, dict[str, str], bool]] = []

    cases.append(("clean baseline", fixture(), False))

    unregistered = fixture()
    unregistered[f"{RUST_SRC}/vspace.rs"] = (
        "\nfn unmap_page(asid: u16, vaddr: u64) {\n"
        "    crate::tlb::tlbi_vae1(asid, vaddr);\n}\n"
    )
    cases.append(("unregistered local call in Rust", unregistered, True))

    via_local = fixture()
    via_local[f"{RUST_SRC}/vspace.rs"] = (
        "\nfn unmap_page(asid: u16, vaddr: u64) {\n"
        "    crate::tlb::tlbi_local(1);\n}\n"
    )
    cases.append(("unregistered `tlbi_local` call", via_local, True))

    prose_only = fixture()
    prose_only[f"{RUST_SRC}/vspace.rs"] = (
        "\nfn unmap_page(asid: u16, vaddr: u64) {\n"
        "    // never call crate::tlb::tlbi_vae1(asid, vaddr) here\n"
        "    crate::tlb::tlbi_for_sharing(0, 1);\n}\n"
    )
    cases.append(("a comment naming the wrapper is not a call", prose_only, False))

    broadcast_ok = fixture()
    broadcast_ok[f"{RUST_SRC}/vspace.rs"] = (
        "\nfn unmap_page(asid: u16, vaddr: u64) {\n"
        "    crate::tlb::tlbi_vmalle1is();\n}\n"
    )
    cases.append(("the IS broadcast wrapper is never flagged", broadcast_ok, False))

    raw_asm = fixture()
    raw_asm[f"{RUST_SRC}/vspace.rs"] = (
        "\nfn unmap_page(asid: u16, vaddr: u64) {\n"
        '    unsafe { core::arch::asm!("tlbi vae1is, {0}", in(reg) 0u64); }\n}\n'
    )
    cases.append(("raw `tlbi` in Rust outside tlb.rs", raw_asm, True))

    raw_asm_s = fixture()
    raw_asm_s[f"{RUST_SRC}/boot.S"] = "_start:\n    tlbi vmalle1\n    nop\n"
    cases.append(("raw `tlbi` in a .S source", raw_asm_s, True))

    asm_prose = fixture()
    asm_prose[f"{RUST_SRC}/boot.S"] = (
        "// the MMU enable path issues tlbi vmalle1 from Rust\n_start:\n    nop\n"
    )
    cases.append(("a .S comment naming tlbi is not an emission", asm_prose, False))

    lean_unregistered = fixture()
    lean_unregistered["SeLe4n/Kernel/Architecture/VSpace.lean"] = (
        "import SeLe4n.Platform.FFI\n\n"
        "def unrelatedEarlierDecl : BaseIO Unit := pure ()\n\n"
        "/-- leading docstring, so the declaration is not on line 1 -/\n"
        "def unmapPage : BaseIO Unit :=\n"
        "  SeLe4n.Platform.FFI.ffiTlbiByVaddr\n"
    )
    cases.append(("unregistered Lean local-FFI reference", lean_unregistered, True))

    lean_prose = fixture()
    lean_prose["SeLe4n/Kernel/Architecture/VSpace.lean"] = (
        "import SeLe4n.Platform.FFI\n\n"
        "-- never call ffiTlbiByVaddr from here\n"
        "def unmapPage : BaseIO Unit :=\n"
        "  SeLe4n.Platform.FFI.ffiTlbiForSharing 0 1\n"
    )
    cases.append(("a Lean comment naming the binding is not a call", lean_prose, False))

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
    cases.append(("local wrapper reached through an aliasing `use`", aliased_use, True))

    fn_pointer = fixture()
    fn_pointer[f"{RUST_SRC}/vspace.rs"] = (
        "\nfn unmap_page(asid: u16, vaddr: u64) {\n"
        "    let invalidate_local = crate::tlb::tlbi_vae1;\n"
        "    invalidate_local(asid, vaddr);\n}\n"
    )
    cases.append(
        ("local wrapper bound to a function pointer, then called", fn_pointer, True)
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
        (
            "a docstring quoting the extern attribute does not exempt the file",
            lean_attr_in_prose,
            True,
        )
    )

    lean_declarer_also_calls = fixture()
    lean_declarer_also_calls["SeLe4n/Platform/FFI.lean"] = (
        BASE_FFI_LEAN
        + "\ndef strayLocalFlush : BaseIO Unit :=\n  ffiTlbiAll\n"
    )
    cases.append(
        (
            "the declaring module's own unregistered CALL is still checked",
            lean_declarer_also_calls,
            True,
        )
    )

    stale = fixture()
    stale[ALLOWLIST] = BASE_ALLOWLIST + "rust/sele4n-hal/src/gone.rs::gone\n"
    cases.append(("allowlist entry with no call site", stale, True))

    no_allowlist = fixture()
    del no_allowlist[ALLOWLIST]
    cases.append(("allowlist file missing", no_allowlist, True))

    # A case expected to be CAUGHT must actually differ from the clean
    # fixture.  A mutation that silently no-ops reads as coverage while
    # asserting nothing, so it is checked rather than trusted.
    clean = fixture()
    failures = 0
    for label, files, expect in cases:
        if expect and files == clean:
            failures += 1
            print(f"[SELF-TEST FAIL] inert mutation, fixture unchanged: {label}")
            continue
        with tempfile.TemporaryDirectory() as tmp:
            write_tree(tmp, files)
            problems = run_checks(tmp)
            if bool(problems) != expect:
                failures += 1
                verb = "missed" if expect else "false-positived on"
                print(f"[SELF-TEST FAIL] gate {verb}: {label}")
                for problem in problems:
                    print(f"                 reported: {problem}")
            else:
                state = "caught" if expect else "accepted"
                print(f"[SELF-TEST OK]   {state}: {label}")

    if failures:
        print(f"\n[FAIL] {failures} self-test case(s) failed")
        return 1
    print(f"\n[PASS] {len(cases)} self-test case(s)")
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
