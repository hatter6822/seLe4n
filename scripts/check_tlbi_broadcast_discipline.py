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
    """Blank `//` comments in a `.S` source, preserving line structure.

    Deliberately NOT `strip_rust`.  In assembly a `//` opens a comment
    wherever it appears; there are no Rust string literals to protect, and
    routing `.S` through the quote-aware Rust view would let a stray `"`
    earlier in the file swallow a later real comment -- or, worse, make a
    commented-out `tlbi` read as live code.  Line-based is the correct
    grammar here, which is why the two strippers stay distinct.
    """
    return "\n".join(
        (line if (idx := line.find("//")) < 0 else line[:idx])
        for line in text.splitlines()
    )


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


# The checks `run_checks` performs, by id.  Each must be exercised by at
# least one PRESERVING negative case below; the harness enforces it.
CHECKS = ("containment", "rust_allowlist", "lean_allowlist", "stale_entries")


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
