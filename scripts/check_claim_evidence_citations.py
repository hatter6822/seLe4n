#!/usr/bin/env python3
"""Every artefact `docs/CLAIM_EVIDENCE_INDEX.md` names must exist.

The index maps each claim the project makes to the artefact that discharges it.
An identifier in it that resolves to nothing is therefore worse than a missing
row: the row asserts that evidence exists and names a thing that does not, and
the reader who checks is the one who finds out.  Four such citations were live
when this gate was written (WS-RR RR7.34, register finding 93) -- one naming a
Python function the boot-entry check had since replaced with an elaborator
contract, one naming the census's per-op advance by a name it never had, one
naming a theorem retired when the property it witnessed became trivial, and one
a false alarm that this gate has to resolve correctly or it reports noise.

**Both sides are derived.**  The citation set is every backticked identifier-
shaped token in the index; the declaration set is every name the tree declares,
in every language the index cites -- Lean, Rust, assembly, Python, shell -- plus
the artefacts that are *files* rather than declarations (a Rust integration test
is named by its file, and the index cites it the way `cargo test` does).  So a
row added tomorrow is checked the day it lands, and a rename on either side
fails here rather than in a reader's grep.

**Where it cannot decide, it says so rather than guessing.**  A citation is
resolved by *name*, so a name this tree declares somewhere counts even if the
row means a different one -- the gate catches a name that exists nowhere, which
is the failure that actually happened, and does not claim to catch a citation
that resolves to the wrong artefact.  Exemptions live in
`CITATION_EXEMPTIONS` with a reason each, for names the index deliberately
discusses without owning: an external ABI symbol, a language builtin, a retired
name a row is explaining.

Run `--self-test` to check the checker.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
import tempfile

REPO = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
INDEX = "docs/CLAIM_EVIDENCE_INDEX.md"

# Names the index names without the tree owning them, each with the reason it
# cannot resolve.  A bare list would be an enumeration standing in for a
# derivation; these are the inputs that *legitimately* produce nothing, which is
# the one branch a scanner is allowed to be silent about -- so it is spelled out
# rather than defaulted.
CITATION_EXEMPTIONS: dict[str, str] = {
    "seL4_Fault_tag": "seL4's own ABI field name, cited for fidelity",
    "seL4_MsgMaxExtraCaps": "seL4 constant, cited for fidelity",
    "seL4_MsgMaxLength": "seL4 constant, cited for fidelity",
    "native_decide": "a Lean tactic, not a declaration",
    "no_mangle": "a Rust attribute, not a declaration",
    "link_name": "a Rust attribute, not a declaration",
    "export_name": "a Rust attribute, not a declaration",
    "target_os": "a Rust cfg key, not a declaration",
    "hw_target": "a Cargo feature name, not a declaration",
    "host_tools": "a Cargo feature name, not a declaration",
}

# A citation is an identifier shape: at least one underscore joining
# alphanumeric runs.  Single-word names (`cell`, `alphabet`) are deliberately
# out of scope -- they collide with English and would make the gate noise.
CITATION = re.compile(r"`([A-Za-z][A-Za-z0-9_]*_[A-Za-z0-9_]+)`")

LEAN_DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:private |protected |partial |noncomputable |unsafe |scoped )*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|axiom"
    r"|macro|notation) +([A-Za-z_«][A-Za-z0-9_.'«»!?]*)", re.M)
RUST_DECL = re.compile(
    r"\b(?:fn|struct|enum|trait|const|static|type|mod|macro_rules!)\s+"
    r"([A-Za-z_][A-Za-z0-9_]*)")
PY_DECL = re.compile(r"^\s*(?:def|class)\s+([A-Za-z_][A-Za-z0-9_]*)"
                     r"|^([A-Za-z_][A-Za-z0-9_]*)\s*[:=]", re.M)
SH_DECL = re.compile(r"^\s*(?:function\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*\(\)"
                     r"|^\s*(?:readonly\s+|export\s+)?([A-Za-z_][A-Za-z0-9_]*)=", re.M)
ASM_DECL = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*:", re.M)


def tracked(root: str, pattern: str) -> list[str]:
    """Files as the index sees them, from git, with a filesystem fallback so the
    self-test's temporary trees work the same way."""
    try:
        out = subprocess.run(["git", "-C", root, "ls-files", pattern],
                             capture_output=True, text=True, check=True).stdout.split()
        if out:
            return out
    except (OSError, subprocess.CalledProcessError):
        pass
    found, suffix = [], pattern.lstrip("*")
    for base, _dirs, files in os.walk(root):
        for name in files:
            if name.endswith(suffix):
                found.append(os.path.relpath(os.path.join(base, name), root))
    return sorted(found)


def _read(root: str, rel: str) -> str:
    try:
        with open(os.path.join(root, rel), "r", encoding="utf-8", errors="replace") as fh:
            return fh.read()
    except OSError:
        return ""


def declared_names(root: str) -> set[str]:
    """Every name the tree declares, across the languages the index cites.

    Includes file-derived names, because some artefacts *are* files: a Rust
    integration test is a binary named by its source file and the index cites it
    the way `cargo test` names it, and a script is cited by its stem.
    """
    names: set[str] = set()

    def add(name: str) -> None:
        name = name.strip("«»")
        if name:
            names.add(name)
            names.add(name.split(".")[-1])

    for rel in tracked(root, "*.lean"):
        for m in LEAN_DECL.finditer(_read(root, rel)):
            add(m.group(1))
    for rel in tracked(root, "*.rs"):
        for name in RUST_DECL.findall(_read(root, rel)):
            add(name)
    for rel in tracked(root, "*.S"):
        text = _read(root, rel)
        for name in ASM_DECL.findall(text):
            add(name)
        for name in re.findall(r"\.(?:globl|global)\s+([A-Za-z_][A-Za-z0-9_]*)", text):
            add(name)
    for rel in tracked(root, "*.py"):
        for a, b in PY_DECL.findall(_read(root, rel)):
            add(a or b)
    for rel in tracked(root, "*.sh"):
        for a, b in SH_DECL.findall(_read(root, rel)):
            add(a or b)
    # File-named artefacts: test binaries, scripts, fixtures.
    for pattern in ("*.rs", "*.sh", "*.py", "*.lean", "*.expected", "*.txt", "*.json"):
        for rel in tracked(root, pattern):
            add(os.path.splitext(os.path.basename(rel))[0])
    return names


def unresolved(root: str) -> list[str]:
    """Citations in the index that resolve to nothing the tree declares."""
    text = _read(root, INDEX)
    if not text:
        # Fail closed: an index this gate cannot read is an index it cannot hold
        # to anything, which reads exactly like an index with no defects.
        return [f"{INDEX}: cannot be read, so no citation in it is checked"]
    names = declared_names(root)
    problems, seen = [], set()
    for m in CITATION.finditer(text):
        name = m.group(1)
        if name in seen:
            continue
        seen.add(name)
        if name in CITATION_EXEMPTIONS or name in names or name.split(".")[-1] in names:
            continue
        line = text.count("\n", 0, m.start()) + 1
        problems.append(
            f"{INDEX}:{line}: `{name}` is named as evidence but is declared "
            f"nowhere in the tree -- a row that names a missing artefact "
            f"asserts evidence that does not exist; correct the name, or add "
            f"it to CITATION_EXEMPTIONS with the reason it is not ours")
    if not seen:
        return [f"{INDEX}: no citations found at all; the gate would pass vacuously"]
    return problems


# ---------------------------------------------------------------------------
# The witness suite.  Each case keeps the citation and breaks its resolution,
# which is the relation this gate is about -- deleting the row would pass any
# presence check and prove nothing.
# ---------------------------------------------------------------------------

CLEAN_INDEX = """# Claim / evidence index

| Claim | Doc | Command | Artefacts |
|---|---|---|---|
| A claim | `X.md` | `./scripts/run_it.sh` | `a_real_theorem`, `a_rust_fn` |
"""
CLEAN_LEAN = "theorem a_real_theorem : True := trivial\n"
CLEAN_RUST = "pub fn a_rust_fn() {}\n"


def _tree() -> dict[str, str]:
    return {
        INDEX: CLEAN_INDEX,
        "SeLe4n/Sample.lean": CLEAN_LEAN,
        "rust/sample/src/lib.rs": CLEAN_RUST,
    }


def _run(files: dict[str, str]) -> list[str]:
    with tempfile.TemporaryDirectory() as tmp:
        for rel, body in files.items():
            path = os.path.join(tmp, rel)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(body)
        return unresolved(tmp)


def self_test() -> int:
    cases: list[tuple[str, bool, list[str]]] = []

    def case(label: str, files: dict[str, str], expect_fail: bool) -> None:
        got = _run(files)
        cases.append((label, bool(got) == expect_fail, got))

    case("a clean index resolves", _tree(), False)

    # The instance: a citation whose artefact was renamed.  Every token of the
    # row survives; only the resolution breaks.
    renamed = _tree()
    renamed["SeLe4n/Sample.lean"] = CLEAN_LEAN.replace("a_real_theorem", "a_renamed_theorem")
    case("a renamed Lean artefact fails its citation", renamed, True)

    # The same, one language over.
    rust_renamed = _tree()
    rust_renamed["rust/sample/src/lib.rs"] = CLEAN_RUST.replace("a_rust_fn", "a_renamed_fn")
    case("a renamed Rust artefact fails its citation", rust_renamed, True)

    # A namespaced Lean declaration resolves by its final component, the way the
    # index cites it.
    namespaced = _tree()
    namespaced["SeLe4n/Sample.lean"] = "theorem Foo.Bar.a_real_theorem : True := trivial\n"
    case("a namespaced declaration resolves by its suffix", namespaced, False)

    # A file-named artefact: an integration test is a binary named by its file.
    filed = _tree()
    filed[INDEX] = CLEAN_INDEX.replace("`a_rust_fn`", "`an_integration_test`")
    filed["rust/sample/tests/an_integration_test.rs"] = "#[test] fn t() {}\n"
    case("an artefact named by its file resolves", filed, False)

    # An exempt name is accepted, and only because it is declared exempt.
    exempt = _tree()
    exempt[INDEX] = CLEAN_INDEX.replace("`a_rust_fn`", "`seL4_Fault_tag`")
    case("an exempt external name is accepted", exempt, False)
    not_exempt = _tree()
    not_exempt[INDEX] = CLEAN_INDEX.replace("`a_rust_fn`", "`seL4_NotAThing_tag`")
    case("a look-alike that is not exempt still fails", not_exempt, True)

    # Fail closed, both ways: an unreadable index and an index with no
    # citations must report rather than pass, since either reads exactly like a
    # clean one.
    case("a missing index reports rather than passing", {}, True)
    empty = _tree()
    empty[INDEX] = "# Claim / evidence index\n\nNothing here yet.\n"
    case("an index with no citations reports rather than passing", empty, True)

    failed = 0
    for label, ok, detail in cases:
        if ok:
            print(f"  PASS: {label}")
        else:
            failed += 1
            print(f"  FAIL: {label} -- got {detail}")
    if failed:
        print(f"SELF-TEST FAILED: {failed} case(s)")
        return 1
    print(f"check_claim_evidence_citations self-test: {len(cases)} cases, all correct.")
    return 0


def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        return self_test()
    problems = unresolved(REPO)
    if problems:
        print(f"FAIL: {len(problems)} unresolved claim-evidence citation(s):")
        for p in problems:
            print(f"  {p}")
        print("\nThe index names the artefact that discharges each claim; a name "
              "that resolves to nothing asserts evidence that does not exist.")
        return 1
    print(f"PASS: every artefact {INDEX} names is declared in the tree "
          f"({len(CITATION_EXEMPTIONS)} declared exemption(s)).")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
