#!/usr/bin/env python3
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
"""WS-BP BP0.2: both sides consume every fixture of the device-tree corpus.

The shared corpus (`tests/fixtures/dtb/`, BP0.1) is worth something only while
**both** the Rust walk's suite and the Lean parser's suite read **all** of it.
A case added to one suite alone — a blob the other side never parses — is the
silent gap the corpus exists to close, so this Tier 0 gate refuses it before any
build runs.  What it holds:

1. **The corpus is fresh**: the checked-in `.dtb.hex` files and `MANIFEST` are
   exactly what `scripts/generate_dtb_corpus.py` renders from its hand-written
   cases, with no orphaned blob.
2. **Every blob on disk has a manifest row and every row a blob.**  Both suites
   iterate the manifest, so a row is consumed by both; a blob with no row is
   consumed by neither.  (Each suite also asserts this at run time, against the
   directory it actually reads.)
3. **The Rust consumer is live**: `every_corpus_fixture_agrees_with_the_manifest`
   is a `#[test]` with no other attribute between it and its `fn` (so no
   `#[ignore]`), inside `mod dtb_corpus_tests`, which is `#[cfg(test)]`; and its
   body drives the manifest through the structure check the bootargs reader
   runs first (`fdt_layout`, `fdt_structure_check`) and through that reader —
   and **compares** the check's answer with the manifest's verdict: the name
   bound to the check is the name tested against `readable`, so a body that
   keeps the call and decides on something else is refused (the `v0.36.2`
   audit: presence of the call is not the comparison).
4. **The Lean consumer is live**: `main`'s body in `tests/Ak9PlatformSuite.lean`
   carries the runner as a statement of its own, and the runner reads the
   manifest, asks both the structural question and the `/memory` one, and
   compares each answer with the manifest's cell the same way.
5. **Both suites are run by a gate**: Tier 2 executes `ak9_platform_suite`, and
   `scripts/test_rust.sh` runs the workspace's unit tests.

Every source is read through its code view (`rust_code_view`, `lean_code_view`),
so a comment naming the runner can neither satisfy nor trip a check.  **WS-BP
BP2.6** retired the Rust `/memory` walk, so the question both suites still share
is the structural one; the corpus and this gate stay for as long as the bootargs
reader walks the structure block in Rust.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

import generate_dtb_corpus as corpus  # noqa: E402
import lean_code_view  # noqa: E402
import rust_code_view  # noqa: E402

ROOT = SCRIPT_DIR.parent
RUST_CONSUMER = ROOT / "rust" / "sele4n-hal" / "src" / "cmdline.rs"
LEAN_CONSUMER = ROOT / "tests" / "Ak9PlatformSuite.lean"
TIER2_SCRIPT = ROOT / "scripts" / "test_tier2_negative.sh"
RUST_SCRIPT = ROOT / "scripts" / "test_rust.sh"

RUST_MODULE = "dtb_corpus_tests"
RUST_TEST = "every_corpus_fixture_agrees_with_the_manifest"
RUST_BODY_CALLS = ("manifest", "fdt_layout", "fdt_structure_check",
                   "find_bootargs_in_dtb", "read_dir")
LEAN_RUNNER = "dtbCorpus_every_fixture_agrees_with_the_manifest"
LEAN_BODY_TOKENS = ('"MANIFEST"', "corpusStructureReadable", "corpusDeclaredRegions",
                    "readDir")
# The comparisons: a name bound to the check's answer, then that name tested
# against the manifest's verdict.  `{name}` is the bound name, escaped.
RUST_VERDICT_BINDING = re.compile(r"let\s+(\w+)\s*=\s*fdt_layout\([^;]*fdt_structure_check\([^;]*;",
                                  re.S)
RUST_VERDICT_COMPARE = r"if\s+{name}\s*!=\s*\*?readable\b"
LEAN_COMPARISONS = (
    (re.compile(r"let\s+(\w+)\s*:=\s*corpusStructureReadable\s+\w+"),
     r"if\s+{name}\s*!=\s*readable\b", "the structural verdict"),
    (re.compile(r"let\s+(\w+)\s*:=\s*corpusDeclaredRegions\s+\w+"),
     r"if\s+{name}\s*!=\s*expected\b", "the regions cell"),
)


def compared_with_manifest(body: str, binding: re.Pattern, compare: str, who: str,
                           subject: str) -> list[str]:
    """The consumer binds a name to the check's answer and tests THAT name
    against the manifest's cell.  A body that keeps the call and compares a
    constant, or the manifest with itself, keeps every token a presence check
    reads and compares nothing."""
    m = binding.search(body)
    if not m:
        return [f"`{who}` does not bind the answer to {subject}"]
    name = m.group(1)
    if not re.search(compare.format(name=re.escape(name)), body):
        return [f"`{who}` binds `{name}` to {subject} and never compares it with the "
                "manifest's cell"]
    return []


def manifest_names(text: str) -> list[str]:
    return [line.split("|")[0].strip() for line in text.splitlines()
            if line.strip() and not line.startswith("#")]


def check_bijection(manifest_text: str, files: set[str]) -> list[str]:
    names = manifest_names(manifest_text)
    problems = []
    dupes = sorted({n for n in names if names.count(n) > 1})
    if dupes:
        problems.append(f"manifest names a fixture twice: {dupes}")
    for missing in sorted(set(names) - files):
        problems.append(f"manifest row with no blob: {missing}")
    for unread in sorted(files - set(names)):
        problems.append(f"blob no suite reads (no manifest row): {unread}{corpus.HEX_SUFFIX}")
    return problems


def _matching(view: str, opened: int) -> int | None:
    depth = 0
    for i in range(opened, len(view)):
        if view[i] == "{":
            depth += 1
        elif view[i] == "}":
            depth -= 1
            if depth == 0:
                return i
    return None


def check_rust_consumer(text: str) -> list[str]:
    view = rust_code_view.code_no_strings(text)
    mod = re.search(r"#\[cfg\(test\)\]\s*mod\s+" + RUST_MODULE + r"\s*\{", view)
    if not mod:
        return [f"no `#[cfg(test)] mod {RUST_MODULE}` in {RUST_CONSUMER.name}"]
    mod_end = _matching(view, mod.end() - 1)
    if mod_end is None:
        return [f"`mod {RUST_MODULE}` has no closing brace"]
    # `#[test]` and then the `fn`, with nothing but whitespace between: an
    # `#[ignore]` (or any attribute) there is refused, not read past.
    test = re.search(r"#\[test\]\s*fn\s+" + RUST_TEST + r"\s*\(", view)
    if not test:
        return [f"`{RUST_TEST}` is not a `#[test]` directly (an attribute in between "
                f"— `#[ignore]` included — is refused)"]
    if not (mod.end() <= test.start() < mod_end):
        return [f"`{RUST_TEST}` is outside `mod {RUST_MODULE}`"]
    body_open = view.index("{", test.end())
    body_close = _matching(view, body_open)
    if body_close is None:
        return [f"`{RUST_TEST}` has no closing brace"]
    body = view[body_open:body_close]
    problems = [f"`{RUST_TEST}` does not call `{c}`" for c in RUST_BODY_CALLS
                if not re.search(r"\b" + re.escape(c) + r"\s*\(", body)]
    return problems + compared_with_manifest(body, RUST_VERDICT_BINDING, RUST_VERDICT_COMPARE,
                                             RUST_TEST, "the structure check")


def _lean_decl_body(view: str, header: str) -> str | None:
    """The text from a column-0 declaration header to the next column-0 line."""
    m = re.search(r"^" + header + r"\b.*$", view, re.M)
    if not m:
        return None
    rest = view[m.end():]
    stop = re.search(r"^\S", rest, re.M)
    return view[m.start():m.end() + (stop.start() if stop else len(rest))]


def check_lean_consumer(text: str) -> list[str]:
    view = lean_code_view.strip(text)
    problems = []
    main = _lean_decl_body(view, r"def main")
    if main is None:
        problems.append(f"no `def main` in {LEAN_CONSUMER.name}")
    elif not re.search(r"^\s+" + LEAN_RUNNER + r"\s*$", main, re.M):
        problems.append(f"`main` does not run `{LEAN_RUNNER}` as a statement")
    runner = _lean_decl_body(view, r"def " + LEAN_RUNNER)
    if runner is None:
        problems.append(f"no `def {LEAN_RUNNER}`")
    else:
        # The runner's string literals are kept by `strip`, which blanks only
        # comments, so the manifest's file name is visible here.
        for tok in LEAN_BODY_TOKENS:
            if tok not in runner:
                problems.append(f"`{LEAN_RUNNER}` does not read `{tok}`")
        for binding, compare, subject in LEAN_COMPARISONS:
            problems += compared_with_manifest(runner, binding, compare, LEAN_RUNNER, subject)
    return problems


def check_gates(tier2: str, rust_script: str) -> list[str]:
    problems = []
    t2 = _shell_code(tier2)
    if not re.search(r"^\s*run_\w+\s+\"?\w+\"?\s+lake exe ak9_platform_suite\b", t2, re.M):
        problems.append("Tier 2 does not run `lake exe ak9_platform_suite`")
    if not re.search(r"^\s*run_\w+\s+.*\bcargo test --all\b", _shell_code(rust_script), re.M):
        problems.append("scripts/test_rust.sh does not run `cargo test --all`")
    return problems


def _shell_code(text: str) -> str:
    """Shell text with `#` comments dropped (a `#` inside quotes is kept)."""
    out = []
    for line in text.splitlines():
        quote = None
        cut = len(line)
        for i, ch in enumerate(line):
            if quote:
                if ch == quote:
                    quote = None
            elif ch in "'\"":
                quote = ch
            elif ch == "#" and (i == 0 or line[i - 1].isspace()):
                cut = i
                break
        out.append(line[:cut])
    return "\n".join(out)


def check_tree() -> list[str]:
    problems = []
    rendered = corpus.render_all()
    on_disk = {p.name[: -len(corpus.HEX_SUFFIX)]
               for p in corpus.CORPUS_DIR.glob("*" + corpus.HEX_SUFFIX)}
    for name, text in rendered.items():
        path = corpus.CORPUS_DIR / name
        if not path.exists() or path.read_text() != text:
            problems.append(f"stale or missing: tests/fixtures/dtb/{name} "
                            "(regenerate with ./scripts/generate_dtb_corpus.py)")
    for orphan in sorted({n + corpus.HEX_SUFFIX for n in on_disk} - set(rendered)):
        problems.append(f"orphaned blob no case renders: tests/fixtures/dtb/{orphan}")
    manifest = corpus.MANIFEST.read_text() if corpus.MANIFEST.exists() else ""
    problems += check_bijection(manifest, on_disk)
    problems += check_rust_consumer(RUST_CONSUMER.read_text())
    problems += check_lean_consumer(LEAN_CONSUMER.read_text())
    problems += check_gates(TIER2_SCRIPT.read_text(), RUST_SCRIPT.read_text())
    return problems


def self_test() -> int:
    """Each case keeps the token the check looks for and breaks the relation."""
    rust = RUST_CONSUMER.read_text()
    lean = LEAN_CONSUMER.read_text()
    manifest = corpus.MANIFEST.read_text()
    names = set(manifest_names(manifest))
    tier2, rust_sh = TIER2_SCRIPT.read_text(), RUST_SCRIPT.read_text()
    cases = [
        ("baseline rust", lambda: check_rust_consumer(rust), False),
        ("baseline lean", lambda: check_lean_consumer(lean), False),
        ("baseline gates", lambda: check_gates(tier2, rust_sh), False),
        ("baseline bijection", lambda: check_bijection(manifest, names), False),
        ("an #[ignore] between #[test] and the fn",
         lambda: check_rust_consumer(rust.replace(
             "#[test]\n    fn " + RUST_TEST, "#[test]\n    #[ignore]\n    fn " + RUST_TEST)),
         True),
        ("the test's #[test] only in a comment",
         lambda: check_rust_consumer(rust.replace(
             "#[test]\n    fn " + RUST_TEST, "// #[test]\n    fn " + RUST_TEST)), True),
        ("the module no longer #[cfg(test)]",
         lambda: check_rust_consumer(rust.replace(
             "#[cfg(test)]\nmod " + RUST_MODULE, "mod " + RUST_MODULE)), True),
        ("the body stops running the structure check",
         lambda: check_rust_consumer(rust.replace(
             "fdt_structure_check(&blob, &layout).is_some()", "true")), True),
        ("the runner stops asking the structural question",
         lambda: check_lean_consumer(lean.replace(
             "let gotReadable := corpusStructureReadable blob", "let gotReadable := readable")),
         True),
        # The v0.36.2 audit: the call kept, the comparison gone -- the shape a
        # presence check passes.
        ("the body keeps the structure check and drops the comparison",
         lambda: check_rust_consumer(rust.replace("if got != *readable {", "if false {")), True),
        ("the body compares the manifest's verdict with itself",
         lambda: check_rust_consumer(rust.replace("if got != *readable {",
                                                  "if *readable != *readable {")), True),
        ("the runner keeps the structural question and drops the comparison",
         lambda: check_lean_consumer(lean.replace("if gotReadable != readable then",
                                                  "if false then")), True),
        ("the runner keeps the regions question and drops the comparison",
         lambda: check_lean_consumer(lean.replace("if got != expected then", "if false then")),
         True),
        ("the runner named in main only in a comment",
         lambda: check_lean_consumer(lean.replace(
             "\n  " + LEAN_RUNNER + "\n", "\n  -- " + LEAN_RUNNER + "\n")), True),
        ("the runner call moved below main into a new def",
         lambda: check_lean_consumer(lean.replace(
             "\n  " + LEAN_RUNNER + "\n", "\n").replace(
             'IO.println "=== All AK9 platform tests passed ==="',
             'IO.println "=== All AK9 platform tests passed ==="\n\ndef unused : IO Unit := do\n  '
             + LEAN_RUNNER)), True),
        ("the runner stops reading the manifest",
         lambda: check_lean_consumer(lean.replace('(dtbCorpusDir / "MANIFEST")',
                                                  '(dtbCorpusDir / "OTHER")')), True),
        ("Tier 2 echoes the suite instead of running it",
         lambda: check_gates(tier2.replace("lake exe ak9_platform_suite",
                                           "echo lake exe ak9_platform_suite"), rust_sh), True),
        ("a blob with no manifest row",
         lambda: check_bijection(manifest, names | {"stray"}), True),
        ("a row with no blob",
         lambda: check_bijection(manifest, names - {sorted(names)[0]}), True),
        ("a row named twice",
         lambda: check_bijection(manifest + "four_gib_low_aperture | refused | refused\n", names),
         True),
    ]
    failed = 0
    for label, run, should_fail in cases:
        problems = run()
        if bool(problems) != should_fail:
            failed += 1
            print(f"SELF-TEST FAIL: {label}: {'no problem reported' if should_fail else problems}")
    if failed:
        return 1
    print(f"check_dtb_corpus_consumers self-test: {len(cases)} cases pass")
    return 0


def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        return self_test()
    problems = check_tree()
    if problems:
        print("WS-BP BP0.2: the shared device-tree corpus is not consumed whole:")
        for p in problems:
            print("  " + p)
        return 1
    n = len(manifest_names(corpus.MANIFEST.read_text()))
    print(f"WS-BP BP0.2: {n} corpus fixtures, each read by the Rust and the Lean suite")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
