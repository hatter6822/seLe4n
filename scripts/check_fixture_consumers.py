#!/usr/bin/env python3
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
"""Every file under `tests/fixtures/` must have a reader in code.

Both sides are derived; neither is listed.  The fixtures are the tracked files
under `tests/fixtures/`.  The readers are the tracked sources under `SeLe4n/`,
`Main.lean`, `tests/`, `scripts/` and `rust/`, each read through its code view,
so a comment or docstring naming a fixture is not a reader.  No Markdown is
read: `.md` files are documentation, neither fixtures nor readers.

A fixture is read when one of these holds:

* **Named**: a reader's code view contains its file name as a whole token,
  usually in a string literal.  A glob such as `*.expected` does not count
  here: a sweep that reads every file of a kind cannot show that one of them
  is needed.
* **Checksum companion** (`X.sha256`, where `X` is a fixture): it is named, or
  a glob in a reader's code view matches it (the Tier 2 checksum sweep), or a
  reader that names `X` also builds a `.sha256` path.
* **Corpus entry** (a file in a fixture subdirectory that holds a `MANIFEST`):
  its stem is the first column of a `MANIFEST` row, and the `MANIFEST` itself
  is named by a reader.

A named mention is taken as a read.  Whether the literal reaches an `open` is
not resolved, so a path spelled in code and never opened still passes.

Fails closed: a reader whose suffix is neither a code language nor a listed
data or documentation type, an unreadable file, an unparseable `MANIFEST` row
and an empty fixture set are each a failure, never a skip.

Usage:
    check_fixture_consumers.py              # check the repository
    check_fixture_consumers.py --self-test  # prove the check still bites
"""

from __future__ import annotations

import fnmatch
import os
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check_identifier_naming  # noqa: E402  (path set up immediately above)
import lean_code_view  # noqa: E402
import rust_code_view  # noqa: E402

FIXTURE_DIR = "tests/fixtures"
READER_ROOTS = ("SeLe4n", "Main.lean", "tests", "scripts", "rust")
THIS_FILE = "scripts/check_fixture_consumers.py"


def _shell_view(text: str) -> str:
    # Double-quoted spans kept: a fixture path is exactly that text.
    return check_identifier_naming.strip_shell(text, keep_quoted=True)


#: The code view of each language that can read a fixture.  `.lean` and `.rs`
#: are the overlay's own (`lean_code_view.code_view_for`), so the two answers
#: cannot drift; Python and shell take the tree's existing views with strings
#: kept.
READER_VIEWS = {
    ".lean": lean_code_view.code_view_for(".lean"),
    ".rs": lean_code_view.code_view_for(".rs"),
    ".py": rust_code_view.python_code_view,
    ".sh": _shell_view,
}

#: Suffixes under the reader roots that are not code that runs at test time:
#: documentation, data, build configuration, assembly and linker input.  A
#: decision, not a default: a suffix in neither table fails the check.
NOT_READERS = {
    ".md", ".txt", ".json", ".toml", ".lock", ".gitignore", ".yaml", ".yml",
    ".S", ".ld", ".h", ".expected", ".hex", ".sha256",
}

NAME_CHAR = "A-Za-z0-9_.-"
#: A maximal run of file-name characters: a whole-token mention is one of these.
NAME_TOKEN = re.compile(rf"[{NAME_CHAR}]+")
#: A file glob in code: file-name characters with a `*`, ending in an extension.
GLOB_TOKEN = re.compile(r"[A-Za-z0-9_.*-]*\*[A-Za-z0-9_.*-]*\.[A-Za-z0-9]+(?![A-Za-z0-9_.*-])")


def tracked(root: str, *paths: str) -> list[str]:
    """Tracked files under `paths`, or a filesystem walk when git is absent."""
    try:
        out = subprocess.run(
            ["git", "-C", root, "ls-files", "-z", "--", *paths],
            capture_output=True, check=True).stdout
        listed = [p for p in out.decode("utf-8", "surrogateescape").split("\0") if p]
        if listed:
            return sorted(listed)
    except (OSError, subprocess.CalledProcessError):
        pass
    found = []
    for path in paths:
        full = os.path.join(root, path)
        if os.path.isfile(full):
            found.append(path)
            continue
        for base, dirs, files in os.walk(full):
            dirs[:] = [d for d in dirs if d != ".git"]
            for name in files:
                found.append(os.path.relpath(os.path.join(base, name), root))
    return sorted(found)


def suffix_of(path: str) -> str:
    base = os.path.basename(path)
    if base.startswith(".") and base.count(".") == 1:
        return base  # a dotfile such as `.gitignore`
    return os.path.splitext(base)[1]


def reader_views(root: str, problems: list[str]) -> dict[str, str]:
    """Each reader's code view, by path.  Unclassifiable readers are problems."""
    views: dict[str, str] = {}
    for path in tracked(root, *READER_ROOTS):
        if path.startswith(FIXTURE_DIR + "/") or path == THIS_FILE:
            continue
        suffix = suffix_of(path)
        if suffix in NOT_READERS:
            continue
        view = READER_VIEWS.get(suffix)
        if view is None:
            problems.append(
                f"{path}: cannot classify suffix `{suffix or '(none)'}`: add it to "
                f"READER_VIEWS (code that can read a fixture) or NOT_READERS")
            continue
        try:
            with open(os.path.join(root, path), encoding="utf-8") as handle:
                views[path] = view(handle.read())
        except (OSError, UnicodeDecodeError) as err:
            problems.append(f"{path}: cannot be read ({err}), so it cannot be "
                            f"ruled out as a fixture's only reader")
    return views


def manifest_names(root: str, manifest: str, problems: list[str]) -> set[str]:
    """First-column names of a corpus `MANIFEST` (`#` lines are comments)."""
    found: set[str] = set()
    with open(os.path.join(root, manifest), encoding="utf-8") as handle:
        for number, line in enumerate(handle, start=1):
            text = line.strip()
            if not text or text.startswith("#"):
                continue
            first = text.split("|", 1)[0].strip()
            if not re.fullmatch(rf"[{NAME_CHAR}]+", first):
                problems.append(f"{manifest}:{number}: cannot read a corpus "
                                f"name from this row")
                continue
            found.add(first)
    return found


def check(root: str) -> list[str]:
    problems: list[str] = []
    fixtures = [p for p in tracked(root, FIXTURE_DIR)
                if suffix_of(p) != ".md"]
    if not fixtures:
        return [f"{FIXTURE_DIR}: no fixtures found, so nothing was checked"]
    views = reader_views(root, problems)
    fixture_set = set(fixtures)
    globs = {g for view in views.values() for g in GLOB_TOKEN.findall(view)}
    # Which readers name each fixture, from one tokenisation per reader.
    wanted = {os.path.basename(p) for p in fixtures} | {"MANIFEST"}
    named_by: dict[str, list[str]] = {}
    for reader, view in views.items():
        for token in set(NAME_TOKEN.findall(view)) & wanted:
            named_by.setdefault(token, []).append(reader)

    def readers_naming(name: str) -> list[str]:
        return named_by.get(name, [])

    manifests: dict[str, set[str]] = {}
    for path in fixtures:
        if os.path.basename(path) == "MANIFEST":
            manifests[os.path.dirname(path)] = manifest_names(root, path, problems)

    for path in fixtures:
        base = os.path.basename(path)
        folder = os.path.dirname(path)
        if base.endswith(".sha256") and path[: -len(".sha256")] in fixture_set:
            primary = os.path.basename(path[: -len(".sha256")])
            if readers_naming(base) or any(fnmatch.fnmatchcase(base, g) for g in globs):
                continue
            if any(".sha256" in views[r] for r in readers_naming(primary)):
                continue
            problems.append(f"{path}: checksum companion with no reader: no code "
                            f"names it, globs it, or checks it beside `{primary}`")
            continue
        if folder in manifests and base != "MANIFEST":
            stem = base.split(".", 1)[0]
            listed = stem in manifests[folder]
            manifest_read = bool(readers_naming("MANIFEST"))
            if listed and manifest_read:
                continue
            why = ("its stem is not a row of the MANIFEST" if not listed
                   else "the MANIFEST that lists it has no reader")
            problems.append(f"{path}: corpus entry with no reader: {why}")
            continue
        if not readers_naming(base):
            problems.append(f"{path}: no reader in code: no code view under "
                            f"{', '.join(READER_ROOTS)} names `{base}`")
    return problems


# --------------------------------------------------------------------------
# Self-test.  Each failing case keeps the file and breaks only its relation to
# a reader, which is the property the check exists to hold.
# --------------------------------------------------------------------------
SUITE_READS = 'def fixture : String := "tests/fixtures/foo.expected"\n'
SWEEP = 'find tests/fixtures -name "*.expected.sha256"\n'
CORPUS_READER = 'fn m() { let _ = dir.join("MANIFEST"); }\n'


def _clean() -> dict[str, str]:
    return {
        "tests/fixtures/foo.expected": "line\n",
        "tests/fixtures/foo.expected.sha256": "0  foo.expected\n",
        "tests/fixtures/dtb/MANIFEST": "# name | shape\nalpha | readable\n",
        "tests/fixtures/dtb/alpha.dtb.hex": "d00dfeed\n",
        "tests/fixtures/README.md": "`foo.expected` | `orphan.expected`\n",
        "tests/FooSuite.lean": SUITE_READS,
        "scripts/sweep.sh": SWEEP,
        "rust/src/corpus.rs": CORPUS_READER,
    }


def _case(label: str, edits: dict[str, str | None], want_clean: bool,
          must_name: str = "") -> tuple[str, dict[str, str], bool, str]:
    files = _clean()
    for path, text in edits.items():
        if text is None:
            files.pop(path, None)
        else:
            files[path] = text
    return label, files, want_clean, must_name


def self_test() -> int:
    f = "tests/fixtures/"
    cases = [
        _case("a clean tree", {}, True),
        _case("a fixture whose only reader is removed",
              {"tests/FooSuite.lean": "def other : Nat := 0\n"}, False, f + "foo.expected"),
        _case("a fixture named only in a Lean comment",
              {"tests/FooSuite.lean": "-- reads foo.expected\ndef x : Nat := 0\n"},
              False, f + "foo.expected"),
        _case("a fixture named only in a shell comment",
              {"tests/FooSuite.lean": "def x : Nat := 0\n",
               "scripts/a.sh": "# cat tests/fixtures/foo.expected\n"}, False, f + "foo.expected"),
        _case("a fixture named only in a Python docstring",
              {"tests/FooSuite.lean": "def x : Nat := 0\n",
               "scripts/a.py": '"""Reads foo.expected here."""\nX = 1\n'}, False, f + "foo.expected"),
        _case("a fixture named in a double-quoted shell string",
              {"tests/FooSuite.lean": "def x : Nat := 0\n",
               "scripts/a.sh": 'diff "tests/fixtures/foo.expected" out\n'}, True),
        _case("a fixture named only in Markdown",
              {"tests/FooSuite.lean": "def x : Nat := 0\n",
               "scripts/NOTES.md": "reads `foo.expected`\n"}, False, f + "foo.expected"),
        _case("a fixture matched only by a glob",
              {"tests/FooSuite.lean": "def x : Nat := 0\n",
               "scripts/a.py": 'paths = d.glob("*.expected")\n'}, False, f + "foo.expected"),
        _case("a longer name does not name a shorter one",
              {"tests/FooSuite.lean": 'def x : String := "foo.expected.bak"\n'},
              False, f + "foo.expected"),
        _case("a checksum companion whose sweep is removed",
              {"scripts/sweep.sh": "true\n"}, False, f + "foo.expected.sha256"),
        _case("a checksum companion checked beside its fixture",
              {"scripts/sweep.sh": "true\n",
               "scripts/a.sh": 'F="tests/fixtures/foo.expected"\nsha256sum -c "${F}.sha256"\n'},
              True),
        _case("a corpus entry its MANIFEST does not list",
              {f + "dtb/beta.dtb.hex": "d00dfeed\n"}, False, f + "dtb/beta.dtb.hex"),
        _case("a corpus whose MANIFEST reader is removed",
              {"rust/src/corpus.rs": "fn m() {}\n"}, False, f + "dtb/alpha.dtb.hex"),
        _case("a MANIFEST row that cannot be read",
              {f + "dtb/MANIFEST": "# name\nalpha | readable\n| bad row\n"},
              False, f + "dtb/MANIFEST:3"),
        _case("a reader suffix nobody classified",
              {"scripts/tool.rb": 'File.read("x")\n'}, False, "scripts/tool.rb"),
        _case("an empty fixture directory",
              {path: None for path in _clean() if path.startswith(f)}, False, f[:-1]),
    ]
    failures = 0
    with tempfile.TemporaryDirectory() as tmp:
        for index, (label, files, want_clean, must_name) in enumerate(cases):
            root = os.path.join(tmp, f"case{index}")
            for path, text in files.items():
                full = os.path.join(root, path)
                os.makedirs(os.path.dirname(full), exist_ok=True)
                with open(full, "w", encoding="utf-8") as handle:
                    handle.write(text)
            problems = check(root)
            if (not problems) != want_clean:
                verdict = "passed" if not problems else f"failed: {problems}"
                print(f"SELF-TEST FAIL: {label}: {verdict}", file=sys.stderr)
                failures += 1
            elif must_name and not any(p.startswith(must_name) for p in problems):
                print(f"SELF-TEST FAIL: {label}: no finding names {must_name}: "
                      f"{problems}", file=sys.stderr)
                failures += 1
    if failures:
        print(f"SELF-TEST FAILED: {failures} of {len(cases)} case(s).", file=sys.stderr)
        return 1
    print(f"Fixture consumer self-test: {len(cases)} cases correct.")
    return 0


def main() -> int:
    if sys.argv[1:] == ["--self-test"]:
        return self_test()
    if sys.argv[1:]:
        print(__doc__, file=sys.stderr)
        return 2
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    problems = check(root)
    if problems:
        print("Fixture consumer check FAIL:", file=sys.stderr)
        for problem in problems:
            print(f"  {problem}", file=sys.stderr)
        return 1
    count = len([p for p in tracked(root, FIXTURE_DIR) if suffix_of(p) != ".md"])
    print(f"Fixture consumers: all {count} files under {FIXTURE_DIR}/ have a reader in code.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
