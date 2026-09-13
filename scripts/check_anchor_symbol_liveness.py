#!/usr/bin/env python3
"""Refuse a Tier 3 anchor that pins a Python symbol nothing reads.

**A pin on a dead symbol is a tautology** (PR #895 review round 16).  Nearly
every anchor in `test_tier3_invariant_surface.sh` is a text scanner asserting
that some construct is present in some file, and an anchor naming a *definition*
keeps reporting PASS after the definition's last consumer goes away -- at which
point it says nothing about the live code at all, while reading in the report
exactly like a check that does.

That is not hypothetical.  Round 16 replaced `classify_extern_item`'s
interior-search body with a leading-form one, which left `_EXTERN_FN_ITEM`,
`_MACRO_INVOCATION` and `_EXTERN_NON_FN_ITEM` with no reader -- and the anchor
`rg -n '^_EXTERN_NON_FN_ITEM'`, whose stated purpose is that the symbol-free
item set lives in the shared view rather than in each gate, went on passing over
a definition the classifier no longer consulted.  The anchor was repointed at
the *read* rather than the definition; this gate is what stops the next one
going dead unnoticed, because a fix applied at one site and not swept onto its
siblings is this project's most-repeated defect.

**What it checks.**  For every `run_check` / `run_negative_check` anchor whose
target is a `.py` file, every identifier the anchor's pattern names that the
target file *binds* must also be *read* somewhere in the tracked Python tree.
Binding-without-reading is the finding.  An identifier the file does not bind is
not a symbol of that file and draws no verdict: an anchor may legitimately name
a string, a comment token or a fragment of prose.

**The default branch is a decision.**  A target file that does not exist, or
that does not parse, fails the gate rather than being skipped: this scanner
builds a set of *checks to validate*, and round 25's rule says a requirement it
drops is a check nobody runs.

Usage:
  check_anchor_symbol_liveness.py              check the tree
  check_anchor_symbol_liveness.py --self-test  run the witness suite
"""

from __future__ import annotations

import ast
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

#: The anchor files whose `.py` targets this gate validates.
ANCHOR_FILES = ("scripts/test_tier3_invariant_surface.sh",)

#: A `run_check` / `run_negative_check` line whose last word is a `.py` path.
#: The pattern may be single- or double-quoted; `rg`'s flags sit between.
_ANCHOR = re.compile(
    r"^run_(?:negative_)?check\s+\"[A-Z][A-Z-]*\"\s+rg\s+(?:-[-\w]+\s+)*"
    r"(?:'(?P<sq>[^']*)'|\"(?P<dq>[^\"]*)\")\s+(?P<path>\S+\.py)\s*$",
    re.M)

_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def anchors_in(text: str) -> list[tuple[str, str]]:
    """The `(pattern, target path)` pairs of every `.py`-targeting anchor."""
    out = []
    for m in _ANCHOR.finditer(text):
        out.append((m.group("sq") if m.group("sq") is not None else m.group("dq"),
                    m.group("path")))
    return out


def bound_and_read(source: str) -> tuple[set[str], set[str]]:
    """The names a module BINDS and the names it READS.

    A name is bound by an assignment target, a `def`, a `class`, an `import ...
    as`, or a function parameter; it is read by a `Load` reference or by an
    attribute access, since a caller in another module reaches a symbol as
    `module.name`.
    """
    tree = ast.parse(source)
    bound: set[str] = set()
    read: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Name):
            (bound if isinstance(node.ctx, ast.Store) else read).add(node.id)
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            bound.add(node.name)
        elif isinstance(node, ast.Attribute):
            read.add(node.attr)
        elif isinstance(node, ast.arg):
            bound.add(node.arg)
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            for alias in node.names:
                bound.add(alias.asname or alias.name.split(".")[0])
    return bound, read


def tracked_python(repo: Path) -> list[Path]:
    """Every tracked `.py` file -- the domain a reader may live in.

    Derived from the index rather than globbed: a reader in a directory nobody
    thought to name is still a reader.
    """
    out = subprocess.run(["git", "ls-files", "-z", "*.py"], cwd=repo,
                         capture_output=True, text=True, check=True).stdout
    return [repo / name for name in out.split("\0") if name]


def dead_anchor_pins(repo: Path, anchor_files=ANCHOR_FILES):
    """`(anchor file, target, symbol, reason)` for every pin this gate refuses."""
    readers: set[str] = set()
    for path in tracked_python(repo):
        try:
            readers |= bound_and_read(path.read_text(encoding="utf-8"))[1]
        except (SyntaxError, UnicodeDecodeError):
            pass          # a reader this gate cannot parse is reported below.
    findings = []
    for anchor_file in anchor_files:
        text = (repo / anchor_file).read_text(encoding="utf-8")
        for pattern, target in anchors_in(text):
            path = repo / target
            if not path.exists():
                findings.append((anchor_file, target, "-", "target file missing"))
                continue
            try:
                bound, _ = bound_and_read(path.read_text(encoding="utf-8"))
            except (SyntaxError, UnicodeDecodeError) as exc:
                findings.append((anchor_file, target, "-", f"target unparseable: {exc}"))
                continue
            for name in sorted(set(_IDENT.findall(pattern))):
                if name in bound and name not in readers:
                    findings.append((anchor_file, target, name,
                                     "anchored and defined, but read nowhere"))
    return findings


# ---------------------------------------------------------------------------
# Self-test.
#
# Every case KEEPS the anchor and changes only the RELATION -- whether the
# symbol it names has a reader -- because a case that deletes the anchor is
# passed by any scanner that merely counts them.
# ---------------------------------------------------------------------------

_CASES = [
    # (label, module source, anchor pattern, expect a finding)
    ("a symbol its own module reads is live",
     "A = 1\ndef f():\n    return A\n", "^A", False),
    ("a symbol NO module reads is a dead pin",
     "_ZZ_UNREAD_SENTINEL = 1\ndef f():\n    return 2\n",
     "^_ZZ_UNREAD_SENTINEL", True),
    # ...and the decisive pair: the same anchor, the same definition, one
    # reader added.  Nothing but the relation moves.
    ("adding a reader makes the same pin live",
     "_ZZ_UNREAD_SENTINEL = 1\ndef f():\n    return _ZZ_UNREAD_SENTINEL\n",
     "^_ZZ_UNREAD_SENTINEL", False),
    # An identifier the module does not bind is not a symbol of it: an anchor
    # may name a string, a comment token or prose, and draws no verdict.
    ("a name the module does not bind draws no verdict",
     "A = 1\ndef f():\n    return A\n", "some prose the file mentions", False),
    # A symbol reached only as `module.name` from elsewhere is read -- the
    # attribute form is what a cross-module consumer writes.
    ("a symbol read only as an attribute is live",
     "def classify_extern_item():\n    return 1\n",
     "^def classify_extern_item", False),
]


def _self_test() -> int:
    import tempfile

    failures = []

    def check(label: str, ok: bool, detail: str = "") -> None:
        print(f"  {'OK  ' if ok else 'FAIL'} {label}" + (f": {detail}" if not ok and detail else ""))
        if not ok:
            failures.append(label)

    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / "scripts").mkdir()
        subprocess.run(["git", "init", "-q"], cwd=root, check=True)
        for label, source, pattern, want in _CASES:
            (root / "scripts" / "subject.py").write_text(source)
            # A second module, so the reader domain is the tracked tree rather
            # than the subject alone -- which is what the attribute case needs.
            (root / "scripts" / "consumer.py").write_text(
                "import subject\n\n\ndef g():\n    return subject.classify_extern_item()\n")
            (root / "scripts" / "anchors.sh").write_text(
                f"run_check \"INVARIANT\" rg -n '{pattern}' scripts/subject.py\n")
            subprocess.run(["git", "add", "-A"], cwd=root, check=True,
                           capture_output=True)
            got = dead_anchor_pins(root, ("scripts/anchors.sh",))
            check(label, bool(got) == want, f"got {got}")

        # The default branch is a decision, in both of its shapes.
        (root / "scripts" / "anchors.sh").write_text(
            "run_check \"INVARIANT\" rg -n '^A' scripts/gone.py\n")
        subprocess.run(["git", "add", "-A"], cwd=root, check=True, capture_output=True)
        check("a missing target fails rather than being skipped",
              any("missing" in f[3] for f in dead_anchor_pins(root, ("scripts/anchors.sh",))))
        (root / "scripts" / "subject.py").write_text("def f(:\n")
        (root / "scripts" / "anchors.sh").write_text(
            "run_check \"INVARIANT\" rg -n '^A' scripts/subject.py\n")
        subprocess.run(["git", "add", "-A"], cwd=root, check=True, capture_output=True)
        check("an unparseable target fails rather than being skipped",
              any("unparseable" in f[3] for f in dead_anchor_pins(root, ("scripts/anchors.sh",))))

    # The anchor parser itself: a `.py` target is recognised in both quotings
    # and past `rg`'s flags, and a non-`.py` target is not this gate's business.
    found = anchors_in(
        "run_check \"INVARIANT\" rg -n '^A' scripts/x.py\n"
        "run_negative_check \"NEGATIVE\" rg -nF \"B\" scripts/y.py\n"
        "run_check \"INVARIANT\" rg -n 'C' SeLe4n/Z.lean\n")
    check("anchors are parsed in both quotings, and only for .py targets",
          found == [("^A", "scripts/x.py"), ("B", "scripts/y.py")], str(found))

    if failures:
        print(f"\n[anchor-symbol-liveness] self-test: {len(failures)} case(s) failed")
        return 1
    print(f"[anchor-symbol-liveness] self-test passed ({len(_CASES) + 3} cases)")
    return 0


def main(argv: list[str]) -> int:
    if argv and argv[0] == "--self-test":
        return _self_test()
    findings = dead_anchor_pins(REPO)
    if findings:
        print("[anchor-symbol-liveness] FAIL: anchors pinning symbols nothing reads")
        for anchor_file, target, name, why in findings:
            print(f"  {anchor_file}: {target}: {name}: {why}")
        print("\nA pin on a dead symbol reports PASS whatever the live code does.")
        print("Repoint the anchor at the symbol's READ, or delete the symbol.")
        return 1
    total = sum(len(anchors_in((REPO / f).read_text(encoding="utf-8")))
                for f in ANCHOR_FILES)
    print(f"[anchor-symbol-liveness] OK: {total} anchor(s) over Python targets, "
          f"every pinned symbol has a reader")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
