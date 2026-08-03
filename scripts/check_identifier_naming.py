#!/usr/bin/env python3
"""Tier 0 hygiene: no workstream/audit/phase codes in identifiers.

CLAUDE.md ("Internal-first naming") requires every identifier to describe
what it is, not which workstream produced it.  Prose is exempt --
docstrings, comments, commit messages and CHANGELOG entries are the
right places to cite a workstream.

Why this scans *tokens* rather than declarations
------------------------------------------------
The rule was enforced by hand for four review rounds of PR #854, and
every pass under-matched: a prefix-only grep missed a phase code in the
middle of a name; an `fn`-only grep missed statics and consts.  The
first automated version of this gate then repeated the mistake at one
level up -- it matched the literal text `pub `, so `pub(crate) fn
phase5_helper` walked straight through, and struct fields were not
scanned at all.  It reported a hard zero while accepting four forbidden
identifiers.

So this does not enumerate declaration forms.  It strips comments and
string literals, then treats *every remaining identifier token* as in
scope -- declarations of any visibility, fields, parameters, locals,
enum variants, and uses alike.  There is no declaration syntax to fail
to think of, which is the only property that makes "zero" mean zero.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

# Code classes from CLAUDE.md: WS-*, AN3-*, AK7-*, ak9ce_01, I-H01, and
# phase codes.  Anchored to a name boundary (start or `_`) so ordinary
# words are not caught -- unanchored `ak[0-9]` matches "break0".
CODE_CLASSES = re.compile(
    r"(?:phase\d)"          # phase5_defaults..., ...Phase7State
    r"|(?:(?:^|_)sm\d)"     # sm1d_..., ..._sm7f3
    r"|(?:(?:^|_)an\d)"     # an3b_...
    r"|(?:(?:^|_)ak\d)"     # ak4_..., AK7_LIMIT
    r"|(?:(?:^|_)ws_[a-z]_)"  # ws_q_...
    r"|(?:_p\d_)",          # ..._p2_...
    re.IGNORECASE,
)

IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")

# Lean's grandfathered count.  CLAUDE.md keeps historical identifiers
# "as-is until touched by a workstream that can rename them in the same
# commit", so this ratchets: it may fall, never rise.  Failing on the
# existing population would be a gate nobody could pass.
LEAN_BASELINE = 150

RUST_GLOBS = ("rust/*/src/**/*.rs", "rust/*/src/*.rs", "rust/*/build.rs")
LEAN_GLOBS = ("SeLe4n/**/*.lean", "tests/**/*.lean", "Main.lean")


def strip_rust(text: str) -> str:
    """Blank out comments, string literals and char literals."""
    out, i, n = [], 0, len(text)
    while i < n:
        ch = text[i]
        if text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif text.startswith("/*", i):
            depth, j = 1, i + 2       # Rust block comments nest
            while j < n and depth:
                if text.startswith("/*", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("*/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append(" " * (j - i))
            i = j
        elif ch == "r" and (m := re.match(r'r(#*)"', text[i:])):
            close = '"' + m.group(1)
            j = text.find(close, i + m.end() - 1)
            j = n if j < 0 else j + len(close)
            out.append(" " * (j - i))
            i = j
        elif ch == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == '"':
                    j += 1
                    break
                j += 1
            out.append(" " * (j - i))
            i = j
        else:
            out.append(ch)
            i += 1
    return "".join(out)


def strip_lean(text: str) -> str:
    """Blank out `--` line comments, `/- -/` blocks and string literals."""
    out, i, n = [], 0, len(text)
    while i < n:
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append(" " * (j - i))
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == '"':
                    j += 1
                    break
                j += 1
            out.append(" " * (j - i))
            i = j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def scan(globs, stripper) -> dict[str, str]:
    """Return {identifier: 'path:line'} for every offending token."""
    found: dict[str, str] = {}
    for pattern in globs:
        for path in sorted(REPO_ROOT.glob(pattern)):
            if not path.is_file() or "target" in path.parts:
                continue
            try:
                stripped = stripper(path.read_text(encoding="utf-8"))
            except (OSError, UnicodeDecodeError):
                continue
            for lineno, line in enumerate(stripped.splitlines(), 1):
                for token in IDENTIFIER.findall(line):
                    if CODE_CLASSES.search(token) and token not in found:
                        rel = path.relative_to(REPO_ROOT)
                        found[token] = f"{rel}:{lineno}"
    return found


def main() -> int:
    status = 0

    rust = scan(RUST_GLOBS, strip_rust)
    if rust:
        print("FAIL: workstream/phase codes in Rust identifiers:", file=sys.stderr)
        for name, where in sorted(rust.items()):
            print(f"  {name}  ({where})", file=sys.stderr)
        print("\nRename by subject (what it does), not by workstream.", file=sys.stderr)
        print("Cite the workstream in a docstring instead -- prose is exempt.", file=sys.stderr)
        print("If build.rs or a gate script reads the name, update those too.", file=sys.stderr)
        status = 1
    else:
        print("PASS: no workstream/phase codes in Rust identifiers.")

    lean = scan(LEAN_GLOBS, strip_lean)
    count = len(lean)
    if count > LEAN_BASELINE:
        print(f"FAIL: Lean identifiers carrying codes rose: baseline "
              f"{LEAN_BASELINE}, found {count}.", file=sys.stderr)
        print("Historical Lean identifiers are grandfathered, but new code "
              "must comply from day one.", file=sys.stderr)
        for name, where in sorted(lean.items())[:15]:
            print(f"  {name}  ({where})", file=sys.stderr)
        status = 1
    elif count < LEAN_BASELINE:
        print(f"PASS: Lean ratchet improved ({count} < {LEAN_BASELINE}).")
        print(f"NOTE: lower LEAN_BASELINE to {count} to lock the gain in.")
    else:
        print(f"PASS: Lean ratchet holding at {count} grandfathered identifiers.")

    return status


if __name__ == "__main__":
    sys.exit(main())
