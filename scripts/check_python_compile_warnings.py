#!/usr/bin/env python3
"""Refuse a tracked Python source that the compiler warns about.

Python 3.12 turns an invalid escape sequence in a non-raw string (`"\\."`,
`"\\w"`, ...) from a silent `DeprecationWarning` into a printed `SyntaxWarning`,
and a later release makes it an error.  The value is unchanged today — Python
keeps the backslash — so nothing fails, and the warning lands in the middle of a
gate's output where it reads as noise.  That is how nine sites across eight Tier
0 gates reached CI: the local 3.11 said nothing at all, and CI's 3.12 printed a
warning above a PASS line.

A compile-time warning is a statement about the *source*, so this asks the
compiler rather than a pattern: every tracked `.py`, read from the index (what is
being committed), is compiled with every warning promoted to an error — which
stops at the first, so a file reports one site per run.  A path
the index lists and this cannot read as UTF-8 is a failure, never a skip — "could
not read it" must not answer the same as "read it and it is clean".

    python3 scripts/check_python_compile_warnings.py            # the tree
    python3 scripts/check_python_compile_warnings.py --self-test
"""

from __future__ import annotations

import os
import sys
import warnings

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from indexed_source import indexed_contents, listed_at  # noqa: E402

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def compile_findings(name: str, text: str) -> list[str]:
    """The compiler's warnings (and errors) for one source, as messages."""
    with warnings.catch_warnings():
        warnings.simplefilter("error")
        try:
            compile(text, name, "exec", dont_inherit=True)
        except (SyntaxError, SyntaxWarning, DeprecationWarning) as err:
            line = getattr(err, "lineno", None)
            return [f"{name}:{line}: {err.msg if isinstance(err, SyntaxError) else err}"]
    return []


def violations(repo: str) -> list[str]:
    paths = listed_at(repo, ":", "*.py")
    texts = indexed_contents(repo, paths)
    found: list[str] = []
    for path in paths:
        if path not in texts:
            found.append(f"{path}: listed by the index but not readable as UTF-8")
            continue
        found.extend(compile_findings(path, texts[path]))
    return found


def self_test() -> int:
    cases = [
        ("an invalid escape in a docstring is refused",
         'def f():\n    """a \\. b"""\n', True),
        ("an invalid escape in a plain string is refused",
         'x = "\\w+"\n', True),
        ("the same text in a raw string is accepted",
         'x = r"\\w+"\n', False),
        ("a doubled backslash is accepted",
         'x = "\\\\w+"\n', False),
        ("a valid escape is accepted",
         'x = "a\\nb\\t\\x41"\n', False),
        ("a syntax error is refused, not skipped",
         'def (:\n', True),
    ]
    failures = []
    for label, src, refused in cases:
        got = bool(compile_findings("case.py", src))
        if got != refused:
            failures.append(f"{label}: expected {'refusal' if refused else 'acceptance'}")
    for f in failures:
        print(f"[FAIL] check_python_compile_warnings self-test: {f}")
    if not failures:
        print(f"[PASS] check_python_compile_warnings self-test: {len(cases)} cases")
    return 1 if failures else 0


def main(argv: list[str]) -> int:
    if argv == ["--self-test"]:
        return self_test()
    if argv:
        print(__doc__)
        return 2
    found = violations(REPO)
    for line in found:
        print(f"[FAIL] {line}")
    if found:
        print(f"FAIL: {len(found)} tracked Python source(s) the compiler warns about; "
              "use a raw string or double the backslash")
        return 1
    count = len(listed_at(REPO, ":", "*.py"))
    print(f"PASS: all {count} tracked Python sources compile with warnings as errors")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
