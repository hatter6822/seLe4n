#!/usr/bin/env python3
"""Tier 0 hygiene: no workstream/audit/phase codes in identifiers or paths.

CLAUDE.md ("Internal-first naming") requires every identifier -- and
every file and directory name -- to describe what it is, not which
workstream produced it.  Prose is exempt: docstrings, comments, commit
messages and CHANGELOG entries are the right places to cite a
workstream.

Design notes, each one paid for by a review round on PR #854
---------------------------------------------------------------
Four consecutive rounds found this rule under-enforced, every time
because the checker's *scope* was hand-specified and narrower than the
rule.  Each mechanism below exists to remove a category of that
mistake rather than to patch one instance:

1. **File discovery is `git ls-files`, not globs.**  Hand-written globs
   missed `rust/*/tests/**` integration suites entirely.  Every tracked
   source is in scope by construction; nothing is in scope because
   someone remembered to add it.
2. **Path components are scanned, not just contents.**  The rule covers
   file names, so `src/ws_sm_helpers.rs` with well-named contents is a
   violation the content scan alone cannot see.
3. **Tokens, not declarations.**  An earlier version matched the
   literal text `pub `, so `pub(crate) fn` and struct fields walked
   through.  Comments and strings are stripped and everything left is
   in scope -- any visibility, fields, params, locals, uses.
4. **The Lean baseline is a set of (identifier, file) pairs, not a
   count.**  A net count passes a patch that deletes one grandfathered
   name and adds a different forbidden one, and -- because the scan
   deduplicates -- it is also blind to copying an existing offender
   into new code.  Pairs reject both: a name may disappear, never
   appear somewhere new.

Scope caveat: `git ls-files` sees *tracked* files, so a new file that
has not been `git add`ed yet is not scanned locally.  That is the right
behaviour for CI (where everything under test is committed) and for the
pre-commit hook (which runs against the index), but it does mean a
local run before staging can report a clean tree.  Stage, then trust
the result.

Regenerate the baseline with `--regenerate-baseline` when a workstream
retires grandfathered names; review the diff, since the flag will also
happily record newly introduced ones.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
BASELINE_PATH = REPO_ROOT / "scripts" / "identifier_naming_baseline.json"

# --- The code grammar -------------------------------------------------
# Documented shapes (CLAUDE.md): WS-*, AN3-*, AK7-*, ak9ce_01, I-H01,
# plus phase codes.  Matching runs over *normalised components*: the
# token is split at `_` and at camelCase boundaries and lowercased, so
# `Sm5iAffinityAnchors`, `sm5i_affinity_anchors` and `SM5I_ANCHORS` are
# one case, not three regexes.
COMPONENT_CODES = (
    re.compile(r"^phase\d+$"),        # phase5
    re.compile(r"^sm\d[a-z\d]*$"),     # sm1d, sm7f3 (digits/letters alternate)
    re.compile(r"^an\d[a-z\d]*$"),     # an3b, an10
    re.compile(r"^ak\d[a-z\d]*$"),     # ak4, ak9ce
    re.compile(r"^ws$"),              # ws_sm_, ws_rc_, ws_q_ (any arity)
    re.compile(r"^h\d{2}$"),          # I-H01 subtask codes
    re.compile(r"^tpi$"),             # TPI-D* tracked-proof ids
)

IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
CAMEL_SPLIT = re.compile(r"(?<=[a-z0-9])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])")


def components(token: str) -> list[str]:
    """Normalise a token to lowercase components."""
    return [c.lower() for c in CAMEL_SPLIT.sub("_", token).split("_") if c]


def is_coded(token: str) -> bool:
    return any(rx.match(c) for c in components(token) for rx in COMPONENT_CODES)


def strip_pairs(text: str, line_comment: str, block: tuple[str, str]) -> str:
    """Blank comments and string literals, preserving offsets."""
    open_b, close_b = block
    out, i, n = [], 0, len(text)
    while i < n:
        if text.startswith(line_comment, i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j
        elif text.startswith(open_b, i):
            depth, j = 1, i + len(open_b)     # both languages nest
            while j < n and depth:
                if text.startswith(open_b, j):
                    depth, j = depth + 1, j + len(open_b)
                elif text.startswith(close_b, j):
                    depth, j = depth - 1, j + len(close_b)
                else:
                    j += 1
            out.append(" " * (j - i)); i = j
        elif text[i] == "r" and (m := re.match(r'r(#*)"', text[i:])):
            close = '"' + m.group(1)
            j = text.find(close, i + m.end() - 1)
            j = n if j < 0 else j + len(close)
            out.append(" " * (j - i)); i = j
        elif text[i] == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2; continue
                if text[j] == '"':
                    j += 1; break
                j += 1
            out.append(" " * (j - i)); i = j
        else:
            out.append(text[i]); i += 1
    return "".join(out)


def strip_rust(t: str) -> str:
    return strip_pairs(t, "//", ("/*", "*/"))


def strip_lean(t: str) -> str:
    return strip_pairs(t, "--", ("/-", "-/"))


def tracked(suffix: str) -> list[Path]:
    out = subprocess.run(["git", "ls-files", f"*{suffix}"], cwd=REPO_ROOT,
                         capture_output=True, text=True, check=True).stdout
    return [REPO_ROOT / p for p in out.split()]


def scan(suffix: str, stripper, roots: tuple[str, ...]) -> dict[str, set[str]]:
    """Return {offending token: {files}} over contents AND path names."""
    found: dict[str, set[str]] = {}

    def record(token: str, rel: str) -> None:
        if is_coded(token):
            found.setdefault(token, set()).add(rel)

    for path in tracked(suffix):
        rel = str(path.relative_to(REPO_ROOT))
        if roots and not rel.startswith(roots):
            continue
        for part in Path(rel).parts:          # path components (finding 1)
            for token in IDENTIFIER.findall(part):
                record(token, rel)
        try:
            text = stripper(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeDecodeError):
            continue
        for token in IDENTIFIER.findall(text):
            record(token, rel)
    return found


def as_pairs(found: dict[str, set[str]]) -> set[tuple[str, str]]:
    return {(name, f) for name, files in found.items() for f in sorted(files)}


def main() -> int:
    status = 0
    regenerate = "--regenerate-baseline" in sys.argv

    rust = scan(".rs", strip_rust, ("rust/",))
    if rust:
        print("FAIL: workstream/phase codes in Rust identifiers or paths:", file=sys.stderr)
        for name, files in sorted(rust.items()):
            print(f"  {name}  ({sorted(files)[0]})", file=sys.stderr)
        print("\nRename by subject (what it does), not by workstream.", file=sys.stderr)
        print("Cite the workstream in a docstring instead -- prose is exempt.", file=sys.stderr)
        status = 1
    else:
        print("PASS: no workstream/phase codes in Rust identifiers or paths.")

    lean = scan(".lean", strip_lean, ("SeLe4n/", "tests/", "Main.lean"))
    if regenerate:
        BASELINE_PATH.write_text(json.dumps(
            {k: sorted(v) for k, v in sorted(lean.items())}, indent=1) + "\n")
        print(f"Wrote baseline: {len(lean)} identifiers, "
              f"{len(as_pairs(lean))} (identifier, file) pairs.")
        return status

    baseline_raw = json.loads(BASELINE_PATH.read_text())
    baseline = {(n, f) for n, fs in baseline_raw.items() for f in fs}
    current = as_pairs(lean)
    new = sorted(current - baseline)
    if new:
        print(f"FAIL: {len(new)} newly introduced Lean naming violation(s):",
              file=sys.stderr)
        for name, f in new[:20]:
            print(f"  {name}  ({f})", file=sys.stderr)
        print("\nHistorical Lean identifiers are grandfathered, but new code "
              "must comply from day one.", file=sys.stderr)
        print("A name may disappear from the baseline; it may never appear "
              "somewhere new.", file=sys.stderr)
        status = 1
    else:
        retired = len(baseline) - len(current)
        note = f"; {retired} retired -- regenerate to lock in" if retired > 0 else ""
        print(f"PASS: no new Lean violations ({len(current)} grandfathered "
              f"pairs{note}).")

    return status


if __name__ == "__main__":
    sys.exit(main())
