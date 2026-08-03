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
   missed `rust/*/tests/**` integration suites entirely, and a later
   round found the suffix list itself was the same mistake: scanning
   only `.rs` and `.lean` let `scripts/phase5_helper.py` through.  Every
   tracked non-documentation file is now in scope by construction --
   paths always, contents wherever `CONTENT_STRIPPERS` knows the
   language.  Nothing is in scope because someone remembered to add it.
   (Documentation is deliberately exempt; see `DOC_PREFIXES`.)
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


def blank_literal(span: str) -> str:
    """Blank a string literal but KEEP interpolation expressions.

    `s!"{phase5_helper}"` (Lean) and `println!("{phase5_helper}")` (Rust
    inline format args) both reference real identifiers from inside what
    lexically looks like a string.  Blanking the whole literal as prose
    hides them; Codex found the Lean case on PR #854 and the Rust case is
    the same shape, so both are handled here.  `{{`/`}}` are escapes, not
    interpolation.  Newlines are preserved so multi-line literals do not
    disturb anything downstream that counts lines.
    """
    out, k, n, depth = [], 0, len(span), 0
    while k < n:
        if depth == 0 and (span.startswith("{{", k) or span.startswith("}}", k)):
            out.append("  "); k += 2; continue
        ch = span[k]
        if ch == "{":
            depth += 1; out.append(" ")
        elif ch == "}" and depth:
            depth -= 1; out.append(" ")
        elif ch == "\n":
            out.append("\n")
        else:
            out.append(ch if depth else " ")
        k += 1
    return "".join(out)


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
            out.append(blank_literal(text[i:j])); i = j
        elif text[i] == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2; continue
                if text[j] == '"':
                    j += 1; break
                j += 1
            out.append(blank_literal(text[i:j])); i = j
        else:
            out.append(text[i]); i += 1
    return "".join(out)


def strip_hash(text: str) -> str:
    """Blank `#` comments and string literals for Python/shell sources.

    Python triple-quoted docstrings must be blanked, not scanned:
    this file's own docstring cites `phase5_helper`, `ak9ce_01` and
    `I-H01` as examples, and a scanner that read its own prose as
    code would fail on itself.  Prose is exempt -- that is the rule,
    not a loophole.
    """
    triple = (chr(34) * 3, chr(39) * 3)
    out, i, n = [], 0, len(text)
    while i < n:
        if text[i] == "#":
            j = text.find(chr(10), i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j
        elif any(text.startswith(q, i) for q in triple):
            q = text[i:i + 3]
            j = text.find(q, i + 3)
            j = n if j < 0 else j + 3
            out.append("".join(c if c == chr(10) else " " for c in text[i:j]))
            i = j
        elif text[i] in (chr(34), chr(39)):
            q, j = text[i], i + 1
            while j < n and text[j] not in (q, chr(10)):
                j += 2 if text[j] == chr(92) else 1
            j = min(j + 1, n)
            out.append(blank_literal(text[i:j])); i = j
        else:
            out.append(text[i]); i += 1
    return "".join(out)


def strip_rust(t: str) -> str:
    return strip_pairs(t, "//", ("/*", "*/"))


def strip_lean(t: str) -> str:
    return strip_pairs(t, "--", ("/-", "-/"))


# Which suffixes carry code (identifiers), and how to strip their prose.
# A file whose suffix is absent has its PATH scanned but not its contents.
CONTENT_STRIPPERS = {
    ".rs": strip_rust,
    ".lean": strip_lean,
    ".py": strip_hash,
    ".sh": strip_hash,
    ".bash": strip_hash,
}

# Documentation is out of scope entirely -- contents AND path.  Audit
# reports, workstream plans and closeout records are *named after* the
# workstream they record: `docs/audits/WS_RC_R4_CLOSEOUT_PLAN.md` is
# correct, not a violation.  CLAUDE.md cites those paths directly and
# `scripts/website_link_manifest.txt` protects them, so "enforcing" the
# rule there would break live citations and the published site to rename
# files whose names are doing their job.  The rule targets code; prose,
# and the documents that exist to carry it, get the same exemption
# docstrings do.
DOC_PREFIXES = ("docs/",)
DOC_SUFFIXES = (".md", ".txt", ".json", ".expected", ".sha256")

# Rust is held at a hard zero; every other code surface ratchets against
# the grandfathered baseline (CLAUDE.md keeps historical identifiers
# until a workstream can rename them in the same commit).
STRICT_PREFIX = "rust/"


def tracked_all() -> list[str]:
    out = subprocess.run(["git", "ls-files"], cwd=REPO_ROOT,
                         capture_output=True, text=True, check=True).stdout
    return out.split()


def is_doc(rel: str) -> bool:
    return rel.startswith(DOC_PREFIXES) or rel.endswith(DOC_SUFFIXES)


def scan() -> tuple[dict[str, set[str]], dict[str, set[str]]]:
    """Scan every tracked non-doc file: path components, then contents.

    Returns (strict, ratcheted) -- Rust and everything else.
    """
    strict: dict[str, set[str]] = {}
    ratcheted: dict[str, set[str]] = {}

    for rel in tracked_all():
        if is_doc(rel):
            continue
        found = strict if rel.startswith(STRICT_PREFIX) else ratcheted

        def record(token: str, _f=found, _r=rel) -> None:
            if is_coded(token):
                _f.setdefault(token, set()).add(_r)

        for part in Path(rel).parts:
            for token in IDENTIFIER.findall(part):
                record(token)

        stripper = CONTENT_STRIPPERS.get(Path(rel).suffix)
        if stripper is None:
            continue
        try:
            text = stripper((REPO_ROOT / rel).read_text(encoding="utf-8"))
        except (OSError, UnicodeDecodeError):
            continue
        for token in IDENTIFIER.findall(text):
            record(token)
    return strict, ratcheted


def as_pairs(found: dict[str, set[str]]) -> set[tuple[str, str]]:
    return {(name, f) for name, files in found.items() for f in sorted(files)}


def main() -> int:
    status = 0
    regenerate = "--regenerate-baseline" in sys.argv

    strict, ratcheted = scan()

    if strict:
        print("FAIL: workstream/phase codes in Rust identifiers or paths:",
              file=sys.stderr)
        for name, files in sorted(strict.items()):
            print(f"  {name}  ({sorted(files)[0]})", file=sys.stderr)
        print("\nRename by subject (what it does), not by workstream.",
              file=sys.stderr)
        print("Cite the workstream in a docstring instead -- prose is exempt.",
              file=sys.stderr)
        status = 1
    else:
        print("PASS: no workstream/phase codes in Rust identifiers or paths.")

    if regenerate:
        BASELINE_PATH.write_text(json.dumps(
            {k: sorted(v) for k, v in sorted(ratcheted.items())}, indent=1) + "\n")
        print(f"Wrote baseline: {len(ratcheted)} identifiers, "
              f"{len(as_pairs(ratcheted))} (identifier, file) pairs.")
        return status

    baseline_raw = json.loads(BASELINE_PATH.read_text())
    baseline = {(n, f) for n, fs in baseline_raw.items() for f in fs}
    current = as_pairs(ratcheted)
    new_pairs = sorted(current - baseline)
    if new_pairs:
        print(f"FAIL: {len(new_pairs)} newly introduced naming violation(s) "
              f"outside Rust:", file=sys.stderr)
        for name, f in new_pairs[:20]:
            print(f"  {name}  ({f})", file=sys.stderr)
        print("\nHistorical identifiers are grandfathered, but new code must "
              "comply from day one.", file=sys.stderr)
        print("A name may disappear from the baseline; it may never appear "
              "somewhere new.", file=sys.stderr)
        status = 1
    else:
        retired = len(baseline) - len(current)
        note = f"; {retired} retired -- regenerate to lock in" if retired > 0 else ""
        print(f"PASS: no new violations outside Rust ({len(current)} "
              f"grandfathered pairs{note}).")

    return status


if __name__ == "__main__":
    sys.exit(main())
