#!/usr/bin/env python3
"""Tier 0 hygiene: no workstream/audit/phase codes in identifiers or paths.

CLAUDE.md ("Internal-first naming") requires every identifier -- and
every file and directory name -- to describe what it is, not which
workstream produced it.  Prose is exempt: docstrings, comments, commit
messages and CHANGELOG entries are the right places to cite a
workstream.

Design notes, each paid for by a review round on PR #854
--------------------------------------------------------
Every round found this rule under-enforced, and every time the cause was
the same: some part of the checker's *scope* was written out by hand and
was narrower than the rule.  Each mechanism below removes one way of
making that mistake.

1. **Discovery is `git ls-files`.**  Hand-written globs missed
   `rust/*/tests/**`; a suffix allowlist then missed `scripts/*.py`.
   Every tracked file is enumerated, and a file is skipped only if it
   is documentation.
2. **Paths are scanned, always.**  The rule covers file names, so
   `src/ws_sm_helpers.rs` with well-named contents is a violation the
   content scan alone cannot see.  Path scanning is independent of
   whether the contents can be parsed, so an unknown format still has
   its name checked.
3. **Contents are scanned as tokens, not declarations.**  An early
   version matched the literal text `pub `, so `pub(crate) fn` and
   struct fields walked through.  Comments and string literals are
   blanked and everything left is in scope -- any visibility, fields,
   params, locals, uses.
4. **Interpolation is code, in every language that has it.**
   `s!"{x}"` (Lean), `println!("{x}")` (Rust) and `f"{x}"` / `f'''{x}'''`
   (Python) reference real identifiers from inside what lexically looks
   like a string.  `blank_literal` keeps the braces' contents.  Python
   needs the `f` prefix checked first: `'''{x}'''` without it is a
   literal brace, and preserving those would start scanning docstring
   prose and break the exemption.
5. **The baseline counts occurrences per (identifier, file).**  A net
   total passes a patch that deletes one grandfathered name and adds a
   different one.  A *set* of pairs additionally cannot see a second
   use of an identifier the file already contains.  Counts close both:
   the number may fall, never rise.  (Line numbers were rejected --
   they churn on every edit above them and the baseline would stop
   meaning anything.)

Documentation is exempt by **location**, not by suffix.  Audit reports
and workstream plans are *named after* the workstream they record --
`docs/audits/WS_RC_R4_CLOSEOUT_PLAN.md` is correct, not a violation --
and CLAUDE.md cites those paths while `website_link_manifest.txt`
protects them.  Scoping the exemption by suffix instead (an earlier
bug) let `scripts/phase5_helper.json` and `tests/phase5_helper.expected`
skip even path scanning.

Scope caveat: `git ls-files` sees *tracked* files, so a new file that
has not been `git add`ed yet is not scanned locally.  That is right for
CI (everything under test is committed) and for the pre-commit hook
(which runs against the index), but a local run before staging can
report a clean tree.  Stage, then trust the result.

Regenerate with `--regenerate-baseline` when a workstream retires
grandfathered names; review the diff, since the flag will also happily
record newly introduced ones.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
BASELINE_PATH = REPO_ROOT / "scripts" / "identifier_naming_baseline.json"

# Documented shapes (CLAUDE.md): WS-*, AN3-*, AK7-*, ak9ce_01, I-H01,
# plus phase codes.  Matching runs over *normalised components*: a token
# is split at `_` and at camelCase boundaries and lowercased, so
# `Sm5iAffinityAnchors`, `sm5i_affinity_anchors` and `SM5I_ANCHORS` are
# one case rather than three regexes.
COMPONENT_CODES = (
    re.compile(r"^phase\d+$"),      # phase5
    re.compile(r"^sm\d[a-z\d]*$"),  # sm1d, sm7f3 (digits/letters alternate)
    re.compile(r"^an\d[a-z\d]*$"),  # an3b, an10
    re.compile(r"^ak\d[a-z\d]*$"),  # ak4, ak9ce
    re.compile(r"^ws$"),            # ws_sm_, ws_rc_, ws_q_ (any arity)
    re.compile(r"^h\d{2}$"),        # I-H01 subtask codes
    re.compile(r"^tpi$"),           # TPI-D* tracked-proof ids
)

IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
CAMEL_SPLIT = re.compile(r"(?<=[a-z0-9])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])")

NEVER = "\x00\x00"      # a line-comment marker for formats that have none


def components(token: str) -> list[str]:
    return [c.lower() for c in CAMEL_SPLIT.sub("_", token).split("_") if c]


# `ws` carries no digits of its own, so unlike `phase5` or `ak9ce` it
# cannot be recognised in isolation: a lone `ws` is as likely to be
# websocket or workspace as a workstream, and is left alone.  In a
# compound it is flagged -- `ws_sm_helper`, `wsRcState`.  That is
# deliberately strict: `wsUrl` would be a false positive, and no such
# name exists here (a microkernel has no websockets) while this gate
# has shipped under-enforced four rounds running.  A narrower rule
# keyed on the following component being a workstream letter-code
# would admit `wsUrl` at the cost of a silent miss whenever a code
# grows past two letters; a false positive fails loudly in CI and is
# fixed by renaming or by baselining it.
BARE_AMBIGUOUS = frozenset({"ws"})


def is_coded(token: str) -> bool:
    parts = components(token)
    for c in parts:
        if c in BARE_AMBIGUOUS and len(parts) == 1:
            continue
        if any(rx.match(c) for rx in COMPONENT_CODES):
            return True
    return False


def blank_literal(span: str) -> str:
    """Blank a string literal but KEEP interpolation expressions."""
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


def blank_prose(span: str) -> str:
    """Blank a literal completely, keeping newlines."""
    return "".join(c if c == "\n" else " " for c in span)


def strip_pairs(text: str, line_comment: str, block: tuple[str, str]) -> str:
    """Blank comments and string literals for C-family / Lean syntax."""
    open_b, close_b = block
    out, i, n = [], 0, len(text)
    while i < n:
        if line_comment != NEVER and text.startswith(line_comment, i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j
        elif text.startswith(open_b, i):
            depth, j = 1, i + len(open_b)     # Lean block comments nest
            while j < n and depth:
                if text.startswith(open_b, j):
                    depth, j = depth + 1, j + len(open_b)
                elif text.startswith(close_b, j):
                    depth, j = depth - 1, j + len(close_b)
                else:
                    j += 1
            out.append(blank_prose(text[i:j])); i = j
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


# Python string prefixes that make braces executable.  `rb`/`b` are not
# f-strings; only a prefix containing `f` interpolates.
FSTRING_PREFIX = re.compile(r"(?:^|[^A-Za-z0-9_])([A-Za-z]{1,3})$")


def _is_fstring(text: str, quote_start: int) -> bool:
    m = FSTRING_PREFIX.search(text[:quote_start])
    return bool(m) and "f" in m.group(1).lower()


def strip_hash(text: str) -> str:
    """Blank `#` comments and string literals for Python/shell/config.

    Triple-quoted docstrings must be blanked, not scanned: this file's
    own docstring cites `phase5_helper`, `ak9ce_01` and `I-H01` as
    examples, and a scanner that read its own prose as code would fail
    on itself.  But a triple-quoted *f-string* holds real expressions,
    so the `f` prefix decides which treatment the literal gets.
    """
    triple = ('"""', "'''")
    out, i, n = [], 0, len(text)
    while i < n:
        if text[i] == "#":
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j
        elif any(text.startswith(q, i) for q in triple):
            q = text[i:i + 3]
            j = text.find(q, i + 3)
            j = n if j < 0 else j + 3
            span = text[i:j]
            out.append(blank_literal(span) if _is_fstring(text, i)
                       else blank_prose(span))
            i = j
        elif text[i] in "\"'":
            q, j = text[i], i + 1
            while j < n and text[j] not in (q, "\n"):
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            span = text[i:j]
            out.append(blank_literal(span) if _is_fstring(text, i)
                       else blank_prose(span))
            i = j
        else:
            out.append(text[i]); i += 1
    return "".join(out)


def strip_asm(t: str) -> str:
    """AArch64 `.S`: `//` and `/* */`.  `#` is cpp, not a comment, so a
    `#define`'s identifiers stay in scope."""
    return strip_pairs(t, "//", ("/*", "*/"))


def strip_block_only(t: str) -> str:
    """Linker scripts: `/* */` only.  `//` is not a comment there, and
    treating it as one would blank real content to end of line."""
    return strip_pairs(t, NEVER, ("/*", "*/"))


def strip_rust(t: str) -> str:
    return strip_pairs(t, "//", ("/*", "*/"))


def strip_lean(t: str) -> str:
    return strip_pairs(t, "--", ("/-", "-/"))


# Every maintained source format, and how to blank its prose.  A format
# absent here still has its PATH scanned (see `scan`), so adding one is
# a strengthening, never the difference between checked and unchecked.
CONTENT_STRIPPERS = {
    ".rs": strip_rust,
    ".lean": strip_lean,
    ".py": strip_hash,
    ".sh": strip_hash,
    ".bash": strip_hash,
    ".S": strip_asm,
    ".ld": strip_block_only,
    ".toml": strip_hash,
    ".yml": strip_hash,
    ".yaml": strip_hash,
}

# Documentation, exempt by LOCATION.  Everything under `docs/` plus the
# root-level documents; nothing is exempted merely for its suffix.
DOC_PREFIXES = ("docs/",)
DOC_ROOT_FILES = frozenset({
    "README.md", "CHANGELOG.md", "CLAUDE.md", "AGENTS.md",
    "THIRD_PARTY_LICENSES.md", "LICENSE", "SECURITY.md",
    "CONTRIBUTING.md", "CODE_OF_CONDUCT.md",
})

# Rust is held at a hard zero; every other code surface ratchets against
# the grandfathered baseline.
STRICT_PREFIX = "rust/"


def tracked_all() -> list[str]:
    out = subprocess.run(["git", "ls-files"], cwd=REPO_ROOT,
                         capture_output=True, text=True, check=True).stdout
    return out.split()


def is_doc(rel: str) -> bool:
    return rel.startswith(DOC_PREFIXES) or rel in DOC_ROOT_FILES


def scan() -> tuple[Counter, Counter]:
    """Count coded-identifier occurrences per (identifier, file).

    Returns (strict, ratcheted) -- Rust and everything else.
    """
    strict: Counter = Counter()
    ratcheted: Counter = Counter()

    for rel in tracked_all():
        if is_doc(rel):
            continue
        bucket = strict if rel.startswith(STRICT_PREFIX) else ratcheted

        for part in Path(rel).parts:
            for token in IDENTIFIER.findall(part):
                if is_coded(token):
                    bucket[(token, rel)] += 1

        stripper = CONTENT_STRIPPERS.get(Path(rel).suffix)
        if stripper is None:
            continue
        try:
            text = stripper((REPO_ROOT / rel).read_text(encoding="utf-8"))
        except (OSError, UnicodeDecodeError):
            continue
        for token in IDENTIFIER.findall(text):
            if is_coded(token):
                bucket[(token, rel)] += 1
    return strict, ratcheted


def to_json(counts: Counter) -> dict:
    out: dict = {}
    for (name, rel), n in sorted(counts.items()):
        out.setdefault(name, {})[rel] = n
    return out


def main() -> int:
    status = 0
    strict, ratcheted = scan()

    if strict:
        print("FAIL: workstream/phase codes in Rust identifiers or paths:",
              file=sys.stderr)
        for (name, rel), n in sorted(strict.items()):
            print(f"  {name}  ({rel}, {n}x)", file=sys.stderr)
        print("\nRename by subject (what it does), not by workstream.",
              file=sys.stderr)
        print("Cite the workstream in a docstring instead -- prose is exempt.",
              file=sys.stderr)
        status = 1
    else:
        print("PASS: no workstream/phase codes in Rust identifiers or paths.")

    if "--regenerate-baseline" in sys.argv:
        BASELINE_PATH.write_text(json.dumps(to_json(ratcheted), indent=1) + "\n")
        print(f"Wrote baseline: {len(set(n for n, _ in ratcheted))} identifiers, "
              f"{len(ratcheted)} (identifier, file) pairs, "
              f"{sum(ratcheted.values())} occurrences.")
        return status

    raw = json.loads(BASELINE_PATH.read_text())
    baseline = Counter({(n, f): c for n, fs in raw.items() for f, c in fs.items()})

    risen = sorted((k for k in ratcheted if ratcheted[k] > baseline.get(k, 0)),
                   key=lambda k: (k[1], k[0]))
    if risen:
        print(f"FAIL: {len(risen)} newly introduced naming violation(s) "
              f"outside Rust:", file=sys.stderr)
        for name, rel in risen[:20]:
            was, now = baseline.get((name, rel), 0), ratcheted[(name, rel)]
            print(f"  {name}  ({rel}): {was} -> {now}", file=sys.stderr)
        print("\nHistorical identifiers are grandfathered, but new code must "
              "comply from day one.", file=sys.stderr)
        print("An occurrence count may fall, never rise.", file=sys.stderr)
        status = 1
    else:
        retired = sum(baseline.values()) - sum(ratcheted.values())
        note = f"; {retired} retired -- regenerate to lock in" if retired > 0 else ""
        print(f"PASS: no new violations outside Rust "
              f"({sum(ratcheted.values())} grandfathered occurrences{note}).")

    return status


if __name__ == "__main__":
    sys.exit(main())
