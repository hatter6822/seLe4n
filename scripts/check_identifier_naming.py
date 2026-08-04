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
6. **The code families are enumerated from the registry, not guessed.**
   Recognising only `sm`/`an`/`ak` let `aa2_helper`, `ae6_gate` and
   eleven further real families through.  Every generalisation tried
   was worse than the list; see `WORKSTREAM_FAMILIES`.
7. **Each language gets the stripper its own syntax needs.**  Sharing
   one between Python and shell is what made `echo "${x}"` invisible:
   Python quotes mark prose, shell quotes do not.  A stripper is now
   added only when its rules have been checked against that language,
   never by pointing a suffix at whichever function looks close.
8. **Discovery is NUL-delimited.**  `git ls-files` split on whitespace
   turns a path containing a space into fragments naming no file; the
   read then fails and is swallowed, so the file is never scanned.
9. **A hyphen separates words in a path.**  `WS-SM_helpers.py` splits
   into `WS` + `SM_helpers`, and the lone `WS` is ignored by the
   bare-token rule -- so the carve-out that keeps `ws` usable as an
   ordinary word opened a hole in the canonical `WS-*` spelling.  Paths
   normalise `-` to `_`; contents do not, since there it is subtraction.
10. **Contents come from the index, not the working tree.**  `git
   ls-files` enumerates the index, so reading the working tree checks a
   state that is not the one being committed.

Every one of these was found by review rather than by the gate itself,
which is what the companion `test_identifier_naming_gate.py` exists to
change: each mechanism is pinned by a check that fails against the
version that lacked it.

Documentation is exempt by **location**, not by suffix.  Audit reports
and workstream plans are *named after* the workstream they record --
`docs/audits/WS_RC_R4_CLOSEOUT_PLAN.md` is correct, not a violation --
and CLAUDE.md cites those paths while `website_link_manifest.txt`
protects them.  Scoping the exemption by suffix instead (an earlier
bug) let `scripts/phase5_helper.json` and `tests/phase5_helper.expected`
skip even path scanning.

Scope caveat: `git ls-files` sees *tracked* files, so a new file that
has not been `git add`ed yet is not scanned at all.  Both the paths and
the contents come from the index, so what is checked is exactly what is
being committed -- but a file you have not staged is invisible.  Stage,
then trust the result.

Regenerate with `--regenerate-baseline` when a workstream retires
grandfathered names; review the diff, since the flag will also happily
record newly introduced ones.  The flag writes the working tree, and
the check reads the index, so a regenerated baseline must be `git
add`ed before a plain run reflects it -- that is the point rather than
a wrinkle: an unstaged baseline excuses nothing, which is what stops a
violation and its pardon from being staged separately.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
BASELINE_REL = "scripts/identifier_naming_baseline.json"
BASELINE_PATH = REPO_ROOT / BASELINE_REL

# Documented shapes (CLAUDE.md): WS-*, AN3-*, AK7-*, ak9ce_01, I-H01,
# plus phase codes.  Matching runs over *normalised components*: a token
# is split at `_` and at camelCase boundaries and lowercased, so
# `Sm5iAffinityAnchors`, `sm5i_affinity_anchors` and `SM5I_ANCHORS` are
# one case rather than three regexes.
# The families are ENUMERATED from `docs/WORKSTREAM_HISTORY.md` rather
# than generalised, because every generalisation tried was worse.  A
# blanket two-letter-plus-digit rule matches 602 further identifiers
# here -- `RPi5`, `ARMv8VSpace`, `AP_RW_EL1`, `CP15BEN`, shellcheck's
# `SC1090`, and `SeLe4n` itself -- since kernel code is full of
# architectural names of that shape.  Narrowing it to `a<letter><digit>`
# still adds `at16`/`at17`.  Enumeration costs one line per family and
# is checked against the registry by the self-test.
WORKSTREAM_FAMILIES = (
    "aa", "ac", "ad", "ae", "af", "ag", "ah",
    "ai", "aj", "ak", "al", "am", "an", "sm",
    "z",        # WS-Z (composable performance objects), phases Z1..Z10
)

COMPONENT_CODES = tuple(
    re.compile(rf"^{f}\d[a-z\d]*$") for f in WORKSTREAM_FAMILIES
) + (
    re.compile(r"^phase\d+$"),      # phase5
    re.compile(r"^ws$"),            # ws_sm_, ws_rc_, ws_q_ (any arity)
    re.compile(r"^h\d{2}$"),        # I-H01 subtask codes
    re.compile(r"^tpi$"),           # TPI-D* tracked-proof ids
)

# Audit IDs (`AUDIT_v0.30.11`) are named by the rule alongside
# workstream IDs, and no COMPONENT_CODE can see one: the shape
# normalises to (`audit`, `v0`, `30`, `11`) and not one of those
# components is coded on its own.  `audit` is an ordinary English word
# -- an audit log, an audited transition -- and `v0` is an ordinary
# version.  What identifies the family is their ADJACENCY: a `v<n>`
# immediately followed by a bare number is a dotted version stamped
# into a name, which is what the rule forbids and what no other naming
# convention here produces.  Measured across every tracked
# non-documentation file: zero matches, so this costs no baseline
# entry and fires only on something new.
VERSION_STAMP = re.compile(r"^v\d+$")
BARE_NUMBER = re.compile(r"^\d+$")

# Three single-letter families are real in the registry and deliberately
# ABSENT here, because as *identifier* rules they collide with the
# architecture's own register namespaces.  Each was measured over the
# whole tracked tree before being rejected, and the numbers are the
# argument -- `z` was measured the same way and added, so this is not a
# blanket refusal of single-letter families.
#
# * `R<n>` (WS-RC R0..R14): `r\d+` matches 76 names, 74 of them not
#   workstream codes -- ARM registers (`r0`, `r1` in
#   `SyscallArgDecode.lean`), Lean proof hypotheses (`hR0`, `h_r1_eq`),
#   test bindings (`_r1`, `r1Cap`).
# * `X<n>` (WS-X X1..X5): `x\d+` matches 247 identifiers; restricting to
#   compounds (the `ws` carve-out shape) still leaves 87, of which **69
#   touch `rust/`** -- `set_x0`, `set_x1`,
#   `syscall_args_from_trap_frame_extracts_x0_to_x5`.  Those are AArch64
#   general-purpose registers, and Rust is held at a hard zero with no
#   grandfathering, so this family would fail CI on register names on
#   the commit that added it.  Exactly one genuine code exists
#   (`runX2RuntimeInvariantTests`, grandfathered under no rule).
# * `D<n>` (WS-AB D1..D6): 24 identifiers, or 10 as compounds, of which
#   **zero** are workstream codes -- Lean proof hypotheses (`hD0`..`hD3`
#   in `DualQueueMembership.lean`), test bindings (`resD1`, `stD2`),
#   page-table descriptors (`d0`/`d1`/`d2` in `PageTable.lean`, named
#   for their level), and the device-tree magic `0xD00DFEED`.
#
# A gate that fires on `x0` in a trap frame or on a DTB magic number is
# a gate people switch off, which costs more than the rule buys.

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
    # Audit IDs live in an adjacency rather than in any one component,
    # so they are checked over consecutive pairs.
    return any(VERSION_STAMP.match(a) and BARE_NUMBER.match(b)
               for a, b in zip(parts, parts[1:]))


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


# A `$` expansion inside double quotes is live code.  `$(...)` nests in
# general; the non-greedy form covers the flat case and anything longer
# degrades to keeping less, never to blanking a name outright.
# Backticks are the legacy spelling of `$(...)` and are executable in
# exactly the same places, including inside double quotes.  Leaving
# them out meant `x="`phase5_helper`"` was blanked as message text
# while the bare `x=`phase5_helper`` one line below survived -- the
# same command, visible or not depending on surrounding quotes.
SHELL_EXPANSION = re.compile(
    r"\$\{[^}]*\}|\$\([^)]*\)|\$[A-Za-z_][A-Za-z0-9_]*|`[^`]*`")


def keep_expansions(span: str) -> str:
    """Blank a double-quoted span except its command substitutions."""
    out = [c if c == "\n" else " " for c in span]
    for m in SHELL_EXPANSION.finditer(span):
        out[m.start():m.end()] = list(span[m.start():m.end()])
    return "".join(out)


def strip_shell(text: str) -> str:
    """Shell: blank `#` comments and KEEP every quoted span.

    Routing `.sh` through the Python stripper blanked quoted text as
    prose, so `echo "${phase5_helper}"` became invisible -- a regression,
    since the pre-f-string code kept braces unconditionally and caught
    it.  Shell needs its own rules, exactly as `.ld` does.

    Quotes do not mark prose in shell the way they do in Python, and the
    two kinds differ from each other:

    * **Single** quotes routinely carry whole executable payloads --
      this repository's Tier-3 script passes ~110-line scripts to
      `bash -lc '...'` -- so their contents stay in scope.  Blanking
      them hid `sm5d_surface`/`sm5e_surface` and 280 further
      occurrences.
    * **Double** quotes are message text with live `$` expansions
      inside.  Keeping the whole span flags every `echo "AN7-A: ..."`
      diagnostic, which is a workstream cited in prose and therefore
      exempt by the rule; so only the expansions survive.

    `#` opens a comment only at the start of a word, so `abc#def` and a
    `${#x}` length expansion keep their text.
    """
    out, i, n = [], 0, len(text)
    while i < n:
        if (m := SHELL_EXPANSION.match(text, i)):
            out.append(m.group(0)); i = m.end()
        elif text[i] == "#" and (i == 0 or text[i - 1] in " \t\n;&|("):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j
        elif text[i] == "'":
            j = text.find("'", i + 1)
            j = n if j < 0 else j + 1
            out.append(text[i:j]); i = j          # payload: keep verbatim
        elif text[i] == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2; continue
                if text[j] == '"':
                    j += 1; break
                j += 1
            out.append(keep_expansions(text[i:j])); i = j
        else:
            out.append(text[i]); i += 1
    return "".join(out)


def strip_config(text: str) -> str:
    """YAML / TOML / plain-text data: blank `#` comments, keep the rest.

    These were routed through the Python stripper, which blanks quoted
    scalars as prose -- but a YAML `run: "phase5_helper"` is a command,
    a TOML `name = "sele4n-hal"` is a package identifier, and neither is
    Python prose.  Same defect as pointing `.sh` at `strip_hash`, in a
    format where quoting carries even less meaning: YAML scalars are
    quoted only when the grammar forces it.

    `#` opens a comment only at the start of a word, so a `#` inside a
    value keeps its line.
    """
    out, i, n = [], 0, len(text)
    while i < n:
        if text[i] == "#" and (i == 0 or text[i - 1] in " \t\n"):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j
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
    ".sh": strip_shell,
    ".bash": strip_shell,
    ".S": strip_asm,
    ".ld": strip_block_only,
    ".toml": strip_config,
    ".yml": strip_config,
    ".yaml": strip_config,
    ".txt": strip_config,
    # Data formats carry no comments and no string/code distinction, so
    # every token is in scope.  Scenario ids and fixture labels are
    # identifiers by the rule's own reckoning -- CLAUDE.md's worked
    # example is renaming a *test*, and a scenario registry names tests.
    ".json": lambda t: t,
    ".expected": lambda t: t,
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
    """Every tracked path, NUL-delimited.

    `git ls-files` alone plus `str.split()` breaks any path containing
    whitespace into fragments that name no file; the read then fails and
    is swallowed, so the real file is never scanned.  `-z` also disables
    the C-style quoting git otherwise applies to unusual bytes.
    """
    out = subprocess.run(["git", "ls-files", "-z"], cwd=REPO_ROOT,
                         capture_output=True, text=True, check=True).stdout
    return [p for p in out.split("\0") if p]


def path_tokens(rel: str) -> list[str]:
    """Tokenise a PATH, treating `-` as the word separator it is there.

    `WS-SM_helpers.py` otherwise splits into `WS` + `SM_helpers`, and the
    lone `WS` is ignored by the bare-token rule -- so the carve-out that
    keeps `ws` usable as an ordinary word opened a hole in exactly the
    canonical `WS-*` spelling.  Contents are deliberately NOT normalised
    this way: there `a-b` is subtraction.

    A `.` inside the STEM is a separator too, and for the same reason:
    `audit_v0.30.11_probe.sh` otherwise yields `audit_v0` and `_probe`
    -- `30` and `11` never become tokens at all, since `IDENTIFIER`
    needs a leading letter -- so the canonical dotted `AUDIT_vX.Y.Z`
    filename escapes the audit-ID rule that exists to catch it.  Only
    the stem is normalised; the suffix stays its own token, so no
    existing name changes and the baseline does not churn.

    Kept as one function so the self-test exercises what `scan` runs
    rather than a copy of it.
    """
    out = []
    for part in Path(rel).parts:
        p = Path(part)
        # `.stem` drops only the LAST suffix, which is what we want:
        # `foo.bar.sh` -> stem `foo.bar` (joined) + suffix `sh`.
        normalised = p.stem.replace("-", "_").replace(".", "_")
        out += IDENTIFIER.findall(normalised)
        out += IDENTIFIER.findall(p.suffix.replace("-", "_"))
    return out


def index_contents(paths: list[str]) -> dict[str, str]:
    """Read every path's STAGED content, in one `git cat-file --batch`.

    `git ls-files` enumerates the index, so reading the working tree
    alongside it checks a state that is not the one being committed: a
    contributor could stage a coded identifier, delete it from the
    unstaged copy, and get a clean result while the index still carries
    the violation.  The docstring promises the pre-commit case runs
    against the index, so it does.

    In CI the two agree (a fresh checkout has an empty diff), which is
    why this is a correctness fix rather than a behaviour change there.
    One batched subprocess keeps it to a single fork for the whole tree
    rather than one per file.
    """
    request = "".join(f":{p}\n" for p in paths).encode()
    proc = subprocess.run(["git", "cat-file", "--batch"], cwd=REPO_ROOT,
                          input=request, capture_output=True)
    out, pos, result = proc.stdout, 0, {}
    for path in paths:
        nl = out.find(b"\n", pos)
        if nl < 0:
            break
        header = out[pos:nl].split()
        if len(header) < 3:            # "missing" -- unmerged or gone
            pos = nl + 1
            continue
        size = int(header[2])
        blob = out[nl + 1:nl + 1 + size]
        pos = nl + 1 + size + 1        # trailing newline after the blob
        try:
            result[path] = blob.decode("utf-8")
        except UnicodeDecodeError:
            continue                   # binary: path still gets scanned
    return result


def is_doc(rel: str) -> bool:
    # The baseline is a record *about* violations and necessarily spells
    # every one of them out, so scanning it reports its own contents and
    # each regeneration would re-add them.  Same self-reference as this
    # module's docstring citing `phase5_helper`, one level up.
    if rel == "scripts/identifier_naming_baseline.json":
        return True
    return rel.startswith(DOC_PREFIXES) or rel in DOC_ROOT_FILES


def scan() -> tuple[Counter, Counter]:
    """Count coded-identifier occurrences per (identifier, file).

    Returns (strict, ratcheted) -- Rust and everything else.
    """
    strict: Counter = Counter()
    ratcheted: Counter = Counter()

    tracked = [p for p in tracked_all() if not is_doc(p)]
    staged = index_contents([p for p in tracked
                             if Path(p).suffix in CONTENT_STRIPPERS])

    for rel in tracked:
        bucket = strict if rel.startswith(STRICT_PREFIX) else ratcheted

        for token in path_tokens(rel):
            if is_coded(token):
                bucket[(token, rel)] += 1

        stripper = CONTENT_STRIPPERS.get(Path(rel).suffix)
        if stripper is None or rel not in staged:
            continue
        for token in IDENTIFIER.findall(stripper(staged[rel])):
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

    # From the INDEX, for the same reason `scan` reads sources there: a
    # baseline regenerated only in the working tree would excuse a
    # violation the index still carries, which is precisely the split
    # state reading sources from the index was meant to close.  Falls
    # back to the working tree when the baseline is not tracked yet
    # (its own introducing commit) or when git is unavailable.
    staged_baseline = index_contents([BASELINE_REL]).get(BASELINE_REL)
    raw = json.loads(staged_baseline if staged_baseline is not None
                     else BASELINE_PATH.read_text())
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
