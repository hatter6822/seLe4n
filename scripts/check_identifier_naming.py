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
6. **The code families are READ from the registry, not listed here.**
   A hand-list let `aa2_helper`, `ae6_gate` and eleven further real
   families through, and then `z`, and then a round arguing about `x`
   and `d` -- five rounds, each closed by appending exactly what the
   reviewer named.  `enforced_families()` now reads
   `docs/WORKSTREAM_HISTORY.md`.  Two-letter families are enforced on
   sight (all 17 collide with nothing); single-letter families collide
   with the architecture's namespaces without exception, so each needs
   a recorded decision and the gate FAILS on one that has none.
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
11. **Every tracked file type carries an explicit scan decision.**
   Four rounds each found a format unscanned or mis-routed.  The two
   tables below (`CONTENT_STRIPPERS`, `NO_CONTENT_SCAN`) must between
   them cover every tracked non-documentation extension, and the gate
   fails on one they do not -- so a new file type is classified when it
   lands, by whoever knows what it is.

Notes 1-9 are fixes to *instances*: a format, a family, a separator.
Notes 6 and 11 are different in kind, and are the reason this file
stopped growing a new hole per round.  Both hand-maintained tables --
the family grammar and the format map -- were the actual generator:
every round, the repository knew about something the table did not, and
only a reader comparing them could tell.  Deriving the families from
the registry and requiring a decision per extension moves that
comparison into CI, where it happens on every commit rather than
whenever someone looks.

Every mechanism here was found by review rather than by the gate
itself, which is what the companion `test_identifier_naming_gate.py`
exists to change: each is pinned by a check that fails against the
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


def read_tracked(rel: str) -> str | None:
    """The ONLY way this gate reads a file: the STAGED blob, or None.

    Three separate inputs feed this check -- the sources, the
    grandfathering baseline, and the workstream registry the grammar is
    derived from -- and each was added on its own read path.  Two review
    rounds went to the same defect in two of them: the check enumerates
    paths from the index, so any input read from the WORKING TREE lets a
    contributor stage one state and present another.  Routing every read
    through one function is what stops the next input being added on the
    wrong path; the self-test pins that no bare `read_text` returns.
    """
    return index_contents([rel]).get(rel)


# Documented shapes (CLAUDE.md): WS-*, AN3-*, AK7-*, ak9ce_01, I-H01,
# plus phase codes.  Matching runs over *normalised components*: a token
# is split at `_` and at camelCase boundaries and lowercased, so
# `Sm5iAffinityAnchors`, `sm5i_affinity_anchors` and `SM5I_ANCHORS` are
# one case rather than three regexes.
#
# The family set is DERIVED from `docs/WORKSTREAM_HISTORY.md`, not
# hand-listed.  A hand-list was the single largest source of holes in
# this gate: five separate review rounds each found families it lacked
# (`aa`/`ae` and eleven more, then `z`, then `x`, `d`) and each was
# fixed by appending exactly what the reviewer named.  The registry is
# the authority for which workstreams exist, so it is what the grammar
# reads -- and a workstream added there tomorrow is covered without
# anyone remembering this file.
#
# Deriving alone is not enough, because the two arities behave
# completely differently as identifier rules.  Measured over the whole
# tracked tree:
#
#   * **Two-letter** families (`aa`..`an`, `ab`, `rc`, `sm`, `z`) match
#     **zero** non-workstream identifiers, all 17 of them.  They are
#     enforced automatically, with no per-family decision needed.
#   * **Single-letter** families collide with the architecture's own
#     namespaces, every one of them: `u` matches 57 (48 in `rust/` --
#     `AtomicU32`, `AtomicU64`), `x` 247 (181 in `rust/` -- AArch64
#     registers), `t` 78 (`_t0`.., thread bindings), `r` 105 (ARM
#     registers, Lean hypotheses), `l` 41 (`BOOT_L1_TABLE`, page-table
#     levels), `c` 67, `h` 52, `b`/`f`/`m` 40 each, `i` (`i32`,
#     `i18n`).  A gate that fires on `AtomicU64` is a gate people
#     switch off.
#
# So a single-letter family needs a recorded decision, and the gate
# FAILS when the registry names one that has none.  That converts "a
# reviewer eventually notices a missing family" into "CI fails the
# moment the registry mentions it", which is the property the
# hand-list never had.
REGISTRY_REL = "docs/WORKSTREAM_HISTORY.md"
REGISTRY_FAMILY_RE = re.compile(r"\bWS-([A-Z]{1,2})\b")

# Single-letter families, each with the measurement that decided it.
# `z` is enforced (it costs nothing); the rest are declined because the
# count in parentheses is what enforcing them would flag.
SINGLE_LETTER_ENFORCED = {"z"}                      # measured: 0 collisions
SINGLE_LETTER_DECLINED = {
    "b": "40 — B1..B4 test bindings, 10 in rust/",
    "c": "67 — C2/C3/C9 clause labels, cache constants",
    "d": "24 — hD0..hD3 hypotheses, page-table d0/d1/d2, 0xD00DFEED",
    "e": "5 — e0/e1/e2 bindings and a git sha",
    "f": "40 — F1/F13 finding ids, 8 in rust/",
    "g": "3 — G2, hNeG1/hNeG2 hypotheses",
    "h": "52 — H1/H12d already covered by the `h\\d{2}` subtask rule",
    "i": "2 — `i32`, `i18n`",
    "k": "4 — hK1/hK2 hypotheses, k1/k2 bindings",
    "l": "41 — BOOT_L1_TABLE, BootL1Table, page-table levels, 6 in rust/",
    "m": "40 — _m1.._m11 bindings",
    "n": "14 — deepN1..deepN4 audit bindings",
    "o": "4 — hO1/hO2 hypotheses",
    "q": "6 — Q1/Q9_A labels, q0/q1 bindings",
    "r": "105 — ARM registers r0/r1, hR0/h_r1_eq hypotheses",
    "s": "27 — S1/S2 labels, hInvS1/hInvS2 hypotheses",
    "t": "78 — _t0.._t3 thread bindings, 12 in rust/",
    "u": "57 — AtomicU32/AtomicU64 and friends, 48 in rust/",
    "v": "27 — version stamps, V8_A2 labels",
    "w": "13 — W3/W5a/W7 labels",
    "x": "247 — AArch64 registers x0..x30, 181 in rust/",
    "y": "1 — hY4 hypothesis",
}


def registry_families() -> set[str]:
    """Family letter-codes named as `WS-XX` in the workstream registry."""
    text = read_tracked(REGISTRY_REL)
    if text is None:                    # registry not tracked: nothing to derive
        raise SystemExit(
            f"FAIL: {REGISTRY_REL} is not in the index; the family grammar "
            "cannot be derived. Stage it, or fix REGISTRY_REL.")
    return {m.lower() for m in REGISTRY_FAMILY_RE.findall(text)}


def enforced_families() -> tuple[str, ...]:
    """Families the grammar matches, derived from the registry.

    Raises if the registry names a single-letter family with no recorded
    decision -- the ratchet that stops this list silently falling behind.
    """
    fams = registry_families()
    singles = {f for f in fams if len(f) == 1}
    unclassified = singles - SINGLE_LETTER_ENFORCED - set(SINGLE_LETTER_DECLINED)
    if unclassified:
        raise SystemExit(
            "FAIL: the workstream registry names single-letter families with "
            "no recorded decision: " + ", ".join(sorted(unclassified))
            + "\n      Measure each over the tracked tree, then add it to "
              "SINGLE_LETTER_ENFORCED (if it collides with nothing) or to "
              "SINGLE_LETTER_DECLINED with the count that decided it.")
    # Every two-letter family is enforced automatically: all 17 in the
    # registry today collide with nothing, and the arity is what makes
    # them safe rather than any property of the individual code.
    return tuple(sorted({f for f in fams if len(f) > 1} | SINGLE_LETTER_ENFORCED))


WORKSTREAM_FAMILIES = enforced_families()

COMPONENT_CODES = tuple(
    re.compile(rf"^{f}\d[a-z\d]*$") for f in WORKSTREAM_FAMILIES
) + (
    # `phase5`, and `phase2a` / `phase12b` -- a phase code may carry a
    # letter suffix.  Widening this costs nothing measurable: `phase`
    # followed by a digit matches zero further identifiers across the
    # tracked tree, so the suffix can only ever fire on something new.
    re.compile(r"^phase\d+[a-z]*$"),
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


# A string literal that supplies a LINKER-VISIBLE identifier is code, not
# prose, and must survive the blanking that every other literal gets.
#
# `#[export_name = "phase5_helper"] pub fn semantic() {}` puts the coded
# name in the symbol table while every Rust identifier around it reads
# clean. That matters more here than the equivalent hole elsewhere: the
# Rust scan is a hard zero with no baseline, so this was the one spelling
# that could carry a coded symbol into the kernel binary itself past a
# gate reporting PASS. The assembly and linker-script formats brought
# into scope by the previous round have the same shape in their quoted
# section and symbol names.
#
# Matched against the text PRECEDING the literal, so ordinary prose
# literals — nearly every string in the tree — are unaffected. The
# directive set is deliberately closed: each entry names a construct
# whose string argument becomes a symbol or section name, which is why a
# bare `name = "..."` is not in it.
IDENT_BEARING_STRING = re.compile(
    r"(?:export_name|link_name|link_section"          # Rust attributes
    r"|\.section|\.globa?l|\.type|\.set|\.weak|\.extern|\.size"  # asm
    r"|PROVIDE|ENTRY|KEEP|OUTPUT_ARCH)"               # linker script
    r"\s*[=(\s]\s*$"
)


def keeps_identifiers(text: str, at: int) -> bool:
    """Does the literal starting at `at` name a linker-visible symbol?"""
    line_start = text.rfind("\n", 0, at) + 1
    return IDENT_BEARING_STRING.search(text[line_start:at]) is not None


# An inline-assembly template is assembly SOURCE, not prose, and the
# symbols it declares are linker-visible exactly as `#[export_name]`'s
# are: `global_asm!(".global phase5_helper\nphase5_helper:")` compiles
# to a `phase5_helper` symbol that `nm` lists, while every Rust
# identifier around it reads clean.
#
# The preceding-text test that covers `export_name` cannot cover this.
# A template is routinely several adjacent literals, one per assembly
# line, and only the first has the macro name in front of it -- so what
# is tracked is the SPAN of the macro's argument list, by the same walk
# that already skips strings and comments correctly.  Matching parens
# over raw text would be fooled by either.
#
# The depth counter can still be skewed by a construct the walk does not
# model -- a Rust char literal holding a bracket, `'('`.  An unmatched
# OPENER only holds the span open longer, which scans more and misses
# nothing; an unmatched CLOSER at the span's own depth would end it
# early.  Neither occurs in this tree, whose template operands are
# string literals and `in(reg) x` bindings.
ASM_MACROS = frozenset({"asm", "global_asm", "naked_asm"})


def _opens_asm_macro(text: str, at: int) -> bool:
    """Is the delimiter at `at` an asm macro's argument list?

    Walks backwards over whitespace, the `!`, and the macro name rather
    than matching a fixed-width window: a window that truncates inside
    a longer identifier makes `notasm!(` read as `asm!(`.
    """
    j = at - 1
    while j >= 0 and text[j] in " \t\r\n":
        j -= 1
    if j < 0 or text[j] != "!":
        return False
    end = j
    j -= 1
    while j >= 0 and (text[j].isalnum() or text[j] == "_"):
        j -= 1
    return text[j + 1:end] in ASM_MACROS      # `core::arch::asm!` -> `asm`


def strip_pairs(text: str, line_comment: str, block: tuple[str, str],
                asm_templates: bool = False) -> str:
    """Blank comments and string literals for C-family / Lean syntax."""
    open_b, close_b = block
    out, i, n = [], 0, len(text)
    # Delimiter nesting depth, and the depth at which an asm macro's
    # argument list opened (None outside one).
    nesting, asm_at = 0, None
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
            out.append(text[i:j] if asm_at is not None or keeps_identifiers(text, i)
                       else blank_literal(text[i:j])); i = j
        elif text[i] == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2; continue
                if text[j] == '"':
                    j += 1; break
                j += 1
            out.append(text[i:j] if asm_at is not None or keeps_identifiers(text, i)
                       else blank_literal(text[i:j])); i = j
        else:
            if asm_templates and text[i] in "([{":
                nesting += 1
                if asm_at is None and _opens_asm_macro(text, i):
                    asm_at = nesting
            elif asm_templates and text[i] in ")]}":
                if asm_at == nesting:
                    asm_at = None
                nesting -= 1
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
    # Rust is the only format here that embeds assembly in a literal.
    return strip_pairs(t, "//", ("/*", "*/"), asm_templates=True)


# `<digest>  <name>`, the record `sha256sum` writes and `-c` reads back.
# Two spaces for text mode, ` *` for binary; the name runs to the line
# end.  The digest is blanked and the NAME kept: it is a real filename
# the tree's own trace gate consumes, and a hex run beginning with a
# letter would otherwise tokenise as an identifier.
CHECKSUM_RECORD = re.compile(r"^([ \t]*[0-9a-fA-F]{32,128})([ \t]+\*?)(?=\S)",
                             re.MULTILINE)


def strip_checksum_manifest(text: str) -> str:
    """`.sha256`: blank the digest, KEEP the filename.

    Previously skipped whole, on the reasoning that the companion
    fixture's name is path-scanned anyway.  But the manifest names the
    file it verifies -- that name is what `sha256sum -c` opens -- and
    nothing forces it to equal the companion path, so scanning the path
    by proxy checks a different string than the one the gate is run on.
    """
    return CHECKSUM_RECORD.sub(lambda m: " " * len(m.group(0)), text)


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
    ".sha256": strip_checksum_manifest,
}

# Formats where a hyphen JOINS a name rather than separating operands.
# In Lean, Rust and Python `a-b` is subtraction, and in shell it opens a
# flag, so content there must not be normalised -- but a YAML key, a
# TOML value, a JSON string and a fixture label are all names, and
# `WS-SM-helper` in one of them is the canonical hyphenated spelling
# the rule names first.  Path tokenisation normalises unconditionally
# (a path component is always a name); this is the content-side
# counterpart, applied only where the character cannot be an operator.
# Measured: 34 further coded identifiers become visible, every one a
# real workstream or audit id (`AK6-A`, `WS-B10`, `Z5-AUD-10`).
HYPHEN_JOINS_NAMES = frozenset({
    ".toml", ".yml", ".yaml", ".txt", ".json", ".expected", ".sha256",
})

# Extensions deliberately NOT content-scanned, each with the reason.
# Together with CONTENT_STRIPPERS this must cover every tracked
# non-documentation extension: `format_coverage_gap()` fails on
# anything in neither, so a new file type cannot enter the repository
# with its contents silently unexamined.
#
# This is the second hand-maintained table that kept this gate behind
# the rule.  Four rounds each found a format missing or mis-routed --
# five formats absent at once, then `.sh` pointed at the Python
# stripper, then `.yml`/`.toml` the same way, then `.txt` -- and every
# fix added exactly the entry named.  Requiring an explicit decision
# per extension turns the next one into a CI failure at the moment the
# file lands, which is the only point where someone knows what the
# format is.
NO_CONTENT_SCAN = {
    ".png": "binary image",
    ".lock": "generated by cargo; names come from Cargo.toml, scanned there",
    ".md": "prose (the few outside docs/ are READMEs and templates)",
    "": "extensionless: LICENSE, git hooks, CI helper stubs",
}


def format_coverage_gap() -> set[str]:
    """Tracked non-doc extensions with no recorded scan decision."""
    seen = {Path(p).suffix for p in tracked_all() if not is_doc(p)}
    return seen - set(CONTENT_STRIPPERS) - set(NO_CONTENT_SCAN)


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

        suffix = Path(rel).suffix
        stripper = CONTENT_STRIPPERS.get(suffix)
        if stripper is None or rel not in staged:
            continue
        body = stripper(staged[rel])
        if suffix in HYPHEN_JOINS_NAMES:
            body = body.replace("-", "_")
        for token in IDENTIFIER.findall(body):
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

    gap = format_coverage_gap()
    if gap:
        print("FAIL: tracked file types with no recorded scan decision: "
              + ", ".join(sorted(x or "(no extension)" for x in gap)),
              file=sys.stderr)
        print("      Add a stripper to CONTENT_STRIPPERS, or an entry to "
              "NO_CONTENT_SCAN saying why the contents hold no identifiers.",
              file=sys.stderr)
        print("      Do not point a new suffix at whichever stripper looks "
              "closest -- check its comment and quoting rules first.",
              file=sys.stderr)
        return 1

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
    staged_baseline = read_tracked(BASELINE_REL)
    if staged_baseline is None:
        print(f"FAIL: {BASELINE_REL} is not in the index; there is nothing to "
              "ratchet against. Stage it (see --regenerate-baseline).",
              file=sys.stderr)
        return 1
    raw = json.loads(staged_baseline)
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
