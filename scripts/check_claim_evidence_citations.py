#!/usr/bin/env python3
"""Every artefact `docs/CLAIM_EVIDENCE_INDEX.md` names must exist.

The index maps each claim the project makes to the artefact that discharges it.
An identifier in it that resolves to nothing is therefore worse than a missing
row: the row asserts that evidence exists and names a thing that does not, and
the reader who checks is the one who finds out.  Four such citations were live
when this gate was written (WS-RR RR7.34, register finding 93) -- one naming a
Python function the boot-entry check had since replaced with an elaborator
contract, one naming the census's per-op advance by a name it never had, one
naming a theorem retired when the property it witnessed became trivial, and one
a false alarm that this gate has to resolve correctly or it reports noise.

**Both sides are derived.**  The citation set is every backticked identifier-
shaped token in the index; the declaration set is every name the tree declares,
in every language the index cites -- Lean, Rust, assembly, Python, shell -- plus
the artefacts that are *files* rather than declarations (a Rust integration test
is named by its file, and the index cites it the way `cargo test` does).  So a
row added tomorrow is checked the day it lands, and a rename on either side
fails here rather than in a reader's grep.

**Where it cannot decide, it says so rather than guessing.**  A citation is
resolved by *name*, so a name this tree declares somewhere counts even if the
row means a different one -- the gate catches a name that exists nowhere, which
is the failure that actually happened, and does not claim to catch a citation
that resolves to the wrong artefact.  Exemptions live in
`CITATION_EXEMPTIONS` with a reason each, for names the index deliberately
discusses without owning: an external ABI symbol, a language builtin, a retired
name a row is explaining -- and an exemption **no citation needs** fails the
gate, since an exemption nobody reconciles reads exactly like coverage.

**The DOMAIN is derived on both axes (WS-RR RR8.16, `v0.35.194`).**  Two
recognised sets used to stand in for it, and both failed open.

*The column axis.*  The citation pattern required an underscore, with a stated
reason -- single words like `cell` collide with English and would make the gate
noise.  But Lean's convention is snake_case for `theorem`s and **lowerCamelCase
for `def`s**, so every definition name in the tree was outside the gate while
every theorem name was inside it: a row naming a deleted `def` as evidence
reported PASS, and one did (`donationHeadPush`, WS-HP HP7).  Widening to any
backticked word would have needed eight hand exemptions for Lean tactics,
hypothesis binders and English words -- the enumeration this project retires.
The derivation is a **column split**: a name must resolve in an *evidence*
column, where the row says what discharges the claim and how to check it, and
claim prose may name a retired symbol freely.  With the split, the pattern can
be the union of the two naming conventions this tree's declarations actually
use, and the exemption table falls from 18 entries to 4.

*The file axis.*  It scanned one path by name, so a dead **theorem** name --
snake_case, squarely inside the old pattern -- passed everywhere else (three
dead `lockSet_*` citations in `CLAUDE.md`, `v0.35.50`).  The domain is now every
tracked Markdown file holding a table that *declares* an evidence column, which
is three files today and checks the fourth on the day it lands.  `CHANGELOG.md`
and `docs/dev_history/` are excluded because they are **records of past
versions**: a record must be free to name what has since been retired, which is
the same reason claim prose is.  The exclusions are reconciled, so one that
matches no tracked path fails.

Run `--self-test` to check the checker.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check_identifier_naming as _naming  # noqa: E402
import lean_code_view as _lean_code_view  # noqa: E402
import rust_code_view  # noqa: E402

REPO = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
INDEX = "docs/CLAIM_EVIDENCE_INDEX.md"

# The columns in which a name is a **claim of evidence** rather than prose.
# Read off the header row, so a table that declares neither contributes nothing
# and a file that declares one is scanned the day it is added.  `Claim` and
# `Where it is made` are deliberately absent: a claim's own text may name a
# retired symbol (a retirement notice is a claim about absence), which is the
# noise the pre-`v0.35.194` single-word exclusion was standing in for.
EVIDENCE_COLUMNS = frozenset({"artefact", "check it with"})

# Records of past versions, which must be free to name what has since been
# retired.  Excluded by the same reasoning that keeps claim prose out of the
# domain -- and reconciled below, so an entry matching no tracked path fails
# rather than silently narrowing the scan.
HISTORY_PATHS: dict[str, str] = {
    "CHANGELOG.md": (
        "the per-version narrative: an entry states what was true at its "
        "version, so it names symbols later cuts deleted (its one evidence "
        "table, at a v0.33-era entry, cites the metric key `production_loc`)"
    ),
    "docs/dev_history/": (
        "closed audits, completed plans and legacy chapters, retained for "
        "traceability; this project's own conventions tell contributors not to "
        "read them, and holding them to the live tree would be holding history "
        "to a present it does not describe"
    ),
}

# Names the index names without the tree owning them, each with the reason it
# cannot resolve.  A bare list would be an enumeration standing in for a
# derivation; these are the inputs that *legitimately* produce nothing, which is
# the one branch a scanner is allowed to be silent about -- so it is spelled out
# rather than defaulted.
CITATION_EXEMPTIONS: dict[str, str] = {
    "seL4_ReplyRecv": "seL4's own syscall name, cited for fidelity",
    "native_decide": "a Lean tactic, not a declaration",
    "hIdle": (
        "a hypothesis binder of `schedulerNoStall_smp`, named so the row can "
        "say which premise the cited theorem discharges; binders are not "
        "declarations and resolve to nothing by construction"
    ),
    "severAtCut_pop_leaves_no_head": (
        "retired at WS-HP HP6.8 (`v0.35.45`) -- its first conjunct was "
        "`cancelledMiddleCallerPolicy = .severAtCut`, so the policy flip deleted it "
        "rather than restating it; the row names it to say it is gone, which is the "
        "one shape a citation may legitimately not resolve"
    ),
}

# A citation is a backticked token shaped like a declaration this tree writes.
# **Two shapes, because Lean has two conventions** and the old single one was a
# recognised set standing in for a derived one: `theorem`s are snake_case and
# `def`s are lowerCamelCase, so requiring an underscore put every definition
# name in the tree outside the gate.  Rust, Python and shell declarations are
# snake_case, so the first shape covers them too.
#
# A single all-lowercase word (`cell`, `decide`) and a single capitalised word
# (`False`) stay out, for the reason the underscore rule was written with: they
# collide with English, and inside an evidence cell that is prose they would
# make the gate noise.  That exclusion is affordable only because of the column
# split -- over the whole file it was hiding the definitions as well.
CITATION_CANDIDATE = re.compile(r"`([A-Za-z][A-Za-z0-9_]*)`")
_SNAKE_CASE = re.compile(r"[A-Za-z][A-Za-z0-9_]*_[A-Za-z0-9_]+\Z")
_LOWER_CAMEL = re.compile(r"[a-z][A-Za-z0-9]*[A-Z][A-Za-z0-9]*\Z")


def is_citation(name: str) -> bool:
    """Whether a backticked token is shaped like a declaration name."""
    return bool(_SNAKE_CASE.match(name) or _LOWER_CAMEL.match(name))

LEAN_DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:private |protected |partial |noncomputable |unsafe |scoped )*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|axiom"
    r"|macro|notation) +([A-Za-z_«][A-Za-z0-9_.'«»!?]*)", re.M)
# **Boundaries from Rust's grammar, not from Python's `\b`** (PR #895 review
# round 21).  `\b` is defined against `\w`, a Unicode-table question, so it
# finds a boundary inside any identifier spelled with a codepoint this CPython
# and rustc do not both have -- reading `<ident>fn foo` as a declaration of
# `foo`.  The keywords this gate scans for are the ones `rust_code_view`
# already spells; `macro_rules!` is not a keyword at all (it is a macro name
# ending in `!`) so it keeps its own boundary, which the `!` makes exact.
RUST_DECL = re.compile(
    "(?:"
    + "|".join(rust_code_view.keyword(word) for word in
               ("fn", "struct", "enum", "trait", "const", "static", "type", "mod"))
    + r"|(?<![A-Za-z0-9_])macro_rules!)"
    + r"\s+([A-Za-z_][A-Za-z0-9_]*)")
PY_DECL = re.compile(r"^\s*(?:def|class)\s+([A-Za-z_][A-Za-z0-9_]*)"
                     r"|^([A-Za-z_][A-Za-z0-9_]*)\s*[:=]", re.M)
SH_DECL = re.compile(r"^\s*(?:function\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*\(\)"
                     r"|^\s*(?:readonly\s+|export\s+)?([A-Za-z_][A-Za-z0-9_]*)=", re.M)
ASM_DECL = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*:", re.M)


def tracked(root: str, pattern: str) -> list[str]:
    """Files as the index sees them, from git, with a filesystem fallback so the
    self-test's temporary trees work the same way.

    NUL-delimited, because `git ls-files` C-quotes a path holding an
    unusual byte and `str.split()` breaks one holding whitespace into
    fragments that name no file -- a requirement dropped from the domain,
    which is a check nobody runs.  Zero tracked paths carry whitespace
    today, so this costs the tree nothing and closes the next one
    (`v0.35.150`; the same defect `check_identifier_naming` records as its
    own item 8).
    """
    try:
        listed = subprocess.run(["git", "-C", root, "ls-files", "-z", pattern],
                                capture_output=True, check=True).stdout
        out = [p for p in listed.decode("utf-8", "surrogateescape").split("\0") if p]
        if out:
            return out
    except (OSError, subprocess.CalledProcessError):
        pass
    found, suffix = [], pattern.lstrip("*")
    for base, _dirs, files in os.walk(root):
        for name in files:
            if name.endswith(suffix):
                found.append(os.path.relpath(os.path.join(base, name), root))
    return sorted(found)


def _read(root: str, rel: str) -> str:
    try:
        with open(os.path.join(root, rel), "r", encoding="utf-8", errors="replace") as fh:
            return fh.read()
    except OSError:
        return ""


def _code_view(rel: str, text: str) -> str:
    """`text` with its comments and prose blanked, byte-aligned.

    **PR #892 review round 8.**  Every inventory below used to run its
    declaration regex over the raw file, so a symbol that had been deleted or
    renamed while its old name survived in a comment or a string still entered
    the declaration set — and the gate then certified a citation whose artefact
    does not exist, which is precisely the failure it is here to prevent.

    The direction matters and is the one this project's conventions state for a
    scanner that builds a set of **providers**: a provider it invents satisfies
    a requirement that was never met, so unreadable input is *dropped* rather
    than read raw.  A suffix absent from the table below therefore contributes
    nothing, and adding a language the index cites means adding its stripper.

    The strippers are the tree's existing ones — `lean_code_view.strip` and the
    per-language views `check_identifier_naming` already maintains — rather than
    a fourth set written here, because "what counts as code in this language" is
    one question and this file answering it separately is how the views drift.
    """
    if rel.endswith(".lean"):
        return _lean_code_view.strip(text)
    if rel.endswith(".rs"):
        return _naming.strip_rust(text)
    if rel.endswith(".S"):
        return _naming.strip_asm(text)
    if rel.endswith(".py") or rel.endswith(".sh"):
        return _naming.strip_shell(text) if rel.endswith(".sh") else _naming.strip_hash(text)
    return ""


def declared_names(root: str) -> set[str]:
    """Every name the tree declares, across the languages the index cites.

    Read over each language's **code view** (PR #892 review round 8): a name
    that survives only in a comment or a string is not a declaration, and a
    citation it would have satisfied is exactly the stale one this gate exists
    to catch.

    Includes file-derived names, because some artefacts *are* files: a Rust
    integration test is a binary named by its source file and the index cites it
    the way `cargo test` names it, and a script is cited by its stem.  Those
    come from the tracked path list rather than from any file's contents, so
    they are unaffected.
    """
    names: set[str] = set()

    def add(name: str) -> None:
        name = name.strip("«»")
        if name:
            names.add(name)
            names.add(name.split(".")[-1])

    def view(rel: str) -> str:
        return _code_view(rel, _read(root, rel))

    for rel in tracked(root, "*.lean"):
        for m in LEAN_DECL.finditer(view(rel)):
            add(m.group(1))
    for rel in tracked(root, "*.rs"):
        for name in RUST_DECL.findall(view(rel)):
            add(name)
    for rel in tracked(root, "*.S"):
        text = view(rel)
        for name in ASM_DECL.findall(text):
            add(name)
        for name in re.findall(r"\.(?:globl|global)\s+([A-Za-z_][A-Za-z0-9_]*)", text):
            add(name)
    for rel in tracked(root, "*.py"):
        for a, b in PY_DECL.findall(view(rel)):
            add(a or b)
    for rel in tracked(root, "*.sh"):
        for a, b in SH_DECL.findall(view(rel)):
            add(a or b)
    # File-named artefacts: test binaries, scripts, fixtures.
    for pattern in ("*.rs", "*.sh", "*.py", "*.lean", "*.expected", "*.txt", "*.json"):
        for rel in tracked(root, pattern):
            add(os.path.splitext(os.path.basename(rel))[0])
    return names


def markdown_tables(text: str) -> list[tuple[int, list[str], list[tuple[int, list[str]]]]]:
    """Every GitHub-flavoured table in `text`, as `(line, header, rows)`.

    A table is a pipe row followed by a delimiter row; it runs to the first line
    that does not start with a pipe.  Cells split on **unescaped** pipes, since
    the index carries a row whose prose contains a `\\|`.

    Returned rather than filtered here, so the caller decides which tables carry
    evidence and a table that carries none contributes nothing rather than being
    silently skipped.
    """
    lines = text.split("\n")
    out: list[tuple[int, list[str], list[tuple[int, list[str]]]]] = []
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        nxt = lines[i + 1].strip() if i + 1 < len(lines) else ""
        if line.startswith("|") and re.fullmatch(r"\|[-: |]+\|", nxt):
            header = _cells(line)
            j, rows = i + 2, []
            while j < len(lines) and lines[j].strip().startswith("|"):
                rows.append((j + 1, _cells(lines[j].strip())))
                j += 1
            out.append((i + 1, header, rows))
            i = j
        else:
            i += 1
    return out


def _cells(row: str) -> list[str]:
    body = row[1:-1] if row.endswith("|") else row[1:]
    return [c.strip() for c in re.split(r"(?<!\\)\|", body)]


def evidence_files(root: str) -> list[str]:
    """Every tracked Markdown file holding a table that declares an evidence
    column, minus the records of past versions.

    Derived, so a second claim table is checked the day it is written; the
    exclusions are `HISTORY_PATHS`, reconciled by the caller.
    """
    out = []
    for rel in tracked(root, "*.md"):
        if any(rel == p or rel.startswith(p) for p in HISTORY_PATHS):
            continue
        text = _read(root, rel)
        if not text:
            continue
        if any(any(h.strip().lower() in EVIDENCE_COLUMNS for h in header)
               for _ln, header, _rows in markdown_tables(text)):
            out.append(rel)
    return out


def unresolved(root: str,
               exemptions: dict[str, str] | None = None) -> list[str]:
    """Citations in an **evidence column** that resolve to nothing the tree
    declares — plus the gate's own fail-closed conditions.

    `exemptions` defaults to `CITATION_EXEMPTIONS` and is a parameter so the
    witness suite can exercise the reconciliation in both directions against its
    own fixtures; a reconciliation only reachable from the live tree is one no
    case can decide.

    Five things are reported rather than passed, because each reads exactly like
    a clean tree: an index that cannot be read, an index that declares no
    evidence column at all (a renamed header would otherwise silence the whole
    scan), a row whose cell count does not match its header (the gate cannot say
    which column a name is in), a run that finds no citation anywhere, and an
    exemption no citation needs.
    """
    exempt = CITATION_EXEMPTIONS if exemptions is None else exemptions
    text = _read(root, INDEX)
    if not text:
        # Fail closed: an index this gate cannot read is an index it cannot hold
        # to anything, which reads exactly like an index with no defects.
        return [f"{INDEX}: cannot be read, so no citation in it is checked"]
    if not any(any(h.strip().lower() in EVIDENCE_COLUMNS for h in header)
               for _ln, header, _rows in markdown_tables(text)):
        return [f"{INDEX}: no table declares an evidence column "
                f"({', '.join(sorted(EVIDENCE_COLUMNS))}), so the column split "
                f"would scan nothing; a renamed header is a gate defect, not a "
                f"clean index"]
    for path, reason in HISTORY_PATHS.items():
        if not any(rel == path or rel.startswith(path) for rel in tracked(root, "*.md")):
            return [f"{path}: excluded as a record of past versions ({reason}), "
                    f"but no tracked Markdown file matches it -- a stale "
                    f"exclusion narrows the scan silently"]

    names = declared_names(root)
    problems: list[str] = []
    seen: set[str] = set()
    used_exemptions: set[str] = set()
    for rel in evidence_files(root):
        body = _read(root, rel)
        for _ln, header, rows in markdown_tables(body):
            columns = [k for k, h in enumerate(header)
                       if h.strip().lower() in EVIDENCE_COLUMNS]
            if not columns:
                continue
            for line, cells in rows:
                if len(cells) != len(header):
                    problems.append(
                        f"{rel}:{line}: {len(cells)} cell(s) against a "
                        f"{len(header)}-column header, so the gate cannot say "
                        f"which column a name sits in; escape an embedded pipe "
                        f"as `\\|`")
                    continue
                for k in columns:
                    for m in CITATION_CANDIDATE.finditer(cells[k]):
                        name = m.group(1)
                        if not is_citation(name) or name in seen:
                            continue
                        seen.add(name)
                        if name in exempt:
                            used_exemptions.add(name)
                            continue
                        if name in names or name.split(".")[-1] in names:
                            continue
                        problems.append(
                            f"{rel}:{line}: `{name}` is named in the "
                            f"'{header[k].strip()}' column but is declared "
                            f"nowhere in the tree -- a row that names a missing "
                            f"artefact asserts evidence that does not exist; "
                            f"correct the name, or add it to "
                            f"CITATION_EXEMPTIONS with the reason it is not ours")
    if not seen:
        return [f"{INDEX}: no citations found at all; the gate would pass vacuously"]
    for name in sorted(set(exempt) - used_exemptions):
        problems.append(
            f"CITATION_EXEMPTIONS: `{name}` is exempted but no evidence column "
            f"cites it -- an exemption nobody reconciles reads exactly like "
            f"coverage; delete it")
    return problems


def domain_summary(root: str) -> tuple[int, int, int]:
    """`(files, evidence citations, prose citations)` — what the gate scanned
    and what the column split deliberately leaves out.

    The third number is the residue, printed rather than implied: a name in a
    claim's own prose is not a claim that evidence exists, so it is out of
    scope, and saying how many there are is what keeps "out of scope" from
    reading as "none".
    """
    files = evidence_files(root)
    evidence = prose = 0
    for rel in files:
        for _ln, header, rows in markdown_tables(_read(root, rel)):
            columns = {k for k, h in enumerate(header)
                       if h.strip().lower() in EVIDENCE_COLUMNS}
            if not columns:
                continue
            for _line, cells in rows:
                if len(cells) != len(header):
                    continue
                for k, cell in enumerate(cells):
                    hits = sum(1 for m in CITATION_CANDIDATE.finditer(cell)
                               if is_citation(m.group(1)))
                    if k in columns:
                        evidence += hits
                    else:
                        prose += hits
    return len(files), evidence, prose


# ---------------------------------------------------------------------------
# The witness suite.  Each case keeps the citation and breaks its resolution,
# its column, or its shape -- the relations this gate is about.  Deleting a row
# would pass any presence check and prove nothing.
# ---------------------------------------------------------------------------

CLEAN_INDEX = """# Claim / evidence index

| Claim | Where it is made | Check it with | Artefact |
|---|---|---|---|
| A claim | `X.md` | `./scripts/run_it.sh` | `a_real_theorem`, `a_rust_fn`, `aRealDefinition` |
"""
CLEAN_LEAN = ("theorem a_real_theorem : True := trivial\n"
              "def aRealDefinition : Nat := 0\n")
CLEAN_RUST = "pub fn a_rust_fn() {}\n"
# The history paths must exist, or the stale-exclusion check fires -- which is
# itself a case below.
CLEAN_HISTORY = "# Changelog\n\nNothing cited here.\n"
CLEAN_DEV_HISTORY = "# A closed audit\n\nNothing cited here.\n"


def _tree() -> dict[str, str]:
    return {
        INDEX: CLEAN_INDEX,
        "SeLe4n/Sample.lean": CLEAN_LEAN,
        "rust/sample/src/lib.rs": CLEAN_RUST,
        "CHANGELOG.md": CLEAN_HISTORY,
        "docs/dev_history/closed.md": CLEAN_DEV_HISTORY,
    }


def _run(files: dict[str, str], exemptions: dict[str, str] | None = None) -> list[str]:
    with tempfile.TemporaryDirectory() as tmp:
        for rel, body in files.items():
            path = os.path.join(tmp, rel)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(body)
        return unresolved(tmp, {} if exemptions is None else exemptions)


def self_test() -> int:
    cases: list[tuple[str, bool, list[str]]] = []

    def case(label: str, files: dict[str, str], expect_fail: bool,
             exemptions: dict[str, str] | None = None) -> None:
        got = _run(files, exemptions)
        cases.append((label, bool(got) == expect_fail, got))

    case("a clean index resolves", _tree(), False)

    # The instance: a citation whose artefact was renamed.  Every token of the
    # row survives; only the resolution breaks.
    renamed = _tree()
    renamed["SeLe4n/Sample.lean"] = CLEAN_LEAN.replace("a_real_theorem", "a_renamed_theorem")
    case("a renamed Lean artefact fails its citation", renamed, True)

    # The same, one language over.
    rust_renamed = _tree()
    rust_renamed["rust/sample/src/lib.rs"] = CLEAN_RUST.replace("a_rust_fn", "a_renamed_fn")
    case("a renamed Rust artefact fails its citation", rust_renamed, True)

    # **The `v0.35.194` instance.**  Lean's convention is lowerCamelCase for
    # `def`s, so before the widening every definition name was outside the
    # pattern: this rename reported PASS, and one like it did
    # (`donationHeadPush`, WS-HP HP7).  Its control is the clean case above,
    # where the same camelCase name resolves.
    def_renamed = _tree()
    def_renamed["SeLe4n/Sample.lean"] = CLEAN_LEAN.replace("aRealDefinition", "aRenamedDefinition")
    case("a renamed camelCase `def` fails its citation", def_renamed, True)

    # PR #892 review round 8: the mutation that finds a raw-text inventory.
    # The declaration is deleted and its name is KEPT, in a comment and in a
    # string -- the preserving mutation for "is this name declared".  Reading
    # the raw file, the regex found it and the citation resolved; over the code
    # view there is no declaration and the citation fails, which is the whole
    # point of the gate.
    lean_prose_only = _tree()
    lean_prose_only["SeLe4n/Sample.lean"] = (
        "/-\n"
        "theorem a_real_theorem : True := trivial\n"
        "-/\n"
        "def aRealDefinition : Nat := 0\n"
    )
    case("a commented-out Lean declaration does not declare it", lean_prose_only, True)

    rust_prose_only = _tree()
    rust_prose_only["rust/sample/src/lib.rs"] = (
        "// `a_rust_fn` was renamed; this comment is all that is left of it.\n"
        'pub const NOTE: &str = "pub fn a_rust_fn";\n'
    )
    case("a Rust name left only in prose does not declare it", rust_prose_only, True)

    # A namespaced Lean declaration resolves by its final component, the way the
    # index cites it.
    namespaced = _tree()
    namespaced["SeLe4n/Sample.lean"] = ("theorem Foo.Bar.a_real_theorem : True := trivial\n"
                                        "def Foo.aRealDefinition : Nat := 0\n")
    case("a namespaced declaration resolves by its suffix", namespaced, False)

    # A file-named artefact: an integration test is a binary named by its file.
    filed = _tree()
    filed[INDEX] = CLEAN_INDEX.replace("`a_rust_fn`", "`an_integration_test`")
    filed["rust/sample/tests/an_integration_test.rs"] = "#[test] fn t() {}\n"
    case("an artefact named by its file resolves", filed, False)

    # ---- the COLUMN split, in both directions -----------------------------
    # The decisive pair: one dead name, two columns.  A claim's own prose may
    # name a retired symbol -- a retirement notice is a claim about absence --
    # and the same name in the Artefact column is a claim that evidence exists.
    # The citation survives both mutations; only its column moves.
    prose_column = _tree()
    prose_column[INDEX] = (
        "# Claim / evidence index\n\n"
        "| Claim | Where it is made | Check it with | Artefact |\n"
        "|---|---|---|---|\n"
        "| `a_retired_theorem` is deleted | `X.md` | `./scripts/run_it.sh` | `a_real_theorem` |\n")
    case("a dead name in the CLAIM column is out of scope", prose_column, False)
    evidence_column = _tree()
    evidence_column[INDEX] = (
        "# Claim / evidence index\n\n"
        "| Claim | Where it is made | Check it with | Artefact |\n"
        "|---|---|---|---|\n"
        "| A claim | `X.md` | `./scripts/run_it.sh` | `a_retired_theorem`, `a_real_theorem` |\n")
    case("the SAME name in the Artefact column fails", evidence_column, True)
    # ...and in the other evidence column, so the pair is not about one header.
    command_column = _tree()
    command_column[INDEX] = (
        "# Claim / evidence index\n\n"
        "| Claim | Where it is made | Check it with | Artefact |\n"
        "|---|---|---|---|\n"
        "| A claim | `X.md` | `./scripts/run_it.sh`, which exercises "
        "`a_missing_theorem` | `a_real_theorem` |\n")
    case("a dead name in the 'Check it with' column fails", command_column, True)

    # The shape exclusion, which the column split is what makes affordable: a
    # single English word in an evidence cell is prose, not a citation.
    english = _tree()
    english[INDEX] = CLEAN_INDEX.replace("`a_rust_fn`", "`decide`")
    case("a single English word in an evidence cell is not a citation", english, False)

    # ---- the FILE domain, derived -----------------------------------------
    second_file = _tree()
    second_file["docs/OTHER_CLAIMS.md"] = (
        "| Claim | Artefact |\n|---|---|\n| A second claim | `a_missing_theorem` |\n")
    case("a SECOND file with an evidence table is scanned", second_file, True)
    second_prose = _tree()
    second_prose["docs/OTHER_CLAIMS.md"] = (
        "| Claim | Notes |\n|---|---|\n| A second claim | `a_missing_theorem` |\n")
    case("...and a table declaring no evidence column is not", second_prose, False)
    history_file = _tree()
    history_file["CHANGELOG.md"] = (
        "# Changelog\n\n| Artefact | Answer |\n|---|---|\n| `a_retired_theorem` | yes |\n")
    case("a record of past versions may name a retired symbol", history_file, False)
    stale_exclusion = _tree()
    del stale_exclusion["CHANGELOG.md"]
    case("a history exclusion matching no tracked file fails", stale_exclusion, True)

    # ---- the EXEMPTION table, reconciled in both directions ----------------
    exempt = _tree()
    exempt[INDEX] = CLEAN_INDEX.replace("`a_rust_fn`", "`seL4_Fault_tag`")
    case("an exempt external name is accepted", exempt, False,
         {"seL4_Fault_tag": "seL4's own ABI field name"})
    not_exempt = _tree()
    not_exempt[INDEX] = CLEAN_INDEX.replace("`a_rust_fn`", "`seL4_NotAThing_tag`")
    case("a look-alike that is not exempt still fails", not_exempt, True,
         {"seL4_Fault_tag": "seL4's own ABI field name"})
    case("an exemption no evidence column cites fails", _tree(), True,
         {"seL4_Fault_tag": "seL4's own ABI field name"})

    # ---- fail closed, four ways -------------------------------------------
    case("a missing index reports rather than passing", {}, True)
    empty = _tree()
    empty[INDEX] = "# Claim / evidence index\n\nNothing here yet.\n"
    case("an index with no citations reports rather than passing", empty, True)
    # A renamed header silences the index alone, so the case pairs it with a
    # SECOND file whose evidence table is intact: citations exist, the vacuity
    # check is satisfied, and only the header check can fail the run.  Without
    # the second file the case would be decided by the vacuity check instead,
    # and a gate with no header check at all would pass it.
    renamed_header = _tree()
    renamed_header[INDEX] = CLEAN_INDEX.replace(
        "| Claim | Where it is made | Check it with | Artefact |",
        "| Claim | Where it is made | Command | Artefacts |")
    renamed_header["docs/OTHER_CLAIMS.md"] = (
        "| Claim | Artefact |\n|---|---|\n| A second claim | `a_real_theorem` |\n")
    case("an index whose evidence header is renamed reports rather than passing",
         renamed_header, True)
    # The ragged row sits BESIDE a well-formed one whose citation resolves, so
    # `seen` is non-empty and the vacuity check cannot rescue the case: only
    # the split failure can fail it.  Without the second row, skipping the
    # ragged one silently would still report -- as "no citations at all" --
    # and the case would test the wrong assertion.
    ragged = _tree()
    ragged[INDEX] = (
        "# Claim / evidence index\n\n"
        "| Claim | Where it is made | Check it with | Artefact |\n"
        "|---|---|---|---|\n"
        "| A well-formed claim | `X.md` | `./scripts/run_it.sh` | `a_real_theorem` |\n"
        "| A claim with an un | escaped pipe | `./scripts/run_it.sh` | "
        "`a_rust_fn` | `aRealDefinition` |\n")
    case("a row the gate cannot split reports rather than passing", ragged, True)
    # Its control, with a well-formed row beside it for the same reason the
    # ragged case has one: an escape-blind split makes this row ragged, and
    # without a second row the run would fail as "no citations at all" -- the
    # right verdict for the wrong reason.
    escaped = _tree()
    escaped[INDEX] = (
        "# Claim / evidence index\n\n"
        "| Claim | Where it is made | Check it with | Artefact |\n"
        "|---|---|---|---|\n"
        "| A well-formed claim | `X.md` | `./scripts/run_it.sh` | `a_real_theorem` |\n"
        "| A claim with an escaped \\| pipe | `X.md` | `./scripts/run_it.sh` | "
        "`a_rust_fn` |\n")
    case("...while an ESCAPED pipe keeps the row splittable", escaped, False)

    failed = 0
    for label, ok, detail in cases:
        if ok:
            print(f"  PASS: {label}")
        else:
            failed += 1
            print(f"  FAIL: {label} -- got {detail}")
    if failed:
        print(f"SELF-TEST FAILED: {failed} case(s)")
        return 1
    print(f"check_claim_evidence_citations self-test: {len(cases)} cases, all correct.")
    return 0


def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        return self_test()
    problems = unresolved(REPO)
    if problems:
        print(f"FAIL: {len(problems)} unresolved claim-evidence citation(s):")
        for p in problems:
            print(f"  {p}")
        print("\nThe index names the artefact that discharges each claim; a name "
              "that resolves to nothing asserts evidence that does not exist.")
        return 1
    files, evidence, prose = domain_summary(REPO)
    print(f"PASS: every name an evidence column declares is declared in the "
          f"tree -- {evidence} citation(s) across {files} file(s) holding a "
          f"table with an evidence column, {len(CITATION_EXEMPTIONS)} declared "
          f"exemption(s).")
    print(f"      scope: evidence columns only "
          f"({', '.join(sorted(EVIDENCE_COLUMNS))}); {prose} citation(s) in "
          f"claim prose are out of scope, since a claim may name a retired "
          f"symbol, and {len(HISTORY_PATHS)} path(s) are excluded as records "
          f"of past versions.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
