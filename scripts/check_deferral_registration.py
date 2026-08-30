#!/usr/bin/env python3
"""Fail when a source file declares its own deferral untracked.

The project keeps one debt register — the *Registered debt index* in
`docs/WORKSTREAM_HISTORY.md`.  A comment that says "no currently-active plan
file tracks it" is a deferral that has opted out of it: self-describing and
unfindable at once, because a reader can only meet it by opening the file it
lives in.  The register enumerates them instead, and each source comment
points there.

Keeping that true by hand does not work.  Three separate review rounds on the
cut that built the register found the sweep incomplete — first a deferral
living in a documentation file rather than in Lean, then two more in one Lean
file, then five others — every time because the sweep matched one phrasing and
the tree used another.  A person grepping one string is the wrong mechanism,
so this gate is the mechanism instead.

**Compliance is citing the register, not avoiding the words.**  A site may
discuss being untracked as long as the surrounding lines name the register;
what fails is a deferral that declares itself untracked and points nowhere.
That way the narrative files which *describe* the problem keep working, and a
new comment that quietly opts out does not.
"""

from __future__ import annotations

import pathlib
import re
import subprocess
import sys

REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent

# **Every tracked text file**, not a list of roots and suffixes.
#
# The first cut of this gate enumerated five directories and seven suffixes,
# and that allowlist was wrong in three ways at once: `rust/sele4n-hal/src/boot.S`
# (assembly carries `//` comments and is where the boot-path deferrals live),
# the root `README.md` and `CLAUDE.md`, and everything under `.github/`.  A
# deferral does not become tracked by living in a file extension nobody
# enumerated -- and this module already argues, twice, that guessing a list is
# the mistake that kept letting sites through.  So the enumeration is the git
# index, minus the narratives that necessarily quote the phrasing, and minus
# whatever does not decode as UTF-8.
BINARY_SUFFIXES = (".png", ".jpg", ".jpeg", ".gif", ".ico", ".pdf", ".woff",
                   ".woff2", ".ttf", ".zip", ".gz", ".o", ".a", ".so")

# Files whose subject *is* the register or the audit that found it, so they
# necessarily quote the phrasing while describing it.  This list is
# deliberately short and each entry is a narrative, never a deferral site.
NARRATIVE_EXEMPT = {
    "docs/WORKSTREAM_HISTORY.md",       # the register itself
    "CHANGELOG.md",                     # historical per-version narrative
    "docs/planning/UNFINISHED_SMP_WORK.md",  # the audit that reported the gap
    "scripts/check_deferral_registration.py",  # this file's own docstring
}

EXEMPT_PREFIXES = ("docs/dev_history/",)

# "no currently-active plan file tracks it" and its observed variants.  Keyed
# on the *claim* — a plan/workstream not tracking something — rather than on
# any one sentence, since matching one sentence is what kept failing.
UNTRACKED_RE = re.compile(
    # The claim, in both orders it is written:
    #
    #   A. "no <modifiers> plan|workstream <noun> tracks it"
    #        no currently-active plan file tracks it
    #        no concrete plan file tracks it yet
    #        No currently-active workstream plan tracks it
    #   B. "not|never tracked in any <modifiers> plan|workstream"
    #        not tracked in any currently-active workstream plan
    #        is NOT tracked in any currently-active WS-AK plan file
    #
    # The modifier is free text and NOT part of the pattern: keying on
    # `currently-active` made the gate miss `no concrete plan file tracks it`,
    # the sixth phrasing this tree turned out to use.  What makes a deferral
    # untracked is the *relationship* — a negation, a plan or workstream, and
    # a tracking verb — so that is what is matched.
    #
    # The spans are short on purpose.  Text is flattened before matching, and
    # code contains few periods, so a wide `[^.]` bound wanders across
    # unrelated statements: a first attempt at this generalisation matched
    # "runs no unwrap at all (… tracked debt, see the plan …)" in a docstring
    # and "does not declare it tracked" in a Python f-string.  Binding the
    # negation tightly to the noun it negates is what separates the claim from
    # prose that merely contains the same words.
    r"\bno\b\s+(?:[\w'-]+\s+){0,3}(?:plan|workstream)[^.]{0,40}?track"
    r"|\b(?:not|never)\s+tracked\b[^.]{0,60}?(?:plan|workstream)",
    re.I,
)

# A site is compliant when the register is cited near the claim.
REGISTER_RE = re.compile(
    r"Registered debt index|WORKSTREAM_HISTORY", re.I
)

# `row 29`, `rows 24-26`, `rows 24, 25 and 31` — the citation forms the
# re-pointed sites use.  Capturing only the first number made a range's other
# members unchecked: `rows 24-26` passed while 25 and 26 were absent from the
# register, which is the half of the citation a reader actually follows.
ROW_CITE_RE = re.compile(
    r"\brows?\s+(\d+(?:\s*(?:[-\u2013]|,|and)\s*\d+)*)", re.I)
_ROW_RANGE_RE = re.compile(r"(\d+)\s*[-\u2013]\s*(\d+)")
# A range wider than this is prose that happens to contain two numbers, not a
# citation; expanding it would invent hundreds of row numbers to check.
MAX_ROW_SPAN = 100


def cited_rows(blob: str) -> list[int]:
    """Every row number a citation names, ranges expanded."""
    out: list[int] = []
    for m in ROW_CITE_RE.finditer(blob):
        for part in re.split(r"\s*(?:,|and)\s*", m.group(1)):
            rng = _ROW_RANGE_RE.fullmatch(part.strip())
            if rng:
                lo, hi = int(rng.group(1)), int(rng.group(2))
                out.extend(range(lo, hi + 1) if lo <= hi <= lo + MAX_ROW_SPAN
                           else (lo, hi))
            elif part.strip().isdigit():
                out.append(int(part.strip()))
    return out

REGISTER_PATH = "docs/WORKSTREAM_HISTORY.md"
_REGISTER_ROW_RE = re.compile(r"^\|\s*(\d+)\s*\|\s*`([^`]+)`", re.M)


class RegisterIndex:
    """The enumerated debt table, parsed from the register.

    Correlation is deliberately shallow and says so: it confirms that a cited
    row *exists* and that each row's file *exists*.  It cannot confirm the row
    describes the deferral beside it — no scanner can — and the diagnostic no
    longer implies otherwise.
    """

    def __init__(self, text: str) -> None:
        self.rows: dict[int, str] = {}
        for m in _REGISTER_ROW_RE.finditer(text):
            self.rows[int(m.group(1))] = m.group(2)

    @classmethod
    def load(cls, root: pathlib.Path) -> "RegisterIndex":
        # The staged register, for the same reason the sources are staged: a
        # commit that adds a citation and the row it cites must be validated
        # against each other, not against whichever half is on disk.
        return cls(read_indexed(REGISTER_PATH) or "")


CONTEXT_LINES = 6


# Comment punctuation, stripped before joining so a wrapped claim reads as one
# sentence.
_COMMENT_LEAD_RE = re.compile(r"^\s*(?:--+|//+|/\*+|\*+/?|#+|>+)?\s*")


def _flatten(lines: list[str]) -> tuple[str, list[int]]:
    """Join comment lines into one string, with an offset -> line-number map.

    A line-based scan missed a claim wrapped across two lines; widening to a
    two-line window then missed one wrapped across three.  Guessing a window
    size is the same mistake as guessing a prefix list, so there is no window:
    the file is flattened and the *sentence* is the unit, bounded by the period
    the patterns already refuse to cross.
    """
    parts: list[str] = []
    line_of: list[int] = []
    for i, ln in enumerate(lines):
        text = _COMMENT_LEAD_RE.sub("", ln)
        parts.append(text)
        line_of.extend([i] * (len(text) + 1))   # +1 for the joining space
    return " ".join(parts), line_of


def scan_text(rel: str, text: str, register: RegisterIndex | None = None) -> list[str]:
    """Return one finding per untracked claim that is not properly registered.

    A claim is compliant when it cites the register **and**, if it names any
    `row N` — including every member of a range like `rows 24-26` — that row
    exists in the register's enumerated table **and** at least one cited row
    records this very file.  Row existence alone is satisfied by any real row,
    which is no registration of the deferral in front of you.  Citing the
    register while naming a row that does not exist is the failure this
    correlation closes: the diagnostic always said a deferral must be both
    cited and listed, and only the citation was ever checked.
    """
    lines = text.splitlines()
    flat, line_of = _flatten(lines)
    out: list[str] = []
    for m in UNTRACKED_RE.finditer(flat):
        idx = min(m.start(), len(line_of) - 1) if line_of else 0
        i = line_of[idx] if line_of else 0
        lo = max(0, i - CONTEXT_LINES)
        hi = min(len(lines), i + CONTEXT_LINES + 1)
        context = "\n".join(lines[lo:hi])
        if not REGISTER_RE.search(context):
            out.append(f"{rel}:{i + 1}: cites no register -- {lines[i].strip()}")
            continue
        if register is not None:
            rows = cited_rows(context)
            missing = [r for r in rows if r not in register.rows]
            if missing:
                out.append(
                    f"{rel}:{i + 1}: cites row {missing[0]}, which the register's "
                    f"enumerated table does not contain -- {lines[i].strip()}"
                )
            elif rows and not any(register.rows[r] == rel for r in rows):
                # A row number that merely *exists* is not a registration of
                # this deferral: any real row would satisfy that, so a new
                # deferral could cite an arbitrary one and pass.  At least one
                # cited row has to name the file the claim is written in.  Not
                # every row -- a range may legitimately span a group of related
                # sites -- but at least the one that makes this file listed.
                named = ", ".join(f"row {r} -> `{register.rows[r]}`" for r in rows)
                out.append(
                    f"{rel}:{i + 1}: cites {named}, but no cited row names this "
                    f"file, so this deferral is not the one the register lists "
                    f"-- {lines[i].strip()}"
                )
    return out


def tracked_files() -> list[str]:
    """Paths as git sees them.  Walking the working tree instead would scan
    build output and untracked scratch while still missing nothing that
    matters, so the index is both narrower and the right authority: a deferral
    that is not committed is not yet a deferral."""
    try:
        out = subprocess.run(["git", "ls-files", "-z"], cwd=REPO_ROOT,
                             capture_output=True, text=True, check=True).stdout
    except (subprocess.CalledProcessError, FileNotFoundError):
        return []
    return sorted(x for x in out.split("\0") if x)


def files_to_scan() -> list[str]:
    """The paths the gate is responsible for, as the index names them."""
    out: list[str] = []
    for rel in tracked_files():
        if rel in NARRATIVE_EXEMPT:
            continue
        if any(rel.startswith(pre) for pre in EXEMPT_PREFIXES):
            continue
        if pathlib.PurePath(rel).suffix.lower() in BINARY_SUFFIXES:
            continue
        out.append(rel)
    return out


def _decode(raw: bytes) -> str | None:
    """`None` for anything that is not UTF-8 text.  Deciding by content rather
    than by extension is what lets the scan cover `.S`, `.ld`, `.expected` and
    extensionless files without an allowlist to keep in step with the tree."""
    try:
        return raw.decode("utf-8")
    except UnicodeDecodeError:
        return None


def indexed_contents(paths: list[str]) -> dict[str, str]:
    """Each path's **staged** content.

    Enumerating from the index while reading from the working tree is a hole,
    not an inconsistency: stage a source edit carrying an unregistered
    deferral, revert it in the working copy, and the gate reports every file
    clean while the very next commit carries the deferral.  The paths and the
    bytes have to come from the same place, and for a gate the place is the
    index -- what is being committed, not what happens to be on disk.

    One `git cat-file --batch` rather than 683 `git show` calls; the batch
    protocol answers `<sha> <type> <size>` and then the raw bytes, so a
    missing entry is reported per line instead of failing the run.
    """
    if not paths:
        return {}
    try:
        out = subprocess.run(
            ["git", "cat-file", "--batch"], cwd=REPO_ROOT,
            input="".join(f":{p}\n" for p in paths).encode(),
            capture_output=True, check=True).stdout
    except (subprocess.CalledProcessError, FileNotFoundError):
        # No git, or no index (a tarball checkout).  Fall back to the working
        # tree rather than scanning nothing -- narrower, and said out loud by
        # the caller rather than inferred from a pass.
        return {}
    res: dict[str, str] = {}
    i = 0
    for rel in paths:
        nl = out.find(b"\n", i)
        if nl < 0:
            break
        header = out[i:nl].decode("utf-8", "replace")
        i = nl + 1
        if header.endswith(("missing", "ambiguous")):
            continue
        try:
            size = int(header.rsplit(" ", 1)[1])
        except (IndexError, ValueError):
            break
        text = _decode(out[i:i + size])
        i += size + 1                      # blob, then its trailing newline
        if text is not None:
            res[rel] = text
    return res


def read_indexed(rel: str) -> str | None:
    """One file's staged content, falling back to the working tree."""
    try:
        return _decode(subprocess.run(
            ["git", "show", f":{rel}"], cwd=REPO_ROOT,
            capture_output=True, check=True).stdout)
    except (subprocess.CalledProcessError, FileNotFoundError):
        p = REPO_ROOT / rel
        return _decode(p.read_bytes()) if p.is_file() else None


def _self_test() -> int:
    cases: list[tuple[str, bool, str]] = []

    def check(name: str, ok: bool, detail: str = "") -> None:
        cases.append((name, ok, detail))

    # Every phrasing the hand sweep missed must be caught.
    for label, text in [
        ("the phrasing the sweep did match",
         "-- post-1.0 candidate; no currently-active plan file tracks it.\n"),
        ("`not tracked in any currently-active workstream plan`",
         "-- work (not tracked in any currently-active workstream plan).\n"),
        ("`No currently-active workstream plan tracks it`",
         "-- work (DS-M04). No currently-active workstream plan tracks it.\n"),
        ("`NOT tracked in any currently-active WS-AK plan file`",
         "-- scope and is NOT tracked in any currently-active WS-AK plan file.\n"),
        ("a claim split with the register absent",
         "-- recorded as a post-1.0 hardening candidate; no currently-active\n"
         "-- plan file tracks it.\n"),
    ]:
        check(f"caught: {label}", bool(scan_text("X.lean", text)), repr(text))

    # Citing the register is what compliance means.
    check("a site citing the register passes",
          not scan_text("X.lean",
                        "-- no currently-active plan file tracks it, so it is\n"
                        "-- registered in the Registered debt index instead.\n"),
          "should not fire")
    check("a citation within the context window passes",
          not scan_text("X.lean",
                        "-- see docs/WORKSTREAM_HISTORY.md\n" + "-- filler\n" * 4 +
                        "-- no currently-active plan file tracks it.\n"),
          "should not fire")
    check("a citation beyond the context window still fires",
          bool(scan_text("X.lean",
                         "-- see docs/WORKSTREAM_HISTORY.md\n" + "-- filler\n" * 12 +
                         "-- no currently-active plan file tracks it.\n")),
          "should fire")

    # The one real false positive the tree contains must stay quiet.
    check("`currently-active ASID` is not a deferral",
          not scan_text("A.lean",
                        "  rollover never returns a currently-active ASID.\n"),
          "should not fire")
    check("ordinary prose is not a deferral",
          not scan_text("A.lean", "-- The active plan is to ship this.\n"),
          "should not fire")

    # A sentence wrapped across three lines is one sentence.  The first fix
    # here scanned single lines and missed a two-line wrap; the second used a
    # two-line window and missed a three-line one.  Guessing a window size is
    # the same mistake as guessing a prefix list, so there is no window.
    # (Codex review round 8, PR #882 — the reviewer's own three-line split.)
    check("a three-line wrapped claim is caught",
          bool(scan_text("X.lean",
                         "-- This debt is not tracked\n"
                         "-- in any currently-active\n"
                         "-- workstream plan.\n")),
          "should fire")
    check("a four-line wrapped claim is caught",
          bool(scan_text("X.lean",
                         "-- This debt\n-- is not tracked\n"
                         "-- in any currently-active\n-- workstream plan.\n")),
          "should fire")
    check("a period still bounds the claim",
          not scan_text("X.lean",
                        "-- Nothing here is not. The active plan tracks everything.\n"),
          "should not fire")

    # Citing the register is necessary but was also *sufficient* — a site could
    # name a row that does not exist and the gate passed, while its own
    # diagnostic claimed the deferral must be listed there.
    reg = RegisterIndex("| 29 | `scripts/check_deferral_registration.py` | thing |\n")
    HERE = "scripts/check_deferral_registration.py"
    check("a citation naming a nonexistent row is caught",
          any("does not contain" in f for f in scan_text(
              HERE,
              "-- no currently-active plan tracks it; see WORKSTREAM_HISTORY.md row 99.\n",
              reg)),
          "should fire")
    check("a citation naming a real row for this file passes",
          not scan_text(
              HERE,
              "-- no currently-active plan tracks it; see WORKSTREAM_HISTORY.md row 29.\n",
              reg),
          "should not fire")
    # Row existence alone is satisfied by any real row, so a deferral in a
    # different file could cite an arbitrary one and never be listed.
    check("a citation of a real row that names another file is caught",
          any("no cited row names this file" in f for f in scan_text(
              "X.lean",
              "-- no currently-active plan tracks it; see WORKSTREAM_HISTORY.md row 29.\n",
              reg)),
          "should fire")
    check("a range naming this file among others passes",
          not scan_text(
              HERE,
              "-- no currently-active plan tracks it; WORKSTREAM_HISTORY.md rows 29-30.\n",
              RegisterIndex("| 29 | `other/file.lean` | x |\n"
                            "| 30 | `scripts/check_deferral_registration.py` | y |\n")),
          "should not fire: row 30 names this file")
    check("the register table is parsed into rows",
          reg.rows == {29: "scripts/check_deferral_registration.py"}, repr(reg.rows))

    # A range's other members were unchecked: the citation form the comment
    # above ROW_CITE_RE advertises was the one the pattern could not read.
    check("a range citation expands to every member",
          cited_rows("see rows 24-26") == [24, 25, 26]
          and cited_rows("rows 3\u20135") == [3, 4, 5]
          and cited_rows("rows 24, 25 and 31") == [24, 25, 31]
          and cited_rows("row 29") == [29],
          repr(cited_rows("see rows 24-26")))
    check("a range whose later members are absent is caught",
          any("does not contain" in f for f in scan_text(
              "scripts/check_deferral_registration.py",
              "-- no currently-active plan tracks it; WORKSTREAM_HISTORY.md rows 29-31.\n",
              reg)),
          "should fire: 30 and 31 are not in the register")
    check("a range whose members all exist passes",
          not scan_text(
              "scripts/check_deferral_registration.py",
              "-- no currently-active plan tracks it; WORKSTREAM_HISTORY.md rows 29-29.\n",
              reg),
          "should not fire")
    check("an implausibly wide range is not expanded into hundreds of rows",
          cited_rows("rows 1-100000") == [1, 100000],
          repr(cited_rows("rows 1-100000"))[:60])

    # An assembly deferral is a deferral.  `//` is already stripped as comment
    # punctuation, so the only thing that ever excluded `boot.S` was the
    # suffix allowlist -- which is why the fix was to delete the allowlist
    # rather than to add one more entry to it.
    check("a claim in assembly `//` comments is caught",
          bool(scan_text("rust/sele4n-hal/src/boot.S",
                         "// secondary entry; no currently-active plan tracks it.\n")),
          "should fire")
    check("a claim in a YAML `#` comment is caught",
          bool(scan_text(".github/workflows/ci.yml",
                         "# pinned by hand; no concrete plan file tracks it yet.\n")),
          "should fire")

    # The scan surface itself, not just the matcher.  Three real paths the
    # allowlist excluded -- assembly, the repository root, and `.github/` --
    # must be enumerated, and the exemptions must survive the widening.
    scanned = set(files_to_scan())
    if scanned:
        for probe in ("rust/sele4n-hal/src/boot.S", "README.md", "CLAUDE.md",
                      ".github/workflows/lean_action_ci.yml"):
            check(f"scan surface covers {probe}", probe in scanned,
                  "excluded from files_to_scan()")
        check("the narrative exemptions survive the widening",
              not (NARRATIVE_EXEMPT & scanned)
              and not any(r.startswith(EXEMPT_PREFIXES) for r in scanned),
              "an exempt narrative is being scanned")
        check("binaries are excluded by suffix",
              not any(r.endswith(BINARY_SUFFIXES) for r in scanned),
              "a binary is being scanned")

    # The paths and the bytes must come from the same place.  Enumerating the
    # index while reading the working tree let a staged deferral, reverted on
    # disk, pass as clean -- so the gate certified a commit it had not read.
    # Driven through the CLI in a throwaway repository, because the defect
    # lives in how `main` sources its content, not in any helper.
    import shutil
    import tempfile
    src = pathlib.Path(__file__).resolve()
    with tempfile.TemporaryDirectory() as td:
        root = pathlib.Path(td)
        (root / "scripts").mkdir()
        (root / "docs").mkdir()
        shutil.copy(src, root / "scripts" / src.name)
        (root / "docs" / "WORKSTREAM_HISTORY.md").write_text(
            "| 1 | `scripts/probe.S` | a row |\n", encoding="utf-8")
        probe = root / "scripts" / "probe.S"
        probe.write_text("// clean\n", encoding="utf-8")
        git = lambda *a: subprocess.run(["git", *a], cwd=root,
                                        capture_output=True, check=True)
        git("init", "-q", "-b", "main")
        git("config", "user.email", "gate@example.invalid")
        git("config", "user.name", "gate")
        git("add", "-A")
        run = lambda: subprocess.run([sys.executable, "scripts/" + src.name],
                                     cwd=root, capture_output=True, text=True)
        check("a clean index passes", run().returncode == 0, "should pass")

        # Stage the deferral, then revert it on disk: the commit carries it.
        probe.write_text(
            "// no currently-active plan file tracks it.\n", encoding="utf-8")
        git("add", "scripts/probe.S")
        probe.write_text("// clean\n", encoding="utf-8")
        r = run()
        check("a deferral staged but reverted on disk is caught",
              r.returncode != 0 and "probe.S" in r.stdout,
              (r.returncode, r.stdout.strip()[:160]))

        # And the converse: a deferral only in the working tree is not the
        # gate's business, since it is not what would be committed.
        probe.write_text("// clean\n", encoding="utf-8")
        git("add", "scripts/probe.S")          # index clean again
        probe.write_text(                       # deferral on disk only
            "// no currently-active plan file tracks it.\n", encoding="utf-8")
        check("a deferral only in the working tree is not reported",
              run().returncode == 0, "should pass: nothing is staged")

    failed = [c for c in cases if not c[1]]
    for name, ok, detail in cases:
        print(f"  {'PASS' if ok else 'FAIL'}: {name}" + (f" -- {detail}" if not ok else ""))
    print(f"deferral-registration gate self-test: {len(cases)} cases, "
          f"{len(cases) - len(failed)} correct.")
    return 1 if failed else 0


def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        return _self_test()
    register = RegisterIndex.load(REPO_ROOT)
    findings: list[str] = []
    # Every enumerated row must name a file that still exists; a row pointing
    # at a deleted path is a deferral that has quietly lost its site.
    indexed = set(tracked_files())
    for row, path in sorted(register.rows.items()):
        if path not in indexed:
            # The index, for the same reason the sources are read from it: a
            # commit that deletes a registered site while the working copy
            # still holds the file would otherwise pass, and the deletion is
            # what ships.
            findings.append(
                f"{REGISTER_PATH}: row {row} cites `{path}`, which the index "
                f"does not track"
            )
    paths = files_to_scan()
    contents = indexed_contents(paths)
    if not contents and paths:
        # Reading nothing is not a clean run.  Said out loud rather than
        # reported as 683 files with no findings.
        print("FAIL: could not read any file from the git index "
              "(no repository, or no index); nothing was scanned.")
        return 1
    for rel in paths:
        text = contents.get(rel)
        if text is None:
            continue
        findings.extend(scan_text(rel, text, register))
    scanned = len(contents)
    if findings:
        print("FAIL: deferral registration is incomplete.")
        print("Each deferral must cite the *Registered debt index* in "
              "docs/WORKSTREAM_HISTORY.md; a cited `row N` must exist in its "
              "enumerated table, and each row must name a file that exists. "
              "(Whether a row *describes* the deferral beside it is a reader's "
              "judgement, not this gate's.)")
        for f in findings:
            print(f"  {f}")
        return 1
    print(f"PASS: {scanned} tracked text file(s) scanned **as staged**; every "
          f"deferral cites the register, every cited row (ranges expanded) "
          f"exists among the {len(register.rows)} enumerated, and every row's "
          f"path is tracked.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
