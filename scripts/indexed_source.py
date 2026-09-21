#!/usr/bin/env python3
"""The git index as a gate reads it — and a failure that is not an empty answer.

Four Tier 0 gates derive their whole domain from git: which paths the index
holds, and what bytes each one holds.  Every one of them wrote the same two
things, and every one of them got the same half wrong.

**The duplication.**  `check_deferral_registration.indexed_contents` and
`generate_smp_theorem_manifest.indexed_text` were the same `cat-file --batch`
parser — the same loop, the same `<sha> <type> <size>` header split, the same
`i += size + 1` and the same trailing comment explaining it — under two names
in two files.  That is this project's oldest duplication hazard (*one question
answered in two places will diverge*) at the point where the two answers had
not yet diverged, which is the cheap moment to collapse them.

**The defect.**  Each one answered a failed derivation with an EMPTY one:
`except (CalledProcessError, FileNotFoundError): return {}`, and `{}` is what a
successful scan of a tree with nothing in it returns.  The caller then iterates
over nothing, finds nothing, and the gate prints PASS — so `git` missing, an
index that cannot be read, or a revision that was never fetched all read as *the
tree is clean*.  Measured across `scripts/`: **seven** such sites, in four
gates, where the review that opened this cut reported two.  Every one of them
sat under a docstring stating the contract its own failure branch violated —
`check_deferral_registration`'s promised a working-tree fallback it did not
perform; `generate_smp_theorem_manifest`'s said "the paths and the bytes come
from the same place, and for a gate that place is the index", then evaluated
neither.

This is `CLAUDE.md`'s *a scanner's default branch is a decision* and its
sharper form, *"the gate could not read it" and "the gate checked it and it
differs" must never produce the same verdict* — stated three times in that file
before this cut and violated in seven places at once.  The direction is the one
that rule fixes for a scanner building **requirements**: refuse, because a
requirement dropped is a check nobody runs.

**What this module is not.**  `select_changed_anchors._git` deliberately returns
a status rather than raising, because three of its callers ask git a *question*
whose answer IS the exit status (`rev-parse --verify` — does this ref exist;
`diff --no-index` — do these differ).  A nonzero status there is data, not a
failure, so that helper must not be folded into `run_git`; only the two callers
for which a nonzero status is a *failure* raise.  The distinction is the whole
reason this module raises rather than returning a status: a raise cannot be
mistaken for an answer.
"""

from __future__ import annotations

import subprocess
from typing import Iterable, Sequence


class DerivationFailed(RuntimeError):
    """git could not answer, so the caller's domain is unknown rather than empty.

    Carries the argv, the exit status and git's own stderr, because a gate that
    says only "the derivation failed" sends a reader to reproduce it by hand.
    """

    def __init__(self, argv: Sequence[str], status: int | None, stderr: str,
                 note: str = "") -> None:
        self.argv = list(argv)
        self.status = status
        self.stderr = stderr.strip()
        self.note = note
        shown = " ".join(self.argv)
        parts = [f"`{shown}`"]
        if status is not None:
            parts.append(f"exited {status}")
        if note:
            parts.append(note)
        if self.stderr:
            parts.append(f"git said: {self.stderr}")
        super().__init__("; ".join(parts))


def run_git(repo: str, argv: Sequence[str], *, stdin: bytes | None = None) -> bytes:
    """git's stdout as bytes, or `DerivationFailed`.

    Bytes rather than text: a path or a blob need not be UTF-8, and decoding
    here would make an undecodable byte a crash rather than a per-entry answer.
    """
    full = ["git", *argv]
    try:
        proc = subprocess.run(full, cwd=repo, input=stdin, capture_output=True)
    except (OSError, FileNotFoundError) as exc:
        raise DerivationFailed(full, None, "", f"could not be run ({exc})") from exc
    if proc.returncode != 0:
        raise DerivationFailed(full, proc.returncode,
                               proc.stderr.decode("utf-8", "replace"))
    return proc.stdout


def listed_at(repo: str, ref: str, *pathspecs: str) -> list[str]:
    """Every path `ref` holds matching `pathspecs`, sorted.

    `ref` is `":"` for the index — what is being committed, which is the honest
    domain for a gate that runs pre-commit — or any tree-ish for a revision.
    Both arms use `-z`, so a path containing whitespace or a byte git would
    otherwise C-quote survives as one entry; splitting `git ls-files` on
    whitespace breaks such a path into fragments that name no file, and the read
    then fails and is swallowed.
    """
    if ref == ":":
        argv = ["ls-files", "-z", "--", *pathspecs]
    else:
        argv = ["ls-tree", "-r", "-z", "--name-only", ref, "--", *pathspecs]
    out = run_git(repo, argv)
    return sorted(p for p in out.decode("utf-8", "surrogateescape").split("\0") if p)


def indexed_contents(repo: str, paths: Iterable[str]) -> dict[str, str]:
    """Each path's **staged** text, in one `git cat-file --batch`.

    Enumerating from the index and then reading the working tree is a hole, not
    an inconsistency: stage an edit, revert it on disk, and the gate reports
    every file clean while the very next commit carries the change.  The paths
    and the bytes have to come from the same place, and for a gate that place is
    the index.

    Three outcomes, deliberately distinguished:

    * a path git reports `missing` or `ambiguous` is **absent from the result**
      — that is git answering per entry, not a derivation failure, so a caller
      reading "not in the dict" as "not in the index" is right;
    * a blob that is not UTF-8 is likewise absent, because deciding text by
      content rather than by extension is what lets a scan cover `.S`, `.ld`,
      `.expected` and extensionless files with no allowlist to keep in step;
    * a header this parser cannot read **raises**.  The superseded copies
      `break` there, returning the prefix they had managed to parse — which is
      the module's own defect one level in, since a truncated result is
      indistinguishable from a complete one and the caller reads it as the whole
      domain.

    The request stream is NUL-framed, as `listed_at`'s listing is and for the same
    reason: a tracked path may contain a newline.  See `parse_batch` for what the
    superseded line framing cost.
    """
    wanted = list(paths)
    if not wanted:
        return {}
    out = run_git(repo, ["cat-file", "--batch", "-Z"],
                  stdin=b"".join(b":" + p.encode("utf-8", "surrogateescape") + b"\0"
                                 for p in wanted))
    return parse_batch(out, wanted)


def parse_batch(out: bytes, wanted: list[str]) -> dict[str, str]:
    """`cat-file --batch -Z` output, entry by entry.

    Separated from the call so the self-test can drive the REFUSALS: git does not
    emit a truncated stream or an unreadable header on demand, so a check that
    could only run git could not witness the two arms that distinguish this parser
    from the two it replaces.

    **NUL-framed in both directions, because a newline occurs in the data**
    (PR #897's review, `v0.35.150`).  The superseded framing wrote one request per
    LINE and read one header per line, and a path is a byte string that may hold a
    newline -- which `listed_at` deliberately preserves, `-z` being exactly what it
    buys.  One such path therefore split into two requests, git answered three
    times for two wanted entries, and the parser paired response 1 with the
    newline-bearing path and response 2 with its NEIGHBOUR: measured, a two-file
    index in which one name holds a newline returned `{}` -- **both** files absent,
    no exception -- so every gate reading the staged domain through this helper
    reported a clean tree.  A delimiter that can occur in the data is not a
    delimiter, and the failure direction here is the one this project refuses: a
    requirement dropped from the domain is a check nobody runs.

    `-Z` is git's own answer (`git cat-file -h`: "stdin and stdout is
    NUL-terminated"); `-z`, which frames only the input, is documented as
    deprecated because the OUTPUT stays ambiguous.  The header is decoded with
    `surrogateescape` for the same reason the request is encoded with it: git
    echoes the request back on a `missing` line, and a path need not be UTF-8.
    """
    res: dict[str, str] = {}
    i = 0
    for n, rel in enumerate(wanted):
        nul = out.find(b"\0", i)
        if nul < 0:
            raise DerivationFailed(
                ["git", "cat-file", "--batch", "-Z"], 0, "",
                f"output ended after {n} of {len(wanted)} entries")
        header = out[i:nul].decode("utf-8", "surrogateescape")
        i = nul + 1
        if header.endswith((" missing", " ambiguous")):
            continue
        try:
            size = int(header.rsplit(" ", 1)[1])
        except (IndexError, ValueError):
            raise DerivationFailed(
                ["git", "cat-file", "--batch", "-Z"], 0, "",
                f"unreadable header for {rel!r}: {header!r}") from None
        # The declared size is CHECKED against the framing, not trusted.  A
        # `find` for the next NUL re-synchronises after any drift -- an entry
        # started one byte late still yields a header whose trailing size token
        # parses -- so an off-by-one in this walk is absorbed and silently
        # returns a different blob's bytes.  Asking that the byte at the declared
        # size IS the terminator makes the two agree, which is the relation the
        # `+ 1` below only assumes.
        if out[i + size:i + size + 1] != b"\0":
            raise DerivationFailed(
                ["git", "cat-file", "--batch", "-Z"], 0, "",
                f"the entry for {rel!r} declares {size} byte(s) but is not "
                f"NUL-terminated there")
        try:
            res[rel] = out[i:i + size].decode("utf-8")
        except UnicodeDecodeError:
            pass                                # not text; the caller decides
        i += size + 1                           # blob, then its trailing NUL
    # ONE response per request, no more.  git emits exactly one entry per input
    # record, so a surplus means the request stream was not the one this walk
    # thinks it sent -- which is precisely how the superseded line framing failed:
    # a path holding a newline became two requests, git answered three times for
    # two wanted entries, and the walk paired response 1 with that path and
    # response 2 with its NEIGHBOUR while ignoring the third.  It is also what
    # makes the walk's own arithmetic decidable: `find` re-synchronises on the
    # next NUL, so a drift inside an oid is absorbed at every entry and shows up
    # only here, at the end.
    if i != len(out):
        over = len(out) - i
        raise DerivationFailed(
            ["git", "cat-file", "--batch", "-Z"], 0, "",
            (f"{over} byte(s) of response remain" if over > 0
             else f"the walk ran {-over} byte(s) past the response")
            + f" after all {len(wanted)} requested entries were read")
    return res


# ---------------------------------------------------------------------------
# Self-test
#
# Every case here breaks a RELATION and keeps the tokens, because the defect
# this module exists to close survives any check that merely deletes something:
# each superseded site still *called* git and still *returned a dict*.  What was
# wrong was which value it returned when the call failed, so the decisive cases
# are the ones where git fails and a result is still demanded.
# ---------------------------------------------------------------------------

#: A git subcommand that LISTS PATHS.  Derived from what each one prints rather
#: than from where a defect was found: these are the subcommands whose output is
#: one path per record, so the record separator has to be one a path cannot hold.
PATH_LISTING_SUBCOMMANDS = frozenset({
    "ls-files", "ls-tree", "diff", "diff-index", "diff-tree", "status",
})

#: The options that make such an invocation PRINT a bare path list.
#:
#: `--error-unmatch` is deliberately absent: it prints nothing on success and is
#: a membership PREDICATE whose answer is the exit status, so its record
#: separator is not a question anyone asks.  An option that does not make git
#: print paths does not need them framed.
PATH_LISTING_OPTIONS = frozenset({
    "--name-only", "--name-status", "--others", "--cached", "--modified",
    "--deleted", "--porcelain",
})

#: ...and the framing that makes the record separator NUL.
NUL_FRAMING = frozenset({"-z", "-Z", "--null"})


PROCESS_RUNNERS = frozenset({"run", "Popen", "check_output", "check_call",
                            "call"})
"""The `subprocess` entry points that start a process.

Named rather than derived because they are another library's surface, not this
tree's: a runner it gains is a line in this set, and one it does not have cannot
be invented by any spelling here.
"""


def _git_wrapper_names(tree) -> "set[str]":
    """The module's own functions that run git, by what their bodies DO.

    A function whose body starts a process whose argv begins with the literal
    `"git"` is a git wrapper, whatever it is called -- so a call to it carries a
    git argv even though nothing in the call site says `git`.  Measured on the
    tracked `scripts/*.py`: 30 such functions, and six unframed listing call
    sites that reach one through a helper named `g`.

    Intra-module, deliberately: `ast` can decide which names this file binds and
    cannot decide what an imported name denotes, so a wrapper imported from
    elsewhere is outside this derivation.  The caller keeps a name test beside
    it for that case, which over-approximates and therefore fails toward
    reporting.
    """
    import ast
    out: "set[str]" = set()
    for fn in ast.walk(tree):
        if not isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        for node in ast.walk(fn):
            if not isinstance(node, ast.Call):
                continue
            callee = node.func
            name = (callee.attr if isinstance(callee, ast.Attribute)
                    else getattr(callee, "id", ""))
            if name not in PROCESS_RUNNERS:
                continue
            argvs = list(node.args) + [k.value for k in node.keywords
                                       if k.arg in (None, "args")]
            for arg in argvs:
                if not isinstance(arg, (ast.List, ast.Tuple)) or not arg.elts:
                    continue
                head = arg.elts[0]
                if isinstance(head, ast.Constant) and head.value == "git":
                    out.add(fn.name)
    return out


def _python_git_argvs(text: str):
    """`(line, argv)` for every call in `text` that runs git, via `ast`.

    **A quoted message is not an invocation, and a call's whole string-argument
    SET is not its argv.**  Matching the line reported
    `f"FAIL: ... \\`git ls-files --others "` -- an error string naming the command
    it explains.  Matching every string argument of a call then reported six
    fixture-builder calls whose arguments happen to include an unrelated `"diff"`
    and an unrelated `"--cached"`: that is a set standing in for a sequence,
    which is this tree's own presence-for-relation defect inside the check
    written to close one.

    So an argv is CONTIGUOUS and is identified two ways, both structural: a
    list or tuple argument whose first element is `"git"`
    (`subprocess.run(["git", ...])`), or a call to a **git wrapper**, whose
    positional string arguments are the argv with the subcommand first.

    **A wrapper is DERIVED, not named** (`v0.35.154`, found by this cut's own
    anchor sweep).  The first draft recognised a wrapper by its callee's final
    name component ending in `git` -- a resemblance, and the measurement is what
    retired it: over the tracked `scripts/*.py` there are **30** functions that
    run git and **6** unframed listing call sites reaching one of them through a
    helper named `g`, every one of which this check reported as clean.  That is
    *a helper the scanner cannot see is a spelling that evades the metric*, in the
    check written to close a domain miss.  `_git_wrapper_names` is the relation:
    a function whose body runs a process whose argv begins with the literal
    `"git"` IS a git wrapper, whatever it is called, and the resolution is
    intra-module because that is what `ast` can decide -- a wrapper imported from
    elsewhere is out of reach and the docstring says so rather than the check
    guessing.  The name test is KEPT beside it, as a pin for the cross-module
    case the derivation cannot see; the two are complementary, not redundant.

    A file that does not parse yields nothing -- the same answer as "contains no
    call", and the caller's domain comes from the git index, which
    `indexed_contents` already refuses to read past.
    """
    import ast
    try:
        tree = ast.parse(text)
    except SyntaxError:
        return
    wrappers = _git_wrapper_names(tree)

    def strings(seq):
        return [e.value for e in seq
                if isinstance(e, ast.Constant) and isinstance(e.value, str)]

    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        line = getattr(node, "lineno", 0)
        for a in node.args:
            if isinstance(a, (ast.List, ast.Tuple)):
                words = strings(a.elts)
                if words and words[0] == "git":
                    yield line, words[1:]
        fn = node.func
        name = fn.attr if isinstance(fn, ast.Attribute) else getattr(fn, "id", "")
        if name and (name in wrappers
                     or name.lower().rstrip("_").endswith("git")):
            words = strings(node.args)
            if words:
                yield line, words


def _shell_git_argvs(text: str):
    """`(line, [words])` for every command in `text` whose HEAD word is `git`.

    **A quoted pattern is not an invocation either.**  A Tier 3 anchor spells the
    very call this check is about inside an `rg` pattern; requiring `git` to be a
    command HEAD -- at the start, or after a `|`, `&&`, `;`, `(`, `<(`, `$(` --
    is what tells the two apart, and it is the same question `test_lib.sh`'s own
    classifier asks of an anchor's head.
    """
    import re
    head = re.compile(r"(?:^|[|&;(]|\$\(|<\()\s*(?:!\s*)?git\s+(?P<rest>[^\n|&;)]*)")
    for n, line in enumerate(text.splitlines(), 1):
        for m in head.finditer(line):
            words = [w.strip("'\"") for w in m.group("rest").split()]
            if words:
                yield n, words


def unframed_path_listings(root: "pathlib.Path") -> list[str]:
    """Every tracked script that lists paths from git without NUL framing.

    **A DELIMITER THAT CAN OCCUR IN THE DATA IS NOT A DELIMITER.**  A tracked
    path is a byte string that may hold any byte but NUL and `/`, and git prints
    one containing a newline, a quote or a backslash in its C-quoted form --
    `"tests/a\\nb.lean"`, quotes and all.  A line-reading consumer then takes
    that spelling for the path, and what happens next depends on the consumer:
    `select_changed_anchors` relates a path that does not exist to every anchor
    target, matches none, and reports a CLEAN SWEEP; the pre-commit hook asks
    `git show ":<quoted>"`, gets nothing, and its `sorry` check passes.  Both
    fail OPEN and both are silent.  Measured on the hook before the fix: a
    staged `$'a\\nb.lean'` holding `theorem bad : True := by sorry` produced no
    finding at all.

    **This check exists because the rule had already been swept once.**
    `v0.35.150` found the class in this module's own `cat-file --batch` loop,
    swept seven sibling listings, and missed five -- the two
    `select_changed_anchors` sites PR #897's review then reported, and three in
    the pre-commit hook that only a sweep for the *question* would find.  A rule
    restated twice gets a check rather than a third telling.

    It reads the git INDEX, so what it checks is what is being committed, and it
    resolves each line into the structure it stands for -- a Python call's
    argument list, a shell command's head -- because a diagnostic string and a
    Tier 3 anchor both spell an invocation without being one.
    """
    out: list[str] = []
    paths = listed_at(str(root), ":", "scripts/*.py", "scripts/*.sh", "*.sh")
    for rel, text in sorted(indexed_contents(str(root), paths).items()):
        walk = _python_git_argvs if rel.endswith(".py") else _shell_git_argvs
        for line, words in walk(text):
            ws = set(words)
            if not (ws & PATH_LISTING_SUBCOMMANDS):
                continue
            if not (ws & PATH_LISTING_OPTIONS):
                continue
            if ws & NUL_FRAMING:
                continue
            out.append(
                f"{rel}:{line}: lists paths from git without NUL framing "
                f"(`-z`), so a path holding a newline, a quote or a backslash "
                f"arrives C-quoted and is taken for the path: {' '.join(words)[:90]}")
    return out


def _self_test() -> int:
    import os
    import subprocess as sp
    import sys
    import tempfile

    failures: list[str] = []

    def check(name: str, ok: bool, detail: object = "") -> None:
        if ok:
            print(f"  ok   {name}")
        else:
            print(f"  FAIL {name}: {detail}")
            failures.append(name)

    def value(fn):
        """`fn()`, or the refusal it raised.

        ANY exception on a SUCCESS-path call is a failure of that case and not of
        the harness.  Letting one escape as a traceback aborts the run, so every
        case after it is skipped and ONE MUTATION CAN MASK ANOTHER -- the hazard
        this project recorded one gate over (`v0.35.124`).  Returning the
        exception makes the comparison fail and prints it as the case's detail,
        which is the gate's own voice.

        Deliberately `Exception` and not `DerivationFailed`: a mutation that
        breaks the request ENCODING raises `UnicodeEncodeError` from inside
        `indexed_contents`, which is the module crashing rather than answering --
        the very thing a case must be able to report.  Narrowing it to the
        module's own refusal would leave exactly that mutation aborting the run.
        """
        try:
            return fn()
        except Exception as exc:                # noqa: BLE001 -- see above
            return exc

    with tempfile.TemporaryDirectory() as td:
        root = os.path.join(td, "repo")
        os.makedirs(os.path.join(root, "docs"))
        git = lambda *a: sp.run(["git", *a], cwd=root, check=True,
                                capture_output=True)
        git("init", "-q", "-b", "main")
        git("config", "user.email", "gate@example.invalid")
        git("config", "user.name", "gate")

        plain = os.path.join(root, "docs", "a.md")
        spaced = os.path.join(root, "docs", "a name.md")
        binary = os.path.join(root, "docs", "b.bin")
        with open(plain, "w", encoding="utf-8") as fh:
            fh.write("staged text\n")
        with open(spaced, "w", encoding="utf-8") as fh:
            fh.write("spaced\n")
        with open(binary, "wb") as fh:
            fh.write(b"\xff\xfe not utf-8")
        git("add", "-A")

        # A path with whitespace survives, which is what `-z` buys.
        listed = value(lambda: listed_at(root, ":"))
        check("listed_at names every indexed path, whitespace included",
              listed == ["docs/a name.md", "docs/a.md", "docs/b.bin"], listed)
        md = value(lambda: listed_at(root, ":", "*.md"))
        check("listed_at honours a pathspec",
              md == ["docs/a name.md", "docs/a.md"], md)

        # THE decisive case for `indexed_contents`: the index, not the disk.
        with open(plain, "w", encoding="utf-8") as fh:
            fh.write("WORKING TREE\n")
        got = value(lambda: indexed_contents(root, ["docs/a.md"]))
        check("indexed_contents reads the INDEX, not the working tree",
              got == {"docs/a.md": "staged text\n"}, got)

        # THE decisive case for the framing: a tracked path containing a NEWLINE.
        # Under the superseded line-framed request this returned `{}` -- the
        # newline-bearing path AND its readable neighbour both absent, with no
        # exception -- so a gate reading the staged domain reported a clean tree.
        # It is a git-driven case rather than a `parse_batch` fixture because what
        # was wrong is the REQUEST framing, which a fixture cannot exercise.
        newline_named = "docs/two\nlines.md"
        with open(os.path.join(root, newline_named), "w", encoding="utf-8") as fh:
            fh.write("newline-named\n")
        # Only this path: a blanket `add -A` would re-stage the working-tree edit
        # the case above made, and so would quietly undo the index/disk split the
        # next check is about.
        git("add", "--", newline_named)
        both = value(lambda: indexed_contents(
            root, [newline_named, "docs/a name.md"]))
        check("a path containing a NEWLINE reads back, and so does its neighbour",
              both == {newline_named: "newline-named\n",
                       "docs/a name.md": "spaced\n"}, both)
        git("rm", "-q", "-f", "--", newline_named)

        # ...and a path whose BYTES are not UTF-8.  `listed_at` decodes with
        # `surrogateescape`, so such a name comes back carrying lone surrogates,
        # and a plain `.encode("utf-8")` of the request raises on it -- which is
        # a crash where the module's contract is a per-entry answer.
        raw_named = os.fsdecode(b"docs/raw-\xff.md")
        with open(os.path.join(root, raw_named), "w", encoding="utf-8") as fh:
            fh.write("raw-named\n")
        git("add", "--", raw_named)
        raw = value(lambda: indexed_contents(root, [raw_named]))
        check("a path whose bytes are not UTF-8 reads back",
              raw == {raw_named: "raw-named\n"}, raw)
        git("rm", "-q", "-f", "--", raw_named)

        # git's own per-entry answers are answers, not failures.
        got = value(lambda: indexed_contents(
            root, ["docs/a.md", "docs/nope.md", "docs/b.bin"]))
        check("a path git reports missing is absent from the result",
              not isinstance(got, dict) or "docs/nope.md" not in got, got)
        check("a blob that is not UTF-8 is absent from the result",
              not isinstance(got, dict) or "docs/b.bin" not in got, got)
        check("the readable neighbours still come back",
              got.get("docs/a.md") == "staged text\n", got)

        # The `ls-tree` arm's SUCCESS path, which the refusal case below cannot
        # reach: without this, a typo in the revision spelling would be silent
        # and only the raise would be exercised.  The commit holds the three
        # staged files; the working tree has since been edited, which is what
        # makes reading a revision different from reading the disk.
        git("commit", "-q", "-m", "fixture")
        at_head = value(lambda: listed_at(root, "HEAD"))
        check("listed_at reads a REVISION, not just the index",
              at_head == ["docs/a name.md", "docs/a.md", "docs/b.bin"], at_head)
        one = value(lambda: listed_at(root, "HEAD", "docs/a.md"))
        check("a revision honours a pathspec too", one == ["docs/a.md"], one)

        # A derivation that FAILED must not answer like one that found nothing.
        try:
            listed_at(root, "refs/heads/never-fetched")
        except DerivationFailed as exc:
            check("a ref that does not exist RAISES rather than listing nothing",
                  "never-fetched" in str(exc) and "exited" in str(exc), str(exc))
        else:
            check("a ref that does not exist RAISES rather than listing nothing",
                  False, "returned normally")

        try:
            run_git(os.path.join(td, "no-such-directory"), ["status"])
        except DerivationFailed as exc:
            check("git that cannot be run RAISES", "could not be run" in str(exc)
                  or "exited" in str(exc), str(exc))
        else:
            check("git that cannot be run RAISES", False, "returned normally")

        # The stderr is carried, because "the derivation failed" alone sends a
        # reader to reproduce it by hand.
        try:
            run_git(root, ["cat-file", "-p", "0000000000000000000000000000000000000000"])
        except DerivationFailed as exc:
            check("the refusal carries git's own stderr", bool(exc.stderr), repr(exc.stderr))
        else:
            check("the refusal carries git's own stderr", False, "returned normally")

    # The two arms git cannot be asked to produce.  Both are the superseded
    # parsers' `break`: a PREFIX of the domain, indistinguishable from all of it.
    ok_stream = b"deadbeef blob 3\0abc\0"
    check("a well-formed stream parses", parse_batch(ok_stream, ["x"]) == {"x": "abc"},
          parse_batch(ok_stream, ["x"]))
    # A blob whose CONTENT holds a newline is one entry, not two: the framing is
    # the size and the NUL, so nothing in the data can end an entry early.
    nl_blob = b"deadbeef blob 7\0a\nb\nc\nd\0cafe blob 1\0z\0"
    check("a blob containing newlines is ONE entry",
          parse_batch(nl_blob, ["x", "y"]) == {"x": "a\nb\nc\nd", "y": "z"},
          parse_batch(nl_blob, ["x", "y"]))
    try:
        parse_batch(b"deadbeef blob 3\0abc\0", ["x", "y"])
    except DerivationFailed as exc:
        check("a TRUNCATED stream raises rather than returning the prefix",
              "1 of 2" in str(exc), str(exc))
    else:
        check("a TRUNCATED stream raises rather than returning the prefix",
              False, "returned a prefix")
    try:
        parse_batch(b"deadbeef blob 3\0abc\0cafe blob 1\0z\0", ["x"])
    except DerivationFailed as exc:
        check("a SURPLUS response raises -- one entry per request",
              "remain after" in str(exc), str(exc))
    else:
        check("a SURPLUS response raises -- one entry per request",
              False, "returned quietly")
    try:
        parse_batch(b"deadbeef blob 4\0abc\0", ["x"])
    except DerivationFailed as exc:
        check("a size that overruns its terminator raises",
              "not \nNUL-terminated".replace("\n", "") in str(exc), str(exc))
    else:
        check("a size that overruns its terminator raises",
              False, "returned quietly")
    try:
        parse_batch(b"deadbeef blob NOT-A-NUMBER\0abc\0", ["x"])
    except DerivationFailed as exc:
        check("an unreadable header raises rather than stopping quietly",
              "unreadable header" in str(exc), str(exc))
    else:
        check("an unreadable header raises rather than stopping quietly",
              False, "returned quietly")
    miss = parse_batch(b":x missing\0", ["x"])
    check("a `missing` line is an ANSWER, not a refusal", miss == {}, miss)

    # ---------------------------------------------------------------------
    # The NUL-framing discipline (`v0.35.154`).  Its witnesses are synthetic,
    # because the live tree is clean and a check that cannot fire is
    # indistinguishable from one that is wrong; the live sweep then runs after
    # them, so the tree is held to what the witnesses pin.
    # ---------------------------------------------------------------------
    import pathlib as _pl

    for name, py, want in [
        ("an unframed `git diff --name-only` is reported",
         'subprocess.run(["git", "diff", "--name-only"])', True),
        ("...and the same call with `-z` is not",
         'subprocess.run(["git", "diff", "-z", "--name-only"])', False),
        ("an unframed `_git(\"ls-files\", \"--others\")` is reported",
         '_git("ls-files", "--others")', True),
        ("...and the same helper call with `-z` is not",
         '_git("ls-files", "--others", "-z")', False),
        # The three shapes that spell an invocation WITHOUT being one -- each
        # was reported by a line-matching draft of this check.
        ("a diagnostic STRING naming the command is not an invocation",
         'x = f"FAIL: `git ls-files --others` exited {code}"', False),
        ("a call whose string arguments merely INCLUDE the words is not an argv",
         'subprocess.run(["git", "add", "-A"], env={"D": "diff", "C": "--cached"})',
         False),
        ("an `--error-unmatch` membership test needs no framing",
         '_git("ls-files", "--error-unmatch", path)', False),
        # **A wrapper is what a function DOES, not what it is called.**  This
        # pair is the whole measurement of the derived-wrapper widening: on the
        # live tree the resemblance-based draft missed six real sites reached
        # through a helper named `g`, and with those fixed the tree is clean, so
        # the case has to be planted.  `g` gives the scanner nothing -- no
        # `git` in its name, no literal argv at the call -- and is recognised
        # only because its BODY runs a process whose argv begins with "git".
        ("a listing through a wrapper whose NAME says nothing is reported",
         'def g(*a):\n'
         '    return subprocess.run(["git", *a])\n'
         'g("ls-files", "--others")\n', True),
        ("...and the same wrapper call with `-z` is not",
         'def g(*a):\n'
         '    return subprocess.run(["git", *a])\n'
         'g("ls-files", "--others", "-z")\n', False),
        # The control that keeps the derivation from becoming "any helper": a
        # function of the same shape that runs something else is not a wrapper,
        # so a listing-shaped call to it is not a git invocation.
        ("a same-shaped helper that runs something else is NOT a wrapper",
         'def g(*a):\n'
         '    return subprocess.run(["hg", *a])\n'
         'g("diff", "--name-only")\n', False),
    ]:
        got = bool(list(
            (line, argv) for line, argv in _python_git_argvs(py)
            if set(argv) & PATH_LISTING_SUBCOMMANDS
            and set(argv) & PATH_LISTING_OPTIONS
            and not (set(argv) & NUL_FRAMING)))
        check(f"nul-framing '{name}'", got == want, f"got {got}, want {want}")

    for name, sh, want in [
        ("an unframed shell `git diff --cached --name-only` is reported",
         'mapfile -t A < <(git diff --cached --name-only)', True),
        ("...and the same command with `-z` is not",
         'while read -r -d "" f; do :; done < <(git diff --cached -z --name-only)',
         False),
        ("a quoted PATTERN naming the command is not an invocation",
         "run_check \"INVARIANT\" rg -F -n 'git diff --cached --name-only' f.py",
         False),
    ]:
        got = bool(list(
            (line, words) for line, words in _shell_git_argvs(sh)
            if set(words) & PATH_LISTING_SUBCOMMANDS
            and set(words) & PATH_LISTING_OPTIONS
            and not (set(words) & NUL_FRAMING)))
        check(f"nul-framing '{name}'", got == want, f"got {got}, want {want}")

    live = unframed_path_listings(_pl.Path(REPO_ROOT if "REPO_ROOT" in globals()
                                           else "."))
    check("nul-framing 'the tree lists no paths from git unframed'",
          not live, "\n    ".join(live))

    if failures:
        print(f"FAIL: indexed_source --self-test — {len(failures)} case(s) failed")
        return 1
    print("PASS: indexed_source --self-test — every case passed")
    return 0


if __name__ == "__main__":
    import sys
    if "--self-test" in sys.argv:
        raise SystemExit(_self_test())
    print(__doc__)
