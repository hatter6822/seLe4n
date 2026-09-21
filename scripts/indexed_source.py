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
    """
    wanted = list(paths)
    if not wanted:
        return {}
    out = run_git(repo, ["cat-file", "--batch"],
                  stdin="".join(f":{p}\n" for p in wanted).encode())
    return parse_batch(out, wanted)


def parse_batch(out: bytes, wanted: list[str]) -> dict[str, str]:
    """`cat-file --batch` output, entry by entry.  Separated from the call so the
    self-test can drive the REFUSALS: git does not emit a truncated stream or an
    unreadable header on demand, so a check that could only run git could not
    witness the two arms that distinguish this parser from the two it replaces."""
    res: dict[str, str] = {}
    i = 0
    for n, rel in enumerate(wanted):
        nl = out.find(b"\n", i)
        if nl < 0:
            raise DerivationFailed(
                ["git", "cat-file", "--batch"], 0, "",
                f"output ended after {n} of {len(wanted)} entries")
        header = out[i:nl].decode("utf-8", "replace")
        i = nl + 1
        if header.endswith((" missing", " ambiguous")):
            continue
        try:
            size = int(header.rsplit(" ", 1)[1])
        except (IndexError, ValueError):
            raise DerivationFailed(
                ["git", "cat-file", "--batch"], 0, "",
                f"unreadable header for {rel!r}: {header!r}") from None
        try:
            res[rel] = out[i:i + size].decode("utf-8")
        except UnicodeDecodeError:
            pass                                # not text; the caller decides
        i += size + 1                           # blob, then its trailing newline
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
        listed = listed_at(root, ":")
        check("listed_at names every indexed path, whitespace included",
              listed == ["docs/a name.md", "docs/a.md", "docs/b.bin"], listed)
        check("listed_at honours a pathspec",
              listed_at(root, ":", "*.md") == ["docs/a name.md", "docs/a.md"],
              listed_at(root, ":", "*.md"))

        # THE decisive case for `indexed_contents`: the index, not the disk.
        with open(plain, "w", encoding="utf-8") as fh:
            fh.write("WORKING TREE\n")
        got = indexed_contents(root, ["docs/a.md"])
        check("indexed_contents reads the INDEX, not the working tree",
              got == {"docs/a.md": "staged text\n"}, got)

        # git's own per-entry answers are answers, not failures.
        got = indexed_contents(root, ["docs/a.md", "docs/nope.md", "docs/b.bin"])
        check("a path git reports missing is absent from the result",
              "docs/nope.md" not in got, sorted(got))
        check("a blob that is not UTF-8 is absent from the result",
              "docs/b.bin" not in got, sorted(got))
        check("the readable neighbours still come back",
              got.get("docs/a.md") == "staged text\n", got)

        # The `ls-tree` arm's SUCCESS path, which the refusal case below cannot
        # reach: without this, a typo in the revision spelling would be silent
        # and only the raise would be exercised.  The commit holds the three
        # staged files; the working tree has since been edited, which is what
        # makes reading a revision different from reading the disk.
        git("commit", "-q", "-m", "fixture")
        at_head = listed_at(root, "HEAD")
        check("listed_at reads a REVISION, not just the index",
              at_head == ["docs/a name.md", "docs/a.md", "docs/b.bin"], at_head)
        check("a revision honours a pathspec too",
              listed_at(root, "HEAD", "docs/a.md") == ["docs/a.md"],
              listed_at(root, "HEAD", "docs/a.md"))

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
    ok_stream = b"deadbeef blob 3\nabc\n"
    check("a well-formed stream parses", parse_batch(ok_stream, ["x"]) == {"x": "abc"},
          parse_batch(ok_stream, ["x"]))
    try:
        parse_batch(b"deadbeef blob 3\nabc\n", ["x", "y"])
    except DerivationFailed as exc:
        check("a TRUNCATED stream raises rather than returning the prefix",
              "1 of 2" in str(exc), str(exc))
    else:
        check("a TRUNCATED stream raises rather than returning the prefix",
              False, "returned a prefix")
    try:
        parse_batch(b"deadbeef blob NOT-A-NUMBER\nabc\n", ["x"])
    except DerivationFailed as exc:
        check("an unreadable header raises rather than stopping quietly",
              "unreadable header" in str(exc), str(exc))
    else:
        check("an unreadable header raises rather than stopping quietly",
              False, "returned quietly")
    miss = parse_batch(b":x missing\n", ["x"])
    check("a `missing` line is an ANSWER, not a refusal", miss == {}, miss)

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
