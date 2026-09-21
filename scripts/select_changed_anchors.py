#!/usr/bin/env python3
"""Which tier anchors does this cut have to re-run?

`CLAUDE.md` states the sweep as a **procedure**: *before running Tier 3, sweep the
anchors over every file the cut touched … and execute each one directly; that is
seconds against tens of minutes per iteration.*  It even gives the `rg` command to
run.  Four consecutive cuts then shipped an anchor that procedure would have
caught, each found fifty minutes into the Full lane:

* `v0.35.116` moved a table parse between two functions and **three** anchors over
  the old home went silent, of which the Tier 3 run reported one.
* `v0.35.118` widened a regex, so the line a `v0.35.115` positive pinned no longer
  existed — two positives over one subject that no tree satisfies.
* `v0.35.119` hoisted a classifier, which left a loop's namespace binding unused;
  it became `_ns`, and a `v0.35.117` anchor had pinned `for ns, files in …`
  verbatim.  Tier 3 stopped there, so the 21 anchors that cut *added* never ran.
* `v0.35.121` bound a state once, retiring the inline spelling a `v0.35.86`
  positive pinned — found by the *ad-hoc* form of this sweep, in seconds, which is
  what said the procedure works and the discipline of running it does not.

A rule restated four times and broken four times is owed a check rather than a
fifth telling; this module is the **selection** half of it, and
`scripts/check_changed_file_anchors.sh` is the execution half.  They are two files
for one reason: an anchor's verdict must come from the tier suites' own
`run_check` / `run_negative_check`, so that this gate and Tier 3 cannot disagree
about any anchor, and those live in bash.

**Three selection rules, all derived from git rather than from a list.**

``path``
    The anchor's command mentions a changed path verbatim.

``dir``
    The anchor's command mentions an **ancestor directory** of a changed path as a
    delimited token.  132 of the tree's 5704 anchors have a directory target, 43 of
    them the whole of `SeLe4n/`, and those are the *must not come back* negatives —
    exactly the ones a new or moved file has to face.  The delimiter is what keeps
    this rule affordable: a command naming
    `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` does **not** match the token
    `SeLe4n/Kernel/IPC/`, because after the optional slash the pattern requires a
    quote, whitespace or end of line.  Without it, `SeLe4n` would select all 4261
    anchors that name any file beneath it and the sweep would be Tier 3.

``diff``
    The anchor line is one this cut **adds or changes** in a tier suite.  `path`
    cannot see these: it selects anchors that *mention* a changed file, and a
    newly written anchor's subject need not be a file the cut also changed.
    `v0.35.119`'s ad-hoc harness collected its new anchors *from the cut's
    version-marker comment onwards*, which is a recognised set standing in for a
    derived one — in the harness written to verify anchors.  The diff is the
    derived form.

**What is swept, and what is deferred with its reason.**  An anchor is swept when
it performs a **text search**, which is `check_anchor_consistency.classify_line`'s
question and not a second reading of it — so a mutation of that classifier fails
both gates.  Two kinds are deferred rather than run, by name and with a count,
never silently:

* `plain` — the invocation runs a *tool* (a `lake build`, a python gate, a
  `test -x`) rather than scanning text, so its subject is not the text of a changed
  file, and Tier 0/1/2 run it in their own lane where its prerequisites exist.
* a command a shell **expands a variable in** that this gate does not define.  The
  tier suites compute a handful in their prologues (`CIBUNDLE_CONJUNCTS`,
  `TRACE_OUTPUT`, `suite_exes`, `ARTIFACT_DIR`, …).  Substituting a guess would
  make the gate disagree with the suite about what it ran; deferring and naming
  them keeps the residue visible, which is the treatment this project already
  applies to a composed search.

  **Asked of `expanding_text`, never of the raw line.**  A `$` is a variable
  reference only where a shell expands it, which is a fact about quoting, and
  `rg -F '${command}'` spells a variable while reading none.  Measured when that
  was corrected: the raw-text scan flagged **five** searching invocations tree-wide
  and **four** were literal dollars in single- or backslash-quoted patterns — all
  four anchors pinning *this gate's own fail-closed branches*, so its blind spot
  sat precisely on its safety machinery.  Exactly **one** is genuine.
* a command that **substitutes** — `$(…)` or a backtick in an expanding position.
  Its value comes from running something, so this gate cannot reproduce what the
  suite ran.  No live invocation does; the branch exists because a scanner's
  default is a decision, and because all five backtick-bearing anchors on this
  tree are Markdown code spans inside a pattern, which a raw scan would have
  deferred over a character that is not shell syntax where it occurs.

`unparsed` and `unlexable` are **failures**, as `unparsed` is in
`check_anchor_consistency.py`: an anchor this gate cannot read is one it cannot
run, and reporting a clean sweep over it is the fail-open the whole mechanism
exists to remove.  The two are distinct so the report names *which* question could
not be answered, even though the executor answers both on one arm.

**And the model has an empirical backstop, so its residue is detectable rather than
assumed empty.**  `expanding_text` over-approximates deliberately, so its only
unsafe direction is misplacing a real expansion as literal; the executor then
requires every swept anchor to reach a **verdict** — a pass, or a recorded failure
— because `set -u` aborts an `eval` that reads an unbound variable and an anchor
counted as swept without being checked is precisely the fail-open this gate is for.
Measuring the outcome beats trusting the model.

**The change set is derived, and failing to derive it is a FAILURE.**  A clean
checkout with no reachable parent cannot say what changed, and answering "nothing
changed, so nothing to sweep" there is the same fail-open: *"the gate could not
read it" and "the gate checked it" must never produce the same PASS line.*  A
derived change set that selects **zero** anchors is an honest zero and passes — the
cut touches no anchored file.

Renames are read with `--no-renames`, so a rename contributes **both** paths (the
old one is where the anchors are), and deletions are in the set for the same
reason: a deleted file breaks every anchor over it, and that is a report rather
than an exemption.
"""

from __future__ import annotations

import argparse
import os
import pathlib
import re
import subprocess
import sys

REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))

# The classifier and the continuation folding are IMPORTED, never re-derived.
# `logical_lines` exists because six live anchors put the file on the continuation
# line; a second line-by-line reader here would reopen that hole for the sweep
# while `check_anchor_consistency.py` stayed correct, which is this project's
# one-question-two-answers hazard at the point where it is cheapest to avoid.
from check_anchor_consistency import (  # noqa: E402
    HELPER_NAME_RE,
    SEARCH_TOOLS,
    TIER_SCRIPT_GLOB,
    classify_line,
    logical_lines,
)

#: Kinds whose subject is the text of a file, so the sweep can decide them.
SEARCHING_KINDS = frozenset({"anchor", "filtered"})

#: Command heads a producer's body may use, beyond the classifier's own
#: `SEARCH_TOOLS`.  **Named rather than derived**, for the reason
#: `indexed_source.PROCESS_RUNNERS` gives: whether a tool has an effect beyond
#: reading its input is a fact about that tool, not about any spelling here.  The
#: set therefore fails CLOSED -- a head outside it leaves the anchor deferred.
READ_ONLY_FILTERS = frozenset({
    "sed", "awk", "wc", "sort", "uniq", "head", "tail", "cut", "tr", "cat",
    "comm", "nl", "basename", "dirname", "true", "printf", "echo",
})

#: A `VAR=value` prefix on a command, which shell allows and which is not the
#: command's head.
_ASSIGNMENT_PREFIX = re.compile(r"^[A-Za-z_][A-Za-z_0-9]*=")

#: A producer the sweep may EXECUTE: `NAME=$( <pipeline> )`, nothing else.
#:
#: **A resolved anchor's executability is a question about the RESOLVED command,
#: and the classifier's `kind` is not that question** (`v0.35.155`, PR #897's
#: review).  `kind` was computed from the anchor ALONE and then compared against
#: `SEARCHING_KINDS`, while `missing` and `substitutes` beside it were computed
#: from the command with its prelude -- one decision drawn from two subjects.  So
#: a resolved threshold check reached `defer:tool` however complete its producer
#: was, and deleting enough conjuncts from a bundle left the changed-file sweep
#: green while direct Tier 3 failed.  `v0.35.152` had fixed the same split for
#: `related` (the provenance question) and not for `kind` (the executability
#: one), which is *a fix applied at one site and not its sibling*.
#:
#: Recomputing `kind` is NOT the remedy, and the measurement says so: a compound
#: `NAME=$( … ); run_check …` is not a line the classifier parses at all, so every
#: such anchor would become `fail:unparsed` -- failing Tier 0 on ten anchors that
#: are correctly deferred.  This is round 16's exit instead: **require a canonical
#: spelling and refuse the rest.**  A producer qualifies when it is a single
#: command substitution whose every command head reads and does not write, with no
#: redirection; the nine that do not are an array assignment folded to a broken or
#: empty prefix (`THEOREM_CHECK_TARGETS=(`, `shell_files_args=()`), a
#: side-effecting `mktemp` feeding a build, or a directory constant feeding a
#: write -- each of which the sweep must not run, and an empty array is the worst
#: of them because the tool would run with no arguments and PASS.
#: The closing parenthesis is the LAST character, not the first one seen: a
#: `sed` pattern may hold `\(theorem\|def\)`, and a body bounded by `[^)]*`
#: stopped inside it -- so `NI_CTORS`, one of the two anchors this contract is
#: for, stayed deferred by its own alternation.  A nested `$(` is refused
#: separately, which is what keeps the greedy bound from spanning two
#: substitutions.
_EXECUTABLE_PRODUCER = re.compile(
    r"^[A-Za-z_][A-Za-z_0-9]*=\$\((?P<body>.*)\)$")

#: ...and the anchor it may feed: a threshold `test` on that one variable.  The
#: only non-searching anchor shape whose subject is still the text of a file --
#: the producer reads the file and the test compares what it found.
_THRESHOLD_ANCHOR = re.compile(
    r"""^run_check\s+"[A-Z]+"\s+test\s+"\$\{[A-Za-z_][A-Za-z_0-9]*\}"\s+"""
    r"""-(?:eq|ne|lt|le|gt|ge)\s+[0-9]+\s*$""")


def executable_threshold(prelude: list[str], command: str) -> bool:
    """Is `prelude; command` a producer-fed threshold the sweep may run?

    Both halves must take their canonical spelling: the producer a single
    command substitution over reading tools with no redirection, and the anchor a
    `test` on the one variable it binds.  Anything else is deferred, because the
    remaining shapes on this tree are an array assignment the fold truncates, a
    `mktemp` with a side effect, and a redirection into the tree.

    Measured when it landed: of eleven anchors with a resolved producer, exactly
    **two** qualify (`CIBUNDLE_CONJUNCTS`, `NI_CTORS`) -- which are the two the
    producer mechanism was written for -- and nine stay deferred.
    """
    if len(prelude) != 1 or not _THRESHOLD_ANCHOR.match(command.strip()):
        return False
    m = _EXECUTABLE_PRODUCER.match(prelude[0].strip())
    if m is None:
        return False
    body = m.group("body")
    if "$(" in body or "`" in body:
        return False
    try:
        words = _shell_words(body)
    except UnlexableCommand:
        return False                   # cannot read it, so will not run it
    # The PIPELINE is split on a bare `|` WORD, never on the character: a `sed`
    # pattern holds `\|` and a `grep` pattern holds `| ` inside quotes, and
    # splitting the text would make each of those a stage whose head is not a
    # tool.  `_shell_words` is the tree's own lexer, so this asks the question
    # bash asks.
    allowed = READ_ONLY_FILTERS | set(SEARCH_TOOLS)
    stage: list[str] = []
    stages = [stage]
    for w in words:
        if w in ("|", "||", "&&", ";", "&"):
            if w != "|":
                return False           # only a plain pipeline is admitted
            stage = []
            stages.append(stage)
            continue
        if w.startswith((">", "<")) or w in (">", ">>", "<"):
            return False               # a redirection is a write or an input
        stage.append(w)
    for st in stages:
        while st and _ASSIGNMENT_PREFIX.match(st[0]):
            st = st[1:]                # a leading VAR=value prefix
        if not st or st[0].strip("'\"") not in allowed:
            return False
    return True


#: Variables `check_changed_file_anchors.sh` defines, and therefore the only ones
#: a swept anchor may reference.  `REPO_ROOT` comes from `test_lib.sh` and
#: `SCRIPT_DIR` is computed the same way every tier suite computes it, so an
#: anchor reading either is running against the same value it would in its own
#: suite.  Anything else is a tier-local prologue computation: see the module
#: docstring.
DEFINED_VARIABLES = frozenset({"REPO_ROOT", "SCRIPT_DIR"})

#: A `${NAME}` or `$NAME` reference.  Both spellings, because an anchor may use
#: either and a gate that recognised one would defer some and run others.  Asked of
#: `expanding_text`, never of the raw command: see `undefined_variables`.
VARIABLE_REF = re.compile(r"\$\{?([A-Za-z_][A-Za-z_0-9]*)")


class UnknownChangeSet(SystemExit):
    """Raised when git cannot say what this cut changed."""


def tier_scripts(scripts_dir: pathlib.Path) -> list[pathlib.Path]:
    """Every tier suite, by discovery.

    An empty result is a hard error rather than an empty pass, for the reason
    `check_anchor_consistency.discover_anchor_scripts` gives: a glob that has
    stopped matching the tree is the same fail-open, one step earlier.
    """
    found = sorted(p for p in scripts_dir.glob(TIER_SCRIPT_GLOB) if p.is_file())
    if not found:
        raise SystemExit(
            f"FAIL: changed-file anchor sweep — no tier suites matched "
            f"{scripts_dir}/{TIER_SCRIPT_GLOB}; the sweep would have run nothing "
            f"and reported PASS."
        )
    return found


def anchor_invocations(
    scripts_dir: pathlib.Path,
) -> list[tuple[str, int, str, str]]:
    """`(script, first line number, kind, joined command line)` per invocation.

    Continuations are folded by `logical_lines`, so a multi-line anchor is one
    record carrying one command — which is both what the selection has to match
    against and what the executor has to `eval`.
    """
    out: list[tuple[str, int, str, str]] = []
    for p in tier_scripts(scripts_dir):
        for line_no, joined in logical_lines(p.read_text(encoding="utf-8")):
            stripped = joined.strip()
            if stripped.startswith("#") or not HELPER_NAME_RE.match(stripped):
                continue
            got = classify_line(stripped)
            kind = got[0] if got is not None else "unparsed"
            out.append((p.name, line_no, kind, stripped))
    return out


#: A top-level `NAME=...` assignment on its own logical line.  Anchored, so a
#: `test "${X}" -ge 5` is not one and an assignment nested inside a command
#: substitution is not reached (`logical_lines` folds continuations, so a
#: multi-line producer arrives as one record).
_PRODUCER_ASSIGNMENT = re.compile(r"^([A-Za-z_][A-Za-z_0-9]*)=(?!=)")


def anchor_producers(
    scripts_dir: pathlib.Path,
) -> dict[str, list[tuple[int, str, str]]]:
    """`{script: [(line, NAME, assignment)]}` -- what each tier script BINDS.

    `v0.35.152` (PR #897 review).  An anchor's inputs are not always spelled in
    its own command: `test "${CIBUNDLE_CONJUNCTS}" -ge 5` names no path, and the
    file it is about is named by the `CIBUNDLE_CONJUNCTS=$( … Defs.lean … )` line
    above it.  Relating changed paths to the anchor's command ALONE therefore
    omitted such an anchor entirely -- not deferred, not reported, absent -- so
    deleting conjuncts from that bundle left the changed-file sweep green while
    direct Tier 3 failed.  Two are live (`CIBUNDLE_CONJUNCTS`, `NI_CTORS`).

    *Resolve the text into the structure it stands for*: a variable reference is
    a reference to its producer, and the producer is the last assignment of that
    name at or before the anchor's line in the same script.  The LAST one,
    because a re-assignment is what the anchor actually reads -- `v0.34.41`
    recorded a shell expander taking the FIRST and reading a setting at a value
    the command never receives.
    """
    out: dict[str, list[tuple[int, str, str]]] = {}
    for path in tier_scripts(scripts_dir):
        rows: list[tuple[int, str, str]] = []
        for line_no, joined in logical_lines(path.read_text(encoding="utf-8")):
            stripped = joined.strip()
            if stripped.startswith("#"):
                continue
            m = _PRODUCER_ASSIGNMENT.match(stripped)
            if m is not None:
                rows.append((line_no, m.group(1), stripped))
        out[path.name] = rows
    return out


def resolve_producers(
    producers: list[tuple[int, str, str]], line: int, names: set[str],
) -> list[str] | None:
    """The assignments binding `names` before `line`, in source order, or `None`.

    `None` when any name has no producer in this script: the anchor then reads
    something the script does not bind, which is the `defer:var` case the
    executor already reports.  Returning a partial list would be the *a FAILED
    derivation is not an EMPTY one* shape -- a caller cannot tell "resolved to
    nothing" from "resolved to these".
    """
    chosen: dict[str, tuple[int, str]] = {}
    for at, name, text in producers:
        if at < line and name in names:
            chosen[name] = (at, text)
    if len(chosen) != len(names):
        return None
    return [text for _, text in sorted(chosen.values())]


def ancestor_dirs(path: str) -> list[str]:
    parts = [p for p in path.split("/") if p]
    return ["/".join(parts[:i]) for i in range(1, len(parts))]


def _dir_token(directory: str) -> re.Pattern:
    """`directory` as a path token, not as a prefix of a longer path.

    The lookbehind stops `SeLe4n` from matching inside `MySeLe4n`; the optional
    trailing slash plus the lookahead is what stops an ancestor from matching every
    file beneath it, which is the whole reason the `dir` rule is affordable.
    """
    return re.compile(r"(?<![\w./-])" + re.escape(directory) + r"/?(?=[\"'\s]|$)")


class UnlexableCommand(ValueError):
    """Raised when the shell-quoting walk cannot finish a quoted span."""


#: The shell's glob metacharacters.  A word carrying one is a **pattern over
#: paths**, so a changed path relates to it by matching rather than by the
#: substring test the `path` rule applies.
_GLOB_META = frozenset("*?[")


def _glob_pattern(value: str) -> "re.Pattern | None":
    r"""`value` as a path-matching regex, or `None` when it carries no glob.

    **Shell semantics, not `fnmatch`'s**: `*` and `?` do not cross a `/`.  That is
    the whole difference between selecting the anchors a change invalidates and
    selecting most of Tier 3 — `tests/*PlatformSuite.lean` must match
    `tests/Ak9PlatformSuite.lean`, and `*.lean` must name a *top-level* file rather
    than every `.lean` in the tree, which is what `fnmatch` would make it.

    **A bracket expression widens to `[^/]` rather than being translated.**  A
    glob's `[a-z]` matches one character from a set, so one character that is not a
    slash is a superset of it — the over-approximating direction — and it keeps this
    function from compiling a fragment of an `rg` pattern as a regex character
    class, which is neither this function's question nor safe to get wrong.  An
    unterminated `[` is a literal, as a shell reads it.

    Over-approximation is the safe direction throughout and is deliberately left
    in: an `rg` **pattern** argument may also carry a `*`, and translating one
    yields a regex a changed path is very unlikely to match — and when one does,
    the cost is an anchor run that Tier 3 runs anyway.
    """
    if not (_GLOB_META & set(value)):
        return None
    out: list[str] = []
    i, n = 0, len(value)
    while i < n:
        c = value[i]
        if c == "*":
            out.append("[^/]*")
        elif c == "?":
            out.append("[^/]")
        elif c == "[":
            j = i + 1
            if j < n and value[j] in "!^":
                j += 1
            if j < n and value[j] == "]":
                j += 1
            while j < n and value[j] != "]":
                j += 1
            if j >= n:
                out.append(re.escape(c))
            else:
                out.append("[^/]")
                i = j + 1
                continue
        else:
            out.append(re.escape(c))
        i += 1
    try:
        return re.compile("".join(out))
    except re.error:
        return None


def glob_targets(command: str, _depth: int = 0) -> list["re.Pattern"]:
    """Every glob a shell would expand in `command`, as path-matching regexes.

    Read off the word **values** rather than the raw text, for the reason
    `expanding_text` reads its own question there: a quoted `'tests/*.lean'` is one
    word whose value is the pattern, and the raw line is not it.  A `-c` script
    word is descended into, since an inner shell expands the globs in it.

    A command this walk cannot lex contributes its whitespace-split raw tokens
    instead of nothing: dropping them is the fail-open direction for a module that
    decides which checks run, and over-selecting costs a run.
    """
    if _depth > _MAX_SHELL_DEPTH:
        return []
    try:
        words = _shell_words(command)
    except UnlexableCommand:
        out: list[re.Pattern] = []
        for w in command.split():
            g = _glob_pattern(w.strip("'" + '"'))
            if g is not None:
                out.append(g)
        return out
    scripts = _script_word_indices(words)
    out: list[re.Pattern] = []
    for idx, word in enumerate(words):
        _outer, value = _word_parts(word)
        if idx in scripts:
            out.extend(glob_targets(value, _depth + 1))
            continue
        g = _glob_pattern(value)
        if g is not None:
            out.append(g)
    return out


#: Commands whose `-c` argument is a SCRIPT an inner shell re-lexes.  A `$` the
#: outer shell protected with single quotes expands *there*, so a view that blanked
#: it would read `bash -lc 'rg -n "p" "${TRACE_OUTPUT}"'` as reading no variable —
#: the fail-open direction, and exactly what the self-test caught when this was
#: first written non-recursively.  `check_identifier_naming.py` reached the same
#: conclusion for `$( … )` bodies; this is that rule for a `-c` argument.
_INNER_SHELLS = frozenset({"bash", "sh", "dash", "zsh", "ksh"})

#: How deep a `bash -lc 'bash -lc "…"'` nest this follows before refusing.
#: Refusing rather than stopping, because depth is the one case where stopping
#: would hide an expansion instead of over-reporting one.
_MAX_SHELL_DEPTH = 4


def _shell_words(command: str) -> list[str]:
    """`command`'s words, split on whitespace *outside* quotes, quotes included.

    Bash joins adjacent quoted and unquoted runs into one word, so the
    `'…'"'"'…'` idiom — five live anchors use it to put a single quote inside a
    `-c` script — is ONE word here, as it is to bash.  Splitting it into three
    would hand each run to the inner-shell view separately, and the first run's
    `rg "pattern` would then look like an unterminated double-quoted span.  That
    is not a hypothetical: it is what the first draft of this function did, and
    those five anchors failed the gate.
    """
    words: list[str] = []
    i, n = 0, len(command)
    while i < n:
        if command[i].isspace():
            i += 1
            continue
        start = i
        while i < n and not command[i].isspace():
            c = command[i]
            if c == "\\":
                i += 2
                continue
            if c == "'":
                i += 1
                while i < n and command[i] != "'":
                    i += 1
                if i >= n:
                    raise UnlexableCommand("unterminated single-quoted span")
                i += 1
                continue
            if c == '"':
                i += 1
                closed = False
                while i < n:
                    if command[i] == "\\":
                        i += 2
                        continue
                    if command[i] == '"':
                        i += 1
                        closed = True
                        break
                    i += 1
                if not closed:
                    raise UnlexableCommand("unterminated double-quoted span")
                continue
            i += 1
        words.append(command[start:min(i, n)])
    return words


def _word_parts(word: str) -> tuple[str, str]:
    r"""`(outer, value)` for one shell word.

    `outer` is the text the **enclosing** shell expands `$` in: the word's unquoted
    runs and its double-quoted interiors.  An escape pair contributes *nothing* to
    it, inside double quotes as well as outside, because a backslash is exactly
    what suppresses expansion — `rg -F "x \${disposition} y"` searches for a
    literal dollar sign and reads no variable.

    `value` is the word's quote-removed value, which is what an inner shell
    receives as a `-c` script: single-quoted interiors verbatim, and an escape pair
    contributing the escaped **character** rather than nothing — `bash -lc "rg -n
    \$X"` hands `$X` to the inner shell, which expands it, so dropping the pair
    outright would be the fail-open direction.
    """
    outer: list[str] = []
    value: list[str] = []
    i, n = 0, len(word)
    while i < n:
        c = word[i]
        if c == "\\":
            if i + 1 < n:
                value.append(word[i + 1])
            i += 2
            continue
        if c == "'":
            i += 1
            while i < n and word[i] != "'":
                value.append(word[i])
                i += 1
            if i >= n:
                raise UnlexableCommand("unterminated single-quoted span")
            i += 1
            continue
        if c == '"':
            i += 1
            closed = False
            while i < n:
                if word[i] == "\\":
                    # Nothing to `outer`: inside double quotes a backslash is
                    # exactly what suppresses expansion, so `"\\${X}"` reads no
                    # variable in THIS shell.  The escaped character still reaches
                    # `value`, because an inner `-c` shell receives it unquoted and
                    # expands it -- the two halves of this pair disagree on
                    # purpose, and collapsing them would be fail-open one way or
                    # over-strict the other.
                    if i + 1 < n:
                        value.append(word[i + 1])
                    i += 2
                    continue
                if word[i] == '"':
                    i += 1
                    closed = True
                    break
                outer.append(word[i])
                value.append(word[i])
                i += 1
            if not closed:
                raise UnlexableCommand("unterminated double-quoted span")
            continue
        outer.append(c)
        value.append(c)
        i += 1
    return "".join(outer), "".join(value)


def _script_word_indices(words: list[str]) -> set[int]:
    """Indices of the `-c` script arguments of inner shells named in `words`.

    The shape required is `<shell> <option containing c> <word>`.  A word whose
    basename is a shell but which is not followed by an option word contributes
    nothing rather than raising: `rg -n bash scripts/x.sh` names a shell as *data*,
    and refusing it would fail a legitimate anchor.  What keeps that liberality
    honest is not this function but the executor — a swept anchor must reach a
    verdict, so an expansion this misses fails there rather than passing.
    Measured when this was written: all 1026 searching anchors naming a shell use a
    `-c` option, so requiring the shape costs the tree nothing.
    """
    found: set[int] = set()
    i = 0
    while i < len(words):
        head = words[i].strip("\"'")
        if head and head.rsplit("/", 1)[-1] in _INNER_SHELLS:
            j = i + 1
            while j < len(words) and words[j].startswith("-"):
                if "c" in words[j]:
                    if j + 1 < len(words):
                        found.add(j + 1)
                        i = j + 1
                    break
                j += 1
        i += 1
    return found


def expanding_text(command: str, _depth: int = 0) -> str:
    r"""The parts of `command` in which a shell expands `$`, concatenated.

    A `$` is a variable reference only where a shell **expands** it, and that is a
    fact about quoting rather than about the text: inside a single-quoted span `$`
    is a literal dollar sign, and after a backslash it is one too.  Asking
    `VARIABLE_REF` of the raw line instead is the presence-for-relation
    substitution `CLAUDE.md` retires — `rg -F '${command}'` spells a variable and
    reads none.

    Deliberately **not** byte-aligned, unlike `lean_code_view` and
    `rust_code_view`.  The answer wanted here is a set of names and a yes/no about
    command substitution, not an offset; and byte alignment would cost the one
    thing that matters — a `-c` script assembled from several quoted runs is ONE
    script to the inner shell, so it must be *reassembled* before it is viewed, and
    reassembly does not preserve offsets.  A script word therefore contributes
    **both** its own outer-expanding runs and a recursive view of its value, since
    `bash -lc "rg -n '${X}' f"` has the outer shell expand `${X}` inside single
    quotes the inner shell would protect.

    **Which direction each misreading takes, stated rather than left to be
    rediscovered.**  Over-reporting an expansion defers an anchor Tier 3 runs
    anyway, which is conservative.  *Under*-reporting is the fail-open, and its two
    routes are a blanked `-c` script (closed above) and a desynchronised quote
    walk.  The desynchronisations are safe by inspection: an unquoted `#` comment
    is not honoured, so a `$` after it reads as expanding when bash expands nothing
    there at all; `$'…'` opens at the same byte as the `'` this walk opens at, so
    the spans coincide; and `$((…))` reads names without a `$`, which no live
    anchor does (measured: zero `$(` in any searching invocation).  What makes the
    residue *detectable* rather than assumed empty is the executor's verdict
    relation: a swept anchor reaching neither a pass nor a recorded failure fails
    the gate.
    """
    if _depth > _MAX_SHELL_DEPTH:
        raise UnlexableCommand("inner-shell nesting deeper than this view follows")
    words = _shell_words(command)
    scripts = _script_word_indices(words)
    chunks: list[str] = []
    for idx, word in enumerate(words):
        outer, value = _word_parts(word)
        chunks.append(outer)
        if idx in scripts:
            chunks.append(expanding_text(value, _depth + 1))
    return "\n".join(chunks)


def undefined_variables(command: str) -> set[str]:
    """Variables `command` reads that the executor does not define.

    Asked of `expanding_text`, never of the raw text.  A raw-text scan is the
    presence-for-relation substitution `CLAUDE.md` retires: `rg -F '${command}'`
    spells a variable and reads none, so the scan defers an anchor it could run.
    Measured when this was corrected: the raw scan flagged **five** searching
    invocations tree-wide and **four** were single- or backslash-quoted patterns —
    all four pinning *this gate's own fail-closed branches*, so its blind spot sat
    precisely on its safety machinery.  One is genuine (`ARTIFACT_DIR`, Tier 4).
    """
    return {v for v in VARIABLE_REF.findall(expanding_text(command))
            if v not in DEFINED_VARIABLES}


def expanding_substitutions(command: str) -> bool:
    """Does `command` run a command substitution the executor cannot reproduce?

    `$(…)` and a backtick, asked of the same view for the same reason: all five
    backtick-bearing anchors on this tree are Markdown code spans inside a
    single-quoted pattern, so a raw-text scan would defer five anchors over a
    character that is not shell syntax where it occurs.  Zero live invocations
    substitute; the branch exists because a scanner's default is a decision, and
    the view's recursion is why a substitution inside a `-c` script is seen too.
    """
    text = expanding_text(command)
    return "$(" in text or "`" in text


def select(
    invocations: list[tuple[str, int, str, str]],
    paths: list[str],
    added: set[tuple[str, int]] | None = None,
    producers: dict[str, list[tuple[int, str, str]]] | None = None,
) -> list[tuple[str, int, str, str, str, str]]:
    """`(script, line, provenance, kind, disposition, command)` for this cut.

    `added` names anchor lines the cut introduced or changed, by `(script, line)`.
    Provenance is reported so a failure says *why* an anchor was run, which is what
    a reader needs in order to judge whether the selection is right.

    **An anchor's target may be a PATTERN, and `glob` is the provenance for one**
    (PR #897's review, `v0.35.142`).  `path` is a substring test and `dir` requires
    a delimited literal directory, so a target spelled `tests/*PlatformSuite.lean`
    matched neither: after the optional `tests/` slash the `dir` lookahead sees a
    `*` and rejects.  Two such targets are live here (`tests/*PlatformSuite.lean`,
    `scripts/*cascade_check_monotonic.sh`), so a change to `Ak9PlatformSuite.lean`
    selected **none** of the anchors over it and the changed-file sweep ran nothing
    that a change to that suite invalidates.  The remedy is the rule `CLAUDE.md`
    states for every scanner here: resolve the text into the structure it stands
    for.  A glob is a pattern over paths, so the changed paths are matched against
    it (`glob_targets`, `_glob_pattern`).

    Disposition is
    `sweep`, `defer:tool`, `defer:var:<NAME>…`, `defer:subst`, `fail:unparsed` or
    `fail:unlexable`.  The two `fail:` dispositions are the explicit default
    branches: an invocation this gate cannot read is a check nobody runs, which is
    the fail-open direction for a module that produces requirements.
    """
    added = added or set()
    exact = [p for p in paths if p]
    dirs: list[re.Pattern] = []
    seen: set[str] = set()
    for p in exact:
        for d in ancestor_dirs(p):
            if d not in seen:
                seen.add(d)
                dirs.append(_dir_token(d))
    producers = producers or {}
    out: list[tuple[str, int, str, str, str, str]] = []
    for script, n, kind, command in invocations:
        # **An anchor's inputs include its PRODUCERS'** (`v0.35.152`, PR #897
        # review).  `test "${X}" -ge 5` names no path; the file it is about is
        # named by the `X=$( … )` line above it, and relating changed paths to
        # the command alone dropped such an anchor from the selection entirely.
        # Resolved here so the relation, the disposition and the executed text
        # are ONE answer: a partial resolution would select the anchor and then
        # defer it, which is the shape that made this invisible.
        prelude: list[str] = []
        try:
            wanted = undefined_variables(command)
        except UnlexableCommand:
            wanted = set()
        if wanted:
            resolved = resolve_producers(producers.get(script, []), n, wanted)
            if resolved is not None:
                prelude = resolved
        related = "\n".join(prelude + [command])
        if (script, n) in added:
            prov = "diff"
        elif any(p in related for p in exact):
            prov = "path"
        elif any(d.search(related) for d in dirs):
            prov = "dir"
        elif _GLOB_META & set(related) and any(
            g.fullmatch(pth) for g in glob_targets(related) for pth in exact
        ):
            prov = "glob"
        else:
            continue
        anchor_only = command
        if prelude:
            # The producer runs, then the anchor, in one `eval` -- so the sweep's
            # verdict is the tier suite's own rather than a deferral.  `;` rather
            # than a newline, because the executor reads TAB-separated rows.
            command = "; ".join(prelude + [command])
        if prelude and executable_threshold(prelude, anchor_only):
            # A canonically-spelled producer feeding a threshold `test`: the
            # subject is still the text of a file, reached through the variable
            # the producer binds, so the sweep can decide it and must.
            disposition = "sweep"
        elif kind == "unparsed":
            disposition = "fail:unparsed"
        elif kind not in SEARCHING_KINDS:
            disposition = "defer:tool"
        else:
            try:
                missing = undefined_variables(command)
                substitutes = expanding_substitutions(command)
            except UnlexableCommand:
                disposition = "fail:unlexable"
            else:
                if missing:
                    disposition = "defer:var:" + ",".join(sorted(missing))
                elif substitutes:
                    disposition = "defer:subst"
                else:
                    disposition = "sweep"
        out.append((script, n, prov, kind, disposition, command))
    return out


def _git(*args: str, cwd: pathlib.Path | None = None) -> tuple[int, str, str]:
    """`(status, stdout, stderr)` -- deliberately NOT raising on a nonzero status.

    Three callers ask git a *question* whose answer IS the exit status:
    `rev-parse --verify` ("does this ref exist"), and `diff --no-index` / `diff`
    ("do these differ", where 1 means yes).  A nonzero status there is data, so
    this helper must stay status-returning and each caller decides whether its
    own nonzero status is an answer or a failure.  That is why the two callers
    for which it is a *failure* raise `UnknownChangeSet` rather than this
    function raising for all of them, and why this one is not folded into
    `indexed_source.run_git`, whose whole contract is the opposite.

    The stderr is carried because a gate that says only "git failed" sends a
    reader to reproduce it by hand.
    """
    r = subprocess.run(
        ["git", *args], cwd=cwd or REPO_ROOT, capture_output=True,
        # A tracked path is a byte string, not text: it may hold any byte but
        # NUL and `/`.  `surrogateescape` round-trips one that is not valid
        # UTF-8 instead of raising, so a path this gate cannot pretty-print is
        # still a path it can compare (`v0.35.154`).
        encoding="utf-8", errors="surrogateescape",
    )
    return r.returncode, r.stdout, r.stderr


def _nul_split(out: str) -> list[str]:
    """A NUL-framed git listing's entries.

    **A DELIMITER that can occur in the data is not a delimiter** (`v0.35.154`,
    PR #897's review).  Without `-z`, git prints a path holding a newline, a
    quote or a backslash in its C-quoted form -- `"tests/a\\nb.lean"`, quotes and
    all -- and a line-splitting reader takes that spelling for the path.  This
    gate then relates a path that does not exist to every anchor target, matches
    none, and reports a clean sweep while running nothing the real change
    invalidates: fail-OPEN, and silent.

    NUL is the one byte a path cannot contain, which is why `-z` is the framing
    and why the split is on it rather than on lines.  A trailing empty field is
    the terminator, not an entry.
    """
    return [p for p in out.split("\0") if p]


def _names(*args: str) -> list[str]:
    """The paths `git diff` names, or `UnknownChangeSet`.

    A failed diff RAISES rather than answering `[]`, because `[]` is also what
    a clean tree returns -- and the two are not interchangeable *here* in a way
    this file already documents: `changed_paths` tries three derivations in
    order and takes the first that is non-empty, so an empty answer from the
    first silently promotes the **next** one.  `_untracked`'s own docstring
    names the consequence for a different cause: the gate "sweeps the
    *previous* cut's change set while reporting a clean run".  A `git diff` that
    fails produces exactly that, and `changed_paths`' docstring already states
    the contract ("**failing** rather than answering 'nothing' when none
    applies") this branch used to violate.
    """
    code, out, err = _git("diff", "--no-renames", "-z", "--name-only", *args)
    if code != 0:
        raise UnknownChangeSet(
            f"FAIL: changed-file anchor sweep — `git diff --no-renames "
            f"--name-only {' '.join(args)}` exited {code}, so this gate cannot "
            f"say what this cut changes.  It will not fall through to an older "
            f"derivation and sweep a different cut's change set."
            + (f"\n  git said: {err.strip()}" if err.strip() else "")
        )
    return _nul_split(out)


def _untracked(repo: pathlib.Path | None = None) -> list[str]:
    """Files this cut ADDS and has not staged.

    `git diff` structurally cannot see them — neither against the index nor
    against `HEAD` — so without this a cut whose only change is a new file falls
    through to the `HEAD~1` derivation and sweeps the *previous* cut's change set
    while reporting a clean run.  Found by running this gate on the cut that adds
    it, which is the first thing it reported.

    `--exclude-standard` honours `.gitignore`, so build output is not a change.

    A failed listing RAISES for the reason `_names` gives: answering `[]` is
    indistinguishable from "this cut adds no file", and the derivation order
    turns that into the very fall-through the paragraph above describes.
    """
    code, out, err = _git("ls-files", "--others", "--exclude-standard", "-z",
                          cwd=repo)
    if code != 0:
        raise UnknownChangeSet(
            f"FAIL: changed-file anchor sweep — `git ls-files --others "
            f"--exclude-standard` exited {code}, so this gate cannot say which "
            f"files this cut adds.  It will not fall through to an older "
            f"derivation and sweep a different cut's change set."
            + (f"\n  git said: {err.strip()}" if err.strip() else "")
        )
    return _nul_split(out)


def changed_paths() -> tuple[list[str], str, str]:
    """`(paths, how, base)` — what this cut changes, and which derivation said so.

    Three derivations, tried in order, and **failing** rather than answering
    "nothing" when none applies:

    1. the index unioned with the worktree **and with the untracked files**,
       against `HEAD` — the local and pre-commit case.  The index first because
       Tier 0 is the staged lane; the worktree unioned in because the anchors
       **execute** against the worktree, so an unstaged edit is one the sweep has
       to see; and the untracked files because `git diff` cannot see a file this
       cut *adds* until it is staged, and without them a cut whose only change is
       a new file falls through to derivation 3 and sweeps the **previous** cut.
    2. `SELE4N_PLAN_BASE_REF` against `HEAD` — the CI case, and *deliberately the
       same variable* `check_workstream_plan.py` reads.  Both gates ask one
       question — *what does this cut change relative to the revision it is
       merging into* — and `lean_action_ci.yml`'s fast lane already fetches that
       base and exports it for the plan gate, so reading it here costs nothing and
       gives the **whole PR** rather than its tip commit.  A second variable would
       be the same question answered in two places, with two chances to go stale.
    3. `HEAD~1` against `HEAD` — a clean local checkout sitting at the tip commit.

    A derived change set that selects zero anchors is an honest zero.  A change
    set that cannot be derived is not: see `UnknownChangeSet`.
    """
    staged = _names("--cached", "HEAD")
    worktree = _names()
    untracked = _untracked()
    if staged or worktree or untracked:
        return (sorted(set(staged) | set(worktree) | set(untracked)),
                "index+worktree+untracked vs HEAD", "HEAD")
    base = os.environ.get("SELE4N_PLAN_BASE_REF", "").strip()
    if base and _git("rev-parse", "--verify", "-q", f"{base}^{{commit}}")[0] == 0:
        return (sorted(set(_names(base, "HEAD"))),
                f"SELE4N_PLAN_BASE_REF ({base}) vs HEAD", base)
    if _git("rev-parse", "--verify", "HEAD~1")[0] != 0:
        raise UnknownChangeSet(
            "FAIL: changed-file anchor sweep — the working tree and the index "
            "match HEAD, `SELE4N_PLAN_BASE_REF` names no reachable commit, and "
            "HEAD has no reachable parent, so this gate cannot derive what this "
            "cut changed.  It will not report a clean sweep over an unknown "
            "change set.\n"
            "  In CI: the fast lane's \"Provide a base revision\" step exports "
            "`SELE4N_PLAN_BASE_REF`; if it resolved nothing, give the checkout "
            "`fetch-depth: 2` or more.\n"
            "  Locally: pass `--paths <file> …`, or `--all` to sweep every anchor."
        )
    return sorted(set(_names("HEAD~1", "HEAD"))), "HEAD~1 vs HEAD", "HEAD~1"


def added_anchor_lines(
    base: str,
    scripts_dir: pathlib.Path,
    repo: pathlib.Path | None = None,
) -> set[tuple[str, int]]:
    """Anchor lines this cut adds or changes, by `(script, first line number)`.

    Read from `git diff -U0`, whose hunk header gives the new line numbers
    directly.  A *moved* anchor appears as a deletion and an addition, so it is
    re-run — the safe direction, since a move can change which declaration a
    bounded gap sits in, and that is `v0.35.116`'s defect exactly.

    The key is the *logical* line, so a multi-line anchor whose continuation the
    diff touched is attributed to the line its helper name is on.

    **An UNTRACKED tier script is diffed against the empty file** (`v0.35.140`,
    PR #897's review).  `git diff` structurally cannot see a file this cut adds
    until it is staged — the fact `changed_paths` records twenty lines above, and
    which this function asked `git diff` anyway, so every anchor in a brand-new
    tier script got an empty diff, no `diff` provenance, and was **not swept**.
    Silent by construction, and silent in the case that matters: an anchor over an
    unchanged file gets no `path` or `dir` provenance either, which is the ordinary
    shape for a new suite.  Measured before choosing — a *staged* new file IS
    reported by `git diff -U0 <base>`, as a `new file mode` whose every line is an
    addition, so the hole is untracked-only and the remedy is to produce that same
    diff for the untracked case rather than to special-case the parse.
    `--no-index` against `os.devnull` is how git produces it, so the hunk header
    the loop below reads is git's own in both branches and the two cannot drift.

    **Both branches fail closed.**  `--no-index` exits **1** for *the two files
    differ*, which is the answer rather than a failure, so only a status above that
    is an error; the tracked branch's nonzero used to `continue`, which is the same
    fail-open one step over — a script whose diff git could not produce contributed
    no anchors and the sweep reported a clean run.

    **A DELETION-ONLY hunk is attributed to the surviving command**
    (`v0.35.143`, PR #897's review).  The loop recorded `+` lines only, so an
    anchor edited by *removing* a continuation contributed nothing — and, the
    changed path being the tier script rather than a file the command names, it
    got no `path` or `dir` provenance either, so the edited anchor was not swept
    at all.  `_deleted_hunk_owners` says which anchors a deletion touches and why
    both new-file neighbours are the right answer.
    """
    out: set[tuple[str, int]] = set()
    untracked = set(_untracked(repo))
    root = repo or REPO_ROOT
    for p in tier_scripts(scripts_dir):
        rel = str(p.relative_to(root)) if p.is_relative_to(root) else str(p)
        if rel in untracked:
            code, diff, _err = _git("diff", "--no-index", "-U0", os.devnull, rel, cwd=repo)
            if code > 1:
                raise UnknownChangeSet(
                    f"FAIL: changed-file anchor sweep — `git diff --no-index` "
                    f"could not diff the untracked tier suite {rel} against the "
                    f"empty file (status {code}), so this gate cannot say which "
                    f"of its anchors this cut adds.  It will not report a clean "
                    f"sweep over a suite it could not read."
                )
        else:
            code, diff, _err = _git("diff", "-U0", base, "--", rel, cwd=repo)
            if code != 0:
                raise UnknownChangeSet(
                    f"FAIL: changed-file anchor sweep — `git diff -U0 {base}` "
                    f"failed on the tier suite {rel} (status {code}), so this "
                    f"gate cannot say which of its anchors this cut adds.  It "
                    f"will not report a clean sweep over a suite it could not "
                    f"read."
                )
        owner, logical = physical_line_owners(p.read_text(encoding="utf-8"))
        lineno = 0
        for line in diff.splitlines():
            m = re.match(r"^@@ -\S+ \+(\d+)(?:,\d+)? @@", line)
            if m:
                lineno = int(m.group(1))
                continue
            if line.startswith("+++") or line.startswith("---"):
                continue
            if line.startswith("-"):
                for first in _deleted_hunk_owners(owner, logical, lineno):
                    out.add((p.name, first))
                continue
            if line.startswith("+"):
                first = owner.get(lineno)
                if first is not None and HELPER_NAME_RE.match(logical[first].strip()):
                    out.add((p.name, first))
                lineno += 1
    return out


def _deleted_hunk_owners(
    owner: dict[int, int],
    logical: dict[int, str],
    lineno: int,
) -> list[int]:
    """The surviving anchors a deletion at new-file position `lineno` touches.

    A DELETION-ONLY hunk carries no `+` line at all -- `git diff -U0` writes it
    `@@ -4 +3,0 @@` -- so a loop that records only additions attributes it to
    nothing.  An anchor edited solely by *removing* a continuation (one `-e`
    pattern, one target) therefore got no `diff` provenance, and because the
    changed path is the tier script rather than a file the command names, it got
    no `path` or `dir` provenance either: the edited anchor was not swept at all
    (PR #897's review, `v0.35.143`).  That is `v0.35.140`'s finding one hunk kind
    over -- there an added file's diff was empty, here a deletion's is nonempty
    and carries nothing the loop reads.

    Git's `+c` for a deletion is the new-file line the removed text sat *after*,
    so the surviving neighbours are `c` and `c + 1`; for a continuation deletion
    both belong to the same logical command, which is why attributing to both is
    exact there rather than merely safe.  Where an anchor was deleted **whole**
    the two neighbours are different commands and those are re-run, which is the
    over-approximating direction and costs a run.  A neighbour whose logical line
    is not a `run_*` helper contributes nothing, so ordinary shell text around an
    edit selects no anchor.
    """
    return [
        first
        for probe in (lineno, lineno + 1)
        if (first := owner.get(probe)) is not None
        and HELPER_NAME_RE.match(logical[first].strip())
    ]


def physical_line_owners(text: str) -> tuple[dict[int, int], dict[int, str]]:
    """`(physical -> logical start, logical start -> joined text)`.

    A diff reports *physical* lines and the selection keys on *logical* ones, so a
    hunk touching only a continuation must be attributed to the line its helper
    name is on.  Derived from `logical_lines` itself rather than by re-detecting
    the trailing backslash, so the two cannot disagree about where a logical line
    ends.
    """
    starts = list(logical_lines(text))
    total = len(text.splitlines())
    owner: dict[int, int] = {}
    joined: dict[int, str] = {}
    for i, (first, text_i) in enumerate(starts):
        end = starts[i + 1][0] if i + 1 < len(starts) else total + 1
        joined[first] = text_i
        for k in range(first, end):
            owner[k] = first
    return owner, joined


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--paths", nargs="*", help="override the derived change set")
    ap.add_argument("--all", action="store_true", help="select every anchor")
    ap.add_argument("--scripts-dir", default=None, help="where the tier suites live")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    scripts_dir = (
        pathlib.Path(args.scripts_dir).resolve()
        if args.scripts_dir
        else REPO_ROOT / "scripts"
    )
    invocations = anchor_invocations(scripts_dir)
    producers = anchor_producers(scripts_dir)

    if args.all:
        every = {(s, n) for s, n, _, _ in invocations}
        chosen = [
            (s, n, "all", k, d, c)
            for s, n, _, k, d, c in select(invocations, [], every, producers)
        ]
        how = "every anchor (--all)"
    elif args.paths is not None:
        chosen = select(invocations, sorted(set(args.paths)), set(), producers)
        how = "--paths"
    else:
        paths, how, base = changed_paths()
        chosen = select(invocations, paths,
                        added_anchor_lines(base, scripts_dir), producers)

    print(f"# derivation: {how}", file=sys.stderr)
    for script, n, prov, kind, disposition, command in chosen:
        print(f"{script}\t{n}\t{prov}\t{kind}\t{disposition}\t{command}")
    return 0


# --------------------------------------------------------------------------- #
# Self-test.
#
# Every selection claim is made over a synthetic invocation list, because
# `select` is pure over `(invocations, paths, added)` — so none of those cases
# needs git or a tier suite.  The three that *cannot* be made that way are made
# over a real temporary repository: a deletion and a rename must each put the OLD
# path in the change set, and a diff touching only a continuation line must be
# attributed to the logical line its helper name is on.
#
# Each case names what it would fail to catch if the rule it exercises were
# removed, because a case that cannot distinguish the fix from its absence reads
# as coverage while asserting nothing.
# --------------------------------------------------------------------------- #

#: The synthetic invocation list, with each command's kind **derived by the real
#: classifier** rather than written by hand.  `select` takes a kind as input, so a
#: hand-written one would let a case assert about a classification the tree cannot
#: produce — and the first draft of this list did exactly that, filing
#: `rg … | wc -l` as `filtered` when an unwrapped pipeline is `unparsed`.  A
#: fixture must be no thinner than the file it stands for.
_COMMANDS = [
    ("t3.sh", 10, 'run_check "I" bash -lc \'rg -n "x" SeLe4n/Kernel/IPC/Foo.lean\''),
    ("t3.sh", 11, 'run_check "I" bash -lc \'rg -n "y" SeLe4n/Kernel/IPC/Bar.lean\''),
    ("t3.sh", 12, "run_negative_check \"I\" rg -n 'z' SeLe4n/Kernel/IPC/"),
    ("t3.sh", 13,
     'run_check "I" bash -lc \'rg -n "w" SeLe4n/Kernel/IPC/Operations/Endpoint.lean\''),
    ("t3.sh", 14, 'run_check "I" bash -lc \'rg -n "v" MySeLe4n/Kernel/Other.lean\''),
    ("t0.sh", 20, 'run_prose_check "H" bash -lc \'rg -n "q" docs/spec/SELE4N_SPEC.md\''),
    ("t0.sh", 21,
     'run_check "H" python3 "${SCRIPT_DIR}/check_thing.py" SeLe4n/Kernel/IPC/Foo.lean'),
    ("t2.sh", 30,
     'run_check "T" bash -lc \'rg -n "p" "${TRACE_OUTPUT}" SeLe4n/Kernel/IPC/Foo.lean\''),
    ("t3.sh", 40,
     'run_check "I" bash -lc \'rg -n "r" SeLe4n/Kernel/IPC/Foo.lean | wc -l\''),
    ("t3.sh", 41, 'run_check "I" rg SeLe4n/Kernel/IPC/Foo.lean'),
    # --- The shell-quoting rows.  Added when the raw-text variable scan was
    # replaced by `expanding_text`; every one is a spelling that scan got wrong,
    # and rows 50-53 are the four it FALSELY deferred on the real tree.
    ("t3.sh", 50,
     """run_check "I" rg -F -n '${command}' SeLe4n/Kernel/IPC/Foo.lean"""),
    ("t3.sh", 51,
     r'''run_check "I" rg -F -n "x \${command} y" SeLe4n/Kernel/IPC/Foo.lean'''),
    ("t3.sh", 52,
     """run_check "I" bash -lc 'rg -n "a'"'"'b" SeLe4n/Kernel/IPC/Foo.lean'"""),
    ("t3.sh", 53,
     """run_check "I" rg -n 'a `b` c' SeLe4n/Kernel/IPC/Foo.lean"""),
    ("t3.sh", 54,
     """run_check "I" bash -lc "rg -n $(cat list) SeLe4n/Kernel/IPC/Foo.lean\""""),
    ("t3.sh", 55,
     """run_check "I" rg -n x SeLe4n/Kernel/IPC/Foo.lean # it's fine"""),
    ("t3.sh", 56,
     """run_check "I" bash -lc "rg -n '${X}' SeLe4n/Kernel/IPC/Foo.lean\""""),
    # --- The GLOB rows (PR #897's review, `v0.35.142`).  Two such targets are live
    # in Tier 3 (`tests/*PlatformSuite.lean`, `scripts/*cascade_check_monotonic.sh`),
    # and neither the substring `path` rule nor the delimited-literal `dir` rule
    # matched one, so a change to a matching suite selected NONE of the anchors
    # over it.  Row 61 is the same pattern inside a `-c` script, which the word
    # values have to be read through.
    ("t3.sh", 60, 'run_check "I" rg -n "g" tests/*PlatformSuite.lean'),
    ("t3.sh", 61,
     """run_check "I" bash -lc 'rg -n "h" tests/*PlatformSuite.lean'"""),
]

#: …and the kinds the classifier must give them, asserted so a change to
#: `classify_line` that reshuffles these is a named failure here rather than a
#: silently different set of cases below.  It has already earned that: `v0.35.120`
#: taught the classifier that a plain search quoted through `bash -lc` is an
#: `anchor` rather than `filtered`, and case 30 — the one that exists to exercise
#: the *undefined-variable* deferral — moved with it.  Row 40 stays `filtered`
#: because it is genuinely composed (`| wc -l`), which is what keeps the two
#: deferral reasons distinguishable.
_EXPECTED_KINDS = {
    10: "anchor", 11: "anchor", 12: "anchor", 13: "anchor", 14: "anchor",
    20: "anchor", 21: "plain", 30: "anchor", 40: "filtered", 41: "unparsed",
    50: "anchor", 51: "anchor", 52: "anchor", 53: "anchor", 54: "filtered",
    55: "anchor", 56: "anchor", 60: "anchor", 61: "anchor",
}

_INV = [
    (script, n, (classify_line(cmd) or ("unparsed",))[0], cmd)
    for script, n, cmd in _COMMANDS
]


def _fail(msg: str) -> int:
    print(f"FAIL: --self-test — {msg}", file=sys.stderr)
    return 1


#: A numbered case marker in `self_test`'s own source, e.g. `# 15b. …`.
_CASE_MARKER = re.compile(r"^[ \t]*# (\d+[a-z]?)\. ", re.MULTILINE)


def _case_count() -> int:
    """How many cases `self_test` actually contains, read from its own source.

    The figure used to be the literal `22` and was **already wrong by two** when
    `v0.35.140` looked: the cases are numbered from zero, so 0..22 is twenty-three,
    and a `15b` had joined them.  A hand-kept number beside an enumeration drifts
    on contact and reads like a measurement — the shape this project retires
    everywhere else — so it is derived, from the markers this function itself
    defines.  `inspect.getsource` is the function asking for its own text, not a
    scanner over an arbitrary file, and it **raises** rather than guessing when the
    source is unavailable, because a count that silently answers zero would be the
    fail-open direction for the line that reports coverage.
    """
    import inspect

    return len(_CASE_MARKER.findall(inspect.getsource(self_test)))


def self_test() -> int:  # noqa: C901 — one assertion per rule, deliberately flat
    import os
    import tempfile

    def picked(paths, added=None):
        return {
            (s, n, prov, disp) for s, n, prov, _k, disp, _c in select(_INV, paths, added)
        }

    FOO = "SeLe4n/Kernel/IPC/Foo.lean"

    # 0. The fixture's kinds are the classifier's.  Without this the cases below
    #    would silently test a different partition the day `classify_line` changes.
    derived = {n: kind for _s, n, kind, _c in _INV}
    if derived != _EXPECTED_KINDS:
        return _fail(
            f"the classifier now gives {derived}, not {_EXPECTED_KINDS}; the "
            f"cases below assume the latter partition"
        )

    # 1. An exact path selects its own anchor, and the enclosing DIRECTORY anchor
    #    comes in by the `dir` rule.  Without the `dir` rule a new file would face
    #    none of the tree's 43 whole-`SeLe4n/` "must not come back" negatives.
    got = picked([FOO])
    for want in (
        ("t3.sh", 10, "path", "sweep"),
        ("t3.sh", 12, "dir", "sweep"),
        ("t0.sh", 21, "path", "defer:tool"),
        ("t3.sh", 40, "path", "sweep"),
    ):
        if want not in got:
            return _fail(f"expected {want} in the selection, got {sorted(got)}")

    # 2. …and the DEEPER file anchor did NOT come in by `dir`.  Remove the token
    #    delimiter and `SeLe4n/Kernel/IPC` selects every file beneath it, which is
    #    4261 anchors on the real tree — the sweep becomes Tier 3 and its whole
    #    reason for existing is gone.
    if any(n in (11, 13) and prov == "dir" for _s, n, prov, _d in got):
        return _fail(
            "an ancestor directory selected an anchor over a DIFFERENT file "
            "beneath it; the token delimiter is not being applied"
        )

    # 3. A near-miss ancestor must not match: `SeLe4n` is not a token inside
    #    `MySeLe4n`.  Remove the lookbehind and an unrelated tree with a similar
    #    name pulls its anchors into every sweep.
    if any(n == 14 for _s, n, _p, _d in got):
        return _fail("`SeLe4n` matched inside `MySeLe4n`; the lookbehind is absent")

    # 4. A changed file nothing anchors selects nothing.  This is the honest zero,
    #    and it is asserted as an EQUALITY: a truthiness test here would pass for a
    #    selector that returned records with the wrong provenance.
    if picked(["docs/README-nothing.md"]) != set():
        return _fail(
            f"an unanchored path selected {sorted(picked(['docs/README-nothing.md']))}"
        )

    # 5. A `plain` invocation is DEFERRED, not run.  Without this the sweep would
    #    re-run Tier 0's 49 python gates and Tier 1's `lake build` in the hygiene
    #    lane, which is not a slower gate but a broken one.
    if ("t0.sh", 21, "path", "defer:tool") not in got:
        return _fail("a tool invocation was not deferred")

    # 6. A command reading a variable this gate does not define is deferred and
    #    NAMED.  Substituting a guess would make the sweep disagree with the suite
    #    about what it ran; dropping it silently is the fail-open.
    got_var = picked([FOO])
    if ("t2.sh", 30, "path", "defer:var:TRACE_OUTPUT") not in got_var:
        return _fail(
            f"an anchor reading `TRACE_OUTPUT` was not deferred by name: "
            f"{sorted(got_var)}"
        )

    # 7. …while `SCRIPT_DIR` and `REPO_ROOT` are defined, so an otherwise
    #    searching anchor that reads one is swept.  The pair is what keeps this
    #    from deferring almost everything in Tier 0.
    inv = [("t0.sh", 50, "anchor", 'run_check "H" rg -n "x" "${REPO_ROOT}/a.lean"')]
    if {d for *_ignored, d, _c in select(inv, ["a.lean"], None)} != {"sweep"}:
        return _fail("an anchor reading `REPO_ROOT` was deferred")

    # 8. An `unparsed` invocation FAILS.  It cannot fire while
    #    `check_anchor_consistency.py` is green, and it is here because that gate
    #    and this one must not disagree about which forms are readable.
    if ("t3.sh", 41, "path", "fail:unparsed") not in picked([FOO]):
        return _fail(
            f"an unparsed invocation was not reported as a failure: "
            f"{sorted(picked([FOO]))}"
        )

    # 9. The `diff` rule reaches an anchor over a file the cut did NOT change —
    #    the case `v0.35.119`'s marker-scoped harness could not express, and the
    #    reason its own 21 new anchors went unrun.
    if picked([], {("t3.sh", 13)}) != {("t3.sh", 13, "diff", "sweep")}:
        return _fail("the `diff` rule did not select a newly added anchor")

    # 10. …and `diff` wins over `path`, so an anchor is reported once.
    got = picked([FOO], {("t3.sh", 10)})
    if ("t3.sh", 10, "diff", "sweep") not in got or any(
        n == 10 and prov == "path" for _s, n, prov, _d in got
    ):
        return _fail("an added anchor over a changed file was reported twice")

    # 11. A prose anchor in another tier suite is reachable: the selection is over
    #     every discovered suite, not Tier 3 alone.
    if picked(["docs/spec/SELE4N_SPEC.md"]) != {("t0.sh", 20, "path", "sweep")}:
        return _fail("a prose anchor in another tier suite was not selected")

    # 11b. A GLOB target is a PATTERN over paths (PR #897's review, `v0.35.142`).
    #      `path` is a substring test and `dir` requires a delimited literal
    #      directory, so `tests/*PlatformSuite.lean` matched neither and a change to
    #      a matching suite selected none of the anchors over it -- two such targets
    #      are live in Tier 3.  Row 61 is the same pattern inside a `-c` script, so
    #      the word VALUES have to be read through.
    if picked(["tests/Ak9PlatformSuite.lean"]) != {
        ("t3.sh", 60, "glob", "sweep"), ("t3.sh", 61, "glob", "sweep")
    }:
        return _fail("a glob-targeted anchor was not selected by a matching path")

    # 11c. ...and `*` does not cross a `/`, which is shell semantics and not
    #      `fnmatch`'s.  Without it `tests/*PlatformSuite.lean` would match a path
    #      at any depth and `*.lean` would select most of Tier 3 -- an
    #      over-selection large enough to make the sweep useless.  The CONTROL is
    #      case 1 beside it: an ordinary path still selects by `path`/`dir` alone.
    if picked(["tests/nested/Ak9PlatformSuite.lean"]) != set():
        return _fail("a glob matched ACROSS a `/`, which is not shell semantics")

    # 12. An empty change set with no added anchors selects nothing.  The refusal
    #     belongs to the *derivation* (case 14), not to the selection.
    if picked([]) != set():
        return _fail("an empty change set selected an anchor")

    # 13. A MULTI-LINE anchor is one record carrying one command.  Nineteen live
    #     anchors put the target on a continuation line; read physically, the
    #     selection misses the path AND the executor would `eval` a command ending
    #     in a backslash.  `physical_line_owners` is what attributes a hunk on the
    #     continuation to the helper's own line.
    with tempfile.TemporaryDirectory() as td:
        sd = pathlib.Path(td)
        (sd / "test_tier9.sh").write_text(
            "#!/usr/bin/env bash\n"
            "run_check \"I\" rg -n 'sym' \\\n"
            "  SeLe4n/Kernel/Cont.lean\n"
            "echo done\n"
        )
        inv = anchor_invocations(sd)
        if len(inv) != 1:
            return _fail(f"a multi-line anchor produced {len(inv)} records, not 1")
        if "SeLe4n/Kernel/Cont.lean" not in inv[0][3] or "\\" in inv[0][3]:
            return _fail(
                f"a multi-line anchor was not folded into one command: {inv[0][3]!r}"
            )
        if not select(inv, ["SeLe4n/Kernel/Cont.lean"], None):
            return _fail("a multi-line anchor was not selected by its target path")
        owner, joined = physical_line_owners((sd / "test_tier9.sh").read_text())
        if owner.get(3) != 2:
            return _fail(
                f"a continuation line was attributed to {owner.get(3)}, not to the "
                f"helper's own line 2"
            )
        if 2 not in joined or "Cont.lean" not in joined[2]:
            return _fail("the logical text at the helper's line is not the joined one")

    # 14. The derivations that need a real repository: a DELETION and a RENAME must
    #     both put the OLD path in the change set, because that is where the
    #     anchors are.  `--no-renames` is what makes the rename report two paths;
    #     the case asserts rename detection would otherwise have hidden one.
    with tempfile.TemporaryDirectory() as td:
        root = pathlib.Path(td)
        env = {
            **os.environ,
            "GIT_AUTHOR_NAME": "t",
            "GIT_AUTHOR_EMAIL": "t@t",
            "GIT_COMMITTER_NAME": "t",
            "GIT_COMMITTER_EMAIL": "t@t",
        }

        def g(*a):
            r = subprocess.run(
                ["git", *a], cwd=root, capture_output=True, text=True, env=env
            )
            if r.returncode != 0:
                raise AssertionError(f"git {a}: {r.stderr}")
            return r.stdout

        def g_paths(*a):
            """A path listing, NUL-framed, split the way production splits.

            The harness asks git for paths the same way the readers it tests do
            (`v0.35.154`).  A fixture that lists paths unframed asserts nothing
            about a path holding a newline -- and it is a member of the very
            population `indexed_source.unframed_path_listings` measures, so
            leaving it here would mean either a gate reporting its own harness
            or an exemption, and an exemption is the enumeration that check
            exists to retire.
            """
            return _nul_split(g(*a, "-z"))

        g("init", "-q", "-b", "main")
        (root / "keep.lean").write_text("a\n")
        (root / "gone.lean").write_text("b\n")
        (root / "old.lean").write_text("c" * 200 + "\n")
        g("add", "-A")
        g("commit", "-qm", "one")
        (root / "gone.lean").unlink()
        (root / "new.lean").write_text("c" * 200 + "\n")
        (root / "old.lean").unlink()
        g("add", "-A")
        names = g_paths("diff", "--no-renames", "--name-only", "--cached", "HEAD")
        for expect in ("gone.lean", "old.lean", "new.lean"):
            if expect not in names:
                return _fail(
                    f"`--no-renames` change set {names} omits {expect}; a deleted "
                    f"or renamed file's anchors would go unswept"
                )
        detected = g_paths("diff", "--name-only", "--cached", "HEAD")
        if "old.lean" in detected:
            return _fail(
                "rename detection was already off in this git, so this case "
                "asserts nothing about `--no-renames`"
            )

        # 15. An UNTRACKED file is a change `git diff` cannot see, in either
        #     direction — so a cut whose only change is a new file would fall
        #     through to the `HEAD~1` derivation and sweep the PREVIOUS cut's
        #     files while reporting a clean run.  This gate reported exactly that
        #     on its own first run, over the two files that add it.
        (root / "brand_new.lean").write_text("d\n")
        both = g_paths("diff", "--name-only", "--cached", "HEAD")
        both += g_paths("diff", "--name-only")
        if "brand_new.lean" in both:
            return _fail(
                "`git diff` reported an untracked file, so this case asserts "
                "nothing about why `--others` is needed"
            )
        others = g_paths("ls-files", "--others", "--exclude-standard")
        if "brand_new.lean" not in others:
            return _fail(
                f"`--others --exclude-standard` change set {others} omits an "
                f"untracked file; a cut that only ADDS a file would sweep the "
                f"previous cut instead"
            )
        (root / ".gitignore").write_text("ignored.lean\n")
        (root / "ignored.lean").write_text("e\n")
        others = g_paths("ls-files", "--others", "--exclude-standard")
        if "ignored.lean" in others:
            return _fail(
                "`--exclude-standard` did not honour `.gitignore`, so build "
                "output would enter the change set"
            )

        # 15b. ...AND `added_anchor_lines` HAD TO LEARN THE SAME THING
        #      (`v0.35.140`, PR #897's review).  Case 15 fixed the CHANGE SET and
        #      this function, twenty lines below it, went on asking `git diff` —
        #      so every anchor in a brand-new tier suite got an empty diff, no
        #      `diff` provenance, and was NOT SWEPT.  Silent by construction, and
        #      silent in the case that matters: an anchor over an unchanged file
        #      gets no `path` or `dir` provenance either.  This case is
        #      FUNCTIONAL — it drives `added_anchor_lines` rather than asserting
        #      about git — and its mutation is the pre-fix reading.
        sd = root / "scripts"
        sd.mkdir()
        (sd / "test_tier0_tracked.sh").write_text(
            'run_check "A" rg -F -n \'x\' a.lean\n'
        )
        g("add", "-A")
        g("commit", "-qm", "two")
        (sd / "test_tier9_added.sh").write_text(
            'run_check "B" rg -F -n \'y\' b.lean\n'
        )
        added = added_anchor_lines("HEAD", sd, repo=root)
        if ("test_tier9_added.sh", 1) not in added:
            return _fail(
                f"an UNTRACKED tier suite contributed {sorted(added)}; `git diff` "
                f"cannot see a file this cut adds, so every anchor in a new suite "
                f"would get no `diff` provenance and go unswept"
            )
        # ...and the CONTROL, so the untracked branch is not "return everything":
        # a tracked, unmodified suite still contributes nothing.
        if ("test_tier0_tracked.sh", 1) in added:
            return _fail(
                "a tracked, UNMODIFIED tier suite contributed an added anchor, so "
                "the untracked branch is reporting every line rather than the "
                "lines this cut adds"
            )
        # ...and a base git cannot read is a REFUSAL, not an empty contribution:
        # the tracked branch used to `continue`, which is the same fail-open one
        # step over — a suite whose diff git could not produce contributed no
        # anchors and the sweep reported a clean run.
        try:
            added_anchor_lines("no-such-ref-for-this-test", sd, repo=root)
        except UnknownChangeSet:
            pass
        else:
            return _fail(
                "`added_anchor_lines` answered for a base `git diff` could not "
                "read; a suite it cannot diff must fail the gate rather than "
                "contribute nothing"
            )

        # 15c. A DELETION-ONLY hunk carries no `+` line, so an anchor edited by
        #      REMOVING a continuation got no `diff` provenance (PR #897's
        #      review, `v0.35.143`).  It got no other provenance either: the
        #      changed path is the tier script rather than a file the command
        #      names.  Case 15b's shape one hunk kind over, and FUNCTIONAL for
        #      the same reason.  Git writes a deletion `@@ -a +c,0 @@`, where `c`
        #      is the new-file line the removed text sat AFTER, so the surviving
        #      neighbours are `c` and `c + 1`.  The five sub-cases below separate
        #      every condition of the two branches, because a fixture on which
        #      both probes land in one command witnesses neither probe, and one
        #      on which every line is a helper witnesses neither filter.
        multi = sd / "test_tier8_multi.sh"
        base_text = (
            "# a header comment, so a deletion ABOVE the first anchor exists\n"
            'run_check "C" rg -n \\\n'
            "  -e 'alpha' \\\n"
            "  -e 'beta' \\\n"
            "  -e 'gamma' \\\n"
            "  c.lean\n"
            # A SECOND anchor, untouched by sub-case (i): it is what makes that
            # control decide the BRANCH rather than the fixture, since
            # "attribute a deletion to every anchor in the file" passes a
            # control that only re-checks the unmodified state.
            "run_check \"D\" rg -n 'zeta' d.lean\n"
            # ...and a run of ordinary shell text at the end, three lines, so an
            # edit INSIDE it has a non-helper logical line on BOTH sides and
            # selects no anchor at all -- which is the only thing the
            # helper-name filter decides, on either branch.
            "# ordinary shell text, three lines, so an edit inside it has a\n"
            "# non-helper logical line on both sides: neither probe of a\n"
            "# deletion here, and no addition here, may select an anchor.\n"
        )
        multi.write_text(base_text)
        g("add", "-A")
        g("commit", "-qm", "three")

        def _after(text: str) -> set[tuple[str, int]]:
            multi.write_text(text)
            found = {n for n in added_anchor_lines("HEAD", sd, repo=root)
                     if n[0] == "test_tier8_multi.sh"}
            multi.write_text(base_text)
            return found

        def _after_deleting(physical: int) -> set[tuple[str, int]]:
            kept = [ln for i, ln in enumerate(base_text.splitlines(keepends=True), 1)
                    if i != physical]
            return _after("".join(kept))

        # (i) THE FINDING: one continuation of a multi-line anchor removed.  Both
        #     probes land in that anchor, which is why it is exact here -- and
        #     the exact-set form is the control: the untouched anchor below must
        #     NOT come with it.
        cut = _after_deleting(4)
        if cut != {("test_tier8_multi.sh", 2)}:
            return _fail(
                f"deleting ONE continuation of a multi-line anchor contributed "
                f"{sorted(cut)} rather than the edited anchor alone; a "
                f"deletion-only hunk has no `+` line, so either the edited "
                f"anchor gets no `diff` provenance and goes unswept, or the "
                f"branch reports every anchor in the file instead of the "
                f"anchors the hunk survives in"
            )
        # (ii) The line BEFORE the cut is load-bearing: deleting the trailing
        #      anchor leaves `c` inside the anchor above and `c + 1` on the
        #      comment run, so `c + 1` alone finds nothing.
        if ("test_tier8_multi.sh", 2) not in _after_deleting(7):
            return _fail(
                "deleting an anchor whose successor is ordinary shell text "
                "swept no anchor; the surviving command above the cut is `c`, "
                "so dropping that probe leaves such a deletion attributed to "
                "nothing"
            )
        # (iii) ...and the line AFTER it likewise: deleting the header comment
        #       puts `c` at 0, which owns nothing, so `c` alone finds nothing.
        if ("test_tier8_multi.sh", 1) not in _after_deleting(1):
            return _fail(
                "deleting the line ABOVE the first anchor swept no anchor; a "
                "deletion at the start of a file has `c = 0`, so dropping the "
                "`c + 1` probe leaves it attributed to nothing"
            )
        # (iv) A DELETION inside ordinary shell text: both probes land on
        #      non-helper logical lines, so the helper-name filter is the only
        #      thing keeping them out of the selection.
        if _after_deleting(9):
            return _fail(
                f"deleting a line of ordinary shell text selected "
                f"{sorted(_after_deleting(9))}; both surviving neighbours are "
                f"comments, so the deletion branch is reporting logical lines "
                f"that are not anchors at all"
            )
        # (v) ...and an ADDITION there likewise, which is the same filter on the
        #     `+` branch -- unwitnessed until this cut, and the reason the `-`
        #     branch inherited the gap.
        if _after(base_text + "# a fourth line of ordinary shell text\n"):
            return _fail(
                "appending a line of ordinary shell text selected an anchor; "
                "the added line's logical owner is a comment, so the addition "
                "branch is reporting logical lines that are not anchors"
            )
        # ...and the last control: an unmodified suite contributes nothing at
        # all, so neither branch is firing on files this cut did not touch.
        if any(n == "test_tier8_multi.sh"
               for n, _ in added_anchor_lines("HEAD", sd, repo=root)):
            return _fail(
                "an UNMODIFIED multi-line anchor contributed an added line, so "
                "the deletion branch is reporting every anchor rather than the "
                "anchors this cut edits"
            )

    # 16. A `$` INSIDE SINGLE QUOTES IS A DOLLAR SIGN, NOT A VARIABLE.  The four
    #     rows 50-53 are the four spellings the raw-text variable scan falsely
    #     deferred on the real tree, and all four were anchors pinning THIS GATE's
    #     own fail-closed branches — so its blind spot sat precisely on its safety
    #     machinery.  Row 50 is `rg -F '${command}'`, row 51 the double-quoted
    #     `"x \${command} y"` (a backslash suppresses expansion inside double
    #     quotes too), row 52 the `'…'"'"'…'` idiom that assembles one `-c` script
    #     from three runs, and row 53 a Markdown code span in a pattern — five live
    #     anchors carry a backtick that way.  Revert `expanding_text` to a scan of
    #     the raw line and every one of these becomes a deferral.
    quoted = picked([FOO])
    for n in (50, 51, 52, 53):
        if ("t3.sh", n, "path", "sweep") not in quoted:
            got_disp = [d for _s, k, _p, d in quoted if k == n]
            return _fail(
                f"row {n} is a literal `$`, a reassembled `-c` script or a "
                f"backtick in a pattern, and must be SWEPT, not {got_disp}"
            )

    # 17. …while a `$` the shell really does expand is still deferred BY NAME, in
    #     both of its positions: row 30 is a single-quoted `-c` script whose
    #     interior double-quotes `${TRACE_OUTPUT}`, which the INNER shell expands
    #     (so the view must recurse), and row 56 is a double-quoted `-c` script
    #     whose interior single-quotes `${X}`, which the OUTER shell expands (so a
    #     script word must contribute its own runs as well as its value).  One of
    #     the two alone is fail-open; that is why `expanding_text` contributes both.
    for n, want in ((30, "defer:var:TRACE_OUTPUT"), (56, "defer:var:X")):
        if ("t3.sh" if n == 56 else "t2.sh", n, "path", want) not in quoted:
            return _fail(f"row {n} must be {want}: {sorted(quoted)}")

    # 18. A command substitution in an EXPANDING position is deferred by reason.
    #     Its value comes from running something, so this gate cannot reproduce
    #     what the suite ran — and it must be distinguished from row 53's
    #     single-quoted backtick, which is data.
    if ("t3.sh", 54, "path", "defer:subst") not in quoted:
        return _fail(f"an expanding `$(…)` was not deferred as `subst`: {sorted(quoted)}")

    # 19. A command this walk cannot LEX fails, and row 55 is the one live-shaped
    #     way to reach it: `shlex` strips a trailing `#` comment, so the classifier
    #     reads the line as an anchor, while this walk — which deliberately does
    #     NOT honour `#`, because honouring it is the fail-open direction — opens a
    #     single-quoted span at the apostrophe in `it's` and never closes it.  A
    #     trailing comment with an apostrophe is legal bash and this gate refuses
    #     it, loudly, naming the row: a spelling the language accepts and the gate
    #     does not is a gate defect that should say so on the day it appears.
    if ("t3.sh", 55, "path", "fail:unlexable") not in quoted:
        return _fail(f"an unlexable command did not fail: {sorted(quoted)}")

    # 20. The two `fail:` dispositions are DISTINCT, so the selector's report says
    #     which question could not be answered even though the executor answers
    #     both on one arm.  Collapsing them would be a report that names the wrong
    #     cause.
    dispositions = {d for _s, _n, _p, d in quoted}
    if not {"fail:unparsed", "fail:unlexable"} <= dispositions:
        return _fail(
            f"the two unreadable dispositions are not both reachable: {sorted(dispositions)}"
        )

    # 21. `_shell_words` splits on whitespace OUTSIDE quotes only, so the `'…'` and
    #     `"…"` runs of row 52 are ONE word, as they are to bash.  Splitting them
    #     would hand `rg -n "a` to the inner-shell view on its own and read it as an
    #     unterminated double-quoted span — which is what the first draft did, and
    #     it failed five live anchors.
    words = _shell_words(_COMMANDS[[c[1] for c in _COMMANDS].index(52)][2])
    if len(words) != 5:
        return _fail(
            f"the `'…'\"'\"'…'` idiom lexed as {len(words) - 4} script words, not "
            f"one: {words}"
        )

    # 22. …and its reassembled value is the script the inner shell receives, with
    #     the embedded single quote present.  Asserted on the VALUE rather than on
    #     the disposition, because a reassembly that dropped the quote would still
    #     sweep and would silently view a different script.
    _outer, value = _word_parts(words[4])
    if "a'b" not in value:
        return _fail(
            f"the reassembled `-c` script lost its embedded single quote: {value!r}"
        )

    # 23. **An anchor's inputs include its PRODUCERS'** (`v0.35.152`, PR #897
    #     review).  `test "${X}" -ge 5` names no path, so relating changed paths
    #     to the command alone dropped it from the selection ENTIRELY -- not
    #     deferred, not reported, absent -- and deleting conjuncts from the
    #     bundle its producer counts left the sweep green while direct Tier 3
    #     failed.  The pair below is decisive: the same anchor, selected only
    #     when the producer map is supplied, which is the pre-fix behaviour and
    #     the fixed one side by side.
    with tempfile.TemporaryDirectory() as td:
        fake = pathlib.Path(td)
        (fake / "test_tier9_fixture.sh").write_text(
            "N=$(grep -c 'x' SeLe4n/Kernel/Fake.lean)\n"
            'run_check "H" test "${N}" -ge 5\n',
            encoding="utf-8")
        invs = anchor_invocations(fake)
        prods = anchor_producers(fake)
        target = ["SeLe4n/Kernel/Fake.lean"]
        without = select(invs, target, set())
        if without:
            return _fail(
                f"a variable-backed anchor was selected with no producer map: "
                f"{without}; the pre-fix reading must select nothing, or this "
                f"case decides nothing")
        with_prod = select(invs, target, set(), prods)
        if len(with_prod) != 1 or with_prod[0][2] != "path":
            return _fail(
                f"a variable-backed anchor was not related to the path its "
                f"PRODUCER names: {with_prod}")
        if not with_prod[0][5].startswith("N=$(grep"):
            return _fail(
                f"the producer was not prepended to the executed text: "
                f"{with_prod[0][5]!r}; the relation and the command must be one "
                f"answer, or the anchor is selected and then deferred")
        # ...and a variable NO producer binds still resolves to nothing, so the
        # executor's `defer:var` arm keeps its subject.  A partial resolution
        # would be the *a FAILED derivation is not an EMPTY one* shape.
        if resolve_producers(
                prods["test_tier9_fixture.sh"], 2, {"N", "MISSING"}) is not None:
            return _fail("an unbound variable resolved to a partial prelude")

    # 15c. ...AND A RESOLVED PRODUCER FEEDING A THRESHOLD IS EXECUTED, not
    #      deferred.  `kind` was computed from the anchor ALONE and compared
    #      against `SEARCHING_KINDS`, while `missing` and `substitutes` beside it
    #      were computed from the command WITH its prelude -- one decision drawn
    #      from two subjects -- so a fully resolved `test "${N}" -ge 5` reached
    #      `defer:tool` and the sweep logged a deferral where Tier 3 fails.
    #      Measured: of eleven anchors with a resolved producer, exactly two take
    #      this shape, and both were deferred.
    THRESHOLD_CASES = [
        # (name, producer, anchor, executable?)
        ("the canonical shape",
         "N=$(grep -c foo SeLe4n/Kernel/Fake.lean)",
         'run_check "INVARIANT" test "${N}" -ge 5', True),
        # The `NI_CTORS` shape: an ALTERNATION inside the `sed` pattern, whose
        # `)` a body bounded by `[^)]*` stopped at -- so one of the two anchors
        # this contract exists for was refused by its own pattern.
        ("a sed pattern holding a parenthesised alternation",
         r"""N=$(sed -n '/^a/,/^\(b\|c\)/p' F.lean | grep -c '^| ')""",
         'run_check "INVARIANT" test "${N}" -ge 20', True),
        # A `|` inside a QUOTED pattern is not a pipeline separator; splitting
        # the text rather than the lexed words made its stage's head a fragment.
        ("a quoted pipe inside a grep pattern",
         """N=$(grep -c 'a | b' F.lean)""",
         'run_check "INVARIANT" test "${N}" -ge 1', True),
        # The nine that must stay deferred, one per reason.
        ("an EMPTY array producer (the tool would run with no arguments)",
         "shell_files_args=()",
         'run_check "HYGIENE" test "${shell_files_args}" -ge 1', False),
        ("an array producer the continuation fold TRUNCATES",
         "THEOREM_CHECK_TARGETS=(",
         'run_check "HYGIENE" test "${THEOREM_CHECK_TARGETS}" -ge 1', False),
        ("a side-effecting `mktemp` producer",
         'D="$(mktemp -d)"',
         'run_check "TRACE" test "${D}" -ge 1', False),
        ("a redirection in the producer body",
         "N=$(grep -c foo F.lean > /tmp/x)",
         'run_check "INVARIANT" test "${N}" -ge 5', False),
        ("a NESTED command substitution",
         "N=$(grep -c foo $(basename F.lean))",
         'run_check "INVARIANT" test "${N}" -ge 5', False),
        ("a `&&` rather than a plain pipeline",
         "N=$(grep -c foo F.lean && rm -rf /)",
         'run_check "INVARIANT" test "${N}" -ge 5', False),
        ("a tool outside the read-only set",
         "N=$(lake build 2)",
         'run_check "BUILD" test "${N}" -ge 5', False),
        # ...and the ANCHOR half: a producer may be perfect and the anchor still
        # not be a threshold, which is the other way this contract can be wrong.
        ("a perfect producer feeding a NON-threshold anchor",
         "N=$(grep -c foo F.lean)",
         'run_check "HYGIENE" python3 check.py "${N}"', False),
        ("...and one feeding a `test` on a DIFFERENT shape",
         "N=$(grep -c foo F.lean)",
         'run_check "INVARIANT" test -f "${N}"', False),
    ]
    for name, producer, command, want in THRESHOLD_CASES:
        got = executable_threshold([producer], command)
        if got != want:
            return _fail(
                f"executable_threshold on {name}: got {got}, want {want} "
                f"(producer {producer!r}, anchor {command!r})")

    # 15d. ...AND THE PREDICATE IS WIRED, which the cases above cannot see: they
    #      exercise `executable_threshold` directly, so a disposition branch that
    #      never consults it would leave every one of them passing while the
    #      anchor went back to `defer:tool`.  An unwitnessed condition is
    #      indistinguishable from a wrong one.
    with tempfile.TemporaryDirectory() as tmp:
        fake = pathlib.Path(tmp)
        (fake / "test_tier9_fixture.sh").write_text(
            "N=$(grep -c foo SeLe4n/Kernel/Fake.lean)\n"
            'run_check "INVARIANT" test "${N}" -ge 5\n')
        invs = anchor_invocations(fake)
        prods = anchor_producers(fake)
        rows = select(invs, ["SeLe4n/Kernel/Fake.lean"], set(), prods)
        if len(rows) != 1 or rows[0][4] != "sweep":
            return _fail(
                f"a resolved threshold anchor was not dispositioned `sweep`: "
                f"{rows}; the producer's verdict must reach the disposition, or "
                f"the sweep logs a deferral where Tier 3 fails")

    print(
        f"SELF-TEST PASS: changed-file anchor selection — {_case_count()} cases: "
        "an exact path, "
        "an ancestor directory with the token delimiter and the lookbehind both "
        "doing work, the honest empty zero, a deferred tool invocation, a "
        "deferred-and-named undefined variable, `SCRIPT_DIR`/`REPO_ROOT` swept, an "
        "unparsed invocation failing, a newly added anchor over an unchanged file, "
        "provenance precedence, another suite's prose anchor, a multi-line anchor "
        "folded and its continuation attributed, a deletion and a rename both "
        "contributing their OLD path, an untracked file in the change set while an "
        "ignored one is not, a literal `$` in four quotings swept while a real one "
        "is deferred by name from either shell, a GLOB target matched as a "
        "pattern over paths while `*` does not cross a `/`, "
        "an expanding `$(…)` deferred by "
        "reason, an unlexable command failing distinguishably, the `'…'\"'\"'…'` "
        "idiom lexed as one word whose reassembled value keeps its quote, and an "
        "untracked tier suite's anchors reported as added while a tracked "
        "unmodified one's are not and an unreadable base is refused, and a "
        "DELETION-ONLY hunk attributed to the anchor it survives in while an "
        "unmodified multi-line anchor contributes nothing, and a "
        "variable-backed anchor related to the path its PRODUCER names and "
        "executed with that producer prepended, while an unbound variable "
        "resolves to no prelude at all."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
