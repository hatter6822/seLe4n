#!/usr/bin/env python3
"""**Who decides "does this declaration carry a body"?**  (Tier 0.)

`ConstantInfo` has exactly eight constructors, and "which of them carry an
executable body" is the first question every environment-derived *domain* in this
tree has to settle.  Between `v0.35.114` and `v0.35.115` it was found to have
**six** answers across six artefacts, four of which matched the definition
constructor alone and wildcarded the rest -- so an `opaque`, which is executable,
whose body `ConstantInfo.value? (allowOpaque := true)` hands back, and which this
tree's foreign surface has seventy-odd of, was silently outside four derived
domains at once:

* `KernelTransitionReachabilityCensus` -- an unreachable `opaque` transition owed
  no wire-or-record judgement;
* `LockFootprintBoundCensus` -- an `opaque` lock-set footprint owed no `_size_le`
  bound, so `boundedWait_under_2pl` and the whole WCRT surface would be **silent**
  about it;
* `IpcDethreadingEnvironmentCensus` -- an `opaque` invariant conjunct dropped out
  of `measuredConjuncts`;
* `check_content_flow_coverage.py`'s probe -- an `opaque` writer of
  `SystemState.declassificationTaint` passed a check whose claim is "one live
  writer";
* `check_live_arm_per_core_routing.py`'s probe -- an `opaque` helper in an arm's
  chain made the reach stop there, so the arm beyond it reached "no" per-core
  slot.

`SeLe4n/Testing/DeclarationKind.lean`'s `bodyBearing` is the owner, exhaustive
over all eight with **no** `_` arm, so a ninth constructor in a future toolchain
is a missing-case error naming that function rather than a silent exclusion.

**This gate exists because stating that was not enough.**  `v0.35.114` gave the
question one owner, repointed four askers and wrote the rule into `CLAUDE.md`; the
fifth and sixth askers were then found by *sweeping the tree for the constructor
names*, not by reading the rule -- and the hand enumeration that opened
`v0.35.115` said "five".  Neither a fix nor a paragraph reaches the site nobody
has written yet, which is this project's own **"when a rule has been restated
twice, the third response is not prose"**.  A contributor who matches a
`ConstantInfo` constructor in a new place now gets a Tier 0 failure naming the
file, the constructor and the count, on the day they write it.

**The domain is derived, and it is LEAN.**  A `match` on one of these
constructors is Lean, so the question can only be *decided* in Lean -- and this
tree writes Lean in two places: `.lean` files, and probe strings inside Python
gates that hand them to `lake env lean`.  Both are in scope, and the second is
derived rather than listed: a module-level string constant whose text carries a
line-anchored `import Lean` **is** Lean source, which is exact enough that the
three such gates are found without any of them being named here, and a fourth is
found the day it is written.  A file whose text carries that line while `ast`
locates no such constant is **refused** rather than skipped, because a probe
assembled some other way is one this gate cannot read and "cannot read" must not
answer the same as "read and clean".

What is therefore *outside* the domain, stated rather than implied: a Python or
shell scanner that decided the body question by pattern-matching Lean **source
text** instead of asking the environment.  None exists (measured over every
tracked `.py` and `.sh`), and one would be the regex-for-a-Lean-question defect
this project already forbids outright -- but it would not be seen here, and that
is a gap rather than an absence.

**Gates read code, prose reads prose.**  Both views are the ones this tree
already owns -- `lean_code_view.strip` for the file, and again for a probe's text
-- rather than a third: several subjects document in their docstrings exactly
which constructors they retired, and a check that counted those would force them
to stop explaining themselves.

**What the inventory decides and what it does not.**  It is keyed
`(subject, constructor)` and carries a **count**, which is both halves of this
project's floor rule: a set of keys alone cannot see a second occurrence inside a
subject that already has one, and a count alone cannot see the first occurrence in
a subject that had none.  Reconciled in **both** directions, so a stale entry
fails as loudly as an unclassified one.  What a cardinality cannot see is an
occurrence *replaced in place* -- deleting a legitimate fail-closed reporter and
adding a wildcard sweep in the same file leaves the count identical.  That case is
semantic, and it is covered where it can be: each census reconciles its own
*derived domain* against a pin, so a domain that silently narrowed shows up there.

Usage:  scripts/check_declaration_kind_askers.py [--rows] [--self-test]
"""

from __future__ import annotations

import ast
import os
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import lean_code_view  # noqa: E402  (needs the path insert above)

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

#: `ConstantInfo`'s eight constructors, read off the toolchain's own
#: `inductive ConstantInfo` (`src/lean/Lean/Declaration.lean`).  Pinned here
#: rather than derived because this is a *Python* scanner with no elaborator to
#: ask -- and the pin is not the weak point: a constructor added upstream must
#: appear in `bodyBearing`'s match, where the missing-case error names the
#: function, and here, where its absence would let the new spelling in
#: unclassified.  The Lean side makes the omission loud; this list makes it
#: *scanned*.
CONSTANT_INFO_CONSTRUCTORS = (
    "axiomInfo", "defnInfo", "thmInfo", "opaqueInfo",
    "quotInfo", "inductInfo", "ctorInfo", "recInfo",
)

#: A Python string constant carrying this line is Lean source, not documentation.
LEAN_PROBE_MARKER = re.compile(r"^import Lean", re.M)

_WORD = {c: re.compile(rf"\b{c}\b") for c in CONSTANT_INFO_CONSTRUCTORS}


class UnreadableProbe(Exception):
    """A file embeds Lean this gate cannot locate as a string constant."""


def _tracked(repo: str, *globs: str) -> list[str]:
    """Tracked paths, so a new subject is in scope the day it is committed."""
    out = subprocess.run(["git", "ls-files", "-z", *globs], cwd=repo,
                         capture_output=True, text=True, check=True).stdout
    return [p for p in out.split("\0") if p]


def embedded_lean(path: str, text: str) -> list[tuple[str, str]]:
    """The Lean probes a Python source embeds, as (name, source) pairs.

    Derived from Python's own grammar: `ast` locates every assignment of a string
    constant to a name -- at module level or nested, since a probe returned from a
    helper is as real as one at the top -- and the ones whose text carries a
    line-anchored `import Lean` are the Lean.  The marker is what distinguishes
    Lean from a docstring that happens to quote some, and the anchor is what keeps
    a quoted `import Lean` inside a sentence from counting.

    Raises `UnreadableProbe` when the file's text carries the marker and no such
    constant does -- a probe assembled by an expression (`A + B`, a `join`, a read
    from disk) is one this scanner cannot see, and skipping it would answer the
    same as reading it.  The remedy is to bind the probe to a name, which is a
    one-line hoist; the alternative, reading past it, is how a gate goes quiet.
    """
    if not LEAN_PROBE_MARKER.search(text):
        return []
    try:
        tree = ast.parse(text)
    except SyntaxError as exc:
        raise UnreadableProbe(
            f"{path} embeds Lean (`import Lean`) and does not parse as Python "
            f"({exc}), so its probe cannot be located.") from None
    found: list[tuple[str, str]] = []
    for node in ast.walk(tree):
        targets: list[ast.expr]
        if isinstance(node, ast.Assign):
            targets = list(node.targets)
        elif isinstance(node, ast.AnnAssign):
            targets = [node.target]
        else:
            continue
        value = node.value
        if not isinstance(value, ast.Constant) or not isinstance(value.value, str):
            continue
        if not LEAN_PROBE_MARKER.search(value.value):
            continue
        for t in targets:
            if isinstance(t, ast.Name):
                found.append((t.id, value.value))
    if not found:
        raise UnreadableProbe(
            f"{path} carries `import Lean` and no module-level string constant "
            f"holding it.  A probe this scanner cannot locate is one whose "
            f"`ConstantInfo` matches it cannot count; assign the probe to a "
            f"module-level name, or the body-bearing discipline is unchecked "
            f"here.")
    return found


def _count(view: str) -> dict[str, int]:
    per: dict[str, int] = {}
    for c, pat in _WORD.items():
        n = len(pat.findall(view))
        if n:
            per[c] = n
    return per


def capture(repo: str | None = None) -> dict[str, dict[str, int]]:
    """{subject: {constructor: count}} over every Lean source in the tree.

    A subject is a `.lean` path, or `<python path>::<PROBE NAME>`.
    """
    repo = repo or REPO
    found: dict[str, dict[str, int]] = {}
    for rel in _tracked(repo, "*.lean"):
        abs_path = os.path.join(repo, rel)
        if not os.path.isfile(abs_path):
            continue
        text = open(abs_path, encoding="utf-8").read()
        if not any(c in text for c in CONSTANT_INFO_CONSTRUCTORS):
            continue
        # An unterminated comment propagates rather than degrading to a raw read
        # or a skip: "a scanner's default branch is a decision".
        per = _count(lean_code_view.strip(text))
        if per:
            found[rel] = per
    for rel in _tracked(repo, "*.py"):
        abs_path = os.path.join(repo, rel)
        if not os.path.isfile(abs_path):
            continue
        text = open(abs_path, encoding="utf-8").read()
        for name, src in embedded_lean(rel, text):
            per = _count(lean_code_view.strip(src))
            if not per:
                continue
            # Two assignments may bind one name (a module-level probe and a
            # nested rebinding).  Their counts ACCUMULATE: taking the last would
            # be a cardinality that hides the other, which is the defect this
            # inventory's shape exists to refuse.
            key = f"{rel}::{name}"
            acc = found.setdefault(key, {})
            for c, n in per.items():
                acc[c] = acc.get(c, 0) + n
    return found


#: Why each subject legitimately matches a `ConstantInfo` constructor.
#:
#: Read these as answers to one question: *what does this subject ask of the
#: constructors, and is it the body-bearing question?*  Exactly one subject may
#: answer "yes" -- the owner.  Every other one asks a genuinely different
#: question of them, or reports one fail-closed.
ASKER_REASONS: dict[str, str] = {
    "SeLe4n/Testing/DeclarationKind.lean":
        "THE OWNER.  `bodyBearing` matches all eight with no wildcard arm, so a "
        "ninth constructor in a future toolchain is a missing-case error naming "
        "this function rather than a silent exclusion.",
    "SeLe4n/Testing/KernelTransitionReachabilityCensus.lean":
        "Two fail-CLOSED theorem reporters, neither of them the body question: a "
        "pin entry that names a theorem, and a pin-check witness that is one, are "
        "each REPORTED as a defect rather than skipped.  The census's own domain "
        "test reads `bodyBearing`.",
    "SeLe4n/Testing/IpcDethreadingEnvironmentCensus.lean":
        "One fail-CLOSED assertion that its single named root is a definition; a "
        "root that is anything else throws.  The frontier walk it drives reads "
        "`bodyBearing`.",
    "SeLe4n/Testing/StoreReadClassificationCensus.lean":
        "`structureLike` asks whether a constant is an INDUCTIVE -- a different "
        "question, for which a `false` wildcard is the right answer, since the "
        "eight constructors partition on that too.",
    "scripts/check_module_axioms.py::PROBE_TEMPLATE":
        "Two questions, neither the body one.  `axiomSweepEdges` enumerates which "
        "constants `CollectAxioms.collect` steps into, case for case over all "
        "eight, with the only default arm being the unknown NAME rather than an "
        "unclassified constructor -- the precedent this discipline generalises, "
        "since it was doing the right thing before there was a rule, which is why "
        "it is a model rather than a finding.  `axiomSweepIsAxiom` is the second "
        "axiom match: is this constant an axiom, which is why that constructor "
        "appears twice.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_PROBE_PY":
        "THIS GATE'S OWN FIXTURE, and pinning it is the point rather than the "
        "price: a fixture that silently lost its constructor matches would go "
        "inert, and an inert fixture reads as coverage while asserting nothing.  "
        "The counts are an artefact of the fixture being PYTHON source that "
        "embeds Lean -- the marker classifies it as Lean, so the Python docstring "
        "outside the probe is read as Lean text and its quoted constructor "
        "counts, and a Lean docstring after a `\"\"\"` is inside what the Lean view "
        "reads as a string literal and so survives.  Neither affects the real "
        "subjects, which are whole `.lean` files and probe VALUES, both pure "
        "Lean; recording the artefact is cheaper and more honest than reshaping "
        "the fixture to hide from the scanner.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_SPLIT_PROBE":
        "THIS GATE'S OWN FIXTURE for the refusal direction, pinned for the same "
        "reason: its `match` is what makes the unlocatable case a fail-OPEN one, "
        "so a fixture that lost it would assert nothing while still passing.",
}

#: The inventory: {subject: {constructor: count}}, reconciled both directions.
#:
#: Counts, not just keys: a set of keys alone cannot see a second occurrence
#: inside a subject that already has one, and a count alone cannot see the first
#: occurrence in a subject that had none, so the floor is both -- the shape
#: `identifier_naming_baseline.json` and the AK7 cascade inventory already have.
DECLARATION_KIND_ASKERS: dict[str, dict[str, int]] = {
    "SeLe4n/Testing/DeclarationKind.lean": {
        "axiomInfo": 1, "defnInfo": 1, "thmInfo": 1, "opaqueInfo": 1,
        "quotInfo": 1, "inductInfo": 1, "ctorInfo": 1, "recInfo": 1,
    },
    "SeLe4n/Testing/KernelTransitionReachabilityCensus.lean": {"thmInfo": 2},
    "SeLe4n/Testing/IpcDethreadingEnvironmentCensus.lean": {"defnInfo": 1},
    "SeLe4n/Testing/StoreReadClassificationCensus.lean": {"inductInfo": 1},
    "scripts/check_module_axioms.py::PROBE_TEMPLATE": {
        "axiomInfo": 2, "defnInfo": 1, "thmInfo": 1, "opaqueInfo": 1,
        "quotInfo": 1, "inductInfo": 1, "ctorInfo": 1, "recInfo": 1,
    },
    "scripts/check_declaration_kind_askers.py::_FIXTURE_PROBE_PY": {
        "ctorInfo": 1, "defnInfo": 1, "thmInfo": 1,
    },
    "scripts/check_declaration_kind_askers.py::_FIXTURE_SPLIT_PROBE": {
        "defnInfo": 1,
    },
}


def violations(repo: str | None = None,
               pin: dict[str, dict[str, int]] | None = None,
               reasons: dict[str, str] | None = None) -> list[str]:
    """Reconcile the capture against the pin, in BOTH directions."""
    pin = DECLARATION_KIND_ASKERS if pin is None else pin
    reasons = ASKER_REASONS if reasons is None else reasons
    try:
        found = capture(repo)
    except UnreadableProbe as exc:
        return [str(exc)]
    problems: list[str] = []
    for subj in sorted(found):
        if subj not in pin:
            names = ", ".join(f"`.{c}` x{n}" for c, n in sorted(found[subj].items()))
            problems.append(
                f"{subj} matches a `ConstantInfo` constructor ({names}) and is "
                f"not a recorded asker.  \"Does this declaration carry a body\" "
                f"has one owner, `SeLe4n/Testing/DeclarationKind.lean`'s "
                f"`bodyBearing`: call it, or read a definition that does, rather "
                f"than matching the constructors here.  If this subject asks a "
                f"DIFFERENT question of them, record it in "
                f"DECLARATION_KIND_ASKERS with a reason.")
    for subj in sorted(pin):
        if subj not in found:
            problems.append(
                f"{subj} is a recorded asker and matches no `ConstantInfo` "
                f"constructor any more.  A stale exemption reads exactly like "
                f"coverage; delete the entry.")
            continue
        want, got = pin[subj], found[subj]
        for c in sorted(set(want) | set(got)):
            w, g = want.get(c, 0), got.get(c, 0)
            if w != g:
                problems.append(
                    f"{subj}: `.{c}` matched {g}x, recorded {w}x.  A new match is "
                    f"a new place deciding the body question; a removed one is a "
                    f"stale record.  Move the count only with the reason in "
                    f"ASKER_REASONS still true of every occurrence.")
    for subj in sorted(pin):
        if subj not in reasons:
            problems.append(
                f"{subj} is recorded in DECLARATION_KIND_ASKERS with no entry in "
                f"ASKER_REASONS.  An exemption with no stated reason is one "
                f"nobody can check.")
    for subj in sorted(reasons):
        if subj not in pin:
            problems.append(
                f"{subj} has an ASKER_REASONS entry and no inventory row.  The "
                f"two tables describe one set and must agree.")
    return problems


# ---------------------------------------------------------------------------
# --self-test
# ---------------------------------------------------------------------------
#
# A discipline check that cannot fire is indistinguishable from one that is
# wrong, so every direction is exercised on a synthetic tree: a clean subject
# passes, an unrecorded one is reported, a stale entry is reported, a moved count
# is reported in either direction, either table orphaned is reported, and a file
# whose Lean the scanner cannot locate is refused rather than skipped.  The tree
# is synthetic rather than a copy of the real one because the capture reads
# `git ls-files`, and a case that mutated the working tree would be a case that
# can corrupt it.

_FIXTURE_OWNER = """\
/-- The body question's owner.

Its docstring names `.defnInfo` and `.opaqueInfo` on purpose: a check that
counted a docstring would force this module to stop explaining itself, so the
comment-free view is what the count is taken over. -/
def bodyBearing : ConstantInfo -> Bool
  | .defnInfo _   => true
  | .opaqueInfo _ => true
  | .thmInfo _    => false
  | .axiomInfo _  => false
  | .quotInfo _   => false
  | .inductInfo _ => false
  | .ctorInfo _   => false
  | .recInfo _    => false
"""

#: A gate with an embedded Lean probe, thick enough to stand for the real ones:
#: a Python docstring naming a constructor outside the probe, and a Lean
#: docstring naming one inside it.  Neither may count; the probe's `match` must.
_FIXTURE_PROBE_PY = '''\
"""A gate with an embedded Lean probe.

This docstring quotes `.defnInfo`, and it must not count: it is not inside the
probe, and the probe is what this scanner reads.
"""

PROBE = """
import SeLe4n
import Lean.Elab.Command

open Lean Elab Command

/-- A probe docstring naming `.thmInfo`, which the Lean view removes. -/
private def probeAsker (ci : ConstantInfo) : Bool :=
  match ci with
  | .ctorInfo _ => true
  | _ => false
"""
'''

_FIXTURE_ROGUE = """\
def rogue (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ => true
  | _ => false
"""

#: A probe assembled by concatenation: the marker is in the file's text and in
#: no single string constant, so `ast` locates nothing and the scan must REFUSE.
_FIXTURE_SPLIT_PROBE = '''\
PROBE = """
import SeLe4n
""" + """
import Lean.Elab.Command

private def hidden (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ => true
  | _ => false
"""
'''


def _git(repo: str, *args: str) -> None:
    subprocess.run(["git", *args], cwd=repo, check=True,
                   capture_output=True, text=True)


def _fixture(root: str, files: dict[str, str]) -> None:
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "selftest@example.invalid")
    _git(root, "config", "user.name", "self-test")
    for rel, body in files.items():
        path = os.path.join(root, rel)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(body)
    _git(root, "add", "-A")


def _self_test() -> int:
    owner = "SeLe4n/Testing/DeclarationKind.lean"
    gate = "scripts/probe_gate.py"
    probe_subject = gate + "::PROBE"
    base = {owner: _FIXTURE_OWNER, gate: _FIXTURE_PROBE_PY}
    owner_pin = {c: 1 for c in CONSTANT_INFO_CONSTRUCTORS}
    base_pin = {owner: dict(owner_pin), probe_subject: {"ctorInfo": 1}}
    base_reasons = {owner: "the owner", probe_subject: "a different question"}

    # (1) The clean fixture passes, and the counts are the ones the VIEW gives:
    #     eight in the owner (its docstring's two are stripped) and exactly one
    #     in the probe (its own Lean docstring's one is stripped, and the Python
    #     docstring outside the probe is not read at all).
    with tempfile.TemporaryDirectory() as root:
        _fixture(root, base)
        got = capture(root)
        if got != base_pin:
            print("FAIL: --self-test — the capture over a clean fixture is")
            print(f"      {got}, expected {base_pin}.  Either the Lean view has")
            print("      stopped stripping comments (a docstring naming a")
            print("      constructor would then be a site, and every subject that")
            print("      documents what it retired would have to stop), or the")
            print("      probe extraction has stopped reading the Lean inside a")
            print("      Python string — which is where two of this cut's six")
            print("      defects were.")
            return 1
        clean = violations(root, base_pin, base_reasons)
        if clean:
            print("FAIL: --self-test — a clean fixture reports violations:")
            for v in clean:
                print(f"      {v}")
            return 1

    # (2) A NEW subject is reported.  The mutation keeps every recorded subject
    #     and every count and adds a sixth asker — the shape each of this cut's
    #     findings had, since each was a new place deciding the question.
    with tempfile.TemporaryDirectory() as root:
        newcomer = "SeLe4n/Kernel/RogueCensus.lean"
        _fixture(root, {**base, newcomer: _FIXTURE_ROGUE})
        problems = violations(root, base_pin, base_reasons)
        if not any(newcomer in p and "not a recorded asker" in p
                   for p in problems):
            print("FAIL: --self-test — a NEW subject matching a constructor was")
            print(f"      not reported: {problems}.  This is the only direction")
            print("      that catches the site nobody has written yet, which is")
            print("      the whole reason this gate exists rather than a third")
            print("      telling of the rule in prose.")
            return 1

    # (3) A STALE entry is reported.  A subject that stops matching must leave
    #     the table: an exemption whose subject is gone reads exactly like
    #     coverage.
    with tempfile.TemporaryDirectory() as root:
        _fixture(root, base)
        stale_key = "SeLe4n/Kernel/Gone.lean"
        stale = {**base_pin, stale_key: {"defnInfo": 1}}
        stale_reasons = {**base_reasons, stale_key: "retired"}
        problems = violations(root, stale, stale_reasons)
        if not any(stale_key in p and "stale exemption" in p for p in problems):
            print("FAIL: --self-test — a STALE inventory entry was not reported:")
            print(f"      {problems}.  Reconciling one direction only is how an")
            print("      exemption outlives the thing it excused.")
            return 1

    # (4) A MOVED count is reported in BOTH directions, with the key present
    #     throughout.  A set of keys alone cannot see a second occurrence inside
    #     a subject that already has one, which is why the floor carries counts;
    #     a count alone cannot see the first occurrence in a subject that had
    #     none, which is why it carries keys.
    with tempfile.TemporaryDirectory() as root:
        _fixture(root, base)
        for moved_counts, why in (({"ctorInfo": 2}, "raised"),
                                  ({"recInfo": 1}, "relabelled")):
            moved = {**base_pin, probe_subject: moved_counts}
            problems = violations(root, moved, base_reasons)
            if not any(probe_subject in p and "recorded" in p
                       for p in problems):
                print(f"FAIL: --self-test — a {why} count was not reported:")
                print(f"      {problems}.")
                return 1

    # (5) Both tables describe one set, and the check says so in both
    #     directions: an inventory row with no reason cannot be audited, and a
    #     reason with no row describes nothing.
    with tempfile.TemporaryDirectory() as root:
        _fixture(root, base)
        no_reason = violations(root, base_pin, {owner: "the owner"})
        if not any(probe_subject in p and "ASKER_REASONS" in p
                   for p in no_reason):
            print("FAIL: --self-test — an inventory row with no stated reason was")
            print(f"      not reported: {no_reason}.")
            return 1
        orphan = violations(root, {owner: dict(owner_pin)}, base_reasons)
        if not any(probe_subject in p and "no inventory row" in p
                   for p in orphan):
            print("FAIL: --self-test — a reason with no inventory row was not")
            print(f"      reported: {orphan}.")
            return 1

    # (6) A file that embeds Lean the scanner cannot LOCATE is refused, not
    #     skipped.  "The gate could not read it" and "the gate read it and it is
    #     clean" must never produce the same verdict, and a probe assembled by
    #     concatenation is exactly the input that produces the second by
    #     accident.
    with tempfile.TemporaryDirectory() as root:
        split = "scripts/split_gate.py"
        _fixture(root, {**base, split: _FIXTURE_SPLIT_PROBE})
        problems = violations(root, base_pin, base_reasons)
        if not any(split in p and "cannot locate" in p for p in problems):
            print("FAIL: --self-test — a Python file carrying `import Lean` with")
            print("      no locatable string constant was not refused:")
            print(f"      {problems}.  A probe this scanner cannot read is one")
            print("      whose constructor matches it cannot count, and a silent")
            print("      skip answers the same as a clean read.")
            return 1

    # (7) The real tree, which is the check the tier runs.
    live = violations()
    if live:
        print("FAIL: --self-test — the live tree reports violations:")
        for v in live:
            print(f"      {v}")
        return 1

    found = capture()
    print(f"[declaration-kind] SELF-TEST PASS: the capture reads the Lean view "
          f"of both a `.lean` file and a probe embedded in Python; a new "
          f"subject, a stale entry, a moved count in either direction, either "
          f"table orphaned, and an unlocatable probe are each reported; the "
          f"live tree is clean at {len(found)} subject(s).")
    return 0


def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        return _self_test()
    if "--rows" in argv:
        for subj, per in sorted(capture().items()):
            for c, n in sorted(per.items()):
                print(f"DECLARATION_KIND_SITE {subj} {c} {n}")
    problems = violations()
    if problems:
        print("FAIL: the body-bearing question is decided outside its owner.")
        for p in problems:
            print(f"  {p}")
        return 1
    found = capture()
    total = sum(sum(v.values()) for v in found.values())
    print(f"[declaration-kind] PASS: {total} `ConstantInfo` constructor match(es) "
          f"across {len(found)} recorded subject(s) "
          f"({sum(1 for s in found if '::' in s)} embedded Lean probe(s)); the "
          f"body-bearing question has one owner.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
