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
#:
#: **Both import roots, since `v0.35.118`.**  It read `^import Lean` alone, and a
#: probe importing only a project module (`import SeLe4n.Testing.DeclarationKind`)
#: carries no such line while exposing `ConstantInfo` just the same -- every
#: project module imports Lean -- so the early return in `embedded_lean` SKIPPED
#: it and a new body-kind asker bypassed this inventory with the gate reporting the
#: tree clean.  That is a domain defect in the gate written to close domain
#: defects, and it is silent by construction: the probe is never examined, no count
#: moves, and the reconciliation goes on reporting that its whole domain is
#: accounted for.
LEAN_PROBE_MARKER = re.compile(r"^import\s+(?:Lean|SeLe4n)\b", re.M)

_WORD = {c: re.compile(rf"\b{c}\b") for c in CONSTANT_INFO_CONSTRUCTORS}

#: The second locator, and the one that does not depend on a probe importing
#: anything at all: a string constant that NAMES a `ConstantInfo` constructor is
#: Lean source deciding the question this gate is about, whatever its imports say.
#: Derived from the same tuple the counters are, so a ninth constructor added there
#: widens the locator and the counts together.
#:
#: It is a LOCATOR and not a refusal trigger.  The refusal asks whether a file
#: EMBEDS Lean it could not locate, and only the import marker *entails* that: a
#: line-anchored `import Lean` / `import SeLe4n` is Lean source, while a
#: constructor name is also what a sentence explaining what a subject retired
#: carries -- this file holds 35 such unattributed constants (the tuple above, the
#: baseline's keys, the reasons' prose).  Refusing on the weaker signal would
#: refuse a file whose only mention is prose and which embeds no probe at all.
#:
#: **Measured, not assumed**: on today's tree the two refusal conditions are
#: indistinguishable -- every file carrying a constructor name also binds a
#: signal-bearing constant, so `found` is non-empty and neither refuses -- which a
#: mutation confirmed by passing the self-test with the refusal moved onto the
#: widened signal.  So the choice rests on which signal entails an embedded probe
#: rather than on an observed failure, and it is stated that way rather than
#: justified by a difference that does not exist yet.  What the widened MARKER does
#: buy is real and is witnessed: an assembled probe (`A + B`, a `join`, an
#: f-string) importing only a project root is now refused where it used to be
#: invisible in both directions at once.
#:
#: It OVER-approximates in one direction, deliberately: a *named* constant holding
#: prose that quotes a constructor is located as a probe and counted.  Measured --
#: no such constant exists today, the seven named signal-bearing constants in the
#: tree all being probes or this gate's own fixtures -- and the remedy if one
#: appears is a recorded row saying so, never a narrowing: over-reporting costs a
#: baseline entry, under-reporting costs the gate.
_ANY_CONSTRUCTOR = re.compile(
    r"\b(?:" + "|".join(CONSTANT_INFO_CONSTRUCTORS) + r")\b")


def _probe_signal(text: str) -> bool:
    """Is this text Lean source that could decide the body-bearing question?"""
    return bool(LEAN_PROBE_MARKER.search(text) or _ANY_CONSTRUCTOR.search(text))


class UnreadableProbe(Exception):
    """A file embeds Lean this gate cannot locate as a string constant."""


def _tracked(repo: str, *globs: str) -> list[str]:
    """Tracked paths, so a new subject is in scope the day it is committed."""
    out = subprocess.run(["git", "ls-files", "-z", *globs], cwd=repo,
                         capture_output=True, text=True, check=True).stdout
    return [p for p in out.split("\0") if p]


def _string_constants(tree: ast.AST) -> list[tuple[str, ast.Constant]]:
    """`(scope, node)` for every string constant, with its enclosing declaration.

    The scope is the nearest enclosing `def`/`class` name, or `<module>`: that is
    what a reader needs in order to find the probe, and unlike a line number it
    survives reformatting.  `ast` carries no parent links, so the walk is explicit.
    """
    out: list[tuple[str, ast.Constant]] = []

    def walk(node: ast.AST, scope: str) -> None:
        for child in ast.iter_child_nodes(node):
            inner = scope
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                                  ast.ClassDef)):
                inner = child.name
            if isinstance(child, ast.Constant) and isinstance(child.value, str):
                out.append((scope, child))
            walk(child, inner)

    walk(tree, "<module>")
    return out


def _is_concatenation(node: ast.AST) -> bool:
    """Does this expression build ONE string out of several parts?

    The four forms this tree's probes are assembled with.  Kept as a predicate
    rather than inlined because the group walk and the assignment walk both ask it,
    and two spellings of "is this a concatenation" could disagree about which
    expression a probe's name belongs to.
    """
    return bool(
        (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add))
        or isinstance(node, ast.JoinedStr)
        or (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr in ("join", "format"))
    )


def _concatenation_groups(
        tree: ast.AST) -> list[tuple[ast.AST, list[ast.Constant]]]:
    """`(expression, its string constants in SOURCE ORDER)` per assembled string.

    `a + b`, an f-string, and a `.join(…)` / `.format(…)` call are the forms this
    tree's probes are assembled with.  The grouping is what makes an ASSEMBLED
    probe readable: one fragment carries the import marker and another carries the
    `ConstantInfo` match, and neither is a probe on its own evidence.

    Deliberately an EXPRESSION and not a statement.  Grouping by statement was
    measured at **1060** admitted fragments, because `ast.walk` of a statement
    descends into every nested one -- a dict of fixtures pulls in all of them.
    Grouping by these four expression forms admits **zero** on the tracked tree, so
    the widening costs nothing and its witnesses are entirely planted.

    Only MAXIMAL groups are returned: a nested concatenation (`f"{x}" + "y"`) is
    part of the string its parent builds, so reporting it as well would count one
    fragment under two subjects.  And the constants are sorted by position, because
    `ast.walk` is breadth-first -- `"a" + "b" + "c"` yields `c, a, b` -- and the
    reassembled text is what the constructor patterns are counted over, so a
    fragment boundary in the wrong place can both invent a match and destroy one.
    """
    nodes = [n for n in ast.walk(tree) if _is_concatenation(n)]
    nested = {id(d) for n in nodes for d in ast.walk(n)
              if d is not n and _is_concatenation(d)}
    groups: list[tuple[ast.AST, list[ast.Constant]]] = []
    for node in nodes:
        if id(node) in nested:
            continue
        constants = sorted(
            (c for c in ast.walk(node)
             if isinstance(c, ast.Constant) and isinstance(c.value, str)),
            key=lambda c: (c.lineno, c.col_offset))
        if constants:
            groups.append((node, constants))
    return groups


def embedded_lean(path: str, text: str) -> list[tuple[str, str]]:
    """The Lean probes a Python source embeds, as (name, source) pairs.

    Derived from Python's own grammar, in three shapes, because the first two were
    each a domain written as a node kind.  `ast` locates (a) every assignment of a
    string constant to a name -- at module level or nested, since a probe returned
    from a helper is as real as one at the top -- (b) every expression that
    ASSEMBLES one out of fragments, named after its assignment target where it has
    one and after its enclosing declaration where it does not, and (c) every
    remaining string constant that binds no name at all, which is what a probe
    handed straight to `run_probe(<literal>)` is.

    (a) is admitted on a **probe signal**; (b) and (c) on the IMPORT MARKER alone.
    Two signals, because one was not enough (`v0.35.118`): a line-anchored import
    of `Lean` **or of a project module**, and a `ConstantInfo` constructor name.
    The import is what distinguishes Lean from a docstring that happens to quote
    some, the anchor is what keeps a quoted `import Lean` inside a sentence from
    counting, and the constructor is what locates a probe that imports neither root
    by the spelling this gate is actually about -- *the question, not one of its
    preconditions*.  For (b) and (c) the constructor alone would be too wide: a
    docstring and a concatenated diagnostic are both ordinary Python, and a
    constructor name is exactly what prose explaining a retired reading carries, so
    admitting them would force every subject in this tree to stop explaining what
    it retired.  An assembled or inline *probe* is by construction Lean source and
    so imports a root.

    Raises `UnreadableProbe` when the located constants do not account for every
    import marker in the file's text -- a probe read from disk, or split so that no
    fragment carries the marker, is one this scanner cannot see, and skipping it
    would answer the same as reading it.  Asked as a COUNT and not as "did we find
    anything", because one located probe used to answer the question for every
    marker in the file: a cardinality is what sees the second occurrence.  The
    remedy is to bind the probe to a name, which is a one-line hoist; the
    alternative, reading past it, is how a gate goes quiet.  The count is over the
    LOCATED CONSTANTS and not over the rows reported, because one constant bound to
    two names (`A = B = <probe>`) reports twice: counting rows would let that surplus
    mask a marker the scanner really cannot see.  Raises it again when
    two probes that bind no name share one scope, since a subject key two probes
    share cannot see a count moving between them -- the same remedy, for the same
    reason.  What it leaves outside is stated rather than implied: a probe that
    imports neither root **and** reaches this scanner as neither a named constant,
    an assembled one, nor a bare one.  Both roots are recognised, so a real Lean
    probe has to import one of them.

    What no source scanner can close, and what this one therefore does NOT claim: a
    fragment that is not a literal contributes text that is not in the file.  A
    `Name` fragment is harmless -- the constant it is bound to is a subject of its
    own, so its matches are counted under that name -- but a fragment computed by a
    call is unreadable, and where such a fragment carries the `ConstantInfo` match
    while a literal one carries the import, the marker IS accounted for and the count
    is a FLOOR.  That is the same residue as a probe read from disk, which has no
    string constant at all; it is stated rather than approximated, because a refusal
    keyed on "some fragment is not a literal" would also refuse the readable
    `HEADER + <literal>` shape.
    """
    if not _probe_signal(text):
        return []
    try:
        tree = ast.parse(text)
    except SyntaxError as exc:
        raise UnreadableProbe(
            f"{path} embeds Lean (an `import Lean`/`import SeLe4n` line, or a "
            f"`ConstantInfo` constructor) and does not parse as Python ({exc}), so "
            f"its probe cannot be located.") from None
    found: list[tuple[str, str]] = []
    named: set[int] = set()
    constants = _string_constants(tree)
    scopes = {id(c): scope for scope, c in constants}
    by_id = {id(c): c for _, c in constants}
    groups = _concatenation_groups(tree)
    group_of: dict[int, list[ast.Constant]] = {id(n): cs for n, cs in groups}
    claimed: set[int] = set()
    for node in ast.walk(tree):
        targets: list[ast.expr]
        if isinstance(node, ast.Assign):
            targets = list(node.targets)
        elif isinstance(node, ast.AnnAssign):
            targets = [node.target]
        else:
            continue
        names = [t.id for t in targets if isinstance(t, ast.Name)]
        if not names:
            continue
        value = node.value
        if isinstance(value, ast.Constant) and isinstance(value.value, str):
            if not _probe_signal(value.value):
                continue
            named.add(id(value))
            for name in names:
                found.append((name, value.value))
            continue
        # ...and a value the assignment ASSEMBLES is named after the same target.
        # A probe bound to a name is bound to it whether the right-hand side is one
        # literal or three, so reporting the assembled one as `<inline in …>` would
        # answer "what is this subject called" two ways -- and, worse, would collapse
        # two assembled probes in one module into ONE key, where the counts add and
        # a count moving between them is invisible.  That is the cardinality-for-a-set
        # defect inside the widening that closes it, so the name is taken here.
        #
        # The signal is the MARKER, not the widened `_probe_signal`: a concatenated
        # message string quoting a constructor is an everyday Python idiom and this
        # tree's own diagnostics are full of them, while an assembled *probe* is by
        # construction Lean source and so imports a root.
        fragments = group_of.get(id(value))
        if fragments is None:
            continue
        if not any(LEAN_PROBE_MARKER.search(c.value) for c in fragments):
            continue
        claimed.add(id(value))
        named.update(id(c) for c in fragments)
        for name in names:
            found.append((name, "".join(c.value for c in fragments)))
    # ...AND the ones that bind no name.  A walker reading only assignments could
    # not see `run_probe("""import SeLe4n … .opaqueInfo …""")`, and an assigned
    # probe elsewhere in the file made `found` non-empty, which suppressed the
    # refusal below -- so an inline probe could re-decide the body-bearing question
    # with the captured inventory unchanged and Tier 0 green, invisible in both
    # directions at once.  Keyed by its ENCLOSING DECLARATION rather than by a line
    # number, so the key survives reformatting; several in one scope accumulate,
    # which is what the per-key counts already do for two assignments to one name.
    #
    # TWO shapes, and the second is why the refusal stopped having to stand in for
    # a locator.  A constant carrying the IMPORT MARKER is probe text on its own
    # evidence.  An expression that ASSEMBLES one carries the marker in one fragment
    # and the `ConstantInfo` match in another, so neither fragment qualifies alone
    # and the whole probe used to be refused rather than read; it is reassembled and
    # counted once, because the expression builds one string.
    #
    # The marker -- not the widened `_probe_signal` -- is what identifies an
    # unnamed constant, because a docstring is an `ast.Constant` too and a
    # constructor name is exactly what prose explaining a retired reading carries.
    # Measured: under the marker, zero unnamed constants on the tracked tree are
    # admitted; under the widened signal, one message string would be, and this
    # tree's own diagnostics would have to stop naming what they retired.
    inline: list[tuple[str, str]] = []
    for node, fragments in groups:
        if id(node) in claimed:
            continue
        if not any(LEAN_PROBE_MARKER.search(c.value) for c in fragments):
            continue
        named.update(id(c) for c in fragments)
        inline.append((scopes[id(fragments[0])],
                       "".join(c.value for c in fragments)))
    for scope, constant in _string_constants(tree):
        if id(constant) in named:
            continue
        if not LEAN_PROBE_MARKER.search(constant.value):
            continue
        named.add(id(constant))
        inline.append((scope, constant.value))
    # TWO unnamed probes in ONE scope are REFUSED, not accumulated.  A key that two
    # subjects share cannot see a count moving between them -- probe A loses a
    # `.defnInfo`, probe B gains one, the total is unchanged and the reconciliation
    # says nothing -- which is the cardinality-for-a-set defect this whole inventory
    # is shaped against.  An ordinal (`<inline #2 in foo>`) would be a key that
    # churns when an earlier probe is deleted, so the answer is the one this project
    # gives everywhere a scanner cannot decide: refuse, name the scope, and state the
    # remedy, which is the same one-line hoist the marker refusal asks for.  Costs
    # nothing today -- zero unnamed probes on the tracked tree -- and it is what
    # keeps `<inline in …>` identifying a subject rather than a bucket.
    per_scope: dict[str, int] = {}
    for scope, _src in inline:
        per_scope[scope] = per_scope.get(scope, 0) + 1
    crowded = sorted(s for s, n in per_scope.items() if n > 1)
    if crowded:
        raise UnreadableProbe(
            f"{path} embeds {per_scope[crowded[0]]} probes that bind no name in "
            f"`{crowded[0]}`" + (f" (and in {', '.join(crowded[1:])})"
                                 if len(crowded) > 1 else "") + ".  They would "
            f"share one subject key, where a count moving from one to the other is "
            f"invisible; bind each probe to a name so each has its own.")
    for scope, src in inline:
        found.append((f"<inline in {scope}>", src))
    # A marker the located constants do not account for is probe text this scanner
    # CANNOT see -- read from disk, or split so that no fragment carries it.  Asked
    # as a COUNT rather than as "did we find anything", because one located probe
    # used to answer the question for every marker in the file: a cardinality is
    # what sees the second occurrence.  The remedy is to bind the probe to a name.
    markers_in_text = len(LEAN_PROBE_MARKER.findall(text))
    markers_located = sum(len(LEAN_PROBE_MARKER.findall(by_id[i].value))
                          for i in named)
    if markers_located < markers_in_text:
        raise UnreadableProbe(
            f"{path} carries {markers_in_text} Lean import marker(s) "
            f"(`import Lean` / `import SeLe4n`) and this scanner located only "
            f"{markers_located} of them in a string constant.  A probe it cannot "
            f"locate is one whose `ConstantInfo` matches it cannot count; assign "
            f"the probe to a name, or the body-bearing discipline is unchecked "
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
        "Three questions, none of them the body one, and the census's own domain "
        "test reads `bodyBearing`.  (1) Two fail-CLOSED theorem reporters: a pin "
        "entry that names a theorem, and a pin-check witness that is one, are each "
        "REPORTED as a defect rather than skipped.  (2) `isErasedConstant` asks "
        "whether a constant is a THEOREM -- Lean compiles no code for one, so the "
        "reachability walk records it as seen and does not expand it; that is "
        "`.thmInfo`'s third occurrence, and the predicate half is delegated to "
        "`ReplyStackWriteCensus.isPredicate` rather than re-spelled.  (3) "
        "`stateCarryingTypes` asks whether a constant is an INDUCTIVE and reads its "
        "CONSTRUCTORS' field types -- a question about a type's shape, for which a "
        "non-inductive is correctly skipped, since the eight constructors partition "
        "on that too.",
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
    "scripts/check_declaration_kind_askers.py::_FIXTURE_OWNER":
        "THIS GATE'S OWN FIXTURE for the owner, and a subject only since "
        "`v0.35.118`: it is Lean source with NO import at all, so the `^import "
        "Lean` marker never located it and the constructor signal does.  Its eight "
        "counts are `bodyBearing`'s own exhaustive match, copied -- which is the "
        "point, since a fixture that lost an arm would stop witnessing the one "
        "declaration allowed to answer yes.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_ROGUE":
        "THIS GATE'S OWN FIXTURE for the new-subject direction, a subject since "
        "`v0.35.118` for the same reason as the owner fixture: Lean with no "
        "import.  Its one `defnInfo` is what makes case (2) report a sixth asker, "
        "so a fixture that lost it would report nothing and pass.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_PROJECT_IMPORT_PROBE":
        "THIS GATE'S OWN FIXTURE for the reported defect: a probe importing only a "
        "PROJECT module, which the `^import Lean` marker skipped outright.  Its "
        "`defnInfo` is the match that must be COUNTED rather than skipped, so a "
        "fixture that lost it would pass with the hole reopened.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_PROJECT_SPLIT_PROBE":
        "THIS GATE'S OWN FIXTURE for the refusal direction on a project-importing "
        "probe -- the case the old marker could see NEITHER way, since it neither "
        "located the probe nor had a marker to refuse on.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_INLINE_PROBE":
        "THIS GATE'S OWN FIXTURE for the reported defect (`v0.35.124`): a probe "
        "passed INLINE, beside an assigned one.  Two counts, and both are "
        "load-bearing -- the `ctorInfo` is the assigned probe that used to suppress "
        "the refusal and the `opaqueInfo` is the inline one that was therefore "
        "neither read nor refused, so a fixture that lost either would stop "
        "witnessing the suppression.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_INLINE_PROSE":
        "THIS GATE'S OWN FIXTURE for the CONTROL that keeps the widening off prose: "
        "a docstring and a call argument naming constructors in exactly the "
        "positions the inline locator reads, and a third builds its text by "
        "CONCATENATION, which is the position the group branch reads.  Its five "
        "counts ARE the control -- they are what a locator admitting every string "
        "constant, or a group admitted on the constructor signal, would file as a "
        "probe -- so recording them is the measurement rather than the price.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_ASSEMBLED_BESIDE_ASSIGNED":
        "THIS GATE'S OWN FIXTURE for the reported defect's cardinality half: an "
        "ASSEMBLED probe beside an assigned one, which one located probe used to "
        "answer for.  Two counts because the file has two subjects, which is the "
        "whole claim.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_INLINE_ASSEMBLED":
        "THIS GATE'S OWN FIXTURE for the one shape with no name to take: an "
        "assembled probe passed inline, keyed by its enclosing declaration.  Its "
        "`opaqueInfo` is what case (13) reads back, so a fixture that lost it would "
        "assert nothing about the group branch's fallback key.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_UNLOCATABLE_MARKER_BESIDE_PROBE":
        "THIS GATE'S OWN FIXTURE for the marker-COUNT refusal: an unlocatable marker "
        "beside a probe that IS located, which is the only shape the superseded "
        "\"did we find anything\" reading passes.  Its `ctorInfo` belongs to the "
        "located probe, and it is what makes `found` non-empty -- the very condition "
        "the case turns on -- so a fixture that lost it would silently become the "
        "weaker witness it replaced.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_DOUBLE_BOUND_PROBE":
        "THIS GATE'S OWN FIXTURE for the one shape on which counting markers over "
        "the located CONSTANTS differs from counting them over the rows reported: a "
        "probe bound to two names, beside a marker nothing locates.  Its `quotInfo` "
        "is the located probe's, and the two names are what produce the surplus the "
        "case is about, so a fixture that dropped either would stop discriminating.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_NESTED_CONCATENATION":
        "THIS GATE'S OWN FIXTURE for the maximal-group rule: a probe whose "
        "concatenation nests, where reporting the inner expression as well would "
        "count the same subject twice.  Its `recInfo` is what case (16) reads back "
        "under ONE key, so a fixture that lost it would assert nothing.  Its "
        "sibling `_FIXTURE_ORDERED_FRAGMENTS` is deliberately NOT a subject: its "
        "constructor name is split across a `\"\"\" + \"\"\"` boundary, so the "
        "literal text of this file carries no match -- which is exactly the "
        "property case (15) is about, one level up.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_TWO_INLINE_ONE_SCOPE":
        "THIS GATE'S OWN FIXTURE for the second refusal: two probes binding no name "
        "in one scope, which would share a subject key.  The two counts are the two "
        "probes, and they must DIFFER -- a count moving between them under a shared "
        "key is precisely what the refusal exists to prevent.",
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
    "SeLe4n/Testing/KernelTransitionReachabilityCensus.lean": {
        "ctorInfo": 1, "inductInfo": 1, "thmInfo": 3,
    },
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
    # Located by the CONSTRUCTOR signal since `v0.35.118`: Lean source carrying no
    # import, which the marker alone could never see.
    "scripts/check_declaration_kind_askers.py::_FIXTURE_OWNER": {
        "axiomInfo": 1, "defnInfo": 1, "thmInfo": 1, "opaqueInfo": 1,
        "quotInfo": 1, "inductInfo": 1, "ctorInfo": 1, "recInfo": 1,
    },
    "scripts/check_declaration_kind_askers.py::_FIXTURE_ROGUE": {
        "defnInfo": 1,
    },
    "scripts/check_declaration_kind_askers.py::_FIXTURE_PROJECT_IMPORT_PROBE": {
        "defnInfo": 1,
    },
    "scripts/check_declaration_kind_askers.py::_FIXTURE_PROJECT_SPLIT_PROBE": {
        "defnInfo": 1,
    },
    # `v0.35.124`: the inline and assembled shapes, located since the probe domain
    # became every string constant rather than every assignment value.
    "scripts/check_declaration_kind_askers.py::_FIXTURE_INLINE_PROBE": {
        "ctorInfo": 1, "opaqueInfo": 1,
    },
    "scripts/check_declaration_kind_askers.py::_FIXTURE_INLINE_PROSE": {
        "ctorInfo": 1, "inductInfo": 1, "opaqueInfo": 1, "recInfo": 1,
        "thmInfo": 1,
    },
    "scripts/check_declaration_kind_askers.py::_FIXTURE_ASSEMBLED_BESIDE_ASSIGNED": {
        "ctorInfo": 1, "defnInfo": 1,
    },
    "scripts/check_declaration_kind_askers.py::_FIXTURE_INLINE_ASSEMBLED": {
        "opaqueInfo": 1,
    },
    "scripts/check_declaration_kind_askers.py::_FIXTURE_TWO_INLINE_ONE_SCOPE": {
        "defnInfo": 1, "opaqueInfo": 1,
    },
    "scripts/check_declaration_kind_askers.py::_FIXTURE_NESTED_CONCATENATION": {
        "recInfo": 1,
    },
    "scripts/check_declaration_kind_askers.py::_FIXTURE_DOUBLE_BOUND_PROBE": {
        "quotInfo": 1,
    },
    "scripts/check_declaration_kind_askers.py::_FIXTURE_UNLOCATABLE_MARKER_BESIDE_PROBE": {
        "ctorInfo": 1,
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

#: THE REPORTED CASE (`v0.35.118`): a probe that imports only a PROJECT module.
#: `SeLe4n.Testing.DeclarationKind` exposes `ConstantInfo` transitively -- every
#: project module imports Lean -- so this decides the body question exactly as a
#: `Lean`-importing probe does, and under the `^import Lean` marker it was SKIPPED:
#: `embedded_lean` returned nothing, no count moved, and the reconciliation went on
#: reporting the tree clean.  Located now by either widened signal, the import root
#: or the constructor name.
_FIXTURE_PROJECT_IMPORT_PROBE = '''\
PROBE = """
import SeLe4n.Testing.DeclarationKind

private def sneaky (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ => true
  | _ => false
"""
'''

#: ...and its ASSEMBLED twin, which is why the refusal had to widen with the
#: locator.  `_FIXTURE_SPLIT_PROBE` below carries `import Lean.Elab.Command` as
#: well, so the old marker refused it; this one imports the project root alone, so
#: the old marker saw nothing to refuse and the probe was invisible in both
#: directions at once.
_FIXTURE_PROJECT_SPLIT_PROBE = '''\
PROBE = """
import SeLe4n.Testing.DeclarationKind
""" + """
private def hidden (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ => true
  | _ => false
"""
'''

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


#: THE REPORTED CASE (PR #897, `v0.35.124`): a probe passed INLINE, beside an
#: assigned one.  The walker considered only `Assign`/`AnnAssign` nodes, so this
#: one was never located -- and the assigned probe made `found` non-empty, which
#: suppressed the refusal.  So an inline probe could re-decide the body-bearing
#: question without changing the captured inventory or failing Tier 0: a domain
#: miss, silent by construction, and invisible in BOTH directions at once.
#:
#: The assigned probe beside it is the whole point.  Every earlier case in this
#: file has at most one probe per fixture, so none of them exercises the
#: suppression, which is why four review rounds and a widening did not find this.
_FIXTURE_INLINE_PROBE = '''\
PROBE = """
import SeLe4n
import Lean.Elab.Command

private def declared (ci : ConstantInfo) : Bool :=
  match ci with
  | .ctorInfo _ => true
  | _ => false
"""

run_probe(PROBE)
run_probe("""
import SeLe4n
import Lean.Elab.Command

private def inline (ci : ConstantInfo) : Bool :=
  match ci with
  | .opaqueInfo _ => true
  | _ => false
""")
'''

#: ...and the CONTROLS that keep the widening from swallowing prose, one per
#: admitted shape.  A docstring and a call argument name constructors in the
#: non-assignment position the bare-constant branch reads; the third `note` builds
#: its text by CONCATENATION, which is the position the group branch reads.  None is
#: a probe.  The signal for both branches is the IMPORT MARKER alone for exactly this
#: reason -- a constructor name is what prose explaining a retired reading carries,
#: and an assembled diagnostic is an everyday Python idiom -- so the widened
#: `_probe_signal` would file this file's own documentation as a probe.  Measured on
#: the tracked tree: zero concatenations carry a constructor name today, so this
#: control is planted rather than drawn from a live one, which is why it has to be
#: written down rather than waited for.
_FIXTURE_INLINE_PROSE = '''\
"""A gate whose docstring mentions `.opaqueInfo` and `.recInfo`.

It is a non-assignment string constant in exactly the position the inline
locator reads, and it carries no Lean import, so it is prose and not a probe.
"""

PROBE = """
import SeLe4n

private def declared (ci : ConstantInfo) : Bool :=
  match ci with
  | .ctorInfo _ => true
  | _ => false
"""

note("this mentions `.thmInfo` and is still prose")
note("a retired reading matched " + "`.inductInfo`" + " and is gone")
'''

#: A file with an assigned probe AND an assembled one.  The refusal used to ask
#: "did we find anything", which one located probe answers for the whole file --
#: so the assembled probe beside it was skipped.  Asked as a COUNT of markers, the
#: second one is visible: a cardinality is what sees the second occurrence.
_FIXTURE_ASSEMBLED_BESIDE_ASSIGNED = '''\
PROBE = """
import SeLe4n

private def declared (ci : ConstantInfo) : Bool :=
  match ci with
  | .ctorInfo _ => true
  | _ => false
"""

HIDDEN = """
import SeLe4n
""" + """
private def hidden (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ => true
  | _ => false
"""
'''

#: A Lean import marker OUTSIDE every string constant, BESIDE a probe the scanner
#: does locate.  The `beside` is what makes it decisive: the refusal asks whether the
#: located constants account for every marker, and a fixture whose only marker is the
#: unlocatable one is refused by the superseded "did we find anything" reading too.
#: Here `found` is non-empty and one marker is still unaccounted for, which exactly
#: one of the two readings catches.
#:
#: Synthetic by necessity: the realistic assembled probes (cases 6, 8, 15 and 16) are
#: now READ, and a probe whose text never appears literally in the source is outside
#: any scanner.  The bare marker is a Python `import` statement, which parses and
#: imports nothing Lean -- that is the point: the scanner sees a marker it cannot
#: attribute to a probe, and says so instead of reading past it.
_FIXTURE_UNLOCATABLE_MARKER_BESIDE_PROBE = '''\
import SeLe4n.Testing

PROBE = """
import SeLe4n

private def declared (ci : ConstantInfo) : Bool :=
  match ci with
  | .ctorInfo _ => true
  | _ => false
"""
'''


#: An ASSEMBLED probe that binds NO name, inside a function: the one shape that
#: reaches the group branch with no assignment target to take its name from, so the
#: key is the enclosing declaration.  It is also the only fixture that exercises the
#: scope tracking THROUGH a group -- every other inline case is a bare constant --
#: which matters because the group's scope is read off its first fragment and a walk
#: that lost the enclosing `def` would report `<module>` with nothing to notice it.
_FIXTURE_INLINE_ASSEMBLED = '''\
def build() -> None:
    run_probe("""
import SeLe4n
""" + """
private def nested (ci : ConstantInfo) : Bool :=
  match ci with
  | .opaqueInfo _ => true
  | _ => false
""")
'''

#: TWO probes that bind no name, in ONE scope.  They would share a single subject
#: key, and a key two subjects share cannot see a count moving between them -- which
#: is the defect the per-(subject, constructor) inventory exists to refuse, so the
#: scanner refuses the file instead of bucketing them.
_FIXTURE_TWO_INLINE_ONE_SCOPE = '''\
run_probe("""
import SeLe4n

private def first (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ => true
  | _ => false
""")

run_probe("""
import SeLe4n

private def second (ci : ConstantInfo) : Bool :=
  match ci with
  | .opaqueInfo _ => true
  | _ => false
""")
'''

#: A probe assembled from THREE fragments with a constructor name split across the
#: last boundary.  `ast.walk` is breadth-first and `A + B + C` parses as
#: `BinOp(BinOp(A, B), C)`, so it yields `C, A, B`: a join in walk order both
#: destroys `.quotInfo` here and could invent a match elsewhere, and only a join in
#: SOURCE order reads what the expression builds.  Two fragments cannot witness this
#: -- a single `BinOp`'s operands come out in order -- which is why the fixture the
#: reported defect came with could not have caught it.
_FIXTURE_ORDERED_FRAGMENTS = '''\
PROBE = """
import SeLe4n
""" + """
private def ordered (ci : ConstantInfo) : Bool :=
  match ci with
  | .quot""" + """Info _ => true
  | _ => false
"""
'''

#: ...and one whose concatenation NESTS.  Only the outermost expression is a
#: subject: the inner `BinOp` builds a part of the same string, so reporting it as
#: well would count its fragments twice -- once under the name the assignment binds
#: and once under the enclosing scope -- which is a subject appearing twice rather
#: than a probe appearing twice.  The `.recInfo` sits wholly inside the middle
#: fragment, so this fixture is decisive for the nesting and silent about the sort,
#: and `_FIXTURE_ORDERED_FRAGMENTS` is the other way round.
_FIXTURE_NESTED_CONCATENATION = '''\
PROBE = """
import SeLe4n
""" + """
private def nested (ci : ConstantInfo) : Bool :=
  match ci with
  | .recInfo _ => true
""" + """  | _ => false
"""
'''

#: One probe bound to TWO names, beside a marker the scanner cannot locate.  The
#: refusal counts markers in LOCATED TEXT, and this shape is the only one on which
#: that differs from counting the rows reported: the shared constant is reported
#: twice, so a row-sum reads two markers accounted for against the two in the file
#: and the unlocatable one is MASKED.  A surplus from double-reporting must not pay
#: for a marker nobody read.
_FIXTURE_DOUBLE_BOUND_PROBE = '''\
import SeLe4n.Testing

PROBE = ALIAS = """
import SeLe4n

private def doubled (ci : ConstantInfo) : Bool :=
  match ci with
  | .quotInfo _ => true
  | _ => false
"""
'''

def _git(repo: str, *args: str) -> None:
    subprocess.run(["git", *args], cwd=repo, check=True,
                   capture_output=True, text=True)


def _capture_fixture(root: str) -> dict[str, dict[str, int]]:
    """`capture`, with a REFUSAL reported in this gate's voice rather than raised.

    A case that asks what the capture contains has failed if the scan refused the
    fixture -- but a traceback is not a verdict, and an exception escaping one case
    skips every case after it, so one mutation could mask another.  `violations`
    already renders a refusal as a problem string for the same reason; this is the
    same treatment for the direct reads.  The empty capture returned here fails every
    assertion a case makes of it, so the refusal cannot read as a pass.
    """
    try:
        return capture(root)
    except UnreadableProbe as exc:
        print("FAIL: --self-test — the scan REFUSED a fixture a case expected to "
              f"read: {exc}")
        return {}


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
    """Every case, in order, stopping at the FIRST one that fails.

    Stated because it changes how a mutation run is read: a revert that breaks
    several cases is reported by the earliest of them, so attributing a mutation to
    the property it broke means reverting one relation at a time.  The alternative
    -- collecting every failure -- would need each case to be a closure, and a case
    that keeps going past its own failed assertion can crash on the next line; with
    one relation reverted per run the earliest case IS the attribution.
    """
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
        got = _capture_fixture(root)
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

    # (6) A probe assembled by CONCATENATION is READ -- as ONE string, named after
    #     the target it is bound to.  Until `v0.35.124` it was refused instead,
    #     because the locator read only assignment *values* and a `BinOp` is not a
    #     string constant, so the whole file was unreadable.  Two things are asserted
    #     and the second is the sharper one.  The probe is reassembled in SOURCE
    #     order rather than scanned fragment by fragment, because a constructor name
    #     split across a fragment boundary belongs to neither half and `ast.walk` is
    #     breadth-first (`"a" + "b" + "c"` yields `c, a, b`).  And the subject is
    #     `::PROBE`, not `::<inline in <module>>`: a probe bound to a name is bound
    #     to it whether the right-hand side is one literal or three, and keying the
    #     assembled one by its scope would collapse two assembled probes in one
    #     module into ONE subject, where the counts add and a count moving between
    #     them is invisible -- the cardinality-for-a-set defect inside the widening
    #     that closes it.  Reading it is strictly stronger than refusing it: the gate
    #     now COUNTS what it could previously only decline.
    with tempfile.TemporaryDirectory() as root:
        split = "scripts/split_gate.py"
        _fixture(root, {**base, split: _FIXTURE_SPLIT_PROBE})
        got = _capture_fixture(root)
        fragments = {k: v for k, v in got.items() if k.startswith(split)}
        if fragments != {split + "::PROBE": {"defnInfo": 1}}:
            print("FAIL: --self-test — an assembled probe was not read as one")
            print(f"      string under its own name: {fragments}.  The expression")
            print("      builds one string and the assignment binds one name, so")
            print("      the subject is the name and the text is the join.")
            return 1
        problems = violations(root, base_pin, base_reasons)
        if not any(split in p and "not a recorded asker" in p for p in problems):
            print("FAIL: --self-test — the assembled probe was read and not")
            print(f"      reported: {problems}.")
            return 1

    # (7) A probe importing only a PROJECT module is LOCATED (`v0.35.118`).
    #     This is the reported defect, and it is token-preserving against case
    #     (2): the same `.defnInfo` match, reached through `import
    #     SeLe4n.Testing.DeclarationKind` instead of `import Lean`.  Under the
    #     `^import Lean` marker `embedded_lean` returned nothing for it, so the
    #     probe was never examined, no count moved, and the reconciliation went on
    #     reporting the tree clean -- a domain miss, which is silent by
    #     construction and therefore cannot be found by reading a failure.
    with tempfile.TemporaryDirectory() as root:
        project = "scripts/project_gate.py"
        _fixture(root, {**base, project: _FIXTURE_PROJECT_IMPORT_PROBE})
        problems = violations(root, base_pin, base_reasons)
        if not any(project + "::PROBE" in p and "not a recorded asker" in p
                   for p in problems):
            print("FAIL: --self-test — a probe importing only a PROJECT module was")
            print(f"      not located: {problems}.  Every project module imports")
            print("      Lean, so such a probe decides the body-bearing question")
            print("      exactly as a `Lean`-importing one does; locating probes by")
            print("      one import spelling is a domain written as a marker.")
            return 1

    # (8) ...and its ASSEMBLED twin, importing the PROJECT root alone, is read the
    #     same way.  Before `v0.35.118` the `^import Lean` marker neither located
    #     it nor had anything to refuse on -- invisible in both directions at once;
    #     before `v0.35.124` it was refused; now it is read.  Kept as a separate
    #     case because the import spelling is the axis `v0.35.118` widened, and a
    #     regression there would be silent in this one and not in case (6).
    with tempfile.TemporaryDirectory() as root:
        psplit = "scripts/project_split_gate.py"
        _fixture(root, {**base, psplit: _FIXTURE_PROJECT_SPLIT_PROBE})
        problems = violations(root, base_pin, base_reasons)
        if not any(psplit in p and "not a recorded asker" in p for p in problems):
            print("FAIL: --self-test — an ASSEMBLED probe importing only a PROJECT")
            print(f"      module was not read: {problems}.")
            return 1

    # (8b) A marker the located constants do not account for is REFUSED, BESIDE a
    #      probe that is located.  The `beside` is the whole of the case: the refusal
    #      asks whether the located constants account for every marker, and a fixture
    #      whose only marker is the unlocatable one is refused by the superseded "did
    #      we find anything" reading as well -- so it would pass with the cardinality
    #      reverted, which is the reading one located probe answered for a whole file.
    #      Here `found` is non-empty and a marker is still unaccounted for, which
    #      exactly one of the two readings catches.
    #
    #      The witness is SYNTHETIC on purpose: with every string constant in the
    #      domain there is no realistic probe shape that reaches this branch, so a
    #      fixture is the only way to show it decides -- the treatment
    #      `BootEntryContract` and `StoreReadClassificationCensus` already carry for
    #      the same reason.  What it cannot catch is stated in `embedded_lean`.
    with tempfile.TemporaryDirectory() as root:
        bare = "scripts/bare_marker_gate.py"
        _fixture(root, {**base,
                        bare: _FIXTURE_UNLOCATABLE_MARKER_BESIDE_PROBE})
        problems = violations(root, base_pin, base_reasons)
        if not any(bare in p and "located only" in p for p in problems):
            print("FAIL: --self-test — a Lean import marker outside every string")
            print(f"      constant was not refused: {problems}.  'Could not read")
            print("      it' and 'read it and it is clean' must never produce the")
            print("      same verdict.")
            return 1

    # (10) An INLINE probe, BESIDE an assigned one, is located (PR #897).  The
    #      walker read only `Assign`/`AnnAssign` nodes, and the assigned probe
    #      made `found` non-empty, which suppressed the refusal -- so this probe
    #      was invisible in both directions at once and could re-decide the
    #      body-bearing question with the inventory unchanged and Tier 0 green.
    #      Every earlier case here has at most one probe per fixture, which is why
    #      none of them exercises the suppression.
    #
    #      Measured on this fixture with BOTH halves of the defect restored -- the
    #      locator reading only assignment values and the refusal asking "did we
    #      find anything" -- the capture is `{::PROBE: {ctorInfo: 1}}` and nothing
    #      is refused: the inline probe's `.opaqueInfo` appears in no row and in no
    #      diagnostic.  With either half alone the file is REFUSED instead, by the
    #      marker count, so only the pair reproduces the reported silence, and this
    #      case is what reads the row back.
    with tempfile.TemporaryDirectory() as root:
        inline = "scripts/inline_gate.py"
        _fixture(root, {**base, inline: _FIXTURE_INLINE_PROBE})
        got = _capture_fixture(root)
        keys = [k for k in got if k.startswith(inline)]
        if not any("<inline in <module>>" in k for k in keys):
            print("FAIL: --self-test — an INLINE probe was not located:")
            print(f"      {sorted(keys)}.  A probe passed as an argument decides")
            print("      the body question exactly as an assigned one does, and a")
            print("      walker that reads only assignments is a domain written as")
            print("      a node kind.")
            return 1
        problems = violations(root, base_pin, base_reasons)
        if not any("<inline in <module>>" in p and "not a recorded asker" in p
                   for p in problems):
            print("FAIL: --self-test — the INLINE probe was located and not")
            print(f"      reported: {problems}.")
            return 1

    # (11) ...and a docstring in the SAME non-assignment position is NOT a probe.
    #      The control for (10): without it, the widening is satisfied by a locator
    #      that files every string constant, which would make this file's own
    #      documentation an asker and force every subject to stop explaining what
    #      it retired.  The inline signal is therefore the IMPORT MARKER alone.
    with tempfile.TemporaryDirectory() as root:
        prose = "scripts/prose_gate.py"
        _fixture(root, {**base, prose: _FIXTURE_INLINE_PROSE})
        got = _capture_fixture(root)
        inline_keys = [k for k in got if k.startswith(prose) and "<inline" in k]
        if inline_keys:
            print("FAIL: --self-test — prose in a non-assignment string constant")
            print(f"      was filed as a probe: {inline_keys}.  A constructor name")
            print("      is what prose explaining a retired reading carries; only")
            print("      the import entails an embedded probe.")
            return 1
        expected = {prose + "::PROBE": {"ctorInfo": 1}}
        if {k: v for k, v in got.items() if k.startswith(prose)} != expected:
            print("FAIL: --self-test — the prose fixture's capture is")
            print(f"      {[(k, v) for k, v in got.items() if k.startswith(prose)]},")
            print(f"      expected {expected}.")
            return 1

    # (12) An ASSEMBLED probe beside an ASSIGNED one yields TWO subjects, each
    #      named, each counted.  This is the reported defect's own shape: the
    #      refusal used to ask "did we find anything", which one located probe
    #      answers for the whole file, so the assembled one was neither read nor
    #      refused -- invisible in both directions at once, free to re-decide the
    #      body-bearing question with the inventory unchanged and Tier 0 green.
    #      Cases (6) and (8) each hold a single probe, so neither exercises the
    #      suppression; what makes this one decisive is the CARDINALITY, two
    #      subjects out of one file, which is exactly what the superseded gate
    #      could not report.
    with tempfile.TemporaryDirectory() as root:
        both = "scripts/both_gate.py"
        _fixture(root, {**base, both: _FIXTURE_ASSEMBLED_BESIDE_ASSIGNED})
        got = {k: v for k, v in _capture_fixture(root).items() if k.startswith(both)}
        expected = {both + "::PROBE": {"ctorInfo": 1},
                    both + "::HIDDEN": {"defnInfo": 1}}
        if got != expected:
            print("FAIL: --self-test — an ASSEMBLED probe beside an assigned one")
            print(f"      did not yield two named subjects: {got}, expected")
            print(f"      {expected}.  One located probe used to answer the")
            print("      question for every marker in the file, which is a")
            print("      cardinality standing in for a set.")
            return 1
        problems = violations(root, base_pin, base_reasons)
        for key in expected:
            if not any(key in p and "not a recorded asker" in p for p in problems):
                print(f"FAIL: --self-test — {key} was located and not reported:")
                print(f"      {problems}.")
                return 1

    # (13) An ASSEMBLED probe that binds NO name is read under its ENCLOSING
    #      DECLARATION.  The one shape with no assignment target to take a name
    #      from, so it is the only witness for the group branch's fallback key --
    #      and the only one that exercises the scope tracking THROUGH a group,
    #      since the group's scope is read off its first fragment and a walk that
    #      lost the enclosing `def` would answer `<module>` with nothing to notice.
    with tempfile.TemporaryDirectory() as root:
        ia = "scripts/inline_assembled_gate.py"
        _fixture(root, {**base, ia: _FIXTURE_INLINE_ASSEMBLED})
        got = {k: v for k, v in _capture_fixture(root).items() if k.startswith(ia)}
        expected = {ia + "::<inline in build>": {"opaqueInfo": 1}}
        if got != expected:
            print("FAIL: --self-test — an unnamed ASSEMBLED probe was not read")
            print(f"      under its enclosing declaration: {got}, expected")
            print(f"      {expected}.")
            return 1

    # (14) ...and TWO probes that bind no name in ONE scope are REFUSED rather than
    #      bucketed.  A subject key two probes share cannot see a count moving
    #      between them -- the first loses a `.defnInfo`, the second gains one, the
    #      total is unchanged and the reconciliation says nothing -- which is the
    #      cardinality-for-a-set defect this inventory's shape exists to refuse, so
    #      accumulating them would reopen it one level down.  An ordinal key would
    #      churn when an earlier probe is deleted, so the answer is the one this
    #      project gives wherever a scanner cannot decide: refuse, name the scope,
    #      and state the remedy.
    with tempfile.TemporaryDirectory() as root:
        two = "scripts/two_inline_gate.py"
        _fixture(root, {**base, two: _FIXTURE_TWO_INLINE_ONE_SCOPE})
        problems = violations(root, base_pin, base_reasons)
        if not any(two in p and "share one subject key" in p for p in problems):
            print("FAIL: --self-test — two probes binding no name in one scope were")
            print(f"      not refused: {problems}.  Bucketing two subjects under")
            print("      one key hides a count moving between them.")
            return 1

    # (15) A three-fragment probe is reassembled in SOURCE order.  `ast.walk` is
    #      breadth-first and `A + B + C` parses as `BinOp(BinOp(A, B), C)`, so it
    #      yields `C, A, B`; here the constructor name straddles the last boundary,
    #      so a join in walk order DESTROYS the match and the subject drops out of
    #      the capture entirely.  Two fragments cannot witness this -- one `BinOp`'s
    #      operands come out in order -- so the fixture the reported defect arrived
    #      with could not have caught it, which is why this case exists rather than
    #      an assertion in a comment.
    with tempfile.TemporaryDirectory() as root:
        order = "scripts/ordered_gate.py"
        _fixture(root, {**base, order: _FIXTURE_ORDERED_FRAGMENTS})
        got = {k: v for k, v in _capture_fixture(root).items() if k.startswith(order)}
        expected = {order + "::PROBE": {"quotInfo": 1}}
        if got != expected:
            print("FAIL: --self-test — a three-fragment probe was not reassembled")
            print(f"      in source order: {got}, expected {expected}.  A join in")
            print("      `ast.walk` order can destroy a constructor name that")
            print("      straddles a fragment boundary, and invent one elsewhere.")
            return 1

    # (16) ...and only the OUTERMOST concatenation is a subject.  The inner
    #      expression builds a part of the same string, so reporting it as well
    #      would count one subject twice -- once under the name the assignment binds
    #      and once under the enclosing scope -- which is a SUBJECT appearing twice,
    #      not a probe.  The exact-equality assertion is the whole check: a second
    #      key here is the defect.
    with tempfile.TemporaryDirectory() as root:
        nest = "scripts/nested_gate.py"
        _fixture(root, {**base, nest: _FIXTURE_NESTED_CONCATENATION})
        got = {k: v for k, v in _capture_fixture(root).items() if k.startswith(nest)}
        expected = {nest + "::PROBE": {"recInfo": 1}}
        if got != expected:
            print("FAIL: --self-test — a NESTED concatenation was reported as a")
            print(f"      second subject: {got}, expected {expected}.  Only the")
            print("      outermost expression builds the probe; an inner one is a")
            print("      part of it.")
            return 1

    # (17) A marker the scanner cannot locate is refused even when a shared constant
    #      is REPORTED TWICE.  `PROBE = ALIAS = <probe>` yields two rows over one
    #      constant, so summing markers over the ROWS reads two accounted for against
    #      the two in the file and the unlocatable one is masked -- a surplus from
    #      double-reporting paying for a marker nobody read.  Counting over the
    #      located CONSTANTS is the fix, and this is the only shape on which the two
    #      readings differ, which is why the case exists rather than a comment.
    with tempfile.TemporaryDirectory() as root:
        dbl = "scripts/double_bound_gate.py"
        _fixture(root, {**base, dbl: _FIXTURE_DOUBLE_BOUND_PROBE})
        problems = violations(root, base_pin, base_reasons)
        if not any(dbl in p and "located only" in p for p in problems):
            print("FAIL: --self-test — an unlocatable marker was masked by a probe")
            print(f"      bound to two names: {problems}.  The count is over the")
            print("      located constants, not over the rows reported.")
            return 1

    # (9) The real tree, which is the check the tier runs.
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
          f"table orphaned, an assembled probe READ as one string under its own "
          f"name, one importing only a project module, an INLINE probe beside an "
          f"assigned one, an assembled probe beside an assigned one as TWO named "
          f"subjects, an unnamed assembled probe under its enclosing declaration, "
          f"a marker outside every constant refused, two unnamed probes in one "
          f"scope refused, a three-fragment probe reassembled in SOURCE order, a "
          f"NESTED concatenation counted once and an unlocatable marker unmasked "
          f"by a probe bound to two names are each reported, while a docstring in "
          f"the same non-assignment position is not; the live tree is clean at "
          f"{len(found)} subject(s).")
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
