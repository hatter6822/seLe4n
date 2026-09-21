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


#: The FILE-level prefilter, which must be strictly WIDER than the value-level
#: signal -- `v0.35.132` (PR #897 review).  `_probe_signal` reads a probe's own
#: text, where the import really does start a line.  Applied to the RAW SOURCE it
#: asks a different question, and gets it wrong for one of the commonest spellings
#: there is: `PROBE = """import SeLe4n ...` opens the literal on the assignment
#: line, so no line in the file begins with the import, and a template that fills
#: `.@KIND@Info` spells no complete constructor either.  Both signals are false,
#: the early return in `embedded_lean` fires, and the file is never parsed -- a
#: body-kind asker outside this inventory with the gate reporting the tree clean.
#: That is the silent domain defect this gate exists to close, in the gate itself.
#:
#: So the prefilter drops the anchor.  Being strictly wider, it can never skip a
#: file the anchored reading would have admitted, and the anchored reading is kept
#: for the two questions that genuinely are about a line start: whether a LOCATED
#: constant is probe text, and whether the file's markers are all accounted for.
_PROBE_PREFILTER_MARKER = re.compile(r"import\s+(?:Lean|SeLe4n)\b")


def _probe_prefilter(text: str) -> bool:
    """Could this FILE embed a probe?  Strictly wider than `_probe_signal`."""
    return bool(_PROBE_PREFILTER_MARKER.search(text)
                or _ANY_CONSTRUCTOR.search(text))


class UnreadableProbe(Exception):
    """A file embeds Lean this gate cannot locate as a string constant."""


def _tracked(repo: str, *globs: str) -> list[str]:
    """Tracked paths, so a new subject is in scope the day it is committed."""
    out = subprocess.run(["git", "ls-files", "-z", *globs], cwd=repo,
                         capture_output=True, text=True, check=True).stdout
    return [p for p in out.split("\0") if p]


def _string_constants(tree: ast.AST) -> list[tuple[str, ast.Constant]]:
    """`(scope, node)` for every string constant, with its enclosing declaration.

    The scope is the enclosing `def`/`class` path, or `<module>`: that is what a
    reader needs in order to find the probe, and unlike a line number it survives
    reformatting.  `ast` carries no parent links, so the walk is explicit.

    **Qualified, not nearest** (`v0.35.127`).  A bare declaration name is a
    *resemblance*: two methods called `probe` in two classes, or a helper defined
    inside two functions, share it, and this scope is what identifies a subject --
    both in the `<inline in …>` key and, since this cut, in a named probe's key.  A
    key two subjects share cannot see a count moving between them, which is the
    defect the whole per-subject inventory is shaped against.  Costs nothing on the
    tracked tree, where every located probe is at module scope.
    """
    out: list[tuple[str, ast.Constant]] = []

    def walk(node: ast.AST, scope: str) -> None:
        for child in ast.iter_child_nodes(node):
            inner = scope
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                                  ast.ClassDef)):
                inner = (child.name if scope == "<module>"
                         else f"{scope}.{child.name}")
            if isinstance(child, ast.Constant) and isinstance(child.value, str):
                out.append((scope, child))
            walk(child, inner)

    walk(tree, "<module>")
    return out


def _qualified(scope: str, name: str) -> str:
    """A named probe's subject key: the binding, qualified by where it is bound.

    `v0.35.127` (PR #897 review).  The key was the bare target name, so two probes
    assigning `PROBE` in two functions shared one subject: change one from
    `.defnInfo` to `.opaqueInfo` and the other the inverse, and every count in the
    inventory is unchanged while **both** askers have re-decided the body-bearing
    question.  That is the cardinality-for-a-set defect this inventory exists against
    -- and `v0.35.124` had already refused it for probes that bind NO name, one branch
    over, under a comment stating the reason.  *A fix applied at one site and not its
    sibling.*

    A module-level name is its own qualification, so every key on the tracked tree
    (where all 17 located probes are at module scope) is byte-identical to before and
    the pin does not move.
    """
    return name if scope == "<module>" else f"{scope}.{name}"


#: The character standing for a fragment of an assembled string this scanner cannot
#: read.  NUL, for two reasons that are both about the question rather than about
#: convenience: it is not a word character, so it can never sit *inside* a
#: `\b`-bounded constructor match and therefore never manufactures one; and a source
#: literal that contained one would make a hole indistinguishable from determined
#: text, which `_reconstruct_holed` refuses outright rather than reading past.
_HOLE = "\x00"

#: The two substitution mini-languages, as HOLE producers rather than as
#: interpreters.  A `str.format` field and a `%`-conversion are each replaced by a
#: hole wherever they occur in a determined template, so the scanner never has to
#: decide which argument lands where -- *a parser for a language you are not parsing
#: is a list of the spellings you have seen*, and the position of the hole is the
#: only thing the constructor question needs.
_FORMAT_FIELD = re.compile(r"\{[^{}]*\}")
_PERCENT_FIELD = re.compile(
    r"%(?:\([^()]*\))?[-+ #0]*(?:\*|[0-9]+)?(?:\.(?:\*|[0-9]+))?[hlL]?[a-zA-Z%]")


#: What each refusal reason means, in the words a maintainer needs to act on it.
#: Three reasons and not one, because they call for different remedies: text the
#: scanner cannot see at all, a transform it cannot model, and a hole written against
#: a constructor spelling.  A single message would name the wrong fix for two of them.
_REFUSAL_REASONS = {
    "unreadable": "a probe literal is assembled by a `.format`, a `%`, an "
                  "interpolating f-string or another string method",
    "form": "a transform this scanner does not model is applied to determined "
            "probe text, so its result is not that text with substitutions",
    "splice": "unread text is substituted into a located probe template at a "
              "position where the template has written part of a `ConstantInfo` "
              "constructor against it, so the constructor the probe decides is "
              "not in any located text",
    "builder": "a probe-signalling literal is handed to a plain-name call whose "
               "RESULT the program uses, so the call builds the probe and the "
               "located literal is not the text it runs",
    "concat": "the probe's Lean source is not ONE text this scanner has read: "
              "unread text is concatenated, interpolated or joined onto determined "
              "probe text rather than substituted into it, so the fragment may "
              "spell a whole `ConstantInfo` constructor and no located text "
              "carries it",
}


def _module_string_bindings(tree: ast.AST) -> dict[str, str]:
    """Names this module binds ONCE, anywhere, to a string literal.

    A named template is reached through its name, so a scanner that cannot resolve
    the name cannot see the text the substitution is applied to -- which is the whole
    of the `v0.35.129` defect.  Resolution is a relation and *a name is not a
    definition*, so it is fail-closed at both ends: a name bound **more than once**
    resolves to nothing (the two bindings are two texts and no occurrence says which
    is live), and so does a name bound to anything but a plain string literal.
    Bindings are collected at every scope and keyed by the bare name, which
    over-approximates the collision set -- a module-level `PROBE` and a local `PROBE`
    in one function count as two bindings and neither resolves -- and that direction
    is the safe one: an unresolved template is a refusal, a wrongly-resolved one is a
    count over text the program never builds.
    """
    return {n: t[0] for n, t in _name_bindings(tree).items()
            if len(t) == 1 and t[0] is not None}


def _name_bindings(tree: ast.AST) -> dict[str, list[str | None]]:
    """Every name binding in the module, as the literal text bound or `None`.

    One walk, because "which text does this name denote" and "is that answer
    ambiguous" are one question and answering them separately is how two readings
    of one fact drift apart.
    """
    seen: dict[str, list[str | None]] = {}
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign):
            targets, value = list(node.targets), node.value
        elif isinstance(node, (ast.AnnAssign, ast.NamedExpr)):
            targets, value = [node.target], node.value
        elif isinstance(node, ast.AugAssign):
            # `X += "..."` binds X to a concatenation this scanner has not evaluated,
            # so it is recorded as a binding with no text: the name then resolves to
            # nothing, which is the direction that refuses rather than misreads.
            targets, value = [node.target], None
        else:
            continue
        text = (value.value if isinstance(value, ast.Constant)
                and isinstance(value.value, str) else None)
        for target in targets:
            if not isinstance(target, ast.Name):
                continue
            seen.setdefault(target.id, []).append(text)
    return seen


def _ambiguous_probe_bindings(tree: ast.AST) -> list[str]:
    """Names bound more than once, at least one binding being probe text.

    The fail-closed half of `_module_string_bindings`, and the residue that made it
    necessary: an unresolvable name is not a refusal by itself -- most names in a
    Python file are not templates -- but a name that denotes PROBE text at one
    binding and something else at another cannot be resolved, so a substitution
    applied to it is read as applying to nothing and the splice refusal never sees
    the template.  The defect walks around the fix by binding the name twice.

    Named here and not folded into the duplicate-SUBJECT-KEY refusal below, because
    the two questions differ: that one is about two probes whose *counts would add*
    under one key, and fires only when both are located; this one is about which text
    a name DENOTES, and fires when a second binding hides a template from resolution
    even though the two probes have distinct keys.

    It is conditioned on an assembly REACHING THROUGH the name, and that condition is
    the whole of its precision rather than an economy.  Two probes bound to one local
    name in two scopes are two perfectly good subjects under two keys -- which is what
    `v0.35.127` established and what this gate's own case (22) pins -- and nothing is
    hidden by the ambiguity until something substitutes into one of them.  So the
    refusal asks both halves: the name is ambiguous, AND a string assembly reads it.
    The reach is asked over the whole module rather than per scope, which
    over-approximates and is the direction that refuses rather than misreads.
    Measured: zero such names on the tracked tree, so it is planted today, and the
    remedy is the same one-line rename.
    """
    reached = {n.id for shape in _string_assembly_shapes(tree)
               for n in ast.walk(shape) if isinstance(n, ast.Name)}
    return sorted(name for name, texts in _name_bindings(tree).items()
                  if name in reached and len(texts) > 1
                  and any(t is not None and LEAN_PROBE_MARKER.search(t)
                          for t in texts))


def _probe_alias_bindings(tree: ast.AST) -> list[tuple[str, str]]:
    """Aliases of a probe name that a string assembly then reads.

    `v0.35.132` (PR #897 review).  `_module_string_bindings` resolves a name to a
    string LITERAL, so an alias -- `ALIAS = PROBE` -- resolves to nothing at all,
    and a transform through it (`ALIAS.replace("@KIND@", kind)`) has an unreadable
    base: the `.replace` arm substitutes into a hole, the result IS a hole, it
    carries no import marker, and so neither the splice refusal nor the unreadable
    refusal ever sees it.  The template itself is still located -- with the
    constructors its *unsubstituted* text spells, which is none -- so the asker is
    invisible in both directions at once.  The same shape as the ambiguous-name
    defect beside it, reached by an extra hop instead of by a second binding.

    Resolving the hop is one remedy and REFUSING it is the other; this takes the
    refusal, because it is the canonical-spelling exit this project prefers
    wherever the subject is code it writes itself: a probe has ONE name, and
    deleting the alias is a one-line change.  Resolution would have to chase a
    chain whose depth nothing bounds, which is the partial-analysis shape that has
    already cost this file several rounds.

    The probe SET is closed transitively all the same, because the refusal has to
    see `B = A` over `A = PROBE`; what is deliberately not chased is the value.
    The closure terminates without a fuel bound: `probes` only grows and is
    bounded by the module's own names, so a bound would be the partial answer
    `v0.35.131` retired one file over.

    Conditioned on a string assembly READING the alias, for the reason the
    ambiguous-name refusal is: `SRC = PROBE` followed by `run(SRC)` hides nothing,
    the template being located and counted under its own name, and refusing it
    would reject correct code.  Measured: zero such aliases on the tracked tree,
    so both directions are planted today.
    """
    probes = {name for name, texts in _name_bindings(tree).items()
              if any(t is not None and LEAN_PROBE_MARKER.search(t) for t in texts)}
    aliases: list[tuple[str, str]] = []
    while True:
        grew = False
        for node in ast.walk(tree):
            if isinstance(node, ast.Assign):
                targets, value = list(node.targets), node.value
            elif isinstance(node, (ast.AnnAssign, ast.NamedExpr)):
                targets, value = [node.target], node.value
            else:
                continue
            if not isinstance(value, ast.Name) or value.id not in probes:
                continue
            for target in targets:
                if isinstance(target, ast.Name) and target.id not in probes:
                    probes.add(target.id)
                    aliases.append((target.id, value.id))
                    grew = True
        if not grew:
            break
    reached = {n.id for shape in _string_assembly_shapes(tree)
               for n in ast.walk(shape) if isinstance(n, ast.Name)}
    return sorted({(alias, source) for alias, source in aliases
                   if alias in reached})


def _reconstruct_holed(node: ast.AST, consts: dict[str, str]) -> str | None:
    """The text `node` builds, with every unreadable fragment as a single `_HOLE`.

    `v0.35.129` (PR #897 review).  `v0.35.127` asked *what value does this expression
    have* and answered "the string, or nothing"; the defect that survived it is the
    case where the answer is **almost** the string.  A named template holding
    `. @KIND@ Info` (without the spaces) is a LOCATED subject in its own right, so its
    import marker is accounted for and the fail-closed marker count is satisfied,
    while its constructor count is **zero** and the probe handed to Lean matches
    `.opaqueInfo`.  Invisible in both directions at once -- the same shape as the
    `.format` finding, at the one place the text is transformed rather than assembled.

    So the reconstruction is partial rather than all-or-nothing: determined text with
    holes where text this scanner cannot read enters it.  `_reconstruct` is then this
    function with "no holes" demanded, and the refusal asks the only question a hole
    leaves open -- whether the unread fragment could COMPLETE a constructor spelling
    the template has written half of.

    `None` is reserved for a form whose result is NOT describable as determined text
    with holes: an unrecognised string method or free function applied to determined
    probe text mangles it in a way no hole can stand for, and reading past it would
    count constructors over text the program never builds.  Where the same form is
    applied to text that is not a probe it is an ordinary value fragment, so it is a
    hole -- which is what keeps `", ".join(names)` (this tree's own idiom) readable
    while `PROBE.upper()` is refused.
    """
    if isinstance(node, ast.Constant):
        if not isinstance(node.value, str):
            return _HOLE
        return None if _HOLE in node.value else node.value
    if isinstance(node, ast.Name):
        return consts.get(node.id, _HOLE)
    if isinstance(node, ast.FormattedValue):
        return _HOLE
    if isinstance(node, ast.JoinedStr):
        parts: list[str] = []
        for value in node.values:
            piece = _reconstruct_holed(value, consts)
            if piece is None:
                return None
            parts.append(piece)
        return "".join(parts)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        left = _reconstruct_holed(node.left, consts)
        right = _reconstruct_holed(node.right, consts)
        return None if left is None or right is None else left + right
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mod):
        left = _reconstruct_holed(node.left, consts)
        return None if left is None else _PERCENT_FIELD.sub(_HOLE, left)
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
        base = _reconstruct_holed(node.func.value, consts)
        if base is None:
            return None
        if (node.func.attr == "join" and not node.keywords and len(node.args) == 1
                and isinstance(node.args[0], (ast.List, ast.Tuple))):
            pieces = [_reconstruct_holed(e, consts) for e in node.args[0].elts]
            if any(p is None for p in pieces):
                return None
            return base.join(pieces)  # type: ignore[arg-type]
        if (node.func.attr == "replace" and not node.keywords
                and len(node.args) == 2):
            needle = _reconstruct_holed(node.args[0], consts)
            value = _reconstruct_holed(node.args[1], consts)
            if needle is not None and value is not None and _HOLE not in needle:
                return base.replace(needle, value)
            return _unreadable_transform(base)
        if node.func.attr == "format":
            return _FORMAT_FIELD.sub(_HOLE, base)
        return _unreadable_transform(base)
    return _HOLE


def _unreadable_transform(base: str) -> str | None:
    """A form this scanner does not model, answered by what it is applied TO.

    The default branch, made explicit: applied to determined probe text the result is
    that text mangled, which no hole describes, so it is `None` and the caller refuses
    it; applied to anything else it is an ordinary value whose content this scanner
    never needed.  Asking about the BASE rather than about the method name is what
    keeps the set of recognised forms from having to be complete -- *a scanner's
    default branch is a decision*, and this one is taken per call site rather than per
    spelling.
    """
    return None if _HOLE not in base and LEAN_PROBE_MARKER.search(base) else _HOLE


def _reconstruct(node: ast.AST, consts: dict[str, str]) -> str | None:
    """The exact string `node` evaluates to, when the source ALONE determines it.

    `v0.35.127` (PR #897 review).  The superseded reader asked *is this expression a
    concatenation* and then **joined its literals in source order**, which is the
    string the program builds for `"a" + "b"` and is **not** for a `.format` on a
    template: joining yields the template followed by the argument, so the constructor
    pattern matches nothing while the template's own import marker is accounted for --
    the fail-closed marker count passed too and the asker was invisible in both
    directions at once.  *A spelling is not the text*, at the one place the text is
    assembled rather than written.

    So the question is not a shape but a **value**: return the string, or `None`.
    Since `v0.35.129` the recursion lives in `_reconstruct_holed` and this is the
    "determined everywhere" reading of it, which also makes `PROBE.replace("@K@",
    "opaque")` on a resolvable template a string rather than a refusal -- the
    *reconstructed* half of that finding's remedy, the refusal being the other.
    """
    text = _reconstruct_holed(node, consts)
    return None if text is None or _HOLE in text else text


def _string_assembly_shapes(tree: ast.AST) -> list[ast.AST]:
    """Every expression that builds a string out of PARTS.

    An operator (`+`, `%`), an f-string, or a method called on a string-valued
    expression.  A `Call` on a plain *name* -- a probe handed straight to a helper --
    is deliberately NOT one: the literal is its ARGUMENT, not a part of a string
    the call builds, and that is the commonest probe idiom in this tree.
    """
    out: list[ast.AST] = []
    for node in ast.walk(tree):
        if isinstance(node, (ast.BinOp, ast.JoinedStr)):
            out.append(node)
        elif isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
            out.append(node)
    return out


def _assembled_strings(
        tree: ast.AST) -> list[tuple[ast.AST, str, list[ast.Constant]]]:
    """`(expression, the string it builds, its string constants)` per assembly.

    Only expressions `_reconstruct` DETERMINES are here, and the second component is
    that reconstruction rather than a re-joining of the fragments -- so the text the
    constructor patterns are counted over is the text the program builds.  The
    superseded `_concatenation_groups` returned the literals in source order and its
    callers joined them, which is right for `+` and wrong for every substituting form;
    `_unreadable_assemblies` refuses those rather than reading them partially.

    Deliberately an EXPRESSION and not a statement.  Grouping by statement was
    measured at **1060** admitted fragments, because `ast.walk` of a statement
    descends into every nested one -- a dict of fixtures pulls in all of them.

    Only MAXIMAL assemblies are returned: a nested one (`("a" + "b") + "c"`) is part
    of the string its parent builds, so reporting it as well would count one fragment
    under two subjects.
    """
    consts = _module_string_bindings(tree)
    determined = [(n, _reconstruct(n, consts)) for n in _string_assembly_shapes(tree)]
    nodes = [(n, v) for n, v in determined if v is not None]
    nested = {id(d) for n, _ in nodes for d in ast.walk(n)
              if d is not n and _reconstruct(d, consts) is not None
              and isinstance(d, (ast.BinOp, ast.JoinedStr, ast.Call))}
    out: list[tuple[ast.AST, str, list[ast.Constant]]] = []
    for node, value in nodes:
        if id(node) in nested:
            continue
        constants = [c for c in ast.walk(node)
                     if isinstance(c, ast.Constant) and isinstance(c.value, str)]
        if constants:
            out.append((node, value, constants))
    return out


def _constructor_completing_holes(holed: str) -> list[int]:
    """Hole offsets at which unread text could COMPLETE a constructor spelling.

    The refusal criterion for a partially determined assembly, and the reason it is
    not an identifier-adjacency resemblance: the question is about the eight spellings
    `_WORD` counts, so it is derived from `CONSTANT_INFO_CONSTRUCTORS` and inherits
    their `\\b` bounds.  A hole completes a constructor when the template itself has
    written part of one against it --

      * a non-empty proper PREFIX of some constructor ends the text before the hole,
        with a non-word character (or nothing) before that prefix, so the leading
        `\\b` holds and the hole supplies the rest; or
      * a non-empty proper SUFFIX of some constructor begins the text after the hole,
        with a non-word character (or nothing) after it, so the trailing `\\b` holds
        and the hole supplies the front.

    A hole whose neighbours write no part of a constructor is a DATA substitution, and
    it is admitted: the located template already carries the decision, and all
    thirteen substitution sites on this tree are of that kind -- measured, in value
    positions (`[@ROOTS@]`, a line of its own, after a colon), zero of them writing a
    constructor against the hole.  A refusal that fired on those would refuse the tree.

    What that admission leaves is a FLOOR and not a count: unread text could contain a
    whole constructor of its own, which no source scanner can exclude.  That is the
    same residue `embedded_lean` already states for a fragment computed by a call, and
    it is stated rather than approximated -- refusing every hole would refuse the four
    real probes, whose decisions are written in their templates and whose holes carry
    module names, counts and quoted lists.
    """
    def wordish(ch: str) -> bool:
        return bool(ch) and (ch.isalnum() or ch == "_")

    out: list[int] = []
    for match in re.finditer(re.escape(_HOLE) + "+", holed):
        before, after = holed[:match.start()], holed[match.end():]
        for ctor in CONSTANT_INFO_CONSTRUCTORS:
            hit = False
            for cut in range(1, len(ctor)):
                prefix, suffix = ctor[:cut], ctor[cut:]
                if (before.endswith(prefix)
                        and not wordish(before[:-len(prefix)][-1:])):
                    hit = True
                elif (after.startswith(suffix)
                        and not wordish(after[len(suffix):len(suffix) + 1])):
                    hit = True
                if hit:
                    break
            if hit:
                out.append(match.start())
                break
    return out


def _substitution_into_determined_text(node: ast.AST,
                                       consts: dict[str, str]) -> bool:
    """Is `node` a `.replace` chain substituting into text this scanner has read?

    The CANONICAL spelling of a probe that carries data: one determined template
    -- a string literal, or a module constant bound to one -- with sentinels
    substituted into it.  All sixteen marker-bearing holed assemblies on the
    tracked tree are that shape, and every one of this tree's four real probes is
    built by one.

    It is the shape a probe MUST take (PR #897's review, `v0.35.144`), because
    the alternative is unbounded.  `HEADER + build_match()` reconstructs to the
    header's text plus one hole: the marker arrives through the name, so no
    string literal of the expression carries it and `_unreadable_assemblies`'
    `literal_marker` is false; the hole borders no partial constructor spelling,
    so `_constructor_completing_holes` is false; and `HEADER` is a located
    subject of its own, so the fail-closed marker count is satisfied.  The
    assembly is then invisible in BOTH directions at once while the text handed
    to Lean decides `.opaqueInfo` -- which is `v0.35.129`'s own finding at the
    one place its admission test was not applied.  That test is *the marker is
    asked of the assembled text, not of the expression's literal parts*, and it
    was applied to the `named` substitution branch and not to its sibling here:
    **a fix applied at one site and not its sibling**, for the fourth time in
    this family.

    Refusing every marker-bearing hole would refuse those sixteen, so the
    question is not *is there a hole* but *is the probe's Lean source ONE text
    this scanner has read*.  A concatenation, an interpolation, a `%` format, a
    `.format` or a `.join` says no -- the source is in two places and one of them
    is unread.  A substitution says yes: the needle is a sentinel inside text the
    scanner read, so the surrounding Lean is complete and the only question left
    is the one `_constructor_completing_holes` asks.

    **The residue is stated rather than assumed away**: a substituted VALUE can
    itself spell a whole constructor (`PROBE.replace("@BODY@", build_match())`),
    which no scanner that cannot read the value can decide.  What bounds it is
    that the probe's own text is read, so a constructor arriving that way is a
    *floor* violation rather than a silent zero, and the reconciliation this gate
    performs is keyed on counts -- see this module's `scope` line.
    """
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == "replace" and not node.keywords
            and len(node.args) == 2):
        return False
    # The NEEDLE is not re-examined here, and that is a division of labour rather
    # than an omission: `_reconstruct_holed` answers `_unreadable_transform(base)`
    # for a `.replace` whose needle it cannot read, which is `None` for determined
    # probe text -- so a computed sentinel is already refused as `form` before this
    # predicate is consulted, and asking again would be a second answer to a settled
    # question.  Case (25b)'s `computed_needle_gate` is the witness that it IS
    # settled there.
    base_text = _reconstruct_holed(node.func.value, consts)
    if base_text is not None and _HOLE not in base_text:
        return True
    return _substitution_into_determined_text(node.func.value, consts)


def _unreadable_assemblies(tree: ast.AST) -> list[tuple[ast.AST, str]]:
    """String assemblies this scanner must refuse rather than read partially.

    The fail-closed half of `_reconstruct`, and the reason narrowing the reader is
    not enough on its own: with `.format` no longer forming an assembly, its template
    literal would fall through to the bare-constant branch and be *located*, so the
    marker count would be satisfied and the hole would reopen one branch over.

    Three reasons, and the third is `v0.35.129`.

    `unreadable` -- the expression does not determine and a marker-bearing string
    LITERAL is among its parts.  The marker is nowhere else, so refusing is the only
    way the probe is seen at all.

    `form` -- the expression applies a transform this scanner does not model to
    determined probe text, so its result is not determined text with holes and no
    partial reading of it is honest.

    `splice` -- the expression IS determined text with holes, the text carries a
    marker, and unread text enters it where the template has written part of a
    constructor spelling.  This is the case the marker count cannot see: the template
    is a located subject of its own, so the marker is accounted for and only the
    CONSTRUCTOR count is wrong -- zero recorded against a probe that decides the
    question.  Refusing on the marker alone here would refuse all four of this tree's
    real probes, whose holes carry data; refusing on nothing would leave the hole.

    `builder` -- `v0.35.142` (PR #897's review), and the fourth reason exists because
    the exclusion above was a hole.  `_string_assembly_shapes` deliberately does not
    treat a `Call` on a plain NAME as an assembly: a probe handed straight to
    `run_probe(<literal>)` is its argument, not a part of a string the call builds.
    But `PROBE = build_probe(<a probe literal>, "opaque")` is
    the same shape with the opposite meaning -- the call *builds* the probe, and the
    literal is located as an inline one, so its import marker is accounted for, its
    constructor count is **zero**, and the asker that decides `.opaqueInfo` at
    runtime is invisible in both directions at once.  What separates the two is
    whether the program USES the call's result: a probe handed to a runner is a bare
    expression statement, and a probe *built* by a call is assigned, returned or
    passed on.  So a plain-name call whose result is used and whose arguments carry
    a probe-signalling literal is refused.

    Measured: **zero** refusals of any of the four reasons on the tracked tree -- the
    only probe-signalling literals passed to plain-name calls are two `print`
    diagnostics, which are statement-level and so not builders -- so all four are
    planted today.
    """
    consts = _module_string_bindings(tree)
    out: list[tuple[ast.AST, str]] = []
    for node in _string_assembly_shapes(tree):
        holed = _reconstruct_holed(node, consts)
        if holed is not None and _HOLE not in holed:
            continue
        literal_marker = any(
            isinstance(c, ast.Constant) and isinstance(c.value, str)
            and LEAN_PROBE_MARKER.search(c.value) for c in ast.walk(node))
        if holed is None:
            out.append((node, "unreadable" if literal_marker else "form"))
        elif literal_marker:
            out.append((node, "unreadable"))
        elif LEAN_PROBE_MARKER.search(holed):
            if _constructor_completing_holes(holed):
                out.append((node, "splice"))
            elif not _substitution_into_determined_text(node, consts):
                out.append((node, "concat"))
    out.extend((call, "builder") for call in _probe_building_calls(tree))
    return out


def _probe_building_calls(tree: ast.AST) -> list[ast.Call]:
    """Plain-name calls that BUILD a probe out of a literal handed to them.

    A `Call` on a plain `Name` is not a string assembly (`_string_assembly_shapes`
    says why), so its literal argument reaches the bare-constant branch and is
    located as an inline probe -- which is right when the call CONSUMES the probe
    and wrong when it builds one.  The structural difference is whether the result
    is used: `run_probe(<literal>)` is a bare expression statement, while
    `PROBE = build_probe(<template>, "opaque")` assigns, returns or passes its
    result on.  A method call is excluded because it is already an assembly, and a
    `Name` argument is excluded because the constant it names is a subject of its
    own.
    """
    bare = {id(node.value) for node in ast.walk(tree)
            if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)}
    out: list[ast.Call] = []
    for node in ast.walk(tree):
        if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)):
            continue
        if id(node) in bare:
            continue
        args = list(node.args) + [kw.value for kw in node.keywords]
        if any(isinstance(a, ast.Constant) and isinstance(a.value, str)
               and _probe_signal(a.value) for a in args):
            out.append(node)
    return out


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
    try:
        tree = ast.parse(text)
    except SyntaxError as exc:
        # **The prefilter decides only whether an UNPARSEABLE file is a refusal**
        # (PR #897's review, `v0.35.142`).  It used to gate the parse itself, and
        # that is the shape `v0.35.132` retired one level up: a prefilter must be
        # strictly WIDER than the predicate it stands in for, and no raw-text test
        # can be wider than "the AST reconstructs a probe" -- a probe assembled as
        # `"im" + "port SeLe4n ... .opaque" + "Info"` carries neither complete
        # token in its source, so both signals were false and the FILE was skipped
        # before it was parsed.  Parsing every tracked Python source costs
        # milliseconds and removes the class; what the prefilter still answers is
        # the one question it can, on a file this scanner could not parse at all:
        # whether to refuse it or to pass over it.
        if not _probe_prefilter(text):
            return []
        raise UnreadableProbe(
            f"{path} embeds Lean (an `import Lean`/`import SeLe4n` line, or a "
            f"`ConstantInfo` constructor) and does not parse as Python ({exc}), so "
            f"its probe cannot be located.") from None
    ambiguous = _ambiguous_probe_bindings(tree)
    if ambiguous:
        raise UnreadableProbe(
            f"{path} binds `{ambiguous[0]}` more than once and at least one binding "
            f"is Lean probe text" + (f" (and so does {', '.join(ambiguous[1:])})"
                                     if len(ambiguous) > 1 else "") + ".  The name "
            f"then denotes no one text, so a template reached through it cannot be "
            f"resolved and a substitution into it is read as applying to nothing; "
            f"give each probe its own name.")
    aliased = _probe_alias_bindings(tree)
    if aliased:
        alias, source = aliased[0]
        raise UnreadableProbe(
            f"{path} binds `{alias}` to the probe name `{source}` and then builds "
            f"string text through `{alias}`"
            + (f" ({len(aliased)} such aliases)" if len(aliased) > 1 else "")
            + ".  A name bound to another NAME resolves to no literal, so the "
            f"transform reads an unreadable base, its result carries no import "
            f"marker, and neither the splice nor the unreadable refusal sees it -- "
            f"while `{source}` is still located, carrying the constructors its "
            f"unsubstituted template spells rather than the ones the probe decides. "
            f" Give the probe one name: apply the substitution to `{source}` "
            f"directly and delete the alias.")
    unreadable = _unreadable_assemblies(tree)
    if unreadable:
        first, reason = unreadable[0]
        raise UnreadableProbe(
            f"{path} builds Lean probe text at line "
            f"{getattr(first, 'lineno', 0)} in a way this scanner refuses to read "
            f"partially ({_REFUSAL_REASONS[reason]}), and {len(unreadable)} "
            f"expression(s) in the file are refused.  Reading it partially would "
            f"count `ConstantInfo` constructors over text the program never builds "
            f"-- and would satisfy the marker check while doing it -- so build the "
            f"probe by `+` over literals, or substitute with an `@NAME@` sentinel on "
            f"a named template (as this tree's other probes do) placed where no "
            f"constructor spelling is written against it, so the located text "
            f"decides the question the recorded count is about.")
    found: list[tuple[str, str]] = []
    named: set[int] = set()
    constants = _string_constants(tree)
    scopes = {id(c): scope for scope, c in constants}
    by_id = {id(c): c for _, c in constants}
    assemblies = _assembled_strings(tree)
    assembly_of: dict[int, tuple[str, list[ast.Constant]]] = {
        id(n): (v, cs) for n, v, cs in assemblies}
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
                found.append((_qualified(scopes[id(value)], name), value.value))
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
        entry = assembly_of.get(id(value))
        if entry is None:
            continue
        assembled, fragments = entry
        # The marker is asked of the ASSEMBLED TEXT, not of the literal fragments
        # (`v0.35.129`).  A template reached through its NAME puts the marker in no
        # fragment of the expression that substitutes into it, so a fragment-only
        # test admitted `"@K@" + "opaque"` and refused the probe the program builds --
        # and the substituted constructor was then recorded against nothing.
        if not LEAN_PROBE_MARKER.search(assembled):
            continue
        claimed.add(id(value))
        named.update(id(c) for c in fragments)
        for name in names:
            found.append((_qualified(scopes[id(fragments[0])], name), assembled))
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
    for node, assembled, fragments in assemblies:
        if id(node) in claimed:
            continue
        # ...on the ASSEMBLED TEXT, for the reason the named branch states.
        if not LEAN_PROBE_MARKER.search(assembled):
            continue
        named.update(id(c) for c in fragments)
        inline.append((scopes[id(fragments[0])], assembled))
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
    # ...and TWO NAMED probes under one qualified key are refused too, which is the
    # same claim for the branch that binds a name.  `A = B = <probe>` is one probe
    # under two keys and is fine; what this refuses is two DISTINCT probe texts whose
    # counts would add under one key -- a name rebound at the same scope, or (before
    # `_qualified`) the same name in two scopes.  Symmetric with the refusal above by
    # construction, because *keeping the tables symmetric* is what stopped this from
    # being found by a review round rather than by the gate.
    #
    # A COUNT, not a set of texts: two assignments of the *same* text to one name
    # also double every constructor in it, and a set cannot see the second one --
    # which is this gate's own rule one level inside the check that enforces it.
    occurrences: dict[str, int] = {}
    for key, _src in found:
        occurrences[key] = occurrences.get(key, 0) + 1
    clashing = sorted(k for k, n in occurrences.items() if n > 1)
    if clashing:
        raise UnreadableProbe(
            f"{path} binds {occurrences[clashing[0]]} probes to the subject key "
            f"`{clashing[0]}`" +
            (f" (and several to {', '.join(clashing[1:])})"
             if len(clashing) > 1 else "") +
            ".  Their constructor counts would add under one key, where a count "
            f"moving from one to the other is invisible; give each probe its own "
            f"name.")
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
    "scripts/check_declaration_kind_askers.py::_FIXTURE_CALL_CONSUMED_PROBE":
        "THIS GATE'S OWN FIXTURE (`v0.35.142`, PR #897's review): the CONTROL for "
        "the plain-name-call refusal beside it -- the same shape with the call's "
        "RESULT unused, which is a probe handed straight to a runner and must be "
        "READ.  Without it the refusal would read as \"a marker-bearing literal may "
        "not be a call argument\", which refuses this tree's own inline-probe idiom.",
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
    "scripts/check_declaration_kind_askers.py::_FIXTURE_CONCATENATED_FRAGMENT":
        "THIS GATE'S OWN FIXTURE for the reported defect (`v0.35.144`, PR #897's "
        "review): a probe whose Lean source is a named header CONCATENATED with an "
        "opaque call's result.  The marker arrives through the name, so no literal "
        "of the expression carries it; the hole borders no partial constructor, so "
        "the splice test is false; and the header is a located subject of its own, "
        "so the marker count is satisfied.  Its `opaqueInfo` is the constructor the "
        "unread fragment decides -- invisible in BOTH directions before the fix.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_COMPUTED_NEEDLE":
        "THIS GATE'S OWN FIXTURE for the NEEDLE half (`v0.35.144`): a substitution "
        "whose sentinel is itself computed, so the scanner cannot say where in the "
        "template the hole lands.  Its own case, because the base half below is "
        "rejected by a different conjunct and a fixture exercising one leaves the "
        "other unwitnessed.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_UNDETERMINED_BASE":
        "THIS GATE'S OWN FIXTURE for the BASE half (`v0.35.144`): a substitution "
        "into text that is itself a concatenation with a hole, so the template is "
        "not text this scanner has read.  Without it, \"any `.replace` is "
        "canonical\" passes every other case.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_CANONICAL_SUBSTITUTION":
        "THIS GATE'S OWN FIXTURE for the CONTROL the three refusals need "
        "(`v0.35.144`): a determined named template with a DATA value substituted "
        "into it, which is what all four of this tree's real probes and all sixteen "
        "of its live marker-bearing holed assemblies are.  Its `opaqueInfo` is read "
        "rather than refused, so a widening that refuses every hole fails here -- "
        "which is the only thing keeping the refusal from refusing the tree.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_NESTED_CONCATENATION":
        "THIS GATE'S OWN FIXTURE for the maximal-group rule: a probe whose "
        "concatenation nests, where reporting the inner expression as well would "
        "count the same subject twice.  Its `recInfo` is what case (16) reads back "
        "under ONE key, so a fixture that lost it would assert nothing.  Its "
        "sibling `_FIXTURE_ORDERED_FRAGMENTS` is deliberately NOT a subject: its "
        "constructor name is split across a `\"\"\" + \"\"\"` boundary, so the "
        "literal text of this file carries no match -- which is exactly the "
        "property case (15) is about, one level up.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_FSTRING_LITERAL":
        "THIS GATE'S OWN FIXTURE, and the CONTROL for the assembly-form axis: an "
        "f-string with no interpolation is a literal, so it reconstructs and is "
        "READ.  Its `axiomInfo` is what case (20) reads back; without it the "
        "refusal beside it would read as \"f-strings are refused\" rather than "
        "\"interpolation cannot be evaluated\", and a fix that banned the node "
        "type would pass case (19).",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_SENTINEL_TEMPLATE":
        "THIS GATE'S OWN FIXTURE, and the CONTROL for the enclosure axis: a "
        "`@SENTINEL@` template consumed by `.replace` is how all four of this "
        "tree's real probes are built, so a refusal that fired here would refuse "
        "the tree.  Its `inductInfo` is what case (21) reads back under the "
        "template's own name, which is where the marker lives.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_UNMODELLED_TRANSFORM":
        "THIS GATE'S OWN FIXTURE for the substitution axis' `form` reason: "
        "determined probe text passed to a transform this scanner does not model.  "
        "Its `opaqueInfo` is in the TEMPLATE, deliberately -- the refusal is about "
        "the transform mangling text the scanner has already read, so a fixture "
        "whose template decided nothing would be refused for the wrong reason and "
        "case (27) would not distinguish `form` from `splice`.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_BOUNDED_HOLE_NEIGHBOURS":
        "THIS GATE'S OWN FIXTURE for the word-boundary half of the completion "
        "test: its `defnInfo` is what case (29) reads back, and reading it is the "
        "claim -- a neighbour spelling part of a constructor inside a longer "
        "identifier cannot complete a word-bounded match, so the template is a "
        "DATA substitution and refusing it would reject a probe this gate should "
        "read.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_AMBIGUOUS_FRAGMENT":
        "THIS GATE'S OWN FIXTURE for the resolution axis: its `defnInfo` sits in "
        "the FIRST of two bindings of one name, which is what makes the fixture "
        "decisive -- a scanner that resolved the name to that binding would read "
        "the probe as deciding it, and the count recorded here is over the "
        "fixture's own literal text rather than over any text the program builds.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_SAME_NAME_TWO_SCOPES":
        "THIS GATE'S OWN FIXTURE for the subject-key axis: two probes binding one "
        "local name in two scopes.  The two counts are the two probes and they "
        "must DIFFER -- under the superseded bare-name key they landed under one "
        "subject and ADDED, so swapping a constructor between them left every "
        "number unchanged, which is exactly what case (22) refutes.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_NAME_REBOUND":
        "THIS GATE'S OWN FIXTURE for the other value of that axis: one name "
        "rebound at a SINGLE scope, which no key can separate, so it is refused.  "
        "Its two counts are the two bindings; they are the surplus a shared key "
        "would produce, and case (23) asserts the refusal rather than the counts.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_TWO_INLINE_ONE_SCOPE":
        "THIS GATE'S OWN FIXTURE for the second refusal: two probes binding no name "
        "in one scope, which would share a subject key.  The two counts are the two "
        "probes, and they must DIFFER -- a count moving between them under a shared "
        "key is precisely what the refusal exists to prevent.",
    "scripts/check_declaration_kind_askers.py::_FIXTURE_ALIASED_PASSTHROUGH":
        "THIS GATE'S OWN FIXTURE for the CONTROL of the alias refusal: a probe "
        "merely passed on by name, with no assembly reading it, which hides nothing "
        "and must still be located and counted under its own name.  Its constructor "
        "is what the control asserts, so a refusal that swallowed the pass-through "
        "would show up as a missing count rather than as a silent pass.",
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
    "scripts/check_declaration_kind_askers.py::_FIXTURE_CALL_CONSUMED_PROBE": {
        "opaqueInfo": 1,
    },
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
    "scripts/check_declaration_kind_askers.py::_FIXTURE_CONCATENATED_FRAGMENT": {
        "opaqueInfo": 1,
    },
    "scripts/check_declaration_kind_askers.py::_FIXTURE_COMPUTED_NEEDLE": {
        "opaqueInfo": 1,
    },
    "scripts/check_declaration_kind_askers.py::_FIXTURE_UNDETERMINED_BASE": {
        "opaqueInfo": 1,
    },
    "scripts/check_declaration_kind_askers.py::_FIXTURE_CANONICAL_SUBSTITUTION": {
        "opaqueInfo": 1,
    },
    "scripts/check_declaration_kind_askers.py::_FIXTURE_DOUBLE_BOUND_PROBE": {
        "quotInfo": 1,
    },
    "scripts/check_declaration_kind_askers.py::_FIXTURE_FSTRING_LITERAL": {
        "axiomInfo": 1,
    },
    "scripts/check_declaration_kind_askers.py::_FIXTURE_SENTINEL_TEMPLATE": {
        "inductInfo": 1,
    },
    "scripts/check_declaration_kind_askers.py::_FIXTURE_ALIASED_PASSTHROUGH": {
        "defnInfo": 1,
    },
    "scripts/check_declaration_kind_askers.py::_FIXTURE_UNMODELLED_TRANSFORM": {
        "opaqueInfo": 1,
    },
    "scripts/check_declaration_kind_askers.py::_FIXTURE_BOUNDED_HOLE_NEIGHBOURS": {
        "defnInfo": 1,
    },
    "scripts/check_declaration_kind_askers.py::_FIXTURE_AMBIGUOUS_FRAGMENT": {
        "defnInfo": 1,
    },
    "scripts/check_declaration_kind_askers.py::_FIXTURE_SAME_NAME_TWO_SCOPES": {
        "defnInfo": 1,
        "opaqueInfo": 1,
    },
    "scripts/check_declaration_kind_askers.py::_FIXTURE_NAME_REBOUND": {
        "defnInfo": 1,
        "opaqueInfo": 1,
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

#: **`v0.35.127` (PR #897 review): the assembly FORMS, at every value of the axis.**
#: `_reconstruct` divides string-building expressions into the ones literals determine
#: and the ones they do not, and the second half is REFUSED rather than partially read.
#: The axis is taken from Python's grammar rather than from the reported spelling: the
#: review named `.format`, and `%`, an interpolating f-string and an arbitrary string
#: method defeat a joining reader in exactly the same way.
_FIXTURE_FORMAT_ASSEMBLED = '''\
TEMPLATE = ("""
import SeLe4n

private def formatted (ci : ConstantInfo) : Bool :=
  match ci with
  | .{}Info _ => true
  | _ => false
""").format("opaque")
'''

#: The same defect in the `%` spelling, which the superseded reader did not even group
#: -- so its template was read as a bare inline probe and the constructor was lost the
#: same way, one branch further over.
_FIXTURE_PERCENT_ASSEMBLED = '''\
TEMPLATE = """
import SeLe4n

private def formatted (ci : ConstantInfo) : Bool :=
  match ci with
  | .%sInfo _ => true
  | _ => false
""" % "opaque"
'''

#: ...and in the f-string spelling, whose `FormattedValue` parts are not literals.
_FIXTURE_FSTRING_INTERPOLATED = '''\
KIND = "opaque"

TEMPLATE = f"""
import SeLe4n

private def interpolated (ci : ConstantInfo) : Bool :=
  match ci with
  | .{KIND}Info _ => true
  | _ => false
"""
'''

#: The CONTROL for the form axis: an f-string with NO interpolation is a literal, so it
#: reconstructs and is read.  Without it the refusal would read as "f-strings are
#: refused" rather than "interpolation cannot be evaluated".
_FIXTURE_FSTRING_LITERAL = '''\
TEMPLATE = f"""
import SeLe4n

private def literalFString (ci : ConstantInfo) : Bool :=
  match ci with
  | .axiomInfo _ => true
  | _ => false
"""
'''

#: The CONTROL for the ENCLOSURE axis, and the one that matters most: `.replace` on a
#: NAMED template with `@SENTINEL@` placeholders is how all four of this tree's real
#: probes are built, and the marker lives in the template's own assignment.  A refusal
#: that fired here would refuse the tree.
_FIXTURE_SENTINEL_TEMPLATE = '''\
PROBE_TEMPLATE = """
import SeLe4n

private def sentinel (ci : ConstantInfo) : Bool :=
  match ci with
  | .inductInfo _ => true
  | _ => false
-- @TARGETS@
"""


def build(names):
    return PROBE_TEMPLATE.replace("@TARGETS@", ", ".join(names))
'''

#: **The SUBSTITUTION axis** (`v0.35.129`, PR #897 review).  A named template holding
#: a constructor spelling with a HOLE in it, substituted at runtime.  The template is
#: a LOCATED subject, so its import marker is accounted for and the fail-closed marker
#: count is satisfied, while its constructor count is **zero** and the probe handed to
#: Lean matches `.opaqueInfo`.  Invisible in both directions at once -- the `.format`
#: finding one artefact over, at the place the text is transformed rather than
#: assembled.  `_constructor_completing_holes` is what sees it: the template has
#: written `Info` against the hole, so unread text can complete a constructor there.
_FIXTURE_SPLICED_CONSTRUCTOR = '''\
PROBE_TEMPLATE = """
import SeLe4n

private def spliced (ci : ConstantInfo) : Bool :=
  match ci with
  | .@KIND@Info _ => true
  | _ => false
"""


def build(kind):
    return PROBE_TEMPLATE.replace("@KIND@", kind)
'''

#: The same splice through the two OTHER substitution mini-languages and through
#: concatenation, so the refusal is about where unread text enters a template rather
#: than about `.replace`.  A fix that taught the scanner one spelling would pass the
#: fixture above and leave all three of these open.
_FIXTURE_SPLICED_BY_FORMAT = '''\
PROBE_TEMPLATE = """
import SeLe4n

private def spliced (ci : ConstantInfo) : Bool :=
  match ci with
  | .{}Info _ => true
  | _ => false
"""


def build(kind):
    return PROBE_TEMPLATE.format(kind)
'''

_FIXTURE_SPLICED_BY_PERCENT = '''\
PROBE_TEMPLATE = """
import SeLe4n

private def spliced (ci : ConstantInfo) : Bool :=
  match ci with
  | .%sInfo _ => true
  | _ => false
"""


def build(kind):
    return PROBE_TEMPLATE % (kind,)
'''

_FIXTURE_SPLICED_BY_CONCATENATION = '''\
PROBE_HEAD = """
import SeLe4n

private def spliced (ci : ConstantInfo) : Bool :=
  match ci with
  | .
"""


def build(kind):
    return PROBE_HEAD + kind + "Info _ => true | _ => false"
'''

#: The DETERMINED half of the same axis, and the *reconstructed* rather than refused
#: outcome: the substituted value is a literal, so the probe the program builds is a
#: string this scanner can read, and the constructor it decides is recorded under the
#: enclosing declaration.  The template keeps its own subject with a count of zero,
#: which is the truth about the template's own text.  Refusing this would be the
#: wrong remedy -- *reconstruct what you can, refuse only what you cannot*.
_FIXTURE_SPLICED_DETERMINED = '''\
PROBE_TEMPLATE = """
import SeLe4n

private def spliced (ci : ConstantInfo) : Bool :=
  match ci with
  | .@KIND@Info _ => true
  | _ => false
"""


def build():
    return PROBE_TEMPLATE.replace("@KIND@", "opaque")
'''

#: A transform this scanner does not model, applied to determined probe text.  Its
#: result is that text mangled, which no hole describes, so reading it partially would
#: count constructors over text the program never builds.  The CONTROL for it is the
#: tree's own `", ".join(names)` inside `_FIXTURE_SENTINEL_TEMPLATE`: the same shape
#: applied to text that is not a probe is an ordinary value fragment and is read.
_FIXTURE_UNMODELLED_TRANSFORM = '''\
PROBE_TEMPLATE = """
import SeLe4n

private def mangled (ci : ConstantInfo) : Bool :=
  match ci with
  | .opaqueInfo _ => true
  | _ => false
"""


def build():
    return PROBE_TEMPLATE.upper()
'''

#: PR #897's review, `v0.35.142`: a probe whose markers are SPLIT across fragments,
#: so its raw source carries neither a complete `import SeLe4n` nor a complete
#: constructor.  The superseded file-level prefilter answered "no probe here" and
#: `embedded_lean` returned before parsing, so the asker was outside the inventory
#: with the gate reporting the tree clean.  Reconstructing the assembly is what sees
#: it; the fragments are all literals, so it READS rather than refuses.
_FIXTURE_SPLIT_MARKER_PROBE = '''\
PROBE = ("im" + """port SeLe4n

private def k (ci : ConstantInfo) : Bool :=
  match ci with | .opaque""" + """Info _ => true | _ => false
""")
'''

#: PR #897's review, `v0.35.142`: a probe BUILT by a plain-name call.  The literal is
#: the call's argument rather than a part of a string the call builds, so it is
#: located as an inline probe -- its import marker accounted for and its constructor
#: count zero -- while the text the program runs decides `.opaqueInfo`.  What
#: separates it from the read case is that the call's RESULT is used.
_FIXTURE_CALL_BUILT_PROBE = '''\
def build_probe(template, kind):
    return template.replace("@KIND@", kind)


PROBE = build_probe("""
import SeLe4n

private def k (ci : ConstantInfo) : Bool :=
  match ci with | .@KIND@Info _ => true | _ => false
""", "opaque")
'''

#: The CONTROL for the one above: the same shape with the call's result UNUSED, which
#: is a probe handed straight to a runner.  Without it the refusal would read as "a
#: marker-bearing literal may not be a call argument", which would refuse this tree's
#: own inline-probe idiom.
_FIXTURE_CALL_CONSUMED_PROBE = '''\
def run_probe(source):
    return source


run_probe("""
import SeLe4n

private def k (ci : ConstantInfo) : Bool :=
  match ci with | .opaqueInfo _ => true | _ => false
""")
'''

#: The RESOLUTION residue, closed.  A template whose name is bound twice -- here at
#: module scope and again inside a function -- denotes no one text, so the substitution
#: below would be read as applying to nothing and the splice refusal would never see
#: the template.  The defect walks around the fix by rebinding the name, so an
#: ambiguous probe-bearing name is refused before any assembly is examined.  Distinct
#: from the duplicate-SUBJECT-KEY refusal beside it: these two probes have different
#: keys, and what fails is *resolution*, not the counts adding.
_FIXTURE_AMBIGUOUS_TEMPLATE_NAME = '''\
PROBE = """
import SeLe4n

private def outer (ci : ConstantInfo) : Bool :=
  match ci with
  | .@KIND@Info _ => true
  | _ => false
"""


def build(kind):
    PROBE = """
import SeLe4n
-- an ordinary second binding
"""
    return PROBE.replace("@KIND@", kind)
'''

#: The WORD-BOUNDARY half of the completion test, which nothing else witnesses.  A
#: constructor is counted as a whole word (`_WORD` is `\b<ctor>\b`), so a neighbour
#: that spells part of one *inside a longer identifier* cannot complete a match: no
#: substitution makes `xopaqueInfo` or `opaqueInformal` a word-bounded `opaqueInfo`.
#: Dropping either guard refuses this template, which is refusing a data substitution
#: -- the fail-CLOSED direction, and still a defect, since the gate would then reject
#: a probe it should read.  Two holes and not one, so a mutation that drops only the
#: front guard or only the back guard is caught by its own half.
_FIXTURE_BOUNDED_HOLE_NEIGHBOURS = '''\
PROBE_TEMPLATE = """
import SeLe4n

private def bounded (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ => true
  | _ => false

-- `xopaque` before the first hole and `Informal` after the second each spell part
-- of a constructor name INSIDE a longer identifier, so neither can complete a
-- word-bounded match however the holes are filled.  The name itself is spelled in
-- this fixture's Python docstring and NOT here: the gate counts a probe's own text,
-- so an explanatory mention inside one would be a decision the probe does not make.
-- front: xopaque@FRONT@ back: @BACK@Informal
"""


def build(front, back):
    return PROBE_TEMPLATE.replace("@FRONT@", front).replace("@BACK@", back)
'''

#: The ASSIGNED half of the determined substitution.  `_FIXTURE_SPLICED_DETERMINED`
#: returns its probe, so it is named after its enclosing declaration; this one binds
#: it, so it is named after the target.  Two fixtures because `embedded_lean` has two
#: branches and both were changed to ask the marker of the ASSEMBLED TEXT: a template
#: reached through its NAME puts the marker in no literal fragment of the expression
#: that substitutes into it, so the superseded fragment-only test dropped the
#: assignment's name and reported the probe under its enclosing scope instead.
#: *Keeping the tables symmetric* is what makes a mutation of either branch visible.
_FIXTURE_ASSIGNED_SUBSTITUTION = '''\
PROBE_TEMPLATE = """
import SeLe4n

private def assigned (ci : ConstantInfo) : Bool :=
  match ci with
  | .@KIND@Info _ => true
  | _ => false
"""

PROBE = PROBE_TEMPLATE.replace("@KIND@", "ctor")
'''

#: The RESOLUTION half in its other direction: an ambiguous name that is NOT probe
#: text, reached by an assembly whose marker comes from a literal.  Resolving it to
#: either binding would read the probe over text the program may never build, so the
#: name resolves to nothing and the assembly is refused as unreadable.  Without this
#: fixture the "bound once" condition carries no witness -- the ambiguous-PROBE
#: refusal fires first for every name that is probe text, so a mutation resolving an
#: ambiguous name to its first binding passed every other case.
_FIXTURE_AMBIGUOUS_FRAGMENT = '''\
SUFFIX = "-- .defnInfo is decided here"
SUFFIX = "-- and nothing is decided here"

PROBE = """
import SeLe4n
""" + SUFFIX
'''

#: **The SUBJECT-KEY axis.**  Two probes binding one local name in two scopes, which
#: the superseded bare-name key collapsed into ONE subject with their counts added --
#: so swapping a constructor between them left every number unchanged.
_FIXTURE_SAME_NAME_TWO_SCOPES = '''\
def probe_definition():
    PROBE = """
import SeLe4n

private def inFirst (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ => true
  | _ => false
"""
    return PROBE


def probe_opaque():
    PROBE = """
import SeLe4n

private def inSecond (ci : ConstantInfo) : Bool :=
  match ci with
  | .opaqueInfo _ => true
  | _ => false
"""
    return PROBE
'''

#: ...and one name REBOUND at a single scope, which no key can separate, so it is
#: refused.  A set of texts could not see this if the two texts were identical, which
#: is why the duplicate check counts occurrences.
_FIXTURE_NAME_REBOUND = '''\
PROBE = """
import SeLe4n

private def firstBinding (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ => true
  | _ => false
"""

PROBE = """
import SeLe4n

private def secondBinding (ci : ConstantInfo) : Bool :=
  match ci with
  | .opaqueInfo _ => true
  | _ => false
"""
'''

#: One probe bound to TWO names, beside a marker the scanner cannot locate.  The
#: refusal counts markers in LOCATED TEXT, and this shape is the only one on which
#: that differs from counting the rows reported: the shared constant is reported
#: twice, so a row-sum reads two markers accounted for against the two in the file
#: and the unlocatable one is MASKED.  A surplus from double-reporting must not pay
#: for a marker nobody read.
#: The FILE-level prefilter's own defect (`v0.35.132`).  The literal OPENS on the
#: assignment line, so no line of the raw source begins with the import, and the
#: template fills `.@KIND@Info`, so no complete constructor is spelled either: both
#: signals are false on the raw text and the file is never parsed.  The located
#: VALUE is anchored at its own start, so the value-level signal admits it the
#: moment the file is read -- which is why the remedy is a wider prefilter rather
#: than a weaker signal.
_FIXTURE_INLINE_OPENED_LITERAL = '''\
PROBE = """import SeLe4n.Platform.FFI

def fixtureProbe : BaseIO Unit := pure ()
"""


def build():
    return PROBE
'''

#: The RESOLUTION residue reached by an extra HOP rather than by a second binding
#: (`v0.35.132`).  `ALIAS = PROBE` resolves to no literal, so `ALIAS.replace(...)`
#: substitutes into a hole; the result is a hole, carries no import marker, and so
#: neither the splice refusal nor the unreadable refusal fires -- while `PROBE` is
#: located carrying zero constructors and the probe handed to Lean matches
#: `.opaqueInfo`.  TWO hops, so a fix that closes only the direct alias is caught
#: by the fixture rather than by the next review round.
_FIXTURE_ALIASED_TEMPLATE = '''\
PROBE = """
import SeLe4n

private def aliased (ci : ConstantInfo) : Bool :=
  match ci with
  | .@KIND@Info _ => true
  | _ => false
"""

HOP = PROBE
ALIAS = HOP


def build(kind):
    return ALIAS.replace("@KIND@", kind)
'''

#: The CONTROL for the alias refusal, and what keeps it from rejecting correct
#: code.  A probe passed on by name with no assembly reading it hides nothing: the
#: template is located and counted under its own name, exactly as it would be
#: without the binding.  Without this case a mutation dropping the `reached`
#: condition refuses every such pass-through and still passes the self-test.
_FIXTURE_ALIASED_PASSTHROUGH = '''\
PROBE = """
import SeLe4n

private def passthrough (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ => true
  | _ => false
"""

SRC = PROBE


def run():
    return _elaborate(SRC)
'''

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

#: The one marker-bearing text case (25b-iii) reads the contract over, with the
#: expression under test substituted in.  Written this way ON PURPOSE: it is the
#: canonical spelling the contract requires, so the case demonstrates the rule it
#: checks, and the four expressions carry no marker and so need no names.
_CONTRACT_SHAPE_TEMPLATE = '''\
T = """
import SeLe4n
"""
P = @EXPRESSION@
'''

_FIXTURE_CONCATENATED_FRAGMENT = '''\
HEADER = """
import SeLe4n

private def asked (ci : ConstantInfo) : Bool :=
  match ci with
"""


def build_match() -> str:
    return "  | .opaqueInfo _ => true\\n  | _ => false\\n"


PROBE = HEADER + build_match()
'''

_FIXTURE_COMPUTED_NEEDLE = '''\
TEMPLATE = """
import SeLe4n

private def asked (ci : ConstantInfo) : Bool :=
  match ci with
@SLOT@
"""


def slot_name() -> str:
    return "@SLOT@"


def body() -> str:
    return "  | .opaqueInfo _ => true\\n  | _ => false\\n"


PROBE = TEMPLATE.replace(slot_name(), body())
'''

_FIXTURE_UNDETERMINED_BASE = '''\
HEADER = """
import SeLe4n

private def asked (ci : ConstantInfo) : Bool :=
  match ci with
"""


def tail() -> str:
    return "@SLOT@\\n"


PROBE = (HEADER + tail()).replace("@SLOT@", "  | .opaqueInfo _ => true\\n")
'''

_FIXTURE_CANONICAL_SUBSTITUTION = '''\
TEMPLATE = """
import SeLe4n

private def asked (ci : ConstantInfo) : Bool :=
  match ci with
  | .opaqueInfo _ => true
  | _ => false
-- @NOTE@
"""


def note() -> str:
    return "built by a data substitution"


PROBE = TEMPLATE.replace("@NOTE@", note())
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

    # (18) A `.format`-assembled probe is REFUSED, not joined.  Source-order joining
    #      is the string `"a" + "b"` builds and is NOT the one `"… .{}Info …"
    #      .format("opaque")` builds: joining yields `… .{}Info … opaque`, so the
    #      constructor pattern matches nothing while the template's own import marker
    #      IS accounted for -- so the fail-closed marker count passes too and the
    #      asker is invisible in both directions at once.  *A spelling is not the
    #      text*, at the one place the text is assembled rather than written.
    with tempfile.TemporaryDirectory() as root:
        fmt = "scripts/format_gate.py"
        _fixture(root, {**base, fmt: _FIXTURE_FORMAT_ASSEMBLED})
        problems = violations(root, base_pin, base_reasons)
        if not any(fmt in p and "refuses to read partially" in p
                   for p in problems):
            print("FAIL: --self-test — a `.format`-assembled probe was not refused:")
            print(f"      {problems}.  Joining its literals counts constructors")
            print("      over text the program never builds.")
            return 1

    # (19) ...and so are its two siblings on the same axis.  The review named
    #      `.format`; `%` was not even GROUPED by the superseded reader, so its
    #      template fell through to the bare-constant branch and was read as an
    #      inline probe with the constructor lost the same way -- the identical
    #      defect one branch further over -- and an interpolating f-string has
    #      `FormattedValue` parts that are not literals at all.  *Take the axis from
    #      the grammar, not from the reported spelling.*
    for label, body in (("percent_gate.py", _FIXTURE_PERCENT_ASSEMBLED),
                        ("fstring_gate.py", _FIXTURE_FSTRING_INTERPOLATED)):
        with tempfile.TemporaryDirectory() as root:
            sib = "scripts/" + label
            _fixture(root, {**base, sib: body})
            problems = violations(root, base_pin, base_reasons)
            if not any(sib in p and "refuses to read partially" in p
                       for p in problems):
                print(f"FAIL: --self-test — {sib} was not refused: {problems}.")
                print("      Every substituting form loses the constructor the same")
                print("      way; the axis is Python's grammar, not one spelling.")
                return 1

    # (20) The CONTROL for that axis: an f-string with NO interpolation is a literal,
    #      so it reconstructs and is READ.  Without it the refusal would read as
    #      "f-strings are refused" rather than "interpolation cannot be evaluated",
    #      and a fix that simply banned the node type would pass case (19).
    with tempfile.TemporaryDirectory() as root:
        lit = "scripts/fstring_literal_gate.py"
        _fixture(root, {**base, lit: _FIXTURE_FSTRING_LITERAL})
        got = {k: v for k, v in _capture_fixture(root).items() if k.startswith(lit)}
        expected = {lit + "::TEMPLATE": {"axiomInfo": 1}}
        if got != expected:
            print("FAIL: --self-test — an f-string with no interpolation was not")
            print(f"      read: {got}, expected {expected}.  It is a literal; the")
            print("      refusal is about substitution, not about the node type.")
            return 1

    # (21) The CONTROL for the ENCLOSURE axis, and the one that matters most:
    #      `.replace("@SENTINEL@", …)` on a NAMED template is how all four of this
    #      tree's real probes are built, and the marker lives in the template's own
    #      assignment, so the located text is the template itself.  A refusal that
    #      fired here would refuse the tree -- which is why the assembly shapes
    #      exclude a call on a plain name, and why this case is an equality rather
    #      than an absence.
    with tempfile.TemporaryDirectory() as root:
        sen = "scripts/sentinel_gate.py"
        _fixture(root, {**base, sen: _FIXTURE_SENTINEL_TEMPLATE})
        got = {k: v for k, v in _capture_fixture(root).items() if k.startswith(sen)}
        expected = {sen + "::PROBE_TEMPLATE": {"inductInfo": 1}}
        if got != expected:
            print("FAIL: --self-test — a `@SENTINEL@` template consumed by")
            print(f"      `.replace` was not read: {got}, expected {expected}.")
            print("      That is the idiom every real probe in this tree uses.")
            return 1

    # (22) TWO probes binding one local name in TWO scopes are two subjects.  The
    #      superseded key was the bare target name, so both landed under
    #      `<path>::PROBE` and their counts ADDED: change one from `.defnInfo` to
    #      `.opaqueInfo` and the other the inverse, and every number in the inventory
    #      is unchanged while both askers have re-decided the body-bearing question.
    #      `v0.35.124` had already refused exactly that for probes binding NO name,
    #      one branch over, under a comment stating the reason -- *a fix applied at
    #      one site and not its sibling*.  The equality is the check: one key here is
    #      the defect.
    with tempfile.TemporaryDirectory() as root:
        two_scopes = "scripts/two_scopes_gate.py"
        _fixture(root, {**base, two_scopes: _FIXTURE_SAME_NAME_TWO_SCOPES})
        got = {k: v for k, v in _capture_fixture(root).items()
               if k.startswith(two_scopes)}
        expected = {two_scopes + "::probe_definition.PROBE": {"defnInfo": 1},
                    two_scopes + "::probe_opaque.PROBE": {"opaqueInfo": 1}}
        if got != expected:
            print("FAIL: --self-test — two probes binding one local name in two")
            print(f"      scopes were not two subjects: {got}, expected {expected}.")
            print("      A shared key cannot see a count moving between them.")
            return 1

    # (23) ...and one name REBOUND at a single scope is refused, because no key can
    #      separate two probes bound to the same name in the same place.  The named
    #      sibling of case (14), and the reason the duplicate check counts
    #      OCCURRENCES rather than distinct texts: two identical rebindings double
    #      every constructor in them, and a set of texts cannot see the second one.
    with tempfile.TemporaryDirectory() as root:
        rebound = "scripts/rebound_gate.py"
        _fixture(root, {**base, rebound: _FIXTURE_NAME_REBOUND})
        problems = violations(root, base_pin, base_reasons)
        if not any(rebound in p and "subject key" in p for p in problems):
            print("FAIL: --self-test — a name rebound at one scope was not refused:")
            print(f"      {problems}.  Two probes under one key add their counts.")
            return 1

    # (9) The real tree, which is the check the tier runs.
    live = violations()
    if live:
        print("FAIL: --self-test — the live tree reports violations:")
        for v in live:
            print(f"      {v}")
        return 1

    # (24) **The SUBSTITUTION axis** (`v0.35.129`, PR #897 review).  A named template
    #      holding `.@KIND@Info`, substituted at runtime, is REFUSED.  `v0.35.127`
    #      asked *what value does this expression have* and answered "the string, or
    #      nothing"; this is the case where the answer is almost the string.  The
    #      template is a LOCATED subject, so its marker is accounted for and the
    #      fail-closed count is satisfied, while its constructor count is zero and
    #      the probe Lean receives matches `.opaqueInfo` -- invisible in both
    #      directions at once.
    with tempfile.TemporaryDirectory() as root:
        spl = "scripts/splice_gate.py"
        _fixture(root, {**base, spl: _FIXTURE_SPLICED_CONSTRUCTOR})
        problems = violations(root, base_pin, base_reasons)
        if not any(spl in p and "constructor against it" in p for p in problems):
            print("FAIL: --self-test — a template splicing its own constructor was")
            print(f"      not refused: {problems}.  The template records zero while")
            print("      the probe it builds decides the question.")
            return 1

    # (25) ...and so does every other way unread text enters a template.  `.format`,
    #      `%` and a concatenation put the hole in the same place; a fix that taught
    #      the scanner `.replace` alone would pass (24) and leave all three open.
    #      *Take the axis from the grammar, not from the reported spelling.*
    for label, body in (("splice_format_gate.py", _FIXTURE_SPLICED_BY_FORMAT),
                        ("splice_percent_gate.py", _FIXTURE_SPLICED_BY_PERCENT),
                        ("splice_concat_gate.py",
                         _FIXTURE_SPLICED_BY_CONCATENATION)):
        with tempfile.TemporaryDirectory() as root:
            sib = "scripts/" + label
            _fixture(root, {**base, sib: body})
            problems = violations(root, base_pin, base_reasons)
            if not any(sib in p and "constructor against it" in p
                       for p in problems):
                print(f"FAIL: --self-test — {sib} was not refused: {problems}.")
                print("      A hole written against a constructor spelling is the")
                print("      same defect however the hole is spelled.")
                return 1

    # (25b) ...and a fragment the scanner cannot read need not border a partial
    #       constructor to decide the question: it can spell a WHOLE one.
    #       `HEADER + build_match()` reconstructs to the header's text plus one
    #       hole -- the marker arrives through a name, so no literal of the
    #       expression carries it and (24)'s `literal_marker` is false; the hole
    #       borders no partial spelling, so (25)'s test is false; and `HEADER` is
    #       a located subject of its own, so the fail-closed marker count is
    #       satisfied.  Invisible in BOTH directions while the text handed to
    #       Lean decides `.opaqueInfo` (PR #897's review, `v0.35.144`).  The
    #       needle and the base each get their own case, because a fixture that
    #       exercises one leaves the other unwitnessed -- and the CONTROL below
    #       is what keeps the refusal about *the probe's source being in two
    #       places* rather than about there being a hole at all, which would
    #       refuse all sixteen marker-bearing substitutions on the live tree.
    for label, body, why in (
            ("concat_fragment_gate.py", _FIXTURE_CONCATENATED_FRAGMENT,
             "unread text is concatenated onto determined probe text"),
            ("undetermined_base_gate.py", _FIXTURE_UNDETERMINED_BASE,
             "the template substituted INTO is not text this scanner has read")):
        with tempfile.TemporaryDirectory() as root:
            sib = "scripts/" + label
            _fixture(root, {**base, sib: body})
            problems = violations(root, base_pin, base_reasons)
            if not any(sib in p and "not ONE text" in p for p in problems):
                print(f"FAIL: --self-test — {sib} was not refused: {problems}.")
                print(f"      {why}, so the probe's Lean source is in two places")
                print("      and one of them is unread.")
                return 1

    # (25b-ii) ...and a COMPUTED sentinel is refused one layer up, by the
    #          reconstruction rather than by the substitution contract: a
    #          `.replace` whose needle this scanner cannot read is an unmodelled
    #          transform applied to determined probe text, which no hole
    #          describes.  Asserting the REASON is what pins the division of
    #          labour -- without it, a second needle test could be added to the
    #          contract and nothing would say the question already had an owner.
    with tempfile.TemporaryDirectory() as root:
        sib = "scripts/computed_needle_gate.py"
        _fixture(root, {**base, sib: _FIXTURE_COMPUTED_NEEDLE})
        problems = violations(root, base_pin, base_reasons)
        if not any(sib in p and "does not model" in p for p in problems):
            print(f"FAIL: --self-test — {sib} was not refused as an unmodelled "
                  f"transform: {problems}.")
            print("      A computed sentinel leaves the scanner unable to say "
                  "where in the")
            print("      template the hole lands, which is the reconstruction's "
                  "question.")
            return 1

    # (25b-iii) ...and the CONTRACT itself, asked directly.  Through
    #           `violations` the base test is invisible: a `.replace` onto an
    #           undetermined base has that base yielded as an assembly of its
    #           own, so the file is refused either way and no fixture separates
    #           "the outer substitution is canonical" from "it is not".  A
    #           condition no case can reach is indistinguishable from a wrong
    #           one, so this reads the predicate.
    for expr, expected, what in (
            ('T.replace("@X@", f())', True,
             "a determined named template with a computed value"),
            ('T.replace("@X@", "a").replace("@Y@", f())', True,
             "a CHAIN of substitutions onto one determined template"),
            ('(T + g()).replace("@X@", "v")', False,
             "a base that is itself a concatenation with a hole"),
            ('T + g()', False,
             "a concatenation, which substitutes into nothing")):
        tree = ast.parse(
            _CONTRACT_SHAPE_TEMPLATE.replace("@EXPRESSION@", expr))
        consts = _module_string_bindings(tree)
        got = _substitution_into_determined_text(tree.body[-1].value, consts)
        if got is not expected:
            print(f"FAIL: --self-test — the substitution contract answered {got} "
                  f"for {what}; a probe's Lean source must be ONE text this "
                  f"scanner has read, with data substituted into it.")
            return 1

    # (25c) The CONTROL: the canonical spelling -- a determined named template
    #       with a DATA value substituted into it -- is read, not refused.  It is
    #       what all four of this tree's real probes are, and what its sixteen
    #       live marker-bearing holed assemblies are, so a refusal that fires
    #       here refuses the tree.  It must also RECORD the constructor the
    #       template spells, since reading it and recording nothing would leave
    #       (25b)'s hole open in its easiest form.
    with tempfile.TemporaryDirectory() as root:
        can = "scripts/canonical_substitution_gate.py"
        _fixture(root, {**base, can: _FIXTURE_CANONICAL_SUBSTITUTION})
        found = _capture_fixture(root)
        # The located SUBJECT is the named template, not the assignment that
        # substitutes into it -- the same key `_FIXTURE_SENTINEL_TEMPLATE` is
        # reported under, and the reason the constructor must be recorded THERE.
        key = f"{can}::TEMPLATE"
        if found.get(key) != {"opaqueInfo": 1}:
            print("FAIL: --self-test — the canonical spelling (a determined "
                  f"template with a data substitution) recorded {found.get(key)} "
                  "rather than the constructor it spells.")
            print("      Every real probe in this tree is that shape, so a "
                  "refusal or a zero here is a gate that refuses the tree.")
            return 1

    # (26) The DETERMINED half, and the *reconstructed* rather than refused outcome:
    #      the substituted value is a literal, so the probe the program builds is a
    #      string this scanner can read and the constructor it decides is recorded
    #      under the enclosing declaration.  Refusing it would be the wrong remedy,
    #      and reading it while recording nothing would leave the reported hole open
    #      in its easiest form -- so this case is an EQUALITY over both subjects.
    with tempfile.TemporaryDirectory() as root:
        det = "scripts/splice_determined_gate.py"
        _fixture(root, {**base, det: _FIXTURE_SPLICED_DETERMINED})
        got = {k: v for k, v in _capture_fixture(root).items()
               if k.startswith(det)}
        expected = {det + "::<inline in build>": {"opaqueInfo": 1}}
        if got != expected:
            print("FAIL: --self-test — a determined substitution was not read:")
            print(f"      {got}, expected {expected}.  The template's own text")
            print("      decides nothing; the string it builds decides `opaqueInfo`.")
            return 1

    # (27) A transform this scanner does not model, applied to determined probe text,
    #      is refused under its own reason: its result is that text mangled, which no
    #      hole describes.  The CONTROL is case (21)'s `", ".join(names)` -- the same
    #      shape applied to text that is not a probe is an ordinary value fragment
    #      and is read -- so the question is asked of what the form is applied TO
    #      rather than of the method name, which is what keeps the recognised set
    #      from having to be complete.
    with tempfile.TemporaryDirectory() as root:
        mng = "scripts/mangled_gate.py"
        _fixture(root, {**base, mng: _FIXTURE_UNMODELLED_TRANSFORM})
        problems = violations(root, base_pin, base_reasons)
        if not any(mng in p and "does not model" in p for p in problems):
            print("FAIL: --self-test — an unmodelled transform of probe text was")
            print(f"      not refused: {problems}.  Its result is not the template")
            print("      with substitutions, so no partial reading of it is honest.")
            return 1

    # (28) The RESOLUTION residue, closed.  A template whose name is bound twice
    #      denotes no one text, so the substitution is read as applying to nothing
    #      and the splice refusal never sees the template -- the defect walks around
    #      (24) by rebinding the name.  Distinct from the duplicate-SUBJECT-KEY
    #      refusal in (23): these two probes have different keys, and what fails here
    #      is RESOLUTION rather than the counts adding.
    with tempfile.TemporaryDirectory() as root:
        amb = "scripts/ambiguous_gate.py"
        _fixture(root, {**base, amb: _FIXTURE_AMBIGUOUS_TEMPLATE_NAME})
        problems = violations(root, base_pin, base_reasons)
        if not any(amb in p and "denotes no one text" in p for p in problems):
            print("FAIL: --self-test — a template bound to an ambiguous name was")
            print(f"      not refused: {problems}.  Resolution failing silently is")
            print("      how the splice refusal is walked around.")
            return 1

    # (29) The WORD-BOUNDARY half of the completion test.  A constructor is counted
    #      as a whole word, so a neighbour spelling part of one INSIDE a longer
    #      identifier cannot complete a match: no substitution makes `xopaqueInfo` or
    #      `opaqueInformal` a word-bounded `opaqueInfo`.  Without this case the two
    #      guards carry no witness -- a mutation dropping them passed every other
    #      case -- and an unwitnessed condition is indistinguishable from a wrong
    #      one.  An EQUALITY, because the claim is that the template is READ, and two
    #      holes, so a mutation dropping one guard is caught by its own half.
    with tempfile.TemporaryDirectory() as root:
        bnd = "scripts/bounded_hole_gate.py"
        _fixture(root, {**base, bnd: _FIXTURE_BOUNDED_HOLE_NEIGHBOURS})
        got = {k: v for k, v in _capture_fixture(root).items()
               if k.startswith(bnd)}
        expected = {bnd + "::PROBE_TEMPLATE": {"defnInfo": 1}}
        if got != expected:
            print("FAIL: --self-test — a template whose hole neighbours spell part")
            print(f"      of a constructor inside a longer identifier was not read:")
            print(f"      {got}, expected {expected}.  `\\b` is what makes those")
            print("      neighbours unable to complete a match.")
            return 1

    # (30) The ASSIGNED half of case (26).  `embedded_lean` has two branches and both
    #      now ask the marker of the ASSEMBLED TEXT, because a template reached
    #      through its NAME puts the marker in no literal fragment of the expression
    #      that substitutes into it.  Under the superseded fragment-only test this
    #      probe lost its assignment's name and was reported under its enclosing
    #      scope, so the case is an EQUALITY over the KEY as much as the count.
    with tempfile.TemporaryDirectory() as root:
        asg = "scripts/assigned_substitution_gate.py"
        _fixture(root, {**base, asg: _FIXTURE_ASSIGNED_SUBSTITUTION})
        got = {k: v for k, v in _capture_fixture(root).items()
               if k.startswith(asg)}
        expected = {asg + "::PROBE": {"ctorInfo": 1}}
        if got != expected:
            print("FAIL: --self-test — an assigned determined substitution was not")
            print(f"      read under its own name: {got}, expected {expected}.")
            print("      The marker is in the template, not in the fragments.")
            return 1

    # (31) ...and the other direction of resolution: an ambiguous name that is NOT
    #      probe text, reached by an assembly whose marker comes from a literal.
    #      Resolving it to either binding would read the probe over text the program
    #      may never build, so it resolves to nothing and the assembly is refused.
    #      Without this the "bound once" condition carries no witness at all -- the
    #      ambiguous-PROBE refusal of case (28) fires first for every name that IS
    #      probe text, so a mutation taking the first binding passed every case.
    with tempfile.TemporaryDirectory() as root:
        afr = "scripts/ambiguous_fragment_gate.py"
        _fixture(root, {**base, afr: _FIXTURE_AMBIGUOUS_FRAGMENT})
        problems = violations(root, base_pin, base_reasons)
        if not any(afr in p and "refuses to read partially" in p
                   for p in problems):
            print("FAIL: --self-test — an assembly over an ambiguous fragment name")
            print(f"      was not refused: {problems}.  Resolving it to either")
            print("      binding reads the probe over text it may never build.")
            return 1

    # (32) The FILE-level prefilter, which is a DIFFERENT question from the
    #      value-level signal and was asked with the same predicate.  Modelled on
    #      the two real gates this found: the literal OPENS on the assignment line,
    #      so no line of the raw source begins with the import, and the probe names
    #      no constructor at all, so the widened locator does not admit the file
    #      either.  Under the anchored reading `embedded_lean` returned before
    #      parsing and every probe in the file was outside the inventory, with the
    #      gate reporting the tree clean.  The located VALUE is anchored at its own
    #      start, so nothing about the signal needed weakening -- only the prefilter
    #      needed widening, and the assertion is LOCATION rather than a count,
    #      because a probe naming no constructor has none.
    opened = "scripts/opened_literal_gate.py"
    located = embedded_lean(opened, _FIXTURE_INLINE_OPENED_LITERAL)
    if [name for name, _ in located] != ["PROBE"]:
        print("FAIL: --self-test — a probe whose literal opens on the assignment")
        print(f"      line was not located: {[n for n, _ in located]}.  The")
        print("      file-level prefilter must be WIDER than the value-level")
        print("      signal, or a whole file is skipped before it is parsed.")
        return 1

    # (33) The RESOLUTION residue reached by an extra HOP.  `ALIAS = PROBE` resolves
    #      to no literal, so the transform reads an unreadable base, its result
    #      carries no marker, and neither the splice nor the unreadable refusal sees
    #      it -- while the template is located carrying zero constructors.  TWO hops,
    #      so a fix closing only the direct alias fails here rather than in the next
    #      review round.
    with tempfile.TemporaryDirectory() as root:
        ali = "scripts/aliased_template_gate.py"
        _fixture(root, {**base, ali: _FIXTURE_ALIASED_TEMPLATE})
        problems = violations(root, base_pin, base_reasons)
        if not any(ali in p and "resolves to no literal" in p for p in problems):
            print("FAIL: --self-test — a transform through an ALIAS of a probe")
            print(f"      name was not refused: {problems}.  The template is then")
            print("      counted with the constructors it does not decide.")
            return 1

    # (34) ...and its control, which is what keeps (33) from rejecting correct code.
    #      A probe passed on by name with no assembly reading it hides nothing, so it
    #      must be located and counted exactly as it would be without the binding.
    #      A mutation dropping the `reached` condition refuses this and passes (33).
    with tempfile.TemporaryDirectory() as root:
        thru = "scripts/aliased_passthrough_gate.py"
        _fixture(root, {**base, thru: _FIXTURE_ALIASED_PASSTHROUGH})
        got = {k: v for k, v in _capture_fixture(root).items()
               if k.startswith(thru)}
        expected = {thru + "::PROBE": {"defnInfo": 1}}
        if got != expected:
            print("FAIL: --self-test — a probe merely passed on by name was not")
            print(f"      read under its own name: {got}, expected {expected}.")
            print("      Refusing a pass-through rejects correct code.")
            return 1

    # (35) PR #897's review, `v0.35.142`: the prefilter gated the PARSE, and no
    #      raw-text test can be wider than "the AST reconstructs a probe".  A probe
    #      whose markers are SPLIT across fragments carries neither a complete
    #      `import SeLe4n` nor a complete constructor in its source, so both signals
    #      were false and the file was skipped before it was parsed -- an asker
    #      outside the inventory with the gate reporting the tree clean.  The
    #      assertion is that the new subject is REPORTED, because the fragments are
    #      all literals and the assembly reads rather than refuses.
    with tempfile.TemporaryDirectory() as root:
        spl = "scripts/split_marker_gate.py"
        _fixture(root, {**base, spl: _FIXTURE_SPLIT_MARKER_PROBE})
        problems = violations(root, base_pin, base_reasons)
        if not any(spl in p and "not a recorded asker" in p for p in problems):
            print("FAIL: --self-test — a probe whose markers are SPLIT across")
            print(f"      fragments was not seen: {problems}.  The file-level")
            print("      prefilter must not gate the parse, or a reassembled")
            print("      probe is outside the inventory with the gate green.")
            return 1

    # (36) ...and the plain-name call that BUILDS a probe, which
    #      `_string_assembly_shapes` deliberately does not treat as an assembly.
    #      The literal is then located as an inline probe -- marker accounted for,
    #      constructor count zero -- while the text the program runs decides
    #      `.opaqueInfo`.  Invisible in both directions at once, which is what makes
    #      a domain miss unfindable by reading a failure.
    with tempfile.TemporaryDirectory() as root:
        bld = "scripts/call_built_gate.py"
        _fixture(root, {**base, bld: _FIXTURE_CALL_BUILT_PROBE})
        problems = violations(root, base_pin, base_reasons)
        if not any(bld in p and "refuses to read partially" in p
                   for p in problems):
            print("FAIL: --self-test — a probe BUILT by a plain-name call was not")
            print(f"      refused: {problems}.  Its located literal is not the")
            print("      text the call builds, so its constructor count is zero")
            print("      against a probe that decides the question.")
            return 1

    # (37) ...and its CONTROL, which is what keeps (36) from refusing this tree's own
    #      inline-probe idiom.  The same shape with the call's result UNUSED is a
    #      probe handed straight to a runner, and it must be READ under its enclosing
    #      declaration.  A mutation dropping the result-used condition refuses this
    #      and passes (36).
    with tempfile.TemporaryDirectory() as root:
        run = "scripts/call_consumed_gate.py"
        _fixture(root, {**base, run: _FIXTURE_CALL_CONSUMED_PROBE})
        got = {k: v for k, v in _capture_fixture(root).items()
               if k.startswith(run)}
        if list(got.values()) != [{"opaqueInfo": 1}]:
            print("FAIL: --self-test — a probe handed straight to a runner was not")
            print(f"      read: {got}.  Refusing it rejects correct code, and the")
            print("      refusal in (36) is about the call's RESULT being used.")
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
          f"the same non-assignment position is not; a `.format`, `%` or "
          f"interpolating-f-string assembly is REFUSED rather than joined while a "
          f"literal f-string and a `@SENTINEL@` template consumed by `.replace` "
          f"are read; two probes binding one local name in two scopes are two "
          f"subjects while one name rebound at a single scope is refused; and a "
          f"template that SPLICES a constructor -- by `.replace`, `.format`, `%` or "
          f"concatenation -- is refused, as is an unmodelled transform of probe text "
          f"and a template whose name is bound twice, while a substitution whose "
          f"value is a literal is RECONSTRUCTED and its constructor recorded; a "
          f"probe whose markers are SPLIT across fragments is seen (the file-level "
          f"prefilter no longer gates the PARSE) and one BUILT by a plain-name call "
          f"is refused while the same shape with the call's result unused is read; "
          f"the live tree is clean at {len(found)} subject(s).")
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
