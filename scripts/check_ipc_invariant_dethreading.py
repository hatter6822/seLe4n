#!/usr/bin/env python3
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
"""WS-RR RR3.1 -- measure `ipcInvariantFull` de-threading, over the code view.

A `*_preserves_ipcInvariantFull` theorem that *binds a conjunct applied to its
own post-state* proves "**if** the post-state already satisfies the conjunct,
the transition is fine" -- not that the transition establishes it.  Threading
one conjunct that way makes the whole bundle conditional, and a bundle read as
an unconditional post-state guarantee is exactly the false-assurance shape
`CLAUDE.md`'s standing constraint warns about.

Ten conjuncts were de-threaded by earlier slices of WS-DT, each with a
canonical primed binder (`hQNBC'`, `hPRR'`, ...), so "de-threaded" could be
checked by grepping the binder name to zero.  The two that remained --
`blockedThreadsPendingMessageConsistent` and `replyCallerLinkageReciprocal` --
have **no canonical binder name**: they appear as `hInv`, `hRecip`, `hWtpmn`
and bare `h` depending on the bundle.  A name-based check would therefore
report success while measuring nothing, which is the failure shape of the
tier-4 gates that scored a skip as a pass.  This gate exists so the criterion
is measured rather than assumed.

**Everything it matches is derived, never enumerated.**  A hand-written list
cannot see the conjunct, the bundle or the transition that does not exist yet,
so the gate would go quiet exactly when something new is added:

* the **conjunct set** is read out of `def ipcInvariantFull` in
  `SeLe4n/Kernel/IPC/Invariant/Defs.lean` and closed under definitional
  expansion, so `replyCallerLinkage`'s two clause predicates
  (`replyCallerLinkageReciprocal`, `blockedOnReplyHasReplyObject`) are found
  by unfolding rather than by being listed;
* the **bundle family** is every declaration whose name contains
  `_preserves_ipcInvariantFull` or `_establishes_ipcInvariantFull`, wherever it
  lives -- both verbs conclude an `ipcInvariantFull`-family proposition of a
  transition's result, so both are where a threaded conjunct would hide;
* the **pre-state** of a bundle is the state its own `ipcInvariantFull`-family
  hypothesis is applied to, and *every other* state a conjunct is applied to is
  a finding.  Deriving the pre-state rather than the post-state is what makes
  the check fail **closed**: an intermediate state, a `.1` projection, a second
  post-state binder under a different name -- none of them has to be
  anticipated to be reported.  The degenerate maximal case -- the *whole*
  invariant hypothesised of the conclusion's own state, which makes every
  per-conjunct comparison succeed while the theorem proves nothing -- is its
  own check (`no_conclusion_state_hypothesis`), because the pre-state list
  cannot both admit a form and police that form's application.

A presence check is not a relation check.  The property here is a *relation*
between a binder's argument and the theorem's own pre-state, so the argument is
resolved to a balanced, whitespace-normalised expression and compared against
that pre-state, rather than a conjunct name being searched for anywhere in the
signature.  See `CLAUDE.md`, "A presence check is not a relation check"; add a
check here only with a negative case that KEEPS its token and breaks only the
relation.

Gates read code, prose reads prose: every Lean source is read through
`lean_code_view.strip`, the repository's one Lean stripper, so a docstring that
names a conjunct beside `st'` while explaining this rule neither satisfies nor
trips a check.

Usage:
    check_ipc_invariant_dethreading.py              # scan the repository
    check_ipc_invariant_dethreading.py --report     # print the full census
    check_ipc_invariant_dethreading.py --self-test  # prove the gate bites

Exits 0 when clean, 1 on any violation or self-test failure.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lean_code_view  # noqa: E402  (path set up immediately above)

DEFS_MODULE = "SeLe4n/Kernel/IPC/Invariant/Defs.lean"
# Two verbs, one family: `_preserves_` theorems carry the invariant across a
# transition, `_establishes_` theorems produce it where the pre-state carries
# only the relaxed form (the composite reply chain).  Both conclude an
# `ipcInvariantFull`-family proposition of a transition's result, so both are
# exactly where a threaded conjunct would hide -- a marker that stopped at
# `preserves` went quiet the day the first `establishes` theorem landed.
BUNDLE_MARKERS = ("_preserves_ipcInvariantFull", "_establishes_ipcInvariantFull")
ROOT_INVARIANT = "ipcInvariantFull"

# The bundle's own hypothesis names the pre-state.  These are the forms a
# bundle states it in: the global invariant, its SMP lift, the structural core
# the reply mutators sequence through, the per-core view, and -- for the
# composite reply chain, whose pre-state is mid-reply -- the bundle relaxed at
# the woken caller.  The `no_conclusion_state_hypothesis` check is what keeps
# this list from becoming a loophole: a bundle hypothesising any of these forms
# of its own conclusion's state fails outright, so listing a form here can
# never launder a post-state assumption into a pre-state.
PRE_STATE_PREDICATES = (
    "ipcInvariantFull_smp",
    "ipcInvariantFull_perCore",
    "ipcInvariantFullExceptDonationOwner",
    "ipcInvariantFull",
    "ipcInvariantCore",
)

# The D8 payoff theorems.  Named here because their *absence* is the finding:
# a de-threaded bundle family with no top-level consumer proves nothing about
# the live kernel, which is the gap RR3.15/RR3.16 close.
#
# `dispatchSyscall` is the tree's name for the top-level dispatcher; the plan
# originally wrote `syscallDispatch`, which names nothing.  The theorem is named
# for the function it is about.
PAYOFF_THEOREMS = (
    "dispatchWithCap_preserves_ipcInvariantFull",
    "dispatchSyscall_preserves_ipcInvariantFull",
)

# Registered residuals: payoff theorems the project has sized and deferred with
# an explicit closure target.  Read from the file rather than hard-coded so the
# registration and its reason live where a reader looks for them, and checked in
# BOTH directions (see `payoff_status`) so it cannot rot into a silent
# exemption.
#
# It lives under `docs/planning/` rather than beside this script because it is a
# register of deferred work, which is prose: its closure targets are workstream
# IDs, and `check_identifier_naming.py` reads a `.txt` outside `docs/` as code.
# Putting it where the debt register lives keeps both gates honest instead of
# baselining a new exemption into the naming one.
PENDING_FILE = "docs/planning/ipc_dethreading_pending.txt"

CHECKS = (
    "conjuncts_derived",
    "family_nonempty",
    "no_post_state_binding",
    "no_conclusion_state_hypothesis",
    "payoff_theorems",
)

_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|partial\s+|noncomputable\s+|unsafe\s+"
    r"|local\s+|scoped\s+)*"
    r"(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.!?]*)",
    re.MULTILINE,
)

_IDENT_CHARS = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'!?."

_OPEN = "([{"
_CLOSE = ")]}"


def _normalise(text: str) -> str:
    """Whitespace-normalise an expression so `st'` and `st '` cannot differ."""
    return re.sub(r"\s+", " ", text).strip()


def lean_sources(root: str) -> list[str]:
    """Every tracked `.lean` file, or every `.lean` file when git is absent.

    Tracked-file listing is the honest set for a gate that runs pre-commit;
    the filesystem walk is the fallback the self-test's temporary trees use.
    """
    try:
        listed = subprocess.run(
            ["git", "-C", root, "ls-files", "*.lean"],
            capture_output=True,
            text=True,
            check=True,
        ).stdout.split()
        if listed:
            return sorted(listed)
    except (OSError, subprocess.CalledProcessError):
        pass
    found = []
    for base, _dirs, files in os.walk(root):
        for name in files:
            if name.endswith(".lean"):
                found.append(
                    os.path.relpath(os.path.join(base, name), root)
                )
    return sorted(found)


def code_view(root: str, relative: str) -> str:
    """The comment-free view of one Lean source."""
    with open(os.path.join(root, relative), encoding="utf-8") as handle:
        return lean_code_view.strip(handle.read())


def balanced_span(text: str, start: int) -> int | None:
    """End offset of the bracketed group opening at `start`, or None."""
    if start >= len(text) or text[start] not in _OPEN:
        return None
    depth = 0
    index = start
    while index < len(text):
        char = text[index]
        if char in _OPEN:
            depth += 1
        elif char in _CLOSE:
            depth -= 1
            if depth == 0:
                return index + 1
        index += 1
    return None


def first_argument(text: str, start: int) -> str | None:
    """The first explicit argument of an application beginning at `start`.

    A bracketed group (with any `.1` / `.2` projections that follow it) or a
    bare identifier.  Returning the *projection-extended* form matters: a
    bundle whose post-state is `(f a st).1` binds the conjunct on exactly that
    expression, and truncating at the closing paren would compare `(f a st)`
    against `(f a st).1` and report a clean signature.
    """
    index = start
    while index < len(text) and text[index] in " \n\t":
        index += 1
    if index >= len(text):
        return None
    if text[index] in _OPEN:
        end = balanced_span(text, index)
        if end is None:
            return None
        projection = re.match(r"(?:\.\d+)*", text[end:])
        return text[index:end] + projection.group(0)
    identifier = re.match(r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.\d+)*", text[index:])
    return identifier.group(0) if identifier else None


def signature_end(text: str, start: int) -> int:
    """Offset of the `:=` that closes a declaration's signature.

    At bracket depth zero, so a `:=` inside a structure-instance binder
    (`{ msg with capsGranted := true }`) -- which several cross-core bundles
    carry in their conclusion -- does not truncate the signature.
    """
    depth = 0
    index = start
    while index < len(text):
        char = text[index]
        if char in _OPEN:
            depth += 1
        elif char in _CLOSE:
            depth -= 1
        elif (
            char == ":"
            and depth == 0
            and index + 1 < len(text)
            and text[index + 1] == "="
        ):
            return index
        index += 1
    return len(text)


def split_conclusion(signature: str) -> tuple[str, str]:
    """Split a signature into (binders, conclusion) at the last depth-0 colon."""
    depth = 0
    cut = None
    index = 0
    while index < len(signature):
        char = signature[index]
        if char in _OPEN:
            depth += 1
        elif char in _CLOSE:
            depth -= 1
        elif char == ":" and depth == 0:
            # `:=` never appears here (the signature was cut at it), but a
            # `::` or a type ascription arrow could; a lone colon is the
            # binder/conclusion separator.
            cut = index
        index += 1
    if cut is None:
        return signature, ""
    return signature[:cut], signature[cut + 1 :]


def split_conjunction(body: str) -> list[str]:
    """Split a `Prop` body on `∧` at bracket depth zero."""
    parts, current, depth = [], [], 0
    index = 0
    while index < len(body):
        char = body[index]
        if char in _OPEN:
            depth += 1
        elif char in _CLOSE:
            depth -= 1
        if char == "∧" and depth == 0:
            parts.append("".join(current))
            current = []
        else:
            current.append(char)
        index += 1
    parts.append("".join(current))
    return parts


def state_predicate_bodies(root: str, sources: list[str]) -> dict[str, str]:
    """Every `def NAME (st : SystemState) : Prop := ...` body in the tree.

    Collected tree-wide rather than from the definition module alone: a clause
    predicate that a bundle threads is a conjunct's half wherever it is
    defined, and a body map restricted to one file would silently stop
    expanding the day one moved.
    """
    bodies: dict[str, str] = {}
    pattern = re.compile(
        r"^def\s+([A-Za-z_][A-Za-z0-9_'!?]*)\s*\(\s*(st|s)\s*:\s*SystemState\s*\)"
        r"\s*:\s*Prop\s*:=",
        re.MULTILINE,
    )
    stop = re.compile(
        r"^(?:@\[|/-|def|theorem|lemma|abbrev|structure|inductive|instance|end|namespace|open)\b",
        re.MULTILINE,
    )
    for relative in sources:
        source = code_view(root, relative)
        for match in pattern.finditer(source):
            tail = source[match.end() :]
            cut = stop.search(tail)
            bodies[match.group(1)] = (tail[: cut.start()] if cut else tail).replace(
                match.group(2), "st"
            )
    return bodies


def derive_conjuncts(bodies: dict[str, str]) -> set[str]:
    """The conjuncts of `ipcInvariantFull`, closed under definitional unfolding.

    Read out of the definition rather than listed, so a twenty-first conjunct
    is measured the day it is added.  The body is split on `∧` at bracket
    depth zero and a part counts only when it is exactly one predicate applied
    to the definition's own state binder -- so the expansion is the definition,
    not a token scrape of it.

    The closure step is what finds `replyCallerLinkage`'s two clause
    predicates: the bundles thread `replyCallerLinkageReciprocal`, which is not
    itself a conjunct of `ipcInvariantFull` but is half of one, and a gate that
    stopped at the top-level names would score those bundles clean.  A conjunct
    whose body is not a conjunction (`ipcInvariant`'s `∀`-formula, say)
    contributes no sub-predicates, which is correct: it has none to thread.
    """
    if ROOT_INVARIANT not in bodies:
        return set()

    applied = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_'!?]*)\s+st\s*$")

    def sub_predicates(body: str) -> set[str]:
        found = set()
        for part in split_conjunction(body):
            hit = applied.match(part)
            if hit:
                found.add(hit.group(1))
        return found

    conjuncts = sub_predicates(bodies[ROOT_INVARIANT])
    frontier = set(conjuncts)
    while frontier:
        name = frontier.pop()
        if name not in bodies:
            continue
        for nested in sub_predicates(bodies[name]):
            if nested not in conjuncts:
                conjuncts.add(nested)
                frontier.add(nested)
    conjuncts.discard(ROOT_INVARIANT)
    return conjuncts


class Bundle:
    """One `*_preserves_ipcInvariantFull` statement, parsed from the code view."""

    def __init__(self, path: str, line: int, name: str, binders: str, conclusion: str):
        self.path = path
        self.line = line
        self.name = name
        self.binders = binders
        self.conclusion = _normalise(conclusion)

    def pre_states(self) -> set[str]:
        """The states this bundle's own invariant hypotheses are applied to."""
        states = set()
        for predicate in PRE_STATE_PREDICATES:
            for hit in re.finditer(
                r"(?<![A-Za-z0-9_'.])" + re.escape(predicate) + r"(?![A-Za-z0-9_'])",
                self.binders,
            ):
                argument = first_argument(self.binders, hit.end())
                if argument:
                    states.add(_normalise(argument))
        return states

    def conclusion_state(self) -> str | None:
        """The state this bundle's conclusion applies its invariant form to.

        `None` when no `ipcInvariantFull`-family predicate application is found
        in the conclusion -- possible only for a declaration that carries the
        family marker in its name without concluding a family proposition, which
        the tree does not contain; the threaded-conjunct check still covers such
        a declaration's binders in full.
        """
        for predicate in PRE_STATE_PREDICATES:
            hit = re.search(
                r"(?<![A-Za-z0-9_'.])" + re.escape(predicate) + r"(?![A-Za-z0-9_'])",
                self.conclusion,
            )
            if hit:
                argument = first_argument(self.conclusion, hit.end())
                if argument:
                    return _normalise(argument)
        return None

    def assumes_conclusion_state(self) -> str | None:
        """The conclusion state, when a whole-bundle hypothesis binds it.

        This is the degenerate maximal threading: a bundle that hypothesises
        `ipcInvariantFull st'` of its own conclusion's `st'` is scored clean by
        the per-conjunct check -- every conjunct binding on `st'` compares equal
        to a "pre-state" -- while proving nothing at all.  The two checks close
        each other's gap: the pre-state list stays usable because this one
        rejects a member of it applied to the conclusion's state.
        """
        state = self.conclusion_state()
        if state is not None and state in self.pre_states():
            return state
        return None

    def threaded(self, conjuncts: set[str]) -> list[tuple[str, str]]:
        """(conjunct, state) for every conjunct bound on a non-pre-state."""
        pre = self.pre_states()
        findings = []
        for conjunct in sorted(conjuncts):
            for hit in re.finditer(
                r"(?<![A-Za-z0-9_'.])" + re.escape(conjunct) + r"(?![A-Za-z0-9_'])",
                self.binders,
            ):
                argument = first_argument(self.binders, hit.end())
                if argument is None:
                    continue
                state = _normalise(argument)
                if state not in pre:
                    findings.append((conjunct, state))
        return findings


def collect_bundles(root: str, sources: list[str]) -> list[Bundle]:
    """Every declaration in the `ipcInvariantFull` bundle family."""
    bundles = []
    for relative in sources:
        source = code_view(root, relative)
        for match in _DECL_RE.finditer(source):
            name = match.group(1)
            if not any(marker in name for marker in BUNDLE_MARKERS):
                continue
            end = signature_end(source, match.end())
            binders, conclusion = split_conclusion(source[match.end() : end])
            line = source.count("\n", 0, match.start()) + 1
            bundles.append(Bundle(relative, line, name, binders, conclusion))
    return bundles


def declared_names(root: str, sources: list[str]) -> set[str]:
    """Every theorem/lemma name declared anywhere in the tree's code view."""
    names = set()
    for relative in sources:
        for match in _DECL_RE.finditer(code_view(root, relative)):
            names.add(match.group(1))
    return names


def read_pending(root: str) -> dict[str, tuple[str, str]]:
    """The registered residuals: name -> (closure target, reason).

    A malformed line is a hard error rather than a skipped one: a registration
    the reader cannot parse is a registration nobody is holding to a target.
    """
    path = os.path.join(root, PENDING_FILE)
    pending: dict[str, tuple[str, str]] = {}
    if not os.path.isfile(path):
        return pending
    with open(path, encoding="utf-8") as handle:
        for lineno, raw in enumerate(handle, start=1):
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            parts = [piece.strip() for piece in line.split("|", 2)]
            if len(parts) != 3 or not all(parts):
                raise ValueError(
                    f"{PENDING_FILE}:{lineno}: expected "
                    f"`<theorem> | <closure target> | <reason>`"
                )
            pending[parts[0]] = (parts[1], parts[2])
    return pending


def payoff_status(names: set[str], pending: dict[str, tuple[str, str]]) -> list[str]:
    """Violations from the payoff check, registration included.

    Four cases, and three of them are failures.  A registered name whose theorem
    has since landed is *stale* and fails, because a registration that outlives
    its residual is how an exemption list stops describing the tree.  A
    registration for something outside the payoff set is *dangling* and fails,
    for the same reason in the other direction.
    """
    problems: list[str] = []
    for payoff in PAYOFF_THEOREMS:
        registered = payoff in pending
        present = payoff in names
        if present and registered:
            problems.append(
                f"payoff_theorems: `{payoff}` is declared but still registered as "
                f"pending in {PENDING_FILE}; delete the registration"
            )
        elif not present and not registered:
            problems.append(
                f"payoff_theorems: `{payoff}` is not declared anywhere in the "
                f"tree and is not registered as pending in {PENDING_FILE}; the "
                f"de-threaded bundles have no top-level consumer"
            )
    for name in sorted(pending):
        if name not in PAYOFF_THEOREMS:
            problems.append(
                f"payoff_theorems: {PENDING_FILE} registers `{name}`, which is "
                f"not one of this gate's payoff theorems"
            )
    return problems


def run_checks(root: str) -> list[str]:
    """Every violation, as a human-readable line.  Empty means clean."""
    problems: list[str] = []
    sources = lean_sources(root)

    defs_path = os.path.join(root, DEFS_MODULE)
    if not os.path.isfile(defs_path):
        return [f"conjuncts_derived: {DEFS_MODULE} is missing"]
    conjuncts = derive_conjuncts(state_predicate_bodies(root, sources))
    if not conjuncts:
        # A silently empty conjunct set would make `no_post_state_binding`
        # vacuous -- the gate would report PASS having measured nothing.
        problems.append(
            f"conjuncts_derived: no conjuncts derived from `def {ROOT_INVARIANT}` "
            f"in {DEFS_MODULE}; the de-threading check would be vacuous"
        )
        return problems

    bundles = collect_bundles(root, sources)
    if not bundles:
        markers = " / ".join(f"`*{marker}*`" for marker in BUNDLE_MARKERS)
        problems.append(
            f"family_nonempty: no declaration matching {markers} found; "
            f"the de-threading check would be vacuous"
        )
        return problems

    for bundle in sorted(bundles, key=lambda b: (b.path, b.line)):
        assumed = bundle.assumes_conclusion_state()
        if assumed is not None:
            # Reported instead of the per-conjunct findings, which would all be
            # suppressed by exactly this hypothesis and so add nothing.
            problems.append(
                f"no_conclusion_state_hypothesis: {bundle.path}:{bundle.line}: "
                f"`{bundle.name}` hypothesises an `ipcInvariantFull`-family "
                f"predicate of `{assumed}`, its own conclusion's state -- the "
                f"whole-bundle form of threading"
            )
            continue
        for conjunct, state in bundle.threaded(conjuncts):
            problems.append(
                f"no_post_state_binding: {bundle.path}:{bundle.line}: "
                f"`{bundle.name}` binds `{conjunct}` on `{state}`, which is not "
                f"its pre-state {sorted(bundle.pre_states()) or '(none found)'}"
            )

    names = declared_names(root, sources)
    try:
        pending = read_pending(root)
    except ValueError as err:
        problems.append(f"payoff_theorems: {err}")
    else:
        problems.extend(payoff_status(names, pending))

    return problems


def report(root: str) -> int:
    """Print the census: bundles, conjuncts, and every post-state binding."""
    sources = lean_sources(root)
    conjuncts = derive_conjuncts(state_predicate_bodies(root, sources))
    bundles = collect_bundles(root, sources)
    print(f"conjuncts derived from `{ROOT_INVARIANT}`: {len(conjuncts)}")
    for conjunct in sorted(conjuncts):
        print(f"  - {conjunct}")
    markers = " / ".join(f"`*{marker}*`" for marker in BUNDLE_MARKERS)
    print(f"\n{markers} statements: {len(bundles)}")
    tally: dict[str, int] = {}
    threaded_bundles = 0
    for bundle in sorted(bundles, key=lambda b: (b.path, b.line)):
        findings = bundle.threaded(conjuncts)
        if not findings:
            continue
        threaded_bundles += 1
        print(f"\n  {bundle.path}:{bundle.line}  {bundle.name}")
        for conjunct, state in findings:
            print(f"      {conjunct}  on  {state}")
            tally[conjunct] = tally.get(conjunct, 0) + 1
    print(
        f"\nthreaded statements: {threaded_bundles} / {len(bundles)}; "
        f"post-state bindings: {sum(tally.values())}"
    )
    for conjunct, count in sorted(tally.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"  {count:4d}  {conjunct}")
    names = declared_names(root, sources)
    try:
        pending = read_pending(root)
    except ValueError as err:
        print(f"\n[FAIL] {err}")
        return 1
    print("\npayoff theorems:")
    for payoff in PAYOFF_THEOREMS:
        if payoff in names:
            print(f"  present    {payoff}")
        elif payoff in pending:
            target, reason = pending[payoff]
            print(f"  PENDING    {payoff}  (closure target: {target})")
            print(f"             {reason}")
        else:
            print(f"  MISSING    {payoff}")
    return 0


# ---------------------------------------------------------------------------
# The witness suite.
#
# Every case states which check it exercises and whether its mutation KEEPS the
# token the check searches for.  A suite made only of deletions certifies
# nothing about a relation, so the harness fails when a check has no
# token-preserving case -- enforced here rather than asserted in a comment.
# ---------------------------------------------------------------------------

CLEAN_DEFS = '''/-- Docstring: blockedThreadsPendingMessageConsistent st' is prose here. -/
def replyCallerLinkageReciprocal (st : SystemState) : Prop :=
  True

def blockedOnReplyHasReplyObject (st : SystemState) : Prop :=
  True

def blockedThreadsPendingMessageConsistent (st : SystemState) : Prop :=
  True

def replyCallerLinkage (st : SystemState) : Prop :=
  replyCallerLinkageReciprocal st ∧ blockedOnReplyHasReplyObject st

def ipcInvariantFull (st : SystemState) : Prop :=
  blockedThreadsPendingMessageConsistent st ∧ replyCallerLinkage st
'''

CLEAN_BUNDLE = '''theorem endpointSendDual_preserves_ipcInvariantFull
    (st st' : SystemState)
    (hInv : ipcInvariantFull st)
    (hStep : endpointSendDual st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hInv hStep
'''

CLEAN_PAYOFF = '''theorem dispatchWithCap_preserves_ipcInvariantFull
    (st st' : SystemState) (hInv : ipcInvariantFull st) :
    ipcInvariantFull st' := by
  exact sample st st' hInv

theorem dispatchSyscall_preserves_ipcInvariantFull
    (st st' : SystemState) (hInv : ipcInvariantFull st) :
    ipcInvariantFull st' := by
  exact sample st st' hInv
'''


def _fixture() -> dict[str, str]:
    return {
        DEFS_MODULE: CLEAN_DEFS,
        "SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean": CLEAN_BUNDLE,
        "SeLe4n/Kernel/API.lean": CLEAN_PAYOFF,
    }


def _write_tree(root: str, files: dict[str, str]) -> None:
    for relative, content in files.items():
        path = os.path.join(root, relative)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as handle:
            handle.write(content)


class _Case:
    def __init__(self, label, files, expect, check=None, mutation="deleting"):
        assert check is None or check in CHECKS, check
        assert mutation in ("none", "deleting", "preserving"), mutation
        self.label = label
        self.files = files
        self.expect = expect
        self.check = check
        self.mutation = mutation


def self_test() -> int:
    cases: list[_Case] = []

    cases.append(_Case("clean tree", _fixture(), False, mutation="none"))

    # --- no_post_state_binding -------------------------------------------
    # Token-PRESERVING: the conjunct stays bound, on the post-state instead of
    # the pre-state.  A gate that searched for the conjunct anywhere in the
    # signature -- or for a `'`-suffixed binder name -- passes this.
    threaded = _fixture()
    threaded["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hAnything : blockedThreadsPendingMessageConsistent st')\n",
        )
    )
    cases.append(
        _Case(
            "conjunct bound on the post-state under a non-canonical binder name",
            threaded,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # Token-PRESERVING: a *clause* of a conjunct, which is not itself named in
    # `ipcInvariantFull` and is only found by unfolding the definition.
    clause = _fixture()
    clause["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (h : replyCallerLinkageReciprocal st')\n",
        )
    )
    cases.append(
        _Case(
            "clause predicate of a conjunct bound on the post-state",
            clause,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # Token-PRESERVING: the post-state is an application, not a variable, and
    # the binding is on the same `.1` projection the conclusion uses.
    projected = _fixture()
    projected["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        "theorem endpointSendDualOnCore_preserves_ipcInvariantFull\n"
        "    (st : SystemState) (c : CoreId)\n"
        "    (hInv : ipcInvariantFull st)\n"
        "    (h : blockedThreadsPendingMessageConsistent (endpointSendDualOnCore c st).1) :\n"
        "    ipcInvariantFull (endpointSendDualOnCore c st).1 := by\n"
        "  exact sample st c hInv h\n"
    )
    cases.append(
        _Case(
            "conjunct bound on a projected application post-state",
            projected,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # Token-PRESERVING: an INTERMEDIATE state, neither the pre-state nor the
    # conclusion's expression.  A conclusion-driven check scores this clean.
    intermediate = _fixture()
    intermediate["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        "theorem endpointCall_preserves_ipcInvariantFull\n"
        "    (st stMid st' : SystemState)\n"
        "    (hInv : ipcInvariantFull st)\n"
        "    (h : blockedThreadsPendingMessageConsistent stMid) :\n"
        "    ipcInvariantFull st' := by\n"
        "  exact sample st stMid st' hInv h\n"
    )
    cases.append(
        _Case(
            "conjunct bound on an intermediate state",
            intermediate,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # NOT a finding: a conjunct on the pre-state is the whole point.
    pre_only = _fixture()
    pre_only["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hPre : blockedThreadsPendingMessageConsistent st)\n",
        )
    )
    cases.append(
        _Case("conjunct bound on the pre-state is accepted", pre_only, False, mutation="none")
    )

    # NOT a finding: prose.  The docstring names the conjunct beside `st'`.
    prose = _fixture()
    prose["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        "/-- This bundle no longer takes `blockedThreadsPendingMessageConsistent st'`. -/\n"
        + CLEAN_BUNDLE
    )
    cases.append(
        _Case("a docstring naming the threaded form is not a finding", prose, False, mutation="none")
    )

    # NOT a finding: a structure-instance `:=` inside the conclusion must not
    # truncate the signature (several cross-core bundles carry one).
    with_update = _fixture()
    with_update["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        "theorem endpointCallWithCaps_preserves_ipcInvariantFull\n"
        "    (st : SystemState) (msg : IpcMessage)\n"
        "    (hInv : ipcInvariantFull st) :\n"
        "    ipcInvariantFull (endpointCall { msg with capsGranted := true } st).1 := by\n"
        "  exact sample st msg hInv\n"
    )
    cases.append(
        _Case(
            "a structure-instance `:=` in the conclusion does not truncate",
            with_update,
            False,
            mutation="none",
        )
    )

    # --- conjuncts_derived ------------------------------------------------
    # Token-PRESERVING: `ipcInvariantFull` is still defined and still names its
    # conjuncts -- but as a different arity, so the derivation finds nothing.
    # A gate that trusted an empty derivation would report PASS.
    renamed_state = _fixture()
    renamed_state[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def ipcInvariantFull (st : SystemState) : Prop :=",
        "def ipcInvariantFull (st : SystemState) (c : CoreId) : Prop :=",
    )
    cases.append(
        _Case(
            "conjunct derivation yields nothing (definition reshaped)",
            renamed_state,
            True,
            check="conjuncts_derived",
            mutation="preserving",
        )
    )

    missing_defs = _fixture()
    del missing_defs[DEFS_MODULE]
    cases.append(
        _Case("the definition module is missing", missing_defs, True, check="conjuncts_derived")
    )

    # --- family_nonempty --------------------------------------------------
    # Token-PRESERVING: the bundles are still there and still say
    # `ipcInvariantFull`, under a name the family marker no longer matches --
    # so a de-threading check driven by the name pattern measures nothing.
    renamed_family = _fixture()
    renamed_family["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "endpointSendDual_preserves_ipcInvariantFull",
            "endpointSendDual_maintains_theInvariant",
        )
    )
    renamed_family["SeLe4n/Kernel/API.lean"] = CLEAN_PAYOFF.replace(
        "_preserves_ipcInvariantFull", "_maintains_theInvariant"
    )
    cases.append(
        _Case(
            "the bundle family is renamed out from under the marker",
            renamed_family,
            True,
            check="family_nonempty",
            mutation="preserving",
        )
    )

    # --- no_post_state_binding, establishes family -----------------------
    # Token-PRESERVING: the threaded conjunct sits on a theorem whose verb is
    # `establishes` rather than `preserves`.  A marker that stopped at
    # `preserves` would score this tree clean while the composite reply-chain
    # payoffs threaded freely.
    establishes_threaded = _fixture()
    establishes_threaded["SeLe4n/Kernel/IPC/CrossCore/ReplyChain.lean"] = (
        "theorem replyChain_establishes_ipcInvariantFull\n"
        "    (st st' : SystemState)\n"
        "    (hInv : ipcInvariantFull st)\n"
        "    (hRecip : replyCallerLinkageReciprocal st')\n"
        "    (hStep : replyChain st = .ok ((), st')) :\n"
        "    ipcInvariantFull st' := by\n"
        "  exact sample st st' hInv hRecip hStep\n"
    )
    cases.append(
        _Case(
            "an establishes-form bundle threads a conjunct on its post-state",
            establishes_threaded,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # --- no_conclusion_state_hypothesis ----------------------------------
    # Token-PRESERVING: every token of a clean bundle survives, a genuine
    # pre-state hypothesis included; what is added is the whole invariant
    # hypothesised of the conclusion's own state.  The per-conjunct check is
    # blind to it by construction -- `st'` becomes a "pre-state", so every
    # conjunct bound on `st'` compares equal -- which is why this is its own
    # check rather than a case of that one.
    whole_bundle_threaded = _fixture()
    whole_bundle_threaded["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hInv' : ipcInvariantFull st')\n",
        ).replace("  exact sample st st' hInv hStep", "  exact hInv'")
    )
    cases.append(
        _Case(
            "the whole invariant is hypothesised of the conclusion's own state",
            whole_bundle_threaded,
            True,
            check="no_conclusion_state_hypothesis",
            mutation="preserving",
        )
    )

    # The relaxed pre-state form is a pre-state, not a finding: the composite
    # reply chain's establishers start from a mid-reply state that satisfies
    # only `ipcInvariantFullExceptDonationOwner`.  Accepted, not caught.
    except_pre_state = _fixture()
    except_pre_state["SeLe4n/Kernel/IPC/Invariant/DonationPreservation.lean"] = (
        "theorem applyReplyDonation_establishes_ipcInvariantFull_of_except\n"
        "    (st st' : SystemState) (woken : SeLe4n.ThreadId)\n"
        "    (hInv : ipcInvariantFullExceptDonationOwner st woken)\n"
        "    (hStep : applyReplyDonation st = .ok ((), st')) :\n"
        "    ipcInvariantFull st' := by\n"
        "  exact sample st st' woken hInv hStep\n"
    )
    cases.append(
        _Case(
            "the relaxed pre-state form is accepted as a pre-state",
            except_pre_state,
            False,
        )
    )

    # --- payoff_theorems --------------------------------------------------
    # Token-PRESERVING: the payoff theorem's NAME survives, as a comment and as
    # a reference inside another proof, while the declaration is gone.
    payoff_mentioned = _fixture()
    payoff_mentioned["SeLe4n/Kernel/API.lean"] = (
        "/-- See `dispatchSyscall_preserves_ipcInvariantFull` for the payoff. -/\n"
        + CLEAN_PAYOFF.split("theorem dispatchSyscall_preserves_ipcInvariantFull")[0]
        + "theorem otherName (st : SystemState) : True := by\n"
        "  exact dispatchSyscall_preserves_ipcInvariantFull st\n"
    )
    cases.append(
        _Case(
            "payoff theorem survives only as a mention and a reference",
            payoff_mentioned,
            True,
            check="payoff_theorems",
            mutation="preserving",
        )
    )

    # Token-PRESERVING: the payoff theorem IS declared, and the registration
    # naming it is still there.  Nothing is deleted; what breaks is the relation
    # between the register and the tree, and a registration that outlives its
    # residual is how an exemption list stops describing the tree.
    stale_registration = _fixture()
    stale_registration[PENDING_FILE] = (
        "dispatchWithCap_preserves_ipcInvariantFull | WS-RR RR3.15 | sized and deferred\n"
    )
    cases.append(
        _Case(
            "a registration outlives the theorem it defers",
            stale_registration,
            True,
            check="payoff_theorems",
            mutation="preserving",
        )
    )

    # Token-PRESERVING: a registration whose name is a real, plausible theorem
    # name -- but not one of this gate's payoff theorems, so it defers nothing
    # and would sit in the file unread.
    dangling_registration = _fixture()
    dangling_registration["SeLe4n/Kernel/API.lean"] = CLEAN_PAYOFF.split(
        "theorem dispatchSyscall_preserves_ipcInvariantFull"
    )[0]
    dangling_registration[PENDING_FILE] = (
        "dispatchSyscall_preserves_ipcInvariantFull | WS-RR RR3.16 | blocked\n"
        "endpointSendDual_preserves_ipcInvariantFull | WS-RR RR3.16 | not a payoff\n"
    )
    cases.append(
        _Case(
            "a registration names something outside the payoff set",
            dangling_registration,
            True,
            check="payoff_theorems",
            mutation="preserving",
        )
    )

    # Token-PRESERVING: the registration's three fields are all present but the
    # second delimiter is gone, so the reader cannot tell target from reason.  A
    # parser that skipped what it cannot split would hold nobody to anything.
    malformed_registration = _fixture()
    malformed_registration["SeLe4n/Kernel/API.lean"] = CLEAN_PAYOFF.split(
        "theorem dispatchSyscall_preserves_ipcInvariantFull"
    )[0]
    malformed_registration[PENDING_FILE] = (
        "dispatchSyscall_preserves_ipcInvariantFull | WS-RR RR3.16 sized and deferred\n"
    )
    cases.append(
        _Case(
            "a malformed registration line is a hard error, not a skip",
            malformed_registration,
            True,
            check="payoff_theorems",
            mutation="preserving",
        )
    )

    # The registration does its job: the theorem is absent and registered, so
    # the gate reports rather than fails.  Accepted, not caught.
    honest_registration = _fixture()
    honest_registration["SeLe4n/Kernel/API.lean"] = CLEAN_PAYOFF.split(
        "theorem dispatchSyscall_preserves_ipcInvariantFull"
    )[0]
    honest_registration[PENDING_FILE] = (
        "dispatchSyscall_preserves_ipcInvariantFull | WS-RR RR3.16 | sized and deferred\n"
    )
    cases.append(
        _Case("a registered residual is reported, not failed", honest_registration, False)
    )

    clean = _fixture()
    failures = 0
    for case in cases:
        if case.expect and case.files == clean:
            failures += 1
            print(f"[SELF-TEST FAIL] inert mutation, fixture unchanged: {case.label}")
            continue
        with tempfile.TemporaryDirectory() as tmp:
            _write_tree(tmp, case.files)
            problems = run_checks(tmp)
            reported = {problem.split(":", 1)[0] for problem in problems}
            wrong_check = (
                case.expect and case.check is not None and case.check not in reported
            )
            if bool(problems) != case.expect or wrong_check:
                failures += 1
                if wrong_check:
                    verb = f"reported {sorted(reported)} instead of `{case.check}` for"
                else:
                    verb = "missed" if case.expect else "false-positived on"
                print(f"[SELF-TEST FAIL] gate {verb}: {case.label}")
                for problem in problems:
                    print(f"                 reported: {problem}")
            else:
                state = "caught" if case.expect else "accepted"
                mark = " [preserving]" if case.mutation == "preserving" else ""
                print(f"[SELF-TEST OK]   {state}: {case.label}{mark}")

    covered = {
        case.check
        for case in cases
        if case.expect and case.mutation == "preserving" and case.check
    }
    for check in CHECKS:
        if check not in covered:
            failures += 1
            print(
                f"[SELF-TEST FAIL] check `{check}` has no token-preserving "
                f"negative case. Add one that keeps the token the check "
                f"searches for and breaks only its relation (CLAUDE.md, "
                f'"Test a gate by breaking the relation, not by deleting '
                f'the token").'
            )

    if failures:
        print(f"\n[FAIL] {failures} self-test case(s) failed")
        return 1
    print(
        f"\n[PASS] {len(cases)} self-test case(s); "
        f"{len(CHECKS)}/{len(CHECKS)} checks have a token-preserving case"
    )
    return 0


def main(argv: list[str]) -> int:
    root = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
    if "--self-test" in argv:
        return self_test()
    if "--report" in argv:
        return report(root)
    problems = run_checks(root)
    if problems:
        print("[FAIL] ipcInvariantFull de-threading (WS-RR RR3.1):")
        for problem in problems:
            print(f"  - {problem}")
        return 1
    sources = lean_sources(root)
    names = declared_names(root, sources)
    pending = {
        name: entry
        for name, entry in read_pending(root).items()
        if name not in names
    }
    if pending:
        print(
            "[PASS] no `ipcInvariantFull` conjunct is bound on a post-state; "
            f"{len(pending)} payoff theorem(s) registered as pending:"
        )
        for name, (target, _reason) in sorted(pending.items()):
            print(f"  - {name} (closure target: {target})")
    else:
        print("[PASS] ipcInvariantFull is de-threaded end to end")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
