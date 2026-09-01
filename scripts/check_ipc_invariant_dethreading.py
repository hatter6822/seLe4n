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
  transition's result, so both are where a threaded conjunct would hide; and
  the name's claim about the conclusion is *checked*, not trusted: a member
  whose final proposition does not entail a family application (the
  application itself, or a depth-0 conjunct of it) is a `family_conclusion`
  violation rather than a silent census drop;
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
# The checked pair is required too (PR #886 review): `dispatchSyscall` is the
# unchecked compatibility/proof path, while the exported entry delegates to
# `syscallEntryChecked` -> `dispatchSyscallChecked` -- a gate satisfied by the
# unchecked pair alone would report the live-kernel payoff complete while the
# dispatcher handling production syscalls regressed unnoticed.
PAYOFF_THEOREMS = (
    "dispatchWithCap_preserves_ipcInvariantFull",
    "dispatchSyscall_preserves_ipcInvariantFull",
    "dispatchWithCapChecked_preserves_ipcInvariantFull",
    "dispatchSyscallChecked_preserves_ipcInvariantFull",
)

# The namespace the payoff theorems are declared in.  A pin, not a derivation:
# a text scanner cannot resolve name elaboration, so the payoff lookups demand
# this exact prefix -- a same-named theorem under any other namespace
# (`namespace Shadow; theorem dispatchSyscall_preserves_… …`) is not the
# payoff and can only shadow it (PR #886 review).  If the payoffs move
# namespaces, this fails visibly and is updated with the move.
PAYOFF_NAMESPACE = "SeLe4n.Kernel"

# The namespace the root invariant definition lives in (`DEFS_MODULE` opens
# it).  Same pin discipline as `PAYOFF_NAMESPACE`: the conjunct derivation
# unions every same-named body, which fails closed against shadows only while
# the *canonical* root's body is among them -- so its presence under this
# prefix is required outright (PR #886 review: an arrow-form refactor the
# collector missed plus any namespaced shadow would have left the union
# holding only the shadow's reduced conjunct set).
ROOT_NAMESPACE = "SeLe4n.Kernel"

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
    "family_conclusion",
    "no_post_state_binding",
    "no_conclusion_state_hypothesis",
    "payoff_theorems",
    "payoff_statement",
)

_DECL_RE = re.compile(
    # `*`, not `?`: `@[simp] @[grind] theorem …` is valid Lean, and a
    # single-block pattern made the second routine attribute delete the
    # declaration from the census (PR #886 review).
    # The modifiers are *captured*, not merely consumed (PR #886 review): a
    # `private` payoff satisfies a presence check that discards visibility
    # while giving downstream modules nothing they can name, so
    # `declared_names` must see it.  The name accepts a guillemet-quoted
    # identifier as one unit, matching the scope scanner.
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?P<mods>(?:private\s+|protected\s+|partial\s+|noncomputable\s+|unsafe\s+"
    r"|local\s+|scoped\s+)*)"
    r"(?:theorem|lemma)\s+(?P<name>«[^»\n]*»|[^\W\d][\w'.!?]*)",
    re.MULTILINE,
)

_IDENT_CHARS = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'!?."

_OPEN = "([{"
_CLOSE = ")]}"


def _normalise(text: str) -> str:
    """Whitespace-normalise an expression, and strip redundant enclosing
    parentheses, so `st'`, `st '` and `(st')` cannot differ (PR #886 review:
    `hInv' : ipcInvariantFull (st')` must compare equal to a conclusion on
    `st'`, or the whole-bundle post-state check misses it).

    A named-argument spelling reduces to its value (PR #886 review, a later
    round): `ipcInvariantFull (st := st')` applies the invariant to `st'`,
    and keeping the `st := st'` group as an opaque "compound state" let the
    named form slip past every state comparison.  Only a bare
    `IDENT := value` group reduces -- a `let`-expression or an application
    carrying an inner named argument does not match the anchored pattern.
    """
    text = re.sub(r"\s+", " ", text).strip()
    while True:
        if text.startswith("(") and text.endswith(")"):
            end = balanced_span(text, 0)
            if end == len(text):
                text = text[1:-1].strip()
                continue
        named = re.fullmatch(r"[^\W\d][\w']*\s*:=\s*(.+)", text)
        if named:
            text = named.group(1).strip()
            continue
        return text


def _qualified(name: str) -> str:
    """Match `name` bare or behind namespace qualifiers of any case.

    The old lookbehind rejected every preceding `.`, so a namespace-qualified
    application (`Foo.blockedThreadsPendingMessageConsistent st'`) escaped the
    scan entirely (PR #886 review), and an uppercase-led qualifier class then
    missed `_root_.` and lowercase namespaces in two later rounds.  The
    pattern now accepts any identifier-led qualifier chain and captures it as
    group 1; what keeps hypothesis projections (`hInv.conjunct`) out is no
    longer a case heuristic but the *binder names of the statement itself* --
    callers skip a hit whose chain's first segment is one of their own
    binders (see `Bundle._binder_names`), which is a derivation where the
    case rule was an enumeration.
    """
    return (
        r"(?<![\w'.])((?:[^\W\d][\w']*\.)*)"
        + re.escape(name)
        + r"(?![\w'])"
    )


def _projection_hit(chain: str, binder_names: set[str]) -> bool:
    """True when a matched qualifier chain is a projection of a local binder."""
    return bool(chain) and chain.split(".", 1)[0] in binder_names


def _connectivity_tokens(text: str, excluded: frozenset[str]) -> set[str]:
    """Identifier tokens that can carry transition connectivity.

    The equality-anchor graph exists to relate *state terms* to the
    conclusion, so tokens that cannot be state-bearing are dropped before
    connectivity is computed (PR #886 review: `hAnchor : ipcInvariantFull
    stMid = ipcInvariantFull stMid` shares only its predicate symbol with
    the conclusion, and that symbol must not anchor `stMid`):

    * the family predicates and every derived conjunct (`excluded`) --
      Prop-formers, never terms;
    * uppercase-initial identifiers -- types and constructors (`Except`,
      `Prod`, `True`) that unrelated propositions routinely share;
    * projection-position identifiers (the `fst` of `.fst`, the `ok` of
      `.ok`) -- field names, not terms, and shared by every equation that
      destructures the same result shape.

    What remains -- binder names, transition-function names, state
    variables -- is the honest residual a text scanner can tie to the
    transition.  Dropping a token can only shrink the anchor set and so
    only add findings: the filter fails closed.
    """
    tokens: set[str] = set()
    for match in re.finditer(r"(?<![\w'.])[^\W\d][\w'!?]*", text):
        token = match.group(0)
        if token[0].isupper() or token in excluded:
            continue
        tokens.add(token)
    return tokens


def _informative_equation(group: str) -> bool:
    """False when the binder group's type is a syntactic tautology `X = X`.

    A reflexive equation is a valid hypothesis carrying no information about
    the transition, and treating it as an anchor group lets it launder every
    state it mentions: `hAnchor : pair st' stMid = pair st' stMid` shares the
    genuinely-anchored `st'` and so bridged `stMid` into the pre-state set
    (PR #886 review, after the predicate-symbol filter closed the
    symbol-sharing variant).  The sides of the group's first plain depth-0
    `=` (not `:=`, `==`, or `=>`) are normalised and compared; textual
    equality means the equation relates nothing, so the group contributes no
    anchors.  A group with no plain equation (a `fun … => …` type, say) is
    left as it was -- this helper only rejects tautologies, it does not
    decide what counts as a step equation.
    """
    colon = None
    depth = 0
    for offset, char in enumerate(group):
        if char in _OPEN:
            depth += 1
        elif char in _CLOSE:
            depth -= 1
        elif (
            char == ":"
            and depth == 0
            and group[offset + 1 : offset + 2] != "="
        ):
            colon = offset
            break
    body = group[colon + 1 :] if colon is not None else group
    depth = 0
    for offset, char in enumerate(body):
        if char in _OPEN:
            depth += 1
        elif char in _CLOSE:
            depth -= 1
        elif (
            char == "="
            and depth == 0
            and body[offset + 1 : offset + 2] not in ("=", ">")
            and (offset == 0 or body[offset - 1] not in ":=!<>")
        ):
            return _normalise(body[:offset]) != _normalise(body[offset + 1 :])
    return True


def _application_spans(part: str, start: int) -> bool:
    """True when everything from `start` to the part's end is argument
    material: identifier, numeral, or bracketed-group units (each with an
    optional projection chain) separated by whitespace.

    This is what makes a family application *occupy* its conjunct rather
    than head an unparsed larger proposition: a depth-0 operator of any
    kind after the arguments -- `= False`, `∨ True`, an arrow -- fails the
    walk (PR #886 review: enumerating rejected connectives left `=`
    accepted, and `ipcInvariantFull st' = False` contradicts the invariant
    while reading as a family conclusion; the application grammar is the
    derivation, the connective list was the enumeration).
    """
    index = start
    while index < len(part):
        char = part[index]
        if char in " \t\n":
            index += 1
            continue
        if char in _OPEN:
            end = balanced_span(part, index)
            if end is None:
                return False
            chain = re.match(r"(?:\.(?:\d+|[^\W\d][\w'!?]*))*", part[end:])
            index = end + chain.end()
            continue
        unit = re.match(
            r"(?:[^\W\d][\w'!?]*|\d+)(?:\.(?:\d+|[^\W\d][\w'!?]*))*",
            part[index:],
        )
        if unit is None or unit.end() == 0:
            return False
        index += unit.end()
    return True


def _returns_state(rhs: str, state: str) -> bool:
    """True when an equation right-hand side's *returned state* is `state`.

    The result must BE the state, not merely mention it (PR #886 review, the
    round after the mention-in-RHS rule landed: `.ok ((f st'), unrelated)`
    mentions the conclusion state inside the payload while returning
    `unrelated`).  Accepted shapes, matching the dispatchers' `Except (α ×
    SystemState)` results: the state itself, `.ok <state>`, and an `.ok`
    payload tuple whose *last* depth-0 component is the state.  Any other
    shape fails closed.
    """
    rhs = _normalise(rhs)
    if rhs == state:
        return True
    ok = re.match(r"^(?:Except\.ok|\.ok)\s+(.+)$", rhs)
    if not ok:
        return False
    payload = _normalise(ok.group(1))
    if payload == state:
        return True
    parts: list[str] = []
    current: list[str] = []
    depth = 0
    for char in payload:
        if char in _OPEN:
            depth += 1
        elif char in _CLOSE:
            depth -= 1
        if char == "," and depth == 0:
            parts.append("".join(current))
            current = []
        else:
            current.append(char)
    parts.append("".join(current))
    return len(parts) > 1 and _normalise(parts[-1]) == state


def _steps_function(binders: str, function: str, state: str) -> bool:
    """True when some binder group's type steps `function` into `state`.

    The group's type begins after its first depth-0 colon; the head is its
    first identifier token.  Requiring the head (rather than any mention)
    and a following top-level `=` is what rejects a dummy hypothesis that
    name-drops the dispatcher beside a step equation for something else.
    The equation's right-hand side -- cut at the first depth-0 logical
    connective, so a conjunct smuggled in after the result cannot satisfy
    this -- must *return* `state`, the payoff's conclusion state, parsed
    structurally by `_returns_state`: an equation whose result is some
    unrelated mid-state proves nothing about the state the conclusion
    speaks of, and neither does one that merely mentions that state inside
    its payload (PR #886 review, two successive rounds).
    """
    index = 0
    while index < len(binders):
        if binders[index] in _OPEN:
            end = balanced_span(binders, index)
            if end is None:
                return False
            group = binders[index + 1 : end - 1]
            colon = None
            depth = 0
            for offset, char in enumerate(group):
                if char in _OPEN:
                    depth += 1
                elif char in _CLOSE:
                    depth -= 1
                elif char == ":" and depth == 0:
                    colon = offset
                    break
            if colon is not None:
                group_type = group[colon + 1 :]
                head = re.match(r"\s*([^\W\d][\w'!?]*)", group_type)
                if head and head.group(1) == function:
                    depth = 0
                    for offset, char in enumerate(group_type):
                        if char in _OPEN:
                            depth += 1
                        elif char in _CLOSE:
                            depth -= 1
                        elif depth == 0 and char == "=":
                            rhs = group_type[offset + 1 :]
                            cut_depth = 0
                            for rhs_offset, rhs_char in enumerate(rhs):
                                if rhs_char in _OPEN:
                                    cut_depth += 1
                                elif rhs_char in _CLOSE:
                                    cut_depth -= 1
                                elif cut_depth == 0 and (
                                    rhs_char in "∧∨→↔"
                                    or (
                                        rhs_char == "-"
                                        and rhs[rhs_offset + 1 : rhs_offset + 2] == ">"
                                    )
                                ):
                                    rhs = rhs[:rhs_offset]
                                    break
                            if _returns_state(rhs, state):
                                return True
                            break
            index = end
        else:
            index += 1
    return False


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


def _blank_strings(source: str) -> str:
    """Blank the contents of double-quoted string literals, offsets kept.

    `lean_code_view.strip` deliberately preserves strings, so a
    theorem-shaped line inside a multiline Lean string satisfied the
    declaration census (PR #886 review).  This gate asks questions about
    declarations, never about string contents, so every character between
    the quotes (escapes included) becomes a space; newlines survive so line
    numbers stay aligned, and the quotes themselves survive so the lexical
    structure stays visible.
    """
    out: list[str] = []
    in_string = False
    in_char = False
    in_quoted = False
    escaped = False
    for char in source:
        if in_string or in_char:
            if escaped:
                out.append(" ")
                escaped = False
            elif char == "\\":
                out.append(" ")
                escaped = True
            elif in_string and char == '"':
                out.append(char)
                in_string = False
            elif in_char and char == "'":
                out.append(char)
                in_char = False
            elif char == "\n":
                out.append(char)
            else:
                out.append(" ")
        elif in_quoted:
            # A guillemet-quoted identifier (`«a"b»`) is code, not data: its
            # characters survive, and a double quote inside it must not open
            # a string, or the rest of the file is blanked and every later
            # declaration leaves the census (PR #886 review).
            out.append(char)
            if char == "»":
                in_quoted = False
        else:
            out.append(char)
            if char == "«":
                in_quoted = True
            elif char == '"':
                in_string = True
            elif char == "'" and (not out[:-1] or not re.match(
                r"[\w'!?]", out[-2] if len(out) >= 2 else " "
            )):
                # A quote after a non-identifier character opens a *char
                # literal* (PR #886 review: `'"'` flipped the string state
                # and blanked the rest of the file); a quote after an
                # identifier character is a prime (`st'`) and stays plain
                # text.
                in_char = True
    return "".join(out)


def code_view(root: str, relative: str) -> str:
    """The comment-free, string-blanked view of one Lean source."""
    with open(os.path.join(root, relative), encoding="utf-8") as handle:
        return _blank_strings(lean_code_view.strip(handle.read()))


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

    A bracketed group or a bare identifier, extended with any projection
    chain that follows -- numeric (`.1` / `.2`) and *named field*
    projections alike (PR #886 review: `ctx.input` and `ctx.output` both
    truncated to `ctx`, so two different state expressions compared equal).
    Returning the projection-extended form matters: a bundle whose
    post-state is `(f a st).1` binds the conjunct on exactly that
    expression, and truncating early reports a clean signature.
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
        projection = re.match(r"(?:\.(?:\d+|[^\W\d][\w'!?]*))*", text[end:])
        return text[index:end] + projection.group(0)
    identifier = re.match(
        r"[^\W\d][\w'!?]*(?:\.(?:\d+|[^\W\d][\w'!?]*))*", text[index:]
    )
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


def split_implication(text: str) -> list[str]:
    """Split at `→` at bracket depth zero.

    The segments before the last are a conclusion's *unnamed premises* -- the
    telescope continued after the declaration colon -- and the last is what
    the theorem actually concludes.
    """
    parts: list[str] = []
    current: list[str] = []
    depth = 0
    index = 0
    while index < len(text):
        char = text[index]
        if char in _OPEN:
            depth += 1
        elif char in _CLOSE:
            depth -= 1
        if depth == 0 and char == "→":
            parts.append("".join(current))
            current = []
            index += 1
            continue
        # Lean's ASCII spelling of the same arrow (PR #886 review: an
        # `->`-spelled premise was never separated, so the whole-post-state
        # hypothesis it carried passed unseen).
        if depth == 0 and char == "-" and index + 1 < len(text) and text[index + 1] == ">":
            parts.append("".join(current))
            current = []
            index += 2
            continue
        current.append(char)
        index += 1
    parts.append("".join(current))
    return parts


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


# Where a captured slice of source ends: at the next command that can open a
# line.  Leading declaration modifiers stop a body too (PR #886 review): a
# `private theorem …` after a definition is a new declaration exactly as
# `theorem …` is, and a stop pattern blind to the modifier appended the
# helper's text to the preceding body, corrupting its trailing conjunct out
# of the derived set.  Same modifier set as `_DECL_RE`.  `opaque` and its
# sibling column-0 commands too (PR #886 review): every Lean command that can
# open at column 0 bounds the preceding body, and a body line is always
# indented, so widening this set can only stop earlier -- never truncate a
# real body.  `include` / `omit` / `run_cmd` / `builtin_initialize` joined by
# the sweep of the same question (PR #886 review, the section-variable round):
# an `include hT` line after a definition's final conjunct was swallowed into
# the body, and the trailing tokens broke that conjunct's exact-application
# parse -- the same corruption `class` caused a round earlier.  Shared by the
# body collector and the `variable`-command capture, so the two slices cannot
# drift.  Commands may be *indented* (PR #886 review): Lean does not require
# column zero, so `  class Dummy where` bounds the preceding body exactly as
# the flush spelling does -- the anchor admits horizontal whitespace, and the
# same-question sweep gave the two collection patterns below the same prefix,
# since an indented `def` is otherwise a definition the map never collects.
# The residual is a body whose own *term* line opens with a command keyword
# (`open … in` inside a definition body): none exists in the tree, and losing
# one truncates the derived set, which the census pin surfaces.
_COMMAND_STOP = re.compile(
    r"^[ \t]*(?:(?:private|protected|partial|noncomputable|unsafe|local|scoped)\s+)*"
    r"(?:@\[|/-|#"
    r"|(?:def|theorem|lemma|abbrev|structure|inductive|instance|class"
    r"|end|namespace|open|opaque|axiom|example|attribute|universe"
    r"|variable|include|omit|macro_rules|macro|syntax|elab_rules|elab"
    r"|deriving|mutual|section|set_option|export|import|initialize"
    r"|builtin_initialize|run_cmd|notation"
    r"|infixl|infixr|infix|postfix|prefix)\b)",
    re.MULTILINE,
)


def state_predicate_bodies(
    root: str, sources: list[str]
) -> dict[str, list[tuple[str, str]]]:
    """Every `def NAME (st : SystemState) : Prop := ...` body in the tree.

    Collected tree-wide rather than from the definition module alone: a clause
    predicate that a bundle threads is a conjunct's half wherever it is
    defined, and a body map restricted to one file would silently stop
    expanding the day one moved.

    Keyed by the *unqualified* name, holding **every** body that name has: a
    text scanner cannot resolve which namespace's definition a reference
    elaborates to, and keeping only one body -- the last in file order --
    let a later-sorted `namespace Shadow; def ipcInvariantFull ...` eclipse
    the real root, collapsing the derived conjunct set to the shadow's
    (PR #886 review).  The union over-approximates instead: a shadowing
    definition can add scanned conjuncts, never remove the real ones, so the
    ambiguity a scanner cannot resolve fails closed.
    """
    bodies: dict[str, list[tuple[str, str]]] = {}
    # `abbrev` too (PR #886 review): a transparently refactored conjunct
    # (`def` -> `abbrev`) kept its meaning but vanished from this map, so its
    # clause predicates silently left the derived set.  The state binder is
    # any identifier, not an enumerated `st|s` (PR #886 review, next round):
    # renaming a binder to `state` is a semantics-preserving refactor, and an
    # enumeration silently dropped the renamed definition's clauses from the
    # derived set -- the enumeration-versus-derivation shape again.  "Any
    # identifier" includes Lean's Unicode ones (PR #886 review, the round
    # after): `(σ : SystemState)` is a routine binder, so the class is
    # letter-or-underscore then word characters, Unicode-aware -- and the
    # substitution boundaries below match, or a Greek binder would collect
    # and then fail to substitute.
    # Leading modifiers on the *collected* declaration too (PR #886 review:
    # the modifier fix reached the stop pattern below and not this, its
    # sibling site four lines up -- a `private def` conjunct vanished from
    # the map while a `private theorem` correctly bounded its neighbour).
    # Attribute blocks before the modifiers likewise (`@[simp] def ...`),
    # and the name capture is the Unicode identifier class, both matching
    # `_DECL_RE` (PR #886 review, next round).
    pattern = re.compile(
        r"^[ \t]*(?:@\[[^\]]*\]\s*)*"
        r"(?:(?:private|protected|partial|noncomputable|unsafe|local|scoped)\s+)*"
        r"(?:def|abbrev)\s+([^\W\d][\w'!?]*)"
        r"\s*\(\s*([^\W\d][\w']*)\s*:\s*SystemState\s*\)"
        r"\s*:\s*Prop\s*:=",
        re.MULTILINE,
    )
    # The arrow-form spelling `def NAME : SystemState → Prop := fun b => …`
    # is the same definition with the binder moved right of the colon
    # (PR #886 review): a collector blind to it dropped the canonical root
    # on a routine refactor while a namespaced shadow kept the union
    # nonempty.
    arrow_pattern = re.compile(
        r"^[ \t]*(?:@\[[^\]]*\]\s*)*"
        r"(?:(?:private|protected|partial|noncomputable|unsafe|local|scoped)\s+)*"
        r"(?:def|abbrev)\s+([^\W\d][\w'!?]*)"
        r"\s*:\s*SystemState\s*(?:→|->)\s*Prop\s*:=\s*"
        r"fun\s+([^\W\d][\w']*)\s*(?:=>|↦)",
        re.MULTILINE,
    )
    for relative in sources:
        source = code_view(root, relative)
        breakpoints = namespace_breakpoints(source)
        for match in [m for p in (pattern, arrow_pattern) for m in p.finditer(source)]:
            tail = source[match.end() :]
            cut = _COMMAND_STOP.search(tail)
            # Identifier-boundary substitution (PR #886 review): a plain
            # `.replace` on a one-letter binder like `s` rewrites every `s`
            # inside predicate *names* (`blockedOnReplyHasReplyObject` ->
            # `...HastReplyObject`), silently dropping real nested conjuncts
            # from the derived set.
            body = tail[: cut.start()] if cut else tail
            bodies.setdefault(match.group(1), []).append(
                (
                    prefix_at(breakpoints, match.start()),
                    re.sub(
                        r"(?<![\w'])" + re.escape(match.group(2)) + r"(?![\w'])",
                        "st",
                        body,
                    ),
                )
            )
    return bodies


# One conjunction part that is exactly one predicate applied to the
# definition's own (already `st`-renamed) state binder.
# The argument may carry redundant grouping -- `newQueueConsistent (st)`
# is the same application as `newQueueConsistent st`, and rejecting the
# grouped spelling would silently drop a new conjunct from the derived
# set (PR #886 review).
# A qualifier on the *definition* side is stripped rather than stored:
# the derived set holds unqualified names, and the bundle scan matches
# them behind any uppercase-led qualifier -- deriving `Foo.pred` verbatim
# would silently stop matching the bare spelling (PR #886 review: the
# qualifier fix applied to the scan and not to this, its sibling site).
# `_root_.` is accepted here for the same reason it is in `_qualified` --
# the same round's sweep of the same question's sibling sites.
# The argument may also be spelled as a named argument (PR #886 review:
# the bundle comparisons normalise `(st := st')` while this, the
# definition side, accepted only the positional form).  The label is
# *any* identifier, not the literal `st` (PR #886 review, a later
# round): the label names the **called** predicate's own binder --
# `replyCallerLinkage (σ := st)` is the routine spelling against a
# `(σ : SystemState)` definition -- while the collection substitution has
# already renamed only *this* definition's binder to `st`, so pinning
# the label to `st` dropped every such application from the derived
# set.
# Case-free qualifier chain, like the bundle scans (PR #886 review: the
# binder-name fix reached the scans and not this, its sibling -- a
# lowercase-namespace conjunct spelling dropped from the derived set).
# A definition body has no hypothesis binders, so no projection filter
# is needed here; `_root_.` is covered by the general class.
_APPLIED_RE = re.compile(
    r"^\s*(?:[^\W\d][\w']*\.)*"
    r"([^\W\d][\w'!?]*)\s+(?:\(\s*(?:[^\W\d][\w']*\s*:=\s*)?st\s*\)|st)\s*$"
)


def _sub_predicates(bodies: dict[str, list[tuple[str, str]]], name: str) -> set[str]:
    """The predicates a name's bodies apply conjunctively to their state.

    Each part is normalised (redundant enclosing parentheses stripped)
    and a part that then still splits is re-split, so a harmlessly
    regrouped body -- `(A st ∧ B st)`, opaque to one depth-0 pass --
    yields its conjuncts instead of silently dropping them
    (PR #886 review).  A `by exact e` wrapper unwraps to its payload
    (PR #886 review, a later round): the tactic spelling elaborates to
    the same proposition, and a parser blind to it derived nothing from
    a body every reader sees as a conjunction.
    """
    found = set()
    for _prefix, body in bodies.get(name, []):
        stack = [body]
        while stack:
            expr = _normalise(stack.pop())
            wrapped = re.match(r"by\s+exact\s+(.+)$", expr, re.DOTALL)
            if wrapped:
                stack.append(wrapped.group(1))
                continue
            parts = split_conjunction(expr)
            if len(parts) > 1:
                stack.extend(parts)
                continue
            hit = _APPLIED_RE.match(parts[0])
            if hit:
                found.add(hit.group(1))
    return found


def derive_conjuncts(bodies: dict[str, list[tuple[str, str]]]) -> set[str]:
    """The conjuncts of `ipcInvariantFull`, closed under definitional unfolding.

    Read out of the definition rather than listed, so a twenty-first conjunct
    is measured the day it is added.  The body is split on `∧` at bracket
    depth zero and a part counts only when it is exactly one predicate applied
    to the definition's own state binder -- so the expansion is the definition,
    not a token scrape of it.  Every body a name has contributes (see
    `state_predicate_bodies`): the derived set is the union over same-named
    definitions, so a namespaced shadow of the root or of a conjunct widens
    the scan rather than replacing it.

    The closure step is what finds `replyCallerLinkage`'s two clause
    predicates: the bundles thread `replyCallerLinkageReciprocal`, which is not
    itself a conjunct of `ipcInvariantFull` but is half of one, and a gate that
    stopped at the top-level names would score those bundles clean.  A conjunct
    whose body is not a conjunction (`ipcInvariant`'s `∀`-formula, say)
    contributes no sub-predicates, which is correct: it has none to thread.
    """
    if ROOT_INVARIANT not in bodies:
        return set()

    conjuncts = _sub_predicates(bodies, ROOT_INVARIANT)
    frontier = set(conjuncts)
    while frontier:
        name = frontier.pop()
        for nested in _sub_predicates(bodies, name):
            if nested not in conjuncts:
                conjuncts.add(nested)
                frontier.add(nested)
    conjuncts.discard(ROOT_INVARIANT)
    return conjuncts


def threading_aliases(
    bodies: dict[str, list[tuple[str, str]]], conjuncts: set[str]
) -> set[str]:
    """Predicates whose definitional expansion entails a measured conjunct.

    A bundle can thread a conjunct without naming it (PR #886 review):
    `abbrev threadedAliasHypothesis (s : SystemState) : Prop :=
    blockedThreadsPendingMessageConsistent s` bound as `(h :
    threadedAliasHypothesis st')` is definitionally the same post-state
    hypothesis, invisible to a scan over canonical names.  The alias set is
    *derived from the same bodies map the conjuncts come from*: any collected
    state-predicate whose conjunctive expansion (transitively) reaches a
    measured conjunct is measured too, so binding it anywhere a conjunct
    could not be bound is the same finding.  A predicate that reaches a
    conjunct only under a weaker connective (`∨`, `∃`) contributes no
    sub-predicates and is correctly excluded -- assuming it does not assume
    the conjunct.  The family's own forms are excluded: they are the
    pre-state vocabulary, policed by `no_conclusion_state_hypothesis`.
    """
    expansions = {name: _sub_predicates(bodies, name) for name in bodies}
    excluded = {ROOT_INVARIANT, *PRE_STATE_PREDICATES, *conjuncts}
    aliases: set[str] = set()
    changed = True
    while changed:
        changed = False
        for name, expansion in expansions.items():
            if name in excluded or name in aliases:
                continue
            if expansion & (conjuncts | aliases):
                aliases.add(name)
                changed = True
    return aliases


class Bundle:
    """One `*_preserves_ipcInvariantFull` statement, parsed from the code view.

    `ambient` is the binder text of every `variable` command in scope at the
    declaration (PR #886 review): Lean elaborates an in-scope
    `variable (hT : …)` marked `include hT` -- or simply mentioned -- into
    the theorem's parameter list, so a post-state hypothesis can be real
    while absent from the declaration slice.  The scanner cannot see which
    variables Lean actually includes, so it over-approximates **in the
    violation direction only**: ambient binders feed the scans that *find*
    threading (`threaded`, `assumes_conclusion_state`, and the projection
    receivers of `_binder_names`) and never the machinery that *suppresses*
    findings (`pre_states`, `_anchor_tokens`) -- a phantom hypothesis can
    then only add findings, never launder a pre-state or anchor into
    existence.  `excluded` is the predicate-name set (family plus derived
    conjuncts) that `_connectivity_tokens` drops from the anchor graph.
    """

    def __init__(
        self,
        path: str,
        line: int,
        name: str,
        binders: str,
        conclusion: str,
        prefix: str = "",
        ambient: str = "",
        excluded: frozenset[str] = frozenset(),
    ):
        self.path = path
        self.line = line
        self.name = name
        self.binders = binders
        self.conclusion = _normalise(conclusion)
        self.prefix = prefix
        self.ambient = ambient
        self.excluded = excluded

    def _binder_names(self) -> set[str]:
        """The statement's own binder names: each group's identifiers before
        its first depth-0 colon.  These are the receivers a hypothesis
        projection can have, and the qualifier scans use them to tell
        `hInv.conjunct` (a projection) from `foo.conjunct` (a namespace
        application) without a case heuristic.  In-scope `variable` binders
        are receivers too (PR #886 review): a projection off an included
        section hypothesis is still a projection."""
        names: set[str] = set()
        for text in (self.ambient, self.binders):
            index = 0
            while index < len(text):
                char = text[index]
                if char in _OPEN:
                    end = balanced_span(text, index)
                    if end is None:
                        break
                    group = text[index + 1 : end - 1]
                    colon = None
                    depth = 0
                    for offset, ch in enumerate(group):
                        if ch in _OPEN:
                            depth += 1
                        elif ch in _CLOSE:
                            depth -= 1
                        elif ch == ":" and depth == 0:
                            colon = offset
                            break
                    head = group if colon is None else group[:colon]
                    names.update(re.findall(r"[^\W\d][\w'!?]*", head))
                    index = end
                else:
                    index += 1
        return names

    def _anchor_tokens(self) -> set[str]:
        """Identifier tokens tied to the transition itself.

        The anchors are the *connectivity* tokens of the conclusion plus
        those of every binder region that carries an `=` -- the step
        equation and its relatives.  A state that appears in neither has no
        connection to the operation being stepped (PR #886 review: `hMid :
        ipcInvariantCore stMid` must not launder `stMid` into the pre-state
        set, or a conjunct threaded on an intermediate state passes as
        clean).  Connectivity runs through state-bearing tokens only (see
        `_connectivity_tokens`; PR #886 review, a later round): a predicate
        symbol or a shared constructor is not a term, so an equation whose
        only overlap with the conclusion is `ipcInvariantFull` itself must
        not anchor its states.  Ambient `variable` binders contribute no
        equality groups -- anchoring suppresses findings, and a section
        hypothesis Lean may not even include must not do that (see the
        class docstring's asymmetry).
        """
        tokens = _connectivity_tokens(self.conclusion, self.excluded)
        groups: list[set[str]] = []
        index = 0
        while index < len(self.binders):
            char = self.binders[index]
            if char in _OPEN:
                end = balanced_span(self.binders, index)
                if end is None:
                    break
                region = self.binders[index:end]
                if "=" in region and _informative_equation(
                    self.binders[index + 1 : end - 1]
                ):
                    groups.append(_connectivity_tokens(region, self.excluded))
                index = end
            else:
                index += 1
        # An equality group anchors its tokens only when it is *connected* to
        # the conclusion through shared tokens -- the fixpoint below grows the
        # anchor set through the equation graph (PR #886 review: a reflexive
        # `hAnchor : stMid = stMid` is a valid hypothesis harvesting nothing
        # about the transition, and wholesale harvesting let it launder
        # `stMid` into the pre-state set).  What remains accepted is an
        # equation chain genuinely reaching the conclusion's tokens, which is
        # the relation this set exists to capture.  A *tautological* equation
        # never joins the graph at all (`_informative_equation`; PR #886
        # review, a later round): `pair st' stMid = pair st' stMid` shares
        # the genuinely-anchored `st'`, and connectivity alone would let a
        # no-information hypothesis launder `stMid` through it.
        changed = True
        while changed:
            changed = False
            for group in groups:
                if group & tokens and not group <= tokens:
                    tokens |= group
                    changed = True
        return tokens

    def pre_states(self) -> set[str]:
        """The states this bundle's own invariant hypotheses are applied to.

        An atomic state qualifies only when it is anchored to the transition
        (see `_anchor_tokens`).  A compound state expression qualifies only
        when *every identifier token in it* is anchored (PR #886 review:
        wholesale acceptance let `ipcInvariantCore (someOperation st).2`
        launder an intermediate state with no step equation naming
        `someOperation`) -- the `…ExceptDonationOwner` composites pass, since
        their constituents all appear in the step equations or conclusion.
        What remains accepted, and is the residual under-approximation, is a
        compound built *only* from anchored tokens that nevertheless is not
        the transition's input; a scanner cannot evaluate the expression, so
        it errs toward accepting expressions whose every part the statement
        itself ties to the step.

        Scanned over the declaration's own binders only, never the ambient
        `variable` text: a pre-state suppresses findings, and a section
        hypothesis Lean may not even include must not mint one (see the
        class docstring's asymmetry).  Compound containment runs on
        connectivity tokens, matching the anchor set's vocabulary -- and a
        compound with *no* connectivity token has nothing tying it to the
        transition at all, so it is rejected rather than vacuously
        contained."""
        anchors = self._anchor_tokens()
        binder_names = self._binder_names()
        states = set()
        for predicate in PRE_STATE_PREDICATES:
            for hit in re.finditer(_qualified(predicate), self.binders):
                if _projection_hit(hit.group(1), binder_names):
                    continue
                argument = first_argument(self.binders, hit.end())
                if argument:
                    state = _normalise(argument)
                    if re.fullmatch(r"[^\W\d][\w'!?]*", state):
                        if state not in anchors:
                            continue
                    else:
                        tokens = _connectivity_tokens(state, self.excluded)
                        if not tokens or not tokens <= anchors:
                            continue
                    states.add(state)
        return states

    def conclusion_state(self) -> str | None:
        """The state this bundle's conclusion applies its invariant form to.

        Read from the *final* segment of the conclusion's depth-0 implication
        chain: `A → ipcInvariantFull st'` concludes about `st'`, and taking
        the first family application in the whole conclusion would read the
        state out of a premise instead (PR #886 review).

        The final segment must *entail* the family application, not merely
        contain it (PR #886 review, a later round): `ipcInvariantFull st' ∨
        True` is provable by its right arm and carries no invariant, yet a
        find-anywhere scan read `st'` out of it.  A conclusion entails the
        application exactly when the application is the whole segment or a
        depth-0 conjunct of it -- a conjunction proves each conjunct, while
        no other connective proves its arms -- so the segment is split on
        depth-0 `∧` recursively and each part counts only when the family
        application *occupies* it: family head at the part's start (behind
        an optional qualifier chain that is not a binder projection), and
        everything after the head parsing as argument material to the
        part's end (`_application_spans`; PR #886 review, the round after:
        rejecting an enumerated `∨`/`↔` left `ipcInvariantFull st' = False`
        -- a conclusion that *contradicts* the invariant -- reading as a
        family conclusion).  The residual under-approximation is a
        conclusion that entails the invariant only semantically (an ASCII
        `/\`-spelled right conjunct, a quantifier-wrapped application);
        those read as `None`, which fails closed via `family_conclusion`.

        `None` for a declaration that carries the family marker in its name
        without concluding a family proposition -- since the vacuous-shape
        round that is a reported `family_conclusion` violation, never a
        silent census drop; the threaded-conjunct check still covers such a
        declaration's binders in full.
        """
        final = split_implication(_normalise(self.conclusion))[-1]
        binder_names = self._binder_names()
        parts: list[str] = [final]
        flat: list[str] = []
        while parts:
            part = _normalise(parts.pop(0))
            split = split_conjunction(part)
            if len(split) > 1:
                parts = split + parts
                continue
            flat.append(part)
        for part in flat:
            for predicate in PRE_STATE_PREDICATES:
                hit = re.match(_qualified(predicate), part)
                if hit is None or _projection_hit(hit.group(1), binder_names):
                    continue
                if not _application_spans(part, hit.end()):
                    continue
                argument = first_argument(part, hit.end())
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

        The hypothesis may hide in any of three places: a named binder, an
        unnamed implication premise after the declaration colon
        (`ipcInvariantFull st' → ipcInvariantFull st'`), which the
        binder-reading pre-state scan never sees (PR #886 review) -- or an
        in-scope `variable` binder the collector's declaration slice never
        contained (PR #886 review, the section-variable round).  The
        premises and the ambient text are scanned alike; the ambient scan is
        the finding-direction half of the class docstring's asymmetry.
        """
        state = self.conclusion_state()
        if state is None:
            return None
        if state in self.pre_states():
            return state
        binder_names = self._binder_names()
        segments = split_implication(_normalise(self.conclusion))
        for premise in list(segments[:-1]) + [self.ambient]:
            for predicate in PRE_STATE_PREDICATES:
                for hit in re.finditer(_qualified(predicate), premise):
                    if _projection_hit(hit.group(1), binder_names):
                        continue
                    argument = first_argument(premise, hit.end())
                    if argument is not None and _normalise(argument) == state:
                        return state
        return None

    def threaded(self, conjuncts: set[str]) -> list[tuple[str, str]]:
        """(conjunct, state) for every conjunct bound on a non-pre-state.

        The conclusion is scanned as well as the named binders: an unnamed
        implication premise after the declaration's colon (`conjunct st' →
        ipcInvariantFull st'`) is the same threading in telescope clothing
        (PR #886 review).  No bundle legitimately *concludes* a conjunct --
        the family concludes family predicates -- so a conjunct application
        anywhere in the signature is a hypothesis.  In-scope `variable`
        binders are scanned too (PR #886 review, the section-variable
        round): an `include`d section hypothesis is telescope, and one Lean
        would not include can only add findings here, never suppress them
        (the class docstring's asymmetry).
        """
        pre = self.pre_states()
        binder_names = self._binder_names()
        findings = []
        for conjunct in sorted(conjuncts):
            for region in (self.ambient, self.binders, self.conclusion):
                for hit in re.finditer(_qualified(conjunct), region):
                    if _projection_hit(hit.group(1), binder_names):
                        continue
                    argument = first_argument(region, hit.end())
                    if argument is None:
                        continue
                    state = _normalise(argument)
                    if state not in pre:
                        findings.append((conjunct, state))
        return findings


# The namespace name is a dotted chain whose segments may be guillemet-quoted
# (PR #886 review): `namespace «shadow»` is a scope Lean accepts, and a
# scanner that did not push it recorded declarations inside under the
# *enclosing* prefix -- which is exactly where a shadow must not be recorded.
_SCOPE_RE = re.compile(
    r"^\s*(?:namespace\s+"
    r"(?P<ns>(?:«[^»\n]*»|[^\W\d][\w']*)(?:\.(?:«[^»\n]*»|[^\W\d][\w']*))*)"
    r"|(?:noncomputable\s+)?(?P<sec>section)\b"
    r"|(?P<mut>mutual)\b"
    r"|(?P<end>end)\b)",
    re.MULTILINE,
)


def namespace_breakpoints(source: str) -> list[tuple[int, str]]:
    """(offset, namespace prefix in force from that offset), in order.

    A line-anchored scan of `namespace` / `section` / `mutual` / `end` over
    the comment-free code view, tracking one scope stack; `end` closes the
    most recent scope of any kind, which is how these sources use it.  A
    misparse cannot pass silently: the payoff lookup demands the canonical
    prefix exactly, so a wrongly tracked prefix surfaces as a visible gate
    failure, never as an accepted shadow.
    """
    breakpoints = [(0, "")]
    stack: list[str | None] = []
    for match in _SCOPE_RE.finditer(source):
        if match.group("ns") is not None:
            stack.append(match.group("ns"))
        elif match.group("end") is not None:
            if stack:
                stack.pop()
        else:
            stack.append(None)
        prefix = ".".join(name for name in stack if name is not None)
        breakpoints.append((match.end(), prefix))
    return breakpoints


def prefix_at(breakpoints: list[tuple[int, str]], offset: int) -> str:
    """The namespace prefix in force at `offset`."""
    prefix = ""
    for start, value in breakpoints:
        if start > offset:
            break
        prefix = value
    return prefix


_VARIABLE_RE = re.compile(r"^\s*variable(?![\w'!?])", re.MULTILINE)


def variable_intervals(source: str) -> list[tuple[int, int, str]]:
    """(activation offset, deactivation offset, binder text) for every
    line-anchored `variable` command, scope-tracked.

    Lean elaborates in-scope `variable` binders into a theorem's parameter
    list when they are mentioned or `include`d, so a hypothesis can be real
    while absent from the declaration slice the collector reads (PR #886
    review).  A command's binder text runs from the keyword to the next
    line-anchored command (`_COMMAND_STOP`, shared with the body collector),
    and it is active from there until the `end` that closes the section,
    namespace or mutual block it was declared in -- file scope lives to end
    of source.  `include` and `omit` are deliberately *not* interpreted:
    which binders Lean actually includes is an elaboration fact a text
    scanner cannot resolve, so every active binder is treated as telescope,
    which over-approximates in the finding direction only (see `Bundle`'s
    docstring for the asymmetry that keeps the over-approximation from
    suppressing anything).
    """
    events = sorted(
        [(match.start(), "scope", match) for match in _SCOPE_RE.finditer(source)]
        + [(match.start(), "var", match) for match in _VARIABLE_RE.finditer(source)],
        key=lambda event: event[0],
    )
    intervals: list[tuple[int, int, str]] = []
    frames: list[list[tuple[int, str]]] = [[]]
    for _offset, kind, match in events:
        if kind == "var":
            tail = source[match.end() :]
            cut = _COMMAND_STOP.search(tail)
            text = tail[: cut.start()] if cut else tail
            frames[-1].append((match.end(), text))
        elif match.group("end") is not None:
            if len(frames) > 1:
                for start, text in frames.pop():
                    intervals.append((start, match.start(), text))
        else:
            frames.append([])
    for frame in frames:
        for start, text in frame:
            intervals.append((start, len(source), text))
    return intervals


def ambient_at(intervals: list[tuple[int, int, str]], offset: int) -> str:
    """The concatenated `variable` binder text in scope at `offset`."""
    return " ".join(
        text for start, end, text in intervals if start <= offset < end
    )


def collect_bundles(
    root: str, sources: list[str], excluded: frozenset[str] = frozenset()
) -> list[Bundle]:
    """Every declaration in the `ipcInvariantFull` bundle family.

    `excluded` is the predicate-name set (family plus derived conjuncts)
    each bundle's `_connectivity_tokens` filter drops from its anchor
    graph; the caller derives it before collecting.
    """
    bundles = []
    for relative in sources:
        source = code_view(root, relative)
        breakpoints = namespace_breakpoints(source)
        intervals = variable_intervals(source)
        for match in _DECL_RE.finditer(source):
            name = match.group("name")
            if not any(marker in name for marker in BUNDLE_MARKERS):
                continue
            end = signature_end(source, match.end())
            binders, conclusion = split_conclusion(source[match.end() : end])
            line = source.count("\n", 0, match.start()) + 1
            bundles.append(
                Bundle(
                    relative,
                    line,
                    name,
                    binders,
                    conclusion,
                    prefix_at(breakpoints, match.start()),
                    ambient_at(intervals, match.start()),
                    excluded,
                )
            )
    return bundles


def declared_names(root: str, sources: list[str]) -> dict[str, set[tuple[str, str]]]:
    """Every theorem/lemma name in the code view -> its (prefix, visibility)
    declaration sites.

    Prefix-aware (PR #886 review): a bare name set let a `namespace Shadow`
    declaration stand in for a deleted global payoff, so the payoff lookups
    must see where each name is declared, not merely that it is.
    Visibility-aware too (PR #886 review, a later round): a `private` payoff
    under the canonical namespace satisfies a presence check that discards
    the modifier while giving downstream modules nothing they can name, so
    each site records `"private"` or `""` alongside its prefix.
    """
    names: dict[str, set[tuple[str, str]]] = {}
    for relative in sources:
        source = code_view(root, relative)
        breakpoints = namespace_breakpoints(source)
        for match in _DECL_RE.finditer(source):
            names.setdefault(match.group("name"), set()).add(
                (
                    prefix_at(breakpoints, match.start()),
                    "private" if "private" in match.group("mods") else "",
                )
            )
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


def payoff_status(
    names: dict[str, set[tuple[str, str]]], pending: dict[str, tuple[str, str]]
) -> list[str]:
    """Violations from the payoff check, registration included.

    Four cases, and three of them are failures.  A registered name whose theorem
    has since landed is *stale* and fails, because a registration that outlives
    its residual is how an exemption list stops describing the tree.  A
    registration for something outside the payoff set is *dangling* and fails,
    for the same reason in the other direction.

    "Declared" means declared *public* under `PAYOFF_NAMESPACE`: a same-named
    theorem in any other namespace is a shadow, not the payoff, and is itself
    a finding whether or not the canonical one exists (PR #886 review) -- and
    a `private` declaration under the canonical namespace is a finding too
    (PR #886 review, a later round), because a module-local theorem is not a
    top-level consumer downstream code can name.
    """
    problems: list[str] = []
    for payoff in PAYOFF_THEOREMS:
        registered = payoff in pending
        entries = names.get(payoff, set())
        prefixes = {prefix for prefix, _visibility in entries}
        present = (PAYOFF_NAMESPACE, "") in entries
        private_only = (PAYOFF_NAMESPACE, "private") in entries and not present
        shadows = sorted(prefixes - {PAYOFF_NAMESPACE})
        if private_only:
            problems.append(
                f"payoff_theorems: `{payoff}` is declared `private` in the "
                f"canonical `{PAYOFF_NAMESPACE}` namespace -- a module-local "
                f"payoff is not a top-level consumer downstream code can name"
            )
        if shadows:
            problems.append(
                f"payoff_theorems: `{payoff}` is declared under namespace(s) "
                f"{shadows} -- a same-named declaration outside the canonical "
                f"`{PAYOFF_NAMESPACE}` namespace is not the payoff and can "
                f"only shadow it"
            )
        if present and registered:
            problems.append(
                f"payoff_theorems: `{payoff}` is declared but still registered as "
                f"pending in {PENDING_FILE}; delete the registration"
            )
        elif not present and not registered and not private_only:
            problems.append(
                f"payoff_theorems: `{payoff}` is not declared in the canonical "
                f"`{PAYOFF_NAMESPACE}` namespace and is not registered as "
                f"pending in {PENDING_FILE}; the de-threaded bundles have no "
                f"top-level consumer"
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
    bodies = state_predicate_bodies(root, sources)
    # The union over same-named bodies fails closed against shadows only
    # while the canonical root's own body is among them (PR #886 review), so
    # its presence under the canonical namespace is required outright.
    if not any(
        prefix == ROOT_NAMESPACE for prefix, _body in bodies.get(ROOT_INVARIANT, [])
    ):
        problems.append(
            f"conjuncts_derived: no `def {ROOT_INVARIANT}` body collected under "
            f"the canonical `{ROOT_NAMESPACE}` namespace; the derived set would "
            f"be a shadow's"
        )
        return problems
    conjuncts = derive_conjuncts(bodies)
    if not conjuncts:
        # A silently empty conjunct set would make `no_post_state_binding`
        # vacuous -- the gate would report PASS having measured nothing.
        problems.append(
            f"conjuncts_derived: no conjuncts derived from `def {ROOT_INVARIANT}` "
            f"in {DEFS_MODULE}; the de-threading check would be vacuous"
        )
        return problems

    # The canonical root's own body must contribute (PR #886 review): the
    # presence check above accepts a body the exact-application parser cannot
    # read (`:= by { exact … }` behind a tactic shape the unwrap does not
    # know), and the union then holds only what *shadows* derived -- the
    # exemption shape again, one level down.  Only the root entry is
    # filtered: shadows of nested conjuncts still widen legitimately.
    canonical_bodies = dict(bodies)
    canonical_bodies[ROOT_INVARIANT] = [
        entry for entry in bodies[ROOT_INVARIANT] if entry[0] == ROOT_NAMESPACE
    ]
    if not derive_conjuncts(canonical_bodies):
        problems.append(
            f"conjuncts_derived: the canonical `{ROOT_NAMESPACE}` body of "
            f"`{ROOT_INVARIANT}` derives no conjuncts on its own -- the "
            f"derived set would be a shadow's; the root body must parse as a "
            f"conjunction of predicate applications"
        )
        return problems

    # Aliases are measured exactly as conjuncts are (PR #886 review): a
    # predicate that definitionally entails a conjunct is that conjunct for
    # threading purposes, and it is a Prop-former for connectivity purposes.
    measured = conjuncts | threading_aliases(bodies, conjuncts)
    bundles = collect_bundles(
        root, sources, frozenset(measured) | frozenset(PRE_STATE_PREDICATES)
    )
    # A family-marker name is a claim about the conclusion, and the claim is
    # checked rather than trusted (PR #886 review): a conclusion that merely
    # *contains* the family application -- `ipcInvariantFull st' ∨ True` is
    # provable by its right arm -- reads as `None` under the entailment
    # parse, and silently dropping such a declaration from the census would
    # let a vacuous rewrite retire a bundle unnoticed.  The payoff names are
    # exempt here only because `payoff_statement` reports the same defect
    # with the payoff-specific message.
    for bundle in sorted(bundles, key=lambda b: (b.path, b.line)):
        if bundle.name in PAYOFF_THEOREMS or bundle.conclusion_state() is not None:
            continue
        problems.append(
            f"family_conclusion: {bundle.path}:{bundle.line}: `{bundle.name}` "
            f"carries the family marker but its final proposition does not "
            f"entail an `ipcInvariantFull`-family application -- the family "
            f"predicate must be the conclusion itself or a depth-0 conjunct "
            f"of it, not an arm of some weaker connective"
        )
    # A bundle counts toward the family only when it *concludes* a family
    # proposition (PR #886 review): the marker lives in the name, and a
    # `dummy_preserves_ipcInvariantFullish : True` would otherwise keep the
    # census nonempty after every real operation bundle vanished.
    operation_bundles = [
        b
        for b in bundles
        if b.name not in PAYOFF_THEOREMS and b.conclusion_state() is not None
    ]
    if not operation_bundles:
        # The payoff names themselves carry the family marker, so a census
        # that counted them would stay "nonempty" after every per-operation
        # bundle vanished (PR #886 review) -- the population that matters is
        # the measured operation family.
        markers = " / ".join(f"`*{marker}*`" for marker in BUNDLE_MARKERS)
        problems.append(
            f"family_nonempty: no declaration matching {markers} found outside "
            f"the payoff tier; the de-threading check would be vacuous"
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
        for conjunct, state in bundle.threaded(measured):
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

    # A payoff that is merely *named* proves nothing: `theorem
    # dispatchSyscall_preserves_ipcInvariantFull : True` would satisfy the
    # presence check while providing no top-level consumer (PR #886 review).
    # Each declared payoff must conclude an `ipcInvariantFull`-family
    # predicate of some state and hypothesise a step equation that carries
    # the dispatch function it is named for into that same state.
    # Canonical-prefix bundles only (PR #886 review): a `namespace Shadow`
    # twin must not be the declaration whose statement gets validated.
    by_name = {
        bundle.name: bundle
        for bundle in bundles
        if bundle.prefix == PAYOFF_NAMESPACE
    }
    for payoff in PAYOFF_THEOREMS:
        bundle = by_name.get(payoff)
        if bundle is None:
            continue  # absence is payoff_theorems' finding, not this one's
        function = payoff[: -len("_preserves_ipcInvariantFull")]
        state = bundle.conclusion_state()
        if state is None:
            problems.append(
                f"payoff_statement: {bundle.path}:{bundle.line}: `{payoff}` "
                f"does not conclude an `ipcInvariantFull`-family predicate "
                f"applied to a state"
            )
        # The dispatcher must be the *head of a step equation whose result
        # carries the conclusion's state*, not merely a token somewhere in
        # the binders: a dummy hypothesis mentioning the name beside a step
        # for another function satisfied the mention-only form, and a step
        # equation into an unrelated mid-state satisfied the head-only form
        # (PR #886 review, two successive rounds).  A binder group's type
        # starts after its first depth-0 colon; the group steps `function`
        # into `state` when that type's head identifier is `function`, a
        # top-level `=` follows, and the equation's right-hand side mentions
        # the conclusion state.
        elif not _steps_function(bundle.binders, function, state):
            problems.append(
                f"payoff_statement: {bundle.path}:{bundle.line}: `{payoff}` "
                f"has no hypothesis whose step equation applies `{function}` "
                f"with `{state}`, its conclusion's state, in the result; a "
                f"payoff that does not step the dispatcher it is named for "
                f"into the state it concludes about consumes nothing"
            )

    return problems


def report(root: str) -> int:
    """Print the census: bundles, conjuncts, and every post-state binding."""
    sources = lean_sources(root)
    bodies = state_predicate_bodies(root, sources)
    conjuncts = derive_conjuncts(bodies)
    measured = conjuncts | threading_aliases(bodies, conjuncts)
    bundles = collect_bundles(
        root, sources, frozenset(measured) | frozenset(PRE_STATE_PREDICATES)
    )
    print(f"conjuncts derived from `{ROOT_INVARIANT}`: {len(conjuncts)}")
    for conjunct in sorted(conjuncts):
        print(f"  - {conjunct}")
    markers = " / ".join(f"`*{marker}*`" for marker in BUNDLE_MARKERS)
    print(f"\n{markers} statements: {len(bundles)}")
    tally: dict[str, int] = {}
    threaded_bundles = 0
    for bundle in sorted(bundles, key=lambda b: (b.path, b.line)):
        findings = bundle.threaded(measured)
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
    # The census is informational; the exit status is not (PR #886 review):
    # `--report` is cited as an evidence command, so it must fail on the
    # same violations the default mode fails on rather than printing them
    # and exiting 0.
    problems = run_checks(root)
    if problems:
        print(f"\n[FAIL] {len(problems)} violation(s); run without --report for the list")
        return 1
    return 0


# ---------------------------------------------------------------------------
# The witness suite.
#
# Every case states which check it exercises and whether its mutation KEEPS the
# token the check searches for.  A suite made only of deletions certifies
# nothing about a relation, so the harness fails when a check has no
# token-preserving case -- enforced here rather than asserted in a comment.
# ---------------------------------------------------------------------------

CLEAN_DEFS = '''namespace SeLe4n.Kernel

/-- Docstring: blockedThreadsPendingMessageConsistent st' is prose here. -/
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

end SeLe4n.Kernel
'''

CLEAN_BUNDLE = '''theorem endpointSendDual_preserves_ipcInvariantFull
    (st st' : SystemState)
    (hInv : ipcInvariantFull st)
    (hStep : endpointSendDual st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hInv hStep
'''

CLEAN_PAYOFF = '''namespace SeLe4n.Kernel

theorem dispatchWithCap_preserves_ipcInvariantFull
    (st st' : SystemState) (hInv : ipcInvariantFull st)
    (hStep : dispatchWithCap st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hInv hStep

theorem dispatchSyscall_preserves_ipcInvariantFull
    (st st' : SystemState) (hInv : ipcInvariantFull st)
    (hStep : dispatchSyscall st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hInv hStep

theorem dispatchWithCapChecked_preserves_ipcInvariantFull
    (st st' : SystemState) (hInv : ipcInvariantFull st)
    (hStep : dispatchWithCapChecked st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hInv hStep

theorem dispatchSyscallChecked_preserves_ipcInvariantFull
    (st st' : SystemState) (hInv : ipcInvariantFull st)
    (hStep : dispatchSyscallChecked st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hInv hStep

end SeLe4n.Kernel
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

    # --- PR #886 review hardening: token-preserving relation breaks ------
    # Qualified application: the conjunct token survives behind an
    # uppercase-led namespace qualifier; the old dot-rejecting lookbehind
    # skipped it entirely.
    qualified = _fixture()
    qualified["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hQ : Foo.blockedThreadsPendingMessageConsistent st')\n",
        )
    )
    cases.append(
        _Case(
            "conjunct bound on the post-state behind a namespace qualifier",
            qualified,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # Parenthesised conclusion state: `ipcInvariantFull (st')` must compare
    # equal to the conclusion's `st'`, or the whole-bundle post-state
    # hypothesis slips past unnormalised.
    parenthesised = _fixture()
    parenthesised["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hInv' : ipcInvariantFull (st'))\n",
        )
    )
    cases.append(
        _Case(
            "whole-bundle hypothesis on the parenthesised conclusion state",
            parenthesised,
            True,
            check="no_conclusion_state_hypothesis",
            mutation="preserving",
        )
    )

    # Mid-state laundering: an invariant-family hypothesis on a state the
    # transition never touches must not admit that state as a pre-state.
    midstate = _fixture()
    midstate["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hMid : ipcInvariantCore stMid)\n"
            "    (hT : blockedThreadsPendingMessageConsistent stMid)\n",
        )
    )
    cases.append(
        _Case(
            "conjunct bound on an unanchored intermediate state",
            midstate,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # One-letter definition binder: substituting `s` -> `st` by raw substring
    # mangled predicate names (`...HasReplyObject` -> `...HastReplyObject`),
    # dropping the nested conjunct from the derived set.
    binder_s = _fixture()
    binder_s[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def replyCallerLinkage (st : SystemState) : Prop :=\n"
        "  replyCallerLinkageReciprocal st ∧ blockedOnReplyHasReplyObject st",
        "def replyCallerLinkage (s : SystemState) : Prop :=\n"
        "  replyCallerLinkageReciprocal s ∧ blockedOnReplyHasReplyObject s",
    )
    binder_s["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (h : blockedOnReplyHasReplyObject st')\n",
        )
    )
    cases.append(
        _Case(
            "nested conjunct threaded when its parent uses a one-letter binder",
            binder_s,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # Stub payoff: the name is present but concludes no family predicate --
    # presence alone must not satisfy the payoff check.
    stub = _fixture()
    stub["SeLe4n/Kernel/API.lean"] = CLEAN_PAYOFF.replace(
        """theorem dispatchSyscall_preserves_ipcInvariantFull
    (st st' : SystemState) (hInv : ipcInvariantFull st)
    (hStep : dispatchSyscall st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hInv hStep""",
        """theorem dispatchSyscall_preserves_ipcInvariantFull
    (st st' : SystemState) (hStep : dispatchSyscall st = .ok ((), st')) :
    True := by
  trivial""",
    )
    cases.append(
        _Case(
            "payoff declared but concluding True instead of the family",
            stub,
            True,
            check="payoff_statement",
            mutation="preserving",
        )
    )

    # Payoff that never steps its dispatcher: same name, family conclusion,
    # but the function the theorem is named for is absent from the binders.
    unstepped = _fixture()
    unstepped["SeLe4n/Kernel/API.lean"] = CLEAN_PAYOFF.replace(
        "    (hStep : dispatchSyscall st = .ok ((), st')) :\n"
        "    ipcInvariantFull st' := by\n"
        "  exact sample st st' hInv hStep",
        "    (hStep : someOtherFunction st = .ok ((), st')) :\n"
        "    ipcInvariantFull st' := by\n"
        "  exact sample st st' hInv hStep",
    )
    cases.append(
        _Case(
            "payoff whose hypotheses never mention the dispatcher it names",
            unstepped,
            True,
            check="payoff_statement",
            mutation="preserving",
        )
    )

    # Grouped conjunct argument: a conjunct written `pred (st)` in the
    # definition must still enter the derived set, or threading it goes
    # unmeasured.
    grouped = _fixture()
    grouped[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def ipcInvariantFull (st : SystemState) : Prop :=\n"
        "  blockedThreadsPendingMessageConsistent st ∧ replyCallerLinkage st",
        "def ipcInvariantFull (st : SystemState) : Prop :=\n"
        "  blockedThreadsPendingMessageConsistent (st) ∧ replyCallerLinkage st",
    )
    grouped["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hT : blockedThreadsPendingMessageConsistent st')\n",
        )
    )
    cases.append(
        _Case(
            "conjunct applied to a parenthesised binder still derives and flags",
            grouped,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # Implication-premise threading: the conjunct hypothesis moves out of the
    # named binders into an unnamed premise after the colon.
    telescoped = _fixture()
    telescoped["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    ipcInvariantFull st' := by",
            "    blockedThreadsPendingMessageConsistent st' → ipcInvariantFull st' := by",
        )
    )
    cases.append(
        _Case(
            "conjunct threaded as an unnamed implication premise in the conclusion",
            telescoped,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # Qualified conjunct in the *definition*: the derivation must strip the
    # qualifier and keep the conjunct, or threading it goes unmeasured.
    qualified_def = _fixture()
    qualified_def[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def ipcInvariantFull (st : SystemState) : Prop :=\n"
        "  blockedThreadsPendingMessageConsistent st ∧ replyCallerLinkage st",
        "def ipcInvariantFull (st : SystemState) : Prop :=\n"
        "  Foo.blockedThreadsPendingMessageConsistent st ∧ replyCallerLinkage st",
    )
    qualified_def["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hT : blockedThreadsPendingMessageConsistent st')\n",
        )
    )
    cases.append(
        _Case(
            "conjunct spelled with a namespace qualifier in the definition",
            qualified_def,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # Two attribute blocks: the declaration must stay in the census.
    attributed = _fixture()
    attributed["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "theorem endpointSendDual_preserves_ipcInvariantFull",
            "@[simp] @[grind] theorem endpointSendDual_preserves_ipcInvariantFull",
        ).replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hT : blockedThreadsPendingMessageConsistent st')\n",
        )
    )
    cases.append(
        _Case(
            "threaded bundle behind two attribute blocks stays in the census",
            attributed,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # Dummy dispatcher mention: the name appears in a side hypothesis while
    # the step equation applies another function -- the mention-only check
    # accepted this.
    namedrop = _fixture()
    namedrop["SeLe4n/Kernel/API.lean"] = CLEAN_PAYOFF.replace(
        """theorem dispatchSyscall_preserves_ipcInvariantFull
    (st st' : SystemState) (hInv : ipcInvariantFull st)
    (hStep : dispatchSyscall st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hInv hStep""",
        """theorem dispatchSyscall_preserves_ipcInvariantFull
    (st st' : SystemState) (hInv : ipcInvariantFull st)
    (hNote : mentions dispatchSyscall)
    (hStep : someOtherOperation st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hInv hStep""",
    )
    cases.append(
        _Case(
            "payoff name-drops its dispatcher beside another function's step",
            namedrop,
            True,
            check="payoff_statement",
            mutation="preserving",
        )
    )

    # Detached step result: the dispatcher heads a genuine step equation --
    # head, `=`, everything the namedrop fix requires -- but into a mid-state,
    # while a second function's step produces the conclusion's state.  The
    # head-plus-`=` form accepted this; the conclusion says nothing about the
    # dispatcher's result.
    detached_step = _fixture()
    detached_step["SeLe4n/Kernel/API.lean"] = CLEAN_PAYOFF.replace(
        """theorem dispatchSyscall_preserves_ipcInvariantFull
    (st st' : SystemState) (hInv : ipcInvariantFull st)
    (hStep : dispatchSyscall st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hInv hStep""",
        """theorem dispatchSyscall_preserves_ipcInvariantFull
    (st stMid st' : SystemState) (hInv : ipcInvariantFull st)
    (hStep : dispatchSyscall st = .ok ((), stMid))
    (hRelay : someOtherOperation stMid = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st stMid st' hInv hStep hRelay""",
    )
    cases.append(
        _Case(
            "payoff steps its dispatcher into a state other than its conclusion's",
            detached_step,
            True,
            check="payoff_statement",
            mutation="preserving",
        )
    )

    # Namespaced shadow of a payoff: the theorem text survives verbatim, but
    # its declaration moves under `namespace Shadow` -- a legal declaration
    # that is not the top-level payoff.  A bare-name census accepted it in
    # place of the deleted global.
    shadow_payoff = _fixture()
    shadow_payoff["SeLe4n/Kernel/API.lean"] = CLEAN_PAYOFF.replace(
        """theorem dispatchSyscall_preserves_ipcInvariantFull
    (st st' : SystemState) (hInv : ipcInvariantFull st)
    (hStep : dispatchSyscall st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hInv hStep""",
        """namespace Shadow

theorem dispatchSyscall_preserves_ipcInvariantFull
    (st st' : SystemState) (hInv : ipcInvariantFull st)
    (hStep : dispatchSyscall st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hInv hStep

end Shadow""",
    )
    cases.append(
        _Case(
            "a namespaced shadow cannot stand in for a deleted payoff",
            shadow_payoff,
            True,
            check="payoff_theorems",
            mutation="preserving",
        )
    )

    # Transparent abbreviation: a conjunct refactored `def` -> `abbrev` must
    # keep its clause predicates in the derived set.
    abbreviated = _fixture()
    abbreviated[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def replyCallerLinkage (st : SystemState) : Prop :=",
        "abbrev replyCallerLinkage (st : SystemState) : Prop :=",
    )
    abbreviated["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (h : replyCallerLinkageReciprocal st')\n",
        )
    )
    cases.append(
        _Case(
            "clause of an `abbrev`-refactored conjunct threaded on the post-state",
            abbreviated,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # Namespaced shadow of the root: a later-sorted file legally defines its
    # own `ipcInvariantFull` inside a namespace.  Keyed last-writer-wins, the
    # shadow's body replaced the real one and the derived conjunct set
    # collapsed to the shadow's -- so a bundle threading a *real* conjunct
    # scored clean.  The union keying keeps every same-named body, so the
    # real conjuncts stay derived and the threading is still caught.
    shadowed_root = _fixture()
    shadowed_root["SeLe4n/Kernel/IPC/Invariant/Structural/ShadowDefs.lean"] = (
        "namespace Shadow\n"
        "\n"
        "def harmlessObservation (st : SystemState) : Prop :=\n"
        "  True\n"
        "\n"
        "def ipcInvariantFull (st : SystemState) : Prop :=\n"
        "  harmlessObservation st\n"
        "\n"
        "end Shadow\n"
    )
    shadowed_root["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hT : blockedThreadsPendingMessageConsistent st')\n",
        )
    )
    cases.append(
        _Case(
            "a namespaced shadow of the root cannot eclipse the real conjuncts",
            shadowed_root,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # Renamed state binder: `st` -> `state` is a semantics-preserving refactor
    # of one conjunct's definition, and an enumerated `st|s` binder pattern
    # dropped the renamed body from the map -- its clauses left the derived
    # set, so threading one scored clean.
    renamed_binder = _fixture()
    renamed_binder[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def replyCallerLinkage (st : SystemState) : Prop :=\n"
        "  replyCallerLinkageReciprocal st ∧ blockedOnReplyHasReplyObject st",
        "def replyCallerLinkage (state : SystemState) : Prop :=\n"
        "  replyCallerLinkageReciprocal state ∧ blockedOnReplyHasReplyObject state",
    )
    renamed_binder["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (h : replyCallerLinkageReciprocal st')\n",
        )
    )
    cases.append(
        _Case(
            "clause of a conjunct whose binder was renamed still derives and flags",
            renamed_binder,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # `_root_.`-qualified threading: Lean's root-namespace escape starts with
    # an underscore, which the uppercase-led qualifier rule rejected -- the
    # conjunct, its post-state, and the qualifier chain are all present, and
    # the scan saw none of it.
    root_qualified = _fixture()
    root_qualified["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hT : _root_.blockedThreadsPendingMessageConsistent st')\n",
        )
    )
    cases.append(
        _Case(
            "conjunct threaded behind the `_root_.` qualifier",
            root_qualified,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # `_root_.` in the *definition*: the sibling site of the same question --
    # a root-qualified conjunct spelling must still derive, or threading its
    # bare spelling goes unmeasured.
    root_qualified_def = _fixture()
    root_qualified_def[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def ipcInvariantFull (st : SystemState) : Prop :=\n"
        "  blockedThreadsPendingMessageConsistent st ∧ replyCallerLinkage st",
        "def ipcInvariantFull (st : SystemState) : Prop :=\n"
        "  _root_.blockedThreadsPendingMessageConsistent st ∧ replyCallerLinkage st",
    )
    root_qualified_def["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hT : blockedThreadsPendingMessageConsistent st')\n",
        )
    )
    cases.append(
        _Case(
            "conjunct spelled with `_root_.` in the definition still derives",
            root_qualified_def,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # Regrouped conjunction: a nested body harmlessly wrapped in parentheses
    # is opaque to one depth-0 split, and both of its clause predicates left
    # the derived set while every token survived.
    regrouped = _fixture()
    regrouped[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def replyCallerLinkage (st : SystemState) : Prop :=\n"
        "  replyCallerLinkageReciprocal st ∧ blockedOnReplyHasReplyObject st",
        "def replyCallerLinkage (st : SystemState) : Prop :=\n"
        "  (replyCallerLinkageReciprocal st ∧ blockedOnReplyHasReplyObject st)",
    )
    regrouped["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (h : replyCallerLinkageReciprocal st')\n",
        )
    )
    cases.append(
        _Case(
            "clause of a parenthesised conjunction body still derives and flags",
            regrouped,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # Modifier-prefixed declaration after a definition: `private theorem …`
    # is a new declaration exactly as `theorem …` is, and a stop pattern
    # blind to the modifier appended the helper's text to the preceding
    # body -- its trailing conjunct then no longer matched and left the
    # derived set.
    modifier_stop = _fixture()
    modifier_stop[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def replyCallerLinkage (st : SystemState) : Prop :=\n"
        "  replyCallerLinkageReciprocal st ∧ blockedOnReplyHasReplyObject st",
        "def replyCallerLinkage (st : SystemState) : Prop :=\n"
        "  replyCallerLinkageReciprocal st ∧ blockedOnReplyHasReplyObject st\n"
        "\n"
        "private theorem replyCallerLinkageTrivial (st : SystemState) : True :=\n"
        "  trivial",
    )
    modifier_stop["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (h : blockedOnReplyHasReplyObject st')\n",
        )
    )
    cases.append(
        _Case(
            "a `private theorem` after a definition still bounds its body",
            modifier_stop,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # Unicode state binder: `(σ : SystemState)` is a routine Lean binder,
    # and an ASCII-only binder class dropped the refactored body from the
    # map -- its clauses left the derived set with every token present.
    unicode_binder = _fixture()
    unicode_binder[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def replyCallerLinkage (st : SystemState) : Prop :=\n"
        "  replyCallerLinkageReciprocal st ∧ blockedOnReplyHasReplyObject st",
        "def replyCallerLinkage (σ : SystemState) : Prop :=\n"
        "  replyCallerLinkageReciprocal σ ∧ blockedOnReplyHasReplyObject σ",
    )
    unicode_binder["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (h : replyCallerLinkageReciprocal st')\n",
        )
    )
    cases.append(
        _Case(
            "clause of a conjunct with a Unicode binder still derives and flags",
            unicode_binder,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # Named-argument spelling: `ipcInvariantFull (st := st')` applies the
    # invariant to `st'`, and treating the `st := st'` group as an opaque
    # compound state let the whole-bundle post-state hypothesis compare
    # unequal to the conclusion's `st'` and pass.
    named_argument = _fixture()
    named_argument["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hInv' : ipcInvariantFull (st := st'))\n",
        ).replace("  exact sample st st' hInv hStep", "  exact hInv'")
    )
    cases.append(
        _Case(
            "whole invariant hypothesised of the conclusion state by named argument",
            named_argument,
            True,
            check="no_conclusion_state_hypothesis",
            mutation="preserving",
        )
    )

    # `private def` conjunct: the modifier fix must reach the collected
    # declaration itself, not only the stop pattern -- a `private def`
    # nested conjunct vanished from the body map with every token present.
    private_def = _fixture()
    private_def[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def replyCallerLinkage (st : SystemState) : Prop :=",
        "private def replyCallerLinkage (st : SystemState) : Prop :=",
    )
    private_def["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (h : replyCallerLinkageReciprocal st')\n",
        )
    )
    cases.append(
        _Case(
            "clause of a `private def` conjunct still derives and flags",
            private_def,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # Result mentioned but not returned: the step equation carries the
    # conclusion state *inside* its ok-payload while returning an unrelated
    # state -- the mention-in-RHS rule accepted this; the structural parse
    # of the returned component does not.
    mentioned_result = _fixture()
    mentioned_result["SeLe4n/Kernel/API.lean"] = CLEAN_PAYOFF.replace(
        """theorem dispatchSyscall_preserves_ipcInvariantFull
    (st st' : SystemState) (hInv : ipcInvariantFull st)
    (hStep : dispatchSyscall st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hInv hStep""",
        """theorem dispatchSyscall_preserves_ipcInvariantFull
    (st stMid st' : SystemState) (hInv : ipcInvariantFull st)
    (hStep : dispatchSyscall st = .ok ((someMessageAbout st'), stMid))
    (hRelay : someOtherOperation stMid = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st stMid st' hInv hStep hRelay""",
    )
    cases.append(
        _Case(
            "payoff step mentions the conclusion state without returning it",
            mentioned_result,
            True,
            check="payoff_statement",
            mutation="preserving",
        )
    )

    # Compound intermediate state: an invariant-family hypothesis on
    # `(someOperation st).2` must not launder that expression into the
    # pre-state set when no step equation names `someOperation` -- the
    # wholesale compound acceptance did exactly that.
    compound_mid = _fixture()
    compound_mid["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hMid : ipcInvariantFull (someOperation st).2)\n"
            "    (hT : blockedThreadsPendingMessageConsistent (someOperation st).2)\n",
        )
    )
    cases.append(
        _Case(
            "conjunct on an unanchored compound state is not laundered as pre",
            compound_mid,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # Unicode-named bundle: `τ_preserves_ipcInvariantFull` is a valid Lean
    # declaration carrying the family marker, and an ASCII-first name class
    # dropped it -- threading included -- from the census entirely.
    unicode_bundle = _fixture()
    unicode_bundle["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE
        + "\ntheorem τ_preserves_ipcInvariantFull\n"
        "    (st st' : SystemState)\n"
        "    (hInv : ipcInvariantFull st)\n"
        "    (hT : blockedThreadsPendingMessageConsistent st')\n"
        "    (hStep : endpointSendDual st = .ok ((), st')) :\n"
        "    ipcInvariantFull st' := by\n"
        "  exact sample st st' hInv hT hStep\n"
    )
    cases.append(
        _Case(
            "a Unicode-named bundle stays in the census and its threading flags",
            unicode_bundle,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # Attributed conjunct definition: `@[simp] def replyCallerLinkage …` is
    # routine annotation, and a collector blind to attribute blocks dropped
    # the body -- its clauses left the derived set with every token present.
    attributed_def = _fixture()
    attributed_def[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def replyCallerLinkage (st : SystemState) : Prop :=",
        "@[simp] def replyCallerLinkage (st : SystemState) : Prop :=",
    )
    attributed_def["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (h : replyCallerLinkageReciprocal st')\n",
        )
    )
    cases.append(
        _Case(
            "clause of an attributed conjunct definition still derives and flags",
            attributed_def,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # Named field projections: `ctx.input` and `ctx.output` are different
    # state expressions, and a numeric-only projection chain truncated both
    # to `ctx` -- the threaded conjunct then compared equal to the pre-state.
    named_projection = _fixture()
    named_projection["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        "theorem endpointSendDual_preserves_ipcInvariantFull\n"
        "    (ctx : SendContext) (st' : SystemState)\n"
        "    (hInv : ipcInvariantFull ctx.input)\n"
        "    (hT : blockedThreadsPendingMessageConsistent ctx.output)\n"
        "    (hStep : endpointSendDual ctx.input = .ok ((), st')) :\n"
        "    ipcInvariantFull st' := by\n"
        "  exact sample ctx st' hInv hT hStep\n"
    )
    cases.append(
        _Case(
            "conjunct on a different named projection than the pre-state flags",
            named_projection,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # Lowercase namespace threading: Lean permits lowercase namespaces, and
    # the case-based qualifier rule read `foo.` as a projection receiver --
    # the binder-name filter reads the statement instead.
    lowercase_namespace = _fixture()
    lowercase_namespace["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hT : foo.blockedThreadsPendingMessageConsistent st')\n",
        )
    )
    cases.append(
        _Case(
            "conjunct threaded behind a lowercase namespace qualifier",
            lowercase_namespace,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # A projection of a local binder is NOT a namespace application: the
    # receiver is the statement's own hypothesis, and flagging it would make
    # every structure-bundle projection a false positive.
    projection_receiver = _fixture()
    projection_receiver["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hView : hInv.blockedThreadsPendingMessageConsistent st')\n",
        )
    )
    cases.append(
        _Case(
            "a binder projection is not misread as a namespace application",
            projection_receiver,
            False,
        )
    )

    # Arrow-form root refactor beside a shadow: the binder moves right of the
    # colon (`: SystemState → Prop := fun s => …`), the old collector dropped
    # the canonical body, and the shadow's reduced conjunct set was all that
    # remained -- scoring real threading clean.
    arrow_root = _fixture()
    arrow_root[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def ipcInvariantFull (st : SystemState) : Prop :=\n"
        "  blockedThreadsPendingMessageConsistent st ∧ replyCallerLinkage st",
        "def ipcInvariantFull : SystemState → Prop := fun s =>\n"
        "  blockedThreadsPendingMessageConsistent s ∧ replyCallerLinkage s",
    )
    arrow_root["SeLe4n/Kernel/IPC/Invariant/Structural/ShadowDefs.lean"] = (
        "namespace Shadow\n"
        "\n"
        "def harmlessObservation (st : SystemState) : Prop :=\n"
        "  True\n"
        "\n"
        "def ipcInvariantFull (st : SystemState) : Prop :=\n"
        "  harmlessObservation st\n"
        "\n"
        "end Shadow\n"
    )
    arrow_root["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hT : blockedThreadsPendingMessageConsistent st')\n",
        )
    )
    cases.append(
        _Case(
            "an arrow-form root refactor still derives beside a shadow",
            arrow_root,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # The canonical root moves into a namespace: every token survives, but
    # the derived union would hold only shadow bodies -- the canonical-prefix
    # requirement refuses to derive from shadows alone.
    displaced_root = _fixture()
    displaced_root[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def ipcInvariantFull (st : SystemState) : Prop :=\n"
        "  blockedThreadsPendingMessageConsistent st ∧ replyCallerLinkage st",
        "namespace Shadow\n"
        "\n"
        "def ipcInvariantFull (st : SystemState) : Prop :=\n"
        "  blockedThreadsPendingMessageConsistent st ∧ replyCallerLinkage st\n"
        "\n"
        "end Shadow",
    )
    cases.append(
        _Case(
            "the root displaced into a namespace fails the canonical requirement",
            displaced_root,
            True,
            check="conjuncts_derived",
            mutation="preserving",
        )
    )

    # `opaque` after a definition is a declaration boundary: blind to it, the
    # collector absorbed the opaque into the preceding body and its trailing
    # conjunct left the derived set.
    opaque_stop = _fixture()
    opaque_stop[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def replyCallerLinkage (st : SystemState) : Prop :=\n"
        "  replyCallerLinkageReciprocal st ∧ blockedOnReplyHasReplyObject st",
        "def replyCallerLinkage (st : SystemState) : Prop :=\n"
        "  replyCallerLinkageReciprocal st ∧ blockedOnReplyHasReplyObject st\n"
        "\n"
        "opaque replyCallerLinkageOpaque : Prop",
    )
    opaque_stop["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (h : blockedOnReplyHasReplyObject st')\n",
        )
    )
    cases.append(
        _Case(
            "an `opaque` declaration after a definition still bounds its body",
            opaque_stop,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # Named-argument spelling in the *definition*: the bundle comparisons
    # normalise `(st := st')` while the definition side accepted only the
    # positional form, so the conjunct left the derived set.
    named_arg_def = _fixture()
    named_arg_def[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def ipcInvariantFull (st : SystemState) : Prop :=\n"
        "  blockedThreadsPendingMessageConsistent st ∧ replyCallerLinkage st",
        "def ipcInvariantFull (st : SystemState) : Prop :=\n"
        "  blockedThreadsPendingMessageConsistent (st := st) ∧ replyCallerLinkage st",
    )
    named_arg_def["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hT : blockedThreadsPendingMessageConsistent st')\n",
        )
    )
    cases.append(
        _Case(
            "conjunct spelled as a named argument in the definition still derives",
            named_arg_def,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # Reflexive-equality anchoring: `hAnchor : stMid = stMid` is a valid
    # hypothesis relating nothing to the transition, and wholesale
    # equality-group harvesting let it launder `stMid` into the pre-states.
    reflexive_anchor = _fixture()
    reflexive_anchor["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (st st' : SystemState)\n",
            "    (st stMid st' : SystemState)\n",
        ).replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hMid : ipcInvariantFull stMid)\n"
            "    (hAnchor : stMid = stMid)\n"
            "    (hT : blockedThreadsPendingMessageConsistent stMid)\n",
        )
    )
    cases.append(
        _Case(
            "a reflexive equality does not anchor an intermediate state",
            reflexive_anchor,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # Marker-substring imposter: `…ipcInvariantFullish` carries the marker in
    # its name while concluding `True`; counting it as an operation bundle
    # kept `family_nonempty` satisfied over an actually-empty family.
    imposter_family = _fixture()
    imposter_family["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        "theorem dummy_preserves_ipcInvariantFullish (st : SystemState) : True :=\n"
        "  trivial\n"
    )
    cases.append(
        _Case(
            "a marker-substring imposter concluding True is not the family",
            imposter_family,
            True,
            check="family_nonempty",
            mutation="preserving",
        )
    )

    # A declaration-shaped line inside a string literal is data, not a
    # declaration: the comment-free view keeps string contents, and the
    # census read a theorem statement out of one -- an inert string kept
    # `family_nonempty` satisfied over an actually-empty family.
    string_declaration = _fixture()
    string_declaration["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        'def bundleCatalogueNote : String :=\n'
        '  "theorem stringOnly_preserves_ipcInvariantFull\n'
        '    (st st\' : SystemState) (hInv : ipcInvariantFull st)\n'
        '    (hStep : endpointSendDual st = .ok ((), st\')) :\n'
        '    ipcInvariantFull st\' := by exact sample st st\' hInv hStep"\n'
    )
    cases.append(
        _Case(
            "a theorem-shaped string literal is not a family declaration",
            string_declaration,
            True,
            check="family_nonempty",
            mutation="preserving",
        )
    )

    # Lowercase qualifier in the *definition*: the binder-name fix reached
    # the scans and not the derivation, its sibling -- a lowercase-namespace
    # conjunct spelling dropped from the derived set with every token there.
    lowercase_def = _fixture()
    lowercase_def[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def ipcInvariantFull (st : SystemState) : Prop :=\n"
        "  blockedThreadsPendingMessageConsistent st ∧ replyCallerLinkage st",
        "def ipcInvariantFull (st : SystemState) : Prop :=\n"
        "  blockedThreadsPendingMessageConsistent st ∧ foo.replyCallerLinkage st",
    )
    lowercase_def["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (h : replyCallerLinkageReciprocal st')\n",
        )
    )
    cases.append(
        _Case(
            "conjunct spelled behind a lowercase qualifier still derives",
            lowercase_def,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # Unicode namespace scope: `namespace σ` is a valid scope the ASCII
    # scanner did not push, so a shadow inside it recorded the *enclosing*
    # canonical prefix and stood in for the deleted payoff.
    unicode_scope_payoff = _fixture()
    unicode_scope_payoff["SeLe4n/Kernel/API.lean"] = CLEAN_PAYOFF.replace(
        """theorem dispatchSyscall_preserves_ipcInvariantFull
    (st st' : SystemState) (hInv : ipcInvariantFull st)
    (hStep : dispatchSyscall st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hInv hStep""",
        """namespace σ

theorem dispatchSyscall_preserves_ipcInvariantFull
    (st st' : SystemState) (hInv : ipcInvariantFull st)
    (hStep : dispatchSyscall st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hInv hStep

end σ""",
    )
    cases.append(
        _Case(
            "a Unicode-namespaced shadow cannot stand in for a deleted payoff",
            unicode_scope_payoff,
            True,
            check="payoff_theorems",
            mutation="preserving",
        )
    )

    # Double-quote character literal: `'"'` is a valid Lean char literal, and
    # a lexer that toggled string state on the inner quote blanked the rest
    # of the file -- a threaded bundle after it vanished while another file's
    # bundle kept the family census satisfied.
    char_literal = _fixture()
    char_literal["SeLe4n/Kernel/IPC/Invariant/Structural/QuotedBundles.lean"] = (
        "def quoteCharacter : Char := '\"'\n"
        "\n"
        + CLEAN_BUNDLE.replace(
            "theorem endpointSendDual_preserves_ipcInvariantFull",
            "theorem endpointReceiveDual_preserves_ipcInvariantFull",
        ).replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hT : blockedThreadsPendingMessageConsistent st')\n",
        )
    )
    cases.append(
        _Case(
            "a bundle after a double-quote char literal stays in the census",
            char_literal,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # `class` after a definition is a declaration boundary like the rest:
    # blind to it, the collector absorbed the class body and the preceding
    # definition's trailing conjunct left the derived set.
    class_stop = _fixture()
    class_stop[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def replyCallerLinkage (st : SystemState) : Prop :=\n"
        "  replyCallerLinkageReciprocal st ∧ blockedOnReplyHasReplyObject st",
        "def replyCallerLinkage (st : SystemState) : Prop :=\n"
        "  replyCallerLinkageReciprocal st ∧ blockedOnReplyHasReplyObject st\n"
        "\n"
        "class ReplyLinkageMarker where\n"
        "  markerField : Prop",
    )
    class_stop["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (h : blockedOnReplyHasReplyObject st')\n",
        )
    )
    cases.append(
        _Case(
            "a `class` declaration after a definition still bounds its body",
            class_stop,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # The ASCII arrow spelling of the same telescope: `->` is `→`, and a
    # splitter that recognised only the Unicode arrow never separated the
    # premise carrying the whole-post-state hypothesis.
    ascii_arrow_premise = _fixture()
    ascii_arrow_premise["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    ipcInvariantFull st' := by\n  exact sample st st' hInv hStep",
            "    ipcInvariantFull st' -> ipcInvariantFull st' := by\n"
            "  exact fun h => h",
        )
    )
    cases.append(
        _Case(
            "the whole invariant as an ASCII-arrow premise is still caught",
            ascii_arrow_premise,
            True,
            check="no_conclusion_state_hypothesis",
            mutation="preserving",
        )
    )

    # Payoff-only family: every per-operation bundle deleted while the payoff
    # names (which carry the family marker) remain -- the census must not
    # count them as the measured population.
    payoff_only = _fixture()
    del payoff_only["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"]
    cases.append(
        _Case(
            "bundle family reduced to the payoff tier alone",
            payoff_only,
            True,
            check="family_nonempty",
            mutation="preserving",
        )
    )

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

    # The same degenerate threading with the hypothesis moved out of the named
    # binders into an unnamed implication premise after the declaration colon:
    # `ipcInvariantFull st' → ipcInvariantFull st'` proves nothing while the
    # binder-reading pre-state scan sees no post-state hypothesis at all.
    whole_premise_threaded = _fixture()
    whole_premise_threaded["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    ipcInvariantFull st' := by\n  exact sample st st' hInv hStep",
            "    ipcInvariantFull st' → ipcInvariantFull st' := by\n"
            "  exact fun h => h",
        )
    )
    cases.append(
        _Case(
            "the whole invariant is an unnamed premise of the conclusion's state",
            whole_premise_threaded,
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
    honest_registration["SeLe4n/Kernel/API.lean"] = CLEAN_PAYOFF.replace(
        """theorem dispatchSyscall_preserves_ipcInvariantFull
    (st st' : SystemState) (hInv : ipcInvariantFull st)
    (hStep : dispatchSyscall st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hInv hStep

""",
        "",
    )
    honest_registration[PENDING_FILE] = (
        "dispatchSyscall_preserves_ipcInvariantFull | WS-RR RR3.16 | sized and deferred\n"
    )
    cases.append(
        _Case("a registered residual is reported, not failed", honest_registration, False)
    )

    # A family application under a disjunction: `ipcInvariantFull st' ∨ True`
    # is provable by its right arm, so a find-anywhere conclusion scan read a
    # family conclusion out of a theorem that carries no invariant.  The
    # entailment parse reads `None`, and a marker-named `None` is a reported
    # violation, never a silent census drop.
    disjunctive = _fixture()
    disjunctive["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    ipcInvariantFull st' := by",
            "    ipcInvariantFull st' ∨ True := by",
        )
    )
    cases.append(
        _Case(
            "a family application under a disjunction is not a family conclusion",
            disjunctive,
            True,
            check="family_conclusion",
            mutation="preserving",
        )
    )

    # A named-argument label naming the *called* predicate's binder: the
    # derivation pinned the label to the literal `st`, so
    # `replyCallerLinkage (σ := st)` dropped the predicate -- and its clause
    # conjuncts -- from the derived set, and a bundle threading the clause
    # scored clean.
    named_label = _fixture()
    named_label[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def replyCallerLinkage (st : SystemState) : Prop :=\n"
        "  replyCallerLinkageReciprocal st ∧ blockedOnReplyHasReplyObject st",
        "def replyCallerLinkage (σ : SystemState) : Prop :=\n"
        "  replyCallerLinkageReciprocal σ ∧ blockedOnReplyHasReplyObject σ",
    ).replace(
        "  blockedThreadsPendingMessageConsistent st ∧ replyCallerLinkage st",
        "  blockedThreadsPendingMessageConsistent st ∧ replyCallerLinkage (σ := st)",
    )
    named_label["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hR : replyCallerLinkageReciprocal st')\n",
        )
    )
    cases.append(
        _Case(
            "a conjunct applied through a non-`st` named-argument label still derives",
            named_label,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # An `include`d section-variable hypothesis: Lean elaborates it into the
    # theorem's parameter list, but it is absent from the declaration slice,
    # so a post-state conjunct hypothesis was real while invisible.
    ambient_variable = _fixture()
    ambient_variable["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        "variable {st' : SystemState}\n"
        "variable (hAmbient : blockedThreadsPendingMessageConsistent st')\n"
        "include hAmbient\n"
        "\n"
        + CLEAN_BUNDLE.replace(
            "    (st st' : SystemState)\n",
            "    (st : SystemState)\n",
        )
    )
    cases.append(
        _Case(
            "an included section-variable hypothesis is part of the telescope",
            ambient_variable,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # A predicate symbol as the only overlap between an equality group and
    # the conclusion: `hAnchor : ipcInvariantFull stMid = ipcInvariantFull
    # stMid` shares `ipcInvariantFull` with the conclusion's tokens, and
    # unfiltered connectivity anchored `stMid` through it -- a Prop-former
    # bridging components it has no term-level business connecting.
    bridged_anchor = _fixture()
    bridged_anchor["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (st st' : SystemState)\n",
            "    (st stMid st' : SystemState)\n",
        ).replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hAnchor : ipcInvariantFull stMid = ipcInvariantFull stMid)\n"
            "    (hMid : ipcInvariantCore stMid)\n"
            "    (hT : blockedThreadsPendingMessageConsistent stMid)\n",
        )
    )
    cases.append(
        _Case(
            "a predicate symbol shared with the conclusion does not anchor a state",
            bridged_anchor,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # A family application heading an equality: `ipcInvariantFull st' = False`
    # contradicts the invariant, and rejecting an enumerated `∨`/`↔` still
    # accepted it -- the application must occupy the conjunct.
    equality_conclusion = _fixture()
    equality_conclusion["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    ipcInvariantFull st' := by",
            "    ipcInvariantFull st' = False := by",
        )
    )
    cases.append(
        _Case(
            "a family application heading an equality is not a family conclusion",
            equality_conclusion,
            True,
            check="family_conclusion",
            mutation="preserving",
        )
    )

    # An *indented* command boundary: Lean does not require column zero, so
    # `  class …` bounds the preceding body exactly as the flush spelling
    # does -- an anchor blind to indentation absorbed it.
    indented_class = _fixture()
    indented_class[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def replyCallerLinkage (st : SystemState) : Prop :=\n"
        "  replyCallerLinkageReciprocal st ∧ blockedOnReplyHasReplyObject st",
        "def replyCallerLinkage (st : SystemState) : Prop :=\n"
        "  replyCallerLinkageReciprocal st ∧ blockedOnReplyHasReplyObject st\n"
        "\n"
        "  class ReplyLinkageMarker where\n"
        "    markerField : Prop",
    )
    indented_class["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (h : blockedOnReplyHasReplyObject st')\n",
        )
    )
    cases.append(
        _Case(
            "an indented `class` declaration still bounds the preceding body",
            indented_class,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # A tautological equation sharing a *real* anchor token: `pair st' stMid
    # = pair st' stMid` relates nothing, yet its genuine `st'` connected it
    # to the conclusion and `stMid` rode along into the anchors.
    tautological_anchor = _fixture()
    tautological_anchor["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (st st' : SystemState)\n",
            "    (st stMid st' : SystemState)\n",
        ).replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hAnchor : pair st' stMid = pair st' stMid)\n"
            "    (hMid : ipcInvariantCore stMid)\n"
            "    (hT : blockedThreadsPendingMessageConsistent stMid)\n",
        )
    )
    cases.append(
        _Case(
            "a tautological equation does not anchor the states it mentions",
            tautological_anchor,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # A guillemet-quoted namespace is a scope: unparsed, its declarations
    # recorded the *enclosing* canonical prefix, so a quoted shadow stood in
    # for a deleted payoff.
    quoted_namespace = _fixture()
    quoted_namespace["SeLe4n/Kernel/API.lean"] = CLEAN_PAYOFF.replace(
        """theorem dispatchSyscallChecked_preserves_ipcInvariantFull
    (st st' : SystemState) (hInv : ipcInvariantFull st)
    (hStep : dispatchSyscallChecked st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hInv hStep""",
        """namespace «shadow»

theorem dispatchSyscallChecked_preserves_ipcInvariantFull
    (st st' : SystemState) (hInv : ipcInvariantFull st)
    (hStep : dispatchSyscallChecked st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hInv hStep

end «shadow»""",
    )
    cases.append(
        _Case(
            "a quoted-namespace shadow cannot stand in for a deleted payoff",
            quoted_namespace,
            True,
            check="payoff_theorems",
            mutation="preserving",
        )
    )

    # A double quote inside a guillemet-quoted identifier is part of the
    # identifier, not a string delimiter: a lexer that opened a string there
    # blanked the rest of the file and its threaded bundle with it.
    quoted_identifier = _fixture()
    quoted_identifier[
        "SeLe4n/Kernel/IPC/Invariant/Structural/QuotedIdentBundles.lean"
    ] = (
        'def «a"b» : Nat := 0\n'
        "\n"
        + CLEAN_BUNDLE.replace(
            "theorem endpointSendDual_preserves_ipcInvariantFull",
            "theorem endpointStashDual_preserves_ipcInvariantFull",
        ).replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hT : blockedThreadsPendingMessageConsistent st')\n",
        )
    )
    cases.append(
        _Case(
            "a threaded bundle after a quote-bearing quoted identifier is seen",
            quoted_identifier,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # A `private` payoff under the canonical namespace: presence that
    # discards visibility scored it as the top-level consumer, which
    # downstream modules cannot even name.
    private_payoff = _fixture()
    private_payoff["SeLe4n/Kernel/API.lean"] = CLEAN_PAYOFF.replace(
        "theorem dispatchSyscall_preserves_ipcInvariantFull",
        "private theorem dispatchSyscall_preserves_ipcInvariantFull",
    )
    cases.append(
        _Case(
            "a private canonical payoff is not a top-level consumer",
            private_payoff,
            True,
            check="payoff_theorems",
            mutation="preserving",
        )
    )

    # A transparent alias of a measured conjunct: binding it on the
    # post-state is definitionally the same hypothesis, invisible to a scan
    # over canonical names only.
    alias_threading = _fixture()
    alias_threading["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        "abbrev threadedAliasHypothesis (s : SystemState) : Prop :=\n"
        "  blockedThreadsPendingMessageConsistent s\n"
        "\n"
        + CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hA : threadedAliasHypothesis st')\n",
        )
    )
    cases.append(
        _Case(
            "a transparent alias of a conjunct is measured like the conjunct",
            alias_threading,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # A `by exact` root body beside a partial shadow: the canonical body
    # derived nothing, the shadow kept the union nonempty, and the conjunct
    # only the canonical body carries went unmeasured.
    tactic_root = _fixture()
    tactic_root[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def ipcInvariantFull (st : SystemState) : Prop :=\n"
        "  blockedThreadsPendingMessageConsistent st ∧ replyCallerLinkage st",
        "def ipcInvariantFull (st : SystemState) : Prop :=\n"
        "  by exact (blockedThreadsPendingMessageConsistent st ∧ replyCallerLinkage st)\n"
        "\n"
        "namespace ShadowView\n"
        "\n"
        "def ipcInvariantFull (st : SystemState) : Prop :=\n"
        "  blockedThreadsPendingMessageConsistent st\n"
        "\n"
        "end ShadowView",
    )
    tactic_root["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hRecip : replyCallerLinkageReciprocal st')\n",
        )
    )
    cases.append(
        _Case(
            "a `by exact` root body still derives its conjunction",
            tactic_root,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # The same shape behind a tactic block the unwrap does not know: the
    # canonical body must contribute on its own, or the derived set is a
    # shadow's -- reported, never silently narrowed.
    opaque_root = _fixture()
    opaque_root[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def ipcInvariantFull (st : SystemState) : Prop :=\n"
        "  blockedThreadsPendingMessageConsistent st ∧ replyCallerLinkage st",
        "def ipcInvariantFull (st : SystemState) : Prop :=\n"
        "  by { exact (blockedThreadsPendingMessageConsistent st ∧ replyCallerLinkage st) }\n"
        "\n"
        "namespace ShadowView\n"
        "\n"
        "def ipcInvariantFull (st : SystemState) : Prop :=\n"
        "  blockedThreadsPendingMessageConsistent st\n"
        "\n"
        "end ShadowView",
    )
    cases.append(
        _Case(
            "a canonical root body that derives nothing is reported, not shadowed",
            opaque_root,
            True,
            check="conjuncts_derived",
            mutation="preserving",
        )
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

    # `--report` must fail on what the default mode fails on: it is cited as
    # an evidence command, and a census that prints violations while exiting
    # 0 scores them as success (PR #886 review).
    with tempfile.TemporaryDirectory() as tmp:
        _write_tree(tmp, threaded)
        import contextlib, io
        with contextlib.redirect_stdout(io.StringIO()):
            rc = report(tmp)
        if rc == 0:
            failures += 1
            print("[SELF-TEST FAIL] --report exits 0 on a threaded fixture")
        else:
            print("[SELF-TEST OK]   caught: --report fails on a threaded fixture [preserving]")

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
