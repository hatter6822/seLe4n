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

import functools
import os
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lean_code_view  # noqa: E402  (path set up immediately above)

# The repository's one quote-aware shell resolver (see CLAUDE.md, "A
# presence check is not a relation check"): commands are read as commands,
# never as line text, so an `echo lake build …` can not mint a build root.
import check_aarch64_cross_target as shell_view  # noqa: E402

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
    "grammar_coverage",
    "minting_machinery",
    "family_references",
    "conjuncts_derived",
    "family_nonempty",
    "family_conclusion",
    "no_post_state_binding",
    "no_conclusion_state_hypothesis",
    "payoff_theorems",
    "payoff_statement",
)

# Declaration-minting machinery: the keywords through which Lean code can
# bring a declaration into existence *without* spelling a declaration the
# census's grammars read.  `macro`/`macro_rules`/`syntax` targeting the
# command category expand to whole commands; `elab`/`elab_rules`,
# `run_cmd`/`run_elab`, `#eval` of a monadic action and
# `initialize`/`builtin_initialize` execute arbitrary elaborator code that
# can call `addDecl`; `declare_syntax_cat` opens a category for any of
# them.  A command *invocation* can then sit at any indentation -- the
# `grammar_coverage` tripwire reads column 0 only, and an indented unknown
# command is indistinguishable in text from a term continuation (PR #886
# review) -- so the gate polices the *mechanism* instead of the position:
# with no external `require` in `lakefile.toml`, an unknown command can
# only exist through machinery declared in this tree, and every machinery
# token is held to the pin below.  `notation`/`infix`-family sugar is
# deliberately outside the set: it expands to term-category rewriting,
# which cannot mint a declaration, and the `(name := …)` parser
# declaration it can mint is a `ParserDescr` whose spelled name the
# `family_references` check resolves like any other token.
_MACHINERY = (
    "macro_rules",
    "macro",
    "elab_rules",
    "elab",
    "syntax",
    "builtin_initialize",
    "initialize",
    "run_cmd",
    "run_elab",
    "declare_syntax_cat",
)

# Every machinery occurrence in the tree, reviewed once and pinned as
# (file, keyword) -> exact count.  The scan is derived (every token in the
# code view); the pin is the reviewed set -- the enumeration-as-pin shape
# CLAUDE.md prescribes.  New machinery anywhere, or a second occurrence in
# a pinned file, fails loudly and gets reviewed; a pinned file whose count
# *fell* fails too, so an entry cannot rot into a standing exemption while
# the file lives.  A pinned file absent from the tree is inert: deletion
# removes the minting surface, and file existence is other gates' concern.
# The reviewed occupants: thirteen theorem-inventory DSLs (a term-category
# `syntax` + `macro_rules` pair each), the manifest's two `census_entry`
# term macros and its two `run_cmd` propositionality censuses, one local
# tactic macro, one per-core NI name macro pair, and three `initialize`
# blocks (a tag attribute and two FFI state refs).  Term-category macros
# cannot mint declarations; the `run_cmd`/`initialize` sites can, which is
# exactly why their files are pinned by count.
MACHINERY_PINS = {
    ("SeLe4n/Kernel/Concurrency/Locks/Deadlock.lean", "macro"): 1,
    ("SeLe4n/Kernel/Concurrency/Locks/DeadlockInventory.lean", "macro_rules"): 1,
    ("SeLe4n/Kernel/Concurrency/Locks/DeadlockInventory.lean", "syntax"): 1,
    ("SeLe4n/Kernel/Concurrency/Locks/LockSetInventory.lean", "macro_rules"): 1,
    ("SeLe4n/Kernel/Concurrency/Locks/LockSetInventory.lean", "syntax"): 1,
    ("SeLe4n/Kernel/Concurrency/Locks/SerializabilityInventory.lean", "macro_rules"): 1,
    ("SeLe4n/Kernel/Concurrency/Locks/SerializabilityInventory.lean", "syntax"): 1,
    ("SeLe4n/Kernel/Concurrency/Locks/WithLockSetInventory.lean", "macro_rules"): 1,
    ("SeLe4n/Kernel/Concurrency/Locks/WithLockSetInventory.lean", "syntax"): 1,
    ("SeLe4n/Kernel/Concurrency/PhaseTheoremManifest.lean", "macro"): 2,
    ("SeLe4n/Kernel/Concurrency/PhaseTheoremManifest.lean", "run_cmd"): 2,
    ("SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean", "macro_rules"): 1,
    ("SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean", "syntax"): 1,
    ("SeLe4n/Kernel/Scheduler/Invariant/PerCoreInvariantSuiteInventory.lean", "macro_rules"): 1,
    ("SeLe4n/Kernel/Scheduler/Invariant/PerCoreInvariantSuiteInventory.lean", "syntax"): 1,
    ("SeLe4n/Kernel/Scheduler/Operations/CrossCoreWakeInventory.lean", "macro_rules"): 1,
    ("SeLe4n/Kernel/Scheduler/Operations/CrossCoreWakeInventory.lean", "syntax"): 1,
    ("SeLe4n/Kernel/Scheduler/Operations/PerCoreCbsInventory.lean", "macro_rules"): 1,
    ("SeLe4n/Kernel/Scheduler/Operations/PerCoreCbsInventory.lean", "syntax"): 1,
    ("SeLe4n/Kernel/Scheduler/Operations/PerCoreDomainInventory.lean", "macro_rules"): 1,
    ("SeLe4n/Kernel/Scheduler/Operations/PerCoreDomainInventory.lean", "syntax"): 1,
    ("SeLe4n/Kernel/Scheduler/Operations/PerCoreIdleInventory.lean", "macro_rules"): 1,
    ("SeLe4n/Kernel/Scheduler/Operations/PerCoreIdleInventory.lean", "syntax"): 1,
    ("SeLe4n/Kernel/Scheduler/Operations/PerCoreTimerInventory.lean", "macro_rules"): 1,
    ("SeLe4n/Kernel/Scheduler/Operations/PerCoreTimerInventory.lean", "syntax"): 1,
    ("SeLe4n/Kernel/Scheduler/Operations/PerCoreWcrtInventory.lean", "macro_rules"): 1,
    ("SeLe4n/Kernel/Scheduler/Operations/PerCoreWcrtInventory.lean", "syntax"): 1,
    ("SeLe4n/Kernel/Scheduler/PriorityInheritance/PerCoreInventory.lean", "macro_rules"): 1,
    ("SeLe4n/Kernel/Scheduler/PriorityInheritance/PerCoreInventory.lean", "syntax"): 1,
    ("SeLe4n/Model/Object/PerObjectLockInventory.lean", "macro_rules"): 1,
    ("SeLe4n/Model/Object/PerObjectLockInventory.lean", "syntax"): 1,
    ("SeLe4n/Platform/FFI.lean", "initialize"): 2,
    ("SeLe4n/Prelude.lean", "initialize"): 1,
}

# The declaration modifiers and top-level commands this gate's grammars
# know.  SINGLE SOURCE (PR #886 review, the churn diagnosis): eight
# consecutive review rounds each taught one more spelling of Lean's
# surface grammar to one more regex, and the class does not converge while
# each site carries its own alternation -- so `_COMMAND_STOP`, the five
# modifier runs, and the `grammar_coverage` tripwire are all built from
# these two tuples, and a keyword learned once is learned everywhere.  The
# tripwire is what ends the *silent* half of the class: a column-0 token
# outside these tuples is a command whose declarations every census and
# scan would miss, and it now fails the gate loudly instead of waiting for
# the next review round to find it.  Longest-first join keeps prefixed
# pairs (`macro_rules`/`macro`, `builtin_initialize`/`initialize`)
# unambiguous without relying on backtracking.
_MODIFIERS = (
    "public",
    "private",
    "protected",
    "partial",
    "noncomputable",
    "unsafe",
    "local",
    "scoped",
    "nonrec",
    "meta",
)
_COMMANDS = (
    "def",
    "theorem",
    "lemma",
    "abbrev",
    "structure",
    "inductive",
    "instance",
    "class",
    "end",
    "namespace",
    "open",
    "opaque",
    "axiom",
    "example",
    "attribute",
    "universe",
    "variable",
    "include",
    "omit",
    "macro_rules",
    "macro",
    "syntax",
    "elab_rules",
    "elab",
    "deriving",
    "mutual",
    "section",
    "set_option",
    "export",
    "import",
    "initialize",
    "builtin_initialize",
    "run_cmd",
    "notation",
    "infixl",
    "infixr",
    "infix",
    "postfix",
    "prefix",
    "register_option",
    "prelude",
    "where",
)
_MODIFIER_ALT = "|".join(sorted(_MODIFIERS, key=len, reverse=True))
_COMMAND_ALT = "|".join(sorted(_COMMANDS, key=len, reverse=True))
_MODIFIER_RUN = r"(?:(?:" + _MODIFIER_ALT + r")\s+)*"
# `open … in <decl>`, `set_option … in <decl>`, `include … in <decl>` and
# `omit … in <decl>` wrap a declaration on one line (PR #886 review sweep,
# toolchain-verified): a census blind to the composite prefix missed the
# declaration behind it.
_COMPOSITE_PREFIX = r"(?:(?:open|set_option|include|omit)[^\n]*?\s+in\s+)*"

# The forms a *family conclusion* may take: every full-invariant view, and
# deliberately not `ipcInvariantCore` (PR #886 review): a marker-named
# theorem concluding only the structural core downgrades the name's claim
# while keeping its census seat -- the core stays pre-state vocabulary
# (`PRE_STATE_PREDICATES`), never a conclusion the family accepts.
_CONCLUSION_FORMS = tuple(
    name for name in PRE_STATE_PREDICATES if name != "ipcInvariantCore"
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
    # `def` and `abbrev` too (PR #886 review): a proof introduced as
    # `def X_preserves_… : ipcInvariantFull st' := …` is a valid Lean
    # spelling of the same declaration, and a census that stopped at
    # `theorem|lemma` let a def-spelled threaded bundle bypass every check.
    # `opaque` and `axiom` complete the proof-capable forms (PR #886
    # review, the next round, plus the sweep): `opaque X_preserves_… (…) :
    # ipcInvariantFull st' := …` is accepted by Lean and was invisible;
    # `axiom` cannot survive the no-axiom gate, but a marker-named axiom is
    # a family *statement* and this census must not be the scanner that
    # missed it.  Either may omit `:=`, in which case `signature_end` runs
    # to the next declaration's `:=` -- over-capture, which can only add
    # scanned text, never remove the following declaration's own entry.
    # `nonrec` joins the modifier run everywhere the run appears (PR #886
    # review: `nonrec theorem` is a routine spelling, and a grammar without
    # the modifier dropped the whole declaration from the census).
    # `instance` too (PR #886 review, another round -- verified against the
    # toolchain: `instance X_preserves_… (…) : ipcInvariantFull st' := …`
    # elaborates even though the type is no class, contradicting the
    # earlier assumption that it could not); its optional priority group is
    # skipped, and an *anonymous* instance has no name for the marker to
    # live in, so the name capture correctly refuses it.  `public` joins
    # the modifier run for the module system's spellings.
    r"^\s*" + _COMPOSITE_PREFIX + r"(?:@\[[^\]]*\]\s*)*"
    r"(?P<mods>" + _MODIFIER_RUN + r")"
    r"(?:theorem|lemma|def|abbrev|opaque|axiom"
    r"|instance(?:\s*\(\s*priority\s*:=[^)]*\))?)\s+"
    r"(?P<name>«[^»\n]*»|[^\W\d][\w'.!?]*)",
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
    case rule was an enumeration.  A chain segment may be guillemet-quoted
    (PR #886 review: `«foo».conjunct st'` is valid Lean the plain-identifier
    grammar could not reach, so the qualified hypothesis went unscanned).
    """
    return (
        r"(?<![\w'.])((?:(?:«[^»\n]*»|[^\W\d][\w']*)\.)*)"
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


def _has_depth0_connective(text: str) -> bool:
    """True when `text` carries a depth-0 connective weaker than `∧`.

    `∨`, `↔`, `→` and their ASCII spellings (`\\/`, `->`): a proposition
    under any of them is not entailed by the hypothesis that contains it,
    so both the step-equation validation and the equation-anchor harvest
    refuse to read through one (PR #886 review: `dispatchSyscall st = .ok
    ((), st') ∨ True` validated as a step after the connective cut kept
    only the arm).  `∧` is deliberately absent: conjunction entails its
    parts, and callers split on it first.
    """
    depth = 0
    for offset, char in enumerate(text):
        if char in _OPEN:
            depth += 1
        elif char in _CLOSE:
            depth -= 1
        elif depth == 0 and (
            char in "∨↔→"
            or (char == "-" and text[offset + 1 : offset + 2] == ">")
            or (char == "\\" and text[offset + 1 : offset + 2] == "/")
        ):
            return True
    return False


def _equation_groups(group: str) -> list[list[str]]:
    """Each *entailed* plain equality in a binder group's type, as its sides.

    The group's type (after its first depth-0 colon) is split on depth-0
    `∧` -- conjuncts are entailed -- and each part carrying a plain depth-0
    `=` (not `:=`, `==`, `=>`) with no weaker depth-0 connective yields one
    equation, returned as the list of texts flanking its `=` signs (a
    chained `a = b = c` yields three sides).  A part under `∨`/`↔`/`→` is
    not established by the hypothesis and contributes nothing -- `stMid =
    st' ∨ True` must not anchor `stMid` (PR #886 review).
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
    equations: list[list[str]] = []
    for part in split_conjunction(body):
        if _has_depth0_connective(part):
            continue
        cuts = []
        depth = 0
        for offset, char in enumerate(part):
            if char in _OPEN:
                depth += 1
            elif char in _CLOSE:
                depth -= 1
            elif (
                char == "="
                and depth == 0
                and part[offset + 1 : offset + 2] not in ("=", ">")
                and (offset == 0 or part[offset - 1] not in ":=!<>")
            ):
                cuts.append(offset)
        if not cuts:
            continue
        sides = []
        start = 0
        for cut in cuts:
            sides.append(part[start:cut])
            start = cut + 1
        sides.append(part[start:])
        equations.append(sides)
    return equations


def _next_unit(text: str, index: int) -> tuple[str, int] | None:
    """The next argument unit at or after `index`: an identifier, numeral,
    or bracketed group, extended with its projection chain.  None at end of
    text or on a character no argument can start with (an operator)."""
    while index < len(text) and text[index] in " \t\n":
        index += 1
    if index >= len(text):
        return None
    if text[index] in _OPEN:
        end = balanced_span(text, index)
        if end is None:
            return None
        chain = re.match(r"(?:\.(?:\d+|[^\W\d][\w'!?]*))*", text[end:])
        return text[index : end + chain.end()], end + chain.end()
    unit = re.match(
        r"(?:[^\W\d][\w'!?]*|\d+)(?:\.(?:\d+|[^\W\d][\w'!?]*))*",
        text[index:],
    )
    if unit is None or unit.end() == 0:
        return None
    return text[index : index + unit.end()], index + unit.end()


def _argument_at(text: str, start: int, index: int) -> str | None:
    """The `index`-th (0-based) explicit argument of the application
    beginning at `start`, or None when the application is shorter."""
    position = start
    for _skip in range(index + 1):
        step = _next_unit(text, position)
        if step is None:
            return None
        argument, position = step
    return argument


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
        if part[index] in " \t\n":
            index += 1
            continue
        step = _next_unit(part, index)
        if step is None:
            return False
        index = step[1]
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


def _steps_function(
    binders: str, function: str, state: str, pre_states: set[str]
) -> bool:
    """True when some binder group's type steps `function` from a covered
    state into `state`.

    The group's type begins after its first depth-0 colon.  The type is
    split on depth-0 `∧` -- conjuncts are entailed -- and a part counts
    only when the hypothesis actually *establishes* its equation: the part
    carries no weaker depth-0 connective (`∨`/`↔`/`→` and their ASCII
    spellings -- `dispatchSyscall st = .ok ((), st') ∨ True` is provable by
    its right arm and establishes no equality, yet the old connective cut
    validated the arm; PR #886 review), its head identifier is `function`
    (rejecting a dummy hypothesis that name-drops the dispatcher beside a
    step equation for something else, `@`-prefixed or bare), and the
    right-hand side of its top-level `=` -- running to the part's end --
    must *return* `state`, the payoff's conclusion state, parsed
    structurally by `_returns_state`: an equation whose result is some
    unrelated mid-state proves nothing about the state the conclusion
    speaks of, and neither does one that merely mentions that state inside
    its payload (PR #886 review, two successive rounds).

    The call's *arguments* are parsed too (PR #886 review, two rounds: the
    bare-transport refusal was beaten by a wrapped transport, `some st' =
    some st`, and the wrapper shapes are unbounded): some argument of the
    dispatch call must be one of the payoff's pre-states -- which the
    derived carriers make satisfiable for the live payoffs, whose invariant
    arrives through a quiescence pack rather than a bare family hypothesis
    (`_carrier_defs` / `carrier_structures`).  A step from a state nothing
    covers proves nothing about a dispatch, however the conclusion is
    reached.  The bare-transport refusal (`_transport_hypothesis`) stays as
    a second layer for the step-present-but-odd shapes.
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
                for part in split_conjunction(group[colon + 1 :]):
                    if _has_depth0_connective(part):
                        continue
                    head = re.match(r"\s*@?([^\W\d][\w'!?]*)", part)
                    if not head or head.group(1) != function:
                        continue
                    depth = 0
                    for offset, char in enumerate(part):
                        if char in _OPEN:
                            depth += 1
                        elif char in _CLOSE:
                            depth -= 1
                        elif depth == 0 and char == "=":
                            covered = False
                            position = head.end()
                            while position < offset:
                                step = _next_unit(part[:offset], position)
                                if step is None:
                                    break
                                if _normalise(step[0]) in pre_states:
                                    covered = True
                                    break
                                position = step[1]
                            if covered and _returns_state(
                                part[offset + 1 :], state
                            ):
                                return True
                            break
            index = end
        else:
            index += 1
    return False


def _transport_hypothesis(binders: str, conclusion: str, state: str) -> bool:
    """True when some entailed equality hands `state` over from another
    bare state.

    A payoff's step equation *defines* its conclusion state; a separate
    bare state-to-state equality on that state (`hEq : st' = st`, either
    orientation, in a binder or an unnamed premise) makes the theorem
    closable by transporting the invariant hypothesis around the step, so
    the step it advertises is dead weight (PR #886 review: `dispatchSyscall
    stOther = .ok ((), st')` beside `hInv : ipcInvariantFull st` and `hEq :
    st' = st` proves the conclusion from `hInv` alone).  Only *bare* sides
    count: a step-shaped equation (`f st = st'`) has an application side
    and stays a step; the residual is a transport wrapped in an expression
    (`(st', 0).1 = st`), which the Lean-side pack-inhabitation witnesses
    cover semantically.  Every binder group and every unnamed premise is
    parsed by `_equation_groups`, so only entailed equalities (∧-parts,
    never `∨`/`→` arms) are read.
    """
    regions: list[str] = []
    index = 0
    while index < len(binders):
        if binders[index] in _OPEN:
            end = balanced_span(binders, index)
            if end is None:
                break
            regions.append(binders[index + 1 : end - 1])
            index = end
        else:
            index += 1
    regions.extend(split_implication(_normalise(conclusion))[:-1])
    bare = re.compile(r"[^\W\d][\w'!?]*")
    for region in regions:
        for sides in _equation_groups(region):
            normalised = [_normalise(side) for side in sides]
            if state not in normalised:
                continue
            for side in normalised:
                if side != state and bare.fullmatch(side):
                    return True
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
            # A guillemet-quoted identifier (`«a"b»`) is code, not data --
            # and it is *one atomic token*, so its word characters survive
            # while every delimiter-significant character inside is
            # neutralised to `_` (PR #886 review, two rounds: a `"` inside
            # flipped the string state and blanked the rest of the file; a
            # `)` inside a quotation terminated `_blank_syntax_quotations`'
            # paren balance early, exposing inert template text to the
            # census).  Neutralising here, at the one layer that already
            # walks the span, is what keeps every downstream
            # bracket-walker -- `balanced_span`, the binder splitter, the
            # quotation balancer -- guillemet-safe without each carrying
            # its own skip.  Word characters survive so a guillemet-quoted
            # *family name* keeps its marker and stays censused; a newline
            # ends the state, since Lean's quoted identifiers cannot span
            # lines, so a stray `«` cannot restyle the rest of the file.
            if char == "»" or char == "\n":
                out.append(char)
                in_quoted = False
            elif char.isalnum() or char in "_'!?":
                out.append(char)
            else:
                out.append("_")
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


def _blank_syntax_quotations(source: str) -> str:
    """Blank the interiors of backtick syntax quotations, offsets kept.

    A macro template is data about future syntax, not a declaration: an
    uninvoked `macro_rules` quotation whose template spells `theorem
    …_preserves_ipcInvariantFull …` satisfied the declaration census while
    declaring nothing (PR #886 review).  Every `` `( `` opens a quotation;
    its interior is blanked to the matching close paren -- newlines and the
    bracketing parens kept, nesting respected -- so template text can
    neither satisfy nor trip a scan.  Blanking is the fail-closed
    direction: a quotation never *contains* a real declaration, so the
    census can only lose imposters.
    """
    out = list(source)
    index = 0
    while index < len(source) - 1:
        char = source[index]
        if char == "«":
            # A guillemet-quoted identifier is one token: a backtick or
            # paren inside it (`«harmless\`(unclosed»`) is identifier text,
            # and treating it as a quotation opener blanked to end of file
            # (PR #886 review) -- the same quote-awareness `_blank_strings`
            # has, at this pass's own trigger.  Since that pass now also
            # *neutralises* delimiter characters inside guillemet spans and
            # runs first (the `code_view` order contract), the balancer
            # below can no longer meet a quoted `)` either -- `«x)»` before
            # a template terminated the paren balance early and exposed the
            # template to the census (PR #886 review, the next round).
            # This skip stays as the local statement of the same fact.
            close = source.find("»", index + 1)
            index = len(source) if close == -1 else close + 1
        elif char == "`" and source[index + 1] == "(":
            depth = 0
            scan = index + 1
            while scan < len(source):
                inner = source[scan]
                if inner == "(":
                    depth += 1
                elif inner == ")":
                    depth -= 1
                    if depth == 0:
                        break
                elif depth > 0 and inner != "\n":
                    out[scan] = " "
                scan += 1
            index = scan + 1
        else:
            index += 1
    return "".join(out)


@functools.lru_cache(maxsize=None)
def code_view(root: str, relative: str) -> str:
    """The comment-free, string- and quotation-blanked view of one source.

    The order is a contract, not a convenience: `_blank_strings` neutralises
    delimiter characters inside guillemet identifiers, so every later pass
    and every bracket-walker downstream may treat `(`/`)` as structure --
    `_blank_syntax_quotations`' balancer in particular relies on it
    (PR #886 review: `«x)»` inside a quotation ended the balance early).

    Memoised: one `run_checks` pass lexes every source seven times (each
    check walks the tree), and the views are pure functions of the file --
    within one process no caller mutates a source between reads, and the
    self-test's fixture trees never share a `(root, relative)` key because
    each case writes into a fresh temporary directory.
    """
    with open(os.path.join(root, relative), encoding="utf-8") as handle:
        return _blank_syntax_quotations(
            _blank_strings(lean_code_view.strip(handle.read()))
        )


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
    r"^[ \t]*" + _MODIFIER_RUN + r"(?:@\[|/-|#|(?:" + _COMMAND_ALT + r")\b)",
    re.MULTILINE,
)


def _state_telescope(
    source: str, start: int
) -> tuple[list[str], int, bool, int] | None:
    """Walk the binder telescope at `start`: (state binder names, the first
    state group's explicit-argument position, exactly-one-state-group?,
    body offset just past `:=`), or None when no group is typed
    `SystemState` or the telescope is not followed by `(: Prop)? :=`.

    Only `(…)` groups advance the explicit position -- implicit and
    instance binders never occupy positional application slots (the
    structure-head parser's discipline, applied to definitions).  A group
    binding several names to `SystemState` collects them all for the
    substitution; more than one state *group* clears the single flag,
    which the carrier and index derivations require -- an ambiguous state
    position must widen the measure without minting positions.
    """
    index = start
    explicit_seen = 0
    binders: list[str] = []
    state_index: int | None = None
    state_groups = 0
    while True:
        probe = index
        while probe < len(source) and source[probe] in " \t\n":
            probe += 1
        if probe >= len(source) or source[probe] not in "({[":
            break
        end = balanced_span(source, probe)
        if end is None:
            break
        group = re.fullmatch(
            r"\s*([^\W\d][\w']*(?:\s+[^\W\d][\w']*)*)\s*:\s*SystemState\s*",
            source[probe + 1 : end - 1],
        )
        if group:
            state_groups += 1
            binders.extend(group.group(1).split())
            if state_index is None:
                state_index = explicit_seen
        if source[probe] == "(":
            explicit_seen += 1
        index = end
    if state_index is None:
        return None
    tail = re.match(r"\s*(?::\s*Prop\s*)?:=", source[index:])
    if tail is None:
        return None
    return binders, state_index, state_groups == 1, index + tail.end()


def state_predicate_bodies(
    root: str, sources: list[str]
) -> dict[str, list[tuple[str, str, int, bool]]]:
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
    bodies: dict[str, list[tuple[str, str, int, bool]]] = {}
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
    # The `: Prop` result annotation is optional (PR #886 review): Lean
    # infers it, and a collector requiring the literal spelling dropped a
    # refactored conjunct -- with its clause predicates -- from the derived
    # set.  Omitting it admits state-valued helpers into the bodies map,
    # which is the fail-closed direction: their bodies parse to no exact
    # predicate applications, and one that does parse IS a Prop.
    # The state binder may be implicit (PR #886 review, toolchain-
    # verified): `{st : SystemState}` declares the same predicate, and
    # the root applies it with a named argument the derivation already
    # normalises.  The binder may also sit *anywhere in the telescope*
    # (PR #886 review, the round after -- toolchain-verified):
    # `def replyCallerLinkage (enabled : Bool) (st : SystemState)` is the
    # same predicate with an ordinary parameter in front, and a collector
    # demanding the state group immediately after the name dropped the
    # definition -- with its clause predicates -- from the derived set.
    # So the header is matched and the telescope *walked*: every binder
    # group in turn, the state group found wherever it is, and its
    # explicit-argument position recorded for the application scans
    # (`_state_indices`).  The bracket class stays deliberately loose --
    # a group Lean would reject only widens the measured set.
    header_pattern = re.compile(
        r"^[ \t]*" + _COMPOSITE_PREFIX + r"(?:@\[[^\]]*\]\s*)*"
                + _MODIFIER_RUN +
        r"(?:def|abbrev)\s+([^\W\d][\w'!?]*)",
        re.MULTILINE,
    )
    # The arrow-form spelling `def NAME : SystemState → Prop := fun b => …`
    # is the same definition with the binder moved right of the colon
    # (PR #886 review): a collector blind to it dropped the canonical root
    # on a routine refactor while a namespaced shadow kept the union
    # nonempty.
    arrow_pattern = re.compile(
        r"^[ \t]*" + _COMPOSITE_PREFIX + r"(?:@\[[^\]]*\]\s*)*"
                + _MODIFIER_RUN +
        r"(?:def|abbrev)\s+([^\W\d][\w'!?]*)"
        r"\s*:\s*SystemState\s*(?:→|->)\s*Prop\s*:=\s*"
        r"fun\s+([^\W\d][\w']*)\s*(?:=>|↦)",
        re.MULTILINE,
    )
    for relative in sources:
        source = code_view(root, relative)
        breakpoints = namespace_breakpoints(source)
        collected: list[tuple[str, list[str], int, bool, int, int]] = []
        for match in header_pattern.finditer(source):
            walked = _state_telescope(source, match.end())
            if walked is None:
                continue
            binders, state_index, single, body_start = walked
            collected.append(
                (match.group(1), binders, state_index, single, match.start(), body_start)
            )
        for match in arrow_pattern.finditer(source):
            collected.append(
                (match.group(1), [match.group(2)], 0, True, match.start(), match.end())
            )
        for name, binders, state_index, single, decl_start, body_start in collected:
            tail = source[body_start:]
            cut = _COMMAND_STOP.search(tail)
            # Identifier-boundary substitution (PR #886 review): a plain
            # `.replace` on a one-letter binder like `s` rewrites every `s`
            # inside predicate *names* (`blockedOnReplyHasReplyObject` ->
            # `...HastReplyObject`), silently dropping real nested conjuncts
            # from the derived set.
            body = tail[: cut.start()] if cut else tail
            for binder in binders:
                body = re.sub(
                    r"(?<![\w'])" + re.escape(binder) + r"(?![\w'])", "st", body
                )
            bodies.setdefault(name, []).append(
                (prefix_at(breakpoints, decl_start), body, state_index, single)
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
# is needed here; `_root_.` is covered by the general class, and a
# guillemet-quoted qualifier segment is accepted exactly as `_qualified`
# accepts it (PR #886 review: the quoted-namespace sweep's sibling site).
# The explicit-application prefix `@` is accepted too (PR #886 review):
# `@replyCallerLinkageReciprocal st` is the same application with
# implicits spelled out, and rejecting it dropped the conjunct.
_APPLIED_RE = re.compile(
    r"^\s*@?(?:(?:«[^»\n]*»|[^\W\d][\w']*)\.)*"
    r"([^\W\d][\w'!?]*)\s+(?:\(\s*(?:[^\W\d][\w']*\s*:=\s*)?st\s*\)|st)\s*$"
)


def _body_predicates(body: str, any_position: bool = False) -> set[str]:
    """The predicates one definition body applies conjunctively to its state.

    `any_position` admits multi-parameter applications whose state sits at
    any argument position (`replyCallerLinkage true st`) -- the measure's
    widening direction, used by `_sub_predicates`; the carrier derivation
    must keep the default strict form, since its set suppresses findings.

    Each part is normalised (redundant enclosing parentheses stripped)
    and a part that then still splits is re-split, so a harmlessly
    regrouped body -- `(A st ∧ B st)`, opaque to one depth-0 pass --
    yields its conjuncts instead of silently dropping them
    (PR #886 review).  Routine proposition wrappers normalise away at
    every recursion depth (PR #886 review, two rounds): `by exact e`
    unwraps to its payload, `show T from e` to `e`, and a trailing
    depth-0 type ascription (`B st : Prop`) is cut -- each spelling
    elaborates to the same proposition, and a parser blind to any of
    them dropped conjuncts a reader plainly sees.
    """
    found = set()
    stack = [body]
    while stack:
        expr = _normalise(stack.pop())
        wrapped = re.match(r"by\s+exact\s+(.+)$", expr, re.DOTALL)
        if wrapped:
            stack.append(wrapped.group(1))
            continue
        if re.match(r"show(?![\w'!?])", expr):
            depth = 0
            unwrapped = False
            for offset in range(len(expr)):
                char = expr[offset]
                if char in _OPEN:
                    depth += 1
                elif char in _CLOSE:
                    depth -= 1
                elif (
                    depth == 0
                    and expr.startswith("from", offset)
                    and offset > 0
                    and not re.match(r"[\w']", expr[offset - 1])
                    and not re.match(r"[\w'!?]", expr[offset + 4 : offset + 5])
                ):
                    stack.append(expr[offset + 4 :])
                    unwrapped = True
                    break
            if unwrapped:
                continue
        parts = split_conjunction(expr)
        if len(parts) > 1:
            stack.extend(parts)
            continue
        part = parts[0]
        depth = 0
        for offset, char in enumerate(part):
            if char in _OPEN:
                depth += 1
            elif char in _CLOSE:
                depth -= 1
            elif (
                char == ":"
                and depth == 0
                and part[offset + 1 : offset + 2] != "="
            ):
                part = part[:offset]
                break
        hit = _APPLIED_RE.match(part)
        if hit:
            found.add(hit.group(1))
            continue
        if not any_position:
            continue
        # The any-position reading (PR #886 review): a multi-parameter
        # predicate is applied `replyCallerLinkage true st`, and the exact
        # unary form above cannot see it.  Accepting the head whenever
        # `st` is one of the application's argument units *widens the
        # measured set*, which is the conjunct and alias derivations'
        # fail-closed direction -- and exactly why `_carrier_defs`, whose
        # derived set suppresses findings, keeps the strict parse.
        head = re.match(
            r"@?(?:(?:«[^»\n]*»|[^\W\d][\w']*)\.)*([^\W\d][\w'!?]*)", part
        )
        if head is None or not _application_spans(part, head.end()):
            continue
        position = head.end()
        while True:
            step = _next_unit(part, position)
            if step is None:
                break
            unit, position = step
            if _normalise(unit) == "st":
                found.add(head.group(1))
                break
    return found


def _sub_predicates(bodies: dict[str, list[tuple[str, str]]], name: str) -> set[str]:
    """The union of `_body_predicates` over every body a name has.

    The union is the *widening* direction -- right for the conjunct and
    alias derivations, where a shadow can only add measured predicates.
    The carrier derivation must NOT use it (see `_carrier_defs`): carriers
    suppress findings, so there the verdict is per-body and unanimous.
    """
    found = set()
    for entry in bodies.get(name, []):
        found |= _body_predicates(entry[1], any_position=True)
    return found


def derive_conjuncts(bodies: dict[str, list[tuple[str, str]]]) -> set[str]:
    """The conjuncts of `ipcInvariantFull`, closed under definitional unfolding.

    Read out of the definition rather than listed, so a twenty-first conjunct
    is measured the day it is added.  The body is split on `∧` at bracket
    depth zero and a part counts only when it is exactly one predicate
    application with the definition's own state binder among its arguments
    (any position -- see `_body_predicates`; PR #886 review, the telescope
    round) -- so the expansion is the definition, not a token scrape of it.  Every body a name has contributes (see
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


def _carrier_defs(bodies: dict[str, list[tuple[str, str]]]) -> set[str]:
    """Collected predicates whose conjunctive expansion entails a family form.

    `ipcReachable st` *is* `ipcInvariantFull st ∧ …`, so a hypothesis on it
    is a pre-state hypothesis exactly as a bare family application is --
    derived from the same bodies map the conjuncts come from, never listed
    (PR #886 review: the payoffs carry their invariant through such
    carriers, and a pre-state scan blind to them could not tie the dispatch
    step to the state the invariant covers).

    Carriers *suppress* findings, so this is the one derived set that must
    under-approximate: the verdict is per-body and **unanimous** (PR #886
    review, a later round -- a same-named shadow definition that carries
    must not make the canonical non-carrying one mint pre-states).  A name
    qualifies only when every collected body of it reaches a family form.
    """
    family = set(PRE_STATE_PREDICATES)
    # Strict per-body parse, deliberately NOT the any-position reading the
    # measure uses (PR #886 review, the telescope round): the family forms
    # a carrier must entail are unary, and a loose reading here would let
    # an over-applied family spelling Lean rejects mint suppression.  The
    # single-state-group flag guards the same direction: a definition with
    # an ambiguous state position must not carry.
    per_body = {
        name: [_body_predicates(entry[1]) for entry in entries]
        for name, entries in bodies.items()
        if all(entry[3] for entry in entries)
    }
    carriers: set[str] = set()
    changed = True
    while changed:
        changed = False
        for name, expansions in per_body.items():
            if name in carriers or name in family:
                continue
            if expansions and all(
                expansion & (family | carriers) for expansion in expansions
            ):
                carriers.add(name)
                changed = True
    return carriers


def _state_indices(
    bodies: dict[str, list[tuple[str, str, int, bool]]]
) -> dict[str, int]:
    """Name -> its state binder's explicit-argument position, where every
    collected body agrees and each declares exactly one state group.

    The unanimity is the carrier discipline extended to positions (PR #886
    review, the telescope round): a text scanner cannot resolve which
    same-named definition an application elaborates to, and a position is
    consumed by both finding scans (`threaded`'s state extraction) and
    suppression (a def-carrier's slot in the carrier map), so only an
    unambiguous position is recorded.  Absent names default to 0 at every
    consumer -- the unary legacy, which is today's whole live tree.
    """
    indices: dict[str, int] = {}
    for name, entries in bodies.items():
        if (
            entries
            and all(entry[3] for entry in entries)
            and len({entry[2] for entry in entries}) == 1
        ):
            indices[name] = entries[0][2]
    return indices


def _carries_state_application(
    part: str, carrier_index: dict[str, int]
) -> bool:
    """True when `part` is exactly one carrier applied with `st` in its
    state position -- the whole part, arguments walked, nothing trailing."""
    part = _normalise(part)
    head = re.match(
        r"@?(?:(?:«[^»\n]*»|[^\W\d][\w']*)\.)*([^\W\d][\w'!?]*)", part
    )
    if head is None or head.group(1) not in carrier_index:
        return False
    argument = _argument_at(part, head.end(), carrier_index[head.group(1)])
    return (
        argument is not None
        and _normalise(argument) == "st"
        and _application_spans(part, head.end())
    )


_STRUCTURE_RE = re.compile(
    r"^[ \t]*" + _COMPOSITE_PREFIX + r"(?:@\[[^\]]*\]\s*)*"
        + _MODIFIER_RUN +
    r"structure\s+([^\W\d][\w'!?]*)",
    re.MULTILINE,
)


def carrier_structures(
    root: str, sources: list[str], def_carriers: set[str]
) -> dict[str, int]:
    """Prop structures carrying a family fact for their state binder ->
    the explicit-argument index of that binder.

    The quiescence packs are structures whose `reachable`-style field is an
    exact carrier application on the pack's own `(st : SystemState)`
    binder, so "this hypothesis covers `st` with the invariant" is
    derivable from the structure text -- naming the packs would be an
    enumeration (PR #886 review).  A structure qualifies when some field's
    type, ∧-split with weaker connectives refused, is exactly one known
    carrier (a family form, a carrier definition, or another carrier
    structure -- the fixpoint finds `base :`-nested packs) applied with the
    state binder in its state position.  Only explicit `(…)` binders count
    toward the argument index, because implicit ones never appear at
    application sites; a structure whose state binder is implicit, appears
    twice, or whose head does not parse contributes nothing -- fewer
    carriers only lose pre-states, which fails closed.

    Like `_carrier_defs`, the verdict is **unanimous across same-named
    declarations** (PR #886 review): a scanner cannot resolve which
    namespace's structure a bare application elaborates to, and carriers
    suppress findings, so a name declared twice qualifies only when every
    declaration parses, carries, and agrees on the state index -- a shadow
    that carries must not make an unrelated same-named pack mint
    pre-states.
    """
    heads: dict[str, list[tuple[int, str] | None]] = {}
    for relative in sources:
        source = code_view(root, relative)
        for match in _STRUCTURE_RE.finditer(source):
            entries = heads.setdefault(match.group(1), [])
            tail = source[match.end() :]
            depth = 0
            where = None
            for offset, char in enumerate(tail):
                if char in _OPEN:
                    depth += 1
                elif char in _CLOSE:
                    depth -= 1
                elif (
                    depth == 0
                    and char == "w"
                    and tail[offset : offset + 5] == "where"
                    and (offset == 0 or not re.match(r"[\w']", tail[offset - 1]))
                    and not re.match(r"[\w'!?]", tail[offset + 5 : offset + 6])
                ):
                    where = offset
                    break
            if where is None:
                entries.append(None)
                continue
            binder_text = tail[:where]
            state_name = None
            state_index = None
            position = 0
            index = 0
            ambiguous = False
            while index < len(binder_text):
                char = binder_text[index]
                if char in _OPEN:
                    end = balanced_span(binder_text, index)
                    if end is None:
                        break
                    if char == "(":
                        group = binder_text[index + 1 : end - 1]
                        colon = None
                        depth = 0
                        for offset, inner in enumerate(group):
                            if inner in _OPEN:
                                depth += 1
                            elif inner in _CLOSE:
                                depth -= 1
                            elif inner == ":" and depth == 0:
                                colon = offset
                                break
                        if colon is not None:
                            names = re.findall(
                                r"[^\W\d][\w'!?]*", group[:colon]
                            )
                            if group[colon + 1 :].strip() == "SystemState":
                                if state_name is not None or len(names) != 1:
                                    ambiguous = True
                                else:
                                    state_name = names[0]
                                    state_index = position
                            position += len(names)
                    index = end
                else:
                    index += 1
            if ambiguous or state_name is None:
                entries.append(None)
                continue
            fields_tail = tail[where + 5 :]
            cut = _COMMAND_STOP.search(fields_tail)
            fields = fields_tail[: cut.start()] if cut else fields_tail
            fields = re.sub(
                r"(?<![\w'])" + re.escape(state_name) + r"(?![\w'])",
                "st",
                fields,
            )
            entries.append((state_index, fields))
    base_index = {name: 0 for name in PRE_STATE_PREDICATES}
    base_index.update({name: 0 for name in def_carriers})

    def entry_carries(fields: str, known: dict[str, int]) -> bool:
        starts = list(
            re.finditer(r"^([ \t]+)[^\W\d][\w'!?]*\s*:", fields, re.MULTILINE)
        )
        if not starts:
            return False
        indent = min(len(match.group(1)) for match in starts)
        field_starts = [
            match.start() for match in starts if len(match.group(1)) == indent
        ]
        for begin, end in zip(field_starts, field_starts[1:] + [len(fields)]):
            field = fields[begin:end]
            colon = field.find(":")
            for piece in split_conjunction(field[colon + 1 :]):
                if _has_depth0_connective(piece):
                    continue
                if _carries_state_application(piece, known):
                    return True
        return False

    carriers: dict[str, int] = {}
    changed = True
    while changed:
        changed = False
        for name, entries in heads.items():
            if name in carriers:
                continue
            if any(entry is None for entry in entries):
                continue
            if len({state_index for state_index, _fields in entries}) != 1:
                continue
            known = dict(base_index)
            known.update(carriers)
            if all(
                entry_carries(fields, known) for _state_index, fields in entries
            ):
                carriers[name] = entries[0][0]
                changed = True
    return carriers


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
        visibility: str = "",
        carriers: dict[str, int] | None = None,
    ):
        self.path = path
        self.line = line
        self.name = name
        self.binders = binders
        self.conclusion = _normalise(conclusion)
        self.prefix = prefix
        self.ambient = ambient
        self.excluded = excluded
        self.visibility = visibility
        # name -> explicit state-argument index, for every form whose
        # hypothesis covers its state with the invariant: the family, the
        # derived carrier definitions, and the derived carrier structures.
        self.carriers = (
            carriers
            if carriers is not None
            else {name: 0 for name in PRE_STATE_PREDICATES}
        )

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

        Anchoring is *directional* (PR #886 review, the round after the
        token filters): an equation admits its tokens only when one of its
        sides is nonempty and already fully anchored, the way a definition
        flows from the determined side to the determining one.  Shared-token
        co-occurrence was not enough: `pair st' stMid = pair st' stMid` and
        its definitionally-reflexive sibling `pair st' stMid = id (pair st'
        stMid)` both share the genuinely-anchored `st'`, yet neither has a
        side the transition determines, so under the directional rule
        neither admits `stMid` -- while a real chain (`stageTwo stMid = .ok
        ((), st')` then `stageOne st = .ok stMid`) unlocks side by side
        from the conclusion outward.  A side whose tokens all filter away
        (`.ok ()`, `True`) can never unlock its equation: an equality with
        a contentless side determines nothing.
        """
        tokens = _connectivity_tokens(self.conclusion, self.excluded)
        groups: list[list[set[str]]] = []
        index = 0
        while index < len(self.binders):
            char = self.binders[index]
            if char in _OPEN:
                end = balanced_span(self.binders, index)
                if end is None:
                    break
                region = self.binders[index:end]
                if "=" in region:
                    for sides in _equation_groups(
                        self.binders[index + 1 : end - 1]
                    ):
                        groups.append(
                            [
                                _connectivity_tokens(side, self.excluded)
                                for side in sides
                            ]
                        )
                index = end
            else:
                index += 1
        changed = True
        while changed:
            changed = False
            for group in groups:
                if any(side and side <= tokens for side in group):
                    union = set().union(*group)
                    if not union <= tokens:
                        tokens |= union
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
        for predicate, arg_index in self.carriers.items():
            for hit in re.finditer(_qualified(predicate), self.binders):
                if _projection_hit(hit.group(1), binder_names):
                    continue
                argument = _argument_at(self.binders, hit.end(), arg_index)
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
            for predicate in _CONCLUSION_FORMS:
                # `@?`: the explicit-application spelling of the same
                # conclusion (PR #886 review sweep with `_APPLIED_RE`).
                hit = re.match(r"@?" + _qualified(predicate), part)
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

        And it may hide behind a *transformation* (PR #886 review, a later
        round): `hInv : ipcInvariantFull (id st')` is definitionally the
        post-state assumption -- Lean reduces `id` -- while comparing
        expressions for equality sees two different texts.  A scanner
        cannot normalise definitional equality, so it fails closed on the
        token relation instead: a family application whose argument
        *carries* every token of the conclusion state (and is not that
        state's own anchored pre-state expression, which the equality tier
        already vets) is treated as a hypothesis about the conclusion
        state.  A transition's genuine pre-state never contains its
        post-state, so the superset test costs nothing on honest bundles.
        """
        state = self.conclusion_state()
        if state is None:
            return None
        if state in self.pre_states():
            return state
        binder_names = self._binder_names()
        state_tokens = set(re.findall(r"[^\W\d][\w'!?]*", state))
        segments = split_implication(_normalise(self.conclusion))
        for region in [self.binders, self.ambient] + list(segments[:-1]):
            for predicate, arg_index in self.carriers.items():
                for hit in re.finditer(_qualified(predicate), region):
                    chain = hit.group(1)
                    if _projection_hit(chain, binder_names):
                        # Dot notation is application (see `threaded`): a
                        # single-segment binder chain with no trailing
                        # argument is the state argument -- the finding
                        # direction of the same asymmetry, so `pre_states`
                        # still skips projections entirely.
                        if (
                            chain.count(".") != 1
                            or first_argument(region, hit.end()) is not None
                        ):
                            continue
                        argument = chain.split(".", 1)[0]
                    else:
                        argument = _argument_at(region, hit.end(), arg_index)
                    if argument is None:
                        continue
                    argument = _normalise(argument)
                    if argument == state:
                        return state
                    tokens = set(re.findall(r"[^\W\d][\w'!?]*", argument))
                    if state_tokens and state_tokens <= tokens:
                        return state
        return None

    def threaded(
        self,
        conjuncts: set[str],
        indices: dict[str, int] | None = None,
    ) -> list[tuple[str, str]]:
        """(conjunct, state) for every conjunct bound on a non-pre-state.

        `indices` maps a measured predicate to its state argument's
        explicit position (PR #886 review, the telescope round): a
        multi-parameter conjunct is bound `replyCallerLinkage true st'`,
        and reading the *first* argument both missed the post-state and
        would flag the clean `replyCallerLinkage true st` on its leading
        `Bool`.  Absent names read position 0 -- the unary legacy.

        The conclusion's *premises* are scanned as well as the named
        binders: an unnamed implication premise after the declaration's
        colon (`conjunct st' → ipcInvariantFull st'`) is the same threading
        in telescope clothing (PR #886 review).  The conclusion's *final
        segment* is not (PR #886 review, a later round): its conjuncts are
        guarantees the theorem establishes -- `ipcInvariantFull st' ∧
        conjunct st'` is a strengthened result, not an assumption -- and
        scanning them flagged theorems for proving more.  In-scope
        `variable` binders are scanned too (PR #886 review, the
        section-variable round): an `include`d section hypothesis is
        telescope, and one Lean would not include can only add findings
        here, never suppress them (the class docstring's asymmetry).
        """
        pre = self.pre_states()
        binder_names = self._binder_names()
        premises = split_implication(_normalise(self.conclusion))[:-1]
        findings = []
        for conjunct in sorted(conjuncts):
            slot = (indices or {}).get(conjunct, 0)
            for region in [self.ambient, self.binders] + premises:
                for hit in re.finditer(_qualified(conjunct), region):
                    chain = hit.group(1)
                    if _projection_hit(chain, binder_names):
                        # Dot notation is application (PR #886 review --
                        # verified against the toolchain): `st'.conjunct`
                        # applies a `SystemState`-namespaced predicate to
                        # `st'`, so a single-segment chain heading at a
                        # binder, with *no trailing argument*, is that
                        # binder as the state argument.  A trailing
                        # argument (`hInv.conjunct st'`) or a multi-segment
                        # chain (`hPack.reachable.…`) stays a projection --
                        # dot notation already supplies the predicate's one
                        # state, so a genuine application has nothing left
                        # to apply.
                        # Position-0 names only: dot notation supplies the
                        # first explicit argument, so for a predicate whose
                        # state sits later the chain stays a projection.
                        if (
                            slot == 0
                            and chain.count(".") == 1
                            and first_argument(region, hit.end()) is None
                        ):
                            state = chain.split(".", 1)[0]
                            if state not in pre:
                                findings.append((conjunct, state))
                        continue
                    argument = _argument_at(region, hit.end(), slot)
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
    # `public section` is a scope like any other (PR #886 review -- verified
    # against the toolchain): a scanner blind to the modifier missed the
    # push, and the section's `end` then popped the enclosing namespace,
    # desynchronising every prefix after it.
    r"|(?:(?:noncomputable|public)\s+)*(?P<sec>section)\b"
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
    root: str,
    sources: list[str],
    excluded: frozenset[str] = frozenset(),
    carriers: dict[str, int] | None = None,
) -> list[Bundle]:
    """Every declaration in the `ipcInvariantFull` bundle family.

    `excluded` is the predicate-name set (family plus derived conjuncts,
    aliases and carriers) each bundle's `_connectivity_tokens` filter drops
    from its anchor graph; `carriers` maps every invariant-carrying form to
    its state-argument index.  The caller derives both before collecting.
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
                    "private" if "private" in match.group("mods") else "",
                    carriers,
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


def grammar_coverage(root: str, sources: list[str]) -> list[str]:
    """Violations for column-0 tokens outside the gate's known grammar.

    This is the tripwire that ends the surface-spelling class (PR #886
    review, the churn diagnosis): eight consecutive review rounds each
    found one more valid Lean command the text grammars did not know --
    `class`, `def`, `opaque`, `instance`, `nonrec`, `public section`, and
    so on -- and every unknown spelling was a *silent* miss until a
    reviewer found it, because a declaration under an unknown command is
    invisible to the census and every scan built on it.  The tripwire
    inverts the failure mode: a column-0 identifier token that is neither
    a known modifier nor a known command fails the gate loudly, so the
    next new spelling -- in the tree today, or written next year -- is the
    gate's own finding, never a review round's.

    Column 0 only, over the code view: body lines are indented, comment
    and string and quotation text is blanked, and a column-0 line opening
    with a non-identifier character (a continuation bracket, an operator)
    is part of a declaration some anchored grammar already captured via
    `signature_end`.  `@[` attributes and `#`-commands are the two known
    non-identifier openers.  Each unknown token is reported once with its
    first location and a count.  The census that designed this set found
    two unknown commands already in the tree (`register_option`,
    `prelude`) -- the class was live, not hypothetical.

    Column 0 is a *convention*, not Lean's grammar: commands parse at any
    indentation, and an indented unknown command is textually
    indistinguishable from a term continuation, so this scan alone fails
    open exactly there (PR #886 review).  What closes the indented channel
    is the pair of token scans beside this one -- position-free by
    construction: `minting_machinery` pins the mechanisms through which an
    unknown command can exist at all (no external `require`, so the
    vocabulary is core plus in-tree machinery), and `family_references`
    resolves every spelled family-shaped token against the census.

    The residual after all three -- and the reason the shared command
    set is an approximation at all -- is that the gate re-implements a
    fragment of Lean's grammar in text: pinned machinery can mint family
    names it never spells.  The structural endpoint is an
    elaborator-backed census (declarations and telescopes read from Lean's
    own environment), registered as tracked debt in
    `docs/WORKSTREAM_HISTORY.md` (WS-DT residuals).
    """
    known = set(_MODIFIERS) | set(_COMMANDS)
    seen: dict[str, tuple[str, int, int]] = {}
    for relative in sources:
        view = code_view(root, relative)
        for line_number, line in enumerate(view.split("\n"), start=1):
            if not line or line[0] in " \t":
                continue
            if line.startswith("@[") or line[0] == "#":
                continue
            token = re.match(r"[^\W\d][\w'!?]*", line)
            if token is None:
                continue
            word = token.group(0)
            if word in known:
                continue
            if word in seen:
                file0, line0, count = seen[word]
                seen[word] = (file0, line0, count + 1)
            else:
                seen[word] = (relative, line_number, 1)
    problems: list[str] = []
    for word in sorted(seen):
        file0, line0, count = seen[word]
        extra = "" if count == 1 else f" ({count} occurrences)"
        problems.append(
            f"grammar_coverage: {file0}:{line0}: leading token `{word}` is "
            f"not a command this gate's grammars know{extra}; declarations "
            f"under an unknown command are invisible to every census and "
            f"scan -- teach `_COMMANDS`/`_MODIFIERS` (one shared source), "
            f"never work around the failure"
        )
    return problems


_MACHINERY_RE = re.compile(
    r"(?<![\w'!?.«#])(?:"
    + "|".join(sorted(_MACHINERY, key=len, reverse=True))
    + r")(?![\w'!?])"
    r"|(?<![\w'!?])#eval(?![\w'!?])"
)


def minting_machinery(root: str, sources: list[str]) -> list[str]:
    """Violations for declaration-minting machinery outside the pin.

    The indentation-insensitive half of the unknown-command tripwire
    (PR #886 review): `grammar_coverage` reads column 0, and an *indented*
    invocation of a user-defined command -- one that expands to a family
    theorem the census never sees -- is textually indistinguishable from a
    term continuation, so position cannot close the class.  Mechanism can:
    a user-defined command exists only through the machinery keywords in
    `_MACHINERY` (there is no external `require` in `lakefile.toml`, so
    the vocabulary is Lean core plus this tree), and those are *token*
    occurrences the code view exposes at any indentation.  Every
    occurrence is held to `MACHINERY_PINS` -- over-pinned deliberately: a
    term-category macro cannot mint a declaration, but classifying
    categories through blanked quotations is guesswork, so the whole
    mechanism set is reviewed by count instead (fail closed).

    The residual is a *pinned* file minting family-shaped names it never
    spells (constructed via `Name` surgery) -- that is the
    elaborator-backed-census debt registered in
    `docs/WORKSTREAM_HISTORY.md` (WS-DT residuals), now confined to the
    pinned files below rather than open anywhere in the tree; spelled
    names are `family_references`' half.
    """
    counts: dict[tuple[str, str], int] = {}
    first: dict[tuple[str, str], int] = {}
    for relative in sources:
        view = code_view(root, relative)
        for match in _MACHINERY_RE.finditer(view):
            key = (relative, match.group(0))
            counts[key] = counts.get(key, 0) + 1
            first.setdefault(key, view.count("\n", 0, match.start()) + 1)
    problems: list[str] = []
    present = set(sources)
    for key in sorted(counts):
        count = counts[key]
        pinned = MACHINERY_PINS.get(key, 0)
        if count > pinned:
            relative, keyword = key
            problems.append(
                f"minting_machinery: {relative}:{first[key]}: `{keyword}` "
                f"occurs {count}x (pinned: {pinned}) -- declaration-minting "
                f"machinery can define commands whose declarations no text "
                f"census sees, at any indentation; review the use and pin "
                f"it in MACHINERY_PINS"
            )
    for key, pinned in sorted(MACHINERY_PINS.items()):
        relative, keyword = key
        if relative in present and counts.get(key, 0) < pinned:
            problems.append(
                f"minting_machinery: {relative}: pin expects {pinned}x "
                f"`{keyword}` but the file carries {counts.get(key, 0)} -- a "
                f"stale pin is a standing exemption; update MACHINERY_PINS "
                f"to match the file"
            )
    return problems


_FAMILY_TOKEN_RE = re.compile(
    r"[\w'!?]*(?:"
    + "|".join(re.escape(marker) for marker in BUNDLE_MARKERS)
    + r")[\w'!?]*"
)


def family_references(root: str, sources: list[str]) -> list[str]:
    """Violations for family-shaped tokens no declaration accounts for.

    The other indentation-insensitive half (PR #886 review): whatever
    position or command shape carries it, a token spelling
    `*_preserves_ipcInvariantFull*` / `*_establishes_ipcInvariantFull*`
    into the code view must resolve to a censused declaration's name --
    the declaration site itself, a proof citing it, an `attribute` or
    `open` listing it.  A DSL invocation naming the theorem it mints, a
    `syntax (name := …_preserves_ipcInvariantFull)` escape, or a citation
    of a declaration whose spelling the census failed to read all surface
    here as an unresolved token, loudly, wherever they sit.  Resolution is
    by marker-bearing segment, so `Foo.bar_preserves_ipcInvariantFull`
    resolves through `bar_…`'s declaration wherever the namespace prefix
    was opened.  The check only ever *adds* findings -- there is no
    suppression side -- so its approximations fail closed.
    """
    names = declared_names(root, sources)
    resolved: set[str] = set()
    for name in names:
        resolved.update(_FAMILY_TOKEN_RE.findall(name))
    seen: dict[str, tuple[str, int, int]] = {}
    for relative in sources:
        view = code_view(root, relative)
        for match in _FAMILY_TOKEN_RE.finditer(view):
            token = match.group(0)
            if token in resolved:
                continue
            if token in seen:
                file0, line0, count = seen[token]
                seen[token] = (file0, line0, count + 1)
            else:
                seen[token] = (
                    relative,
                    view.count("\n", 0, match.start()) + 1,
                    1,
                )
    problems: list[str] = []
    for token in sorted(seen):
        file0, line0, count = seen[token]
        extra = "" if count == 1 else f" ({count} occurrences)"
        problems.append(
            f"family_references: {file0}:{line0}: `{token}` carries a "
            f"family marker but resolves to no censused declaration"
            f"{extra} -- either a declaration the census cannot read or a "
            f"name minted outside it; make the declaration one the gate's "
            f"grammars parse"
        )
    return problems


def _reachable_modules(
    root: str, sources: list[str]
) -> tuple[set[str] | None, list[str]]:
    """(modules a build root reaches over the import graph, hard problems).

    A payoff module nothing builds is an orphan (PR #886 review): the
    partition gate polices only *production* reachability, so dropping a
    staged payoff module's import from `Platform.Staged` would leave every
    text scan satisfied while CI stopped compiling the theorems.  The
    build roots are *derived*, never listed: every executable `root = "…"`
    in `lakefile.toml`, the library's own root module, and every module a
    CI script builds by name (`lake build <Module>` in `scripts/*.sh`) --
    the union of what the build system and the tier scripts actually
    compile.  `(None, [])` when there is no `lakefile.toml`: the
    self-test's fixture trees carry no build configuration, and
    reachability is a question about a buildable tree.  A lakefile whose
    roots resolve to no tracked module is a hard violation, because a
    reachability check with no roots would silently pass everything.
    """
    lakefile = os.path.join(root, "lakefile.toml")
    if not os.path.isfile(lakefile):
        return None, []
    candidates: set[str] = set()
    section = ""
    with open(lakefile, encoding="utf-8") as handle:
        for raw in handle:
            line = raw.strip()
            if line.startswith("[["):
                section = line
                continue
            hit = re.fullmatch(r'root\s*=\s*"([^"]+)"', line)
            if hit:
                candidates.add(hit.group(1))
                continue
            hit = re.fullmatch(r'name\s*=\s*"([^"]+)"', line)
            if hit and section == "[[lean_lib]]":
                candidates.add(hit.group(1))
    # `lake build <Module>` counts as a root only in *command position*
    # (PR #886 review: the raw-text scan let `echo lake build …` -- a
    # comment, a log line -- mint a root, and roots suppress findings, so
    # this is a place the scan must under-approximate).  Scripts are
    # comment-stripped and split into commands by the repository's shared
    # quote-aware resolver; `lake` qualifies at argv position 0, or behind
    # a *derived* wrapper: a shell function the scripts themselves define
    # whose own body executes its arguments (`"$@"`) -- `run_check` and
    # its relatives -- with the `lake build` pair located inside the
    # wrapper's argument list.  `echo` defines no such function.
    scripts_dir = os.path.join(root, "scripts")
    if os.path.isdir(scripts_dir):
        script_texts: list[str] = []
        for name in sorted(os.listdir(scripts_dir)):
            if name.endswith(".sh"):
                with open(
                    os.path.join(scripts_dir, name), encoding="utf-8"
                ) as handle:
                    script_texts.append(handle.read())
        wrappers: set[str] = set()
        for text in script_texts:
            for match in re.finditer(
                r"^([A-Za-z_][\w]*)\s*\(\)\s*\{", text, re.MULTILINE
            ):
                brace = text.index("{", match.start())
                close = text.find("\n}", brace)
                body = text[brace : close if close != -1 else len(text)]
                if '"$@"' in body:
                    wrappers.add(match.group(1))
        for text in script_texts:
            stripped = "\n".join(
                shell_view.split_comment(line) for line in text.split("\n")
            )
            for command in shell_view.shell_commands(stripped):
                argv = shell_view.argv_of(command)
                if not argv:
                    continue
                start = None
                if argv[0] == "lake":
                    start = 0
                elif argv[0] in wrappers:
                    for index in range(1, len(argv) - 1):
                        if argv[index] == "lake" and argv[index + 1] == "build":
                            start = index
                            break
                if (
                    start is None
                    or len(argv) < start + 2
                    or argv[start + 1] != "build"
                ):
                    continue
                candidates.update(
                    token
                    for token in argv[start + 2 :]
                    if re.fullmatch(r"[A-Za-z_][\w.']*", token)
                )
    modules = {
        relative[: -len(".lean")].replace("/", "."): relative
        for relative in sources
    }
    resolved = {name for name in candidates if name in modules}
    if not resolved:
        return None, [
            "payoff_theorems: lakefile.toml is present but no build root "
            "resolves to a tracked module; the reachability check has "
            "nothing to walk from"
        ]
    imports: dict[str, list[str]] = {}
    for module, relative in modules.items():
        imports[module] = re.findall(
            r"^\s*import\s+([\w.'«»]+)",
            code_view(root, relative),
            re.MULTILINE,
        )
    reachable: set[str] = set()
    frontier = list(resolved)
    while frontier:
        module = frontier.pop()
        if module in reachable:
            continue
        reachable.add(module)
        frontier.extend(
            target for target in imports.get(module, []) if target in modules
        )
    return reachable, []


def run_checks(root: str) -> list[str]:
    """Every violation, as a human-readable line.  Empty means clean."""
    problems: list[str] = []
    sources = lean_sources(root)

    # First, because everything else assumes it: an unknown command means
    # unknown blind spots in every check below, so its findings lead.  The
    # machinery and reference scans belong beside it -- they are the
    # indentation-insensitive halves of the same tripwire, and they must
    # run before any early return below can cut the pass short.  The
    # other checks still run -- more information, not less.
    problems.extend(grammar_coverage(root, sources))
    problems.extend(minting_machinery(root, sources))
    problems.extend(family_references(root, sources))

    defs_path = os.path.join(root, DEFS_MODULE)
    if not os.path.isfile(defs_path):
        return [f"conjuncts_derived: {DEFS_MODULE} is missing"]
    bodies = state_predicate_bodies(root, sources)
    # The union over same-named bodies fails closed against shadows only
    # while the canonical root's own body is among them (PR #886 review), so
    # its presence under the canonical namespace is required outright.
    if not any(
        entry[0] == ROOT_NAMESPACE for entry in bodies.get(ROOT_INVARIANT, [])
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
    # Carriers are pre-state vocabulary (PR #886 review): a definition or
    # structure whose expansion entails a family form covers its state with
    # the invariant, so the packs the payoffs consume mint pre-states.
    def_carriers = _carrier_defs(bodies)
    # A def-carrier's state slot is its telescope-derived position (PR #886
    # review, the telescope round): a blanket 0 would resolve a
    # multi-parameter carrier's pre-state from its leading non-state
    # argument.  Names without a unanimous position read 0, the unary
    # legacy.
    indices = _state_indices(bodies)
    carrier_map = {name: 0 for name in PRE_STATE_PREDICATES}
    carrier_map.update({name: indices.get(name, 0) for name in def_carriers})
    carrier_map.update(carrier_structures(root, sources, def_carriers))
    bundles = collect_bundles(
        root,
        sources,
        frozenset(measured)
        | frozenset(PRE_STATE_PREDICATES)
        | frozenset(carrier_map),
        carrier_map,
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
        for conjunct, state in bundle.threaded(measured, indices):
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
    # Canonical-prefix *public* bundles only (PR #886 review, two rounds):
    # a `namespace Shadow` twin must not be the declaration whose statement
    # gets validated, and neither may a `private` twin -- last-wins over a
    # visibility-blind dictionary let a later-sorted private theorem stand
    # validation in place of a vacuous public one.
    by_name = {
        bundle.name: bundle
        for bundle in bundles
        if bundle.prefix == PAYOFF_NAMESPACE and bundle.visibility != "private"
    }
    reachable, reach_problems = _reachable_modules(root, sources)
    problems.extend(reach_problems)
    for payoff in PAYOFF_THEOREMS:
        bundle = by_name.get(payoff)
        if bundle is None:
            continue  # absence is payoff_theorems' finding, not this one's
        if reachable is not None:
            module = bundle.path[: -len(".lean")].replace("/", ".")
            if module not in reachable:
                problems.append(
                    f"payoff_theorems: `{payoff}` is declared in "
                    f"{bundle.path}, which no build root reaches -- an "
                    f"unbuilt payoff proves nothing; import its module from "
                    f"a build root (the lakefile's roots, the library root, "
                    f"or a module a CI script builds)"
                )
        function = payoff[: -len("_preserves_ipcInvariantFull")]
        state = bundle.conclusion_state()
        if state is None:
            problems.append(
                f"payoff_statement: {bundle.path}:{bundle.line}: `{payoff}` "
                f"does not conclude an `ipcInvariantFull`-family predicate "
                f"applied to a state"
            )
        # The dispatcher must be the *head of a step equation from a covered
        # state into the conclusion's state*, not merely a token somewhere
        # in the binders: a dummy hypothesis mentioning the name beside a
        # step for another function satisfied the mention-only form, a step
        # equation into an unrelated mid-state satisfied the head-only form,
        # and a step *from* an unrelated state -- closable through the
        # invariant hypothesis plus a (bare or wrapped) transport equality
        # -- satisfied the result-only form (PR #886 review, three rounds;
        # the derived carriers are what make the input rule satisfiable for
        # the pack-based live payoffs).
        elif not _steps_function(
            bundle.binders, function, state, bundle.pre_states()
        ):
            problems.append(
                f"payoff_statement: {bundle.path}:{bundle.line}: `{payoff}` "
                f"has no hypothesis whose step equation applies `{function}` "
                f"to a covered pre-state with `{state}`, its conclusion's "
                f"state, in the result; a payoff that does not step the "
                f"dispatcher it is named for from a state its hypotheses "
                f"cover into the state it concludes about consumes nothing"
            )
        elif _transport_hypothesis(bundle.binders, bundle.conclusion, state):
            problems.append(
                f"payoff_statement: {bundle.path}:{bundle.line}: `{payoff}` "
                f"carries a bare transport equality on `{state}`, its "
                f"conclusion's state -- the theorem is closable by handing "
                f"the invariant over from another state, so the step it "
                f"advertises is dead weight"
            )

    return problems


def report(root: str) -> int:
    """Print the census: bundles, conjuncts, and every post-state binding."""
    sources = lean_sources(root)
    bodies = state_predicate_bodies(root, sources)
    conjuncts = derive_conjuncts(bodies)
    measured = conjuncts | threading_aliases(bodies, conjuncts)
    def_carriers = _carrier_defs(bodies)
    indices = _state_indices(bodies)
    carrier_map = {name: 0 for name in PRE_STATE_PREDICATES}
    carrier_map.update({name: indices.get(name, 0) for name in def_carriers})
    carrier_map.update(carrier_structures(root, sources, def_carriers))
    bundles = collect_bundles(
        root,
        sources,
        frozenset(measured)
        | frozenset(PRE_STATE_PREDICATES)
        | frozenset(carrier_map),
        carrier_map,
    )
    print(f"conjuncts derived from `{ROOT_INVARIANT}`: {len(conjuncts)}")
    for conjunct in sorted(conjuncts):
        print(f"  - {conjunct}")
    markers = " / ".join(f"`*{marker}*`" for marker in BUNDLE_MARKERS)
    print(f"\n{markers} statements: {len(bundles)}")
    tally: dict[str, int] = {}
    threaded_bundles = 0
    for bundle in sorted(bundles, key=lambda b: (b.path, b.line)):
        findings = bundle.threaded(measured, indices)
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
    # Writing a tree invalidates the memoised views: temporary directory
    # names are unique among *existing* directories, not across a process's
    # lifetime, so a recycled path must never serve a previous case's view.
    code_view.cache_clear()
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
    # conjuncts -- but behind a curried `→ Prop` return type the collector
    # deliberately does not read, so the derivation finds nothing.  A gate
    # that trusted an empty derivation would report PASS.  (The original
    # mutation here appended a second binder group; the telescope walk now
    # *collects* that spelling -- the round-24 fix -- so the reshape moved
    # to a form that must still fail loudly rather than silently measure
    # nothing.)
    renamed_state = _fixture()
    renamed_state[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def ipcInvariantFull (st : SystemState) : Prop :=",
        "def ipcInvariantFull (st : SystemState) : CoreId → Prop :=",
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

    # A def-spelled proof: `def X_preserves_… : ipcInvariantFull st' := …`
    # is a valid Lean declaration of the same theorem, and a census that
    # stopped at `theorem|lemma` let it bypass every check.
    def_bundle = _fixture()
    def_bundle["SeLe4n/Kernel/IPC/Invariant/Structural/DefBundles.lean"] = (
        "def endpointHiddenDual_preserves_ipcInvariantFull\n"
        "    (st st' : SystemState)\n"
        "    (hInv : ipcInvariantFull st)\n"
        "    (hStep : endpointHiddenDual st = .ok ((), st'))\n"
        "    (hT : blockedThreadsPendingMessageConsistent st') :\n"
        "    ipcInvariantFull st' :=\n"
        "  sample st st' hInv hStep\n"
    )
    cases.append(
        _Case(
            "a def-spelled threaded bundle is measured like a theorem",
            def_bundle,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # An opaque-spelled proof: `opaque X_preserves_… : … := …` is the last
    # proof-capable declaration form Lean accepts, and the census must not
    # be the scanner that missed it.
    opaque_bundle = _fixture()
    opaque_bundle["SeLe4n/Kernel/IPC/Invariant/Structural/OpaqueBundles.lean"] = (
        "opaque endpointOpaqueDual_preserves_ipcInvariantFull\n"
        "    (st st' : SystemState)\n"
        "    (hInv : ipcInvariantFull st)\n"
        "    (hStep : endpointOpaqueDual st = .ok ((), st'))\n"
        "    (hT : blockedThreadsPendingMessageConsistent st') :\n"
        "    ipcInvariantFull st' :=\n"
        "  sample st st' hInv hStep\n"
    )
    cases.append(
        _Case(
            "an opaque-spelled threaded bundle is measured like a theorem",
            opaque_bundle,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # An inferred-`Prop` conjunct definition: Lean infers the result type,
    # and a collector requiring the literal `: Prop` dropped the definition
    # -- and its clause predicates -- from the derived set.
    inferred_prop = _fixture()
    inferred_prop[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def replyCallerLinkage (st : SystemState) : Prop :=",
        "def replyCallerLinkage (st : SystemState) :=",
    )
    inferred_prop["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hR : replyCallerLinkageReciprocal st')\n",
        )
    )
    cases.append(
        _Case(
            "an inferred-Prop conjunct definition still derives",
            inferred_prop,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # An explicit application in a definition body: `@pred st` is the same
    # application with implicits spelled out, and the exact-application
    # parser rejected it.
    explicit_application = _fixture()
    explicit_application[DEFS_MODULE] = CLEAN_DEFS.replace(
        "  replyCallerLinkageReciprocal st ∧ blockedOnReplyHasReplyObject st",
        "  @replyCallerLinkageReciprocal st ∧ blockedOnReplyHasReplyObject st",
    )
    explicit_application["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hR : replyCallerLinkageReciprocal st')\n",
        )
    )
    cases.append(
        _Case(
            "an explicit-application conjunct spelling still derives",
            explicit_application,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # A step equation from an unrelated state: the theorem closes through
    # `hInv` and a side equality, never establishing preservation for the
    # dispatched input -- the dispatcher must step an invariant-bearing
    # pre-state.
    unrelated_step = _fixture()
    unrelated_step["SeLe4n/Kernel/API.lean"] = CLEAN_PAYOFF.replace(
        """theorem dispatchSyscall_preserves_ipcInvariantFull
    (st st' : SystemState) (hInv : ipcInvariantFull st)
    (hStep : dispatchSyscall st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hInv hStep""",
        """theorem dispatchSyscall_preserves_ipcInvariantFull
    (st stOther st' : SystemState) (hInv : ipcInvariantFull st)
    (hStep : dispatchSyscall stOther = .ok ((), st'))
    (hEq : st' = st) :
    ipcInvariantFull st' := by
  exact hEq ▸ hInv""",
    )
    cases.append(
        _Case(
            "a step equation from an unrelated state does not validate a payoff",
            unrelated_step,
            True,
            check="payoff_statement",
            mutation="preserving",
        )
    )

    # A private twin standing validation for a vacuous public payoff: the
    # visibility-blind last-wins dictionary validated the private theorem
    # while presence saw the public one.
    private_shadow = _fixture()
    private_shadow["SeLe4n/Kernel/API.lean"] = CLEAN_PAYOFF.replace(
        """theorem dispatchSyscall_preserves_ipcInvariantFull
    (st st' : SystemState) (hInv : ipcInvariantFull st)
    (hStep : dispatchSyscall st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hInv hStep""",
        """theorem dispatchSyscall_preserves_ipcInvariantFull :
    True := trivial""",
    )
    private_shadow["SeLe4n/Kernel/ZzPrivateTwin.lean"] = (
        "namespace SeLe4n.Kernel\n"
        "\n"
        "private theorem dispatchSyscall_preserves_ipcInvariantFull\n"
        "    (st st' : SystemState) (hInv : ipcInvariantFull st)\n"
        "    (hStep : dispatchSyscall st = .ok ((), st')) :\n"
        "    ipcInvariantFull st' := by\n"
        "  exact sample st st' hInv hStep\n"
        "\n"
        "end SeLe4n.Kernel\n"
    )
    cases.append(
        _Case(
            "a private twin cannot stand validation for a vacuous public payoff",
            private_shadow,
            True,
            check="payoff_statement",
            mutation="preserving",
        )
    )

    # An orphaned payoff module: every declaration intact, but no build
    # root reaches its file, so CI compiles none of the theorems.
    orphan_payoff = _fixture()
    orphan_payoff["lakefile.toml"] = (
        'name = "fixturekernel"\n'
        'defaultTargets = ["fixturekernel"]\n'
        "\n"
        "[[lean_exe]]\n"
        'name = "fixturekernel"\n'
        'root = "Main"\n'
    )
    orphan_payoff["Main.lean"] = (
        "import SeLe4n.Kernel.IPC.Invariant.Defs\n"
        "import SeLe4n.Kernel.IPC.Invariant.Structural.Bundles\n"
        "\n"
        "def main : IO Unit := pure ()\n"
    )
    cases.append(
        _Case(
            "a payoff module no build root reaches is an orphan, not a consumer",
            orphan_payoff,
            True,
            check="payoff_theorems",
            mutation="preserving",
        )
    )

    # A nonrec-spelled bundle: the modifier is routine, and a grammar
    # without it dropped the declaration -- and its threaded hypothesis --
    # from the census.
    nonrec_bundle = _fixture()
    nonrec_bundle["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "theorem endpointSendDual_preserves_ipcInvariantFull",
            "nonrec theorem endpointSendDual_preserves_ipcInvariantFull",
        ).replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hT : blockedThreadsPendingMessageConsistent st')\n",
        )
    )
    cases.append(
        _Case(
            "a nonrec-spelled threaded bundle is measured like a theorem",
            nonrec_bundle,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # A wrapped transport: `some st' = some st` closes the theorem via
    # `Option.some.inj` while the step from an unrelated state stays
    # unused, and no bare-side test can enumerate the wrapper shapes --
    # only tying the step's input to a covered pre-state ends the class.
    wrapped_transport = _fixture()
    wrapped_transport["SeLe4n/Kernel/API.lean"] = CLEAN_PAYOFF.replace(
        """theorem dispatchSyscall_preserves_ipcInvariantFull
    (st st' : SystemState) (hInv : ipcInvariantFull st)
    (hStep : dispatchSyscall st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hInv hStep""",
        """theorem dispatchSyscall_preserves_ipcInvariantFull
    (st stOther st' : SystemState) (hInv : ipcInvariantFull st)
    (hStep : dispatchSyscall stOther = .ok ((), st'))
    (hEq : some st' = some st) :
    ipcInvariantFull st' := by
  exact (Option.some.inj hEq) ▸ hInv""",
    )
    cases.append(
        _Case(
            "a wrapped transport does not validate an unrelated-input step",
            wrapped_transport,
            True,
            check="payoff_statement",
            mutation="preserving",
        )
    )

    # The pack-carried pre-state, accepted: a structure whose field is an
    # exact family application on its own state binder covers that state,
    # so a payoff consuming the pack steps a covered state.  Pins the
    # carrier derivation positively -- the live payoffs are this shape.
    pack_carried = _fixture()
    pack_carried["SeLe4n/Kernel/API.lean"] = CLEAN_PAYOFF.replace(
        """theorem dispatchSyscall_preserves_ipcInvariantFull
    (st st' : SystemState) (hInv : ipcInvariantFull st)
    (hStep : dispatchSyscall st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hInv hStep""",
        """structure fixtureDispatchQuiescence (budget : Nat)
    (st : SystemState) : Prop where
  reachable : ipcInvariantFull st

theorem dispatchSyscall_preserves_ipcInvariantFull
    (budget : Nat) (st st' : SystemState)
    (hPack : fixtureDispatchQuiescence budget st)
    (hStep : dispatchSyscall st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hPack.reachable hStep""",
    )
    cases.append(
        _Case(
            "a pack-carried pre-state satisfies the step-input rule",
            pack_carried,
            False,
        )
    )

    # An instance-spelled proof: the toolchain elaborates a named instance
    # of a non-class Prop, so the census must not be the scanner that
    # assumed it could not.
    instance_bundle = _fixture()
    instance_bundle[
        "SeLe4n/Kernel/IPC/Invariant/Structural/InstanceBundles.lean"
    ] = (
        "instance endpointInstanceDual_preserves_ipcInvariantFull\n"
        "    (st st' : SystemState)\n"
        "    (hInv : ipcInvariantFull st)\n"
        "    (hStep : endpointInstanceDual st = .ok ((), st'))\n"
        "    (hT : blockedThreadsPendingMessageConsistent st') :\n"
        "    ipcInvariantFull st' :=\n"
        "  sample st st' hInv hStep\n"
    )
    cases.append(
        _Case(
            "an instance-spelled threaded bundle is measured like a theorem",
            instance_bundle,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # A `public section`: unbalanced in the scanner, its `end` popped the
    # enclosing namespace, so a nested same-name namespace recorded the
    # canonical prefix while Lean placed its declarations deeper.
    public_section = _fixture()
    public_section["SeLe4n/Kernel/API.lean"] = CLEAN_PAYOFF.replace(
        "namespace SeLe4n.Kernel\n",
        "namespace SeLe4n.Kernel\n"
        "\n"
        "public section Hidden\n"
        "end Hidden\n"
        "\n"
        "namespace SeLe4n.Kernel\n",
        1,
    ).replace(
        "end SeLe4n.Kernel",
        "end SeLe4n.Kernel\n\nend SeLe4n.Kernel",
    )
    cases.append(
        _Case(
            "a public section cannot desynchronise the namespace prefixes",
            public_section,
            True,
            check="payoff_theorems",
            mutation="preserving",
        )
    )

    # Dot-notation application: `st'.blockedThreadsPendingMessageConsistent`
    # applies the SystemState-namespaced predicate to `st'`, and a scan
    # that read every binder-headed chain as a field projection missed the
    # threaded hypothesis.
    dot_notation = _fixture()
    dot_notation["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        "def SystemState.blockedThreadsPendingMessageConsistent\n"
        "    (s : SystemState) : Prop :=\n"
        "  blockedThreadsPendingMessageConsistent s\n"
        "\n"
        + CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hT : st'.blockedThreadsPendingMessageConsistent)\n",
        )
    )
    cases.append(
        _Case(
            "a dot-notation conjunct application is a threaded hypothesis",
            dot_notation,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # A backtick-paren inside a guillemet identifier is identifier text: a
    # quotation blanker blind to «…» scope blanked from there to end of
    # file, and the threaded bundle after it left the census.
    guillemet_backtick = _fixture()
    guillemet_backtick[
        "SeLe4n/Kernel/IPC/Invariant/Structural/GuillemetBundles.lean"
    ] = (
        "def «harmless`(unclosed» : Nat := 0\n"
        "\n"
        + CLEAN_BUNDLE.replace(
            "theorem endpointSendDual_preserves_ipcInvariantFull",
            "theorem endpointGuillemetDual_preserves_ipcInvariantFull",
        ).replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hT : blockedThreadsPendingMessageConsistent st')\n",
        )
    )
    cases.append(
        _Case(
            "a threaded bundle after a backtick-bearing quoted identifier is seen",
            guillemet_backtick,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # A `show Prop from` wrapper inside a nested conjunct body: the
    # spelling elaborates identically, and a walker that stopped at
    # `by exact` left the leading conjunct unmatched.
    show_from = _fixture()
    show_from[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def replyCallerLinkage (st : SystemState) : Prop :=\n"
        "  replyCallerLinkageReciprocal st ∧ blockedOnReplyHasReplyObject st",
        "def replyCallerLinkage (st : SystemState) : Prop :=\n"
        "  by exact show Prop from replyCallerLinkageReciprocal st ∧ blockedOnReplyHasReplyObject st",
    )
    show_from["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hR : replyCallerLinkageReciprocal st')\n",
        )
    )
    cases.append(
        _Case(
            "a show-from wrapped conjunct body still derives",
            show_from,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # A strengthened conclusion, accepted: conjuncts in the final segment
    # are guarantees the theorem establishes, not assumptions -- flagging
    # them punished proving more.
    strengthened = _fixture()
    strengthened["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    ipcInvariantFull st' := by",
            "    ipcInvariantFull st' ∧ blockedThreadsPendingMessageConsistent st' := by",
        )
    )
    cases.append(
        _Case(
            "a strengthened conclusion's own conjuncts are not threading",
            strengthened,
            False,
        )
    )

    # A same-named shadow pack that carries must not make the canonical
    # non-carrying pack mint pre-states: carriers suppress findings, so
    # the verdict is unanimous across declarations.
    shadow_pack = _fixture()
    shadow_pack["SeLe4n/Kernel/API.lean"] = CLEAN_PAYOFF.replace(
        """theorem dispatchSyscall_preserves_ipcInvariantFull
    (st st' : SystemState) (hInv : ipcInvariantFull st)
    (hStep : dispatchSyscall st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hInv hStep""",
        """structure fixtureQuiescencePack (st : SystemState) : Prop where
  trivialFact : True

namespace ShadowView

structure fixtureQuiescencePack (st : SystemState) : Prop where
  reachable : ipcInvariantFull st

end ShadowView

theorem dispatchSyscall_preserves_ipcInvariantFull
    (st st' : SystemState)
    (hPack : fixtureQuiescencePack st)
    (hStep : dispatchSyscall st = .ok ((), st')) :
    ipcInvariantFull st' := by
  exact sample st st' hPack.trivialFact hStep""",
    )
    cases.append(
        _Case(
            "a carrying shadow pack cannot cover a non-carrying canonical pack",
            shadow_pack,
            True,
            check="payoff_statement",
            mutation="preserving",
        )
    )

    # An unknown command carrying a threaded declaration: the whole
    # surface-spelling class in one fixture.  Before the tripwire, a
    # declaration under a command the grammars did not know was silently
    # invisible to every census and scan -- the shape eight review rounds
    # found one spelling at a time.  Now the unknown token itself is the
    # finding.
    unknown_command = _fixture()
    unknown_command[
        "SeLe4n/Kernel/IPC/Invariant/Structural/DslBundles.lean"
    ] = (
        "register_theorem endpointDslDual_preserves_ipcInvariantFull\n"
        "    (st st' : SystemState)\n"
        "    (hInv : ipcInvariantFull st)\n"
        "    (hStep : endpointDslDual st = .ok ((), st'))\n"
        "    (hT : blockedThreadsPendingMessageConsistent st') :\n"
        "    ipcInvariantFull st' :=\n"
        "  sample st st' hInv hStep\n"
    )
    cases.append(
        _Case(
            "an unknown command is the gate's finding, not a silent blind spot",
            unknown_command,
            True,
            check="grammar_coverage",
            mutation="preserving",
        )
    )

    # A one-line composite command: `open … in theorem …` wraps the
    # declaration on the `open`'s own line, and a line-anchored census
    # blind to the prefix missed it entirely.
    inline_composite = _fixture()
    inline_composite["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "theorem endpointSendDual_preserves_ipcInvariantFull",
            "open Nat in theorem endpointSendDual_preserves_ipcInvariantFull",
        ).replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hT : blockedThreadsPendingMessageConsistent st')\n",
        )
    )
    cases.append(
        _Case(
            "a declaration behind a one-line open-in prefix is censused",
            inline_composite,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # A meta-spelled proof: `meta def X_preserves_… : … := …` elaborates
    # (toolchain-verified), and with the single-source refactor the
    # modifier is learned once for every grammar at once.
    meta_bundle = _fixture()
    meta_bundle["SeLe4n/Kernel/IPC/Invariant/Structural/MetaBundles.lean"] = (
        "meta def endpointMetaDual_preserves_ipcInvariantFull\n"
        "    (st st' : SystemState)\n"
        "    (hInv : ipcInvariantFull st)\n"
        "    (hStep : endpointMetaDual st = .ok ((), st'))\n"
        "    (hT : blockedThreadsPendingMessageConsistent st') :\n"
        "    ipcInvariantFull st' :=\n"
        "  sample st st' hInv hStep\n"
    )
    cases.append(
        _Case(
            "a meta-spelled threaded bundle is measured like a theorem",
            meta_bundle,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # `echo lake build …` is a log line, not a build: roots suppress
    # findings, so a root minted from non-command text is the fail-open
    # direction, and the quote-aware command resolver refuses it.
    echo_root = _fixture()
    echo_root["lakefile.toml"] = (
        'name = "fixturekernel"\n'
        'defaultTargets = ["fixturekernel"]\n'
        "\n"
        "[[lean_exe]]\n"
        'name = "fixturekernel"\n'
        'root = "Main"\n'
    )
    echo_root["Main.lean"] = (
        "import SeLe4n.Kernel.IPC.Invariant.Defs\n"
        "import SeLe4n.Kernel.IPC.Invariant.Structural.Bundles\n"
        "\n"
        "def main : IO Unit := pure ()\n"
    )
    echo_root["scripts/fixture_note.sh"] = (
        "#!/bin/sh\n"
        'echo lake build SeLe4n.Kernel.API\n'
    )
    cases.append(
        _Case(
            "an echoed lake-build line does not mint a build root",
            echo_root,
            True,
            check="payoff_theorems",
            mutation="preserving",
        )
    )

    # A marker-named theorem concluding only the structural core: the name
    # claims the full invariant, and the census must not seat a downgraded
    # conclusion -- `ipcInvariantCore` stays pre-state vocabulary.
    core_conclusion = _fixture()
    core_conclusion["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    ipcInvariantFull st' := by",
            "    ipcInvariantCore st' := by",
        )
    )
    cases.append(
        _Case(
            "a core-only conclusion does not satisfy the family's name",
            core_conclusion,
            True,
            check="family_conclusion",
            mutation="preserving",
        )
    )

    # An implicit state binder: `{st : SystemState}` declares the same
    # predicate (toolchain-verified), applied by the root with the named
    # argument the derivation already normalises.
    implicit_binder = _fixture()
    implicit_binder[DEFS_MODULE] = CLEAN_DEFS.replace(
        "def replyCallerLinkage (st : SystemState) : Prop :=",
        "def replyCallerLinkage {st : SystemState} : Prop :=",
    ).replace(
        "  blockedThreadsPendingMessageConsistent st ∧ replyCallerLinkage st",
        "  blockedThreadsPendingMessageConsistent st ∧ replyCallerLinkage (st := st)",
    )
    implicit_binder["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hR : replyCallerLinkageReciprocal st')\n",
        )
    )
    cases.append(
        _Case(
            "an implicit-binder conjunct definition still derives",
            implicit_binder,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # A quoted qualifier segment: `«foo».conjunct st'` is valid Lean the
    # plain-identifier chain grammar could not reach.
    quoted_qualifier = _fixture()
    quoted_qualifier["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hQ : «foo».blockedThreadsPendingMessageConsistent st')\n",
        )
    )
    cases.append(
        _Case(
            "a conjunct behind a quoted qualifier segment is still scanned",
            quoted_qualifier,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # A disjunctive step hypothesis: `dispatchSyscall st = .ok ((), st') ∨
    # True` establishes no equality, yet the old connective cut validated
    # the arm it kept.
    disjunctive_step = _fixture()
    disjunctive_step["SeLe4n/Kernel/API.lean"] = CLEAN_PAYOFF.replace(
        "    (hStep : dispatchSyscall st = .ok ((), st')) :",
        "    (hStep : dispatchSyscall st = .ok ((), st') ∨ True) :",
    )
    cases.append(
        _Case(
            "a step equation under a disjunction does not validate a payoff",
            disjunctive_step,
            True,
            check="payoff_statement",
            mutation="preserving",
        )
    )

    # A transformed whole-invariant hypothesis: `ipcInvariantFull (id st')`
    # is definitionally the post-state assumption, textually unequal to it.
    transformed_invariant = _fixture()
    transformed_invariant["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hInv' : ipcInvariantFull (id st'))\n",
        )
    )
    cases.append(
        _Case(
            "a whole-invariant hypothesis carrying the conclusion state is caught",
            transformed_invariant,
            True,
            check="no_conclusion_state_hypothesis",
            mutation="preserving",
        )
    )

    # A definitionally reflexive anchor: `pair st' stMid = id (pair st'
    # stMid)` is provable by `rfl` with textually different sides -- only
    # the directional rule (a side must be fully anchored to unlock the
    # equation) keeps it from laundering `stMid` through the shared `st'`.
    definitional_anchor = _fixture()
    definitional_anchor["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (st st' : SystemState)\n",
            "    (st stMid st' : SystemState)\n",
        ).replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hAnchor : pair st' stMid = id (pair st' stMid))\n"
            "    (hMid : ipcInvariantCore stMid)\n"
            "    (hT : blockedThreadsPendingMessageConsistent stMid)\n",
        )
    )
    cases.append(
        _Case(
            "a definitionally reflexive equation does not anchor its states",
            definitional_anchor,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # An uninvoked macro template: the quotation's text spells a theorem
    # that declares nothing, and the census must not count syntax data.
    quotation_census = _fixture()
    quotation_census["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        'macro "declareSendBundle" : command => `(\n'
        "theorem endpointSendDual_preserves_ipcInvariantFull\n"
        "    (st st' : SystemState)\n"
        "    (hInv : ipcInvariantFull st)\n"
        "    (hStep : endpointSendDual st = .ok ((), st')) :\n"
        "    ipcInvariantFull st' := by\n"
        "  exact sample st st' hInv hStep\n"
        ")\n"
    )
    cases.append(
        _Case(
            "an uninvoked macro template is not a family declaration",
            quotation_census,
            True,
            check="family_nonempty",
            mutation="preserving",
        )
    )

    # An *indented* user-defined command (PR #886 review): `grammar_coverage`
    # reads column 0 only, and inside the namespace the invocation
    # `  registerHidden` is textually a term continuation, so the theorem it
    # would mint -- threaded hypothesis and all -- is invisible to every
    # census.  Position cannot close the class; mechanism can: the `macro`
    # declaring the command is a token at any indentation, and it is not
    # pinned.
    indented_dsl = _fixture()
    indented_dsl["SeLe4n/Kernel/IPC/Invariant/Structural/HiddenDsl.lean"] = (
        'macro "registerHidden" : command => `(\n'
        "theorem hidden_preserves_ipcInvariantFull\n"
        "    (st st' : SystemState)\n"
        "    (hInv : ipcInvariantFull st)\n"
        "    (hT : blockedThreadsPendingMessageConsistent st') :\n"
        "    ipcInvariantFull st' := by\n"
        "  exact sample st st' hInv hT\n"
        ")\n"
        "namespace Hidden\n"
        "  registerHidden\n"
        "end Hidden\n"
    )
    cases.append(
        _Case(
            "an indented command's minting machinery is caught by token, not position",
            indented_dsl,
            True,
            check="minting_machinery",
            mutation="preserving",
        )
    )

    # The stale-pin direction: the pinned manifest file exists but carries
    # none of its pinned machinery -- the pin token survives in the gate
    # while the file relation is broken, and a pin that tolerated the drift
    # would rot into a standing exemption for whatever machinery returns
    # under that path.
    stale_pin = _fixture()
    stale_pin["SeLe4n/Kernel/Concurrency/PhaseTheoremManifest.lean"] = (
        "def phaseManifestPlaceholder : Prop := True\n"
    )
    cases.append(
        _Case(
            "a pinned file that lost its machinery is a stale pin, not an exemption",
            stale_pin,
            True,
            check="minting_machinery",
            mutation="preserving",
        )
    )

    # A family-shaped token nothing declares: the marker is present and the
    # relation (resolution to a censused declaration) is broken -- the shape
    # a DSL invocation naming its minted theorem takes, wherever it sits.
    ghost_reference = _fixture()
    ghost_reference["SeLe4n/Kernel/IPC/Invariant/Structural/GhostUser.lean"] = (
        "theorem ghostConsumer (st st' : SystemState) : True := by\n"
        "  exact ghost_preserves_ipcInvariantFull st st'\n"
    )
    cases.append(
        _Case(
            "a family-shaped token with no censused declaration fails to resolve",
            ghost_reference,
            True,
            check="family_references",
            mutation="preserving",
        )
    )

    # A quoted identifier's `)` inside a quotation (PR #886 review): the
    # balancer read `«x)»`'s paren as the quotation terminator and exposed
    # the inert template to the census, so syntax data satisfied
    # `family_nonempty`.  With guillemet interiors neutralised at the
    # string layer, the template blanks fully and the sole "bundle"
    # vanishes -- the family census goes honestly empty.
    quoted_attribute = _fixture()
    quoted_attribute["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        'macro "declareSendBundle" : command => `(\n'
        "@[«x)»] theorem endpointSendDual_preserves_ipcInvariantFull\n"
        "    (st st' : SystemState)\n"
        "    (hInv : ipcInvariantFull st)\n"
        "    (hStep : endpointSendDual st = .ok ((), st')) :\n"
        "    ipcInvariantFull st' := by\n"
        "  exact sample st st' hInv hStep\n"
        ")\n"
    )
    cases.append(
        _Case(
            "a quoted identifier's paren does not terminate a quotation's balance",
            quoted_attribute,
            True,
            check="family_nonempty",
            mutation="preserving",
        )
    )

    # The two accepted guillemet trees, pinning the fix's own fail-closed
    # edges: a delimiter inside a quoted *binder* must not desynchronise
    # the binder walkers, and a guillemet-quoted *family name* must keep
    # its marker (word characters survive neutralisation) or the census
    # would lose a real declaration.
    guillemet_binder = _fixture()
    guillemet_binder["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (st st' : SystemState)\n",
            "    (st st' : SystemState) («h)note» : True)\n",
        )
    )
    cases.append(
        _Case(
            "a guillemet identifier with a delimiter inside stays one atomic token",
            guillemet_binder,
            False,
            mutation="none",
        )
    )

    guillemet_name = _fixture()
    guillemet_name["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "theorem endpointSendDual_preserves_ipcInvariantFull\n",
            "theorem «endpointSendDual_preserves_ipcInvariantFull»\n",
        )
    )
    cases.append(
        _Case(
            "a guillemet-quoted family name keeps its marker and census seat",
            guillemet_name,
            False,
            mutation="none",
        )
    )

    # A non-leading state parameter (PR #886 review, toolchain-verified):
    # `replyCallerLinkage (enabled : Bool) (st : SystemState)` is the same
    # nested conjunct with an ordinary parameter in front, and the root
    # applies it `replyCallerLinkage true st`.  The old collector demanded
    # the state group immediately after the name and the old application
    # parse was unary, so the definition -- and through the closure its
    # clause predicates -- left the derived set: threading
    # `replyCallerLinkageReciprocal st'` scored clean.
    nonleading_defs = CLEAN_DEFS.replace(
        "def replyCallerLinkage (st : SystemState) : Prop :=\n"
        "  replyCallerLinkageReciprocal st ∧ blockedOnReplyHasReplyObject st",
        "def replyCallerLinkage (enabled : Bool) (st : SystemState) : Prop :=\n"
        "  replyCallerLinkageReciprocal st ∧ blockedOnReplyHasReplyObject st",
    ).replace(
        "  blockedThreadsPendingMessageConsistent st ∧ replyCallerLinkage st",
        "  blockedThreadsPendingMessageConsistent st ∧ replyCallerLinkage true st",
    )
    nonleading_clause = _fixture()
    nonleading_clause[DEFS_MODULE] = nonleading_defs
    nonleading_clause["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hR : replyCallerLinkageReciprocal st')\n",
        )
    )
    cases.append(
        _Case(
            "a clause of a non-leading-state parent is still a measured conjunct",
            nonleading_clause,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # The multi-parameter conjunct itself, bound with the post-state in its
    # *state* slot: the state is the second explicit argument, so a scan
    # reading the first would miss `st'` behind the leading `true`.
    nonleading_slot = _fixture()
    nonleading_slot[DEFS_MODULE] = nonleading_defs
    nonleading_slot["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hQ : replyCallerLinkage true st')\n",
        )
    )
    cases.append(
        _Case(
            "a non-leading state slot's post-state binding is found at its position",
            nonleading_slot,
            True,
            check="no_post_state_binding",
            mutation="preserving",
        )
    )

    # And the accepted twin: the same hypothesis on the *pre*-state must
    # stay clean -- a scan that read the first argument would flag the
    # leading `true` as a bound non-pre-state on perfectly clean code.
    nonleading_clean = _fixture()
    nonleading_clean[DEFS_MODULE] = nonleading_defs
    nonleading_clean["SeLe4n/Kernel/IPC/Invariant/Structural/Bundles.lean"] = (
        CLEAN_BUNDLE.replace(
            "    (hInv : ipcInvariantFull st)\n",
            "    (hInv : ipcInvariantFull st)\n"
            "    (hOk : replyCallerLinkage true st)\n",
        )
    )
    cases.append(
        _Case(
            "a non-leading state slot bound on the pre-state stays clean",
            nonleading_clean,
            False,
            mutation="none",
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
