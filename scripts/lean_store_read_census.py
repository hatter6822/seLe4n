#!/usr/bin/env python3
"""Census of raw object-store reads, classified by what the read *is*.

A `st.objects[k]?` in a theorem statement and one in a transition body are not
the same thing, and the AK7 cascade's `RAW_LOOKUP_TID` counted them together.
The first is the vocabulary a proposition about the store is written in -- there
is no helper form of "the store holds this at that key", because
`getTcb? k = none` is satisfied both by an absent key and by a wrong-kinded
object, so a frame statement quantified over every key cannot be phrased
through a variant accessor without weakening it.  The second is a transition
declining to use a reader that exists, which is the thing the migration drives
out.

So this census emits two populations:

  CODE  -- the read sits in a term position of a declaration whose result is
           *not* a `Prop`: a transition, a resolver, a projection.  These are
           migratable and the gate holds them at a ceiling.
  SPEC  -- everything else: `theorem`/`lemma` bodies and statements, the fields
           of a `Prop`-valued `structure`, the arguments of an `inductive`
           constructor, and the binders and result of a `def` that returns a
           `Prop`.  Reported, never enforced.

Rows are keyed by **(file, enclosing declaration)** with an occurrence count.
That granularity is deliberate and is the one `RAW_SITE` already uses: a
(file) key is a cardinality one level up, so hygienizing one declaration while
another starts reading raw leaves the row unmoved -- the very movement the
inventory exists to catch.  The declaration is the unit of hygienization, so
finer keys (line numbers) would churn on every unrelated edit above them.

Occurrences are counted, not lines: two reads on one line are two reads, and a
reflow that joins two lines must not lower the number.

Reads are counted over the comment-free code view, so a docstring quoting the
pattern is not a read.

Usage:
    lean_store_read_census.py --rows            # CODE/SPEC rows for the baseline
    lean_store_read_census.py --totals          # the two scalars
    lean_store_read_census.py --self-test       # fixture-driven checks
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(Path(__file__).resolve().parent))
import lean_code_view  # noqa: E402  (needs the path above)

# A raw read of an object table, in **either** spelling.  `.objects.insert` is a
# write and is a different question (STOREOBJECTCHECKED_ADOPTION asks it).
#
# **Both spellings, because they are one read.**  `s.objects[k]?` is `GetElem?`
# notation whose instance *is* `RHTable.get?`, which this tree proves outright
# (`objects_getElem?_eq_get?`, by `rfl`).  Counting the bracket alone therefore
# measured a spelling rather than a read, and the gap was not theoretical: a cut
# wrote `Concurrency.updateObjectAt` in the method form and said so in its own
# docstring — *"so the AK7-cascade raw-match floor stays at its v0.31.2
# baseline"* — which is choosing a spelling to evade a metric.  A scanner that
# can be satisfied by a rename is a scanner asserting nothing, and an enforced
# zero that one spelling walks around is worse than no zero at all, because the
# number reads like a measurement.
#
# The frozen surface is in scope for the same reason it was never out of it: the
# claim is about *executable code discriminating a kernel object's variant at
# the call site*, `FrozenSystemState.objects` holds the live `Reply`, `TCB` and
# `SchedContext` records verbatim, and the hazard is identical.  It has its own
# accessor family now (`Model/FrozenState.lean`), so both tables answer the
# same question the same way.
READ = re.compile(
    r"\.objects(?:\[|\.get\?)"                       # `st.objects[k]?` / `st.objects.get? k`
    r"|\b(?:RHTable|FrozenMap)\.get\?\s+[\w'.]*\.objects\b"  # the qualified call
)

# **What this gate can and cannot claim.**
#
# It recognises the spellings above.  It is NOT a proof that no executable
# definition reads the object table: the set of ways to write that read is
# unbounded -- notation, `open`, an alias, a qualified call, a helper that takes
# the table -- and two review rounds each found one more.  A count over a
# recognised set is a FLOOR, and reporting it as a bare `0` is what made each
# widening read as a defect report rather than an improvement.
#
# The property this gate is named for -- "executable code obtains a typed object
# through an accessor" -- is a coding convention over unbounded syntax, and it
# has no closed formulation, in text or in the environment.  The elaborator
# answers questions about *elaboration* (which declaration a name denotes, what
# a term reaches); "is this occurrence a read rather than a write" is a question
# about an API's meaning, and the environment has no opinion on it.  Measured
# rather than assumed (`v0.35.13`): 245 hand-written executable definitions
# mention the object-table projection, because writing the store is what a
# transition does, so "never mention it" is not a stateable contract either.
#
# So the number is reported as a floor and the gate says so.  The ZERO_METRICS
# entry still bites -- a recognised read fails Tier 0 outright -- and widening
# the recogniser is an improvement to a diagnostic, not the closing of a hole
# that was claimed shut.

# **A command may be indented.**  Lean permits leading whitespace before a
# declaration, and anchoring the pattern at column zero meant an indented `def`
# was not recognised at all: its body stayed attributed to the *previous*
# declaration, so a raw store read in an indented transition following a
# `theorem` was emitted as `SPEC` and walked around the enforced
# `STORE_READ_CODE = 0` (PR #895 review round 5).
# **An unrecognised declaration keyword is not a missing feature, it is a
# misattribution.**  `opaque` was absent from this alternation, and the tree has
# **73** `opaque` declarations at column zero: each one left `sig_open`/`decl`
# pointing at whatever declaration preceded it, so an executable `opaque` body
# following a `theorem` had its reads emitted under the theorem's name as
# `SPEC` -- past the enforced `STORE_READ_CODE = 0` (PR #895 review round 6).
# No `opaque` body holds a recognised read today, so the floor was not false;
# the hole was open and unoccupied.
#
# What bounds the class rather than this one keyword is the elaborator:
# `SeLe4n/Testing/StoreReadClassificationCensus.lean` asks
# `findDeclarationRanges?` which declaration owns each emitted line, so a read
# attributed to the wrong declaration is a Tier 1 build failure whatever
# spelling caused it -- which is why its mismatch message names exactly this
# case.  Keep this list current anyway: Tier 0 is where the metric is read, and
# a gate that needs its sibling to notice every miss is a worse gate.
DECL = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|partial\s+|noncomputable\s+|nonrec\s+|scoped\s+|unsafe\s+)*"
    r"(theorem|lemma|def|abbrev|instance|example|structure|inductive|class|opaque|axiom)"
    r"\b\s+([^\s:({\[]*)"
)

# Declaration keywords whose contents are propositions or types whatever their
# signature: a `theorem`/`lemma`/`example` body is a proof, and an `inductive`
# body is its constructors' argument types.
PROP_KINDS = {"theorem", "lemma", "example", "inductive"}

# **A field default is executable, and a structure is not wholly a proposition.**
# `structure` and `class` used to sit in `PROP_KINDS`, so every line of their
# bodies was spec -- but a field may carry a DEFAULT, and a default is a term
# the elaborator compiles and the runtime evaluates:
#
#     structure Cache where
#       cached : Option KernelObject := st.objects[oid]?   -- executes
#
# So a raw store read in a default was filed `SPEC` and walked around the
# enforced `STORE_READ_CODE = 0` floor.  That is this file's own "a recognised
# set is not a derived set" once more: the *kind* of a declaration was taken to
# decide the nature of every line inside it, when the two halves of a field line
# have different natures.  A field's TYPE stays spec -- the invariant bundles in
# this tree are structures whose fields are propositions about the store, and
# reading those as transitions would be reading a hypothesis as code.
FIELD_KINDS = {"structure", "class"}

# **A binder is not the result.**  `PROP_RESULT` used to be `:\s*Prop\b` over the
# whole signature, so `def step (proof : Prop) (st : SystemState) : SystemState`
# read as Prop-valued and a raw store read in its body was filed `SPEC` —
# bypassing the enforced `STORE_READ_CODE = 0` floor.  That is this file's own
# "a recognised set is not a derived set" one level in: the *domain* of the code
# population was decided by a regex that matched anywhere in the signature.
#
# The question is the declaration's TERMINAL result, so parse it: the first `:`
# at bracket depth zero opens the result type, and the last top-level `→` arrow
# within it names what the declaration ultimately returns.  A signature with no
# depth-zero `:` has no declared result and fails CLOSED (its body counts as
# code), which is the safe direction for a gate that produces a zero floor.
_OPENERS = "([{⟨"
_CLOSERS = ")]}⟩"


def _result_type(head: str) -> str:
    """The declared result type of a signature, or `""` when none is declared."""
    depth = 0
    for i, ch in enumerate(head):
        if ch in _OPENERS:
            depth += 1
        elif ch in _CLOSERS:
            depth -= 1
        elif ch == ":" and depth == 0:
            # `:=` is the signature terminator and never opens a result type;
            # `_signature_head` has already cut there, so a bare `:` is ours.
            return head[i + 1:].strip()
    return ""


ASSIGN = re.compile(r":=")


def _depth_zero_scan(line: str, pattern: "re.Pattern[str]", depth: int = 0):
    """`(first depth-zero match of `pattern` on this line or None, depth after)`.

    **One walk, every top-level-token question.**  A binder's `optParam`
    (`(n : Nat := 0)`), a record literal's fields and a defaulted argument all
    sit at depth > 0, so only a depth-zero match is the declaration's own
    terminator or the field's own default.

    **Depth carries across lines**, and the caller threads it back in: resetting
    per line reads a continuation as though its bracket had never been opened —
    this file's own *a nested construct is not a sibling*, which it paid for
    once in the structure split and once, three functions away, in the signature
    terminator that kept using a bare `search` under a comment promising
    "top-level" (PR #895 review rounds 4 and 5).
    """
    found = None
    i = 0
    while i < len(line):
        ch = line[i]
        if ch in _OPENERS:
            depth += 1
        elif ch in _CLOSERS:
            depth -= 1
        elif found is None and depth == 0:
            m = pattern.match(line, i)
            if m is not None:
                found = m
        i += 1
    return found, depth


def _top_level_assign(line: str, depth: int = 0):
    """The depth-zero `:=` that opens a structure field's default value."""
    m, depth = _depth_zero_scan(line, ASSIGN, depth)
    return (m.start() if m is not None else None), depth


#: A term-level binder keyword whose own `:=` is not a binder default's.
_TERM_BINDERS = ("let", "have", "suffices", "show")

_TERM_BINDER_SCAN = re.compile(
    r"(?<![A-Za-z0-9_'!?.])(" + "|".join(_TERM_BINDERS) + r")(?![A-Za-z0-9_'!?.])")


def _binding_open_at(text: str, at: int, depth: int) -> bool:
    """Does the `:=` at `at` belong to a `let`/`have` rather than to a binder?

    **Not every `:=` inside a binder group is a default** (PR #895 review
    round 12).  A binder *type* may contain a term-level binding —
    `(h : (let obj := st.objects[oid]?; obj = none))`, which Lean accepts — and
    reading that `:=` as the start of an executable default filed the read as
    CODE, so a valid declaration was refused against the enforced
    `STORE_READ_CODE = 0`.  The Tier 1 reconciliation cannot correct it either:
    a declaration-level verdict does not distinguish a default from a type.

    The discriminator is that a binder's default separator is the FIRST `:=`
    after the group's own `:` with no term-level binder keyword between them —
    a `let` opens a binding whose `:=` is its own.  Scanning back to the
    group's opener rather than to the line start is what keeps a `let` in a
    *previous* binder group from suppressing this one's default.

    Over-approximating here files the whole group as specification, which is the
    fail-open direction against the zero — so the scan is deliberately narrow:
    only a whole-word keyword at the `:=`'s **own** depth counts.

    **A keyword in a nested group does not own this `:=`** (PR #895 review round
    13).  Scanning the enclosing group's whole span found a `let` that had
    already closed — `(obj : (let T := Option KernelObject; T) := st.objects[oid]?)`,
    which Lean accepts — so the binder default was read as that `let`'s
    assignment and the executable read was filed `SPEC region=sig`.  Signature
    rows are the one region the Tier 1 reconciliation does not judge (a
    declaration-level verdict cannot adjudicate a hypothesis binder), so the read
    bypassed BOTH enforcement tiers rather than one.  The span is therefore
    walked at depth rather than searched: `_depth_zero_scan` is the same walk
    every other top-level-token question in this file already uses, so the
    nesting rule has one implementation and not a second that can disagree.
    """
    start, level = 0, depth
    for j in range(at - 1, -1, -1):
        ch = text[j]
        if ch in _CLOSERS:
            level += 1
        elif ch in _OPENERS:
            level -= 1
            if level < depth:
                start = j + 1
                break
    found, _ = _depth_zero_scan(text[start:at], _TERM_BINDER_SCAN)
    return found is not None


def _split_binder_defaults(text: str, depth: int = 0, default_depth=None):
    """Split signature text into binder TYPES and binder DEFAULT VALUES.

    `(text spec, text code, depth after, default depth after)`.

    **A binder's type is a proposition; its default is a term.**  In
    `def step (obj : Option KernelObject := st.objects[oid]?) := obj` the
    default is elaborated and evaluated whenever the argument is omitted, so it
    is executable exactly as the declaration's body is -- while the binder type
    beside it is a hypothesis or a type, which is why the signature as a whole
    is specification.  Emitting the whole signature as one bucket therefore let
    an executable read live in a signature and walk around the enforced
    `STORE_READ_CODE = 0` (PR #895 review round 6); it escaped the elaborator
    reconciliation too, which skips `sig` rows because a declaration-level
    verdict cannot adjudicate a hypothesis binder.  A *default* it can
    adjudicate, so these reads are emitted under their own region and judged.

    A default opens at a `:=` **nested inside a binder group** -- a depth-zero
    `:=` is the signature's own terminator, which `_signature_end` has already
    cut -- and closes when that group closes.  Both counters are threaded by the
    caller, since a binder may span lines.
    """
    spec, code = [], []
    i = 0
    while i < len(text):
        ch = text[i]
        if ch in _OPENERS:
            depth += 1
            (code if default_depth is not None else spec).append(ch)
        elif ch in _CLOSERS:
            depth -= 1
            if default_depth is not None and depth < default_depth:
                # The group carrying the default closed, so the binder ended.
                default_depth = None
                spec.append(ch)
            else:
                (code if default_depth is not None else spec).append(ch)
        elif (default_depth is None and depth > 0 and text.startswith(":=", i)
              and not _binding_open_at(text, i, depth)):
            default_depth = depth
            i += 2
            continue
        else:
            (code if default_depth is not None else spec).append(ch)
        i += 1
    return "".join(spec), "".join(code), depth, default_depth


# A declaration whose VALUE is a single name: `abbrev Pred := Prop`.  Chained
# through `prop_aliases` below, this is what makes a predicate written
# `… : Pred` read as specification.
#: `namespace A.B` and its `end`.  Lean's `section` also scopes `variable`s but
#: introduces no name prefix, so it is deliberately not matched here.
NAMESPACE_OPEN = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'!?.]*)\s*$")
NAMESPACE_END = re.compile(r"^\s*end\b")

PROP_ALIAS = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|scoped\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(?:abbrev|def)\s+([A-Za-z_][A-Za-z0-9_'!?]*)[^\n]*?:=\s*([A-Za-z_][A-Za-z0-9_'!?.]*)\s*$"
)


def prop_aliases(view: Path) -> frozenset:
    """The names that denote `Prop`, transitively.

    A predicate may be written `def holds … : Pred := …` over
    `abbrev Pred := Prop`, and testing the terminal result for the literal token
    `Prop` files that read as EXECUTABLE -- rejecting legitimate specification
    text against an enforced zero (PR #895 review round 6).

    **This tree declares none**, measured over the code view, so the set is
    empty and nothing here moves a live number; it exists so that the first one
    written does not fail the build.

    Lexical and therefore incomplete: an alias reached through an import this
    scan does not read, or built by anything but a direct `:=`, is not resolved.
    That residue keeps failing CLOSED -- its reads count as code, never as spec,
    so nothing hides -- and `StoreReadClassificationCensus` reports it as a
    classifier defect rather than leaving the Tier 0 refusal unexplained.
    """
    direct = {}
    for f in sorted(view.rglob("SeLe4n/**/*.lean")):
        scope: list[str] = []
        for line in f.read_text().splitlines():
            opened = NAMESPACE_OPEN.match(line)
            if opened is not None:
                scope.append(opened.group(1))
                continue
            if NAMESPACE_END.match(line) is not None:
                if scope:
                    scope.pop()
                continue
            m = PROP_ALIAS.match(line)
            if m:
                # **A qualified identity, not a last component** (PR #895 review
                # round 12).  Two namespaces may each declare a `Pred`, one an
                # alias of `Prop` and one of `Nat`, and a set of bare names
                # cannot tell a use of the second from a use of the first — so
                # an executable declaration read as specification and its raw
                # store reads walked around the enforced zero.
                here = ".".join(scope + [m.group(1)])
                target = m.group(2)
                direct[here] = (target if target == "Prop"
                                else ".".join(scope + [target]))
    names = set()
    for name in direct:
        seen, cur = set(), name
        while cur in direct and cur not in seen:
            seen.add(cur)
            cur = direct[cur]
        if cur == "Prop":
            names.update(seen)
    return frozenset(names)


def _returns_prop(head: str, aliases: frozenset = frozenset(),
                  scope: tuple = ()) -> bool:
    """Does this signature's terminal result type return `Prop`?"""
    result = _result_type(head)
    if not result:
        return False
    # Split on top-level arrows: `SystemState → Prop` returns `Prop`.
    depth, last = 0, 0
    parts = []
    i = 0
    while i < len(result):
        ch = result[i]
        if ch in _OPENERS:
            depth += 1
        elif ch in _CLOSERS:
            depth -= 1
        elif depth == 0 and result.startswith("→", i):
            parts.append(result[last:i])
            last = i + 1
        elif depth == 0 and result.startswith("->", i):
            # Lean accepts both arrow spellings and this tree uses both, so a
            # predicate written `SystemState -> Prop` must not read as a
            # declaration returning something executable -- that direction
            # fails STRICT, rejecting legitimate specification code against an
            # enforced zero.
            parts.append(result[last:i])
            i += 1
            last = i + 1
        i += 1
    parts.append(result[last:])
    term = parts[-1].strip()
    if re.match(r"Prop\b", term) is not None:
        return True
    if not aliases:
        return False
    head_token = re.match(r"([A-Za-z_][A-Za-z0-9_'!?.]*)", term)
    if head_token is None:
        return False
    tok = head_token.group(1)
    # **Resolved against the use site's namespaces, never by last component**
    # (PR #895 review round 12).  Accepting any alias with the same final
    # component let `B.Pred := Nat` be read as specification because some other
    # namespace declared a `Pred := Prop`, and a raw store read in that
    # declaration then merged into `sig` and escaped both the enforced zero and
    # the Tier 1 reconciliation, which skips that region.  Lean resolves a
    # reference against the enclosing namespaces, longest prefix first, so that
    # is what is tried — and nothing else is.
    for depth in range(len(scope), -1, -1):
        if ".".join(list(scope[:depth]) + [tok]) in aliases:
            return True
    return False


def code_view(root: Path) -> Path:
    """Materialise the comment-free overlay the AK7 gates read."""
    out = REPO / ".lake" / "build" / "leancodeview"
    subprocess.run(
        [sys.executable, str(REPO / "scripts" / "lean_code_view.py"), "--overlay", str(out)],
        check=True, capture_output=True,
    )
    return out


# A signature ends at the first top-level `:=`, `where`, or **equation clause**.
# `where` must be a whole word — `elsewhere` is not a terminator — and none of
# the three may sit inside a string literal, which the code view has already
# blanked by the time the census reads a file.
#
# **The third is a body, and Lean writes it with no terminator token at all.**
# `def f : A → B` followed by `| .a => …` is the direct equation syntax: there is
# no `:=` and no `where`, so a two-token terminator left `sig_open` true for the
# whole declaration and every clause was emitted as *signature* (PR #895 review
# round 7).  Measured on the tree at the time: **4778 lines** of equation-clause
# body across 263 declarations, filed as signature.
#
# What made that worse than a miscount is where the residue landed.  `sig` is
# the one region `StoreReadClassificationCensus` deliberately does not judge —
# a declaration-level verdict cannot adjudicate a hypothesis binder — so the
# regex's failure mode drained into the bucket the elaborator refuses to check.
# A skip is not neutral: it is a sink, and a sink collects exactly the defects
# the judge exists to find.  Hence the terminator below *and* the refusal in
# `classify`: a signature the parser cannot close is now a named failure rather
# than a silent SPEC filing.
#
# The clause bar is recognised structurally rather than by indentation, so both
# `inductive T | a | b` and the multi-line spelling terminate.  Lean's bar-ish
# operators are excluded by shape, not by a list: `||`, `|||`, `|>.` and `<|>`
# each either follow a `|`/`<` or precede a `|`/`>`, and a clause bar does
# neither.  Measured over the tree: 1633 depth-zero bars in signature regions
# are clause bars and the only 4 others are `||` / `|||` occurrences, all
# excluded by that shape.
SIG_END = re.compile(r":=|\bwhere\b|(?<![|<])(?=\|(?![|>]))")

# Declaration forms with **no body**, whose signature therefore ends with their
# own bracket-balanced text rather than at a terminator.  Every other form has a
# body, so a signature the parser never closes is a parser defect — see
# `classify`'s `unparsed` channel.
BODYLESS_KINDS = {"opaque", "axiom"}


def _signature_end(line: str, depth: int = 0):
    """`(the match ending a signature on this line or None, depth after)`.

    A defaulted binder (`(fallback : Nat := 0)`) is **not** a terminator: its
    `:=` is inside the binder's own parentheses.  Reading it as one closed the
    signature early, so a later hypothesis binder carrying a store read was
    emitted as body — `CODE` — and the zero floor rejected valid specification
    input (PR #895 review round 5).
    """
    return _depth_zero_scan(line, SIG_END, depth)


def _signature_head(signature: str) -> str:
    """The signature up to its terminator — what the result type is read from."""
    m, _ = _depth_zero_scan(signature, SIG_END)
    return signature[: m.start()] if m is not None else signature


def _declaration_is_valueless(lines: list[str], at: int) -> bool:
    """Does the declaration starting at `lines[at]` reach its end with no body?

    Looks ahead to the next column-zero declaration keyword and reports whether
    any line before it carries a signature terminator.  An `opaque` that reaches
    the next declaration without one is genuinely valueless and its signature is
    its whole text; one that meets a `:=` has a body, and closing early would
    file that body's reads under a head missing its result type.

    Bounded by the next declaration rather than by a line budget, so a long
    multi-line signature is read whole; a declaration at end of file ends there.
    """
    depth = 0
    offset = 0
    for line in lines[at:]:
        # The declaration boundary is tested FIRST: a later declaration's own
        # `:=` is not this one's body, and checking the terminator first made
        # every valueless `opaque` in the tree look like it had one.
        if offset and DECL.match(line):
            return True
        end, depth = _signature_end(line, depth)
        if end is not None:
            return False
        offset += 1
    return True


def classify(path: Path, aliases: frozenset = frozenset(), unparsed=None):
    """Yield (declaration, is_prop, occurrences, line, region) per read-bearing line.

    `unparsed`, when a list is supplied, collects
    `(declaration, kind, line, reason)` for every declaration whose signature
    this parser could not close.  That is a **refusal channel, not a
    diagnostic**: a signature left open swallows the declaration's whole body
    into the `sig` region, which is SPEC and which the Tier 1 elaborator
    reconciliation deliberately skips, so an unclosed signature is a silent
    route around the enforced `STORE_READ_CODE = 0`.  The caller fails the gate
    on a non-empty list, which is this project's own *a scanner's default branch
    is a decision* applied to a region boundary.

    `region` is `"sig"` for a read in the declaration's signature — a hypothesis
    binder or the result type, which is a proposition whatever the declaration
    is — and `"body"` otherwise.  The Tier 1 reconciliation needs the
    distinction: the elaborator's verdict is per *declaration*, so it cannot
    adjudicate a proposition sitting inside an executable declaration's binder.

    A read in a declaration's SIGNATURE -- anywhere before the top-level `:=`,
    which is where its hypothesis binders and its result type live -- is spec
    whatever the declaration's kind, because a binder is a proposition.  That
    is not a technicality: `mkRetypeTarget` is a smart constructor taking
    `(hTypeMeta : ∀ obj, st.objects[target]? = some obj → …)`, and reading that
    as a transition declining to use an accessor would be reading a hypothesis
    as code.  Only a read in the BODY of a declaration whose result is not a
    `Prop` is a transition reading the store raw.
    """
    lines = path.read_text().splitlines()
    decl, kind, signature, sig_open = "<file scope>", "<none>", "", False
    in_default, body_depth, sig_depth, field_col = False, 0, 0, None
    binder_depth, binder_default = 0, None
    decl_line = 0
    # The enclosing namespaces of the line being classified: what a bare alias
    # reference at this point resolves against (PR #895 review round 12).
    scope: list[str] = []

    def refuse(reason: str) -> None:
        if unparsed is not None:
            unparsed.append((decl, kind, decl_line, reason))

    for idx, (lineno, line) in enumerate(zip(range(1, len(lines) + 1), lines)):
        if not sig_open:
            opened = NAMESPACE_OPEN.match(line)
            if opened is not None:
                scope.append(opened.group(1))
                continue
            if NAMESPACE_END.match(line) is not None:
                if scope:
                    scope.pop()
                continue
        m = DECL.match(line)
        if m:
            if sig_open:
                refuse("a new declaration began while its signature was open")
            kind, decl = m.group(1), m.group(2) or "<anonymous>"
            signature, sig_open, decl_line = line, True, lineno
            in_default, body_depth, sig_depth, field_col = False, 0, 0, None
            binder_depth, binder_default = 0, None
        sig_part, body_part = line, ""
        if sig_open:
            # **Two ways a signature ends, because Lean has two.**  `:=` opens a
            # term body; `where` opens an equation body (`def f : A → B where
            # | a, b => …`), and a declaration written that way carries no `:=`
            # at all.  Treating only `:=` as the terminator left `sig_open` true
            # for the rest of the file, so every body read of such a declaration
            # was emitted as *signature* — and the signature bucket is SPEC,
            # which is diagnostic.  A raw executable read therefore passed an
            # enforced zero by being written in a legal declaration form.
            end, sig_depth = _signature_end(line, sig_depth)
            if end is not None:
                sig_part, body_part = line[:end.start()], line[end.end():]
                sig_open = False
            if m is None and line.strip():
                signature += " " + line.strip()
            if sig_open and len(signature) > 4000:
                # The runaway guard closes the signature, so what follows is
                # read as a body: an unparsable declaration fails CLOSED (its
                # reads count as code) rather than silently becoming spec.  It
                # is reported as well as closed — closing is the safe direction
                # and still means this declaration was not parsed.
                refuse("the signature exceeded 4000 characters")
                sig_open = False
            if sig_open and kind in BODYLESS_KINDS and sig_depth == 0:
                # **A declaration that MAY be valueless is not one that IS.**
                # `axiom` never carries a body, so its balanced text is its whole
                # signature.  `opaque` may: `opaque f : T := v` is legal, and so
                # is the same split across lines.  Closing the signature at the
                # first balanced line therefore cut `opaque holds` off before its
                # own `: Prop :=`, the accumulated head never saw the result
                # type, and a raw read in the body filed CODE against the
                # enforced zero — Tier 0 rejecting valid specification text
                # (PR #895 review round 11).
                #
                # The eager close was justified by a MEASUREMENT — 73 `opaque`s
                # in the tree, every one a single line — and stated as a fact
                # about the language.  A measurement of today's tree cannot say
                # what a contributor may write tomorrow, which is why the close
                # now waits for the declaration to actually end.
                if kind == "axiom" or _declaration_is_valueless(lines, idx):
                    sig_open = False
        else:
            sig_part, body_part = "", line
        head = _signature_head(signature)
        is_prop_decl = kind in PROP_KINDS or kind in FIELD_KINDS or _returns_prop(head, aliases, tuple(scope))
        # Split a structure/class body line into its field-type half and its
        # default half.  Once a default has opened it stays open for the rest of
        # the declaration: a default may span lines, there is no terminator a
        # line scanner can see, and over-approximating CODE is the direction a
        # zero floor must fail in.  Measured rather than assumed -- the tree is
        # still at `STORE_READ_CODE=0` under this reading.
        body_spec, body_code = (body_part, "") if is_prop_decl else ("", body_part)
        # A `Prop`-sorted structure has no executable content: every field is a
        # proof and so is every default, so it is spec whole and the split below
        # does not apply to it.
        if kind in FIELD_KINDS and body_part and not _returns_prop(head, aliases, tuple(scope)):
            # **A default ends where the next field begins.**  Carrying
            # `in_default` to the end of the declaration classified every later
            # field TYPE as executable, so `tag : Nat := 0` followed by a
            # proposition field made that proposition `CODE` and the zero floor
            # rejected valid specification text (PR #895 review round 5).  A
            # structure's fields share an indentation; a default's continuation
            # lines are indented further, so a body line at or left of the field
            # column is the next field.
            stripped = body_part.strip()
            if stripped:
                col = len(body_part) - len(body_part.lstrip())
                if field_col is None:
                    field_col = col
                elif col <= field_col:
                    in_default, body_depth = False, 0
            if in_default:
                body_spec, body_code = "", body_part
            else:
                cut, body_depth = _top_level_assign(body_part, body_depth)
                if cut is None:
                    body_spec, body_code = body_part, ""
                else:
                    body_spec, body_code = body_part[:cut], body_part[cut + 2:]
                    in_default = True
        # A binder's default value is executable exactly when the declaration is
        # -- a `theorem`'s defaulted binder carries a proof, a `def`'s carries a
        # term -- so the split is gated by the same `is_prop_decl` the body uses.
        sig_spec, sig_default, binder_depth, binder_default = _split_binder_defaults(
            sig_part, binder_depth, binder_default
        )
        if is_prop_decl:
            sig_spec, sig_default = sig_spec + sig_default, ""
        n_sig = len(READ.findall(sig_spec))
        n_default = len(READ.findall(sig_default))
        n_spec = len(READ.findall(body_spec))
        n_code = len(READ.findall(body_code))
        if n_sig:
            yield decl, True, n_sig, lineno, "sig"   # a binder or result type
        if n_default:
            # Its own region: unlike a hypothesis binder, a default IS something
            # a declaration-level verdict can adjudicate, so Tier 1 judges it.
            yield decl, False, n_default, lineno, "default"
        if n_spec:
            yield decl, True, n_spec, lineno, "body"
        if n_code:
            yield decl, False, n_code, lineno, "body"
    if sig_open:
        refuse("the file ended while its signature was open")


# The definitions whose body IS the raw read, which is what makes each of them
# the accessor or the store primitive rather than a caller of one.  Exempting
# them hides nothing this census exists to catch: an accessor does the variant
# discrimination once so that no call site has to, and a primitive does not
# discriminate at all -- `storeObject` and `updateObjectAt` both apply to
# whatever is stored.
#
# **Per declaration, not per file.**  An earlier cut skipped
# `SeLe4n/Model/State.lean` whole, which is a 4800-line module that is not only
# accessors, so a raw read added anywhere in it was invisible.  And it could not
# express the frozen family at all, whose accessors share `FrozenOps/Core.lean`
# with twenty-nine transitions that are not accessors.
#
# Reconciled in BOTH directions by `accessor_registry_violations`: an entry that
# no longer reads raw is a **stale exemption**, and a stale exemption reads like
# coverage.
ACCESSOR_BODIES = {
    # The live object store -- `SystemState.objects`.
    ("SeLe4n/Model/State.lean", d): "live object-store accessor"
    for d in ("getObject?", "getObjectType?", "getTcb?", "getEndpoint?",
              "getNotification?", "getCNode?", "getVSpaceRoot?", "getUntyped?",
              "getSchedContext?", "getReply?",
              "lookupObject", "lookupCNode", "lookupVSpaceRoot")
} | {
    ("SeLe4n/Model/State.lean", d): "live object-store write primitive"
    for d in ("storeObject", "storeObjectKindChecked")
} | {
    # The frozen object store -- `FrozenSystemState.objects`, which holds the
    # live `TCB` / `Reply` / `SchedContext` records verbatim.
    ("SeLe4n/Model/FrozenState.lean", "FrozenSystemState." + d):
        "frozen object-store accessor"
    for d in ("getObject?", "getTcb?", "getEndpoint?", "getNotification?",
              "getCNode?", "getVSpaceRoot?", "getSchedContext?", "getReply?")
} | {
    # The lock domain's store primitive: it reads the store generically and
    # writes it back, applying a lock-only transform to whatever is stored.
    ("SeLe4n/Kernel/Concurrency/Locks/WithLockSet.lean", "updateObjectAt"):
        "lock-domain store primitive; kind-agnostic, `f : KernelObject → KernelObject`",
}


#: The kernel-state tables this census's read patterns are ABOUT, each with the
#: head of its field type.
#:
#: **A field name is not a receiver type** (PR #895 review round 12).  The read
#: patterns key on the spelling `.objects[…]?` / `.objects.get? …`, so a
#: definition over any other type carrying an `objects` field — `cache.objects[0]?`
#: — is emitted as `STORE_READ_CODE` and refused by the enforced zero, though it
#: never touches kernel state.  Resolving the receiver's type is a question for
#: the elaborator and this gate runs in Tier 0, before any build.
#:
#: So the *ambiguity* is bounded instead of the receiver resolved: the owners are
#: derived from the Lean sources and reconciled against this list, so a third
#: type declaring an `objects` field is a **named** Tier 0 failure on the day it
#: is written — "teach the census or rename the field" — rather than a silent
#: false positive against a zero.  Two of the four live owners are function-valued
#: and cannot be indexed at all, which is why they are recorded here rather than
#: assumed away: recording them is what makes their becoming indexable visible.
#: `{structure: (field-type head, is the field INDEXABLE by these patterns)}`.
#: Derived once and pinned; `objects_owner_violations` reconciles both ways.
OBJECTS_FIELD_OWNERS = {
    # The two kernel-state tables this census is actually about.
    "SystemState": ("RHTable", True),
    "FrozenSystemState": ("FrozenMap", True),
    # Function-valued: `v.objects oid` is application, so no `[…]?` or `.get?`
    # spelling reaches them.  Registered anyway, because recording them is what
    # makes their becoming indexable visible.
    "ObservableState": ("SeLe4n.ObjId", False),
    "SharedObservableFragment": ("SeLe4n.ObjId", False),
    # A `Prop`-valued structure whose `objects` field is an equation.
    "sharedViewUnchanged": ("projectObjects", False),
    # **A live ambiguity, not a hypothetical one.**  `List` has a `GetElem?`
    # instance, so `builder.objects[0]?` in the test state builder would be
    # counted as a kernel-state read and refused by the enforced zero.  There
    # is no such read today; the entry is what makes the first one fail with
    # an explanation rather than with a bare zero-floor rejection.
    "BootstrapBuilder": ("List", True),
}

#: A `structure`/`class` header, and a field named `objects` inside one.
STRUCTURE_HEAD = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|scoped\s+|noncomputable\s+|unsafe\s+)*"
    r"(?:structure|class)\s+([A-Za-z_][A-Za-z0-9_'!?.]*)")
OBJECTS_FIELD = re.compile(r"^\s+objects\s*:\s*([A-Za-z_][A-Za-z0-9_'!?.]*)")


def objects_field_owners(view: Path) -> dict:
    """`{structure: field-type head}` for every declared field named `objects`."""
    owners: dict = {}
    for f in sorted(view.rglob("SeLe4n/**/*.lean")):
        current = None
        for line in f.read_text().splitlines():
            head = STRUCTURE_HEAD.match(line)
            if head is not None:
                current = head.group(1)
                continue
            if DECL.match(line) is not None:
                current = None
                continue
            field = OBJECTS_FIELD.match(line)
            if field is not None and current is not None:
                owners[current] = field.group(1)
    return owners


def objects_owner_violations(view: Path) -> list[str]:
    """Owners of an `objects` field that this census's patterns do not expect."""
    found = objects_field_owners(view)
    added = {k: v for k, v in found.items() if k not in OBJECTS_FIELD_OWNERS}
    changed = {k: (OBJECTS_FIELD_OWNERS[k][0], v) for k, v in found.items()
               if k in OBJECTS_FIELD_OWNERS and v != OBJECTS_FIELD_OWNERS[k][0]}
    gone = sorted(set(OBJECTS_FIELD_OWNERS) - set(found))
    out = []
    if added:
        out.append(f"{len(added)} type(s) declare an `objects` field this census does "
                   f"not know ({added}).  Its read patterns key on the FIELD NAME, so "
                   f"a read through the new type would be counted as a kernel-state "
                   f"read and refused by the enforced zero.  Register it in "
                   f"OBJECTS_FIELD_OWNERS, or rename the field.")
    if changed:
        out.append(f"{len(changed)} `objects` field(s) changed type ({changed}); a "
                   f"field that becomes indexable becomes readable by these patterns.")
    if gone:
        out.append(f"{len(gone)} registered `objects` owner(s) no longer exist ({gone}) "
                   f"-- a stale entry reads like coverage.")
    return out


def accessor_registry_violations(code: dict, exempt_hits: dict) -> list[str]:
    """Registry entries that no longer name a raw-reading executable body."""
    stale = [f"{f}|{d}" for (f, d) in ACCESSOR_BODIES if (f, d) not in exempt_hits]
    if not stale:
        return []
    return [f"{len(stale)} accessor-registry entry(ies) no longer read the store raw "
            f"({stale}) -- a stale exemption reads like coverage.  Remove the entry, or "
            f"restore the body it names."]


def census(view: Path):
    """(executable reads, specification reads, registry hits, rows, unparsed).

    The third is what the registry is reconciled against, so an entry that stops
    naming a raw read is reported rather than silently kept.  The fifth is the
    parser's own refusals — declarations whose signature it could not close —
    which the caller fails on rather than reporting, for the reason `classify`
    states: an unclosed signature files a body as specification, which is the
    direction the enforced zero cannot afford.
    """
    code, spec, exempt_hits, attribution, unparsed = {}, {}, {}, [], []
    aliases = prop_aliases(view)
    for f in sorted(view.rglob("SeLe4n/**/*.lean")):
        rel = str(f.relative_to(view))
        here = []
        for decl, is_prop, n, lineno, region in classify(f, aliases, here):
            # Emitted for every read-bearing line, exempt or not: the
            # reconciliation asks whether the CLASSIFIER agreed with the
            # elaborator, and an exempted accessor is classified like any other.
            attribution.append((rel, lineno, decl, is_prop, region))
            if not is_prop and (rel, decl) in ACCESSOR_BODIES:
                exempt_hits[(rel, decl)] = exempt_hits.get((rel, decl), 0) + n
                continue
            bucket = spec if is_prop else code
            bucket[(rel, decl)] = bucket.get((rel, decl), 0) + n
        unparsed.extend((rel, d, k, ln, why) for d, k, ln, why in here)
    return code, spec, exempt_hits, attribution, unparsed


# ---------------------------------------------------------------------------
# Self-test.
#
# Every case is TOKEN-PRESERVING where it can be: the fixture keeps the reads it
# had and changes the *relation* the census asserts -- which population a read
# belongs to, or which declaration owns it.  A deleting case proves nothing
# about a census, because any count survives a deletion.
# ---------------------------------------------------------------------------
FIXTURES = {
    # A transition: a term-position read in a non-Prop `def`.
    "code_read": ("""
def step (st : SystemState) (tid : ThreadId) : SystemState :=
  match st.objects[tid.toObjId]? with
  | some (.tcb t) => st
  | _ => st
""", {("f.lean", "step"): 1}, {}),
    # The same text as a proposition: `def` returning `Prop`.
    "prop_def": ("""
def holds (st : SystemState) (tid : ThreadId) : Prop :=
  ∃ t, st.objects[tid.toObjId]? = some (.tcb t)
""", {}, {("f.lean", "holds"): 1}),
    # A theorem: spec whatever its signature says.
    "theorem_read": ("""
theorem frame (st : SystemState) : st.objects[oid]? = st.objects[oid]? := rfl
""", {}, {("f.lean", "frame"): 2}),
    # A `Prop`-valued structure's fields are spec.
    "structure_read": ("""
structure Framed (st st' : SystemState) : Prop where
  agree : ∀ oid, st'.objects[oid]? = st.objects[oid]?
""", {}, {("f.lean", "Framed"): 2}),
    # ...and a DATA-bearing structure's field DEFAULT is executable: the
    # elaborator compiles it and the runtime evaluates it, so a raw read there
    # is a transition reading the store.  Token-preserving against
    # `structure_read` above: same keyword, same read, moved from a field's
    # TYPE to a field's DEFAULT.
    "structure_default_is_code": ("""
structure Cache (st : SystemState) (oid : ObjId) where
  cached : Option KernelObject := st.objects[oid]?
""", {("f.lean", "Cache"): 1}, {}),
    # ...while a field's TYPE in the same data-bearing structure stays spec, so
    # the split is at the `:=` rather than at the keyword.
    "structure_field_type_is_spec": ("""
structure Witness (st : SystemState) (oid : ObjId) where
  present : st.objects[oid]? = none
  tag : Nat := 0
""", {}, {("f.lean", "Witness"): 1}),
    # A NESTED construct is not a sibling: the `:=` of a record literal inside a
    # field's TYPE sits at brace depth one, and the brace may have been opened on
    # an earlier line.  A per-line depth reset reads the continuation as a
    # default opening and files everything after it as code.
    "structure_multiline_literal": ("""
structure Bundle (st : SystemState) (oid : ObjId) : Prop where
  shape : deliver
      { registers := #[],
        caps := #[] } st = st
  read : st.objects[oid]? = none
""", {}, {("f.lean", "Bundle"): 1}),
    # THE ASCII ARROW.  Lean accepts `->` for `→` and this tree uses both, so a
    # predicate spelled the ASCII way must not read as executable -- that
    # direction fails STRICT, rejecting legitimate specification code against an
    # enforced zero.  Token-preserving against `prop_def`: same declaration, same
    # read, the arrow respelled.
    "ascii_arrow_prop": ("""
def holds : SystemState -> ObjId -> Prop := fun st oid =>
  st.objects[oid]? = none
""", {}, {("f.lean", "holds"): 1}),
    # AN INDENTED DECLARATION.  Lean allows leading whitespace before a command,
    # and an anchored pattern does not see one — so the read below stayed
    # attributed to the *theorem* above it and filed SPEC.  Token-preserving
    # against `code_read`: the same declaration, indented, after a `theorem`.
    "indented_decl_after_theorem": ("""
theorem frame (st : SystemState) : True := trivial

  def step (st : SystemState) : SystemState :=
    match st.objects[oid]? with
    | _ => st
""", {("f.lean", "step"): 1}, {}),
    # A DEFAULTED BINDER is not a signature terminator: its `:=` is inside the
    # binder's own parentheses.  Reading it as one closed the signature early and
    # filed the later hypothesis binder's read as executable.
    "defaulted_binder_is_not_a_terminator": ("""
def mk (fallback : Nat := 0) (st : SystemState)
    (hMeta : ∀ obj, st.objects[target]? = some obj → True) : Token :=
  Token.mk
""", {}, {("f.lean", "mk"): 1}),
    # A DEFAULT ENDS WHERE THE NEXT FIELD BEGINS.  Carrying the default state to
    # the end of the declaration made every later field TYPE executable.
    # Token-preserving against `structure_field_type_is_spec`: the same two
    # fields, with the defaulted one written first.
    "structure_default_then_field_type": ("""
structure W (st : SystemState) (oid : ObjId) where
  tag : Nat := 0
  present : st.objects[oid]? = none
""", {}, {("f.lean", "W"): 1}),
    # Two reads on ONE line count twice: the census counts occurrences.
    "two_per_line": ("""
def both (st st' : SystemState) : Bool :=
  st.objects[a]? == st'.objects[a]?
""", {("f.lean", "both"): 2}, {}),
    # MOVED: the same read, relocated to another declaration in the same file.
    # A per-file count cannot see this; a per-declaration key must.
    "moved": ("""
def first (st : SystemState) : SystemState := st

def second (st : SystemState) : SystemState :=
  match st.objects[oid]? with
  | _ => st
""", {("f.lean", "second"): 1}, {}),
    # A hypothesis BINDER of a non-Prop `def` is a proposition, not a
    # transition reading the store: `mkRetypeTarget` is the real instance.
    "binder_is_spec": ("""
def mk (st : SystemState) (target : ObjId)
    (hMeta : ∀ obj, st.objects[target]? = some obj → True) : Token :=
  Token.mk
""", {}, {("f.lean", "mk"): 1}),
    # ...and a read in that same declaration's BODY still counts as code.
    "binder_and_body": ("""
def both (st : SystemState) (target : ObjId)
    (hMeta : ∀ obj, st.objects[target]? = some obj → True) : SystemState :=
  match st.objects[target]? with
  | _ => st
""", {("f.lean", "both"): 1}, {("f.lean", "both"): 1}),
    # THE SPELLING CASE.  `s.objects[k]?` and `s.objects.get? k` are one read --
    # `objects_getElem?_eq_get?` proves it by `rfl` -- so a census that counts
    # the bracket alone is satisfied by a rename.  This case keeps the read and
    # changes only how it is written, which is the mutation that finds the class.
    "method_form_read": ("""
def step (st : SystemState) (tid : ThreadId) : SystemState :=
  match st.objects.get? tid.toObjId with
  | some (.tcb t) => st
  | _ => st
""", {("f.lean", "step"): 1}, {}),
    # ...and the two spellings in one declaration count twice, not once: the
    # census counts reads, and a rename of either must not move the total.
    "both_spellings": ("""
def both (st st' : SystemState) : Bool :=
  st.objects[a]? == st'.objects.get? a
""", {("f.lean", "both"): 2}, {}),
    # The frozen table is the same question: the records it holds are the live
    # `TCB` / `Reply` / `SchedContext`, so a frozen transition discriminating a
    # variant at the call site is the defect this census is named for.
    "frozen_method_form_read": ("""
def frozenStep (st : FrozenSystemState) (tid : ThreadId) : FrozenSystemState :=
  match st.objects.get? tid.toObjId with
  | some (.tcb t) => st
  | _ => st
""", {("f.lean", "frozenStep"): 1}, {}),
    # A `where` EQUATION body is a body: the declaration carries no `:=` at all,
    # and reading only `:=` as the terminator put every read of it in the
    # signature bucket -- which is SPEC, which is diagnostic, so a raw
    # executable read passed the enforced zero by being legally spelled.
    # DECISIVE for the binder-vs-result distinction (PR #895 review round 3).
    # A `Prop` in a PARAMETER used to make the whole declaration read as
    # Prop-valued, so this executable body's raw read was filed SPEC and walked
    # around the enforced zero.  The mutation keeps every token and moves the
    # `Prop` from the result to a binder, which is exactly what the superseded
    # regex could not see.
    "prop_binder_is_not_a_prop_result": ("""
def step (proof : Prop) (st : SystemState) (oid : ObjId) : SystemState :=
  match st.objects[oid]? with
  | some _ => st
  | none => st
""", {("f.lean", "step"): 1}, {}),
    # ...and the genuinely Prop-valued shape is still SPEC, so the fix did not
    # simply reclassify everything as code.
    "prop_result_is_still_spec": ("""
def holds (st : SystemState) (oid : ObjId) : Prop :=
  match st.objects[oid]? with
  | some _ => True
  | none => False
""", {}, {("f.lean", "holds"): 1}),
    "where_equation_body": ("""
def step : SystemState -> ObjId -> SystemState where
  | st, oid => match st.objects[oid]? with
    | some _ => st
    | none => st
""", {("f.lean", "step"): 1}, {}),
    # ...and a `where` in a declaration that DOES have a `:=` body still ends
    # the signature, so its auxiliary definitions read as body, not signature.
    "where_after_term_body": ("""
def step (st : SystemState) (oid : ObjId) : SystemState :=
  go st
where
  go (s : SystemState) : SystemState :=
    match s.objects[oid]? with
    | _ => s
""", {("f.lean", "step"): 1}, {}),
    # The QUALIFIED call: `RHTable.get? st.objects k` is the same read again,
    # with the namespace written out.  A third spelling in two review rounds --
    # which is the evidence that this recogniser is a floor, not a proof.
    "qualified_call_read": ("""
def step (st : SystemState) (oid : ObjId) : SystemState :=
  match RHTable.get? st.objects oid with
  | some _ => st
  | none => st
""", {("f.lean", "step"): 1}, {}),
    # A comment quoting the pattern is not a read.
    "comment_only": ("""
/-- Opens by matching `st.objects[oid]?`. -/
def documented (st : SystemState) : SystemState := st
""", {}, {}),
    # AN UNRECOGNISED DECLARATION KEYWORD IS A MISATTRIBUTION.  `opaque` was
    # absent from `DECL`, so this body stayed attributed to the `theorem` above
    # it and its read was emitted as SPEC -- past the enforced zero.  The
    # mutation is token-preserving in the sharpest sense available: the same
    # read, the same file, only the keyword introducing its declaration.
    "opaque_after_theorem": ("""
theorem pre (st : SystemState) : True := by trivial

opaque step (st : SystemState) (oid : ObjId) : Option KernelObject :=
  st.objects[oid]?
""", {("f.lean", "step"): 1}, {}),
    # A BINDER'S DEFAULT IS A TERM.  It is elaborated and evaluated whenever the
    # argument is omitted, so a read there is executable -- while the binder
    # TYPE beside it is a hypothesis.  Emitting the whole signature as one
    # bucket let this read bypass the zero (PR #895 review round 6).
    "binder_default_is_code": ("""
def step (st : SystemState) (obj : Option KernelObject := st.objects[oid]?) :=
  obj
""", {("f.lean", "step"): 1}, {}),
    # ...and the same defaulted binder on a `theorem` carries a PROOF, so it
    # stays spec.  Token-preserving against the case above: same binder, same
    # read, only the declaration's kind.
    "binder_default_in_theorem_is_spec": ("""
theorem keep (h : Option KernelObject := st.objects[oid]?) : True := by trivial
""", {}, {("f.lean", "keep"): 1}),
    # **An alias is resolved against the use site's namespaces** (PR #895
    # review round 12).  `Beta.Pred` IS `Prop`; `Alpha.Pred` is `Nat`, and a
    # bare-last-component test read the second as the first, so an executable
    # declaration filed SPEC and its raw reads walked around the enforced zero.
    "alias_is_resolved_by_namespace": ("""
namespace Beta
abbrev Pred := Prop
end Beta

namespace Alpha
def Pred := Nat

def usesLocalAlias (st : SystemState) (oid : ObjId)
    (k : Nat := (st.objects[oid]?).isSome.toNat) : Pred :=
  0
end Alpha
""", {("f.lean", "usesLocalAlias"): 1}, {}),
    # ...and the control that keeps the fix from being "aliases never resolve":
    # the SAME file, the same alias set, a declaration returning the qualified
    # `Beta.Pred`, which really is `Prop`.
    "qualified_alias_still_resolves": ("""
namespace Beta
abbrev Pred := Prop
end Beta

def usesRealAlias (st : SystemState) (oid : ObjId) : Beta.Pred :=
  st.objects[oid]? = none
""", {}, {("f.lean", "usesRealAlias"): 1}),
    # ...and the third case, which stops the fix from degrading into "a bare
    # alias never resolves" -- that would refuse valid SPECIFICATION text,
    # which round 6 recorded as a defect in its own right.  A bare `Pred`
    # written inside the namespace that declares it IS `Prop`.
    "bare_alias_resolves_in_its_own_namespace": ("""
namespace Beta
abbrev Pred := Prop

def usesBareInOwnNamespace (st : SystemState) (oid : ObjId) : Pred :=
  st.objects[oid]? = none
end Beta
""", {}, {("f.lean", "usesBareInOwnNamespace"): 1}),
    # **A `let` inside a binder TYPE owns its own `:=`** (PR #895 review
    # round 12).  Lean accepts this, and reading that `:=` as a default's start
    # filed a type-level read as CODE -- refusing a valid declaration against
    # the enforced zero, which the declaration-level Tier 1 reconciliation
    # cannot correct because it does not adjudicate a binder.
    "nested_let_in_binder_type_is_spec": ("""
def step (st : SystemState) (h : (let obj := st.objects[oid]?; obj = none)) : Nat :=
  0
""", {}, {("f.lean", "step"): 1}),
    # ...and the decisive control: the SAME declaration with a real default
    # stays CODE, so the fix above narrows the rule rather than disabling it.
    "binder_default_beside_a_let_is_code": ("""
def step (st : SystemState) (h : (let a := 1; a = 1))
    (obj : Option KernelObject := st.objects[oid]?) : Nat :=
  0
""", {("f.lean", "step"): 1}, {}),
    # ...and the case the control above structurally cannot reach (PR #895
    # review round 13): the `let` sits in the type of the **same** binder that
    # carries the default, so scanning the enclosing group's whole span finds a
    # keyword belonging to a group that has already closed.  Filed `SPEC
    # region=sig`, which the Tier 1 reconciliation skips -- so an executable
    # read bypassed BOTH tiers, not one.  The row above has the `let` in a
    # PREVIOUS binder, where a span-wide search already stopped at the group
    # opener; only this shape discriminates.
    "let_inside_the_same_binders_type_is_code": ("""
def step (st : SystemState)
    (obj : (let T := Option KernelObject; T) := st.objects[oid]?) : Nat :=
  0
""", {("f.lean", "step"): 1}, {}),
    # ...while a hypothesis binder's TYPE is spec in an executable declaration
    # too, which is the distinction the region split exists to preserve.
    "binder_type_stays_spec": ("""
def keep (h : st.objects[oid]? = none) (n : Nat := 0) : Nat :=
  n
""", {}, {("f.lean", "keep"): 1}),
    # A RESULT TYPE MAY BE AN ALIAS OF `Prop`.  Testing for the literal token
    # filed this predicate as executable, so Tier 0 rejected legitimate
    # specification text against an enforced zero.  The fixture declares the
    # alias in its own file, so what this pins is the RESOLUTION as well as the
    # classification.
    "prop_alias_result": ("""
abbrev Pred := Prop

def holds (st : SystemState) (oid : ObjId) : Pred :=
  st.objects[oid]? = none
""", {}, {("f.lean", "holds"): 1}),
    # **An equation body is a body.**  Lean's direct equation syntax carries no
    # `:=` and no `where`, so a two-token terminator never closed the signature
    # and every clause was emitted as *signature* -- SPEC, and in the one region
    # the Tier 1 reconciliation skips, so the read passed the enforced zero
    # twice over (PR #895 review round 7).  Token-preserving against
    # `code_read`: the same declaration, the same read, written in the form
    # Lean also accepts.
    "equation_body_code": ("""
def lookup : SystemState → ObjId → Option KernelObject
  | st, oid => st.objects[oid]?
""", {("f.lean", "lookup"): 1}, {}),
    # ...and the same form returning `Prop` is still specification, so the
    # terminator did not start over-filing legitimate invariant text.  The two
    # differ only in the result type.
    "equation_body_prop": ("""
def holdsAt : SystemState → ObjId → Prop
  | st, oid => st.objects[oid]? = none
""", {}, {("f.lean", "holdsAt"): 1}),
    # An `inductive` written with direct constructor clauses: its constructor
    # arguments are propositions, exactly as the `where` spelling's are.
    "inductive_equation_clauses": ("""
inductive ReadShape (st : SystemState) (oid : ObjId) : Type
  | absent (h : st.objects[oid]? = none)
  | present (obj : KernelObject) (h : st.objects[oid]? = some obj)
""", {}, {("f.lean", "ReadShape"): 2}),
    # **A bar-ish operator is not a clause.**  `|||` sits at bracket depth zero
    # in a result type, so a terminator written as a bare `|` cuts the signature
    # there and files the hypothesis binder that follows as an executable body.
    # Token-preserving: the read never moves, only which construct the parser
    # thinks precedes it.
    "or_operator_is_not_a_clause": ("""
def orGuard (a b : Nat) :
    a ||| b < 16 → st.objects[oid]? = none → Nat := fun _ _ => 0
""", {}, {("f.lean", "orGuard"): 1}),
    # A declaration form the parser cannot close is REFUSED, not filed.  A
    # field-less `structure` reaches no terminator, so without the refusal
    # everything after it up to the next declaration is read as its signature --
    # SPEC, unjudged.  The `def` below is classified normally, which is what
    # shows the refusal is about the boundary rather than the census failing.
    "unterminated_is_refused": ("""
structure Marker

def step (st : SystemState) (oid : ObjId) : SystemState :=
  match st.objects[oid]? with
  | some _ => st
  | none => st
""", {("f.lean", "step"): 1}, {}),
    # ...and a form that legitimately has no body is NOT refused.  `opaque` and
    # `axiom` end with their own bracket-balanced text; refusing them would make
    # the gate fire on 73 correct declarations.
    "bodyless_opaque_is_not_refused": ("""
opaque ffiReadObject : UInt64 → BaseIO UInt32

def step (st : SystemState) (oid : ObjId) : Option KernelObject :=
  st.objects[oid]?
""", {("f.lean", "step"): 1}, {}),
    # **...and an `opaque` that DOES have a body keeps its signature open until
    # it** (PR #895 review round 11).  Closing at the first balanced line cut
    # `opaque holds` off before its own `: Prop :=`, so the head never saw the
    # result type and the body's read filed CODE against the enforced zero —
    # Tier 0 rejecting valid specification text.  Token-preserving against the
    # case above: the keyword, the name and the type all survive; only the body
    # is added.
    "multiline_opaque_with_a_body_is_spec": ("""
opaque holds
    : Prop :=
  (st.objects[oid]?).isSome
""", {}, {("f.lean", "holds"): 1}),
    # The same declaration written as a `def` must classify identically — the
    # two differ in a keyword, not in whether their body is a proposition.
    "multiline_def_with_a_body_is_spec": ("""
def holds
    : Prop :=
  (st.objects[oid]?).isSome
""", {}, {("f.lean", "holds"): 1}),
}

#: Cases whose fixture the parser must REFUSE, and how many declarations it must
#: name.  Every other case asserts **zero**, which is the other direction of the
#: same reconciliation: a terminator that starts rejecting valid Lean fails the
#: twenty-nine cases that do not appear here.
EXPECT_REFUSALS = {"unterminated_is_refused": 1}


def self_test() -> int:
    failed = 0
    with tempfile.TemporaryDirectory() as td:
        for name, (src, want_code, want_spec) in FIXTURES.items():
            root = Path(td) / name / "SeLe4n"
            root.mkdir(parents=True)
            # Through the same stripper the census reads its files over, so a
            # comment quoting the pattern cannot become a read -- the wiring is
            # part of what this pins, not only the classification.
            (root / "f.lean").write_text(lean_code_view.strip(src))
            # Aliases are resolved from the fixture's own tree, so a case may
            # declare `abbrev Pred := Prop` and have it apply — what this pins
            # is the RESOLUTION as well as the classification.
            aliases = prop_aliases(Path(td) / name)
            got_code, got_spec, refused = {}, {}, []
            for decl, is_prop, n, _line, _region in classify(root / "f.lean", aliases, refused):
                key = ("f.lean", decl)
                (got_spec if is_prop else got_code)[key] = \
                    (got_spec if is_prop else got_code).get(key, 0) + n
            want_refusals = EXPECT_REFUSALS.get(name, 0)
            if (got_code != want_code or got_spec != want_spec
                    or len(refused) != want_refusals):
                print(f"  FAIL {name}")
                print(f"    code:     got {got_code} want {want_code}")
                print(f"    spec:     got {got_spec} want {want_spec}")
                print(f"    refusals: got {len(refused)} want {want_refusals} {refused}")
                failed += 1
            else:
                print(f"  ok   {name}")
    # **The DOMAIN, on a synthetic tree.**  `objects_field_owners` reads the
    # real repository, so nothing in FIXTURES can reach it -- and the property
    # it pins is precisely that this census's read patterns key on a field NAME
    # whose owning types it must therefore know.  A fix whose revert breaks
    # nothing is indistinguishable from no fix.
    with tempfile.TemporaryDirectory() as td:
        root = Path(td) / "SeLe4n"
        root.mkdir(parents=True)
        (root / "s.lean").write_text(
            "structure SystemState where\n  objects : RHTable K V\n\n"
            "structure FrozenSystemState where\n  objects : FrozenMap K V\n")
        for case, extra, expect in [
            ("a new owner is reported", "", False),
            ("an UNREGISTERED owner fails",
             "structure Cache where\n  objects : List Entry\n", True),
            ("a registered owner whose type CHANGED fails",
             "", True),
        ]:
            (root / "extra.lean").write_text(extra)
            if case.startswith("a registered owner whose type"):
                (root / "s.lean").write_text(
                    "structure SystemState where\n  objects : List V\n\n"
                    "structure FrozenSystemState where\n  objects : FrozenMap K V\n")
            known = dict(OBJECTS_FIELD_OWNERS)
            try:
                globals()["OBJECTS_FIELD_OWNERS"] = {
                    "SystemState": ("RHTable", True),
                    "FrozenSystemState": ("FrozenMap", True),
                }
                drifted = bool(objects_owner_violations(Path(td)))
            finally:
                globals()["OBJECTS_FIELD_OWNERS"] = known
            if drifted != expect:
                print(f"  SELF-TEST FAIL: owner-domain '{case}': "
                      f"reported {drifted}, want {expect}")
                failed += 1
            else:
                print(f"  ok   owner-domain '{case}'")
    # ...and the live registry must agree with the live tree, in both
    # directions, so a stale entry cannot read like coverage.
    live = objects_owner_violations(REPO)
    if live:
        for line in live:
            print(f"  SELF-TEST FAIL: {line}")
        failed += len(live)
    else:
        print("  ok   owner-domain 'the live registry reconciles both ways'")
    if failed:
        print(f"[store-read-census] self-test: {failed} case(s) failed")
        return 1
    print(f"[store-read-census] self-test passed ({len(FIXTURES)} cases)")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--rows", action="store_true")
    ap.add_argument("--totals", action="store_true")
    # The per-line attribution the Tier 1 reconciliation consumes.  It is the
    # classifier's OWN answer to the two structural questions — which
    # declaration owns this line, and is that declaration executable — stated
    # per line so `SeLe4n/Testing/StoreReadClassificationCensus.lean` can put
    # both to the elaborator, which cannot miss a Lean spelling.
    ap.add_argument("--attribution", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    view = code_view(REPO)
    # Checked in EVERY mode, beside the registry, for the same reason: these
    # patterns key on a FIELD NAME, so the set of types carrying that name is
    # the domain they are silently assuming.  A new one is a named failure
    # here rather than a mystery rejection at the zero floor later.
    drifted = objects_owner_violations(view)
    if drifted:
        for line in drifted:
            print(f"FAIL: {line}")
        return 1
    code, spec, exempt_hits, attribution, unparsed = census(view)
    # Refused in EVERY mode, for the same reason the registry is reconciled in
    # every mode: `--rows` is what Tier 0 calls, and a check only the unused
    # mode runs is a check nobody runs.
    if unparsed:
        for rel, d, k, ln, why in unparsed:
            print(f"FAIL: {rel}:{ln}: the signature of `{k} {d}` was never closed "
                  f"({why}).  Its body is being filed as SPECIFICATION, which the "
                  f"elaborator reconciliation does not judge, so an executable "
                  f"store read there would pass the enforced zero.  Teach "
                  f"`SIG_END` this declaration form, or add its kind to "
                  f"`BODYLESS_KINDS` if it has no body.", file=sys.stderr)
        return 1
    # Reconciled in EVERY mode, `--rows` included: that is the mode the Tier 0
    # baseline calls, so skipping it there would leave the registry checkable
    # only by a command nothing runs — a gate with a silent default branch,
    # which is the shape this project keeps paying for.
    stale = accessor_registry_violations(code, exempt_hits)
    if stale:
        for problem in stale:
            print(f"FAIL: {problem}", file=sys.stderr)
        return 1
    if args.attribution:
        for rel, lineno, decl, is_prop, region in attribution:
            print(f"STORE_READ_ATTRIB={rel}|{lineno}|{decl}|{1 if is_prop else 0}|{region}")
        return 0
    if args.rows:
        for (f, d), n in sorted(code.items()):
            print(f"STORE_READ_CODE_SITE={f}|{d}|{n}")
        for (f, d), n in sorted(spec.items()):
            print(f"STORE_READ_SPEC_SITE={f}|{d}|{n}")
    if args.totals or not args.rows:
        print(f"STORE_READ_CODE={sum(code.values())}")
        print(f"STORE_READ_SPEC={sum(spec.values())}")
        # The claim, beside the number.  A bare `0` reads as "there are none";
        # what this gate can say is "none in the spellings it recognises", and
        # saying so is what makes the next widening an improvement rather than
        # a defect report.
        print("STORE_READ_SCOPE=recognised spellings only "
              "(subscript, method, qualified call); a floor, not a proof of absence")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
