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
        elif default_depth is None and depth > 0 and text.startswith(":=", i):
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
        for line in f.read_text().splitlines():
            m = PROP_ALIAS.match(line)
            if m:
                direct[m.group(1)] = m.group(2)
    names = set()
    for name in direct:
        seen, cur = set(), name
        while cur in direct and cur not in seen:
            seen.add(cur)
            cur = direct[cur]
        if cur == "Prop":
            names.update(seen)
    return frozenset(names)


def _returns_prop(head: str, aliases: frozenset = frozenset()) -> bool:
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
    # Both spellings, since an alias declared inside a `namespace` is written
    # qualified at a use site outside it.  A bare last component is accepted on
    # purpose: the alternative is resolving Lean names by text, which this file
    # does not do -- and the direction of any over-match is SPEC, which the
    # elaborator reconciliation judges.
    return tok in aliases or tok.split(".")[-1] in aliases


def code_view(root: Path) -> Path:
    """Materialise the comment-free overlay the AK7 gates read."""
    out = REPO / ".lake" / "build" / "leancodeview"
    subprocess.run(
        [sys.executable, str(REPO / "scripts" / "lean_code_view.py"), "--overlay", str(out)],
        check=True, capture_output=True,
    )
    return out


# A signature ends at the first top-level `:=` or `where`.  `where` must be a
# whole word — `elsewhere` is not a terminator — and neither may sit inside a
# string literal, which the code view has already blanked by the time the census
# reads a file.
SIG_END = re.compile(r":=|\bwhere\b")


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


def classify(path: Path, aliases: frozenset = frozenset()):
    """Yield (declaration, is_prop, occurrences, line, region) per read-bearing line.

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
    for lineno, line in enumerate(lines, start=1):
        m = DECL.match(line)
        if m:
            kind, decl = m.group(1), m.group(2) or "<anonymous>"
            signature, sig_open = line, True
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
            if len(signature) > 4000:
                # The runaway guard closes the signature, so what follows is
                # read as a body: an unparsable declaration fails CLOSED (its
                # reads count as code) rather than silently becoming spec.
                sig_open = False
        else:
            sig_part, body_part = "", line
        head = _signature_head(signature)
        is_prop_decl = kind in PROP_KINDS or kind in FIELD_KINDS or _returns_prop(head, aliases)
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
        if kind in FIELD_KINDS and body_part and not _returns_prop(head, aliases):
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


def accessor_registry_violations(code: dict, exempt_hits: dict) -> list[str]:
    """Registry entries that no longer name a raw-reading executable body."""
    stale = [f"{f}|{d}" for (f, d) in ACCESSOR_BODIES if (f, d) not in exempt_hits]
    if not stale:
        return []
    return [f"{len(stale)} accessor-registry entry(ies) no longer read the store raw "
            f"({stale}) -- a stale exemption reads like coverage.  Remove the entry, or "
            f"restore the body it names."]


def census(view: Path):
    """(executable reads, specification reads, registry hits, attribution rows).

    The third is what the registry is reconciled against, so an entry that stops
    naming a raw read is reported rather than silently kept.
    """
    code, spec, exempt_hits, attribution = {}, {}, {}, []
    aliases = prop_aliases(view)
    for f in sorted(view.rglob("SeLe4n/**/*.lean")):
        rel = str(f.relative_to(view))
        for decl, is_prop, n, lineno, region in classify(f, aliases):
            # Emitted for every read-bearing line, exempt or not: the
            # reconciliation asks whether the CLASSIFIER agreed with the
            # elaborator, and an exempted accessor is classified like any other.
            attribution.append((rel, lineno, decl, is_prop, region))
            if not is_prop and (rel, decl) in ACCESSOR_BODIES:
                exempt_hits[(rel, decl)] = exempt_hits.get((rel, decl), 0) + n
                continue
            bucket = spec if is_prop else code
            bucket[(rel, decl)] = bucket.get((rel, decl), 0) + n
    return code, spec, exempt_hits, attribution


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
}


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
            got_code, got_spec = {}, {}
            for decl, is_prop, n, _line, _region in classify(root / "f.lean", aliases):
                key = ("f.lean", decl)
                (got_spec if is_prop else got_code)[key] = \
                    (got_spec if is_prop else got_code).get(key, 0) + n
            if got_code != want_code or got_spec != want_spec:
                print(f"  FAIL {name}")
                print(f"    code: got {got_code} want {want_code}")
                print(f"    spec: got {got_spec} want {want_spec}")
                failed += 1
            else:
                print(f"  ok   {name}")
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
    code, spec, exempt_hits, attribution = census(view)
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
