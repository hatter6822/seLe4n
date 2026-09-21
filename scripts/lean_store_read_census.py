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

The same classifier, run over the raw WRITE spellings (`.objects.insert` /
`.objects.erase` and the qualified table calls), emits `STORE_WRITE_CODE` /
`STORE_WRITE_SPEC` beside the read pair (`v0.35.76`): the raw-write migration
drove every executable write onto the store primitives, so `STORE_WRITE_CODE`
is enforced at zero with those primitives registered in
`WRITE_PRIMITIVE_BODIES`.

Usage:
    lean_store_read_census.py --rows            # CODE/SPEC rows for the baseline (reads and writes)
    lean_store_read_census.py --totals          # the four scalars
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
#
# **Both branches are built from one classification** (PR #897 review).  Each
# pattern below has a *method* branch and a *qualified* branch, and until this cut
# they enumerated their operations independently: `WRITE`'s qualified branch named
# `set` and its method branch did not, so `st.objects.set k v` -- the frozen
# surface's ordinary store spelling -- was invisible to an **enforced zero**, and
# 31 executable raw writes across 22 frozen declarations walked around it.  That is
# *keep the tables symmetric* (PR #895 review round 11) at the level of a regex's
# two alternations, and the remedy is round 9's: not a third telling but a
# mechanism, so the two branches read `_TABLE_OPS` and cannot name different sets.
#
# `_TABLE_OPS` is also this gate's **domain**, reconciled against the two sources
# in both directions by `table_op_violations` -- an operation on either table that
# it does not classify is a *named* Tier 0 failure rather than a silent hole, which
# is the shape `OBJECTS_FIELD_OWNERS` already has for the receiver question.
#
#   `read`   a KEYED lookup yielding one object for the call site to discriminate.
#            This is the population `STORE_READ_CODE`'s enforced zero is about.
#   `write`  a keyed mutation.  `STORE_WRITE_CODE`'s population.
#   `sweep`  a whole-table traversal.  Its call sites *do* discriminate objects,
#            but a sweep over a heterogeneous table has no typed-accessor form --
#            it is not a lookup -- so it is **reported and not enforced**, the
#            treatment `STORE_READ_SPEC` already has.  Measured rather than
#            assumed empty: 15 executable sites today.
#   `other`  yields no object at all (a projection, a predicate, a constructor).
_TABLE_OPS = {
    "get?": "read",
    "insert": "write",
    "insertNoResize": "write",
    "erase": "write",
    "set": "write",
    "fold": "sweep",
    "toList": "sweep",
    "filter": "sweep",
    "contains": "other",
    "empty": "other",
    "ofList": "other",
    "resize": "other",
    "invExtK": "other",
    "wellFormed": "other",
    "size": "other",
    # `RHTable`'s remaining structure fields.  Projections, so they yield no
    # object; classified because the reconciliation's domain includes fields --
    # `size` is a field on one table and a `def` on the other, which is exactly
    # the asymmetry a field-blind derivation would hide.
    "slots": "other",
    "capacity": "other",
    "hCapGe4": "other",
    "hSlotsLen": "other",
    # ...and `FrozenMap`'s.
    "data": "other",
    "indexMap": "other",
}


def _op_alternation(kinds: tuple[str, ...]) -> str:
    """The alternation of every `_TABLE_OPS` entry of one of `kinds`.

    A trailing `\b` only where the operation ends in a word character: `get?`
    ends in `?`, and a word boundary after it would never match.
    """
    ops = sorted(o for o, k in _TABLE_OPS.items() if k in kinds)
    parts = [re.escape(o) + (r"\b" if o[-1].isalnum() or o[-1] == "_" else "")
             for o in ops]
    return "(?:" + "|".join(parts) + ")"


#: **A receiver may be parenthesised, and every pattern here keys on its TEXT.**
#:
#: Lean permits redundant parentheses around any expression, so `(st.objects)[k]?`
#: *is* `st.objects[k]?` and `(objs).insert k v` *is* `objs.insert k v` -- the same
#: access, on the same table, with a bracket run in between.  Every receiver
#: position below therefore composes these two, and they are ONE definition for the
#: reason `_TABLE_TYPE` is: seven positions ask this question, a widening applied at
#: whichever branch a review points at leaves the other six open, and that is this
#: project's own *a fix applied at one site and not its sibling*.
#:
#: Measured before choosing (`v0.35.151`): the tree already spells four keyed reads
#: `({ st with objects := ... }.objects)[tid.toObjId]?`, which `READ` could not see.
#: They sit in a `theorem`, so `STORE_READ_CODE`'s enforced zero was untouched -- by
#: accident, not by construction: the same expression in a `def` body walks around
#: it, which is `v0.35.12`'s *a spelling is not a read* and `v0.35.97`'s *a spelling
#: is not a write* at the one position neither of those cuts swept.
#:
#: `_RECV_CLOSE` admits whitespace only INSIDE the group (`( x )`), never between
#: the last `)` and the accessor -- which is exact rather than conservative, because
#: Lean's own lexer requires it: `x[i]` is a subscript and `x [i]` is an application
#: to a list, and `x.f` is a projection while `x .f` is an application to an
#: anonymous constructor.  So `f (st.objects) [a, b]` is correctly NOT a read.
#:
#: Where it over-approximates it does so in the direction a floor must fail in, and
#: the same direction `table_receivers` already documents: `(f st.objects).erase k`
#: has `f`'s result as its receiver, not the table, and is counted -- a *named* Tier
#: 0 failure a maintainer can see, never a silent miss.  Zero such sites today.
_RECV_OPEN = r"(?:\(\s*)*"
_RECV_CLOSE = r"(?:\s*\))*"


def _table_access(kinds: tuple[str, ...], extra_method: str = "") -> str:
    """The method and qualified spellings of every operation of one of `kinds`.

    One alternation, two branches, so a widening reaches both by construction.

    Both branches compose `_RECV_OPEN` / `_RECV_CLOSE`; see them for why a
    receiver's parentheses are part of this question and not a separate one.  The
    qualified branch additionally admits a parenthesised APPLICATION as the
    projection's head (`RHTable.erase (spliceOutMidQueueNode st tid).objects k`),
    which `[\w'.]*` structurally cannot span -- a shape this tree already writes at
    five sites for theorem helpers, so a write spelled that way is one rename away.
    """
    alt = _op_alternation(kinds)
    method = rf"\.objects{_RECV_CLOSE}\.{alt}"
    if extra_method:
        method = rf"(?:{method}|{extra_method})"
    qualified = (rf"\b(?:RHTable|FrozenMap)\.{alt}\s+{_RECV_OPEN}"
                 rf"(?:\([^()\n]*\)|[\w'.]*)\.objects\b")
    return rf"{method}|{qualified}"


# `st.objects[k]?` is the subscript spelling of the keyed read and has no
# qualified counterpart, so it is the one branch that is not derived from an
# operation name.
READ = re.compile(_table_access(
    ("read",), extra_method=rf"\.objects{_RECV_CLOSE}\["))

# A raw WRITE of an object table, in either spelling (`v0.35.76`): the method
# form `st.objects.insert k v` / `st.objects.erase k` and the qualified call
# `RHTable.insert st.objects k v` / `FrozenMap.set st.objects k v`.  Both, for
# the reason `READ` gives: a census that a rename walks around asserts nothing.
# The population it measures is the one the raw-write migration
# (`v0.35.64`..`v0.35.75`) drove to the five store primitives — every other
# executable write goes through `storeObject`, `withObjectStored`,
# `rewriteObject` or a typed update over it, so the honest floor is **zero**,
# with the primitives themselves and one planted census witness registered in
# `WRITE_PRIMITIVE_BODIES` and reconciled in both directions.
WRITE = re.compile(_table_access(("write",)))

# The whole-table traversals, reported as a diagnostic beside the two enforced
# populations.  See `_TABLE_OPS` for why they are not in `READ`.
SWEEP = re.compile(_table_access(("sweep",)))

# ---------------------------------------------------------------------------
# The INDIRECT population (`v0.35.117`).
#
# Every pattern above keys on the receiver text `.objects`, so **an indirection
# defeats all of them**.  There are two spellings of that indirection and they are
# one question:
#
#   ALIAS  `let objs := st.objects` and then `objs.insert k v` -- a keyed write no
#          `WRITE` match can see, and `objs[k]?` a keyed read no `READ` match can.
#   PARAM  a declaration handed the table itself (`(objs : RHTable ObjId
#          KernelObject)`) and keying into it.
#
# Not hypothetical, and not one site.  Derived over the tree: `endpointQueueRemove`
# and `spliceOutMidQueueNode` bind the table and perform **six executable writes
# and four executable reads** between them, and `queueNeighbourPatch` takes it as a
# parameter for **one more of each** -- so `STORE_WRITE_CODE = 0` and
# `STORE_READ_CODE = 0` were *evaded* rather than satisfied, and that is why the
# raw-write migration (`v0.35.64`..`v0.35.78`) passed over all three.  `CLAUDE.md`
# already states the rule -- *a new store primitive takes the state, never the
# table* -- and nothing enforced it.
#
# **One classifier, both spellings**, because flooring one and describing the other
# in prose is this project's own *a fix applied at one site and not its sibling*:
# `table_receivers` derives the set of identifiers that denote the table, from the
# signature and from the bindings alike and closed transitively, and the access
# alternation is `_TABLE_OPS`' -- the same one `READ` and `WRITE` are built from --
# so a newly classified operation reaches the direct and indirect censuses by
# construction.  The *provenance* is reported as the shape rather than deciding
# which check runs.
#
# The population is **reported and floored per (file, declaration, shape, kind)**,
# not enforced at zero, because it is not zero.  A `ZERO_METRICS` entry this project
# may not re-anchor would have to be false on the day it landed, and a floor that
# says "these, here, and no more" is a true statement where a zero would be a false
# one.  The floor is keys AND counts, the shape `identifier_naming_baseline.json`
# has for the reason this file already records twice: a set of keys alone cannot see
# a second access inside a declaration that already has one, and a count alone
# cannot see the first in a declaration that had none.
#
# The unit is the **access**, not the binding.  A binding count cannot see a second
# `objs.insert` added to a declaration that already aliases, which is the same
# defect one level down and is exactly what the two enforced zeros count.
#
# Driving it to zero is registered (`docs/REGISTERED_DEBT.md` table C).  The writes
# are correct; what this closes is their *invisibility*.
# ---------------------------------------------------------------------------


def _indirect_access(kinds: tuple[str, ...], receiver: str,
                     extra_method: str = "") -> str:
    """`_table_access`, over a BOUND receiver rather than the `.objects` projection.

    Built from the same `_op_alternation` for the same reason `_table_access`
    gives: an operation classified once in `_TABLE_OPS` is then recognised in the
    direct spelling *and* the indirect one, so a widening cannot reach one and
    silently miss the other.

    The receiver is delimited on both sides against `[\\w'.]` rather than by `\\b`,
    so `objs` does not match inside `myobjs` and does not match the *field path*
    `st.objs`: a name is a table because of how it was bound, and a suffix of
    another path was not bound here at all.

    ...and it may be parenthesised, in all three spellings, through the same
    `_RECV_OPEN` / `_RECV_CLOSE` the direct patterns compose -- so `(objs).insert k
    v`, `(objs)[k]?` and `RHTable.insert (objs) k v` are the accesses they are.
    """
    alt = _op_alternation(kinds)
    r = re.escape(receiver)
    method = rf"(?<![\w'.]){r}{_RECV_CLOSE}\.{alt}"
    if extra_method:
        method = rf"(?:{method}|{extra_method})"
    qualified = (rf"\b(?:RHTable|FrozenMap)\.{alt}\s+{_RECV_OPEN}{r}"
                 rf"{_RECV_CLOSE}(?![\w'.])")
    return rf"{method}|{qualified}"


def indirect_patterns(receiver: str) -> dict:
    """{kind: pattern} for the keyed accesses on `receiver`.

    The subscript spelling `objs[k]?` is the indirect counterpart of `READ`'s
    `extra_method` and has no qualified form, for the same reason.
    """
    r = re.escape(receiver)
    return {
        "read": re.compile(_indirect_access(
            ("read",), receiver,
            extra_method=rf"(?<![\w'.]){r}{_RECV_CLOSE}\[")),
        "write": re.compile(_indirect_access(("write",), receiver)),
    }


#: The two object-table types, and where their operations are declared.  The
#: reconciliation below reads these files rather than a list of names, so an
#: operation added to either table is a *named* Tier 0 failure -- "classify it in
#: `_TABLE_OPS`" -- rather than a spelling the patterns silently do not see.
_TABLE_SOURCES = {
    "RHTable": ("SeLe4n/Kernel/RobinHood/Core.lean",
                "SeLe4n/Kernel/RobinHood/Bridge.lean"),
    "FrozenMap": ("SeLe4n/Model/FrozenState.lean",),
}

#: Every line-initial declaration named `RHTable.x` / `FrozenMap.x`, whatever its
#: KIND: optional attributes, then any run of visibility and definition modifiers,
#: then the keyword, then the name.  `@[inline] def FrozenMap.bar`,
#: `protected def RHTable.foo`, `theorem RHTable.insert_eq`, `opaque
#: RHTable.rawSet` -- all matched, and `_TABLE_OP_KINDS` decides which of them
#: DEFINE an operation a call site can key through.
#:
#: **Keyword-agnostic since `v0.35.119`** (PR #897 Codex review), and the reason is
#: the one this file states three ways already.  It read `(?:def|abbrev)`, so an
#: `opaque RHTable.rawSet` -- executable, since Lean requires an inhabitant and
#: `ConstantInfo.value? (allowOpaque := true)` hands the body back, and this tree's
#: FFI surface has seventy-odd of them -- was matched by nothing.
#: `table_op_violations` therefore never demanded its classification, and `READ`,
#: `WRITE` and `SWEEP` are **built from** that classification, so a keyed access
#: through the new operation was outside all three patterns and walked around an
#: enforced zero.  That is `v0.35.114`'s *a default branch over a closed set of
#: declaration kinds* arriving at a Python regex instead of a `ConstantInfo` match,
#: and it is silent by construction: the declaration is never examined, no count
#: moves, and the reconciliation goes on reporting its whole domain accounted for.
_TABLE_DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:private|protected|partial|unsafe|noncomputable|scoped|local)\s+)*"
    r"(?P<kw>[A-Za-z_][A-Za-z_0-9]*)\s+"
    r"(?P<ns>RHTable|FrozenMap)\.(?P<op>[A-Za-z0-9_?'!]+)", re.MULTILINE)

#: A declaration of one of these kinds, named for a table in the table's own
#: source, DEFINES an operation a call site can key a table access through.
#:
#: `instance` is here rather than below deliberately, and the direction is the
#: argument: this set feeds a **requirements** derivation (what `_TABLE_OPS` must
#: classify), so an entry admitted in error costs one classification and a *named*
#: failure, while one omitted in error costs the gate its silence.  A named
#: `instance RHTable.instGetElem` really can be the operation a `[k]?` resolves to.
_TABLE_OP_KINDS = frozenset({"def", "abbrev", "opaque", "instance"})

#: ...and the kinds that define something no call site can key THROUGH: a
#: proposition, or a type.  `structure RHTable.WF : Prop` is the live member; the
#: 49 `theorem RHTable.*` / `FrozenMap.*` are the bulk.
#:
#: Named rather than omitted, because **omission is what produced the defect
#: above**.  With both sets explicit, a keyword in NEITHER is a gate defect that
#: `table_op_violations` reports by name, so a Lean declaration form this scanner
#: has not seen fails Tier 0 on the day it is introduced rather than quietly
#: shrinking the domain -- *a scanner's default branch is a decision*.
_TABLE_NON_OP_KINDS = frozenset({
    "theorem", "lemma", "example", "axiom", "structure", "class", "inductive",
})

#: ...and the structure's own fields, which are operations too as far as a call
#: site is concerned: `RHTable.size` is a FIELD and `FrozenMap.size` is a `def`,
#: which is exactly the asymmetry a field-blind derivation would hide.
_TABLE_STRUCT = re.compile(
    r"^structure\s+(?P<ns>RHTable|FrozenMap)(?![.\w])[^\n]*\bwhere\s*$", re.MULTILINE)
_STRUCT_FIELD = re.compile(r"^\s{2}(?P<name>[A-Za-z0-9_?'!]+)\s*:")


def classify_table_declarations(text: str) -> tuple[set[str], set[tuple[str, str]]]:
    """One table source's operations, and the declarations it could not classify.

    Returns `(operations, unclassified)`, where `unclassified` holds
    `(keyword, name)` for a declaration whose kind is in neither
    `_TABLE_OP_KINDS` nor `_TABLE_NON_OP_KINDS`.

    Pure over the text so a witness can exercise it on a synthetic source: the
    walker below reads the real tree, and the case that matters -- a declaration
    kind this tree does not yet contain -- cannot be reached by mutating a
    classification the way `table_op_violations`' own cases do.
    """
    ops: set[str] = set()
    unclassified: set[tuple[str, str]] = set()
    for m in _TABLE_DECL.finditer(text):
        kw = m.group("kw")
        if kw in _TABLE_OP_KINDS:
            ops.add(m.group("op"))
        elif kw not in _TABLE_NON_OP_KINDS:
            unclassified.add((kw, f"{m.group('ns')}.{m.group('op')}"))
    for m in _TABLE_STRUCT.finditer(text):
        # Fields run from the `where` to the first line that is not an
        # indented `name :` binding.
        for line in text[m.end():].splitlines()[1:]:
            if not line.strip() or line.lstrip().startswith("--"):
                continue
            fm = _STRUCT_FIELD.match(line)
            if fm is None:
                break
            ops.add(fm.group("name"))
    return ops, unclassified


def _walk_table_sources() -> tuple[set[str], set[tuple[str, str, str]]]:
    """`classify_table_declarations` over every table source's CODE view.

    The **code view**, because *gates read code, prose reads prose*: a `def
    RHTable.oldOp` written at column 0 inside a docstring is not a declaration,
    and counting it would demand a `_TABLE_OPS` entry for an operation that does
    not exist.  Measured at `v0.35.119` -- no such line exists today, so the view
    costs the derivation nothing and removes a way for it to be wrong.
    """
    ops: set[str] = set()
    unclassified: set[tuple[str, str, str]] = set()
    for _ns, files in _TABLE_SOURCES.items():
        for rel in files:
            text = lean_code_view.strip((REPO / rel).read_text(encoding="utf-8"))
            found, unread = classify_table_declarations(text)
            ops |= found
            unclassified |= {(rel, kw, name) for kw, name in unread}
    return ops, unclassified


def declared_table_operations() -> set[str]:
    """Every operation of either object table, derived from the sources."""
    return _walk_table_sources()[0]


def table_op_violations() -> list[str]:
    """Where `_TABLE_OPS` and the sources disagree -- both directions.

    An *unclassified* operation is the dangerous one: the patterns are built
    from the classification, so an operation nobody classified is one neither
    pattern looks for, which is how `set` stayed out of the WRITE method branch.
    A *stale* entry is the other, and is still a failure: a classification that
    no longer describes the tree reads exactly like one that does.

    A declaration kind this scanner cannot classify is the **third** direction
    (`v0.35.119`), and it is the one the other two cannot see: an unrecognised
    keyword yields no operation, so the reconciliation finds nothing missing and
    nothing stale and reports the domain accounted for.  Refusing by name is what
    makes a new Lean declaration form a Tier 0 failure on the day it appears
    rather than a silent narrowing of what READ, WRITE and SWEEP look for.
    """
    declared, unclassified = _walk_table_sources()
    out = []
    for rel, kw, name in sorted(unclassified):
        out.append(f"{rel}: `{kw} {name}` -- this scanner cannot classify the "
                   f"declaration kind `{kw}`, so it cannot say whether `{name}` is "
                   f"an operation a call site keys a table access through; add "
                   f"`{kw}` to `_TABLE_OP_KINDS` or to `_TABLE_NON_OP_KINDS`")
    for op in sorted(declared - set(_TABLE_OPS)):
        out.append(f"`{op}` is an operation of an object table and `_TABLE_OPS` does not "
                   f"classify it -- classify it `read`, `write`, `sweep` or `other`, or "
                   f"neither pattern will ever look for it")
    for op in sorted(set(_TABLE_OPS) - declared):
        out.append(f"`{op}` is classified in `_TABLE_OPS` and is not an operation of either "
                   f"object table -- a stale entry reads exactly like a live one")
    return out


#: The spellings every classified operation must be recognised in, as
#: `(description, template)` where `{op}` is the operation name.  **Derived over,
#: not enumerated beside**: `branch_symmetry_violations` crosses this list with
#: `_TABLE_OPS`, so classifying an operation checks it in every spelling and adding
#: a spelling checks it for every operation.  A hand-written pair of `if`s is what
#: let `set` live in one branch and not the other past an enforced zero.
_OPERATION_SPELLINGS = (
    ("METHOD", "  let t := st.objects.{op} k v"),
    ("QUALIFIED", "  let t := RHTable.{op} st.objects k v"),
    # ...and the same two with the receiver parenthesised.  Lean permits it, this
    # tree already writes the parenthesised projection at five sites, and every
    # pattern here keys on the receiver's TEXT -- see `_RECV_OPEN` / `_RECV_CLOSE`.
    ("PARENTHESISED METHOD", "  let t := (st.objects).{op} k v"),
    ("PARENTHESISED QUALIFIED ARGUMENT",
     "  let t := RHTable.{op} (st.objects) k v"),
    # The projection's head may itself be a parenthesised application, which
    # `[\w'.]*` structurally cannot span.
    ("PARENTHESISED QUALIFIED HEAD",
     "  let t := RHTable.{op} (spliceOutMidQueueNode st tid).objects k v"),
)


def branch_symmetry_violations() -> list[str]:
    """Every classified operation is recognised in every spelling of its access.

    The defect this is the mechanism for: `WRITE` named `set` in its qualified
    branch and not in its method branch, so the tree's ordinary frozen store
    spelling was invisible to an enforced zero.  Asserting the symmetry directly
    is what makes a future widening reach both branches by construction --
    stating the rule a fourth time is what had already failed.

    Since `v0.35.151` the spellings are `_OPERATION_SPELLINGS` rather than two
    inline templates, for the reason the whole cut is about: the receiver may be
    parenthesised, seven positions ask that question, and a reconciliation that
    names two of them is the presence check this file spends its length retiring.

    The SUBSCRIPT read has no per-operation form -- it is notation, not a named
    operation -- so it is asserted once, in both spellings, beside the crossing.
    """
    out = []
    for op, kind in sorted(_TABLE_OPS.items()):
        pat = {"read": READ, "write": WRITE, "sweep": SWEEP}.get(kind)
        if pat is None:
            continue
        for what, template in _OPERATION_SPELLINGS:
            probe = template.format(op=op)
            if not pat.search(probe):
                out.append(f"`{op}` is classified `{kind}` and the {what} spelling "
                           f"`{probe.strip()}` is not recognised")
    for what, probe in (("SUBSCRIPT", "  have h : st.objects[k]? = none"),
                        ("PARENTHESISED SUBSCRIPT",
                         "  have h : (st.objects)[k]? = none")):
        if not READ.search(probe):
            out.append(f"the {what} read `{probe.strip()}` is not recognised")
    # ...and the one spelling that must NOT be a read, because Lean's own lexer
    # says so: `x[i]` is a subscript and `x [i]` is an application to a list.
    # Asserted here rather than left implicit, since the widening that admits
    # `(st.objects)[k]?` is one whitespace class away from admitting this.
    if READ.search("  f (st.objects) [a, b]"):
        out.append("`f (st.objects) [a, b]` is an application to a list literal, "
                   "not a subscript read, and `READ` matched it -- `_RECV_CLOSE` "
                   "must not admit whitespace after the closing parenthesis")
    return out


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
# misattribution.**  `opaque` was absent from this alternation, and the tree had
# **73** `opaque` declarations at column zero when that was measured (`v0.35.19`;
# the figure is dated because a live count in a comment drifts on contact, and
# this one had reached 76 by `v0.35.114`): each one left `sig_open`/`decl`
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


def census_view(path: Path) -> str:
    """The overlay file with string CONTENTS blanked as well.

    **The view you read depends on the question** (PR #895 review round 16).
    The shared overlay keeps string contents deliberately — a Tier 3 anchor may
    be about text an `asm!` template or a `.global` directive puts in the symbol
    table — and this census asks a different question: `READ` matches a
    *spelling of a store read*, so a diagnostic string naming that spelling,
    `def diagnostic : String := "avoid .objects[raw]? syntax"`, was counted as
    an executable raw read.  The enforced zero then refused valid code, and the
    Tier 1 reconciliation could not correct it: it sees a genuine executable
    `def` and agrees with the classifier about the declaration.  Refusing
    correct code is the fail-CLOSED direction and still a defect — round 6
    recorded that the safe direction is a direction too.

    Blanked in process rather than as a second overlay: a whole-repo mirror
    costs 324 MB and the only difference would be the text inside literals.
    Blanking is byte-aligned and idempotent over an already comment-free file,
    so every line, column and offset this file computes is unchanged.

    `_SIGNATURE_END`'s own comment already asserted that the view had blanked
    strings.  It had not; this is what makes that sentence true.
    """
    return lean_code_view.strip(path.read_text(), blank_strings=True)


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


def classify(path: Path, aliases: frozenset = frozenset(), unparsed=None,
             pattern=READ, collect=None):
    """Yield (declaration, is_prop, occurrences, line, region) per access-bearing line.

    `pattern` is the access being counted — `READ` (the default) or `WRITE`.  The
    two questions share every structural decision below (which declaration owns
    a line, whether it is executable, which region the access sits in); only the
    spelling counted differs, which is why the write census is this classifier
    with one argument rather than a second parser (`v0.35.76`).

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

    `collect`, when a callable is supplied, is invoked once per line with
    `(declaration, kind, signature_text, specification_text, executable_text)` --
    the same four region texts this classifier counts `pattern` in, with the two
    executable regions (a body that is not a proposition, and a binder default)
    joined because both are code.  It is how the INDIRECT census
    (`indirect_accesses`) reads declarations: that question needs a
    declaration's signature *and* its body at once, which no line pattern can
    express, and routing it through this classifier is what keeps the
    declaration boundary, the `Prop` verdict and the region split ONE answer
    shared by the direct and indirect censuses -- so a mutation of any of them
    fails both rather than one.

    A read in a declaration's SIGNATURE -- anywhere before the top-level `:=`,
    which is where its hypothesis binders and its result type live -- is spec
    whatever the declaration's kind, because a binder is a proposition.  That
    is not a technicality: `mkRetypeTarget` is a smart constructor taking
    `(hTypeMeta : ∀ obj, st.objects[target]? = some obj → …)`, and reading that
    as a transition declining to use an accessor would be reading a hypothesis
    as code.  Only a read in the BODY of a declaration whose result is not a
    `Prop` is a transition reading the store raw.
    """
    lines = census_view(path).splitlines()
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
        if collect is not None:
            collect(decl, kind, sig_spec, body_spec, sig_default + body_code)
        n_sig = len(pattern.findall(sig_spec))
        n_default = len(pattern.findall(sig_default))
        n_spec = len(pattern.findall(body_spec))
        n_code = len(pattern.findall(body_code))
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
              "getTcbWitnessed?", "getSchedContextWitnessed?",
              "getEndpointWitnessed?", "getNotificationWitnessed?",
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

#: The declarations that write an object table RAW by design (`v0.35.76`) —
#: the five store primitives every other executable write goes through, and
#: one planted witness.  Reconciled in both directions, exactly as
#: `ACCESSOR_BODIES` is: an entry that no longer writes raw is a stale
#: exemption, and a raw write anywhere else is a `STORE_WRITE_CODE` violation.
#:
#: `updateObjectAt` cannot be a `rewriteObject`: it is kind-agnostic and a
#: CNode or VSpace root is not rewrite-neutral, so it stays the lock domain's
#: raw read-modify-write over `storeObject`'s bookkeeping.  The planted
#: witness is the reply-stack write census's own fixture — a definition that
#: stores a chain-bearing record through the bare table so that census is
#: known to see a raw table write — and it must stay raw for exactly that
#: reason.
WRITE_PRIMITIVE_BODIES = {
    ("SeLe4n/Model/State.lean", "storeObject"):
        "the object-store write: the insert plus its bookkeeping",
    ("SeLe4n/Model/State.lean", "rewriteObject"):
        "the proof-carrying in-place rewrite: the bare insert under `rewriteAdmissible`",
    ("SeLe4n/Model/Builder.lean", "createObject"):
        "the boot-time population, capacity-bounded by `PlatformConfig`",
    ("SeLe4n/Kernel/Concurrency/Locks/WithLockSet.lean", "updateObjectAt"):
        "lock-domain read-modify-write; kind-agnostic, so not a rewrite",
    ("SeLe4n/Kernel/FrozenOps/Core.lean", "frozenWithObjectStored"):
        "the frozen surface's one store, over `FrozenMap.set`",
    ("SeLe4n/Testing/ReplyStackWriteCensus.lean", "censusWitnessRawTableWrite"):
        "the reply-stack write census's planted raw-table witness",
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


def accessor_registry_violations(code: dict, exempt_hits: dict,
                                 registry: dict = ACCESSOR_BODIES,
                                 what: str = "read") -> list[str]:
    """Registry entries that no longer name a raw-accessing executable body.

    `registry` is `ACCESSOR_BODIES` for the read census and
    `WRITE_PRIMITIVE_BODIES` for the write census; `what` names the access in
    the message.
    """
    stale = [f"{f}|{d}" for (f, d) in registry if (f, d) not in exempt_hits]
    if not stale:
        return []
    return [f"{len(stale)} {what}-registry entry(ies) no longer {what} the store raw "
            f"({stale}) -- a stale exemption reads like coverage.  Remove the entry, or "
            f"restore the body it names."]


def census(view: Path, pattern=READ, registry: dict = ACCESSOR_BODIES):
    """(executable accesses, specification accesses, registry hits, rows, unparsed).

    `pattern` / `registry` select the census: `READ` with `ACCESSOR_BODIES`
    (the default) or `WRITE` with `WRITE_PRIMITIVE_BODIES` (`v0.35.76`).

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
        for decl, is_prop, n, lineno, region in classify(f, aliases, here, pattern):
            # Emitted for every access-bearing line, exempt or not: the
            # reconciliation asks whether the CLASSIFIER agreed with the
            # elaborator, and an exempted accessor is classified like any other.
            attribution.append((rel, lineno, decl, is_prop, region))
            if not is_prop and (rel, decl) in registry:
                exempt_hits[(rel, decl)] = exempt_hits.get((rel, decl), 0) + n
                continue
            bucket = spec if is_prop else code
            bucket[(rel, decl)] = bucket.get((rel, decl), 0) + n
        unparsed.extend((rel, d, k, ln, why) for d, k, ln, why in here)
    return code, spec, exempt_hits, attribution, unparsed


# ---------------------------------------------------------------------------
# The INDIRECT census.  See the pattern builders above for why it exists and why
# both spellings of the indirection go through one classifier.
# ---------------------------------------------------------------------------

#: The object-table type, in either spelling.  ONE definition, so a bracketed
#: binder and an unbracketed ascription cannot disagree about what a table is.
_TABLE_TYPE = (r"(?:RHTable\s+(?:SeLe4n\.)?ObjId\s+KernelObject|FrozenMap)"
               r"(?![\w'.])")

#: A BRACKETED binder of object-table type: `(objs : RHTable ObjId KernelObject)`,
#: `{fm : FrozenMap}`, `⦃t : FrozenMap⦄`.  One binder may bind several names
#: (`(a b : RHTable ...)`), so the name group is split rather than captured singly.
TABLE_BINDER = re.compile(
    r"[(\{⦃]\s*(?P<names>[\w'][\w' ]*?)\s*:\s*" + _TABLE_TYPE)

#: ...and the UNBRACKETED ascription, `let objs : FrozenMap ... := ...` / `fun objs
#: : RHTable ... => ...`, which the bracketed form cannot see.  Live in the tree
#: once (`Model.freeze`'s `frozenObjects`, which *constructs* a table and keys into
#: nothing), so it costs the baseline nothing and makes a keyed access added to it
#: a Tier 0 failure rather than a silent exclusion.
TABLE_ASCRIPTION = re.compile(
    r"\b(?:let|have|fun)\s+(?P<name>[\w']+)\s*:\s*" + _TABLE_TYPE)

#: A binding whose value IS a table.  The right-hand side must END at the name:
#: `let x := st.objects.toList` is a sweep, already classified and counted there,
#: and a record field assignment (`{ st with objects := t }`) is not a binding.
#:
#: ...and it may be parenthesised (`let objs := (st.objects)`), through the same
#: `_RECV_OPEN` / `_RECV_CLOSE` every other receiver position composes.  The
#: brackets sit OUTSIDE the `rhs` group deliberately: `table_receivers` tests that
#: group with `.endswith(".objects")`, so capturing a `)` would make the test a
#: statement about punctuation.
TABLE_BINDING = re.compile(
    r"(?:^|[;(]|\bdo\b|\bthen\b|\belse\b|=>)\s*(?:let|have)\s+"
    r"(?P<name>[\w']+)\s*(?::[^:=\n]*)?:=\s*" + _RECV_OPEN
    + r"(?P<rhs>[\w'.]+)" + _RECV_CLOSE + r"\s*(?=$|[;)])", re.M)


def table_receivers(signature: str, body: str) -> dict:
    """{identifier: shape} for every name in this declaration that denotes a table.

    `param` — a signature binder of table type.  `alias` — a binding whose value is
    the `.objects` projection, or another name already known to be one, closed
    **transitively**, so `let a := st.objects; let b := a` is one population rather
    than a hole one rename opens.

    A name with both provenances is reported `alias`: a binding is the later and
    more specific evidence, and the shape is a reported attribute rather than a
    selector for which check runs, so the choice only has to be deterministic.

    The `.objects` test inherits the bounded ambiguity `READ` and `WRITE` already
    carry, and for the same reason: resolving a receiver's *type* is an elaborator
    question and this census runs in Tier 0, before any build.  Six types in this
    tree carry an `objects` field (`OBJECTS_FIELD_OWNERS`, derived and reconciled
    both ways), so binding a non-table one and keying into it would be
    over-reported — a false Tier 0 failure naming the declaration, which is the
    direction a floor must fail in, and which the reconciliation makes a *named*
    failure rather than a mystery.
    """
    names: dict = {}
    text = signature + "\n" + body
    # Over the WHOLE declaration, not the signature alone: a `fun` binder or an
    # ascription sits in the BODY, and a table bound there keys into the store
    # exactly as a parameter does -- so a signature-only scan would leave the third
    # spelling of the indirection invisible.
    for m in TABLE_BINDER.finditer(text):
        for n in m.group("names").split():
            names[n] = "param"
    for m in TABLE_ASCRIPTION.finditer(text):
        names[m.group("name")] = "param"
    changed = True
    while changed:
        changed = False
        for m in TABLE_BINDING.finditer(text):
            rhs, name = m.group("rhs"), m.group("name")
            if (rhs.endswith(".objects") or rhs in names) and names.get(name) != "alias":
                names[name] = "alias"
                changed = True
    return names


def table_primitive_declarations() -> set:
    """`(file, declaration)` for every operation of either object table.

    **Derived from `_TABLE_SOURCES`, never listed.**  A declaration named
    `RHTable.insert` or `FrozenMap.set`, in the table's own source, *is* the table
    operation: its parameter is the table because it is the primitive, so counting
    it as an indirection would report the definition of the thing being measured.
    Deriving it means a primitive added tomorrow is exempt on the day it is
    written, where a hand list would have made it a finding.

    It reads the **code view**, exactly as its sibling `declared_table_operations`
    does -- both go through `_TABLE_DECL` and `_TABLE_OP_KINDS`, so the two cannot
    disagree about what an operation of either table is, which is the whole reason
    the classification has one owner.  The view is what stops a `def RHTable.oldOp`
    written at column 0 inside a docstring from minting a phantom exemption; it
    costs the one theoretical case a raw read bought, a synthetic self-test tree
    holding a file at a `_TABLE_SOURCES` path, and no fixture is at one.

    **`v0.35.119`: the kind is classified.**  It matched `def`/`abbrev` with its
    sibling and so exempted neither an `opaque` nor an `instance` table primitive
    -- the direction that matters here is the opposite of the sibling's, since a
    missing exemption reports the primitive's own definition as an indirection,
    which is loud rather than silent.  Sharing the classification fixes both at
    once.
    """
    out: set = set()
    for _ns, files in _TABLE_SOURCES.items():
        for rel in files:
            text = lean_code_view.strip((REPO / rel).read_text(encoding="utf-8"))
            for m in _TABLE_DECL.finditer(text):
                if m.group("kw") in _TABLE_OP_KINDS:
                    out.add((rel, f"{m.group('ns')}.{m.group('op')}"))
    return out


def indirect_accesses(view: Path):
    """(code, spec, primitive_hits, unparsed) keyed `(file, declaration, shape, kind)`.

    Driven through `classify`, so the declaration boundary, the `Prop` verdict and
    the signature/body/default split are the SAME answers the direct censuses read
    — a mutation of any of them fails this census too.

    `primitive_hits` is what `table_primitive_declarations` matched, reconciled by
    the caller so an exemption that stops applying is reported rather than kept: an
    exemption nobody reconciles reads exactly like coverage.
    """
    code, spec, prim, unparsed = {}, {}, {}, []
    aliases = prop_aliases(view)
    primitives = table_primitive_declarations()
    for f in sorted(view.rglob("SeLe4n/**/*.lean")):
        rel = str(f.relative_to(view))
        segments: dict = {}

        def collect(decl, kind, sig, spec_text, code_text, _seg=segments):
            cell = _seg.setdefault(decl, ["", "", ""])
            cell[0] += sig + "\n"
            cell[1] += spec_text + "\n"
            cell[2] += code_text + "\n"

        here: list = []
        for _ in classify(f, aliases, here, READ, collect):
            pass
        unparsed.extend((rel, d, k, ln, why) for d, k, ln, why in here)
        for decl, (sig, spec_text, code_text) in segments.items():
            receivers = table_receivers(sig, spec_text + "\n" + code_text)
            for name, shape in sorted(receivers.items()):
                for kind, pat in sorted(indirect_patterns(name).items()):
                    n_code = len(pat.findall(code_text))
                    n_spec = len(pat.findall(spec_text))
                    if n_code and (rel, decl) in primitives:
                        prim[(rel, decl)] = prim.get((rel, decl), 0) + n_code
                    elif n_code:
                        key = (rel, decl, shape, kind)
                        code[key] = code.get(key, 0) + n_code
                    if n_spec:
                        key = (rel, decl, shape, kind)
                        spec[key] = spec.get(key, 0) + n_spec
    return code, spec, prim, unparsed


#: Every executable indirect access in the tree today, keyed
#: `(file, declaration, shape, kind)` with its count.  Reconciled in BOTH
#: directions in every mode: a key the baseline does not name, or a count above the
#: one it records, is a NEW evasion of the two enforced zeros; a key the tree no
#: longer has is a stale entry, which reads exactly like coverage.
INDIRECT_BASELINE = {
    # The queue-remove path binds the table and writes four neighbours and the
    # endpoint through the binding, reading two of them first.
    ("SeLe4n/Kernel/IPC/DualQueue/Core.lean",
     "endpointQueueRemove", "alias", "read"): 2,
    ("SeLe4n/Kernel/IPC/DualQueue/Core.lean",
     "endpointQueueRemove", "alias", "write"): 4,
    # The mid-queue splice binds it and patches both neighbours.
    ("SeLe4n/Kernel/Lifecycle/Operations/Cleanup.lean",
     "spliceOutMidQueueNode", "alias", "read"): 2,
    ("SeLe4n/Kernel/Lifecycle/Operations/Cleanup.lean",
     "spliceOutMidQueueNode", "alias", "write"): 2,
    # ...and the helper those two splices are stated over is handed the table
    # itself, which is the second spelling of the same indirection.
    ("SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean",
     "queueNeighbourPatch", "param", "read"): 1,
    ("SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean",
     "queueNeighbourPatch", "param", "write"): 1,
}

#: The exemptions `table_primitive_declarations` is expected to match, so a
#: primitive that stops keying into its own table is reported.  Derived on one side
#: and pinned on the other, the shape `WRITE_PRIMITIVE_BODIES` already has.
INDIRECT_PRIMITIVES = {
    ("SeLe4n/Model/FrozenState.lean", "FrozenMap.insert"): 1,
}


def indirect_violations(code: dict, prim: dict) -> list:
    """The floor and the exemption reconciliation, both in both directions."""
    out: list = []
    for key, n in sorted(code.items()):
        rel, decl, shape, kind = key
        was = INDIRECT_BASELINE.get(key)
        how = ("binds the object table" if shape == "alias"
               else "is handed the object table as a parameter")
        if was is None:
            out.append(
                f"{rel}: `{decl}` {how} and performs {n} keyed {kind}(s) through it."
                f"  Every store census keys on the receiver text `.objects`, so an"
                f" indirect access is one none of them can see -- which is how six"
                f" writes and four reads stayed outside two ENFORCED ZEROS until"
                f" `v0.35.117`.  A store primitive takes the STATE, never the table:"
                f" write through `storeObject` / `withObjectStored` / `rewriteObject`"
                f" or a typed update over it, and read through an accessor.")
        elif n > was:
            out.append(
                f"{rel}: `{decl}` performs {n} keyed {kind}(s) on an indirectly held"
                f" object table, up from {was}.  This floor may fall and never rise;"
                f" a new indirect access is a new keyed access outside both enforced"
                f" zeros.")
    for key, was in sorted(INDIRECT_BASELINE.items()):
        if key not in code:
            out.append(
                f"{key[0]}: stale INDIRECT_BASELINE entry -- `{key[1]}` no longer"
                f" performs {was} keyed {key[3]}(s) on an object table held as"
                f" `{key[2]}`, so delete the row.  An entry nothing reconciles reads"
                f" exactly like coverage.")
    for key, n in sorted(prim.items()):
        was = INDIRECT_PRIMITIVES.get(key)
        if was is None:
            out.append(
                f"{key[0]}: `{key[1]}` is exempted as an object-table primitive and"
                f" `INDIRECT_PRIMITIVES` does not record it -- record it with its"
                f" count, or the exemption is one nothing reconciles.")
        elif n != was:
            out.append(
                f"{key[0]}: `{key[1]}` keys into its own table {n}x where"
                f" `INDIRECT_PRIMITIVES` records {was}.")
    for key, was in sorted(INDIRECT_PRIMITIVES.items()):
        if key not in prim:
            out.append(
                f"{key[0]}: stale INDIRECT_PRIMITIVES entry for `{key[1]}` ({was}x)"
                f" -- it no longer keys into its own table, so delete the row.")
    return out


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
    # **A SPELLING QUOTED IN A STRING IS NOT A READ** (PR #895 review round
    # 16).  `READ` matches a spelling, so a diagnostic naming that spelling was
    # counted as an executable raw store read and the enforced zero refused
    # valid code -- while the Tier 1 reconciliation, which sees a genuine
    # executable `def` and agrees about the declaration, could not correct it.
    # Fail-CLOSED, and round 6 recorded that the safe direction is a direction.
    # Token-preserving against the case below, which is the decisive control:
    # the same spelling, outside quotes, must still count.
    "a_read_quoted_in_a_string_is_not_a_read": ("""
def diagnostic : String := "avoid .objects[raw]? syntax"
""", {}, {}),
    "the_same_spelling_unquoted_is_still_a_read": ("""
def peek (st : SystemState) (oid : ObjId) : Bool :=
  (st.objects[oid]?).isSome
""", {("f.lean", "peek"): 1}, {}),
    # **The decisive cases for `_RECV_CLOSE`** (`v0.35.151`).  A receiver may be
    # parenthesised, and the SUBSCRIPT spelling is the one the live tree already
    # writes: four keyed reads in `Scheduler/Invariant.lean` are spelled
    # `({ st with objects := ... }.objects)[tid.toObjId]?`, which `READ` could
    # not see.  They sit in a `theorem`, so the enforced zero was untouched by
    # ACCIDENT; this fixture is the same read in a `def` body, where it is not.
    # Token-preserving against `code_read`: same read, same operand, brackets
    # moved from around the subscript to around the receiver.
    "parenthesised_subscript_read": ("""
def peek (st : SystemState) (oid : ObjId) : Option KernelObject :=
  (st.objects)[oid]?
""", {("f.lean", "peek"): 1}, {}),
    # ...and the method spelling of the same keyed read.
    "parenthesised_method_read": ("""
def peek (st : SystemState) (oid : ObjId) : Option KernelObject :=
  (st.objects).get? oid
""", {("f.lean", "peek"): 1}, {}),
    # **The control that keeps the widening exact rather than conservative.**
    # Lean's own lexer separates `x[i]` (a subscript) from `x [i]` (an
    # application to a list literal), so `_RECV_CLOSE` admits whitespace only
    # INSIDE the bracket group and never between the last `)` and the accessor.
    # Token-preserving against `parenthesised_subscript_read`: one space.
    "a_spaced_bracket_is_an_application_not_a_read": ("""
def build (st : SystemState) (a b : ObjId) : List ObjId :=
  consumeTable (st.objects) [a, b]
""", {}, {}),
}

#: Cases whose fixture the parser must REFUSE, and how many declarations it must
#: name.  Every other case asserts **zero**, which is the other direction of the
#: same reconciliation: a terminator that starts rejecting valid Lean fails the
#: twenty-nine cases that do not appear here.
EXPECT_REFUSALS = {"unterminated_is_refused": 1}


#: The write census's own cases, classified with `WRITE` (`v0.35.76`).  Every
#: mutation is token-preserving against a sibling: the same raw write moved
#: between a transition and a proposition, or between two spellings of one
#: write, or into a string literal that names it.
WRITE_FIXTURES = {
    # A transition writing the table raw: the migratable population.
    "code_write": ("""
def step (st : SystemState) (k : ObjId) (o : KernelObject) : SystemState :=
  { st with objects := st.objects.insert k o }
""", {("f.lean", "step"): 1}, {}),
    # The same write as a proposition's vocabulary: a theorem about the store.
    "theorem_write": ("""
theorem frame (st : SystemState) (k : ObjId) (o : KernelObject) :
    (st.objects.insert k o)[k]? = some o := by
  exact RHTable.getElem?_insert_self _ _ _ (by assumption)
""", {}, {("f.lean", "frame"): 1}),
    # The qualified spelling is the same write (a spelling is not a write).
    "qualified_write": ("""
def step (st : SystemState) (k : ObjId) (o : KernelObject) : SystemState :=
  { st with objects := RHTable.insert st.objects k o }
""", {("f.lean", "step"): 1}, {}),
    # The frozen table's `set`, on a frozen state.
    "frozen_write": ("""
def frozenStep (st : FrozenSystemState) (k : ObjId) (o : FrozenKernelObject) :
    FrozenSystemState :=
  { st with objects := FrozenMap.set st.objects k o }
""", {("f.lean", "frozenStep"): 1}, {}),
    # **The decisive case for this branch** (`v0.35.97`): the SAME write, in the
    # METHOD spelling.  `WRITE` named `set` in its qualified branch and not in
    # its method branch, so `st.objects.set k o` -- the frozen surface's
    # ordinary store -- was invisible to an enforced zero while
    # `FrozenMap.set st.objects k o` above was seen.  The mutation that decides
    # this keeps the write and changes only how it is written, which is why the
    # two fixtures are token-preserving with respect to each other.
    "frozen_write_method_form": ("""
def frozenStepMethod (st : FrozenSystemState) (k : ObjId) (o : FrozenKernelObject) :
    Option FrozenSystemState :=
  (st.objects.set k o).map (fun m => { st with objects := m })
""", {("f.lean", "frozenStepMethod"): 1}, {}),
    # ...and `insert` in the method spelling, which is how the one frozen
    # transition that escaped the `set`-only branch actually spelled its write.
    "frozen_insert_method_form": ("""
def frozenRewrite (st : FrozenSystemState) (k : ObjId) (o : FrozenKernelObject) :
    FrozenSystemState :=
  { st with objects := st.objects.insert k o }
""", {("f.lean", "frozenRewrite"): 1}, {}),
    # An erase is a write too.
    "erase_write": ("""
def drop (st : SystemState) (k : ObjId) : SystemState :=
  { st with objects := st.objects.erase k }
""", {("f.lean", "drop"): 1}, {}),
    # A `def` returning `Prop` files its write as specification.
    "prop_def_write": ("""
def stored (st : SystemState) (k : ObjId) (o : KernelObject) : Prop :=
  (st.objects.insert k o)[k]? = some o
""", {}, {("f.lean", "stored"): 1}),
    # A write named INSIDE A STRING is not a write: this census reads the
    # string-blanked view.  Token-preserving against `code_write`.
    "string_names_a_write": ("""
def diagnostic : String := "avoid { st with objects := st.objects.insert k o }"
""", {}, {}),
    # **The decisive cases for `_RECV_CLOSE` / `_RECV_OPEN`** (`v0.35.151`): the
    # SAME write, with the receiver parenthesised.  Lean permits redundant
    # brackets around any expression, and every pattern here keys on the
    # receiver's TEXT, so each of these walked around an enforced zero.  Each is
    # token-preserving against `code_write` / `qualified_write` above -- the
    # write and its operands are identical and only the brackets move, which is
    # the mutation this class needs (*keep the token, break the relation*).
    "parenthesised_method_write": ("""
def step (st : SystemState) (k : ObjId) (o : KernelObject) : SystemState :=
  { st with objects := (st.objects).insert k o }
""", {("f.lean", "step"): 1}, {}),
    "parenthesised_qualified_argument_write": ("""
def step (st : SystemState) (k : ObjId) (o : KernelObject) : SystemState :=
  { st with objects := RHTable.insert (st.objects) k o }
""", {("f.lean", "step"): 1}, {}),
    # ...and the projection's HEAD parenthesised, which `[\w'.]*` structurally
    # cannot span.  This tree already writes that shape at five sites for
    # theorem helpers (`RHTable.fold_preserves_of_lookup (spliceOutMidQueueNode
    # st tid).objects`), so a write spelled this way is one rename away.
    "parenthesised_qualified_head_write": ("""
def step (st : SystemState) (tid : ThreadId) (k : ObjId) : SystemState :=
  { st with objects := RHTable.erase (spliceOutMidQueueNode st tid).objects k }
""", {("f.lean", "step"): 1}, {}),
}


# ---------------------------------------------------------------------------
# INDIRECT fixtures: `(source, want_code, want_spec)` keyed
# `(file, declaration, shape, kind)`.
#
# Token-preserving where the property allows: a case that keeps the access and
# changes only *how the table was obtained* is what distinguishes this census from
# the receiver-keyed ones, and a case that keeps the access and changes the
# declaration's kind is what pins the population split.
# ---------------------------------------------------------------------------
INDIRECT_FIXTURES = {
    # THE FINDING: bind the table, write through the binding.  Invisible to
    # `WRITE`, which keys on the receiver text `.objects`.
    "alias_write": ("""
def step (st : SystemState) (k : ObjId) (o : KernelObject) : SystemState :=
  let objs := st.objects
  { st with objects := objs.insert k o }
""", {("SeLe4n/f.lean", "step", "alias", "write"): 1}, {}),
    # ...and read through it, invisible to `READ` for the same reason.
    "alias_read": ("""
def peek (st : SystemState) (k : ObjId) : Option KernelObject :=
  let objs := st.objects
  objs[k]?
""", {("SeLe4n/f.lean", "peek", "alias", "read"): 1}, {}),
    # THE SECOND SPELLING: the table itself as a parameter.  Token-preserving
    # against `alias_write` -- same write, obtained by being handed the table.
    "param_write": ("""
def patch (objs : RHTable SeLe4n.ObjId KernelObject) (k : ObjId)
    (o : KernelObject) : RHTable SeLe4n.ObjId KernelObject :=
  objs.insert k o
""", {("SeLe4n/f.lean", "patch", "param", "write"): 1}, {}),
    # A binder may bind SEVERAL names, and each is a table.  A capture that took
    # only the last would leave the first's accesses invisible, so this reads
    # through one name and writes through the other.
    "param_two_names": ("""
def merge (a b : RHTable SeLe4n.ObjId KernelObject) (k : ObjId) :
    RHTable SeLe4n.ObjId KernelObject :=
  match a[k]? with
  | some v => b.insert k v
  | none => b.erase k
""", {("SeLe4n/f.lean", "merge", "param", "read"): 1,
      ("SeLe4n/f.lean", "merge", "param", "write"): 2}, {}),
    # A SUBSCRIPT ON A DERIVED EXPRESSION is not an access on the bound name:
    # `(objs.insert k o)[k]?` reads the table the insert returned, not `objs`.
    # That is exactly what the direct censuses say of
    # `(st.objects.insert k o)[k]?` -- one write, no read -- so the two agree by
    # construction rather than by two authors choosing the same reading.
    "derived_subscript_is_not_a_read": ("""
def roundTrip (st : SystemState) (k : ObjId) (o : KernelObject) :
    Option KernelObject :=
  let objs := st.objects
  (objs.insert k o)[k]?
""", {("SeLe4n/f.lean", "roundTrip", "alias", "write"): 1}, {}),
    # THE POPULATION SPLIT.  Token-preserving against `alias_write`: the same
    # binding and the same write, in a `theorem`, which is specification.
    "alias_write_in_theorem_is_spec": ("""
theorem frame (st : SystemState) (k : ObjId) (o : KernelObject) : True :=
  let objs := st.objects
  have _h : (objs.insert k o).invExt := proofPlaceholder
  trivial
""", {}, {("SeLe4n/f.lean", "frame", "alias", "write"): 1}),
    # TRANSITIVITY.  `let b := a` where `a` is already the table.  Closing the
    # alias set transitively is what stops one extra binding hiding an access --
    # the same hole one rename opens.
    "alias_transitive": ("""
def step (st : SystemState) (k : ObjId) (o : KernelObject) : SystemState :=
  let a := st.objects
  let b := a
  { st with objects := b.insert k o }
""", {("SeLe4n/f.lean", "step", "alias", "write"): 1}, {}),
    # A SWEEP BINDING IS NOT AN ALIAS.  The right-hand side must END at the
    # projection: `st.objects.toList` is a traversal, already classified and
    # counted by `SWEEP`, and its result is a list rather than a table -- so a
    # subscript on it is not a keyed store access.
    "sweep_binding_is_not_an_alias": ("""
def count (st : SystemState) : Option (ObjId × KernelObject) :=
  let entries := st.objects.toList
  entries[0]?
""", {}, {}),
    # THE RECEIVER IS DELIMITED.  A longer identifier that merely CONTAINS the
    # alias, and a field path that ends in it, are not the bound name.
    "receiver_is_delimited": ("""
def step (st : SystemState) (other : Shadow) (k : ObjId)
    (o : KernelObject) : SystemState :=
  let objs := st.objects
  let _a := myobjs.insert k o
  let _b := other.objs.insert k o
  { st with objects := objs.insert k o }
""", {("SeLe4n/f.lean", "step", "alias", "write"): 1}, {}),
    # THE QUALIFIED SPELLING, indirect.  `RHTable.insert objs k o` is the same
    # write; a method-only pattern is the asymmetry `WRITE` already paid for.
    "qualified_indirect_write": ("""
def step (st : SystemState) (k : ObjId) (o : KernelObject) : SystemState :=
  let objs := st.objects
  { st with objects := RHTable.insert objs k o }
""", {("SeLe4n/f.lean", "step", "alias", "write"): 1}, {}),
    # THE FROZEN TABLE, as a parameter.  `FrozenMap.set` is the frozen store's
    # ordinary write, and the frozen surface is production (`v0.35.60`).
    "frozen_param_write": ("""
def frozenPatch (fm : FrozenMap) (k : ObjId) (o : FrozenKernelObject) : FrozenMap :=
  fm.set k o
""", {("SeLe4n/f.lean", "frozenPatch", "param", "write"): 1}, {}),
    # A LAMBDA BINDER of table type, which sits in the BODY.  Token-preserving
    # against `param_write`: the same write, the table bound by a `fun` rather than
    # by the declaration's own signature.
    "lambda_binder_write": ("""
def apply (st : SystemState) (k : ObjId) (o : KernelObject) : SystemState :=
  let f := fun (objs : RHTable SeLe4n.ObjId KernelObject) => objs.insert k o
  { st with objects := f st.objects }
""", {("SeLe4n/f.lean", "apply", "param", "write"): 1}, {}),
    # ...and the UNBRACKETED ascription, which the bracketed binder cannot see.
    # Live in the tree once (`Model.freeze`'s `frozenObjects`), keying into
    # nothing -- so this is the arm that must be planted to be shown to work.
    "ascribed_binding_write": ("""
def build (st : SystemState) (k : ObjId) (o : KernelObject) : SystemState :=
  let t : RHTable SeLe4n.ObjId KernelObject := RHTable.empty 16
  { st with objects := t.insert k o }
""", {("SeLe4n/f.lean", "build", "param", "write"): 1}, {}),
    # A BINDING OF SOMETHING ELSE is not a table, however it is spelled.  The
    # control for `alias_write`: same shape, a right-hand side that is not the
    # projection.
    "unrelated_binding": ("""
def step (st : SystemState) (k : ObjId) (o : KernelObject) : SystemState :=
  let q := st.scheduler
  { st with scheduler := q.insert k o }
""", {}, {}),
    # **THE REPORTED FINDING** (PR #897 review, `v0.35.151`): the binding's
    # right-hand side may be parenthesised, and `TABLE_BINDING`'s `rhs` group is
    # a bare path class, so `let objs := (st.objects)` bound no table at all and
    # every access through `objs` was outside this census.  Token-preserving
    # against `alias_write`: the same binding and the same write, two brackets.
    "parenthesised_binding_rhs": ("""
def step (st : SystemState) (k : ObjId) (o : KernelObject) : SystemState :=
  let objs := (st.objects)
  { st with objects := objs.insert k o }
""", {("SeLe4n/f.lean", "step", "alias", "write"): 1}, {}),
    # ...and the ACCESS may be parenthesised in each of its three spellings, on
    # a receiver bound the ordinary way.  Each is token-preserving against
    # `alias_write` / `alias_read`: the same access, two brackets.
    "parenthesised_alias_method_write": ("""
def step (st : SystemState) (k : ObjId) (o : KernelObject) : SystemState :=
  let objs := st.objects
  { st with objects := (objs).insert k o }
""", {("SeLe4n/f.lean", "step", "alias", "write"): 1}, {}),
    "parenthesised_alias_subscript_read": ("""
def peek (st : SystemState) (k : ObjId) : Option KernelObject :=
  let objs := st.objects
  (objs)[k]?
""", {("SeLe4n/f.lean", "peek", "alias", "read"): 1}, {}),
    "parenthesised_alias_qualified_write": ("""
def step (st : SystemState) (k : ObjId) (o : KernelObject) : SystemState :=
  let objs := st.objects
  { st with objects := RHTable.insert (objs) k o }
""", {("SeLe4n/f.lean", "step", "alias", "write"): 1}, {}),
    # The CONTROL for the widened binding: `_RECV_OPEN` / `_RECV_CLOSE` admit
    # brackets around the right-hand side and must not make the right-hand side
    # itself looser.  `(st.scheduler)` is still not a table.
    "parenthesised_unrelated_binding": ("""
def step (st : SystemState) (k : ObjId) (o : KernelObject) : SystemState :=
  let q := (st.scheduler)
  { st with scheduler := (q).insert k o }
""", {}, {}),
}


def self_test() -> int:
    failed = 0
    with tempfile.TemporaryDirectory() as td:
        for name, (src, want_code, want_spec) in WRITE_FIXTURES.items():
            root = Path(td) / ("w_" + name) / "SeLe4n"
            root.mkdir(parents=True)
            (root / "f.lean").write_text(lean_code_view.strip(src))
            aliases = prop_aliases(Path(td) / ("w_" + name))
            got_code, got_spec, refused = {}, {}, []
            for decl, is_prop, n, _line, _region in classify(root / "f.lean", aliases, refused, WRITE):
                key = ("f.lean", decl)
                (got_spec if is_prop else got_code)[key] = \
                    (got_spec if is_prop else got_code).get(key, 0) + n
            if got_code != want_code or got_spec != want_spec or refused:
                print(f"  FAIL write:{name}")
                print(f"    code:     got {got_code} want {want_code}")
                print(f"    spec:     got {got_spec} want {want_spec}")
                print(f"    refusals: {refused}")
                failed += 1
            else:
                print(f"  ok   write:{name}")
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
    # **The INDIRECT census**, on synthetic trees.  It is driven through
    # `indirect_accesses` rather than through `classify` directly, because the
    # property is a relation between a declaration's SIGNATURE and its BODY that no
    # line pattern can express -- which is the whole reason the `collect` hook
    # exists.
    with tempfile.TemporaryDirectory() as td:
        for name, (src, want_code, want_spec) in INDIRECT_FIXTURES.items():
            root = Path(td) / ("i_" + name) / "SeLe4n"
            root.mkdir(parents=True)
            (root / "f.lean").write_text(lean_code_view.strip(src))
            got_code, got_spec, _prim, refused = indirect_accesses(
                Path(td) / ("i_" + name))
            if got_code != want_code or got_spec != want_spec or refused:
                print(f"  FAIL indirect:{name}")
                print(f"    code:     got {got_code} want {want_code}")
                print(f"    spec:     got {got_spec} want {want_spec}")
                print(f"    refusals: {refused}")
                failed += 1
            else:
                print(f"  ok   indirect:{name}")
    # **The FLOOR, in both directions.**  Every case is token-preserving: the tree
    # is the live one and only the BASELINE moves, so what each case decides is
    # what the reconciliation asserts rather than what the scanner can see.
    # Over the CODE VIEW, as `main` does: a comment naming a binding is not a
    # binding, and the docstrings above quote both spellings in order to explain
    # them.  Reading the raw tree here would make the self-test disagree with the
    # gate about the live population -- two answers to one question.
    live_code, live_spec, live_prim, _ = indirect_accesses(code_view(REPO))
    saved_baseline = dict(INDIRECT_BASELINE)
    saved_prims = dict(INDIRECT_PRIMITIVES)
    a_key = ("SeLe4n/Kernel/IPC/DualQueue/Core.lean",
             "endpointQueueRemove", "alias", "write")
    for case, mutate, expect in [
        ("the live tree reconciles both ways", None, False),
        # A NEW indirect access -- the thing this census exists to refuse.  The
        # mutation drops the key rather than the site, so the tree is unchanged
        # and what fails is the claim that the site was known.
        ("an UNRECORDED indirect access fails",
         lambda b, p: b.pop(a_key), True),
        # A count that ROSE.  A set of keys alone cannot see this.
        ("a RAISED count fails",
         lambda b, p: b.__setitem__(a_key, b[a_key] - 1), True),
        # ...and a count that FELL is the floor working: it may fall and never
        # rise, so this direction must PASS or the census would forbid progress.
        ("a LOWERED count passes",
         lambda b, p: b.__setitem__(a_key, b[a_key] + 1), False),
        # A STALE key reads exactly like coverage, so it fails too.
        ("a STALE baseline entry fails",
         lambda b, p: b.__setitem__(
             ("SeLe4n/Model/State.lean", "ghost", "alias", "write"), 1), True),
        # The PRIMITIVE exemption, both ways.  An exemption nothing reconciles
        # reads like coverage, and a stale one reads like a live one.
        ("an UNRECORDED primitive exemption fails",
         lambda b, p: p.clear(), True),
        ("a STALE primitive exemption fails",
         lambda b, p: p.__setitem__(
             ("SeLe4n/Model/FrozenState.lean", "FrozenMap.ghost"), 1), True),
    ]:
        try:
            if mutate is not None:
                mutate(globals()["INDIRECT_BASELINE"], globals()["INDIRECT_PRIMITIVES"])
            got = bool(indirect_violations(live_code, live_prim))
        finally:
            globals()["INDIRECT_BASELINE"] = dict(saved_baseline)
            globals()["INDIRECT_PRIMITIVES"] = dict(saved_prims)
        if got != expect:
            print(f"  SELF-TEST FAIL: indirect-floor '{case}': "
                  f"reported {got}, want {expect}")
            failed += 1
        else:
            print(f"  ok   indirect-floor '{case}'")
    # The INDIRECT population is reported, not enforced at zero, so the number
    # itself is part of the claim: a census that silently stopped seeing the sites
    # would report a smaller number and pass every case above.
    if sum(live_code.values()) == 0:
        print("  SELF-TEST FAIL: indirect-floor 'the census sees the live "
              "population' -- STORE_INDIRECT_CODE is 0, which this tree is not")
        failed += 1
    else:
        print(f"  ok   indirect-floor 'the census sees the live population' "
              f"({sum(live_code.values())} access(es))")
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
    # **The CLASSIFICATION, and the SYMMETRY of the two branches.**  The
    # patterns are BUILT from `_TABLE_OPS`, so an operation nobody classified
    # is one neither pattern ever looks for -- and a kind named in one branch
    # and not the other is the same hole one level down, which is exactly how
    # `set` came to be recognised qualified and not as a method.  Both
    # reconciliations are mutation-tested here, because a discipline check that
    # cannot fire is indistinguishable from one that is wrong.
    known_ops = dict(_TABLE_OPS)
    for case, mutate, expect_unclassified, expect_asymmetric in [
        ("the live classification reconciles both ways", None, False, False),
        ("an UNCLASSIFIED table operation fails",
         lambda d: d.pop("set", None), True, False),
        # A stale entry trips BOTH: it names no table operation, and the
        # compiled pattern -- built from the real classification -- does not
        # recognise it either.  Expecting only the first would be asserting
        # less than the gate says.
        ("a STALE classification entry fails",
         lambda d: d.update({"notAnOperation": "write"}), True, True),
    ]:
        try:
            if mutate is not None:
                mutate(globals()["_TABLE_OPS"])
            got_unclassified = bool(table_op_violations())
            got_asymmetric = bool(branch_symmetry_violations())
        finally:
            globals()["_TABLE_OPS"] = dict(known_ops)
        if got_unclassified != expect_unclassified or got_asymmetric != expect_asymmetric:
            print(f"  SELF-TEST FAIL: table-ops '{case}': reported "
                  f"unclassified={got_unclassified} asymmetric={got_asymmetric}, "
                  f"want unclassified={expect_unclassified} "
                  f"asymmetric={expect_asymmetric}")
            failed += 1
        else:
            print(f"  ok   table-ops '{case}'")
    # The symmetry check's own decisive case: a kind recognised in ONE branch.
    # The mutation keeps `set` classified `write` -- it changes only which
    # spellings the pattern is built to see, which is the pre-fix state.
    saved_write = globals()["WRITE"]
    try:
        globals()["WRITE"] = re.compile(
            r"\b(?:RHTable|FrozenMap)\." + _op_alternation(("write",))
            + r"\s+[\w'.]*\.objects\b")
        asymmetric = bool(branch_symmetry_violations())
    finally:
        globals()["WRITE"] = saved_write
    if not asymmetric:
        print("  SELF-TEST FAIL: table-ops 'a QUALIFIED-ONLY write branch must "
              "be reported' -- the symmetry check did not fire")
        failed += 1
    else:
        print("  ok   table-ops 'a QUALIFIED-ONLY write branch is reported'")
    # **The paren spellings' own decisive cases** (`v0.35.151`).  The fixtures
    # above pin that the patterns SEE a parenthesised receiver; these pin that
    # the RECONCILIATION would report it if they stopped, which is the half a
    # fixture cannot assert.  Each mutation rebuilds `WRITE` / `READ` with one
    # piece of the receiver admission removed and keeps everything else, so what
    # is being measured is that piece and nothing beside it.
    #
    # Each case names the substring its violation must carry, so what it decides
    # is WHICH assertion fired.  A case that merely asked "was anything
    # reported" is satisfied by a neighbouring assertion, and the first run of
    # this block measured exactly that: dropping the PARENTHESISED SUBSCRIPT
    # check left the suite green, because no case could reach it.  The two
    # subscript cases below are therefore each other's controls -- one requires
    # a bracket where Lean does not, the other admits none where Lean does.
    for case, kind, pattern, want in [
        # The closing run: `(st.objects).insert k v` becomes invisible.
        ("a receiver whose CLOSING bracket is not admitted is reported",
         "WRITE",
         re.compile(rf"\.objects\.{_op_alternation(('write',))}"
                    rf"|\b(?:RHTable|FrozenMap)\.{_op_alternation(('write',))}"
                    rf"\s+{_RECV_OPEN}(?:\([^()\n]*\)|[\w'.]*)\.objects\b"),
         "PARENTHESISED METHOD"),
        # The opening run: `RHTable.insert (st.objects) k v` becomes invisible.
        ("a receiver whose OPENING bracket is not admitted is reported",
         "WRITE",
         re.compile(rf"\.objects{_RECV_CLOSE}\.{_op_alternation(('write',))}"
                    rf"|\b(?:RHTable|FrozenMap)\.{_op_alternation(('write',))}"
                    rf"\s+(?:\([^()\n]*\)|[\w'.]*)\.objects\b"),
         "PARENTHESISED QUALIFIED ARGUMENT"),
        # The parenthesised APPLICATION head, which `[\w'.]*` cannot span.
        ("a parenthesised projection HEAD that is not admitted is reported",
         "WRITE",
         re.compile(rf"\.objects{_RECV_CLOSE}\.{_op_alternation(('write',))}"
                    rf"|\b(?:RHTable|FrozenMap)\.{_op_alternation(('write',))}"
                    rf"\s+{_RECV_OPEN}[\w'.]*\.objects\b"),
         "PARENTHESISED QUALIFIED HEAD"),
        # The SUBSCRIPT is notation rather than a named operation, so it is
        # asserted once beside the crossing -- and each of its two spellings
        # needs the case the other cannot produce.  Here the bracket is
        # REQUIRED, so the bare `st.objects[k]?` stops being a read.
        ("a subscript branch that requires a bracket is reported",
         "READ",
         re.compile(rf"(?:\.objects{_RECV_CLOSE}\.{_op_alternation(('read',))}"
                    rf"|\.objects(?:\s*\))+\[)"
                    rf"|\b(?:RHTable|FrozenMap)\.{_op_alternation(('read',))}"
                    rf"\s+{_RECV_OPEN}(?:\([^()\n]*\)|[\w'.]*)\.objects\b"),
         "the SUBSCRIPT read"),
        # ...and here it is REFUSED, which is the pre-`v0.35.151` state and the
        # spelling the live tree already writes four times.
        ("a subscript branch that admits no bracket is reported",
         "READ",
         re.compile(rf"(?:\.objects{_RECV_CLOSE}\.{_op_alternation(('read',))}"
                    rf"|\.objects\[)"
                    rf"|\b(?:RHTable|FrozenMap)\.{_op_alternation(('read',))}"
                    rf"\s+{_RECV_OPEN}(?:\([^()\n]*\)|[\w'.]*)\.objects\b"),
         "the PARENTHESISED SUBSCRIPT read"),
        # ...and the other direction: a closing run that admits TRAILING
        # whitespace turns `f (st.objects) [a, b]` -- an application to a list
        # literal -- into a subscript read.  The one case where the widening
        # must be shown to be exact rather than merely safe.
        ("a closing run that admits trailing whitespace is reported",
         "READ",
         re.compile(rf"(?:\.objects(?:\s*\))*\s*\.{_op_alternation(('read',))}"
                    rf"|\.objects(?:\s*\))*\s*\[)"
                    rf"|\b(?:RHTable|FrozenMap)\.{_op_alternation(('read',))}"
                    rf"\s+{_RECV_OPEN}(?:\([^()\n]*\)|[\w'.]*)\.objects\b"),
         "application to a list literal"),
    ]:
        saved = globals()[kind]
        try:
            globals()[kind] = pattern
            reported = branch_symmetry_violations()
        finally:
            globals()[kind] = saved
        if not any(want in line for line in reported):
            print(f"  SELF-TEST FAIL: table-ops '{case}' -- no violation "
                  f"carrying {want!r} was reported (got {reported})")
            failed += 1
        else:
            print(f"  ok   table-ops '{case}'")
    # `v0.35.119`: the declaration KIND decides, and a kind in NEITHER set is
    # refused rather than skipped.  Over synthetic text, because the case that
    # matters -- a declaration form this tree does not yet contain -- cannot be
    # reached by mutating a classification the way the cases above do, and because
    # the pre-fix `(?:def|abbrev)` pattern makes the `opaque` row FAIL while every
    # other row passes: that asymmetry is the measurement.
    for case, src, want_ops, want_unclassified in [
        ("a `def` table operation is discovered",
         "def RHTable.insert (t : RHTable a b) : RHTable a b := t\n",
         {"insert"}, set()),
        ("an `opaque` table operation is discovered -- the pre-fix blind spot",
         "opaque RHTable.rawSet : RHTable a b -> RHTable a b\n",
         {"rawSet"}, set()),
        ("...and so is one behind attributes and modifiers",
         "@[inline] private noncomputable opaque FrozenMap.rawPut : Nat\n",
         {"rawPut"}, set()),
        ("a `theorem` ABOUT a table is not an operation",
         "theorem RHTable.insert_eq : True := trivial\n",
         set(), set()),
        ("...nor is a `Prop`-valued dotted structure",
         "structure RHTable.WF (t : RHTable a b) : Prop where\n  ok : True\n",
         set(), set()),
        # The undotted structure is a different path: `_TABLE_DECL` requires the
        # dot, so the table's own fields still come from `_TABLE_STRUCT`.  Kept
        # because a widening that broke the field harvest would pass every row
        # above.
        ("the table STRUCTURE's own fields are still operations",
         "structure RHTable (a : Type) (b : Type) where\n  size : Nat\n"
         "  buckets : Array Nat\n\ndef unrelated := 1\n",
         {"size", "buckets"}, set()),
        # `macro` stands for "a declaration form this scanner has not seen": Lean 4
        # has added several, and the refusal is what makes the NEXT one loud
        # instead of silently shrinking what READ, WRITE and SWEEP look for.
        ("a kind in NEITHER set is REFUSED rather than skipped",
         "macro RHTable.smuggle : Nat := 0\n",
         set(), {("macro", "RHTable.smuggle")}),
    ]:
        got_ops, got_unclassified = classify_table_declarations(src)
        if got_ops != want_ops or got_unclassified != want_unclassified:
            print(f"  SELF-TEST FAIL: table-kind '{case}': ops={sorted(got_ops)} "
                  f"unclassified={sorted(got_unclassified)}, want "
                  f"ops={sorted(want_ops)} "
                  f"unclassified={sorted(want_unclassified)}")
            failed += 1
        else:
            print(f"  ok   table-kind '{case}'")
    # ...and the live sources must hold no unclassifiable declaration, so the
    # refusal is known to be quiet on this tree rather than merely present.
    _live_ops, live_unclassified = _walk_table_sources()
    if live_unclassified:
        for rel, kw, name in sorted(live_unclassified):
            print(f"  SELF-TEST FAIL: table-kind live tree: {rel} `{kw} {name}`")
        failed += len(live_unclassified)
    else:
        print("  ok   table-kind 'every live table declaration is classified'")
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
    # The figures are the fixture dictionaries' own lengths, never literals: a
    # hand-kept count beside a derivation drifts on contact, and this line is what
    # a reader takes as the claim about how much ran.
    print(f"[store-read-census] self-test passed ({len(FIXTURES)} read cases, "
          f"{len(WRITE_FIXTURES)} write cases, "
          f"{len(INDIRECT_FIXTURES)} indirect cases)")
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
    # The patterns are BUILT from `_TABLE_OPS`, so an operation nobody
    # classified is one neither pattern ever looks for -- which is how `set`
    # stayed out of the WRITE method branch past an enforced zero.  Both
    # directions, and both branches, in every mode.
    misclassified = table_op_violations() + branch_symmetry_violations()
    if misclassified:
        for line in misclassified:
            print(f"FAIL: {line}")
        return 1
    code, spec, exempt_hits, attribution, unparsed = census(view)
    wcode, wspec, wexempt_hits, wattribution, _ = census(view, WRITE, WRITE_PRIMITIVE_BODIES)
    scode, sspec, _, _, _ = census(view, SWEEP, {})
    # The INDIRECT population, driven through the SAME classifier: a table held
    # through a binding or a parameter is only a finding where the holding
    # declaration is executable, and "which population is this declaration in"
    # already has one answer.
    icode, ispec, iprim, iunparsed = indirect_accesses(view)
    # The refusal channel is the classifier's own, so an unclosed signature fails
    # here exactly as it does for the direct censuses rather than silently filing a
    # declaration's whole body as specification.
    unparsed = list(unparsed) + [u for u in iunparsed if u not in unparsed]
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
    # Refused in EVERY mode, for the reason the registry is: `--rows` is what
    # Tier 0 calls, and a check only the unused mode runs is a check nobody runs.
    # AFTER the refusal channel above, deliberately: an unclosed signature makes
    # the receiver derivation unreliable, so reporting "a new indirect access"
    # there would name the wrong cause -- "the gate could not read it" and "the
    # gate read it and it differs" must not produce the same failure.
    indirect = indirect_violations(icode, iprim)
    if indirect:
        for problem in indirect:
            print(f"FAIL: {problem}", file=sys.stderr)
        return 1
    # Reconciled in EVERY mode, `--rows` included: that is the mode the Tier 0
    # baseline calls, so skipping it there would leave the registry checkable
    # only by a command nothing runs — a gate with a silent default branch,
    # which is the shape this project keeps paying for.
    stale = (accessor_registry_violations(code, exempt_hits)
             + accessor_registry_violations(wcode, wexempt_hits, WRITE_PRIMITIVE_BODIES, "write"))
    if stale:
        for problem in stale:
            print(f"FAIL: {problem}", file=sys.stderr)
        return 1
    if args.attribution:
        # One stream for both populations: the reconciliation judges the
        # CLASSIFIER's two structural answers per line, and those do not
        # depend on which access the line carries.  A line carrying both is
        # one row.
        for rel, lineno, decl, is_prop, region in sorted(set(attribution) | set(wattribution)):
            print(f"STORE_ACCESS_ATTRIB={rel}|{lineno}|{decl}|{1 if is_prop else 0}|{region}")
        return 0
    if args.rows:
        for (f, d), n in sorted(code.items()):
            print(f"STORE_READ_CODE_SITE={f}|{d}|{n}")
        for (f, d), n in sorted(spec.items()):
            print(f"STORE_READ_SPEC_SITE={f}|{d}|{n}")
        for (f, d), n in sorted(wcode.items()):
            print(f"STORE_WRITE_CODE_SITE={f}|{d}|{n}")
        for (f, d), n in sorted(wspec.items()):
            print(f"STORE_WRITE_SPEC_SITE={f}|{d}|{n}")
        for (f, d, shape, kind), n in sorted(icode.items()):
            print(f"STORE_INDIRECT_CODE_SITE={f}|{d}|{shape}|{kind}|{n}")
    if args.totals or not args.rows:
        print(f"STORE_READ_CODE={sum(code.values())}")
        print(f"STORE_READ_SPEC={sum(spec.values())}")
        print(f"STORE_WRITE_CODE={sum(wcode.values())}")
        print(f"STORE_WRITE_SPEC={sum(wspec.values())}")
        # The claim, beside the number.  A bare `0` reads as "there are none";
        # what this gate can say is "none in the spellings it recognises", and
        # saying so is what makes the next widening an improvement rather than
        # a defect report.
        print("STORE_READ_SCOPE=recognised spellings only "
              "(subscript, method, qualified call); a floor, not a proof of absence")
        print("STORE_WRITE_SCOPE=recognised spellings only "
              "(method insert/erase/set, qualified RHTable/FrozenMap call); "
              "a floor, not a proof of absence")
        # The whole-table traversals, reported and NOT enforced: a fold or a
        # `toList` is outside the keyed population both zeros are about, and a
        # number beside them is what stops that being read as absence.
        print(f"STORE_SWEEP_CODE={sum(scode.values())}")
        print(f"STORE_SWEEP_SPEC={sum(sspec.values())}")
        print("STORE_SWEEP_SCOPE=whole-table traversals; diagnostic only, never enforced")
        # The population the two zeros cannot see, reported with its floor.  A
        # zero beside an invisible population is worse than a number: it reads as
        # a measurement of absence.
        print(f"STORE_INDIRECT_CODE={sum(icode.values())}")
        print(f"STORE_INDIRECT_SPEC={sum(ispec.values())}")
        print("STORE_INDIRECT_SCOPE=keyed accesses on an object table held through "
              "an indirection -- bound from `.objects` (alias) or taken as a "
              "parameter (param) -- which defeat every receiver-keyed pattern above; "
              "floored per (file, declaration, shape, kind), not enforced at zero. "
              "Three binder spellings are derived (a signature binder, a lambda "
              "binder, an unbracketed ascription) plus the projection binding, "
              "closed transitively. The table's own operations are exempt, derived "
              "from _TABLE_SOURCES and reconciled both ways. Outside it, by "
              "decision: a whole-table SWEEP through an indirection, which the "
              "direct census also reports rather than enforces. Outside it, out of "
              "reach: a table whose receiver has no syntactic provenance in its own "
              "declaration -- an unannotated lambda parameter, a structure field, a "
              "returned closure -- which is an elaborator question and so "
              "unanswerable at Tier 0, where this gate runs")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
