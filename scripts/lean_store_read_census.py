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
READ = re.compile(r"\.objects(?:\[|\.get\?)")

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|partial\s+|noncomputable\s+|nonrec\s+|scoped\s+|unsafe\s+)*"
    r"(theorem|lemma|def|abbrev|instance|example|structure|inductive|class)\b\s+([^\s:({\[]*)"
)

# Declaration keywords whose contents are propositions whatever their signature.
PROP_KINDS = {"theorem", "lemma", "example", "structure", "inductive", "class"}

PROP_RESULT = re.compile(r":\s*Prop\b")


def code_view(root: Path) -> Path:
    """Materialise the comment-free overlay the AK7 gates read."""
    out = REPO / ".lake" / "build" / "leancodeview"
    subprocess.run(
        [sys.executable, str(REPO / "scripts" / "lean_code_view.py"), "--overlay", str(out)],
        check=True, capture_output=True,
    )
    return out


def classify(path: Path):
    """Yield (declaration, is_prop, occurrences) for each read-bearing line.

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
    for line in lines:
        m = DECL.match(line)
        if m:
            kind, decl = m.group(1), m.group(2) or "<anonymous>"
            signature, sig_open = line, True
        sig_part, body_part = line, ""
        if sig_open:
            if ":=" in line:
                sig_part, body_part = line.split(":=", 1)
                sig_open = False
            if m is None and line.strip():
                signature += " " + line.strip()
            if len(signature) > 4000:
                sig_open = False
        else:
            sig_part, body_part = "", line
        head = signature.split(":=", 1)[0]
        is_prop_decl = kind in PROP_KINDS or bool(PROP_RESULT.search(head))
        n_sig = len(READ.findall(sig_part))
        n_body = len(READ.findall(body_part))
        if n_sig:
            yield decl, True, n_sig          # a binder or result type: a proposition
        if n_body:
            yield decl, is_prop_decl, n_body


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
    """(executable reads, specification reads, registry hits).

    The third is what the registry is reconciled against, so an entry that stops
    naming a raw read is reported rather than silently kept.
    """
    code, spec, exempt_hits = {}, {}, {}
    for f in sorted(view.rglob("SeLe4n/**/*.lean")):
        rel = str(f.relative_to(view))
        for decl, is_prop, n in classify(f):
            if not is_prop and (rel, decl) in ACCESSOR_BODIES:
                exempt_hits[(rel, decl)] = exempt_hits.get((rel, decl), 0) + n
                continue
            bucket = spec if is_prop else code
            bucket[(rel, decl)] = bucket.get((rel, decl), 0) + n
    return code, spec, exempt_hits


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
    # A comment quoting the pattern is not a read.
    "comment_only": ("""
/-- Opens by matching `st.objects[oid]?`. -/
def documented (st : SystemState) : SystemState := st
""", {}, {}),
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
            got_code, got_spec = {}, {}
            for decl, is_prop, n in classify(root / "f.lean"):
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
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    view = code_view(REPO)
    code, spec, exempt_hits = census(view)
    # Reconciled in EVERY mode, `--rows` included: that is the mode the Tier 0
    # baseline calls, so skipping it there would leave the registry checkable
    # only by a command nothing runs — a gate with a silent default branch,
    # which is the shape this project keeps paying for.
    stale = accessor_registry_violations(code, exempt_hits)
    if stale:
        for problem in stale:
            print(f"FAIL: {problem}", file=sys.stderr)
        return 1
    if args.rows:
        for (f, d), n in sorted(code.items()):
            print(f"STORE_READ_CODE_SITE={f}|{d}|{n}")
        for (f, d), n in sorted(spec.items()):
            print(f"STORE_READ_SPEC_SITE={f}|{d}|{n}")
    if args.totals or not args.rows:
        print(f"STORE_READ_CODE={sum(code.values())}")
        print(f"STORE_READ_SPEC={sum(spec.values())}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
