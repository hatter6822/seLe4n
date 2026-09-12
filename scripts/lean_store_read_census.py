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

# A raw read is a subscript of the object table.  `.objects.insert` is a write
# and is a different question (STOREOBJECTCHECKED_ADOPTION asks it).
READ = re.compile(r"\.objects\[")

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


def census(view: Path):
    code, spec = {}, {}
    for f in sorted(view.rglob("SeLe4n/**/*.lean")):
        rel = str(f.relative_to(view))
        # `Model/State.lean` defines the accessors; the raw read is their body.
        if rel == "SeLe4n/Model/State.lean":
            continue
        for decl, is_prop, n in classify(f):
            bucket = spec if is_prop else code
            bucket[(rel, decl)] = bucket.get((rel, decl), 0) + n
    return code, spec


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
    code, spec = census(view)
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
