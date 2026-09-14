#!/usr/bin/env python3
"""Refuse a Tier 3 anchor that pins a Python symbol nothing reads.

**A pin on a dead symbol is a tautology** (PR #895 review round 16).  Nearly
every anchor in `test_tier3_invariant_surface.sh` is a text scanner asserting
that some construct is present in some file, and an anchor naming a *definition*
keeps reporting PASS after the definition's last consumer goes away -- at which
point it says nothing about the live code at all, while reading in the report
exactly like a check that does.

That is not hypothetical.  Round 16 replaced `classify_extern_item`'s
interior-search body with a leading-form one, which left `_EXTERN_FN_ITEM`,
`_MACRO_INVOCATION` and `_EXTERN_NON_FN_ITEM` with no reader -- and the anchor
`rg -n '^_EXTERN_NON_FN_ITEM'`, whose stated purpose is that the symbol-free
item set lives in the shared view rather than in each gate, went on passing over
a definition the classifier no longer consulted.  The anchor was repointed at
the *read* rather than the definition; this gate is what stops the next one
going dead unnoticed, because a fix applied at one site and not swept onto its
siblings is this project's most-repeated defect.

**What it checks.**  For every `run_check` / `run_negative_check` anchor whose
target is a `.py` file, every identifier the anchor's pattern names that the
target file *binds* must also be *read* somewhere in the tracked Python tree.
Binding-without-reading is the finding.  An identifier the file does not bind is
not a symbol of that file and draws no verdict: an anchor may legitimately name
a string, a comment token or a fragment of prose.

**The default branch is a decision.**  A target file that does not exist, or
that does not parse, fails the gate rather than being skipped: this scanner
builds a set of *checks to validate*, and round 25's rule says a requirement it
drops is a check nobody runs.

Usage:
  check_anchor_symbol_liveness.py              check the tree
  check_anchor_symbol_liveness.py --self-test  run the witness suite
"""

from __future__ import annotations

import ast
import re
import subprocess
import symtable
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import rust_code_view  # noqa: E402

REPO = Path(__file__).resolve().parent.parent

#: The anchor files whose `.py` targets this gate validates.
ANCHOR_FILES = ("scripts/test_tier3_invariant_surface.sh",)

#: A `run_check` / `run_negative_check` line whose last word is a `.py` path.
#: The pattern may be single- or double-quoted; `rg`'s flags sit between.
_ANCHOR = re.compile(
    r"^run_(?:negative_)?check\s+\"[A-Z][A-Z-]*\"\s+rg\s+(?:-[-\w]+\s+)*"
    r"(?:'(?P<sq>[^']*)'|\"(?P<dq>[^\"]*)\")\s+(?P<path>\S+\.py)\s*$",
    re.M)

#: A candidate identifier inside an anchor pattern.
#:
#: Python's identifier grammar is UAX#31, the same one Rust uses, and an
#: ASCII class UNDER-matches it -- which here is fail-**open**, since a name
#: the scan never extracts is a pin nobody checks (PR #895 review round 18).
_IDENT = re.compile(rust_code_view.ident())


def anchors_in(text: str) -> list[tuple[str, str]]:
    """The `(pattern, target path)` pairs of every `.py`-targeting anchor."""
    out = []
    for m in _ANCHOR.finditer(text):
        out.append((m.group("sq") if m.group("sq") is not None else m.group("dq"),
                    m.group("path")))
    return out


def module_scope_facts(source: str) -> "tuple[set[str], dict[str, set[str]]]":
    """The names a module BINDS at module scope, and who READS each as a global.

    **Scope resolution is CPython's own** (`symtable`), not a walk over `Name`
    nodes.  A bare identifier is a read of the module's global only when no
    enclosing function binds it, and deciding that by hand is the mistake this
    gate exists to refuse: `def helper(_DEAD): return _DEAD` reads a parameter,
    and counting it as a read of a module-level `_DEAD` suppresses exactly the
    finding this gate is for (PR #895 review round 17).  `symtable` is the
    compiler's own answer, so shadowing by a parameter, a comprehension target,
    a `with`/`except` binding or a nested `def` is not a form to enumerate.

    **...and a reference is not an incoming read** (PR #895 review round 22).
    The reads were returned as a flat SET, and the gate then asked "does this
    name occur as a global read" where its question is "does anything else read
    it" — this project's oldest rule, a presence check standing in for a
    relation, inside the gate written to retire a different instance of it.  A
    recursive definition references its own name from inside its own body, so
    `def _dead(n): return _dead(n - 1)` put `_dead` in the set and kept a Tier 3
    anchor on a helper nothing calls reading LIVE.  That is the tautological pin
    this gate exists to refuse, surviving the refusal.

    So each read is **attributed** to the declaration it occurs in — the name of
    the nearest enclosing `def`/`class`, or `""` for module scope — and the
    target route below asks for an owner other than the name itself.  Nesting is
    carried, so a reference from a closure inside `_dead` is still `_dead`'s: if
    nothing outside the definition calls it, nothing does.

    What attribution does **not** decide is a CYCLE: two definitions that
    reference each other and nothing else reads still own each other's reads, so
    they read live.  That is over-approximating liveness, which for this gate is
    the fail-OPEN direction, and it is stated rather than assumed away —
    deciding it is reachability from an entry point, and the entry points here
    include cross-module readers, so a module-scope-only seed would report every
    helper of an imported function dead.  A mutual pair of dead anchored
    definitions is the residue.
    """
    top = symtable.symtable(source, "<anchor-target>", "exec")
    bound = {sym.get_name() for sym in top.get_symbols()
             if sym.is_assigned() or sym.is_imported()}
    reads: dict[str, set[str]] = {}
    # `(table, owner)` — the owner is the nearest enclosing declaration's name,
    # inherited by nested tables so a closure's reference is attributed to the
    # declaration it is written inside.
    pending = [(top, "")]
    while pending:
        table, owner = pending.pop()
        for sym in table.get_symbols():
            if not sym.is_referenced():
                continue
            # At module scope every reference IS the global; inside a function
            # only one `symtable` resolved to the global scope.
            if table.get_type() == "module" or sym.is_global():
                reads.setdefault(sym.get_name(), set()).add(owner)
        for child in table.get_children():
            child_owner = owner
            if child.get_type() in ("function", "class") and not owner:
                child_owner = child.get_name()
            pending.append((child, child_owner))
    return bound, reads


def rebound_import_names(source: str) -> "set[str]":
    """Import-bound names this module ALSO binds some other way.

    **PR #895 review round 20.**  Round 18 answered this with a hand-written
    `ast` walk over the binding constructs it had thought of, and the review
    supplied one it had not — a `match` capture, `case subject:`.  Measuring
    the walk rather than patching the reported cell found the shape: it
    handled *every* binder Python had before PEP 634 (assignment, augmented
    and annotated, `for`, `with ... as`, `except ... as`, the walrus, `def`
    and `class`) and **none** of structural pattern matching's, which is a
    whole family — `MatchAs` bare and after a class pattern, `MatchStar`, a
    `MatchMapping` rest — four forms, not the one reported.  None binds
    through a `Name` in `Store` context, so none was collected, and
    `module_import_facts` kept the import mapping while the receiver denoted
    something else.  That is fail-**open** here: the gate builds a set of
    *readers*, and one it invents keeps a pin alive that names nothing.

    The lesson is not that four beats one; it is that an enumeration of a
    language's binders is a list of the ones that existed when it was written,
    so the next grammar addition silently empties it.  **CPython already
    answers this**: `symtable` reports `is_assigned()` **False** for a name
    bound only by an import and **True** the moment anything else binds it —
    measured across all eleven forms above plus the `subject.table[k] = v` and
    `subject.x = v` controls, which bind no name and correctly read False.
    Round 18's own rule (*check whether the exact answer is already in reach*)
    applied to the gate round 18 wrote: the oracle was imported in that very
    cut, for scope resolution, and asked nothing about binding.

    Parameters are counted too (`is_parameter`, which `is_assigned` does not
    imply): a read inside a scope that shadows the alias resolves to the
    parameter, and `attribute_reads` does not record which scope a read came
    from, so the fail-closed answer is to refuse the receiver.  Over-refusing
    fails the gate visibly; under-refusing passes it silently.
    """
    imported: set[str] = set()
    tree = ast.parse(source)
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                imported.add(alias.asname or alias.name.split(".")[0])
        elif isinstance(node, ast.ImportFrom):
            for alias in node.names:
                if alias.name != "*":
                    imported.add(alias.asname or alias.name)
    if not imported:
        return set()
    rebound: set[str] = set()
    pending = [symtable.symtable(source, "<rebinding-scan>", "exec")]
    while pending:
        table = pending.pop()
        for sym in table.get_symbols():
            name = sym.get_name()
            if name in imported and (sym.is_assigned() or sym.is_parameter()):
                rebound.add(name)
        pending.extend(table.get_children())
    return rebound


def module_import_facts(source: str):
    """How a module names OTHER modules, and which attributes it reads on them.

    Returns `(module_aliases, from_imports, attribute_reads, unresolved)`:
    the local name each imported module is bound to, the `(module, symbol)` each
    `from`-imported name stands for, the attributes read on each receiver name,
    and the import forms this scanner declines to resolve.

    `unresolved` is the explicit default branch (PR #889 review round 25): a
    star import publishes names no scanner can attribute, and a dotted import
    binds only its first component, so either could hide a reader.  They are
    reported rather than read past — but only when they could reach a target,
    which is why the caller filters them by stem.
    """
    tree = ast.parse(source)
    module_aliases: dict[str, str] = {}
    from_imports: dict[str, tuple[str, str]] = {}
    attribute_reads: dict[str, set[str]] = {}
    unresolved: list[str] = []
    rebound = rebound_import_names(source)
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                parts = alias.name.split(".")
                if len(parts) > 1:
                    unresolved.append(f"dotted import {alias.name}")
                    continue
                module_aliases[alias.asname or parts[0]] = parts[0]
        elif isinstance(node, ast.ImportFrom):
            if node.level:
                unresolved.append("relative import")
                continue
            stem = (node.module or "").split(".")[-1]
            for alias in node.names:
                if alias.name == "*":
                    unresolved.append(f"star import from {stem}")
                    continue
                from_imports[alias.asname or alias.name] = (stem, alias.name)
        elif isinstance(node, ast.Attribute) and isinstance(node.ctx, ast.Load):
            if isinstance(node.value, ast.Name):
                attribute_reads.setdefault(node.value.id, set()).add(node.attr)
    # A name bound both by an import and by something else names the module at
    # some occurrences and not at others, and which is which is a dataflow
    # question (PR #895 review round 18).  Drop it from BOTH resolution routes
    # and report the form: the read stops counting, so the gate cannot be kept
    # green by a rebound receiver, and the form names the stem so an anchor on
    # that target fails visibly rather than the refusal being silent.
    for local in sorted(rebound):
        stem = module_aliases.pop(local, None)
        if stem is not None:
            unresolved.append(f"rebound import alias {local} for {stem}")
        origin = from_imports.pop(local, None)
        if origin is not None:
            unresolved.append(
                f"rebound `from` import {local} of {origin[1]} from {origin[0]}")
    return module_aliases, from_imports, attribute_reads, unresolved


def reads_target_symbol(facts, target_stem: str, name: str, is_target: bool) -> bool:
    """Does this module read `target_stem`'s module-level `name`?

    Three ways, and a bare identifier that matches none of them is **not** a
    read of that symbol -- which is the whole correction: a global union over
    every tracked module let an unrelated local of the same spelling keep a dead
    anchor green.
    """
    _, global_reads, module_aliases, from_imports, attribute_reads = facts
    if is_target:
        # An owner other than the name itself: a definition's references to
        # itself are not an incoming read of it.
        return any(owner != name for owner in global_reads.get(name, ()))
    for alias, stem in module_aliases.items():
        if stem == target_stem and name in attribute_reads.get(alias, ()):
            return True
    for local, (stem, original) in from_imports.items():
        if stem == target_stem and original == name and local in global_reads:
            return True
    return False


def tracked_python(repo: Path) -> list[Path]:
    """Every tracked `.py` file -- the domain a reader may live in.

    Derived from the index rather than globbed: a reader in a directory nobody
    thought to name is still a reader.
    """
    out = subprocess.run(["git", "ls-files", "-z", "*.py"], cwd=repo,
                         capture_output=True, text=True, check=True).stdout
    return [repo / name for name in out.split("\0") if name]


def dead_anchor_pins(repo: Path, anchor_files=ANCHOR_FILES):
    """`(anchor file, target, symbol, reason)` for every pin this gate refuses."""
    facts: dict[str, tuple] = {}
    unreadable: list[tuple[str, str]] = []
    for path in tracked_python(repo):
        try:
            source = path.read_text(encoding="utf-8")
            bound, global_reads = module_scope_facts(source)
            aliases, from_imports, attribute_reads, unresolved = module_import_facts(source)
        except (SyntaxError, ValueError, UnicodeDecodeError) as exc:
            unreadable.append((path.name, str(exc)))
            continue
        facts[path.name] = (bound, global_reads, aliases, from_imports, attribute_reads)
        for form in unresolved:
            unreadable.append((path.name, form))

    findings = []
    for anchor_file in anchor_files:
        text = (repo / anchor_file).read_text(encoding="utf-8")
        for pattern, target in anchors_in(text):
            path = repo / target
            if not path.exists():
                findings.append((anchor_file, target, "-", "target file missing"))
                continue
            if path.name not in facts:
                reason = next((why for name, why in unreadable if name == path.name),
                              "target unparseable")
                findings.append((anchor_file, target, "-", f"target unreadable: {reason}"))
                continue
            target_stem = path.stem
            # An import form this scanner declines to resolve could hide a
            # reader of THIS target, so it fails the gate rather than being read
            # past -- but only when it names the target, since an unrelated
            # dotted import cannot reach it.
            for name, form in unreadable:
                if target_stem in form:
                    findings.append((anchor_file, target, "-",
                                     f"{name}: unresolved import form ({form})"))
            bound = facts[path.name][0]
            for name in sorted(set(_IDENT.findall(pattern))):
                if name not in bound:
                    continue
                if any(reads_target_symbol(f, target_stem, name, module == path.name)
                       for module, f in facts.items()):
                    continue
                findings.append((anchor_file, target, name,
                                 "anchored and defined, but read nowhere"))
    return findings


# ---------------------------------------------------------------------------
# Self-test.
#
# Every case KEEPS the anchor and changes only the RELATION -- whether the
# symbol it names has a reader -- because a case that deletes the anchor is
# passed by any scanner that merely counts them.
# ---------------------------------------------------------------------------

#: `(label, subject module, consumer module, anchor pattern, expect a finding)`.
#:
#: The axes are the ways a module-level symbol can be READ (PR #895 review round
#: 17): from the target itself, as an attribute on the imported module (plain or
#: aliased), or through a `from` import -- crossed with the ways a bare
#: identifier of the same spelling is NOT a read of it.  Enumerating the routes
#: rather than the reported spelling is this project's own rule for a case list.
_CASES = [
    # --- the symbol is genuinely read, by each route ---------------------
    ("a symbol its own module reads is live",
     "A = 1\ndef f():\n    return A\n", "", "^A", False),
    ("a symbol read as an attribute on a plain import is live",
     "A = 1\n", "import subject\n\n\ndef g():\n    return subject.A\n", "^A", False),
    ("a symbol read through an ALIASED import is live",
     "A = 1\n", "import subject as _s\n\n\ndef g():\n    return _s.A\n", "^A", False),
    ("a symbol read through a `from` import is live",
     "A = 1\n", "from subject import A\n\n\ndef g():\n    return A\n", "^A", False),
    # --- ...and the ways a matching bare name is NOT a read of it ---------
    # The round-17 finding: a global union over every tracked module let an
    # unrelated local of the same spelling keep a dead anchor green.
    ("an unrelated module's PARAMETER of the same name is not a read",
     "A = 1\n", "def helper(A):\n    return A + 1\n", "^A", True),
    ("an unrelated module's local binding of the same name is not a read",
     "A = 1\n", "def helper():\n    A = 2\n    return A\n", "^A", True),
    # ...and the same defect one level in, which `symtable` closes for free:
    # a parameter in the TARGET's own module shadows the global it matches.
    ("a parameter in the target's own module is not a read of the global",
     "A = 1\n\n\ndef helper(A):\n    return A\n", "", "^A", True),
    ("a comprehension target in the target's own module is not a read",
     "A = 1\n\n\ndef helper():\n    return [A for A in range(3)]\n", "", "^A", True),
    # --- ...and a SELF-reference is not an incoming read (round 22) -------
    # The flat read set answered "does this name occur as a global read", where
    # the question is "does anything else read it" -- so a recursive definition
    # kept its own anchor alive.  Each row keeps the definition and the anchor
    # and changes only WHO references the name, which is the mutation this class
    # needs; deleting the reference passes under the superseded set.
    ("a recursive definition nothing else calls is NOT read",
     "def _A(n):\n    return _A(n - 1)\n", "", "^_A", True),
    ("...nor when the self-reference is written inside a closure",
     "def _A(n):\n    def inner():\n        return _A(n - 1)\n    return inner\n",
     "", "^_A", True),
    ("...and the same holds for a self-referential class",
     "class _A:\n    def clone(self):\n        return _A()\n", "", "^_A", True),
    # ...and the rows the fix must NOT change: a real caller makes it live,
    # whether it recurses or not.
    ("a recursive definition WITH a caller is live",
     "def _A(n):\n    return _A(n - 1)\n\n\ndef main():\n    return _A(3)\n",
     "", "^_A", False),
    ("a module-scope reference is an incoming read",
     "def _A(n):\n    return n\n\n\n_USED = _A(1)\n", "", "^_A", False),
    ("a caller in ANOTHER module is still an incoming read",
     "def _A(n):\n    return _A(n - 1)\n",
     "import subject\n\n\ndef g():\n    return subject._A(2)\n", "^_A", False),
    # A `from` import of a DIFFERENT module's same-named symbol is not a read
    # of this target's -- the route exists but does not resolve here.
    ("a `from` import of another module's same name is not a read",
     "A = 1\n", "from elsewhere import A\n\n\ndef g():\n    return A\n", "^A", True),
    # An attribute of that name on something that is not the target module.
    ("an attribute of the same name on another receiver is not a read",
     "A = 1\n", "import os\n\n\ndef g():\n    return os.A\n", "^A", True),
    # --- a receiver that no longer names the module (round 18) ------------
    # Each KEEPS the import and the attribute read and changes only whether the
    # receiver still denotes the module, which is the mutation that finds this
    # class: a case that deletes the import passes under the superseded scan.
    ("a read through a REBOUND module alias is not a read",
     "A = 1\n",
     "import subject\n\nsubject = object()\n\n\ndef g():\n    return subject.A\n",
     "^A", True),
    ("a read through a REBOUND `from` import is not a read",
     "A = 1\n",
     "from subject import A\n\nA = 5\n\n\ndef g():\n    return A\n",
     "^A", True),
    ("a parameter shadowing the alias refuses the receiver",
     "A = 1\n",
     "import subject\n\n\ndef g(subject):\n    return subject.A\n",
     "^A", True),
    # --- the binder family the round-18 enumeration missed (round 20) ------
    # The review reported ONE cell (`case subject:`); the family is four, and
    # they are enumerated here rather than the reported cell alone, because a
    # witness drawn from a finding tests the finding.  All four are structural
    # pattern matching's binders: none binds through a `Name` in `Store`
    # context, so the hand-written walk collected none of them and kept the
    # import mapping over a receiver that denotes something else.  `symtable`
    # answers every one without being told it exists, which is why the
    # enumeration is gone rather than extended.
    ("a `match` capture rebinding the alias refuses the receiver",
     "A = 1\n",
     "import subject\n\n\ndef g(v):\n    match v:\n        case subject:\n"
     "            return subject.A\n",
     "^A", True),
    ("a `match` star capture rebinding the alias refuses the receiver",
     "A = 1\n",
     "import subject\n\n\ndef g(v):\n    match v:\n        case [*subject]:\n"
     "            return subject.A\n",
     "^A", True),
    ("a `match` mapping rest rebinding the alias refuses the receiver",
     "A = 1\n",
     "import subject\n\n\ndef g(v):\n    match v:\n        case {'k': 1, **subject}:\n"
     "            return subject.A\n",
     "^A", True),
    ("a `match` class capture rebinding the alias refuses the receiver",
     "A = 1\n",
     "import subject\n\n\ndef g(v):\n    match v:\n        case int() as subject:\n"
     "            return subject.A\n",
     "^A", True),
    # ...and two the round-18 walk DID handle, kept as the rows that say so:
    # the fix must be shown to be a generalisation, not a different rule that
    # happens to cover the reported cell.
    ("a walrus rebinding the alias refuses the receiver",
     "A = 1\n",
     "import subject\n\n\ndef g(v):\n    if (subject := v):\n"
     "        return subject.A\n",
     "^A", True),
    ("an `except ... as` rebinding the alias refuses the receiver",
     "A = 1\n",
     "import subject\n\n\ndef g():\n    try:\n        pass\n"
     "    except ValueError as subject:\n        return subject.A\n",
     "^A", True),
    # ...and the control that keeps the fix from degrading into "an alias with
    # any store nearby never resolves": a subscript or attribute target mutates
    # an object and rebinds no name.
    ("a subscript store on the alias is not a rebinding",
     "A = 1\n",
     "import subject\n\nsubject.table['k'] = 1\n\n\ndef g():\n    return subject.A\n",
     "^A", False),
    # ...and the row that pins the query's DIRECTION where it is inexact.  A
    # whole-module query answers for every scope, so a same-named local in an
    # unrelated function refuses a module-scope receiver that really does denote
    # the import.  That is the over-approximation the docstring declares -- the
    # exact answer needs each attribute read attributed to its own scope, which
    # `attribute_reads` does not record -- and it is taken deliberately, because
    # the alternative (ask the module scope alone) is fail-OPEN for a shadowed
    # read, which is the very thing this gate exists to catch.  Measured before
    # choosing: across all 31 tracked `.py` files, zero import-bound names are
    # assigned at module scope and zero at nested scope, so the two queries
    # agree on the whole tree and the conservative one costs it nothing.
    ("a nested-scope binding of the alias refuses the receiver (fail-closed)",
     "A = 1\n",
     "import subject\n\n\ndef other():\n    subject = 1\n    return subject\n"
     "\n\ndef g():\n    return subject.A\n",
     "^A", True),
    # --- the domain, not the predicate -----------------------------------
    ("a name the module does not bind draws no verdict",
     "A = 1\ndef f():\n    return A\n", "", "some prose the file mentions", False),
]

def _self_test() -> int:
    import tempfile

    failures = []
    ran = 0

    def check(label: str, ok: bool, detail: str = "") -> None:
        nonlocal ran
        ran += 1
        print(f"  {'OK  ' if ok else 'FAIL'} {label}" + (f": {detail}" if not ok and detail else ""))
        if not ok:
            failures.append(label)

    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / "scripts").mkdir()
        subprocess.run(["git", "init", "-q"], cwd=root, check=True)
        for label, subject, consumer, pattern, want in _CASES:
            (root / "scripts" / "subject.py").write_text(subject)
            (root / "scripts" / "consumer.py").write_text(consumer)
            (root / "scripts" / "anchors.sh").write_text(
                f"run_check \"INVARIANT\" rg -n '{pattern}' scripts/subject.py\n")
            subprocess.run(["git", "add", "-A"], cwd=root, check=True,
                           capture_output=True)
            got = dead_anchor_pins(root, ("scripts/anchors.sh",))
            check(label, bool(got) == want, f"got {got}")

        # The default branch is a decision, in each of its shapes.
        (root / "scripts" / "subject.py").write_text("A = 1\n")
        (root / "scripts" / "consumer.py").write_text("")
        (root / "scripts" / "anchors.sh").write_text(
            "run_check \"INVARIANT\" rg -n '^A' scripts/gone.py\n")
        subprocess.run(["git", "add", "-A"], cwd=root, check=True, capture_output=True)
        check("a missing target fails rather than being skipped",
              any("missing" in f[3] for f in dead_anchor_pins(root, ("scripts/anchors.sh",))))
        (root / "scripts" / "subject.py").write_text("def f(:\n")
        (root / "scripts" / "anchors.sh").write_text(
            "run_check \"INVARIANT\" rg -n '^A' scripts/subject.py\n")
        subprocess.run(["git", "add", "-A"], cwd=root, check=True, capture_output=True)
        check("an unparseable target fails rather than being skipped",
              any("unreadable" in f[3] for f in dead_anchor_pins(root, ("scripts/anchors.sh",))))
        # An import form this scanner declines to resolve could hide a reader of
        # the target, so it fails rather than reading past it -- and only when
        # it names the target, since an unrelated one cannot reach it.
        (root / "scripts" / "subject.py").write_text("A = 1\ndef f():\n    return A\n")
        (root / "scripts" / "consumer.py").write_text("from subject import *\n")
        subprocess.run(["git", "add", "-A"], cwd=root, check=True, capture_output=True)
        check("a star import naming the target fails the gate",
              any("unresolved import form" in f[3]
                  for f in dead_anchor_pins(root, ("scripts/anchors.sh",))))
        (root / "scripts" / "consumer.py").write_text("import importlib.util\n")
        subprocess.run(["git", "add", "-A"], cwd=root, check=True, capture_output=True)
        check("an unrelated dotted import does not fail the gate",
              not dead_anchor_pins(root, ("scripts/anchors.sh",)))

    # The anchor parser itself: a `.py` target is recognised in both quotings
    # and past `rg`'s flags, and a non-`.py` target is not this gate's business.
    found = anchors_in(
        "run_check \"INVARIANT\" rg -n '^A' scripts/x.py\n"
        "run_negative_check \"NEGATIVE\" rg -nF \"B\" scripts/y.py\n"
        "run_check \"INVARIANT\" rg -n 'C' SeLe4n/Z.lean\n")
    check("anchors are parsed in both quotings, and only for .py targets",
          found == [("^A", "scripts/x.py"), ("B", "scripts/y.py")], str(found))

    if failures:
        print(f"\n[anchor-symbol-liveness] self-test: {len(failures)} case(s) failed")
        return 1
    # Counted from the checks that RAN, never `len(_CASES) + <n>`: a
    # hand-kept figure beside a derivation is what this project keeps paying
    # for, and this one was already wrong by two the moment cases were added.
    print(f"[anchor-symbol-liveness] self-test passed ({ran} cases)")
    return 0


def main(argv: list[str]) -> int:
    if argv and argv[0] == "--self-test":
        return _self_test()
    findings = dead_anchor_pins(REPO)
    if findings:
        print("[anchor-symbol-liveness] FAIL: anchors pinning symbols nothing reads")
        for anchor_file, target, name, why in findings:
            print(f"  {anchor_file}: {target}: {name}: {why}")
        print("\nA pin on a dead symbol reports PASS whatever the live code does.")
        print("Repoint the anchor at the symbol's READ, or delete the symbol.")
        return 1
    total = sum(len(anchors_in((REPO / f).read_text(encoding="utf-8")))
                for f in ANCHOR_FILES)
    print(f"[anchor-symbol-liveness] OK: {total} anchor(s) over Python targets, "
          f"every pinned symbol has a reader")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
