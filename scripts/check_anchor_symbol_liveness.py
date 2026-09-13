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


def module_scope_facts(source: str) -> "tuple[set[str], set[str]]":
    """The names a module BINDS at module scope, and those it READS as globals.

    **Scope resolution is CPython's own** (`symtable`), not a walk over `Name`
    nodes.  A bare identifier is a read of the module's global only when no
    enclosing function binds it, and deciding that by hand is the mistake this
    gate exists to refuse: `def helper(_DEAD): return _DEAD` reads a parameter,
    and counting it as a read of a module-level `_DEAD` suppresses exactly the
    finding this gate is for (PR #895 review round 17).  `symtable` is the
    compiler's own answer, so shadowing by a parameter, a comprehension target,
    a `with`/`except` binding or a nested `def` is not a form to enumerate.
    """
    top = symtable.symtable(source, "<anchor-target>", "exec")
    bound = {sym.get_name() for sym in top.get_symbols()
             if sym.is_assigned() or sym.is_imported()}
    reads: set[str] = set()
    pending = [top]
    while pending:
        table = pending.pop()
        for sym in table.get_symbols():
            if not sym.is_referenced():
                continue
            # At module scope every reference IS the global; inside a function
            # only one `symtable` resolved to the global scope.
            if table.get_type() == "module" or sym.is_global():
                reads.add(sym.get_name())
        pending.extend(table.get_children())
    return bound, reads


def _binding_statement_names(node) -> "set[str]":
    """Names `node` binds, EXCLUDING the imports (which bind deliberately).

    A `Subscript` or `Attribute` target mutates an object and binds no name --
    `os.environ["X"] = "y"` does not rebind `os` -- so those are skipped.  That
    distinction is not cosmetic: counting them reported three rebindings in this
    workspace that do not exist, which is the defect class this gate is about,
    inside the measurement taken to size it.
    """
    def stored(target) -> "set[str]":
        if isinstance(target, ast.Name):
            return {target.id}
        if isinstance(target, (ast.Tuple, ast.List)):
            return {n for e in target.elts for n in stored(e)}
        if isinstance(target, ast.Starred):
            return stored(target.value)
        return set()

    if isinstance(node, ast.Assign):
        return {n for t in node.targets for n in stored(t)}
    if isinstance(node, (ast.AugAssign, ast.AnnAssign, ast.For, ast.AsyncFor)):
        return stored(node.target)
    if isinstance(node, ast.NamedExpr):
        return stored(node.target)
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return {node.name}
    if isinstance(node, ast.ExceptHandler):
        return {node.name} if node.name else set()
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return {n for item in node.items if item.optional_vars
                for n in stored(item.optional_vars)}
    if isinstance(node, (ast.Lambda, ast.FunctionDef, ast.AsyncFunctionDef)):
        return set()
    return set()


def rebound_import_names(tree) -> "set[str]":
    """Import-bound names this module ALSO binds some other way.

    **PR #895 review round 18.**  `module_import_facts` keyed attribute reads by
    the receiver's *spelling*, so

        import subject
        subject = object()
        print(subject.A)

    counted as a read of the target's `A` and kept a dead anchor green.  That is
    fail-**open** in the one direction this gate exists to close: the set it
    builds is a set of *readers*, and a reader it invents keeps a pin alive that
    names nothing.

    Whether a given occurrence still refers to the module is a dataflow question
    -- the import may come before or after the rebinding, on one branch or both
    -- and no scanner decides it.  So the name is refused: the gate stops
    counting reads through it AND reports the form, rather than reading past it.
    That is this project's rule for a scanner that cannot decide, and it costs
    nothing today -- no tracked module rebinds an import alias -- while refusing
    the first one that does.

    Function parameters and comprehension targets are included, because a read
    inside such a scope resolves to the local and `attribute_reads` does not
    record which scope it came from.  Over-refusing is the safe direction here:
    it fails the gate visibly rather than passing silently.
    """
    imported: set[str] = set()
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
    for node in ast.walk(tree):
        rebound |= _binding_statement_names(node) & imported
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            args = node.args
            for arg in (*args.posonlyargs, *args.args, *args.kwonlyargs,
                        args.vararg, args.kwarg):
                if arg is not None and arg.arg in imported:
                    rebound.add(arg.arg)
        elif isinstance(node, (ast.comprehension,)):
            rebound |= _binding_statement_names(ast.Assign(
                targets=[node.target], value=ast.Constant(value=None))) & imported
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
    rebound = rebound_import_names(tree)
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
        return name in global_reads
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
    # ...and the control that keeps the fix from degrading into "an alias with
    # any store nearby never resolves": a subscript or attribute target mutates
    # an object and rebinds no name.
    ("a subscript store on the alias is not a rebinding",
     "A = 1\n",
     "import subject\n\nsubject.table['k'] = 1\n\n\ndef g():\n    return subject.A\n",
     "^A", False),
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
