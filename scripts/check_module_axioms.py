#!/usr/bin/env python3
"""Exhaustively verify that every term-level declaration of the named modules
depends only on Lean's three standard axioms.

Why this exists (WS-SM SM8.B, v0.33.6).  The SM8.B landing claimed its axiom
check was exhaustive, but the ad-hoc generator behind it extracted declarations
with a regex anchored at `^(private )?(theorem|def|...)`.  That silently skipped
every declaration carrying an attribute prefix -- `@[simp] theorem ...` -- so
three of a hundred and eighty-four went unchecked.  A regex over source text is
the wrong instrument: it has to re-implement Lean's declaration grammar, and it
fails open when it falls behind.

This script reads `docs/codebase_map.json` instead, which is generated from the
elaborated source and records each declaration's `kind`.  Anything the map calls
a `theorem`/`def`/`abbrev`/`instance` gets a `#print axioms`; the sweep is
therefore exhaustive by construction, and a declaration form nobody anticipated
still lands in the map.

Usage:
    scripts/check_module_axioms.py <Module.Name> [<Module.Name> ...]
    scripts/check_module_axioms.py --all-smp-information-flow

Exit status is non-zero if any declaration depends on a non-standard axiom, if a
module is absent from the map, or if the map is stale with respect to the tree.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MAP = os.path.join(REPO, "docs", "codebase_map.json")

# The three axioms Lean's own `Classical` development introduces.  Anything else
# is a trust-base extension and must fail the gate.
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

# Declaration kinds that name a term and can therefore be probed.  `opaque`,
# `axiom` and `constant` are included deliberately: PR #861 review pointed out
# that an `opaque` whose body reaches an imported non-standard axiom would have
# been skipped while the gate still reported everything clean, and the Tier 0
# textual scan only prevents *declaring* a local `axiom`.
TERM_KINDS = {"theorem", "lemma", "def", "abbrev", "instance",
              "opaque", "axiom", "constant"}

# Kinds that name no term and so have nothing to probe.  Anything the map
# reports that is in neither set is an unrecognised kind and fails the gate
# rather than being silently dropped -- a sweep that quietly ignores a
# declaration form it has not seen before fails open.
NON_TERM_KINDS = {"namespace", "structure", "inductive", "class",
                  "section", "end", "macro", "macro_rules", "syntax",
                  "notation", "elab", "elab_rules", "instance_type",
                  "example", "attribute", "open", "deriving"}

# The WS-SM SM8 information-flow surface, as a convenience selector.
SMP_INFORMATION_FLOW = [
    "SeLe4n.Kernel.InformationFlow.ObservableStatePerCore",
    "SeLe4n.Kernel.InformationFlow.NonInterferencePerCore",
    "SeLe4n.Kernel.InformationFlow.CovertChannelPerCore",
    "SeLe4n.Kernel.InformationFlow.NonInterferenceCrossCore",
]


def load_modules(names: list[str]) -> tuple[dict[str, list[str]], list[str]]:
    """Return (probeable declarations per module, private declarations skipped).

    `#print axioms` cannot name a `private` declaration from another file, so
    those are separated out rather than crashing the probe.  They are not a hole:
    a private helper is by construction used only inside its own module, and
    `#print axioms` on a public consumer reports the union of everything that
    consumer's proof term touches -- so a private helper reaching for a
    non-standard axiom surfaces at whichever public theorem uses it.  A private
    helper used by *nothing* is dead code, which the unused-declaration lint
    covers.  They are printed either way, so the skip is never silent.
    """
    with open(MAP) as fh:
        data = json.load(fh)
    by_name = {m["module"]: m for m in data["modules"]}
    out: dict[str, list[str]] = {}
    skipped: list[str] = []
    for name in names:
        mod = by_name.get(name)
        if mod is None:
            print(f"FAIL: module {name} is absent from docs/codebase_map.json.")
            print("      Regenerate with ./scripts/generate_codebase_map.py "
                  "--pretty --output docs/codebase_map.json")
            sys.exit(2)
        src = open(os.path.join(REPO, mod["path"])).read().splitlines()
        probeable = []
        for d in mod["declarations"]:
            if d["kind"] in NON_TERM_KINDS:
                continue
            if d["kind"] not in TERM_KINDS:
                print(f"FAIL: {name}.{d['name']} has unrecognised declaration "
                      f"kind {d['kind']!r}.  Classify it in TERM_KINDS or "
                      f"NON_TERM_KINDS -- refusing to skip it silently.")
                sys.exit(2)
            line = src[d["line"] - 1] if 0 < d["line"] <= len(src) else ""
            if line.lstrip().startswith("private "):
                skipped.append(f"{name}.{d['name']}")
            else:
                probeable.append(d["name"])
        out[name] = probeable
    return out, skipped


def build_probe(modules: dict[str, list[str]]) -> tuple[str, int]:
    lines = [f"import {name}" for name in modules]
    # Every module in scope opens the same namespaces; declaration names in the
    # map are unqualified, so open the enclosing namespace to resolve them.
    lines.append("open SeLe4n SeLe4n.Model SeLe4n.Kernel")
    total = 0
    for decls in modules.values():
        for d in decls:
            lines.append(f"#print axioms {d}")
            total += 1
    return "\n".join(lines) + "\n", total


def parse(output: str) -> tuple[int, int, list[str]]:
    """Return (with-axioms, axiom-free, offenders).

    Lean wraps long records across lines; a new record always begins with a
    quote at column zero, so split on that rather than on newlines.
    """
    records, current = [], []
    for line in output.splitlines():
        if line.startswith("'") and current:
            records.append(" ".join(current))
            current = [line.strip()]
        else:
            current.append(line.strip())
    if current:
        records.append(" ".join(current))

    dep = free = 0
    offenders = []
    for rec in records:
        rec = " ".join(rec.split())
        if "does not depend on any axioms" in rec:
            free += 1
        elif "depends on axioms" in rec:
            dep += 1
            name = rec.split("'")[1] if "'" in rec else rec[:60]
            inside = rec.split("depends on axioms:", 1)[1].strip()
            inside = inside.lstrip("[").rstrip("]")
            used = {a.strip() for a in inside.split(",") if a.strip()}
            extra = used - ALLOWED
            if extra:
                offenders.append(f"{name}: {sorted(extra)}")
    return dep, free, offenders


def main() -> int:
    args = sys.argv[1:]
    if not args:
        print(__doc__)
        return 2
    names = SMP_INFORMATION_FLOW if args[0] == "--all-smp-information-flow" else args

    modules, skipped = load_modules(names)
    probe, total = build_probe(modules)
    if total == 0:
        print("FAIL: no term-level declarations found -- is the map stale?")
        return 2

    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as fh:
        fh.write(probe)
        probe_path = fh.name
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", probe_path],
            cwd=REPO, capture_output=True, text=True)
    finally:
        os.unlink(probe_path)

    combined = proc.stdout + proc.stderr
    # Match Lean diagnostics by position prefix, not by the bare word "error":
    # declaration names legitimately contain it (`syscallEntry_error_perCore_NI`).
    diag = re.compile(r"^.*\.lean:\d+:\d+: error")
    errors = [ln for ln in combined.splitlines() if diag.match(ln)]
    if errors:
        print("FAIL: the axiom probe did not elaborate.")
        print("      The usual cause is a STALE docs/codebase_map.json: the probe")
        print("      names declarations from the map, so a rename or removal that")
        print("      has not been regenerated produces unknown-identifier errors.")
        print("      Regenerate with ./scripts/generate_codebase_map.py "
              "--pretty --output docs/codebase_map.json")
        for line in errors:
            print("  " + line)
        return 1

    dep, free, offenders = parse(combined)
    checked = dep + free

    for name, decls in modules.items():
        print(f"  {name}: {len(decls)} term-level declarations")
    if skipped:
        print(f"  skipped {len(skipped)} `private` declaration(s), unreachable by "
              f"`#print axioms` from another file (covered transitively by their "
              f"public consumers):")
        for s in skipped:
            print("    " + s)

    if checked != total:
        print(f"FAIL: asked for {total} declarations, Lean reported {checked}.")
        return 1
    if offenders:
        print(f"FAIL: {len(offenders)} declaration(s) use a non-standard axiom:")
        for o in offenders:
            print("  " + o)
        return 1

    print(f"PASS: all {checked} term-level declarations "
          f"({dep} via {{propext, Classical.choice, Quot.sound}}, "
          f"{free} axiom-free) are axiom-clean.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
