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

`private` declarations cannot be named from another file, so they are probed by
re-elaborating their own module's source with the probes appended.  They are not
skipped: an earlier form of this script excluded them on the strength of an
"unused-declaration lint" that does not exist in this repository (PR #861
review), which made a private declaration with no public consumer an exercised
fail-open path.

Exit status is non-zero if any declaration depends on a non-standard axiom, if a
module is absent from the map, if the map presents a declaration kind neither
set classifies, or if the map is stale with respect to the tree.
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

    `#print axioms` cannot name a `private` declaration from *another* file, so
    they are collected separately and probed by `probe_private` below, which
    elaborates the module's own source with the probes appended -- inside the
    defining module the names are in scope.

    They are NOT waved through.  An earlier form of this script skipped them,
    arguing that a public consumer's `#print axioms` would surface any bad axiom
    a private helper reached and that an unused private helper is dead code
    "which the unused-declaration lint covers".  PR #861 review established that
    no such lint exists in this repository, so that was a false justification
    for an exercised fail-open path: a private declaration with no public
    consumer would have been dropped from both the probe and the total while the
    gate still reported everything clean.
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


def probe_private(names: list[str]) -> tuple[str, int]:
    """Probe `private` declarations by elaborating each defining module's own
    source with `#print axioms` appended.

    Costs a re-elaboration of the module, which is why only modules that
    actually declare private terms are re-run.  It is the only way to name a
    private declaration: Lean mangles the real name, and `open private` is a
    Mathlib command this toolchain does not carry.
    """
    with open(MAP) as fh:
        data = json.load(fh)
    by_name = {m["module"]: m for m in data["modules"]}

    by_module: dict[str, list[str]] = {}
    for qualified in names:
        mod, _, decl = qualified.rpartition(".")
        by_module.setdefault(mod, []).append(decl)

    combined, total = "", 0
    for mod, decls in by_module.items():
        src_path = os.path.join(REPO, by_name[mod]["path"])
        body = open(src_path).read()
        body += ("\n\n-- axiom probe (appended by scripts/check_module_axioms.py)\n"
                 "open SeLe4n SeLe4n.Model SeLe4n.Kernel\n")
        for d in decls:
            body += f"#print axioms {d}\n"
            total += 1
        with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as fh:
            fh.write(body)
            path = fh.name
        try:
            proc = subprocess.run(["lake", "env", "lean", path],
                                  cwd=REPO, capture_output=True, text=True)
        finally:
            os.unlink(path)
        combined += proc.stdout + proc.stderr
    return combined, total


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

    priv_out, priv_total = ("", 0)
    if skipped:
        priv_out, priv_total = probe_private(skipped)
        priv_errors = [ln for ln in priv_out.splitlines() if diag.match(ln)]
        if priv_errors:
            print("FAIL: the private-declaration probe did not elaborate.")
            for line in priv_errors:
                print("  " + line)
            return 1

    dep, free, offenders = parse(combined + priv_out)
    checked = dep + free
    total += priv_total

    for name, decls in modules.items():
        print(f"  {name}: {len(decls)} term-level declarations")
    if skipped:
        print(f"  probed {len(skipped)} `private` declaration(s) inside their "
              f"defining module (not reachable by name from another file):")
        for p in skipped:
            print("    " + p)

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
