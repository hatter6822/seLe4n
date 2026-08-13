#!/usr/bin/env python3
"""Exhaustively verify that every constant the named modules add to Lean's
environment depends only on Lean's three standard axioms.

Why this exists, and why it was rewritten twice (WS-SM SM8.B).

The SM8.B landing claimed an exhaustive axiom check, but the generator behind
it extracted declarations with a regex anchored at
`^(private )?(theorem|def|...)`, which silently skipped every declaration
carrying an attribute prefix (`@[simp] theorem ...`).  That was replaced by a
sweep driven off `docs/codebase_map.json`, described as "generated from the
elaborated source" and therefore "exhaustive by construction".

**That description was false, and PR #861 review round 5 caught it.**
`scripts/generate_codebase_map.py` builds the map with a line-oriented
`DECL_HEAD_RE` over source text — it never consults Lean's environment.  So the
map sees the *syntax* a file contains, not the *constants* the file produces:
a `macro_rules`/`elab` command that generates a theorem contributes only the
macro invocation to the map, and the generated constant is absent from both the
probe and the total.  Such a constant can reach an imported non-standard axiom
without the textual `axiom` keyword appearing anywhere, leaving every gate
green.  The gap is not hypothetical in size: on the SM8 information-flow
surface the map lists 442 declarations while the environment holds 1359
constants for the same four modules — equation lemmas, match auxiliaries,
instance projections and other elaborator output that no source regex sees.

This version therefore enumerates **Lean's own environment**.  It elaborates a
generated file that imports the target modules and walks `env.constants`,
keeping every constant whose defining module (`Environment.getModuleIdxFor?`)
is one of the targets, and calls `Lean.collectAxioms` on each.  There is no
filtering by declaration kind, by name shape, or by privacy: a constant that
exists in the compiled module is swept, however it got there.  Exhaustiveness
is now a property of the mechanism rather than a claim about a source scanner.

The map is still read, but only to report the source-declaration count
alongside the environment count, so the difference stays visible rather than
being mistaken for agreement.

Usage:
    scripts/check_module_axioms.py <Module.Name> [<Module.Name> ...]
    scripts/check_module_axioms.py --all-smp-information-flow

Exit status is non-zero if any constant depends on a non-standard axiom, if the
generated probe fails to elaborate, or if the sweep reports no constants at all.
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

# The three axioms Lean's own `Classical` development introduces.  Anything
# else is a trust-base extension and must fail the gate.
ALLOWED = ["propext", "Classical.choice", "Quot.sound"]

# The WS-SM SM8 information-flow surface, as a convenience selector.
SMP_INFORMATION_FLOW = [
    "SeLe4n.Kernel.InformationFlow.ObservableStatePerCore",
    "SeLe4n.Kernel.InformationFlow.NonInterferencePerCore",
    "SeLe4n.Kernel.InformationFlow.CovertChannelPerCore",
    "SeLe4n.Kernel.InformationFlow.NonInterferenceCrossCore",
    "SeLe4n.Kernel.InformationFlow.DeclassificationPerCore",
]

PROBE_TEMPLATE = """@IMPORTS@
import Lean.Elab.Command

open Lean Elab Command

private def axiomSweepTargets : List Name :=
  [@TARGETS@]

private def axiomSweepAllowed : List Name :=
  [@ALLOWED@]

run_cmd do
  let env ← getEnv
  let mut total := 0
  let mut free := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (n, _ci) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | none => pure ()
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      if axiomSweepTargets.contains m then
        total := total + 1
        let axs ← liftCoreM (Lean.collectAxioms n)
        if axs.isEmpty then free := free + 1
        let extra := axs.filter (fun a => !axiomSweepAllowed.contains a)
        if !extra.isEmpty then bad := bad.push (n, extra)
  logInfo m!"AXIOMSWEEP_TOTAL {total}"
  logInfo m!"AXIOMSWEEP_FREE {free}"
  for (n, e) in bad do
    logInfo m!"AXIOMSWEEP_BAD {n} {e}"
  logInfo m!"AXIOMSWEEP_BADCOUNT {bad.size}"
"""


def map_declaration_counts(names: list[str]) -> dict[str, int]:
    """Source-declaration counts, reported for contrast only.

    Deliberately NOT the sweep's input: the map is a source scan, and the whole
    point of this rewrite is that a source scan cannot see elaborator output.
    """
    try:
        with open(MAP) as fh:
            data = json.load(fh)
    except (OSError, ValueError):
        return {}
    by_name = {m["module"]: m for m in data.get("modules", [])}
    return {n: len(by_name[n]["declarations"]) for n in names if n in by_name}


def build_probe(names: list[str]) -> str:
    return (PROBE_TEMPLATE
            .replace("@IMPORTS@", "\n".join(f"import {n}" for n in names))
            .replace("@TARGETS@", "\n  , ".join(f"`{n}" for n in names))
            .replace("@ALLOWED@", ", ".join(f"`{a}" for a in ALLOWED)))


def main() -> int:
    args = sys.argv[1:]
    if not args:
        print(__doc__)
        return 2
    names = SMP_INFORMATION_FLOW if args[0] == "--all-smp-information-flow" else args

    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as fh:
        fh.write(build_probe(names))
        probe_path = fh.name
    try:
        proc = subprocess.run(["lake", "env", "lean", probe_path],
                              cwd=REPO, capture_output=True, text=True)
    finally:
        os.unlink(probe_path)

    combined = proc.stdout + proc.stderr
    # PR #861 review round 12: **any** nonzero exit is a failure, checked before
    # the summary is parsed.  `lake` can fail before Lean runs at all (no
    # toolchain, a broken manifest, an unbuildable dependency), and it can fail
    # *after* the `run_cmd` sweep has already printed `AXIOMSWEEP_BADCOUNT 0` —
    # a kill signal, or a later driver failure.  Either way the position regex
    # below matches nothing, so without this the script would parse the
    # already-emitted zero and report PASS on a run that did not complete.  A
    # fail-closed proof-surface gate cannot do that, so the exit code decides
    # first and the captured diagnostics are printed either way.
    if proc.returncode != 0:
        print(f"FAIL: the axiom probe exited {proc.returncode}.  A nonzero exit is")
        print("      rejected before the sweep summary is read: the probe may have")
        print("      printed a summary and then died, and a partial run proves")
        print("      nothing about the constants it never reached.")
        print(combined[-4000:] or "      (no output)")
        return 1
    # Match Lean diagnostics by position prefix, not by the bare word "error":
    # declaration names legitimately contain it (`syscallEntry_error_perCore_NI`).
    diag = re.compile(r"^.*\.lean:\d+:\d+: error")
    errors = [ln for ln in combined.splitlines() if diag.match(ln)]
    if errors:
        print("FAIL: the environment axiom probe did not elaborate.")
        print("      The usual cause is a module that does not build, or a")
        print("      module name that does not exist.  Full diagnostics:")
        for line in errors:
            print("  " + line)
        return 1

    def scalar(tag: str) -> int | None:
        m = re.search(rf"AXIOMSWEEP_{tag} (\d+)", combined)
        return int(m.group(1)) if m else None

    total, free, badcount = scalar("TOTAL"), scalar("FREE"), scalar("BADCOUNT")
    if total is None or free is None or badcount is None:
        print("FAIL: the probe elaborated but produced no sweep summary.")
        print(combined[-2000:])
        return 1
    if total == 0:
        print("FAIL: the sweep found no constants — are the module names right?")
        return 1

    source_counts = map_declaration_counts(names)
    for name in names:
        src = source_counts.get(name)
        suffix = f" ({src} source declarations in the map)" if src is not None else ""
        print(f"  {name}{suffix}")

    if badcount:
        print(f"FAIL: {badcount} constant(s) depend on a non-standard axiom:")
        for line in combined.splitlines():
            if "AXIOMSWEEP_BAD " in line:
                print("  " + line.split("AXIOMSWEEP_BAD ", 1)[1])
        return 1

    mapped = sum(source_counts.values()) if source_counts else 0
    print(f"PASS: all {total} environment constants "
          f"({total - free} via {{{', '.join(ALLOWED)}}}, {free} axiom-free) "
          f"are axiom-clean.")
    if mapped:
        print(f"      (The source map lists {mapped} declarations for these "
              f"modules; the difference is elaborator output — equation "
              f"lemmas, match auxiliaries, instance projections — which a "
              f"source scan cannot see and this sweep does.)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
