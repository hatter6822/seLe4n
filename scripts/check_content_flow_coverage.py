#!/usr/bin/env python3
"""Fail if a live syscall arm moves content its taint classification does not admit.

WS-SM SM9.D.7.  `contentFlowClass` (`InformationFlow/TaintPropagation.lean`) is
a **total** `SyscallId -> ContentFlowClass`, so a new syscall is a missing case
at elaboration.  That is necessary and not sufficient, and §3.7 of
`docs/planning/SMP_DECLASSIFICATION_COMPLETION_PLAN.md` says why in the sharpest
form the plan reaches: *totality over the wrong domain proves nothing about the
right one*.  `SyscallId` is exhaustive of dispatch **arms**; the taint
propagation is about **sub-transitions**, and no type in the tree enumerates
those.

So the completeness of the classification is established by **reach**, in the
idiom `check_live_arm_per_core_routing.py` already set for exactly this shape of
obligation: start from the live arms, walk the transitive callees through Lean's
elaborated environment, and fail on any arm that reaches a content write its
class does not admit.

Three properties, and each one has caught a different mistake in review:

* **(A) No unclassified content movement.**  An arm classified `.inert` (or
  `.clearsProvenance`) must not reach a constant that writes a content channel.
  A missed site here is a detector that misses real laundering — the unsafe
  direction.
* **(B) No vacuous classification.**  An arm classified `.movesContent` must
  reach one.  A classification that claims content movement and declares no
  edges is a lie in the other direction, and it is exactly what a hand-written
  table drifts into.
* **(C) One taint writer.**  The constants that write `SystemState.declassificationTaint`
  must be exactly the declared propagation surface.  This is the machine-checked
  form of SM9.D.12's "frames for every non-content transition": rather than
  hand-writing a frame lemma per transition, the gate establishes that no other
  constant can move the field at all, which `storeObject_declassificationTaint_eq`
  then makes true of every object write.

**What a content channel is, derived rather than asserted.**  A kernel object
carries user content in exactly two fields — `TCB.pendingMessage` (the IPC
message a thread holds) and `Notification.state` (the badge).  The probe finds
*writes* to those fields structurally: an application of the structure's
constructor whose argument at that field's index is neither a projection of the
same record (an unchanged field in a `{ r with ... }` update) nor a closed term
(`none`, `.idle` — a **clear**, which destroys content rather than moving it).
No spelling of the update can hide from that, which is the reason detection runs
against the elaborated environment and not against source text.

**Reach, stated honestly.**  Arm bodies come from the source text of the three
dispatch functions — text answers "which functions does this arm name" correctly
— read through the comment-free code view, so a commented-out call cannot add a
root and a docstring cannot remove one.  Everything after that is the elaborated
environment.  The walk is bounded by `--depth`; `--self-test` is the check that
the reach is not vacuous, planting a content write under an inert arm and
requiring the gate to find it.

Usage:  scripts/check_content_flow_coverage.py [--depth N] [--list] [--self-test]
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO, "scripts"))
import lean_code_view  # noqa: E402  (needs the path insert above)

API = os.path.join(REPO, "SeLe4n", "Kernel", "API.lean")
TAINT = os.path.join(REPO, "SeLe4n", "Kernel", "InformationFlow", "TaintPropagation.lean")

# The three dispatch functions whose arms are the live roots.  `dispatchWithCap`
# is the unchecked twin; it is walked too, because a content move reachable only
# from the unchecked arm is still a content move.
DISPATCHERS = ("dispatchCapabilityOnly", "dispatchWithCap", "dispatchWithCapChecked")

# WS-SM SM9.D.7 (C): the declared taint-writing surface.  Every other constant
# in the tree must leave `declassificationTaint` alone — which is what makes
# `applySyscallTaint` "the one writer" a checked fact.  Entries are the
# propagation API itself plus the entry point that applies it.
DECLARED_TAINT_WRITERS = {
    "SeLe4n.Kernel.TaintTable.set",
    "SeLe4n.Kernel.TaintTable.joinAt",
    "SeLe4n.Kernel.TaintTable.clearAt",
    "SeLe4n.Kernel.applyTaintFlow",
    "SeLe4n.Kernel.applyTaintClears",
    "SeLe4n.Kernel.applyOrigination",
    "SeLe4n.Kernel.applySyscallTaint",
}

# The two content channels, as (structure, field) pairs.  Named because they are
# the *subject* the gate is about; the gate then checks that the domain it
# quantifies over — every live arm — is exhaustive of what it polices.
# WS-SM SM9.D.7 (C): definitions that legitimately consume the taint-writing API
# without being part of it — the live entry point that applies a plan, and the
# planner that builds one.  Anything else naming the API is a finding.
DECLARED_TAINT_CONSUMERS = {
    "SeLe4n.Kernel.syscallEntryChecked",
    "SeLe4n.Kernel.TaintTable.empty",
}

# WS-SM SM9.D.17 (audit): the definitions allowed to write
# `SystemState.declassificationTaint` DIRECTLY (a `{ st with .. }` update whose
# taint argument is not the field's own projection).  Exactly the apply step —
# everything else must route through it or leave the field alone.
DECLARED_FIELD_WRITERS = {
    "SeLe4n.Kernel.applySyscallTaint",
}

CONTENT_CHANNELS = [
    ("SeLe4n.Model.TCB", "pendingMessage"),
    ("SeLe4n.Model.Notification", "pendingBadge"),
]

# The self-test's planted channel: a field every inert scheduling arm writes
# with an open value (`priority := newPrio`).  If the write detector has stopped
# detecting, planting it flags nothing and the self-test fails — which is the
# whole point, since a gate that has lost its reach reports PASS.
SELF_TEST_CHANNEL = ("SeLe4n.Model.TCB", "priority")

SHAPE = os.path.join(REPO, "SeLe4n", "Kernel", "Architecture", "SyscallReturn.lean")

PROBE = r"""
import SeLe4n
import SeLe4n.Platform.Staged
import Lean.Elab.Command

open Lean Elab Command

private def cfChannels : List (Name × Name) :=
  [@CHANNELS@]

private def cfRoots : List (String × String) :=
  [@ROOTS@]

private def cfTaintApi : List Name :=
  [@TAINTAPI@]

private def cfDepth : Nat := @DEPTH@

/-- Total: `Name.getString!` panics on a numeric component and this environment
has well over a hundred thousand constants. -/
private def cfLast : Name -> String
  | .str _ s => s
  | _        => ""

/-- Is `e` the projection of `field` out of *some* record?  Both spellings:
the compiler's `Expr.proj` and an application of the generated projection
function.  An unchanged field of a `{ r with .. }` update is one of these, and
must not be read as a write. -/
private def cfIsProjection (structName field : Name) (idx : Nat) (e : Expr) : Bool :=
  match e with
  | .proj s i _ => s == structName && i == idx
  | _ =>
    match e.getAppFn with
    | .const n _ => n == structName ++ field
    | _ => false

/-- A **write** of one content channel: the constructor applied with an argument
at the field's index that is neither a projection (unchanged) nor a closed term
(a clear -- `none`, `.idle`).  An open term is content coming from somewhere
else, which is precisely what taint has to follow. -/
private partial def cfScan (structName field : Name) (idx : Nat) : Expr -> Bool
  | e@(.app _ _) =>
      let hit :=
        match e.getAppFn with
        | .const n _ =>
            if n == structName ++ `mk then
              match e.getAppArgs[idx]? with
              | none => false
              | some a =>
                  !cfIsProjection structName field idx a && (a.hasLooseBVars || a.hasFVar)
            else false
        | _ => false
      hit || e.getAppArgs.any (cfScan structName field idx)
        || cfScan structName field idx e.getAppFn
  | .lam _ t b _ => cfScan structName field idx t || cfScan structName field idx b
  | .forallE _ t b _ => cfScan structName field idx t || cfScan structName field idx b
  | .letE _ t v b _ =>
      cfScan structName field idx t || cfScan structName field idx v
        || cfScan structName field idx b
  | .mdata _ b => cfScan structName field idx b
  | .proj _ _ b => cfScan structName field idx b
  | _ => false

/-- The channel indices, resolved once. -/
private def cfChannelIdx (env : Environment) : List (Name × Name × Nat) :=
  cfChannels.filterMap fun (structName, field) =>
    match (getStructureFields env structName).findIdx? (· == field) with
    | none => none
    | some idx => some (structName, field, idx)

private def cfWritesChannel (idxs : List (Name × Name × Nat)) (e : Expr) : Bool :=
  idxs.any fun (structName, field, idx) => cfScan structName field idx e

/-- Resolve a short name to every non-internal constant whose last component
matches.  Ambiguity is harmless here: the walk is a union, so over-resolving can
only widen the reach, never hide a write. -/
private def cfResolve (env : Environment) (stem : String) : List Name :=
  env.constants.fold (init := []) fun acc n _ =>
    if cfLast n == stem && !n.isInternal then n :: acc else acc

private def cfUsed (env : Environment) (n : Name) : List Name :=
  match env.find? n with
  | none => []
  | some ci =>
    match ci.value? with
    | some v => v.getUsedConstants.toList
    | none => []

/-- Bounded transitive closure over the elaborated call graph. -/
private partial def cfClosureGo (env : Environment) (frontier : List Name) (d : Nat)
    (seen : NameSet) : NameSet :=
  match d with
  | 0 => seen
  | d + 1 =>
    let next := frontier.flatMap (cfUsed env)
    let fresh := next.filter (fun n => !seen.contains n)
    if fresh.isEmpty then seen
    else cfClosureGo env fresh d (fresh.foldl (fun s n => s.insert n) seen)

private def cfClosure (env : Environment) (seeds : List Name) (depth : Nat) : NameSet :=
  cfClosureGo env seeds depth (seeds.foldl (fun s n => s.insert n) ({} : NameSet))

/-- Is `e` a projection of *any* field of `structName`?  Both spellings, with
the projection-function spelling checked against the structure's own field
list rather than a namespace prefix — `SystemState.getTcb? st` lives in the
namespace but is not a projection, and reading it as one would let an update
masquerade as a fresh literal. -/
private def cfIsAnyProjection (structName : Name) (fields : List Name) (e : Expr) : Bool :=
  match e with
  | .proj s _ _ => s == structName
  | _ =>
    match e.getAppFn with
    | .const n _ => fields.any (fun f => n == structName ++ f)
    | _ => false

/-- A **direct write of one structure field in an update**: the constructor
applied with (a) at least one *other* argument that is a projection of the same
structure — which is what distinguishes `{ st with .. }` from a fresh literal —
and (b) the watched field's argument not a projection.  Open or closed: a
closed non-projection argument in an update is a silent *clear*, which for a
provenance table is a laundering enabler and must be as visible as a rewrite. -/
private partial def cfUpdateWritesField (structName field : Name) (fields : List Name)
    (idx : Nat) : Expr -> Bool
  | e@(.app _ _) =>
      let hit :=
        match e.getAppFn with
        | .const n _ =>
            if n == structName ++ `mk then
              let args := e.getAppArgs
              let isUpdate := (List.range args.size).any fun i =>
                i != idx && match args[i]? with
                  | some a => cfIsAnyProjection structName fields a
                  | none => false
              match args[idx]? with
              | none => false
              | some a => isUpdate && !cfIsProjection structName field idx a
            else false
        | _ => false
      hit || e.getAppArgs.any (cfUpdateWritesField structName field fields idx)
        || cfUpdateWritesField structName field fields idx e.getAppFn
  | .lam _ t b _ =>
      cfUpdateWritesField structName field fields idx t
        || cfUpdateWritesField structName field fields idx b
  | .forallE _ t b _ =>
      cfUpdateWritesField structName field fields idx t
        || cfUpdateWritesField structName field fields idx b
  | .letE _ t v b _ =>
      cfUpdateWritesField structName field fields idx t
        || cfUpdateWritesField structName field fields idx v
        || cfUpdateWritesField structName field fields idx b
  | .mdata _ b => cfUpdateWritesField structName field fields idx b
  | .proj _ _ b => cfUpdateWritesField structName field fields idx b
  | _ => false

run_cmd do
  let env <- getEnv
  let idxs := cfChannelIdx env
  if idxs.length != cfChannels.length then
    logInfo m!"CF_CHANNEL_UNRESOLVED {cfChannels.length - idxs.length}"
  -- (C2) every definition that writes `SystemState.declassificationTaint`
  -- DIRECTLY, in a structure update — the write no API-naming check can see.
  let stateName := `SeLe4n.Model.SystemState
  let stateFields := (getStructureFields env stateName).toList
  match stateFields.findIdx? (· == `declassificationTaint) with
  | none => logInfo m!"CF_FIELD_UNRESOLVED declassificationTaint"
  | some fieldIdx =>
    let fieldWriters : List Name :=
      env.constants.fold (init := []) fun acc n ci =>
        if n.isInternal then acc
        else match ci with
          | .defnInfo di =>
              -- Prefilter on the constructor's presence: an Expr that never
              -- names `SystemState.mk` cannot apply it, and the used-constant
              -- set is cached where a structural walk is not.
              if di.value.getUsedConstants.contains (stateName ++ `mk)
                  && cfUpdateWritesField stateName `declassificationTaint stateFields
                      fieldIdx di.value then n :: acc
              else acc
          | _ => acc
    for w in fieldWriters do
      logInfo m!"CF_FIELD_WRITER {w}"
  -- (C) every constant whose value names the taint-writing API.
  -- Only **definitions** are reported: a theorem naming the API states a
  -- property of it, and a property cannot move a field.  `ConstantInfo.defnInfo`
  -- is exactly that distinction, decided by the elaborator rather than by a
  -- name pattern.
  let writers : List Name :=
    env.constants.fold (init := []) fun acc n ci =>
      if n.isInternal then acc
      else match ci with
        | .defnInfo di =>
            if cfTaintApi.any (fun a => di.value.getUsedConstants.contains a) then n :: acc
            else acc
        | _ => acc
  for w in writers do
    logInfo m!"CF_TAINT_WRITER {w}"
  -- roots: resolve each arm's named callees, then walk.
  for (arm, stems) in cfRoots do
    let stemList := (stems.splitOn " ").filter (fun s => s != "")
    let seeds : List Name := stemList.flatMap (cfResolve env)
    if seeds.isEmpty then
      logInfo m!"CF_NO_ROOT {arm}"
    else
      let reach := cfClosure env seeds cfDepth
      let hits : List Name :=
        reach.toList.filter fun n =>
          match env.find? n with
          | none => false
          | some ci =>
            match ci.value? with
            | none => false
            | some v => cfWritesChannel idxs v
      logInfo m!"CF_ARM {arm} {hits.length}"
      for h in hits.take 6 do
        logInfo m!"CF_HIT {arm} {h}"
"""


def return_shapes() -> dict[str, str]:
    """`syscallReturnShape`'s own arms — the WS-RA total map from syscall to
    the shape of the value it hands back."""
    src = code_view(SHAPE)
    m = re.search(r"^def syscallReturnShape", src, re.M)
    if m is None:
        raise RuntimeError("`syscallReturnShape` not found in SyscallReturn.lean")
    body = src[m.end():]
    nxt = re.search(r"\n(?:private )?(?:def|theorem|abbrev|instance)\s", body)
    if nxt is not None:
        body = body[: nxt.start()]
    out = {}
    for arm, shape in re.findall(r"\|\s*\.([A-Za-z][A-Za-z0-9']*)\s*=>\s*\.([A-Za-z]+)", body):
        out[arm] = shape
    if not out:
        raise RuntimeError("`syscallReturnShape` parsed to no arms")
    return out


def code_view(path: str) -> str:
    return lean_code_view.strip(open(path, encoding="utf-8").read())


def arm_roots() -> dict[str, set[str]]:
    """Per-syscall root stems, read off the dispatch arms' own text."""
    src = code_view(API)
    roots: dict[str, set[str]] = {}
    for dispatcher in DISPATCHERS:
        m = re.search(rf"^(?:private )?def {dispatcher}\b", src, re.M)
        if m is None:
            raise RuntimeError(f"dispatcher `{dispatcher}` not found in API.lean")
        body = src[m.start():]
        nxt = re.search(r"\n(?:private )?(?:def|theorem|abbrev|instance)\s", body[1:])
        if nxt is not None:
            body = body[: nxt.start() + 1]
        # Arms are `| .<name> =>` at the match's own indentation.
        parts = re.split(r"\n\s*\|\s*\.([A-Za-z][A-Za-z0-9']*)\s*=>", body)
        for i in range(1, len(parts) - 1, 2):
            arm, text = parts[i], parts[i + 1]
            ids = set(re.findall(r"\b([a-z][A-Za-z0-9_']{3,})\b", text))
            roots.setdefault(arm, set()).update(ids)
    if not roots:
        raise RuntimeError("no dispatch arms parsed from API.lean")
    return roots


def classification() -> dict[str, str]:
    """`contentFlowClass`'s own arms, read off its source."""
    src = code_view(TAINT)
    m = re.search(r"^def contentFlowClass : SyscallId → ContentFlowClass$", src, re.M)
    if m is None:
        raise RuntimeError("`contentFlowClass` not found in TaintPropagation.lean")
    body = src[m.end():]
    nxt = re.search(r"\n(?:private )?(?:def|theorem|abbrev|instance)\s", body)
    if nxt is not None:
        body = body[: nxt.start()]
    out = {}
    for arm, cls in re.findall(r"\|\s*\.([A-Za-z][A-Za-z0-9']*)\s*=>\s*\.([A-Za-z]+)", body):
        out[arm] = cls
    if not out:
        raise RuntimeError("`contentFlowClass` parsed to no arms")
    return out


def run_probe(roots: dict[str, set[str]], depth: int, channels) -> str:
    quoted_channels = ", ".join(f"(`{s}, `{f})" for s, f in channels)
    quoted_roots = ", ".join(
        '("{}", "{}")'.format(arm, " ".join(sorted(stems)))
        for arm, stems in sorted(roots.items()))
    quoted_api = ", ".join(f"`{n}" for n in sorted(DECLARED_TAINT_WRITERS))
    src = (PROBE
           .replace("@CHANNELS@", quoted_channels)
           .replace("@ROOTS@", quoted_roots)
           .replace("@TAINTAPI@", quoted_api)
           .replace("@DEPTH@", str(depth)))
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as fh:
        fh.write(src)
        path = fh.name
    try:
        proc = subprocess.run(["lake", "env", "lean", path],
                              cwd=REPO, capture_output=True, text=True)
    except FileNotFoundError:
        raise RuntimeError(
            "`lake` is not on PATH, so the content-flow probe cannot elaborate.\n"
            "      This gate detects against Lean's elaborated environment and must run\n"
            "      in a tier that has a built toolchain — it is wired into\n"
            "      test_tier1_build.sh, after the builds.  Tier 0 is deliberately\n"
            "      build-free and cannot host it.") from None
    finally:
        os.unlink(path)
    out = proc.stdout + proc.stderr
    if proc.returncode != 0:
        raise RuntimeError(f"the content-flow probe exited {proc.returncode}\n{out[-4000:]}")
    if re.search(r"^.*\.lean:\d+:\d+: error", out, re.M):
        raise RuntimeError(f"the content-flow probe did not elaborate\n{out[-4000:]}")
    return out


def parse(out: str):
    hits = {}
    for arm, n in re.findall(r"CF_ARM (\S+) (\d+)", out):
        hits[arm] = int(n)
    detail = {}
    for arm, name in re.findall(r"CF_HIT (\S+) (\S+)", out):
        detail.setdefault(arm, []).append(name)
    writers = set(re.findall(r"CF_TAINT_WRITER (\S+)", out))
    field_writers = set(re.findall(r"CF_FIELD_WRITER (\S+)", out))
    field_unresolved = bool(re.search(r"CF_FIELD_UNRESOLVED", out))
    noroot = set(re.findall(r"CF_NO_ROOT (\S+)", out))
    return hits, detail, writers, field_writers, field_unresolved, noroot


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--depth", type=int, default=6)
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    cls = classification()
    roots = arm_roots()
    # Only arms the classification knows about are in scope: an arm name parsed
    # out of the dispatch source that is not a `SyscallId` is a parse artefact,
    # not a syscall.
    roots = {a: s for a, s in roots.items() if a in cls}

    missing = sorted(set(cls) - set(roots))
    channels = list(CONTENT_CHANNELS)
    if args.self_test:
        channels = channels + [SELF_TEST_CHANNEL]

    out = run_probe(roots, args.depth, channels)
    hits, detail, writers, field_writers, field_unresolved, noroot = parse(out)

    failures: list[str] = []

    if args.list:
        for arm in sorted(roots):
            print(f"  {arm:<24} {cls[arm]:<18} content-writes reached: {hits.get(arm, 0)}")
        print(f"  taint writers: {len(writers)}")

    if args.self_test:
        planted = [a for a in roots if cls[a] == "inert" and hits.get(a, 0) > 0]
        if not planted:
            print("FAIL: --self-test planted `TCB.priority` as a content channel and the")
            print("      gate flagged no inert arm.  The write detector has stopped")
            print("      detecting: every production finding below would be a false PASS.")
            return 1
        # The field-writer sweep must detect the one real writer: a sweep that
        # has gone blind reports zero unexpected writers for the same reason it
        # would miss a rogue one, so its bite is asserted here rather than
        # trusted.
        if "SeLe4n.Kernel.applySyscallTaint" not in field_writers:
            print("FAIL: --self-test — the direct-field-writer sweep did not detect")
            print("      `applySyscallTaint`, the one definition that writes")
            print("      `SystemState.declassificationTaint`.  The sweep is blind:")
            print("      a rogue writer would pass check (C2) for the same reason.")
            return 1
        print(f"PASS: --self-test — the planted channel was detected on "
              f"{len(planted)} inert arm(s); the field-writer sweep detected the "
              f"declared writer.")
        return 0

    # (A) no unclassified content movement
    for arm in sorted(roots):
        if cls[arm] in ("inert", "clearsProvenance") and hits.get(arm, 0) > 0:
            failures.append(
                f"  `.{arm}` is classified `.{cls[arm]}` but reaches "
                f"{hits[arm]} content write(s): {', '.join(detail.get(arm, [])[:4])}")

    # (B) no vacuous classification.  A content-moving arm must either write a
    # content channel or deliver through the WS-RA return frame — `syscallReturnShape`
    # is total, so "this syscall hands the caller a value drawn from kernel state"
    # is a derived fact rather than an exception list.  `.notificationWait` is the
    # case: it clears the notification's `pendingBadge` (a closed write) and the
    # badge reaches the waiter in `x0`, so no *object* carries it.  The disjunct can
    # only make the gate more permissive about a `.movesContent` claim, never less
    # strict about an `.inert` one, which is the safe direction.
    shapes = return_shapes()
    for arm in sorted(roots):
        if cls[arm] == "movesContent" and hits.get(arm, 0) == 0:
            if shapes.get(arm, "unit") == "unit":
                failures.append(
                    f"  `.{arm}` is classified `.movesContent`, returns `.unit`, and reaches "
                    f"no content write — either the classification is wrong or the reach "
                    f"has been lost")

    # (C) one taint writer
    # A *theorem* naming the API states a property of it; only a **definition**
    # can move the field.  The check is therefore over constants with
    # computational content, minus the compiler's own equation and match
    # auxiliaries, which carry a definition's body rather than a new one.
    def is_auxiliary(name: str) -> bool:
        return any(seg in name for seg in
                   (".eq_", ".eq_def", "._eq", ".match_", ".proof_", ".induct",
                    ".fun_cases", ".brecOn", ".below", "._sunfold", "._unsafe_rec",
                    ".ind_", ".congr", ".sizeOf"))

    unexpected = sorted(w for w in writers
                        if w not in DECLARED_TAINT_WRITERS
                        and not is_auxiliary(w)
                        and w not in DECLARED_TAINT_CONSUMERS)
    if unexpected:
        failures.append(
            "  constants outside the declared propagation surface name the taint-writing "
            "API:\n      " + "\n      ".join(unexpected[:12]))

    # (C2) one field writer.  Check (C) sees only constants that NAME the taint
    # API; a definition writing `SystemState.declassificationTaint` directly in
    # a `{ st with .. }` update names nothing and would escape it — including a
    # closed-term write, which for a provenance table is a silent whole-table
    # clear, a laundering enabler.  The probe therefore scans every definition's
    # elaborated value for an update whose taint-field argument is not the
    # field's own projection.  Fresh literals (boot, defaults, test builders)
    # carry no same-structure projection and are exactly the constructions this
    # sweep must not flag.
    if field_unresolved:
        failures.append(
            "  the probe could not resolve `SystemState.declassificationTaint`'s field "
            "index — the direct-write sweep ran on nothing.  Fails closed.")
    unexpected_field = sorted(w for w in field_writers
                              if w not in DECLARED_FIELD_WRITERS
                              and not is_auxiliary(w))
    if unexpected_field:
        failures.append(
            "  constants write `SystemState.declassificationTaint` directly, outside "
            "the declared writer:\n      " + "\n      ".join(unexpected_field[:12]))

    if noroot:
        failures.append(
            "  no callee could be resolved for arm(s): " + ", ".join(sorted(noroot)) +
            "\n      The gate fails closed: an arm whose roots do not resolve is "
            "unchecked, not clean.")

    if missing:
        failures.append(
            "  classified syscalls with no dispatch arm parsed: " + ", ".join(missing) +
            "\n      Either the arm was renamed or the parser has lost its reach.")

    if failures:
        print("FAIL: content-flow coverage (WS-SM SM9.D.7)")
        for f in failures:
            print(f)
        return 1

    moving = sum(1 for a in roots if cls[a] == "movesContent")
    by_write = sum(1 for a in roots if cls[a] == "movesContent" and hits.get(a, 0) > 0)
    print(f"PASS: content-flow coverage — {len(roots)} live arms classified; "
          f"{moving} moving content ({by_write} reaching an object content write, "
          f"{moving - by_write} delivering through the return frame); "
          f"{len(roots) - moving} inert or clearing, none reaching a content write.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
